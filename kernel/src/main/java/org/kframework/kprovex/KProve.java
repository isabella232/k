// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.kprovex;

import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.attributes.Source;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kprove.KProveOptions;
import org.kframework.krun.KRun;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.unparser.ToJson;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.io.File;
import java.io.UnsupportedEncodingException;
import java.util.function.Function;

public class KProve {

    public static final String BOUNDARY_CELL_PREFIX = "BOUND_";

    private final KExceptionManager kem;
    private final FileUtil files;
    private final KPrint kprint;
    private final KProveOptions kproveOptions;
    private final CompiledDefinition compiledDefinition;
    private final BinaryLoader loader;
    private final ProofDefinitionBuilder proofDefinitionBuilder;
    private final Function<Definition, Rewriter> rewriterGenerator;
    private final Stopwatch sw;

    @Inject
    public KProve(KExceptionManager kem, FileUtil files, KPrint kprint, KProveOptions kproveOptions,
                  CompiledDefinition compiledDefinition, BinaryLoader loader,
                  ProofDefinitionBuilder proofDefinitionBuilder, Function<Definition, Rewriter> rewriterGenerator, Stopwatch sw) {
        this.kem = kem;
        this.files = files;
        this.kprint = kprint;
        this.kproveOptions = kproveOptions;
        this.compiledDefinition = compiledDefinition;
        this.loader = loader;
        this.proofDefinitionBuilder = proofDefinitionBuilder;
        this.rewriterGenerator = rewriterGenerator;
        this.sw = sw;
        // validate kprovex options. There are too many dependencies to have duplicate options files
        // so use the same class, but throw an error if used by accident. It would have been silent anyway.
        // TODO: remove once transition to kprovex is finished
        if (kproveOptions.defModule != null) {
            throw KEMException.criticalError("Option `--def-module` no longer supported in the kprovex tool.");
        }
        if (kproveOptions.saveProofDefinitionTo != null) {
            throw KEMException.criticalError("Option `--save-proof-definition-to` no longer supported in the kprovex tool.");
        }
        if (!kproveOptions.extraConcreteRuleLabels.isEmpty()) {
            throw KEMException.criticalError("Option `--concrete-rules` no longer supported in the kprovex tool.");
        }
    }

    public int run() {
        if (!kproveOptions.specFile(files).exists()) {
            throw KEMException.criticalError("Definition file doesn't exist: " +
                    kproveOptions.specFile(files).getAbsolutePath());
        }

        Tuple2<Definition, Module> compiled = proofDefinitionBuilder
                .build(kproveOptions.specFile(files), kproveOptions.specModule, compiledDefinition.kompileOptions.readOnlyKompiledDirectory);

        Rewriter rewriter = rewriterGenerator.apply(compiled._1());
        Module specModule = compiled._2();
        Rule boundaryPattern = buildBoundaryPattern(compiledDefinition);

        if (kproveOptions.emitJson) {
            try {
                files.saveToKompiled("prove-definition.json", new String(ToJson.apply(compiled._1()), "UTF-8"));
            } catch (UnsupportedEncodingException e) {
                throw KEMException.criticalError("Unsupported encoding `UTF-8` when saving JSON definition.");
            }
        }

        if (kproveOptions.emitJsonSpec != null) {
            files.saveToWorkingDirectory(kproveOptions.emitJsonSpec, ToJson.apply(specModule));
        }

        RewriterResult results = rewriter.prove(specModule, boundaryPattern, true);
        sw.printIntermediate("Backend");
        kprint.prettyPrint(compiled._1(), compiled._1().getModule("LANGUAGE-PARSING").get(), kprint::outputFile,
                results.k());
        sw.printTotal("Total");
        return results.exitCode().orElse(KEMException.TERMINATED_WITH_ERRORS_EXIT_CODE);
    }

    /**
     * A pattern that implements --boundary-cells functionality. When this pattern matches, in the resulting
     * substitution, for each boundary cell there will be a variable starting with {@code "BOUND_"}. Other variables
     * must be ignored.
     *
     * @return the rule corresponding to boundary pattern, or null if no boundary cells were set.
     */
    public Rule buildBoundaryPattern(CompiledDefinition compiledDefinition) {
        if (kproveOptions.boundaryCells.isEmpty()) {
            return null;
        }
        StringBuilder patternStr = new StringBuilder();
        for (String cell : kproveOptions.boundaryCells) {
            //for each boundary cell add a sequence of the form `<cell> VAR </cell>`
            patternStr.append(String.format("<%2$s> %1$s%2$s </%2$s> ", BOUNDARY_CELL_PREFIX, cell));
        }

        return KRun.compilePattern(files, kem, patternStr.toString(), compiledDefinition,
                Source.apply("<option --boundary-cells>"));
    }
}
