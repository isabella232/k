package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.KLabel;

/**
 * Propagate macro, macro-rec, alias, and alias-rec labels from productions to rules that only contain that klabel on the LHS
 * This prepares rules for macro expansion in ExpandMacros
 */
public class PropagateMacro {
    private final Module m;

    public PropagateMacro(Module m) {
        this.m = m;
    }

    public Sentence propagate(Sentence s) {
        if (s instanceof Rule && m.ruleLhsHasMacroKLabel((Rule) s)) {
            Att macroAtt = m.attributesFor().apply(m.matchKLabel((Rule) s));
            return Rule.apply(((Rule) s).body(), ((Rule) s).requires(), ((Rule) s).ensures(), s.att().add(macroAtt.getMacro().get()));
        }
        return s;
    }
}
