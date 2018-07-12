/+ How to use:
 +
 + If you just want to use the provider parser generators, just `import pathogen`.
 + If you want to extend `pathogen`, e.g. generate parsers for new types, you can `import pathogen.gene : gene`,
 + and then `mixin gene!()`. This is because parser generators in `pathogen` will need to use the parser generator
 + templates defined in your package, and this is not possible under normal lookup rules.
 +/
module pathogen;

public import pathogen.base;
import pathogen.gene : gene;
mixin gene!();
