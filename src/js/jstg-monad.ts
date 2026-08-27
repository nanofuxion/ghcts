/** Port of GHC.JS.JStg.Monad: the computational environment for the eDSL used
 * to write the JS backend's RTS - a state monad holding a prefix to tag
 * identifiers with, and a supply of fresh identifiers.
 *
 * Haskell threads this through `do`-notation over `State JEnv`; TypeScript has
 * no equivalent sugar, so JSM is a small stateful class instead and the
 * threading is explicit. The free functions below (newIdent, withTag,
 * initJSM, runJSM) mirror the Haskell export list and just delegate to it. */
import type { Ident } from "./ident.js";
import { name } from "./ident.js";

/** GHC.JS.JStg.Monad's JEnv: prefix for generated names plus the identifier
 * supply. JSM plays the role of both JEnv and the State monad over it. */
export class JSM {
  private next = 0;
  constructor(private prefix = "js") {}

  /** generate a fresh Ident, formatted as GHC's mk_ident: "<prefix>_<unique>" */
  newIdent(): Ident {
    return name(`${this.prefix}_${this.next++}`);
  }

  /** tag the name generator with a prefix for the duration of the action,
   * then restore the previous prefix - GHC.JS.JStg.Monad.withTag. */
  withTag<T>(tag: string, action: (env: JSM) => T): T {
    const old = this.prefix;
    this.prefix = tag;
    try {
      return action(this);
    } finally {
      this.prefix = old;
    }
  }
}

/** GHC.JS.JStg.Monad.newIdent, as a free function over an explicit env. */
export const newIdent = (env: JSM): Ident => env.newIdent();

/** GHC.JS.JStg.Monad.withTag, as a free function over an explicit env. */
export const withTag = <T>(env: JSM, tag: string, action: (env: JSM) => T): T => env.withTag(tag, action);

/** GHC.JS.JStg.Monad.initJSM: create a new environment tagged "js". */
export const initJSM = (): JSM => new JSM("js");

/** GHC.JS.JStg.Monad.runJSM: run a JSM computation against an environment. */
export const runJSM = <T>(env: JSM, computation: (env: JSM) => T): T => computation(env);
