/** Port of GHC.JS.Ident.
 *
 * Kept as small as possible, exactly as the Haskell module insists: anything
 * added here couples every consumer of the JS backend EDSL to it.
 */
export type Ident = string;

/** GHC.JS.Ident.name: FastString -> Ident. A FastString is just a string in
 * TS, so this smart constructor is identity - but it stays as the single
 * seam consumers should go through, matching the Haskell module's intent. */
export const name = (fastString: string): Ident => fastString;
