import type { Declaration, Module } from './ast.js';

/** Module-owned names collected before type inference.  This deliberately
 * preserves qualification; later phases resolve imports against interfaces
 * instead of flattening every declaration into one global environment. */
export interface ModuleInterface {
  module: string;
  values: ReadonlySet<string>;
  constructors: ReadonlySet<string>;
  fields: ReadonlySet<string>;
  constructorsByType: ReadonlyMap<string, ReadonlySet<string>>;
  fieldsByType: ReadonlyMap<string, ReadonlySet<string>>;
  types: ReadonlySet<string>;
  /** False when parsed declarations still have no namespace representation
   * (for example a class).  Such an interface cannot soundly reject an
   * explicit import list yet. */
  complete: boolean;
}

export function collectInterface(module: Module): ModuleInterface {
  const values = new Set<string>(); const constructors = new Set<string>(); const fields = new Set<string>(); const types = new Set<string>(); const constructorsByType = new Map<string, ReadonlySet<string>>(); const fieldsByType = new Map<string, ReadonlySet<string>>(); let complete = true;
  for (const declaration of module.declarations) { collect(declaration, values, constructors, fields, types); if (declaration.tag === 'data') { constructorsByType.set(declaration.name, new Set(declaration.constructors.map(constructor => constructor.name))); fieldsByType.set(declaration.name, new Set(declaration.constructors.flatMap(constructor => constructor.fields ?? []))); } if (declaration.tag === 'unsupported') complete = false; }
  return { module: module.name, values, constructors, fields, types, constructorsByType, fieldsByType, complete };
}

function collect(declaration: Declaration, values: Set<string>, constructors: Set<string>, fields: Set<string>, types: Set<string>) {
  if (declaration.tag === 'value' || declaration.tag === 'foreign' || declaration.tag === 'signature') values.add(declaration.name);
  if (declaration.tag === 'data') { types.add(declaration.name); for (const constructor of declaration.constructors) { constructors.add(constructor.name); for (const field of constructor.fields ?? []) fields.add(field); } }
  if (declaration.tag === 'typeAlias') types.add(declaration.name);
  if (declaration.tag === 'class') { types.add(declaration.name); for (const member of declaration.members) collect(member, values, constructors, fields, types); }
  if (declaration.tag === 'instance') for (const member of declaration.members) collect(member, values, constructors, fields, types);
}
