/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Basic

/-!
# Projection formulas for adelic norm maps

For a finite extension of number fields `L/K`, the relative norm of an adele multiplied by an
extended base adele is the norm of the original adele multiplied by the `[L : K]`-th power of
the base adele. This is the projection formula

`N_{L/K}(a x) = a ^ [L : K] N_{L/K}(x)`.

The formula is stated for finite adeles, infinite adeles, and full adeles, where scalar
multiplication uses the algebra structure induced by the corresponding extension map. For ideles
and idele classes, the extension is a group homomorphism rather than an algebra structure, and
the formula is the `simp` normal form given by `map_mul` together with
`ideleNormMap_ideleExtension` and `ideleClassNormMap_ideleClassExtension`.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleNorm_smul`: the finite-adele projection formula.
* `TauCeti.GlobalNumberFields.infiniteAdeleNorm_smul`: the infinite-adele projection formula.
* `TauCeti.GlobalNumberFields.adeleNorm_smul`: the full-adele projection formula.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, (8.4), and Chapter VI, §2.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped AdeleExtension FiniteAdeleExtension InfiniteAdeleExtension

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The finite-adele projection formula.** The relative norm of a finite adele multiplied by
an extended base adele is the norm of the original adele multiplied by the field-degree power of
the base adele. -/
@[simp]
theorem finiteAdeleNorm_smul (a : FiniteAdeleRing (𝓞 K) K)
    (x : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleNorm K L (a • x) = a ^ Module.finrank K L * finiteAdeleNorm K L x := by
  rw [Algebra.smul_def, algebraMap_finiteAdeleExtensionAlgebra, map_mul,
    finiteAdeleNorm_finiteAdeleExtension]

/-- **The infinite-adele projection formula.** The relative norm of an infinite adele multiplied
by an extended base adele is the norm of the original adele multiplied by the field-degree power
of the base adele. -/
@[simp]
theorem infiniteAdeleNorm_smul (a : InfiniteAdeleRing K) (x : InfiniteAdeleRing L) :
    infiniteAdeleNorm K L (a • x) = a ^ Module.finrank K L * infiniteAdeleNorm K L x := by
  rw [Algebra.smul_def, algebraMap_infiniteAdeleExtensionAlgebra, map_mul,
    infiniteAdeleNorm_infiniteAdeleExtension]

/-- **The adele projection formula.** The relative norm of an adele multiplied by an extended
base adele is the norm of the original adele multiplied by the field-degree power of the base
adele. -/
@[simp]
theorem adeleNorm_smul (a : AdeleRing (𝓞 K) K) (x : AdeleRing (𝓞 L) L) :
    adeleNorm K L (a • x) = a ^ Module.finrank K L * adeleNorm K L x := by
  rw [Algebra.smul_def, algebraMap_adeleExtensionAlgebra, map_mul,
    adeleNorm_adeleExtension]

end TauCeti.GlobalNumberFields
