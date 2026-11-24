/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Dual.Transpose
public import TauCeti.Algebra.Lie.Multiplicity
-- Non-public: a finite-dimensional module is reflexive.
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The multiplicity of an irreducible module in a dual module

For Lie modules `M` and `S`, `LieModule.isotypicMultiplicity R L M S` is the finrank of the space
of morphisms `S → M`. This file computes the multiplicity of the dual `S*` in the dual `M*`:

`m_{M*}(S*) = dim (M →ₗ⁅R,L⁆ S)`,

because transposition identifies `S* → M*` with `M → S` once `S` is reflexive
(`TauCeti.LieModule.dualMapEquiv`). The right-hand side counts morphisms *out of* `M`, while the
multiplicity counts morphisms *into* `M`; the two have the same rank when `M` is completely
reducible and `S` is irreducible (`LieModule.finrank_lieModuleHom_eq_isotypicMultiplicity`). Hence

`m_{M*}(S*) = m_M(S)`

for every finite-dimensional completely reducible `M` and finite-dimensional irreducible `S` over a
field (`LieModule.isotypicMultiplicity_dual_dual`).
Applied to a finite-dimensional semisimple Lie algebra over a field of characteristic zero, where
every finite-dimensional module is completely reducible, this computes the multiplicities of the
dual module from those of the module.

## Main results

* `LieModule.isotypicMultiplicity_dual_dual_eq_finrank_lieModuleHom`: the multiplicity of `S*` in
  `M*` is `dim (M →ₗ⁅R,L⁆ S)`, for every reflexive `S`.
* `LieModule.isotypicMultiplicity_dual_dual`: **`S*` occurs in `M*` as often as `S` occurs in
  `M`**, for finite-dimensional completely reducible `M` and finite-dimensional irreducible `S`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre I, §3.3.
-/

public section

open Module (Dual finrank)

universe u v w w₁

namespace LieModule

/-! ### The multiplicity of a dual in a dual -/

section Dual

variable (R : Type u) (L : Type v) (M : Type w) (S : Type w₁)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]

/-- **The multiplicity of `S*` in `M*` counts the morphisms `M → S`**, for reflexive `S`. -/
theorem isotypicMultiplicity_dual_dual_eq_finrank_lieModuleHom [Module.IsReflexive R S] :
    isotypicMultiplicity R L (Dual R M) (Dual R S) = finrank R (M →ₗ⁅R,L⁆ S) := by
  rw [isotypicMultiplicity_def, (TauCeti.LieModule.dualMapEquiv R L M S).finrank_eq]

end Dual

section CompletelyReducible

variable {K : Type u} {L : Type v} (M : Type w) (S : Type w₁)
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
variable [ComplementedLattice (LieSubmodule K L M)]
variable [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S] [IsIrreducible K L S]

/-- **`S*` occurs in `M*` as often as `S` occurs in `M`.** Here `M` is a finite-dimensional
module over a field whose Lie submodules form a complemented lattice, and `S` is a
finite-dimensional irreducible module. -/
theorem isotypicMultiplicity_dual_dual [FiniteDimensional K S] :
    isotypicMultiplicity K L (Dual K M) (Dual K S) = isotypicMultiplicity K L M S := by
  rw [isotypicMultiplicity_dual_dual_eq_finrank_lieModuleHom,
    finrank_lieModuleHom_eq_isotypicMultiplicity]

end CompletelyReducible

end LieModule
