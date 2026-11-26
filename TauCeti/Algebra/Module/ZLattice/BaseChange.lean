/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.RingTheory.IsTensorProduct
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# A full lattice as an integral form of its ambient space

Let `L` be a `ℤ`-lattice in a finite-dimensional vector space `E` over a normed ordered field `K`,
that is, a discrete subgroup spanning `E`. Every `ℤ`-basis of `L` is a `K`-basis of `E`
(`Module.Basis.ofZLatticeBasis`), so `E` is the base change `K ⊗[ℤ] L` through the inclusion of
`L`. This is the analogue, for a normed field such as `ℝ` in place of the field of fractions `ℚ`,
of `Submodule.isBaseChange_subtype`.

In this form a lattice can be fed to statements about integral forms of a representation, such
as the comparison of the Herbrand quotients of two Galois-stable lattices in one real
representation (`TauCeti.TateCohomology.herbrandQuotient_eq_of_isBaseChange`).

## Main results

* `ZLattice.isBaseChange_subtype`: the inclusion of a full `ℤ`-lattice exhibits the ambient space
  as its base change to `K`.
* `TauCeti.ZLattice.baseChangeEquiv`: the resulting identification `K ⊗[ℤ] L ≃ E`,
  `r ⊗ x ↦ r • x`.
* `TauCeti.ZLattice.baseChangeEquiv_baseChange_restrict`: this identification is natural in
  `K`-linear maps `f : E → E'` with `f(L) ⊆ L'`.
-/

public section

open Module TensorProduct

namespace ZLattice

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E] [ProperSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L]

/-- **A full lattice is an integral form of its ambient space**: the inclusion of a discrete
`ℤ`-submodule `L` spanning `E` over `K` exhibits `E` as the base change `K ⊗[ℤ] L`. -/
theorem isBaseChange_subtype : IsBaseChange K L.subtype := by
  have := ZLattice.module_free K L
  -- `L.subtype` carries a `ℤ`-basis `b` of `L` to the `K`-basis `b.ofZLatticeBasis K L` of `E`
  let b := Free.chooseBasis ℤ L
  exact b.isBaseChange_of_map_basis (b.ofZLatticeBasis K L) L.subtype
    fun i ↦ (b.ofZLatticeBasis_apply K L i).symm

end ZLattice

namespace TauCeti.ZLattice

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E] [ProperSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L]

/-- The base change `K ⊗[ℤ] L` of a full lattice `L ⊆ E` is identified with `E`, by
`r ⊗ x ↦ r • x`. -/
noncomputable def baseChangeEquiv : K ⊗[ℤ] L ≃ₗ[K] E :=
  (_root_.ZLattice.isBaseChange_subtype K L).equiv

/-- The identification sends a pure tensor `r ⊗ x` to `r • x`. -/
@[simp]
theorem baseChangeEquiv_tmul (r : K) (x : L) :
    baseChangeEquiv K L (r ⊗ₜ x) = r • (x : E) :=
  (_root_.ZLattice.isBaseChange_subtype K L).equiv_tmul r x

/-- A lattice vector `x` corresponds to `1 ⊗ x` in the base change. -/
@[simp]
theorem baseChangeEquiv_symm_coe (x : L) :
    (baseChangeEquiv K L).symm x = 1 ⊗ₜ x :=
  (_root_.ZLattice.isBaseChange_subtype K L).equiv_symm_apply x

variable {K L} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace K E'] [FiniteDimensional K E']
  [ProperSpace E'] {L' : Submodule ℤ E'} [DiscreteTopology L'] [IsZLattice K L']

/-- **Naturality of `baseChangeEquiv`**: for a `K`-linear map `f : E → E'` carrying `L` into
`L'`, the base change of its restriction `L → L'` corresponds to `f` under the identifications
`K ⊗[ℤ] L ≃ E` and `K ⊗[ℤ] L' ≃ E'`. -/
@[simp]
theorem baseChangeEquiv_baseChange_restrict (f : E →ₗ[K] E')
    (hf : ∀ x ∈ L, f.restrictScalars ℤ x ∈ L') (x : K ⊗[ℤ] L) :
    baseChangeEquiv K L' (LinearMap.baseChange K ((f.restrictScalars ℤ).restrict hf) x) =
      f (baseChangeEquiv K L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp
  | add x y hx hy => simp [hx, hy]

end TauCeti.ZLattice
