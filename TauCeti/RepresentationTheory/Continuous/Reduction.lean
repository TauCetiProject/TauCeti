/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Charpoly

/-!
# Reduction of a continuous representation to the residue field

Let `A` be a topological local ring with a ring topology on its residue field `k_A` for which the
residue map is continuous (`ContinuousSMul A k_A`). The case of interest is the discrete topology
on `k_A`, where continuity of the residue map says that the maximal ideal is open. The
*raw reduction* of a continuous representation `ρ` of `Γ` on a finite `A`-module `M` is its
extension of scalars `k_A ⊗[A] M` to `k_A`, a continuous representation over `k_A`. On a finite
free module the characteristic polynomial and the determinant of `g` on the reduction are the
reductions modulo `𝔪_A` of those of `ρ g`, and over a finite residue field the reduction has
finite image.

No semisimplification is applied: for `(1 a; 0 1)` with `a ∈ ℤ_ℓ^×` acting on `ℚ_ℓ²`, the
lattices `ℤ_ℓ²` and `ℤ_ℓ e₁ ⊕ ℓℤ_ℓ e₂` have non-isomorphic raw reductions (non-split and
trivial).

The continuity hypothesis on the residue map is needed. With the indiscrete topologies on `ℤ_3`
and `ℚ_3`, a discontinuous sign character of `∏_ℕ C₂` acts continuously on a stable rank-one
lattice, while its reduction to the discrete field `𝔽_3` is discontinuous.

## Main definitions

* `TauCeti.ContinuousRep.reduction`: the raw reduction `k_A ⊗[A] M` of a continuous
  representation over a topological local ring.

## Main results

* `TauCeti.ContinuousRep.charpoly_reduction_apply`: the characteristic polynomial of `g` on
  the reduction is the reduction of `charpoly (ρ g)`.
* `TauCeti.ContinuousRep.linearMap_det_reduction_apply`: the determinant of `g` on the
  reduction is the residue of `det (ρ g)`.
* `TauCeti.ContinuousRep.reduction_apply_of_forall_apply_eq_smul`: an element acting by a scalar
  acts on the reduction by its residue.
* `TauCeti.ContinuousRep.finite_range_reduction`: over a finite residue field the reduction has
  finite image.

Since `reduction` is the base change to `k_A`, the base-change API of `ContinuousRep` applies to
it directly; for instance `TauCeti.ContinuousRep.baseChangeTrivialIso` shows that the trivial
representation reduces to the trivial representation.

## References

* F. Diamond and J. Im, *Modular forms and modular curves*, 6.12.
* K. Ribet, *Galois representations attached to eigenforms with Nebentypus*, §2.
-/

public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [IsLocalRing A]
  [TopologicalSpace A] [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [TopologicalSpace (ResidueField A)] [IsTopologicalRing (ResidueField A)]
  [ContinuousSMul A (ResidueField A)] [TopologicalSpace (ResidueField A ⊗[A] M)]
  [IsModuleTopology (ResidueField A) (ResidueField A ⊗[A] M)]

/-- **The raw reduction** of a continuous representation `ρ` on a finite module over a
topological local ring `A` with continuous residue map to its residue field `k_A` (typically
discrete): the extension of scalars `k_A ⊗[A] M`, with its `k_A`-module topology. -/
noncomputable abbrev reduction (ρ : ContinuousRep Γ A M) :
    ContinuousRep Γ (ResidueField A) (ResidueField A ⊗[A] M) :=
  ρ.baseChange (ResidueField A)

/-- **The characteristic polynomial of the reduction** at `g` is the reduction modulo `𝔪_A` of
the characteristic polynomial of `ρ g`. -/
theorem charpoly_reduction_apply [Module.Free A M] (ρ : ContinuousRep Γ A M) (g : Γ) :
    (ρ.reduction g).charpoly = (ρ g).charpoly.map (residue A) := by
  rw [charpoly_baseChange_apply, ResidueField.algebraMap_eq]

/-- **The determinant of the reduction** at `g` is the residue of the determinant of `ρ g`. -/
theorem linearMap_det_reduction_apply [Module.Free A M] (ρ : ContinuousRep Γ A M) (g : Γ) :
    LinearMap.det (ρ.reduction g) = residue A (LinearMap.det (ρ g)) := by
  rw [linearMap_det_baseChange_apply, ResidueField.algebraMap_eq]

/-- If `g` acts on `M` by the scalar `c`, it acts on the reduction by the residue of `c`. -/
theorem reduction_apply_of_forall_apply_eq_smul (ρ : ContinuousRep Γ A M) {g : Γ} {c : A}
    (h : ∀ x, ρ g x = c • x) (y : ResidueField A ⊗[A] M) :
    ρ.reduction g y = residue A c • y := by
  rw [← ResidueField.algebraMap_eq]
  exact ρ.baseChange_apply_of_forall_apply_eq_smul _ h y

/-- **Finite image.** Over a finite residue field, the reduction of a continuous representation
takes only finitely many values. -/
theorem finite_range_reduction [Finite (ResidueField A)] (ρ : ContinuousRep Γ A M) :
    (Set.range (ρ.reduction : Γ → Module.End (ResidueField A) (ResidueField A ⊗[A] M))).Finite :=
  have : Finite (ResidueField A ⊗[A] M) := Module.finite_of_finite (ResidueField A)
  finite_range _

end TauCeti.ContinuousRep
