/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.LinearAlgebra.Quotient.Map
public import TauCeti.Geometry.Symplectic.LinearReduction

/-!
# Linear symplectic reduction in stages

Let `ω` be a linear symplectic form on a real vector space `V`, and let `L ≤ U` be subspaces.
Reducing along `U` gives the symplectic vector space `U_red = U ⧸ (U ∩ U^ω)`
(`TauCeti.SymplecticForm.ReducedSpace ω U`), in which `L` has an image `L'` under the quotient
map, equivalently `L' = (L + U ∩ U^ω) ⧸ (U ∩ U^ω)`. This file shows that reducing `U_red` along
`L'` is the same as reducing `V` along `L` directly:

`(U_red)_red along L' ≃ L ⧸ (L ∩ L^ω)`, `[[l]] ↤ [l]`,

as symplectic vector spaces (`TauCeti.SymplecticForm.reducedSpaceStagesEquiv`,
`TauCeti.SymplecticForm.isSymplectomorphism_reducedSpaceStagesEquiv`). This is the pointwise
linear algebra of symplectic reduction in stages: at a point of the zero level of a moment map of
a Lie algebra `𝔤` with a subalgebra `𝔫`, `U` is the tangent space of the level of the restricted
moment map and `L` that of the level of the full moment map. No finite-dimensionality is needed,
and `L` need not be coisotropic. For an arbitrary subspace `L`, the image of `L` in `U_red` is the
image of `L ∩ U`, so the result applies to `L ∩ U`.

The image `L'` is computed through its symplectic complement in `U_red`: for every subspace `L`,
`L'^ω` is the image of `(L ∩ U)^ω ∩ U`
(`TauCeti.SymplecticForm.reduction_orthogonal_map`). In particular a coisotropic `L ≤ U` has a
coisotropic image (`TauCeti.SymplecticForm.IsCoisotropic.reduction_map_of_le`), so the two-stage
reduction of a coisotropic subspace is again the reduction by a coisotropic subspace.

## Main results

* `TauCeti.SymplecticForm.reduction_orthogonal_map`: the symplectic complement of the image of `L`
  in the reduced space is the image of `(L ∩ U)^ω`.
* `TauCeti.SymplecticForm.IsCoisotropic.reduction_map_of_le`: the image of a coisotropic subspace
  of `U` is coisotropic.
* `TauCeti.SymplecticForm.reducedSpaceStagesEquiv`,
  `TauCeti.SymplecticForm.isSymplectomorphism_reducedSpaceStagesEquiv`: **linear reduction in
  stages**.

## References

* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 5 (reduction by stages at
  the level of tangent spaces).
* Alan Weinstein, *Lectures on Symplectic Manifolds*, CBMS Regional Conference Series in
  Mathematics 29, American Mathematical Society, 1977 (linear symplectic reduction by a
  coisotropic subspace).
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V} {U L : Submodule ℝ V}

/-- The kernel `U ∩ U^ω` of the restriction of `ω` to `U` lies in the preimage in `U` of the
symplectic complement of every subspace of `U`. -/
private theorem ker_restrict_le_comap_orthogonal (L : Submodule ℝ V) :
    LinearMap.ker (ω.toBilinForm.restrict U) ≤ (ω.orthogonal (L ⊓ U)).comap U.subtype := by
  intro u hu
  exact ω.orthogonal_le inf_le_right ((mem_ker_restrict_iff ω U).1 hu)

/-- **The symplectic complement of an image in the reduced space.** The symplectic complement in
`U ⧸ (U ∩ U^ω)` of the image of a subspace `L` is the image of `(L ∩ U)^ω ∩ U`. -/
theorem reduction_orthogonal_map (L : Submodule ℝ V) :
    (ω.reduction U).orthogonal
        ((L.comap U.subtype).map (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ) =
      ((ω.orthogonal (L ⊓ U)).comap U.subtype).map
        (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H u =>
  rw [Submodule.Quotient.mk_mem_map_mkQ_iff (ker_restrict_le_comap_orthogonal L),
    mem_orthogonal_iff, Submodule.mem_comap, Submodule.subtype_apply, mem_orthogonal_iff]
  refine ⟨fun h l hl ↦ ?_, ?_⟩
  · simpa using h _ ⟨⟨l, hl.2⟩, hl.1, rfl⟩
  · rintro h _ ⟨v, hv, rfl⟩
    simpa using h v ⟨hv, v.property⟩

/-- **Coisotropic subspaces stay coisotropic after reduction.** The image in the reduced space
`U ⧸ (U ∩ U^ω)` of a coisotropic subspace `L ≤ U` is coisotropic. -/
theorem IsCoisotropic.reduction_map_of_le (hL : ω.IsCoisotropic L) (hLU : L ≤ U) :
    (ω.reduction U).IsCoisotropic
      ((L.comap U.subtype).map (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ) := by
  rw [isCoisotropic_iff_le, reduction_orthogonal_map, inf_eq_left.2 hLU]
  exact Submodule.map_mono (Submodule.comap_mono (isCoisotropic_iff_le.1 hL))

variable (ω) in
/-- The map `l ↦ [[l]]` from `L` to the reduction along the image of `L` of the reduced space
`U ⧸ (U ∩ U^ω)`, for `L ≤ U`. It is onto, with kernel `L ∩ L^ω`. -/
private noncomputable def toReducedSpaceStages (hLU : L ≤ U) :
    L →ₗ[ℝ] (ω.reduction U).ReducedSpace
      ((L.comap U.subtype).map (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ) :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _
    ((LinearMap.ker (ω.toBilinForm.restrict U)).mkQ ∘ₗ Submodule.inclusion hLU)
    fun l ↦ ⟨Submodule.inclusion hLU l, l.property, rfl⟩

private theorem toReducedSpaceStages_apply (hLU : L ≤ U) (l : L) :
    toReducedSpaceStages ω hLU l =
      Submodule.Quotient.mk ⟨Submodule.Quotient.mk (Submodule.inclusion hLU l),
        ⟨Submodule.inclusion hLU l, l.property, rfl⟩⟩ :=
  (rfl)

private theorem surjective_toReducedSpaceStages (hLU : L ≤ U) :
    Function.Surjective (toReducedSpaceStages ω hLU) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H w =>
  obtain ⟨w, ⟨u, hu, rfl⟩⟩ := w
  exact ⟨⟨u, hu⟩, rfl⟩

private theorem ker_toReducedSpaceStages (hLU : L ≤ U) :
    LinearMap.ker (toReducedSpaceStages ω hLU) = LinearMap.ker (ω.toBilinForm.restrict L) := by
  ext l
  rw [LinearMap.mem_ker, toReducedSpaceStages_apply, Submodule.Quotient.mk_eq_zero,
    mem_ker_restrict_iff, reduction_orthogonal_map,
    Submodule.Quotient.mk_mem_map_mkQ_iff (ker_restrict_le_comap_orthogonal L), inf_eq_left.2 hLU,
    mem_ker_restrict_iff, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion]

variable (ω) in
/-- **Linear symplectic reduction in stages.** For subspaces `L ≤ U`, reducing `V` along `L` is the
same as first reducing along `U` and then reducing the reduced space `U ⧸ (U ∩ U^ω)` along the
image of `L`: the map `[l] ↦ [[l]]` is a linear equivalence, and a symplectomorphism
(`TauCeti.SymplecticForm.isSymplectomorphism_reducedSpaceStagesEquiv`). -/
noncomputable def reducedSpaceStagesEquiv (hLU : L ≤ U) :
    ω.ReducedSpace L ≃ₗ[ℝ] (ω.reduction U).ReducedSpace
      ((L.comap U.subtype).map (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ) :=
  (Submodule.quotEquivOfEq _ _ (ker_toReducedSpaceStages hLU).symm).trans
    ((toReducedSpaceStages ω hLU).quotKerEquivOfSurjective (surjective_toReducedSpaceStages hLU))

/-- The reduction-in-stages equivalence sends `[l]` to `[[l]]`. -/
@[simp]
theorem reducedSpaceStagesEquiv_mk (hLU : L ≤ U) (l : L) :
    ω.reducedSpaceStagesEquiv hLU (Submodule.Quotient.mk l) =
      Submodule.Quotient.mk ⟨Submodule.Quotient.mk (Submodule.inclusion hLU l),
        ⟨Submodule.inclusion hLU l, l.property, rfl⟩⟩ := by
  rw [reducedSpaceStagesEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, toReducedSpaceStages_apply]

/-- **Linear symplectic reduction in stages** is a symplectomorphism: the reduced form of `L`
agrees with the reduced form of the image of `L` in the reduced space of `U`. -/
theorem isSymplectomorphism_reducedSpaceStagesEquiv (hLU : L ≤ U) :
    IsSymplectomorphism (ω.reduction L) ((ω.reduction U).reduction
      ((L.comap U.subtype).map (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ))
      (ω.reducedSpaceStagesEquiv hLU) := by
  rw [isSymplectomorphism_iff]
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H l =>
  induction y using Submodule.Quotient.induction_on with
  | H l' => simp

end TauCeti.SymplecticForm
