/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale

/-!
# The closed fibre of a standard étale algebra

Let `P` be a standard étale pair over a ring `A`, let `J` be an ideal of `A`, and suppose the
generator of `P.Ring` is congruent to an element `a` of `A` modulo the extended ideal. Then
`P.Ring` has the same closed fibre as `A`, that is, the canonical map
`A ⧸ J → P.Ring ⧸ J P.Ring` is bijective, if and only if the defining equations of `P` hold
modulo `J` at `a` (`StandardEtalePair.algebraMap_quotient_bijective_iff_hasMap`).

## References

* Mathlib's `Mathlib.RingTheory.Etale.StandardEtale`, for `StandardEtalePair` and its
  universal mapping API.
-/

public section

namespace StandardEtalePair

variable {A : Type*} [CommRing A]

/-- If the generator of a standard étale algebra is congruent to an element `a` of the base
modulo the extended ideal of `J`, then the algebra has the same closed fibre as its base along `J`
if and only if its defining equations hold modulo `J` at `a`. -/
theorem algebraMap_quotient_bijective_iff_hasMap (P : StandardEtalePair A) (J : Ideal A) {a : A}
    (hX : P.X - algebraMap A P.Ring a ∈ J.map (algebraMap A P.Ring)) :
    Function.Bijective (algebraMap (A ⧸ J) (P.Ring ⧸ J.map (algebraMap A P.Ring))) ↔
      P.HasMap (Ideal.Quotient.mk J a) := by
  -- The generator and `a` have the same image in the closed fibre of `P.Ring`.
  have hXa : Ideal.Quotient.mk (J.map (algebraMap A P.Ring)) P.X =
      algebraMap (A ⧸ J) _ (Ideal.Quotient.mk J a) :=
    Ideal.Quotient.eq.mpr hX
  refine ⟨fun h ↦ ?_, fun ha ↦ ?_⟩
  · -- The inverse of the canonical map carries the generator of the closed fibre to `a`.
    have hf : Function.Bijective
        (IsScalarTower.toAlgHom A (A ⧸ J) (P.Ring ⧸ J.map (algebraMap A P.Ring))) := by
      rwa [IsScalarTower.coe_toAlgHom']
    have := (P.hasMap_X.map (Ideal.Quotient.mkₐ A _)).map (AlgEquiv.ofBijective _ hf).symm.toAlgHom
    rwa [Ideal.Quotient.mkₐ_eq_mk, hXa, ← IsScalarTower.coe_toAlgHom' A, AlgEquiv.coe_toAlgHom,
      AlgEquiv.ofBijective_symm_apply_apply] at this
  -- The map `X ↦ a` factors through the closed fibre of `P.Ring`, and the factored map is
  -- inverse to the canonical map because the generator is congruent to `a`.
  have hker : J.map (algebraMap A P.Ring) ≤ RingHom.ker (P.lift _ ha) :=
    Ideal.map_le_iff_le_comap.mpr fun j hj ↦ by
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hj
  let σ := Ideal.Quotient.liftₐ _ (P.lift _ ha) fun y hy ↦ RingHom.mem_ker.mp (hker hy)
  have hright : (IsScalarTower.toAlgHom A (A ⧸ J) _).comp σ = AlgHom.id A _ :=
    Ideal.Quotient.algHom_ext _ <| P.hom_ext <| by
      simpa [AlgHom.comp_assoc, σ, Ideal.Quotient.liftₐ_comp] using hXa.symm
  refine Function.bijective_iff_has_inverse.mpr ⟨σ, fun r ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [σ]
  · simpa using DFunLike.congr_fun hright y

end StandardEtalePair
