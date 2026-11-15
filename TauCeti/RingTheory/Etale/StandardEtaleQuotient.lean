/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale

/-!
# The closed fibre of a standard étale algebra

Let `P` be a standard étale pair over a ring `A` and let `J` be an ideal of `A`. If the defining
equations of `P` hold modulo `J` at an element `a` of `A`, and the generator of `P.Ring` is
congruent to `a` modulo the extended ideal, then `P.Ring` has the same closed fibre as `A`: the
canonical map `A ⧸ J → P.Ring ⧸ J P.Ring` is bijective
(`StandardEtalePair.algebraMap_quotient_bijective_of_hasMap`).

## References

* Mathlib's `Mathlib.RingTheory.Etale.StandardEtale`, for `StandardEtalePair` and its
  universal mapping API.
-/

public section

namespace StandardEtalePair

variable {A : Type*} [CommRing A]

/-- A standard étale algebra has the same closed fibre as its base along an ideal `J`, provided
its defining equations hold modulo `J` at an element `a` of the base and its generator is
congruent to `a` modulo the extended ideal. -/
theorem algebraMap_quotient_bijective_of_hasMap (P : StandardEtalePair A) (J : Ideal A) {a : A}
    (ha : P.HasMap (Ideal.Quotient.mk J a))
    (hX : P.X - algebraMap A P.Ring a ∈ J.map (algebraMap A P.Ring)) :
    Function.Bijective (algebraMap (A ⧸ J) (P.Ring ⧸ J.map (algebraMap A P.Ring))) := by
  -- The map `X ↦ a` is a retraction onto the closed fibre of `A`, and it is inverse to the
  -- canonical map because the generator is congruent to `a`.
  let σ := P.lift _ ha
  have hker : J.map (algebraMap A P.Ring) ≤ RingHom.ker (σ : P.Ring →+* A ⧸ J) :=
    Ideal.map_le_iff_le_comap.mpr fun j hj ↦ by
      simpa [σ] using Ideal.Quotient.eq_zero_iff_mem.mpr hj
  let σbar := Ideal.Quotient.lift _ (σ : P.Ring →+* A ⧸ J) fun y hy ↦
    RingHom.mem_ker.mp (hker hy)
  have hright : (IsScalarTower.toAlgHom A (A ⧸ J) (P.Ring ⧸ J.map (algebraMap A P.Ring))).comp σ =
      Ideal.Quotient.mkₐ A (J.map (algebraMap A P.Ring)) := by
    apply P.hom_ext
    simpa [σ, P.lift_X] using (Ideal.Quotient.eq.mpr hX).symm
  refine Function.bijective_iff_has_inverse.mpr ⟨σbar, fun r ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact σ.commutes r
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simpa [σbar] using DFunLike.congr_fun hright y

end StandardEtalePair
