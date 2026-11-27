/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

/-!
# Matrix stability of the projection monoid and of `K₀`

Let `R` be a star ring and `n` a finite type. For `i : n`, the **corner embedding**
`R → M_n(R)`, `r ↦ r eᵢᵢ` (`Matrix.singleNonUnitalStarRingHom R i`), is a nonunital star ring
homomorphism. It induces isomorphisms `V(R) ≃+ V(M_n(R))`
(`TauCeti.ProjectionMonoid.cornerEquiv`) and `K₀(R) ≃+ K₀(M_n(R))`
(`TauCeti.ProjectionKZero.cornerEquiv`), whatever the corner `i`.

The proof goes through the identification `M_k(M_n(R)) ≅ M_{k × n}(R)` of Mathlib's
`Matrix.comp`, under which two projections over `M_n(R)` are Murray–von Neumann equivalent exactly
when their flattenings over `R` are (`Matrix.isMurrayVonNeumannEquivalent_comp_iff`). The
flattening of the entrywise corner image of a projection `p` over `R` is equivalent to `p`
(`Matrix.isMurrayVonNeumannEquivalent_comp_map_singleNonUnitalStarRingHom`). This gives
injectivity of the induced map on `V`, and surjectivity because every projection `P` over
`M_n(R)` is then equivalent to the corner image of its flattening, which also describes the inverse
(`TauCeti.ProjectionMonoid.cornerEquiv_symm_mk`).

## Main declarations

* `TauCeti.ProjectionMonoid.cornerEquiv`: `V(R) ≃+ V(M_n(R))`.
* `TauCeti.ProjectionKZero.cornerEquiv`: `K₀(R) ≃+ K₀(M_n(R))`.

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Section 6.4 (stability of `K₀`).
-/

public section

open Matrix Algebra

namespace TauCeti

variable {R : Type*} [NonUnitalSemiring R] [StarRing R] {n : Type*} [Fintype n] [DecidableEq n]

namespace ProjectionMonoid

/-- Every class in `V(M_n(R))` is the image of the class of its flattening. -/
private theorem mk_eq_map_singleNonUnitalStarRingHom {k : Type*} [Fintype k]
    {P : Matrix k k (Matrix n n R)} (hP : IsStarProjection P) (i : n) :
    mk P hP = map (singleNonUnitalStarRingHom R i)
      (mk (comp k k n n R P) (isStarProjection_comp_iff.2 hP)) := by
  rw [map_mk]
  refine mk_eq_mk (isMurrayVonNeumannEquivalent_comp_iff.1 ?_)
  exact isMurrayVonNeumannEquivalent_comp_map_singleNonUnitalStarRingHom
    (isStarProjection_comp_iff.2 hP) i

/-- The corner embedding induces a bijection `V(R) → V(M_n(R))`. -/
theorem map_singleNonUnitalStarRingHom_bijective (i : n) :
    Function.Bijective (map (singleNonUnitalStarRingHom R i)) := by
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · induction x using ind with | mk _ p hp => ?_
    induction y using ind with | mk _ q hq => ?_
    rw [map_mk, map_mk, mk_eq_mk_iff] at hxy
    refine mk_eq_mk ?_
    have h := isMurrayVonNeumannEquivalent_comp_iff.2 hxy
    exact ((isMurrayVonNeumannEquivalent_comp_map_singleNonUnitalStarRingHom hp i).trans h).trans
      (isMurrayVonNeumannEquivalent_comp_map_singleNonUnitalStarRingHom hq i).symm
  · induction z using ind with | mk _ P hP => ?_
    exact ⟨_, (mk_eq_map_singleNonUnitalStarRingHom hP i).symm⟩

/-- **Matrix stability of `V`.** The corner embedding `r ↦ r eᵢᵢ` induces `V(R) ≃+ V(M_n(R))`. -/
noncomputable def cornerEquiv (i : n) : ProjectionMonoid R ≃+ ProjectionMonoid (Matrix n n R) :=
  AddEquiv.ofBijective (map (singleNonUnitalStarRingHom R i))
    (map_singleNonUnitalStarRingHom_bijective i)

@[simp]
theorem cornerEquiv_apply (i : n) (x : ProjectionMonoid R) :
    cornerEquiv i x = map (singleNonUnitalStarRingHom R i) x :=
  (rfl)

/-- The inverse of the stability isomorphism sends the class of a projection over `M_n(R)` to the
class of its flattening. -/
@[simp]
theorem cornerEquiv_symm_mk (i : n) {k : Type*} [Fintype k] {P : Matrix k k (Matrix n n R)}
    (hP : IsStarProjection P) :
    (cornerEquiv i).symm (mk P hP) = mk (comp k k n n R P) (isStarProjection_comp_iff.2 hP) := by
  rw [AddEquiv.symm_apply_eq, cornerEquiv_apply, ← mk_eq_map_singleNonUnitalStarRingHom]

end ProjectionMonoid

namespace ProjectionKZero

/-- **Matrix stability of `K₀`.** The corner embedding `r ↦ r eᵢᵢ` induces
`K₀(R) ≃+ K₀(M_n(R))`. -/
noncomputable def cornerEquiv (i : n) : ProjectionKZero R ≃+ ProjectionKZero (Matrix n n R) :=
  GrothendieckAddGroup.congr (ProjectionMonoid.cornerEquiv i)

/-- The stability isomorphism `K₀(R) ≃+ K₀(M_n(R))` is induced by the corner embedding. -/
@[simp]
theorem cornerEquiv_apply (i : n) (x : ProjectionKZero R) :
    cornerEquiv i x = map (singleNonUnitalStarRingHom R i) x :=
  DFunLike.congr_fun (GrothendieckAddGroup.addHom_ext (F₁ := (cornerEquiv i).toAddMonoidHom)
    fun y ↦ by rw [AddEquiv.coe_toAddMonoidHom, cornerEquiv, GrothendieckAddGroup.congr_of,
      map_of, ProjectionMonoid.cornerEquiv_apply]) x

-- Not `@[simp]`: the simp normal form of `Algebra.GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `TauCeti.ProjectionKZero.map_of`.
/-- On the image of `V(M_n(R))`, the inverse of the stability isomorphism on `K₀` is that on `V`,
which sends the class of a projection to the class of its flattening
(`TauCeti.ProjectionMonoid.cornerEquiv_symm_mk`). -/
theorem cornerEquiv_symm_of (i : n) (x : ProjectionMonoid (Matrix n n R)) :
    (cornerEquiv i).symm (GrothendieckAddGroup.of x) =
      GrothendieckAddGroup.of ((ProjectionMonoid.cornerEquiv i).symm x) := by
  rw [AddEquiv.symm_apply_eq, cornerEquiv, GrothendieckAddGroup.congr_of,
    AddEquiv.apply_symm_apply]

end ProjectionKZero

end TauCeti
