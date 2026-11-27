/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Composition
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero
import Mathlib.Data.Matrix.Basis

/-!
# Matrix stability of the projection monoid and of `K₀`

Let `R` be a unital star ring and `n` a finite type. For `i : n`, the **corner embedding**
`R → M_n(R)`, `r ↦ r eᵢᵢ` (`TauCeti.cornerStarRingHom R i`), is a nonunital star ring
homomorphism. It induces isomorphisms `V(R) ≃+ V(M_n(R))`
(`TauCeti.ProjectionMonoid.cornerEquiv`) and `K₀(R) ≃+ K₀(M_n(R))`
(`TauCeti.ProjectionKZero.cornerEquiv`), whatever the corner `i`.

The proof goes through the identification `M_k(M_n(R)) ≅ M_{k × n}(R)` of Mathlib's
`Matrix.comp`, which is multiplicative and commutes with conjugate transposes also for
rectangular matrices (`Matrix.comp_mul_comp`, `Matrix.comp_conjTranspose`). Hence two
projections over `M_n(R)` are Murray–von Neumann equivalent exactly when their flattenings over
`R` are (`Matrix.isMurrayVonNeumannEquivalent_comp_iff`). The flattening of the entrywise corner
image of a projection `p` over `R` is `p` placed on the rows and columns `(a, i)`, which is
equivalent to `p` (`Matrix.isMurrayVonNeumannEquivalent_comp_map_cornerStarRingHom`). This gives
injectivity of the induced map on `V`, and surjectivity because every projection `P` over
`M_n(R)` is then equivalent to the corner image of its flattening.

## Main declarations

* `TauCeti.cornerStarRingHom R i`: the corner embedding `r ↦ r eᵢᵢ`.
* `TauCeti.ProjectionMonoid.cornerEquiv`: `V(R) ≃+ V(M_n(R))`.
* `TauCeti.ProjectionKZero.cornerEquiv`: `K₀(R) ≃+ K₀(M_n(R))`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definitions 5.1.1 and 5.1.2.
-/

public section

open Matrix Algebra

namespace Matrix

variable {R : Type*} {I J K L M : Type*} [Fintype J] [Fintype L]

/-- Flattening `M_{I×J}(M_L(R)) → M_{(I×L)×(J×L)}(R)` is multiplicative, also for rectangular
outer matrices. -/
theorem comp_mul_comp [NonUnitalNonAssocSemiring R] (A : Matrix I J (Matrix L L R))
    (B : Matrix J M (Matrix L L R)) :
    comp I M L L R (A * B) = comp I J L L R A * comp J M L L R B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [comp_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

omit [Fintype J] [Fintype L] in
/-- Flattening commutes with conjugate transposes. -/
theorem comp_conjTranspose [Star R] (A : Matrix I J (Matrix L L R)) :
    comp J I L L R Aᴴ = (comp I J L L R A)ᴴ := by
  ext ⟨j, l⟩ ⟨i, k⟩
  simp [comp_apply, conjTranspose_apply]

omit [Fintype J] in
/-- Flattening preserves and reflects star projections. -/
theorem isStarProjection_comp_iff [Fintype I] [NonUnitalSemiring R] [StarRing R]
    {p : Matrix I I (Matrix L L R)} : IsStarProjection (comp I I L L R p) ↔ IsStarProjection p := by
  simp only [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, star_eq_conjTranspose,
    ← comp_mul_comp, ← comp_conjTranspose, (comp I I L L R).injective.eq_iff]

omit [Fintype J] in
/-- **Flattening and Murray–von Neumann equivalence.** Projections over `M_n(R)` are equivalent
exactly when their flattenings over `R` are. -/
theorem isMurrayVonNeumannEquivalent_comp_iff [Fintype I] [Fintype K] [NonUnitalSemiring R]
    [StarRing R] {p : Matrix I I (Matrix L L R)} {q : Matrix K K (Matrix L L R)} :
    IsMurrayVonNeumannEquivalent (comp I I L L R p) (comp K K L L R q) ↔
      IsMurrayVonNeumannEquivalent p q := by
  constructor
  · rintro ⟨hp, hq, v, hvp, hvq⟩
    refine ⟨isStarProjection_comp_iff.1 hp, isStarProjection_comp_iff.1 hq,
      (comp K I L L R).symm v, ?_, ?_⟩
    · rw [← (comp I I L L R).injective.eq_iff, comp_mul_comp, comp_conjTranspose,
        Equiv.apply_symm_apply, hvp]
    · rw [← (comp K K L L R).injective.eq_iff, comp_mul_comp, comp_conjTranspose,
        Equiv.apply_symm_apply, hvq]
  · rintro ⟨hp, hq, v, hvp, hvq⟩
    refine ⟨isStarProjection_comp_iff.2 hp, isStarProjection_comp_iff.2 hq,
      comp K I L L R v, ?_, ?_⟩
    · rw [← comp_conjTranspose, ← comp_mul_comp, hvp]
    · rw [← comp_conjTranspose, ← comp_mul_comp, hvq]

end Matrix

namespace TauCeti

variable (R : Type*) [Semiring R] [StarRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **corner embedding** `R → M_n(R)`, `r ↦ r eᵢᵢ`, as a nonunital star ring homomorphism. -/
def cornerStarRingHom (i : n) : R →⋆ₙ+* Matrix n n R where
  toFun r := single i i r
  map_zero' := by simp
  map_add' r s := single_add i i r s
  map_mul' r s := (single_mul_single_same r i i i s).symm
  map_star' r := by rw [star_eq_conjTranspose, conjTranspose_single]

variable {R}

@[simp]
theorem cornerStarRingHom_apply (i : n) (r : R) : cornerStarRingHom R i r = single i i r :=
  (rfl)

end TauCeti

namespace Matrix

open TauCeti

variable {R : Type*} [Semiring R] [StarRing R] {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq n]

/-- The flattening of the entrywise corner image of a projection `p` over `R` is equivalent to
`p`: it is `p` placed on the rows and columns `(a, i)`. -/
theorem isMurrayVonNeumannEquivalent_comp_map_cornerStarRingHom {p : Matrix m m R}
    (hp : IsStarProjection p) (i : n) :
    IsMurrayVonNeumannEquivalent p (comp m m n n R (p.map (cornerStarRingHom R i))) := by
  classical
  let w : Matrix (m × n) m R := of fun b a ↦ if b = (a, i) then 1 else 0
  have hw : wᴴ * w = 1 := by
    ext a a'
    simp [w, Matrix.mul_apply, Matrix.one_apply, conjTranspose_apply, apply_ite (star : R → R),
      eq_comm]
  have hwp : w * p * wᴴ = comp m m n n R (p.map (cornerStarRingHom R i)) := by
    ext ⟨b, y⟩ ⟨b', y'⟩
    by_cases hy : y = i
    · subst hy
      by_cases hy' : y' = y
      · subst hy'
        simp [w, Matrix.mul_apply, comp_apply, conjTranspose_apply, apply_ite (star : R → R)]
      · simp [w, Matrix.mul_apply, comp_apply, conjTranspose_apply, hy', Ne.symm hy']
    · simp [w, Matrix.mul_apply, comp_apply, conjTranspose_apply, hy, Ne.symm hy]
  rw [← hwp]
  exact hp.isMurrayVonNeumannEquivalent_mul_mul_conjTranspose (by rw [hw, Matrix.one_mul])

end Matrix

namespace TauCeti

variable {R : Type*} [Semiring R] [StarRing R] {n : Type*} [Fintype n] [DecidableEq n]

namespace ProjectionMonoid

/-- Every class in `V(M_n(R))` is the image of the class of its flattening. -/
private theorem mk_eq_map_cornerStarRingHom {k : Type*} [Fintype k]
    {P : Matrix k k (Matrix n n R)} (hP : IsStarProjection P) (i : n) :
    mk P hP = map (cornerStarRingHom R i)
      (mk (comp k k n n R P) (isStarProjection_comp_iff.2 hP)) := by
  rw [map_mk]
  refine mk_eq_mk (isMurrayVonNeumannEquivalent_comp_iff.1 ?_)
  exact isMurrayVonNeumannEquivalent_comp_map_cornerStarRingHom
    (isStarProjection_comp_iff.2 hP) i

/-- The corner embedding induces a bijection `V(R) → V(M_n(R))`. -/
theorem bijective_map_cornerStarRingHom (i : n) :
    Function.Bijective (map (cornerStarRingHom R i)) := by
  classical
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · induction x using ind with | mk _ p hp => ?_
    induction y using ind with | mk _ q hq => ?_
    rw [map_mk, map_mk, mk_eq_mk_iff] at hxy
    refine mk_eq_mk ?_
    have h := isMurrayVonNeumannEquivalent_comp_iff.2 hxy
    exact ((isMurrayVonNeumannEquivalent_comp_map_cornerStarRingHom hp i).trans h).trans
      (isMurrayVonNeumannEquivalent_comp_map_cornerStarRingHom hq i).symm
  · induction z using ind with | mk _ P hP => ?_
    exact ⟨_, (mk_eq_map_cornerStarRingHom hP i).symm⟩

/-- **Matrix stability of `V`.** The corner embedding `r ↦ r eᵢᵢ` induces `V(R) ≃+ V(M_n(R))`. -/
noncomputable def cornerEquiv (i : n) : ProjectionMonoid R ≃+ ProjectionMonoid (Matrix n n R) :=
  AddEquiv.ofBijective (map (cornerStarRingHom R i)) (bijective_map_cornerStarRingHom i)

@[simp]
theorem cornerEquiv_apply (i : n) (x : ProjectionMonoid R) :
    cornerEquiv i x = map (cornerStarRingHom R i) x :=
  (rfl)

end ProjectionMonoid

namespace ProjectionKZero

/-- **Matrix stability of `K₀`.** The corner embedding `r ↦ r eᵢᵢ` induces
`K₀(R) ≃+ K₀(M_n(R))`. -/
noncomputable def cornerEquiv (i : n) : ProjectionKZero R ≃+ ProjectionKZero (Matrix n n R) :=
  AddMonoidHom.toAddEquiv (map (cornerStarRingHom R i))
    (GrothendieckAddGroup.lift ((GrothendieckAddGroup.of : ProjectionMonoid R →+ _).comp
      (ProjectionMonoid.cornerEquiv (R := R) i).symm.toAddMonoidHom))
    (GrothendieckAddGroup.addHom_ext fun x ↦ by
      rw [AddMonoidHom.comp_apply, map_of, GrothendieckAddGroup.lift_apply_of,
        AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, ← ProjectionMonoid.cornerEquiv_apply,
        AddEquiv.symm_apply_apply, AddMonoidHom.id_apply])
    (GrothendieckAddGroup.addHom_ext fun x ↦ by
      rw [AddMonoidHom.comp_apply, GrothendieckAddGroup.lift_apply_of, AddMonoidHom.comp_apply,
        map_of, AddEquiv.coe_toAddMonoidHom, ← ProjectionMonoid.cornerEquiv_apply,
        AddEquiv.apply_symm_apply, AddMonoidHom.id_apply])

/-- The stability isomorphism `K₀(R) ≃+ K₀(M_n(R))` is induced by the corner embedding. -/
@[simp]
theorem cornerEquiv_apply (i : n) (x : ProjectionKZero R) :
    cornerEquiv i x = map (cornerStarRingHom R i) x :=
  (rfl)

end ProjectionKZero

end TauCeti
