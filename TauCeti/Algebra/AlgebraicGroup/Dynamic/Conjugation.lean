/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.ClosedImmersion.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Conjugate cocharacters and the Levi subgroups of a dynamic parabolic

Let `λ : 𝔾ₘ → G` be a cocharacter of an affine group `G = Spec H`, with dynamic parabolic
`P(λ)`, dynamic unipotent subgroup `U(λ)` and dynamic Levi subgroup `Z(λ)`. A rational point
`g` of `G` conjugates `λ` to the cocharacter `gλg⁻¹ : t ↦ g λ(t) g⁻¹`
(`BialgHom.conjCocharacter`), and the dynamic subgroups of `gλg⁻¹` are the `g`-conjugates of
those of `λ`, on points over every value algebra and as closed subgroup schemes.

If `p` is a rational point of `P(λ)`, conjugation by `p` preserves `P(λ)` and `U(λ)`. Hence
`P(pλp⁻¹) = P(λ)` and `U(pλp⁻¹) = U(λ)`, and `Z(pλp⁻¹) = pZ(λ)p⁻¹` is another Levi factor of
the same parabolic, complementary to the same unipotent subgroup. The main theorem says that the
normalizer of `Z(λ)` in `P(λ)` is `Z(λ)` itself: a rational point of `P(λ)` conjugating `Z(λ)`
to itself lies in `Z(λ)`. Consequently `U(λ)` acts freely by conjugation on the Levi factors
`Z(uλu⁻¹)`: distinct rational points of `U(λ)` give distinct Levi subgroups.

The pointwise heart of the argument is the following. Write `p = uz` with `u ∈ U(λ)` and
`z ∈ Z(λ)`. If `p` conjugates the generic point `λ(T)` into `Z(λ)`, so does `u`, and then the
commutator `u λ(T) u⁻¹ λ(T)⁻¹` lies both in `Z(λ)` and, since `λ(T)` normalizes `U(λ)`, in
`U(λ)`. These meet trivially, so `u` commutes with `λ(T)`, that is `u ∈ Z(λ) ∩ U(λ) = 1`.

No field, smoothness, connectedness or reductivity hypothesis is needed. The statements about
points hold over every commutative value semiring; those about closed subgroup schemes hold
over a commutative base ring.

## Main declarations

* `BialgHom.conjCocharacter`: the conjugate of a cocharacter by a rational point.
* `BialgHom.conj_mem_parabolic_conjCocharacter_iff`,
  `BialgHom.conj_mem_levi_conjCocharacter_iff` and
  `BialgHom.conj_mem_unipotent_conjCocharacter_iff`: the dynamic subgroups of a conjugate
  cocharacter are the conjugate subgroups, with `BialgHom.mem_parabolic_conjCocharacter_iff`,
  `BialgHom.mem_levi_conjCocharacter_iff` and `BialgHom.mem_unipotent_conjCocharacter_iff`
  testing membership by conjugating back.
* `BialgHom.parabolicDefiningHopfIdeal_conjCocharacter`,
  `BialgHom.leviDefiningHopfIdeal_conjCocharacter` and
  `BialgHom.unipotentDefiningHopfIdeal_conjCocharacter`: the same for the closed subgroup
  schemes.
* `BialgHom.parabolicDefiningHopfIdeal_conjCocharacter_of_mem_parabolic` and
  `BialgHom.unipotentDefiningHopfIdeal_conjCocharacter_of_mem_parabolic`: conjugating by a
  rational point of `P(λ)` does not change `P(λ)` or `U(λ)`.
* `BialgHom.conjugate_leviDefiningHopfIdeal_eq_self_iff` and
  `BialgHom.stabilizer_leviDefiningHopfIdeal_inf_parabolic`: the normalizer of `Z(λ)` in
  `P(λ)` is `Z(λ)`, on rational points.
* `BialgHom.injOn_conjugate_leviDefiningHopfIdeal`: rational points of `U(λ)` act freely by
  conjugation on the Levi factors of `P(λ)` conjugate to `Z(λ)`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open WithConv TauCeti TauCeti.Cocharacter

namespace BialgHom

/-! ### Conjugate cocharacters -/

section Points

variable {R H A : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
variable [CommSemiring A] [Algebra R A]

/-- The **conjugate** `t ↦ g λ(t) g⁻¹` of a cocharacter `λ` by a rational point `g`. On
coordinate rings it is `λ` precomposed with the coordinate automorphism of `x ↦ g x g⁻¹`. -/
noncomputable def conjCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) : H →ₐc[R] LaurentPolynomial R :=
  l.comp (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom

/-- On coordinates, the conjugate cocharacter precomposes with point conjugation. -/
@[simp]
theorem conjCocharacter_apply (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] R))
    (h : H) : l.conjCocharacter g h = l (HopfAlgebra.pointConjugationAlgHom g h) := by
  rw [conjCocharacter, comp_apply]
  exact congrArg l (DFunLike.congr_fun (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g) h)

/-- Conjugating by the identity point does not change a cocharacter. -/
@[simp]
theorem conjCocharacter_one (l : H →ₐc[R] LaurentPolynomial R) : l.conjCocharacter 1 = l := by
  ext h : 1
  rw [conjCocharacter_apply, HopfAlgebra.pointConjugationAlgHom_one, AlgHom.id_apply]

/-- Conjugating by `g` and then by `g'` is conjugating by `g' * g`. -/
@[simp]
theorem conjCocharacter_conjCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g g' : WithConv (H →ₐ[R] R)) :
    (l.conjCocharacter g).conjCocharacter g' = l.conjCocharacter (g' * g) := by
  ext h : 1
  rw [conjCocharacter_apply, conjCocharacter_apply, conjCocharacter_apply,
    HopfAlgebra.pointConjugationAlgHom_mul, AlgHom.comp_apply]

/-- The conjugate cocharacter sends a unit `t` to `g λ(t) g⁻¹`. -/
theorem pointsHom_conjCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) (t : Aˣ) :
    pointsHom A (l.conjCocharacter g) t =
      AlgHom.mapValue (H := H) (Algebra.ofId R A) g * pointsHom A l t *
        (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ := by
  rw [pointsHom_apply, pointsHom_apply, conjCocharacter, mapDomain_comp, MonoidHom.comp_apply,
    HopfAlgebra.mapDomain_pointConjugationBialgEquiv]

/-- The generic point of the conjugate cocharacter is `g λ(T) g⁻¹`. -/
theorem genericPoint_conjCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) :
    genericPoint A (l.conjCocharacter g) =
      AlgHom.mapValue (H := H) (Algebra.ofId R (LaurentPolynomial A)) g * genericPoint A l *
        (AlgHom.mapValue (H := H) (Algebra.ofId R (LaurentPolynomial A)) g)⁻¹ := by
  rw [genericPoint_eq_pointsHom, genericPoint_eq_pointsHom, pointsHom_conjCocharacter]

/-- **The dynamic parabolic of a conjugate cocharacter** is the conjugate parabolic:
`P(gλg⁻¹) = gP(λ)g⁻¹`. -/
theorem conj_mem_parabolic_conjCocharacter_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue (H := H) (Algebra.ofId R A) g * x *
          (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ ∈
        parabolic A (l.conjCocharacter g) ↔ x ∈ parabolic A l := by
  rw [← HopfAlgebra.mapDomain_pointConjugationBialgEquiv, conjCocharacter]
  exact (mem_parabolic_iff_of_surjective _
    (HopfAlgebra.pointConjugationBialgEquiv_surjective g) l x).symm

/-- **The dynamic Levi of a conjugate cocharacter** is the conjugate Levi:
`Z(gλg⁻¹) = gZ(λ)g⁻¹`. -/
theorem conj_mem_levi_conjCocharacter_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue (H := H) (Algebra.ofId R A) g * x *
          (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ ∈
        levi A (l.conjCocharacter g) ↔ x ∈ levi A l := by
  rw [← HopfAlgebra.mapDomain_pointConjugationBialgEquiv, conjCocharacter]
  exact (mem_levi_iff_of_surjective _
    (HopfAlgebra.pointConjugationBialgEquiv_surjective g) l x).symm

/-- **The dynamic unipotent subgroup of a conjugate cocharacter** is the conjugate subgroup:
`U(gλg⁻¹) = gU(λ)g⁻¹`. -/
theorem conj_mem_unipotent_conjCocharacter_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue (H := H) (Algebra.ofId R A) g * x *
          (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ ∈
        unipotent A (l.conjCocharacter g) ↔ x ∈ unipotent A l := by
  rw [← HopfAlgebra.mapDomain_pointConjugationBialgEquiv, conjCocharacter]
  exact (mem_unipotent_iff_of_surjective _
    (HopfAlgebra.pointConjugationBialgEquiv_surjective g) l x).symm

/-- A point lies in `P(gλg⁻¹)` exactly when its conjugate by `g⁻¹` lies in `P(λ)`. -/
theorem mem_parabolic_conjCocharacter_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    x ∈ parabolic A (l.conjCocharacter g) ↔
      (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ * x *
        AlgHom.mapValue (H := H) (Algebra.ofId R A) g ∈ parabolic A l := by
  rw [← conj_mem_parabolic_conjCocharacter_iff l g, mul_assoc, mul_inv_cancel_right,
    mul_inv_cancel_left]

/-- A point lies in `Z(gλg⁻¹)` exactly when its conjugate by `g⁻¹` lies in `Z(λ)`. -/
theorem mem_levi_conjCocharacter_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    x ∈ levi A (l.conjCocharacter g) ↔
      (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ * x *
        AlgHom.mapValue (H := H) (Algebra.ofId R A) g ∈ levi A l := by
  rw [← conj_mem_levi_conjCocharacter_iff l g, mul_assoc, mul_inv_cancel_right,
    mul_inv_cancel_left]

/-- A point lies in `U(gλg⁻¹)` exactly when its conjugate by `g⁻¹` lies in `U(λ)`. -/
theorem mem_unipotent_conjCocharacter_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    x ∈ unipotent A (l.conjCocharacter g) ↔
      (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ * x *
        AlgHom.mapValue (H := H) (Algebra.ofId R A) g ∈ unipotent A l := by
  rw [← conj_mem_unipotent_conjCocharacter_iff l g, mul_assoc, mul_inv_cancel_right,
    mul_inv_cancel_left]

/-- Conjugating by a point of the dynamic parabolic does not change it: `P(pλp⁻¹) = P(λ)` for a
rational point `p` of `P(λ)`. -/
@[simp]
theorem parabolic_conjCocharacter_of_mem_parabolic (l : H →ₐc[R] LaurentPolynomial R)
    {p : WithConv (H →ₐ[R] R)} (hp : p ∈ parabolic R l) :
    parabolic A (l.conjCocharacter p) = parabolic A l := by
  set q := AlgHom.mapValue (H := H) (Algebra.ofId R A) p
  have hq : q ∈ parabolic A l := parabolic_le_comap (Algebra.ofId R A) hp
  ext x
  rw [mem_parabolic_conjCocharacter_iff, Subgroup.mul_mem_cancel_right _ hq,
    Subgroup.mul_mem_cancel_left _ (inv_mem hq)]

/-- Conjugating by a point of the dynamic parabolic does not change the dynamic unipotent
subgroup: `U(pλp⁻¹) = U(λ)` for a rational point `p` of `P(λ)`. -/
@[simp]
theorem unipotent_conjCocharacter_of_mem_parabolic (l : H →ₐc[R] LaurentPolynomial R)
    {p : WithConv (H →ₐ[R] R)} (hp : p ∈ parabolic R l) :
    unipotent A (l.conjCocharacter p) = unipotent A l := by
  set q := AlgHom.mapValue (H := H) (Algebra.ofId R A) p
  have hq : q ∈ parabolic A l := parabolic_le_comap (Algebra.ofId R A) hp
  ext x
  -- `q` also lies in `P(pλp⁻¹) = P(λ)`, so it normalizes `U(pλp⁻¹)` as well.
  have hq' : q ∈ parabolic A (l.conjCocharacter p) := by
    rwa [parabolic_conjCocharacter_of_mem_parabolic l hp]
  refine ⟨fun h => (conj_mem_unipotent_conjCocharacter_iff l p x).mp (conj_mem_unipotent hq' h),
    fun h => (mem_unipotent_conjCocharacter_iff l p x).mpr ?_⟩
  simpa only [inv_inv] using conj_mem_unipotent (inv_mem hq) h

end Points

/-! ### The closed subgroup schemes -/

section HopfIdeal

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- The defining Hopf ideal of `P(gλg⁻¹)` is the `g`-conjugate of that of `P(λ)`. -/
theorem parabolicDefiningHopfIdeal_conjCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) :
    parabolicDefiningHopfIdeal (l.conjCocharacter g) = (parabolicDefiningHopfIdeal l).conjugate g :=
  HopfIdeal.eq_conjugate_of_forall_mem_iff g <| by
    rintro ⟨A⟩ x
    rw [quotientPointsSubgroup_parabolicDefiningHopfIdeal,
      quotientPointsSubgroup_parabolicDefiningHopfIdeal]
    exact conj_mem_parabolic_conjCocharacter_iff l g x

/-- The defining Hopf ideal of `Z(gλg⁻¹)` is the `g`-conjugate of that of `Z(λ)`. -/
theorem leviDefiningHopfIdeal_conjCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) :
    leviDefiningHopfIdeal (l.conjCocharacter g) = (leviDefiningHopfIdeal l).conjugate g :=
  HopfIdeal.eq_conjugate_of_forall_mem_iff g fun A x => by
    rw [quotientPointsSubgroup_leviDefiningHopfIdeal, quotientPointsSubgroup_leviDefiningHopfIdeal]
    exact conj_mem_levi_conjCocharacter_iff l g x

/-- The defining Hopf ideal of `U(gλg⁻¹)` is the `g`-conjugate of that of `U(λ)`. -/
theorem unipotentDefiningHopfIdeal_conjCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] R)) :
    (l.conjCocharacter g).unipotentDefiningHopfIdeal = l.unipotentDefiningHopfIdeal.conjugate g :=
  HopfIdeal.eq_conjugate_of_forall_mem_iff g <| by
    rintro ⟨A⟩ x
    rw [quotientPointsSubgroup_unipotentDefiningHopfIdeal,
      quotientPointsSubgroup_unipotentDefiningHopfIdeal]
    exact conj_mem_unipotent_conjCocharacter_iff l g x

/-- For a rational point `p` of `P(λ)`, the closed subgroup schemes `P(pλp⁻¹)` and `P(λ)`
coincide. -/
@[simp]
theorem parabolicDefiningHopfIdeal_conjCocharacter_of_mem_parabolic
    (l : H →ₐc[R] LaurentPolynomial R) {p : WithConv (H →ₐ[R] R)} (hp : p ∈ parabolic R l) :
    parabolicDefiningHopfIdeal (l.conjCocharacter p) = parabolicDefiningHopfIdeal l := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq (H := _root_.CommHopfAlgCat.of R H)
  rintro ⟨A⟩
  rw [quotientPointsSubgroup_parabolicDefiningHopfIdeal,
    quotientPointsSubgroup_parabolicDefiningHopfIdeal,
    parabolic_conjCocharacter_of_mem_parabolic l hp]

/-- For a rational point `p` of `P(λ)`, the closed subgroup schemes `U(pλp⁻¹)` and `U(λ)`
coincide. -/
@[simp]
theorem unipotentDefiningHopfIdeal_conjCocharacter_of_mem_parabolic
    (l : H →ₐc[R] LaurentPolynomial R) {p : WithConv (H →ₐ[R] R)} (hp : p ∈ parabolic R l) :
    (l.conjCocharacter p).unipotentDefiningHopfIdeal = l.unipotentDefiningHopfIdeal := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq (H := _root_.CommHopfAlgCat.of R H)
  rintro ⟨A⟩
  rw [quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    unipotent_conjCocharacter_of_mem_parabolic l hp]

/-- A rational point of `P(λ)` normalizes `P(λ)`. -/
theorem conjugate_parabolicDefiningHopfIdeal_eq_self_of_mem_parabolic
    (l : H →ₐc[R] LaurentPolynomial R) {p : WithConv (H →ₐ[R] R)} (hp : p ∈ parabolic R l) :
    (parabolicDefiningHopfIdeal l).conjugate p = parabolicDefiningHopfIdeal l := by
  rw [← parabolicDefiningHopfIdeal_conjCocharacter,
    parabolicDefiningHopfIdeal_conjCocharacter_of_mem_parabolic l hp]

/-- A rational point of `P(λ)` normalizes `U(λ)`. -/
theorem conjugate_unipotentDefiningHopfIdeal_eq_self_of_mem_parabolic
    (l : H →ₐc[R] LaurentPolynomial R) {p : WithConv (H →ₐ[R] R)} (hp : p ∈ parabolic R l) :
    l.unipotentDefiningHopfIdeal.conjugate p = l.unipotentDefiningHopfIdeal := by
  rw [← unipotentDefiningHopfIdeal_conjCocharacter,
    unipotentDefiningHopfIdeal_conjCocharacter_of_mem_parabolic l hp]

/-- **The normalizer of the dynamic Levi in the dynamic parabolic is the Levi.** A rational
point `p` of `P(λ)` conjugates the closed subgroup `Z(λ)` to itself exactly when `p` lies in
`Z(λ)`. -/
theorem conjugate_leviDefiningHopfIdeal_eq_self_iff (l : H →ₐc[R] LaurentPolynomial R)
    {p : WithConv (H →ₐ[R] R)} (hp : p ∈ parabolic R l) :
    (leviDefiningHopfIdeal l).conjugate p = leviDefiningHopfIdeal l ↔ p ∈ levi R l := by
  constructor
  · intro h
    -- Test the conjugate of the generic point `λ(T)`, a point of `Z(λ)` over `R[T;T⁻¹]`.
    have hmem := (CommHopfAlgCat.pointConjugation_mem_conjugate_iff (leviDefiningHopfIdeal l) p
      (CommAlgCat.of R (LaurentPolynomial R)) (genericPoint R l)).mpr (by
        rw [quotientPointsSubgroup_leviDefiningHopfIdeal]
        exact genericPoint_mem_levi l)
    rw [h, quotientPointsSubgroup_leviDefiningHopfIdeal] at hmem
    rw [← constPoint_mapValue_ofId, Algebra.ofId_self, AlgHom.mapValue_id,
      MonoidHom.id_apply] at hmem
    exact (conj_genericPoint_mem_levi_iff l hp).mp hmem
  · intro hz
    refine (HopfIdeal.eq_conjugate_of_forall_mem_iff p fun A x => ?_).symm
    have hq : AlgHom.mapValue (H := H) (Algebra.ofId R A) p ∈ levi A l :=
      levi_le_comap (Algebra.ofId R A) hz
    rw [quotientPointsSubgroup_leviDefiningHopfIdeal,
      Subgroup.mul_mem_cancel_right _ (inv_mem hq), Subgroup.mul_mem_cancel_left _ hq]

/-- **The normalizer of the dynamic Levi in the dynamic parabolic**, as a stabilizer: the
rational points of `P(λ)` whose conjugation action fixes `Z(λ)` are the rational points of
`Z(λ)`. -/
theorem stabilizer_leviDefiningHopfIdeal_inf_parabolic (l : H →ₐc[R] LaurentPolynomial R) :
    MulAction.stabilizer (WithConv (H →ₐ[R] R)) (leviDefiningHopfIdeal l) ⊓ parabolic R l =
      levi R l := by
  ext p
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, HopfIdeal.smul_eq_conjugate]
  exact ⟨fun h => (conjugate_leviDefiningHopfIdeal_eq_self_iff l h.2).mp h.1,
    fun h => ⟨(conjugate_leviDefiningHopfIdeal_eq_self_iff l (levi_le_parabolic h)).mpr h,
      levi_le_parabolic h⟩⟩

/-- A rational point of `U(λ)` fixes `Z(λ)` under conjugation only if it is the identity. -/
theorem conjugate_leviDefiningHopfIdeal_eq_self_iff_of_mem_unipotent
    (l : H →ₐc[R] LaurentPolynomial R) {u : WithConv (H →ₐ[R] R)} (hu : u ∈ unipotent R l) :
    (leviDefiningHopfIdeal l).conjugate u = leviDefiningHopfIdeal l ↔ u = 1 := by
  rw [conjugate_leviDefiningHopfIdeal_eq_self_iff l (unipotent_le_parabolic hu)]
  exact ⟨eq_one_of_mem_unipotent_of_mem_levi hu, fun h => h ▸ one_mem _⟩

/-- **The unipotent subgroup acts freely on the conjugates of the Levi.** Distinct rational
points `u` of `U(λ)` give distinct Levi factors `uZ(λ)u⁻¹ = Z(uλu⁻¹)` of `P(λ)`. -/
theorem injOn_conjugate_leviDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R) :
    Set.InjOn (leviDefiningHopfIdeal l).conjugate (unipotent R l) := by
  intro u₁ hu₁ u₂ hu₂ h
  have hfix : (leviDefiningHopfIdeal l).conjugate (u₂⁻¹ * u₁) = leviDefiningHopfIdeal l := by
    rw [HopfIdeal.conjugate_mul, h, HopfIdeal.conjugate_inv_conjugate]
  rw [conjugate_leviDefiningHopfIdeal_eq_self_iff_of_mem_unipotent l
    (mul_mem (inv_mem hu₂) hu₁), inv_mul_eq_one] at hfix
  exact hfix.symm

end HopfIdeal

end BialgHom
