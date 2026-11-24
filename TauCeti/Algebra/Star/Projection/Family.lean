/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.RingTheory.Idempotents

/-!
# Complete orthogonal projection families and central projection decompositions

A complete orthogonal projection family is a complete family of orthogonal idempotents whose
members are self-adjoint. For endomorphisms of a Hilbert space, these families describe orthogonal
decompositions of the identity.

When a star projection `z` is multiplicatively central, `{a : A | z * a = a}` is a principal
two-sided `⋆`-ideal (`IsStarProjection.centralSubalgebra`) carrying a unital algebra structure with
identity `z`. A complete orthogonal family of central star projections decomposes `A` as a
`⋆`-algebra direct product of these ideals
(`TauCeti.IsCompleteOrthogonalProjectionFamily.starAlgEquivPiOfIsMulCentral`), paralleling
`CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral`.

The matched overlap `∑ i, Q i * P i` has algebraic block formulas requiring only orthogonal
idempotents. These formulas support simultaneous intertwining of projection families, without
requiring the spectral or polar-decomposition API here.

## Main definitions

* `IsStarProjection.centralSubalgebra`: the principal `⋆`-ideal `{a : A | z * a = a}` of a central
  star projection `z`, equipped with unital `Semiring`, `Ring`, and `Algebra` instances with unit
  `z`.
* `AlgEquiv.centralSubalgebraSingle`: identify the `i`-th factor of an algebraic product
  decomposition `A ≃ₐ[R] ∀ i, B i` with the central `⋆`-subalgebra of `e.symm (Pi.single i 1)` when
  that central idempotent is a star projection.
* `TauCeti.IsCompleteOrthogonalProjectionFamily`: a complete orthogonal family of self-adjoint
  idempotents.
* `TauCeti.IsCompleteOrthogonalProjectionFamily.starAlgEquivPiOfIsMulCentral`: decompose a unital
  star algebra along a complete orthogonal family of central star projections.
* `TauCeti.projectionFamilyOverlap`: the matched overlap `∑ i, Q i * P i`.
-/

public section

namespace IsStarProjection

section CentralSubalgebra

/-- The principal two-sided `⋆`-ideal `{a : A | z * a = a}` cut out by a multiplicatively central
star projection `z`, bundled as a `NonUnitalStarSubalgebra R A`. -/
def centralSubalgebra {A : Type*} [NonUnitalSemiring A] [StarRing A] {z : A}
    (hz : IsStarProjection z) (R : Type*) [CommSemiring R] [Module R A] [SMulCommClass R A A]
    (hc : IsMulCentral z) : NonUnitalStarSubalgebra R A where
  carrier := {a : A | z * a = a}
  add_mem' {a b} ha hb := by dsimp at ha hb ⊢; rw [mul_add, ha, hb]
  zero_mem' := mul_zero z
  mul_mem' {a b} ha _ := by dsimp at ha ⊢; rw [← mul_assoc, ha]
  smul_mem' r {a} ha := by dsimp at ha ⊢; rw [mul_smul_comm, ha]
  star_mem' {a} ha := by
    dsimp at ha ⊢
    rw [(hc.comm (star a)).eq, ← hz.isSelfAdjoint.star_eq, ← star_mul, ha]

@[simp]
theorem mem_centralSubalgebra {A : Type*} [NonUnitalSemiring A] [StarRing A] {z a : A}
    (hz : IsStarProjection z) (R : Type*) [CommSemiring R] [Module R A] [SMulCommClass R A A]
    (hc : IsMulCentral z) :
    a ∈ hz.centralSubalgebra R hc ↔ z * a = a :=
  Iff.rfl

instance instSemiringCentralSubalgebra {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] [SMulCommClass R A A] {z : A} (hz : IsStarProjection z)
    (hc : IsMulCentral z) : Semiring (hz.centralSubalgebra R hc) where
  __ : NonUnitalSemiring (hz.centralSubalgebra R hc) := inferInstance
  one := ⟨z, (hz.mem_centralSubalgebra R hc).mpr hz.isIdempotentElem.eq⟩
  one_mul x := Subtype.ext ((hz.mem_centralSubalgebra R hc).mp x.property)
  mul_one x := Subtype.ext ((hc.comm x.val).symm.trans ((hz.mem_centralSubalgebra R hc).mp
    x.property))

@[simp]
theorem coe_one_centralSubalgebra {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] [SMulCommClass R A A] {z : A} (hz : IsStarProjection z)
    (hc : IsMulCentral z) : ((1 : hz.centralSubalgebra R hc) : A) = z :=
  (rfl)

instance instRingCentralSubalgebra {R A : Type*} [CommRing R] [NonUnitalRing A]
    [StarRing A] [Module R A] [SMulCommClass R A A] {z : A} (hz : IsStarProjection z)
    (hc : IsMulCentral z) : Ring (hz.centralSubalgebra R hc) where
  __ : NonUnitalRing (hz.centralSubalgebra R hc) := inferInstance
  __ : Semiring (hz.centralSubalgebra R hc) := inferInstance

instance instAlgebraCentralSubalgebra {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] {z : A}
    (hz : IsStarProjection z) (hc : IsMulCentral z) : Algebra R (hz.centralSubalgebra R hc) :=
  Algebra.ofModule'
    (fun r x ↦ Subtype.ext <|
      (smul_mul_assoc r z x.val).trans
        (congrArg (r • ·) ((hz.mem_centralSubalgebra R hc).mp x.property)))
    (fun r x ↦ Subtype.ext <| (mul_smul_comm r x.val z).trans
      (congrArg (r • ·) ((hc.comm x.val).symm.trans
        ((hz.mem_centralSubalgebra R hc).mp x.property))))

@[simp]
theorem coe_algebraMap_centralSubalgebra {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] {z : A}
    (hz : IsStarProjection z) (hc : IsMulCentral z) (r : R) :
    (algebraMap R (hz.centralSubalgebra R hc) r : A) = r • z :=
  (rfl)

end CentralSubalgebra

end IsStarProjection

namespace AlgEquiv

/-- In an algebraic product decomposition `e : A ≃ₐ[R] ∀ i, B i`, the pullback of the `i`-th
coordinate unit `Pi.single i 1` is multiplicatively central in `A`. -/
theorem isMulCentral_symm_single_one {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [DecidableEq ι] {B : ι → Type*} [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
    (e : A ≃ₐ[R] ∀ i, B i) (i : ι) : IsMulCentral (e.symm (Pi.single i 1)) := by
  refine Semigroup.mem_center_iff.mpr fun a ↦ e.injective ?_
  rw [map_mul, map_mul, e.apply_symm_apply, ← Pi.single_mul_left, ← Pi.single_mul_right,
    one_mul, mul_one]

/-- Identify the `i`-th factor `B i` of an algebraic product decomposition `e : A ≃ₐ[R] ∀ i, B i`
with the central `⋆`-subalgebra cut out by `e.symm (Pi.single i 1)` when that central idempotent is
a star projection. -/
def centralSubalgebraSingle {R A ι : Type*} [CommSemiring R] [Semiring A] [StarRing A]
    [Algebra R A] [DecidableEq ι] {B : ι → Type*} [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
    (e : A ≃ₐ[R] ∀ i, B i) {i : ι} (hz : IsStarProjection (e.symm (Pi.single i 1))) :
    B i ≃ₐ[R] hz.centralSubalgebra R (e.isMulCentral_symm_single_one i) where
  toFun b := ⟨e.symm (Pi.single i b), by
    rw [IsStarProjection.mem_centralSubalgebra, ← map_mul, ← Pi.single_mul, one_mul]⟩
  invFun x := e x.val i
  left_inv b := by simp
  right_inv x := Subtype.ext <| e.injective <| by
    rw [e.apply_symm_apply]
    have hx : e x.val = Pi.single i 1 * e x.val := by
      simpa only [map_mul, e.apply_symm_apply] using
        congrArg e ((hz.mem_centralSubalgebra R _).mp x.property).symm
    rw [hx, ← Pi.single_mul_left, one_mul]
  map_mul' b₁ b₂ := Subtype.ext <| by dsimp; rw [Pi.single_mul, map_mul]
  map_add' b₁ b₂ := Subtype.ext <| by dsimp; rw [Pi.single_add, map_add]
  commutes' r := Subtype.ext <| by
    simp [Algebra.algebraMap_eq_smul_one, ← map_smul, ← Pi.single_smul]

@[simp]
theorem coe_centralSubalgebraSingle_apply {R A ι : Type*} [CommSemiring R] [Semiring A]
    [StarRing A] [Algebra R A] [DecidableEq ι] {B : ι → Type*} [∀ i, Semiring (B i)]
    [∀ i, Algebra R (B i)] (e : A ≃ₐ[R] ∀ i, B i) {i : ι}
    (hz : IsStarProjection (e.symm (Pi.single i 1))) (b : B i) :
    ((e.centralSubalgebraSingle hz b :
      hz.centralSubalgebra R (e.isMulCentral_symm_single_one i)) : A) = e.symm (Pi.single i b) :=
  (rfl)

@[simp]
theorem centralSubalgebraSingle_symm_apply {R A ι : Type*} [CommSemiring R] [Semiring A]
    [StarRing A] [Algebra R A] [DecidableEq ι] {B : ι → Type*} [∀ i, Semiring (B i)]
    [∀ i, Algebra R (B i)] (e : A ≃ₐ[R] ∀ i, B i) {i : ι}
    (hz : IsStarProjection (e.symm (Pi.single i 1)))
    (x : hz.centralSubalgebra R (e.isMulCentral_symm_single_one i)) :
    (e.centralSubalgebraSingle hz).symm x = e x.val i :=
  (rfl)

end AlgEquiv

namespace TauCeti

section Family

variable {R ι : Type*} [Semiring R] [Fintype ι]

/-- A finite family of self-adjoint orthogonal idempotents with sum equal to the identity.
For Hilbert-space endomorphisms, its members are orthogonal projections. -/
structure IsCompleteOrthogonalProjectionFamily [Star R] (P : ι → R) : Prop
    extends CompleteOrthogonalIdempotents P where
  /-- Each member is self-adjoint. -/
  isSelfAdjoint : ∀ i, IsSelfAdjoint (P i)

/-- Every member of a complete orthogonal projection family is a star projection. -/
theorem IsCompleteOrthogonalProjectionFamily.isStarProjection [Star R] {P : ι → R}
    (hP : IsCompleteOrthogonalProjectionFamily P) (i : ι) : IsStarProjection (P i) :=
  ⟨hP.idem i, hP.isSelfAdjoint i⟩

/-- Complete orthogonal projection families are complete orthogonal idempotent families
whose members are star projections. -/
theorem isCompleteOrthogonalProjectionFamily_iff [Star R] (P : ι → R) :
    IsCompleteOrthogonalProjectionFamily P ↔
      CompleteOrthogonalIdempotents P ∧ ∀ i, IsStarProjection (P i) :=
  ⟨fun hP ↦ ⟨hP.toCompleteOrthogonalIdempotents, hP.isStarProjection⟩,
    fun ⟨hP, hPstar⟩ ↦ ⟨hP, fun i ↦ (hPstar i).isSelfAdjoint⟩⟩

/-- Decompose a unital star algebra `R` over `S` as the direct product of the principal `⋆`-ideals
`IsStarProjection.centralSubalgebra` cut out by a complete orthogonal family of central star
projections, paralleling `CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral`. -/
def IsCompleteOrthogonalProjectionFamily.starAlgEquivPiOfIsMulCentral [StarRing R]
    {z : ι → R} (hz : IsCompleteOrthogonalProjectionFamily z)
    (S : Type*) [CommSemiring S] [Module S R] [SMulCommClass S R R]
    (hc : ∀ i, IsMulCentral (z i)) :
    R ≃⋆ₐ[S] ∀ i, (hz.isStarProjection i).centralSubalgebra S (hc i) where
  toFun a i := ⟨z i * a, by
    rw [IsStarProjection.mem_centralSubalgebra, ← mul_assoc, (hz.idem i).eq]⟩
  invFun y := ∑ i, (y i).val
  left_inv a := by simp [← Finset.sum_mul, hz.complete]
  right_inv y := by
    ext i : 2
    dsimp
    rw [Finset.mul_sum]
    refine (Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)).trans
      (((hz.isStarProjection i).mem_centralSubalgebra S (hc i)).mp (y i).property)
    rw [← ((hz.isStarProjection j).mem_centralSubalgebra S (hc j)).mp (y j).property,
      ← mul_assoc, hz.ortho hji.symm, zero_mul]
  map_mul' a b := by
    ext i : 2
    dsimp
    calc
      z i * (a * b) = (z i * z i) * (a * b) := by rw [(hz.idem i).eq]
      _ = z i * (z i * a) * b := by simp only [mul_assoc]
      _ = z i * (a * z i) * b := by rw [((hc i).comm a).eq]
      _ = (z i * a) * (z i * b) := by simp only [mul_assoc]
  map_add' a b := by ext i : 2; exact mul_add (z i) a b
  map_star' a := by
    ext i : 2
    dsimp
    rw [star_mul, (hz.isSelfAdjoint i).star_eq, ((hc i).comm (star a)).eq]
  map_smul' r a := by ext i : 2; exact mul_smul_comm r (z i) a

@[simp]
theorem IsCompleteOrthogonalProjectionFamily.coe_starAlgEquivPiOfIsMulCentral_apply [StarRing R]
    {z : ι → R} (hz : IsCompleteOrthogonalProjectionFamily z)
    (S : Type*) [CommSemiring S] [Module S R] [SMulCommClass S R R]
    (hc : ∀ i, IsMulCentral (z i)) (a : R) (i : ι) :
    ((hz.starAlgEquivPiOfIsMulCentral S hc a i :
      (hz.isStarProjection i).centralSubalgebra S (hc i)) : R) = z i * a :=
  (rfl)

@[simp]
theorem IsCompleteOrthogonalProjectionFamily.starAlgEquivPiOfIsMulCentral_symm_apply [StarRing R]
    {z : ι → R} (hz : IsCompleteOrthogonalProjectionFamily z)
    (S : Type*) [CommSemiring S] [Module S R] [SMulCommClass S R R]
    (hc : ∀ i, IsMulCentral (z i))
    (y : ∀ i, (hz.isStarProjection i).centralSubalgebra S (hc i)) :
    (hz.starAlgEquivPiOfIsMulCentral S hc).symm y = ∑ i, (y i).val :=
  (rfl)

end Family

section Overlap

variable {R ι : Type*} [Semiring R] [Fintype ι]

/-- The overlap between two projection families, with each source block sent into the
corresponding target block in the endomorphism setting. -/
noncomputable def projectionFamilyOverlap (P Q : ι → R) : R := ∑ i, Q i * P i

/-- The overlap is the sum of the matched projection products. -/
theorem projectionFamilyOverlap_def (P Q : ι → R) :
    projectionFamilyOverlap P Q = ∑ i, Q i * P i := (rfl)

/-- Taking the star of the overlap reverses the two self-adjoint families. -/
@[simp]
theorem star_projectionFamilyOverlap [StarRing R] {P Q : ι → R}
    (hP : ∀ i, IsSelfAdjoint (P i)) (hQ : ∀ i, IsSelfAdjoint (Q i)) :
    star (projectionFamilyOverlap P Q) = projectionFamilyOverlap Q P := by
  simp only [projectionFamilyOverlap_def, star_sum, star_mul,
    fun i ↦ (hP i).star_eq, fun i ↦ (hQ i).star_eq]

end Overlap

end TauCeti

namespace OrthogonalIdempotents

open TauCeti

variable {R ι : Type*} [Semiring R] [Fintype ι] {P Q : ι → R}

/-- Restricting the overlap to a source block retains just its matched product. -/
@[simp]
theorem projectionFamilyOverlap_mul (hP : OrthogonalIdempotents P) (Q : ι → R) (i : ι) :
    projectionFamilyOverlap P Q * P i = Q i * P i := by
  classical
  simp [projectionFamilyOverlap_def, Finset.sum_mul, mul_assoc, hP.mul_eq, mul_ite]

/-- Projecting the overlap onto a target block retains just its matched product. -/
@[simp]
theorem mul_projectionFamilyOverlap (hQ : OrthogonalIdempotents Q) (P : ι → R) (i : ι) :
    Q i * projectionFamilyOverlap P Q = Q i * P i := by
  classical
  simp [projectionFamilyOverlap_def, Finset.mul_sum, ← mul_assoc, hQ.mul_eq, ite_mul]

end OrthogonalIdempotents
