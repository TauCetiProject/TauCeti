/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.LinearAlgebra.Graded.ExtendByZero

/-!
# Gradings on the dual numbers

This file supplies two standard nonnegative internal gradings on `DualNumber R`:

1. **The degree-two grading** (`TauCeti.dualNumberGrade`, `TauCeti.dualNumberIntegerGrade`):
   scalars have degree zero and the infinitesimal generator `DualNumber.eps` has degree two,
   modelling `R[x]/(x²)` with `deg x = 2` (the zigzag algebra of a single vertex with no edges).
2. **The degree-one grading** (`TauCeti.dualNumberLinearGrade`,
   `TauCeti.dualNumberLinearIntegerGrade`): scalars have degree zero and `DualNumber.eps` has
   degree one, modelling the exterior algebra `R[x]/(x²)` on one generator of degree one.

Both gradings are internal to `DualNumber R`, so the graded algebras supplied here compare directly
with the usual ungraded dual-number algebra.

## Main definitions

* `TauCeti.dualNumberGrade` and `TauCeti.dualNumberGradedAlgebra`: the degree-two `ℕ`-grading and
  its graded-algebra structure.
* `TauCeti.dualNumberIntegerGrade` and `TauCeti.dualNumberIntegerGradedAlgebra`: the degree-two
  grading extended by zero to `ℤ`.
* `TauCeti.dualNumberLinearGrade` and `TauCeti.dualNumberLinearGradedAlgebra`: the degree-one
  `ℕ`-grading and its graded-algebra structure.
* `TauCeti.dualNumberLinearIntegerGrade` and `TauCeti.dualNumberLinearIntegerGradedAlgebra`: the
  degree-one grading extended by zero to `ℤ`.

## Main results

* `TauCeti.isInternal_dualNumberGrade` and `TauCeti.isInternal_dualNumberLinearGrade`: the dual
  numbers are the internal direct sum of their scalar and infinitesimal pieces in each grading.
* `TauCeti.dualNumberGradeZeroEquiv`, `TauCeti.dualNumberGradeTwoEquiv`,
  `TauCeti.dualNumberLinearGradeZeroEquiv`, and `TauCeti.dualNumberLinearGradeOneEquiv`: the
  nonzero pieces are linearly equivalent to the base ring.
* `TauCeti.dualNumberIntegerGrade_zero_eq_span_one` and
  `TauCeti.dualNumberLinearIntegerGrade_zero_eq_span_one`: in both integer gradings, degree zero is
  the line through `1`.
-/

public section

namespace TauCeti

universe u

variable (R : Type u) [CommSemiring R]

/-- The standard nonnegative grading on the dual numbers: degree zero consists of scalars,
degree two consists of scalar multiples of `DualNumber.eps`, and every other degree is zero. -/
noncomputable def dualNumberGrade (n : ℕ) : Submodule R (DualNumber R) :=
  if n = 0 then LinearMap.ker (TrivSqZeroExt.sndHom R R)
  else if n = 2 then LinearMap.ker (TrivSqZeroExt.fstHom R R R).toLinearMap
  else ⊥

/-- The degree-zero piece consists exactly of dual numbers with zero infinitesimal coordinate. -/
theorem dualNumberGrade_zero_eq_ker_snd :
    dualNumberGrade R 0 = LinearMap.ker (TrivSqZeroExt.sndHom R R) := by
  simp [dualNumberGrade]

/-- The degree-two piece consists exactly of dual numbers with zero scalar coordinate. -/
theorem dualNumberGrade_two_eq_ker_fst :
    dualNumberGrade R 2 = LinearMap.ker (TrivSqZeroExt.fstHom R R R).toLinearMap := by
  simp [dualNumberGrade]

/-- All pieces other than degrees zero and two vanish. -/
theorem dualNumberGrade_eq_bot {n : ℕ} (h0 : n ≠ 0) (h2 : n ≠ 2) :
    dualNumberGrade R n = ⊥ := by
  simp [dualNumberGrade, h0, h2]

/-- Membership in degree zero is detected by the infinitesimal coordinate. -/
@[simp]
theorem mem_dualNumberGrade_zero {x : DualNumber R} :
    x ∈ dualNumberGrade R 0 ↔ x.snd = 0 := by
  simp [dualNumberGrade_zero_eq_ker_snd]

/-- Membership in degree two is detected by the scalar coordinate. -/
@[simp]
theorem mem_dualNumberGrade_two {x : DualNumber R} :
    x ∈ dualNumberGrade R 2 ↔ x.fst = 0 := by
  simp [dualNumberGrade_two_eq_ker_fst]

/-- The scalar inclusion lands in degree zero. -/
theorem inl_mem_dualNumberGrade_zero (r : R) :
    TrivSqZeroExt.inl r ∈ dualNumberGrade R 0 := by
  simp

/-- The algebra map lands in degree zero. -/
theorem algebraMap_mem_dualNumberGrade_zero (r : R) :
    algebraMap R (DualNumber R) r ∈ dualNumberGrade R 0 := by
  simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- The infinitesimal inclusion lands in degree two. -/
theorem inr_mem_dualNumberGrade_two (r : R) :
    TrivSqZeroExt.inr r ∈ dualNumberGrade R 2 := by
  simp

/-- The dual-number generator has degree two. -/
theorem eps_mem_dualNumberGrade_two :
    DualNumber.eps ∈ dualNumberGrade R 2 := by
  simpa only [DualNumber.eps] using inr_mem_dualNumberGrade_two R 1

/-- The degree-zero piece of the dual numbers is linearly equivalent to the base ring. -/
noncomputable def dualNumberGradeZeroEquiv : dualNumberGrade R 0 ≃ₗ[R] R where
  toFun x := x.1.fst
  invFun r := ⟨TrivSqZeroExt.inl r, inl_mem_dualNumberGrade_zero R r⟩
  left_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · simp
    · simp [(mem_dualNumberGrade_zero (R := R)).mp x.2]
  right_inv r := by simp
  map_add' x y := by simp
  map_smul' r x := by simp

/-- The degree-zero equivalence reads the scalar coordinate. -/
@[simp]
theorem dualNumberGradeZeroEquiv_apply (x : dualNumberGrade R 0) :
    dualNumberGradeZeroEquiv R x = x.1.fst := by
  unfold dualNumberGradeZeroEquiv
  rfl

/-- The inverse degree-zero equivalence inserts a scalar dual number. -/
@[simp]
theorem dualNumberGradeZeroEquiv_symm_apply (r : R) :
    (dualNumberGradeZeroEquiv R).symm r =
      ⟨TrivSqZeroExt.inl r, inl_mem_dualNumberGrade_zero R r⟩ := by
  unfold dualNumberGradeZeroEquiv
  rfl

/-- The degree-two piece of the dual numbers is linearly equivalent to the base ring. -/
noncomputable def dualNumberGradeTwoEquiv : dualNumberGrade R 2 ≃ₗ[R] R where
  toFun x := x.1.snd
  invFun r := ⟨TrivSqZeroExt.inr r, inr_mem_dualNumberGrade_two R r⟩
  left_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · simp [(mem_dualNumberGrade_two (R := R)).mp x.2]
    · simp
  right_inv r := by simp
  map_add' x y := by simp
  map_smul' r x := by simp

/-- The degree-two equivalence reads the infinitesimal coordinate. -/
@[simp]
theorem dualNumberGradeTwoEquiv_apply (x : dualNumberGrade R 2) :
    dualNumberGradeTwoEquiv R x = x.1.snd := by
  unfold dualNumberGradeTwoEquiv
  rfl

/-- The inverse degree-two equivalence inserts an infinitesimal dual number. -/
@[simp]
theorem dualNumberGradeTwoEquiv_symm_apply (r : R) :
    (dualNumberGradeTwoEquiv R).symm r =
      ⟨TrivSqZeroExt.inr r, inr_mem_dualNumberGrade_two R r⟩ := by
  unfold dualNumberGradeTwoEquiv
  rfl

/-- Multiplication adds degrees in the standard grading of the dual numbers. -/
theorem mul_mem_dualNumberGrade {m n : ℕ} {x y : DualNumber R}
    (hx : x ∈ dualNumberGrade R m) (hy : y ∈ dualNumberGrade R n) :
    x * y ∈ dualNumberGrade R (m + n) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · rcases eq_or_ne n 0 with rfl | hn0
    · simp only [mem_dualNumberGrade_zero] at hx hy ⊢
      simp [hx, hy]
    · rcases eq_or_ne n 2 with rfl | hn2
      · simp only [mem_dualNumberGrade_zero] at hx
        simp only [mem_dualNumberGrade_two] at hy ⊢
        simp [hy]
      · have : y = 0 := by
          rw [dualNumberGrade_eq_bot R hn0 hn2] at hy
          exact hy
        subst y
        simp
  · rcases eq_or_ne m 2 with rfl | hm2
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp only [mem_dualNumberGrade_two] at hx
        simp only [mem_dualNumberGrade_zero] at hy
        simp [hx]
      · rcases eq_or_ne n 2 with rfl | hn2
        · have hxfst : x.fst = 0 := (mem_dualNumberGrade_two (R := R)).mp hx
          have hyfst : y.fst = 0 := (mem_dualNumberGrade_two (R := R)).mp hy
          have hxy : x * y = 0 := by
            apply TrivSqZeroExt.ext
            · simp [hxfst, hyfst]
            · simp [hxfst, hyfst]
          rw [hxy]
          exact (dualNumberGrade R (2 + 2)).zero_mem
        · have : y = 0 := by
            simpa [dualNumberGrade_eq_bot R hn0 hn2] using hy
          subst y
          simp
    · have : x = 0 := by
        simpa [dualNumberGrade_eq_bot R hm0 hm2] using hx
      subst x
      simp

/-- The standard grading makes the dual numbers a graded monoid. This is a theorem rather than a
global instance so callers choose when to install the grading. -/
theorem dualNumberGradedMonoid : SetLike.GradedMonoid (dualNumberGrade R) where
  one_mem := by simp
  mul_mem _ _ _ _ := mul_mem_dualNumberGrade R

namespace DualNumberGrading

/-- The degree-zero part of a dual number, valued in the degree-zero submodule. -/
private noncomputable def degreeZeroPart : DualNumber R →ₗ[R] dualNumberGrade R 0 :=
  ((TrivSqZeroExt.inlAlgHom R R R).toLinearMap.comp
    (TrivSqZeroExt.fstHom R R R).toLinearMap).codRestrict
      (dualNumberGrade R 0) fun _ => by simp

/-- The degree-two part of a dual number, valued in the degree-two submodule. -/
private noncomputable def degreeTwoPart : DualNumber R →ₗ[R] dualNumberGrade R 2 :=
  ((TrivSqZeroExt.inrHom R R).comp (TrivSqZeroExt.sndHom R R)).codRestrict
    (dualNumberGrade R 2) fun _ => by simp

@[simp]
private theorem coe_degreeZeroPart_apply (x : DualNumber R) :
    (degreeZeroPart R x : DualNumber R) = TrivSqZeroExt.inl x.fst := by
  rfl

@[simp]
private theorem coe_degreeTwoPart_apply (x : DualNumber R) :
    (degreeTwoPart R x : DualNumber R) = TrivSqZeroExt.inr x.snd := by
  rfl

/-- The two-coordinate decomposition, regarded as an element of the direct sum of all grades. -/
private noncomputable def decompose :
    DualNumber R →ₗ[R] DirectSum ℕ (fun n => dualNumberGrade R n) :=
  (DirectSum.lof R ℕ (fun n => dualNumberGrade R n) 0).comp (degreeZeroPart R) +
    (DirectSum.lof R ℕ (fun n => dualNumberGrade R n) 2).comp (degreeTwoPart R)

/-- Reassembling the two coordinate parts recovers the original dual number. -/
private theorem coeAddMonoidHom_decompose (x : DualNumber R) :
    DirectSum.coeAddMonoidHom (dualNumberGrade R) (decompose R x) = x := by
  simpa [decompose, DirectSum.lof_eq_of] using TrivSqZeroExt.inl_fst_add_inr_snd_eq x

/-- Decomposing the sum of a family of graded components recovers that family. -/
private theorem decompose_coeAddMonoidHom (x : DirectSum ℕ (fun n => dualNumberGrade R n)) :
    decompose R (DirectSum.coeAddMonoidHom (dualNumberGrade R) x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n x =>
      rcases eq_or_ne n 0 with rfl | hn0
      · have hx := (mem_dualNumberGrade_zero R).1 x.property
        have hzero : degreeZeroPart R x = x := Subtype.ext (TrivSqZeroExt.ext rfl (by simp [hx]))
        have htwo : degreeTwoPart R x = 0 := Subtype.ext (by simp [hx])
        simp [decompose, hzero, htwo, DirectSum.lof_eq_of]
      rcases eq_or_ne n 2 with rfl | hn2
      · have hx := (mem_dualNumberGrade_two R).1 x.property
        have hzero : degreeZeroPart R x = 0 := Subtype.ext (by simp [hx])
        have htwo : degreeTwoPart R x = x := Subtype.ext (TrivSqZeroExt.ext (by simp [hx]) rfl)
        simp [decompose, hzero, htwo, DirectSum.lof_eq_of]
      · obtain rfl : x = 0 := Subtype.ext (by simpa [dualNumberGrade_eq_bot R hn0 hn2] using x.2)
        simp

/-- The coordinate decomposition of the dual numbers into their degree pieces. -/
@[instance_reducible]
private noncomputable def decomposition : DirectSum.Decomposition (dualNumberGrade R) where
  decompose' := decompose R
  left_inv := coeAddMonoidHom_decompose R
  right_inv := decompose_coeAddMonoidHom R

end DualNumberGrading

/-- The dual numbers are the internal direct sum of the scalar piece in degree zero and the
infinitesimal piece in degree two. -/
theorem isInternal_dualNumberGrade : DirectSum.IsInternal (dualNumberGrade R) :=
  letI := DualNumberGrading.decomposition R
  DirectSum.Decomposition.isInternal _

/-- The standard degree-two grading makes `DualNumber R` a graded algebra. This is a definition
rather than a global instance so callers choose when to install it locally. -/
@[instance_reducible]
noncomputable def dualNumberGradedAlgebra : GradedAlgebra (dualNumberGrade R) := by
  letI := dualNumberGradedMonoid R
  exact DirectSum.IsInternal.gradedAlgebra (isInternal_dualNumberGrade R)

/-! ### Integer degrees -/

/-- The standard grading of the dual numbers, extended by zero from natural to integer degrees.
This is the indexing used by internal shifts of graded modules. -/
noncomputable def dualNumberIntegerGrade (d : ℤ) : Submodule R (DualNumber R) :=
  Graded.extendByZero (dualNumberGrade R) d

/-- In a natural degree `n`, the integer grading is the degree-`n` piece of the standard grading. -/
@[simp]
theorem dualNumberIntegerGrade_ofNat (n : ℕ) :
    dualNumberIntegerGrade R n = dualNumberGrade R n :=
  Graded.extendByZero_natCast _ n

/-- The integer grading of the dual numbers vanishes in negative degrees. -/
@[simp]
theorem dualNumberIntegerGrade_eq_bot_of_neg {d : ℤ} (hd : d < 0) :
    dualNumberIntegerGrade R d = ⊥ :=
  Graded.extendByZero_of_neg _ hd

/-- The unit of the dual numbers has integer degree zero. -/
theorem one_mem_dualNumberIntegerGrade_zero :
    (1 : DualNumber R) ∈ dualNumberIntegerGrade R 0 := by
  rw [← Nat.cast_zero, dualNumberIntegerGrade_ofNat, mem_dualNumberGrade_zero,
    TrivSqZeroExt.snd_one]

/-- The dual-number generator has integer degree two. -/
theorem eps_mem_dualNumberIntegerGrade_two :
    DualNumber.eps ∈ dualNumberIntegerGrade R 2 := by
  simpa using dualNumberIntegerGrade_ofNat R 2 ▸ eps_mem_dualNumberGrade_two R

/-- **Integer degree zero is the line through `1`.** -/
theorem dualNumberIntegerGrade_zero_eq_span_one :
    dualNumberIntegerGrade R 0 = R ∙ (1 : DualNumber R) := by
  ext x
  rw [← Nat.cast_zero, dualNumberIntegerGrade_ofNat, mem_dualNumberGrade_zero,
    Submodule.mem_span_singleton]
  refine ⟨fun hx => ⟨x.fst, TrivSqZeroExt.ext (by simp) (by simp [hx])⟩, ?_⟩
  rintro ⟨r, rfl⟩
  simp

/-- The dual numbers are integer graded, with `ε` in degree two and zero pieces in negative
degrees. This is a definition rather than a global instance, like `dualNumberGradedAlgebra`. -/
@[instance_reducible]
noncomputable def dualNumberIntegerGradedAlgebra : GradedAlgebra (dualNumberIntegerGrade R) :=
  let _ := dualNumberGradedAlgebra R
  Graded.gradedAlgebraExtendByZero (dualNumberGrade R)

/-! ### The degree-one grading -/

/-- The degree-one nonnegative grading on the dual numbers: degree zero consists of scalars,
degree one consists of scalar multiples of `DualNumber.eps`, and every degree `≥ 2` vanishes. -/
noncomputable def dualNumberLinearGrade (n : ℕ) : Submodule R (DualNumber R) :=
  if n = 0 then LinearMap.ker (TrivSqZeroExt.sndHom R R)
  else if n = 1 then LinearMap.ker (TrivSqZeroExt.fstHom R R R).toLinearMap
  else ⊥

/-- In the degree-one grading, degree zero consists of dual numbers with zero infinitesimal
coordinate. -/
theorem dualNumberLinearGrade_zero_eq_ker_snd :
    dualNumberLinearGrade R 0 = LinearMap.ker (TrivSqZeroExt.sndHom R R) := by
  simp [dualNumberLinearGrade]

/-- In the degree-one grading, degree one consists of dual numbers with zero scalar coordinate. -/
theorem dualNumberLinearGrade_one_eq_ker_fst :
    dualNumberLinearGrade R 1 = LinearMap.ker (TrivSqZeroExt.fstHom R R R).toLinearMap := by
  simp [dualNumberLinearGrade]

/-- All pieces other than degrees zero and one vanish in `TauCeti.dualNumberLinearGrade`. -/
theorem dualNumberLinearGrade_eq_bot {n : ℕ} (h0 : n ≠ 0) (h1 : n ≠ 1) :
    dualNumberLinearGrade R n = ⊥ := by
  simp [dualNumberLinearGrade, h0, h1]

/-- Membership in degree zero of `TauCeti.dualNumberLinearGrade` is detected by the infinitesimal
coordinate. -/
@[simp]
theorem mem_dualNumberLinearGrade_zero {x : DualNumber R} :
    x ∈ dualNumberLinearGrade R 0 ↔ x.snd = 0 := by
  simp [dualNumberLinearGrade_zero_eq_ker_snd]

/-- Membership in degree one of `TauCeti.dualNumberLinearGrade` is detected by the scalar
coordinate. -/
@[simp]
theorem mem_dualNumberLinearGrade_one {x : DualNumber R} :
    x ∈ dualNumberLinearGrade R 1 ↔ x.fst = 0 := by
  simp [dualNumberLinearGrade_one_eq_ker_fst]

/-- The scalar inclusion lands in degree zero of `TauCeti.dualNumberLinearGrade`. -/
theorem inl_mem_dualNumberLinearGrade_zero (r : R) :
    TrivSqZeroExt.inl r ∈ dualNumberLinearGrade R 0 := by
  simp

/-- The infinitesimal inclusion lands in degree one of `TauCeti.dualNumberLinearGrade`. -/
theorem inr_mem_dualNumberLinearGrade_one (r : R) :
    TrivSqZeroExt.inr r ∈ dualNumberLinearGrade R 1 := by
  simp

/-- The dual-number generator has degree one in `TauCeti.dualNumberLinearGrade`. -/
theorem eps_mem_dualNumberLinearGrade_one :
    DualNumber.eps ∈ dualNumberLinearGrade R 1 := by
  simpa only [DualNumber.eps] using inr_mem_dualNumberLinearGrade_one R 1

/-- The degree-zero piece of `TauCeti.dualNumberLinearGrade` is linearly equivalent to `R`. -/
noncomputable def dualNumberLinearGradeZeroEquiv : dualNumberLinearGrade R 0 ≃ₗ[R] R :=
  LinearEquiv.ofEq _ _
      ((dualNumberLinearGrade_zero_eq_ker_snd R).trans (dualNumberGrade_zero_eq_ker_snd R).symm) ≪≫ₗ
    dualNumberGradeZeroEquiv R

/-- The degree-one piece of `TauCeti.dualNumberLinearGrade` is linearly equivalent to `R`. -/
noncomputable def dualNumberLinearGradeOneEquiv : dualNumberLinearGrade R 1 ≃ₗ[R] R :=
  LinearEquiv.ofEq _ _
      ((dualNumberLinearGrade_one_eq_ker_fst R).trans (dualNumberGrade_two_eq_ker_fst R).symm) ≪≫ₗ
    dualNumberGradeTwoEquiv R

/-- Multiplication adds degrees in `TauCeti.dualNumberLinearGrade`. -/
theorem mul_mem_dualNumberLinearGrade {m n : ℕ} {x y : DualNumber R}
    (hx : x ∈ dualNumberLinearGrade R m) (hy : y ∈ dualNumberLinearGrade R n) :
    x * y ∈ dualNumberLinearGrade R (m + n) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · rcases eq_or_ne n 0 with rfl | hn0
    · simp only [mem_dualNumberLinearGrade_zero] at hx hy ⊢
      simp [hx, hy]
    · rcases eq_or_ne n 1 with rfl | hn1
      · simp only [mem_dualNumberLinearGrade_zero] at hx
        simp only [mem_dualNumberLinearGrade_one] at hy ⊢
        simp [hy]
      · have hy0 : y = 0 := by simpa [dualNumberLinearGrade_eq_bot R hn0 hn1] using hy
        subst y
        simp
  · rcases eq_or_ne m 1 with rfl | hm1
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp only [mem_dualNumberLinearGrade_one] at hx
        simp only [mem_dualNumberLinearGrade_zero] at hy
        simp [hx]
      · rcases eq_or_ne n 1 with rfl | hn1
        · have hxfst : x.fst = 0 := (mem_dualNumberLinearGrade_one R).mp hx
          have hyfst : y.fst = 0 := (mem_dualNumberLinearGrade_one R).mp hy
          have hxy : x * y = 0 :=
            TrivSqZeroExt.ext (by simp [hxfst, hyfst]) (by simp [hxfst, hyfst])
          rw [hxy]
          exact (dualNumberLinearGrade R (1 + 1)).zero_mem
        · have hy0 : y = 0 := by simpa [dualNumberLinearGrade_eq_bot R hn0 hn1] using hy
          subst y
          simp
    · have hx0 : x = 0 := by simpa [dualNumberLinearGrade_eq_bot R hm0 hm1] using hx
      subst x
      simp

/-- The degree-one grading makes the dual numbers a graded monoid. -/
theorem dualNumberLinearGradedMonoid : SetLike.GradedMonoid (dualNumberLinearGrade R) where
  one_mem := by simp
  mul_mem _ _ _ _ := mul_mem_dualNumberLinearGrade R

namespace DualNumberLinearGrading

private noncomputable def degreeZeroPart : DualNumber R →ₗ[R] dualNumberLinearGrade R 0 :=
  ((TrivSqZeroExt.inlAlgHom R R R).toLinearMap.comp
    (TrivSqZeroExt.fstHom R R R).toLinearMap).codRestrict
      (dualNumberLinearGrade R 0) fun _ => by simp

private noncomputable def degreeOnePart : DualNumber R →ₗ[R] dualNumberLinearGrade R 1 :=
  ((TrivSqZeroExt.inrHom R R).comp (TrivSqZeroExt.sndHom R R)).codRestrict
    (dualNumberLinearGrade R 1) fun _ => by simp

@[simp]
private theorem coe_degreeZeroPart_apply (x : DualNumber R) :
    (degreeZeroPart R x : DualNumber R) = TrivSqZeroExt.inl x.fst :=
  rfl

@[simp]
private theorem coe_degreeOnePart_apply (x : DualNumber R) :
    (degreeOnePart R x : DualNumber R) = TrivSqZeroExt.inr x.snd :=
  rfl

private noncomputable def decompose :
    DualNumber R →ₗ[R] DirectSum ℕ (fun n => dualNumberLinearGrade R n) :=
  (DirectSum.lof R ℕ (fun n => dualNumberLinearGrade R n) 0).comp (degreeZeroPart R) +
    (DirectSum.lof R ℕ (fun n => dualNumberLinearGrade R n) 1).comp (degreeOnePart R)

private theorem coeAddMonoidHom_decompose (x : DualNumber R) :
    DirectSum.coeAddMonoidHom (dualNumberLinearGrade R) (decompose R x) = x := by
  simpa [decompose, DirectSum.lof_eq_of] using TrivSqZeroExt.inl_fst_add_inr_snd_eq x

private theorem decompose_coeAddMonoidHom
    (x : DirectSum ℕ (fun n => dualNumberLinearGrade R n)) :
    decompose R (DirectSum.coeAddMonoidHom (dualNumberLinearGrade R) x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n x =>
      rcases eq_or_ne n 0 with rfl | hn0
      · have hx := (mem_dualNumberLinearGrade_zero R).1 x.property
        have hzero : degreeZeroPart R x = x := Subtype.ext (TrivSqZeroExt.ext rfl (by simp [hx]))
        have hone : degreeOnePart R x = 0 := Subtype.ext (by simp [hx])
        simp [decompose, hzero, hone, DirectSum.lof_eq_of]
      rcases eq_or_ne n 1 with rfl | hn1
      · have hx := (mem_dualNumberLinearGrade_one R).1 x.property
        have hzero : degreeZeroPart R x = 0 := Subtype.ext (by simp [hx])
        have hone : degreeOnePart R x = x := Subtype.ext (TrivSqZeroExt.ext (by simp [hx]) rfl)
        simp [decompose, hzero, hone, DirectSum.lof_eq_of]
      · obtain rfl : x = 0 :=
          Subtype.ext (by simpa [dualNumberLinearGrade_eq_bot R hn0 hn1] using x.2)
        simp

@[instance_reducible]
private noncomputable def decomposition : DirectSum.Decomposition (dualNumberLinearGrade R) where
  decompose' := decompose R
  left_inv := coeAddMonoidHom_decompose R
  right_inv := decompose_coeAddMonoidHom R

end DualNumberLinearGrading

/-- The dual numbers are the internal direct sum of their scalar piece in degree zero and their
infinitesimal piece in degree one. -/
theorem isInternal_dualNumberLinearGrade : DirectSum.IsInternal (dualNumberLinearGrade R) :=
  letI := DualNumberLinearGrading.decomposition R
  DirectSum.Decomposition.isInternal _

/-- The degree-one grading makes `DualNumber R` a graded algebra. Like `dualNumberGradedAlgebra`,
this is a definition rather than a global instance so callers choose when to install it locally. -/
@[instance_reducible]
noncomputable def dualNumberLinearGradedAlgebra : GradedAlgebra (dualNumberLinearGrade R) := by
  letI := dualNumberLinearGradedMonoid R
  exact DirectSum.IsInternal.gradedAlgebra (isInternal_dualNumberLinearGrade R)

/-- The degree-one grading of the dual numbers extended by zero from natural to integer degrees. -/
noncomputable def dualNumberLinearIntegerGrade (d : ℤ) : Submodule R (DualNumber R) :=
  Graded.extendByZero (dualNumberLinearGrade R) d

/-- In a natural degree `n`, `TauCeti.dualNumberLinearIntegerGrade` agrees with
`TauCeti.dualNumberLinearGrade`. -/
@[simp]
theorem dualNumberLinearIntegerGrade_ofNat (n : ℕ) :
    dualNumberLinearIntegerGrade R n = dualNumberLinearGrade R n :=
  Graded.extendByZero_natCast _ n

/-- `TauCeti.dualNumberLinearIntegerGrade` vanishes in negative degrees. -/
@[simp]
theorem dualNumberLinearIntegerGrade_eq_bot_of_neg {d : ℤ} (hd : d < 0) :
    dualNumberLinearIntegerGrade R d = ⊥ :=
  Graded.extendByZero_of_neg _ hd

/-- The unit of the dual numbers has integer degree zero in
`TauCeti.dualNumberLinearIntegerGrade`. -/
theorem one_mem_dualNumberLinearIntegerGrade_zero :
    (1 : DualNumber R) ∈ dualNumberLinearIntegerGrade R 0 := by
  rw [← Nat.cast_zero, dualNumberLinearIntegerGrade_ofNat, mem_dualNumberLinearGrade_zero,
    TrivSqZeroExt.snd_one]

/-- The dual-number generator has integer degree one in
`TauCeti.dualNumberLinearIntegerGrade`. -/
theorem eps_mem_dualNumberLinearIntegerGrade_one :
    DualNumber.eps ∈ dualNumberLinearIntegerGrade R 1 := by
  simpa using dualNumberLinearIntegerGrade_ofNat R 1 ▸ eps_mem_dualNumberLinearGrade_one R

/-- **In the degree-one integer grading, degree zero is the line through `1`.** -/
theorem dualNumberLinearIntegerGrade_zero_eq_span_one :
    dualNumberLinearIntegerGrade R 0 = R ∙ (1 : DualNumber R) := by
  ext x
  rw [← Nat.cast_zero, dualNumberLinearIntegerGrade_ofNat, mem_dualNumberLinearGrade_zero,
    Submodule.mem_span_singleton]
  refine ⟨fun hx => ⟨x.fst, TrivSqZeroExt.ext (by simp) (by simp [hx])⟩, ?_⟩
  rintro ⟨r, rfl⟩
  simp

/-- The dual numbers are integer graded with `ε` in degree one and zero pieces in negative degrees.
This is a definition rather than a global instance, like `dualNumberIntegerGradedAlgebra`. -/
@[instance_reducible]
noncomputable def dualNumberLinearIntegerGradedAlgebra :
    GradedAlgebra (dualNumberLinearIntegerGrade R) :=
  let _ := dualNumberLinearGradedAlgebra R
  Graded.gradedAlgebraExtendByZero (dualNumberLinearGrade R)

end TauCeti
