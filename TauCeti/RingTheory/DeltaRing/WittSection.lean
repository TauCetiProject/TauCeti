/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Truncated.Basic

import Mathlib.Tactic.FinCases

/-!
# Delta structures as length-two Witt-vector sections

A delta structure on a commutative ring is equivalent to a ring section of the zeroth
coordinate of its length-two Witt vectors. The section sends `x` to `(x, delta p x)`.
Its ghost component at index one is the Frobenius lift. This description works with arbitrary
`p`-torsion and therefore retains information that the Frobenius lift alone may forget.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Remark 2.4.
-/

public section

namespace TauCeti.DeltaRing

variable (p : ℕ) (A : Type*) [CommRing A] [Fact p.Prime]

section Section

variable [DeltaRing p A]

/-- The length-two Witt-vector ring section `x ↦ (x, delta p x)` of a delta ring. -/
noncomputable def wittSection : A →+* TruncatedWittVector p 2 A where
  toFun x := TruncatedWittVector.mk p fun i => if i = 0 then x else delta p x
  map_zero' := by
    ext i
    fin_cases i <;> simp
  map_one' := by
    ext i
    fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i <;>
      simp [TruncatedWittVector.add_coeff_one, delta_add]
  map_mul' x y := by
    ext i
    fin_cases i <;>
      simp [TruncatedWittVector.mul_coeff_one, delta_mul]

/-- The zeroth coordinate of the Witt section is the original element. -/
-- Evaluate before a ring-homomorphism numeral rule erases the section application.
@[simp↓]
theorem wittSection_coeff_zero (x : A) : (wittSection p A x).coeff 0 = x := (rfl)

/-- The first coordinate of the Witt section is the delta operation. -/
@[simp↓]
theorem wittSection_coeff_one (x : A) : (wittSection p A x).coeff 1 = delta p x := (rfl)

/-- The Witt section is a section of the zeroth-coordinate ring homomorphism. -/
@[simp]
theorem constantCoeff_comp_wittSection :
    (TruncatedWittVector.constantCoeff (p := p)).comp (wittSection p A) = RingHom.id A := by
  ext x
  simp [TruncatedWittVector.constantCoeff_apply]

/-- The ghost component at index one of the Witt section is the delta-ring Frobenius lift. -/
@[simp]
theorem ghostComponentOne_comp_wittSection :
    (TruncatedWittVector.ghostComponentOne (p := p)).comp (wittSection p A) =
      frobenius p A := by
  ext x
  simp [TruncatedWittVector.ghostComponentOne_apply, frobenius_apply]

end Section

/-- Over any commutative ring, delta structures are equivalent to ring sections of the zeroth
coordinate on length-two Witt vectors (Bhatt–Scholze, Remark 2.4). -/
noncomputable def equivWittSection : DeltaRing p A ≃
    {s : A →+* TruncatedWittVector p 2 A //
      (TruncatedWittVector.constantCoeff (p := p)).comp s = RingHom.id A} where
  toFun d := letI := d; ⟨wittSection p A, constantCoeff_comp_wittSection p A⟩
  invFun s := by
    have hs (x : A) : (s.val x).coeff 0 = x := by
      simpa [TruncatedWittVector.constantCoeff_apply] using DFunLike.congr_fun s.property x
    refine
      { delta := fun x => (s.val x).coeff 1
        delta_zero := by simp
        delta_one := by simp
        delta_add := ?_
        delta_mul := ?_ }
    · intro x y
      simp [TruncatedWittVector.add_coeff_one, hs]
    · intro x y
      simp [TruncatedWittVector.mul_coeff_one, hs]
  left_inv d := by
    ext x
    rfl
  right_inv s := by
    apply Subtype.ext
    ext x i
    fin_cases i
    · simpa [TruncatedWittVector.constantCoeff_apply] using
        (DFunLike.congr_fun s.property x).symm
    · rfl

/-- The equivalence sends a delta structure to its Witt section. -/
@[simp]
theorem equivWittSection_apply (d : DeltaRing p A) :
    (equivWittSection p A d).val = @wittSection p A _ _ d := (rfl)

/-- The inverse equivalence recovers the first Witt coordinate as the delta operation. -/
@[simp]
theorem delta_equivWittSection_symm
    (s : {s : A →+* TruncatedWittVector p 2 A //
      (TruncatedWittVector.constantCoeff (p := p)).comp s = RingHom.id A}) (x : A) :
    @delta p A _ ((equivWittSection p A).symm s) x = (s.val x).coeff 1 := (rfl)

end TauCeti.DeltaRing
