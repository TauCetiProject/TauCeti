/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.LinearAlgebra.Graded.ExtendByZero

/-!
# The integer grading of an exterior algebra

The exterior algebra `Λ_R M` is graded by exterior degree, with pieces the exterior powers
`⋀[R]^n M`; Mathlib records this as an `ℕ`-graded algebra.  Extending by zero in negative degrees
gives the cohomological `ℤ`-grading (`TauCeti.ExteriorAlgebra.integerGrading`), in which the
generators `ι R m` have degree one.

For this grading the grade involution is the sign `(-1) ^ p` on the piece of degree `p`, a
contraction lowers the degree by one, and left multiplication by a generator raises it by one.

## Main definitions

* `TauCeti.ExteriorAlgebra.integerGrading`: the `ℤ`-grading of `Λ_R M` by exterior degree.
* `TauCeti.ExteriorAlgebra.integerGradedAlgebra`: `Λ_R M` as a `ℤ`-graded algebra.

## Main results

* `TauCeti.ExteriorAlgebra.involute_of_mem_integerGrading`: the grade involution is `p.negOnePow`
  on the piece of degree `p`.
* `TauCeti.ExteriorAlgebra.contractLeft_mem_integerGrading`: contraction has degree `-1`.
* `TauCeti.ExteriorAlgebra.ι_mul_mem_integerGrading`: left multiplication by a generator has
  degree one.
-/

public section

open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

variable (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The cohomological `ℤ`-grading of the exterior algebra by exterior degree: the `n`-th exterior
power in degree `n ≥ 0`, and zero in negative degrees. -/
def integerGrading : ℤ → Submodule R (ExteriorAlgebra R M) :=
  Graded.extendByZero fun n : ℕ ↦ ⋀[R]^n M

/-- The exterior algebra is a `ℤ`-graded algebra for `integerGrading`, as the extension by zero of
the exterior powers. -/
@[instance_reducible]
noncomputable def integerGradedAlgebra : GradedAlgebra (integerGrading R M) :=
  Graded.gradedAlgebraExtendByZero _

attribute [instance] integerGradedAlgebra

variable {R M}

/-- In a nonnegative degree the integer grading is the exterior power. -/
@[simp]
theorem integerGrading_natCast (n : ℕ) : integerGrading R M n = ⋀[R]^n M :=
  Graded.extendByZero_natCast _ n

/-- The integer grading vanishes in negative degrees. -/
theorem integerGrading_of_neg {p : ℤ} (hp : p < 0) : integerGrading R M p = ⊥ :=
  Graded.extendByZero_of_neg _ hp

/-- The generators have degree one. -/
theorem ι_mem_integerGrading_one (m : M) : ExteriorAlgebra.ι R m ∈ integerGrading R M 1 := by
  rw [← Nat.cast_one, integerGrading_natCast, _root_.ExteriorAlgebra.exteriorPower, pow_one]
  exact LinearMap.mem_range_self _ _

/-- **The grade involution acts on the piece of degree `p` by `(-1) ^ p`.** -/
theorem involute_of_mem_integerGrading {p : ℤ} {x : ExteriorAlgebra R M}
    (hx : x ∈ integerGrading R M p) :
    involute (Q := (0 : QuadraticForm R M)) x = p.negOnePow • x := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [integerGrading_of_neg hp, Submodule.mem_bot] at hx
    simp [hx]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [integerGrading_natCast] at hx
  rw [involute_of_mem_exteriorPower hx]
  simp [Int.negOnePow_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R]

/-- **Contraction lowers the degree by one.** -/
theorem contractLeft_mem_integerGrading (d : Module.Dual R M) {p : ℤ} {x : ExteriorAlgebra R M}
    (hx : x ∈ integerGrading R M p) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ integerGrading R M (p - 1) := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [integerGrading_of_neg hp, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [integerGrading_natCast] at hx
  rcases n with _ | n
  · rw [contractLeft_eq_zero_of_mem_exteriorPower_zero _ hx]
    exact zero_mem _
  · rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring, integerGrading_natCast]
    exact contractLeft_mem_exteriorPower _ hx

/-- **Left multiplication by a generator raises the degree by one.** -/
theorem ι_mul_mem_integerGrading (m : M) {p : ℤ} {x : ExteriorAlgebra R M}
    (hx : x ∈ integerGrading R M p) :
    ExteriorAlgebra.ι R m * x ∈ integerGrading R M (p + 1) := by
  rw [add_comm]
  exact SetLike.mul_mem_graded (ι_mem_integerGrading_one m) hx

end TauCeti.ExteriorAlgebra
