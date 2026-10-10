/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Torsion
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Symbol

/-!
# Kummer-cup Brauer classes

A primitive root of unity selects a pairing on Kummer coefficients. The cup of two Kummer
classes, followed by the coefficient inclusion into the Brauer group, defines `kummerBrauerClass`.
This file records its bilinearity, torsion and Steinberg relation.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, (6.2.1).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

universe u

variable {K : Type u} [Field K]

variable {n : ℕ} [NeZero n] (ζ : K) (hζ : IsPrimitiveRoot ζ n)

/-- The Brauer class of the cup of two Kummer classes, using the pairing selected by `ζ`. -/
def kummerBrauerClass (a b : Kˣ) : Br K :=
  h2MuToBr n K ((kummerCupPairing ζ hζ).cup 1 1
    (kummerClass K hζ.neZero'.out.isUnit a) (kummerClass K hζ.neZero'.out.isUnit b))

/-- The Kummer-cup Brauer class is the canonical cup followed by the coefficient inclusion. -/
theorem kummerBrauerClass_def (a b : Kˣ) :
    kummerBrauerClass ζ hζ a b =
      h2MuToBr n K ((kummerCupPairing ζ hζ).cup 1 1
        (kummerClass K hζ.neZero'.out.isUnit a) (kummerClass K hζ.neZero'.out.isUnit b)) :=
  (rfl)

/-- The argument `1` on the left gives the zero Brauer class. -/
@[simp]
theorem kummerBrauerClass_one_left (b : Kˣ) : kummerBrauerClass ζ hζ 1 b = 0 := by
  simp [kummerBrauerClass_def]

/-- The argument `1` on the right gives the zero Brauer class. -/
@[simp]
theorem kummerBrauerClass_one_right (a : Kˣ) : kummerBrauerClass ζ hζ a 1 = 0 := by
  simp [kummerBrauerClass_def]

/-- The Kummer-cup Brauer class is additive in its first unit argument. -/
theorem kummerBrauerClass_mul_left (a a' b : Kˣ) :
    kummerBrauerClass ζ hζ (a * a') b =
      kummerBrauerClass ζ hζ a b + kummerBrauerClass ζ hζ a' b := by
  simp [kummerBrauerClass_def, kummerClass_mul, LinearMap.add_apply]

/-- The Kummer-cup Brauer class is additive in its second unit argument. -/
theorem kummerBrauerClass_mul_right (a b b' : Kˣ) :
    kummerBrauerClass ζ hζ a (b * b') =
      kummerBrauerClass ζ hζ a b + kummerBrauerClass ζ hζ a b' := by
  simp [kummerBrauerClass_def, kummerClass_mul]

/-- The Kummer-cup Brauer class is killed by its exponent. -/
theorem nsmul_kummerBrauerClass_eq_zero (a b : Kˣ) : n • kummerBrauerClass ζ hζ a b = 0 :=
  (h2MuToBr_range n K hζ.neZero'.out.isUnit _).mp ⟨_, kummerBrauerClass_def ζ hζ a b |>.symm⟩

/-- The Kummer-cup Brauer class satisfies the Steinberg relation. -/
theorem kummerBrauerClass_eq_zero_of_add_eq_one {a b : Kˣ} (hab : (a : K) + b = 1) :
    kummerBrauerClass ζ hζ a b = 0 := by
  rw [kummerBrauerClass_def,
    cup_kummerClass_eq_zero_of_add_eq_one _ hζ.neZero'.out.isUnit hab, map_zero]

end TauCeti.ClassFieldTheory
