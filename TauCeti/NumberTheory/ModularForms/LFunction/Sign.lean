/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LFunction.FunctionalEquation
public import TauCeti.NumberTheory.ModularForms.Newforms.AnalyticInvariants
public import TauCeti.NumberTheory.ModularForms.Newforms.Fricke
import TauCeti.NumberTheory.ModularForms.Parity

/-!
# The sign of the functional equation

Hecke's functional equation relates the completed L-function of a cusp form `f` of level `Γ₁(N)`
to that of its Petersson-normalized Fricke companion: `Λ_N(k - s, f) = i^k Λ_N(s, 𝒲_N f)`, a
relation between *two* forms. When `f` is an eigenvector of the normalized Fricke operator,
`𝒲_N f = ε • f`, the companion is `f` again up to the scalar `ε`, and the relation becomes a
functional equation for `Λ_N(·, f)` alone, with **sign** `i^k ε`.

On a newform of trivial nebentypus the eigenvalue is the Fricke sign `ε_N(f) ∈ {1, -1}` and the
weight is even, so the sign of the functional equation is `i^k ε_N(f)`, again `1` or `-1`. A sign
different from `1` forces the completed L-function to vanish at the central point `s = k / 2`,
and hence makes the analytic rank of the newform positive.

## Main results

* `CuspForm.frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul`: the one-form
  functional equation `Λ_N(k - s, f) = i^k ε Λ_N(s, f)` on a Fricke eigenvector.
* `CuspForm.Λ_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul`: the same equation for Mathlib's
  `ModularForm.Λ`, where the change of normalization contributes a factor `N ^ (s - k / 2)`.
* `CuspForm.Λ_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul`,
  `CuspForm.L_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul`: a sign different from `1` kills
  the central value of the completed and of the ordinary L-function.
* `HeckeRing.GL2.Newform.frickeCompletedL_sub_eq`: the functional equation of a newform of
  trivial nebentypus, with sign `i^k ε_N(f)`.
* `HeckeRing.GL2.Newform.I_zpow_mul_frickeSign_eq_one_or_neg_one`: that sign is `1` or `-1`.
* `HeckeRing.GL2.Newform.analyticRank_pos_of_I_zpow_mul_frickeSign_ne_one`: a sign different
  from `1` makes the analytic rank positive.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.10.2.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.3.5.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace CuspForm

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {ε : ℂ}

/-! ### The functional equation of a Fricke eigenvector -/

/-- **The one-form functional equation.** If a cusp form of level `Γ₁(N)` and positive weight `k`
is an eigenvector of the normalized Fricke operator with eigenvalue `ε`, then its level-`N`
completed L-function satisfies

`Λ_N(k - s, f) = i^k ε Λ_N(s, f)`.

The sign of the functional equation is therefore `i^k ε`; the factor `i^k` comes from the
two-form equation `frickeCompletedL_functional_equation_gamma1`. -/
theorem frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul (hk : 0 < k)
    (hε : normalizedFrickeOperatorCusp k f = ε • f) (s : ℂ) :
    frickeCompletedL f (N.toPNat (NeZero.pos N)) ((k : ℂ) - s) =
      Complex.I ^ k * ε * frickeCompletedL f (N.toPNat (NeZero.pos N)) s := by
  rw [frickeCompletedL_functional_equation_gamma1 f hk s, hε, frickeCompletedL_smul, mul_assoc]

/-- **The functional equation in Mathlib's normalization.** For a Fricke eigenvector with
eigenvalue `ε`, Mathlib's completed L-function satisfies

`Λ(k - s, f) = i^k ε N^(s - k/2) Λ(s, f)`,

the level-dependent factor `N^(s - k/2)` being what distinguishes `ModularForm.Λ` from the
level-`N` completion `Λ_N = N^(s/2) Λ`; it is `1` at the central point `s = k / 2`. -/
theorem Λ_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul (hk : 0 < k)
    (hε : normalizedFrickeOperatorCusp k f = ε • f) (s : ℂ) :
    ModularForm.Λ hk f ((k : ℂ) - s) =
      Complex.I ^ k * ε * (N : ℂ) ^ (s - (k : ℂ) / 2) * ModularForm.Λ hk f s := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hA : (N : ℂ) ^ (((k : ℂ) - s) / 2) ≠ 0 :=
    fun h ↦ hN ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have h := frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul f hk hε s
  -- `Nat.toPNat` is the subtype constructor, so its coercion back to `ℕ` is definitional; there
  -- is no `Nat.toPNat_coe` in Mathlib to rewrite with.
  rw [frickeCompletedL_eq_cpow_mul_Λ f (N.toPNat (NeZero.pos N)) hk,
    frickeCompletedL_eq_cpow_mul_Λ f (N.toPNat (NeZero.pos N)) hk,
    show ((N.toPNat (NeZero.pos N) : ℕ+) : ℕ) = N from rfl] at h
  have hexponent : ((k : ℂ) - s) / 2 + (s - (k : ℂ) / 2) = s / 2 := by ring
  have hcpow : (N : ℂ) ^ (s / 2) =
      (N : ℂ) ^ (((k : ℂ) - s) / 2) * (N : ℂ) ^ (s - (k : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hN, hexponent]
  refine mul_left_cancel₀ hA (h.trans ?_)
  rw [hcpow]
  ring

/-! ### Vanishing at the central point -/

/-- **The central point of a functional equation with sign different from `1`.** The central
point `s = k / 2` is the fixed point of `s ↦ k - s`, so the functional equation reads
`Λ_N(k/2, f) = i^k ε Λ_N(k/2, f)` there; unless the sign `i^k ε` is `1`, the value vanishes. -/
theorem frickeCompletedL_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul (hk : 0 < k)
    (hε : normalizedFrickeOperatorCusp k f = ε • f) (hsign : Complex.I ^ k * ε ≠ 1) :
    frickeCompletedL f (N.toPNat (NeZero.pos N)) ((k : ℂ) / 2) = 0 := by
  have h := frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul f hk hε ((k : ℂ) / 2)
  have hcenter : (k : ℂ) - (k : ℂ) / 2 = (k : ℂ) / 2 := by ring
  rw [hcenter] at h
  exact (mul_left_eq_self₀.mp h.symm).resolve_left hsign

/-- **Mathlib's completed L-function vanishes at the central point** when the sign of the
functional equation is different from `1`: the central point is the fixed point of `s ↦ k - s`,
where the normalization factor `N ^ (s - k / 2)` is `1`. -/
theorem Λ_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul (hk : 0 < k)
    (hε : normalizedFrickeOperatorCusp k f = ε • f) (hsign : Complex.I ^ k * ε ≠ 1) :
    ModularForm.Λ hk f ((k : ℂ) / 2) = 0 := by
  have h := Λ_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul f hk hε ((k : ℂ) / 2)
  have hcenter : (k : ℂ) - (k : ℂ) / 2 = (k : ℂ) / 2 := by ring
  rw [hcenter, sub_self, Complex.cpow_zero, mul_one] at h
  exact (mul_left_eq_self₀.mp h.symm).resolve_left hsign

/-- **The central value of the L-function vanishes** when the sign of the functional equation is
different from `1`. -/
theorem L_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul (hk : 0 < k)
    (hε : normalizedFrickeOperatorCusp k f = ε • f) (hsign : Complex.I ^ k * ε ≠ 1) :
    ModularForm.L hk f ((k : ℂ) / 2) = 0 := by
  -- Mathlib offers no lemma for `L = Λ * (2 / Gammaℂ)`, so the definition is unfolded here.
  unfold ModularForm.L
  rw [Λ_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul f hk hε hsign, zero_mul]

end CuspForm

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ### The functional equation of a newform of trivial nebentypus -/

/-- **The functional equation of a newform of trivial nebentypus**, with sign `i^k ε_N(f)` for
`ε_N(f)` the Fricke sign:

`Λ_N(k - s, f) = i^k ε_N(f) Λ_N(s, f)`. -/
theorem frickeCompletedL_sub_eq (f : Newform N k) (hχ : f.χ = 1) (hk : 0 < k) (s : ℂ) :
    CuspForm.frickeCompletedL f.toCuspForm (N.toPNat (NeZero.pos N)) ((k : ℂ) - s) =
      Complex.I ^ k * f.frickeSign hχ *
        CuspForm.frickeCompletedL f.toCuspForm (N.toPNat (NeZero.pos N)) s :=
  CuspForm.frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul f.toCuspForm hk
    (f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ) s

/-- **The sign of the functional equation of a newform of trivial nebentypus is `1` or `-1`.**
A nonzero form with trivial nebentypus has even weight, so `i^k` is `(-1) ^ (k / 2)`, and the
Fricke sign is itself `± 1`. -/
theorem I_zpow_mul_frickeSign_eq_one_or_neg_one (f : Newform N k) (hχ : f.χ = 1) :
    Complex.I ^ k * f.frickeSign hχ = 1 ∨ Complex.I ^ k * f.frickeSign hχ = -1 := by
  obtain ⟨m, hm⟩ := even_of_mem_cuspFormCharSpace_one (hχ ▸ f.mem_charSpace) f.ne_zero
  have hI : Complex.I ^ k = (-1 : ℂ) ^ m := by
    rw [hm, ← two_mul m, zpow_mul, zpow_two, Complex.I_mul_I]
  rcases f.frickeSign_eq_one_or_neg_one hχ with hε | hε <;>
    rcases Int.even_or_odd m with hpar | hpar <;>
    simp [hI, hε, hpar.neg_one_zpow]

/-! ### Positive analytic rank -/

/-- **A newform of trivial nebentypus whose functional equation has sign different from `1` has
positive analytic rank**: its L-function vanishes at the central point `s = k / 2`. -/
theorem analyticRank_pos_of_I_zpow_mul_frickeSign_ne_one (f : Newform N k) (hχ : f.χ = 1)
    (hk : 0 < k) (hsign : Complex.I ^ k * f.frickeSign hχ ≠ 1) :
    0 < f.analyticRank hk :=
  (f.analyticRank_pos_iff hk).mpr
    (CuspForm.L_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul f.toCuspForm hk
      (f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ) hsign)

end HeckeRing.GL2.Newform
