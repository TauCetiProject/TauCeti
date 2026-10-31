/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Expand
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
import Mathlib.NumberTheory.Basic
import TauCeti.RingTheory.MvPowerSeries.Expand
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Hazewinkel's functional equation lemma

Let `A` be a subring of a commutative ring `K`, let `p` be a prime, let `σ` be a ring endomorphism
of `K` that maps `A` into itself and lifts the Frobenius of `A / p A`, so that
`σ(a) ≡ a ^ p` modulo `p A` for `a ∈ A`, and let `s₁, s₂, …` be elements of `K` with `p sᵢ ∈ A`. A
power series `h` over `K` satisfies the *functional equation* if

  `h(X) - ∑_{i ≥ 1} sᵢ (σⁱ h)(X ^ (pⁱ)) ∈ A⟦X⟧`,

where `σⁱ h` applies `σⁱ` to the coefficients of `h`. Hazewinkel's functional equation lemma
says that if a power series `f = b₁ X + ⋯` in one variable, with `b₁` a unit of `A`, satisfies the
functional equation, then the formal group law `f⁻¹(f(X) + f(Y))` with logarithm `f` has all its
coefficients in `A`, although the coefficients of `f` itself have denominators.

The proof characterises the integral series of zero constant coefficient as those `ψ` for which
`f(ψ)` satisfies the functional equation (`TauCeti.satisfiesFunctionalEquation_subst_iff`). For
integral `ψ`, the defect of `f(ψ)` is computed from that of `f`: it differs by the terms
`sᵢ σⁱ(bₘ) (ψ ^ (pⁱ m) - (σⁱ ψ)(X ^ (pⁱ)) ^ m)`, and these are integral because
`ψ ^ (pⁱ) ≡ (σⁱ ψ)(X ^ (pⁱ))` modulo `p` while `p ^ (vₚ(m)) bₘ ∈ A`. Conversely the lowest
nonintegral coefficient of `ψ` would reappear, multiplied by `b₁`, in the defect of `f(ψ)`. The
formal group law `F = f⁻¹(f(X) + f(Y))` has `f(F) = f(X) + f(Y)`, whose defect is the sum of the
integral defects of `f(X)` and `f(Y)`.

With `A = ℤ_(p)[v₁, v₂, …]` inside `K = ℚ[v₁, v₂, …]`, `σ(vᵢ) = vᵢ ^ p` and `sᵢ = vᵢ / p`, the
lemma shows that the logarithm defined by Hazewinkel's recursion `p mₙ = ∑ vᵢ σⁱ(m_(n - i))` is
the logarithm of a formal group law over `ℤ_(p)[v₁, v₂, …]`. With `σ = id` and a single nonzero
`sₕ = 1 / p` it gives the formal group law over `ℤ_(p)` with logarithm `∑ₖ X ^ (p ^ (h k)) / pᵏ`.

## Main definitions

* `TauCeti.functionalEquationSum p σ s`: the twisted sum `h ↦ ∑_{i ≥ 1} sᵢ (σⁱ h)(X ^ (pⁱ))`.
* `TauCeti.SatisfiesFunctionalEquation p σ s A h`: `h` satisfies the functional equation, that is
  `h - ∑_{i ≥ 1} sᵢ (σⁱ h)(X ^ (pⁱ))` has coefficients in `A`.

## Main results

* `TauCeti.SatisfiesFunctionalEquation.natCast_pow_factorization_mul_coeff_mem`: a solution `f`
  of the functional equation has `p ^ (vₚ(n)) fₙ ∈ A`.
* `TauCeti.satisfiesFunctionalEquation_subst_iff`: for a solution `f = b₁ X + ⋯` with `b₁` a
  unit of `A` and `ψ` of zero constant coefficient, `f(ψ)` satisfies the functional equation if
  and only if `ψ` has coefficients in `A`.
* `TauCeti.coeff_inv_smul_𝔾ₐ_toPowerSeries_mem`: **Hazewinkel's functional equation lemma**, the
  formal group law `f⁻¹(f(X) + f(Y))` has coefficients in `A`.

## References

* M. Hazewinkel, *Formal Groups and Applications*, Chapter I, §2 (the functional equation lemma).
-/

public section

open MvPowerSeries

namespace TauCeti

variable {K : Type*} [CommRing K] {τ : Type*}

section Def

variable (p : ℕ) [NeZero p] (σ : K →+* K) (s : ℕ → K)

/-- The twisted sum `h ↦ ∑_{i ≥ 1} sᵢ (σⁱ h)(X ^ (pⁱ))` of the functional equation, where `σⁱ h`
applies `σⁱ` to the coefficients of `h`. It is defined degree by degree: the coefficient of `X^d`
sums over `1 ≤ i ≤ |d|`. For `d ≠ 0` the terms with `i > |d|` vanish, because `pⁱ > |d|` cannot
divide a nonzero exponent of `X^d`, so this is the infinite sum in every nonzero degree; in degree
zero it is `0`, which is the value of the infinite sum when `h` has zero constant coefficient. -/
noncomputable def functionalEquationSum : MvPowerSeries τ K →+ MvPowerSeries τ K where
  toFun h d := ∑ i ∈ Finset.Icc 1 d.degree,
    s i * coeff d (expand (p ^ i) (NeZero.ne _) (map (σ ^ i) h))
  map_zero' := by ext d; simp; rfl
  map_add' h₁ h₂ := by ext d; simp [mul_add, Finset.sum_add_distrib]; rfl

/-- The coefficient of `X^d` in `∑_{i ≥ 1} sᵢ (σⁱ h)(X ^ (pⁱ))`. -/
theorem coeff_functionalEquationSum (h : MvPowerSeries τ K) (d : τ →₀ ℕ) :
    coeff d (functionalEquationSum p σ s h) = ∑ i ∈ Finset.Icc 1 d.degree,
      s i * coeff d (expand (p ^ i) (NeZero.ne _) (map (σ ^ i) h)) :=
  (rfl)

/-- In one variable, the coefficient of `Xⁿ` in `∑_{i ≥ 1} sᵢ (σⁱ f)(X ^ (pⁱ))` is the sum of
`sᵢ σⁱ(f_(n / pⁱ))` over the `1 ≤ i ≤ n` with `pⁱ ∣ n`. -/
theorem powerSeries_coeff_functionalEquationSum (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (functionalEquationSum p σ s f : PowerSeries K) =
      ∑ i ∈ Finset.Icc 1 n,
        s i * if p ^ i ∣ n then (σ ^ i) (PowerSeries.coeff (n / p ^ i) f) else 0 := by
  rw [PowerSeries.coeff_def Finsupp.single_eq_same, coeff_functionalEquationSum,
    Finsupp.degree_single]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- `PowerSeries.expand` and `PowerSeries.map` are the multivariate operations in one variable
  have : expand (p ^ i) (NeZero.ne _) (map (σ ^ i) f) =
      PowerSeries.expand (p ^ i) (NeZero.ne _) (PowerSeries.map (σ ^ i) f) := (rfl)
  rw [this, ← PowerSeries.coeff_def Finsupp.single_eq_same, PowerSeries.coeff_expand,
    PowerSeries.coeff_map]

/-- `h` satisfies the **functional equation** for `(p, σ, s)` relative to the subring `A`:
`h - ∑_{i ≥ 1} sᵢ (σⁱ h)(X ^ (pⁱ))` has all its coefficients in `A`. -/
def SatisfiesFunctionalEquation (A : Subring K) (h : MvPowerSeries τ K) : Prop :=
  ∀ d, coeff d (h - functionalEquationSum p σ s h) ∈ A

variable {p σ s} {A : Subring K}

/-- Solutions of the functional equation are closed under addition. -/
theorem SatisfiesFunctionalEquation.add {h₁ h₂ : MvPowerSeries τ K}
    (h₁' : SatisfiesFunctionalEquation p σ s A h₁) (h₂' : SatisfiesFunctionalEquation p σ s A h₂) :
    SatisfiesFunctionalEquation p σ s A (h₁ + h₂) := fun d ↦ by
  simpa [map_add, add_sub_add_comm] using add_mem (h₁' d) (h₂' d)

end Def

section Integrality

variable {p : ℕ} [hp : Fact p.Prime] {σ : K →+* K} {s : ℕ → K} {A : Subring K}

omit hp in
private theorem mapsTo_pow (hσ : Set.MapsTo σ A A) (i : ℕ) : Set.MapsTo ⇑(σ ^ i) A A := by
  rw [RingHom.coe_pow]
  exact hσ.iterate i

/-- **Denominators of a solution of the functional equation.** If `f` satisfies the functional
equation, then `p ^ (vₚ(n)) fₙ ∈ A` for the coefficient `fₙ` of `Xⁿ`. -/
theorem SatisfiesFunctionalEquation.natCast_pow_factorization_mul_coeff_mem
    (hσ : Set.MapsTo σ A A) (hs : ∀ i, (p : K) * s i ∈ A) {f : PowerSeries K}
    (hf : SatisfiesFunctionalEquation p σ s A f) (n : ℕ) :
    (p : K) ^ n.factorization p * PowerSeries.coeff n f ∈ A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have key := hf (Finsupp.single () n)
  rw [← PowerSeries.coeff_def Finsupp.single_eq_same, map_sub,
    powerSeries_coeff_functionalEquationSum] at key
  set r := n.factorization p
  have hsplit : (p : K) ^ r * PowerSeries.coeff n f =
      (p : K) ^ r * (PowerSeries.coeff n f - ∑ i ∈ Finset.Icc 1 n,
        s i * if p ^ i ∣ n then (σ ^ i) (PowerSeries.coeff (n / p ^ i) f) else 0) +
      ∑ i ∈ Finset.Icc 1 n,
        (p : K) ^ r *
          (s i * if p ^ i ∣ n then (σ ^ i) (PowerSeries.coeff (n / p ^ i) f) else 0) := by
    rw [← Finset.mul_sum, ← mul_add, sub_add_cancel]
  rw [hsplit]
  refine add_mem (mul_mem (pow_mem (natCast_mem A p) r) key) (Subring.sum_mem _ fun i hi ↦ ?_)
  split_ifs with hdvd
  · obtain ⟨hi₁, hin⟩ := Finset.mem_Icc.mp hi
    have hn : n ≠ 0 := by omega
    have hir : i ≤ r := (hp.out.pow_dvd_iff_le_factorization hn).mp hdvd
    have hlt : n / p ^ i < n := Nat.div_lt_self (by omega) (Nat.one_lt_pow (by omega) hp.out.one_lt)
    have hfac : (n / p ^ i).factorization p = r - i := by
      simp [r, Nat.factorization_div hdvd, hp.out.factorization_self]
    have hmem := mapsTo_pow hσ i (ih _ hlt)
    rw [hfac, map_mul, map_pow, map_natCast] at hmem
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hir
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi₁
    rw [hk, Nat.add_sub_cancel_left] at hmem
    have : (p : K) ^ r * (s (j + 1) * (σ ^ (j + 1)) (PowerSeries.coeff (n / p ^ (j + 1)) f)) =
        (p : K) ^ j * ((p : K) * s (j + 1)) *
          ((p : K) ^ k * (σ ^ (j + 1)) (PowerSeries.coeff (n / p ^ (j + 1)) f)) := by
      rw [hk]; ring
    rw [this]
    exact mul_mem (mul_mem (pow_mem (natCast_mem A p) j) (hs _)) hmem
  · simp

omit hp in
private theorem natCast_dvd_restrict_pow_sub (hσ : Set.MapsTo σ A A)
    (hσp : ∀ a ∈ A, ∃ b ∈ A, σ a - a ^ p = p * b) (i : ℕ) (a : A) :
    (p : A) ∣ ((σ.restrict A A fun _ h ↦ hσ h) ^ i) a - a ^ p ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    set y := ((σ.restrict A A fun _ h ↦ hσ h) ^ i) a
    obtain ⟨b, hb, hb'⟩ := hσp y y.2
    have h₁ : (p : A) ∣ (σ.restrict A A fun _ h ↦ hσ h) y - y ^ p :=
      ⟨⟨b, hb⟩, Subtype.ext (by simpa using hb')⟩
    have h₂ : (p : A) ∣ y ^ p - (a ^ p ^ i) ^ p := ih.trans (sub_dvd_pow_sub_pow _ _ _)
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, pow_succ, pow_mul]
    have := dvd_add h₁ h₂
    rwa [sub_add_sub_cancel] at this

private theorem coe_restrict_pow_apply (hσ : Set.MapsTo σ A A) (i : ℕ) (a : A) :
    (((σ.restrict A A fun _ h ↦ hσ h) ^ i) a : K) = (σ ^ i) a := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, RingHom.coe_restrict_apply, ih,
      pow_succ', RingHom.mul_def, RingHom.comp_apply]

/-- Substituting `ψ` into `∑_{i ≥ 1} sᵢ (σⁱ f)(X ^ (pⁱ))` substitutes `ψ ^ (pⁱ)` into `σⁱ f`. -/
private theorem coeff_subst_functionalEquationSum {f : PowerSeries K}
    (hf₀ : PowerSeries.constantCoeff f = 0) {ψ : MvPowerSeries τ K} (hψ₀ : constantCoeff ψ = 0)
    (d : τ →₀ ℕ) :
    coeff d (PowerSeries.subst ψ (functionalEquationSum p σ s f : PowerSeries K)) =
      ∑ i ∈ Finset.Icc 1 d.degree,
        s i * coeff d ((PowerSeries.map (σ ^ i) f).subst (ψ ^ p ^ i)) := by
  have hR (i : ℕ) : coeff d ((PowerSeries.map (σ ^ i) f).subst (ψ ^ p ^ i)) =
      ∑ n ∈ Finset.range (d.degree + 1),
        (if p ^ i ∣ n then (σ ^ i) (PowerSeries.coeff (n / p ^ i) f) else 0) *
          coeff d (ψ ^ n) := by
    rw [← PowerSeries.subst_expand (p ^ i) (NeZero.ne _) (.of_constantCoeff_zero hψ₀),
      PowerSeries.coeff_subst_eq_sum_range hψ₀]
    simp_rw [smul_eq_mul, PowerSeries.coeff_expand, PowerSeries.coeff_map]
  simp_rw [hR, PowerSeries.coeff_subst_eq_sum_range hψ₀, smul_eq_mul, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [powerSeries_coeff_functionalEquationSum]
  -- the terms with `n < i` vanish, as then `pⁱ ∤ n` unless `n = 0`
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))) fun i hi hni ↦ ?_
  have hlt : n < p ^ i := by
    simp only [Finset.mem_Icc, not_and, not_le] at hi hni
    exact (hni hi.1).trans (Nat.lt_pow_self hp.out.one_lt)
  split_ifs with hdvd
  · rw [Nat.eq_zero_of_dvd_of_lt hdvd hlt, Nat.zero_div,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf₀, map_zero, mul_zero]
  · rw [mul_zero]

/-- For integral `ψ`, the term `sᵢ σⁱ(fₘ) (ψ ^ (pⁱ m) - (σⁱ ψ)(X ^ (pⁱ)) ^ m)` is integral:
`ψ ^ (pⁱ) ≡ (σⁱ ψ)(X ^ (pⁱ))` modulo `p`, so the difference of `m`-th powers is divisible by
`p ^ (vₚ(m) + 1)`, which cancels the denominators of `sᵢ` and `fₘ`. -/
private theorem mul_coeff_pow_sub_expand_pow_mem (hσ : Set.MapsTo σ A A)
    (hσp : ∀ a ∈ A, ∃ b ∈ A, σ a - a ^ p = p * b) (hs : ∀ i, (p : K) * s i ∈ A)
    {f : PowerSeries K} (hf : SatisfiesFunctionalEquation p σ s A f) {ψ : MvPowerSeries τ K}
    (hψ : ∀ d, coeff d ψ ∈ A) (i m : ℕ) (d : τ →₀ ℕ) :
    s i * ((σ ^ i) (PowerSeries.coeff m f) *
      coeff d ((ψ ^ p ^ i) ^ m - expand (p ^ i) (NeZero.ne _) (map (σ ^ i) ψ) ^ m)) ∈ A := by
  -- the congruence holds over `A`
  let ψA : MvPowerSeries τ A := fun e ↦ ⟨coeff e ψ, hψ e⟩
  have hψA : map A.subtype ψA = ψ := ext fun e ↦ rfl
  set U := ψA ^ p ^ i
  set W := expand (p ^ i) (NeZero.ne _) (map ((σ.restrict A A fun _ h ↦ hσ h) ^ i) ψA)
  have hU : map A.subtype U = ψ ^ p ^ i := by rw [map_pow, hψA]
  have hW : map A.subtype W = expand (p ^ i) (NeZero.ne _) (map (σ ^ i) ψ) := by
    have hcomp :
        A.subtype.comp ((σ.restrict A A fun _ h ↦ hσ h) ^ i) = (σ ^ i).comp A.subtype :=
      RingHom.ext (coe_restrict_pow_apply hσ i)
    rw [map_expand, map_map, hcomp, ← map_map, hψA]
  set r := m.factorization p
  obtain ⟨E, hE⟩ : (p : MvPowerSeries τ A) ^ (r + 1) ∣ U ^ m - W ^ m := by
    refine (dvd_sub_pow_of_dvd_sub (natCast_dvd_pow_sub_expand_map i
      (natCast_dvd_restrict_pow_sub hσ hσp i) ψA) r).trans ?_
    conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p, pow_mul, pow_mul]
    exact sub_dvd_pow_sub_pow _ _ _
  rw [← hU, ← hW, ← map_pow, ← map_pow, ← map_sub, hE, coeff_map,
    ← map_natCast (C (σ := τ) (R := A)), ← map_pow, coeff_C_mul, map_mul, map_pow, map_natCast]
  have hmem := mapsTo_pow hσ i (hf.natCast_pow_factorization_mul_coeff_mem hσ hs m)
  rw [map_mul, map_pow, map_natCast] at hmem
  have : s i * ((σ ^ i) (PowerSeries.coeff m f) * ((p : K) ^ (r + 1) * A.subtype (coeff d E))) =
      ((p : K) * s i) * (((p : K) ^ r * (σ ^ i) (PowerSeries.coeff m f)) *
        A.subtype (coeff d E)) := by ring
  rw [this]
  exact mul_mem (hs i) (mul_mem hmem (Subtype.mem _))

/-- If `f` satisfies the functional equation and `ψ` is an integral power series of zero constant
coefficient, in any number of variables, then `f(ψ)` satisfies the functional equation. -/
theorem SatisfiesFunctionalEquation.subst (hσ : Set.MapsTo σ A A)
    (hσp : ∀ a ∈ A, ∃ b ∈ A, σ a - a ^ p = p * b) (hs : ∀ i, (p : K) * s i ∈ A)
    {f : PowerSeries K} (hf₀ : PowerSeries.constantCoeff f = 0)
    (hf : SatisfiesFunctionalEquation p σ s A f) {ψ : MvPowerSeries τ K}
    (hψ₀ : constantCoeff ψ = 0) (hψ : ∀ d, coeff d ψ ∈ A) :
    SatisfiesFunctionalEquation p σ s A (f.subst ψ) := by
  intro d
  have hψs : PowerSeries.HasSubst ψ := .of_constantCoeff_zero hψ₀
  -- the defect `g = f - ∑ sᵢ (σⁱ f)(X ^ (pⁱ))` of `f` is integral, hence so is `g (ψ)`
  set g : PowerSeries K := f - functionalEquationSum p σ s f with hg_def
  have hT₁ : coeff d (g.subst ψ) ∈ A := by
    let ψA : MvPowerSeries τ A := fun e ↦ ⟨coeff e ψ, hψ e⟩
    let gA : PowerSeries A := fun e ↦ ⟨coeff e g, hf e⟩
    have hψA : map A.subtype ψA = ψ := ext fun e ↦ rfl
    have hgA : PowerSeries.map A.subtype gA = g := ext fun e ↦ rfl
    have hψA₀ : constantCoeff ψA = 0 := Subtype.ext hψ₀
    rw [← hgA, ← hψA, ← PowerSeries.map_subst (.of_constantCoeff_zero hψA₀), coeff_map]
    exact Subtype.mem _
  -- the twisted sum of `f (ψ)`
  have hT₃ : coeff d (functionalEquationSum p σ s (f.subst ψ)) =
      ∑ i ∈ Finset.Icc 1 d.degree, s i * coeff d ((PowerSeries.map (σ ^ i) f).subst
        (expand (p ^ i) (NeZero.ne _) (map (σ ^ i) ψ))) := by
    rw [coeff_functionalEquationSum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PowerSeries.map_subst hψs, PowerSeries.expand_subst _ _
      (.of_constantCoeff_zero (by rw [constantCoeff_map, hψ₀, map_zero]))]
  -- so the defect of `f (ψ)` is `g (ψ)` plus the terms of `mul_coeff_pow_sub_expand_pow_mem`
  have hdecomp : coeff d (f.subst ψ - functionalEquationSum p σ s (f.subst ψ)) =
      coeff d (g.subst ψ) +
        (coeff d (PowerSeries.subst ψ (functionalEquationSum p σ s f : PowerSeries K)) -
          coeff d (functionalEquationSum p σ s (f.subst ψ))) := by
    rw [hg_def, ← PowerSeries.coe_substAlgHom hψs]
    simp only [map_sub]
    ring
  rw [hdecomp, coeff_subst_functionalEquationSum hf₀ hψ₀, hT₃, ← Finset.sum_sub_distrib]
  refine add_mem hT₁ (Subring.sum_mem _ fun i _ ↦ ?_)
  have hu₀ : constantCoeff (ψ ^ p ^ i) = 0 := by rw [map_pow, hψ₀, zero_pow (NeZero.ne _)]
  have hw₀ : constantCoeff (expand (p ^ i) (NeZero.ne _) (map (σ ^ i) ψ)) = 0 := by
    rw [constantCoeff_expand, constantCoeff_map, hψ₀, map_zero]
  rw [← mul_sub, PowerSeries.coeff_subst_eq_sum_range hu₀,
    PowerSeries.coeff_subst_eq_sum_range hw₀, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Subring.sum_mem _ fun m _ ↦ ?_
  rw [PowerSeries.coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub]
  exact mul_coeff_pow_sub_expand_pow_mem hσ hσp hs hf hψ i m d

/-- If `ψ` and `ψ'` have zero constant coefficient and agree below degree `D ≥ 1`, then in degree
`D` the defects `h - ∑ sᵢ (σⁱ h)(X ^ (pⁱ))` of `h = f(ψ)` and `h = f(ψ')` differ by
`f'(0) (ψ - ψ')`: the twisted sums agree there, as `(σⁱ h)(X ^ (pⁱ))` only involves the
coefficients of `h` in degrees at most `D / pⁱ < D`. -/
private theorem coeff_sub_functionalEquationSum_subst_sub (f : PowerSeries K)
    {ψ ψ' : MvPowerSeries τ K} (hψ₀ : constantCoeff ψ = 0) (hψ'₀ : constantCoeff ψ' = 0)
    {D : ℕ} (hD₀ : 0 < D) (hε : (D : ℕ∞) ≤ (ψ - ψ').order) {d : τ →₀ ℕ} (hD : d.degree = D) :
    coeff d (f.subst ψ - functionalEquationSum p σ s (f.subst ψ)) -
        coeff d (f.subst ψ' - functionalEquationSum p σ s (f.subst ψ')) =
      PowerSeries.coeff 1 f * (coeff d ψ - coeff d ψ') := by
  -- `ψ ^ n - ψ' ^ n` is a multiple of `ψ - ψ'`, with a factor of zero constant term if `2 ≤ n`
  have hpow (n : ℕ) :
      ((D + if 2 ≤ n then 1 else 0 : ℕ) : ℕ∞) ≤ (ψ ^ n - ψ' ^ n).order := by
    rw [← geom_sum₂_mul, Nat.cast_add, add_comm]
    refine (add_le_add ?_ hε).trans le_order_mul
    split_ifs with hn
    · refine one_le_order_iff_constCoeff_eq_zero.mpr ?_
      rw [map_sum]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      rcases Nat.eq_zero_or_pos i with rfl | hi₀
      · rw [map_mul, map_pow, map_pow, hψ'₀, zero_pow (by omega), mul_zero]
      · rw [map_mul, map_pow, hψ₀, zero_pow hi₀.ne', zero_mul]
    · exact zero_le
  have hcoeff (n : ℕ) {e : τ →₀ ℕ} (he : e.degree < D + (if 2 ≤ n then 1 else 0)) :
      coeff e (ψ ^ n) - coeff e (ψ' ^ n) = 0 := by
    rw [← map_sub]
    exact coeff_of_lt_order ((Nat.cast_lt.mpr he).trans_le (hpow n))
  -- so `f (ψ)` and `f (ψ')` differ by `f'(0) (ψ - ψ')` in degree `D` and agree below
  have hsub (e : τ →₀ ℕ) : coeff e (f.subst ψ) - coeff e (f.subst ψ') =
      ∑ n ∈ Finset.range (e.degree + 1),
        PowerSeries.coeff n f * (coeff e (ψ ^ n) - coeff e (ψ' ^ n)) := by
    simp_rw [PowerSeries.coeff_subst_eq_sum_range hψ₀, PowerSeries.coeff_subst_eq_sum_range hψ'₀,
      ← Finset.sum_sub_distrib, smul_eq_mul, mul_sub]
  have hA : coeff d (f.subst ψ) - coeff d (f.subst ψ') =
      PowerSeries.coeff 1 f * (coeff d ψ - coeff d ψ') := by
    rw [hsub, Finset.sum_eq_single 1]
    · simp
    · intro n _ hn
      rcases n with _ | _ | n
      · simp
      · exact absurd rfl hn
      · rw [hcoeff (n + 2) (by simp [hD]), mul_zero]
    · intro h1
      simp [hD] at h1
      omega
  have hB : coeff d (functionalEquationSum p σ s (f.subst ψ)) -
      coeff d (functionalEquationSum p σ s (f.subst ψ')) = 0 := by
    rw [← map_sub, ← map_sub, coeff_functionalEquationSum]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi₁ : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hδ : (D : ℕ∞) ≤ (map (σ ^ i) (f.subst ψ - f.subst ψ')).order := le_order fun e he ↦ by
      rw [coeff_map, map_sub, hsub, Finset.sum_eq_zero, map_zero]
      intro n _
      rw [hcoeff n ((by exact_mod_cast he : e.degree < D).trans_le (Nat.le_add_right _ _)),
        mul_zero]
    rw [coeff_of_lt_order, mul_zero]
    rw [order_expand]
    refine lt_of_lt_of_le ?_ (nsmul_le_nsmul_right hδ _)
    rw [hD, nsmul_eq_mul]
    have : D < p ^ i * D := lt_mul_left hD₀ (Nat.one_lt_pow (by omega) hp.out.one_lt)
    exact_mod_cast this
  rw [map_sub, map_sub, sub_sub_sub_comm, hA, hB, sub_zero]

/-- Let `f = b₁ X + ⋯` satisfy the functional equation, with `b₁` a unit of `A`. If `ψ` has zero
constant coefficient and `f(ψ)` satisfies the functional equation, then `ψ` has coefficients
in `A`. -/
theorem coeff_mem_of_satisfiesFunctionalEquation_subst (hσ : Set.MapsTo σ A A)
    (hσp : ∀ a ∈ A, ∃ b ∈ A, σ a - a ^ p = p * b) (hs : ∀ i, (p : K) * s i ∈ A)
    {f : PowerSeries K} (hf₀ : PowerSeries.constantCoeff f = 0)
    (hf₁ : ∃ u ∈ A, u * PowerSeries.coeff 1 f = 1) (hf : SatisfiesFunctionalEquation p σ s A f)
    {ψ : MvPowerSeries τ K} (hψ₀ : constantCoeff ψ = 0)
    (h : SatisfiesFunctionalEquation p σ s A (f.subst ψ)) (d : τ →₀ ℕ) : coeff d ψ ∈ A := by
  obtain ⟨u, hu, hu₁⟩ := hf₁
  induction hD : d.degree using Nat.strong_induction_on generalizing d with
  | _ D ih =>
  rcases Nat.eq_zero_or_pos D with rfl | hD₀
  · rw [(Finsupp.degree_eq_zero_iff d).mp hD, coeff_zero_eq_constantCoeff_apply, hψ₀]
    exact zero_mem A
  -- the truncation `ψ'` of `ψ` below degree `D` is integral by induction, so `f (ψ')` satisfies
  -- the functional equation; comparing defects in degree `D` gives `b₁ ψ_d ∈ A`
  set ψ' : MvPowerSeries τ K := fun e ↦ if e.degree < D then coeff e ψ else 0
  have hψ'c (e : τ →₀ ℕ) : coeff e ψ' = if e.degree < D then coeff e ψ else 0 := (rfl)
  have hψ'A (e : τ →₀ ℕ) : coeff e ψ' ∈ A := by
    rw [hψ'c]
    split_ifs with he
    exacts [ih _ he e rfl, zero_mem A]
  have hψ'₀ : constantCoeff ψ' = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hψ'c, coeff_zero_eq_constantCoeff_apply, hψ₀,
      ite_self]
  have hε : (D : ℕ∞) ≤ (ψ - ψ').order := le_order fun e he ↦ by
    have he' : e.degree < D := by exact_mod_cast he
    simp [hψ'c, he']
  have hkey := coeff_sub_functionalEquationSum_subst_sub (p := p) (σ := σ) (s := s) f hψ₀ hψ'₀
    hD₀ hε hD
  simp only [hψ'c, hD, lt_self_iff_false, ↓reduceIte, sub_zero] at hkey
  rw [← one_mul (coeff d ψ), ← hu₁, mul_assoc, ← hkey]
  exact mul_mem hu (sub_mem (h d) (hf.subst hσ hσp hs hf₀ hψ'₀ hψ'A d))

/-- **Integral substitutions.** Let `f = b₁ X + ⋯` satisfy the functional equation, with `b₁` a
unit of `A`. A power series `ψ` of zero constant coefficient has coefficients in `A` if and only
if `f(ψ)` satisfies the functional equation. -/
theorem satisfiesFunctionalEquation_subst_iff (hσ : Set.MapsTo σ A A)
    (hσp : ∀ a ∈ A, ∃ b ∈ A, σ a - a ^ p = p * b) (hs : ∀ i, (p : K) * s i ∈ A)
    {f : PowerSeries K} (hf₀ : PowerSeries.constantCoeff f = 0)
    (hf₁ : ∃ u ∈ A, u * PowerSeries.coeff 1 f = 1) (hf : SatisfiesFunctionalEquation p σ s A f)
    {ψ : MvPowerSeries τ K} (hψ₀ : constantCoeff ψ = 0) :
    SatisfiesFunctionalEquation p σ s A (f.subst ψ) ↔ ∀ d, coeff d ψ ∈ A :=
  ⟨coeff_mem_of_satisfiesFunctionalEquation_subst hσ hσp hs hf₀ hf₁ hf hψ₀,
    hf.subst hσ hσp hs hf₀ hψ₀⟩

/-- **Hazewinkel's functional equation lemma.** Let `f = b₁ X + ⋯` be a formal coordinate over `K`
whose linear coefficient `b₁` is a unit of `A`, and suppose that `f` satisfies the functional
equation. Then the formal group law `f⁻¹(f(X) + f(Y))` with logarithm `f`, the transport
`f⁻¹ • 𝔾ₐ` of the additive formal group law, has all its coefficients in `A`. -/
theorem coeff_inv_smul_𝔾ₐ_toPowerSeries_mem (hσ : Set.MapsTo σ A A)
    (hσp : ∀ a ∈ A, ∃ b ∈ A, σ a - a ^ p = p * b) (hs : ∀ i, (p : K) * s i ∈ A)
    (f : FormalCoordinate K) (hf₁ : ∃ u ∈ A, u * PowerSeries.coeff 1 f.toPowerSeries = 1)
    (hf : SatisfiesFunctionalEquation p σ s A f.toPowerSeries) (d : Fin 2 →₀ ℕ) :
    coeff d (f⁻¹ • FormalGroup.𝔾ₐ (R := K)).toPowerSeries ∈ A := by
  refine coeff_mem_of_satisfiesFunctionalEquation_subst hσ hσp hs f.constantCoeff_toPowerSeries
    hf₁ hf (f⁻¹ • FormalGroup.𝔾ₐ).zero_constantCoeff ?_ d
  have hX (j : Fin 2) : SatisfiesFunctionalEquation p σ s A
      (f.toPowerSeries.subst (X j : MvPowerSeries (Fin 2) K)) :=
    hf.subst hσ hσp hs f.constantCoeff_toPowerSeries (constantCoeff_X j) fun e ↦ by
      rw [coeff_X]
      split_ifs
      exacts [one_mem A, zero_mem A]
  have h := hasSubst_finTwo (f.hasSubst_subst (PowerSeries.HasSubst.X (S := K) (0 : Fin 2)))
    (f.hasSubst_subst (PowerSeries.HasSubst.X (S := K) (1 : Fin 2)))
  -- `f (F (X, Y)) = f (X) + f (Y)` for `F = f⁻¹ • 𝔾ₐ`
  rw [FormalGroup.subst_toPowerSeries_eq_subst_smul_toPowerSeries, smul_smul, mul_inv_cancel,
    one_smul, FormalGroup.𝔾ₐ_toPowerSeries, subst_add h, subst_X h, subst_X h]
  exact (hX 0).add (hX 1)

end Integrality

end TauCeti
