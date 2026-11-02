/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Periodic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Holomorphic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Infty
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Periodic
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The `q`-expansion of the upper-triangular Hecke sum

`UpperTri/Sum.lean` defines `heckeSlashUpperTri k p f = ∑ b < p, f ∣[k] !![1, b; 0, p]`, and the
files beside it carry it past holomorphy, the cusps and invariance under `T`. What was missing is
what the sum does to Fourier coefficients, and that is what this file computes:

`aₘ(heckeSlashUpperTri k p f) = a_{p m}(f)`.

Three steps do it. Slashing by `!![1, b; 0, p]` sends `τ` to `(τ + b) / p`, and both the
determinant and the denominator are `p`, so the automorphy factor is `p ^ (k - 1) * p ^ (-k)`,
that is `p⁻¹`: **the weight cancels out**, which is why the answer below carries no power of `p`.
The local parameter then splits, `𝕢 1 ((τ + b) / p) = 𝕢 p τ * 𝕢 p b`. Finally the offsets
contribute the `p`-th roots of unity `𝕢 p b`, whose `m`-th powers sum to `p` exactly when
`p ∣ m` (`TauCeti.Periodic.sum_qParam_natCast_pow`); the `p` cancels the `p⁻¹`, and only the
indices in `p ℕ` survive.

## Two conventions worth stating

* This is the operator that Diamond–Shurman's `Tₚ` degenerates to at `p ∣ N` — the one modern
  papers write `Uₚ`. Following the sources, no separate `Uₚ` is introduced: the classical `Tₚ`
  will be built on top of this sum, and at `p ∣ N` it is this sum. For `p ∤ N` the classical `Tₚ`
  has one further coset representative, `!![p, 0; 0, 1]`, which contributes the second term
  `χ(p) p ^ (k - 1) a_{m/p}(f)` of the recurrence; that representative is not part of this sum
  and does not appear here.
* The expansions are taken at width `1`, which is the width of `∞` for every group between
  `Γ₁(N)` and `Γ₀(N)`. The hypotheses are the three that Mathlib's `q`-expansion API asks of a
  raw function on `ℍ` — periodicity through `ofComplex`, holomorphy, boundedness at `i∞` — and
  `qExpansion_coeff_heckeSlashUpperTri'` discharges all three from `ModularFormClass`.

## Main results

* `HeckeRing.GL2.coe_upperTriRep_smul`, `HeckeRing.GL2.qParam_one_upperTriRep_smul`: the Möbius
  image `(τ + b) / p` of a representative, and the resulting factorisation of the local
  parameter.
* `HeckeRing.GL2.slash_upperTriRep_apply`: slashing by a representative is `p⁻¹ * f ((τ + b)/p)`,
  whatever the weight; `HeckeRing.GL2.coe_smul_of_coe_eq_upperTri` and
  `HeckeRing.GL2.slash_apply_of_coe_eq_upperTri` are the same facts for any rational matrix
  `!![1, b; 0, p]`.
* `HeckeRing.GL2.hasSum_qExpansion_sum_slash_of_coe_eq_upperTri`: for an `N`-periodic `f`, the
  sum of its slashes by `!![1, N c; 0, p]` (`c < p`) is given everywhere by the convergent
  expansion `∑ j, a_{p j}(f) q_N ^ j` at period `N`.
* `HeckeRing.GL2.hasSum_qExpansion_heckeSlashUpperTri`: its case `N = 1`, the upper-triangular
  Hecke sum.
* `HeckeRing.GL2.qExpansion_coeff_heckeSlashUpperTri` and `qExpansion_heckeSlashUpperTri`: the
  coefficient formula `aₘ = a_{p m}` and its power-series form, and
  `qExpansion_coeff_heckeSlashUpperTri'`, the same for a bundled modular form.
* `HeckeRing.GL2.periodic_heckeSlashUpperTri`: the periodicity fact used by the coefficient
  uniqueness argument.

## Provenance

No code is transcribed. The computation is the classical one — the `q`-expansion of the operator
Diamond–Shurman write `Tₚ` — run here through Mathlib's `q`-expansion API and the roots-of-unity
orthogonality relation, rather than through a transcribed proof.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2–5.3.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
-/

public section

open Function UpperHalfPlane

open scoped ModularForm Manifold

local notation "𝕢" => Function.Periodic.qParam

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

private lemma det_pos_of_coe_eq_upperTri (hp : 0 < p) {g : GL (Fin 2) ℚ} {b : ℚ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ) = !![1, b; 0, (p : ℚ)]) :
    0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [hg, Matrix.det_fin_two_of]
  simpa using hp

/-- The Möbius image of `τ` under any rational matrix `!![1, b; 0, p]` is `(τ + b) / p`. -/
lemma coe_smul_of_coe_eq_upperTri (hp : 0 < p) {g : GL (Fin 2) ℚ} {b : ℚ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ) = !![1, b; 0, (p : ℚ)]) (τ : ℍ) :
    ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • τ : ℍ) : ℂ) = ((τ : ℂ) + b) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos
    (ModularForm.det_map_ratCast_pos (det_pos_of_coe_eq_upperTri p hp hg))]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, hg]

/-- **Slashing by a rational matrix `!![1, b; 0, p]`**: the determinant and the denominator are
both `p`, so the automorphy factor collapses to `p ^ (k - 1) * p ^ (-k) = p⁻¹`, independent of
the weight. -/
lemma slash_apply_of_coe_eq_upperTri (hp : 0 < p) {g : GL (Fin 2) ℚ} {b : ℚ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ) = !![1, b; 0, (p : ℚ)]) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] g) τ = (p : ℂ)⁻¹ * f (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • τ) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [ModularForm.rat_slash_apply_of_det_pos k (det_pos_of_coe_eq_upperTri p hp hg)]
  have hdet : ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g).det : ℝ) = (p : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_map_apply,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, hg, Matrix.det_fin_two_of]
    simp
  have hden : denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) τ = (p : ℂ) := by
    simp [UpperHalfPlane.denom, hg]
  rw [hdet, hden, abs_of_nonneg (Nat.cast_nonneg p), Complex.ofReal_natCast, mul_assoc,
    ← zpow_add₀ hp0]
  have hk : k - 1 + -k = (-1 : ℤ) := by omega
  rw [hk, zpow_neg_one, mul_comm]

/-- The Möbius image of `τ` under `!![1, b; 0, p]` is `(τ + b) / p`. -/
lemma coe_upperTriRep_smul (b : Fin p) (τ : ℍ) :
    ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b) • τ : ℍ) : ℂ)
      = ((τ : ℂ) + b) / p := by
  simpa using coe_smul_of_coe_eq_upperTri p b.pos (coe_upperTriRep p b) τ

/-- The local parameter of width `1` at `(τ + b) / p` factors as the parameter of width `p`
at `τ` times its value at the offset `b`. -/
lemma qParam_one_upperTriRep_smul (b : Fin p) (τ : ℍ) :
    𝕢 1 ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b) • τ : ℍ) : ℂ)
      = 𝕢 (p : ℝ) (τ : ℂ) * 𝕢 (p : ℝ) (b : ℂ) := by
  rw [coe_upperTriRep_smul]
  simp only [Function.Periodic.qParam, ← Complex.exp_add, Complex.ofReal_natCast,
    Complex.ofReal_one]
  ring_nf

/-- **Slashing by `!![1, b; 0, p]`**: the determinant and the denominator are both `p`, so the
automorphy factor collapses to `p ^ (k - 1) * p ^ (-k) = p⁻¹`, independent of the weight. -/
lemma slash_upperTriRep_apply (f : ℍ → ℂ) (b : Fin p) (τ : ℍ) :
    (f ∣[k] (upperTriRep p b : GL (Fin 2) ℚ)) τ
      = (p : ℂ)⁻¹ *
          f (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b) • τ) :=
  slash_apply_of_coe_eq_upperTri k p b.pos (coe_upperTriRep p b) f τ

/-- **A sum of slashes by `!![1, N c; 0, p]` has the expansion of `f` at period `N` along
`p ℕ`.** For an `N`-periodic `f`, slashing by `!![1, N c; 0, p]` scales the expansion at period
`N` by `p⁻¹` and twists its `m`-th term by the `p`-th root of unity `𝕢 p c ^ m`. Summing over
the offsets `c < p`, the roots-of-unity orthogonality relation kills every term whose index is
not divisible by `p`, and the surviving terms are exactly `a_{p j}(f) q^j`. At `N = 1` this is
`hasSum_qExpansion_heckeSlashUpperTri`; at other periods it computes Hecke operators at cusps
of width `N`. -/
theorem hasSum_qExpansion_sum_slash_of_coe_eq_upperTri {N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {g : Fin p → GL (Fin 2) ℚ}
    (hg : ∀ c, (g c : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (N : ℚ) * c; 0, (p : ℚ)]) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) N) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (τ : ℍ) :
    HasSum (fun j : ℕ ↦ (qExpansion N f).coeff (p * j) • 𝕢 N (τ : ℂ) ^ j)
      (∑ c : Fin p, (f ∣[k] g c) τ) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq : ∀ c : Fin p,
      𝕢 N ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g c) • τ : ℍ) : ℂ) =
        𝕢 (p * N : ℝ) (τ : ℂ) * 𝕢 (p : ℝ) (c : ℂ) := fun c ↦ by
    rw [coe_smul_of_coe_eq_upperTri p hp (hg c)]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp only [Function.Periodic.qParam, ← Complex.exp_add, Complex.ofReal_mul,
      Complex.ofReal_natCast]
    congr 1
    push_cast
    field_simp
  -- The expansion of each slash is the expansion of `f`, scaled and twisted by a root of unity.
  have hterm : ∀ c : Fin p, HasSum (fun m : ℕ ↦ (p : ℂ)⁻¹ * ((qExpansion N f).coeff m *
      (𝕢 (p * N : ℝ) (τ : ℂ) ^ m * 𝕢 (p : ℝ) (c : ℂ) ^ m))) ((f ∣[k] g c) τ) := fun c ↦ by
    rw [slash_apply_of_coe_eq_upperTri k p hp (hg c) f τ]
    refine HasSum.mul_left _ ?_
    simpa only [hq, mul_pow, smul_eq_mul] using UpperHalfPlane.hasSum_qExpansion hN' hfper hfhol
      hfbdd (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g c) • τ)
  have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin p))) fun c _ ↦ hterm c
  -- Collapse the inner sum over the offsets: it is `p` when `p ∣ m` and `0` otherwise.
  have hcollapse : ∀ m : ℕ, (∑ c : Fin p, (p : ℂ)⁻¹ * ((qExpansion N f).coeff m *
      (𝕢 (p * N : ℝ) (τ : ℂ) ^ m * 𝕢 (p : ℝ) (c : ℂ) ^ m))) =
        if p ∣ m then (qExpansion N f).coeff m * 𝕢 (p * N : ℝ) (τ : ℂ) ^ m else 0 := by
    intro m
    have hfac : ∀ c : Fin p, (p : ℂ)⁻¹ * ((qExpansion N f).coeff m *
        (𝕢 (p * N : ℝ) (τ : ℂ) ^ m * 𝕢 (p : ℝ) (c : ℂ) ^ m)) =
          ((p : ℂ)⁻¹ * ((qExpansion N f).coeff m * 𝕢 (p * N : ℝ) (τ : ℂ) ^ m)) *
            𝕢 (p : ℝ) (c : ℂ) ^ m := fun c ↦ by ring
    rw [Finset.sum_congr rfl fun c _ ↦ hfac c, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun c ↦ 𝕢 (p : ℝ) (c : ℂ) ^ m),
      TauCeti.Periodic.sum_qParam_natCast_pow m]
    split_ifs
    · field_simp
    · ring
  rw [funext hcollapse] at hsum
  -- Reindex along `j ↦ p * j`: the discarded indices are exactly the vanishing terms.
  have hinj : Injective fun j : ℕ ↦ p * j := fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left hp h
  have hzero : ∀ x ∉ Set.range fun j : ℕ ↦ p * j,
      (if p ∣ x then (qExpansion N f).coeff x * 𝕢 (p * N : ℝ) (τ : ℂ) ^ x else 0) = 0 := by
    intro x hx
    have hnd : ¬p ∣ x := fun ⟨j, hj⟩ ↦ hx ⟨j, hj.symm⟩
    simp [hnd]
  have hbase : 𝕢 (p * N : ℝ) (τ : ℂ) ^ p = 𝕢 N (τ : ℂ) :=
    TauCeti.Periodic.qParam_nat_mul_pow hp.ne' (τ : ℂ)
  refine ((hinj.hasSum_iff hzero).mpr hsum).congr_fun fun j ↦ ?_
  simp [Dvd.intro j rfl, pow_mul, hbase]

/-- **The upper-triangular Hecke sum has the `q`-expansion of `f` along the progression `p ℕ`.**
This is the case `N = 1` of `hasSum_qExpansion_sum_slash_of_coe_eq_upperTri`. -/
theorem hasSum_qExpansion_heckeSlashUpperTri (hp : 0 < p) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (τ : ℍ) :
    HasSum (fun j : ℕ ↦ (qExpansion 1 f).coeff (p * j) • 𝕢 1 (τ : ℂ) ^ j)
      (heckeSlashUpperTri k p f τ) := by
  rw [heckeSlashUpperTri_apply]
  simpa using hasSum_qExpansion_sum_slash_of_coe_eq_upperTri k p (N := 1) hp one_pos
    (fun b ↦ by simp) (by simpa using hfper) hfhol hfbdd τ

/-- **The upper-triangular sum of a `1`-periodic function is `1`-periodic**, in the
`ofComplex`-extended form the `q`-expansion API asks for. -/
theorem periodic_heckeSlashUpperTri {f : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1) :
    Periodic (heckeSlashUpperTri k p f ∘ ofComplex) 1 :=
  TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff.mpr <|
    heckeSlashUpperTri_shift_one k p f
      (TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff.mp hfper)

/-- The cusp function of the upper-triangular sum is analytic at `q = 0`: the sum inherits
periodicity, holomorphy and boundedness at `i∞` from `f`. -/
private theorem analyticAt_cuspFunction_heckeSlashUpperTri {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    AnalyticAt ℂ (cuspFunction 1 (heckeSlashUpperTri k p f)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos (periodic_heckeSlashUpperTri k p hfper)
    (mdifferentiable_heckeSlashUpperTri k p hfhol) (isBoundedAtImInfty_heckeSlashUpperTri k p hfbdd)

/-- **The coefficient formula for the upper-triangular Hecke sum**:
`aₘ(∑_{b < p} f ∣[k] !![1, b; 0, p]) = a_{p m}(f)`.

This is the operator classical sources write `Uₚ` at `p ∣ N`, and it is the first half of the
Diamond–Shurman recurrence `aₘ(Tₚ f) = a_{m p}(f) + χ(p) p^{k−1} a_{m/p}(f)`; the second term
comes from the remaining representative `!![p, 0; 0, 1]`, which is not part of this sum. Note
that the weight has disappeared: the automorphy factor of each representative is `p⁻¹`
whatever `k` is, and the `p` cancels against the number of offsets. -/
@[simp]
theorem qExpansion_coeff_heckeSlashUpperTri (hp : 0 < p) {f : ℍ → ℂ}
    (hfper : ∀ x : ℂ, f (ofComplex (x + 1)) = f (ofComplex x))
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (m : ℕ) :
    (qExpansion 1 (heckeSlashUpperTri k p f)).coeff m = (qExpansion 1 f).coeff (p * m) := by
  have hfper' : Periodic (f ∘ ofComplex) 1 := by
    simpa only [Periodic, comp_apply] using hfper
  exact (TauCeti.UpperHalfPlane.qExpansion_coeff_unique one_pos
    (analyticAt_cuspFunction_heckeSlashUpperTri k p hfper' hfhol hfbdd)
    (hasSum_qExpansion_heckeSlashUpperTri k p hp hfper' hfhol hfbdd) m).symm

/-- `qExpansion_coeff_heckeSlashUpperTri` as an identity of power series: the upper-triangular
sum extracts the subseries of `f` supported on the multiples of `p`, reindexed. -/
theorem qExpansion_heckeSlashUpperTri (hp : 0 < p) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    qExpansion 1 (heckeSlashUpperTri k p f)
      = PowerSeries.mk fun m ↦ (qExpansion 1 f).coeff (p * m) := by
  have hfper' : ∀ x : ℂ, f (ofComplex (x + 1)) = f (ofComplex x) := by
    simpa only [Periodic, comp_apply] using hfper
  exact PowerSeries.ext fun m ↦ by
    rw [qExpansion_coeff_heckeSlashUpperTri k p hp hfper' hfhol hfbdd m,
      PowerSeries.coeff_mk]

/-- **The coefficient formula for a bundled modular form**, the shape Layer 2(b) consumes: for
`f` a modular form of weight `k` on a group with `1` among its strict periods — every
congruence subgroup between `Γ₁(N)` and `Γ₀(N)` has this, since it contains `T` — the
upper-triangular sum reads off the coefficients of `f` along `p ℕ`. -/
@[simp]
theorem qExpansion_coeff_heckeSlashUpperTri' {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [ModularFormClass F Γ k] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (hp : 0 < p) (f : F) (m : ℕ) :
    (qExpansion 1 (heckeSlashUpperTri k p f)).coeff m = (qExpansion 1 f).coeff (p * m) :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hfper : ∀ x : ℂ, f (ofComplex (x + 1)) = f (ofComplex x) := by
    simpa only [Periodic, comp_apply, Complex.ofReal_one] using
      SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  qExpansion_coeff_heckeSlashUpperTri k p hp
    hfper (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) m

end HeckeRing.GL2

end
