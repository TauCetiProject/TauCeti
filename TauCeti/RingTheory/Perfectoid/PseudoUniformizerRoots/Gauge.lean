/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import TauCeti.RingTheory.Huber.TateGauge.SpectralSeminorm
public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Basic

/-!
# The spectral gauge of a pseudouniformiser with compatible roots

Let `R` be a uniform Huber ring and `ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` a pseudouniformiser with compatible
`p`-power roots, `p > 1`. Its *spectral gauge* is
`|x|_ϖ = inf { 2 ^ (-q) | q ∈ ℤ[1/p], ϖ ^ (-q) x ∈ R° }`.
It is the spectral seminorm (`TauCeti.Huber.spectralSeminorm`) of the norm datum `(R°, ϖ, 1/2)`,
which is how it is defined here; the compatible roots then give the `ℤ[1/p]`-exponent formula
above (`PseudoUniformizerRoots.gauge_eq_sInf`), where `ϖ ^ q` is `PseudoUniformizerRoots.zpow`.

The gauge is a power-multiplicative ultrametric ring seminorm, and multiplication by
`ϖ ^ (m / p ^ n)` scales it exactly by `2 ^ (-(m / p ^ n))`. Its closed unit ball is `R°` and its
open unit ball is the set `R°°` of topologically nilpotent elements; more generally its closed
ball of radius `2 ^ (-q)` is `ϖ ^ q R°`. Its open balls, like the `ϖ ^ q R°`, are a neighbourhood
basis of zero, so it defines the topology of `R`, and it is a norm when `R` is Hausdorff. In a
nonzero Hausdorff ring it is power-multiplicative at every exponent and normalised by
`|ϖ|_ϖ = 1 / 2`.

The gauge measures elements of a perfectoid Tate ring against its root system; it is the norm
with which the tilt and its sharp map are compared to the ring.

## Main definitions

* `TauCeti.Perfectoid.PseudoUniformizerRoots.normDatum`: the norm datum `(R°, ϖ, 1/2)`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge`: the spectral gauge `|·|_ϖ`.

## Main results

* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_zpow_mul`:
  `|ϖ ^ (m / p ^ n) x|_ϖ = 2 ^ (-(m / p ^ n)) |x|_ϖ`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_root_mul`:
  `|ϖ ^ (1 / p ^ n) x|_ϖ = 2 ^ (-(1 / p ^ n)) |x|_ϖ`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_le_one_iff`: `|x|_ϖ ≤ 1 ↔ x ∈ R°`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_lt_one_iff`: `|x|_ϖ < 1` iff `x` is
  topologically nilpotent.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_le_rpow_iff`: the closed ball of radius
  `2 ^ (-(m / p ^ n))` is `ϖ ^ (m / p ^ n) R°`.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_eq_sInf`: the `ℤ[1/p]`-exponent formula.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_hasBasis_nhds_zero`: the gauge defines the
  topology.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.hasBasis_nhds_zero_zpow_mul_mem`: the `ϖ ^ q R°`,
  `q ∈ ℤ[1/p]`, are a neighbourhood basis of zero.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_eq_zero_iff`: the gauge is a norm on a
  Hausdorff ring.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.gauge_pow`: in a nonzero Hausdorff ring,
  `|x ^ n|_ϖ = |x|_ϖ ^ n` for every `n`.

## References

* P. Scholze, *Étale cohomology of diamonds*, §3, Lemma 3.10.
* P. Scholze, *Perfectoid spaces*, Remark 3.5.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Lemma 6.2.2 and its proof.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Definition 2.1.9.
-/

public section

open Filter Topology TauCeti.Huber

namespace TauCeti.Perfectoid.PseudoUniformizerRoots

variable {p : ℕ} [NeZero p] {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsHuberRing R] [IsUniform R] (ϖ : PseudoUniformizerRoots p R)

/-- The norm datum `(R°, ϖ, 1/2)` of a uniform Huber ring with a pseudouniformiser with compatible
roots: the power-bounded subring `R°`, open and bounded since `R` is uniform, the
pseudouniformiser `ϖ` and the radius `1 / 2`. -/
noncomputable def normDatum : TateNormDatum R where
  ringOfDefinition := powerBoundedSubring R
  isOpen_ringOfDefinition := isOpen_powerBoundedSubring R
  isBounded_ringOfDefinition := IsUniform.isBounded_powerBoundedSubring
  pseudoUniformizer := ϖ.unitRoot 0
  isTopologicallyNilpotent_pseudoUniformizer := by
    simpa using ϖ.isPseudoUniformizer_root_zero.isTopologicallyNilpotent
  pseudoUniformizer_mem := by simpa using (ϖ.rootPB 0).2
  radius := 1 / 2
  radius_pos := by norm_num
  radius_lt_one := by norm_num

/-- The ring of definition of `(R°, ϖ, 1/2)` is `R°`. -/
@[simp]
theorem normDatum_ringOfDefinition : ϖ.normDatum.ringOfDefinition = powerBoundedSubring R :=
  (rfl)

/-- The pseudouniformiser of `(R°, ϖ, 1/2)` is `ϖ`. -/
@[simp]
theorem normDatum_pseudoUniformizer : ϖ.normDatum.pseudoUniformizer = ϖ.unitRoot 0 :=
  (rfl)

/-- The radius of `(R°, ϖ, 1/2)` is `1 / 2`. -/
@[simp]
theorem normDatum_radius : ϖ.normDatum.radius = 1 / 2 :=
  (rfl)

/-- The *spectral gauge* `|·|_ϖ` of a pseudouniformiser with compatible roots of a uniform Huber
ring: the spectral seminorm of the norm datum `(R°, ϖ, 1/2)`. For `p > 1` it is
`|x|_ϖ = inf { 2 ^ (-q) | q ∈ ℤ[1/p], ϖ ^ (-q) x ∈ R° }` (`gauge_eq_sInf`). -/
noncomputable def gauge : RingSeminorm R :=
  spectralSeminorm ϖ.normDatum

/-- The spectral gauge is the spectral seminorm of the norm datum `(R°, ϖ, 1/2)`. -/
theorem gauge_eq_spectralSeminorm : ϖ.gauge = spectralSeminorm ϖ.normDatum :=
  (rfl)

/-- The spectral gauge is power-multiplicative: `|x ^ n|_ϖ = |x|_ϖ ^ n` for `n ≥ 1`. -/
theorem isPowMul_gauge : IsPowMul ϖ.gauge :=
  isPowMul_spectralSeminorm _

/-- The spectral gauge is ultrametric. -/
theorem isNonarchimedean_gauge : IsNonarchimedean ϖ.gauge :=
  isNonarchimedean_spectralSeminorm _

/-- **Scaling by the roots.** Multiplication by `ϖ ^ (m / p ^ n)` scales the spectral gauge
exactly by `2 ^ (-(m / p ^ n))`. -/
@[simp]
theorem gauge_zpow_mul (m : ℤ) (n : ℕ) (x : R) :
    ϖ.gauge (ϖ.zpow m n * x) = 2 ^ (-((m : ℝ) / p ^ n)) * ϖ.gauge x := by
  -- Both sides are nonnegative, and their `p ^ n`-th powers are `2 ^ (-m) |x ^ p ^ n|_ϖ`, since
  -- `(ϖ ^ (m / p ^ n)) ^ p ^ n = ϖ ^ m` and `(2 ^ (-(m / p ^ n))) ^ p ^ n = (1 / 2) ^ m`.
  have hN : p ^ n ≠ 0 := pow_ne_zero n (NeZero.ne p)
  have h2 : ((2 : ℝ) ^ (-((m : ℝ) / p ^ n))) ^ p ^ n = (1 / 2) ^ m := by
    rw [← Real.rpow_mul_natCast zero_le_two]
    field_simp
    simp [Real.rpow_neg, Real.rpow_intCast]
  have hpow (y : R) := ϖ.isPowMul_gauge y (Nat.one_le_iff_ne_zero.mpr hN)
  refine (pow_left_inj₀ (apply_nonneg _ _) (by positivity) hN).mp ?_
  rw [← hpow, mul_pow, mul_pow, h2, ← hpow, ← Units.val_pow_eq_pow_val, zpow_pow, zpow_def]
  exact spectralSeminorm_zpow_mul ϖ.normDatum m _

/-- Multiplication by `ϖ ^ (-(m / p ^ n))` scales the spectral gauge by `2 ^ (m / p ^ n)`. -/
private theorem gauge_zpow_neg_mul (m : ℤ) (n : ℕ) (x : R) :
    ϖ.gauge (ϖ.zpow (-m) n * x) = 2 ^ ((m : ℝ) / p ^ n) * ϖ.gauge x := by
  simpa [neg_div] using ϖ.gauge_zpow_mul (-m) n x

/-- **Scaling by a root.** Multiplication by `ϖ ^ (1 / p ^ n)` scales the spectral gauge exactly
by `2 ^ (-(1 / p ^ n))`. -/
@[simp]
theorem gauge_root_mul (n : ℕ) (x : R) :
    ϖ.gauge (ϖ.root n * x) = 2 ^ (-(1 / (p : ℝ) ^ n)) * ϖ.gauge x := by
  simpa using ϖ.gauge_zpow_mul 1 n x

/-- Multiplication by `ϖ` halves the spectral gauge. Its priority lets it fire before
`gauge_root_mul`, which would leave `2 ^ (-1)`. -/
@[simp high]
theorem gauge_root_zero_mul (x : R) : ϖ.gauge (ϖ.root 0 * x) = 1 / 2 * ϖ.gauge x := by
  simp [Real.rpow_neg_one]

/-- The spectral gauge takes values at most one on the powers of an element of gauge at most
one. -/
private theorem gauge_pow_le_one {x : R} (hx : ϖ.gauge x ≤ 1) (k : ℕ) : ϖ.gauge (x ^ k) ≤ 1 := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simpa using ϖ.isPowMul_gauge.map_one_le_one
  · rw [ϖ.isPowMul_gauge _ hk]
    exact pow_le_one₀ (apply_nonneg _ _) hx

/-- **The closed unit ball of the spectral gauge is `R°`.** -/
theorem gauge_le_one_iff {x : R} : ϖ.gauge x ≤ 1 ↔ x ∈ powerBoundedSubring R := by
  refine ⟨fun hx ↦ ?_, fun hx ↦
    spectralSeminorm_le_one_of_isPowerBounded _ (mem_powerBoundedSubring.mp hx)⟩
  -- Each `ϖ x ^ k` has gauge at most `1 / 2`, so it is topologically nilpotent and lies in `R°`;
  -- hence the powers of `x` lie in the bounded set `ϖ⁻¹ R°`.
  have hpow (k : ℕ) : (ϖ.unitRoot 0 : R) * x ^ k ∈ powerBoundedSubring R := by
    refine mem_powerBoundedSubring.mpr (.of_isTopologicallyNilpotent ?_)
    rw [← spectralSeminorm_lt_one_iff ϖ.normDatum, ← normDatum_pseudoUniformizer,
      spectralSeminorm_pseudoUniformizer_mul, normDatum_radius, ← gauge_eq_spectralSeminorm]
    linarith [ϖ.gauge_pow_le_one hx k]
  refine mem_powerBoundedSubring.mpr <| isPowerBounded_iff.mpr <|
    ((isBounded_singleton ((ϖ.unitRoot 0)⁻¹ : Rˣ).1).mul
      IsUniform.isBounded_powerBoundedSubring).subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl, _, hpow k, Units.inv_mul_cancel_left _ _⟩

/-- **The open unit ball of the spectral gauge is `R°°`**: `|x|_ϖ < 1` exactly when `x` is
topologically nilpotent. -/
theorem gauge_lt_one_iff {x : R} : ϖ.gauge x < 1 ↔ IsTopologicallyNilpotent x :=
  spectralSeminorm_lt_one_iff _

/-- **The closed balls of the spectral gauge**: `|x|_ϖ ≤ 2 ^ (-(m / p ^ n))` exactly when
`ϖ ^ (-(m / p ^ n)) x ∈ R°`, i.e. the closed ball of radius `2 ^ (-q)` is `ϖ ^ q R°`. -/
theorem gauge_le_rpow_iff {x : R} (m : ℤ) (n : ℕ) :
    ϖ.gauge x ≤ 2 ^ (-((m : ℝ) / p ^ n)) ↔
      (ϖ.zpow (-m) n : R) * x ∈ powerBoundedSubring R := by
  rw [Real.rpow_neg zero_le_two, ← one_div, le_div_iff₀' (by positivity),
    ← gauge_zpow_neg_mul, gauge_le_one_iff]

/-- **The open balls of the spectral gauge**: `|x|_ϖ < 2 ^ (-(m / p ^ n))` exactly when
`ϖ ^ (-(m / p ^ n)) x` is topologically nilpotent. -/
theorem gauge_lt_rpow_iff {x : R} (m : ℤ) (n : ℕ) :
    ϖ.gauge x < 2 ^ (-((m : ℝ) / p ^ n)) ↔
      IsTopologicallyNilpotent ((ϖ.zpow (-m) n : R) * x) := by
  rw [Real.rpow_neg zero_le_two, ← one_div, lt_div_iff₀' (by positivity),
    ← gauge_zpow_neg_mul, gauge_lt_one_iff]

/-- An element of spectral gauge at most `2 ^ (-k)` has Tate norm at most `2 ^ (-k)` for the
norm datum `(R°, ϖ, 1/2)`. -/
private theorem tateNorm_le_of_gauge_le {x : R} {k : ℕ} (hx : ϖ.gauge x ≤ (1 / 2) ^ k) :
    tateNorm ϖ.normDatum x ≤ (1 / 2) ^ k := by
  have h := (ϖ.gauge_le_rpow_iff k 0).mp (by
    simpa [Real.rpow_neg, Real.rpow_natCast] using hx)
  rw [← ϖ.normDatum_radius, ← zpow_natCast, tateNorm_le_zpow_iff]
  simpa [zpow_def] using h

/-- **The spectral gauge defines the topology**: its open balls about zero are a neighbourhood
basis of zero. -/
theorem gauge_hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun ε : ℝ ↦ 0 < ε) fun ε ↦ {x | ϖ.gauge x < ε} := by
  refine (tateNorm_hasBasis_nhds_zero ϖ.normDatum).to_hasBasis (fun ε hε ↦ ?_)
    fun ε hε ↦ ⟨ε, hε, fun x hx ↦ (spectralSeminorm_le_tateNorm _ x).trans_lt hx⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨(1 / 2) ^ k, by positivity, fun x hx ↦ (ϖ.tateNorm_le_of_gauge_le hx.le).trans_lt hk⟩

/-- **The `ϖ ^ q R°` are a neighbourhood basis of zero**, for `q = m / p ^ n` in `ℤ[1/p]`. -/
theorem hasBasis_nhds_zero_zpow_mul_mem :
    (𝓝 (0 : R)).HasBasis (fun _ : ℤ × ℕ ↦ True)
      fun q ↦ {x | (ϖ.zpow (-q.1) q.2 : R) * x ∈ powerBoundedSubring R} := by
  refine ϖ.gauge_hasBasis_nhds_zero.to_hasBasis (fun ε hε ↦ ?_)
    fun q _ ↦ ⟨_, by positivity, fun x hx ↦ (ϖ.gauge_le_rpow_iff q.1 q.2).mp hx.le⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨(k, 0), trivial, fun x hx ↦ ((ϖ.gauge_le_rpow_iff k 0).mpr hx).trans_lt ?_⟩
  simpa [Real.rpow_neg, Real.rpow_natCast] using hk

/-- **The spectral gauge is a norm on a Hausdorff ring.** -/
@[simp]
theorem gauge_eq_zero_iff [T1Space R] {x : R} : ϖ.gauge x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ map_zero _⟩
  -- `x` has Tate norm at most `2 ^ (-k)` for every `k`, so it lies in the closure of zero.
  have h : tateNorm ϖ.normDatum x = 0 :=
    le_antisymm (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num : (1 / 2 : ℝ) < 1)) fun k ↦ ϖ.tateNorm_le_of_gauge_le (hx ▸ by positivity))
      (apply_nonneg _ _)
  simpa using (tateNorm_eq_zero_iff ϖ.normDatum).mp h

/-- In a nonzero Hausdorff ring the spectral gauge takes the value one at one. -/
@[simp]
theorem gauge_one [T1Space R] [Nontrivial R] : ϖ.gauge 1 = 1 :=
  spectralSeminorm_one _

/-- In a nonzero Hausdorff ring the spectral gauge is power-multiplicative at every exponent:
`|x ^ n|_ϖ = |x|_ϖ ^ n`. -/
@[simp]
theorem gauge_pow [T1Space R] [Nontrivial R] (x : R) (n : ℕ) :
    ϖ.gauge (x ^ n) = ϖ.gauge x ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact ϖ.isPowMul_gauge x hn

/-- In a nonzero Hausdorff ring, `|ϖ ^ (m / p ^ n)|_ϖ = 2 ^ (-(m / p ^ n))`. -/
@[simp]
theorem gauge_zpow [T1Space R] [Nontrivial R] (m : ℤ) (n : ℕ) :
    ϖ.gauge (ϖ.zpow m n) = 2 ^ (-((m : ℝ) / p ^ n)) := by
  simpa using ϖ.gauge_zpow_mul m n 1

/-- In a nonzero Hausdorff ring, `|ϖ ^ (1 / p ^ n)|_ϖ = 2 ^ (-(1 / p ^ n))`. -/
@[simp]
theorem gauge_root [T1Space R] [Nontrivial R] (n : ℕ) :
    ϖ.gauge (ϖ.root n) = 2 ^ (-(1 / (p : ℝ) ^ n)) := by
  simpa using ϖ.gauge_root_mul n 1

/-- **Normalisation**: in a nonzero Hausdorff ring, `|ϖ|_ϖ = 1 / 2`. Its priority lets it fire
before `gauge_root`, which would leave `2 ^ (-1)`. -/
@[simp high]
theorem gauge_root_zero [T1Space R] [Nontrivial R] : ϖ.gauge (ϖ.root 0) = 1 / 2 := by
  simpa using ϖ.gauge_root_zero_mul 1

/-- **The `ℤ[1/p]`-exponent formula** for `p > 1`:
`|x|_ϖ = inf { 2 ^ (-(m / p ^ n)) | ϖ ^ (-(m / p ^ n)) x ∈ R° }`. -/
theorem gauge_eq_sInf (hp : 1 < p) (x : R) :
    ϖ.gauge x = sInf ((fun q : ℤ × ℕ ↦ (2 : ℝ) ^ (-((q.1 : ℝ) / p ^ q.2))) ''
      {q | (ϖ.zpow (-q.1) q.2 : R) * x ∈ powerBoundedSubring R}) := by
  refine le_antisymm (le_csInf ?_ ?_) (le_of_forall_gt fun c hc ↦ ?_)
  · obtain ⟨k, hk⟩ := ϖ.normDatum.exists_zpow_mul_mem x
    exact ⟨_, ⟨(-k, 0), by simpa [zpow_def] using hk, rfl⟩⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (ϖ.gauge_le_rpow_iff q.1 q.2).mpr hq
  -- Choose `q = m / p ^ n` with `|x|_ϖ < 2 ^ (-q) < c`, i.e. `-log₂ c < q < b` for the bound `b`
  -- below, using the density of the `m / p ^ n`.
  have hc0 : 0 < c := (apply_nonneg _ _).trans_lt hc
  obtain ⟨b, hb, hbx⟩ : ∃ b, -Real.logb 2 c < b ∧ ∀ q : ℝ, q < b → ϖ.gauge x < 2 ^ (-q) := by
    rcases (apply_nonneg ϖ.gauge x).eq_or_lt with h0 | h0
    · exact ⟨-Real.logb 2 c + 1, lt_add_one _, fun q _ ↦ by rw [← h0]; positivity⟩
    · exact ⟨-Real.logb 2 (ϖ.gauge x), neg_lt_neg (Real.logb_lt_logb one_lt_two h0 hc),
        fun q hq ↦ (Real.logb_lt_iff_lt_rpow one_lt_two h0).mp (by linarith)⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b - -Real.logb 2 c)⁻¹
    (by exact_mod_cast hp : (1 : ℝ) < p)
  obtain ⟨m, hlt, hgt⟩ := exists_div_btwn hb (n := p ^ n) (by exact_mod_cast hn)
  push_cast at hlt hgt
  replace hgt := hbx _ hgt
  have hq := (ϖ.gauge_le_rpow_iff m n).mp hgt.le
  refine (csInf_lt_iff ?_ ?_).2 ⟨_, ⟨(m, n), hq, rfl⟩, ?_⟩
  · exact ⟨0, by rintro _ ⟨q, -, rfl⟩; positivity⟩
  · exact ⟨_, (m, n), hq, rfl⟩
  · rw [← Real.lt_logb_iff_rpow_lt one_lt_two hc0]
    linarith

end TauCeti.Perfectoid.PseudoUniformizerRoots
