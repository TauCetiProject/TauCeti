/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.MeasureTheory.Function.LocalLipschitzConstant
public import TauCeti.Topology.Semicontinuity.Basic

/-!
# The Cheeger energy of a metric-measure space

Let `X` be an extended pseudometric space with a measure `m`. The *Cheeger energy* of a function
`f ∈ L²(X, m)` is the relaxation of the Dirichlet energy of Lipschitz functions,

`Ch(f) = ½ inf { liminf_n ∫ |D uₙ|² dm | uₙ Lipschitz, uₙ → f in L²(X, m) }`,

where `|D u|` is the local Lipschitz constant `TauCeti.localLipschitzConstant u` of `u`. It is the
energy whose `L²` gradient flow is the heat flow of a metric-measure space; a metric-measure space
is *infinitesimally Hilbertian* when it is a quadratic form, and the Riemannian curvature-dimension
condition `RCD(K, ∞)` asks for this on top of the curvature-dimension condition `CD(K, ∞)`.

The definition `TauCeti.cheegerEnergy m` is the lower semicontinuous envelope on `L²(X, m)` of the
functional equal to `½ ∫ |D u|² dm` on the classes of Lipschitz functions `u` (minimized over the
Lipschitz representatives) and to `∞` elsewhere: at `f` it is the supremum over the
neighbourhoods `s` of `f` of the infimum of `½ ∫ |D u|² dm` over the Lipschitz `u` whose class lies
in `s`. It is therefore lower semicontinuous on `L²(X, m)`
(`TauCeti.lowerSemicontinuous_cheegerEnergy`), and the formula of Ambrosio–Gigli–Savaré, an
infimum over sequences of Lipschitz functions converging in `L²`, is a theorem
(`TauCeti.cheegerEnergy_eq_iInf_liminf`): the Cheeger energy is at most the lower limit of the
energies along every such sequence, and is the limit of the energies along a suitable one.

The Cheeger energy is convex (`TauCeti.convexOn_cheegerEnergy`), since the local Lipschitz
constant is subadditive and positively homogeneous and the square is convex, and it is
`2`-homogeneous: `Ch(c f) = |c|² Ch(f)` (`TauCeti.cheegerEnergy_smul`).

## Main definitions

* `TauCeti.cheegerEnergy m f`: the Cheeger energy of `f ∈ L²(X, m)`.
* `TauCeti.cheegerEnergyDomain m`: its domain, the classes of finite Cheeger energy.

## Main results

* `TauCeti.cheegerEnergy_le_lintegral`: the Cheeger energy of a Lipschitz function is at most
  `½ ∫ |D u|² dm`.
* `TauCeti.lowerSemicontinuous_cheegerEnergy`: lower semicontinuity on `L²(X, m)`.
* `TauCeti.cheegerEnergy_le_liminf` and `TauCeti.exists_tendsto_cheegerEnergy`: the lower bound
  along Lipschitz approximations, and an optimal approximating sequence.
* `TauCeti.cheegerEnergy_eq_iInf_liminf`: the sequential formula.
* `TauCeti.convexOn_cheegerEnergy` and `TauCeti.cheegerEnergy_smul`: convexity and
  `2`-homogeneity.
* `TauCeti.cheegerEnergyDomain`: the Sobolev space `W^{1,2}(X, d, m)` of classes of finite Cheeger
  energy, a linear subspace of `L²(X, m)`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Calculus and heat flow in metric measure spaces and
  applications to spaces with Ricci bounds from below*, Invent. Math. 195 (2014), 289--391,
  Section 4.1.
* J. Cheeger, *Differentiability of Lipschitz functions on metric measure spaces*, Geom. Funct.
  Anal. 9 (1999), 428--517.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] {m : Measure X}

variable (m) in
/-- The *Cheeger energy* of `f ∈ L²(X, m)`: the lower semicontinuous envelope on `L²(X, m)` of
`½ ∫ |D u|² dm` over the Lipschitz functions `u`, where `|D u|` is the local Lipschitz constant.
At `f` it is the supremum, over the neighbourhoods `s` of `f`, of the infimum of
`½ ∫ |D u|² dm` over the Lipschitz functions `u` whose class lies in `s`. -/
def cheegerEnergy (f : Lp ℝ 2 m) : ℝ≥0∞ :=
  ⨆ s ∈ 𝓝 f, ⨅ (u : X → ℝ) (_ : ∃ K, LipschitzWith K u) (hu : MemLp u 2 m) (_ : hu.toLp u ∈ s),
    (∫⁻ x, localLipschitzConstant u x ^ 2 ∂m) / 2

variable (m) in
/-- The defining formula of the Cheeger energy, as a lower semicontinuous envelope. -/
theorem cheegerEnergy_def (f : Lp ℝ 2 m) :
    cheegerEnergy m f = ⨆ s ∈ 𝓝 f, ⨅ (u : X → ℝ) (_ : ∃ K, LipschitzWith K u) (hu : MemLp u 2 m)
      (_ : hu.toLp u ∈ s), (∫⁻ x, localLipschitzConstant u x ^ 2 ∂m) / 2 :=
  (rfl)

/-- The Cheeger energy of the class of a Lipschitz function `u` is at most `½ ∫ |D u|² dm`. -/
theorem cheegerEnergy_le_lintegral {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu : MemLp u 2 m) :
    cheegerEnergy m (hu.toLp u) ≤ (∫⁻ x, localLipschitzConstant u x ^ 2 ∂m) / 2 := by
  rw [cheegerEnergy_def]
  exact iSup₂_le fun s hs ↦ iInf_le_of_le u <| iInf_le_of_le ⟨K, hK⟩ <| iInf_le_of_le hu <|
    iInf_le_of_le (mem_of_mem_nhds hs) le_rfl

/-- The Cheeger energy of `0` is `0`. -/
@[simp]
theorem cheegerEnergy_zero : cheegerEnergy m 0 = 0 := by
  have h := cheegerEnergy_le_lintegral (m := m) (u := 0) (LipschitzWith.const (0 : ℝ)) MemLp.zero
  rw [MemLp.toLp_zero] at h
  exact nonpos_iff_eq_zero.1 (h.trans (by simp [Pi.zero_def]))

/-- The Cheeger energy is lower semicontinuous on `L²(X, m)`. -/
theorem lowerSemicontinuous_cheegerEnergy : LowerSemicontinuous (cheegerEnergy m) := by
  rw [funext (cheegerEnergy_def m)]
  exact lowerSemicontinuous_iSup_nhds _

/-- Along Lipschitz functions `uᵢ` whose classes converge to `f` in `L²(X, m)`, the Cheeger energy
of `f` is at most the lower limit of `½ ∫ |D uᵢ|² dm`. -/
theorem cheegerEnergy_le_liminf {ι : Type*} {l : Filter ι} {u : ι → X → ℝ}
    (hlip : ∀ i, ∃ K, LipschitzWith K (u i)) (hu : ∀ i, MemLp (u i) 2 m) {f : Lp ℝ 2 m}
    (hf : Tendsto (fun i ↦ (hu i).toLp (u i)) l (𝓝 f)) :
    cheegerEnergy m f ≤ liminf (fun i ↦ (∫⁻ x, localLipschitzConstant (u i) x ^ 2 ∂m) / 2) l := by
  rw [cheegerEnergy_def]
  refine iSup₂_le fun s hs ↦ le_liminf_of_le (h := ?_)
  filter_upwards [hf hs] with i hi
  exact iInf_le_of_le (u i) <| iInf_le_of_le (hlip i) <| iInf_le_of_le (hu i) <|
    iInf_le_of_le hi le_rfl

/-- A function of finite Cheeger energy is the limit in `L²(X, m)` of the classes of Lipschitz
functions `uₙ` whose energies `½ ∫ |D uₙ|² dm` converge to its Cheeger energy. -/
theorem exists_tendsto_cheegerEnergy {f : Lp ℝ 2 m} (hf : cheegerEnergy m f ≠ ∞) :
    ∃ (u : ℕ → X → ℝ) (hu : ∀ n, MemLp (u n) 2 m), (∀ n, ∃ K, LipschitzWith K (u n)) ∧
      Tendsto (fun n ↦ (hu n).toLp (u n)) atTop (𝓝 f) ∧
      Tendsto (fun n ↦ (∫⁻ x, localLipschitzConstant (u n) x ^ 2 ∂m) / 2) atTop
        (𝓝 (cheegerEnergy m f)) := by
  have key : ∀ n : ℕ, ∃ (u : X → ℝ) (hu : MemLp u 2 m), (∃ K, LipschitzWith K u) ∧
      hu.toLp u ∈ Metric.ball f (1 / (n + 1)) ∧
      (∫⁻ x, localLipschitzConstant u x ^ 2 ∂m) / 2 < cheegerEnergy m f + (n : ℝ≥0∞)⁻¹ := by
    intro n
    have hlt := (le_iSup₂ (f := fun s (_ : s ∈ 𝓝 f) ↦ ⨅ (u : X → ℝ)
      (_ : ∃ K, LipschitzWith K u) (hu : MemLp u 2 m) (_ : hu.toLp u ∈ s),
        (∫⁻ x, localLipschitzConstant u x ^ 2 ∂m) / 2) (Metric.ball f (1 / (n + 1)))
      (Metric.ball_mem_nhds f (Nat.one_div_pos_of_nat (n := n)))).trans_lt
      (ENNReal.lt_add_right hf (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)))
    rw [← cheegerEnergy_def] at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨u, hK, hu, hmem, hE⟩ := hlt
    exact ⟨u, hu, hK, hmem, hE⟩
  choose u hu hK hmem hE using key
  have htend : Tendsto (fun n ↦ (hu n).toLp (u n)) atTop (𝓝 f) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ (Metric.mem_ball.1 (hmem n)).le) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨u, hu, hK, htend, tendsto_of_le_liminf_of_limsup_le
    (cheegerEnergy_le_liminf hK hu htend) ?_⟩
  have hlim : Tendsto (fun n : ℕ ↦ cheegerEnergy m f + (n : ℝ≥0∞)⁻¹) atTop
      (𝓝 (cheegerEnergy m f)) := by
    simpa using tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
  exact (limsup_le_limsup (Eventually.of_forall fun n ↦ (hE n).le)).trans hlim.limsup_eq.le

/-- The **Cheeger energy** of `f ∈ L²(X, m)` is the infimum, over the sequences of Lipschitz
functions `uₙ` whose classes converge to `f` in `L²(X, m)`, of the lower limit of
`½ ∫ |D uₙ|² dm`. This is the formula by which Ambrosio–Gigli–Savaré define the Cheeger energy.
-/
theorem cheegerEnergy_eq_iInf_liminf (f : Lp ℝ 2 m) :
    cheegerEnergy m f = ⨅ (u : ℕ → X → ℝ) (_ : ∀ n, ∃ K, LipschitzWith K (u n))
      (hu : ∀ n, MemLp (u n) 2 m) (_ : Tendsto (fun n ↦ (hu n).toLp (u n)) atTop (𝓝 f)),
        liminf (fun n ↦ (∫⁻ x, localLipschitzConstant (u n) x ^ 2 ∂m) / 2) atTop := by
  refine le_antisymm (le_iInf fun u ↦ le_iInf fun hK ↦ le_iInf fun hu ↦ le_iInf fun hf ↦
    cheegerEnergy_le_liminf hK hu hf) ?_
  rcases eq_or_ne (cheegerEnergy m f) ∞ with hf | hf
  · exact hf ▸ le_top
  obtain ⟨u, hu, hK, htend, hE⟩ := exists_tendsto_cheegerEnergy hf
  exact iInf_le_of_le u <| iInf_le_of_le hK <| iInf_le_of_le hu <| iInf_le_of_le htend
    hE.liminf_eq.le

/-! ### Convexity and homogeneity -/

/-- Scaling `u` by `c` scales `½ ∫ |D u|² dm` by `|c|²`. -/
private theorem lintegral_localLipschitzConstant_smul_sq_div_two (c : ℝ) (u : X → ℝ) :
    (∫⁻ x, localLipschitzConstant (c • u) x ^ 2 ∂m) / 2 =
      ‖c‖ₑ ^ 2 * ((∫⁻ x, localLipschitzConstant u x ^ 2 ∂m) / 2) := by
  simp_rw [localLipschitzConstant_const_smul, mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top), mul_div_assoc]

/-- For a convex combination of a continuous `u` and any `v`, the energy `½ ∫ |D ·|² dm` is at most
the convex combination of the energies. -/
private theorem lintegral_localLipschitzConstant_smul_add_smul_sq_div_two_le
    [OpensMeasurableSpace X] {u : X → ℝ} (hu : Continuous u) (v : X → ℝ) {a b : ℝ≥0}
    (hab : a + b = 1) :
    (∫⁻ x, localLipschitzConstant ((a : ℝ) • u + (b : ℝ) • v) x ^ 2 ∂m) / 2 ≤
      a * ((∫⁻ x, localLipschitzConstant u x ^ 2 ∂m) / 2) +
        b * ((∫⁻ x, localLipschitzConstant v x ^ 2 ∂m) / 2) := by
  have hab' : (a : ℝ≥0∞) + b = 1 := by exact_mod_cast hab
  have hpt : ∀ x, localLipschitzConstant ((a : ℝ) • u + (b : ℝ) • v) x ^ 2 ≤
      a * localLipschitzConstant u x ^ 2 + b * localLipschitzConstant v x ^ 2 := fun x ↦
    calc localLipschitzConstant ((a : ℝ) • u + (b : ℝ) • v) x ^ 2
        ≤ ((a : ℝ≥0∞) * localLipschitzConstant u x + b * localLipschitzConstant v x) ^ 2 := by
          gcongr
          simpa [localLipschitzConstant_const_smul] using
            localLipschitzConstant_add_le ((a : ℝ) • u) ((b : ℝ) • v) x
      _ ≤ a * localLipschitzConstant u x ^ 2 + b * localLipschitzConstant v x ^ 2 := by
          simpa [ENNReal.rpow_two] using ENNReal.rpow_arith_mean_le_arith_mean2_rpow _ _
            (localLipschitzConstant u x) (localLipschitzConstant v x) hab' one_le_two
  calc (∫⁻ x, localLipschitzConstant ((a : ℝ) • u + (b : ℝ) • v) x ^ 2 ∂m) / 2
      ≤ (∫⁻ x, a * localLipschitzConstant u x ^ 2 + b * localLipschitzConstant v x ^ 2 ∂m) / 2 :=
        ENNReal.div_le_div_right (lintegral_mono hpt) _
    _ = a * ((∫⁻ x, localLipschitzConstant u x ^ 2 ∂m) / 2) +
          b * ((∫⁻ x, localLipschitzConstant v x ^ 2 ∂m) / 2) := by
        rw [lintegral_add_left ((hu.measurable_localLipschitzConstant.pow_const 2).const_mul _),
          lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          ENNReal.add_div, mul_div_assoc, mul_div_assoc]

/-- The Cheeger energy is convex. -/
theorem convexOn_cheegerEnergy [OpensMeasurableSpace X] :
    ConvexOn ℝ≥0 univ (cheegerEnergy m) := by
  refine ⟨convex_univ, fun f _ g _ a b _ _ hab ↦ ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_add] at hab
    simp [hab]
  rcases eq_or_ne b 0 with rfl | hb
  · rw [add_zero] at hab
    simp [hab]
  rcases eq_or_ne (cheegerEnergy m f) ∞ with hf | hf
  · simp [hf, ENNReal.smul_def, ha]
  rcases eq_or_ne (cheegerEnergy m g) ∞ with hg | hg
  · simp [hg, ENNReal.smul_def, hb]
  obtain ⟨u, hu, hKu, hfu, hEu⟩ := exists_tendsto_cheegerEnergy hf
  obtain ⟨v, hv, hKv, hgv, hEv⟩ := exists_tendsto_cheegerEnergy hg
  have hw : ∀ n, MemLp ((a : ℝ) • u n + (b : ℝ) • v n) 2 m := fun n ↦
    ((hu n).const_smul _).add ((hv n).const_smul _)
  have hKw : ∀ n, ∃ K, LipschitzWith K ((a : ℝ) • u n + (b : ℝ) • v n) := fun n ↦ by
    obtain ⟨K, hK⟩ := hKu n
    obtain ⟨L, hL⟩ := hKv n
    exact ⟨_, ((lipschitzWith_smul (a : ℝ)).comp hK).add ((lipschitzWith_smul (b : ℝ)).comp hL)⟩
  have htend : Tendsto (fun n ↦ (hw n).toLp _) atTop (𝓝 (a • f + b • g)) := by
    rw [NNReal.smul_def, NNReal.smul_def]
    refine ((hfu.const_smul (a : ℝ)).add (hgv.const_smul (b : ℝ))).congr fun n ↦ ?_
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
  calc cheegerEnergy m (a • f + b • g)
      ≤ liminf (fun n ↦
          (∫⁻ x, localLipschitzConstant ((a : ℝ) • u n + (b : ℝ) • v n) x ^ 2 ∂m) / 2) atTop :=
        cheegerEnergy_le_liminf hKw hw htend
    _ ≤ liminf (fun n ↦ a * ((∫⁻ x, localLipschitzConstant (u n) x ^ 2 ∂m) / 2) +
          b * ((∫⁻ x, localLipschitzConstant (v n) x ^ 2 ∂m) / 2)) atTop :=
        liminf_le_liminf <| Eventually.of_forall fun n ↦ by
          obtain ⟨K, hK⟩ := hKu n
          exact lintegral_localLipschitzConstant_smul_add_smul_sq_div_two_le hK.continuous _ hab
    _ = a • cheegerEnergy m f + b • cheegerEnergy m g :=
        ((ENNReal.Tendsto.const_mul hEu (Or.inr ENNReal.coe_ne_top)).add
          (ENNReal.Tendsto.const_mul hEv (Or.inr ENNReal.coe_ne_top))).liminf_eq

private theorem cheegerEnergy_smul_le (c : ℝ) (f : Lp ℝ 2 m) :
    cheegerEnergy m (c • f) ≤ ‖c‖ₑ ^ 2 * cheegerEnergy m f := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne (cheegerEnergy m f) ∞ with hf | hf
  · simp [hf, hc]
  obtain ⟨u, hu, hK, hfu, hE⟩ := exists_tendsto_cheegerEnergy hf
  have hcu : ∀ n, MemLp (c • u n) 2 m := fun n ↦ (hu n).const_smul c
  have hKc : ∀ n, ∃ K, LipschitzWith K (c • u n) := fun n ↦ by
    obtain ⟨K, hK⟩ := hK n
    exact ⟨_, (lipschitzWith_smul c).comp hK⟩
  have htend : Tendsto (fun n ↦ (hcu n).toLp (c • u n)) atTop (𝓝 (c • f)) :=
    (hfu.const_smul c).congr fun n ↦ (MemLp.toLp_const_smul c (hu n)).symm
  refine (cheegerEnergy_le_liminf hKc hcu htend).trans_eq ?_
  simp_rw [lintegral_localLipschitzConstant_smul_sq_div_two]
  exact (ENNReal.Tendsto.const_mul hE (Or.inr (ENNReal.pow_ne_top enorm_ne_top))).liminf_eq

/-- The Cheeger energy is `2`-homogeneous: `Ch(c f) = |c|² Ch(f)`. -/
@[simp]
theorem cheegerEnergy_smul (c : ℝ) (f : Lp ℝ 2 m) :
    cheegerEnergy m (c • f) = ‖c‖ₑ ^ 2 * cheegerEnergy m f := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine (cheegerEnergy_smul_le c f).antisymm ?_
  have h := cheegerEnergy_smul_le c⁻¹ (c • f)
  rw [inv_smul_smul₀ hc] at h
  calc ‖c‖ₑ ^ 2 * cheegerEnergy m f ≤ ‖c‖ₑ ^ 2 * (‖c⁻¹‖ₑ ^ 2 * cheegerEnergy m (c • f)) := by
        gcongr
    _ = cheegerEnergy m (c • f) := by
        rw [← mul_assoc, ← mul_pow, enorm_inv hc,
          ENNReal.mul_inv_cancel (enorm_ne_zero.2 hc) enorm_ne_top, one_pow, one_mul]

/-- The Cheeger energy of `-f` is that of `f`. -/
@[simp]
theorem cheegerEnergy_neg (f : Lp ℝ 2 m) : cheegerEnergy m (-f) = cheegerEnergy m f := by
  simpa using cheegerEnergy_smul (-1) f

/-! ### The Sobolev space `W^{1,2}` -/

variable (m) in
/-- The *domain* of the Cheeger energy: the classes `f ∈ L²(X, m)` of finite Cheeger energy. This
is the Sobolev space `W^{1,2}(X, d, m)` of the metric-measure space; it is a linear subspace of
`L²(X, m)` since the Cheeger energy is convex and `2`-homogeneous. -/
def cheegerEnergyDomain [OpensMeasurableSpace X] : Submodule ℝ (Lp ℝ 2 m) where
  carrier := {f | cheegerEnergy m f ≠ ∞}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    have hfg : f + g = (2 : ℝ) • ((1 / 2 : ℝ≥0) • f + (1 / 2 : ℝ≥0) • g) := by
      rw [NNReal.smul_def, NNReal.smul_def, smul_add, smul_smul, smul_smul]
      norm_num
    have hle := convexOn_cheegerEnergy.2 (mem_univ f) (mem_univ g) zero_le zero_le
      (add_halves (1 : ℝ≥0))
    simp only [mem_ofPred_eq, ENNReal.smul_def, smul_eq_mul] at hf hg hle ⊢
    rw [hfg, cheegerEnergy_smul]
    exact ENNReal.mul_ne_top (by simp) <| ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hf,
        ENNReal.mul_ne_top ENNReal.coe_ne_top hg⟩) hle
  smul_mem' c f hf := by
    simp only [mem_ofPred_eq] at hf ⊢
    rw [cheegerEnergy_smul]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) hf

/-- A class lies in the domain of the Cheeger energy exactly when its Cheeger energy is finite. -/
@[simp]
theorem mem_cheegerEnergyDomain [OpensMeasurableSpace X] {f : Lp ℝ 2 m} :
    f ∈ cheegerEnergyDomain m ↔ cheegerEnergy m f ≠ ∞ :=
  Iff.rfl

end TauCeti
