/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CheegerEnergy.Basic
public import TauCeti.Analysis.Convex.SquareRootSeminorm
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The Cheeger Sobolev norm

The finite domain of Cheeger energy carries the Sobolev norm
`‖f‖² = ‖f‖₂² + 2 Ch(f)`. This is a complete norm even when Cheeger energy is not quadratic.
The inclusion in `L²` is a continuous linear injection. Convergence in the Sobolev norm is
precisely convergence in `L²` together with vanishing Cheeger energy of the differences.

The carrier is a copy of `cheegerEnergyDomain`, so its topology is independent of the topology
that this submodule inherits from `L²`. No Hilbertianity of the underlying metric-measure space
is assumed.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Calculus and heat flow in metric measure spaces and
  applications to spaces with Ricci bounds from below*, Invent. Math. 195 (2014), Section 4.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (m : Measure X)

/-- The finite Cheeger-energy domain, equipped with its Sobolev topology rather than the
subspace topology from `L²`. -/
def CheegerSobolevSpace := ↥(cheegerEnergyDomain m)

namespace CheegerSobolevSpace

instance : AddCommGroup (CheegerSobolevSpace m) :=
  inferInstanceAs (AddCommGroup ↥(cheegerEnergyDomain m))

instance : Module ℝ (CheegerSobolevSpace m) :=
  inferInstanceAs (Module ℝ ↥(cheegerEnergyDomain m))

/-- The underlying `L²` class of a Cheeger Sobolev function. -/
def toLp : CheegerSobolevSpace m →ₗ[ℝ] Lp ℝ 2 m := (cheegerEnergyDomain m).subtype

variable {m}

/-- A class in `L²` of finite Cheeger energy defines a Sobolev function. -/
def mk (f : Lp ℝ 2 m) (hf : cheegerEnergy m f ≠ ∞) : CheegerSobolevSpace m :=
  ⟨f, mem_cheegerEnergyDomain.2 hf⟩

@[simp]
theorem toLp_mk (f : Lp ℝ 2 m) (hf) : toLp m (mk f hf) = f := (rfl)

/-- The inclusion in `L²` is injective. -/
theorem toLp_injective : Function.Injective (toLp m) := Subtype.val_injective

@[ext]
theorem ext {f g : CheegerSobolevSpace m} (h : toLp m f = toLp m g) : f = g :=
  toLp_injective h

/-- Sobolev functions have finite Cheeger energy. -/
theorem cheegerEnergy_ne_top (f : CheegerSobolevSpace m) : cheegerEnergy m (toLp m f) ≠ ∞ :=
  mem_cheegerEnergyDomain.1 f.2

@[simp]
theorem mk_toLp (f : CheegerSobolevSpace m) : mk (toLp m f) f.cheegerEnergy_ne_top = f := (rfl)

/-- The real Cheeger energy is convex on its finite domain. -/
theorem convexOn_toReal_cheegerEnergy :
    ConvexOn ℝ univ (fun f : CheegerSobolevSpace m ↦ (cheegerEnergy m (toLp m f)).toReal) := by
  refine ⟨convex_univ, fun f _ g _ a b ha hb hab ↦ ?_⟩
  let A : ℝ≥0 := ⟨a, ha⟩
  let B : ℝ≥0 := ⟨b, hb⟩
  have hab' : A + B = 1 := NNReal.eq hab
  have h := convexOn_cheegerEnergy.2 (mem_univ (toLp m f)) (mem_univ (toLp m g))
    (show 0 ≤ A from zero_le) (show 0 ≤ B from zero_le) hab'
  have hf := ENNReal.mul_ne_top (a := (A : ℝ≥0∞)) ENNReal.coe_ne_top f.cheegerEnergy_ne_top
  have hg := ENNReal.mul_ne_top (a := (B : ℝ≥0∞)) ENNReal.coe_ne_top g.cheegerEnergy_ne_top
  simp only [NNReal.smul_def A (toLp m f), NNReal.smul_def B (toLp m g),
    ENNReal.smul_def, smul_eq_mul] at h
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf, hg⟩) h
  rw [ENNReal.toReal_add hf hg, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
  have hA : (A : ℝ) = a := (rfl)
  have hB : (B : ℝ) = b := (rfl)
  rw [hA, hB] at hreal
  simpa only [map_add, map_smul, smul_eq_mul] using hreal

private def normSq (f : CheegerSobolevSpace m) : ℝ :=
  ‖toLp m f‖ ^ 2 + 2 * (cheegerEnergy m (toLp m f)).toReal

private theorem normSq_nonneg (f : CheegerSobolevSpace m) : 0 ≤ normSq f := by
  unfold normSq
  positivity

private theorem convexOn_normSq : ConvexOn ℝ univ (normSq (m := m)) :=
  ((convexOn_norm convex_univ).comp_linearMap (toLp m)).pow (fun _ _ ↦ norm_nonneg _) 2 |>.add
    (convexOn_toReal_cheegerEnergy.smul (by norm_num : (0 : ℝ) ≤ 2))

private theorem normSq_smul (c : ℝ) (f : CheegerSobolevSpace m) :
    normSq (c • f) = c ^ 2 * normSq f := by
  simp only [normSq, map_smul, norm_smul, cheegerEnergy_smul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, toReal_enorm, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

instance : Norm (CheegerSobolevSpace m) :=
  ⟨fun f ↦ √(‖toLp m f‖ ^ 2 + 2 * (cheegerEnergy m (toLp m f)).toReal)⟩

/-- The Sobolev norm is the square root of the sum of the squared `L²` norm and twice the
Cheeger energy. -/
theorem norm_def (f : CheegerSobolevSpace m) :
    ‖f‖ = √(‖toLp m f‖ ^ 2 + 2 * (cheegerEnergy m (toLp m f)).toReal) := (rfl)

private theorem normedSpaceCore : NormedSpace.Core ℝ (CheegerSobolevSpace m) where
  norm_nonneg f := Real.sqrt_nonneg _
  norm_smul c f := by
    simpa only [squareRootSeminorm_apply, normSq, norm_def] using
      map_smul_eq_mul (squareRootSeminorm normSq convexOn_normSq normSq_smul) c f
  norm_triangle := sqrt_add_le_of_convexOn_smul_sq convexOn_normSq normSq_smul
  norm_eq_zero_iff f := by
    constructor
    · intro h
      apply toLp_injective
      have hsq := Real.sq_sqrt (normSq_nonneg f)
      dsimp only [normSq] at hsq
      rw [← norm_def] at hsq
      rw [h] at hsq
      have hn : ‖toLp m f‖ = 0 := by
        nlinarith [ENNReal.toReal_nonneg (a := cheegerEnergy m (toLp m f))]
      simpa using norm_eq_zero.1 hn
    · rintro rfl
      simp [norm_def]

instance : NormedAddCommGroup (CheegerSobolevSpace m) := by
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) (by exact normedSpaceCore (m := m))
instance : NormedSpace ℝ (CheegerSobolevSpace m) := by
  exact NormedSpace.ofCore (by exact normedSpaceCore (m := m))

/-- The square of the Sobolev norm. -/
theorem norm_sq (f : CheegerSobolevSpace m) :
    ‖f‖ ^ 2 = ‖toLp m f‖ ^ 2 + 2 * (cheegerEnergy m (toLp m f)).toReal :=
  Real.sq_sqrt (normSq_nonneg f)

/-- The inclusion in `L²` decreases the norm. -/
theorem norm_toLp_le (f : CheegerSobolevSpace m) : ‖toLp m f‖ ≤ ‖f‖ := by
  have h := norm_sq f
  nlinarith [norm_nonneg f, norm_nonneg (toLp m f),
    ENNReal.toReal_nonneg (a := cheegerEnergy m (toLp m f))]

/-- Twice the Cheeger energy is bounded by the squared Sobolev norm. -/
theorem two_mul_cheegerEnergy_le (f : CheegerSobolevSpace m) :
    2 * cheegerEnergy m (toLp m f) ≤ ENNReal.ofReal (‖f‖ ^ 2) := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (by norm_num) f.cheegerEnergy_ne_top) ENNReal.ofReal_ne_top).1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  nlinarith [norm_sq f, sq_nonneg ‖toLp m f‖]

/-- The continuous linear inclusion of the Cheeger Sobolev space in `L²`. -/
def toLpCLM : CheegerSobolevSpace m →L[ℝ] Lp ℝ 2 m :=
  (toLp m).mkContinuous 1 (fun f ↦ by simpa using norm_toLp_le (m := m) f)

@[simp]
theorem toLpCLM_apply (f : CheegerSobolevSpace m) : toLpCLM f = toLp m f := (rfl)

/-- The extended-valued formula for the square of the Sobolev norm. -/
theorem enorm_sq (f : CheegerSobolevSpace m) :
    ‖f‖ₑ ^ 2 = ‖toLp m f‖ₑ ^ 2 + 2 * cheegerEnergy m (toLp m f) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by
    exact ENNReal.add_ne_top.2 ⟨by finiteness,
      ENNReal.mul_ne_top (by norm_num) f.cheegerEnergy_ne_top⟩)).1
  rw [ENNReal.toReal_add (by finiteness)
    (ENNReal.mul_ne_top (by norm_num) f.cheegerEnergy_ne_top)]
  simp only [ENNReal.toReal_pow, toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofNat, norm_sq]

omit [OpensMeasurableSpace X] in
private theorem lowerSemicontinuous_enorm_sq_add_cheegerEnergy :
    LowerSemicontinuous fun f : Lp ℝ 2 m ↦ ‖f‖ₑ ^ 2 + 2 * cheegerEnergy m f := by
  refine ((ENNReal.continuous_pow 2).comp continuous_enorm).lowerSemicontinuous.add ?_
  exact (ENNReal.continuous_const_mul (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).comp_lowerSemicontinuous
    lowerSemicontinuous_cheegerEnergy (fun _ _ h ↦ by dsimp only; gcongr)

/-- An `L²` limit of functions with a common Sobolev norm bound has finite Cheeger energy
and satisfies the same bound. The convergence filter may be arbitrary and nontrivial. -/
theorem exists_toLp_eq_norm_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → CheegerSobolevSpace m} {f : Lp ℝ 2 m} {r : ℝ}
    (hu : Tendsto (fun i ↦ toLp m (u i)) l (𝓝 f)) (hr : 0 ≤ r)
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ r) :
    ∃ g : CheegerSobolevSpace m, toLp m g = f ∧ ‖g‖ ≤ r := by
  have hclosed := lowerSemicontinuous_enorm_sq_add_cheegerEnergy (m := m)
    |>.isClosed_preimage (ENNReal.ofReal (r ^ 2))
  have hlim : ‖f‖ₑ ^ 2 + 2 * cheegerEnergy m f ≤ ENNReal.ofReal (r ^ 2) := by
    apply hclosed.mem_of_tendsto hu
    filter_upwards [hbound] with i hi
    rw [mem_preimage, mem_Iic, ← enorm_sq, ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hi 2)
  have henergy : cheegerEnergy m f ≤ ‖f‖ₑ ^ 2 + 2 * cheegerEnergy m f := by
    calc cheegerEnergy m f ≤ 2 * cheegerEnergy m f := by
          exact le_mul_of_one_le_left' (by norm_num)
      _ ≤ ‖f‖ₑ ^ 2 + 2 * cheegerEnergy m f := le_add_left le_rfl
  have hf : cheegerEnergy m f ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (henergy.trans hlim)
  refine ⟨mk f hf, toLp_mk f hf, ?_⟩
  have hle : ‖mk f hf‖ₑ ^ 2 ≤ ENNReal.ofReal (r ^ 2) := by
    simpa only [enorm_sq, toLp_mk] using hlim
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)] at hle
  nlinarith [norm_nonneg (mk f hf)]

/-- Sobolev convergence is exactly `L²` convergence together with vanishing Cheeger energy
of the differences. No sequentiality assumption on the convergence filter is needed. -/
theorem tendsto_iff_toLp_cheegerEnergy {ι : Type*} {l : Filter ι}
    {u : ι → CheegerSobolevSpace m} {f : CheegerSobolevSpace m} :
    Tendsto u l (𝓝 f) ↔ Tendsto (fun i ↦ toLp m (u i)) l (𝓝 (toLp m f)) ∧
      Tendsto (fun i ↦ cheegerEnergy m (toLp m (u i) - toLp m f)) l (𝓝 0) := by
  have hfin (i) : cheegerEnergy m (toLp m (u i) - toLp m f) ≠ ∞ := by
    simpa only [map_sub] using (u i - f).cheegerEnergy_ne_top
  constructor
  · intro h
    refine ⟨(toLpCLM (m := m)).continuous.tendsto f |>.comp h, ?_⟩
    have hn := (tendsto_iff_norm_sub_tendsto_zero.1 h).pow 2
    have hE : Tendsto (fun i ↦ (cheegerEnergy m (toLp m (u i) - toLp m f)).toReal)
        l (𝓝 0) := squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg) (fun i ↦ ?_) (by simpa using hn)
    · exact (ENNReal.tendsto_toReal_zero_iff hfin).1 hE
    · have hi := norm_sq (u i - f)
      simp only [map_sub] at hi
      nlinarith [sq_nonneg ‖toLp m (u i) - toLp m f‖,
        ENNReal.toReal_nonneg (a := cheegerEnergy m (toLp m (u i) - toLp m f))]
  · rintro ⟨hL, hE⟩
    have hn := (tendsto_iff_norm_sub_tendsto_zero.1 hL).pow 2
    have hEr := (ENNReal.tendsto_toReal_zero_iff hfin).2 hE
    have htotal : Tendsto (fun i ↦ ‖toLp m (u i) - toLp m f‖ ^ 2 +
        2 * (cheegerEnergy m (toLp m (u i) - toLp m f)).toReal) l (𝓝 0) := by
      simpa using hn.add (hEr.const_mul 2)
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [norm_def, map_sub, Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp htotal

/-- The Cheeger Sobolev space is complete in its Sobolev norm, without assuming that Cheeger
energy is quadratic or that the reference measure is finite. -/
instance instCompleteSpace : CompleteSpace (CheegerSobolevSpace m) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have huc : CauchySeq (fun n ↦ toLp m (u n)) :=
    (toLpCLM (m := m)).uniformContinuous.comp_cauchySeq hu
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete huc
  obtain ⟨r, hr⟩ := hu.norm_bddAbove
  have hr0 : 0 ≤ r := (norm_nonneg (u 0)).trans (hr (mem_range_self 0))
  obtain ⟨g, hg, -⟩ := exists_toLp_eq_norm_le_of_tendsto hf hr0
    (Eventually.of_forall fun n ↦ hr (mem_range_self n))
  refine ⟨g, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hlim : Tendsto (fun k ↦ toLp m (u n - u k)) atTop (𝓝 (toLp m (u n - g))) := by
    simpa only [map_sub, hg] using tendsto_const_nhds.sub hf
  obtain ⟨w, hw, hwr⟩ := exists_toLp_eq_norm_le_of_tendsto hlim (half_pos hε).le
    (eventually_atTop.2 ⟨N, fun k hk ↦ by
      simpa only [dist_eq_norm] using (hN n hn k hk).le⟩)
  have hw' : w = u n - g := toLp_injective hw
  rw [hw'] at hwr
  simpa only [dist_eq_norm] using hwr.trans_lt (half_lt_self hε)

end CheegerSobolevSpace

end TauCeti
