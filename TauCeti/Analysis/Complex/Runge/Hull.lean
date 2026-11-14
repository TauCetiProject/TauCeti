/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Analysis.Normed.Module.Exhaustion
import TauCeti.Topology.ConnectedComponents

/-!
# Holomorphic hulls and explicit Runge exhaustions

For an open subset `Ω ⊆ ℂ` and a subset `K ⊆ Ω`, the **holomorphic hull**
`TauCeti.holomorphicHull Ω K` consists of all points `z ∈ Ω` where every holomorphic function on
`Ω` satisfies every real modulus bound it satisfies on `K`. For compact `K ⊆ Ω`, this is the set
of `z ∈ Ω` with `‖f z‖ ≤ sup_K ‖f‖` for every `f` holomorphic on `Ω`; for `K = ∅`, universal
bounds force the hull to be empty.

This file establishes the pre-Runge theory of `holomorphicHull` and constructs the explicit Runge
exhaustion:

* Extensivity, monotonicity, idempotence, and compactness of `holomorphicHull Ω K` (proved directly
  using `z ↦ z` for boundedness and `z ↦ (z - ζ)⁻¹` for `ζ ∉ Ω` to stay inside `Ω`).
* Maximum-principle inclusion: `K` together with every component of `Ω \ K` having compact closure
  inside `Ω` lies in `holomorphicHull Ω K` (the reverse inclusion is proved after Runge
  approximation in `TauCeti.Analysis.Complex.Runge.Approximation`).
* Filledness of `holomorphicHull Ω K` in `Ω`, equality of extended distances to `Ωᶜ`, inclusion
  in `convexHull ℝ K`, and comparison with `TauCeti.polynomialHull` when `Ω = Set.univ`.
* Explicit Runge exhaustion `TauCeti.rungeExhaustion Ω n` defined as
  `closedBall 0 (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ` in a proper real normed space, with
  compactness, filledness in `Ω`, nested interiors
  `rungeExhaustion Ω n ⊆ interior (rungeExhaustion Ω (n + 1))`, union `Ω`, and compact cofinality.

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 11.3 and proof of Theorem 12.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Complex Filter Metric Set Topology
open scoped ENNReal

namespace TauCeti

section HolomorphicHull

/-- The holomorphic hull of `K` inside `Ω`: all points `z ∈ Ω` where every `Ω`-holomorphic
function satisfies every real modulus bound it satisfies on `K`. Universal bounds make the hull of
the empty set empty. -/
def holomorphicHull (Ω K : Set ℂ) : Set ℂ :=
  {z | z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
    ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B}

/-- Membership in `TauCeti.holomorphicHull`. -/
theorem mem_holomorphicHull_iff {Ω K : Set ℂ} {z : ℂ} :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
        ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B :=
  Iff.rfl

/-- The holomorphic hull of any set lies inside the ambient domain `Ω`. -/
theorem holomorphicHull_subset {Ω K : Set ℂ} : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz => hz.1

/-- Extensivity: a subset `K ⊆ Ω` is contained in its holomorphic hull in `Ω`. -/
theorem subset_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  fun z hz => ⟨hKΩ hz, fun _ _ _ hB => hB z hz⟩

/-- Monotonicity of `TauCeti.holomorphicHull` in the subset `K`. -/
@[gcongr]
theorem holomorphicHull_mono {Ω K L : Set ℂ} (hKL : K ⊆ L) :
    holomorphicHull Ω K ⊆ holomorphicHull Ω L :=
  fun _ hz => ⟨hz.1, fun f hf B hB => hz.2 f hf B fun w hw => hB w (hKL hw)⟩

/-- The holomorphic hull of the empty set is empty. -/
@[simp]
theorem holomorphicHull_empty (Ω : Set ℂ) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun z hz => by
    have h := hz.2 (fun _ => 0) (differentiableOn_const 0) (-1) (by simp)
    norm_num at h

/-- Idempotence of `TauCeti.holomorphicHull`. -/
@[simp]
theorem holomorphicHull_idem (Ω K : Set ℂ) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  (subset_holomorphicHull holomorphicHull_subset).antisymm' fun _ hz =>
    ⟨hz.1, fun f hf B hB => hz.2 f hf B fun _ hw => hw.2 f hf B hB⟩

/-- For compact `K ⊆ Ω`, `holomorphicHull Ω K` is closed in `ℂ` and bounded, hence compact, without
using any approximation theorem. -/
theorem isCompact_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : IsCompact (holomorphicHull Ω K) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  -- Boundedness comes from the identity function `z ↦ z`.
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hbound : holomorphicHull Ω K ⊆ closedBall 0 R := fun z hz => by
    have hzR := hz.2 id differentiableOn_id R fun w hw => by
      simpa only [id_eq, mem_closedBall, dist_zero_right] using hR hw
    simpa only [id_eq, mem_closedBall, dist_zero_right] using hzR
  -- Closedness in `ℂ`: points outside `Ω` are separated from `K` by `1 / (z - ζ)`.
  have hclosed : IsClosed (holomorphicHull Ω K) := by
    refine closure_subset_iff_isClosed.mp fun ζ hζ => ?_
    have hζΩ : ζ ∈ Ω := by
      by_contra hζnΩ
      have hζK : ζ ∉ K := fun h => hζnΩ (hKΩ h)
      have hcont : ContinuousOn (fun w : ℂ => ‖(w - ζ)⁻¹‖) K :=
        ((continuousOn_id.sub continuousOn_const).inv₀
          fun w hw => sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hζK)).norm
      obtain ⟨w₀, hw₀, hw₀max⟩ := hK.exists_isMaxOn hKne hcont
      set M := ‖(w₀ - ζ)⁻¹‖
      have hM : 0 < M := by
        refine norm_pos_iff.mpr (inv_ne_zero (sub_ne_zero.mpr ?_))
        intro h
        exact hζK (h ▸ hw₀)
      have hf : DifferentiableOn ℂ (fun w : ℂ => (w - ζ)⁻¹) Ω :=
        ((differentiableOn_id (𝕜 := ℂ)).sub_const ζ).inv
          fun w hw => sub_ne_zero.mpr fun h => hζnΩ (h ▸ hw)
      have hdisj : ∀ z ∈ holomorphicHull Ω K, M⁻¹ ≤ dist z ζ := fun z hz => by
        have hle : ‖(z - ζ)⁻¹‖ ≤ M := hz.2 _ hf M fun w hw => hw₀max hw
        have hzζ : z ≠ ζ := fun h => hζnΩ (h ▸ hz.1)
        rw [dist_eq_norm]
        calc M⁻¹ ≤ ‖(z - ζ)⁻¹‖⁻¹ :=
              inv_anti₀ (norm_pos_iff.mpr (inv_ne_zero (sub_ne_zero.mpr hzζ))) hle
          _ = ‖z - ζ‖ := by rw [norm_inv, inv_inv]
      obtain ⟨z, hzH, hzball⟩ := Metric.mem_closure_iff.mp hζ M⁻¹ (inv_pos.mpr hM)
      rw [dist_comm] at hzball
      exact (hdisj z hzH).not_gt hzball
    refine ⟨hζΩ, fun f hf B hB => ?_⟩
    have hfc : ContinuousAt f ζ := hf.continuousOn.continuousAt (hΩ.mem_nhds hζΩ)
    have hlim : Tendsto (fun z => ‖f z‖) (𝓝[holomorphicHull Ω K] ζ) (𝓝 ‖f ζ‖) :=
      hfc.norm.continuousWithinAt.tendsto
    have hne : (𝓝[holomorphicHull Ω K] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζ
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun z hz => hz.2 f hf B hB)
  exact (isCompact_closedBall 0 R).of_isClosed_subset hclosed hbound

/-- **Maximum-principle inclusion.** Every connected component of `Ω \ K` whose closure is compact
and contained in `Ω` lies inside `holomorphicHull Ω K` (the reverse inclusion is proved after
Runge approximation). -/
theorem fill_subset_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    K ∪ {z | z ∈ Ω \ K ∧ IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} ⊆ holomorphicHull Ω K := by
  rintro z (hzK | ⟨hzΩK, hcpt, hsub⟩)
  · exact subset_holomorphicHull hKΩ hzK
  refine ⟨hzΩK.1, fun f hf B hB => ?_⟩
  set C := connectedComponentIn (Ω \ K) z
  have hfr : frontier C ⊆ K := fun w hw => by
    have hwΩ : w ∈ Ω := hsub (frontier_subset_closure hw)
    have hwn := frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK.isClosed) z hw
    by_contra hwK
    exact hwn ⟨hwΩ, hwK⟩
  have hdiff : DiffContOnCl ℂ f C :=
    ⟨hf.mono ((connectedComponentIn_subset _ _).trans sdiff_subset), hf.continuousOn.mono hsub⟩
  exact Complex.norm_le_of_forall_mem_frontier_norm_le (hcpt.isBounded.subset subset_closure)
    hdiff (fun w hw => hB w (hfr hw)) (subset_closure (mem_connectedComponentIn hzΩK))

/-- The holomorphic hull of a compact set `K ⊆ Ω` is filled in `Ω`. -/
theorem isFilledIn_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : IsFilledIn (holomorphicHull Ω K) Ω := by
  rw [isFilledIn_iff]
  intro z hz ⟨hcpt, hsub⟩
  have hHK := isCompact_holomorphicHull hΩ hK hKΩ
  have hz_mem : z ∈ holomorphicHull Ω K := by
    have hsub_hull := fill_subset_holomorphicHull hΩ hHK holomorphicHull_subset
      (Or.inr ⟨hz, hcpt, hsub⟩)
    rwa [holomorphicHull_idem] at hsub_hull
  exact hz.2 hz_mem

/-- Extended distance to `Ωᶜ` is preserved by taking the holomorphic hull of a compact subset
`K ⊆ Ω`. Empty infima equal `⊤`, covering `K = ∅` and `Ω = Set.univ`. -/
theorem iInf_edist_holomorphicHull_eq {Ω K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ w ∈ Ωᶜ, edist z w) =
      (⨅ z ∈ K, ⨅ w ∈ Ωᶜ, edist z w) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun a ha => le_iInf₂ fun w hw => ?_
    exact iInf₂_le_of_le a (subset_holomorphicHull hKΩ ha) (iInf₂_le w hw)
  · refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · simp at hz
    have hwK : w ∉ K := fun h => hw (hKΩ h)
    have hcont : ContinuousOn (fun a : ℂ => ‖(a - w)⁻¹‖) K :=
      ((continuousOn_id.sub continuousOn_const).inv₀
        fun a ha => sub_ne_zero.mpr (ne_of_mem_of_not_mem ha hwK)).norm
    obtain ⟨a₀, ha₀, ha₀max⟩ := hK.exists_isMaxOn hKne hcont
    have hf : DifferentiableOn ℂ (fun a : ℂ => (a - w)⁻¹) Ω :=
      ((differentiableOn_id (𝕜 := ℂ)).sub_const w).inv
        fun a ha => sub_ne_zero.mpr fun h => hw (h ▸ ha)
    have hle : ‖(z - w)⁻¹‖ ≤ ‖(a₀ - w)⁻¹‖ := hz.2 _ hf _ fun a ha => ha₀max ha
    have hdist : ‖a₀ - w‖ ≤ ‖z - w‖ := by
      have ha₀ne : a₀ - w ≠ 0 := sub_ne_zero.mpr (by intro h; exact hwK (h ▸ ha₀))
      have hzne : z - w ≠ 0 := sub_ne_zero.mpr fun h => hw (h ▸ hz.1)
      rw [norm_inv, norm_inv, inv_le_inv₀ (norm_pos_iff.mpr hzne) (norm_pos_iff.mpr ha₀ne)] at hle
      exact hle
    calc
      (⨅ a ∈ K, ⨅ b ∈ Ωᶜ, edist a b) ≤ edist a₀ w :=
        iInf₂_le_of_le a₀ ha₀ (iInf₂_le w hw)
      _ ≤ edist z w := by
        simpa only [edist_dist, dist_eq_norm] using ENNReal.ofReal_le_ofReal hdist

/-- For compact `K`, the holomorphic hull in `Ω` lies inside `convexHull ℝ K`. -/
theorem holomorphicHull_subset_convexHull {Ω K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull Ω K ⊆ convexHull ℝ K := by
  intro z hz
  rcases K.eq_empty_or_nonempty with rfl | _hKne
  · simp at hz
  by_contra hz_conv
  have hconv_cpt : IsCompact (convexHull ℝ K) := IsCompact.convexHull hK
  obtain ⟨ℓ, u, hℓ_lt, hu_lt⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ K) hconv_cpt.isClosed hz_conv
  -- Build a `ℂ`-linear functional whose real part is `-ℓ`.
  let φ : ℂ → ℂ := fun w => ((-ℓ w : ℝ) : ℂ) + I * (ℓ (I * w) : ℂ)
  have hφ_add : ∀ x y : ℂ, φ (x + y) = φ x + φ y := fun x y => by
    simp only [φ, mul_add, map_add, neg_add, Complex.ofReal_add]
    ring
  have hφ_smul : ∀ c x : ℂ, φ (c * x) = c * φ x := fun c x => by
    have h1 : c * x = c.re • x + c.im • (I * x) := by
      apply Complex.ext
      · simp [sub_eq_add_neg]
      · simp
    have hI : φ (I * x) = I * φ x := by
      apply Complex.ext <;> simp [φ, ← mul_assoc]
    have hreal (r : ℝ) (y : ℂ) : φ (r • y) = (r : ℂ) * φ y := by
      have hlr : ℓ ((r : ℂ) * y) = r * ℓ y := by
        rw [← Complex.real_smul, map_smul, smul_eq_mul]
      have hlI : ℓ (I * ((r : ℂ) * y)) = r * ℓ (I * y) := by
        rw [mul_left_comm, ← Complex.real_smul, map_smul, smul_eq_mul]
      apply Complex.ext <;> simp [φ, hlr, hlI]
    rw [h1, hφ_add, hreal c.re x, hreal c.im (I * x), hI]
    apply Complex.ext
    · simp [φ, sub_eq_add_neg]
    · simp [φ]
  let L : ℂ →L[ℂ] ℂ :=
    { toFun := φ
      map_add' := hφ_add
      map_smul' := hφ_smul
      cont := by
        refine Continuous.add (Complex.continuous_ofReal.comp ℓ.continuous.neg)
          (continuous_const.mul (Complex.continuous_ofReal.comp
            (ℓ.continuous.comp (continuous_const.mul continuous_id)))) }
  have hf : DifferentiableOn ℂ (fun w => Complex.exp (φ w)) Ω :=
    (L.differentiable.cexp).differentiableOn
  have hre (w : ℂ) : (φ w).re = -ℓ w := by
    simp [φ]
  have hnorm (w : ℂ) : ‖Complex.exp (φ w)‖ = Real.exp (-ℓ w) := by
    rw [Complex.norm_exp, hre]
  have hB : ∀ w ∈ K, ‖Complex.exp (φ w)‖ ≤ Real.exp (-u) := fun w hw => by
    rw [hnorm]
    exact Real.exp_le_exp.mpr (neg_le_neg (hu_lt w (subset_convexHull ℝ K hw)).le)
  have hzle := hz.2 _ hf (Real.exp (-u)) hB
  rw [hnorm] at hzle
  exact (Real.exp_lt_exp.mpr (neg_lt_neg hℓ_lt)).not_ge hzle

/-- For `Ω = Set.univ` and compact `K ⊆ ℂ`, `holomorphicHull Set.univ K` coincides with
`TauCeti.polynomialHull` under the canonical identification `z ↦ (fun _ : Fin 1 => z)`. -/
theorem holomorphicHull_univ_eq_preimage_polynomialHull {K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull Set.univ K =
      (fun z (_ : Fin 1) => z) ⁻¹' polynomialHull ((fun z (_ : Fin 1) => z) '' K) := by
  let e : ℂ → Fin 1 → ℂ := fun z _ => z
  have he : Differentiable ℂ e := differentiable_pi.mpr fun _ => differentiable_id
  refine Subset.antisymm (fun z hz => ?_) (fun z hz => ⟨mem_univ z, fun f hf B hB => ?_⟩)
  · rw [mem_preimage, mem_polynomialHull_iff]
    intro p c hpc
    have hdiff : DifferentiableOn ℂ (fun w => MvPolynomial.eval (e w) p) Set.univ := fun w _ =>
      ((AnalyticOnNhd.eval_mvPolynomial p (e w) trivial).differentiableAt.comp
        w (he w)).differentiableWithinAt
    have hBK : ∀ w ∈ K, ‖MvPolynomial.eval (e w) p‖ ≤ c := fun w hw =>
      hpc (e w) (mem_image_of_mem e hw)
    exact hz.2 _ hdiff c hBK
  · -- Approximate the entire function `f` uniformly on `K ∪ {z}` by Taylor polynomials at `0`.
    obtain ⟨R₀, hR₀⟩ := (hK.insert z).isBounded.subset_ball 0
    set R : NNReal := (max R₀ 1).toNNReal
    have hR : (R : ℝ) = max R₀ 1 := Real.coe_toNNReal _ (le_max_of_le_right zero_le_one)
    have hRpos : 0 < R := by
      rw [← NNReal.coe_pos, hR]
      exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    set R' : NNReal := R + 1
    have hR'pos : 0 < R' := lt_of_lt_of_le hRpos (le_self_add)
    have hKsub : K ⊆ ball (0 : ℂ) R := fun w hw =>
      ball_subset_ball (hR ▸ le_max_left _ _) (hR₀ (mem_insert_of_mem z hw))
    have hzball : z ∈ ball (0 : ℂ) R :=
      ball_subset_ball (hR ▸ le_max_left _ _) (hR₀ (mem_insert z K))
    have hps := (hf.mono (subset_univ (closedBall (0 : ℂ) R'))).hasFPowerSeriesOnBall hR'pos
    have hu := hps.tendstoUniformlyOn (r' := R) (ENNReal.coe_lt_coe.2 (lt_add_one R))
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 hu (ε / 2) (half_pos hε)).exists
    set p := cauchyPowerSeries f 0 R'
    set P : MvPolynomial (Fin 1) ℂ :=
      ∑ n ∈ Finset.range N, MvPolynomial.C (p.coeff n) * (MvPolynomial.X 0) ^ n
    have hP_eval (w : ℂ) : MvPolynomial.eval (e w) P = p.partialSum N w := by
      simp only [P, map_sum, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, e,
        FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
        smul_eq_mul, mul_comm]
    have hPK : ∀ y ∈ e '' K, ‖MvPolynomial.eval y P‖ ≤ B + ε / 2 := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hP_eval w]
      have hdist := hN w (hKsub hw)
      rw [zero_add, dist_eq_norm, norm_sub_rev] at hdist
      calc ‖p.partialSum N w‖ ≤ ‖f w‖ + ‖p.partialSum N w - f w‖ := by
            simpa only [add_sub_cancel] using norm_add_le (f w) (p.partialSum N w - f w)
        _ ≤ B + ε / 2 := add_le_add (hB w hw) hdist.le
    have hPz : ‖MvPolynomial.eval (e z) P‖ ≤ B + ε / 2 :=
      mem_polynomialHull_iff.mp hz P (B + ε / 2) hPK
    rw [hP_eval z] at hPz
    have hzdist := hN z hzball
    rw [zero_add, dist_eq_norm] at hzdist
    calc ‖f z‖ ≤ ‖p.partialSum N z‖ + ‖f z - p.partialSum N z‖ := by
          simpa only [add_sub_cancel] using norm_add_le (p.partialSum N z) (f z - p.partialSum N z)
      _ ≤ (B + ε / 2) + ε / 2 := add_le_add hPz hzdist.le
      _ = B + ε := by ring

end HolomorphicHull

section RungeExhaustion

variable {E : Type*} [NormedAddCommGroup E]

/-- The explicit Runge exhaustion of an open subset `Ω` of a proper real normed space:
`rungeExhaustion Ω n = closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ`. -/
noncomputable def rungeExhaustion (Ω : Set E) (n : ℕ) : Set E :=
  closedBall (0 : E) (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ

/-- Unfolding `TauCeti.rungeExhaustion`. -/
theorem rungeExhaustion_def (Ω : Set E) (n : ℕ) :
    rungeExhaustion Ω n = closedBall (0 : E) (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ :=
  (rfl)

/-- Each stage of `TauCeti.rungeExhaustion` is compact. -/
theorem isCompact_rungeExhaustion [ProperSpace E] (Ω : Set E) (n : ℕ) :
    IsCompact (rungeExhaustion Ω n) :=
  (isCompact_closedBall (0 : E) _).diff isOpen_thickening

/-- Each stage of `TauCeti.rungeExhaustion` is contained in `Ω`. -/
theorem rungeExhaustion_subset (Ω : Set E) (n : ℕ) : rungeExhaustion Ω n ⊆ Ω := fun _ hx => by
  by_contra hxΩ
  exact hx.2 (self_subset_thickening (by positivity) _ hxΩ)

/-- Successive stages of `TauCeti.rungeExhaustion` nest into each other's interiors:
`rungeExhaustion Ω n ⊆ interior (rungeExhaustion Ω (n + 1))`. -/
theorem rungeExhaustion_subset_interior_succ (Ω : Set E) (n : ℕ) :
    rungeExhaustion Ω n ⊆ interior (rungeExhaustion Ω (n + 1)) := by
  have hopen : IsOpen (ball (0 : E) (n + 1 + 1) \ cthickening (n + 1 + 1 : ℝ)⁻¹ Ωᶜ) :=
    isOpen_ball.sdiff isClosed_cthickening
  refine Subset.trans ?_ (hopen.subset_interior_iff.mpr ?_)
  · rintro x ⟨hx₁, hx₂⟩
    refine ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx₁).trans_lt (by linarith)),
      fun h => hx₂ (cthickening_subset_thickening' (by positivity) ?_ _ h)⟩
    gcongr
    linarith
  · simp only [rungeExhaustion_def, Nat.cast_add, Nat.cast_one]
    exact sdiff_subset_sdiff ball_subset_closedBall (thickening_subset_cthickening _ _)

/-- Monotonicity of `TauCeti.rungeExhaustion`. -/
theorem monotone_rungeExhaustion (Ω : Set E) : Monotone (rungeExhaustion Ω) :=
  monotone_nat_of_le_succ fun n => (rungeExhaustion_subset_interior_succ Ω n).trans interior_subset

/-- The stages of `TauCeti.rungeExhaustion` cover an open `Ω`. -/
theorem iUnion_rungeExhaustion {Ω : Set E} (hΩ : IsOpen Ω) :
    ⋃ n, rungeExhaustion Ω n = Ω := by
  refine Subset.antisymm (iUnion_subset (rungeExhaustion_subset Ω)) fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ ε⁻¹)
  have hn₁ : ‖x‖ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : ε⁻¹ < n + 1 := ((le_max_right _ _).trans hn).trans_lt (by linarith)
  refine mem_iUnion.mpr ⟨n, mem_closedBall_zero_iff.mpr (by linarith), fun h => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp h
  refine hy (hball ?_)
  rw [mem_ball, dist_comm]
  exact hxy.trans (inv_lt_of_inv_lt₀ hε hn₂)

/-- Compact cofinality: every compact subset of an open `Ω` is contained in some stage of
`TauCeti.rungeExhaustion Ω`. -/
theorem exists_subset_rungeExhaustion_of_isCompact {Ω K : Set E} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ n : ℕ, K ⊆ rungeExhaustion Ω n := by
  have hcov : K ⊆ ⋃ n, interior (rungeExhaustion Ω (n + 1)) := fun x hx => by
    obtain ⟨n, hn⟩ := mem_iUnion.mp ((iUnion_rungeExhaustion hΩ).symm ▸ hKΩ hx)
    exact mem_iUnion.mpr ⟨n, rungeExhaustion_subset_interior_succ Ω n hn⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n => interior (rungeExhaustion Ω (n + 1)))
    (fun _ => isOpen_interior) hcov
  refine ⟨t.sup id + 1, fun x hx => ?_⟩
  obtain ⟨n, hnt, hnx⟩ := mem_iUnion₂.mp (ht hx)
  have hle : n + 1 ≤ t.sup id + 1 := Nat.succ_le_succ (Finset.le_sup (f := id) hnt)
  exact monotone_rungeExhaustion Ω hle (interior_subset hnx)

section Proper

variable [NormedSpace ℝ E] [ProperSpace E]

/-- Each stage of `TauCeti.rungeExhaustion` is filled in an open `Ω`. -/
theorem isFilledIn_rungeExhaustion {Ω : Set E} (hΩ : IsOpen Ω) (n : ℕ) :
    IsFilledIn (rungeExhaustion Ω n) Ω :=
  hΩ.isFilledIn_closedBall_sdiff_thickening 0 (by positivity) (by positivity)

end Proper

end RungeExhaustion

end TauCeti
