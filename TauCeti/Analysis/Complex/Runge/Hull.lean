/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Analysis.Normed.Module.InfDist

/-!
# Holomorphic hulls

For a subset `Ω ⊆ ℂ` and a subset `K ⊆ Ω`, the **holomorphic hull** `TauCeti.holomorphicHull Ω K`
consists of all points `z ∈ Ω` where every holomorphic function on `Ω` satisfies every real modulus
bound it satisfies on `K`. For compact `K ⊆ Ω`, this is the set of `z ∈ Ω` with
`‖f z‖ ≤ sup_K ‖f‖` for every `f` holomorphic on `Ω`; for `K = ∅`, universal bounds force the hull
to be empty.

Holomorphic hulls govern Runge approximation on open domains `Ω ⊆ ℂ`: as established in
`TauCeti.Analysis.Complex.Runge.Approximation`, a compact set `K ⊆ Ω` admits uniform approximation
by `Ω`-holomorphic functions if and only if `holomorphicHull Ω K = K` (equivalently, `K` has no
relatively compact complementary components in `Ω`), and telescoping such approximations along the
explicit filled compact exhaustion `TauCeti.rungeExhaustion Ω`
(`TauCeti.Analysis.Normed.Module.Exhaustion`) constructs global holomorphic functions on `Ω`.

## Main declarations and results

* `TauCeti.holomorphicHull`: the `Ω`-holomorphic hull of `K`, with extensivity, monotonicity in
  both `Ω` and `K`, empty normal forms, and idempotence.
* `TauCeti.iInf_edist_holomorphicHull_eq` and
  `TauCeti.iInf_infDist_frontier_holomorphicHull_eq`: preservation of extended distance to `Ωᶜ`
  and real distance to `frontier Ω`.
* `TauCeti.isCompact_holomorphicHull`: compactness of `holomorphicHull Ω K` for compact `K ⊆ Ω`.
* `TauCeti.fillIn_subset_holomorphicHull` and `TauCeti.isFilledIn_holomorphicHull`:
  maximum-principle inclusion of `TauCeti.fillIn K Ω` in `holomorphicHull Ω K`, and filledness of
  `holomorphicHull Ω K` in an open `Ω`.
* `TauCeti.holomorphicHull_subset_convexHull`: inclusion in `convexHull ℝ K` for compact `K`.
* `TauCeti.holomorphicHull_univ_eq_preimage_polynomialHull` and
  `TauCeti.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex`: comparison with
  `TauCeti.polynomialHull` and `TauCeti.IsPolynomiallyConvex` when `Ω = Set.univ` and `K` is
  bounded.

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 11.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Complex Filter Metric Set Topology
open scoped ENNReal

namespace TauCeti

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
  (Iff.rfl)

/-- The holomorphic hull of any set lies inside the ambient set `Ω`. -/
theorem holomorphicHull_subset {Ω K : Set ℂ} : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz => hz.1

/-- Elimination rule for `TauCeti.holomorphicHull`: any modulus bound satisfied on `K` by an
`Ω`-holomorphic function also holds at every point of `holomorphicHull Ω K`. -/
theorem norm_le_of_mem_holomorphicHull {Ω K : Set ℂ} {z : ℂ} (hz : z ∈ holomorphicHull Ω K)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) {B : ℝ} (hB : ∀ w ∈ K, ‖f w‖ ≤ B) :
    ‖f z‖ ≤ B :=
  hz.2 f hf B hB

/-- Extensivity: a subset `K ⊆ Ω` is contained in its holomorphic hull in `Ω`. -/
theorem subset_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  fun z hz => ⟨hKΩ hz, fun _ _ _ hB => hB z hz⟩

/-- Monotonicity of `TauCeti.holomorphicHull` in both `Ω` and `K`: enlarging `Ω` restricts the
family of test functions `DifferentiableOn ℂ f Ω`, enlarging the hull. -/
@[gcongr]
theorem holomorphicHull_mono {Ω₁ Ω₂ K₁ K₂ : Set ℂ} (hΩ : Ω₁ ⊆ Ω₂) (hK : K₁ ⊆ K₂) :
    holomorphicHull Ω₁ K₁ ⊆ holomorphicHull Ω₂ K₂ :=
  fun _ hz => ⟨hΩ hz.1, fun f hf B hB => hz.2 f (hf.mono hΩ) B fun w hw => hB w (hK hw)⟩

/-- The holomorphic hull in the empty ambient set is empty. -/
@[simp]
theorem holomorphicHull_empty_left (K : Set ℂ) : holomorphicHull ∅ K = ∅ :=
  eq_empty_of_subset holomorphicHull_subset rfl

/-- The holomorphic hull of the empty set is empty. -/
@[simp]
theorem holomorphicHull_empty (Ω : Set ℂ) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hz => by
    have h := norm_le_of_mem_holomorphicHull hz (differentiableOn_const 0) (B := -1) (by simp)
    norm_num at h

/-- Idempotence of `TauCeti.holomorphicHull`. -/
@[simp]
theorem holomorphicHull_idem (Ω K : Set ℂ) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  (subset_holomorphicHull holomorphicHull_subset).antisymm' fun _ hz =>
    ⟨hz.1, fun f hf B hB => hz.2 f hf B fun _ hw => hw.2 f hf B hB⟩

/-- Separating points of `holomorphicHull Ω K` from a point `ζ ∉ Ω` using `w ↦ (w - ζ)⁻¹`. -/
private lemma infEDist_le_edist_of_mem_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω)
    {z ζ : ℂ} (hz : z ∈ holomorphicHull Ω K) (hζ : ζ ∉ Ω) :
    infEDist ζ K ≤ edist z ζ := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · simp at hz
  by_cases hd0 : infEDist ζ K = 0
  · simp [hd0]
  have hd_top : infEDist ζ K ≠ ⊤ :=
    ((infEDist_le_edist_of_mem hw₀).trans_lt (edist_lt_top ζ w₀)).ne
  set d : ℝ := (infEDist ζ K).toReal
  have hd_pos : 0 < d := ENNReal.toReal_pos hd0 hd_top
  have hf : DifferentiableOn ℂ (fun w : ℂ => (w - ζ)⁻¹) Ω :=
    ((differentiableOn_id (𝕜 := ℂ)).sub_const ζ).inv fun w hw =>
      sub_ne_zero.mpr fun h => hζ (h ▸ hw)
  have hB : ∀ w ∈ K, ‖(w - ζ)⁻¹‖ ≤ d⁻¹ := fun w hw => by
    have hdw : d ≤ ‖w - ζ‖ := by
      have hed : ENNReal.ofReal d ≤ edist w ζ := by
        rw [ENNReal.ofReal_toReal hd_top, edist_comm]
        exact infEDist_le_edist_of_mem hw
      rwa [edist_dist, dist_eq_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at hed
    rw [norm_inv]
    exact inv_anti₀ hd_pos hdw
  have hle : ‖(z - ζ)⁻¹‖ ≤ d⁻¹ := norm_le_of_mem_holomorphicHull hz hf hB
  have hz_pos : 0 < ‖z - ζ‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hζ (h ▸ holomorphicHull_subset hz))
  have hdz : d ≤ ‖z - ζ‖ := by
    rwa [norm_inv, inv_le_inv₀ hz_pos hd_pos] at hle
  rw [← ENNReal.ofReal_toReal hd_top, edist_dist, dist_eq_norm]
  exact ENNReal.ofReal_le_ofReal hdz

/-- Extended distance to `Ωᶜ` is preserved by taking the holomorphic hull of any subset `K ⊆ Ω`.
Empty infima equal `⊤`, covering `K = ∅` and `Ω = Set.univ`. -/
theorem iInf_edist_holomorphicHull_eq {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ w ∈ Ωᶜ, edist z w) =
      (⨅ z ∈ K, ⨅ w ∈ Ωᶜ, edist z w) := by
  refine le_antisymm ?_ ?_
  · exact le_iInf₂ fun a ha => le_iInf₂ fun w hw =>
      iInf₂_le_of_le a (subset_holomorphicHull hKΩ ha) (iInf₂_le w hw)
  · refine le_iInf₂ fun z hz => le_iInf₂ fun ζ hζ => ?_
    calc (⨅ a ∈ K, ⨅ w ∈ Ωᶜ, edist a w)
        ≤ infEDist ζ K := le_infEDist.mpr fun a ha =>
          edist_comm a ζ ▸ iInf₂_le_of_le a ha (iInf₂_le ζ hζ)
      _ ≤ edist z ζ := infEDist_le_edist_of_mem_holomorphicHull hKΩ hz hζ

/-- Real distance to `frontier Ω` is preserved by taking the holomorphic hull of any subset
`K ⊆ Ω`. -/
theorem iInf_infDist_frontier_holomorphicHull_eq {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    (⨅ z : holomorphicHull Ω K, infDist (z : ℂ) (frontier Ω)) =
      ⨅ z : K, infDist (z : ℂ) (frontier Ω) := by
  by_cases hΩ : Ω = Set.univ
  · subst hΩ
    simp
  obtain ⟨w₀, hw₀⟩ := nonempty_compl.mpr hΩ
  have h_eq : ∀ {s : Set ℂ}, s ⊆ Ω →
      (⨅ z : s, infDist (z : ℂ) (frontier Ω)) = (⨅ z ∈ s, ⨅ w ∈ Ωᶜ, edist z w).toReal := by
    intro s hs
    rw [iInf_subtype', ENNReal.toReal_iInf
      (fun z : s => ((iInf₂_le w₀ hw₀).trans_lt (edist_lt_top (z : ℂ) w₀)).ne)]
    exact congrArg iInf (funext fun z =>
      infDist_frontier_eq_infDist_compl (subset_closure (hs z.2)))
  rw [h_eq holomorphicHull_subset, h_eq hKΩ, iInf_edist_holomorphicHull_eq hKΩ]

/-- For any subset `Ω ⊆ ℂ` and compact `K ⊆ Ω`, `holomorphicHull Ω K` is compact. -/
theorem isCompact_holomorphicHull {Ω K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (holomorphicHull Ω K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hbound : holomorphicHull Ω K ⊆ closedBall 0 R := fun z hz => by
    have hzR := norm_le_of_mem_holomorphicHull hz differentiableOn_id (B := R) fun w hw => by
      simpa only [id_eq, mem_closedBall, dist_zero_right] using hR hw
    simpa only [id_eq, mem_closedBall, dist_zero_right] using hzR
  have hclosed : IsClosed (holomorphicHull Ω K) := by
    refine closure_subset_iff_isClosed.mp fun ζ hζ => ?_
    have hζΩ : ζ ∈ Ω := by
      by_contra hζnΩ
      have hpos : 0 < infEDist ζ K := infEDist_pos_iff_notMem_closure.mpr <| by
        rw [hK.isClosed.closure_eq]
        exact fun h => hζnΩ (hKΩ h)
      obtain ⟨z, hzH, hz_lt⟩ := EMetric.mem_closure_iff.mp hζ (infEDist ζ K) hpos
      rw [edist_comm] at hz_lt
      exact (infEDist_le_edist_of_mem_holomorphicHull hKΩ hzH hζnΩ).not_gt hz_lt
    refine ⟨hζΩ, fun f hf B hB => ?_⟩
    have hlim : Tendsto (fun z => ‖f z‖) (𝓝[holomorphicHull Ω K] ζ) (𝓝 ‖f ζ‖) :=
      ((hf.continuousOn ζ hζΩ).mono holomorphicHull_subset).norm
    have hne : (𝓝[holomorphicHull Ω K] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζ
    exact le_of_tendsto hlim
      (eventually_nhdsWithin_of_forall fun z hz => norm_le_of_mem_holomorphicHull hz hf hB)
  exact (isCompact_closedBall 0 R).of_isClosed_subset hclosed hbound

/-- **Maximum-principle inclusion.** When `Ω \ K` is open and `K ⊆ Ω`, `TauCeti.fillIn K Ω` lies
inside `holomorphicHull Ω K` (for open `Ω` and compact `K`, equality is
`TauCeti.holomorphicHull_eq_fill`). -/
theorem fillIn_subset_holomorphicHull {Ω K : Set ℂ} (hΩK : IsOpen (Ω \ K)) (hKΩ : K ⊆ Ω) :
    fillIn K Ω ⊆ holomorphicHull Ω K := by
  intro z hz
  rcases mem_fillIn_iff.mp hz with hzK | ⟨hzΩK, hcpt, hsub⟩
  · exact subset_holomorphicHull hKΩ hzK
  refine ⟨hzΩK.1, fun f hf B hB => ?_⟩
  set C := connectedComponentIn (Ω \ K) z
  have hfr : frontier C ⊆ K := frontier_connectedComponentIn_sdiff_subset hΩK hsub
  have hdiff : DiffContOnCl ℂ f C :=
    ⟨hf.mono ((connectedComponentIn_subset _ _).trans sdiff_subset), hf.continuousOn.mono hsub⟩
  exact Complex.norm_le_of_forall_mem_frontier_norm_le (hcpt.isBounded.subset subset_closure)
    hdiff (fun w hw => hB w (hfr hw)) (subset_closure (mem_connectedComponentIn hzΩK))

/-- For any open `Ω ⊆ ℂ` and any `K : Set ℂ`, `holomorphicHull Ω K` is filled in `Ω`. -/
theorem isFilledIn_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω) :
    IsFilledIn (holomorphicHull Ω K) Ω := by
  have hopen_sdiff : IsOpen (Ω \ holomorphicHull Ω K) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzΩ, hzH⟩
    rw [mem_holomorphicHull_iff] at hzH
    push Not at hzH
    obtain ⟨f, hf, B, hBK, hBz⟩ := hzH hzΩ
    have hcont : ContinuousAt (fun w => ‖f w‖) z :=
      (hf.continuousOn.continuousAt (hΩ.mem_nhds hzΩ)).norm
    filter_upwards [hΩ.mem_nhds hzΩ, hcont.eventually (lt_mem_nhds hBz)] with w hwΩ hwB
    exact ⟨hwΩ, fun hwH => hwB.not_ge (norm_le_of_mem_holomorphicHull hwH hf hBK)⟩
  refine isFilledIn_iff.mpr fun z hz ⟨hcpt, hsub⟩ => hz.2 ?_
  have hz_mem := fillIn_subset_holomorphicHull hopen_sdiff holomorphicHull_subset
    (mem_fillIn_iff.mpr (Or.inr ⟨hz, hcpt, hsub⟩))
  rwa [holomorphicHull_idem] at hz_mem

/-- For compact `K ⊆ ℂ`, the holomorphic hull in `Ω` lies inside `convexHull ℝ K`. -/
theorem holomorphicHull_subset_convexHull {Ω K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull Ω K ⊆ convexHull ℝ K := by
  intro z hz
  by_contra hz_conv
  obtain ⟨f, u, hu_lt, hfz⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) (convex_convexHull ℝ K)
      hK.convexHull.isClosed hz_conv
  have hf : DifferentiableOn ℂ (fun w => Complex.exp (f w)) Ω :=
    (f.differentiable.cexp).differentiableOn
  have hB : ∀ w ∈ K, ‖Complex.exp (f w)‖ ≤ Real.exp u := fun w hw => by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hu_lt w (subset_convexHull ℝ K hw)).le
  have hzle := norm_le_of_mem_holomorphicHull hz hf hB
  rw [Complex.norm_exp] at hzle
  exact (Real.exp_lt_exp.mpr hfz).not_ge hzle

/-- For `Ω = Set.univ` and any bounded set `K ⊆ ℂ`, `holomorphicHull Set.univ K` coincides with
`TauCeti.polynomialHull` under the canonical identification `z ↦ (fun _ : Fin 1 => z)`. -/
theorem holomorphicHull_univ_eq_preimage_polynomialHull {K : Set ℂ} (hK : Bornology.IsBounded K) :
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
    exact norm_le_of_mem_holomorphicHull hz hdiff fun w hw => hpc (e w) (mem_image_of_mem e hw)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨p, hp⟩ := (differentiableOn_univ.mp hf).exists_polynomial_norm_sub_lt
      (hK.insert z) (half_pos hε)
    set P : MvPolynomial (Fin 1) ℂ := p.toMvPolynomial 0
    have hPK : ∀ y ∈ e '' K, ‖MvPolynomial.eval y P‖ ≤ B + ε / 2 := by
      rintro _ ⟨w, hw, rfl⟩
      rw [MvPolynomial.eval_toMvPolynomial]
      have hdist := hp w (mem_insert_of_mem z hw)
      rw [norm_sub_rev] at hdist
      calc ‖p.eval w‖ ≤ ‖f w‖ + ‖p.eval w - f w‖ := by
            simpa only [add_sub_cancel] using norm_add_le (f w) (p.eval w - f w)
        _ ≤ B + ε / 2 := add_le_add (hB w hw) hdist.le
    have hPz : ‖MvPolynomial.eval (e z) P‖ ≤ B + ε / 2 :=
      mem_polynomialHull_iff.mp hz P (B + ε / 2) hPK
    rw [MvPolynomial.eval_toMvPolynomial] at hPz
    have hzdist := hp z (mem_insert z K)
    calc ‖f z‖ ≤ ‖p.eval z‖ + ‖f z - p.eval z‖ := by
          simpa only [add_sub_cancel] using norm_add_le (p.eval z) (f z - p.eval z)
      _ ≤ (B + ε / 2) + ε / 2 := add_le_add hPz hzdist.le
      _ = B + ε := by ring

/-- For bounded `K ⊆ ℂ`, `holomorphicHull Set.univ K = K` if and only if the image of `K` in
`Fin 1 → ℂ` is polynomially convex. -/
theorem holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex
    {K : Set ℂ} (hK : Bornology.IsBounded K) :
    holomorphicHull Set.univ K = K ↔ IsPolynomiallyConvex ((fun z (_ : Fin 1) => z) '' K) := by
  let e : ℂ → Fin 1 → ℂ := fun z _ => z
  have he_inj : Function.Injective e := fun _ _ h => congrFun h 0
  rw [holomorphicHull_univ_eq_preimage_polynomialHull hK, isPolynomiallyConvex_iff]
  constructor
  · rintro h y hy
    have hy0 : y 0 ∈ e ⁻¹' polynomialHull (e '' K) := by
      have hy_eq : e (y 0) = y := funext fun i => congrArg y (Subsingleton.elim 0 i)
      simpa only [mem_preimage, hy_eq] using hy
    have hmem : y 0 ∈ K := h ▸ hy0
    exact ⟨y 0, hmem, funext fun i => congrArg y (Subsingleton.elim 0 i)⟩
  · intro h
    refine Subset.antisymm (fun z hz => ?_) (subset_polynomialHull (e '' K) |> preimage_mono |>
      Subset.trans (subset_preimage_image e K))
    exact (he_inj.mem_set_image).mp (h hz)

end TauCeti
