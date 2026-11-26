/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Dynamics.Flow.Stable
import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Dynamics.Flow.Lyapunov

/-!
# The stable set of a compact set of rest points under a length bound

Let `φ` be a real flow on a metric space, `g` a continuous function that is antitone along every
orbit, and `C` a compact set on which `g` takes the constant value `b`. The **stable set** of `C`
is the union `S = ⋃ p ∈ C, stableSet φ p` of the points whose forward orbits converge to a point
of `C`. For a point `x ∈ S` write `ℓ x` for the limit of its orbit, `limUnder atTop (φ · x)`.

Suppose that near `C` the displacement of an orbit is controlled by the drop of `g`: there are a
neighbourhood `U` of `C` and a function `Ψ` with `Ψ e → 0` as `e → 0⁺` such that

`dist (φ T x) x ≤ Ψ (g x - b)`

whenever the orbit segment `φ t x`, `0 ≤ t ≤ T`, lies in `U` and `g (φ T x) ≥ b`. For the negative
gradient flow of a function satisfying a Łojasiewicz inequality `‖∇g‖ ≥ c (g - b) ^ θ` on `U`
this holds with `Ψ e = e ^ (1 - θ) / (c (1 - θ))`, by the finite-length argument
(`TauCeti.Analysis.Calculus.Morse.Lojasiewicz.Retraction`). Under this hypothesis:

* **Trapping.** An orbit that starts close enough to `C`, with `g - b` small enough and `g ≥ b`
  along it, never leaves `U`, and moves by at most `Ψ (g x - b)` in all forward time
  (`Flow.dist_apply_le_of_infDist_lt`). The orbit cannot leave without first spending a time
  interval in `U` over which the length bound applies. For a point of `S`, along whose orbit
  `g ≥ b` automatically (`Flow.le_apply_of_mem_biUnion_stableSet`), this bounds the distance of
  the tail of the orbit from its limit (`Flow.dist_limUnder_apply_le_of_infDist_lt`).
* **Locally uniform convergence.** On `S`, the time maps `φ t` converge to `ℓ` locally
  uniformly as `t → ∞` (`Flow.tendstoLocallyUniformlyOn_limUnder_biUnion_stableSet`): after a
  common time, all orbits starting near a point of `S` are trapped near the same point of `C`.
  Hence the limit map `ℓ` is continuous on `S`
  (`Flow.continuousOn_limUnder_biUnion_stableSet`), and on compact subsets of `S` the
  convergence is uniform (`Flow.tendstoUniformlyOn_limUnder_of_subset_biUnion_stableSet`).
* **Strong deformation retraction.** If the points of `C` are rest points, then `C ⊆ S`, and `S`
  strong deformation retracts onto `C`
  (`Flow.exists_strong_deformation_retraction_biUnion_stableSet`). The proof deforms `S` along
  the reparametrized flow `(s, x) ↦ φ (s / (1 - s)) x` for `s < 1`, ending at `(1, x) ↦ ℓ x`.

Some such bound is needed: without it, orbits starting near `C` need not converge. A smooth
gradient flow can have an orbit spiralling towards a circle of critical points, with no limit at
all. Nothing here assumes that `C` is a manifold, that the critical points are nondegenerate in
any sense, or that the ambient space is locally compact; the compactness of `C` alone makes the
trapping neighbourhood uniform.

## References

* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, arXiv:math/0410568, proof of Theorem 1.1.
* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, CNRS, Paris, 1963, 87–89.
-/

public section

open Filter Metric Set Topology unitInterval

namespace Flow

section Trapping

variable {α : Type*} [PseudoMetricSpace α] {φ : _root_.Flow ℝ α} {g : α → ℝ} {C U : Set α}
  {b δ : ℝ} {Ψ : ℝ → ℝ}

/-- **Trapping near `C` under a length bound.** Let the displacement of orbit segments in `U`
along which `g ≥ b` be bounded by `Ψ` of the drop of `g`, and let the `δ`-thickening of `C` lie
in `U`. If `g ≥ b` along the forward orbit of `y`, and `y` is so close to `C` that
`infDist y C < δ` and `infDist y C + Ψ (g y - b) < δ`, then every point `φ T y`, `T ≥ 0`, of the
forward orbit is within `Ψ (g y - b)` of `y`. In particular the forward orbit never leaves the
`δ`-thickening of `C`. -/
theorem dist_apply_le_of_infDist_lt (hC : C.Nonempty) (hδU : thickening δ C ⊆ U)
    (hlen : ∀ x T, 0 ≤ T → (∀ t ∈ Icc 0 T, φ t x ∈ U) → b ≤ g (φ T x) →
      dist (φ T x) x ≤ Ψ (g x - b))
    {y : α} (hy : infDist y C < δ) (hyΨ : infDist y C + Ψ (g y - b) < δ)
    (hb : ∀ t, 0 ≤ t → b ≤ g (φ t y)) {T : ℝ} (hT : 0 ≤ T) :
    dist (φ T y) y ≤ Ψ (g y - b) := by
  set h : ℝ → ℝ := fun t ↦ infDist (φ t y) C with hh
  have hcont : Continuous h :=
    (continuous_infDist_pt C).comp (φ.continuous continuous_id continuous_const)
  -- The length bound applies along every segment that stays `δ`-close to `C`.
  have hkey : ∀ T, 0 ≤ T → (∀ t ∈ Icc 0 T, h t < δ) → dist (φ T y) y ≤ Ψ (g y - b) :=
    fun T hT hlt ↦ hlen y T hT
      (fun t ht ↦ hδU ((mem_thickening_iff_infDist_lt hC).2 (hlt t ht))) (hb T hT)
  have hle : ∀ T, 0 ≤ T → (∀ t ∈ Icc 0 T, h t < δ) → h T ≤ infDist y C + Ψ (g y - b) :=
    fun T hT hlt ↦ infDist_le_infDist_add_dist.trans (add_le_add le_rfl (hkey T hT hlt))
  have hΨ₀ : 0 ≤ Ψ (g y - b) := dist_nonneg.trans (hkey 0 le_rfl fun t ht ↦ by
    simpa [hh, le_antisymm ht.2 ht.1] using hy)
  suffices hall : ∀ t, 0 ≤ t → h t < δ from hkey T hT fun t ht ↦ hall t ht.1
  -- Otherwise consider the first time `t₁` at which the orbit is `δ`-far from `C`. Before `t₁`
  -- the length bound keeps it `(infDist y C + Ψ (g y - b))`-close, hence also at `t₁`.
  intro t₀ ht₀
  by_contra! hδt₀
  set K := {t ∈ Icc 0 t₀ | δ ≤ h t}
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const hcont)
  have ht₁K : sInf K ∈ K := hKc.sInf_mem ⟨t₀, ⟨ht₀, le_rfl⟩, hδt₀⟩
  have hbelow : ∀ r ∈ Ico 0 (sInf K), h r < δ := fun r hr ↦ by
    by_contra! hr'
    exact not_le.2 hr.2 (csInf_le hKc.bddBelow ⟨⟨hr.1, hr.2.le.trans ht₁K.1.2⟩, hr'⟩)
  have ht₁ : h (sInf K) ≤ infDist y C + Ψ (g y - b) := by
    rcases ht₁K.1.1.eq_or_lt with h0 | hpos
    · simpa [hh, ← h0] using hΨ₀
    · refine le_of_tendsto ((hcont.tendsto _).mono_left (nhdsWithin_le_nhds (s := Iio (sInf K)))) ?_
      filter_upwards [Ioo_mem_nhdsLT hpos] with r hr
      exact hle r hr.1.le fun t ht ↦ hbelow t ⟨ht.1, ht.2.trans_lt hr.2⟩
  exact (ht₁K.2.trans ht₁).not_gt hyΨ

end Trapping

section Limit

variable {α : Type*} [MetricSpace α] {φ : _root_.Flow ℝ α} {g : α → ℝ} {C U : Set α} {b : ℝ}
  {Ψ : ℝ → ℝ} [Nonempty α] (hg : Continuous g) (hanti : ∀ x, Antitone fun t ↦ g (φ t x))
  (hC : IsCompact C) (hCb : ∀ p ∈ C, g p = b) (hU : U ∈ 𝓝ˢ C) (hΨ : Tendsto Ψ (𝓝[≥] 0) (𝓝 0))
  (hlen : ∀ x T, 0 ≤ T → (∀ t ∈ Icc 0 T, φ t x ∈ U) → b ≤ g (φ T x) →
    dist (φ T x) x ≤ Ψ (g x - b))
include hg hanti hC hCb hU hΨ hlen

omit [Nonempty α] hC hU hΨ hlen in
/-- Along the orbit of a point of the stable set of `C`, the function `g` stays above its value
`b` on `C`. -/
theorem le_apply_of_mem_biUnion_stableSet {y : α} (hy : y ∈ ⋃ p ∈ C, φ.stableSet p) (t : ℝ) :
    b ≤ g (φ t y) := by
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 hy
  exact hCb p hp ▸ le_of_mem_stableSet_of_antitone ((φ.apply_mem_stableSet_iff t).2 hyp)
    hg.continuousAt (hanti _)

omit hC hU hΨ in
/-- **Tail bound in the stable set.** Let the `δ`-thickening of `C` lie in `U`, and let `y` be a
point of the stable set of `C` whose orbit at time `T` satisfies the closeness conditions of the
trapping lemma `Flow.dist_apply_le_of_infDist_lt`. Then from time `T` on, the orbit of `y` stays
within `2 Ψ (g (φ T y) - b)` of its limit. -/
theorem dist_limUnder_apply_le_of_infDist_lt {δ : ℝ} (hδU : thickening δ C ⊆ U) {y : α}
    (hy : y ∈ ⋃ p ∈ C, φ.stableSet p) {T : ℝ} (hT : infDist (φ T y) C < δ)
    (hTΨ : infDist (φ T y) C + Ψ (g (φ T y) - b) < δ) {t : ℝ} (ht : T ≤ t) :
    dist (limUnder atTop fun s ↦ φ s y) (φ t y) ≤ 2 * Ψ (g (φ T y) - b) := by
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 hy
  -- The orbit of `φ T y` is trapped near `C`.
  have hmove : ∀ s, T ≤ s → dist (φ s y) (φ T y) ≤ Ψ (g (φ T y) - b) := fun s hs ↦ by
    have hyT : φ T y ∈ ⋃ p ∈ C, φ.stableSet p :=
      mem_biUnion hp ((φ.apply_mem_stableSet_iff T).2 hyp)
    simpa [← Flow.map_add] using dist_apply_le_of_infDist_lt ⟨p, hp⟩ hδU hlen hT hTΨ
      (fun r _ ↦ le_apply_of_mem_biUnion_stableSet hg hanti hCb hyT r) (sub_nonneg.2 hs)
  have hlim : dist (limUnder atTop fun s ↦ φ s y) (φ T y) ≤ Ψ (g (φ T y) - b) := by
    rw [limUnder_atTop_eq_of_mem_stableSet hyp]
    refine le_of_tendsto ((mem_stableSet.1 hyp).dist tendsto_const_nhds) ?_
    filter_upwards [eventually_ge_atTop T] with s hs using hmove s hs
  calc dist (limUnder atTop fun s ↦ φ s y) (φ t y)
      ≤ dist (limUnder atTop fun s ↦ φ s y) (φ T y) + dist (φ t y) (φ T y) :=
        dist_triangle_right _ _ _
    _ ≤ 2 * Ψ (g (φ T y) - b) := by linarith [hmove t ht]

/-- **Orbits in the stable set of `C` converge locally uniformly.** If near the compact set `C`,
on which `g = b`, the displacement of orbit segments is bounded by `Ψ` of the drop of `g`, with
`Ψ e → 0` as `e → 0⁺`, then on the stable set of `C` the time maps `φ t` converge locally
uniformly to the limit map `x ↦ limUnder atTop (φ · x)` as `t → ∞`. -/
theorem tendstoLocallyUniformlyOn_limUnder_biUnion_stableSet :
    TendstoLocallyUniformlyOn (fun t x ↦ φ t x) (fun x ↦ limUnder atTop fun t ↦ φ t x) atTop
      (⋃ p ∈ C, φ.stableSet p) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x₀ hx₀
  obtain ⟨p₀, hp₀, hx₀p₀⟩ := mem_iUnion₂.1 hx₀
  obtain ⟨δ, hδ, hδU⟩ := hC.exists_thickening_subset_open isOpen_interior
    (subset_interior_iff_mem_nhdsSet.2 hU)
  set η := min δ ε / 4 with hηdef
  have hη : 0 < η := by positivity
  have hηδ : 4 * η ≤ δ := by rw [hηdef]; linarith [min_le_left δ ε]
  have hηε : 4 * η ≤ ε := by rw [hηdef]; linarith [min_le_right δ ε]
  obtain ⟨η₂, hη₂, hΨη⟩ := Metric.tendsto_nhdsWithin_nhds.1 hΨ η hη
  -- After a time `T`, the orbit of `x₀` is close to `p₀` and `g` is close to `b` along it.
  have hφx₀ : Tendsto (fun t ↦ φ t x₀) atTop (𝓝 p₀) := mem_stableSet.1 hx₀p₀
  have hgx₀ : Tendsto (fun t ↦ g (φ t x₀)) atTop (𝓝 b) :=
    hCb p₀ hp₀ ▸ (hg.tendsto p₀).comp hφx₀
  obtain ⟨T, hTp, hTg⟩ := ((Metric.tendsto_nhds.1 hφx₀ η hη).and
    (Metric.tendsto_nhds.1 hgx₀ (η₂ / 2) (half_pos hη₂))).exists
  -- At time `T`, the orbits of all points near `x₀` are close to `p₀`, with `g` close to `b`.
  set N := {y | dist (φ T y) (φ T x₀) < η ∧ dist (g (φ T y)) (g (φ T x₀)) < η₂ / 2}
  have hN : N ∈ 𝓝 x₀ := by
    have hφT : Continuous (φ T) := φ.continuous continuous_const continuous_id
    exact ((isOpen_lt (continuous_dist.comp (hφT.prodMk continuous_const)) continuous_const).inter
      (isOpen_lt (continuous_dist.comp ((hg.comp hφT).prodMk continuous_const))
        continuous_const)).mem_nhds ⟨by simpa using hη, by simpa using half_pos hη₂⟩
  refine ⟨(⋃ p ∈ C, φ.stableSet p) ∩ N, inter_mem_nhdsWithin _ hN, ?_⟩
  filter_upwards [eventually_ge_atTop T] with n hn y ⟨hyS, hyN⟩
  -- The point `φ T y` is close to `p₀`, and `g - b` is small and nonnegative there.
  have hzC : infDist (φ T y) C < 2 * η := by
    calc infDist (φ T y) C ≤ dist (φ T y) p₀ := infDist_le_dist_of_mem hp₀
      _ ≤ dist (φ T y) (φ T x₀) + dist (φ T x₀) p₀ := dist_triangle _ _ _
      _ < η + η := add_lt_add hyN.1 hTp
      _ = 2 * η := by ring
  have hgz₀ : 0 ≤ g (φ T y) - b :=
    sub_nonneg.2 (le_apply_of_mem_biUnion_stableSet hg hanti hCb hyS T)
  have hgz : g (φ T y) - b < η₂ := by
    have h₁ := hyN.2
    have h₂ := hTg
    rw [Real.dist_eq] at h₁ h₂
    linarith [abs_lt.1 h₁, abs_lt.1 h₂]
  have hΨz : |Ψ (g (φ T y) - b)| < η := by
    simpa [Real.dist_eq] using
      hΨη (mem_Ici.2 hgz₀) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hgz₀])
  have hΨz' := (le_abs_self _).trans_lt hΨz
  calc dist (limUnder atTop fun t ↦ φ t y) (φ n y)
      ≤ 2 * Ψ (g (φ T y) - b) :=
        dist_limUnder_apply_le_of_infDist_lt hg hanti hCb hlen (hδU.trans interior_subset) hyS
          (by linarith) (by linarith) hn
    _ < ε := by linarith

/-- **Orbits in the stable set of `C` converge uniformly on compact sets.** Under the length bound
of `Flow.tendstoLocallyUniformlyOn_limUnder_biUnion_stableSet`, the time maps `φ t` converge to
the limit map uniformly on every compact subset of the stable set of `C`. -/
theorem tendstoUniformlyOn_limUnder_of_subset_biUnion_stableSet {K : Set α} (hK : IsCompact K)
    (hKS : K ⊆ ⋃ p ∈ C, φ.stableSet p) :
    TendstoUniformlyOn (fun t x ↦ φ t x) (fun x ↦ limUnder atTop fun t ↦ φ t x) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    ((tendstoLocallyUniformlyOn_limUnder_biUnion_stableSet hg hanti hC hCb hU hΨ hlen).mono hKS)

/-- **The limit map is continuous on the stable set.** Under the length bound of
`Flow.tendstoLocallyUniformlyOn_limUnder_biUnion_stableSet`, the map sending a point of the
stable set of `C` to the limit of its orbit is continuous on that stable set. -/
theorem continuousOn_limUnder_biUnion_stableSet :
    ContinuousOn (fun x ↦ limUnder atTop fun t ↦ φ t x) (⋃ p ∈ C, φ.stableSet p) :=
  (tendstoLocallyUniformlyOn_limUnder_biUnion_stableSet hg hanti hC hCb hU hΨ hlen).continuousOn
    (Frequently.of_forall fun _ ↦ (φ.continuous continuous_const continuous_id).continuousOn)

/-- The reparametrization `s ↦ φ (s / (1 - s)) x` of the forward orbit by `s ∈ [0, 1)`, ending at
the limit `limUnder atTop (φ · x)` at `s = 1`. -/
private noncomputable def retractionMap (φ : _root_.Flow ℝ α) (q : I × α) : α :=
  if (q.1 : ℝ) < 1 then φ (q.1 / (1 - q.1)) q.2 else limUnder atTop fun t ↦ φ t q.2

omit hg hanti hC hCb hU hΨ hlen in
private theorem retractionMap_of_lt {q : I × α} (hq : (q.1 : ℝ) < 1) :
    retractionMap φ q = φ (q.1 / (1 - q.1)) q.2 := by
  simp [retractionMap, hq]

omit hg hanti hC hCb hU hΨ hlen in
private theorem retractionMap_of_not_lt {q : I × α} (hq : ¬(q.1 : ℝ) < 1) :
    retractionMap φ q = limUnder atTop fun t ↦ φ t q.2 := by
  simp [retractionMap, hq]

omit hg hanti hC hCb hU hΨ hlen in
private theorem retractionMap_one (x : α) :
    retractionMap φ (1, x) = limUnder atTop fun t ↦ φ t x := by
  simp [retractionMap]

/-- The reparametrized orbits converge to the limit map, jointly in the time `s → 1` and the
point, on the stable set of `C`. -/
private theorem continuousOn_retractionMap :
    ContinuousOn (retractionMap φ) (univ ×ˢ ⋃ p ∈ C, φ.stableSet p) := by
  rintro ⟨s₀, x₀⟩ ⟨-, hx₀⟩
  rcases (unitInterval.le_one s₀).lt_or_eq with hs₀ | hs₀
  · -- Before time `1`, the map is a reparametrization of the flow.
    have hev : retractionMap φ =ᶠ[𝓝 (s₀, x₀)] fun q ↦ φ (q.1 / (1 - q.1)) q.2 := by
      filter_upwards [(isOpen_lt (continuous_subtypeVal.comp continuous_fst)
        continuous_const).mem_nhds hs₀] with q hq using retractionMap_of_lt hq
    refine (ContinuousAt.congr ?_ hev.symm).continuousWithinAt
    have hτ : ContinuousAt (fun q : I × α ↦ (q.1 : ℝ) / (1 - q.1)) (s₀, x₀) :=
      ((continuous_subtypeVal.comp continuous_fst).continuousAt).div
        ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).continuousAt)
        (sub_ne_zero.2 hs₀.ne')
    exact φ.cont'.continuousAt.comp (hτ.prodMk continuous_snd.continuousAt)
  · -- At time `1`, use the locally uniform convergence and the continuity of the limit map.
    obtain rfl : s₀ = 1 := Subtype.ext hs₀
    rw [ContinuousWithinAt, retractionMap_one, nhdsWithin_prod_eq, nhdsWithin_univ,
      Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN, hNev⟩ := Metric.tendstoLocallyUniformlyOn_iff.1
      (tendstoLocallyUniformlyOn_limUnder_biUnion_stableSet hg hanti hC hCb hU hΨ hlen)
      (ε / 2) (half_pos hε) x₀ hx₀
    obtain ⟨T, hT⟩ := eventually_atTop.1 hNev
    set T' := max T 0
    have hc : T' / (1 + T') < 1 := (div_lt_one (by positivity)).2 (by linarith)
    have hs : ∀ᶠ s : I in 𝓝 1, T' / (1 + T') < s :=
      (isOpen_lt continuous_const continuous_subtypeVal).mem_nhds hc
    have hx : ∀ᶠ x in 𝓝[⋃ p ∈ C, φ.stableSet p] x₀,
        x ∈ N ∧ dist (limUnder atTop fun t ↦ φ t x) (limUnder atTop fun t ↦ φ t x₀) < ε / 2 :=
      (eventually_mem_set.2 hN).and (Metric.tendsto_nhds.1
        (continuousOn_limUnder_biUnion_stableSet hg hanti hC hCb hU hΨ hlen x₀ hx₀) _
        (half_pos hε))
    filter_upwards [hs.prod_mk hx] with ⟨s, x⟩ ⟨hs, hxN, hxℓ⟩
    refine (dist_triangle _ (limUnder atTop fun t ↦ φ t x) _).trans_lt ?_
    refine (add_lt_add_of_le_of_lt ?_ hxℓ).trans_eq (add_halves ε)
    by_cases hs1 : (s : ℝ) < 1
    · -- The reparametrized time `s / (1 - s)` exceeds `T`.
      have hτT : T ≤ s / (1 - s) := by
        refine (le_max_left T 0).trans ((le_div_iff₀ (sub_pos.2 hs1)).2 ?_)
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 1 + T')).1 hs
        nlinarith
      rw [retractionMap_of_lt hs1, dist_comm]
      exact (hT _ hτT x hxN).le
    · rw [retractionMap_of_not_lt hs1]
      simpa using (half_pos hε).le

/-- **The stable set of a compact set of rest points deformation retracts onto it.** Let `φ` be a
real flow on a metric space, `g` a continuous function antitone along every orbit, and `C` a
compact set of rest points of `φ` on which `g = b`. Suppose that near `C` the displacement of
orbit segments along which `g ≥ b` is bounded by `Ψ` of the drop of `g`, with `Ψ e → 0` as
`e → 0⁺`. Then the stable set `⋃ p ∈ C, stableSet φ p` strong deformation retracts onto `C`. -/
theorem exists_strong_deformation_retraction_biUnion_stableSet
    (hfix : ∀ p ∈ C, ∀ t, φ t p = p) :
    ∃ r : C(↥(⋃ p ∈ C, φ.stableSet p), C),
      (∀ p, r (ContinuousMap.inclusion (subset_biUnion_stableSet hfix) p) = p) ∧
      (ContinuousMap.id _).HomotopicRel
        ((ContinuousMap.inclusion (subset_biUnion_stableSet hfix)).comp r) {x | (x : α) ∈ C} := by
  set S := ⋃ p ∈ C, φ.stableSet p
  have hcont := continuousOn_retractionMap hg hanti hC hCb hU hΨ hlen
  -- The deformation keeps the stable set inside itself.
  have hmem : ∀ q : I × S, retractionMap φ (q.1, q.2) ∈ S := by
    rintro ⟨s, x, hx⟩
    by_cases hs : (s : ℝ) < 1
    · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
      rw [retractionMap_of_lt hs]
      exact mem_biUnion hp ((φ.apply_mem_stableSet_iff _).2 hxp)
    · rw [retractionMap_of_not_lt hs]
      exact subset_biUnion_stableSet hfix (limUnder_atTop_mem_of_mem_biUnion_stableSet hx)
  have hlimfix : ∀ p ∈ C, (limUnder atTop fun t ↦ φ t p) = p := fun p hp ↦
    limUnder_atTop_eq_of_mem_stableSet (self_mem_stableSet_iff.2 (hfix p hp))
  let r : C(S, C) := ⟨fun x ↦ ⟨limUnder atTop fun t ↦ φ t x,
      limUnder_atTop_mem_of_mem_biUnion_stableSet x.property⟩,
    ((continuousOn_limUnder_biUnion_stableSet hg hanti hC hCb hU hΨ hlen).domRestrict).subtype_mk _⟩
  refine ⟨r, fun p ↦ Subtype.ext (hlimfix p p.property), ⟨?_⟩⟩
  exact
    { toFun := fun q ↦ ⟨retractionMap φ (q.1, q.2), hmem q⟩
      continuous_toFun := (hcont.comp_continuous
        (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))
        fun q ↦ ⟨mem_univ _, q.2.property⟩).subtype_mk _
      map_zero_left := fun x ↦ Subtype.ext (by simp [retractionMap_of_lt])
      map_one_left := fun x ↦ Subtype.ext (retractionMap_one _)
      prop' := fun s x hx ↦ Subtype.ext (by
        by_cases hs : (s : ℝ) < 1
        · simpa [retractionMap_of_lt (q := (s, (x : α))) hs] using hfix _ hx _
        · simp [retractionMap_of_not_lt (q := (s, (x : α))) hs, hlimfix _ hx]) }

end Limit

end Flow
