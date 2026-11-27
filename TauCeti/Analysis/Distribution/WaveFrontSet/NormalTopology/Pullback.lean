/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Convex.Cone.InfDist
import TauCeti.Analysis.Distribution.TestFunction.Compact
import TauCeti.Analysis.Distribution.TestFunction.DominatedSeries
import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.Normed.Module.Seminorm.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Continuity of the pullback to `E × {0}` in the normal topology

Let `W` be an open set of the Euclidean product `WithLp 2 (E × D)` of finite-dimensional real
inner product spaces, `U` an open set of `E` with `U × {0} ⊆ W`, and `Γ` a closed cone of nonzero
covectors over `W` (closed in `W × ((E × D) \ {0})`) containing no conormal covector
`((x, 0), (0, η))` of `E × {0}` over `U`. Every distribution `T` with wave front set in `Γ` then
has a pullback `ι^* T` along the inclusion `ι : x ↦ (x, 0)` (`Distribution.pullbackInl`), whose
wave front set lies in the fixed cone

`ιᵀ Γ = {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}` (`TauCeti.pullbackInlCone`).

This file proves that the pullback is continuous for the normal topologies of Hörmander's spaces
(`TauCeti.WaveFrontSpace.pullbackInlCLM`):

`ι^* : 𝓓'_Γ(W) →L[ℂ] 𝓓'_{ιᵀ Γ}(U)`.

This is the restriction step of the pullback along a smooth map, which composes it with a pullback
along a submersion (Brouder, Dang and Hélein, Theorem 6.3, in the case of a linear injection).

## The estimates

Fix a compact set `K ⊆ U` and a closed cone `V` of frequencies with no point of `ιᵀ Γ` over `K` in
a direction of `V`; for a seminorm `‖ι^* T‖_{ψ,V,N}` of the target, `K` is the support of `ψ`, and
for the topology of `𝓓'(U)`, `V = {0}`. Since `Γ` is a closed cone, no point of `Γ` lies over a
neighbourhood of `K × {0}` in a direction of the closed cone
`A = {ζ | dist (ζ.fst, V) ≤ ε ‖ζ‖}` for small `ε > 0`, so a cutoff `χ` equal to one on
`K × closedBall 0 δ` and supported in that neighbourhood, with the cone `A`, gives seminorms
`‖T‖_{χ,A,M}` of the source (`exists_cutoff_disjoint_bigCone`). The localized Fourier transform of
`ι^* T` with a cutoff `ψ` supported in `K` is the lattice series

`ι^* T (ψ e_ξ) = ∑ m, (covolume L)⁻¹ 𝓕 ψ (ξ + m.fst) T (χ e_(-m))`

(`Distribution.localFourier_pullbackInl_eq_tsum`). The terms with `-m ∈ A` are controlled by the
seminorms `‖T‖_{χ,A,M}`. Off `A`, `‖ξ + m.fst‖` is comparable to `‖ξ‖ + ‖m‖` for `ξ ∈ V`, so the
coefficients `𝓕 ψ (ξ + m.fst)` decay rapidly in `ξ` and `m` jointly, and these terms sum to the
pairing of `T` with a single test function: the Fourier series
`∑ m, (covolume L)⁻¹ 𝓕 ψ (ξ + m.fst) χ e_(-m)` restricted to these `m`, which converges in the
smooth functions supported in `tsupport χ` (`localFourier_pullbackInl_eq_add`). Weighted by
`(1 + ‖ξ‖) ^ N`, these test functions depend continuously on `ξ ∈ V` and tend to zero at infinity
(`ContDiffMapSupportedIn.tendsto_tsum_smul_of_dominated`), so together with `0` they form a
compact set, on which `T` is bounded by a continuous seminorm of `𝓓'(W)`. For the topology of
`𝓓'(U)`, a compact set of test functions has its supports in one compact set `K`
(`TestFunction.exists_compacts_forall_tsupport_subset_of_isCompact`), and the same test functions
depend continuously on `ψ` in that compact set.

## Main declarations

* `TauCeti.WaveFrontSpace.pullbackInlCLM`: the pullback `ι^* : 𝓓'_Γ(W) →L[ℂ] 𝓓'_{ιᵀ Γ}(U)`.
* `TauCeti.WaveFrontSpace.toDistribution_pullbackInlCLM`: it is `Distribution.pullbackInl`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the pullback and its sequential continuity on `𝓓'_Γ`).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, Theorem 6.3 (continuity of the pullback in the normal topology).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction WithLp
open scoped Distributions Topology FourierTransform ContDiff Real RealInnerProductSpace Pointwise
  SchwartzMap

namespace TauCeti

open Distribution

namespace WaveFrontSpace

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  {U : Opens E} {W : Opens (WithLp 2 (E × D))} {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))}

/-! ### The cone `A` of the source seminorms -/

variable (D) in
/-- The closed cone `A = {ζ | dist (ζ.fst, V) ≤ ε ‖ζ‖}` of the covectors of `E × D` whose first
component is within `ε ‖ζ‖` of `V`. -/
private def bigCone (V : Set E) (ε : ℝ) : Set (WithLp 2 (E × D)) :=
  {ζ | infDist ζ.fst V ≤ ε * ‖ζ‖}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
private theorem isClosed_bigCone (V : Set E) (ε : ℝ) : IsClosed (bigCone D V ε) :=
  isClosed_le ((continuous_infDist_pt V).comp (by fun_prop)) (continuous_const.mul continuous_norm)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
private theorem smul_mem_bigCone {V : Set E} (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    {ε : ℝ} (t : ℝ) (ht : 0 < t) (ζ : WithLp 2 (E × D)) (hζ : ζ ∈ bigCone D V ε) :
    t • ζ ∈ bigCone D V ε := by
  simp only [bigCone, mem_ofPred_eq, WithLp.smul_fst, norm_smul, Real.norm_of_nonneg ht.le,
    infDist_smul_of_forall_smul_mem hVcone ht] at hζ ⊢
  nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
/-- The cone `A` contains the cone `‖ζ.fst‖ < ε ‖ζ.snd‖` around the conormal directions. -/
private theorem mem_bigCone_of_norm_fst_lt {V : Set E} (hV0 : (0 : E) ∈ V) {ε : ℝ} (hε : 0 ≤ ε)
    {ζ : WithLp 2 (E × D)} (hζ : ‖ζ.fst‖ < ε * ‖ζ.snd‖) : ζ ∈ bigCone D V ε :=
  ((infDist_le_dist_of_mem hV0).trans_eq (dist_zero_right _)).trans
    (hζ.le.trans (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le (x := ζ)) hε))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
/-- Off the cone `A`, the first component of a covector stays away from `V`:
`ε / (2 + ε) (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖` for `ξ ∈ V`. -/
private theorem mul_add_le_norm_fst_sub {V : Set E} {ε : ℝ} (hε : 0 < ε) {ξ : E} (hξ : ξ ∈ V)
    {ζ : WithLp 2 (E × D)} (hζ : ζ ∉ bigCone D V ε) :
    ε / (2 + ε) * (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖ := by
  simp only [bigCone, mem_ofPred_eq, not_le] at hζ
  have h1 : ε * ‖ζ‖ ≤ ‖ζ.fst - ξ‖ :=
    hζ.le.trans ((infDist_le_dist_of_mem hξ).trans_eq (dist_eq_norm _ _))
  have h2 : ‖ξ‖ - ‖ζ‖ ≤ ‖ζ.fst - ξ‖ := by
    have h3 := norm_sub_norm_le ξ ζ.fst
    have h4 := WithLp.norm_fst_le (x := ζ)
    rw [norm_sub_rev] at h3
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-! ### A cutoff adapted to `Γ` -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- A nonzero covector `ζ` of the cone `A`, rescaled to the unit sphere, is within `4 ε` of a unit
covector whose first component lies in `V`, for `ε ≤ 1 / 4`. -/
private theorem exists_mem_sphere_dist_lt {V : Set E} (hV0 : (0 : E) ∈ V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    {ζ : WithLp 2 (E × D)} (hζ0 : ζ ≠ 0) (hζ : ζ ∈ bigCone D V ε) :
    ∃ ζ'' ∈ sphere (0 : WithLp 2 (E × D)) 1, ζ''.fst ∈ V ∧ dist (‖ζ‖⁻¹ • ζ) ζ'' < 4 * ε := by
  set r := ‖ζ‖
  have hr : 0 < r := norm_pos_iff.2 hζ0
  -- A point `v ∈ V` with `‖ζ.fst - v‖ < 2 ε ‖ζ‖`.
  obtain ⟨v, hvV, hv⟩ : ∃ v ∈ V, dist ζ.fst v < 2 * ε * r :=
    (infDist_lt_iff ⟨0, hV0⟩).1 (lt_of_le_of_lt hζ (by nlinarith))
  -- The unit covector `ζ̂ = r⁻¹ ζ` is within `2 ε` of `ζ' = (r⁻¹ v, ζ̂.snd)`, which is within
  -- `2 ε` of the unit covector `ζ'' = ‖ζ'‖⁻¹ ζ'` whose first component lies in `V`.
  set ζh : WithLp 2 (E × D) := r⁻¹ • ζ
  have hζh : ‖ζh‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  set ζ' : WithLp 2 (E × D) := toLp 2 (r⁻¹ • v, ζh.snd)
  have h1 : ‖ζ' - ζh‖ < 2 * ε := by
    have hfst : (ζ' - ζh).fst = r⁻¹ • (v - ζ.fst) := by simp [ζ', ζh, smul_sub]
    rw [WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero (by simp [ζ']), hfst, norm_smul, norm_inv,
      norm_norm, ← dist_eq_norm, dist_comm, inv_mul_lt_iff₀ hr]
    linarith
  set s := ‖ζ'‖
  have hs : |s - 1| < 2 * ε := by
    rw [← hζh]
    exact (abs_norm_sub_norm_le ζ' ζh).trans_lt h1
  have hs0 : 0 < s := by
    have := (abs_lt.1 hs).1
    linarith
  have h2 : ‖s⁻¹ • ζ' - ζ'‖ < 2 * ε := by
    have : s⁻¹ • ζ' - ζ' = (s⁻¹ - 1) • ζ' := by simp [sub_smul]
    have hs1 : |s⁻¹ - 1| * s = |1 - s| := by
      rw [← abs_of_pos hs0, ← abs_mul, abs_of_pos hs0]
      congr 1
      field_simp
    rwa [this, norm_smul, Real.norm_eq_abs, hs1, abs_sub_comm]
  refine ⟨s⁻¹ • ζ', ?_, hVcone _ (inv_pos.2 hs0) _ (hVcone _ (inv_pos.2 hr) v hvV), ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0.ne']
  · rw [dist_eq_norm]
    calc ‖ζh - s⁻¹ • ζ'‖ ≤ ‖s⁻¹ • ζ' - ζ'‖ + ‖ζ' - ζh‖ := by
          rw [norm_sub_rev ζh]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 2 * ε + 2 * ε := add_lt_add h2 h1
      _ = 4 * ε := by ring

/-- Since `Γ` is a closed cone, no point of `Γ` lies over a neighbourhood `G` of `K × {0}` in a
direction of the cone `A = {ζ | dist (ζ.fst, V) ≤ ε ‖ζ‖}` for small `ε`, when none lies over
`K × {0}` in the directions with first component in `V`. -/
private theorem exists_isOpen_forall_notMem
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {K : Set E} (hK : IsCompact K) (hKW : ∀ x ∈ K, toLp 2 (x, (0 : D)) ∈ W)
    {V : Set E} (hV : IsClosed V) (hV0 : (0 : E) ∈ V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    (hKV : Disjoint (K ×ˢ V) (pullbackInlCone Γ)) :
    ∃ ε > 0, ∃ G : Set (WithLp 2 (E × D)), IsOpen G ∧ (∀ x ∈ K, toLp 2 (x, (0 : D)) ∈ G) ∧
      ∀ p ∈ G, ∀ ζ ∈ bigCone D V ε, (p, ζ) ∉ Γ := by
  set ι : E → WithLp 2 (E × D) := fun x ↦ toLp 2 (x, (0 : D))
  have hι : Continuous ι :=
    (prod_continuous_toLp 2 E D).comp (continuous_id.prodMk continuous_const)
  -- The compact set of unit covectors over `K × {0}` with first component in `V`.
  set C₀ : Set (WithLp 2 (E × D) × WithLp 2 (E × D)) :=
    (ι '' K) ×ˢ (sphere 0 1 ∩ WithLp.fst ⁻¹' V)
  have hC₀ : IsCompact C₀ :=
    (hK.image hι).prod ((isCompact_sphere 0 1).inter_right (hV.preimage (by fun_prop)))
  have hC₀sub : C₀ ⊆ ((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ := by
    rintro ⟨_, ζ⟩ ⟨⟨x, hx, rfl⟩, hζ, hζV⟩
    refine ⟨⟨hKW x hx, ?_⟩, fun hΓζ ↦ disjoint_left.1 hKV (mk_mem_prod hx hζV)
      (mem_pullbackInlCone.2 ⟨ζ.snd, ?_⟩)⟩
    · exact ne_zero_of_mem_unit_sphere (⟨ζ, hζ⟩ : sphere (0 : WithLp 2 (E × D)) 1)
    · have hζeq : toLp 2 (ζ.fst, ζ.snd) = ζ := by
        rw [← ofLp_fst, ← ofLp_snd, Prod.mk.eta, toLp_ofLp]
      simpa [ι, hζeq] using hΓζ
  obtain ⟨δ, hδ, hδsub⟩ := hC₀.exists_thickening_subset_open hΓ hC₀sub
  set ε := min (δ / 8) (1 / 4)
  have hε : 0 < ε := by positivity
  have hεδ : ε ≤ δ / 8 := min_le_left _ _
  have hε4 : ε ≤ 1 / 4 := min_le_right _ _
  refine ⟨ε, hε, thickening (δ / 2) (ι '' K), isOpen_thickening,
    fun x hx ↦ self_subset_thickening (half_pos hδ) _ ⟨x, hx, rfl⟩, fun p hp ζ hζ hpΓ ↦ ?_⟩
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · exact hΓ0 _ hpΓ rfl
  obtain ⟨ζ'', hζ''1, hζ''V, hζ''⟩ := exists_mem_sphere_dist_lt hV0 hVcone hε hε4 hζ0 hζ
  obtain ⟨_, ⟨x, hx, rfl⟩, hpx⟩ := mem_thickening_iff.1 hp
  -- `(p, ‖ζ‖⁻¹ ζ)` is within `δ` of the point `(ι x, ζ'')` of `C₀`.
  have hmem : (p, ‖ζ‖⁻¹ • ζ) ∈ thickening δ C₀ := by
    refine mem_thickening_iff.2 ⟨(ι x, ζ''), ⟨⟨x, hx, rfl⟩, hζ''1, hζ''V⟩, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hpx.trans (half_lt_self hδ), hζ''.trans (by linarith)⟩
  exact (hδsub hmem).2 (hcone _ hpΓ ‖ζ‖⁻¹ (inv_pos.2 (norm_pos_iff.2 hζ0)))

/-- A cutoff `χ` equal to one on `K × closedBall 0 δ`, such that no point of `Γ` lies over its
support in a direction of the cone `A`. -/
private theorem exists_cutoff_disjoint_bigCone
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {V : Set E} (hV : IsClosed V) (hV0 : (0 : E) ∈ V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    (hKV : Disjoint (K ×ˢ V) (pullbackInlCone Γ)) :
    ∃ ε > 0, ∃ δ > 0, ∃ χ : 𝓓(W, ℂ), (∀ x ∈ K, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1) ∧
      Disjoint (tsupport χ ×ˢ bigCone D V ε) Γ := by
  obtain ⟨ε, hε, G, hG, hKG, hGΓ⟩ := exists_isOpen_forall_notMem hΓ hcone hΓ0 hK
    (fun x hx ↦ hU (hKU hx)) hV hV0 hVcone hKV
  obtain ⟨δ, hδ, χ, hχ1, hχG⟩ :=
    exists_cutoff_eq_one_prod_closedBall hK hG fun x hx ↦ ⟨hKG x hx, hU (hKU hx)⟩
  exact ⟨ε, hε, δ, hδ, χ, hχ1, disjoint_left.2 fun ⟨p, ζ⟩ ⟨hp, hζ⟩ ↦ hGΓ p (hχG hp) ζ hζ⟩

/-- The data `(χ, A, N)` of a seminorm of `𝓓'_Γ(W)`, for the cone `A` of `bigCone`. -/
private def bigConeIndex {χ : 𝓓(W, ℂ)} {V : Set E} (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    {ε : ℝ}
    (hχ : Disjoint (tsupport χ ×ˢ bigCone D V ε) Γ) (N : ℕ) : WaveFrontSeminormIndex W Γ where
  cutoff := χ
  cone := bigCone D V ε
  order := N
  isClosed_cone := isClosed_bigCone V ε
  smul_mem_cone := smul_mem_bigCone hVcone
  disjoint := hχ

/-! ### Splitting the lattice series of the pullback -/

section Measurable

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]

/-- The coefficients `(covolume L)⁻¹ f (ξ + m.fst)` of the lattice series of the pullback, for
the `m` with `-m ∉ A`. -/
private def badCoeff (L : Submodule ℤ (WithLp 2 (E × D)))
    (A : Set (WithLp 2 (E × D))) (f : E → ℂ) (ξ : E) (m : ZLattice.dual L) : ℂ :=
  {m : ZLattice.dual L | -(m : WithLp 2 (E × D)) ∉ A}.indicator
    (fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * f (ξ + (m : WithLp 2 (E × D)).fst)) m

/-- The terms `(covolume L)⁻¹ f (ξ + m.fst) F (-m)` of the lattice series of the pullback, for
the `m` with `-m ∈ A`. -/
private def goodTerm (L : Submodule ℤ (WithLp 2 (E × D)))
    (A : Set (WithLp 2 (E × D))) (f : E → ℂ) (F : WithLp 2 (E × D) → ℂ) (ξ : E)
    (m : ZLattice.dual L) : ℂ :=
  {m : ZLattice.dual L | -(m : WithLp 2 (E × D)) ∈ A}.indicator
    (fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * (f (ξ + (m : WithLp 2 (E × D)).fst) * F (-m))) m

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- Peetre's inequality for the frequencies of the lattice series:
`1 + ‖ξ‖ ≤ (1 + ‖ξ + m.fst‖) (1 + ‖m‖)`. -/
private theorem one_add_norm_le_mul (ξ : E) (m : WithLp 2 (E × D)) :
    1 + ‖ξ‖ ≤ (1 + ‖ξ + m.fst‖) * (1 + ‖m‖) :=
  calc 1 + ‖ξ‖ = 1 + ‖(ξ + m.fst) + -m.fst‖ := by rw [add_neg_cancel_right]
    _ ≤ (1 + ‖ξ + m.fst‖) * (1 + ‖-m.fst‖) := one_add_norm_add_le _ _
    _ ≤ (1 + ‖ξ + m.fst‖) * (1 + ‖m‖) := by
        rw [norm_neg]
        gcongr
        exact WithLp.norm_fst_le (x := m)

/-- A decay bound is nonnegative. -/
private theorem nonneg_of_one_add_norm_pow_mul_norm_le {X G : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup G] {f : X → G} {x : X} {n : ℕ} {B : ℝ}
    (hB : (1 + ‖x‖) ^ n * ‖f x‖ ≤ B) : 0 ≤ B :=
  (by positivity : (0 : ℝ) ≤ (1 + ‖x‖) ^ n * ‖f x‖).trans hB

/-- **A term in `A`.** If `f` decays to order `N` with constant `B` and `F` decays on `A` to order
`N + q` with constant `S`, then the term of index `m` of the lattice series is at most
`‖(covolume L)⁻¹‖ B S (1 + ‖ξ‖)⁻ᴺ (1 + ‖m‖)⁻ᵠ` when `-m ∈ A`, and vanishes otherwise. -/
private theorem norm_goodTerm_le
    (L : Submodule ℤ (WithLp 2 (E × D)))
    {A : Set (WithLp 2 (E × D))} {f : E → ℂ} {F : WithLp 2 (E × D) → ℂ} {N q : ℕ} {B S : ℝ}
    (hS0 : 0 ≤ S) (hB : ∀ η, (1 + ‖η‖) ^ N * ‖f η‖ ≤ B)
    (hS : ∀ ζ ∈ A, (1 + ‖ζ‖) ^ (N + q) * ‖F ζ‖ ≤ S) (ξ : E) (m : ZLattice.dual L) :
    ‖goodTerm L A f F ξ m‖ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * B * S * ((1 + ‖ξ‖) ^ N)⁻¹ *
      ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  have hB0 := nonneg_of_one_add_norm_pow_mul_norm_le (hB 0)
  rw [mul_right_comm _ ((1 + ‖ξ‖) ^ N)⁻¹, ← div_eq_mul_inv _ ((1 + ‖ξ‖) ^ N),
    le_div_iff₀' (by positivity)]
  by_cases hm : -(m : WithLp 2 (E × D)) ∈ A
  · rw [goodTerm, indicator_of_mem (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)) ∈ A})
      hm, norm_mul, norm_mul]
    have h2 := hS _ hm
    rw [norm_neg] at h2
    have h2' : (1 + ‖(m : WithLp 2 (E × D))‖) ^ N * ‖F (-m)‖ ≤
        S * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      calc _ = (1 + ‖(m : WithLp 2 (E × D))‖) ^ (N + q) * ‖F (-m)‖ := by ring
        _ ≤ S := h2
    have hP := pow_le_pow_left₀ (by positivity) (one_add_norm_le_mul ξ (m : WithLp 2 (E × D))) N
    rw [mul_pow] at hP
    calc (1 + ‖ξ‖) ^ N * (‖a‖ * (‖f (ξ + (m : WithLp 2 (E × D)).fst)‖ * ‖F (-m)‖))
        ≤ ((1 + ‖ξ + (m : WithLp 2 (E × D)).fst‖) ^ N * (1 + ‖(m : WithLp 2 (E × D))‖) ^ N) *
            (‖a‖ * (‖f (ξ + (m : WithLp 2 (E × D)).fst)‖ * ‖F (-m)‖)) := by gcongr
      _ = ‖a‖ * (((1 + ‖ξ + (m : WithLp 2 (E × D)).fst‖) ^ N *
            ‖f (ξ + (m : WithLp 2 (E × D)).fst)‖) *
          ((1 + ‖(m : WithLp 2 (E × D))‖) ^ N * ‖F (-m)‖)) := by ring
      _ ≤ ‖a‖ * (B * (S * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹)) := by
          gcongr
          · exact hB _
      _ = _ := by ring
  · rw [goodTerm, indicator_of_notMem (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)) ∈ A})
      hm, norm_zero, mul_zero]
    positivity

/-- A coefficient off `A` depends continuously on a parameter on which `f (ξ + m.fst)` depends
continuously. -/
private theorem continuous_badCoeff (L : Submodule ℤ (WithLp 2 (E × D)))
    {X : Type*} [TopologicalSpace X] {A : Set (WithLp 2 (E × D))} {f : X → E → ℂ} {ξ : X → E}
    {m : ZLattice.dual L} (hf : Continuous fun x ↦ f x (ξ x + (m : WithLp 2 (E × D)).fst)) :
    Continuous fun x ↦ badCoeff L A (f x) (ξ x) m := by
  by_cases hm : -(m : WithLp 2 (E × D)) ∈ A
  · simp only [badCoeff, mem_ofPred_eq, hm, not_true_eq_false, not_false_eq_true,
      indicator_of_notMem]
    exact continuous_const
  · simp only [badCoeff, indicator_of_mem
      (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)) ∉ A}) hm]
    exact continuous_const.mul hf

/-- **The terms in `A`.** If `f` decays to order `N` with constant `B` and `F` decays on `A` to
order `N + q` with constant `S`, then the sum of the terms of the lattice series with `-m ∈ A`
decays to order `N` in `ξ`. -/
private theorem one_add_norm_pow_mul_norm_tsum_goodTerm_le
    (L : Submodule ℤ (WithLp 2 (E × D)))
    {A : Set (WithLp 2 (E × D))} {f : E → ℂ} {F : WithLp 2 (E × D) → ℂ} {N q : ℕ} {B S : ℝ}
    (hS0 : 0 ≤ S) (hB : ∀ η, (1 + ‖η‖) ^ N * ‖f η‖ ≤ B)
    (hS : ∀ ζ ∈ A, (1 + ‖ζ‖) ^ (N + q) * ‖F ζ‖ ≤ S)
    (hq : Summable fun m : ZLattice.dual L ↦ ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹) (ξ : E) :
    (1 + ‖ξ‖) ^ N * ‖∑' m, goodTerm L A f F ξ m‖ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * B * S *
      ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
  have hle := tsum_of_norm_bounded (hq.hasSum.mul_left _) (norm_goodTerm_le L hS0 hB hS ξ)
  calc (1 + ‖ξ‖) ^ N * ‖∑' m, goodTerm L A f F ξ m‖
      ≤ (1 + ‖ξ‖) ^ N * (‖(ZLattice.covolume L : ℂ)⁻¹‖ * B * S * ((1 + ‖ξ‖) ^ N)⁻¹ *
          ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹) := by gcongr
    _ = _ := by field_simp

/-- **The splitting of the lattice series.** The localized Fourier transform of the pullback
with cutoff `ψ` at `ξ` is the sum of the terms of its lattice series with `-m ∈ A`, and of the
pairing of `T` with the series of the remaining terms, a smooth function supported in
`tsupport χ`. -/
private theorem localFourier_pullbackInl_eq_add
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) {T : 𝓓'(W, ℂ)}
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    {V : Set E} (hV0 : (0 : E) ∈ V) {ε : ℝ} (hε : 0 < ε) {K : Set E} {χ : 𝓓(W, ℂ)} {δ : ℝ}
    (hδ : 0 < δ) (hχ : ∀ x ∈ K, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ ∈ bigCone D V ε, (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C)
    {ψ : 𝓓(U, ℂ)} (hψ : tsupport ψ ⊆ K) (ξ : E)
    (hbad : Summable fun m ↦ badCoeff L (bigCone D V ε) (𝓕 (ψ : E → ℂ)) ξ m •
      χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))) :
    (T.pullbackInl hU h).localFourier ψ ξ =
      (∑' m, goodTerm L (bigCone D V ε) (𝓕 (ψ : E → ℂ)) (T.localFourier χ) ξ m) +
      T.complexPairing (ofSupportedIn χ.tsupport_subset (∑' m, badCoeff L (bigCone D V ε)
        (𝓕 (ψ : E → ℂ)) ξ m • χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)))) := by
  set A := bigCone D V ε
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  set f : E → ℂ := 𝓕 (ψ : E → ℂ)
  -- The terms with `-m ∉ A` sum to the pairing of `T` with the series of modulated cutoffs.
  have hb := hasSum_mul_localFourier_neg T χ hbad
  -- The terms with `-m ∈ A` are summable, by the decay of `T` on `A`.
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  obtain ⟨B, hB⟩ := exists_one_add_norm_pow_mul_norm_fourier_le ψ.contDiff ψ.hasCompactSupport 0
  obtain ⟨C, hC⟩ := hdecay q
  have hC0 := nonneg_of_one_add_norm_pow_mul_norm_le
    (hC 0 (by simp [A, bigCone, infDist_zero_of_mem hV0]))
  have hg : Summable (goodTerm L A f (T.localFourier χ) ξ) :=
    Summable.of_norm_bounded (hq.mul_left _) (norm_goodTerm_le L (N := 0) hC0 hB
      (fun ζ hζ ↦ by simpa using hC ζ hζ) ξ)
  rw [localFourier_pullbackInl_eq_tsum T hU h hδ (fun x hx ↦ hχ x (hψ hx)) L hL hε
    (fun N ↦ (hdecay N).imp fun C hC ζ hζ ↦ hC ζ (mem_bigCone_of_norm_fst_lt hV0 hε.le hζ)) ξ]
  refine ((hg.hasSum.add hb).congr_fun fun m ↦ ?_).tsum_eq
  by_cases hm : -(m : WithLp 2 (E × D)) ∈ A
  · simp [goodTerm, badCoeff, hm, f]
  · simp [goodTerm, badCoeff, hm, f, mul_assoc]

/-! ### Estimates for the two parts -/

/-- **The coefficients off `A`.** For `ξ ∈ V` and `-m ∉ A`, `‖ξ + m.fst‖` is comparable to
`1 + ‖ξ‖ + ‖m‖`, so a decay estimate of order `M` for `f` gives one for the coefficients. -/
private theorem pow_mul_one_add_pow_mul_norm_badCoeff_le
    (L : Submodule ℤ (WithLp 2 (E × D))) {V : Set E}
    {ε : ℝ} (hε : 0 < ε) {f : E → ℂ} {M : ℕ} {B : ℝ} (hB : ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ B)
    {ξ : E} (hξ : ξ ∈ V) (m : ZLattice.dual L) :
    (ε / (2 + ε)) ^ M * (1 + ‖ξ‖ + ‖(m : WithLp 2 (E × D))‖) ^ M *
      ‖badCoeff L (bigCone D V ε) f ξ m‖ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * B := by
  have hB0 := nonneg_of_one_add_norm_pow_mul_norm_le (hB 0)
  by_cases hm : -(m : WithLp 2 (E × D)) ∈ bigCone D V ε
  · simp only [badCoeff, mem_ofPred_eq, hm, not_true_eq_false, not_false_eq_true,
      indicator_of_notMem, norm_zero, mul_zero]
    positivity
  · rw [badCoeff, indicator_of_mem
      (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)) ∉ bigCone D V ε}) hm, norm_mul]
    have hsep := mul_add_le_norm_fst_sub hε hξ hm
    rw [show (-(m : WithLp 2 (E × D))).fst - ξ = -(ξ + (m : WithLp 2 (E × D)).fst) by
      rw [WithLp.neg_fst]; abel, norm_neg, norm_neg] at hsep
    set c := ε / (2 + ε)
    have hc1 : c ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have key : c * (1 + ‖ξ‖ + ‖(m : WithLp 2 (E × D))‖) ≤ 1 + ‖ξ + (m : WithLp 2 (E × D)).fst‖ := by
      nlinarith
    calc c ^ M * (1 + ‖ξ‖ + ‖(m : WithLp 2 (E × D))‖) ^ M *
          (‖(ZLattice.covolume L : ℂ)⁻¹‖ * ‖f (ξ + (m : WithLp 2 (E × D)).fst)‖)
        = ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ((c * (1 + ‖ξ‖ + ‖(m : WithLp 2 (E × D))‖)) ^ M *
            ‖f (ξ + (m : WithLp 2 (E × D)).fst)‖) := by rw [mul_pow]; ring
      _ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ((1 + ‖ξ + (m : WithLp 2 (E × D)).fst‖) ^ M *
            ‖f (ξ + (m : WithLp 2 (E × D)).fst)‖) := by gcongr
      _ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * B := by gcongr; exact hB _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
private theorem one_add_pow_mul_one_add_pow_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {i j M : ℕ}
    (h : i + j ≤ M) : (1 + s) ^ i * (1 + t) ^ j ≤ (1 + s + t) ^ M :=
  calc (1 + s) ^ i * (1 + t) ^ j ≤ (1 + s + t) ^ i * (1 + s + t) ^ j :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) i)
          (pow_le_pow_left₀ (by linarith) (by linarith) j) (by positivity) (by positivity)
    _ = (1 + s + t) ^ (i + j) := (pow_add _ _ _).symm
    _ ≤ (1 + s + t) ^ M := pow_le_pow_right₀ (by linarith) h

/-- **The terms off `A`, weighted.** The products of the coefficients off `A`, weighted by
`(1 + ‖ξ‖) ^ N`, with the seminorms of the modulated cutoffs are dominated by a summable sequence,
uniformly in `ξ ∈ V`. -/
private theorem one_add_pow_mul_norm_badCoeff_mul_seminorm_le
    (L : Submodule ℤ (WithLp 2 (E × D))) {V : Set E}
    {ε : ℝ} (hε : 0 < ε) (χ : 𝓓(W, ℂ)) {f : E → ℂ} {N M k q : ℕ} (hM : N + k + q ≤ M) {B : ℝ}
    (hB : ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ B) {ξ : E} (hξ : ξ ∈ V) (m : ZLattice.dual L) :
    (1 + ‖ξ‖) ^ N * ‖badCoeff L (bigCone D V ε) f ξ m‖ *
        N[ℂ]_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩, k}
          (χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))) ≤
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * B * (ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤
        ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩ k χ.toSupportedInTSupport * (1 + 2 * π) ^ k) /
          (ε / (2 + ε)) ^ M * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
  set c := ε / (2 + ε)
  set s := ‖ξ‖
  set t := ‖(m : WithLp 2 (E × D))‖
  set Sk := ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤
    ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩ k χ.toSupportedInTSupport
  have hbad := pow_mul_one_add_pow_mul_norm_badCoeff_le L hε hB hξ m
  -- The derivatives of the modulated cutoff grow at most polynomially.
  have hmod : N[ℂ]_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩, k}
      (χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))) ≤
        Sk * (1 + 2 * π) ^ k * (1 + t) ^ k :=
    ContDiffMapSupportedIn.seminorm_modulate_le_of_norm_le _ le_rfl k
  rw [le_mul_inv_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  calc (1 + s) ^ N * ‖badCoeff L (bigCone D V ε) f ξ m‖ *
        N[ℂ]_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩, k}
          (χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))) * (1 + t) ^ q * c ^ M
      ≤ (1 + s) ^ N * ‖badCoeff L (bigCone D V ε) f ξ m‖ * (Sk * (1 + 2 * π) ^ k * (1 + t) ^ k) *
          (1 + t) ^ q * c ^ M := by gcongr
    _ = c ^ M * ((1 + s) ^ N * ((1 + t) ^ k * (1 + t) ^ q)) *
          ‖badCoeff L (bigCone D V ε) f ξ m‖ * (Sk * (1 + 2 * π) ^ k) := by ring
    _ ≤ c ^ M * (1 + s + t) ^ M * ‖badCoeff L (bigCone D V ε) f ξ m‖ *
          (Sk * (1 + 2 * π) ^ k) := by
        have hpow : (1 + s) ^ N * ((1 + t) ^ k * (1 + t) ^ q) ≤ (1 + s + t) ^ M := by
          rw [← pow_add]
          exact one_add_pow_mul_one_add_pow_le (norm_nonneg _) (norm_nonneg _) (by omega)
        gcongr
    _ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * B * (Sk * (1 + 2 * π) ^ k) :=
        mul_le_mul_of_nonneg_right hbad (by positivity)
    _ = _ := by ring

/-- **The coefficients off `A` tend to zero.** Weighted by `(1 + ‖ξ‖) ^ N`, the coefficients off
`A` still decay like `(1 + ‖ξ‖)⁻¹`, for a decay estimate of `f` of order `M ≥ N + 1`. -/
private theorem one_add_pow_mul_norm_badCoeff_le
    (L : Submodule ℤ (WithLp 2 (E × D))) {V : Set E}
    {ε : ℝ} (hε : 0 < ε) {f : E → ℂ} {N M : ℕ} (hM : N + 1 ≤ M) {B : ℝ}
    (hB : ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ B) {ξ : E} (hξ : ξ ∈ V) (m : ZLattice.dual L) :
    (1 + ‖ξ‖) ^ N * ‖badCoeff L (bigCone D V ε) f ξ m‖ ≤
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * B / (ε / (2 + ε)) ^ M * (1 + ‖ξ‖)⁻¹ := by
  have hbad := pow_mul_one_add_pow_mul_norm_badCoeff_le L hε hB hξ m
  have hpow : (1 + ‖ξ‖) ^ (N + 1) * (1 + ‖(m : WithLp 2 (E × D))‖) ^ 0 ≤
      (1 + ‖ξ‖ + ‖(m : WithLp 2 (E × D))‖) ^ M :=
    one_add_pow_mul_one_add_pow_le (norm_nonneg _) (norm_nonneg _) (by omega)
  rw [pow_zero, mul_one] at hpow
  rw [le_mul_inv_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  calc (1 + ‖ξ‖) ^ N * ‖badCoeff L (bigCone D V ε) f ξ m‖ * (1 + ‖ξ‖) * (ε / (2 + ε)) ^ M
      = (ε / (2 + ε)) ^ M * (1 + ‖ξ‖) ^ (N + 1) * ‖badCoeff L (bigCone D V ε) f ξ m‖ := by ring
    _ ≤ (ε / (2 + ε)) ^ M * (1 + ‖ξ‖ + ‖(m : WithLp 2 (E × D))‖) ^ M *
          ‖badCoeff L (bigCone D V ε) f ξ m‖ := by gcongr
    _ ≤ _ := hbad

/-- **Domination of the Fourier series off `A`.** For a family `F` of functions decaying rapidly,
uniformly, the products of the coefficients off `A`, weighted by `(1 + ‖ξ‖) ^ N`, with the
seminorms of the modulated cutoffs are dominated by nonnegative summable sequences, uniformly in
`f ∈ F` and `ξ ∈ V`. -/
private theorem exists_summable_one_add_pow_mul_norm_badCoeff_mul_seminorm_le
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L] {V : Set E}
    {ε : ℝ} (hε : 0 < ε) (χ : 𝓓(W, ℂ)) (N : ℕ) {F : Set (E → ℂ)}
    (hF : ∀ M : ℕ, ∃ B, ∀ f ∈ F, ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ B) :
    ∃ b : ℕ → ZLattice.dual L → ℝ, (∀ k, Summable (b k)) ∧ (∀ k m, 0 ≤ b k m) ∧
      ∀ f ∈ F, ∀ ξ ∈ V, ∀ k m, (1 + ‖ξ‖) ^ N * ‖badCoeff L (bigCone D V ε) f ξ m‖ *
        N[ℂ]_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩, k}
          (χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))) ≤ b k m := by
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  choose B hB using fun k : ℕ ↦ hF (N + k + q)
  set b : ℕ → ZLattice.dual L → ℝ := fun k m ↦
    ‖(ZLattice.covolume L : ℂ)⁻¹‖ * max (B k) 0 * (ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤
      ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩ k χ.toSupportedInTSupport * (1 + 2 * π) ^ k) /
        (ε / (2 + ε)) ^ (N + k + q) * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹
  have hb (k : ℕ) : Summable (b k) := hq.mul_left _
  refine ⟨b, hb, fun k m ↦ ?_, fun f hf ξ hξ k m ↦ ?_⟩
  · have := apply_nonneg (ContDiffMapSupportedIn.supSeminorm ℂ (WithLp 2 (E × D)) ℂ ⊤
      ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩ k) χ.toSupportedInTSupport
    positivity
  · exact one_add_pow_mul_norm_badCoeff_mul_seminorm_le L hε χ le_rfl
      (fun η ↦ (hB k f hf η).trans (le_max_left _ _)) hξ m

/-- The Fourier series off `A` converges in `𝓓_K`, for a rapidly decreasing `f`. -/
private theorem summable_badCoeff_smul_modulate (L : Submodule ℤ (WithLp 2 (E × D)))
    [DiscreteTopology L] [IsZLattice ℝ L] {V : Set E} {ε : ℝ} (hε : 0 < ε) (χ : 𝓓(W, ℂ))
    {f : E → ℂ} (hf : ∀ M : ℕ, ∃ B, ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ B) {ξ : E} (hξ : ξ ∈ V) :
    Summable fun m ↦ badCoeff L (bigCone D V ε) f ξ m •
      χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)) := by
  obtain ⟨b, hb, -, hbound⟩ := exists_summable_one_add_pow_mul_norm_badCoeff_mul_seminorm_le
    (V := V) L hε χ 0 (F := {f}) fun M ↦ (hf M).imp fun B hB g hg ↦ by
      rw [mem_singleton_iff.1 hg]
      exact hB
  refine ContDiffMapSupportedIn.summable_smul_of_le hb fun k m ↦ ?_
  simpa using hbound f rfl ξ hξ k m

/-! ### Compact sets of test functions -/

/-- The coefficients off `A`, weighted by `(1 + ‖ξ‖) ^ N`, tend to zero at infinity in `V`. -/
private theorem tendsto_one_add_pow_mul_badCoeff (L : Submodule ℤ (WithLp 2 (E × D)))
    {V : Set E} (hV : IsClosed V) {ε : ℝ} (hε : 0 < ε)
    {f : E → ℂ} {N : ℕ} (hB : ∃ B, ∀ η, (1 + ‖η‖) ^ (N + 1) * ‖f η‖ ≤ B) (m : ZLattice.dual L) :
    Tendsto (fun ξ : V ↦ (((1 + ‖(ξ : E)‖) ^ N : ℝ) : ℂ) * badCoeff L (bigCone D V ε) f ξ m)
      (cocompact V) (𝓝 0) := by
  obtain ⟨B, hB⟩ := hB
  have hnormV : Tendsto (fun ξ : V ↦ ‖(ξ : E)‖) (cocompact V) atTop :=
    tendsto_norm_cocompact_atTop.comp hV.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hinv := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 hnormV)).const_mul
    (‖(ZLattice.covolume L : ℂ)⁻¹‖ * B / (ε / (2 + ε)) ^ (N + 1))
  rw [mul_zero] at hinv
  refine squeeze_zero_norm (fun ξ ↦ ?_) hinv
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact one_add_pow_mul_norm_badCoeff_le L hε le_rfl hB ξ.property m

/-- **The weighted Fourier series off `A` form a compact set.** For `ξ ∈ V`, the series of the
modulated cutoffs with the coefficients off `A` weighted by `(1 + ‖ξ‖) ^ N` depends continuously on
`ξ` and tends to zero at infinity, so these series and `0` form a compact set. -/
private theorem isCompact_insert_range_tsum (L : Submodule ℤ (WithLp 2 (E × D)))
    [DiscreteTopology L] [IsZLattice ℝ L] {V : Set E} (hV : IsClosed V) {ε : ℝ} (hε : 0 < ε)
    (χ : 𝓓(W, ℂ)) (φ : 𝓓(U, ℂ)) (N : ℕ) :
    IsCompact (insert 0 (range fun ξ : V ↦ ∑' m : ZLattice.dual L,
      ((((1 + ‖(ξ : E)‖) ^ N : ℝ) : ℂ) * badCoeff L (bigCone D V ε) (𝓕 (φ : E → ℂ)) ξ m) •
        χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)))) := by
  obtain ⟨b, hb, -, hbound'⟩ := exists_summable_one_add_pow_mul_norm_badCoeff_mul_seminorm_le
    (V := V) L hε χ N (F := {𝓕 (φ : E → ℂ)}) fun M ↦
      (exists_one_add_norm_pow_mul_norm_fourier_le φ.contDiff φ.hasCompactSupport M).imp
        fun B hB g hg ↦ by
          rw [mem_singleton_iff.1 hg]
          exact hB
  set c : V → ZLattice.dual L → ℂ := fun ξ m ↦
    (((1 + ‖(ξ : E)‖) ^ N : ℝ) : ℂ) * badCoeff L (bigCone D V ε) (𝓕 (φ : E → ℂ)) ξ m
  have hnorm (ξ : V) (m : ZLattice.dual L) :
      ‖c ξ m‖ = (1 + ‖(ξ : E)‖) ^ N * ‖badCoeff L (bigCone D V ε) (𝓕 (φ : E → ℂ)) ξ m‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hbound (ξ : V) (k : ℕ) (m : ZLattice.dual L) :
      ‖c ξ m‖ * N[ℂ]_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩, k}
        (χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))) ≤ b k m := by
    rw [hnorm]
    exact hbound' _ rfl ξ ξ.property k m
  -- Each coefficient is continuous in `ξ`.
  have hcont (m : ZLattice.dual L) : Continuous fun ξ : V ↦ c ξ m :=
    (Complex.continuous_ofReal.comp ((continuous_const.add
      (continuous_norm.comp continuous_subtypeVal)).pow N)).mul (continuous_badCoeff L
        ((φ.continuous.integrable_of_hasCompactSupport
          φ.hasCompactSupport).continuous_fourier.comp
            (continuous_subtypeVal.add continuous_const)))
  -- Each coefficient tends to zero at infinity in `V`.
  have hlim (m : ZLattice.dual L) : Tendsto (fun ξ : V ↦ c ξ m) (cocompact V) (𝓝 0) :=
    tendsto_one_add_pow_mul_badCoeff L hV hε
      (exists_one_add_norm_pow_mul_norm_fourier_le φ.contDiff φ.hasCompactSupport (N + 1)) m
  exact ContDiffMapSupportedIn.isCompact_insert_range_tsum_smul hb hbound hcont hlim

/-- **The Fourier series off `A` for a compact set of cutoffs.** At `ξ = 0`, the series of the
modulated cutoffs with the coefficients off `A` depends continuously on the cutoff `ψ`, so over a
compact set of cutoffs these series form a compact set. -/
private theorem isCompact_range_tsum (L : Submodule ℤ (WithLp 2 (E × D)))
    [DiscreteTopology L] [IsZLattice ℝ L] {ε : ℝ} (hε : 0 < ε) (χ : 𝓓(W, ℂ))
    {Q : Set 𝓓(U, ℂ)} (hQ : IsCompact Q) :
    IsCompact (range fun ψ : Q ↦ ∑' m : ZLattice.dual L,
      badCoeff L (bigCone D {0} ε) (𝓕 ((ψ : 𝓓(U, ℂ)) : E → ℂ)) 0 m •
        χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))) := by
  have : CompactSpace Q := isCompact_iff_compactSpace.1 hQ
  obtain ⟨b, hb, -, hbound'⟩ := exists_summable_one_add_pow_mul_norm_badCoeff_mul_seminorm_le
    (V := {0}) L hε χ 0 (F := (fun ψ : 𝓓(U, ℂ) ↦ 𝓕 (ψ : E → ℂ)) '' Q) fun M ↦
      (exists_forall_one_add_norm_pow_mul_norm_fourier_le hQ M).imp fun B hB ↦ by
        rintro _ ⟨ψ, hψ, rfl⟩
        exact hB ψ hψ
  have hbound (ψ : Q) (k : ℕ) (m : ZLattice.dual L) :
      ‖badCoeff L (bigCone D {0} ε) (𝓕 ((ψ : 𝓓(U, ℂ)) : E → ℂ)) 0 m‖ *
        N[ℂ]_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩, k}
          (χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))) ≤ b k m := by
    simpa using hbound' _ ⟨ψ, ψ.property, rfl⟩ 0 (mem_singleton 0) k m
  -- Each coefficient is continuous in `ψ`.
  have hcont (m : ZLattice.dual L) : Continuous fun ψ : Q ↦
      badCoeff L (bigCone D {0} ε) (𝓕 ((ψ : 𝓓(U, ℂ)) : E → ℂ)) 0 m :=
    continuous_badCoeff L ((continuous_fourier_apply (Ω := U) _).comp continuous_subtypeVal)
  exact isCompact_range <| continuous_iff_continuousAt.2 fun ψ₀ ↦
    ContDiffMapSupportedIn.tendsto_tsum_smul_of_dominated hb (Eventually.of_forall (hbound ·))
      (hbound ψ₀) fun m ↦ (hcont m).continuousAt

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- A distribution with wave front set in `Γ` has no conormal covector of `E × {0}` over `U` in
its wave front set. -/
private theorem notMem_waveFrontSet
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ u.toDistribution.waveFrontSet :=
  fun x hx η hη hmem ↦ hN x hx η hη (u.waveFrontSet_toDistribution_subset hmem)

/-- **The estimate behind both seminorm bounds.** Let `φ x`, `x ∈ X`, be cutoffs supported in a
compact set `K ⊆ U` whose Fourier transforms decay to order `N` with a common constant, and let
`ξ x` lie in a closed cone `V` containing `0` with `K × V` disjoint from `ιᵀ Γ`. If, for every
cutoff `χ` and lattice `L`, the weighted series of the terms off `A` form a compact set together
with `0`, then `(1 + ‖ξ x‖) ^ N ‖ι^* T (φ x e_{ξ x})‖ ≤ p T` for a continuous seminorm `p` of
`𝓓'_Γ(W)`. -/
private theorem exists_seminorm_localFourier_pullbackInl_le_of_isCompact
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {V : Set E} (hV : IsClosed V)
    (hV0 : (0 : E) ∈ V) (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    (hKV : Disjoint (K ×ˢ V) (pullbackInlCone Γ)) {X : Type*} {φ : X → 𝓓(U, ℂ)}
    (hφK : ∀ x, tsupport (φ x) ⊆ K) {ξ : X → E} (hξV : ∀ x, ξ x ∈ V) {N : ℕ} {B : ℝ}
    (hB : ∀ x η, (1 + ‖η‖) ^ N * ‖𝓕 (φ x : E → ℂ) η‖ ≤ B)
    (hS : ∀ (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L] {ε : ℝ},
      0 < ε → ∀ χ : 𝓓(W, ℂ), IsCompact (insert 0 (range fun x : X ↦ ∑' m : ZLattice.dual L,
        ((((1 + ‖ξ x‖) ^ N : ℝ) : ℂ) * badCoeff L (bigCone D V ε) (𝓕 (φ x : E → ℂ)) (ξ x) m) •
          χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))))) :
    ∃ p : Seminorm ℂ (WaveFrontSpace W Γ), Continuous p ∧ ∀ u : WaveFrontSpace W Γ, ∀ x : X,
      (1 + ‖ξ x‖) ^ N *
        ‖(u.toDistribution.pullbackInl hU (notMem_waveFrontSet hN u)).localFourier (φ x) (ξ x)‖ ≤
          p u := by
  obtain ⟨ε, hε, δ, hδ, χ, hχ1, hχΓ⟩ :=
    exists_cutoff_disjoint_bigCone hU hΓ hcone hΓ0 hK hKU hV hV0 hVcone hKV
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  obtain ⟨p', hp', hp'le⟩ := exists_continuous_seminorm_norm_complexPairing_le (Γ := Γ)
    ((hS L hε χ).image (continuous_ofSupportedIn χ.tsupport_subset))
  set i := bigConeIndex hVcone hχΓ (N + q)
  set K₀ : ℝ := ‖(ZLattice.covolume L : ℂ)⁻¹‖ * max B 0 *
    ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹
  have hK₀ : 0 ≤ K₀ := by positivity
  refine ⟨K₀.toNNReal • WaveFrontSpace.seminorm i + p',
    ((continuous_seminorm i).const_smul _).add hp', fun u x ↦ ?_⟩
  set T := u.toDistribution
  -- The decay of `T` on the cone `A`, from the seminorms `‖T‖_{χ,A,M}`.
  have hdecay (M : ℕ) : ∃ C, ∀ ζ ∈ bigCone D V ε, (1 + ‖ζ‖) ^ M * ‖T.localFourier χ ζ‖ ≤ C :=
    ⟨_, fun ζ hζ ↦ le_seminorm (bigConeIndex hVcone hχΓ M) u hζ⟩
  -- The series off `A` converges.
  have hbad := summable_badCoeff_smul_modulate L hε χ
    (exists_one_add_norm_pow_mul_norm_fourier_le (φ x).contDiff (φ x).hasCompactSupport) (hξV x)
  rw [localFourier_pullbackInl_eq_add hU _ hV0 hε hδ hχ1 L hL hdecay (hφK x) (ξ x) hbad]
  -- The terms in `A`.
  have hgood := one_add_norm_pow_mul_norm_tsum_goodTerm_le L (apply_nonneg _ u)
    (fun η ↦ (hB x η).trans (le_max_left B 0)) (fun ζ hζ ↦ le_seminorm i u hζ) hq (ξ x)
  -- The terms off `A`: the weighted series lies in the compact set `hS`.
  have hbadle := hp'le u (ofSupportedIn χ.tsupport_subset (∑' m : ZLattice.dual L,
      ((((1 + ‖ξ x‖) ^ N : ℝ) : ℂ) * badCoeff L (bigCone D V ε) (𝓕 (φ x : E → ℂ)) (ξ x) m) •
        χ.toSupportedInTSupport.modulate (m : WithLp 2 (E × D))))
    (mem_image_of_mem _ (mem_insert_of_mem _ ⟨x, rfl⟩))
  rw [← mul_norm_complexPairing_tsum_smul T χ.tsupport_subset (by positivity) hbad] at hbadle
  exact Seminorm.mul_norm_add_le_smul_add_apply _ _ u (by positivity) hK₀
    (hgood.trans_eq (by simp only [K₀]; ring)) hbadle

/-- **The seminorms of the pullback.** For the data `(φ, V, N)` of a seminorm of `𝓓'_{ιᵀ Γ}(U)`,
the decay estimate `(1 + ‖ξ‖) ^ N ‖ι^* T (φ e_ξ)‖ ≤ p T` on `V` holds for a continuous seminorm
`p` of `𝓓'_Γ(W)`. -/
private theorem exists_seminorm_localFourier_pullbackInl_le
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (j : WaveFrontSeminormIndex U (pullbackInlCone Γ)) :
    ∃ p : Seminorm ℂ (WaveFrontSpace W Γ), Continuous p ∧ ∀ u : WaveFrontSpace W Γ, ∀ ξ ∈ j.cone,
      (1 + ‖ξ‖) ^ j.order *
        ‖(u.toDistribution.pullbackInl hU (notMem_waveFrontSet hN u)).localFourier j.cutoff ξ‖ ≤
          p u := by
  rcases j.cone.eq_empty_or_nonempty with hV | ⟨ξ₀, hξ₀⟩
  · exact ⟨0, continuous_const, fun u ξ hξ ↦ by simp [hV] at hξ⟩
  have hV0 := j.isClosed_cone.zero_mem_of_smul_mem j.smul_mem_cone hξ₀
  obtain ⟨B, hB⟩ :=
    exists_one_add_norm_pow_mul_norm_fourier_le j.cutoff.contDiff j.cutoff.hasCompactSupport j.order
  -- The family of cutoffs is constant, indexed by the points of the cone.
  obtain ⟨p, hp, hpj⟩ := exists_seminorm_localFourier_pullbackInl_le_of_isCompact hU hΓ hcone hΓ0
    hN j.cutoff.hasCompactSupport.isCompact j.cutoff.tsupport_subset j.isClosed_cone hV0
    j.smul_mem_cone j.disjoint (X := j.cone) (φ := fun _ ↦ j.cutoff) (fun _ ↦ subset_rfl)
    (ξ := (↑)) Subtype.property (fun _ ↦ hB) (by
      intro L _ _ ε hε χ
      exact isCompact_insert_range_tsum L j.isClosed_cone hε χ j.cutoff j.order)
  exact ⟨p, hp, fun u ξ hξ ↦ hpj u ⟨ξ, hξ⟩⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- No point of `ιᵀ Γ` over `K ⊆ U` lies in the direction `0`, when `Γ` contains neither zero
covectors nor conormal covectors of `E × {0}` over `U`. -/
private theorem disjoint_prod_zero_pullbackInlCone (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    {K : Set E} (hKU : K ⊆ U) : Disjoint (K ×ˢ ({0} : Set E)) (pullbackInlCone Γ) := by
  refine disjoint_left.2 ?_
  rintro ⟨x, ξ⟩ ⟨hx, hξ⟩ hmem
  obtain ⟨η, hη⟩ := mem_pullbackInlCone.1 hmem
  rw [mem_singleton_iff] at hξ
  subst hξ
  rcases eq_or_ne η 0 with rfl | hη0
  · exact hΓ0 _ hη (by simp)
  · exact hN x (hKU hx) η hη0 hη

/-- **The pullback on a compact set of test functions.** For a compact set `Q` of real test
functions on `U`, the values `ι^* T ψ`, `ψ ∈ Q`, are bounded by a continuous seminorm of
`𝓓'_Γ(W)`. -/
private theorem exists_seminorm_pullbackInl_apply_le
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    {Q : Set 𝓓(U, ℝ)} (hQ : IsCompact Q) :
    ∃ p : Seminorm ℂ (WaveFrontSpace W Γ), Continuous p ∧ ∀ u : WaveFrontSpace W Γ, ∀ ψ ∈ Q,
      ‖u.toDistribution.pullbackInl hU (notMem_waveFrontSet hN u) ψ‖ ≤ p u := by
  -- The complexified test functions of `Q` are supported in one compact set `K`.
  set Qc : Set 𝓓(U, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM '' Q
  have hQc : IsCompact Qc := hQ.image (postcompCLM _).continuous
  obtain ⟨K, hKU, hQK⟩ := TestFunction.exists_compacts_forall_tsupport_subset_of_isCompact hQc
  have hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ ({0} : Set E), t • ξ ∈ ({0} : Set E) := by
    rintro t - ξ rfl
    simp
  obtain ⟨B, hB⟩ := exists_forall_one_add_norm_pow_mul_norm_fourier_le hQc 0
  -- The family of cutoffs is `Qc`, all at the point `ξ = 0`, with weight order `0`.
  obtain ⟨p, hp, hpQ⟩ := exists_seminorm_localFourier_pullbackInl_le_of_isCompact hU hΓ hcone hΓ0
    hN K.isCompact hKU isClosed_singleton (mem_singleton 0) hVcone
    (disjoint_prod_zero_pullbackInlCone hΓ0 hN hKU) (X := Qc) (φ := (↑)) (fun ψ ↦ hQK _ ψ.property)
    (ξ := fun _ ↦ 0) (fun _ ↦ mem_singleton 0) (N := 0) (fun ψ ↦ hB ψ ψ.property) (by
      intro L _ _ ε hε χ
      simpa only [pow_zero, Complex.ofReal_one, one_mul] using
        (isCompact_range_tsum L hε χ hQc).insert 0)
  refine ⟨p, hp, fun u ψ hψ ↦ ?_⟩
  -- `ι^* T ψ` is the localized Fourier transform of `ι^* T` with cutoff `ψ` at `0`.
  have h := hpQ u ⟨postcompCLM (𝕜 := ℝ) ofRealCLM ψ, ψ, hψ, rfl⟩
  rwa [pow_zero, one_mul, localFourier_at_zero, complexPairing_postcompCLM_ofRealCLM] at h

end Measurable

/-! ### The pullback as a continuous linear map -/

/-- The pullback `ι^* : 𝓓'_Γ(W) → 𝓓'_{ιᵀ Γ}(U)` as a linear map, before its continuity is
proved. -/
private def pullbackInlₗ (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    WaveFrontSpace W Γ →ₗ[ℂ] WaveFrontSpace U (pullbackInlCone Γ) where
  toFun u := mk (u.toDistribution.pullbackInl hU fun x hx η hη hmem ↦
      hN x hx η hη (u.waveFrontSet_toDistribution_subset hmem))
    (waveFrontSet_pullbackInl_subset_pullbackInlCone hU _ u.waveFrontSet_toDistribution_subset)
  map_add' u v := ext <| by
    simp only [toDistribution_mk, map_add]
    exact pullbackInl_add hU (notMem_waveFrontSet hN u) (notMem_waveFrontSet hN v)
  map_smul' c u := ext <| by
    simp only [toDistribution_mk, map_smul, RingHom.id_apply]
    exact pullbackInl_smul hU c (notMem_waveFrontSet hN u)

private theorem toDistribution_pullbackInlₗ
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) :
    (pullbackInlₗ hU hN u).toDistribution =
      u.toDistribution.pullbackInl hU fun x hx η hη hmem ↦
        hN x hx η hη (u.waveFrontSet_toDistribution_subset hmem) :=
  toDistribution_mk _ _

/-- **Continuity of the pullback to `E × {0}` in the normal topology.** Let `Γ` be a cone of
nonzero covectors over `W`, closed in `W × ((E × D) \ {0})`, containing no conormal covector
`((x, 0), (0, η))` of `E × {0}` over `U`. Then the pullback `ι^* T` along `ι : x ↦ (x, 0)`
(`Distribution.pullbackInl`) is a continuous linear map from `𝓓'_Γ(W)` to `𝓓'_{ιᵀ Γ}(U)`, where
`ιᵀ Γ = {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}` (Brouder, Dang and Hélein, Theorem 6.3, for the
linear injection `ι`). -/
def pullbackInlCLM (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    WaveFrontSpace W Γ →L[ℂ] WaveFrontSpace U (pullbackInlCone Γ) :=
  ⟨pullbackInlₗ hU hN, by
    borelize E D
    refine continuous_linearMap_of_le _ ?_ fun j ↦ ?_
    · -- Continuity into `𝓓'(U)`: the values on a compact set of test functions.
      refine continuous_of_tendsto_nhds_zero (toDistribution ∘ₗ pullbackInlₗ hU hN) ?_
      refine CompactConvergenceCLM.hasBasis_nhds_zero.tendsto_right_iff.2 fun ⟨Q, V'⟩ ⟨hQ, hV'⟩ ↦ ?_
      obtain ⟨r, hr, hrV'⟩ := Metric.mem_nhds_iff.1 hV'
      obtain ⟨p, hp, hpQ⟩ := exists_seminorm_pullbackInl_apply_le hU hΓ hcone hΓ0 hN hQ
      filter_upwards [(hp.tendsto' 0 0 (map_zero p)) (Iio_mem_nhds hr)] with u hu ψ hψ
      have h := hpQ u ψ hψ
      rw [LinearMap.coe_comp, Function.comp_apply, toDistribution_pullbackInlₗ]
      exact hrV' (mem_ball_zero_iff.2 (h.trans_lt hu))
    · -- The seminorms of the target.
      obtain ⟨p, hp, hpj⟩ := exists_seminorm_localFourier_pullbackInl_le hU hΓ hcone hΓ0 hN j
      refine ⟨p, hp, fun u ↦ seminorm_le_bound j _ (apply_nonneg _ _) fun ξ hξ ↦ ?_⟩
      simpa only [toDistribution_pullbackInlₗ] using hpj u ξ hξ⟩

@[simp]
theorem toDistribution_pullbackInlCLM (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) :
    (pullbackInlCLM hU hΓ hcone hΓ0 hN u).toDistribution =
      u.toDistribution.pullbackInl hU fun x hx η hη hmem ↦
        hN x hx η hη (u.waveFrontSet_toDistribution_subset hmem) :=
  toDistribution_pullbackInlₗ hU hN u

end WaveFrontSpace

end TauCeti
