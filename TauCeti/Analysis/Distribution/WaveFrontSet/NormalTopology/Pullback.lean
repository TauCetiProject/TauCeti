/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Basic
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Distribution.TestFunction.Compact
import TauCeti.Analysis.Distribution.TestFunction.FourierAtom
import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Normed.Module.Cone
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Continuity of the pullback to `E × {0}` in the normal topology

Let `W` be an open set of the Euclidean product `WithLp 2 (E × D)`, `U` an open set of `E` with
`U × {0} ⊆ W`, and `Γ` a set of covectors on `W`. A distribution `T` on `W` whose wave front set
contains no covector conormal to `E × {0}` over `U` has a pullback `ι^* T` along `ι : x ↦ (x, 0)`
(`Distribution.pullbackInl`), and `WF(ι^* T)` lies in the image of `WF(T)` under the transpose
`ιᵀ (ξ, η) = ξ`. So if `WF(T) ⊆ Γ`, the wave front set of `ι^* T` lies in the fixed set

`pullbackInlCone Γ = {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}`

(`TauCeti.waveFrontSet_pullbackInl_subset_pullbackInlCone`). This file proves that the pullback is
continuous for the normal topologies of Hörmander's spaces (`TauCeti.WaveFrontSpace`):

`ι^* : 𝓓'_Γ(W) →L[ℂ] 𝓓'_{pullbackInlCone Γ}(U)`

(`TauCeti.WaveFrontSpace.pullbackInlCLM`), when `Γ` is a closed cone in `W × (E × D \ {0})` which
contains no covector over `U × {0}` conormal to `E × {0}`, as in Brouder, Dang and Hélein.

## The argument

Fix a compact set `K ⊆ U`. Since `Γ` is closed and conic, there are a cutoff `χ` equal to one near
`K × {0}` and a closed cone `V''` containing a conic neighbourhood of the conormal directions such
that no covector of `Γ` over the support of `χ` points into `V''`
(`TauCeti.exists_isOpen_cone_forall_notMem`). Expanding along a lattice adapted to the support of
`χ` (`Distribution.complexPairing_pullbackInl_eq_tsum`), for `ψ` supported in `K`

`ι^* T (ψ) = c ∑ m, 𝓕 ψ (m.fst) T (χ e_(-m))`,

and the series splits in two. Over `-V''`, `|T (χ e_(-m))|` is bounded by the seminorm
`‖T‖_{χ,V'',N}` of the normal topology times `(1 + ‖m‖)^(-N)`. Off `-V''`, `‖m‖` is comparable
to `‖m.fst‖`, where `𝓕 ψ` decays rapidly, so the terms sum in the topology of test functions to
`T` paired with one test function `A ψ`, the *synthesis* of `𝓕 ψ` from the modulated cutoffs
`χ.modulate m`; `A` is a continuous linear map of `ψ`. Hence

`|ι^* T (ψ)| ≤ C |T (A ψ)| + C sup |𝓕 ψ| ‖T‖_{χ,V'',N}`.

A compact set of test functions on `U` is supported in a single compact `K`
(`TestFunction.exists_compacts_forall_tsupport_subset`), and `A` maps it to a compact set, so this
gives continuity into `𝓓'(U)`, whose topology is uniform convergence on compact sets.

For a seminorm `‖·‖_{φ,V,N}` of the target, the same split is applied to the localized Fourier
transform `ι^* T (φ e_ξ)`, `ξ ∈ V`, with `V''` a closed cone containing a conic neighbourhood of
the covectors with first component in `V ∪ {0}`. Off `-V''`, `‖m.fst + ξ‖` is at least
`c (‖ξ‖ + ‖m‖)`, so the syntheses `(1 + ‖ξ‖)^N A (φ e_ξ)` tend to zero as `ξ → ∞` in `V` and lie
in a compact set `S` of test functions. Over `-V''`, Peetre's inequality
`1 + ‖ξ‖ ≤ (1 + ‖m.fst + ξ‖) (1 + ‖m‖)` moves the weight onto `m`. This gives

`‖ι^* T‖_{φ,V,N} ≤ C sup_{g ∈ S} |T g| + C ‖T‖_{χ,V'',N + q}`.

## Main declarations

* `TauCeti.pullbackInlCone Γ`: the image of `Γ` over `E × {0}` under `(ξ, η) ↦ ξ`.
* `TauCeti.waveFrontSet_pullbackInl_subset_pullbackInlCone`: the wave front set of the pullback
  of a distribution with wave front set in `Γ` lies in `pullbackInlCone Γ`.
* `TauCeti.WaveFrontSpace.pullbackInlCLM`: the pullback to `E × {0}` as a continuous linear map
  `𝓓'_Γ(W) →L[ℂ] 𝓓'_{pullbackInlCone Γ}(U)` for the normal topologies, with
  `TauCeti.WaveFrontSpace.toDistribution_pullbackInlCLM`.

## References

* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, §5, Proposition 5.1 (continuity of the pullback in the normal
  topology).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory WithLp
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff Real SchwartzMap

namespace TauCeti

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- If the direction of a covector `ζ ≠ 0` is at distance more than `ε ≤ 1` from the unit
covectors with first component in a cone `V`, then the first component of `ζ` is far from `V`:
`ε / 8 (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖` for `ξ ∈ V`. Otherwise `ζ` would be close to
`ζ' = (ξ, ζ.snd)`, whose direction lies in that set. -/
private theorem mul_add_le_norm_fst_sub {V : Set E} (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    {ε : ℝ} (hε1 : ε ≤ 1) {ξ : E} (hξ : ξ ∈ V) {ζ : WithLp 2 (E × D)} (hζ0 : ζ ≠ 0)
    (hζC : ‖ζ‖⁻¹ • ζ ∉ cthickening ε (WithLp.fst ⁻¹' V ∩ sphere 0 1)) :
    ε / 8 * (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖ := by
  by_contra hlt
  push Not at hlt
  set n := ‖ζ‖
  have hn : 0 < n := norm_pos_iff.2 hζ0
  set d := ‖ζ.fst - ξ‖
  have hξn : ‖ξ‖ ≤ n + d := by
    have h1 : ‖ξ‖ ≤ ‖ζ.fst‖ + ‖ζ.fst - ξ‖ := by
      simpa using norm_sub_le ζ.fst (ζ.fst - ξ)
    linarith [WithLp.norm_fst_le (x := ζ)]
  have hd : 2 * d < ε * n := by
    have hd0 : 0 ≤ d := norm_nonneg _
    have hε : 0 ≤ ε := by
      by_contra h
      push Not at h
      nlinarith [norm_nonneg ξ]
    have h2 : d < ε / 8 * (2 * n + d) :=
      hlt.trans_le (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have h3 : ε / 8 * d ≤ d / 8 := by nlinarith
    nlinarith
  -- `ζ` is close to `ζ' = (ξ, ζ.snd)`, whose direction lies in the set.
  set ζ' : WithLp 2 (E × D) := toLp 2 (ξ, ζ.snd)
  have hζζ' : ‖ζ' - ζ‖ = d := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp [ζ', norm_sub_rev ξ ζ.fst, d]
  have hζ'0 : ζ' ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg] at hζζ'
    nlinarith [mul_le_mul_of_nonneg_right hε1 hn.le]
  have hmem : ‖ζ'‖⁻¹ • ζ' ∈ WithLp.fst ⁻¹' V ∩ sphere 0 1 := by
    refine ⟨hVcone _ (inv_pos.2 (norm_pos_iff.2 hζ'0)) ξ hξ, ?_⟩
    simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hζ'0)]
  refine hζC (mem_cthickening_of_dist_le _ _ _ _ hmem ?_)
  rw [dist_eq_norm, norm_sub_rev, ← mul_le_mul_iff_of_pos_right hn]
  have h := norm_inv_smul_sub_inv_smul_mul_norm_le hζ'0 hζ0
  rw [hζζ'] at h
  linarith

/-- **A closed cone separated from a closed cone of first components.** Let `V` be a closed cone of
`E` and `O` an open cone of `E × D` containing every nonzero covector whose first component lies in
`V`. There are a closed cone `V'' ⊆ O ∪ {0}` and `c > 0` such that, for `ξ ∈ V` and `ζ ∉ V''`,
the first component of `ζ` is far from `ξ`: `c (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖`. -/
private theorem exists_isClosed_cone_mul_add_le_norm_fst_sub {V : Set E} (hV : IsClosed V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {O : Set (WithLp 2 (E × D))} (hO : IsOpen O)
    (hOcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ O, t • ζ ∈ O)
    (hVO : ∀ ζ : WithLp 2 (E × D), ζ.fst ∈ V → ζ ≠ 0 → ζ ∈ O) :
    ∃ V'' : Set (WithLp 2 (E × D)), IsClosed V'' ∧ (∀ t : ℝ, 0 < t → ∀ ζ ∈ V'', t • ζ ∈ V'') ∧
      (∀ ζ ∈ V'', ζ ≠ 0 → ζ ∈ O) ∧
      ∃ c > 0, ∀ ξ ∈ V, ∀ ζ ∉ V'', c * (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖ := by
  -- The unit covectors with first component in `V` form a compact subset of `O`.
  set C : Set (WithLp 2 (E × D)) := WithLp.fst ⁻¹' V ∩ sphere 0 1
  have hC : IsCompact C := (isCompact_sphere _ _).inter_left (hV.preimage (by fun_prop))
  obtain ⟨ε₀, hε₀, hε₀O⟩ := hC.exists_cthickening_subset_open hO fun ζ hζ ↦
    hVO ζ hζ.1 (ne_zero_of_mem_unit_sphere ⟨ζ, hζ.2⟩)
  set ε := min ε₀ 1
  have hεO : cthickening ε C ⊆ O := (cthickening_mono (min_le_left _ _) _).trans hε₀O
  set u : WithLp 2 (E × D) → WithLp 2 (E × D) := fun ζ ↦ ‖ζ‖⁻¹ • ζ
  have hu : ContinuousOn u {0}ᶜ :=
    (continuous_norm.continuousOn.inv₀ fun ζ hζ ↦ norm_ne_zero_iff.2 hζ).smul continuousOn_id
  have hut (t : ℝ) (ht : 0 < t) (ζ : WithLp 2 (E × D)) : u (t • ζ) = u ζ := by
    simp only [u, norm_smul, Real.norm_of_nonneg ht.le, mul_inv, smul_smul]
    rw [mul_right_comm, inv_mul_cancel₀ ht.ne', one_mul]
  -- `V''` is the cone over the closed `ε`-neighbourhood of `C`.
  refine ⟨{ζ | ζ = 0 ∨ u ζ ∈ cthickening ε C}, ?_, ?_, ?_, ε / 8, by positivity, ?_⟩
  · rw [← isOpen_compl_iff]
    have h : {ζ | ζ = 0 ∨ u ζ ∈ cthickening ε C}ᶜ = {0}ᶜ ∩ u ⁻¹' (cthickening ε C)ᶜ := by
      ext ζ
      simp [not_or]
    rw [h]
    exact hu.isOpen_inter_preimage isOpen_compl_singleton isClosed_cthickening.isOpen_compl
  · rintro t ht ζ (h0 | hζ)
    · exact Or.inl (by rw [h0, smul_zero])
    · exact Or.inr (by rw [mem_ofPred_eq, hut t ht]; exact hζ)
  · rintro ζ (h0 | hζ) hζ0
    · exact absurd h0 hζ0
    · have h := hOcone ‖ζ‖ (norm_pos_iff.2 hζ0) _ (hεO hζ)
      rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hζ0), one_smul] at h
  · intro ξ hξ ζ hζ
    simp only [mem_ofPred_eq, not_or] at hζ
    exact mul_add_le_norm_fst_sub hVcone (min_le_right _ _) hξ hζ.1 hζ.2

/-! ### Lattice synthesis of Schwartz functions -/

/-- The Schwartz seminorm `sup_{x} (1 + ‖x‖)^k ‖h x‖`, up to the factor `2^k`. -/
private abbrev decaySeminorm (k : ℕ) : Seminorm ℂ 𝓢(E, ℂ) :=
  (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ E ℂ)

omit [FiniteDimensional ℝ E] in
private theorem one_add_norm_pow_mul_norm_le (h : 𝓢(E, ℂ)) (k : ℕ) (x : E) :
    (1 + ‖x‖) ^ k * ‖h x‖ ≤ 2 ^ k * decaySeminorm k h := by
  have := h.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl x
  rwa [norm_iteratedFDeriv_zero] at this

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] in
/-- On a set `M` of covectors with `‖ζ‖ ≤ R ‖ζ.fst‖`, the values `h ζ.fst` of a Schwartz function
decay rapidly in `ζ`, uniformly in terms of the Schwartz seminorms of `h`. -/
private theorem norm_apply_fst_mul_le {R : ℝ} {ζ : WithLp 2 (E × D)} (hζ : ‖ζ‖ ≤ R * ‖ζ.fst‖)
    (h : 𝓢(E, ℂ)) (k : ℕ) :
    (1 + ‖ζ‖) ^ k * ‖h ζ.fst‖ ≤ (1 + |R|) ^ k * 2 ^ k * decaySeminorm k h := by
  have h1 : 1 + ‖ζ‖ ≤ (1 + |R|) * (1 + ‖ζ.fst‖) := by
    nlinarith [le_abs_self R, abs_nonneg R, norm_nonneg ζ.fst,
      mul_le_mul_of_nonneg_right (le_abs_self R) (norm_nonneg ζ.fst)]
  calc (1 + ‖ζ‖) ^ k * ‖h ζ.fst‖ ≤ ((1 + |R|) * (1 + ‖ζ.fst‖)) ^ k * ‖h ζ.fst‖ := by gcongr
    _ = (1 + |R|) ^ k * ((1 + ‖ζ.fst‖) ^ k * ‖h ζ.fst‖) := by rw [mul_pow, mul_assoc]
    _ ≤ (1 + |R|) ^ k * (2 ^ k * decaySeminorm k h) :=
        mul_le_mul_of_nonneg_left (one_add_norm_pow_mul_norm_le h k _) (by positivity)
    _ = _ := by ring


section Synthesis

variable {K : Compacts (WithLp 2 (E × D))} (χ : 𝓓_{K}(WithLp 2 (E × D), ℂ))
  (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
  {M : Set (WithLp 2 (E × D))} {R : ℝ} (hM : ∀ ζ ∈ M, ‖ζ‖ ≤ R * ‖ζ.fst‖)

/-- The coefficient `h ζ.fst` of the modulated cutoff `χ.modulate ζ` in the synthesis of `h`,
for `ζ ∈ M`. -/
private def synthesisCoeff (M : Set (WithLp 2 (E × D))) (h : 𝓢(E, ℂ)) (ζ : WithLp 2 (E × D)) :
    ℂ :=
  M.indicator (fun ζ ↦ h ζ.fst) ζ

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
include hM in
/-- The terms `h ζ.fst • χ.modulate ζ`, `ζ ∈ M`, of the synthesis decay rapidly in every
seminorm `N_k`, uniformly in terms of a Schwartz seminorm of `h`. -/
private theorem seminorm_synthesisCoeff_smul_modulate_le (h : 𝓢(E, ℂ)) (k q : ℕ)
    (ζ : WithLp 2 (E × D)) :
    N[ℂ]_{K, k} (synthesisCoeff M h ζ • χ.modulate ζ) ≤
      ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ * (2 * π) ^ k * (1 + |R|) ^ (k + q) *
        2 ^ (k + q) * decaySeminorm (k + q) h * ((1 + ‖ζ‖) ^ q)⁻¹ := by
  set S := ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ
  rw [map_smul_eq_mul]
  by_cases hζ : ζ ∈ M
  · have hpi : (1 + 2 * π * ‖ζ‖) ^ k ≤ (2 * π) ^ k * (1 + ‖ζ‖) ^ k := by
      rw [← mul_pow]
      gcongr
      nlinarith [Real.two_le_pi, norm_nonneg ζ]
    have hdecay := norm_apply_fst_mul_le (hM ζ hζ) h (k + q)
    have hpos : 0 < (1 + ‖ζ‖) ^ q := by positivity
    rw [synthesisCoeff, indicator_of_mem hζ, le_mul_inv_iff₀ hpos]
    calc ‖h ζ.fst‖ * N[ℂ]_{K, k} (χ.modulate ζ) * (1 + ‖ζ‖) ^ q
        ≤ ‖h ζ.fst‖ * (S * ((2 * π) ^ k * (1 + ‖ζ‖) ^ k)) * (1 + ‖ζ‖) ^ q := by
          gcongr
          exact (ContDiffMapSupportedIn.seminorm_modulate_le χ ζ k).trans (by gcongr)
      _ = S * (2 * π) ^ k * ((1 + ‖ζ‖) ^ (k + q) * ‖h ζ.fst‖) := by ring
      _ ≤ S * (2 * π) ^ k * ((1 + |R|) ^ (k + q) * 2 ^ (k + q) * decaySeminorm (k + q) h) := by
          gcongr
      _ = _ := by ring
  · rw [synthesisCoeff, indicator_of_notMem hζ, norm_zero, zero_mul]
    positivity

include hM in
/-- For every `k`, the seminorms `N_k` of the terms of the synthesis are summable over the dual
lattice. -/
private theorem summable_seminorm_synthesisCoeff_smul_modulate (h : 𝓢(E, ℂ)) (k : ℕ) :
    Summable fun m : ZLattice.dual L ↦
      ContDiffMapSupportedIn.seminorm ℝ _ ℂ ⊤ K k (synthesisCoeff M h m • χ.modulate m) := by
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hsum := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  refine (hsum.mul_left (ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ * (2 * π) ^ k *
    (1 + |R|) ^ (k + q) * 2 ^ (k + q) * decaySeminorm (k + q) h)).of_nonneg_of_le
    (fun _ ↦ apply_nonneg _ _) fun m ↦ ?_
  rw [← ContDiffMapSupportedIn.seminorm_apply_eq_of_scalars (𝕜 := ℂ)]
  exact seminorm_synthesisCoeff_smul_modulate_le χ hM h k q m

include hM in
private theorem summable_synthesisCoeff_smul_modulate (h : 𝓢(E, ℂ)) :
    Summable fun m : ZLattice.dual L ↦ synthesisCoeff M h m • χ.modulate m :=
  ContDiffMapSupportedIn.summable_of_forall_summable_seminorm
    (summable_seminorm_synthesisCoeff_smul_modulate χ L hM h)

/-- The synthesis `h ↦ ∑ m ∈ M, h m.fst • χ.modulate m` over the vectors `m` of the dual lattice
lying in `M`, as a linear map. -/
private def synthesisₗ : 𝓢(E, ℂ) →ₗ[ℂ] 𝓓_{K}(WithLp 2 (E × D), ℂ) where
  toFun h := ∑' m : ZLattice.dual L, synthesisCoeff M h m • χ.modulate m
  map_add' h h' := by
    rw [← (summable_synthesisCoeff_smul_modulate χ L hM h).tsum_add
      (summable_synthesisCoeff_smul_modulate χ L hM h')]
    congr 1 with m : 1
    rw [← add_smul]
    congr 1
    by_cases hm : (m : WithLp 2 (E × D)) ∈ M <;> simp [synthesisCoeff, hm]
  map_smul' c h := by
    rw [RingHom.id_apply, ← (summable_synthesisCoeff_smul_modulate χ L hM h).tsum_const_smul c]
    congr 1 with m : 1
    rw [smul_smul]
    congr 1
    by_cases hm : (m : WithLp 2 (E × D)) ∈ M <;> simp [synthesisCoeff, hm]

include hM in
/-- The seminorms of the synthesis are bounded by Schwartz seminorms. -/
private theorem seminorm_synthesisₗ_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : 𝓢(E, ℂ), N[ℂ]_{K, k} (synthesisₗ χ L hM h) ≤
      C * decaySeminorm (k + (Module.finrank ℤ (ZLattice.dual L) + 1)) h := by
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hsum := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  set A := ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ * (2 * π) ^ k * (1 + |R|) ^ (k + q) *
    2 ^ (k + q)
  set B₀ := ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹
  have hA : 0 ≤ A * B₀ := mul_nonneg (by positivity) (tsum_nonneg fun _ ↦ by positivity)
  refine ⟨A * B₀, hA, fun h ↦ ?_⟩
  rw [ContDiffMapSupportedIn.seminorm_apply_eq_of_scalars]
  refine (ContDiffMapSupportedIn.seminorm_tsum_le
    (summable_seminorm_synthesisCoeff_smul_modulate χ L hM h) k).trans ?_
  calc ∑' m : ZLattice.dual L, ContDiffMapSupportedIn.seminorm ℝ _ ℂ ⊤ K k
        (synthesisCoeff M h m • χ.modulate m)
      ≤ ∑' m : ZLattice.dual L, A * decaySeminorm (k + q) h *
          ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
        refine (summable_seminorm_synthesisCoeff_smul_modulate χ L hM h k).tsum_le_tsum
          (fun m ↦ ?_) (hsum.mul_left _)
        rw [← ContDiffMapSupportedIn.seminorm_apply_eq_of_scalars (𝕜 := ℂ)]
        exact seminorm_synthesisCoeff_smul_modulate_le χ hM h k q m
    _ = A * B₀ * decaySeminorm (k + q) h := by
        rw [tsum_mul_left]
        ring

/-- The synthesis `h ↦ ∑ m ∈ M, h m.fst • χ.modulate m` over the vectors `m` of the dual lattice
lying in `M`, a continuous linear map from the Schwartz functions to the smooth functions
supported in `K`, for `‖ζ‖ ≤ R ‖ζ.fst‖` on `M`. -/
private def synthesis : 𝓢(E, ℂ) →L[ℂ] 𝓓_{K}(WithLp 2 (E × D), ℂ) where
  toLinearMap := synthesisₗ χ L hM
  cont := WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms ℂ E ℂ)
    (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ ⊤ K) _ fun k ↦ by
      obtain ⟨C, hC0, hC⟩ := seminorm_synthesisₗ_le χ L hM k
      exact ⟨Finset.Iic (k + (Module.finrank ℤ (ZLattice.dual L) + 1), 0), ⟨C, hC0⟩,
        fun h ↦ hC h⟩

private theorem synthesis_apply (h : 𝓢(E, ℂ)) :
    synthesis χ L hM h = ∑' m : ZLattice.dual L, synthesisCoeff M h m • χ.modulate m :=
  rfl

end Synthesis


omit [FiniteDimensional ℝ E] in
/-- A Schwartz function `h` decays at a point `y` far from a frequency `ξ` and a scale `r`: if
`c (‖ξ‖ + r) ≤ ‖y‖`, then `(1 + ‖ξ‖)^a (1 + r)^b ‖h y‖` is bounded by a Schwartz seminorm of `h`. -/
private theorem one_add_norm_pow_mul_one_add_pow_mul_norm_le {c : ℝ} (hc : 0 < c) (h : 𝓢(E, ℂ))
    {ξ y : E} {r : ℝ} (hr : 0 ≤ r) (hsep : c * (‖ξ‖ + r) ≤ ‖y‖) (a b : ℕ) :
    (1 + ‖ξ‖) ^ a * (1 + r) ^ b * ‖h y‖ ≤
      (min c 1)⁻¹ ^ (a + b) * (2 ^ (a + b) * decaySeminorm (a + b) h) := by
  set c' := min c 1
  have hc' : 0 < c' := lt_min hc one_pos
  have h1 : 1 + ‖ξ‖ + r ≤ c'⁻¹ * (1 + ‖y‖) := by
    rw [le_inv_mul_iff₀ hc']
    have h2 : c' * (‖ξ‖ + r) ≤ c * (‖ξ‖ + r) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    nlinarith [min_le_right c 1]
  calc (1 + ‖ξ‖) ^ a * (1 + r) ^ b * ‖h y‖ ≤ (1 + ‖ξ‖ + r) ^ (a + b) * ‖h y‖ := by
        rw [pow_add]
        refine mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (by positivity)
          (by linarith) a) (pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg ξ]) b)
          (by positivity) (by positivity)) (norm_nonneg _)
    _ ≤ (c'⁻¹ * (1 + ‖y‖)) ^ (a + b) * ‖h y‖ := by gcongr
    _ = c'⁻¹ ^ (a + b) * ((1 + ‖y‖) ^ (a + b) * ‖h y‖) := by rw [mul_pow, mul_assoc]
    _ ≤ c'⁻¹ ^ (a + b) * (2 ^ (a + b) * decaySeminorm (a + b) h) :=
        mul_le_mul_of_nonneg_left (one_add_norm_pow_mul_norm_le h _ y) (by positivity)

/-- A continuous map on a closed subset `V` of a proper space that tends to `y` at infinity on `V`
has its values on `V` in a compact set. -/
private theorem exists_isCompact_forall_mem {E X : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [TopologicalSpace X] {f : E → X} (hf : Continuous f) {V : Set E} (hV : IsClosed V) {y : X}
    (hy : ∀ s ∈ 𝓝 y, ∃ R, ∀ ξ ∈ V, R < ‖ξ‖ → f ξ ∈ s) :
    ∃ S : Set X, IsCompact S ∧ ∀ ξ ∈ V, f ξ ∈ S := by
  -- Extend `f` to the one-point compactification of `V` by `y` at infinity.
  have htend : Tendsto (fun ξ : V ↦ f ξ) (coclosedCompact V) (𝓝 y) := by
    refine hasBasis_coclosedCompact.tendsto_left_iff.2 fun s hs ↦ ?_
    obtain ⟨R, hR⟩ := hy s hs
    refine ⟨{ξ : V | ‖(ξ : E)‖ ≤ R}, ⟨isClosed_le (by fun_prop) continuous_const, ?_⟩,
      fun ξ hξ ↦ hR ξ ξ.property (lt_of_not_ge hξ)⟩
    have himage : ((↑) : V → E) '' {ξ : V | ‖(ξ : E)‖ ≤ R} = closedBall 0 R ∩ V := by
      ext x
      simp [and_comm]
    exact Subtype.isCompact_iff.2 (himage ▸ (isCompact_closedBall (0 : E) R).inter_right hV)
  let g := OnePoint.continuousMapMk ⟨fun ξ : V ↦ f ξ, hf.comp continuous_subtypeVal⟩ y htend
  exact ⟨range g, isCompact_range g.continuous, fun ξ hξ ↦ ⟨(⟨ξ, hξ⟩ : V), rfl⟩⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- A term `h m.fst • χ.modulate m` of the synthesis of a translate `h = H (· + ξ)`, with `m` in a
set `M` far from `ξ`, decays jointly in `ξ` and `m` in the seminorm `N_k`. -/
private theorem one_add_norm_pow_mul_seminorm_synthesisCoeff_smul_modulate_le
    {K : Compacts (WithLp 2 (E × D))} (χ : 𝓓_{K}(WithLp 2 (E × D), ℂ))
    {M : Set (WithLp 2 (E × D))} {h H : 𝓢(E, ℂ)} {ξ : E} (hh : ∀ x, h x = H (x + ξ)) {c : ℝ}
    (hc : 0 < c) (hsep : ∀ m ∈ M, c * (‖ξ‖ + ‖m‖) ≤ ‖m.fst + ξ‖) (N k q : ℕ)
    (m : WithLp 2 (E × D)) :
    (1 + ‖ξ‖) ^ N * N[ℂ]_{K, k} (synthesisCoeff M h m • χ.modulate m) ≤
      ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ * (2 * π) ^ k *
        ((min c 1)⁻¹ ^ (N + 1 + (k + q)) * (2 ^ (N + 1 + (k + q)) *
          decaySeminorm (N + 1 + (k + q)) H)) * (1 + ‖ξ‖)⁻¹ * ((1 + ‖m‖) ^ q)⁻¹ := by
  set S := ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ
  rw [map_smul_eq_mul]
  by_cases hm : m ∈ M
  · have hcoef := one_add_norm_pow_mul_one_add_pow_mul_norm_le hc H (y := m.fst + ξ)
      (norm_nonneg _) (hsep m hm) (N + 1) (k + q)
    have hpi : N[ℂ]_{K, k} (χ.modulate m) ≤ S * ((2 * π) ^ k * (1 + ‖m‖) ^ k) := by
      refine (ContDiffMapSupportedIn.seminorm_modulate_le χ m k).trans ?_
      gcongr
      rw [← mul_pow]
      gcongr
      nlinarith [Real.two_le_pi, norm_nonneg m]
    rw [synthesisCoeff, indicator_of_mem hm, hh]
    calc (1 + ‖ξ‖) ^ N * (‖H (m.fst + ξ)‖ * N[ℂ]_{K, k} (χ.modulate m))
        ≤ (1 + ‖ξ‖) ^ N * (‖H (m.fst + ξ)‖ * (S * ((2 * π) ^ k * (1 + ‖m‖) ^ k))) := by gcongr
      _ = S * (2 * π) ^ k * ((1 + ‖ξ‖) ^ (N + 1) * (1 + ‖m‖) ^ (k + q) * ‖H (m.fst + ξ)‖) *
            (1 + ‖ξ‖)⁻¹ * ((1 + ‖m‖) ^ q)⁻¹ := by
        field_simp
        ring
      _ ≤ _ := by gcongr
  · rw [synthesisCoeff, indicator_of_notMem hm, norm_zero, zero_mul, mul_zero]
    positivity

/-- Modulating a smooth function supported in `K` by frequencies `ξ` in a cone `V` far from the set
`M` of covectors: the synthesis of the Fourier transform of `φ e_ξ`, weighted by `(1 + ‖ξ‖)^N`,
decays like `(1 + ‖ξ‖)⁻¹` in every seminorm. -/
private theorem exists_seminorm_smul_synthesis_le [MeasurableSpace E] [BorelSpace E] {U : Opens E}
    {K : Compacts (WithLp 2 (E × D))}
    (χ : 𝓓_{K}(WithLp 2 (E × D), ℂ)) (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L]
    [IsZLattice ℝ L] {M : Set (WithLp 2 (E × D))} {R : ℝ} (hM : ∀ ζ ∈ M, ‖ζ‖ ≤ R * ‖ζ.fst‖)
    {V : Set E} {c : ℝ} (hc : 0 < c)
    (hsep : ∀ ξ ∈ V, ∀ m ∈ M, c * (‖ξ‖ + ‖m‖) ≤ ‖m.fst + ξ‖) (φ : 𝓓(U, ℂ)) (N k : ℕ) :
    ∃ C, ∀ ξ ∈ V, N[ℂ]_{K, k} ((((1 + ‖ξ‖) ^ N : ℝ) : ℂ) • synthesis χ L hM
      (𝓕 (toSchwartzMapCLM ℂ (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
        (TauCeti.contDiff_fourierAtom ξ) φ)))) ≤ C * (1 + ‖ξ‖)⁻¹ := by
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hsum := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  set H := 𝓕 (toSchwartzMapCLM ℂ φ)
  set K₀ := (min c 1)⁻¹ ^ (N + 1 + (k + q)) * (2 ^ (N + 1 + (k + q)) *
    decaySeminorm (N + 1 + (k + q)) H)
  set A := ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ * (2 * π) ^ k * K₀
  refine ⟨A * ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹, fun ξ hξ ↦ ?_⟩
  set h := 𝓕 (toSchwartzMapCLM ℂ (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (TauCeti.contDiff_fourierAtom ξ) φ))
  have hh (x : E) : h x = H (x + ξ) := by
    simp only [h, H, SchwartzMap.fourier_coe, coe_toSchwartzMapCLM]
    exact TestFunction.fourier_bilinLeftCLM_fourierAtom φ ξ x
  -- Each term of the synthesis decays jointly in `ξ` and `m`.
  have hterm (m : ZLattice.dual L) :
      (1 + ‖ξ‖) ^ N * ContDiffMapSupportedIn.seminorm ℝ _ ℂ ⊤ K k
        (synthesisCoeff M h m • χ.modulate m) ≤
        A * (1 + ‖ξ‖)⁻¹ * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
    rw [← ContDiffMapSupportedIn.seminorm_apply_eq_of_scalars (𝕜 := ℂ)]
    exact one_add_norm_pow_mul_seminorm_synthesisCoeff_smul_modulate_le χ hh hc (hsep ξ hξ) N k q m
  have hsyn := summable_seminorm_synthesisCoeff_smul_modulate χ L hM h k
  rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    ContDiffMapSupportedIn.seminorm_apply_eq_of_scalars, synthesis_apply]
  calc (1 + ‖ξ‖) ^ N * ContDiffMapSupportedIn.seminorm ℝ _ ℂ ⊤ K k
        (∑' m : ZLattice.dual L, synthesisCoeff M h m • χ.modulate m)
      ≤ (1 + ‖ξ‖) ^ N * ∑' m : ZLattice.dual L, ContDiffMapSupportedIn.seminorm ℝ _ ℂ ⊤ K k
          (synthesisCoeff M h m • χ.modulate m) := by
        gcongr
        exact ContDiffMapSupportedIn.seminorm_tsum_le
          (summable_seminorm_synthesisCoeff_smul_modulate χ L hM h) k
    _ ≤ ∑' m : ZLattice.dual L, A * (1 + ‖ξ‖)⁻¹ * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
        rw [← tsum_mul_left]
        exact (hsyn.mul_left _).tsum_le_tsum hterm (hsum.mul_left _)
    _ = _ := by
        rw [tsum_mul_left]
        ring

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- A family of smooth functions supported in `K`, indexed by `ξ` in `V`, whose seminorms decay
like `(1 + ‖ξ‖)⁻¹` eventually enters every neighbourhood of `0`. -/
private theorem exists_forall_mem_of_seminorm_le {K : Compacts (WithLp 2 (E × D))} {V : Set E}
    {g : E → 𝓓_{K}(WithLp 2 (E × D), ℂ)}
    (hg : ∀ k, ∃ C, ∀ ξ ∈ V, N[ℂ]_{K, k} (g ξ) ≤ C * (1 + ‖ξ‖)⁻¹)
    {s : Set 𝓓_{K}(WithLp 2 (E × D), ℂ)} (hs : s ∈ 𝓝 0) :
    ∃ R, ∀ ξ ∈ V, R < ‖ξ‖ → g ξ ∈ s := by
  choose C hC using hg
  obtain ⟨t, r, hr, hts⟩ :=
    (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ ⊤ K).mem_nhds_iff 0 s |>.1 hs
  refine ⟨∑ k ∈ t, |C k| / r, fun ξ hξ hR ↦ hts ?_⟩
  rw [Seminorm.mem_ball_zero]
  refine Seminorm.finset_sup_apply_lt hr fun k hk ↦ ?_
  have hξ0 : 0 < 1 + ‖ξ‖ := by positivity
  have hk' : |C k| / r < 1 + ‖ξ‖ :=
    (Finset.single_le_sum (f := fun k ↦ |C k| / r) (fun _ _ ↦ by positivity) hk).trans_lt
      (hR.trans (lt_one_add _))
  calc N[ℂ]_{K, k} (g ξ) ≤ C k * (1 + ‖ξ‖)⁻¹ := hC k ξ hξ
    _ ≤ |C k| * (1 + ‖ξ‖)⁻¹ := by gcongr; exact le_abs_self _
    _ < r := by
        rw [← div_eq_mul_inv, div_lt_iff₀ hξ0]
        rwa [div_lt_iff₀ hr, mul_comm] at hk'

/-- The weighted syntheses `(1 + ‖ξ‖)^N A (φ e_ξ)` of the modulated cutoffs `φ e_ξ`, for `ξ` in a
closed cone `V` far from `M`, lie in a compact set of test functions on `W`. -/
private theorem exists_isCompact_forall_smul_synthesis_mem [MeasurableSpace E] [BorelSpace E]
    {U : Opens E} {W : Opens (WithLp 2 (E × D))} {K : Compacts (WithLp 2 (E × D))}
    (hKW : (K : Set (WithLp 2 (E × D))) ⊆ W) (χ : 𝓓_{K}(WithLp 2 (E × D), ℂ))
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    {M : Set (WithLp 2 (E × D))} {R : ℝ} (hM : ∀ ζ ∈ M, ‖ζ‖ ≤ R * ‖ζ.fst‖) {V : Set E}
    (hV : IsClosed V) {c : ℝ} (hc : 0 < c)
    (hsep : ∀ ξ ∈ V, ∀ m ∈ M, c * (‖ξ‖ + ‖m‖) ≤ ‖m.fst + ξ‖) (φ : 𝓓(U, ℂ)) (N : ℕ) :
    ∃ S : Set 𝓓(W, ℂ), IsCompact S ∧ ∀ ξ ∈ V, ((1 + ‖ξ‖) ^ N : ℝ) •
      ofSupportedIn hKW (synthesis χ L hM (𝓕 (toSchwartzMapCLM ℂ
        (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom ξ) φ)))) ∈ S := by
  set A : 𝓓(U, ℂ) →L[ℂ] 𝓓(W, ℂ) := ofSupportedInCLM ℂ hKW ∘L synthesis χ L hM ∘L
    SchwartzMap.fourierTransformCLM ℂ ∘L toSchwartzMapCLM ℂ
  set f : E → 𝓓(W, ℂ) := fun ξ ↦ ((1 + ‖ξ‖) ^ N : ℝ) •
    A (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom ξ) φ)
  have hf : Continuous f := (by fun_prop : Continuous fun ξ : E ↦ (1 + ‖ξ‖) ^ N).smul
    (A.continuous.comp (TestFunction.continuous_bilinLeftCLM_fourierAtom φ))
  -- `f ξ` tends to zero at infinity on `V`, as the synthesis decays like `(1 + ‖ξ‖)⁻¹`.
  have hy (s : Set 𝓓(W, ℂ)) (hs : s ∈ 𝓝 0) : ∃ R, ∀ ξ ∈ V, R < ‖ξ‖ → f ξ ∈ s := by
    have hs' := (ofSupportedInCLM ℂ (n := ⊤) (F := ℂ) hKW).continuous.continuousAt.preimage_mem_nhds
      (by rwa [map_zero])
    obtain ⟨R, hR⟩ := exists_forall_mem_of_seminorm_le
      (fun k ↦ exists_seminorm_smul_synthesis_le χ L hM hc hsep φ N k) hs'
    refine ⟨R, fun ξ hξ hRξ ↦ ?_⟩
    have h := hR ξ hξ hRξ
    rw [mem_preimage, map_smul, Complex.coe_smul] at h
    simpa only [f, A, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM,
      SchwartzMap.fourierTransformCLM_apply] using h
  obtain ⟨S, hS, hfS⟩ := exists_isCompact_forall_mem hf hV hy
  refine ⟨S, hS, fun ξ hξ ↦ ?_⟩
  simpa only [f, A, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM,
    SchwartzMap.fourierTransformCLM_apply] using hfS ξ hξ

/-- Peetre's inequality turned into the bound on one term of the lattice series for the localized
Fourier transform of a pullback: if `1 + a ≤ (1 + y) (1 + r)`, `(1 + y)^N g ≤ K` and
`(1 + r)^(N + q) f ≤ s`, then `(1 + a)^N g f ≤ K s (1 + r)^(-q)`. -/
private theorem one_add_pow_mul_mul_le {a y r g f K s : ℝ} (N q : ℕ) (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hr : 0 ≤ r) (hg : 0 ≤ g) (hf : 0 ≤ f) (hpeetre : 1 + a ≤ (1 + y) * (1 + r))
    (hG : (1 + y) ^ N * g ≤ K) (hF : (1 + r) ^ (N + q) * f ≤ s) :
    (1 + a) ^ N * (g * f) ≤ K * s * ((1 + r) ^ q)⁻¹ := by
  calc (1 + a) ^ N * (g * f) ≤ ((1 + y) * (1 + r)) ^ N * (g * f) := by gcongr
    _ = ((1 + y) ^ N * g) * ((1 + r) ^ (N + q) * f) * ((1 + r) ^ q)⁻¹ := by
        rw [pow_add, mul_pow]
        field_simp
    _ ≤ K * s * ((1 + r) ^ q)⁻¹ := by
        gcongr
        exact (mul_nonneg (by positivity) hg).trans hG

/-! ### Cutoffs adapted to `Γ` near `E × {0}` -/

section Cutoff

variable {U : Opens E} {W : Opens (WithLp 2 (E × D))}
  {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))}

/-- **Cutoffs and seminorm cones adapted to `Γ`.** Let `Γ` be closed under positive dilations,
closed in `W × (E × D \ {0})` and free of zero covectors and of covectors over `E × {0}` conormal
to `E × {0}`. Suppose that `Γ` contains no covector over a point `(x, 0)`, `x ∈ K`, whose first
component lies in a closed cone `V` of `E`, for a compact `K ⊆ U`. Then there are a cutoff `χ`
equal to one on `K × closedBall 0 δ` for some `δ > 0` and a closed cone `V''` such that no
covector over the support of `χ` in a direction of `V''` lies in `Γ`, and `V''` contains a conic
neighbourhood of the covectors with first component in `V ∪ {0}`: for some `c > 0`, the first
component of every `ζ ∉ V''` is at distance at least `c (‖ξ‖ + ‖ζ‖)` from every `ξ ∈ V ∪ {0}`. -/
private theorem exists_cutoff_isClosed_cone
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ζ, (p, ζ) ∈ Γ → ∀ t : ℝ, 0 < t → (p, t • ζ) ∈ Γ) (hzero : ∀ p, (p, 0) ∉ Γ)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {V : Set E} (hV : IsClosed V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    (hKV : ∀ x ∈ K, ∀ ζ : WithLp 2 (E × D), ζ.fst ∈ V → ζ ≠ 0 → (toLp 2 (x, 0), ζ) ∉ Γ) :
    ∃ δ > 0, ∃ χ : 𝓓(W, ℂ), (∀ x ∈ K, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1) ∧
      ∃ V'' : Set (WithLp 2 (E × D)), IsClosed V'' ∧ (∀ t : ℝ, 0 < t → ∀ ζ ∈ V'', t • ζ ∈ V'') ∧
        Disjoint (tsupport χ ×ˢ V'') Γ ∧
        ∃ c > 0, ∀ ξ ∈ insert 0 V, ∀ ζ ∉ V'', c * (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖ := by
  have hι : Continuous fun x : E ↦ toLp 2 (x, (0 : D)) :=
    (prod_continuous_toLp 2 E D).comp (continuous_id.prodMk continuous_const)
  -- The closed cone `V₀ = V ∪ {0}`, which adds the conormal directions.
  set V₀ : Set E := insert 0 V
  have hV₀ : IsClosed V₀ := isClosed_singleton.union hV
  have hV₀cone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V₀, t • ξ ∈ V₀ := by
    rintro t ht ξ (rfl | hξ)
    · exact Or.inl (smul_zero t)
    · exact Or.inr (hVcone t ht ξ hξ)
  obtain ⟨G, hG, hKG, O, hO, hVO, hOcone, hGO⟩ := exists_isOpen_cone_forall_notMem hΓ hcone
    (hK.image hι) (image_subset_iff.2 fun x hx ↦ hU (hKU hx))
    (C := WithLp.fst ⁻¹' V₀) (hV₀.preimage (by fun_prop))
    (fun t ht ζ hζ ↦ by simpa using hV₀cone t ht _ hζ) (by
      rintro _ ⟨x, hx, rfl⟩ ζ (h0 | hζ) hζ0 hmem
      · have hζ' : ζ = toLp 2 ((0 : E), ζ.snd) := by
          rw [← h0, ← ofLp_fst, ← ofLp_snd, Prod.mk.eta, toLp_ofLp]
        exact hnormal x (hKU hx) ζ.snd (hζ' ▸ hmem)
      · exact hKV x hx ζ hζ hζ0 hmem)
  obtain ⟨δ, hδ, χ, hχ1, hχG⟩ := TestFunction.exists_eq_one_prod_closedBall_tsupport_subset hK hG
    fun x hx ↦ ⟨hKG ⟨x, hx, rfl⟩, hU (hKU hx)⟩
  obtain ⟨V'', hV''c, hV''cone, hV''O, c, hc, hsep⟩ :=
    exists_isClosed_cone_mul_add_le_norm_fst_sub hV₀ hV₀cone hO hOcone hVO
  refine ⟨δ, hδ, χ, hχ1, V'', hV''c, hV''cone, disjoint_left.2 fun ⟨p, ζ⟩ ⟨hp, hζ⟩ hpζ ↦ ?_, c,
    hc, hsep⟩
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · exact hzero p hpζ
  · exact hGO p (hχG hp) ζ (hV''O ζ hζ hζ0) hpζ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
/-- The separation of `exists_cutoff_isClosed_cone` at `ξ = 0`: off `V''`, first components are
bounded below. -/
private theorem forall_mul_norm_le_norm_fst {V : Set E} {V'' : Set (WithLp 2 (E × D))} {c : ℝ}
    (hsep : ∀ ξ ∈ insert 0 V, ∀ ζ ∉ V'', c * (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖) :
    ∀ ζ ∉ V'', c * ‖ζ‖ ≤ ‖ζ.fst‖ :=
  fun ζ hζ ↦ by simpa using hsep 0 (mem_insert _ _) ζ hζ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
/-- The separation of `exists_cutoff_isClosed_cone` for `-m ∉ V''`, read on `m`. -/
private theorem forall_mul_add_le_norm_fst_add {V : Set E} {V'' : Set (WithLp 2 (E × D))} {c : ℝ}
    (hsep : ∀ ξ ∈ insert 0 V, ∀ ζ ∉ V'', c * (‖ξ‖ + ‖ζ‖) ≤ ‖ζ.fst - ξ‖) :
    ∀ ξ ∈ V, ∀ m ∈ {ζ | -ζ ∉ V''}, c * (‖ξ‖ + ‖m‖) ≤ ‖m.fst + ξ‖ := fun ξ hξ m hm ↦ by
  have h := hsep ξ (mem_insert_of_mem _ hξ) (-m) hm
  rwa [norm_neg, WithLp.neg_fst, ← neg_add', norm_neg] at h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
/-- Off `-V''`, a covector is comparable to its first component, when the first components of the
covectors off `V''` are bounded below. -/
private theorem norm_le_inv_mul_norm_fst {V'' : Set (WithLp 2 (E × D))} {c : ℝ} (hc : 0 < c)
    (hsep : ∀ ζ ∉ V'', c * ‖ζ‖ ≤ ‖ζ.fst‖) {ζ : WithLp 2 (E × D)} (hζ : ζ ∈ {ζ | -ζ ∉ V''}) :
    ‖ζ‖ ≤ c⁻¹ * ‖ζ.fst‖ := by
  have h := hsep (-ζ) hζ
  rwa [norm_neg, WithLp.neg_fst, norm_neg, ← le_inv_mul_iff₀ hc] at h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
/-- A cone `V''` off which first components are bounded below contains the cone
`‖ζ.fst‖ < c ‖ζ.snd‖` around the conormal directions. -/
private theorem mem_of_norm_fst_lt {V'' : Set (WithLp 2 (E × D))} {c : ℝ}
    (hsep : ∀ ζ ∉ V'', c * ‖ζ‖ ≤ ‖ζ.fst‖) {ζ : WithLp 2 (E × D)}
    (hζ : ‖ζ.fst‖ < c * ‖ζ.snd‖) : ζ ∈ V'' := by
  by_contra hζV
  have hc : 0 < c := pos_of_mul_pos_left ((norm_nonneg _).trans_lt hζ) (norm_nonneg _)
  nlinarith [hsep ζ hζV, WithLp.norm_snd_le (x := ζ)]

end Cutoff

/-! ### The pullback split along a lattice -/

section Split

variable {U : Opens E} {W : Opens (WithLp 2 (E × D))}

/-- The cutoff `χ` as a smooth function supported in its own support. -/
private abbrev cutoffSupportedIn (χ : 𝓓(W, ℂ)) :
    𝓓_{⟨tsupport χ, χ.hasCompactSupport⟩}(WithLp 2 (E × D), ℂ) :=
  ContDiffMapSupportedIn.of_support_subset χ.contDiff (subset_tsupport _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- Pairing `T` with a modulated cutoff `χ.modulate m` is the localized Fourier transform of `T`
with cutoff `χ` at `-m`. -/
private theorem complexPairing_cutoffSupportedIn_modulate (T : 𝓓'(W, ℂ)) (χ : 𝓓(W, ℂ))
    (m : WithLp 2 (E × D)) :
    T.complexPairing (ofSupportedIn χ.tsupport_subset ((cutoffSupportedIn χ).modulate m)) =
      T.localFourier χ (-m) := by
  rw [Distribution.localFourier_eq_complexPairing_modulate T χ.tsupport_subset
    (f := cutoffSupportedIn χ) (fun x ↦ ContDiffMapSupportedIn.coe_of_support_subset _ _ x),
    neg_neg]

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]

/-- **The pullback split along a lattice.** In the lattice series for the pullback paired with
`ψ` (`Distribution.complexPairing_pullbackInl_eq_tsum`), the terms over a set `M` of covectors
with `‖ζ‖ ≤ R ‖ζ.fst‖`, where `𝓕 ψ (ζ.fst)` decays rapidly in `ζ`, sum to `T` paired with the
synthesis of `𝓕 ψ`. -/
private theorem complexPairing_pullbackInl_eq_add (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) {ψ : 𝓓(U, ℂ)} {χ : 𝓓(W, ℂ)}
    {δ : ℝ} (hδ : 0 < δ) (hχ : ∀ x ∈ tsupport ψ, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C)
    {M : Set (WithLp 2 (E × D))} {R : ℝ} (hM : ∀ ζ ∈ M, ‖ζ‖ ≤ R * ‖ζ.fst‖)
    (hMc : Summable fun m : ZLattice.dual L ↦ Mᶜ.indicator (fun ζ ↦ 𝓕 (ψ : E → ℂ) ζ.fst) m *
      T.localFourier χ (-m)) :
    (T.pullbackInl hU h).complexPairing ψ = (ZLattice.covolume L : ℂ)⁻¹ *
      (T.complexPairing (ofSupportedIn χ.tsupport_subset
        (synthesis (cutoffSupportedIn χ) L hM (𝓕 (toSchwartzMapCLM ℂ ψ)))) +
      ∑' m : ZLattice.dual L, Mᶜ.indicator (fun ζ ↦ 𝓕 (ψ : E → ℂ) ζ.fst) m *
        T.localFourier χ (-m)) := by
  set h₀ := 𝓕 (toSchwartzMapCLM ℂ ψ)
  have hh₀ : (h₀ : E → ℂ) = 𝓕 (ψ : E → ℂ) := by
    rw [SchwartzMap.fourier_coe, coe_toSchwartzMapCLM]
  -- The terms over `M` sum to `T` paired with the synthesis.
  have hsyn := ((summable_synthesisCoeff_smul_modulate (cutoffSupportedIn χ) L hM h₀).hasSum.mapL
    (T.complexPairing ∘L ofSupportedInCLM ℂ χ.tsupport_subset))
  simp only [ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM, map_smul, smul_eq_mul,
    complexPairing_cutoffSupportedIn_modulate] at hsyn
  rw [Distribution.complexPairing_pullbackInl_eq_tsum T hU h hδ hχ L hL hc hdecay]
  refine ((hsyn.add hMc.hasSum).mul_left _ |>.congr_fun fun m ↦ ?_).tsum_eq
  rw [synthesisCoeff, hh₀, ← add_mul, Set.indicator_self_add_compl_apply, mul_assoc]

end Split

/-! ### The target cone -/

/-- The image `{(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}` of the part of `Γ` over `E × {0}` under the
transpose `(ξ, η) ↦ ξ` of the inclusion `x ↦ (x, 0)`. The pullback to `E × {0}` sends the
distributions with wave front set in `Γ` to distributions with wave front set in this set
(`TauCeti.waveFrontSet_pullbackInl_subset_pullbackInlCone`). -/
def pullbackInlCone (Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))) : Set (E × E) :=
  {p | ∃ η : D, (toLp 2 (p.1, (0 : D)), toLp 2 (p.2, η)) ∈ Γ}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] in
@[simp]
theorem mem_pullbackInlCone {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))} {p : E × E} :
    p ∈ pullbackInlCone Γ ↔ ∃ η : D, (toLp 2 (p.1, (0 : D)), toLp 2 (p.2, η)) ∈ Γ :=
  Iff.rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] in
/-- `pullbackInlCone` is monotone. -/
theorem pullbackInlCone_mono {Γ Γ' : Set (WithLp 2 (E × D) × WithLp 2 (E × D))} (h : Γ ⊆ Γ') :
    pullbackInlCone Γ ⊆ pullbackInlCone Γ' :=
  fun _ ⟨η, hη⟩ ↦ ⟨η, h hη⟩

/-- The wave front set of the pullback of `T` to `E × {0}` lies in `pullbackInlCone Γ` whenever
that of `T` lies in `Γ`. -/
theorem waveFrontSet_pullbackInl_subset_pullbackInlCone {U : Opens E}
    {W : Opens (WithLp 2 (E × D))} {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))}
    (T : 𝓓'(W, ℂ)) (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (hT : T.waveFrontSet ⊆ Γ) :
    (T.pullbackInl hU h).waveFrontSet ⊆ pullbackInlCone Γ :=
  (Distribution.waveFrontSet_pullbackInl_subset T hU h).trans fun _ ⟨η, hη⟩ ↦ ⟨η, hT hη⟩

/-! ### Continuity into `𝓓'(U)` -/

section Continuity

variable {U : Opens E} {W : Opens (WithLp 2 (E × D))}
  {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))}

namespace WaveFrontSpace

/-- If `Γ` contains no covector over `E × {0}` conormal to `E × {0}`, every distribution with wave
front set in `Γ` satisfies the hypothesis of `Distribution.pullbackInl`. -/
theorem notMem_waveFrontSet_toDistribution
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) :
    ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ u.toDistribution.waveFrontSet :=
  fun x hx η _ hmem ↦ hnormal x hx η (u.waveFrontSet_toDistribution_subset hmem)

/-- The pullback `T ↦ ι^* T` to `E × {0}` on `𝓓'_Γ(W)`, as a linear map to `𝓓'(U)`. -/
private def pullbackInlₗ (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    WaveFrontSpace W Γ →ₗ[ℂ] 𝓓'(U, ℂ) where
  toFun u := u.toDistribution.pullbackInl hU (notMem_waveFrontSet_toDistribution hnormal u)
  map_add' u v := by
    simp only [map_add]
    exact Distribution.pullbackInl_add hU _ _
  map_smul' c u := by
    simp only [map_smul, RingHom.id_apply]
    exact Distribution.pullbackInl_smul hU c _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- The values `T g` for `g` in a compact set `S` of complex test functions are uniformly small
for `T` near `0` in `𝓓'(Ω)`: the real and imaginary parts of `S` are compact. -/
private theorem eventually_forall_norm_complexPairing_lt {Ω : Opens (WithLp 2 (E × D))}
    {S : Set 𝓓(Ω, ℂ)} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in 𝓝 (0 : 𝓓'(Ω, ℂ)), ∀ g ∈ S, ‖T.complexPairing g‖ < 2 * ε := by
  set S' : Set 𝓓(Ω, ℝ) :=
    postcompCLM (𝕜 := ℝ) reCLM '' S ∪ postcompCLM (𝕜 := ℝ) imCLM '' S
  have hS' : IsCompact S' :=
    (hS.image (postcompCLM (𝕜 := ℝ) reCLM).continuous).union
      (hS.image (postcompCLM (𝕜 := ℝ) imCLM).continuous)
  filter_upwards [CompactConvergenceCLM.hasBasis_nhds_zero.mem_of_mem
    (i := (S', ball (0 : ℂ) ε)) ⟨hS', ball_mem_nhds 0 hε⟩] with T hT g hg
  have hre := mem_ball_zero_iff.1 (hT _ (Or.inl ⟨g, hg, rfl⟩))
  have him := mem_ball_zero_iff.1 (hT _ (Or.inr ⟨g, hg, rfl⟩))
  rw [Distribution.complexPairing_apply]
  calc ‖T (postcompCLM (𝕜 := ℝ) reCLM g) + I * T (postcompCLM (𝕜 := ℝ) imCLM g)‖
      ≤ ‖T (postcompCLM (𝕜 := ℝ) reCLM g)‖ + ‖T (postcompCLM (𝕜 := ℝ) imCLM g)‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_mul, Complex.norm_I, one_mul]
    _ < 2 * ε := by linarith

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]

/-- **The pullback split along a lattice, for `T ∈ 𝓓'_Γ(W)`.** With a cutoff `χ` equal to one near
`tsupport ψ × {0}` and a closed cone `V''` free of `Γ` over the support of `χ`, off which first
components are bounded below, the pullback of `T` paired with `ψ` is `T` paired with the synthesis
of `𝓕 ψ` over `M = {ζ | -ζ ∉ V''}`, plus the lattice series over `-V''`. -/
private theorem complexPairing_pullbackInlₗ_eq_add
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    {δ : ℝ} (hδ : 0 < δ) {χ : 𝓓(W, ℂ)} {ψ : 𝓓(U, ℂ)}
    (hχ : ∀ x ∈ tsupport ψ, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    {V'' : Set (WithLp 2 (E × D))} (hV''c : IsClosed V'')
    (hV''cone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ V'', t • ζ ∈ V'') (hdisj : Disjoint (tsupport χ ×ˢ V'') Γ)
    {c : ℝ} (hc : 0 < c) (hsep : ∀ ζ ∉ V'', c * ‖ζ‖ ≤ ‖ζ.fst‖)
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0) (u : WaveFrontSpace W Γ)
    (hsum : Summable fun m : ZLattice.dual L ↦
      {ζ | -ζ ∉ V''}ᶜ.indicator (fun ζ ↦ 𝓕 (ψ : E → ℂ) ζ.fst) m *
        u.toDistribution.localFourier χ (-m)) :
    (pullbackInlₗ hU hnormal u).complexPairing ψ = (ZLattice.covolume L : ℂ)⁻¹ *
      (u.toDistribution.complexPairing (ofSupportedIn χ.tsupport_subset
        (synthesis (cutoffSupportedIn χ) L (fun _ hζ ↦ norm_le_inv_mul_norm_fst hc hsep hζ)
          (𝓕 (toSchwartzMapCLM ℂ ψ)))) +
      ∑' m : ZLattice.dual L, {ζ | -ζ ∉ V''}ᶜ.indicator (fun ζ ↦ 𝓕 (ψ : E → ℂ) ζ.fst) m *
        u.toDistribution.localFourier χ (-m)) := by
  -- `T` decays on the cone `‖ζ.fst‖ < c ‖ζ.snd‖ ⊆ V''`, by the seminorms with cone `V''`.
  let i : WaveFrontSeminormIndex W Γ := ⟨χ, V'', 0, hV''c, hV''cone, hdisj⟩
  refine complexPairing_pullbackInl_eq_add _ hU _ hδ hχ L hL hc
    (fun N ↦ ⟨WaveFrontSpace.seminorm (i.withOrder N) u, fun ζ hζ ↦ ?_⟩) _ hsum
  have h := le_seminorm (i.withOrder N) u (η := ζ)
    (by rw [WaveFrontSeminormIndex.withOrder_cone]; exact mem_of_norm_fst_lt hsep hζ)
  rwa [WaveFrontSeminormIndex.withOrder_order, WaveFrontSeminormIndex.withOrder_cutoff] at h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- **The terms of the lattice series over `-V`.** Let `F` be a translate `x ↦ H (x + ξ)` of a
Schwartz function. The term `F (m.fst) T (χ e_(-m))` of the lattice series over `m ∈ -V`, weighted
by `(1 + ‖ξ‖)^N`, is bounded by the seminorm `‖T‖_{χ,V,N+q}` times `(1 + ‖m‖)^(-q)`, by Peetre's
inequality `1 + ‖ξ‖ ≤ (1 + ‖m.fst + ξ‖) (1 + ‖m‖)`. -/
private theorem one_add_norm_pow_mul_norm_indicator_mul_localFourier_le (u : WaveFrontSpace W Γ)
    (i : WaveFrontSeminormIndex W Γ) {N q : ℕ} (hNq : i.order = N + q) {F : E → ℂ}
    {H : 𝓢(E, ℂ)} {ξ : E} (hF : ∀ x, F x = H (x + ξ)) (m : WithLp 2 (E × D)) :
    (1 + ‖ξ‖) ^ N * ‖{ζ | -ζ ∉ i.cone}ᶜ.indicator (fun ζ ↦ F ζ.fst) m *
      u.toDistribution.localFourier i.cutoff (-m)‖ ≤
      2 ^ N * decaySeminorm N H * WaveFrontSpace.seminorm i u * ((1 + ‖m‖) ^ q)⁻¹ := by
  by_cases hm : m ∈ {ζ | -ζ ∉ i.cone}ᶜ
  · have h1 := le_seminorm i u (η := -m) (not_not.1 hm)
    rw [norm_neg, hNq] at h1
    have hpeetre : 1 + ‖ξ‖ ≤ (1 + ‖m.fst + ξ‖) * (1 + ‖m‖) := by
      have h3 := norm_sub_le (m.fst + ξ) m.fst
      rw [add_sub_cancel_left] at h3
      nlinarith [WithLp.norm_fst_le (x := m), norm_nonneg (m.fst + ξ), norm_nonneg m]
    rw [indicator_of_mem hm, norm_mul, hF]
    exact one_add_pow_mul_mul_le N q (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) hpeetre (one_add_norm_pow_mul_norm_le H N _) h1
  · rw [indicator_of_notMem hm, zero_mul, norm_zero, mul_zero]
    positivity

/-- **The local estimate behind the continuity of the pullback.** Over a compact `K ⊆ U`, the
pullback of `T ∈ 𝓓'_Γ(W)` paired with a test function `ψ` supported in `K` is bounded by `T`
paired with `A ψ`, for a continuous linear map `A`, plus a multiple of a seminorm `‖T‖_{χ,V,N}`
of the normal topology times the sup norm of `𝓕 ψ`. -/
private theorem exists_norm_complexPairing_pullbackInlₗ_le
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ζ, (p, ζ) ∈ Γ → ∀ t : ℝ, 0 < t → (p, t • ζ) ∈ Γ) (hzero : ∀ p, (p, 0) ∉ Γ)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (A : 𝓓(U, ℂ) →L[ℂ] 𝓓(W, ℂ)) (i : WaveFrontSeminormIndex W Γ) (C : ℝ), 0 ≤ C ∧
      ∀ (u : WaveFrontSpace W Γ) (ψ : 𝓓(U, ℂ)), tsupport ψ ⊆ K →
        ‖(pullbackInlₗ hU hnormal u).complexPairing ψ‖ ≤
          C * ‖u.toDistribution.complexPairing (A ψ)‖ +
            C * decaySeminorm 0 (𝓕 (toSchwartzMapCLM ℂ ψ)) * WaveFrontSpace.seminorm i u := by
  -- A cutoff `χ` and a closed cone `V''` around the conormal directions free of `Γ`.
  obtain ⟨δ, hδ, χ, hχ1, V'', hV''c, hV''cone, hdisj, c, hc, hsep⟩ :=
    exists_cutoff_isClosed_cone hU hΓ hcone hzero hnormal hK hKU (V := ∅) isClosed_empty
      (by simp) (by simp)
  have hsep0 := forall_mul_norm_le_norm_fst hsep
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hsum := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  let i : WaveFrontSeminormIndex W Γ := ⟨χ, V'', q, hV''c, hV''cone, hdisj⟩
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  set S₀ := ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹
  refine ⟨ofSupportedInCLM ℂ χ.tsupport_subset ∘L
    synthesis (cutoffSupportedIn χ) L (fun _ hζ ↦ norm_le_inv_mul_norm_fst hc hsep0 hζ) ∘L
    SchwartzMap.fourierTransformCLM ℂ ∘L toSchwartzMapCLM ℂ, i, ‖a‖ * max 1 S₀, by positivity,
    fun u ψ hψ ↦ ?_⟩
  set T := u.toDistribution
  set B := decaySeminorm 0 (𝓕 (toSchwartzMapCLM ℂ ψ))
  -- The terms over `-V''` are controlled by the seminorm `‖T‖_{χ,V'',q}`.
  have hterm (m : ZLattice.dual L) :
      ‖{ζ | -ζ ∉ V''}ᶜ.indicator (fun ζ ↦ 𝓕 (ψ : E → ℂ) ζ.fst) m * T.localFourier χ (-m)‖ ≤
        B * WaveFrontSpace.seminorm i u * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
    have h := one_add_norm_pow_mul_norm_indicator_mul_localFourier_le u i (N := 0) (q := q)
      (zero_add q).symm (F := 𝓕 (ψ : E → ℂ)) (H := 𝓕 (toSchwartzMapCLM ℂ ψ)) (ξ := 0)
      (fun x ↦ by rw [add_zero, SchwartzMap.fourier_coe, coe_toSchwartzMapCLM]) m
    simpa only [norm_zero, add_zero, pow_zero, one_mul] using h
  have hMsum := (hsum.mul_left _).of_norm_bounded hterm
  rw [complexPairing_pullbackInlₗ_eq_add hU hnormal hδ (fun x hx ↦ hχ1 x (hψ hx)) hV''c hV''cone
    hdisj hc hsep0 L hL u hMsum, norm_mul]
  have htsum := (norm_tsum_le_tsum_norm hMsum.norm).trans
    (hMsum.norm.tsum_le_tsum hterm (hsum.mul_left _))
  rw [tsum_mul_left] at htsum
  have hB : 0 ≤ B * WaveFrontSpace.seminorm i u := by positivity
  calc ‖a‖ * ‖T.complexPairing _ + _‖
      ≤ ‖a‖ * (‖T.complexPairing _‖ + B * WaveFrontSpace.seminorm i u * S₀) := by
        gcongr
        exact (norm_add_le _ _).trans (by gcongr)
    _ ≤ ‖a‖ * (max 1 S₀ * ‖T.complexPairing _‖ +
          max 1 S₀ * (B * WaveFrontSpace.seminorm i u)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add
          (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)) ?_) (norm_nonneg a)
        rw [mul_comm (B * _)]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hB
    _ = _ := by
        simp only [ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM,
          SchwartzMap.fourierTransformCLM_apply]
        ring

/-- **Continuity of the pullback into `𝓓'(U)`.** -/
private theorem continuous_pullbackInlₗ
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ζ, (p, ζ) ∈ Γ → ∀ t : ℝ, 0 < t → (p, t • ζ) ∈ Γ) (hzero : ∀ p, (p, 0) ∉ Γ)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    Continuous (pullbackInlₗ hU hnormal) := by
  refine continuous_of_continuousAt_zero (pullbackInlₗ hU hnormal) ?_
  rw [ContinuousAt, map_zero]
  refine CompactConvergenceCLM.hasBasis_nhds_zero.tendsto_right_iff.2 fun ⟨S, N⟩ ⟨hS, hN⟩ ↦ ?_
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨K, hKU, hSK⟩ := TestFunction.exists_compacts_forall_tsupport_subset hS
  obtain ⟨A, i, C, hC, hest⟩ :=
    exists_norm_complexPairing_pullbackInlₗ_le hU hΓ hcone hzero hnormal K.isCompact hKU
  set ι : 𝓓(U, ℝ) →L[ℝ] 𝓓(U, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM
  -- A bound for the sup norms of the Fourier transforms over `S`.
  have hcont : Continuous fun ψ ↦ decaySeminorm 0 (𝓕 (toSchwartzMapCLM ℂ (ι ψ))) :=
    ((schwartz_withSeminorms ℂ E ℂ).continuous_finsetSup_seminorm _).comp
      ((SchwartzMap.fourierTransformCLM ℂ).continuous.comp
        ((toSchwartzMapCLM ℂ).continuous.comp ι.continuous))
  obtain ⟨B, hB⟩ := (hS.image hcont).isBounded.exists_norm_le
  set ε' := ε / (2 * C + C * |B| + 1)
  have hε' : 0 < ε' := by positivity
  have hAS : IsCompact ((fun ψ ↦ A (ι ψ)) '' S) :=
    hS.image ((A.continuous.comp ι.continuous))
  filter_upwards [(continuous_toDistribution.tendsto' 0 0 (map_zero _)).eventually
      (eventually_forall_norm_complexPairing_lt hAS hε'),
    ((continuous_seminorm i).tendsto' 0 0 (map_zero _)).eventually (gt_mem_nhds hε')]
    with u hu hu' ψ hψ
  refine hεN (mem_ball_zero_iff.2 ?_)
  have hψK : tsupport (ι ψ) ⊆ K := (tsupport_comp_subset (map_zero ofRealCLM) ψ).trans (hSK ψ hψ)
  have hBψ : decaySeminorm 0 (𝓕 (toSchwartzMapCLM ℂ (ι ψ))) ≤ |B| := by
    have h := hB _ ⟨ψ, hψ, rfl⟩
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_abs_self B))
  calc ‖pullbackInlₗ hU hnormal u ψ‖ = ‖(pullbackInlₗ hU hnormal u).complexPairing (ι ψ)‖ := by
        rw [Distribution.complexPairing_postcompCLM_ofRealCLM]
    _ ≤ C * ‖u.toDistribution.complexPairing (A (ι ψ))‖ +
          C * decaySeminorm 0 (𝓕 (toSchwartzMapCLM ℂ (ι ψ))) * WaveFrontSpace.seminorm i u :=
        hest u (ι ψ) hψK
    _ ≤ C * (2 * ε') + C * |B| * ε' := by
        gcongr
        exact (hu _ ⟨ψ, hψ, rfl⟩).le
    _ < ε := by
        have h1 : C * (2 * ε') + C * |B| * ε' =
            ε * ((2 * C + C * |B|) / (2 * C + C * |B| + 1)) := by
          simp only [ε']
          field_simp
        rw [h1]
        exact mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).2 (lt_add_one _))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace D] [BorelSpace D] in
/-- The last step of the seminorm estimate: `a w ‖X + Y‖ ≤ C B + C s` for `C = a max 1 (K S₀)`,
when `w ‖X‖ ≤ B` and `w ‖Y‖ ≤ K s S₀`. -/
private theorem mul_mul_norm_add_le {a w B s K S₀ : ℝ} {X Y : ℂ} (ha : 0 ≤ a) (hw : 0 ≤ w)
    (hB : 0 ≤ B) (hs : 0 ≤ s) (hX : w * ‖X‖ ≤ B) (hY : w * ‖Y‖ ≤ K * s * S₀) :
    a * (w * ‖X + Y‖) ≤ a * max 1 (K * S₀) * B + a * max 1 (K * S₀) * s := by
  calc a * (w * ‖X + Y‖) ≤ a * (B + K * s * S₀) := by
        gcongr
        exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hw).trans (by rw [mul_add]; linarith)
    _ ≤ a * (max 1 (K * S₀) * B + max 1 (K * S₀) * s) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (le_mul_of_one_le_left hB
          (le_max_left _ _)) ?_) ha
        rw [mul_right_comm]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hs
    _ = _ := by ring

/-- **The seminorm estimate behind the continuity of the pullback.** For every seminorm
`‖·‖_{φ,V,N}` of `𝓓'_{Γ'}(U)`, `Γ' = pullbackInlCone Γ`, there are a compact set `S` of test
functions on `W`, a seminorm `‖·‖_{χ,V'',N'}` of `𝓓'_Γ(W)` and a constant `C` such that
`‖ι^* T‖_{φ,V,N} ≤ C B + C ‖T‖_{χ,V'',N'}` whenever `|T g| ≤ B` for every `g ∈ S`. -/
private theorem exists_localFourier_pullbackInlₗ_le
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ζ, (p, ζ) ∈ Γ → ∀ t : ℝ, 0 < t → (p, t • ζ) ∈ Γ) (hzero : ∀ p, (p, 0) ∉ Γ)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (j : WaveFrontSeminormIndex U (pullbackInlCone Γ)) :
    ∃ (S : Set 𝓓(W, ℂ)) (i : WaveFrontSeminormIndex W Γ) (C : ℝ), IsCompact S ∧ 0 ≤ C ∧
      ∀ (u : WaveFrontSpace W Γ) (B : ℝ), (∀ g ∈ S, ‖u.toDistribution.complexPairing g‖ ≤ B) →
        ∀ ξ ∈ j.cone, (1 + ‖ξ‖) ^ j.order *
          ‖(pullbackInlₗ hU hnormal u).localFourier j.cutoff ξ‖ ≤
            C * B + C * WaveFrontSpace.seminorm i u := by
  set φ := j.cutoff
  set N := j.order
  -- A cutoff `χ` and a closed cone `V''` free of `Γ` containing the directions `(ξ, η)`, `ξ ∈ V`.
  obtain ⟨δ, hδ, χ, hχ1, V'', hV''c, hV''cone, hdisj, c, hc, hsep⟩ :=
    exists_cutoff_isClosed_cone hU hΓ hcone hzero hnormal φ.hasCompactSupport.isCompact
      φ.tsupport_subset j.isClosed_cone j.smul_mem_cone fun x hx ζ hζ _ hmem ↦
        disjoint_left.1 j.disjoint (mk_mem_prod hx hζ) ⟨ζ.snd, by
          rwa [← ofLp_fst, ← ofLp_snd, Prod.mk.eta, toLp_ofLp]⟩
  have hsep0 := forall_mul_norm_le_norm_fst hsep
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hsum := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  let i : WaveFrontSeminormIndex W Γ := ⟨χ, V'', N + q, hV''c, hV''cone, hdisj⟩
  obtain ⟨S, hS, hfS⟩ := exists_isCompact_forall_smul_synthesis_mem χ.tsupport_subset
    (cutoffSupportedIn χ) L (fun _ hζ ↦ norm_le_inv_mul_norm_fst hc hsep0 hζ) j.isClosed_cone hc
    (forall_mul_add_le_norm_fst_add hsep) φ N
  set H := 𝓕 (toSchwartzMapCLM ℂ φ)
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  set S₀ := ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹
  set Kφ := 2 ^ N * decaySeminorm N H
  refine ⟨S, i, ‖a‖ * max 1 (Kφ * S₀), hS, by positivity, fun u B hB ξ hξ ↦ ?_⟩
  set T := u.toDistribution
  set e := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom ξ) φ
  -- The terms over `-V''` are controlled by Peetre's inequality and `‖T‖_{χ,V'',N+q}`.
  have hterm (m : ZLattice.dual L) := one_add_norm_pow_mul_norm_indicator_mul_localFourier_le u i
    (N := N) (q := q) rfl (F := 𝓕 (e : E → ℂ)) (H := H) (ξ := ξ) (fun x ↦ by
      rw [TestFunction.fourier_bilinLeftCLM_fourierAtom, SchwartzMap.fourier_coe,
        coe_toSchwartzMapCLM]) m
  have hMc := (hsum.mul_left _).of_norm_bounded fun m ↦
    (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by simp))).trans (hterm m)
  -- The pullback paired with `φ e_ξ`, split along the lattice.
  rw [Distribution.localFourier_def, complexPairing_pullbackInlₗ_eq_add hU hnormal hδ
    (fun x hx y hy ↦ hχ1 x (tsupport_mul_subset_left (by
      simpa [e, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply'] using hx)) y hy)
    hV''c hV''cone hdisj hc hsep0 L hL u hMc, norm_mul, mul_left_comm]
  have hX := hB _ (hfS ξ hξ)
  rw [← Complex.coe_smul, map_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)] at hX
  have hsum' := (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hMc.norm)
    (by positivity)).trans ((tsum_mul_left.symm.le).trans
      ((hMc.norm.mul_left _).tsum_le_tsum hterm (hsum.mul_left _)))
  rw [tsum_mul_left] at hsum'
  exact mul_mul_norm_add_le (norm_nonneg a) (by positivity)
    ((norm_nonneg _).trans (hB _ (hfS ξ hξ))) (apply_nonneg _ _) hX hsum'

end WaveFrontSpace

end Continuity

/-! ### The pullback on `𝓓'_Γ(W)` -/

section CLM

variable {U : Opens E} {W : Opens (WithLp 2 (E × D))}
  {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))}

namespace WaveFrontSpace

/-- The pullback `T ↦ ι^* T` as a linear map `𝓓'_Γ(W) → 𝓓'_{Γ'}(U)`, `Γ' = pullbackInlCone Γ`,
before its continuity is proved. -/
private def pullbackInlₗ' (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    WaveFrontSpace W Γ →ₗ[ℂ] WaveFrontSpace U (pullbackInlCone Γ) where
  toFun u := mk (pullbackInlₗ hU hnormal u) (waveFrontSet_pullbackInl_subset_pullbackInlCone _ hU _
    u.waveFrontSet_toDistribution_subset)
  map_add' u v := ext <| by
    simp only [map_add, toDistribution_mk]
    exact congrArg₂ (· + ·) (toDistribution_mk _ _).symm (toDistribution_mk _ _).symm
  map_smul' c u := ext <| by
    simp only [map_smul, toDistribution_mk, RingHom.id_apply]
    exact congrArg (c • ·) (toDistribution_mk _ _).symm

private theorem toDistribution_pullbackInlₗ'
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) :
    (pullbackInlₗ' hU hnormal u).toDistribution = pullbackInlₗ hU hnormal u :=
  toDistribution_mk _ _

/-- **The seminorms of a pullback** (Brouder–Dang–Hélein). For every seminorm `‖·‖_{φ,V,N}` of
`𝓓'_{Γ'}(U)`, `Γ' = pullbackInlCone Γ`, there are a compact set `S` of test functions on `W`, a
seminorm `‖·‖_{χ,V'',N'}` of `𝓓'_Γ(W)` and `C ≥ 0` such that
`‖ι^* T‖_{φ,V,N} ≤ C B + C ‖T‖_{χ,V'',N'}` whenever `|T g| ≤ B` for all `g ∈ S`. -/
private theorem exists_seminorm_pullbackInlₗ'_le
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ζ, (p, ζ) ∈ Γ → ∀ t : ℝ, 0 < t → (p, t • ζ) ∈ Γ) (hzero : ∀ p, (p, 0) ∉ Γ)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (j : WaveFrontSeminormIndex U (pullbackInlCone Γ)) :
    ∃ (S : Set 𝓓(W, ℂ)) (i : WaveFrontSeminormIndex W Γ) (C : ℝ), IsCompact S ∧ 0 ≤ C ∧
      ∀ (u : WaveFrontSpace W Γ) (B : ℝ), 0 ≤ B →
        (∀ g ∈ S, ‖u.toDistribution.complexPairing g‖ ≤ B) →
        WaveFrontSpace.seminorm j (pullbackInlₗ' hU hnormal u) ≤
          C * B + C * WaveFrontSpace.seminorm i u := by
  borelize E D
  obtain ⟨S, i, C, hS, hC, h⟩ := exists_localFourier_pullbackInlₗ_le hU hΓ hcone hzero hnormal j
  refine ⟨S, i, C, hS, hC, fun u B hB0 hB ↦ ?_⟩
  refine seminorm_le_bound j _ (by positivity) fun ξ hξ ↦ ?_
  rw [toDistribution_pullbackInlₗ']
  exact h u B hB ξ hξ

private theorem continuous_pullbackInlₗ'
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ζ, (p, ζ) ∈ Γ → ∀ t : ℝ, 0 < t → (p, t • ζ) ∈ Γ) (hzero : ∀ p, (p, 0) ∉ Γ)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    Continuous (pullbackInlₗ' hU hnormal) := by
  borelize E D
  refine continuous_of_continuousAt_zero (pullbackInlₗ' hU hnormal) ?_
  rw [ContinuousAt, map_zero]
  refine tendsto_nhds_of_eventually_seminorm_le ?_ fun j ↦ ?_
  · have h := (continuous_pullbackInlₗ hU hΓ hcone hzero hnormal).tendsto 0
    simpa only [toDistribution_pullbackInlₗ', map_zero] using h
  · obtain ⟨S, i, C, hS, hC, hle⟩ := exists_seminorm_pullbackInlₗ'_le hU hΓ hcone hzero hnormal j
    refine ⟨C * 2 + C * 1, ?_⟩
    filter_upwards [(continuous_toDistribution.tendsto' 0 0 (map_zero _)).eventually
        (eventually_forall_norm_complexPairing_lt hS one_pos),
      ((continuous_seminorm i).tendsto' 0 0 (map_zero _)).eventually (gt_mem_nhds one_pos)]
      with u hu hu'
    refine (hle u 2 zero_le_two fun g hg ↦ by simpa using (hu g hg).le).trans ?_
    gcongr

/-- **Continuity of the pullback to `E × {0}` in the normal topology** (Brouder–Dang–Hélein).
Let `Γ` be a set of covectors on `W ⊆ E × D` which is closed under positive dilations, contains no
zero covector and is closed in `W × (E × D \ {0})`, and suppose that no covector of `Γ` over a
point `(x, 0)`, `x ∈ U`, is conormal to `E × {0}`. Then every distribution in `𝓓'_Γ(W)` has a
pullback to `E × {0}` (`Distribution.pullbackInl`), and the pullback is a continuous linear map

`ι^* : 𝓓'_Γ(W) →L[ℂ] 𝓓'_{Γ'}(U)`, `Γ' = pullbackInlCone Γ = {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}`,

for the normal topologies of Hörmander's spaces. -/
def pullbackInlCLM (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ζ, (p, ζ) ∈ Γ → ∀ t : ℝ, 0 < t → (p, t • ζ) ∈ Γ) (hzero : ∀ p, (p, 0) ∉ Γ)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    WaveFrontSpace W Γ →L[ℂ] WaveFrontSpace U (pullbackInlCone Γ) :=
  ⟨pullbackInlₗ' hU hnormal, continuous_pullbackInlₗ' hU hΓ hcone hzero hnormal⟩

@[simp]
theorem toDistribution_pullbackInlCLM (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ζ, (p, ζ) ∈ Γ → ∀ t : ℝ, 0 < t → (p, t • ζ) ∈ Γ) (hzero : ∀ p, (p, 0) ∉ Γ)
    (hnormal : ∀ x ∈ U, ∀ η : D, (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) :
    (pullbackInlCLM hU hΓ hcone hzero hnormal u).toDistribution =
      u.toDistribution.pullbackInl hU (notMem_waveFrontSet_toDistribution hnormal u) :=
  toDistribution_pullbackInlₗ' hU hnormal u

end WaveFrontSpace

end CLM

end TauCeti
