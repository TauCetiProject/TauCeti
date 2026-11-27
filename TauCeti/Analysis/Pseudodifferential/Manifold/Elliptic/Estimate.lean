/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Besov
public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LocalizedChangeOfVariables
import TauCeti.Analysis.Pseudodifferential.Lp.BesselPotentialSpace
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables

/-!
# The elliptic estimate on a compact manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on
`ℝⁿ` (`TauCeti.classicalPseudodifferentialOperators`) which is elliptic
(`TauCeti.IsClassicalElliptic`). Let `ψᵢ` be finitely many cutoffs in charts `e'ᵢ` whose readings
`Ψᵢ = ψᵢ ∘ e'ᵢ` on `M` add up to `1`; this forces `M` to be compact
(`TauCeti.compactSpace_of_forall_sum_cutoffPullback_eq_one`). For `1 < p < ∞` the norm
`∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{s,p}}` of a smooth function `u` defines the Bessel-potential space
`H^{s,p}(M)` up to equivalence of norms, and `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}` the Besov space
`B^s_{p,∞}(M)`, for `1 ≤ p ≤ ∞`; at `p = ∞` it is the Hölder–Zygmund space `𝒞^s(M)`. This file
proves the **elliptic estimate** in these norms: for all real `s` and `r` there is a constant `C`
such that every smooth `u` on `M` satisfies

`‖u‖_{s + m} ≤ C (‖P u‖_s + ‖u‖_r)`

(`TauCeti.IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_le_add` and
`TauCeti.IsClassicalElliptic.exists_sum_norm_toBesovSpaceCLM_le_add`, where the left side may be
read through any finite family of charts and cutoffs). It is meaningful for `r < s + m`. The
lower-order term cannot be dropped: on the circle, the Laplacian kills the constant function `1`,
whose norms are positive.

The estimate follows from a parametrix. For every `N : ℕ` there is an operator `Q` of order `-m`
such that `R = Q ∘ P - 1` has order `-N`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`), so
`u = Q (P u) - R u`. The mapping estimates on `M` bound `Q (P u)` in order `s + m` by `P u` in
order `s`, and `R u` in order `r + N` by `u` in order `r`. For `N ≥ s + m - r` the space of order
`r + N` embeds continuously into the space of order `s + m`. As for the mapping estimates
(`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum`), the argument is carried out
once for abstract norms `‖Ls ·‖`, `‖Lr ·‖` and `‖Lt ·‖` on `𝓢(ℝⁿ, ℂ)` of the orders `s`, `r` and
`s + m`, given the Euclidean estimates for symbols of orders `-m` and `-N` with compact spatial
support (`TauCeti.IsClassicalElliptic.exists_sum_norm_cutoffPushforwardSchwartz_le_add`).

The estimate is the a priori half of the regularity theory of an elliptic operator on a compact
manifold. Finiteness of its smooth kernel is proved separately, from Rellich's theorem
(`TauCeti.IsClassicalElliptic.finiteDimensional_ker`).

## Main results

* `TauCeti.IsClassicalElliptic.exists_sum_norm_cutoffPushforwardSchwartz_le_add`: the elliptic
  estimate for abstract norms on the chart readings.
* `TauCeti.IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_le_add`: the elliptic
  estimate `‖u‖_{H^{s + m,p}} ≤ C (‖P u‖_{H^{s,p}} + ‖u‖_{H^{r,p}})`, `1 < p < ∞`.
* `TauCeti.IsClassicalElliptic.exists_sum_norm_toBesovSpaceCLM_le_add`: the elliptic estimate
  `‖u‖_{B^{s + m}_{p,∞}} ≤ C (‖P u‖_{B^s_{p,∞}} + ‖u‖_{B^r_{p,∞}})`, `1 ≤ p ≤ ∞`, which at `p = ∞`
  is the Hölder–Zygmund estimate.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.6)–(4.11) (elliptic estimates from a parametrix), (3.32)–(3.34) (Zygmund spaces), and
  Lecture II, (3.1)–(3.8) (the `H^{s,p}` estimates).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.2.
-/

public section

open Filter Set OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap Topology BesselPotentialSpace ENNReal

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **The elliptic estimate on a compact manifold, for abstract norms.** Let `Ls`, `Lr` and `Lt`
be linear maps out of `𝓢(ℝⁿ, ℂ)` into normed spaces, with `Ls` and `Lr` injective and every
localized change of variables bounded in `‖Ls ·‖` and in `‖Lr ·‖`. Suppose that for every symbol
`a` with compact spatial support, `‖Lt (Op(a) w)‖ ≤ A ‖Ls w‖` when `a` has order `-m`, and
`‖Lt (Op(a) w)‖ ≤ A ‖Lr w‖` when `a` has order `-N`. Let `P` be an elliptic classical
pseudodifferential operator of order `m`, and `ψᵢ` finitely many cutoffs in charts `e'ᵢ` whose
readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`. For finitely many cutoffs `φⱼ`
in charts `eⱼ` there is a constant `C` such that every smooth `u` on `M` satisfies

`∑ⱼ ‖Lt (φⱼ · (u ∘ eⱼ⁻¹))‖ ≤
  C (∑ᵢ ‖Ls (ψᵢ · ((P u) ∘ e'ᵢ⁻¹))‖ + ∑ᵢ ‖Lr (ψᵢ · (u ∘ e'ᵢ⁻¹))‖)`. -/
theorem IsClassicalElliptic.exists_sum_norm_cutoffPushforwardSchwartz_le_add
    {Xs Xr Y Gs Gr Gt : Type*} [NormedAddCommGroup Xs] [NormedSpace ℂ Xs]
    [NormedAddCommGroup Xr] [NormedSpace ℂ Xr] [SeminormedAddCommGroup Y] [NormedSpace ℂ Y]
    [FunLike Gs 𝓢(CoordinateSpace n, ℂ) Xs] [LinearMapClass Gs ℂ 𝓢(CoordinateSpace n, ℂ) Xs]
    [FunLike Gr 𝓢(CoordinateSpace n, ℂ) Xr] [LinearMapClass Gr ℂ 𝓢(CoordinateSpace n, ℂ) Xr]
    [FunLike Gt 𝓢(CoordinateSpace n, ℂ) Y] [LinearMapClass Gt ℂ 𝓢(CoordinateSpace n, ℂ) Y]
    (hPe : IsClassicalElliptic m P) {Ls : Gs} (hLs : Function.Injective Ls)
    (hcovs : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖Ls v‖ ≤ C * ‖Ls u‖)
    {Lr : Gr} (hLr : Function.Injective Lr)
    (hcovr : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖Lr v‖ ≤ C * ‖Lr u‖)
    (Lt : Gt) (hq : ∀ a : Symbol n ℂ ℂ (-m), ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Ls w‖)
    (N : ℕ) (hqN : ∀ a : Symbol n ℂ ℂ (-N), ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Lr w‖)
    {κ : Type*} [Fintype κ] {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ j, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j) u)‖ ≤
        C * (∑ i, ‖Ls ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) (P u))‖ +
          ∑ i, ‖Lr ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖) := by
  have := compactSpace_of_forall_sum_cutoffPullback_eq_one he' ψ hψ
  -- A parametrix `Q` of order `-m` with `R = Q P - 1` of order `-N`.
  obtain ⟨Q, hQ, -, hR⟩ := hPe.exists_comp_sub_id_mem_classicalPseudodifferentialOperators N
  set R : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ := Q ∘ₗ P - LinearMap.id with hRdef
  obtain ⟨A, hA⟩ :=
    exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum hQ hLs hcovs Lt hq he φ he' ψ hψ
  obtain ⟨B, hB⟩ :=
    exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum hR hLr hcovr Lt hqN he φ he' ψ hψ
  refine ⟨|A| + |B|, fun u ↦ ?_⟩
  set X := ∑ i, ‖Ls ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) (P u))‖
  set Y := ∑ i, ‖Lr ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  -- Each reading of `u = Q (P u) - R u` is split accordingly.
  have hsplit : u = Q (P u) - R u := by simp [hRdef]
  calc ∑ j, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j) u)‖
      ≤ ∑ j, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j) (Q (P u)))‖ +
          ∑ j, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j) (R u))‖ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ ↦ ?_
        conv_lhs => rw [hsplit, map_sub, map_sub]
        exact norm_sub_le _ _
    _ ≤ A * X + B * Y := add_le_add (hA (P u)) (hB u)
    _ ≤ |A| * X + |B| * Y := by gcongr <;> exact le_abs_self _
    _ ≤ (|A| + |B|) * (X + Y) := by
        have := mul_nonneg (abs_nonneg A) hY
        have := mul_nonneg (abs_nonneg B) hX
        nlinarith

/-- **The elliptic estimate on a compact manifold, in `H^{s,p}`.** Let `P` be an elliptic classical
pseudodifferential operator of order `m`, and `ψᵢ` finitely many cutoffs in charts `e'ᵢ` whose
readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`. For finitely many cutoffs `φⱼ` in
charts `eⱼ`, `1 < p < ∞` and all real `s` and `r` there is a constant `C` such that every smooth
`u` on `M` satisfies

`∑ⱼ ‖φⱼ · (u ∘ eⱼ⁻¹)‖_{H^{s + m,p}} ≤
  C (∑ᵢ ‖ψᵢ · ((P u) ∘ e'ᵢ⁻¹)‖_{H^{s,p}} + ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{r,p}})`. -/
theorem IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_le_add
    (hPe : IsClassicalElliptic m P)
    {κ : Type*} [Fintype κ] {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) (s r : ℝ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ j, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) p
          ((e j).cutoffPushforwardSchwartz (he j) (φ j) u)‖ ≤
        C * (∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s p
            ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) (P u))‖ +
          ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r p
            ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖) := by
  -- `R = Q P - 1` is taken of order `-N` with `s + m ≤ r + N`.
  have hN : s + m ≤ r - -(⌈s + m - r⌉₊ : ℝ) := by
    linarith [Nat.le_ceil (s + m - r)]
  refine hPe.exists_sum_norm_cutoffPushforwardSchwartz_le_add
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s p)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs hp hp_top s)
    (SchwartzMap.toBesselPotentialSpaceCLM_injective r p)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs hp hp_top r)
    _ (fun a ha ↦ ?_) ⌈s + m - r⌉₊ (fun a ha ↦ ?_) he φ he' ψ hψ
  · obtain ⟨C, hC⟩ :=
      ha.isUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
    rw [sub_neg_eq_add] at hC
    exact ⟨C, hC⟩
  · -- `Op(a)` maps `H^{r,p}` to `H^{r + N,p}`, which embeds into `H^{s + m,p}`.
    obtain ⟨C, hC⟩ :=
      ha.isUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le r hp hp_top
    refine ⟨‖BesselPotentialSpace.inclusion (E := CoordinateSpace n) (G := ℂ) (p := p) hN‖ * C,
      fun w ↦ ?_⟩
    rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hN, mul_assoc]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (hC w) (norm_nonneg _))

/-- **The elliptic estimate on a compact manifold, in Besov and Hölder–Zygmund norms.** Let `P`
be an elliptic classical pseudodifferential operator of order `m`, and `ψᵢ` finitely many cutoffs
in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`. For finitely
many cutoffs `φⱼ` in charts `eⱼ`, `1 ≤ p ≤ ∞` and all real `s` and `r` there is a constant `C` such
that every smooth `u` on `M` satisfies

`∑ⱼ ‖φⱼ · (u ∘ eⱼ⁻¹)‖_{B^{s + m}_{p,∞}} ≤
  C (∑ᵢ ‖ψᵢ · ((P u) ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}} + ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{B^r_{p,∞}})`.

For `p = ∞` these are the Hölder–Zygmund norms `𝒞^s = B^s_{∞,∞}`. -/
theorem IsClassicalElliptic.exists_sum_norm_toBesovSpaceCLM_le_add
    (hPe : IsClassicalElliptic m P)
    {κ : Type*} [Fintype κ] {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (b : ContDiffBump (0 : CoordinateSpace n)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (s r : ℝ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ j, ‖SchwartzMap.toBesovSpaceCLM ℂ b (s + m) p ∞
          ((e j).cutoffPushforwardSchwartz (he j) (φ j) u)‖ ≤
        C * (∑ i, ‖SchwartzMap.toBesovSpaceCLM ℂ b s p ∞
            ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) (P u))‖ +
          ∑ i, ‖SchwartzMap.toBesovSpaceCLM ℂ b r p ∞
            ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖) := by
  -- `R = Q P - 1` is taken of order `-N` with `s + m ≤ r + N`.
  have hN : s + m ≤ r - -(⌈s + m - r⌉₊ : ℝ) := by
    linarith [Nat.le_ceil (s + m - r)]
  refine hPe.exists_sum_norm_cutoffPushforwardSchwartz_le_add
    (SchwartzMap.toBesovSpaceCLM_injective ℂ b s p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs b s p ∞)
    (SchwartzMap.toBesovSpaceCLM_injective ℂ b r p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs b r p ∞)
    _ (fun a ha ↦ ?_) ⌈s + m - r⌉₊ (fun a ha ↦ ?_) he φ he' ψ hψ
  · obtain ⟨C, -, hC⟩ := ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le b s
    refine ⟨C, fun w ↦ ?_⟩
    have := hC (p := p) w
    rwa [sub_neg_eq_add] at this
  · -- `Op(a)` maps `B^r_{p,∞}` to `B^{r + N}_{p,∞}`, which embeds into `B^{s + m}_{p,∞}`.
    obtain ⟨C, -, hC⟩ := ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le b r
    refine ⟨‖BesovSpace.inclusion ℂ b p (q := ∞) (q' := ∞) hN le_rfl‖ * C, fun w ↦ ?_⟩
    rw [← SchwartzMap.inclusion_toBesovSpaceCLM hN le_rfl, mul_assoc]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (hC w) (norm_nonneg _))

end TauCeti
