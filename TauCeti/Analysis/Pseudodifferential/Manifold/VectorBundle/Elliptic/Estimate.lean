/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Besov
public import TauCeti.Analysis.Pseudodifferential.Lp.BesselPotentialSpace
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.ChartPatching
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LocalizedChangeOfVariables
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables

/-!
# The elliptic estimate between vector bundles on a compact manifold

Let `M` be a manifold modelled on `ℝⁿ`, let `E`, `F` be smooth complex vector bundles over `M`
with finite-dimensional model fibres `V` and `W`, and let `P : Γ(E) → Γ(F)` be a linear map
between their smooth sections. A smooth section `u` of `E` is read through finitely many cutoffs
`ψᵢ` in charts `e'ᵢ`, whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to `1`, trivializations `tᵢ` of `E`
and a basis `(b_k)` of `V`: its readings are the Schwartz functions
`ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)` on `ℝⁿ`, where `ρᵢ b_k*(tᵢ u)` is the cut-off frame coefficient
(`Bundle.Trivialization.cutoffFrameCoeff`). For `1 < p < ∞` the norm
`∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{H^{s,p}}` defines the Bessel-potential space
`H^{s,p}(M; E)` up to equivalence, and the same sum of `B^s_{p,∞}` norms the Besov space
`B^s_{p,∞}(M; E)`, for `1 ≤ p ≤ ∞`; at `p = ∞` it is the Hölder–Zygmund space `𝒞^s(M; E)`.

Suppose that `P` has a **left parametrix** of order `-m` modulo order `-N`: a classical
pseudodifferential operator `Q : Γ(F) → Γ(E)` of order `-m`
(`TauCeti.sectionClassicalPseudodifferentialOperators`) such that `Q ∘ P - 1` has order `-N`. This
file proves the **elliptic estimate** for `P` in these norms: for real `s` and `r` with
`s + m ≤ r + N` there is a constant `C` such that every smooth section `u` of `E` satisfies

`‖u‖_{s + m} ≤ C (‖P u‖_s + ‖u‖_r)`

(`exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add`
and `exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add`, in the
namespace `TauCeti`, where the left side may be read through any finite family of charts,
trivializations and functionals). Elliptic classical pseudodifferential operators of order `m`
between bundles over a compact manifold have such parametrices for every `N` (Hörmander, §18.1),
and for them the estimate holds for all real `s` and `r`. Only the existence of `Q` is used, so the
estimate also applies to operators which are invertible modulo lower order only on the left. The
lower-order term cannot be dropped: on the circle, the Laplacian kills the constant function `1`,
whose norms are positive.

The proof is the parametrix argument, `u = Q (P u) - R u` with `R = Q ∘ P - 1`. The mapping
estimates between bundles bound `Q (P u)` in order `s + m` by `P u` in order `s`, and `R u` in
order `r + N` by `u` in order `r`; the space of order `r + N` embeds continuously into the space of
order `s + m`. As for the mapping estimates
(`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`), the argument is
carried out once for abstract norms `‖Ls ·‖`, `‖Lr ·‖` and `‖Lt ·‖` on `𝓢(ℝⁿ, ℂ)`
(`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add`). This is the bundle
form of the scalar elliptic estimate
`TauCeti.IsClassicalElliptic.exists_sum_norm_cutoffPushforwardSchwartz_le_add`.

## Main results

* `TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add`: the elliptic
  estimate for abstract norms on the readings of frame coefficients.
* `exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add`:
  the elliptic estimate `‖u‖_{H^{s + m,p}} ≤ C (‖P u‖_{H^{s,p}} + ‖u‖_{H^{r,p}})`, `1 < p < ∞`.
* `TauCeti.exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add`: the
  elliptic estimate `‖u‖_{B^{s + m}_{p,∞}} ≤ C (‖P u‖_{B^s_{p,∞}} + ‖u‖_{B^r_{p,∞}})`,
  `1 ≤ p ≤ ∞`, which at `p = ∞` is the Hölder–Zygmund estimate.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.6)–(4.11) (elliptic estimates from a parametrix), (3.32)–(3.34) (Zygmund spaces) and §8
  (operators between bundles), and Lecture II, (3.1)–(3.8) (the `H^{s,p}` estimates).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 and §19.2.
-/

public section

noncomputable section

open Bundle Set TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace ENNReal

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
  {Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
  {m N : ℝ}

/-- **The elliptic estimate between bundles, for abstract norms.** Let `Ls`, `Lr` and `Lt` be
linear maps out of `𝓢(ℝⁿ, ℂ)` into normed spaces, with `Ls` and `Lr` injective and every localized
change of variables bounded in `‖Ls ·‖` and in `‖Lr ·‖`. Suppose that for every symbol `a` with
compact spatial support, `‖Lt (Op(a) w)‖ ≤ A ‖Ls w‖` when `a` has order `-m`, and
`‖Lt (Op(a) w)‖ ≤ A ‖Lr w‖` when `a` has order `-N`. Let `P : Γ(E) → Γ(F)` be linear with a left
parametrix `Q : Γ(F) → Γ(E)`, a classical pseudodifferential operator of order `-m` such that
`Q ∘ P - 1` has order `-N`.

Read `P u` through cutoffs `ψᵢ` in charts `e'ᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to `1`,
trivializations `tᵢ` of `F` with smooth functions `ρᵢ` supported in their base sets and equal to
`1` on `e'ᵢ⁻¹(supp ψᵢ)`, and a basis `(c_k)` of `W`; read `u` through a second such family `ψ'ᵢ`,
`e''ᵢ`, `t''ᵢ`, `ρ'ᵢ` for `E`, with a basis `(b_k)` of `V`. For finitely many cutoffs `φⱼ` in
charts `eⱼ`, trivializations `t'ⱼ` of `E` with cutoffs `χⱼ` and finitely many functionals `ℓₗ` on
`V`, there is a constant `C` such that every smooth section `u` of `E` satisfies

`∑ⱼ ∑ₗ ‖Lt (φⱼ · (χⱼ ℓₗ(t'ⱼ u) ∘ eⱼ⁻¹))‖ ≤`
`  C (∑ᵢ ∑ₖ ‖Ls (ψᵢ · (ρᵢ c_k*(tᵢ (P u)) ∘ e'ᵢ⁻¹))‖ +`
`    ∑ᵢ ∑ₖ ‖Lr (ψ'ᵢ · (ρ'ᵢ b_k*(t''ᵢ u) ∘ e''ᵢ⁻¹))‖)`. -/
theorem exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add
    {Xs Xr Y Gs Gr Gt : Type*} [NormedAddCommGroup Xs] [NormedSpace ℂ Xs]
    [NormedAddCommGroup Xr] [NormedSpace ℂ Xr] [SeminormedAddCommGroup Y] [NormedSpace ℂ Y]
    [FunLike Gs 𝓢(CoordinateSpace n, ℂ) Xs] [LinearMapClass Gs ℂ 𝓢(CoordinateSpace n, ℂ) Xs]
    [FunLike Gr 𝓢(CoordinateSpace n, ℂ) Xr] [LinearMapClass Gr ℂ 𝓢(CoordinateSpace n, ℂ) Xr]
    [FunLike Gt 𝓢(CoordinateSpace n, ℂ) Y] [LinearMapClass Gt ℂ 𝓢(CoordinateSpace n, ℂ) Y]
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators (-m))
    (hQP : Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N))
    {Ls : Gs} (hLs : Function.Injective Ls)
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
    (hqN : ∀ a : Symbol n ℂ ℂ (-N), ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Lr w‖)
    {ν : Type*} [Fintype ν] {e : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) (t' : ν → Trivialization V (π V E))
    [∀ j, MemTrivializationAtlas (t' j)] (χ : ν → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : ∀ j, tsupport (χ j) ⊆ (t' j).baseSet) {μ : Type*} [Fintype μ] (ℓ : μ → V →L[ℂ] ℂ)
    {κ : Type*} [Fintype κ] {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (t : κ → Trivialization W (π W F)) [∀ i, MemTrivializationAtlas (t i)]
    (ρ : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1)
    {ι : Type*} [Fintype ι] (c : Module.Basis ι ℂ W)
    {κ' : Type*} [Fintype κ'] {e'' : κ' → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he'' : ∀ i, e'' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ' : ∀ i, 𝓓(⟨(e'' i).target, (e'' i).open_target⟩, ℝ))
    (hψ' : ∀ x, ∑ i, (e'' i).cutoffPullback (he'' i) (ψ' i) 1 x = 1)
    (t'' : κ' → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t'' i)]
    (ρ' : κ' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hρ' : ∀ i, tsupport (ρ' i) ⊆ (t'' i).baseSet)
    (hρψ' : ∀ i, ∀ y ∈ tsupport (ψ' i), ρ' i ((e'' i).symm y) = 1)
    {ι' : Type*} [Fintype ι'] (b : Module.Basis ι' ℂ V) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ∑ j, ∑ l, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j)
          ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) u))‖ ≤
        C * (∑ i, ∑ k, ‖Ls ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
            ((t i).cutoffFrameCoeff (ρ i) (hρ i) (c.coord k).toContinuousLinearMap (P u)))‖ +
          ∑ i, ∑ k, ‖Lr ((e'' i).cutoffPushforwardSchwartz (he'' i) (ψ' i)
            ((t'' i).cutoffFrameCoeff (ρ' i) (hρ' i) (b.coord k).toContinuousLinearMap u))‖) := by
  set R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ :=
    Q ∘ₗ P - LinearMap.id with hRdef
  -- The mapping estimates for `Q`, from order `s` to order `s + m`, and for `R`.
  obtain ⟨A, hA⟩ := exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hQ hLs
    hcovs Lt hq he φ t' χ hχ ℓ he' ψ hψ t ρ hρ hρψ c
  obtain ⟨B, hB⟩ := exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hQP hLr
    hcovr Lt hqN he φ t' χ hχ ℓ he'' ψ' hψ' t'' ρ' hρ' hρψ' b
  refine ⟨|A| + |B|, fun u ↦ ?_⟩
  set X := ∑ i, ∑ k, ‖Ls ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
    ((t i).cutoffFrameCoeff (ρ i) (hρ i) (c.coord k).toContinuousLinearMap (P u)))‖
  set Y := ∑ i, ∑ k, ‖Lr ((e'' i).cutoffPushforwardSchwartz (he'' i) (ψ' i)
    ((t'' i).cutoffFrameCoeff (ρ' i) (hρ' i) (b.coord k).toContinuousLinearMap u))‖
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  -- Each reading of `u = Q (P u) - R u` is split accordingly.
  have hsplit : u = Q (P u) - R u := by simp [hRdef]
  calc ∑ j, ∑ l, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j)
          ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) u))‖
      ≤ ∑ j, ∑ l, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j)
            ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) (Q (P u))))‖ +
          ∑ j, ∑ l, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j)
            ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) (R u)))‖ := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun l _ ↦ ?_
        conv_lhs => rw [hsplit, map_sub, map_sub, map_sub]
        exact norm_sub_le _ _
    _ ≤ A * X + B * Y := add_le_add (hA (P u)) (hB u)
    _ ≤ |A| * X + |B| * Y := by gcongr <;> exact le_abs_self _
    _ ≤ (|A| + |B|) * (X + Y) := by
        have := mul_nonneg (abs_nonneg A) hY
        have := mul_nonneg (abs_nonneg B) hX
        nlinarith

/-- **The elliptic estimate between bundles, in `H^{s,p}`.** Let `P : Γ(E) → Γ(F)` be linear with a
left parametrix `Q : Γ(F) → Γ(E)`, a classical pseudodifferential operator of order `-m` such that
`Q ∘ P - 1` has order `-N`. Read `P u` and `u` through two families of cutoffs `ψᵢ`, `ψ'ᵢ` in
charts, adding up to `1` on `M`, with trivializations `tᵢ` of `F` and `t''ᵢ` of `E` and bases
`(c_k)` of `W` and `(b_k)` of `V`, as in
`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add`. For finitely many
target readings `φⱼ · (χⱼ ℓₗ(t'ⱼ u) ∘ eⱼ⁻¹)` of `u`, `1 < p < ∞` and real `s`, `r` with
`s + m ≤ r + N`, there is a constant `C` such that every smooth section `u` of `E` satisfies

`∑ⱼ ∑ₗ ‖φⱼ · (χⱼ ℓₗ(t'ⱼ u) ∘ eⱼ⁻¹)‖_{H^{s + m,p}} ≤`
`  C (∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ c_k*(tᵢ (P u)) ∘ e'ᵢ⁻¹)‖_{H^{s,p}} +`
`    ∑ᵢ ∑ₖ ‖ψ'ᵢ · (ρ'ᵢ b_k*(t''ᵢ u) ∘ e''ᵢ⁻¹)‖_{H^{r,p}})`. -/
theorem exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators (-m))
    (hQP : Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N))
    {ν : Type*} [Fintype ν] {e : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) (t' : ν → Trivialization V (π V E))
    [∀ j, MemTrivializationAtlas (t' j)] (χ : ν → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : ∀ j, tsupport (χ j) ⊆ (t' j).baseSet) {μ : Type*} [Fintype μ] (ℓ : μ → V →L[ℂ] ℂ)
    {κ : Type*} [Fintype κ] {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (t : κ → Trivialization W (π W F)) [∀ i, MemTrivializationAtlas (t i)]
    (ρ : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1)
    {ι : Type*} [Fintype ι] (c : Module.Basis ι ℂ W)
    {κ' : Type*} [Fintype κ'] {e'' : κ' → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he'' : ∀ i, e'' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ' : ∀ i, 𝓓(⟨(e'' i).target, (e'' i).open_target⟩, ℝ))
    (hψ' : ∀ x, ∑ i, (e'' i).cutoffPullback (he'' i) (ψ' i) 1 x = 1)
    (t'' : κ' → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t'' i)]
    (ρ' : κ' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hρ' : ∀ i, tsupport (ρ' i) ⊆ (t'' i).baseSet)
    (hρψ' : ∀ i, ∀ y ∈ tsupport (ψ' i), ρ' i ((e'' i).symm y) = 1)
    {ι' : Type*} [Fintype ι'] (b : Module.Basis ι' ℂ V)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) {s r : ℝ} (hsr : s + m ≤ r + N) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ∑ j, ∑ l, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) p
          ((e j).cutoffPushforwardSchwartz (he j) (φ j)
            ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) u))‖ ≤
        C * (∑ i, ∑ k, ‖SchwartzMap.toBesselPotentialSpaceCLM s p
            ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
              ((t i).cutoffFrameCoeff (ρ i) (hρ i) (c.coord k).toContinuousLinearMap (P u)))‖ +
          ∑ i, ∑ k, ‖SchwartzMap.toBesselPotentialSpaceCLM r p
            ((e'' i).cutoffPushforwardSchwartz (he'' i) (ψ' i)
              ((t'' i).cutoffFrameCoeff (ρ' i) (hρ' i) (b.coord k).toContinuousLinearMap u))‖) := by
  have hN : s + m ≤ r - -N := by rwa [sub_neg_eq_add]
  refine exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add hQ hQP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s p)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs hp hp_top s)
    (SchwartzMap.toBesselPotentialSpaceCLM_injective r p)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs hp hp_top r)
    _ (fun a ha ↦ ?_) (fun a ha ↦ ?_) he φ t' χ hχ ℓ he' ψ hψ t ρ hρ hρψ c he'' ψ' hψ' t'' ρ' hρ'
    hρψ' b
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

/-- **The elliptic estimate between bundles, in Besov and Hölder–Zygmund norms.** Let
`P : Γ(E) → Γ(F)` be linear with a left parametrix `Q : Γ(F) → Γ(E)`, a classical
pseudodifferential operator of order `-m` such that `Q ∘ P - 1` has order `-N`. Read `P u` and `u`
through two families of cutoffs `ψᵢ`, `ψ'ᵢ` in charts, adding up to `1` on `M`, with
trivializations `tᵢ` of `F` and `t''ᵢ` of `E` and bases `(c_k)` of `W` and `(b_k)` of `V`, as in
`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add`. For finitely many
target readings `φⱼ · (χⱼ ℓₗ(t'ⱼ u) ∘ eⱼ⁻¹)` of `u`, `1 ≤ p ≤ ∞` and real `s`, `r` with
`s + m ≤ r + N`, there is a constant `C` such that every smooth section `u` of `E` satisfies

`∑ⱼ ∑ₗ ‖φⱼ · (χⱼ ℓₗ(t'ⱼ u) ∘ eⱼ⁻¹)‖_{B^{s + m}_{p,∞}} ≤`
`  C (∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ c_k*(tᵢ (P u)) ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}} +`
`    ∑ᵢ ∑ₖ ‖ψ'ᵢ · (ρ'ᵢ b_k*(t''ᵢ u) ∘ e''ᵢ⁻¹)‖_{B^r_{p,∞}})`.

For `p = ∞` these are the Hölder–Zygmund norms `𝒞^s = B^s_{∞,∞}`. -/
theorem exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators (-m))
    (hQP : Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N))
    {ν : Type*} [Fintype ν] {e : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) (t' : ν → Trivialization V (π V E))
    [∀ j, MemTrivializationAtlas (t' j)] (χ : ν → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : ∀ j, tsupport (χ j) ⊆ (t' j).baseSet) {μ : Type*} [Fintype μ] (ℓ : μ → V →L[ℂ] ℂ)
    {κ : Type*} [Fintype κ] {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (t : κ → Trivialization W (π W F)) [∀ i, MemTrivializationAtlas (t i)]
    (ρ : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1)
    {ι : Type*} [Fintype ι] (c : Module.Basis ι ℂ W)
    {κ' : Type*} [Fintype κ'] {e'' : κ' → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he'' : ∀ i, e'' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ' : ∀ i, 𝓓(⟨(e'' i).target, (e'' i).open_target⟩, ℝ))
    (hψ' : ∀ x, ∑ i, (e'' i).cutoffPullback (he'' i) (ψ' i) 1 x = 1)
    (t'' : κ' → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t'' i)]
    (ρ' : κ' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hρ' : ∀ i, tsupport (ρ' i) ⊆ (t'' i).baseSet)
    (hρψ' : ∀ i, ∀ y ∈ tsupport (ψ' i), ρ' i ((e'' i).symm y) = 1)
    {ι' : Type*} [Fintype ι'] (b : Module.Basis ι' ℂ V)
    (β : ContDiffBump (0 : CoordinateSpace n)) (p : ℝ≥0∞) [Fact (1 ≤ p)] {s r : ℝ}
    (hsr : s + m ≤ r + N) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ∑ j, ∑ l, ‖SchwartzMap.toBesovSpaceCLM ℂ β (s + m) p ∞
          ((e j).cutoffPushforwardSchwartz (he j) (φ j)
            ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) u))‖ ≤
        C * (∑ i, ∑ k, ‖SchwartzMap.toBesovSpaceCLM ℂ β s p ∞
            ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
              ((t i).cutoffFrameCoeff (ρ i) (hρ i) (c.coord k).toContinuousLinearMap (P u)))‖ +
          ∑ i, ∑ k, ‖SchwartzMap.toBesovSpaceCLM ℂ β r p ∞
            ((e'' i).cutoffPushforwardSchwartz (he'' i) (ψ' i)
              ((t'' i).cutoffFrameCoeff (ρ' i) (hρ' i) (b.coord k).toContinuousLinearMap u))‖) := by
  have hN : s + m ≤ r - -N := by rwa [sub_neg_eq_add]
  refine exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_add hQ hQP
    (SchwartzMap.toBesovSpaceCLM_injective ℂ β s p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs β s p ∞)
    (SchwartzMap.toBesovSpaceCLM_injective ℂ β r p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs β r p ∞)
    _ (fun a ha ↦ ?_) (fun a ha ↦ ?_) he φ t' χ hχ ℓ he' ψ hψ t ρ hρ hρψ c he'' ψ' hψ' t'' ρ' hρ'
    hρψ' b
  · obtain ⟨C, -, hC⟩ := ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le β s
    refine ⟨C, fun w ↦ ?_⟩
    have := hC (p := p) w
    rwa [sub_neg_eq_add] at this
  · -- `Op(a)` maps `B^r_{p,∞}` to `B^{r + N}_{p,∞}`, which embeds into `B^{s + m}_{p,∞}`.
    obtain ⟨C, -, hC⟩ := ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le β r
    refine ⟨‖BesovSpace.inclusion ℂ β p (q := ∞) (q' := ∞) hN le_rfl‖ * C, fun w ↦ ?_⟩
    rw [← SchwartzMap.inclusion_toBesovSpaceCLM hN le_rfl, mul_assoc]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (hC w) (norm_nonneg _))

end TauCeti
