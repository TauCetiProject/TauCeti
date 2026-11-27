/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology
public import TauCeti.Analysis.Distribution.WaveFrontSet.TensorProduct
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Convex.Cone.InfDist
import TauCeti.Analysis.Distribution.TestFunction.DominatedSeries
import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Prod
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Continuity of the tensor product in the normal topology

Let `Ω ⊆ E` and `O ⊆ D` be open sets of finite-dimensional real inner product spaces, and `Γ₁`,
`Γ₂` cones of nonzero covectors over `Ω` and `O`, closed in `Ω × (E \ {0})` and
`O × (D \ {0})`. The tensor product `S ⊗ T` of distributions (`Distribution.tensorProduct`),
moved to an open set `W` of the Euclidean product `WithLp 2 (E × D)` by
`Distribution.transportCLM`, has its wave front set in the fixed cone `Γ₁ ⊠ Γ₂`
(`TauCeti.tensorCone`) of the nonzero covectors `((x, y), (ξ, η))` with `ξ = 0` or
`(x, ξ) ∈ Γ₁`, and `η = 0` or `(y, η) ∈ Γ₂`, whenever `WF(S) ⊆ Γ₁` and `WF(T) ⊆ Γ₂`
(`Distribution.waveFrontSet_transportCLM_tensorProduct_subset_tensorCone`).

This file proves that for a fixed `v ∈ 𝓓'_{Γ₂}(O)` the map `u ↦ u ⊗ v` is continuous for the
normal topologies of Hörmander's spaces (`TauCeti.WaveFrontSpace.tensorProductRightCLM`):

`· ⊗ v : 𝓓'_{Γ₁}(Ω) →L[ℂ] 𝓓'_{Γ₁ ⊠ Γ₂}(W)`.

This is the continuity of the tensor product in its first variable.

## The estimates

Continuity into `𝓓'(W)` holds because `(u ⊗ v) ψ` is the value of `u` at the partial pairing
of `v` with `ψ`, which depends continuously on `ψ`. For a seminorm `‖·‖_{φ,Λ,N}` of the target, a
partition of unity cuts `φ` into pieces supported near single points `p₀ = (x₀, y₀)` of its
support. Near `p₀` there are closed cones `A₁` and `A₂` of directions avoiding `Γ₁` and `Γ₂`, and
a product cutoff `χ (x, y) = χ₁ x χ₂ y` equal to one near `p₀`, such that every covector `n` lies
in one of three regions (`exists_cone_data`):

* `n.fst ∈ A₁` and `c ‖n.snd‖ ≤ ‖n.fst‖`, where `u` decays in the direction `n.fst` over the
  support of `χ₁`;
* `n.snd ∈ A₂` and `c ‖n.fst‖ ≤ ‖n.snd‖`, where `v` decays in the direction `n.snd` over the
  support of `χ₂`;
* or `n` is close to a direction of `Γ₁ ⊠ Γ₂` at `p₀`, hence far from `Λ`:
  `κ (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖` for `ζ ∈ Λ`.

The localized Fourier transform of `u ⊗ v` with a cutoff `φ` supported near `p₀` is the lattice
series (`Distribution.hasSum_fourier_add_mul_localFourier`)

`(u ⊗ v) (φ e_ζ) = ∑ m, (covolume L)⁻¹ 𝓕 φ (ζ + m) u (χ₁ e_(-m.fst)) v (χ₂ e_(-m.snd))`.

In each region one factor decays rapidly, so the terms decay jointly in `ζ ∈ Λ` and `m`
(`exists_bound_of_offRegions`), except for the factor `u (χ₁ e_(-m.fst))`, which only the
continuous seminorm `‖u‖_{χ₁,A₁,K}` of `𝓓'_{Γ₁}(Ω)` controls, for `-m.fst ∈ A₁`. The terms with
`-m.fst ∉ A₁` are the pairing of `u` with a single test function, the Fourier series of the
modulated cutoffs `χ₁ e_(m.fst)` with the remaining coefficients. Weighted by `(1 + ‖ζ‖) ^ N`,
these test functions depend continuously on `ζ ∈ Λ` and tend to zero at infinity, so together
with `0` they form a compact set, on which `u` is bounded by a continuous seminorm of `𝓓'(Ω)`. The
argument follows that of `TauCeti.WaveFrontSpace.pullbackInlCLM`.

## Main declarations

* `TauCeti.WaveFrontSpace.tensorProductRightCLM`: the tensor product
  `· ⊗ v : 𝓓'_{Γ₁}(Ω) →L[ℂ] 𝓓'_{Γ₁ ⊠ Γ₂}(W)` with a fixed `v ∈ 𝓓'_{Γ₂}(O)`.
* `TauCeti.WaveFrontSpace.toDistribution_tensorProductRightCLM`: it is
  `Distribution.tensorProduct`, transported to `W`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.9 (the wave front set of a tensor product).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, §4, Theorem 4.6 (the tensor product in the normal topology).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction WithLp
open scoped Distributions Topology FourierTransform ContDiff Real RealInnerProductSpace Pointwise

namespace TauCeti

open Distribution

/-! ### Cones of directions at a point -/

section Cone

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- The directions of `Γ` at `x`, together with `0`. -/
private def dirSet (Γ : Set (F × F)) (x : F) : Set F :=
  insert 0 {ξ | (x, ξ) ∈ Γ}

omit [NormedSpace ℝ F] in
/-- The directions of a closed cone `Γ` at a point `x ∈ Ω`, together with `0`, form a closed
set. -/
private theorem isClosed_dirSet {Ω : Set F} {Γ : Set (F × F)}
    (hΓ : IsOpen ((Ω ×ˢ {0}ᶜ) \ Γ)) {x : F} (hx : x ∈ Ω) : IsClosed (dirSet Γ x) := by
  refine isOpen_compl_iff.1 ?_
  have h : (dirSet Γ x)ᶜ = (fun ξ ↦ (x, ξ)) ⁻¹' ((Ω ×ˢ {0}ᶜ) \ Γ) := by
    ext ξ
    simp [dirSet, hx]
  rw [h]
  exact hΓ.preimage (by fun_prop)

private theorem smul_mem_dirSet {Γ : Set (F × F)}
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) {x : F} {t : ℝ} (ht : 0 < t) {ξ : F}
    (hξ : ξ ∈ dirSet Γ x) : t • ξ ∈ dirSet Γ x := by
  rcases hξ with rfl | hξ
  · simp [dirSet]
  · exact Or.inr (hcone _ hξ t ht)

/-- **A cone of directions avoiding `Γ` at a point avoids it nearby.** If no direction of the
closed cone `A` is a direction of the closed cone `Γ` at `x₀ ∈ Ω`, then the same holds over a
neighbourhood of `x₀`. -/
private theorem exists_mem_nhds_disjoint_prod [ProperSpace F] {Ω : Set F} {Γ : Set (F × F)}
    (hΓ : IsOpen ((Ω ×ˢ {0}ᶜ) \ Γ)) (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ)
    (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0) {x₀ : F} (hx₀ : x₀ ∈ Ω) {A : Set F} (hA : IsClosed A)
    (hAcone : ∀ t : ℝ, 0 < t → ∀ a ∈ A, t • a ∈ A) (hA0 : ∀ a ∈ A, a ≠ 0 → (x₀, a) ∉ Γ) :
    ∃ U ∈ 𝓝 x₀, Disjoint (U ×ˢ A) Γ := by
  set C : Set (F × F) := {x₀} ×ˢ (A ∩ sphere 0 1)
  have hC : IsCompact C := isCompact_singleton.prod ((isCompact_sphere 0 1).inter_left hA)
  have hCsub : C ⊆ (Ω ×ˢ {0}ᶜ) \ Γ := by
    rintro ⟨x, a⟩ ⟨hx, ha, ha1⟩
    rw [mem_singleton_iff] at hx
    subst hx
    have ha0 : a ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨a, ha1⟩
    exact ⟨⟨hx₀, ha0⟩, hA0 a ha ha0⟩
  obtain ⟨δ, hδ, hδsub⟩ := hC.exists_thickening_subset_open hΓ hCsub
  refine ⟨ball x₀ δ, ball_mem_nhds _ hδ, disjoint_left.2 ?_⟩
  rintro ⟨x, a⟩ ⟨hx, ha⟩ hxa
  have ha0 : a ≠ 0 := hΓ0 _ hxa
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hmem : (x, ‖a‖⁻¹ • a) ∈ thickening δ C := by
    refine mem_thickening_iff.2 ⟨(x₀, ‖a‖⁻¹ • a), ⟨rfl, hAcone _ (inv_pos.2 hna) a ha, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna.ne']
    · rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact mem_ball.1 hx
  exact (hδsub hmem).2 (hcone _ hxa _ (inv_pos.2 hna))

/-- **A cone of directions far from `Γ` at a point.** For `θ > 0`, the directions at distance at
least `θ ‖a‖` from the directions of `Γ` at `x₀ ∈ Ω` form a closed cone `A` avoiding `Γ` over a
neighbourhood `U` of `x₀`; the directions outside `A` are within `θ ‖a‖` of those of `Γ`. -/
private theorem exists_nhds_cone_far [ProperSpace F] {Ω : Set F} {Γ : Set (F × F)}
    (hΓ : IsOpen ((Ω ×ˢ {0}ᶜ) \ Γ)) (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ)
    (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0) {x₀ : F} (hx₀ : x₀ ∈ Ω) {θ : ℝ} (hθ : 0 < θ) :
    ∃ U ∈ 𝓝 x₀, ∃ A : Set F, IsClosed A ∧ (∀ t : ℝ, 0 < t → ∀ a ∈ A, t • a ∈ A) ∧
      Disjoint (U ×ˢ A) Γ ∧ ∀ a ∉ A, infDist a (dirSet Γ x₀) < θ * ‖a‖ := by
  set Z := dirSet Γ x₀
  have hZc : ∀ t : ℝ, 0 < t → ∀ z ∈ Z, t • z ∈ Z := fun t ht _ hz ↦ smul_mem_dirSet hcone ht hz
  set A : Set F := {a | θ * ‖a‖ ≤ infDist a Z}
  have hA : IsClosed A :=
    isClosed_le (continuous_const.mul continuous_norm) (continuous_infDist_pt Z)
  have hAc : ∀ t : ℝ, 0 < t → ∀ a ∈ A, t • a ∈ A := fun t ht a ha ↦ by
    simp only [A, mem_ofPred_eq, infDist_smul_of_forall_smul_mem hZc ht, norm_smul,
      Real.norm_of_nonneg ht.le] at ha ⊢
    nlinarith
  have hAΓ : ∀ a ∈ A, a ≠ 0 → (x₀, a) ∉ Γ := fun a ha ha0 hmem ↦ by
    have h0 : infDist a Z = 0 := infDist_zero_of_mem (Or.inr hmem)
    have : 0 < θ * ‖a‖ := by have := norm_pos_iff.2 ha0; positivity
    exact (lt_irrefl (0 : ℝ)) (this.trans_le (h0 ▸ ha))
  obtain ⟨U, hU, hUΓ⟩ := exists_mem_nhds_disjoint_prod hΓ hcone hΓ0 hx₀ hA hAc hAΓ
  exact ⟨U, hU, A, hA, hAc, hUΓ, fun a ha ↦ by simpa [A] using ha⟩

end Cone

section Separation

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D]

omit [NormedSpace ℝ E] [NormedSpace ℝ D] in
/-- The sum of the distances of the two components of `ζ` to `Z₁` and `Z₂`. -/
private def dirDist (Z₁ : Set E) (Z₂ : Set D) (ζ : WithLp 2 (E × D)) : ℝ :=
  infDist ζ.fst Z₁ + infDist ζ.snd Z₂

omit [NormedSpace ℝ E] [NormedSpace ℝ D] in
private theorem continuous_dirDist (Z₁ : Set E) (Z₂ : Set D) : Continuous (dirDist Z₁ Z₂) :=
  ((continuous_infDist_pt Z₁).comp (by fun_prop)).add
    ((continuous_infDist_pt Z₂).comp (by fun_prop))

private theorem dirDist_smul {Z₁ : Set E} {Z₂ : Set D}
    (hZ₁ : ∀ t : ℝ, 0 < t → ∀ z ∈ Z₁, t • z ∈ Z₁) (hZ₂ : ∀ t : ℝ, 0 < t → ∀ z ∈ Z₂, t • z ∈ Z₂)
    {t : ℝ} (ht : 0 < t) (ζ : WithLp 2 (E × D)) : dirDist Z₁ Z₂ (t • ζ) = t * dirDist Z₁ Z₂ ζ := by
  simp only [dirDist, WithLp.smul_fst, WithLp.smul_snd, infDist_smul_of_forall_smul_mem hZ₁ ht,
    infDist_smul_of_forall_smul_mem hZ₂ ht]
  ring

omit [NormedSpace ℝ E] [NormedSpace ℝ D] in
/-- `dirDist` is `2`-Lipschitz. -/
private theorem dirDist_le_add (Z₁ : Set E) (Z₂ : Set D) (ζ n : WithLp 2 (E × D)) :
    dirDist Z₁ Z₂ ζ ≤ dirDist Z₁ Z₂ n + 2 * ‖ζ - n‖ := by
  have h₁ := infDist_le_infDist_add_dist (x := ζ.fst) (y := n.fst) (s := Z₁)
  have h₂ := infDist_le_infDist_add_dist (x := ζ.snd) (y := n.snd) (s := Z₂)
  have h₃ : dist ζ.fst n.fst ≤ ‖ζ - n‖ := by
    simpa only [dist_eq_norm, WithLp.sub_fst] using WithLp.norm_fst_le (x := ζ - n)
  have h₄ : dist ζ.snd n.snd ≤ ‖ζ - n‖ := by
    simpa only [dist_eq_norm, WithLp.sub_snd] using WithLp.norm_snd_le (x := ζ - n)
  simp only [dirDist]
  linarith

/-- On a closed cone `V` none of whose nonzero directions has both components in the closed cones
`Z₁` and `Z₂`, `dirDist Z₁ Z₂` is bounded below by a positive multiple of the norm. -/
private theorem exists_mul_norm_le_dirDist [FiniteDimensional ℝ E] [FiniteDimensional ℝ D]
    {Z₁ : Set E} {Z₂ : Set D} (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hZ₁0 : (0 : E) ∈ Z₁)
    (hZ₂0 : (0 : D) ∈ Z₂) (hZ₁c : ∀ t : ℝ, 0 < t → ∀ z ∈ Z₁, t • z ∈ Z₁)
    (hZ₂c : ∀ t : ℝ, 0 < t → ∀ z ∈ Z₂, t • z ∈ Z₂) {V : Set (WithLp 2 (E × D))} (hV : IsClosed V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ V, t • ζ ∈ V)
    (hVZ : ∀ ζ ∈ V, ζ ≠ 0 → ζ.fst ∈ Z₁ → ζ.snd ∉ Z₂) :
    ∃ β > 0, β ≤ 1 ∧ ∀ ζ ∈ V, β * ‖ζ‖ ≤ dirDist Z₁ Z₂ ζ := by
  set K := V ∩ sphere (0 : WithLp 2 (E × D)) 1
  have hK : IsCompact K := (isCompact_sphere 0 1).inter_left hV
  -- The bound on the unit sphere gives the bound everywhere, by homogeneity.
  have hscale {β : ℝ} (hβ : ∀ u ∈ K, β ≤ dirDist Z₁ Z₂ u) (ζ : WithLp 2 (E × D)) (hζ : ζ ∈ V) :
      β * ‖ζ‖ ≤ dirDist Z₁ Z₂ ζ := by
    rcases eq_or_ne ζ 0 with rfl | hζ0
    · simp only [norm_zero, mul_zero, dirDist]
      exact add_nonneg infDist_nonneg infDist_nonneg
    have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
    have hu : ‖ζ‖⁻¹ • ζ ∈ K := ⟨hVcone _ (inv_pos.2 hn) ζ hζ, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩
    have h := hβ _ hu
    rw [dirDist_smul hZ₁c hZ₂c (inv_pos.2 hn), le_inv_mul_iff₀ hn] at h
    linarith
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · exact ⟨1, one_pos, le_rfl, hscale (by simp [hK0])⟩
  obtain ⟨u₀, hu₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_dirDist Z₁ Z₂).continuousOn
  -- The minimum is positive: otherwise both components of `u₀` would lie in the cones.
  have hpos : 0 < dirDist Z₁ Z₂ u₀ := by
    have h₁ := infDist_nonneg (x := u₀.fst) (s := Z₁)
    have h₂ := infDist_nonneg (x := u₀.snd) (s := Z₂)
    by_contra hle
    have h₁' : infDist u₀.fst Z₁ = 0 := by simp only [dirDist] at hle; linarith
    have h₂' : infDist u₀.snd Z₂ = 0 := by simp only [dirDist] at hle; linarith
    have hu₀0 : u₀ ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨u₀, hu₀.2⟩
    exact hVZ u₀ hu₀.1 hu₀0 ((hZ₁.mem_iff_infDist_zero ⟨0, hZ₁0⟩).2 h₁')
      ((hZ₂.mem_iff_infDist_zero ⟨0, hZ₂0⟩).2 h₂')
  exact ⟨min (dirDist Z₁ Z₂ u₀) 1, lt_min hpos one_pos, min_le_right _ _,
    hscale fun u hu ↦ (min_le_left _ _).trans (hmin hu)⟩

/-- The covectors `n` lying in neither of the two regions
`R₁ = {n.fst ∈ A₁, c ‖n.snd‖ ≤ ‖n.fst‖}` and `R₂ = {n.snd ∈ A₂, c ‖n.fst‖ ≤ ‖n.snd‖}`. -/
private def offRegions (A₁ : Set E) (A₂ : Set D) (c : ℝ) (n : WithLp 2 (E × D)) : Prop :=
  ¬(n.fst ∈ A₁ ∧ c * ‖n.snd‖ ≤ ‖n.fst‖) ∧ ¬(n.snd ∈ A₂ ∧ c * ‖n.fst‖ ≤ ‖n.snd‖)

omit [NormedSpace ℝ E] in
/-- Off the region `{a ∈ A, c s ≤ ‖a‖}`, a vector `a` with `‖a‖ ≤ r` and `s ≤ r` is within `c r`
of `Z`, when the complement of `A` is within `c ‖·‖` of `Z` and `0 ∈ Z`. It is applied to either
component `a` of a covector `n`, with `s` the norm of the other component and `r = ‖n‖`. -/
private theorem infDist_le_mul_of_not_and {Z A : Set E} (hZ0 : (0 : E) ∈ Z) {c : ℝ}
    (hA : ∀ a ∉ A, infDist a Z < c * ‖a‖) (hc : 0 ≤ c) {a : E} {r s : ℝ} (har : ‖a‖ ≤ r)
    (hsr : s ≤ r) (ha : ¬(a ∈ A ∧ c * s ≤ ‖a‖)) : infDist a Z ≤ c * r := by
  have h0 : infDist a Z ≤ ‖a‖ := by simpa using infDist_le_dist_of_mem (x := a) hZ0
  rcases not_and_or.1 ha with hA' | hlt
  · exact (hA _ hA').le.trans (mul_le_mul_of_nonneg_left har hc)
  · push Not at hlt
    nlinarith

omit [NormedSpace ℝ E] [NormedSpace ℝ D] in
/-- **Separation from the cone `V`.** If `β ‖ζ‖ ≤ dirDist Z₁ Z₂ ζ` on `V`, with `β ≤ 1`, and the
complements of `A₁` and `A₂` are within `(β / 4) ‖·‖` of `Z₁` and `Z₂`, then every covector `n`
off the two regions `R₁` and `R₂` is far from `V`:
`β / (12 + β) (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖` for `ζ ∈ V`. -/
private theorem mul_add_le_norm_sub_of_offRegions {Z₁ A₁ : Set E} {Z₂ A₂ : Set D}
    (hZ₁0 : (0 : E) ∈ Z₁) (hZ₂0 : (0 : D) ∈ Z₂) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hA₁ : ∀ a ∉ A₁, infDist a Z₁ < β / 4 * ‖a‖) (hA₂ : ∀ a ∉ A₂, infDist a Z₂ < β / 4 * ‖a‖)
    {ζ : WithLp 2 (E × D)} (hζ : β * ‖ζ‖ ≤ dirDist Z₁ Z₂ ζ) {n : WithLp 2 (E × D)}
    (hn : offRegions A₁ A₂ (β / 4) n) : β / (12 + β) * (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖ := by
  have h₁ := infDist_le_mul_of_not_and hZ₁0 hA₁ (by positivity) (WithLp.norm_fst_le (x := n))
    (WithLp.norm_snd_le (x := n)) hn.1
  have h₂ := infDist_le_mul_of_not_and hZ₂0 hA₂ (by positivity) (WithLp.norm_snd_le (x := n))
    (WithLp.norm_fst_le (x := n)) hn.2
  have hL := dirDist_le_add Z₁ Z₂ ζ n
  have htri : ‖n‖ ≤ ‖ζ‖ + ‖ζ - n‖ := by
    simpa [norm_sub_rev] using norm_le_norm_add_norm_sub' n ζ
  have hd := norm_nonneg (ζ - n)
  simp only [dirDist] at hL hζ
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

end Separation

section ConeData

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]

/-- **Cones adapted to a seminorm of the tensor product.** Let `V` be a closed cone of covectors of
`E × D` none of whose directions at `p₀` lies in `Γ₁ ⊠ Γ₂`. Then there are neighbourhoods `U₁` of
`p₀.fst` and `U₂` of `p₀.snd`, closed cones `A₁` and `A₂` of directions avoiding `Γ₁` over `U₁`
and `Γ₂` over `U₂`, and constants `c, κ > 0` such that every covector `n` lying in neither of the
regions `{n.fst ∈ A₁, c ‖n.snd‖ ≤ ‖n.fst‖}` and `{n.snd ∈ A₂, c ‖n.fst‖ ≤ ‖n.snd‖}` is far from
`V`: `κ (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖` for `ζ ∈ V`. -/
private theorem exists_cone_data {Ω : Set E} {O : Set D} {Γ₁ : Set (E × E)} {Γ₂ : Set (D × D)}
    (hΓ₁ : IsOpen ((Ω ×ˢ {0}ᶜ) \ Γ₁)) (hcone₁ : ∀ p ∈ Γ₁, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₁)
    (hΓ₁0 : ∀ p ∈ Γ₁, p.2 ≠ 0) (hΓ₂ : IsOpen ((O ×ˢ {0}ᶜ) \ Γ₂))
    (hcone₂ : ∀ p ∈ Γ₂, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₂) (hΓ₂0 : ∀ p ∈ Γ₂, p.2 ≠ 0)
    {p₀ : WithLp 2 (E × D)} (hp₀ : p₀.fst ∈ Ω ∧ p₀.snd ∈ O) {V : Set (WithLp 2 (E × D))}
    (hV : IsClosed V) (hVcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ V, t • ζ ∈ V)
    (hVΓ : ∀ ζ ∈ V, (p₀, ζ) ∉ tensorCone Γ₁ Γ₂) :
    ∃ U₁ ∈ 𝓝 p₀.fst, ∃ U₂ ∈ 𝓝 p₀.snd, ∃ (A₁ : Set E) (A₂ : Set D), IsClosed A₁ ∧
      (∀ t : ℝ, 0 < t → ∀ a ∈ A₁, t • a ∈ A₁) ∧ IsClosed A₂ ∧
      (∀ t : ℝ, 0 < t → ∀ a ∈ A₂, t • a ∈ A₂) ∧ Disjoint (U₁ ×ˢ A₁) Γ₁ ∧
      Disjoint (U₂ ×ˢ A₂) Γ₂ ∧ ∃ c > 0, ∃ κ > 0, κ ≤ 1 ∧ ∀ ζ ∈ V, ∀ n,
        offRegions A₁ A₂ c n → κ * (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖ := by
  set Z₁ := dirSet Γ₁ p₀.fst
  set Z₂ := dirSet Γ₂ p₀.snd
  have hZ₁ : IsClosed Z₁ := isClosed_dirSet hΓ₁ hp₀.1
  have hZ₂ : IsClosed Z₂ := isClosed_dirSet hΓ₂ hp₀.2
  have hZ₁c : ∀ t : ℝ, 0 < t → ∀ z ∈ Z₁, t • z ∈ Z₁ := fun t ht _ hz ↦ smul_mem_dirSet hcone₁ ht hz
  have hZ₂c : ∀ t : ℝ, 0 < t → ∀ z ∈ Z₂, t • z ∈ Z₂ := fun t ht _ hz ↦ smul_mem_dirSet hcone₂ ht hz
  have hZ₁0 : (0 : E) ∈ Z₁ := mem_insert _ _
  have hZ₂0 : (0 : D) ∈ Z₂ := mem_insert _ _
  obtain ⟨β, hβ, hβ1, hβV⟩ := exists_mul_norm_le_dirDist hZ₁ hZ₂ hZ₁0 hZ₂0 hZ₁c hZ₂c hV hVcone
    fun ζ hζ hζ0 h₁ h₂ ↦ hVΓ ζ hζ (mem_tensorCone.2 ⟨hζ0, h₁, h₂⟩)
  -- The cones `A₁ = {a | (β / 4) ‖a‖ ≤ dist (a, Z₁)}` and `A₂` avoid `Γ₁` and `Γ₂` nearby.
  obtain ⟨U₁, hU₁, A₁, hA₁, hA₁c, hU₁Γ, hA₁Z⟩ :=
    exists_nhds_cone_far hΓ₁ hcone₁ hΓ₁0 hp₀.1 (by positivity : 0 < β / 4)
  obtain ⟨U₂, hU₂, A₂, hA₂, hA₂c, hU₂Γ, hA₂Z⟩ :=
    exists_nhds_cone_far hΓ₂ hcone₂ hΓ₂0 hp₀.2 (by positivity : 0 < β / 4)
  exact ⟨U₁, hU₁, U₂, hU₂, A₁, A₂, hA₁, hA₁c, hA₂, hA₂c, hU₁Γ, hU₂Γ, β / 4, by positivity,
    β / (12 + β), by positivity, by rw [div_le_one (by positivity)]; linarith,
    fun ζ hζ n hn ↦ mul_add_le_norm_sub_of_offRegions hZ₁0 hZ₂0 hβ hβ1 hA₁Z hA₂Z (hβV ζ hζ) hn⟩

end ConeData

/-! ### Decay of the terms of the lattice series -/

section Decay

variable {E D : Type*} [NormedAddCommGroup E] [NormedAddCommGroup D]

/-- `1 + ‖ζ‖ ≤ (1 + ‖ζ - n‖) (1 + ‖n‖)`. -/
private theorem one_add_norm_le_mul_sub (ζ n : WithLp 2 (E × D)) :
    1 + ‖ζ‖ ≤ (1 + ‖ζ - n‖) * (1 + ‖n‖) := by
  simpa using one_add_norm_add_le (ζ - n) n

/-- If `r ≤ a + b` and `c b ≤ a`, then `1 + r ≤ (1 + c⁻¹) (1 + a)`. It is applied with `r = ‖n‖`
and `a`, `b` the norms of the two components of a covector `n`, on the region where the component
of norm `a` dominates. -/
private theorem one_add_le_of_le_add_of_mul_le {c : ℝ} (hc : 0 < c) {r a b : ℝ} (hr : r ≤ a + b)
    (hb : c * b ≤ a) : 1 + r ≤ (1 + c⁻¹) * (1 + a) := by
  have h' : b ≤ c⁻¹ * a := by rwa [le_inv_mul_iff₀ hc]
  have he : (1 + c⁻¹) * (1 + a) = 1 + a + c⁻¹ * a + c⁻¹ := by ring
  have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
  linarith [he]

variable {f : WithLp 2 (E × D) → ℂ} {g : D → ℂ} {ζ n : WithLp 2 (E × D)} {N P k : ℕ}

/-- **The region `c ‖n.snd‖ ≤ ‖n.fst‖`.** There `1 + ‖n‖` is comparable to `1 + ‖n.fst‖`, so the
polynomial growth of `g` and the shift of the weight of `ζ` cost a power of `1 + ‖n.fst‖`. -/
private theorem bound_of_mul_norm_snd_le {c : ℝ} (hc : 0 < c) (hn : c * ‖n.snd‖ ≤ ‖n.fst‖)
    {B Cg : ℝ} (hB : (1 + ‖ζ - n‖) ^ N * ‖f (ζ - n)‖ ≤ B) (hCg : 0 ≤ Cg)
    (hg : ‖g n.snd‖ ≤ Cg * (1 + ‖n.snd‖) ^ k) :
    (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤
      B * Cg * (1 + c⁻¹) ^ (N + P + k) * (1 + ‖n.fst‖) ^ (N + P + k) := by
  have hpe := one_add_norm_le_mul_sub ζ n
  have hnn := one_add_le_of_le_add_of_mul_le hc (WithLp.prod_norm_le_norm_fst_add_norm_snd n) hn
  have hsnd : 1 + ‖n.snd‖ ≤ 1 + ‖n‖ := by gcongr; exact WithLp.norm_snd_le (x := n)
  have hB0 : 0 ≤ B := (by positivity : (0 : ℝ) ≤ (1 + ‖ζ - n‖) ^ N * ‖f (ζ - n)‖).trans hB
  rw [norm_mul]
  calc (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * (‖f (ζ - n)‖ * ‖g n.snd‖))
      ≤ ((1 + ‖ζ - n‖) * (1 + ‖n‖)) ^ N *
          ((1 + ‖n‖) ^ P * (‖f (ζ - n)‖ * (Cg * (1 + ‖n‖) ^ k))) := by
        gcongr
        exact hg.trans (by gcongr)
    _ = ((1 + ‖ζ - n‖) ^ N * ‖f (ζ - n)‖) * Cg * (1 + ‖n‖) ^ (N + P + k) := by
        rw [mul_pow]; ring
    _ ≤ B * Cg * ((1 + c⁻¹) * (1 + ‖n.fst‖)) ^ (N + P + k) := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- **The region `c ‖n.fst‖ ≤ ‖n.snd‖`.** There `1 + ‖n‖` is comparable to `1 + ‖n.snd‖`, and
the decay of `g` absorbs the weights. -/
private theorem bound_of_mul_norm_fst_le {c : ℝ} (hc : 0 < c) (hn : c * ‖n.fst‖ ≤ ‖n.snd‖)
    {B Dg : ℝ} (hB : (1 + ‖ζ - n‖) ^ N * ‖f (ζ - n)‖ ≤ B)
    (hD : (1 + ‖n.snd‖) ^ (N + P) * ‖g n.snd‖ ≤ Dg) :
    (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ B * (1 + c⁻¹) ^ (N + P) * Dg := by
  have hpe := one_add_norm_le_mul_sub ζ n
  have hnn := one_add_le_of_le_add_of_mul_le hc
    ((WithLp.prod_norm_le_norm_fst_add_norm_snd n).trans_eq (add_comm _ _)) hn
  have hB0 : 0 ≤ B := (by positivity : (0 : ℝ) ≤ (1 + ‖ζ - n‖) ^ N * ‖f (ζ - n)‖).trans hB
  rw [norm_mul]
  calc (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * (‖f (ζ - n)‖ * ‖g n.snd‖))
      ≤ ((1 + ‖ζ - n‖) * (1 + ‖n‖)) ^ N * ((1 + ‖n‖) ^ P * (‖f (ζ - n)‖ * ‖g n.snd‖)) := by
        gcongr
    _ = ((1 + ‖ζ - n‖) ^ N * ‖f (ζ - n)‖) * ((1 + ‖n‖) ^ (N + P) * ‖g n.snd‖) := by
        rw [mul_pow]; ring
    _ ≤ B * (((1 + c⁻¹) * (1 + ‖n.snd‖)) ^ (N + P) * ‖g n.snd‖) := by gcongr
    _ = B * (1 + c⁻¹) ^ (N + P) * ((1 + ‖n.snd‖) ^ (N + P) * ‖g n.snd‖) := by
        rw [mul_pow]; ring
    _ ≤ _ := by gcongr

/-- **Off the two regions.** There `‖ζ - n‖` is comparable to `‖ζ‖ + ‖n‖`, and the decay of `f`
absorbs the weights and the polynomial growth of `g`. -/
private theorem bound_of_mul_add_le {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hsep : κ * (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖) {B Cg : ℝ}
    (hB : (1 + ‖ζ - n‖) ^ (N + P + k) * ‖f (ζ - n)‖ ≤ B) (hCg : 0 ≤ Cg)
    (hg : ‖g n.snd‖ ≤ Cg * (1 + ‖n.snd‖) ^ k) :
    (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ (κ⁻¹) ^ (N + P + k) * B * Cg := by
  have hsnd : 1 + ‖n.snd‖ ≤ 1 + ‖ζ‖ + ‖n‖ := by
    have := WithLp.norm_snd_le (x := n)
    linarith [norm_nonneg ζ]
  have hsum : 1 + ‖ζ‖ + ‖n‖ ≤ κ⁻¹ * (1 + ‖ζ - n‖) := by
    rw [le_inv_mul_iff₀ hκ]
    nlinarith [norm_nonneg ζ, norm_nonneg n]
  have hpow : (1 + ‖ζ‖) ^ N * (1 + ‖n‖) ^ P * (1 + ‖n.snd‖) ^ k ≤
      (κ⁻¹ * (1 + ‖ζ - n‖)) ^ (N + P + k) := by
    have h₁ : (1 + ‖ζ‖) ^ N ≤ (1 + ‖ζ‖ + ‖n‖) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg n]) N
    have h₂ : (1 + ‖n‖) ^ P ≤ (1 + ‖ζ‖ + ‖n‖) ^ P :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg ζ]) P
    have h₃ : (1 + ‖n.snd‖) ^ k ≤ (1 + ‖ζ‖ + ‖n‖) ^ k := pow_le_pow_left₀ (by positivity) hsnd k
    calc (1 + ‖ζ‖) ^ N * (1 + ‖n‖) ^ P * (1 + ‖n.snd‖) ^ k
        ≤ (1 + ‖ζ‖ + ‖n‖) ^ N * (1 + ‖ζ‖ + ‖n‖) ^ P * (1 + ‖ζ‖ + ‖n‖) ^ k :=
          mul_le_mul (mul_le_mul h₁ h₂ (by positivity) (by positivity)) h₃ (by positivity)
            (by positivity)
      _ = (1 + ‖ζ‖ + ‖n‖) ^ (N + P + k) := by rw [pow_add, pow_add]
      _ ≤ _ := by gcongr
  rw [norm_mul]
  calc (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * (‖f (ζ - n)‖ * ‖g n.snd‖))
      ≤ (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * (‖f (ζ - n)‖ * (Cg * (1 + ‖n.snd‖) ^ k))) := by
        gcongr
    _ = ((1 + ‖ζ‖) ^ N * (1 + ‖n‖) ^ P * (1 + ‖n.snd‖) ^ k) * ‖f (ζ - n)‖ * Cg := by ring
    _ ≤ (κ⁻¹ * (1 + ‖ζ - n‖)) ^ (N + P + k) * ‖f (ζ - n)‖ * Cg := by gcongr
    _ = (κ⁻¹) ^ (N + P + k) * ((1 + ‖ζ - n‖) ^ (N + P + k) * ‖f (ζ - n)‖) * Cg := by
        rw [mul_pow]; ring
    _ ≤ _ := by gcongr

/-- **Decay of the terms of the lattice series.** Let `f` decay rapidly, and let `g` grow at most
polynomially and decay rapidly on `A₂`. If every covector `n` off the two regions
`{n.fst ∈ A₁, c ‖n.snd‖ ≤ ‖n.fst‖}` and `{n.snd ∈ A₂, c ‖n.fst‖ ≤ ‖n.snd‖}` is far from the cone
`V`, then the weighted products `(1 + ‖ζ‖) ^ N (1 + ‖n‖) ^ P ‖f (ζ - n) g (n.snd)‖`, for `ζ ∈ V`,
are bounded by `C (1 + ‖n.fst‖) ^ K`, and by `C` when `n.fst ∉ A₁`. -/
private theorem exists_bound_of_offRegions {A₁ : Set E} {A₂ : Set D} {c κ : ℝ} (hc : 0 < c)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {V : Set (WithLp 2 (E × D))}
    (hsep : ∀ ζ ∈ V, ∀ n, offRegions A₁ A₂ c n → κ * (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖)
    (hf : ∀ M : ℕ, ∃ B, ∀ v, (1 + ‖v‖) ^ M * ‖f v‖ ≤ B)
    (hg : ∃ (C : ℝ) (k : ℕ), ∀ b, ‖g b‖ ≤ C * (1 + ‖b‖) ^ k)
    (hgA : ∀ M : ℕ, ∃ C, ∀ b ∈ A₂, (1 + ‖b‖) ^ M * ‖g b‖ ≤ C) (N P : ℕ) :
    ∃ (C : ℝ) (K : ℕ), ∀ ζ ∈ V, ∀ n,
      (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ C * (1 + ‖n.fst‖) ^ K ∧
      (n.fst ∉ A₁ → (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ C) := by
  obtain ⟨Cg, k, hCg⟩ := hg
  obtain ⟨B₁, hB₁⟩ := hf N
  obtain ⟨B₂, hB₂⟩ := hf (N + P + k)
  obtain ⟨Dg, hDg⟩ := hgA (N + P)
  set Cg' := max Cg 0
  have hCg' : ∀ b, ‖g b‖ ≤ Cg' * (1 + ‖b‖) ^ k := fun b ↦
    (hCg b).trans (by gcongr; exact le_max_left _ _)
  have hB₂0 : 0 ≤ B₂ := (by positivity : (0 : ℝ) ≤ (1 + ‖(0 : WithLp 2 (E × D))‖) ^ (N + P + k) *
    ‖f 0‖).trans (hB₂ 0)
  set C₁ := B₁ * Cg' * (1 + c⁻¹) ^ (N + P + k)
  set C₂ := B₁ * (1 + c⁻¹) ^ (N + P) * Dg
  set C₃ := (κ⁻¹) ^ (N + P + k) * B₂ * Cg'
  have hC₃ : 0 ≤ C₃ := by positivity
  set C := max C₁ (max C₂ C₃)
  have hC : 0 ≤ C := hC₃.trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, N + P + k, fun ζ hζ n ↦ ?_⟩
  have hK : C ≤ C * (1 + ‖n.fst‖) ^ (N + P + k) :=
    le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [norm_nonneg n.fst]))
  by_cases h₁ : n.fst ∈ A₁ ∧ c * ‖n.snd‖ ≤ ‖n.fst‖
  · have h := bound_of_mul_norm_snd_le (ζ := ζ) (P := P) hc h₁.2 (hB₁ _) (le_max_right _ _) (hCg' _)
    exact ⟨h.trans (by gcongr; exact le_max_left _ _), fun h' ↦ (h' h₁.1).elim⟩
  have hbound : (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ C := by
    by_cases h₂ : n.snd ∈ A₂ ∧ c * ‖n.fst‖ ≤ ‖n.snd‖
    · exact (bound_of_mul_norm_fst_le (ζ := ζ) hc h₂.2 (hB₁ _) (hDg _ h₂.1)).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact (bound_of_mul_add_le (P := P) hκ hκ1 (hsep ζ hζ n ⟨h₁, h₂⟩) (hB₂ _) (le_max_right _ _)
        (hCg' _)).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact ⟨hbound.trans hK, fun _ ↦ hbound⟩

end Decay

/-! ### The lattice series of the tensor product -/

section Lattice

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]
  (L : Submodule ℤ (WithLp 2 (E × D))) (A₁ : Set E)

/-- The terms `(covolume L)⁻¹ f (ζ + m) g (-m.snd) h (-m.fst)` of the lattice series of the
tensor product, for the `m` with `-m.fst ∈ A₁`. -/
private def goodTerm (f : WithLp 2 (E × D) → ℂ) (h : E → ℂ) (g : D → ℂ) (ζ : WithLp 2 (E × D))
    (m : ZLattice.dual L) : ℂ :=
  {m : ZLattice.dual L | -(m : WithLp 2 (E × D)).fst ∈ A₁}.indicator
    (fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * (f (ζ + m) * g (-(m : WithLp 2 (E × D)).snd) *
      h (-(m : WithLp 2 (E × D)).fst))) m

/-- The coefficients `(covolume L)⁻¹ f (ζ + m) g (-m.snd)` of the lattice series of the tensor
product, for the `m` with `-m.fst ∉ A₁`. -/
private def badCoeff (f : WithLp 2 (E × D) → ℂ) (g : D → ℂ) (ζ : WithLp 2 (E × D))
    (m : ZLattice.dual L) : ℂ :=
  {m : ZLattice.dual L | -(m : WithLp 2 (E × D)).fst ∉ A₁}.indicator
    (fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * (f (ζ + m) * g (-(m : WithLp 2 (E × D)).snd))) m

variable {L A₁}

variable {Ω : Opens E} {O : Opens D} {V : Opens (E × D)} {W : Opens (WithLp 2 (E × D))}
  (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
  (hW : MapsTo (prodContinuousLinearEquiv 2 ℝ E D) W V)

/-- **The splitting of the lattice series of the tensor product.** For a product cutoff
`χ (x, y) = χ₁ x χ₂ y` equal to one on the support of `φ`, the localized Fourier transform of
`S ⊗ T` with cutoff `φ` at `ζ` is the sum of the terms of its lattice series with `-m.fst ∈ A₁`,
and of the pairing of `S` with the series of the remaining terms, a smooth function supported in
`tsupport χ₁`. -/
private theorem localFourier_tensorProduct_eq_add (S : 𝓓'(Ω, ℂ)) (T : 𝓓'(O, ℂ)) {χ₁ : 𝓓(Ω, ℂ)}
    {χ₂ : 𝓓(O, ℂ)} {χ : 𝓓(W, ℂ)} (hχ : ∀ p, χ p = χ₁ p.fst * χ₂ p.snd) [DiscreteTopology L]
    [IsZLattice ℝ L] (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0)
    {φ : 𝓓(W, ℂ)} (hφ : EqOn (χ : WithLp 2 (E × D) → ℂ) 1 (support φ)) (ζ : WithLp 2 (E × D))
    (hgood : Summable (goodTerm L A₁ (𝓕 (φ : WithLp 2 (E × D) → ℂ)) (S.localFourier χ₁)
      (T.localFourier χ₂) ζ))
    (hbad : Summable fun m ↦ badCoeff L A₁ (𝓕 (φ : WithLp 2 (E × D) → ℂ)) (T.localFourier χ₂) ζ m
      • χ₁.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)).fst) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).localFourier φ ζ =
      (∑' m, goodTerm L A₁ (𝓕 (φ : WithLp 2 (E × D) → ℂ)) (S.localFourier χ₁)
        (T.localFourier χ₂) ζ m) +
      S.complexPairing (ofSupportedIn χ₁.tsupport_subset (∑' m, badCoeff L A₁
        (𝓕 (φ : WithLp 2 (E × D) → ℂ)) (T.localFourier χ₂) ζ m •
          χ₁.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)).fst)) := by
  set f : WithLp 2 (E × D) → ℂ := 𝓕 (φ : WithLp 2 (E × D) → ℂ)
  -- The terms with `-m.fst ∉ A₁` sum to the pairing of `S` with the series of modulated cutoffs.
  have hb := hasSum_mul_localFourier_neg S χ₁ hbad
  refine ((hasSum_fourier_add_mul_localFourier _ χ L hL hφ ζ).unique
    ((hgood.hasSum.add hb).congr_fun fun m ↦ ?_))
  rw [localFourier_transportCLM_tensorProduct S T hV hW hχ, WithLp.neg_fst, WithLp.neg_snd,
    add_comm (m : WithLp 2 (E × D)) ζ]
  by_cases hm : -(m : WithLp 2 (E × D)).fst ∈ A₁
  · rw [goodTerm, badCoeff, indicator_of_mem (s := {m : ZLattice.dual L |
      -(m : WithLp 2 (E × D)).fst ∈ A₁}) hm, indicator_of_notMem (s := {m : ZLattice.dual L |
      -(m : WithLp 2 (E × D)).fst ∉ A₁}) (not_not_intro hm), zero_mul, add_zero]
    ring
  · rw [goodTerm, badCoeff, indicator_of_notMem (s := {m : ZLattice.dual L |
      -(m : WithLp 2 (E × D)).fst ∈ A₁}) hm, indicator_of_mem (s := {m : ZLattice.dual L |
      -(m : WithLp 2 (E × D)).fst ∉ A₁}) hm, zero_add]
    ring

/-! ### Estimates for the two parts -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- The bounds of `exists_bound_of_offRegions` at `n = -m`. -/
private theorem bound_neg {f : WithLp 2 (E × D) → ℂ} {g : D → ℂ} {ζ : WithLp 2 (E × D)} {N P : ℕ}
    {B : ℝ} (m : WithLp 2 (E × D))
    (h : (1 + ‖ζ‖) ^ N * ((1 + ‖-m‖) ^ P * ‖f (ζ - -m) * g (-m).snd‖) ≤ B) :
    (1 + ‖ζ‖) ^ N * ((1 + ‖m‖) ^ P * ‖f (ζ + m) * g (-m.snd)‖) ≤ B := by
  simpa only [norm_neg, sub_neg_eq_add, WithLp.neg_snd] using h

/-- **A term with `-m.fst ∈ A₁`.** If the weighted products of `f` and `g` are bounded by
`C (1 + ‖n.fst‖) ^ K` and `h` decays to order `K` on `A₁` with constant `σ`, then the term of index
`m` is at most `‖(covolume L)⁻¹‖ C σ (1 + ‖ζ‖)⁻ᴺ (1 + ‖m‖)⁻ᵠ`. -/
private theorem norm_goodTerm_le {f : WithLp 2 (E × D) → ℂ} {h : E → ℂ} {g : D → ℂ}
    {ζ : WithLp 2 (E × D)} {N q K : ℕ} {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hfg : ∀ n : WithLp 2 (E × D),
      (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ q * ‖f (ζ - n) * g n.snd‖) ≤ C * (1 + ‖n.fst‖) ^ K)
    (hh : ∀ a ∈ A₁, (1 + ‖a‖) ^ K * ‖h a‖ ≤ σ) (m : ZLattice.dual L) :
    ‖goodTerm L A₁ f h g ζ m‖ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C * σ * ((1 + ‖ζ‖) ^ N)⁻¹ *
      ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  by_cases hm : -(m : WithLp 2 (E × D)).fst ∈ A₁
  · rw [goodTerm, indicator_of_mem
      (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)).fst ∈ A₁}) hm, norm_mul, norm_mul]
    have H := bound_neg (m : WithLp 2 (E × D)) (hfg (-(m : WithLp 2 (E × D))))
    have Hh := hh _ hm
    rw [WithLp.neg_fst, norm_neg] at H
    rw [norm_neg] at Hh
    have hW : 0 < (1 + ‖ζ‖) ^ N * (1 + ‖(m : WithLp 2 (E × D))‖) ^ q := by positivity
    have key : ‖f (ζ + ↑m) * g (-(m : WithLp 2 (E × D)).snd)‖ * ‖h (-(m : WithLp 2 (E × D)).fst)‖ *
        ((1 + ‖ζ‖) ^ N * (1 + ‖(m : WithLp 2 (E × D))‖) ^ q) ≤ C * σ :=
      calc _ = ((1 + ‖ζ‖) ^ N * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q *
            ‖f (ζ + ↑m) * g (-(m : WithLp 2 (E × D)).snd)‖)) *
              ‖h (-(m : WithLp 2 (E × D)).fst)‖ := by ring
        _ ≤ (C * (1 + ‖(m : WithLp 2 (E × D)).fst‖) ^ K) *
              ‖h (-(m : WithLp 2 (E × D)).fst)‖ := by gcongr
        _ = C * ((1 + ‖(m : WithLp 2 (E × D)).fst‖) ^ K * ‖h (-(m : WithLp 2 (E × D)).fst)‖) := by
            ring
        _ ≤ C * σ := by gcongr
    have key' : ‖f (ζ + ↑m) * g (-(m : WithLp 2 (E × D)).snd)‖ *
        ‖h (-(m : WithLp 2 (E × D)).fst)‖ ≤
          C * σ * ((1 + ‖ζ‖) ^ N)⁻¹ * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
      rw [mul_assoc (C * σ), ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ hW]
      exact key
    calc _ ≤ ‖a‖ * (C * σ * ((1 + ‖ζ‖) ^ N)⁻¹ * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹) := by
          gcongr
      _ = _ := by ring
  · rw [goodTerm, indicator_of_notMem
      (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)).fst ∈ A₁}) hm, norm_zero]
    positivity

/-- **The terms with `-m.fst ∈ A₁`.** Under the hypotheses of `norm_goodTerm_le`, the sum of
these terms decays to order `N` in `ζ`. -/
private theorem one_add_norm_pow_mul_norm_tsum_goodTerm_le {f : WithLp 2 (E × D) → ℂ}
    {h : E → ℂ} {g : D → ℂ} {ζ : WithLp 2 (E × D)} {N q K : ℕ} {C σ : ℝ} (hC : 0 ≤ C)
    (hσ : 0 ≤ σ)
    (hfg : ∀ n : WithLp 2 (E × D),
      (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ q * ‖f (ζ - n) * g n.snd‖) ≤ C * (1 + ‖n.fst‖) ^ K)
    (hh : ∀ a ∈ A₁, (1 + ‖a‖) ^ K * ‖h a‖ ≤ σ)
    (hq : Summable fun m : ZLattice.dual L ↦ ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹) :
    Summable (goodTerm L A₁ f h g ζ) ∧
      (1 + ‖ζ‖) ^ N * ‖∑' m, goodTerm L A₁ f h g ζ m‖ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C * σ *
        ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
  have hle := norm_goodTerm_le (L := L) hC hσ hfg hh
  refine ⟨Summable.of_norm_bounded (hq.mul_left _) hle, ?_⟩
  calc (1 + ‖ζ‖) ^ N * ‖∑' m, goodTerm L A₁ f h g ζ m‖
      ≤ (1 + ‖ζ‖) ^ N * (‖(ZLattice.covolume L : ℂ)⁻¹‖ * C * σ * ((1 + ‖ζ‖) ^ N)⁻¹ *
          ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹) := by
        gcongr
        exact tsum_of_norm_bounded (hq.hasSum.mul_left _) hle
    _ = _ := by field_simp

/-- **A coefficient with `-m.fst ∉ A₁`.** If the weighted products of `f` and `g` are bounded by
`C` for `n.fst ∉ A₁`, then `(1 + ‖ζ‖) ^ N ‖badCoeff m‖ (1 + ‖m‖) ^ P ≤ ‖(covolume L)⁻¹‖ C`. -/
private theorem one_add_pow_mul_norm_badCoeff_le {f : WithLp 2 (E × D) → ℂ} {g : D → ℂ}
    {ζ : WithLp 2 (E × D)} {N P : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ n : WithLp 2 (E × D), n.fst ∉ A₁ →
      (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ C) (m : ZLattice.dual L) :
    (1 + ‖ζ‖) ^ N * ‖badCoeff L A₁ f g ζ m‖ * (1 + ‖(m : WithLp 2 (E × D))‖) ^ P ≤
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C := by
  by_cases hm : -(m : WithLp 2 (E × D)).fst ∈ A₁
  · rw [badCoeff, indicator_of_notMem
      (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)).fst ∉ A₁}) (by simpa using hm),
      norm_zero, mul_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) hC
  · rw [badCoeff, indicator_of_mem
      (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)).fst ∉ A₁}) hm, norm_mul]
    have H := bound_neg (m : WithLp 2 (E × D))
      (hfg (-(m : WithLp 2 (E × D))) (by rwa [WithLp.neg_fst]))
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left H (norm_nonneg _))
    ring

/-- A coefficient with `-m.fst ∉ A₁` depends continuously on `ζ` when `f` is continuous. -/
private theorem continuous_badCoeff {f : WithLp 2 (E × D) → ℂ} (hf : Continuous f) (g : D → ℂ)
    (m : ZLattice.dual L) : Continuous fun ζ ↦ badCoeff L A₁ f g ζ m := by
  by_cases hm : -(m : WithLp 2 (E × D)).fst ∈ A₁
  · simp only [badCoeff, indicator_of_notMem
      (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)).fst ∉ A₁}) (by simpa using hm)]
    exact continuous_const
  · simp only [badCoeff, indicator_of_mem
      (s := {m : ZLattice.dual L | -(m : WithLp 2 (E × D)).fst ∉ A₁}) hm]
    fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
/-- The derivatives of the modulated cutoff grow at most polynomially in the modulation. -/
private theorem seminorm_modulate_fst_le {Ω : Opens E} (χ₁ : 𝓓(Ω, ℂ)) (k : ℕ)
    (m : WithLp 2 (E × D)) :
    N[ℂ]_{⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩, k}
        (χ₁.toSupportedInTSupport.modulate m.fst) ≤
      ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ ⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩ k
        χ₁.toSupportedInTSupport * (1 + 2 * π) ^ k * (1 + ‖m‖) ^ k := by
  have hfst := WithLp.norm_fst_le (x := m)
  calc _ ≤ ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ ⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩
        k χ₁.toSupportedInTSupport * (1 + 2 * π * ‖m.fst‖) ^ k :=
        ContDiffMapSupportedIn.seminorm_modulate_le _ _ k
    _ ≤ ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ ⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩
        k χ₁.toSupportedInTSupport * ((1 + 2 * π) * (1 + ‖m‖)) ^ k := by
        gcongr
        nlinarith [Real.pi_pos, norm_nonneg m]
    _ = _ := by rw [mul_pow, mul_assoc]

/-- **The terms of the series off `A₁`, weighted.** If the weighted products of `f` and `g` are
bounded by `C` to order `q + k` in `n` for `n.fst ∉ A₁`, then the products of the weighted
coefficients with the `k`-th seminorms of the modulated cutoffs are bounded by a constant times
`(1 + ‖m‖)⁻ᵠ`. -/
private theorem one_add_pow_mul_norm_badCoeff_mul_seminorm_le {Ω : Opens E} (χ₁ : 𝓓(Ω, ℂ))
    {f : WithLp 2 (E × D) → ℂ} {g : D → ℂ} {ζ : WithLp 2 (E × D)} {N q k : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hfg : ∀ n : WithLp 2 (E × D), n.fst ∉ A₁ →
      (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ (q + k) * ‖f (ζ - n) * g n.snd‖) ≤ C) (m : ZLattice.dual L) :
    (1 + ‖ζ‖) ^ N * ‖badCoeff L A₁ f g ζ m‖ *
        N[ℂ]_{⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩, k}
          (χ₁.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)).fst) ≤
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C * (ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤
        ⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩ k χ₁.toSupportedInTSupport *
          (1 + 2 * π) ^ k) * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
  set Sk := ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤
    ⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩ k χ₁.toSupportedInTSupport
  have _hSk : 0 ≤ Sk := apply_nonneg _ _
  have h := one_add_pow_mul_norm_badCoeff_le (L := L) (A₁ := A₁) (P := q + k) hC hfg m
  rw [pow_add] at h
  have hmod := seminorm_modulate_fst_le χ₁ k (m : WithLp 2 (E × D))
  rw [le_mul_inv_iff₀ (by positivity)]
  calc (1 + ‖ζ‖) ^ N * ‖badCoeff L A₁ f g ζ m‖ *
        N[ℂ]_{⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩, k}
          (χ₁.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)).fst) *
          (1 + ‖(m : WithLp 2 (E × D))‖) ^ q
      ≤ (1 + ‖ζ‖) ^ N * ‖badCoeff L A₁ f g ζ m‖ *
          (Sk * (1 + 2 * π) ^ k * (1 + ‖(m : WithLp 2 (E × D))‖) ^ k) *
          (1 + ‖(m : WithLp 2 (E × D))‖) ^ q := by gcongr
    _ = (1 + ‖ζ‖) ^ N * ‖badCoeff L A₁ f g ζ m‖ *
          ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q * (1 + ‖(m : WithLp 2 (E × D))‖) ^ k) *
            (Sk * (1 + 2 * π) ^ k) := by ring
    _ ≤ _ := by gcongr

/-- The series of the modulated cutoffs with the coefficients off `A₁` converges in `𝓓_K`. -/
private theorem summable_badCoeff_smul_modulate [DiscreteTopology L] [IsZLattice ℝ L]
    {Ω : Opens E} (χ₁ : 𝓓(Ω, ℂ)) {f : WithLp 2 (E × D) → ℂ} {g : D → ℂ}
    {ζ : WithLp 2 (E × D)} {N : ℕ}
    (hfg : ∀ P : ℕ, ∃ C, ∀ n : WithLp 2 (E × D), n.fst ∉ A₁ →
      (1 + ‖ζ‖) ^ N * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ C) :
    Summable fun m ↦ badCoeff L A₁ f g ζ m •
      χ₁.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)).fst := by
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  choose C hC using hfg
  have hζ : 0 < (1 + ‖ζ‖) ^ N := by positivity
  set b : ℕ → ZLattice.dual L → ℝ := fun k m ↦
    ‖(ZLattice.covolume L : ℂ)⁻¹‖ * max (C (q + k)) 0 * (ContDiffMapSupportedIn.supSeminorm ℂ E
      ℂ ⊤ ⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩ k χ₁.toSupportedInTSupport *
        (1 + 2 * π) ^ k) * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ / (1 + ‖ζ‖) ^ N
  have hb (k : ℕ) : Summable (b k) := (hq.mul_left _).div_const _
  refine ContDiffMapSupportedIn.summable_smul_of_le hb fun k m ↦ ?_
  have h := one_add_pow_mul_norm_badCoeff_mul_seminorm_le (A₁ := A₁) χ₁
    (le_max_right (C (q + k)) 0) (fun n hn ↦ (hC (q + k) n hn).trans (le_max_left _ _)) m
  rw [le_div_iff₀ hζ]
  linarith

/-- **The coefficients off `A₁` tend to zero.** Weighted by `(1 + ‖ζ‖) ^ N`, the coefficients
with `-m.fst ∉ A₁` still decay like `(1 + ‖ζ‖)⁻¹` along the cone `Λ`, when the weighted products
of `f` and `g` are bounded to order `N + 1` in `ζ`. -/
private theorem tendsto_one_add_pow_mul_badCoeff {Λ : Set (WithLp 2 (E × D))} (hΛ : IsClosed Λ)
    {f : WithLp 2 (E × D) → ℂ} {g : D → ℂ} {N : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ ζ ∈ Λ, ∀ n : WithLp 2 (E × D), n.fst ∉ A₁ →
      (1 + ‖ζ‖) ^ (N + 1) * ((1 + ‖n‖) ^ 0 * ‖f (ζ - n) * g n.snd‖) ≤ C)
    (m : ZLattice.dual L) :
    Tendsto (fun ζ : Λ ↦ (((1 + ‖(ζ : WithLp 2 (E × D))‖) ^ N : ℝ) : ℂ) *
      badCoeff L A₁ f g ζ m) (cocompact Λ) (𝓝 0) := by
  have hnormV : Tendsto (fun ζ : Λ ↦ ‖(ζ : WithLp 2 (E × D))‖) (cocompact Λ) atTop :=
    tendsto_norm_cocompact_atTop.comp hΛ.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hinv := (tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left _ 1 hnormV)).const_mul (‖(ZLattice.covolume L : ℂ)⁻¹‖ * C)
  rw [mul_zero] at hinv
  refine squeeze_zero_norm (fun ζ ↦ ?_) hinv
  have hζ : 0 < 1 + ‖(ζ : WithLp 2 (E × D))‖ := by positivity
  have h := one_add_pow_mul_norm_badCoeff_le (L := L) hC (hfg ζ ζ.property) m
  rw [pow_zero, mul_one, pow_succ] at h
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Function.comp_apply,
    le_mul_inv_iff₀ hζ]
  linarith

/-- **The weighted Fourier series of the terms with `-m.fst ∉ A₁` form a compact set.** If the
weighted products of a continuous `f` and of `g` are bounded for `n.fst ∉ A₁`, to every order in
`n` and in `ζ ∈ Λ`, then the series of the modulated cutoffs with the
coefficients of these terms weighted by `(1 + ‖ζ‖) ^ N` depend continuously on `ζ ∈ Λ` and tend to
zero at infinity, so together with `0` they form a compact set. -/
private theorem isCompact_insert_range_tsum [DiscreteTopology L] [IsZLattice ℝ L]
    {Λ : Set (WithLp 2 (E × D))} (hΛ : IsClosed Λ) {Ω : Opens E} (χ₁ : 𝓓(Ω, ℂ))
    {f : WithLp 2 (E × D) → ℂ} (hf : Continuous f) {g : D → ℂ} (N : ℕ)
    (hfg : ∀ N' P : ℕ, ∃ C, ∀ ζ ∈ Λ, ∀ n : WithLp 2 (E × D), n.fst ∉ A₁ →
      (1 + ‖ζ‖) ^ N' * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ C) :
    IsCompact (insert 0 (range fun ζ : Λ ↦ ∑' m : ZLattice.dual L,
      ((((1 + ‖(ζ : WithLp 2 (E × D))‖) ^ N : ℝ) : ℂ) * badCoeff L A₁ f g ζ m) •
        χ₁.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)).fst)) := by
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  set K : Compacts E := ⟨tsupport χ₁, χ₁.hasCompactSupport.isCompact⟩
  set a := ‖(ZLattice.covolume L : ℂ)⁻¹‖
  choose C hC using hfg
  set Sk : ℕ → ℝ := fun k ↦
    ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ₁.toSupportedInTSupport
  set b : ℕ → ZLattice.dual L → ℝ := fun k m ↦
    a * max (C N (q + k)) 0 * (Sk k * (1 + 2 * π) ^ k) * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹
  have hb (k : ℕ) : Summable (b k) := hq.mul_left _
  set c : Λ → ZLattice.dual L → ℂ := fun ζ m ↦
    (((1 + ‖(ζ : WithLp 2 (E × D))‖) ^ N : ℝ) : ℂ) * badCoeff L A₁ f g ζ m
  have hbound (ζ : Λ) (k : ℕ) (m : ZLattice.dual L) :
      ‖c ζ m‖ * N[ℂ]_{K, k} (χ₁.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)).fst) ≤
        b k m := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact one_add_pow_mul_norm_badCoeff_mul_seminorm_le χ₁ (le_max_right _ _)
      (fun n hn ↦ (hC N (q + k) ζ ζ.property n hn).trans (le_max_left _ _)) m
  -- Each coefficient is continuous in `ζ`.
  have hcont (m : ZLattice.dual L) : Continuous fun ζ : Λ ↦ c ζ m :=
    (Complex.continuous_ofReal.comp ((continuous_const.add
      (continuous_norm.comp continuous_subtypeVal)).pow N)).mul
        ((continuous_badCoeff hf g m).comp continuous_subtypeVal)
  -- Each coefficient tends to zero at infinity in `Λ`, by the bound of order `N + 1`.
  have hlim (m : ZLattice.dual L) : Tendsto (fun ζ : Λ ↦ c ζ m) (cocompact Λ) (𝓝 0) :=
    tendsto_one_add_pow_mul_badCoeff hΛ (le_max_right (C (N + 1) 0) 0)
      (fun ζ hζ n hn ↦ (hC (N + 1) 0 ζ hζ n hn).trans (le_max_left _ _)) m
  exact ContDiffMapSupportedIn.isCompact_insert_range_tsum_smul hb hbound hcont hlim

/-! ### The seminorms of the tensor product -/

variable {Γ₁ : Set (E × E)}

omit [FiniteDimensional ℝ E] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- Combining the bounds on the two parts of the lattice series: the weight `w ≥ 0` of the pairing
of `S` with a series in `𝓓_K` moves into the coefficients of the series. -/
private theorem mul_norm_add_complexPairing_tsum_le (S : 𝓓'(Ω, ℂ)) {K : Compacts E}
    (hK : (K : Set E) ⊆ Ω) {ι : Type*} {c : ι → ℂ} {v : ι → 𝓓_{K}(E, ℂ)} {w : ℝ} (hw : 0 ≤ w)
    (hc : Summable fun m ↦ c m • v m) {G : ℂ} {A B : ℝ} (hG : w * ‖G‖ ≤ A)
    (hS : ‖S.complexPairing (ofSupportedIn hK (∑' m, ((w : ℂ) * c m) • v m))‖ ≤ B) :
    w * ‖G + S.complexPairing (ofSupportedIn hK (∑' m, c m • v m))‖ ≤ A + B := by
  calc w * ‖G + S.complexPairing (ofSupportedIn hK (∑' m, c m • v m))‖
      ≤ w * ‖G‖ + w * ‖S.complexPairing (ofSupportedIn hK (∑' m, c m • v m))‖ := by
        rw [← mul_add]
        gcongr
        exact norm_add_le _ _
    _ ≤ A + B := add_le_add hG (mul_norm_complexPairing_tsum_smul S hK hw hc ▸ hS)

/-- **The seminorm estimate for a product cutoff.** Let `χ (x, y) = χ₁ x χ₂ y` be equal to one on
the support of `φ`, let `A₁` and `A₂` be closed cones avoiding `Γ₁` over `tsupport χ₁` and
`WF(T)` over `tsupport χ₂`, and let every covector off the two regions of `offRegions A₁ A₂ c` be
far from the closed cone `Λ`. Then `(1 + ‖ζ‖) ^ N ‖(S ⊗ T) (φ e_ζ)‖ ≤ p S` for `ζ ∈ Λ` and a
continuous seminorm `p` of `𝓓'_{Γ₁}(Ω)`. -/
private theorem exists_seminorm_localFourier_tensorProduct_le_of_cutoff (T : 𝓓'(O, ℂ))
    {χ₁ : 𝓓(Ω, ℂ)} {χ₂ : 𝓓(O, ℂ)} {χ : 𝓓(W, ℂ)} (hχ : ∀ p, χ p = χ₁ p.fst * χ₂ p.snd)
    {A₁ : Set E} {A₂ : Set D} (hA₁ : IsClosed A₁) (hA₁c : ∀ t : ℝ, 0 < t → ∀ a ∈ A₁, t • a ∈ A₁)
    (hA₂ : IsClosed A₂) (hA₂c : ∀ t : ℝ, 0 < t → ∀ a ∈ A₂, t • a ∈ A₂)
    (hχ₁Γ : Disjoint (tsupport χ₁ ×ˢ A₁) Γ₁) (hχ₂T : Disjoint (tsupport χ₂ ×ˢ A₂) T.waveFrontSet)
    {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hκ1 : κ ≤ 1) {Λ : Set (WithLp 2 (E × D))}
    (hΛ : IsClosed Λ)
    (hsep : ∀ ζ ∈ Λ, ∀ n, offRegions A₁ A₂ c n → κ * (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖) {φ : 𝓓(W, ℂ)}
    (hφ : EqOn (χ : WithLp 2 (E × D) → ℂ) 1 (support φ)) (N : ℕ) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω Γ₁), Continuous p ∧ ∀ u : WaveFrontSpace Ω Γ₁,
      ∀ ζ ∈ Λ, (1 + ‖ζ‖) ^ N * ‖(transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (u.toDistribution.tensorProduct T hV.subset)).localFourier φ ζ‖ ≤ p u := by
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  set f : WithLp 2 (E × D) → ℂ := 𝓕 (φ : WithLp 2 (E × D) → ℂ)
  set g : D → ℂ := T.localFourier χ₂
  have hf : ∀ M : ℕ, ∃ B, ∀ v, (1 + ‖v‖) ^ M * ‖f v‖ ≤ B :=
    exists_one_add_norm_pow_mul_norm_fourier_le φ.contDiff φ.hasCompactSupport
  have hfc : Continuous f :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).continuous_fourier
  have hgA (M : ℕ) : ∃ C, ∀ b ∈ A₂, (1 + ‖b‖) ^ M * ‖g b‖ ≤ C :=
    (exists_forall_one_add_norm_pow_mul_norm_localFourier_le_of_disjoint hA₂ hA₂c hχ₂T M).imp
      fun _ hC ↦ hC.2
  have hbound := exists_bound_of_offRegions hc hκ hκ1 hsep hf (exists_norm_localFourier_le T χ₂)
    hgA
  obtain ⟨C, K, hCK⟩ := hbound N q
  -- The seminorm `‖S‖_{χ₁,A₁,K}` controls the terms with `-m.fst ∈ A₁`.
  set i : WaveFrontSeminormIndex Ω Γ₁ := ⟨χ₁, A₁, K, hA₁, hA₁c, hχ₁Γ⟩
  -- The terms with `-m.fst ∉ A₁` pair `S` with the members of a compact set.
  have hbad (N' : ℕ) (P : ℕ) : ∃ C, ∀ ζ ∈ Λ, ∀ n : WithLp 2 (E × D), n.fst ∉ A₁ →
      (1 + ‖ζ‖) ^ N' * ((1 + ‖n‖) ^ P * ‖f (ζ - n) * g n.snd‖) ≤ C :=
    let ⟨C, _, h⟩ := hbound N' P
    ⟨C, fun ζ hζ n hn ↦ (h ζ hζ n).2 hn⟩
  have hQ := isCompact_insert_range_tsum (L := L) (A₁ := A₁) hΛ χ₁ hfc (g := g) N hbad
  obtain ⟨p', hp', hp'le⟩ :=
    WaveFrontSpace.exists_continuous_seminorm_norm_complexPairing_le (Γ := Γ₁)
    (hQ.image (continuous_ofSupportedIn χ₁.tsupport_subset))
  set K₀ : ℝ := ‖(ZLattice.covolume L : ℂ)⁻¹‖ * max C 0 *
    ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ with hK₀def
  have hK₀ : 0 ≤ K₀ := by positivity
  refine ⟨K₀.toNNReal • WaveFrontSpace.seminorm i + p',
    ((WaveFrontSpace.continuous_seminorm i).const_smul _).add hp', fun u ζ hζ ↦ ?_⟩
  set S := u.toDistribution
  obtain ⟨hgood, hgoodle⟩ := one_add_norm_pow_mul_norm_tsum_goodTerm_le (L := L) (A₁ := A₁)
    (h := S.localFourier χ₁) (le_max_right C 0) (apply_nonneg _ u)
    (fun n ↦ (hCK ζ hζ n).1.trans (by gcongr; exact le_max_left _ _))
    (fun a ha ↦ WaveFrontSpace.le_seminorm i u ha) hq
  have hsum := summable_badCoeff_smul_modulate (L := L) (A₁ := A₁) χ₁ (N := N)
    fun P ↦ (hbad N P).imp fun _ h n hn ↦ h ζ hζ n hn
  rw [localFourier_tensorProduct_eq_add hV hW S T hχ hL hφ ζ hgood hsum]
  -- The terms off `A₁`: the weighted series lies in the compact set `hQ`.
  have hbadle := hp'le u (ofSupportedIn χ₁.tsupport_subset (∑' m : ZLattice.dual L,
      ((((1 + ‖ζ‖) ^ N : ℝ) : ℂ) * badCoeff L A₁ f g ζ m) •
        χ₁.toSupportedInTSupport.modulate (m : WithLp 2 (E × D)).fst))
    (mem_image_of_mem _ (mem_insert_of_mem _ ⟨⟨ζ, hζ⟩, rfl⟩))
  refine (mul_norm_add_complexPairing_tsum_le S χ₁.tsupport_subset (by positivity) hsum
    (A := K₀ * WaveFrontSpace.seminorm i u) (hgoodle.trans_eq (by rw [hK₀def]; ring))
    hbadle).trans_eq ?_
  simp [NNReal.smul_def, Real.coe_toNNReal _ hK₀]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
include hV hW in
/-- **The cutoffs at a point.** Around a point `p₀` of `W` over which no direction of the closed
cone `Λ` lies in `Γ₁ ⊠ Γ₂`, there are a neighbourhood `G` of `p₀` and a product cutoff
`χ (x, y) = χ₁ x χ₂ y` equal to one on `G`, with the cone data of `exists_cone_data` holding over
the supports of `χ₁` and `χ₂`. -/
private theorem exists_nhds_cutoff {Γ₂ : Set (D × D)}
    (hΓ₁ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ₁))
    (hcone₁ : ∀ p ∈ Γ₁, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₁) (hΓ₁0 : ∀ p ∈ Γ₁, p.2 ≠ 0)
    (hΓ₂ : IsOpen (((O : Set D) ×ˢ {0}ᶜ) \ Γ₂))
    (hcone₂ : ∀ p ∈ Γ₂, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₂) (hΓ₂0 : ∀ p ∈ Γ₂, p.2 ≠ 0)
    {p₀ : WithLp 2 (E × D)} (hp₀ : p₀ ∈ W) {Λ : Set (WithLp 2 (E × D))} (hΛ : IsClosed Λ)
    (hΛc : ∀ t : ℝ, 0 < t → ∀ ζ ∈ Λ, t • ζ ∈ Λ) (hΛΓ : ∀ ζ ∈ Λ, (p₀, ζ) ∉ tensorCone Γ₁ Γ₂) :
    ∃ G ∈ 𝓝 p₀, ∃ (χ₁ : 𝓓(Ω, ℂ)) (χ₂ : 𝓓(O, ℂ)) (χ : 𝓓(W, ℂ)),
      (∀ p, χ p = χ₁ p.fst * χ₂ p.snd) ∧ EqOn (χ : WithLp 2 (E × D) → ℂ) 1 G ∧
      ∃ (A₁ : Set E) (A₂ : Set D), IsClosed A₁ ∧ (∀ t : ℝ, 0 < t → ∀ a ∈ A₁, t • a ∈ A₁) ∧
        IsClosed A₂ ∧ (∀ t : ℝ, 0 < t → ∀ a ∈ A₂, t • a ∈ A₂) ∧
        Disjoint (tsupport χ₁ ×ˢ A₁) Γ₁ ∧ Disjoint (tsupport χ₂ ×ˢ A₂) Γ₂ ∧
        ∃ c > 0, ∃ κ > 0, κ ≤ 1 ∧ ∀ ζ ∈ Λ, ∀ n,
          offRegions A₁ A₂ c n → κ * (‖ζ‖ + ‖n‖) ≤ ‖ζ - n‖ := by
  have hp₀' : p₀.fst ∈ Ω ∧ p₀.snd ∈ O := by simpa [hV] using hW hp₀
  obtain ⟨U₁, hU₁, U₂, hU₂, A₁, A₂, hA₁, hA₁c, hA₂, hA₂c, hU₁Γ, hU₂Γ, c, hc, κ, hκ, hκ1, hsep⟩ :=
    exists_cone_data hΓ₁ hcone₁ hΓ₁0 hΓ₂ hcone₂ hΓ₂0 hp₀' hΛ hΛc hΛΓ
  obtain ⟨B₁, hB₁, B₂, hB₂, hprod⟩ := exists_nhds_prod_cutoff (Ω := Ω) (O := O) hp₀
  obtain ⟨χ₁, G₁, hG₁, hpG₁, hχ₁1, hχ₁s⟩ :=
    exists_eqOn_one_tsupport_subset (n := ⊤) (𝕜 := ℂ) (inter_mem hU₁ hB₁) hp₀'.1
  obtain ⟨χ₂, G₂, hG₂, hpG₂, hχ₂1, hχ₂s⟩ :=
    exists_eqOn_one_tsupport_subset (n := ⊤) (𝕜 := ℂ) (inter_mem hU₂ hB₂) hp₀'.2
  obtain ⟨χ, hχ, -⟩ := hprod χ₁ χ₂ (hχ₁s.trans inter_subset_right)
    (hχ₂s.trans inter_subset_right)
  refine ⟨WithLp.fst ⁻¹' G₁ ∩ WithLp.snd ⁻¹' G₂, ?_, χ₁, χ₂, χ, hχ, fun p hp ↦ ?_, A₁, A₂, hA₁,
    hA₁c, hA₂, hA₂c, hU₁Γ.mono_left (prod_mono (hχ₁s.trans inter_subset_left) subset_rfl),
    hU₂Γ.mono_left (prod_mono (hχ₂s.trans inter_subset_left) subset_rfl), c, hc, κ, hκ, hκ1,
    hsep⟩
  · exact ((hG₁.preimage (by fun_prop)).inter (hG₂.preimage (by fun_prop))).mem_nhds ⟨hpG₁, hpG₂⟩
  · rw [hχ, hχ₁1 hp.1, hχ₂1 hp.2]
    simp

/-- **The seminorms of the tensor product near a point.** Around a point `p₀` of `W` over which
no direction of the closed cone `Λ` lies in `Γ₁ ⊠ Γ₂`, every cutoff `φ` supported close enough to
`p₀` gives the estimate `(1 + ‖ζ‖) ^ N ‖(S ⊗ T) (φ e_ζ)‖ ≤ p S` for `ζ ∈ Λ` and a continuous
seminorm `p` of `𝓓'_{Γ₁}(Ω)`. -/
private theorem exists_nhds_forall_seminorm_localFourier_tensorProduct_le {Γ₂ : Set (D × D)}
    (hΓ₁ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ₁))
    (hcone₁ : ∀ p ∈ Γ₁, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₁) (hΓ₁0 : ∀ p ∈ Γ₁, p.2 ≠ 0)
    (hΓ₂ : IsOpen (((O : Set D) ×ˢ {0}ᶜ) \ Γ₂))
    (hcone₂ : ∀ p ∈ Γ₂, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₂) (hΓ₂0 : ∀ p ∈ Γ₂, p.2 ≠ 0)
    (T : 𝓓'(O, ℂ)) (hT : T.waveFrontSet ⊆ Γ₂) {p₀ : WithLp 2 (E × D)} (hp₀ : p₀ ∈ W)
    {Λ : Set (WithLp 2 (E × D))} (hΛ : IsClosed Λ) (hΛc : ∀ t : ℝ, 0 < t → ∀ ζ ∈ Λ, t • ζ ∈ Λ)
    (hΛΓ : ∀ ζ ∈ Λ, (p₀, ζ) ∉ tensorCone Γ₁ Γ₂) (N : ℕ) :
    ∃ G ∈ 𝓝 p₀, ∀ φ : 𝓓(W, ℂ), tsupport φ ⊆ G →
      ∃ p : Seminorm ℂ (WaveFrontSpace Ω Γ₁), Continuous p ∧ ∀ u : WaveFrontSpace Ω Γ₁,
        ∀ ζ ∈ Λ, (1 + ‖ζ‖) ^ N * ‖(transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
          (u.toDistribution.tensorProduct T hV.subset)).localFourier φ ζ‖ ≤ p u := by
  obtain ⟨G, hG, χ₁, χ₂, χ, hχ, hχG, A₁, A₂, hA₁, hA₁c, hA₂, hA₂c, hχ₁Γ, hχ₂Γ, c, hc, κ, hκ, hκ1,
    hsep⟩ := exists_nhds_cutoff hV hW hΓ₁ hcone₁ hΓ₁0 hΓ₂ hcone₂ hΓ₂0 hp₀ hΛ hΛc hΛΓ
  exact ⟨G, hG, fun φ hφ ↦ exists_seminorm_localFourier_tensorProduct_le_of_cutoff hV hW T hχ hA₁
    hA₁c hA₂ hA₂c hχ₁Γ (hχ₂Γ.mono_right hT) hc hκ hκ1 hΛ hsep
    (fun p hp ↦ hχG (hφ (subset_tsupport _ hp))) N⟩

/-- **The seminorms of the tensor product.** For the data `(φ, Λ, N)` of a seminorm of
`𝓓'_{Γ₁ ⊠ Γ₂}(W)`, the estimate `(1 + ‖ζ‖) ^ N ‖(S ⊗ T) (φ e_ζ)‖ ≤ p S` holds on `Λ` for a
continuous seminorm `p` of `𝓓'_{Γ₁}(Ω)`: cut `φ` into pieces supported near single points with a
partition of unity, and apply `exists_nhds_forall_seminorm_localFourier_tensorProduct_le`. -/
private theorem exists_seminorm_localFourier_tensorProduct_le {Γ₂ : Set (D × D)}
    (hΓ₁ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ₁))
    (hcone₁ : ∀ p ∈ Γ₁, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₁) (hΓ₁0 : ∀ p ∈ Γ₁, p.2 ≠ 0)
    (hΓ₂ : IsOpen (((O : Set D) ×ˢ {0}ᶜ) \ Γ₂))
    (hcone₂ : ∀ p ∈ Γ₂, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₂) (hΓ₂0 : ∀ p ∈ Γ₂, p.2 ≠ 0)
    (T : 𝓓'(O, ℂ)) (hT : T.waveFrontSet ⊆ Γ₂) (j : WaveFrontSeminormIndex W (tensorCone Γ₁ Γ₂)) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω Γ₁), Continuous p ∧ ∀ u : WaveFrontSpace Ω Γ₁,
      ∀ ζ ∈ j.cone, (1 + ‖ζ‖) ^ j.order * ‖(transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (u.toDistribution.tensorProduct T hV.subset)).localFourier j.cutoff ζ‖ ≤ p u := by
  have hloc (p₀ : tsupport j.cutoff) := exists_nhds_forall_seminorm_localFourier_tensorProduct_le
    hV hW hΓ₁ hcone₁ hΓ₁0 hΓ₂ hcone₂ hΓ₂0 T hT (j.cutoff.tsupport_subset p₀.property)
    j.isClosed_cone j.smul_mem_cone
    (fun ζ hζ hmem ↦ disjoint_left.1 j.disjoint (mk_mem_prod p₀.property hζ) hmem)
    j.order
  choose G hG hGφ using hloc
  obtain ⟨s, ψ, hψ, hsum, -⟩ := j.cutoff.exists_sum_subordinate (fun p₀ ↦ interior (G p₀))
    (fun _ ↦ isOpen_interior)
    fun p hp ↦ mem_iUnion.2 ⟨⟨p, hp⟩, mem_interior_iff_mem_nhds.2 (hG ⟨p, hp⟩)⟩
  choose P hP hPle using fun i : s ↦ hGφ i (ψ i) ((hψ i).trans interior_subset)
  refine ⟨∑ i, P i, Seminorm.continuous_finsetSum fun i _ ↦ hP i, fun u ζ hζ ↦ ?_⟩
  -- The sum of the seminorms is evaluated termwise.
  have hcoe : (∑ i, P i) u = ∑ i, P i u := by
    rw [← FunLike.coeAddMonoidHom_apply]
    simp [map_sum, Finset.sum_apply]
  rw [hcoe]
  have hR : (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (u.toDistribution.tensorProduct T hV.subset)).localFourier j.cutoff ζ =
        ∑ i, (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
          (u.toDistribution.tensorProduct T hV.subset)).localFourier (ψ i) ζ := by
    rw [← localFourier_sum_cutoff, hsum]
  rw [hR]
  · calc (1 + ‖ζ‖) ^ j.order * ‖∑ i, (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
          (u.toDistribution.tensorProduct T hV.subset)).localFourier (ψ i) ζ‖
        ≤ ∑ i, (1 + ‖ζ‖) ^ j.order * ‖(transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
          (u.toDistribution.tensorProduct T hV.subset)).localFourier (ψ i) ζ‖ := by
          rw [← Finset.mul_sum]
          gcongr
          exact norm_sum_le _ _
      _ ≤ ∑ i, P i u := Finset.sum_le_sum fun i _ ↦ hPle i u ζ hζ

omit [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D]
  [BorelSpace D] in
/-- **The tensor product on a compact set of test functions.** For a compact set `Q` of real test
functions on `W`, the values `(S ⊗ T) ψ`, `ψ ∈ Q`, are bounded by a continuous seminorm of
`S ∈ 𝓓'_{Γ₁}(Ω)`: they are the values of `S` on the compact set of partial pairings of `T` with
the members of `Q`. -/
private theorem exists_seminorm_tensorProduct_apply_le (T : 𝓓'(O, ℂ)) {Q : Set 𝓓(W, ℝ)}
    (hQ : IsCompact Q) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω Γ₁), Continuous p ∧ ∀ u : WaveFrontSpace Ω Γ₁, ∀ ψ ∈ Q,
      ‖transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (u.toDistribution.tensorProduct T hV.subset) ψ‖ ≤ p u := by
  set P := (T.partialPairing hV.subset).comp
    ((prodContinuousLinearEquiv 2 ℝ E D).transportTestFunction ℝ hW)
  obtain ⟨p, hp, hpQ⟩ := WaveFrontSpace.exists_continuous_seminorm_norm_complexPairing_le
    (Γ := Γ₁) (hQ.image P.continuous)
  refine ⟨p, hp, fun u ψ hψ ↦ ?_⟩
  have h := hpQ u _ ⟨ψ, hψ, rfl⟩
  rwa [ContinuousLinearMap.comp_apply, ← tensorProduct_apply, ← transportCLM_apply] at h

end Lattice

/-! ### The tensor product as a continuous linear map -/

namespace WaveFrontSpace

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  {Ω : Opens E} {O : Opens D} {V : Opens (E × D)} {W : Opens (WithLp 2 (E × D))}
  (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
  (hW : MapsTo (prodContinuousLinearEquiv 2 ℝ E D) W V) {Γ₁ : Set (E × E)} {Γ₂ : Set (D × D)}

/-- The tensor product `u ↦ u ⊗ v` with a fixed `v ∈ 𝓓'_{Γ₂}(O)`, as a linear map
`𝓓'_{Γ₁}(Ω) → 𝓓'_{Γ₁ ⊠ Γ₂}(W)`, before its continuity is proved. -/
private def tensorProductRightₗ (v : WaveFrontSpace O Γ₂) :
    WaveFrontSpace Ω Γ₁ →ₗ[ℂ] WaveFrontSpace W (tensorCone Γ₁ Γ₂) where
  toFun u := mk (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (u.toDistribution.tensorProduct v.toDistribution hV.subset))
    (waveFrontSet_transportCLM_tensorProduct_subset_tensorCone _ _ hV hW
      u.waveFrontSet_toDistribution_subset v.waveFrontSet_toDistribution_subset)
  map_add' u v := ext (by simp)
  map_smul' c u := ext <| by
    ext φ
    simp [transportCLM_apply]

private theorem toDistribution_tensorProductRightₗ (v : WaveFrontSpace O Γ₂)
    (u : WaveFrontSpace Ω Γ₁) :
    (tensorProductRightₗ hV hW v u).toDistribution = transportCLM
      (prodContinuousLinearEquiv 2 ℝ E D) hW (u.toDistribution.tensorProduct v.toDistribution
        hV.subset) :=
  toDistribution_mk _ _

/-- **Continuity of the tensor product in the normal topology.** Let `Γ₁` and `Γ₂` be cones of
nonzero covectors over `Ω` and `O`, closed in `Ω × (E \ {0})` and `O × (D \ {0})`. For a fixed
`v ∈ 𝓓'_{Γ₂}(O)`, the tensor product `u ↦ u ⊗ v`, transported to the Euclidean product
`W ⊆ WithLp 2 (E × D)`, is a continuous linear map from `𝓓'_{Γ₁}(Ω)` to `𝓓'_{Γ₁ ⊠ Γ₂}(W)`, where
`Γ₁ ⊠ Γ₂` (`TauCeti.tensorCone`) consists of the nonzero covectors `((x, y), (ξ, η))` with
`ξ = 0` or `(x, ξ) ∈ Γ₁`, and `η = 0` or `(y, η) ∈ Γ₂` (Brouder, Dang and Hélein, Theorem 4.6,
continuity in the first variable). -/
def tensorProductRightCLM (hΓ₁ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ₁))
    (hcone₁ : ∀ p ∈ Γ₁, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₁) (hΓ₁0 : ∀ p ∈ Γ₁, p.2 ≠ 0)
    (hΓ₂ : IsOpen (((O : Set D) ×ˢ {0}ᶜ) \ Γ₂))
    (hcone₂ : ∀ p ∈ Γ₂, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₂) (hΓ₂0 : ∀ p ∈ Γ₂, p.2 ≠ 0)
    (v : WaveFrontSpace O Γ₂) :
    WaveFrontSpace Ω Γ₁ →L[ℂ] WaveFrontSpace W (tensorCone Γ₁ Γ₂) :=
  ⟨tensorProductRightₗ hV hW v, by
    borelize E D
    refine continuous_linearMap_of_le _ ?_ fun j ↦ ?_
    · -- Continuity into `𝓓'(W)`: the values on a compact set of test functions.
      refine continuous_of_tendsto_nhds_zero (toDistribution ∘ₗ tensorProductRightₗ hV hW v) ?_
      refine CompactConvergenceCLM.hasBasis_nhds_zero.tendsto_right_iff.2 fun ⟨Q, V'⟩ ⟨hQ, hV'⟩ ↦ ?_
      obtain ⟨r, hr, hrV'⟩ := Metric.mem_nhds_iff.1 hV'
      obtain ⟨p, hp, hpQ⟩ := exists_seminorm_tensorProduct_apply_le hV hW (Γ₁ := Γ₁)
        v.toDistribution hQ
      filter_upwards [(hp.tendsto' 0 0 (map_zero p)) (Iio_mem_nhds hr)] with u hu ψ hψ
      rw [LinearMap.coe_comp, Function.comp_apply, toDistribution_tensorProductRightₗ]
      exact hrV' (mem_ball_zero_iff.2 ((hpQ u ψ hψ).trans_lt hu))
    · -- The seminorms of the target.
      obtain ⟨p, hp, hpj⟩ := exists_seminorm_localFourier_tensorProduct_le hV hW hΓ₁ hcone₁ hΓ₁0
        hΓ₂ hcone₂ hΓ₂0 v.toDistribution v.waveFrontSet_toDistribution_subset j
      refine ⟨p, hp, fun u ↦ seminorm_le_bound j _ (apply_nonneg _ _) fun ζ hζ ↦ ?_⟩
      simpa only [toDistribution_tensorProductRightₗ] using hpj u ζ hζ⟩

@[simp]
theorem toDistribution_tensorProductRightCLM (hΓ₁ : IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ Γ₁))
    (hcone₁ : ∀ p ∈ Γ₁, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₁) (hΓ₁0 : ∀ p ∈ Γ₁, p.2 ≠ 0)
    (hΓ₂ : IsOpen (((O : Set D) ×ˢ {0}ᶜ) \ Γ₂))
    (hcone₂ : ∀ p ∈ Γ₂, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ₂) (hΓ₂0 : ∀ p ∈ Γ₂, p.2 ≠ 0)
    (v : WaveFrontSpace O Γ₂) (u : WaveFrontSpace Ω Γ₁) :
    (tensorProductRightCLM hV hW hΓ₁ hcone₁ hΓ₁0 hΓ₂ hcone₂ hΓ₂0 v u).toDistribution =
      transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (u.toDistribution.tensorProduct v.toDistribution hV.subset) :=
  toDistribution_tensorProductRightₗ hV hW v u

end WaveFrontSpace

end TauCeti
