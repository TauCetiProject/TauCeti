/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Convergence in `Cⁱ` of the slices of a smooth map

Let `f : P × E → F` be `C^i` on an open set `D` containing `{a₀} × K` for a compact `K`. Its slices
`x ↦ f (a, x)` then converge to `x ↦ f (a₀, x)` together with their first `i` derivatives,
uniformly on `K`, as `a → a₀`: the derivatives of the slices are the partial derivatives of `f`
(`ContDiffAt.iteratedFDeriv_prod_right`), which are jointly continuous, and joint continuity along
`{a₀} × K` gives uniform convergence on `K` (`IsCompact.tendstoUniformlyOn_of_continuousAt`).

The statement is phrased for a family `g a` that only agrees with the slices of `f` on `D`. This is
how it is used for rescaled families: `g a` is defined for every parameter but is a singular
expression in `a`, such as a quotient by `a`, and Hadamard's lemma rewrites it as the slice of a
map `f` that is smooth in `(a, x)` jointly, including at `a = a₀`.

If `f` has one more derivative, the convergence has rate `O(‖a - a₀‖)`: the `i`-th derivatives of
the slices are the values of a map `Φ` that is `C¹` on `D`, the derivative of `Φ` is bounded near
the compact set `{a₀} × K`, and the mean value inequality along the segment from `(a₀, x)` to
`(a, x)` bounds the difference of the slices at `x` by that bound times `‖a - a₀‖`. This is stated
over `ℝ`, where the mean value inequality holds.

## Main results

* `ContDiffOn.tendstoUniformlyOn_iteratedFDeriv_slice`: the `i`-th derivatives of `g a` converge
  uniformly on `K` to those of `x ↦ f (a₀, x)` along any filter `l ≤ 𝓝 a₀`.
* `ContDiffOn.exists_forall_norm_iteratedFDeriv_slice_sub_le`: if `f` is `C^(i+1)`, they converge
  at rate `O(‖a - a₀‖)`, uniformly on `K`.
-/

public section

open Filter Topology

namespace ContDiffOn

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Uniform convergence of the derivatives of slices.** Let `f` be `C^i` on an open set
`D ⊆ P × E` containing `{a₀} × K` for a compact `K`, and let `g a` agree with the slice
`x ↦ f (a, x)` wherever `(a, x) ∈ D`, for `a` eventually along a filter `l ≤ 𝓝 a₀`. Then the
`i`-th derivatives of `g a` converge to those of `x ↦ f (a₀, x)` uniformly on `K` along `l`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_slice {f : P × E → F} {D : Set (P × E)} {i : ℕ}
    (hf : ContDiffOn 𝕜 i f D) (hD : IsOpen D) {a₀ : P} {K : Set E} (hK : IsCompact K)
    (hKD : ∀ x ∈ K, (a₀, x) ∈ D) {l : Filter P} (hl : l ≤ 𝓝 a₀) {g : P → E → F}
    (hg : ∀ᶠ a in l, ∀ x, (a, x) ∈ D → g a x = f (a, x)) :
    TendstoUniformlyOn (fun a ↦ iteratedFDeriv 𝕜 i (g a))
      (iteratedFDeriv 𝕜 i fun x ↦ f (a₀, x)) l K := by
  -- The derivatives in `x` of the slices of `f` are jointly continuous along `{a₀} × K`.
  have hΦ : ∀ x ∈ K, ContinuousAt (Function.uncurry fun a y ↦
      iteratedFDeriv 𝕜 i (fun z ↦ f (a, z)) y) (a₀, x) := by
    intro x hx
    have hmem := hD.mem_nhds (hKD x hx)
    have hc : ContinuousAt (fun q : P × E ↦ (iteratedFDeriv 𝕜 i f q).compContinuousLinearMap
        fun _ ↦ ContinuousLinearMap.inr 𝕜 P E) (a₀, x) :=
      (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.continuousAt.comp
        ((hf.contDiffAt hmem).continuousAt_iteratedFDeriv le_rfl)
    refine hc.congr ?_
    filter_upwards [hmem] with q hq
    exact ((hf.contDiffAt (hD.mem_nhds hq)).iteratedFDeriv_prod_right i le_rfl).symm
  have h : TendstoUniformlyOn (fun a ↦ iteratedFDeriv 𝕜 i fun z ↦ f (a, z))
      (iteratedFDeriv 𝕜 i fun x ↦ f (a₀, x)) l K :=
    fun u hu ↦ hl (hK.tendstoUniformlyOn_of_continuousAt hΦ u hu)
  refine h.congr ?_
  -- Eventually `{a} × K` lies in `D`, where `g a` agrees with the slice near every point of `K`.
  filter_upwards [hl (hK.eventually_forall_of_forall_eventually
    (P := fun a x ↦ (a, x) ∈ D) fun x hx ↦ hD.mem_nhds (hKD x hx)), hg] with a haK hga x hx
  refine (EventuallyEq.iteratedFDeriv 𝕜 ?_ i).eq_of_nhds
  filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
    (hD.mem_nhds (haK x hx))] with y hy
  exact (hga y hy).symm

end NontriviallyNormedField

section Real

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The rate of convergence of the derivatives of slices.** Let `f` be `C^(i+1)` on an open set
`D ⊆ P × E` containing `{a₀} × K` for a compact `K`, and let `g a` agree with the slice
`x ↦ f (a, x)` wherever `(a, x) ∈ D`, for `a` eventually along a filter `l ≤ 𝓝 a₀`. Then there is
a constant `C` such that, for `a` eventually along `l`, the `i`-th derivatives of `g a` differ from
those of `x ↦ f (a₀, x)` by at most `C ‖a - a₀‖` at every point of `K`. -/
theorem exists_forall_norm_iteratedFDeriv_slice_sub_le {f : P × E → F} {D : Set (P × E)} {i : ℕ}
    (hf : ContDiffOn ℝ (i + 1) f D) (hD : IsOpen D) {a₀ : P} {K : Set E} (hK : IsCompact K)
    (hKD : ∀ x ∈ K, (a₀, x) ∈ D) {l : Filter P} (hl : l ≤ 𝓝 a₀) {g : P → E → F}
    (hg : ∀ᶠ a in l, ∀ x, (a, x) ∈ D → g a x = f (a, x)) :
    ∃ C, ∀ᶠ a in l, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i (g a) x - iteratedFDeriv ℝ i (fun y ↦ f (a₀, y)) x‖ ≤
        C * ‖a - a₀‖ := by
  -- The `i`-th derivatives of the slices are the values of `Φ`, which is `C¹` on `D`.
  set Φ : P × E → ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ E) F := fun q ↦
    (iteratedFDeriv ℝ i f q).compContinuousLinearMap fun _ ↦ ContinuousLinearMap.inr ℝ P E
  have hΦ : ContDiffOn ℝ 1 Φ D := fun q hq ↦
    ((ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
      fun _ : Fin i ↦ ContinuousLinearMap.inr ℝ P E).contDiff.contDiffAt.comp q
      ((hf.contDiffAt (hD.mem_nhds hq)).iteratedFDeriv_right (by rw [add_comm]))).contDiffWithinAt
  have hslice {a : P} {x : E} (hax : (a, x) ∈ D) :
      iteratedFDeriv ℝ i (fun y ↦ f (a, y)) x = Φ (a, x) :=
    (hf.contDiffAt (hD.mem_nhds hax)).iteratedFDeriv_prod_right i (by simp)
  -- The continuity of `fderiv ℝ Φ` is taken through `ContDiffOn.continuousOn`, so that it is
  -- stated for the topology of the operator norm, which is not syntactically the default topology
  -- on operators.
  have hdΦ := (hΦ.fderiv_of_isOpen hD (m := 0) (by norm_num)).continuousOn
  have hK₀ : IsCompact ({a₀} ×ˢ K) := isCompact_singleton.prod hK
  have hK₀D : {a₀} ×ˢ K ⊆ D := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    obtain rfl : a = a₀ := ha
    exact hKD x hx
  -- The derivative of `Φ` is bounded by `M + 1` on an open set `U ⊆ D` around `{a₀} × K`, which
  -- contains a box `ball a₀ ε × v` with `K ⊆ v`.
  obtain ⟨M, hM⟩ := hK₀.exists_bound_of_continuousOn (hdΦ.mono hK₀D)
  set U := D ∩ (fun q ↦ ‖fderiv ℝ Φ q‖) ⁻¹' Set.Iio (M + 1)
  have hU : IsOpen U := hdΦ.norm.isOpen_inter_preimage hD isOpen_Iio
  have hK₀U : {a₀} ×ˢ K ⊆ U := fun q hq ↦ ⟨hK₀D hq, by simpa using (hM q hq).trans_lt (by simp)⟩
  obtain ⟨u, v, hu, -, ha₀u, hKv, huvU⟩ := generalized_tube_lemma isCompact_singleton hK hU hK₀U
  obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu a₀ (ha₀u rfl)
  refine ⟨M + 1, ?_⟩
  filter_upwards [hl (Metric.ball_mem_nhds a₀ hε), hg] with a ha hga x hx
  -- Along the segment from `(a₀, x)` to `(a, x)`, which lies in `ball a₀ ε × {x} ⊆ U`, the mean
  -- value inequality bounds the increment of `Φ`.
  have hsU : Metric.ball a₀ ε ×ˢ {x} ⊆ U := fun q hq ↦
    huvU ⟨hεu hq.1, (Set.mem_singleton_iff.1 hq.2).symm ▸ hKv hx⟩
  have hs : Convex ℝ (Metric.ball a₀ ε ×ˢ {x}) := (convex_ball a₀ ε).prod (convex_singleton x)
  have hmem₀ : (a₀, x) ∈ Metric.ball a₀ ε ×ˢ {x} := ⟨Metric.mem_ball_self hε, rfl⟩
  have hmem : (a, x) ∈ Metric.ball a₀ ε ×ˢ {x} := ⟨ha, rfl⟩
  have hMVT := hs.norm_image_sub_le_of_norm_fderiv_le
    (fun q hq ↦ (hΦ.contDiffAt (hD.mem_nhds (hsU hq).1)).differentiableAt one_ne_zero)
    (fun q hq ↦ (hsU hq).2.le) hmem₀ hmem
  have hd : ‖((a, x) : P × E) - (a₀, x)‖ = ‖a - a₀‖ := by simp
  -- Near `x`, the map `g a` is the slice of `f` at `a`.
  have hax : (a, x) ∈ D := (hsU hmem).1
  have hgx : iteratedFDeriv ℝ i (g a) x = iteratedFDeriv ℝ i (fun y ↦ f (a, y)) x := by
    refine (EventuallyEq.iteratedFDeriv ℝ ?_ i).eq_of_nhds
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hD.mem_nhds hax)] with y hy
    exact hga y hy
  rw [hgx, hslice hax, hslice (hK₀D ⟨rfl, hx⟩)]
  rwa [hd] at hMVT

end Real

end ContDiffOn
