/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.UniformSpace.UniformConvergence
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

## Main results

* `ContDiffOn.tendstoUniformlyOn_iteratedFDeriv_slice`: the `i`-th derivatives of `g a` converge
  uniformly on `K` to those of `x ↦ f (a₀, x)` along any filter `l ≤ 𝓝 a₀`.
-/

public section

open Filter Topology

namespace ContDiffOn

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

end ContDiffOn
