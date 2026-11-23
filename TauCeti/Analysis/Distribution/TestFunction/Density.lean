/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Calculus.BumpFunction.DerivativeApproximation
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Distribution.TestFunction.Convergence

/-!
# Smooth functions are dense in `𝓓^{n}_{K}(E, F)` for convex `K`

For a compact set `K` in a real normed space `E`, a real normed space `F` and `n ≤ ∞`, the space
`𝓓^{n}_{K}(E, F)` of `Cⁿ` functions from `E` to `F` supported in `K` carries the topology of
uniform convergence of all derivatives of order at most `n`. When `K` is convex and `F` is a Banach
space, the smooth functions supported in `K` are dense in it: the inclusion
`𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)` has dense range for all `n₂ ≤ n₁`
(`ContDiffMapSupportedIn.denseRange_monoCLM`). The approximants keep their support in `K` itself,
not merely in a neighbourhood of `K`, and no extension theorem across the boundary of `K` is used.
For finite `n` the topology of `𝓓^{n}_{K}(E, F)` is given by finitely many seminorms, so for a
Banach space `F` it serves as a complete normable space of perturbations in transversality
arguments; density lets a property that is open in this `Cⁿ` topology, and holds for some `Cⁿ`
perturbation, hold for a smooth perturbation with the same support.

The proof contracts and then mollifies. A continuous function vanishing off `K` vanishes off the
interior of `K`: its set-theoretic support `Function.support f` lies in `interior K`
(`ContDiffMapSupportedIn.support_subset_interior`), although its closed support `tsupport f` may
meet the boundary of `K`. So there is nothing to prove when `K` has empty interior. Otherwise fix
`p` in the interior of `K`. For `a > 1` the function `x ↦ f (p + a • (x - p))` is supported in the
image of `K` under the homothety of centre `p` and ratio `a⁻¹`, a compact subset of the interior
of `K` by convexity; its derivatives are `a ^ k` times those of `f` at the dilated point, so it
tends to `f` in `𝓓^{n}_{K}(E, F)` as `a → 1`. A compact set with nonempty interior forces `E` to
be finite-dimensional, and there each contracted function is approximated in every derivative of
order at most `n` by mollifications whose supports stay inside the interior of `K`
(`ContDiff.exists_contDiff_hasCompactSupport_tendstoUniformly_iteratedFDeriv`).

## Main results

* `ContDiffMapSupportedIn.support_subset_interior`: a function in `𝓓^{n}_{K}(E, F)` vanishes off
  the interior of `K`, i.e. `Function.support f ⊆ interior K`.
* `ContDiffMapSupportedIn.denseRange_monoCLM`: for convex `K`, a Banach space `F` and `n₂ ≤ n₁`,
  the inclusion `𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)` has dense range; for `n₁ = ∞` this says
  that smooth functions supported in `K` are dense in `𝓓^{n₂}_{K}(E, F)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §1.3 (regularization by convolution).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications 52, 2012, §3.2 (Banach spaces of perturbations and smooth regular
  choices in transversality arguments).
-/

public section

open Filter Function Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {n : ℕ∞} {K : Compacts E}

/-- A function in `𝓓^{n}_{K}(E, F)` vanishes off the interior of `K`: its set-theoretic support
`Function.support f` lies in `interior K`, although `tsupport f` may meet the boundary of `K`. In
particular `𝓓^{n}_{K}(E, F)` is trivial when `K` has empty interior. -/
theorem support_subset_interior (f : 𝓓^{n}_{K}(E, F)) : support f ⊆ interior (K : Set E) :=
  interior_maximal f.support_subset f.continuous.isOpen_support

section Contraction

variable {p : E}

/-- The contraction of `f` towards `p`: the function `x ↦ f (p + a • (x - p))` for a ratio
`a ≥ 1`, which is supported in `K` when `K` is convex and contains `p`. -/
private noncomputable def contraction (hK : Convex ℝ (K : Set E)) (hp : p ∈ (K : Set E))
    (f : 𝓓^{n}_{K}(E, F)) (a : Ici (1 : ℝ)) : 𝓓^{n}_{K}(E, F) :=
  .of_support_subset (f := fun x ↦ f (p + (a : ℝ) • (x - p)))
    (f.contDiff.comp (contDiff_const.add (contDiff_const.smul (contDiff_id.sub contDiff_const))))
    fun x hx ↦ by
      have ha : (0 : ℝ) < a := zero_lt_one.trans_le a.property
      have hy := f.support_subset hx
      have hx' : x = p + (a : ℝ)⁻¹ • (p + (a : ℝ) • (x - p) - p) := by
        rw [add_sub_cancel_left, inv_smul_smul₀ ha.ne', add_sub_cancel]
      rw [hx']
      exact hK.add_smul_sub_mem hp hy ⟨inv_nonneg.2 ha.le, inv_le_one_of_one_le₀ a.property⟩

private theorem coe_contraction (hK : Convex ℝ (K : Set E)) (hp : p ∈ (K : Set E))
    (f : 𝓓^{n}_{K}(E, F)) (a : Ici (1 : ℝ)) :
    ⇑(contraction hK hp f a) = fun x ↦ f (p + (a : ℝ) • (x - p)) :=
  funext <| coe_of_support_subset _ _

private theorem contraction_one (hK : Convex ℝ (K : Set E)) (hp : p ∈ (K : Set E))
    (f : 𝓓^{n}_{K}(E, F)) : contraction hK hp f ⟨1, le_rfl⟩ = f :=
  ext fun x ↦ by simp [coe_contraction]

/-- The derivatives of the contraction are `a ^ k` times those of `f` at the dilated point. -/
private theorem iteratedFDeriv_contraction (hK : Convex ℝ (K : Set E)) (hp : p ∈ (K : Set E))
    (f : 𝓓^{n}_{K}(E, F)) (a : Ici (1 : ℝ)) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (contraction hK hp f a) x =
      (a : ℝ) ^ k • iteratedFDeriv ℝ k f (p + (a : ℝ) • (x - p)) := by
  rw [coe_contraction, iteratedFDeriv_comp_sub (f := fun z ↦ f (p + (a : ℝ) • z)),
    TauCeti.iteratedFDeriv_comp_const_smul_apply (fun w ↦ f (p + w)), iteratedFDeriv_comp_add_left]

/-- The contraction depends continuously on the ratio, so it tends to `f` as the ratio tends
to `1`. -/
private theorem continuous_contraction (hK : Convex ℝ (K : Set E)) (hp : p ∈ (K : Set E))
    (f : 𝓓^{n}_{K}(E, F)) : Continuous (contraction hK hp f) := by
  refine continuous_of_continuous_iteratedFDeriv fun k hk ↦ ?_
  simp only [iteratedFDeriv_contraction]
  have hfk := f.contDiff.continuous_iteratedFDeriv (m := k) (by exact_mod_cast hk)
  fun_prop

/-- For a ratio `a > 1` and `p` in the interior of `K`, the closed support of the contraction lies
in the interior of `K`: it lies in the image of `K` under the homothety of centre `p` and ratio
`a⁻¹`, a compact subset of the interior of `K`. -/
private theorem tsupport_contraction_subset_interior (hK : Convex ℝ (K : Set E))
    (hp : p ∈ interior (K : Set E)) (f : 𝓓^{n}_{K}(E, F)) (a : Ici (1 : ℝ)) (ha : 1 < (a : ℝ)) :
    tsupport (contraction hK (interior_subset hp) f a) ⊆ interior (K : Set E) := by
  rw [coe_contraction]
  refine (tsupport_comp_subset_preimage (f : E → F) (f := fun x ↦ p + (a : ℝ) • (x - p))
    (by fun_prop)).trans fun x hx ↦ ?_
  obtain ⟨y, hy, hxy⟩ := hK.closure_subset_image_homothety_interior_of_one_lt hp a ha
    (subset_closure (f.tsupport_subset hx))
  rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm] at hxy
  exact sub_left_inj.1
    (smul_right_injective E (zero_lt_one.trans ha).ne' (add_left_cancel hxy)) ▸ hy

end Contraction

/-- **Smooth functions supported in a convex compact set are dense.** For convex `K`, a Banach
space `F` (`[CompleteSpace F]`) and `n₂ ≤ n₁`, the inclusion `𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)`
has dense range. For `n₁ = ∞` this says that every `C^{n₂}` function supported in `K` is a limit,
in every derivative of order at most `n₂` uniformly, of smooth functions supported in `K`. -/
theorem denseRange_monoCLM [CompleteSpace F] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] {n₁ n₂ : ℕ∞} (hn : n₂ ≤ n₁)
    (hK : Convex ℝ (K : Set E)) :
    DenseRange (monoCLM 𝕜 : 𝓓^{n₁}_{K}(E, F) →L[𝕜] 𝓓^{n₂}_{K}(E, F)) := by
  classical
  -- Smooth functions map into `𝓓^{n₂}_{K}(E, F)` through `𝓓^{n₁}_{K}(E, F)`, so it suffices to
  -- approximate by smooth functions.
  refine Dense.mono (s₁ := range (monoCLM 𝕜 : 𝓓_{K}(E, F) →L[𝕜] 𝓓^{n₂}_{K}(E, F)))
    (fun _ ⟨g, hg⟩ ↦ ⟨monoCLM 𝕜 g, hg ▸ ext fun x ↦ by simp [hn]⟩) fun f ↦ ?_
  rcases (interior (K : Set E)).eq_empty_or_nonempty with hint | ⟨p, hp⟩
  · -- If `K` has empty interior, then `f = 0`.
    have hf : f = 0 := ext fun x ↦ by
      simpa using mt (fun hx ↦ f.support_subset_interior hx) (by simp [hint])
    exact subset_closure ⟨0, by simp [hf]⟩
  -- A compact set with nonempty interior forces `E` to be finite-dimensional.
  have : FiniteDimensional ℝ E :=
    .of_totallyBounded_nhds ℝ (mem_interior_iff_mem_nhds.mp hp) K.isCompact.totallyBounded
  -- Each contraction of `f` with ratio `> 1` is a limit of mollifications supported in `K`.
  have hmem (a : Ici (1 : ℝ)) (ha : 1 < (a : ℝ)) :
      contraction hK (interior_subset hp) f a ∈ closure (range (monoCLM 𝕜 :
        𝓓_{K}(E, F) →L[𝕜] 𝓓^{n₂}_{K}(E, F))) := by
    set fa := contraction hK (interior_subset hp) f a
    obtain ⟨g, L, -, hLK, hg, hlim⟩ :=
      fa.contDiff.exists_contDiff_hasCompactSupport_tendstoUniformly_iteratedFDeriv
        fa.hasCompactSupport isOpen_interior (tsupport_contraction_subset_interior hK hp f a ha)
    let gK : ℕ → 𝓓_{K}(E, F) := fun m ↦ .of_support_subset (hg m).1
      ((subset_tsupport _).trans ((hg m).2.trans (hLK.trans interior_subset)))
    refine mem_closure_of_tendsto (b := atTop) (f := fun m ↦ monoCLM 𝕜 (gK m)) ?_
      (Eventually.of_forall fun m ↦ mem_range_self _)
    have hgK (m : ℕ) : ⇑(gK m) = g m := funext <| coe_of_support_subset _ _
    refine tendsto_iff_tendstoUniformly_iteratedFDeriv.2 fun k hk ↦ ?_
    simpa [hgK] using hlim k hk
  -- The contractions tend to `f` as the ratio tends to `1`.
  let a : ℕ → Ici (1 : ℝ) := fun m ↦
    ⟨1 + 1 / ((m : ℝ) + 1), le_add_of_nonneg_right (by positivity)⟩
  have ha : Tendsto a atTop (𝓝 ⟨1, le_rfl⟩) := by
    rw [tendsto_subtype_rng]
    simpa [a] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim := ((continuous_contraction hK (interior_subset hp) f).tendsto _).comp ha
  rw [contraction_one] at hlim
  exact isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall fun m ↦ hmem (a m) (lt_add_of_pos_right _ (by positivity)))

end ContDiffMapSupportedIn
