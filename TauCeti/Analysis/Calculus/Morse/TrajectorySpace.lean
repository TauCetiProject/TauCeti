/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.OrbitSlice
public import TauCeti.Analysis.Calculus.Morse.Transversality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Analysis.Calculus.Morse.RegularLevel

/-!
# Level slices of transverse Morse trajectories

Let `p ≠ q` be nondegenerate critical points of a globally `C²` function `f` with globally
Lipschitz gradient on a finite-dimensional real inner product space. A negative-gradient
trajectory from `p` to `q` crosses each intermediate level `{f = c}` exactly once, so the level
slice `W^u(p) ∩ W^s(q) ∩ {f = c}` is in bijection with the space of unparametrized trajectories
from `p` to `q` (`Flow.IsNegativeGradient.bijOn_quotient_mk_unstableSet_inter_stableSet_level`).
This file shows that, where `W^u(p)` and `W^s(q)` meet transversally, the slice is an embedded
`C¹` submanifold of dimension `morseIndex f p - morseIndex f q - 1`.

The level `{f = c}` is cut transversally: the velocity `-∇f y` of the trajectory through a point
`y` of the slice is tangent to `W^u(p) ∩ W^s(q)`, while `df_y(-∇f y) = -‖∇f y‖² ≠ 0`. Hence the
tangent space of the slice at `y` is the tangent space of `W^u(p) ∩ W^s(q)` cut by `ker df_y`,
one dimension less.

When the Morse indices differ by one, the slice is therefore discrete under the Morse–Smale
condition: its points are the isolated trajectories that the Morse differential counts.
Finiteness of the count needs, in addition, compactness of the slice.

## Main results

* `TauCeti.span_tangentConeAt_unstableSet_inter_stableSet_sup_ker_fderiv_eq_top`: every level of
  `f` is transverse to `W^u(p) ∩ W^s(q)`.
* `TauCeti.IsNondegenerateCriticalPoint.exists_unstableSet_inter_stableSet_level_chart`: under
  transversality, the level slice is flattened by a `C¹` chart with `C¹` inverse.
* `TauCeti.IsNondegenerateCriticalPoint.span_tangentConeAt_unstableSet_inter_stableSet_level`: its
  tangent space is the tangent space of `W^u(p) ∩ W^s(q)` cut by `ker df_y`.
* `finrank_span_tangentConeAt_unstableSet_inter_stableSet_level_add_morseIndex` (in the namespace
  `TauCeti.IsNondegenerateCriticalPoint`): the slice has dimension
  `morseIndex f p - morseIndex f q - 1`.
* `TauCeti.IsNondegenerateCriticalPoint.isDiscrete_unstableSet_inter_stableSet_level`: if the
  Morse indices differ by one and the Morse–Smale condition holds along the slice, then the slice
  is discrete.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of trajectories).
-/

public section

open Filter Set Topology
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {p q y : E} {K : ℝ≥0} {c : ℝ}

/-- At a point `y` of a nonconstant connecting trajectory, `df_y` does not vanish on `∇f y`. -/
private theorem fderiv_apply_gradient_ne_zero (hf : LipschitzWith K (∇ f)) (hpq : p ≠ q)
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    fderiv ℝ f y (∇ f y) ≠ 0 := by
  have hgrad : ∇ f y ≠ 0 := Flow.gradient_ne_zero_of_mem_unstableSet_inter_stableSet
    (fun z ↦ (forall_negativeGradientFlow_eq_self_iff f hf z).2) hpq ⟨hyu, hys⟩
  rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
  positivity

/-- **Levels are transverse to connecting trajectories.** At a point `y` of `W^u(p) ∩ W^s(q)` with
`p ≠ q`, the tangent space of `W^u(p) ∩ W^s(q)` and the kernel of `df_y`, the tangent space of the
level of `f` through `y`, span the whole space. -/
theorem span_tangentConeAt_unstableSet_inter_stableSet_sup_ker_fderiv_eq_top
    (hf : LipschitzWith K (∇ f)) (hpq : p ≠ q)
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q) y) ⊔ (fderiv ℝ f y).ker = ⊤ := by
  have hmem := (Submodule.span ℝ _).neg_mem <| Submodule.subset_span
    (neg_gradient_mem_tangentConeAt_unstableSet_inter_stableSet hf hyu hys)
  rw [neg_neg] at hmem
  refine top_unique ?_
  rw [← LinearMap.span_singleton_sup_ker_eq_top (fderiv ℝ f y : E →ₗ[ℝ] ℝ)
    (fderiv_apply_gradient_ne_zero hf hpq hyu hys)]
  exact sup_le_sup_right ((Submodule.span_singleton_le_iff_mem _ _).2 hmem) _

namespace IsNondegenerateCriticalPoint

/-- Under transversality, the level slice through `y` is cut out of `W^u(p) ∩ W^s(q)` by a
transverse regular level set: it is flattened by a `C¹` chart, and its tangent space is that of
`W^u(p) ∩ W^s(q)` cut by `ker df_y`. -/
private theorem level_slice (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hpq : p ≠ q) (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    (htr : Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤)
    (hyc : f y = c) :
    (∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      IsSliceChart e ((Submodule.span ℝ (tangentConeAt ℝ
          (Flow.unstableSet (negativeGradientFlow f hf) p ∩
            Flow.stableSet (negativeGradientFlow f hf) q) y) ⊓
          (fderiv ℝ f y).ker : Submodule ℝ E) : Set E)
        (Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c})) ∧
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) y) =
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q) y) ⊓ (fderiv ℝ f y).ker := by
  obtain ⟨e₁, hy₁, he₁, hes₁, hS₁⟩ :=
    hp.exists_unstableSet_inter_stableSet_chart hq hfs hf hyu hys htr
  rw [← hp.span_tangentConeAt_unstableSet_inter_stableSet hq hfs hf hyu hys htr] at hS₁
  -- The level `{f = c}` is the regular zero set of `f - c` near `y`.
  have hlevel : {x | f x = c} = (fun z ↦ f z - c) ⁻¹' {0} := by ext; simp [sub_eq_zero]
  have hg := ((hfs.contDiffAt (x := y)).hasStrictFDerivAt (by norm_num)).sub_const c
  have hg' := LinearMap.range_eq_top.2 (Flow.fderiv_surjective_of_mem_unstableSet_inter_stableSet
    (fun z ↦ (forall_negativeGradientFlow_eq_self_iff f hf z).2) hpq ⟨hyu, hys⟩)
  have hgC (z : E) (_ : z ∈ univ) : ContDiffAt ℝ 1 (fun z ↦ f z - c) z :=
    ((hfs.of_le one_le_two).sub contDiff_const).contDiffAt
  have hgy : f y - c = 0 := by simp [hyc]
  have hs₁ := (hes₁ _ (e₁.map_source hy₁)).differentiableAt one_ne_zero
  have htr' := span_tangentConeAt_unstableSet_inter_stableSet_sup_ker_fderiv_eq_top
    hf hpq hyu hys
  rw [hlevel]
  exact ⟨exists_isSliceChart_inter_preimage_zero one_ne_zero (isSliceChart_iff.2 hS₁) hy₁
      ⟨hyu, hys⟩ he₁ hs₁ hg hg' hgy isOpen_univ (mem_univ y) hgC htr',
    span_tangentConeAt_inter_preimage_zero one_ne_zero (isSliceChart_iff.2 hS₁) hy₁ ⟨hyu, hys⟩ he₁
      hs₁ hg hg' hgy isOpen_univ (mem_univ y) hgC htr'⟩

/-- **The level slice of a transverse intersection is an embedded submanifold.** If the unstable
set of a Morse critical point `p` and the stable set of a different Morse critical point `q` meet
transversally at `y`, and `f y = c`, then near `y` the level slice `W^u(p) ∩ W^s(q) ∩ {f = c}` is
flattened by a `C¹` chart with `C¹` inverse onto the intersection of the tangent spaces of `W^u(p)`
and `W^s(q)` with `ker df_y`. -/
theorem exists_unstableSet_inter_stableSet_level_chart (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hpq : p ≠ q) (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    (htr : Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤)
    (hyc : f y = c) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c} ↔
        e z ∈
          Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
            Submodule.span ℝ
              (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) ⊓
            (fderiv ℝ f y).ker := by
  obtain ⟨⟨e, hye, he, hes, hS⟩, -⟩ := hp.level_slice hq hfs hf hpq hyu hys htr hyc
  rw [hp.span_tangentConeAt_unstableSet_inter_stableSet hq hfs hf hyu hys htr] at hS
  exact ⟨e, hye, he, hes, isSliceChart_iff.1 hS⟩

/-- **The tangent space of a transverse level slice.** If the unstable set of a Morse critical
point `p` and the stable set of a different Morse critical point `q` meet transversally at `y`, and
`f y = c`, then the tangent space of the level slice `W^u(p) ∩ W^s(q) ∩ {f = c}` at `y` is the
intersection of the tangent spaces of `W^u(p)` and `W^s(q)` with `ker df_y`. -/
theorem span_tangentConeAt_unstableSet_inter_stableSet_level
    (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hpq : p ≠ q) (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    (htr : Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤)
    (hyc : f y = c) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) y) =
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) ⊓
        (fderiv ℝ f y).ker := by
  rw [(hp.level_slice hq hfs hf hpq hyu hys htr hyc).2,
    hp.span_tangentConeAt_unstableSet_inter_stableSet hq hfs hf hyu hys htr]

/-- **The level slice has dimension the index difference minus one.** If the unstable set of a
Morse critical point `p` and the stable set of a different Morse critical point `q` meet
transversally at `y`, then the tangent space at `y` of the level slice
`W^u(p) ∩ W^s(q) ∩ {f = f y}` has dimension `morseIndex f p - morseIndex f q - 1`. -/
theorem finrank_span_tangentConeAt_unstableSet_inter_stableSet_level_add_morseIndex
    (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hpq : p ≠ q) (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    (htr : Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤)
    (hyc : f y = c) :
    Module.finrank ℝ
        (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) y)) +
      morseIndex f q + 1 = morseIndex f p := by
  -- Cutting by the hyperplane `ker df_y`, which is transverse, lowers the dimension by one.
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q) y)) (fderiv ℝ f y).ker
  rw [span_tangentConeAt_unstableSet_inter_stableSet_sup_ker_fderiv_eq_top hf hpq hyu hys,
    finrank_top,
    ← (hp.level_slice hq hfs hf hpq hyu hys htr hyc).2] at hdim
  have hker := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ f y : E →ₗ[ℝ] ℝ)
  rw [LinearMap.range_eq_top.2 (Flow.fderiv_surjective_of_mem_unstableSet_inter_stableSet
    (fun z ↦ (forall_negativeGradientFlow_eq_self_iff f hf z).2) hpq ⟨hyu, hys⟩), finrank_top,
    Module.finrank_self] at hker
  have hW :=
    hp.finrank_span_tangentConeAt_unstableSet_inter_stableSet_add_morseIndex hq hfs hf hyu hys htr
  omega

/-- **Index-difference-one level slices are discrete.** If the Morse indices of `p` and `q` differ
by one and the unstable set of `p` meets the stable set of `q` transversally at every point of the
level slice `W^u(p) ∩ W^s(q) ∩ {f = c}`, then the slice is discrete: each of the trajectories it
parametrizes is isolated. -/
theorem isDiscrete_unstableSet_inter_stableSet_level (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hind : morseIndex f p = morseIndex f q + 1)
    (htr : ∀ y ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c},
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤) :
    IsDiscrete (Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) := by
  have hpq : p ≠ q := by rintro rfl; omega
  refine isDiscrete_iff_discreteTopology.2 (discreteTopology_of_noAccPts fun y hy ↦ ?_)
  have htry := htr y hy
  obtain ⟨⟨hyu, hys⟩, hyc⟩ := hy
  -- The slice is zero-dimensional, so the chart at `y` flattens it onto the point `0`.
  have hdim := hp.finrank_span_tangentConeAt_unstableSet_inter_stableSet_level_add_morseIndex hq
    hfs hf hpq hyu hys htry hyc
  obtain ⟨e, hye, -, -, he⟩ :=
    hp.exists_unstableSet_inter_stableSet_level_chart hq hfs hf hpq hyu hys htry hyc
  have h0 : Module.finrank ℝ (Submodule.span ℝ (tangentConeAt ℝ
      (Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q ∩ {x | f x = c}) y)) = 0 := by
    omega
  rw [← hp.span_tangentConeAt_unstableSet_inter_stableSet_level hq hfs hf hpq hyu hys htry hyc,
    Submodule.finrank_eq_zero.1 h0] at he
  have hey : e y = 0 := (he y hye).1 ⟨⟨hyu, hys⟩, hyc⟩
  intro hacc
  obtain ⟨z, ⟨hz, hzS⟩, hzy⟩ := accPt_iff_nhds.1 hacc e.source (e.open_source.mem_nhds hye)
  exact hzy (e.injOn hz hye (by rw [hey]; exact (he z hz).1 hzS))

end IsNondegenerateCriticalPoint

end TauCeti
