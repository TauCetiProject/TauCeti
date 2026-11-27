/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Perturbation
public import TauCeti.Dynamics.FixedPoints.Persistence
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.LeftRightNhds
import TauCeti.Analysis.Calculus.ContDiff.Comp

/-!
# Persistence of periodic points under small `C¹` perturbations

Let `f` be a self-map of a finite-dimensional real normed space, `K` a compact set and `k` a
period. A point `x` with `f^[k] x = x` is a nondegenerate periodic point of period `k` when `1` is
not an eigenvalue of the linearized return map `D(f^[k])(x)`, that is, when `x` is a nondegenerate
fixed point of `f^[k]` (`TauCeti.IsNondegenerateFixedPt`). Suppose that `f` is `C¹` along the
first `k` points `f^[j] x`, `j < k`, of the orbits of the points `x ∈ K`, and let `U` be a
neighbourhood of these orbit points. This file shows that the periodic points of period `k` in `K`
are stable under every perturbation `g` of `f` that is small in `C¹` on `U`, that is, whose values
and derivatives are uniformly close to those of `f` on `U`:

* if all the points of period `k` of `f` in `K` are nondegenerate, so are those of `g`
  (`IsCompact.exists_pos_forall_isNondegenerateFixedPt_iterate`);
* if moreover they lie in the interior of `K`, those of `g` correspond to them bijectively, each
  close to its partner and with the same sign of `det (1 - D(g^[k]))`
  (`IsCompact.exists_pos_forall_exists_bijOn_fixedPoints_iterate_inter`), so the number of points
  of period `k` in `K` and their signed count `∑ sign det (1 - D(f^[k]))` do not change
  (`IsCompact.exists_pos_forall_ncard_fixedPoints_iterate_inter_eq`,
  `IsCompact.exists_pos_forall_finsum_sign_det_iterate_eq`).

The proofs apply the persistence of nondegenerate fixed points of
`TauCeti.Dynamics.FixedPoints.Persistence` to `f^[k]` and `g^[k]`, which are `C¹`-close on `K`
when `f` and `g` are `C¹`-close on `U`
(`IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le`).

Since finitely many conditions of this kind hold together for small enough perturbations, the
nondegeneracy, the number and the signed count of the points of period `k` in `K` are preserved
for all periods `1 ≤ k ≤ N` up to a cutoff `N` at once
(`IsCompact.exists_pos_forall_mem_Icc_isNondegenerateFixedPt_iterate`,
`IsCompact.exists_pos_forall_mem_Icc_ncard_fixedPoints_iterate_inter_eq`,
`IsCompact.exists_pos_forall_mem_Icc_finsum_sign_det_iterate_eq`). The first statement says that
the maps all of whose periodic points of period at most `N` in `K` are nondegenerate form a
`C¹`-open set, as a Baire argument making the periodic points of an area-preserving surface map
nondegenerate up to a period cutoff requires: once a localized perturbation has made the periodic
points of some period nondegenerate, every later perturbation small enough in `C¹` keeps them so.
The signed counts `∑ sign det (1 - D(f^[k]))`, `1 ≤ k ≤ N`, are the contributions from `K` to the
Lefschetz numbers of the iterates of `f`, which are the coefficients of the logarithmic derivative
of the Lefschetz zeta function of `f`; the unsigned counts play the same role for the Artin–Mazur
zeta function. The last two statements say that these contributions through order `N` do not
depend on the perturbation, among small nondegenerate ones.

For a `C¹` map `f`, three more statements of this kind hold for all small enough `δ > 0` and all
maps `g` that are `δ`-close to `f` in value and derivative at every point. If no point of `K` has
period `j`, neither has any for `g` (`IsCompact.eventually_forall_not_isFixedPt_iterate`). If the
points of period `k` in `K` are nondegenerate and remain periodic for `g`, then `g` has no other
points of period `k` in `K` (`IsCompact.eventually_forall_fixedPoints_iterate_inter_eq`): on a
compact neighbourhood of `K` whose points of period `k` are interior, those of `g` correspond
bijectively to those of `f`. If, for some `n ≤ N`, every point of `K` of period at most `n` is a
nondegenerate fixed point of each `f^[k]`, `1 ≤ k ≤ N`, fixing it, the same holds for `g`
(`IsCompact.eventually_forall_isNondegenerateFixedPt_iterate_of_exists_isFixedPt`): these orbits
are finitely many, near them persistence applies, and away from them avoidance does. This is the
invariant of the induction over the periods that makes all periodic points of period at most `N`
of an area-preserving map of the plane nondegenerate
(`TauCeti.exists_forall_mem_Icc_isNondegenerateFixedPt_iterate_comp`).

For perturbations of the form `g ∘ ψ` with `ψ` close to the identity in `C¹` (`TauCeti.IsNearId`),
as they arise when localized perturbations are composed one after another, nondegeneracy and the
avoidance of a closed set by the graph of an iterate hold for all `ψ` close enough to the identity
(`TauCeti.eventually_forall_isNearId_isNondegenerateFixedPt_iterate_comp`,
`TauCeti.eventually_forall_isNearId_iterate_comp_notMem`).

## Main results

* `IsCompact.exists_pos_forall_isNondegenerateFixedPt_iterate`: nondegeneracy of the periodic
  points of period `k` in a compact set is `C¹`-open.
* `IsCompact.exists_pos_forall_exists_bijOn_fixedPoints_iterate_inter`: the periodic points of
  period `k` in a compact set persist, with the signs of their linearized return maps.
* `IsCompact.exists_pos_forall_ncard_fixedPoints_iterate_inter_eq`,
  `IsCompact.exists_pos_forall_finsum_sign_det_iterate_eq`: their number and signed count are
  unchanged.
* `IsCompact.exists_pos_forall_mem_Icc_isNondegenerateFixedPt_iterate`,
  `IsCompact.exists_pos_forall_mem_Icc_ncard_fixedPoints_iterate_inter_eq`,
  `IsCompact.exists_pos_forall_mem_Icc_finsum_sign_det_iterate_eq`: nondegeneracy, number and
  signed count for all periods `1 ≤ k ≤ N` at once.
* `IsCompact.eventually_forall_not_isFixedPt_iterate`: the absence of points of period `j` from a
  compact set is `C¹`-open.
* `IsCompact.eventually_forall_fixedPoints_iterate_inter_eq`: a small `C¹` perturbation keeping the
  nondegenerate points of period `k` in a compact set periodic has no other such points there.
* `IsCompact.eventually_forall_isNondegenerateFixedPt_iterate_of_exists_isFixedPt`: nondegeneracy
  of the orbits of period at most `n` in all their covers of period at most `N` is `C¹`-open.
* `TauCeti.eventually_forall_isNearId_isNondegenerateFixedPt_iterate_comp`,
  `TauCeti.eventually_forall_isNearId_iterate_comp_notMem`: nondegeneracy and avoidance persist
  for `g ∘ ψ` with `ψ` close enough to the identity in `C¹`.

## References

* R. C. Robinson, *Generic properties of conservative systems*, Amer. J. Math. 92 (1970),
  562–603, for the openness of nondegeneracy of the periodic points of bounded period, and its use
  in the genericity of nondegenerate periodic points of conservative maps.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapters 2 and 3, for the `C¹` topology and the openness of transversality.
-/

public section

open Filter Function Set
open scoped Manifold Topology

namespace IsCompact

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → E} {K U : Set E} {k N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- A conclusion about the maps that are `C¹`-close to `f^[k]` on `K` holds for the iterates
`g^[k]` of the maps `g` that are `C¹`-close enough to `f` on a neighbourhood `U` of the first `k`
points of the orbits of the points of `K`. -/
private theorem exists_pos_forall_iterate_of_exists_pos (hK : IsCompact K)
    (hf : ∀ j < k, ∀ x ∈ K, ContDiffAt ℝ 1 f (f^[j] x)) (hU : U ∈ 𝓝ˢ (⋃ j < k, f^[j] '' K))
    {P : (E → E) → Prop}
    (h : ∃ ε > 0, ∀ g : E → E, (∀ x ∈ K, DifferentiableAt ℝ g x) →
      (∀ x ∈ K, ‖g x - f^[k] x‖ ≤ ε) → (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f^[k] x‖ ≤ ε) → P g) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) → P g^[k] := by
  obtain ⟨ε, hε, hP⟩ := h
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le hf hε hU
  exact ⟨δ, hδ, fun g hg₁ hg₂ hg₃ ↦ hP g^[k] (fun x hx ↦ (h g hg₁ hg₂ hg₃ x hx).1)
    (fun x hx ↦ (h g hg₁ hg₂ hg₃ x hx).2.1) fun x hx ↦ (h g hg₁ hg₂ hg₃ x hx).2.2⟩

/-- **Nondegeneracy of the periodic points of period `k` in a compact set persists under small `C¹`
perturbations.**

Let `f` be `C¹` at the first `k` points `f^[j] x`, `j < k`, of the orbit of every `x ∈ K`, and let
every `x ∈ K` with `f^[k] x = x` be a nondegenerate fixed point of `f^[k]`. For every neighbourhood
`U` of these orbit points there is `δ > 0` such that every map `g`, differentiable on `U`, within
`δ` of `f` on `U` and whose derivative is within `δ` of that of `f` on `U`, again has only
nondegenerate periodic points of period `k` in `K`. -/
theorem exists_pos_forall_isNondegenerateFixedPt_iterate (hK : IsCompact K)
    (hf : ∀ j < k, ∀ x ∈ K, ContDiffAt ℝ 1 f (f^[j] x))
    (hnd : ∀ x ∈ K, IsFixedPt f^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x)
    (hU : U ∈ 𝓝ˢ (⋃ j < k, f^[j] '' K)) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      ∀ x ∈ K, IsFixedPt g^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, E) g^[k] x := by
  have hfk (x : E) (hx : x ∈ K) : ContDiffAt ℝ 1 f^[k] x :=
    contDiffAt_iterate fun j hj ↦ hf j hj x hx
  exact hK.exists_pos_forall_iterate_of_exists_pos hf hU <|
    hK.exists_pos_forall_isNondegenerateFixedPt
      (fun x hx ↦ (hfk x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ ((hfk x hx).continuousAt_fderiv one_ne_zero).continuousWithinAt) hnd

/-- **The periodic points of period `k` in a compact set persist under small `C¹` perturbations,
with their signs.**

Let `f` be `C¹` at the first `k` points `f^[j] x`, `j < k`, of the orbit of every `x ∈ K`, and let
the points `x ∈ K` with `f^[k] x = x` be nondegenerate fixed points of `f^[k]` lying in the interior
of `K`. Let `U` be a neighbourhood of these orbit points and `ε > 0`. There is `δ > 0` with the
following property. If `g` is differentiable on `U`, within `δ` of `f` on `U`, and its derivative
is within `δ` of that of `f` on `U`, then some map `φ` is a bijection from the points of period `k`
of `f` in `K` to those of `g` in `K`. It moves each point by at most `ε`, its values are
nondegenerate fixed points of `g^[k]`, and it preserves the sign of `det (1 - D(·^[k]))`. -/
theorem exists_pos_forall_exists_bijOn_fixedPoints_iterate_inter (hK : IsCompact K)
    (hf : ∀ j < k, ∀ x ∈ K, ContDiffAt ℝ 1 f (f^[j] x))
    (hnd : ∀ x ∈ K, IsFixedPt f^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x)
    (hint : ∀ x ∈ K, IsFixedPt f^[k] x → x ∈ interior K) (hU : U ∈ 𝓝ˢ (⋃ j < k, f^[j] '' K))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      ∃ φ : E → E, BijOn φ (fixedPoints f^[k] ∩ K) (fixedPoints g^[k] ∩ K) ∧
        ∀ x ∈ fixedPoints f^[k] ∩ K, dist (φ x) x ≤ ε ∧
          IsNondegenerateFixedPt 𝓘(ℝ, E) g^[k] (φ x) ∧
          SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ g^[k] (φ x) : E →ₗ[ℝ] E))) =
            SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ f^[k] x : E →ₗ[ℝ] E))) := by
  have hfk (x : E) (hx : x ∈ K) : ContDiffAt ℝ 1 f^[k] x :=
    contDiffAt_iterate fun j hj ↦ hf j hj x hx
  exact hK.exists_pos_forall_iterate_of_exists_pos hf hU <|
    hK.exists_pos_forall_exists_bijOn_fixedPoints_inter
      (fun x hx ↦ (hfk x hx).continuousAt.continuousWithinAt)
      (fun x hx _ ↦ (hfk x hx).continuousAt_fderiv one_ne_zero) hnd hint hε

/-- **The number of periodic points of period `k` in a compact set is stable under small `C¹`
perturbations.**

Under the hypotheses of `IsCompact.exists_pos_forall_exists_bijOn_fixedPoints_iterate_inter`, every
map `g` that is `C¹`-close to `f` on `U` has as many points of period `k` in `K` as `f`. -/
theorem exists_pos_forall_ncard_fixedPoints_iterate_inter_eq (hK : IsCompact K)
    (hf : ∀ j < k, ∀ x ∈ K, ContDiffAt ℝ 1 f (f^[j] x))
    (hnd : ∀ x ∈ K, IsFixedPt f^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x)
    (hint : ∀ x ∈ K, IsFixedPt f^[k] x → x ∈ interior K) (hU : U ∈ 𝓝ˢ (⋃ j < k, f^[j] '' K)) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      (fixedPoints g^[k] ∩ K).ncard = (fixedPoints f^[k] ∩ K).ncard := by
  have hfk (x : E) (hx : x ∈ K) : ContDiffAt ℝ 1 f^[k] x :=
    contDiffAt_iterate fun j hj ↦ hf j hj x hx
  exact hK.exists_pos_forall_iterate_of_exists_pos hf hU <|
    hK.exists_pos_forall_ncard_fixedPoints_inter_eq
      (fun x hx ↦ (hfk x hx).continuousAt.continuousWithinAt)
      (fun x hx _ ↦ (hfk x hx).continuousAt_fderiv one_ne_zero) hnd hint

/-- **The signed count of the periodic points of period `k` in a compact set is stable under small
`C¹` perturbations.**

Under the hypotheses of `IsCompact.exists_pos_forall_exists_bijOn_fixedPoints_iterate_inter`, every
map `g` that is `C¹`-close to `f` on `U` has the same sum of the local Lefschetz signs
`sign det (1 - D(g^[k])(y))` over its points `y` of period `k` in `K` as `f`. -/
theorem exists_pos_forall_finsum_sign_det_iterate_eq (hK : IsCompact K)
    (hf : ∀ j < k, ∀ x ∈ K, ContDiffAt ℝ 1 f (f^[j] x))
    (hnd : ∀ x ∈ K, IsFixedPt f^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x)
    (hint : ∀ x ∈ K, IsFixedPt f^[k] x → x ∈ interior K) (hU : U ∈ 𝓝ˢ (⋃ j < k, f^[j] '' K)) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      ∑ᶠ y ∈ fixedPoints g^[k] ∩ K,
          (SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ g^[k] y : E →ₗ[ℝ] E))) : ℤ) =
        ∑ᶠ x ∈ fixedPoints f^[k] ∩ K,
          (SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ f^[k] x : E →ₗ[ℝ] E))) : ℤ) := by
  have hfk (x : E) (hx : x ∈ K) : ContDiffAt ℝ 1 f^[k] x :=
    contDiffAt_iterate fun j hj ↦ hf j hj x hx
  exact hK.exists_pos_forall_iterate_of_exists_pos hf hU <|
    hK.exists_pos_forall_finsum_sign_det_eq
      (fun x hx ↦ (hfk x hx).continuousAt.continuousWithinAt)
      (fun x hx _ ↦ (hfk x hx).continuousAt_fderiv one_ne_zero) hnd hint

/-! ### All periods up to a cutoff -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A neighbourhood of the first `N` points of the orbits of the points of `K` is a neighbourhood
of their first `k` points for `k ≤ N`. -/
private theorem nhdsSet_iUnion_iterate_image_mono {s : Set E} (hk : k ≤ N)
    (hU : s ∈ 𝓝ˢ (⋃ j < N, f^[j] '' K)) : s ∈ 𝓝ˢ (⋃ j < k, f^[j] '' K) :=
  nhdsSet_mono (iUnion₂_subset fun j hj ↦
    subset_iUnion₂ (s := fun j (_ : j < N) ↦ f^[j] '' K) j (by omega)) hU

omit [FiniteDimensional ℝ E] in
/-- A conclusion about the perturbations `g` of `f` that are `δ`-close in `C¹` on `U`, which holds
for some `δ > 0`, holds for every smaller `δ > 0`. -/
private theorem eventually_nhdsGT_of_exists_pos {P : (E → E) → Prop}
    (h : ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) → P g) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) →
      (∀ y ∈ U, ‖g y - f y‖ ≤ δ) → (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) → P g := by
  obtain ⟨δ, hδ, h⟩ := h
  filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ' g hg₁ hg₂ hg₃
  exact h g hg₁ (fun y hy ↦ (hg₂ y hy).trans hδ'.2.le) fun y hy ↦ (hg₃ y hy).trans hδ'.2.le

omit [FiniteDimensional ℝ E] in
/-- Finitely many conclusions about the perturbations `g` of `f` that are `δ`-close in `C¹` on `U`,
each of which holds for some `δ > 0`, hold together for some `δ > 0`. -/
private theorem exists_pos_forall_mem_finset {s : Finset ℕ} {P : ℕ → (E → E) → Prop}
    (h : ∀ k ∈ s, ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) →
      (∀ y ∈ U, ‖g y - f y‖ ≤ δ) → (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) → P k g) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) → ∀ k ∈ s, P k g := by
  obtain ⟨δ, hδ, hδ₀⟩ := (((eventually_all_finset s).2 fun k hk ↦
    eventually_nhdsGT_of_exists_pos (h k hk)).and self_mem_nhdsWithin).exists
  exact ⟨δ, hδ₀, fun g hg₁ hg₂ hg₃ k hk ↦ hδ k hk g hg₁ hg₂ hg₃⟩

/-- **Nondegeneracy of all periodic points of period at most `N` in a compact set persists under
small `C¹` perturbations.**

Let `f` be `C¹` at the first `N` points `f^[j] x`, `j < N`, of the orbit of every `x ∈ K`, and
for every `1 ≤ k ≤ N` let every `x ∈ K` with `f^[k] x = x` be a nondegenerate fixed point of
`f^[k]`. For every neighbourhood `U` of these orbit points there is `δ > 0` such that every map
`g`, differentiable on `U`, within `δ` of `f` on `U` and whose derivative is within `δ` of that of
`f` on `U`, has the same property: for every `1 ≤ k ≤ N`, its periodic points of period `k` in `K`
are nondegenerate. So the maps all of whose periodic points of period at most `N` in `K` are
nondegenerate form a `C¹`-open set. -/
theorem exists_pos_forall_mem_Icc_isNondegenerateFixedPt_iterate (hK : IsCompact K)
    (hf : ∀ j < N, ∀ x ∈ K, ContDiffAt ℝ 1 f (f^[j] x))
    (hnd : ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt f^[k] x →
      IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x)
    (hU : U ∈ 𝓝ˢ (⋃ j < N, f^[j] '' K)) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt g^[k] x →
        IsNondegenerateFixedPt 𝓘(ℝ, E) g^[k] x :=
  exists_pos_forall_mem_finset fun k hk ↦ hK.exists_pos_forall_isNondegenerateFixedPt_iterate
    (fun j hj ↦ hf j (hj.trans_le (Finset.mem_Icc.1 hk).2)) (hnd k hk)
    (nhdsSet_iUnion_iterate_image_mono (Finset.mem_Icc.1 hk).2 hU)

/-- **The signed counts of the periodic points of all periods at most `N` in a compact set are
stable under small `C¹` perturbations.**

Let `f` be `C¹` at the first `N` points `f^[j] x`, `j < N`, of the orbit of every `x ∈ K`, and
for every `1 ≤ k ≤ N` let the points `x ∈ K` with `f^[k] x = x` be nondegenerate fixed points of
`f^[k]` lying in the interior of `K`. For every neighbourhood `U` of these orbit points there is
`δ > 0` such that every map `g` that is `δ`-close to `f` in `C¹` on `U` has, for every
`1 ≤ k ≤ N`, the same sum of the local Lefschetz signs `sign det (1 - D(g^[k])(y))` over its points
`y` of period `k` in `K` as `f`. -/
theorem exists_pos_forall_mem_Icc_finsum_sign_det_iterate_eq (hK : IsCompact K)
    (hf : ∀ j < N, ∀ x ∈ K, ContDiffAt ℝ 1 f (f^[j] x))
    (hnd : ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt f^[k] x →
      IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x)
    (hint : ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt f^[k] x → x ∈ interior K)
    (hU : U ∈ 𝓝ˢ (⋃ j < N, f^[j] '' K)) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      ∀ k ∈ Finset.Icc 1 N,
        ∑ᶠ y ∈ fixedPoints g^[k] ∩ K,
            (SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ g^[k] y : E →ₗ[ℝ] E))) : ℤ) =
          ∑ᶠ x ∈ fixedPoints f^[k] ∩ K,
            (SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ f^[k] x : E →ₗ[ℝ] E))) :
              ℤ) :=
  exists_pos_forall_mem_finset fun k hk ↦ hK.exists_pos_forall_finsum_sign_det_iterate_eq
    (fun j hj ↦ hf j (hj.trans_le (Finset.mem_Icc.1 hk).2)) (hnd k hk) (hint k hk)
    (nhdsSet_iUnion_iterate_image_mono (Finset.mem_Icc.1 hk).2 hU)

/-- **The numbers of periodic points of all periods at most `N` in a compact set are stable under
small `C¹` perturbations.**

Under the hypotheses of `IsCompact.exists_pos_forall_mem_Icc_finsum_sign_det_iterate_eq`, every map
`g` that is `C¹`-close to `f` on `U` has, for every `1 ≤ k ≤ N`, as many points of period `k` in `K`
as `f`. -/
theorem exists_pos_forall_mem_Icc_ncard_fixedPoints_iterate_inter_eq (hK : IsCompact K)
    (hf : ∀ j < N, ∀ x ∈ K, ContDiffAt ℝ 1 f (f^[j] x))
    (hnd : ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt f^[k] x →
      IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x)
    (hint : ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt f^[k] x → x ∈ interior K)
    (hU : U ∈ 𝓝ˢ (⋃ j < N, f^[j] '' K)) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt ℝ g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      ∀ k ∈ Finset.Icc 1 N, (fixedPoints g^[k] ∩ K).ncard = (fixedPoints f^[k] ∩ K).ncard :=
  exists_pos_forall_mem_finset fun k hk ↦ hK.exists_pos_forall_ncard_fixedPoints_iterate_inter_eq
    (fun j hj ↦ hf j (hj.trans_le (Finset.mem_Icc.1 hk).2)) (hnd k hk) (hint k hk)
    (nhdsSet_iUnion_iterate_image_mono (Finset.mem_Icc.1 hk).2 hU)

/-! ### Perturbations keeping the old periodic points -/

section Short

open Metric

omit [FiniteDimensional ℝ E] in
/-- **Avoiding periodic points is `C¹`-open.** If no point of the compact set `K` is fixed by
`f^[j]`, for a `C¹` map `f`, then for all small enough `δ > 0` the same holds for every
differentiable map `g` that is `δ`-close to `f` in value and derivative at every point. -/
theorem eventually_forall_not_isFixedPt_iterate (hK : IsCompact K) (hf : ContDiff ℝ 1 f) (j : ℕ)
    (h : ∀ y ∈ K, ¬IsFixedPt f^[j] y) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ g : E → E, Differentiable ℝ g → (∀ y, ‖g y - f y‖ ≤ δ) →
      (∀ y, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) → ∀ y ∈ K, ¬IsFixedPt g^[j] y := by
  -- The displacement `f^[j] y - y` stays at distance `η > 0` from zero on `K`.
  have hC : IsCompact ((fun y ↦ f^[j] y - y) '' K) :=
    hK.image ((hf.continuous.iterate j).sub continuous_id)
  have h0 : (0 : E) ∉ (fun y ↦ f^[j] y - y) '' K := fun ⟨y, hy, hy0⟩ ↦ h y hy (sub_eq_zero.1 hy0)
  obtain ⟨η, hη, hηC⟩ := Metric.isOpen_iff.1 hC.isClosed.isOpen_compl 0 h0
  filter_upwards [hK.eventually_forall_norm_iterate_sub_le hf j (half_pos hη)]
    with δ hδ g hg hg₀ hg₁ y hy hfix
  have h1 := hδ g hg hg₀ hg₁ y hy
  have h2 : ¬‖f^[j] y - y‖ < η := fun h ↦ hηC (mem_ball_zero_iff.2 h) ⟨y, hy, rfl⟩
  rw [hfix.eq, norm_sub_rev] at h1
  linarith

/-- **No new periodic points appear in a compact set.** Let `f` be `C¹` and let every point of
period `k` of `f` in the compact set `K` be a nondegenerate fixed point of `f^[k]`. For all small
enough `δ > 0`, every differentiable map `g` that is `δ`-close to `f` in value and derivative at
every point, and keeps the points of period `k` of `f` in `K` periodic of period `k`, has no other
points of period `k` in `K`. -/
theorem eventually_forall_fixedPoints_iterate_inter_eq (hK : IsCompact K) (hf : ContDiff ℝ 1 f)
    (k : ℕ) (hnd : ∀ x ∈ K, IsFixedPt f^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ g : E → E, Differentiable ℝ g → (∀ y, ‖g y - f y‖ ≤ δ) →
      (∀ y, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) → fixedPoints f^[k] ∩ K ⊆ fixedPoints g^[k] →
      fixedPoints g^[k] ∩ K = fixedPoints f^[k] ∩ K := by
  set F := fixedPoints f^[k] ∩ K
  have hFfin : F.Finite := (hK.inter_left (isClosed_fixedPoints (hf.continuous.iterate k)))
    |>.finite_of_isNondegenerateFixedPt fun x hx ↦ hnd x hx.2 hx.1
  -- Each point of `F` has a closed ball around it containing no other point of period `k`.
  have hiso (x : E) (hx : x ∈ F) : ∃ ρ > 0, ∀ y ∈ closedBall x ρ, IsFixedPt f^[k] y → y = x :=
    (hnd x hx.2 hx.1).exists_pos_forall_mem_closedBall_isFixedPt_eq
  choose! ρ hρ0 hρ using hiso
  -- On `K₂ = K ∪ ⋃ x ∈ F, closedBall x (ρ x)` the points of period `k` are those of `F`, and they
  -- lie in the interior of `K₂`, so they persist bijectively.
  set K₂ := K ∪ ⋃ x ∈ F, closedBall x (ρ x)
  have hF₂ : fixedPoints f^[k] ∩ K₂ = F := by
    refine Subset.antisymm ?_ fun y hy ↦ ⟨hy.1, Or.inl hy.2⟩
    rintro y ⟨hy, hyK | hyB⟩
    · exact ⟨hy, hyK⟩
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyB
      rw [hρ x hx y hyx hy]
      exact hx
  obtain ⟨δ, hδ, hbij⟩ := (hK.union (hFfin.isCompact_biUnion fun x _ ↦ isCompact_closedBall x _))
    |>.exists_pos_forall_exists_bijOn_fixedPoints_iterate_inter (fun _ _ _ _ ↦ hf.contDiffAt)
      (fun x hx hfix ↦ (hF₂ ▸ ⟨hfix, hx⟩ : x ∈ F) |> fun h ↦ hnd x h.2 h.1)
      (fun x hx hfix ↦ mem_interior.2 ⟨ball x (ρ x), fun y hy ↦ Or.inr (mem_iUnion₂.2
        ⟨x, hF₂ ▸ ⟨hfix, hx⟩, ball_subset_closedBall hy⟩), isOpen_ball,
        mem_ball_self (hρ0 x (hF₂ ▸ ⟨hfix, hx⟩))⟩) univ_mem one_pos
  filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ' g hg hg₀ hg₁ hsub
  obtain ⟨φ, hφ, -⟩ := hbij g (fun y _ ↦ hg y) (fun y _ ↦ (hg₀ y).trans hδ'.2.le)
    (fun y _ ↦ (hg₁ y).trans hδ'.2.le)
  rw [hF₂] at hφ
  -- The points of period `k` of `g` in `K₂` are the image of `F`, and contain `F`.
  have hT : F = fixedPoints g^[k] ∩ K₂ := by
    rw [← hφ.image_eq]
    exact Set.eq_of_subset_of_ncard_le (fun y hy ↦ hφ.image_eq ▸ ⟨hsub hy, Or.inl hy.2⟩)
      (ncard_image_le hFfin) (hFfin.image φ)
  exact Subset.antisymm (fun y hy ↦ hT ▸ (⟨hy.1, Or.inl hy.2⟩ : y ∈ fixedPoints g^[k] ∩ K₂))
    fun y hy ↦ ⟨hsub hy, hy.2⟩

/-- **Nondegeneracy of the covers of short orbits is `C¹`-open.** Let `f` be `C¹`, `K` compact and
`n ≤ N`. Suppose that every point `x ∈ K` fixed by some `f^[j]` with `1 ≤ j ≤ n` is a
nondegenerate fixed point of every `f^[k]`, `1 ≤ k ≤ N`, that fixes it: the periodic orbits of
period at most `n` through `K` are nondegenerate in all their covers of period at most `N`. Then for
all small enough `δ > 0` the same holds for every differentiable map `g` that is `δ`-close to `f`
in value and derivative at every point. -/
theorem eventually_forall_isNondegenerateFixedPt_iterate_of_exists_isFixedPt (hK : IsCompact K)
    (hf : ContDiff ℝ 1 f) {n : ℕ} (hnN : n ≤ N)
    (hnd : ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt f^[k] x →
      (∃ j ∈ Finset.Icc 1 n, IsFixedPt f^[j] x) → IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ g : E → E, Differentiable ℝ g → (∀ y, ‖g y - f y‖ ≤ δ) →
      (∀ y, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) → ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K,
        IsFixedPt g^[k] x → (∃ j ∈ Finset.Icc 1 n, IsFixedPt g^[j] x) →
          IsNondegenerateFixedPt 𝓘(ℝ, E) g^[k] x := by
  -- The points `F` of `K` of period at most `n` are nondegenerate, hence finitely many.
  set F := ⋃ j ∈ Finset.Icc 1 n, fixedPoints f^[j] ∩ K
  have hmemF {j : ℕ} {y : E} (hj : j ∈ Finset.Icc 1 n) (hy : IsFixedPt f^[j] y) (hyK : y ∈ K) :
      y ∈ F :=
    mem_iUnion₂.2 ⟨j, hj, hy, hyK⟩
  have hFfin : F.Finite := (Finset.Icc 1 n).finite_toSet.biUnion fun j hj ↦
    (hK.inter_left (isClosed_fixedPoints (hf.continuous.iterate j)))
      |>.finite_of_isNondegenerateFixedPt fun x hx ↦ hnd j
        (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2.trans hnN⟩) x hx.2 hx.1
        ⟨j, hj, hx.1⟩
  -- Each point of `F` has a closed ball around it containing no other point of period at most `N`.
  have hiso (x : E) (hx : x ∈ F) : ∃ r > 0, ∀ y ∈ closedBall x r, y ≠ x →
      ∀ k ∈ Finset.Icc 1 N, ¬IsFixedPt f^[k] y := by
    have hev : ∀ᶠ y in 𝓝[≠] x, ∀ k ∈ Finset.Icc 1 N, ¬IsFixedPt f^[k] y := by
      refine (eventually_all_finset _).2 fun k hk ↦ ?_
      by_cases hxk : IsFixedPt f^[k] x
      · obtain ⟨j, hj, hjx⟩ := mem_iUnion₂.1 hx
        exact (hnd k hk x hjx.2 hxk ⟨j, hj, hjx.1⟩).eventually_not_isFixedPt
      · exact nhdsWithin_le_nhds
          ((isClosed_fixedPoints (hf.continuous.iterate k)).isOpen_compl.mem_nhds hxk)
    obtain ⟨r, hr, hr'⟩ := (nhdsWithin_hasBasis nhds_basis_closedBall _).eventually_iff.1 hev
    exact ⟨r, hr, fun y hy hyx ↦ hr' ⟨hy, hyx⟩⟩
  choose! r hr0 hr using hiso
  -- On the balls, all points of period at most `N` are points of `F`, which are nondegenerate.
  set L := K ∩ ⋃ x ∈ F, closedBall x (r x)
  have hLnd : ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ L, IsFixedPt f^[k] x →
      IsNondegenerateFixedPt 𝓘(ℝ, E) f^[k] x := by
    rintro k hk x ⟨hxK, hxB⟩ hfix
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hxB
    obtain rfl : x = z := by_contra fun hne ↦ hr z hz x hxz hne k hk hfix
    obtain ⟨j, hj, hjx⟩ := mem_iUnion₂.1 hz
    exact hnd k hk x hxK hfix ⟨j, hj, hjx.1⟩
  obtain ⟨δ₁, hδ₁, hpers⟩ := (hK.inter_right (hFfin.isClosed_biUnion fun x _ ↦ isClosed_closedBall))
    |>.exists_pos_forall_mem_Icc_isNondegenerateFixedPt_iterate (fun _ _ _ _ ↦ hf.contDiffAt) hLnd
      univ_mem
  -- Off the balls, `K` has no point of period at most `n`, and this persists.
  set K' := K \ ⋃ x ∈ F, ball x (r x)
  have havoid (j : ℕ) (hj : j ∈ Finset.Icc 1 n) := (hK.diff (isOpen_biUnion fun _ _ ↦ isOpen_ball))
    |>.eventually_forall_not_isFixedPt_iterate hf j fun y hy hfix ↦
      hy.2 (mem_iUnion₂.2 ⟨y, hmemF hj hfix hy.1, mem_ball_self (hr0 y (hmemF hj hfix hy.1))⟩)
  filter_upwards [Ioo_mem_nhdsGT hδ₁, (eventually_all_finset _).2 havoid]
    with δ hδ hav g hg hg₀ hg₁ k hk x hxK hfix ⟨j, hj, hjx⟩
  by_cases hxB : x ∈ ⋃ z ∈ F, ball z (r z)
  · obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hxB
    exact hpers g (fun y _ ↦ hg y) (fun y _ ↦ (hg₀ y).trans hδ.2.le)
      (fun y _ ↦ (hg₁ y).trans hδ.2.le) k hk x
      ⟨hxK, mem_iUnion₂.2 ⟨z, hz, ball_subset_closedBall hxz⟩⟩ hfix
  · exact absurd hjx (hav j hj g hg hg₀ hg₁ x ⟨hxK, hxB⟩)

end Short

end IsCompact

namespace TauCeti

open Metric

/-! ### Openness under composition with maps close to the identity -/

/-- A compact neighbourhood of the first `l` points of the orbits of a compact set under a
continuous map. -/
theorem exists_isCompact_mem_nhdsSet_iUnion_iterate_image {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] {g : X → X} (hg : Continuous g) {C : Set X} (hC : IsCompact C)
    (l : ℕ) : ∃ U, IsCompact U ∧ U ∈ 𝓝ˢ (⋃ j < l, g^[j] '' C) := by
  obtain ⟨U, hU, hOU⟩ := exists_compact_superset <|
    (finite_lt_nat l).isCompact_biUnion fun j _ ↦ hC.image (hg.iterate j)
  exact ⟨U, hU, subset_interior_iff_mem_nhdsSet.1 hOU⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Avoidance is `C¹`-open.** If the `l`-th iterate of a `C¹` map `g` sends every point `y` of a
compact set `C` to a point `z` with `(y, z)` off a closed set `T`, then so does the `l`-th iterate
of `g ∘ ψ` for every `ψ` close enough to the identity in `C¹`. -/
theorem eventually_forall_isNearId_iterate_comp_notMem {g : E → E} (hg : ContDiff ℝ 1 g)
    {C : Set E} (hC : IsCompact C) (l : ℕ) {T : Set (E × E)} (hT : IsClosed T)
    (h : ∀ y ∈ C, (y, g^[l] y) ∉ T) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ ψ, IsNearId ℝ η ψ → ∀ y ∈ C, (y, (g ∘ ψ)^[l] y) ∉ T := by
  -- The graph of `g^[l]` over `C` is compact and avoids `T`, hence so does a neighbourhood of it.
  have hG : IsCompact ((fun y ↦ (y, g^[l] y)) '' C) :=
    hC.image (continuous_id.prodMk (hg.continuous.iterate l))
  obtain ⟨θ, hθ, hθT⟩ := hG.exists_cthickening_subset_open hT.isOpen_compl
    (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
  obtain ⟨U, hU, hUn⟩ := exists_isCompact_mem_nhdsSet_iUnion_iterate_image hg.continuous hC l
  obtain ⟨δ, hδ, hit⟩ := hC.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le
    (fun _ _ _ _ ↦ hg.contDiffAt) hθ hUn
  refine eventually_forall_isNearId_comp (Q := fun g' ↦ ∀ y ∈ C, (y, g'^[l] y) ∉ T) hg hU
    ⟨δ, hδ, fun g' hg' hg'₀ hg'₁ y hy ↦ hθT ?_⟩
  refine mem_cthickening_of_dist_le _ (y, g^[l] y) θ _ (mem_image_of_mem _ hy) ?_
  simpa [Prod.dist_eq, dist_eq_norm, hθ.le] using (hit g' hg' hg'₀ hg'₁ y hy).2.1

/-- **Nondegeneracy is `C¹`-open under composition with maps close to the identity.** If the
points of period `k` of a `C¹` map `g` in a compact set `L` are nondegenerate, so are those of
`g ∘ ψ` for every `ψ` close enough to the identity in `C¹`. -/
theorem eventually_forall_isNearId_isNondegenerateFixedPt_iterate_comp {g : E → E}
    (hg : ContDiff ℝ 1 g) {L : Set E} (hL : IsCompact L) (k : ℕ)
    (hnd : ∀ x ∈ L, IsFixedPt g^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, E) g^[k] x) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ ψ, IsNearId ℝ η ψ →
      ∀ x ∈ L, IsFixedPt (g ∘ ψ)^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, E) (g ∘ ψ)^[k] x := by
  obtain ⟨U, hU, hUn⟩ := exists_isCompact_mem_nhdsSet_iUnion_iterate_image hg.continuous hL k
  exact eventually_forall_isNearId_comp hg hU
    (hL.exists_pos_forall_isNondegenerateFixedPt_iterate (fun _ _ _ _ ↦ hg.contDiffAt) hnd hUn)

end TauCeti
