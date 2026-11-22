/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Perturbation
public import TauCeti.Dynamics.FixedPoints.Persistence
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

end IsCompact
