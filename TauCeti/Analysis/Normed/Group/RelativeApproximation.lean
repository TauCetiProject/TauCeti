/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-!
# Maps within relative error of an additive map

A map `f : U → V` from an additive group to a seminormed additive group is within relative error
`δ` of an additive map `A` on a set `p` when `‖f x - f y - A (x - y)‖ ≤ δ * ‖A (x - y)‖` for all
`x y ∈ p`. Such a map satisfies `(1 - δ) ‖A x - A y‖ ≤ ‖f x - f y‖ ≤ (1 + δ) ‖A x - A y‖` on `p`.
If `A` is injective and the relative error is some `ε < 1`, then `f ∘ invFun A` is therefore
`(1 + ε)`-Lipschitz and `(1 - ε)⁻¹`-antilipschitz on `A '' p`. If `U` also carries a
pseudo-emetric for which `A` is `c`-antilipschitz and `δ < 1`, then `f` is
`c (1 - δ)⁻¹`-antilipschitz on `p` (`AntilipschitzWith.domRestrict_of_approx`).

These estimates turn a piecewise approximation of a differentiable map by linear maps, with
small relative error, into bi-Lipschitz bounds on each piece; the decomposition into injective
pieces used by the area formula is built this way.
-/

public section

open Set Function
open scoped NNReal

namespace TauCeti

section AddGroup

variable {U V 𝓕 : Type*} [AddGroup U] [SeminormedAddCommGroup V] [FunLike 𝓕 U V]
  [AddMonoidHomClass 𝓕 U V] {f : U → V} {p : Set U} {A : 𝓕} {δ : ℝ}

/-- A map within relative error `δ` of an additive map `A` on `p` satisfies
`(1 - δ) ‖A x - A y‖ ≤ ‖f x - f y‖` there. -/
theorem one_sub_mul_norm_sub_le_norm_sub
    (happ : ∀ x ∈ p, ∀ y ∈ p, ‖f x - f y - A (x - y)‖ ≤ δ * ‖A (x - y)‖) {x y : U} (hx : x ∈ p)
    (hy : y ∈ p) : (1 - δ) * ‖A x - A y‖ ≤ ‖f x - f y‖ := by
  have h := happ x hx y hy
  rw [map_sub] at h
  have := norm_sub_norm_le (A x - A y) (f x - f y)
  rw [norm_sub_rev (A x - A y)] at this
  linarith

/-- A map within relative error `δ` of an additive map `A` on `p` satisfies
`‖f x - f y‖ ≤ (1 + δ) ‖A x - A y‖` there. -/
theorem norm_sub_le_one_add_mul_norm_sub
    (happ : ∀ x ∈ p, ∀ y ∈ p, ‖f x - f y - A (x - y)‖ ≤ δ * ‖A (x - y)‖) {x y : U} (hx : x ∈ p)
    (hy : y ∈ p) : ‖f x - f y‖ ≤ (1 + δ) * ‖A x - A y‖ := by
  have h := happ x hx y hy
  rw [map_sub] at h
  have := norm_sub_norm_le (f x - f y) (A x - A y)
  linarith

/-- A map `f` within relative error `ε < 1` of an injective additive map `A` on `p`, read through
`A`, is `(1 + ε)`-Lipschitz and `(1 - ε)⁻¹`-antilipschitz on `A '' p`. -/
theorem _root_.Function.Injective.lipschitzOnWith_and_antilipschitzWith_of_approx {ε : ℝ≥0}
    (hA : Injective A) (hε : ε < 1)
    (happ : ∀ x ∈ p, ∀ y ∈ p, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) :
    LipschitzOnWith (1 + ε) (f ∘ invFun A) (A '' p) ∧
      AntilipschitzWith (1 - ε)⁻¹ ((A '' p).domRestrict (f ∘ invFun A)) := by
  have hinv (x : U) : invFun A (A x) = x := leftInverse_invFun hA x
  have hε' : (0 : ℝ) < ((1 - ε : ℝ≥0) : ℝ) := NNReal.coe_pos.2 (tsub_pos_of_lt hε)
  refine ⟨LipschitzOnWith.of_dist_le_mul ?_, AntilipschitzWith.of_le_mul_dist ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [comp_apply, hinv, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
    exact norm_sub_le_one_add_mul_norm_sub happ hx hy
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    simp only [Subtype.dist_eq, domRestrict_apply, comp_apply, hinv, dist_eq_norm, NNReal.coe_inv]
    rw [le_inv_mul_iff₀ hε', NNReal.coe_sub hε.le, NNReal.coe_one]
    exact one_sub_mul_norm_sub_le_norm_sub happ hx hy

/-- A map within relative error `δ < 1` of a `c`-antilipschitz additive map `A` on `p` is
`c (1 - δ)⁻¹`-antilipschitz on `p`. -/
theorem _root_.AntilipschitzWith.domRestrict_of_approx [PseudoEMetricSpace U] {c : ℝ≥0}
    (hA : AntilipschitzWith c A) (hδ : δ < 1)
    (happ : ∀ x ∈ p, ∀ y ∈ p, ‖f x - f y - A (x - y)‖ ≤ δ * ‖A (x - y)‖) :
    AntilipschitzWith (c * (Real.toNNReal (1 - δ))⁻¹) (p.domRestrict f) := by
  -- `A` is antilipschitz into a metric space, so all distances in `U` are finite.
  let : PseudoMetricSpace U := PseudoEMetricSpace.toPseudoMetricSpace hA.edist_ne_top
  have hδ' : 0 < 1 - δ := sub_pos.2 hδ
  refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
  have hxy : dist (x : U) y ≤ c * ‖A x - A y‖ := by
    simpa only [dist_eq_norm] using hA.le_mul_dist (x : U) y
  have h := one_sub_mul_norm_sub_le_norm_sub happ x.2 y.2
  simp only [Subtype.dist_eq, domRestrict_apply, dist_eq_norm, NNReal.coe_mul, NNReal.coe_inv,
    Real.coe_toNNReal _ hδ'.le]
  calc dist (x : U) y ≤ c * ‖A x - A y‖ := hxy
    _ ≤ c * ((1 - δ)⁻¹ * ‖f x - f y‖) := by
        gcongr
        rwa [le_inv_mul_iff₀ hδ']
    _ = c * (1 - δ)⁻¹ * ‖f x - f y‖ := by ring

end AddGroup

end TauCeti
