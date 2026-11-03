/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Principal

/-!
# Principal cycles

This file defines the principal cycle `div(r) = Σ_x ord_x(r) [x]` of a nonzero rational function
`r` on a locally Noetherian integral scheme, as one of Mathlib's algebraic cycles, following
[Stacks, Section 42.17](https://stacks.math.columbia.edu/tag/02RO).

* `Scheme.exists_mem_nhds_finite_inter_support_ord`: the orders of vanishing of a nonzero rational
  function have locally finite support. The function is a unit on a nonempty open `U`, and on a
  Noetherian open only finitely many codimension-one points lie outside `U`.
* `AlgebraicCycle.div r`: the principal cycle of `r`, with `div(r s) = div r + div s`,
  `div(r⁻¹) = -div r` and `div 1 = 0`.
-/

public section

open AlgebraicGeometry Order Topology TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]

namespace Scheme

/-- The orders of a nonzero rational function on a locally Noetherian integral scheme have locally
finite support. The function is a unit on a nonempty open `U`, where its orders vanish, and a
Noetherian open `V` contains only finitely many codimension-one points outside `U`
(`SchemeWeilDivisor.finite_setOfPred_not_mem`). -/
lemma exists_mem_nhds_finite_inter_support_ord (r : W.functionFieldˣ) (z : W) :
    ∃ t ∈ 𝓝 z, (t ∩ Function.support fun x ↦ W.ord (r : W.functionField) x).Finite := by
  obtain ⟨U, -, f, hU, hfr, hf⟩ := exists_isUnit_germ_eq W (r : W.functionField) r.ne_zero
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : IsNoetherianRing Γ(W, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace (Scheme.Opens.toScheme V) := noetherianSpace_of_isAffineOpen V hV
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have : Nonempty ((Scheme.Opens.ι V) ⁻¹ᵁ U) := by
    obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen
      (Set.nonempty_coe_sort.mp hU) ⟨z, hzV⟩
    exact ⟨⟨⟨x, hxV⟩, hxU⟩⟩
  refine ⟨V, V.isOpen.mem_nhds hzV, ((SchemeWeilDivisor.finite_setOfPred_not_mem
    ((Scheme.Opens.ι V) ⁻¹ᵁ U)).image fun x ↦ (Scheme.Opens.ι V) x.1).subset ?_⟩
  rintro x ⟨hxV, hx⟩
  have hx1 : coheight x = 1 := by
    by_contra h
    exact hx (W.ord_eq_zero_of_coheight_neq_one h _)
  have hxU : x ∉ U := fun hxU ↦ hx (by rw [← hfr]; exact W.ord_of_isUnit hf hxU)
  obtain ⟨y, rfl⟩ : x ∈ Set.range (Scheme.Opens.ι V) := by rwa [Scheme.Opens.range_ι]
  exact ⟨⟨y, (coheight_eq_of_isOpenImmersion (Scheme.Opens.ι V)).symm.trans hx1⟩, hxU, rfl⟩

end Scheme

namespace AlgebraicCycle

/-- The principal cycle `div(r) = Σ_x ord_x(r) [x]` of a nonzero rational function `r` on a locally
Noetherian integral scheme, with coefficients Mathlib's orders of vanishing `Scheme.ord`. These
vanish away from the points of codimension one. -/
noncomputable def div (r : W.functionFieldˣ) : AlgebraicCycle W ℤ where
  toFun x := W.ord (r : W.functionField) x
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' z _ := Scheme.exists_mem_nhds_finite_inter_support_ord r z

/-- The coefficients of `div r` are the orders of vanishing of `r`. -/
@[simp]
lemma div_apply (r : W.functionFieldˣ) (x : W) : div r x = W.ord (r : W.functionField) x :=
  (rfl)

/-- `div(r s) = div r + div s`. -/
@[simp]
lemma div_mul (r s : W.functionFieldˣ) : div (r * s) = div r + div s := by
  ext x
  simp [Scheme.ord_mul r.ne_zero s.ne_zero]

/-- `div(r⁻¹) = -div r`. -/
@[simp]
lemma div_inv (r : W.functionFieldˣ) : div r⁻¹ = -div r := by
  ext x
  simp [Scheme.ord_inv]

/-- The principal cycle of the constant function one vanishes. -/
@[simp]
lemma div_one : div (1 : W.functionFieldˣ) = 0 := by
  ext x
  simp

end AlgebraicCycle

end TauCeti.AlgebraicGeometry
