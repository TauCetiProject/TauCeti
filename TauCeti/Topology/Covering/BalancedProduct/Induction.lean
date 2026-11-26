/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.BalancedProduct.Basic

/-!
# The universal property of induction of group actions

Let `K` be a subgroup of a group `G` and `Z` a `K`-set. With `K` acting on `G` by left
multiplication, the balanced product `TauCeti.BalancedProduct K G Z` is the quotient of `G × Z`
by `h • (g, z) = (h g, h • z)`. It is a `G`-set under `a • ⟦g, z⟧ = ⟦g a⁻¹, z⟧`, and through
`⟦g, z⟧ ↦ ⟦g⁻¹, z⟧` it is the induced `G`-set `G ×_K Z`, with `G` acting on the left factor.

This file proves its universal property: for a `G`-set `Y`, restricting a `G`-map
`f : BalancedProduct K G Z → Y` along `z ↦ ⟦1, z⟧` is a bijection onto the `K`-maps `Z → Y`, with
inverse `ι ↦ (⟦g, z⟧ ↦ g⁻¹ • ι z)` (`TauCeti.bijOn_balancedProduct_lift`). So `z ↦ ⟦1, z⟧` is a
universal arrow from `Z` to restriction of the action from `G` to `K`.

The `G`-maps are stated as functions satisfying `f ⟦g a⁻¹, z⟧ = a • f ⟦g, z⟧`, so that no
`G`-action on the balanced product has to be chosen as an instance.

## Main results

* `TauCeti.bijOn_balancedProduct_lift`: **the universal property of induction.**

## References

Induced `G`-sets are standard; compare G. E. Bredon, *Introduction to Compact Transformation
Groups*, Academic Press, 1972, Section II.2, for the twisted products `G ×_K A`.
-/

public section

namespace TauCeti

open BalancedProduct

variable {G : Type*} [Group G] (K : Subgroup G) (Z : Type*) [MulAction K Z] (Y : Type*)
  [MulAction G Y]

/-- The map `⟦g, z⟧ ↦ g⁻¹ • ι z` out of the balanced product, for a `K`-map `ι : Z → Y`. -/
private def inducedLift {ι : Z → Y} (hι : ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z) :
    BalancedProduct K G Z → Y :=
  Quotient.lift (fun p : G × Z ↦ p.1⁻¹ • ι p.2) fun _ _ ⟨h, hh⟩ ↦ by
    rw [← hh]
    simp only [Prod.smul_fst, Prod.smul_snd, hι, Subgroup.smul_def, smul_eq_mul, mul_inv_rev,
      mul_smul, inv_smul_smul]

private theorem inducedLift_mk {ι : Z → Y} (hι : ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z)
    (g : G) (z : Z) : inducedLift K Z Y hι (mk K g z) = g⁻¹ • ι z :=
  (rfl)

/-- **The universal property of induction.** For a subgroup `K` of `G`, a `K`-set `Z` and a
`G`-set `Y`, restricting along `z ↦ ⟦1, z⟧` is a bijection from the `G`-maps out of the balanced
product `TauCeti.BalancedProduct K G Z` to `Y` onto the `K`-maps `Z → Y`, with inverse
`ι ↦ (⟦g, z⟧ ↦ g⁻¹ • ι z)`. -/
theorem bijOn_balancedProduct_lift :
    Set.BijOn (fun (f : BalancedProduct K G Z → Y) (z : Z) ↦ f (mk K (1 : G) z))
      {f | ∀ (a g : G) (z : Z), f (mk K (g * a⁻¹) z) = a • f (mk K g z)}
      {ι | ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z} := by
  -- The class of `(1, h • z)` is that of `(1 * h⁻¹, z)`, and every class is that of `(1 * a⁻¹, z)`.
  have hmk (h : K) (z : Z) : mk K (1 : G) (h • z) = mk K ((1 : G) * (h : G)⁻¹) z := by
    have h' := mk_smul_left (G := K) h⁻¹ (1 : G) z
    rw [inv_inv] at h'
    rw [← h', Subgroup.smul_def, smul_eq_mul, mul_one, one_mul, Subgroup.coe_inv]
  refine ⟨fun f hf h z ↦ ?_, fun f hf f' hf' hff' ↦ ?_, fun ι hι ↦ ?_⟩
  · change f (mk K 1 (h • z)) = (h : G) • f (mk K 1 z)
    rw [hmk, hf]
  · funext x
    induction x using Quotient.inductionOn with
    | h p =>
      obtain ⟨g, z⟩ := p
      have hg : mk K g z = mk K ((1 : G) * g⁻¹⁻¹) z := by rw [inv_inv, one_mul]
      change f (mk K g z) = f' (mk K g z)
      rw [hg, hf, hf']
      exact congrArg _ (congrFun hff' z)
  · refine ⟨inducedLift K Z Y hι, fun a g z ↦ ?_, funext fun z ↦ ?_⟩
    · rw [inducedLift_mk, inducedLift_mk, mul_inv_rev, inv_inv, mul_smul]
    · change inducedLift K Z Y hι (mk K 1 z) = ι z
      rw [inducedLift_mk, inv_one, one_smul]

end TauCeti
