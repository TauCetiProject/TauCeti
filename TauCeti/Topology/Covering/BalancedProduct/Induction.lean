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

## Main definitions

* `TauCeti.BalancedProduct.inducedLift`: the map `⟦g, z⟧ ↦ g⁻¹ • ι z` induced by a `K`-map `ι`,
  `G`-equivariant (`inducedLift_mul_inv`), restricting to `ι` (`inducedLift_mk_one`) and the only
  `G`-map doing so (`eq_inducedLift`).

## Main results

* `TauCeti.BalancedProduct.apply_mk_eq_inv_smul_apply_mk_one`: a `G`-map sends `⟦g, z⟧` to
  `g⁻¹ • f ⟦1, z⟧`.
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

/-- The map `⟦g, z⟧ ↦ g⁻¹ • ι z` out of the balanced product, for a `K`-map `ι : Z → Y`: the
inverse of restriction in the universal property of induction
(`TauCeti.bijOn_balancedProduct_lift`). -/
def BalancedProduct.inducedLift {ι : Z → Y} (hι : ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z) :
    BalancedProduct K G Z → Y :=
  Quotient.lift (fun p : G × Z ↦ p.1⁻¹ • ι p.2) fun _ _ ⟨h, hh⟩ ↦ by
    rw [← hh]
    simp only [Prod.smul_fst, Prod.smul_snd, hι, Subgroup.smul_def, smul_eq_mul, mul_inv_rev,
      mul_smul, inv_smul_smul]

/-- The induced map sends the class of `(g, z)` to `g⁻¹ • ι z`. -/
@[simp]
theorem BalancedProduct.inducedLift_mk {ι : Z → Y}
    (hι : ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z) (g : G) (z : Z) :
    inducedLift K Z Y hι (mk K g z) = g⁻¹ • ι z :=
  (rfl)

/-- The induced map is `G`-equivariant: `a` acts on the balanced product by
`⟦g, z⟧ ↦ ⟦g a⁻¹, z⟧`. -/
theorem BalancedProduct.inducedLift_mul_inv {ι : Z → Y}
    (hι : ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z) (a g : G) (z : Z) :
    inducedLift K Z Y hι (mk K (g * a⁻¹) z) = a • inducedLift K Z Y hι (mk K g z) := by
  simp [mul_smul]

/-- Restricting the induced map along `z ↦ ⟦1, z⟧` gives back `ι`. Not `@[simp]`: `simp` proves
it from `inducedLift_mk`. -/
theorem BalancedProduct.inducedLift_mk_one {ι : Z → Y}
    (hι : ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z) (z : Z) :
    inducedLift K Z Y hι (mk K 1 z) = ι z := by
  simp

variable {K Z Y}

/-- A `G`-map out of the balanced product is determined by its values on the classes `⟦1, z⟧`:
it sends `⟦g, z⟧` to `g⁻¹ • f ⟦1, z⟧`. -/
theorem BalancedProduct.apply_mk_eq_inv_smul_apply_mk_one {f : BalancedProduct K G Z → Y}
    (hf : ∀ (a g : G) (z : Z), f (mk K (g * a⁻¹) z) = a • f (mk K g z)) (g : G) (z : Z) :
    f (mk K g z) = g⁻¹ • f (mk K 1 z) := by
  simpa using hf g⁻¹ 1 z

/-- The restriction of a `G`-map out of the balanced product along `z ↦ ⟦1, z⟧` is a `K`-map. -/
theorem BalancedProduct.apply_mk_one_smul {f : BalancedProduct K G Z → Y}
    (hf : ∀ (a g : G) (z : Z), f (mk K (g * a⁻¹) z) = a • f (mk K g z)) (h : K) (z : Z) :
    f (mk K 1 (h • z)) = (h : G) • f (mk K 1 z) := by
  rw [mk_smul_right, apply_mk_eq_inv_smul_apply_mk_one hf]
  simp [Subgroup.smul_def]

/-- **Uniqueness of the induced map**: a `G`-map out of the balanced product which restricts to
`ι` along `z ↦ ⟦1, z⟧` is the induced map. -/
theorem BalancedProduct.eq_inducedLift {f : BalancedProduct K G Z → Y}
    (hf : ∀ (a g : G) (z : Z), f (mk K (g * a⁻¹) z) = a • f (mk K g z)) {ι : Z → Y}
    (hι : ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z) (hfι : ∀ z, f (mk K 1 z) = ι z) :
    f = inducedLift K Z Y hι := by
  funext x
  induction x using BalancedProduct.ind with
  | h g z => rw [apply_mk_eq_inv_smul_apply_mk_one hf, hfι, inducedLift_mk]

/-- The induced map of the restriction of a `G`-map is that `G`-map. -/
theorem BalancedProduct.inducedLift_apply_mk_one {f : BalancedProduct K G Z → Y}
    (hf : ∀ (a g : G) (z : Z), f (mk K (g * a⁻¹) z) = a • f (mk K g z)) :
    inducedLift K Z Y (ι := fun z ↦ f (mk K 1 z)) (apply_mk_one_smul hf) = f :=
  (eq_inducedLift hf _ fun _ ↦ rfl).symm

variable (K Z Y)

/-- **The universal property of induction.** For a subgroup `K` of `G`, a `K`-set `Z` and a
`G`-set `Y`, restricting along `z ↦ ⟦1, z⟧` is a bijection from the `G`-maps out of the balanced
product `TauCeti.BalancedProduct K G Z` to `Y` onto the `K`-maps `Z → Y`, with inverse
`TauCeti.BalancedProduct.inducedLift`, `ι ↦ (⟦g, z⟧ ↦ g⁻¹ • ι z)`. -/
theorem bijOn_balancedProduct_lift :
    Set.BijOn (fun (f : BalancedProduct K G Z → Y) (z : Z) ↦ f (mk K (1 : G) z))
      {f | ∀ (a g : G) (z : Z), f (mk K (g * a⁻¹) z) = a • f (mk K g z)}
      {ι | ∀ (h : K) (z : Z), ι (h • z) = (h : G) • ι z} := by
  refine ⟨fun f hf ↦ BalancedProduct.apply_mk_one_smul hf, fun f hf f' hf' hff' ↦ ?_,
    fun ι hι ↦ ⟨BalancedProduct.inducedLift K Z Y hι, BalancedProduct.inducedLift_mul_inv K Z Y hι,
      funext (BalancedProduct.inducedLift_mk_one K Z Y hι)⟩⟩
  funext x
  induction x using BalancedProduct.ind with
  | h g z =>
    rw [BalancedProduct.apply_mk_eq_inv_smul_apply_mk_one hf,
      BalancedProduct.apply_mk_eq_inv_smul_apply_mk_one hf']
    exact congrArg _ (congrFun hff' z)

end TauCeti
