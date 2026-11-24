/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Basic
public import TauCeti.Topology.Homotopy.Monodromy.SignCharacter

/-!
# Monodromy of the sign local system of a double cover

Let `p : E → X` be a double cover whose fibres are the pairs `{e, σ e}` with `σ e ≠ e`. Transport
in its sign local system along a loop `g` at `x` is multiplication by the sign character of `g`
(`IsCoveringMap.signLocalSystemObjEquiv_map_asHom_apply`), because monodromy along the inverse of
`g` multiplies a function changing sign under `σ` by that character
(`IsCoveringMap.apply_monodromy_inv_asHom_of_mem_signFiber`): the lift of `g` either closes up, and
transport is the identity, or exchanges the two points of the fibre, and transport negates the
functions changing sign under `σ`. So the sign character is the monodromy of the sign local
system. For the orientation double cover of a real vector bundle this says that the orientation
character is the monodromy of the orientation local system.

## Main results

* `IsCoveringMap.apply_monodromy_inv_asHom_of_mem_signFiber`: monodromy along the inverse of a
  loop multiplies a function changing sign by the sign character of the loop.
* `IsCoveringMap.signLocalSystemObjEquiv_map_asHom_apply`: transport in the sign local system
  along a loop is multiplication by its sign character.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficient systems and the orientation
  system).
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace IsCoveringMap

section DoubleCover

variable {E : Type w} [TopologicalSpace E] {X : Type*} [TopologicalSpace X] {p : E → X}
  {R : Type u} [Ring R] (hp : IsCoveringMap p) {σ : E → E} {hσ : p ∘ σ = p}
  (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

include hfix hfib in
/-- **Monodromy multiplies functions changing sign by the sign character.** A function `φ` on
the fibre over `x` changing sign under `σ`, evaluated at the endpoint of the lift of the inverse
of a loop `g`, is `φ` multiplied by the sign character of `g`. -/
theorem apply_monodromy_inv_asHom_of_mem_signFiber {x : X} (hx : (p ⁻¹' {x}).Finite)
    (g : FundamentalGroup X x) {φ : p ⁻¹' {x} → R} (hφ : φ ∈ TauCeti.signFiber R σ hσ x)
    (e : p ⁻¹' {x}) :
    φ (hp.monodromy (inv g.asHom) e) = (hp.signCharacter hx g : ℤ) • φ e := by
  -- The inverse arrow is the class of the inverse loop, whose character is the same. In `π₁`
  -- the product `g⁻¹ * g` is the composite `g ≫ g⁻¹` of arrows.
  have hinv : inv g.asHom = (g⁻¹).toPath :=
    IsIso.inv_eq_of_hom_inv_id
      (congrArg (fun q : FundamentalGroup X x ↦ q.asHom) (inv_mul_cancel g))
  have hχ : hp.signCharacter hx g⁻¹ = hp.signCharacter hx g := by
    rw [map_inv, Int.units_inv_eq_self]
  rw [hinv]
  rcases Int.units_eq_one_or (hp.signCharacter hx g) with h | h
  · rw [(hp.signCharacter_eq_one_iff_monodromy_eq hfib hx g⁻¹ e).1 (hχ.trans h), h,
      Units.val_one, one_smul]
  · have hm : hp.monodromy (g⁻¹).toPath e = Function.fiberMap σ hσ x e :=
      Subtype.ext (((hp.signCharacter_eq_neg_one_iff hfix hfib hx g⁻¹ e).1 (hχ.trans h)).trans
        (Function.fiberMap_apply_coe σ hσ x e).symm)
    rw [hm, h, Units.val_neg, Units.val_one, neg_one_zsmul]
    exact TauCeti.mem_signFiber_iff.1 hφ e

end DoubleCover

variable {E : Type w} [TopologicalSpace E] {X : TopCat.{v}} {p : E → X} {R : Type u} [Ring R]
  (hp : IsCoveringMap p) {σ : C(E, E)} {hσ : p ∘ σ = p} (hfix : ∀ e, σ e ≠ e)
  (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

include hfix hfib in
/-- **Transport in the sign local system along a loop is multiplication by its sign
character.** Evaluated at a point `e` of the fibre, transport along a loop `g` at `x` multiplies
by the sign of the monodromy permutation of `g`. -/
theorem signLocalSystemObjEquiv_map_asHom_apply {x : X} (hx : (p ⁻¹' {x}).Finite)
    (g : FundamentalGroup X x) (f : (hp.signLocalSystem R σ hσ).obj (FundamentalGroupoid.mk x))
    (e : p ⁻¹' {x}) :
    (hp.signLocalSystemObjEquiv σ hσ _ (((hp.signLocalSystem R σ hσ).map g.asHom).hom f) :
      p ⁻¹' {x} → R) e =
      (hp.signCharacter hx g : ℤ) • (hp.signLocalSystemObjEquiv σ hσ _ f : p ⁻¹' {x} → R) e := by
  rw [signLocalSystemObjEquiv_map_apply]
  exact hp.apply_monodromy_inv_asHom_of_mem_signFiber hfix hfib hx g
    (hp.signLocalSystemObjEquiv σ hσ _ f).property e

end IsCoveringMap
