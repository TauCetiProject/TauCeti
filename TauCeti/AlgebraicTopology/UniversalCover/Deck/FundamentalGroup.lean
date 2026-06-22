/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.AlgebraicTopology.UniversalCover.Deck.QuotientCovering
import Mathlib.Topology.Homotopy.Lifting

/-!
# The fundamental group of the base of a regular cover and its deck group

For a covering map `p : E → X` with **simply connected** total space whose deck action is
**regular** (`p` surjective, with `Deck p` acting transitively on every fibre), the
fundamental group of the base is anti-isomorphic to the deck transformation group:

  `FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ`.

This is the Stage 1 target of the universal-covers roadmap
(`Deck (UniversalCover.proj x₀) ≃* FundamentalGroup X x₀`, "possibly up to `ᵐᵒᵖ`; pin the
action/composition convention first"). It is stated here for an arbitrary regular cover with
simply connected total space, of which the universal cover is the special case
`E = UniversalCover x₀` (where simple connectivity and regularity of the deck action hold).

The `ᵐᵒᵖ` is genuine and pins the convention noted in the roadmap. The deck group acts on
the total space on the *left* (`Deck.smul_eq_apply : φ • e = φ.1 e`), while the monodromy of
`π₁(X, x)` acts on each fibre on the *right* (`monodromy (γ.trans γ') = monodromy γ' ∘
monodromy γ`); choosing a basepoint lift `e` in the fibre and matching the deck element that
realises a monodromy therefore reverses multiplication, so the natural isomorphism lands in
`(Deck p)ᵐᵒᵖ`.

The isomorphism is Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv`, instantiated at
the group `Deck p` through `Deck.IsRegular.isQuotientCoveringMap`: a regular preconnected
covering exhibits its base as the quotient of the total space by `Deck p`, and for a simply
connected total space Mathlib's quotient-covering machinery identifies the deck group with
`π₁` of the base. As a corollary, choosing a basepoint lift `e` in the fibre over `x`
identifies `π₁(X, x)` with that fibre via monodromy.

## Main declarations

* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeckOp`: the anti-isomorphism
  `FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ`.
* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeckOp_unop_smul`: the deck element
  attached to `γ` moves the chosen lift `e` to `monodromy γ e`.
* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeckOp_eq_iff`: characterizes equality
  with an arbitrary deck transformation by its value at the chosen lift.
* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeckOp_eq_one_iff`: `γ` maps to the
  identity exactly when its monodromy fixes `e`.

## References

The comparison map is Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` (Junyan Xu,
`Mathlib/Topology/Homotopy/Lifting.lean`); the quotient-covering presentation of a regular
deck action is `TauCeti.Deck.IsRegular.isQuotientCoveringMap`. This discharges the Stage 1
target of the Tau Ceti universal-covers roadmap.
-/

namespace TauCeti

namespace Deck

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}

/-- For a regular covering map `p : E → X` with simply connected total space, the fundamental
group of the base is anti-isomorphic to the deck transformation group:
`FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ`. The `ᵐᵒᵖ` reflects that the deck group acts on the
left while the monodromy of `π₁` acts on the right; see the module docstring. -/
noncomputable def IsRegular.fundamentalGroupMulEquivDeckOp [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ :=
  (hreg.isQuotientCoveringMap hp).fundamentalGroupEquiv e

/-- The deck transformation attached to a loop class `γ` moves the chosen basepoint lift `e`
along the monodromy of `γ`. -/
@[simp]
lemma IsRegular.fundamentalGroupMulEquivDeckOp_unop_smul [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (hreg.fundamentalGroupMulEquivDeckOp hp e γ).unop • (e : E) = (hp.monodromy γ e : E) :=
  (hreg.isQuotientCoveringMap hp).unop_fundamentalGroupToMulOpposite_smul

/-- The fundamental group element `γ` corresponds to a deck transformation `g` exactly when
`g.unop` moves the chosen lift `e` to the monodromy translate of `e` along `γ`. -/
lemma IsRegular.fundamentalGroupMulEquivDeckOp_eq_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) (g : (Deck p)ᵐᵒᵖ) :
    hreg.fundamentalGroupMulEquivDeckOp hp e γ = g ↔
      g.unop • (e : E) = hp.monodromy γ e :=
  (hreg.isQuotientCoveringMap hp).fundamentalGroupToMulOpposite_apply_eq_Iff

/-- A loop class `γ` maps to the identity deck transformation exactly when its monodromy
fixes the chosen basepoint lift `e`. -/
@[simp]
lemma IsRegular.fundamentalGroupMulEquivDeckOp_eq_one_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    hreg.fundamentalGroupMulEquivDeckOp hp e γ = 1 ↔ hp.monodromy γ e = e :=
  (hreg.isQuotientCoveringMap hp).fundamentalGroupToMulOpposite_eq_one_iff

end Deck

end TauCeti
