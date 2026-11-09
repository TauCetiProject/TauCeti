/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Trace

/-!
# Skew-zigzag algebras are self-injective

The normalized functional of a finite skew-zigzag relation quotient without isolated vertices is
Frobenius. Consequently the algebra is left and right self-injective over every field. The skew
parameters need not be gauge-equivalent to the ordinary parameter, and no symmetry assumption on
the functional is needed. In particular these results apply to the exterior-skew parameter on an
odd cycle, even when the characteristic is not two.

The functional is packaged using `LinearMap.IsFrobeniusFunctional`. Over a field, its dual-module
identification and Nakayama automorphism are available through the general Frobenius API after
installing `TauCeti.moduleFinite_skewZigzagQuotient` as a local instance.
The functional depends on the incident edges used to normalize its volume classes, whereas
self-injectivity does not; the self-injectivity statements therefore require only the existence
of an incident edge at every vertex. These are statements about the relation quotient, not a
componentwise algebra with dual-number factors at isolated vertices.

## Main results

* `TauCeti.isFrobeniusFunctional_skewZigzagTrace`: the normalized functional is Frobenius over
  every commutative ring.
* `TauCeti.moduleInjective_skewZigzagQuotient` and
  `TauCeti.moduleInjective_op_skewZigzagQuotient`: the regular left and right modules are injective
  over every field, including characteristic two.

## References

* C. Couture, *Skew-Zigzag Algebras*, Section 3, https://arxiv.org/abs/1509.08405, for the
  parameterized relation quotient.
* T. Y. Lam, *Lectures on modules and rings*, Section 16, for self-injectivity of Frobenius
  algebras. We use the general Frobenius-functional criterion, rather than transporting the
  ordinary zigzag result along an algebra isomorphism, which need not exist.
-/

public section

namespace TauCeti

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V) [Finite V]

section CommRing

variable [CommRing k] (c : SkewZigzagParameter k G)

/-- The normalized skew-zigzag functional is Frobenius, whether or not it is symmetric. -/
theorem isFrobeniusFunctional_skewZigzagTrace (t : ∀ i : V, {j : V // G.Adj i j}) :
    (skewZigzagTrace k G c t).IsFrobeniusFunctional := by
  refine LinearMap.isFrobeniusFunctional_iff.mpr ⟨?_, ?_⟩
  · intro x hx
    exact (skewZigzagTracePairing_nondegenerate k G c t).1 x fun y => by simpa using hx y
  · intro y hy
    exact (skewZigzagTracePairing_nondegenerate k G c t).2 y fun x => by simpa using hy x

end CommRing

section Field

variable [Field k] (c : SkewZigzagParameter k G) (hns : ∀ i : V, ∃ j, G.Adj i j)

/-- Incident edges used only to choose a Frobenius functional for the self-injectivity proofs. -/
private noncomputable def selfInjectiveIncidentEdges : ∀ i : V, {j : V // G.Adj i j} :=
  fun i => ⟨(hns i).choose, (hns i).choose_spec⟩

include hns

/-- Every skew-zigzag relation quotient of a finite graph without isolated vertices is left
self-injective. No condition on the gauge class of its parameter is required. -/
theorem moduleInjective_skewZigzagQuotient :
    Module.Injective (skewZigzagQuotient k G c) (skewZigzagQuotient k G c) := by
  let t := selfInjectiveIncidentEdges G hns
  let _ := moduleFinite_skewZigzagQuotient k G c hns
  exact (isFrobeniusFunctional_skewZigzagTrace k G c t).moduleInjective_self

/-- Every skew-zigzag relation quotient of a finite graph without isolated vertices is right
self-injective, expressed using its standard module structure over the opposite algebra. -/
theorem moduleInjective_op_skewZigzagQuotient :
    Module.Injective (skewZigzagQuotient k G c)ᵐᵒᵖ (skewZigzagQuotient k G c) := by
  let t := selfInjectiveIncidentEdges G hns
  let _ := moduleFinite_skewZigzagQuotient k G c hns
  exact (isFrobeniusFunctional_skewZigzagTrace k G c t).moduleInjective_op_self

end Field

end TauCeti
