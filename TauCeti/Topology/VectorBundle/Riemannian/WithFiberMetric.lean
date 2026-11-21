/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# The fibres of a vector bundle carrying a chosen metric

A continuous Riemannian metric `g` on a real vector bundle `E` is data, and the fibres `E b` may
already carry a norm that `g` does not induce: for instance the fibres of the bundle of
alternating forms on a Riemannian manifold carry the operator norm, while their natural metric
is the Gram inner product. Installing `g` as an inner product on `E b` would give two
non-defeq norms on one type.

`TauCeti.WithFiberMetric g` is instead a copy of the fibres of `E`, with the same topology,
addition, scalar action and bundle structure, on which `g` is the inner product, through
Mathlib's `RiemannianBundle` mechanism. The metric `g` selects the inner product instance on
the copy; the underlying type `WithFiberMetric g b` unfolds to `E b` definitionally, whatever
the metric. The copy is a continuous Riemannian bundle, so its fibre norm is continuous, and
the analytic constructions over a Riemannian bundle, such as the Hilbert space of
square-integrable sections, apply to the metric `g`. The identity
`TauCeti.WithFiberMetric.toWithFiberMetric` transports vectors of `E` to the copy.

## Main definitions

* `TauCeti.WithFiberMetric g`: the fibres of `E` carrying the inner product `g`.
* `TauCeti.WithFiberMetric.toWithFiberMetric`: the identity of a fibre of `E`, as a continuous
  linear equivalence onto the copy.

## Main results

* `TauCeti.WithFiberMetric.inner_toWithFiberMetric`: the inner product of the copy is `g`.
-/

public section

noncomputable section

open Bundle
open scoped InnerProductSpace

namespace TauCeti

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

-- The copy must unfold to `E b` and its instances to those of `E`, so that sections of `E` are
-- sections of the copy and the inner product of the copy computes as `g`.
/-- The fibre at `b` of the vector bundle `E`, carrying the inner product of the continuous
Riemannian metric `g`: a copy of `E b` with its topology, addition and scalar action, on which
`g` does not compete with any norm already present on `E b`. -/
@[expose] def WithFiberMetric (_g : ContinuousRiemannianMetric F E) (b : B) : Type _ :=
  E b

namespace WithFiberMetric

variable (g : ContinuousRiemannianMetric F E)

instance (b : B) : TopologicalSpace (WithFiberMetric g b) :=
  inferInstanceAs (TopologicalSpace (E b))

instance (b : B) : AddCommGroup (WithFiberMetric g b) :=
  inferInstanceAs (AddCommGroup (E b))

instance (b : B) : Module ℝ (WithFiberMetric g b) :=
  inferInstanceAs (Module ℝ (E b))

instance (b : B) : IsTopologicalAddGroup (WithFiberMetric g b) :=
  inferInstanceAs (IsTopologicalAddGroup (E b))

instance (b : B) : ContinuousConstSMul ℝ (WithFiberMetric g b) :=
  inferInstanceAs (ContinuousConstSMul ℝ (E b))

/-- The total space of the copy is the total space of `E`. -/
instance : TopologicalSpace (TotalSpace F (WithFiberMetric g)) :=
  inferInstanceAs (TopologicalSpace (TotalSpace F E))

instance : FiberBundle F (WithFiberMetric g) :=
  inferInstanceAs (FiberBundle F E)

instance : VectorBundle ℝ F (WithFiberMetric g) :=
  inferInstanceAs (VectorBundle ℝ F E)

/-- The inner product on the fibres of the copy is `g`. -/
instance : RiemannianBundle (WithFiberMetric g) :=
  ⟨g.toRiemannianMetric⟩

/-- The metric `g` varies continuously, so the copy is a continuous Riemannian bundle. -/
instance : IsContinuousRiemannianBundle F (WithFiberMetric g) :=
  ⟨⟨g.inner, g.continuous, fun _ _ _ ↦ rfl⟩⟩

/-- The identity of the fibre `E b`, as a continuous linear equivalence onto the copy carrying
the metric `g`. -/
def toWithFiberMetric (b : B) : E b ≃L[ℝ] WithFiberMetric g b :=
  ContinuousLinearEquiv.refl ℝ (E b)

-- Use these identities for explicit rewriting: simplifying away the transport loses the
-- fibre copy in inferred types and can prevent matching lemmas about its metric and norm.
omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- Transport to the fibre carrying `g` preserves the underlying vector. -/
theorem toWithFiberMetric_apply (b : B) (v : E b) :
    toWithFiberMetric g b v = v :=
  (rfl)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- Transport back from the fibre carrying `g` preserves the underlying vector. -/
theorem toWithFiberMetric_symm_apply (b : B) (v : WithFiberMetric g b) :
    (toWithFiberMetric g b).symm v = v :=
  (rfl)

/-- The inner product of the copy is the metric `g`. -/
@[simp]
theorem inner_toWithFiberMetric (b : B) (v w : E b) :
    ⟪toWithFiberMetric g b v, toWithFiberMetric g b w⟫_ℝ = g.inner b v w :=
  (rfl)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- A map into the total space of `E` is continuous exactly when it is continuous into the total
space of the copy: both total spaces carry the same topology. -/
theorem continuous_totalSpaceMk_toWithFiberMetric_iff {X : Type*} [TopologicalSpace X]
    {p : X → B} {s : ∀ x, E (p x)} :
    Continuous (fun x ↦ TotalSpace.mk' F (E := WithFiberMetric g) (p x)
        (toWithFiberMetric g (p x) (s x))) ↔
      Continuous (fun x ↦ TotalSpace.mk' F (p x) (s x)) :=
  Iff.rfl

end WithFiberMetric

end TauCeti
