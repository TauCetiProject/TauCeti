/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Lift

/-!
# Orientations of manifolds with corners

A manifold orientation is a source-indexed orientation lift modulo simultaneous reversal of its
model orientation and all chart signs. It induces an actual, locally constant orientation of the
tangent bundle. This definition includes boundary and corner points.
Orientability records existence; every model with corners is orientable.
-/

public section

noncomputable section

namespace TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

/-- An orientation of a manifold, including its boundary and corners. -/
def Orientation (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (ι : Type*) [Fintype ι] : Type _ :=
  Quotient (OrientationLift.setoid (I := I) (M := M) (ι := ι))

namespace Orientation

variable {I}

/-- The orientation represented by a lift. -/
def mk (o : OrientationLift I M ι) : Orientation I M ι := Quotient.mk _ o

/-- Two lifts represent the same orientation exactly when they agree or differ by the
simultaneous reversal of model orientation and source signs. -/
theorem mk_eq_mk_iff (a b : OrientationLift I M ι) :
    mk a = mk b ↔ a = b ∨ a = b.flip := by
  constructor
  · intro h
    have hr := Quotient.exact h
    rcases (OrientationLift.setoid_rel a b).mp hr with h | h
    · exact .inl h.symm
    · exact .inr (by rw [h, OrientationLift.flip_flip])
  · rintro (rfl | rfl)
    · rfl
    · apply Quotient.sound
      apply (OrientationLift.setoid_rel b.flip b).mpr
      exact .inr b.flip_flip.symm

/-- Define a function on orientations from a function on lifts invariant under diagonal flip. -/
def lift {α : Sort*} (f : OrientationLift I M ι → α)
    (hflip : ∀ l, f l.flip = f l) : Orientation I M ι → α :=
  Quotient.lift f (fun a b h ↦ by
    rcases (OrientationLift.setoid_rel a b).mp h with rfl | rfl
    · rfl
    · exact (hflip a).symm)

/-- A function induced from lifts evaluates on a represented orientation at its lift. -/
@[simp] theorem lift_mk {α : Sort*} (f : OrientationLift I M ι → α)
    (hflip : ∀ l, f l.flip = f l) (l : OrientationLift I M ι) :
    lift f hflip (mk l) = f l := (rfl)

/-- Every manifold orientation has a source-indexed lift. -/
theorem exists_lift (o : Orientation I M ι) : ∃ l : OrientationLift I M ι, mk l = o :=
  Quotient.inductionOn o fun l ↦ ⟨l, rfl⟩

/-- Prove a property of orientations by proving it for every source-indexed lift. -/
@[elab_as_elim]
theorem inductionOn {p : Orientation I M ι → Prop} (o : Orientation I M ι)
    (h : ∀ l : OrientationLift I M ι, p (mk l)) : p o :=
  Quotient.inductionOn o h

/-- The index type has the dimension of the model space. -/
theorem card_eq (o : Orientation I M ι) : Fintype.card ι = Module.finrank ℝ E :=
  Quotient.inductionOn o OrientationLift.card_eq

/-- Reverse the tangent orientations by reversing the model orientation of a lift. -/
def neg (o : Orientation I M ι) : Orientation I M ι :=
  lift (fun l ↦ mk (-l)) (fun l ↦
    (mk_eq_mk_iff _ _).mpr (.inr l.flip_neg.symm)) o

instance : Neg (Orientation I M ι) := ⟨Orientation.neg⟩

@[simp]
theorem neg_mk (o : OrientationLift I M ι) : -(mk o) = mk (-o) := (rfl)

variable [IsManifold I 1 M]

/-- The induced orientation of the tangent bundle. -/
def toVectorBundleOrientation (o : Orientation I M ι) :
    TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι :=
  lift OrientationLift.toVectorBundleOrientation (fun l ↦ by
    ext x
    simpa only [OrientationLift.toVectorBundleOrientation_apply] using l.orientationAt_flip x) o

@[simp]
theorem toVectorBundleOrientation_mk (o : OrientationLift I M ι) :
    (mk o).toVectorBundleOrientation = o.toVectorBundleOrientation := (rfl)

@[simp]
theorem toVectorBundleOrientation_neg (o : Orientation I M ι) :
    (-o).toVectorBundleOrientation = -o.toVectorBundleOrientation := by
  induction o using Quotient.inductionOn with | _ o =>
    apply TauCeti.VectorBundleOrientation.ext
    intro x
    -- Quotient induction produces raw representatives; use the public constructor to
    -- reduce tangent-bundle negation through its representative equation.
    change (mk (-o)).toVectorBundleOrientation x = -(mk o).toVectorBundleOrientation x
    simpa only [toVectorBundleOrientation_mk, OrientationLift.toVectorBundleOrientation_apply]
      using o.orientationAt_neg x

end Orientation

variable [IsManifold I 1 M]

variable {I}

namespace Orientation

/-- The orientation of a tangent space induced by a manifold orientation. -/
def orientationAt (o : Orientation I M ι) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) ι := o.toVectorBundleOrientation x

/-- Evaluation of the tangent-bundle interpretation is the manifold's tangent orientation. -/
@[simp]
theorem toVectorBundleOrientation_apply (o : Orientation I M ι) (x : M) :
    o.toVectorBundleOrientation x = o.orientationAt x := (rfl)

/-- The tangent orientation of a represented manifold orientation is the representative's
intrinsic tangent orientation, including at boundary and corner points. -/
@[simp]
theorem orientationAt_mk (o : OrientationLift I M ι) (x : M) :
    orientationAt (Orientation.mk o) x = o.orientationAt x := by
  simp only [orientationAt, Orientation.toVectorBundleOrientation_mk,
    OrientationLift.toVectorBundleOrientation_apply]

@[simp]
theorem orientationAt_neg (o : Orientation I M ι) (x : M) :
    orientationAt (-o) x = -orientationAt o x := by
  simp only [orientationAt, Orientation.toVectorBundleOrientation_neg,
    TauCeti.VectorBundleOrientation.neg_apply]

/-- A manifold orientation is determined by its actual tangent orientations. -/
@[ext]
theorem ext {o o' : Orientation I M ι}
    (h : ∀ x, orientationAt o x = orientationAt o' x) : o = o' := by
  induction o using Orientation.inductionOn with | _ a =>
    induction o' using Orientation.inductionOn with | _ b =>
      simp only [orientationAt_mk] at h
      exact (mk_eq_mk_iff a b).mpr (OrientationLift.eq_or_eq_flip_of_orientationAt h)

/-- Over a preconnected manifold there are at most two orientations. -/
theorem eq_or_eq_neg [PreconnectedSpace M] (o o' : Orientation I M ι) :
    o = o' ∨ o = -o' := by
  rcases o.toVectorBundleOrientation.eq_or_eq_neg o.card_eq o'.toVectorBundleOrientation with h | h
  · exact .inl (ext fun x ↦ congrArg (fun v ↦ v x) h)
  · right
    apply ext
    intro x
    rw [orientationAt_neg]
    exact congrArg (fun v ↦ v x) h

/-- An orientation differs from its opposite on every nonempty manifold. -/
theorem neg_ne_self [Nonempty M] (o : Orientation I M ι) : -o ≠ o := by
  intro h
  have hx := congrArg (fun v ↦ orientationAt v (Classical.arbitrary M)) h
  rw [orientationAt_neg] at hx
  exact Module.Ray.ne_neg_self _ hx.symm

protected theorem neg_neg (o : Orientation I M ι) : - -o = o := by
  apply ext
  intro x
  rw [orientationAt_neg, orientationAt_neg]
  exact _root_.neg_neg (orientationAt o x)

instance : InvolutiveNeg (Orientation I M ι) where
  neg_neg := Orientation.neg_neg

/-- Construct a manifold orientation from a locally constant orientation of its tangent bundle.
The choice of model orientation affects only its representative lift. -/
def ofVectorBundleOrientation (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι) :
    Orientation I M ι := mk (OrientationLift.ofVectorBundleOrientation model hι o)

@[simp]
theorem orientationAt_ofVectorBundleOrientation (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι) (x : M) :
    orientationAt (ofVectorBundleOrientation model hι o) x = o x := by
  simp only [ofVectorBundleOrientation, orientationAt, toVectorBundleOrientation_mk,
    OrientationLift.toVectorBundleOrientation_apply,
    OrientationLift.orientationAt_ofVectorBundleOrientation]

/-- Interpreting the orientation reconstructed from tangent orientations recovers the bundle
orientation. -/
@[simp]
theorem toVectorBundleOrientation_ofVectorBundleOrientation
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι) :
    (ofVectorBundleOrientation model hι o).toVectorBundleOrientation = o := by
  ext x
  exact orientationAt_ofVectorBundleOrientation model hι o x

/-- Recovering a manifold orientation from its tangent bundle orientations is independent of
the chosen model orientation. -/
@[simp]
theorem ofVectorBundleOrientation_toVectorBundleOrientation
    (model : _root_.Orientation ℝ E ι) (o : Orientation I M ι) :
    ofVectorBundleOrientation model o.card_eq o.toVectorBundleOrientation = o := by
  apply ext
  intro x
  exact orientationAt_ofVectorBundleOrientation model o.card_eq o.toVectorBundleOrientation x

/-- The constant orientation of a model with corners. -/
def model (o : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E) :
    Orientation I H ι := mk (OrientationLift.model (I := I) o hι)

/-- The constant model orientation is represented by its actual constant orientation lift. -/
theorem model_eq_mk (o : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) :
    model (I := I) o hι = mk (OrientationLift.model (I := I) o hι) := (rfl)

@[simp]
theorem orientationAt_model (o : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) (x : H) :
    orientationAt (model (I := I) o hι) x = o := by
  simp only [model, orientationAt, toVectorBundleOrientation_mk,
    OrientationLift.toVectorBundleOrientation_apply, OrientationLift.orientationAt_model]
  -- The tangent space of the model uses its model-space scalar structure.
  rfl

end Orientation
end TauCeti.Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A manifold with corners is orientable when it carries an orientation of its tangent spaces
compatible with the within-range chart Jacobians. -/
class Orientable : Prop where
  /-- A manifold orientation exists. -/
  nonempty_orientation : Nonempty (Manifold.Orientation I M (Fin (Module.finrank ℝ E)))

variable {I M}

/-- Every model with corners carries its constant model orientation. -/
instance : Orientable I H :=
  ⟨⟨Manifold.Orientation.model (I := I) (Module.finBasis ℝ E).orientation
    (Fintype.card_fin _)⟩⟩

/-- A manifold is orientable exactly when its tangent bundle is orientable. -/
theorem orientable_iff_nonempty_vectorBundleOrientation [IsManifold I 1 M] :
    Orientable I M ↔ Nonempty
      (VectorBundleOrientation E (TangentSpace I : M → Type _) (Fin (Module.finrank ℝ E))) :=
  ⟨fun ⟨⟨o⟩⟩ ↦ ⟨o.toVectorBundleOrientation⟩, fun ⟨o⟩ ↦
    ⟨⟨Manifold.Orientation.ofVectorBundleOrientation (Module.finBasis ℝ E).orientation
      (Fintype.card_fin _) o⟩⟩⟩

end TauCeti
