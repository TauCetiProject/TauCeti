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
  Quotient.map (sa := OrientationLift.setoid (I := I) (M := M) (ι := ι))
    (sb := OrientationLift.setoid (I := I) (M := M) (ι := ι)) Neg.neg (fun a b h ↦ by
      -- Quotient.map hides the relation behind the two quotient setoid parameters.
      change OrientationLift.setoid.r a b at h
      change OrientationLift.setoid.r (-a) (-b)
      rw [OrientationLift.setoid_rel] at h ⊢
      rcases h with rfl | rfl
      · exact .inl rfl
      · exact .inr a.flip_neg.symm) o

instance : Neg (Orientation I M ι) := ⟨Orientation.neg⟩

@[simp]
theorem neg_mk (o : OrientationLift I M ι) : -(mk o) = mk (-o) := (rfl)

variable [IsManifold I 1 M]

/-- The induced orientation of the tangent bundle. -/
def toVectorBundleOrientation (o : Orientation I M ι) :
    TauCeti.VectorBundleOrientation E (TangentSpace I : M → Type _) ι :=
  Quotient.lift OrientationLift.toVectorBundleOrientation (fun a b h ↦ by
    apply TauCeti.VectorBundleOrientation.ext
    intro x
    rcases (OrientationLift.setoid_rel a b).mp h with rfl | rfl
    · rfl
    · simpa only [OrientationLift.toVectorBundleOrientation_apply] using
        (a.orientationAt_flip x).symm) o

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

/-- At the base point of its own preferred chart, the representative's sign twists the model
orientation. This equation also holds at boundary and corner points. -/
@[simp]
theorem orientationAt_mk (o : OrientationLift I M ι) (x : M) :
    orientationAt (Orientation.mk o) x =
      if o.sign x ⟨x, mem_chart_source H x⟩ = 1 then o.modelOrientation
      else -o.modelOrientation := by
  simp only [orientationAt, Orientation.toVectorBundleOrientation_mk,
    OrientationLift.toVectorBundleOrientation_apply]
  exact (o.orientationAt_eq x).trans (o.chartOrientation_def _ _)

@[simp]
theorem orientationAt_neg (o : Orientation I M ι) (x : M) :
    orientationAt (-o) x = -orientationAt o x := by
  simp only [orientationAt, Orientation.toVectorBundleOrientation_neg,
    TauCeti.VectorBundleOrientation.neg_apply]

/-- A manifold orientation is determined by its actual tangent orientations. -/
@[ext]
theorem ext {o o' : Orientation I M ι}
    (h : ∀ x, orientationAt o x = orientationAt o' x) : o = o' := by
  induction o using Quotient.inductionOn with | _ a =>
    induction o' using Quotient.inductionOn with | _ b =>
      apply Quotient.sound (s := OrientationLift.setoid)
      -- Quotient induction exposes raw Quotient.mk terms; present them as Orientation.mk
      -- so the public representative equations apply without unfolding the quotient lift.
      change ∀ x, (mk a).toVectorBundleOrientation x =
        (mk b).toVectorBundleOrientation x at h
      simp only [toVectorBundleOrientation_mk,
        OrientationLift.toVectorBundleOrientation_apply] at h
      -- The quotient equality uses the same lift setoid as the representative constructor.
      change OrientationLift.setoid.r a b
      rw [OrientationLift.setoid_rel]
      rcases OrientationLift.eq_or_eq_flip_of_orientationAt (fun x ↦ (h x).symm) with h | h
      · exact .inl h
      · exact .inr h

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

@[simp]
theorem orientationAt_model (o : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) (x : H) :
    orientationAt (model (I := I) o hι) x = o := by
  simp only [model, orientationAt, toVectorBundleOrientation_mk,
    OrientationLift.toVectorBundleOrientation_apply, OrientationLift.orientationAt_model]
  rfl

end Orientation
end TauCeti.Manifold
