/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.LocallyClosed
import TauCeti.Logic.Function.Fiber

/-!
# Piecewise-affine maps with rational linear parts

Finite covers describe maps that agree piecewise with affine maps whose linear parts
are rational for the specified lattices. The offsets can be arbitrary real vectors.
For finite branches, the covers use locally closed rational-normal polyhedra, and each
representative is injective on its own piece. Injectivity on finitely many pieces gives finite
fibers even on nonclosed domains; see `IsFiniteBranchOn.finite_fiber`.

The predicates and their operations are adapted from
`Mei/Geometry/Convex/Polyhedron/Rational/SemilinearFamily/Basic.lean`
at `bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

open TauCeti (IsLocallyClosedPolyhedron IsRationalSemilinear
  isLocallyClosedPolyhedron_setOf_forall_neg)

namespace TauCeti

variable {N V N' W N'' X : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [AddCommGroup W] [Module ℝ W] [AddCommGroup N''] [AddCommGroup X]
  [Module ℝ X] {i : N →+ V} {i' : N' →+ W} {i'' : N'' →+ X}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}

/-- A map `f` on `D` is piecewise affine with rational linear parts: finitely many rational
semilinear pieces cover `D`, and on each piece `f` is an affine map, with arbitrary real
offset, whose linear part is rational for the two lattices. -/
def IsRationalPiecewiseAffine (h : TauCeti.Toric.IsIntegralLattice i)
    (h' : TauCeti.Toric.IsIntegralLattice i') (D : Set V) (f : D → W) : Prop :=
  ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
    (⋃ k, S k) = D ∧ ∀ k, IsRationalSemilinear h (S k) ∧
      TauCeti.Toric.IsRationalLinearMap h h' (g k).linear ∧ ∀ x : D, x.val ∈ S k → f x = g k x

/-- A map `f` on `D` is a finite branch: finitely many locally closed rational-normal
polyhedra cover `D`, and on each of them `f` agrees with an affine map, with rational
linear part, that is injective on the polyhedron. The domain need not be closed. -/
def IsFiniteBranchOn (h : TauCeti.Toric.IsIntegralLattice i)
    (h' : TauCeti.Toric.IsIntegralLattice i') (D : Set V) (f : D → W) : Prop :=
  ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
    (⋃ k, S k) = D ∧ ∀ k, IsLocallyClosedPolyhedron h (S k) ∧
      TauCeti.Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.InjOn (g k) (S k) ∧
        ∀ x : D, x.val ∈ S k → f x = g k x

/-- A rational piecewise-affine map is characterized by a finite rational semilinear cover
and affine representatives with rational linear parts. Their offsets are unrestricted. -/
theorem isRationalPiecewiseAffine_iff {D : Set V} {f : D → W} :
    IsRationalPiecewiseAffine h h' D f ↔
      ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
        (⋃ k, S k) = D ∧ ∀ k, IsRationalSemilinear h (S k) ∧
          TauCeti.Toric.IsRationalLinearMap h h' (g k).linear ∧
            ∀ x : D, x.val ∈ S k → f x = g k x := (Iff.rfl)

/-- A finite branch is characterized by a finite cover by locally closed rational-normal
polyhedra and affine representatives with rational linear parts that are injective on their
respective pieces. -/
theorem isFiniteBranchOn_iff {D : Set V} {f : D → W} :
    IsFiniteBranchOn h h' D f ↔
      ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
        (⋃ k, S k) = D ∧ ∀ k, IsLocallyClosedPolyhedron h (S k) ∧
          TauCeti.Toric.IsRationalLinearMap h h' (g k).linear ∧ Set.InjOn (g k) (S k) ∧
            ∀ x : D, x.val ∈ S k → f x = g k x := (Iff.rfl)

/-- An affine map with rational linear part on a rational semilinear domain is rational
piecewise affine, with a single piece and arbitrary real offset. -/
theorem IsRationalSemilinear.isRationalPiecewiseAffine {D : Set V}
    (hD : IsRationalSemilinear h D) (g : V →ᵃ[ℝ] W)
    (hg : TauCeti.Toric.IsRationalLinearMap h h' g.linear) :
    IsRationalPiecewiseAffine h h' D (fun x => g x) :=
  isRationalPiecewiseAffine_iff.mpr
    ⟨Unit, inferInstance, fun _ => D, fun _ => g, Set.iUnion_const _,
      fun _ => ⟨hD, hg, fun _ _ => rfl⟩⟩

/-- An affine map with rational linear part, injective on a rational semilinear
set, is a finite branch on that set. -/
theorem IsRationalSemilinear.isFiniteBranchOn {D : Set V}
    (hD : IsRationalSemilinear h D) (g : V →ᵃ[ℝ] W)
    (hg : TauCeti.Toric.IsRationalLinearMap h h' g.linear) (hinj : Set.InjOn g D) :
    IsFiniteBranchOn h h' D (fun x => g x) := by
  obtain ⟨κ, _, S, hS, -, hcover⟩ :=
    TauCeti.isRationalSemilinear_iff_exists_pairwise_disjoint.mp hD
  refine isFiniteBranchOn_iff.mpr ⟨κ, ‹_›, S, fun _ => g, hcover, fun k =>
    ⟨hS k, hg, hinj.mono ?_, fun _ _ => rfl⟩⟩
  rw [← hcover]
  exact Set.subset_iUnion S k

namespace IsRationalPiecewiseAffine

/-- The domain of a rational piecewise-affine map is rational semilinear. -/
theorem isRationalSemilinear {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) :
    IsRationalSemilinear h D := by
  obtain ⟨κ, _, S, g, rfl, hS⟩ := hf
  exact IsRationalSemilinear.iUnion fun k => (hS k).1

/-- Restricting a piecewise-affine map requires semilinearity only of the actual
intersection of its domain with the cut. -/
theorem inter {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f) {P : Set V}
    (hP : IsRationalSemilinear h (D ∩ P)) :
    IsRationalPiecewiseAffine h h' (D ∩ P)
      (Set.domRestrict₂ (π := fun _ : V => W) Set.inter_subset_left f) := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  refine ⟨κ, ‹_›, fun k => S k ∩ (D ∩ P), g, ?_, fun k =>
    ⟨(hS k).1.inter hP, (hS k).2.1, fun x hx => (hS k).2.2 ⟨x.val, x.property.1⟩ hx.1⟩⟩
  calc
    (⋃ k, S k ∩ (D ∩ P)) = D ∩ (D ∩ P) := by rw [← Set.iUnion_inter, hD]
    _ = D ∩ P := Set.inter_eq_right.mpr Set.inter_subset_left

/-- Composing the values with an affine map with rational linear part
keeps the map piecewise affine. -/
theorem postcomp {D : Set V} {f : D → W} (hf : IsRationalPiecewiseAffine h h' D f)
    (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear) :
    IsRationalPiecewiseAffine h h'' D fun x => φ (f x) := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  refine ⟨κ, ‹_›, S, fun k => φ.comp (g k), hD, fun k => ⟨(hS k).1, ?_, fun x hx => ?_⟩⟩
  · rw [AffineMap.comp_linear]
    exact hφ.comp (hS k).2.1
  · simp only [AffineMap.comp_apply, (hS k).2.2 x hx]

end IsRationalPiecewiseAffine

namespace IsFiniteBranchOn

/-- A finite branch is piecewise affine with rational linear parts. -/
theorem isRationalPiecewiseAffine {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) :
    IsRationalPiecewiseAffine h h' D f := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  exact ⟨κ, ‹_›, S, g, hD, fun k =>
    ⟨(hS k).1.isRationalSemilinear, (hS k).2.1, (hS k).2.2.2⟩⟩

/-- A finite branch remains so after a cut whose intersection with the domain
is rational semilinear; the cut need not be semilinear in the ambient space. -/
theorem inter {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) {P : Set V}
    (hP : IsRationalSemilinear h (D ∩ P)) :
    IsFiniteBranchOn h h' (D ∩ P)
      (Set.domRestrict₂ (π := fun _ : V => W) Set.inter_subset_left f) := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  obtain ⟨μ, _, C, hC, -, hcover⟩ :=
    TauCeti.isRationalSemilinear_iff_exists_pairwise_disjoint.mp hP
  refine ⟨κ × μ, inferInstance, fun p => S p.1 ∩ C p.2, fun p => g p.1, ?_, fun p =>
    ⟨(hS p.1).1.inter (hC p.2), (hS p.1).2.1, (hS p.1).2.2.1.mono Set.inter_subset_left,
      fun x hx => (hS p.1).2.2.2 ⟨x.val, x.property.1⟩ hx.1⟩⟩
  calc
    (⋃ p : κ × μ, S p.1 ∩ C p.2) = D ∩ (D ∩ P) := by
      rw [Set.iUnion_prod', ← Set.iUnion_inter_iUnion, hD, hcover]
    _ = D ∩ P := Set.inter_eq_right.mpr Set.inter_subset_left

/-- Rational affine post-composition preserves finite branches when injective on the image. -/
theorem postcomp {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f)
    (φ : W →ᵃ[ℝ] X) (hφ : TauCeti.Toric.IsRationalLinearMap h' h'' φ.linear)
    (hinj : Set.InjOn φ (Set.range f)) : IsFiniteBranchOn h h'' D (fun x => φ (f x)) := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  refine ⟨κ, ‹_›, S, fun k => φ.comp (g k), hD, fun k =>
    ⟨(hS k).1, ?_, ?_, ?_⟩⟩
  · rw [AffineMap.comp_linear]
    exact hφ.comp (hS k).2.1
  · have hmaps : Set.MapsTo (g k) (S k) (Set.range f) := by
      intro x hx
      exact ⟨⟨x, hD ▸ Set.mem_iUnion.mpr ⟨k, hx⟩⟩, (hS k).2.2.2 _ hx⟩
    exact hinj.comp (hS k).2.2.1 hmaps
  · intro x hx
    simp only [AffineMap.comp_apply, (hS k).2.2.2 x hx]

/-- A finite branch has finite fibers: on each piece the affine map is injective. -/
theorem finite_fiber {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) (w : W) :
    Finite {x : D // f x = w} := by
  obtain ⟨κ, _, S, g, hD, hS⟩ := hf
  apply Set.finite_fiber_of_subset_iUnion (S := fun k => Subtype.val ⁻¹' S k) w
  · rw [← Set.preimage_iUnion, hD]
    exact fun x _ => x.property
  · intro k
    exact (((hS k).2.2.1.comp Set.injOn_subtypeVal (fun _ hx => hx)).congr
      (fun x hx => ((hS k).2.2.2 x hx).symm)).mono Set.inter_subset_left

end IsFiniteBranchOn

end TauCeti
