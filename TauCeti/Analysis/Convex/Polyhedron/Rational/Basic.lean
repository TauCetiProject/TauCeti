/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.RationalFunctional
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Rational-normal affine polyhedra

A presentation consists of finitely many continuous affine inequalities whose
linear parts are rational multiples of lattice characters. Offsets are arbitrary
real numbers. Distinct presentations may have the same carrier; no extensionality
of presentations is asserted. Rational offsets are a separate condition.
These carriers serve as affine cells of polyhedral decompositions: intersection
and rational affine pullback retain the finite rational-normal presentation.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `61509bfe75ce943898bc99cfa509fb40bb78c614` (Apache 2.0).
-/

public section

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {i : N →+ V}

/-- A finite rational-normal presentation, with arbitrary real affine offsets. -/
structure RationalAffinePolyhedron (h : TauCeti.Toric.IsIntegralLattice i) where
  /-- The number of inequalities, including any redundant inequalities. -/
  numConstraints : ℕ
  /-- The affine functions required to be nonpositive. -/
  inequality : Fin numConstraints → (V →ᴬ[ℝ] ℝ)
  /-- Every linear part is a rational multiple of a lattice character. -/
  rational_linear : ∀ j, Toric.IsRationalFunctional h (inequality j).toAffineMap.linear

namespace RationalAffinePolyhedron

variable {h : TauCeti.Toric.IsIntegralLattice i}

/-- The closed set defined by the affine inequalities. -/
def carrier (P : RationalAffinePolyhedron h) : Set V :=
  {x | ∀ j, P.inequality j x ≤ 0}

/-- Membership is simultaneous satisfaction of all inequalities. -/
@[simp]
theorem mem_carrier {P : RationalAffinePolyhedron h} {x : V} :
    x ∈ P.carrier ↔ ∀ j, P.inequality j x ≤ 0 := Iff.rfl

/-- The presentation is a convex polyhedron on the existing supplier's carrier. -/
theorem isConvexPolyhedron (P : RationalAffinePolyhedron h) :
    TauCeti.IsConvexPolyhedron P.carrier :=
  TauCeti.isConvexPolyhedron_setOf_forall P.inequality

/-- Rational-normal polyhedra are closed. -/
theorem isClosed (P : RationalAffinePolyhedron h) : IsClosed P.carrier :=
  P.isConvexPolyhedron.isClosed

/-- Rational-normal polyhedra are convex. -/
theorem convex (P : RationalAffinePolyhedron h) : Convex ℝ P.carrier :=
  P.isConvexPolyhedron.convex

/-- Rational offsets are additional data; the default presentation allows real offsets. -/
def HasRationalOffsets (P : RationalAffinePolyhedron h) : Prop :=
  ∀ j, ∃ q : ℚ, P.inequality j 0 = (q : ℝ)

/-- Rational offsets mean that every inequality takes a rational value at zero. -/
theorem hasRationalOffsets_iff {P : RationalAffinePolyhedron h} :
    P.HasRationalOffsets ↔ ∀ j, ∃ q : ℚ, P.inequality j 0 = (q : ℝ) := Iff.rfl

/-- Reindex a finite family of rational-normal inequalities by a finite ordinal. -/
noncomputable def ofFinite {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    RationalAffinePolyhedron h := by
  letI := Fintype.ofFinite ι
  exact ⟨Fintype.card ι, fun j => g ((Fintype.equivFin ι).symm j), fun j => hg _⟩

/-- Reindexing preserves the exact simultaneous-inequality carrier. -/
@[simp high] -- Apply before `mem_carrier` exposes the reindexed inequalities.
theorem mem_carrier_ofFinite {ι : Type*} [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) {x : V} :
    x ∈ (ofFinite g hg).carrier ↔ ∀ j, g j x ≤ 0 := by
  classical
  let _ := Fintype.ofFinite ι
  dsimp only [carrier, ofFinite, Set.mem_ofPred_eq]
  exact (Fintype.equivFin ι).symm.forall_congr_right (q := fun j => g j x ≤ 0)

/-- Finite reindexing has rational offsets exactly when the original family does. -/
@[simp]
theorem hasRationalOffsets_ofFinite_iff {ι : Type*} [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    (ofFinite g hg).HasRationalOffsets ↔ ∀ j, ∃ q : ℚ, g j 0 = (q : ℝ) := by
  classical
  let _ := Fintype.ofFinite ι
  dsimp only [HasRationalOffsets, ofFinite]
  exact (Fintype.equivFin ι).symm.forall_congr_right
    (q := fun j => ∃ q : ℚ, g j 0 = (q : ℝ))

/-- Intersect two presentations by retaining both families of inequalities. -/
noncomputable def inter (P Q : RationalAffinePolyhedron h) : RationalAffinePolyhedron h :=
  ofFinite (Sum.elim P.inequality Q.inequality) (by
    intro j
    cases j with
    | inl j => exact P.rational_linear j
    | inr j => exact Q.rational_linear j)

/-- Intersection of presentations has the intersection of their carriers. -/
@[simp]
theorem carrier_inter (P Q : RationalAffinePolyhedron h) :
    (P.inter Q).carrier = P.carrier ∩ Q.carrier := by
  ext x
  unfold inter
  rw [mem_carrier_ofFinite]
  simp [Sum.forall]

/-- Intersection has rational offsets exactly when both presentations do. -/
@[simp]
theorem hasRationalOffsets_inter_iff {P Q : RationalAffinePolyhedron h} :
    (P.inter Q).HasRationalOffsets ↔ P.HasRationalOffsets ∧ Q.HasRationalOffsets := by
  rw [inter, hasRationalOffsets_ofFinite_iff]
  simp [Sum.forall, hasRationalOffsets_iff]

/-- The empty family of inequalities presents the entire space. -/
def univ (h : TauCeti.Toric.IsIntegralLattice i) : RationalAffinePolyhedron h :=
  ⟨0, Fin.elim0, fun j => Fin.elim0 j⟩

/-- The empty family has full carrier. -/
@[simp]
theorem carrier_univ (h : TauCeti.Toric.IsIntegralLattice i) :
    (univ h).carrier = Set.univ := by
  ext x
  simp [carrier, univ]

/-- The presentation of the entire space has rational offsets. -/
@[simp]
theorem hasRationalOffsets_univ (h : TauCeti.Toric.IsIntegralLattice i) :
    (univ h).HasRationalOffsets := by
  simp [HasRationalOffsets, univ]

/-- A contradictory constant inequality presents the empty set. -/
def empty (h : TauCeti.Toric.IsIntegralLattice i) : RationalAffinePolyhedron h :=
  ⟨1, fun _ => ContinuousAffineMap.const ℝ V 1,
    fun _ => Toric.IsRationalFunctional.zero h⟩

/-- The contradictory constant inequality has empty carrier. -/
@[simp]
theorem carrier_empty (h : TauCeti.Toric.IsIntegralLattice i) :
    (empty h).carrier = ∅ := by
  ext x
  simp [carrier, empty]

/-- The contradictory constant presentation has rational offsets. -/
@[simp]
theorem hasRationalOffsets_empty (h : TauCeti.Toric.IsIntegralLattice i) :
    (empty h).HasRationalOffsets := by
  rw [hasRationalOffsets_iff]
  intro j
  exact ⟨1, by simp [empty]⟩

variable {N' W : Type*} [AddCommGroup N'] [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace W]
  {i' : N' →+ W} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- Pull back a presentation along an affine map with rational linear part.
Translations may be arbitrary real vectors, as the offsets may be real. -/
def preimage (P : RationalAffinePolyhedron h) (f : W →ᴬ[ℝ] V)
    (hf : Toric.IsRationalLinearMap h' h f.toAffineMap.linear) :
    RationalAffinePolyhedron h' where
  numConstraints := P.numConstraints
  inequality j := (P.inequality j).comp f
  rational_linear j := hf.map_functional (P.rational_linear j)

/-- Pulling back the inequalities pulls back the carrier. -/
@[simp]
theorem carrier_preimage (P : RationalAffinePolyhedron h) (f : W →ᴬ[ℝ] V)
    (hf : Toric.IsRationalLinearMap h' h f.toAffineMap.linear) :
    (P.preimage f hf).carrier = f ⁻¹' P.carrier := by
  ext x
  rfl

end RationalAffinePolyhedron

/-- A set admits a finite rational-normal affine presentation. -/
def IsRationalNormalPolyhedron (h : TauCeti.Toric.IsIntegralLattice i) (P : Set V) : Prop :=
  ∃ Q : RationalAffinePolyhedron h, Q.carrier = P

/-- A rational polyhedron also admits rational offsets. -/
def IsRationalPolyhedron (h : TauCeti.Toric.IsIntegralLattice i) (P : Set V) : Prop :=
  ∃ Q : RationalAffinePolyhedron h, Q.carrier = P ∧ Q.HasRationalOffsets

/-- Rational-normal polyhedrality is the existence of a presentation with this carrier. -/
theorem isRationalNormalPolyhedron_iff {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V} :
    IsRationalNormalPolyhedron h P ↔ ∃ Q : RationalAffinePolyhedron h, Q.carrier = P :=
  Iff.rfl

/-- Rational polyhedrality additionally requires rational offsets in the presentation. -/
theorem isRationalPolyhedron_iff {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V} :
    IsRationalPolyhedron h P ↔
      ∃ Q : RationalAffinePolyhedron h, Q.carrier = P ∧ Q.HasRationalOffsets := Iff.rfl

/-- A constant contradictory row gives an empty presentation with rational offsets. -/
@[simp]
theorem IsRationalPolyhedron.empty (h : TauCeti.Toric.IsIntegralLattice i) :
    IsRationalPolyhedron h (∅ : Set V) := by
  exact isRationalPolyhedron_iff.mpr
    ⟨RationalAffinePolyhedron.empty h, RationalAffinePolyhedron.carrier_empty h,
      RationalAffinePolyhedron.hasRationalOffsets_empty h⟩

namespace IsRationalPolyhedron

variable {h : Toric.IsIntegralLattice i} {P Q : Set V}

/-- Rational offsets in particular give a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron (hP : IsRationalPolyhedron h P) :
    IsRationalNormalPolyhedron h P := by
  obtain ⟨Q, hQ, _⟩ := hP
  exact ⟨Q, hQ⟩

/-- The whole space admits the empty presentation with rational offsets. -/
@[simp]
theorem univ (h : Toric.IsIntegralLattice i) : IsRationalPolyhedron h (Set.univ : Set V) :=
  ⟨RationalAffinePolyhedron.univ h, RationalAffinePolyhedron.carrier_univ h,
    RationalAffinePolyhedron.hasRationalOffsets_univ h⟩

/-- Intersection preserves rational normals and rational offsets. -/
theorem inter (hP : IsRationalPolyhedron h P) (hQ : IsRationalPolyhedron h Q) :
    IsRationalPolyhedron h (P ∩ Q) := by
  obtain ⟨P, rfl, hP⟩ := hP
  obtain ⟨Q, rfl, hQ⟩ := hQ
  exact ⟨P.inter Q, P.carrier_inter Q,
    RationalAffinePolyhedron.hasRationalOffsets_inter_iff.mpr ⟨hP, hQ⟩⟩

end IsRationalPolyhedron

namespace IsRationalNormalPolyhedron

variable {h : TauCeti.Toric.IsIntegralLattice i}

/-- The whole space is a rational-normal polyhedron. -/
@[simp]
theorem univ (h : TauCeti.Toric.IsIntegralLattice i) :
    IsRationalNormalPolyhedron h (Set.univ : Set V) :=
  isRationalNormalPolyhedron_iff.mpr
    ⟨RationalAffinePolyhedron.univ h, RationalAffinePolyhedron.carrier_univ h⟩

/-- The empty set is a rational-normal polyhedron. -/
@[simp]
theorem empty (h : TauCeti.Toric.IsIntegralLattice i) :
    IsRationalNormalPolyhedron h (∅ : Set V) :=
  isRationalNormalPolyhedron_iff.mpr
    ⟨RationalAffinePolyhedron.empty h, RationalAffinePolyhedron.carrier_empty h⟩

/-- Rational-normal polyhedra are closed. -/
theorem isClosed {P : Set V} (hP : IsRationalNormalPolyhedron h P) : IsClosed P := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  exact Q.isClosed

/-- Rational-normal polyhedra are convex. -/
theorem convex {P : Set V} (hP : IsRationalNormalPolyhedron h P) : Convex ℝ P := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  exact Q.convex

/-- A rational-normal polyhedron is a convex polyhedron in the sense of the supplier library. -/
theorem isConvexPolyhedron {P : Set V} (hP : IsRationalNormalPolyhedron h P) :
    TauCeti.IsConvexPolyhedron P := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  exact Q.isConvexPolyhedron

/-- Rational-normal polyhedra are closed under intersection. -/
theorem inter {P Q : Set V} (hP : IsRationalNormalPolyhedron h P)
    (hQ : IsRationalNormalPolyhedron h Q) : IsRationalNormalPolyhedron h (P ∩ Q) := by
  obtain ⟨P, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hQ
  exact isRationalNormalPolyhedron_iff.mpr ⟨P.inter Q, P.carrier_inter Q⟩

variable {N' W : Type*} [AddCommGroup N'] [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace W]
  {i' : N' →+ W} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- Rational-normal polyhedra pull back along affine maps with rational linear part. -/
theorem preimage {P : Set V} (hP : IsRationalNormalPolyhedron h P) (f : W →ᴬ[ℝ] V)
    (hf : Toric.IsRationalLinearMap h' h f.toAffineMap.linear) :
    IsRationalNormalPolyhedron h' (f ⁻¹' P) := by
  obtain ⟨P, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  exact isRationalNormalPolyhedron_iff.mpr ⟨P.preimage f hf, P.carrier_preimage f hf⟩

end IsRationalNormalPolyhedron

/-- Finitely many affine inequalities with rational linear parts cut out a
rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_setOf_forall {h : TauCeti.Toric.IsIntegralLattice i}
    {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    IsRationalNormalPolyhedron h {x | ∀ j, g j x ≤ 0} :=
  isRationalNormalPolyhedron_iff.mpr ⟨RationalAffinePolyhedron.ofFinite g hg, by
    ext x
    exact RationalAffinePolyhedron.mem_carrier_ofFinite hg⟩

/-- A finite family with rational linear parts and rational values at the origin
presents a rational polyhedron. -/
theorem isRationalPolyhedron_setOf_forall {h : Toric.IsIntegralLattice i}
    {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (ho : ∀ j, ∃ q : ℚ, g j 0 = (q : ℝ)) :
    IsRationalPolyhedron h {x | ∀ j, g j x ≤ 0} :=
  ⟨RationalAffinePolyhedron.ofFinite g hg, by
    ext x
    exact RationalAffinePolyhedron.mem_carrier_ofFinite hg,
    (RationalAffinePolyhedron.hasRationalOffsets_ofFinite_iff hg).mpr ho⟩

/-- A closed half-space `{x | ℓ x ≤ b}` bounded by a hyperplane with rational normal is a
rational-normal polyhedron, for any real offset `b`. -/
theorem isRationalNormalPolyhedron_setOf_le {h : TauCeti.Toric.IsIntegralLattice i}
    (ℓ : V →L[ℝ] ℝ) (hℓ : Toric.IsRationalFunctional h ℓ.toLinearMap) (b : ℝ) :
    IsRationalNormalPolyhedron h {x | ℓ x ≤ b} := by
  let g : V →ᴬ[ℝ] ℝ := ℓ.toContinuousAffineMap - ContinuousAffineMap.const ℝ V b
  have hg : g.toAffineMap.linear = ℓ.toLinearMap := by
    refine LinearMap.ext fun v => ?_
    simpa [g] using AffineMap.linear_apply_vsub g.toAffineMap v 0
  convert isRationalNormalPolyhedron_setOf_forall (h := h) (ι := Unit) (fun _ => g)
    (fun _ => hg ▸ hℓ) using 1
  ext x
  simp [g]

end TauCeti
