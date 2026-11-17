/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Sigma
public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic

/-!
# Transformations of generalised equations

A *transformation* of a generalised equation `Ω` (Kharlampovich–Myasnikov, §5.1) is a finite
family of formally consistent generalised equations `Ω₁, …, Ω_r`, the *successors* of `Ω`,
together with surjective `F(A)`-homomorphisms `θᵢ : F_{R(Ω)} → F_{R(Ωᵢ)}` of coordinate groups and
a map sending every solution `U` of `Ω` to a pair `(Ωᵢ, Uᵢ)` of a successor and a solution of it
such that `π_{Uᵢ} ∘ θᵢ = π_U`, where `π_U : F_{R(Ω)} → F(A)` is the homomorphism of the solution
`U`.

The source asks of an elementary transformation that the pair `(Ωᵢ, Uᵢ)` be the only one making
the triangle commute; here this is the property
`TauCeti.GenEq.Transformation.TransfersUniquely`, which every transformation with a single
successor has. Transformations compose (`TauCeti.GenEq.Transformation.bind`), and the derived
transformations of Makanin's process are such composites; uniqueness of the pair is not preserved
by composition in general, because a solution of a later successor need only compose to a group
solution of an intermediate equation, which is why the transfer map is part of the data.

In the other direction, composing the homomorphism of a solution of a successor with `θᵢ` always
gives a point of `Ω*` in `F(A)` (`TauCeti.GenEq.Transformation.solution_backward`), in general not
a solution of `Ω`: adjacent words may cancel.

## Main definitions

* `TauCeti.GenEq.Transformation`: transformations of a generalised equation.
* `TauCeti.GenEq.Transformation.id`: the identity transformation.
* `TauCeti.GenEq.Transformation.bind`, `TauCeti.GenEq.Transformation.andThen`: composition of
  transformations.
* `TauCeti.GenEq.Transformation.ofFamily`: the transformation whose successors are the formally
  consistent members of a finite family of generalised equations.
* `TauCeti.GenEq.Transformation.TransfersUniquely`: every solution has exactly one transfer.

## Main results

* `TauCeti.GenEq.Transformation.solution_forward`: if a transformation transfers solutions
  uniquely, every solution of `Ω` corresponds to exactly one pair of a successor and a solution
  of it.
* `TauCeti.GenEq.Transformation.solution_backward`: a solution of a successor composes to a point
  of `Ω*` in `F(A)`.
* `TauCeti.GenEq.Transformation.transfersUniquely_of_subsingleton`: a transformation with at most
  one successor transfers solutions uniquely; in particular the identity does.
* `TauCeti.GenEq.Transformation.transfersUniquely_ofFamily_iff`: for the transformation given by
  a family, uniqueness of the pair may be checked over all members of the family, formally
  consistent or not.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod

variable {A : Type*}

/-- A transformation of a generalised equation `Ω` (Kharlampovich–Myasnikov, §5.1): a finite
family of formally consistent generalised equations, each with a surjective `F(A)`-homomorphism
from the coordinate group of `Ω`, and a transfer of every solution of `Ω` to a solution of a
member of the family through which the homomorphism of the solution factors. The equation `Ω`
itself is not required to be formally consistent; if it is not, it has no solution. -/
structure Transformation (Ω : GenEq A) where
  /-- The index set of the successors. -/
  ι : Type
  /-- There are finitely many successors. -/
  finite : Finite ι
  /-- The successors. -/
  target : ι → GenEq A
  /-- The successors are formally consistent. -/
  isFormallyConsistent_target : ∀ i, (target i).IsFormallyConsistent
  /-- The `F(A)`-homomorphism from the coordinate group of `Ω` to that of a successor. -/
  hom : ∀ i, GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (target i).toSystem)
  /-- The homomorphisms to the successors are surjective. -/
  hom_surjective : ∀ i, Function.Surjective (hom i)
  /-- The transfer of a solution of `Ω` to a successor. -/
  transfer : Ω.Solution → (i : ι) × (target i).Solution
  /-- The homomorphism of a solution factors through the homomorphism of its transfer. -/
  toHom_transfer : ∀ U, (transfer U).2.toHom.comp (hom (transfer U).1) = U.toHom

namespace Transformation

attribute [instance] Transformation.finite

variable {Ω : GenEq A}

/-- The identity transformation of a formally consistent generalised equation: its only successor
is `Ω`, with the identity homomorphism, and every solution is transferred to itself. -/
@[expose] def id (Ω : GenEq A) (hΩ : Ω.IsFormallyConsistent) : Transformation Ω where
  ι := Unit
  finite := inferInstance
  target _ := Ω
  isFormallyConsistent_target _ := hΩ
  hom _ := GHom.id _
  hom_surjective _ := by
    rw [GHom.coe_id]
    exact Function.surjective_id
  transfer U := ⟨(), U⟩
  toHom_transfer _ := GHom.comp_id _

/-- The only successor of the identity transformation is `Ω` itself. -/
@[simp]
theorem id_target (hΩ : Ω.IsFormallyConsistent) (i : (Transformation.id Ω hΩ).ι) :
    (Transformation.id Ω hΩ).target i = Ω :=
  (rfl)

/-- The identity transformation carries the identity homomorphism of coordinate groups. -/
@[simp]
theorem id_hom (hΩ : Ω.IsFormallyConsistent) (i : (Transformation.id Ω hΩ).ι) :
    (Transformation.id Ω hΩ).hom i = GHom.id _ :=
  (rfl)

/-- The identity transformation leaves every solution unchanged. -/
@[simp]
theorem id_transfer (hΩ : Ω.IsFormallyConsistent) (U : Ω.Solution) :
    (Transformation.id Ω hΩ).transfer U = ⟨(), U⟩ :=
  (rfl)

/-- Composition of transformations: apply `T`, then to each successor `T.target i` the
transformation `S i`. The successors are those of the `S i`, with the composite homomorphisms and
the composite transfer. -/
@[expose] def bind (T : Transformation Ω) (S : ∀ i, Transformation (T.target i)) :
    Transformation Ω where
  ι := (i : T.ι) × (S i).ι
  finite := inferInstance
  target p := (S p.1).target p.2
  isFormallyConsistent_target p := (S p.1).isFormallyConsistent_target p.2
  hom p := ((S p.1).hom p.2).comp (T.hom p.1)
  hom_surjective p := by
    rw [GHom.coe_comp]
    exact ((S p.1).hom_surjective p.2).comp (T.hom_surjective p.1)
  transfer U :=
    ⟨⟨(T.transfer U).1, ((S (T.transfer U).1).transfer (T.transfer U).2).1⟩,
      ((S (T.transfer U).1).transfer (T.transfer U).2).2⟩
  toHom_transfer U := by
    rw [← GHom.comp_assoc, (S (T.transfer U).1).toHom_transfer, T.toHom_transfer]

/-- The successors of a composite are the successors of the second transformations. -/
@[simp]
theorem bind_target (T : Transformation Ω) (S : ∀ i, Transformation (T.target i))
    (p : (T.bind S).ι) : (T.bind S).target p = (S p.1).target p.2 :=
  (rfl)

/-- The homomorphism to a successor of a composite is the composite of the homomorphisms. -/
@[simp]
theorem bind_hom (T : Transformation Ω) (S : ∀ i, Transformation (T.target i)) (p : (T.bind S).ι) :
    (T.bind S).hom p = ((S p.1).hom p.2).comp (T.hom p.1) :=
  (rfl)

/-- A composite transfers a solution first by `T`, then by the transformation applied to the
successor receiving it. -/
@[simp]
theorem bind_transfer (T : Transformation Ω) (S : ∀ i, Transformation (T.target i))
    (U : Ω.Solution) : (T.bind S).transfer U =
      ⟨⟨(T.transfer U).1, ((S (T.transfer U).1).transfer (T.transfer U).2).1⟩,
        ((S (T.transfer U).1).transfer (T.transfer U).2).2⟩ :=
  (rfl)

/-- Composition with a transformation defined for every formally consistent generalised
equation: apply `T`, then `S` to each successor. -/
abbrev andThen (T : Transformation Ω)
    (S : ∀ Ω' : GenEq A, Ω'.IsFormallyConsistent → Transformation Ω') : Transformation Ω :=
  T.bind fun i => S (T.target i) (T.isFormallyConsistent_target i)

/-- Composing the homomorphism of a solution of a successor with the homomorphism of the
transformation gives a point of `Ω*` in `F(A)`: a group solution of `Ω`. -/
theorem solution_backward (T : Transformation Ω) (i : T.ι) (U' : (T.target i).Solution) :
    (fun k => U'.toHom (T.hom i ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) :
      Ω.coordGroup))) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem := by
  convert (CoordGroup.homEquiv _ _ (U'.toHom.comp (T.hom i))).2 using 1
  ext k
  simp

/-- Two solutions of a successor whose homomorphisms agree after composition with the
homomorphism of the transformation are equal. -/
theorem eq_of_toHom_comp_hom_eq (T : Transformation Ω) (i : T.ι) {U₁ U₂ : (T.target i).Solution}
    (h : U₁.toHom.comp (T.hom i) = U₂.toHom.comp (T.hom i)) : U₁ = U₂ := by
  refine Solution.point_injective (funext fun k => ?_)
  obtain ⟨y, hy⟩ := T.hom_surjective i
    ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin (T.target i).numItems)) :
      (T.target i).coordGroup)
  simpa [hy] using DFunLike.congr_fun h y

/-- A transformation transfers solutions uniquely when, for every solution `U` of `Ω`, the
transfer of `U` is the only pair of a successor and a solution of it through which the
homomorphism of `U` factors. Successors with different indices are different pairs, even if they
are equal generalised equations. -/
def TransfersUniquely (T : Transformation Ω) : Prop :=
  ∀ (U : Ω.Solution) (p : (i : T.ι) × (T.target i).Solution),
    p.2.toHom.comp (T.hom p.1) = U.toHom → p = T.transfer U

/-- Unfolding `TransfersUniquely`. -/
theorem transfersUniquely_iff (T : Transformation Ω) : T.TransfersUniquely ↔
    ∀ (U : Ω.Solution) (p : (i : T.ι) × (T.target i).Solution),
      p.2.toHom.comp (T.hom p.1) = U.toHom → p = T.transfer U :=
  Iff.rfl

/-- If a transformation transfers solutions uniquely, every solution of `Ω` corresponds to exactly
one pair of a successor and a solution of it making the triangle of homomorphisms commute. -/
theorem solution_forward {T : Transformation Ω} (hT : T.TransfersUniquely) (U : Ω.Solution) :
    ∃! p : (i : T.ι) × (T.target i).Solution, p.2.toHom.comp (T.hom p.1) = U.toHom :=
  ⟨T.transfer U, T.toHom_transfer U, fun p hp => hT U p hp⟩

/-- A transformation with at most one successor transfers solutions uniquely. -/
theorem transfersUniquely_of_subsingleton (T : Transformation Ω) [Subsingleton T.ι] :
    T.TransfersUniquely := by
  intro U ⟨i, U'⟩ h
  have ht := T.toHom_transfer U
  generalize T.transfer U = q at ht ⊢
  obtain ⟨j, U''⟩ := q
  obtain rfl := Subsingleton.elim i j
  obtain rfl := T.eq_of_toHom_comp_hom_eq i (h.trans ht.symm)
  rfl

/-- The identity transformation transfers solutions uniquely. -/
theorem transfersUniquely_id (hΩ : Ω.IsFormallyConsistent) :
    (Transformation.id Ω hΩ).TransfersUniquely :=
  have : Subsingleton (Transformation.id Ω hΩ).ι := inferInstanceAs (Subsingleton Unit)
  transfersUniquely_of_subsingleton _

/-! ### Transformations given by a family of generalised equations -/

section ofFamily

variable {κ : Type} [Finite κ] (target : κ → GenEq A)
  (hom : ∀ k, GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (target k).toSystem))
  (hom_surjective : ∀ k, Function.Surjective (hom k))
  (transfer : Ω.Solution → (k : κ) × (target k).Solution)
  (toHom_transfer : ∀ U, (transfer U).2.toHom.comp (hom (transfer U).1) = U.toHom)

/-- The transformation whose successors are the formally consistent members of a finite family
of generalised equations with surjective homomorphisms from the coordinate group of `Ω`, given a
transfer of every solution of `Ω` to a member of the family. A member receiving a solution is
formally consistent, so no transfer is lost. -/
@[expose] def ofFamily : Transformation Ω where
  ι := {k // (target k).IsFormallyConsistent}
  finite := inferInstance
  target i := target i.1
  isFormallyConsistent_target i := i.2
  hom i := hom i.1
  hom_surjective i := hom_surjective i.1
  transfer U := ⟨⟨(transfer U).1, (transfer U).2.isFormallyConsistent⟩, (transfer U).2⟩
  toHom_transfer := toHom_transfer

/-- The successors of `ofFamily` are the formally consistent members of the family. -/
@[simp]
theorem ofFamily_target (i : (ofFamily target hom hom_surjective transfer toHom_transfer).ι) :
    (ofFamily target hom hom_surjective transfer toHom_transfer).target i = target i.1 :=
  (rfl)

/-- The homomorphisms of `ofFamily` are those of the family. -/
@[simp]
theorem ofFamily_hom (i : (ofFamily target hom hom_surjective transfer toHom_transfer).ι) :
    (ofFamily target hom hom_surjective transfer toHom_transfer).hom i = hom i.1 :=
  (rfl)

/-- `ofFamily` transfers every solution to the member of the family chosen by the given
transfer, with the same solution. -/
@[simp]
theorem ofFamily_transfer (U : Ω.Solution) :
    (ofFamily target hom hom_surjective transfer toHom_transfer).transfer U =
      ⟨⟨(transfer U).1, (transfer U).2.isFormallyConsistent⟩, (transfer U).2⟩ :=
  (rfl)

variable {target hom hom_surjective transfer toHom_transfer} in
/-- The transformation whose successors are the formally consistent members of a family transfers
solutions uniquely if and only if, for every solution `U` of `Ω`, the given transfer of `U` is the
only pair of a member of the family and a solution of it through which the homomorphism of `U`
factors. -/
theorem transfersUniquely_ofFamily_iff :
    (ofFamily target hom hom_surjective transfer toHom_transfer).TransfersUniquely ↔
      ∀ (U : Ω.Solution) (p : (k : κ) × (target k).Solution),
        p.2.toHom.comp (hom p.1) = U.toHom → p = transfer U := by
  refine ⟨fun h U ⟨k, U'⟩ hp => ?_, fun h U ⟨⟨k, hk⟩, U'⟩ hp => ?_⟩
  · have h' := h U ⟨⟨k, U'.isFormallyConsistent⟩, U'⟩ hp
    rw [ofFamily_transfer] at h'
    generalize transfer U = q at h' ⊢
    obtain ⟨k', U''⟩ := q
    cases h'
    rfl
  · have h' := h U ⟨k, U'⟩ hp
    rw [ofFamily_transfer]
    generalize transfer U = q at h' ⊢
    subst h'
    rfl

end ofFamily

/-! ### Examples -/

/-- Uniqueness of the transfer depends on the indices of the successors: the family of two copies
of the empty generalised equation, each with the identity homomorphism, does not transfer solutions
uniquely, since the solution of the empty generalised equation factors through either copy. -/
example : ¬ (ofFamily (Ω := (GenEq.empty : GenEq A)) (κ := Bool) (fun _ => GenEq.empty)
    (fun _ => GHom.id _) (fun _ => by rw [GHom.coe_id]; exact Function.surjective_id)
    (fun U => ⟨true, U⟩) (fun _ => GHom.comp_id _)).TransfersUniquely := by
  rw [transfersUniquely_ofFamily_iff]
  intro h
  simpa using h default ⟨false, default⟩ (GHom.comp_id _)

end Transformation

end GenEq

end TauCeti
