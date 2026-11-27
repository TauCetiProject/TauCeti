/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Module
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.KZero

/-!
# `K₀` of a C⋆-inductive limit is the direct limit of the `K₀`-groups

Let `(A i, f i j)` be a directed system of C⋆-algebras, possibly without unit and with connecting
maps that need not be injective, and `L = CStarInductiveLimit A f` its C⋆-inductive limit. The
projection `K₀`-groups `TauCeti.ProjectionKZero (A i)` form a directed system of abelian groups
along the induced maps (`TauCeti.CStarInductiveLimit.projectionKZeroSystem`), and the maps induced
by the canonical maps `of i : A i → L` assemble to an isomorphism

`TauCeti.CStarInductiveLimit.projectionKZeroDirectLimitEquiv :
  AddCommGroup.DirectLimit (fun i ↦ ProjectionKZero (A i)) _ ≃+ ProjectionKZero L`,

sending the class of `y : K₀(A i)` to the image of `y` under `of i`. Surjectivity and injectivity
are the two halves of the continuity of `K₀` on main
(`TauCeti.CStarInductiveLimit.exists_projectionKZero_map_of_eq`,
`TauCeti.CStarInductiveLimit.exists_projectionKZero_map_f_eq_zero_of_map_of_eq_zero`).

## Main declarations

* `TauCeti.CStarInductiveLimit.projectionKZeroSystem`: the directed system of `K₀`-groups.
* `TauCeti.CStarInductiveLimit.projectionKZeroDirectLimitEquiv`: `lim K₀(A i) ≃+ K₀(L)`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  5.2.4.
-/

public section

noncomputable section

namespace TauCeti

namespace CStarInductiveLimit

open NonUnitalStarRingHom (ofClass)

variable {ι : Type*} [Preorder ι] {A : ι → Type*}
  [∀ i, NonUnitalCStarAlgebra (A i)] {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
  [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
  [∀ i j (h : i ≤ j), NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
  [∀ i j (h : i ≤ j), StarHomClass (T h) (A i) (A j)]

variable (A f) in
/-- The directed system of projection `K₀`-groups of a directed system of C⋆-algebras, along the
maps induced by the connecting maps. -/
def projectionKZeroSystem (i j : ι) (h : i ≤ j) :
    ProjectionKZero (A i) →+ ProjectionKZero (A j) :=
  ProjectionKZero.map (ofClass (f i j h))

@[simp]
theorem projectionKZeroSystem_apply {i j : ι} (h : i ≤ j) (y : ProjectionKZero (A i)) :
    projectionKZeroSystem A f i j h y = ProjectionKZero.map (ofClass (f i j h)) y :=
  (rfl)

variable [DirectedSystem A (f · · ·)]

/-- The projection `K₀`-groups of a directed system of C⋆-algebras form a directed system. -/
instance directedSystem_projectionKZeroSystem :
    DirectedSystem (fun i ↦ ProjectionKZero (A i)) (projectionKZeroSystem A f · · ·) where
  map_self i y := by
    have h : ofClass (f i i le_rfl) = NonUnitalStarRingHom.id (A i) :=
      NonUnitalStarRingHom.ext fun a ↦ DirectedSystem.map_self (f := (f · · ·)) a
    rw [projectionKZeroSystem_apply, h, ProjectionKZero.map_id, AddMonoidHom.id_apply]
  map_map {i j k} hij hjk y := by
    rw [projectionKZeroSystem_apply, projectionKZeroSystem_apply, projectionKZeroSystem_apply,
      projectionKZero_map_f_map_f]

variable [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]

variable (A f) in
/-- The homomorphism `lim K₀(A i) → K₀(L)` induced by the canonical maps `of i : A i → L`. -/
def projectionKZeroDirectLimitHom :
    AddCommGroup.DirectLimit (fun i ↦ ProjectionKZero (A i)) (projectionKZeroSystem A f) →+
      ProjectionKZero (CStarInductiveLimit A f) :=
  AddCommGroup.DirectLimit.lift _ _ _ (fun i ↦ ProjectionKZero.map (ofClass (of A f i)))
    fun _ _ hij y ↦ projectionKZero_map_of_map_f hij y

@[simp]
theorem projectionKZeroDirectLimitHom_of (i : ι) (y : ProjectionKZero (A i)) :
    projectionKZeroDirectLimitHom A f (AddCommGroup.DirectLimit.of _ _ i y) =
      ProjectionKZero.map (ofClass (of A f i)) y :=
  AddCommGroup.DirectLimit.lift_of _ _ _ _ _

/-- Every class of `K₀(L)` comes from a stage. -/
theorem projectionKZeroDirectLimitHom_surjective :
    Function.Surjective (projectionKZeroDirectLimitHom A f) := fun x ↦ by
  obtain ⟨i, y, rfl⟩ := exists_projectionKZero_map_of_eq x
  exact ⟨_, projectionKZeroDirectLimitHom_of i y⟩

/-- A class of a stage that vanishes in `K₀(L)` vanishes at a later stage. -/
theorem projectionKZeroDirectLimitHom_injective :
    Function.Injective (projectionKZeroDirectLimitHom A f) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  induction z using AddCommGroup.DirectLimit.induction_on with
  | ih i y =>
    rw [projectionKZeroDirectLimitHom_of] at hz
    obtain ⟨j, hij, hj⟩ := exists_projectionKZero_map_f_eq_zero_of_map_of_eq_zero hz
    rw [← AddCommGroup.DirectLimit.of_f (G := fun i ↦ ProjectionKZero (A i)) hij,
      projectionKZeroSystem_apply, hj, map_zero]

variable (A f) in
/-- **Continuity of `K₀`.** For a directed system of C⋆-algebras with C⋆-inductive limit `L`, the
maps induced by the canonical maps `of i : A i → L` give an isomorphism
`lim K₀(A i) ≃+ K₀(L)` from the direct limit of the projection `K₀`-groups. -/
def projectionKZeroDirectLimitEquiv :
    AddCommGroup.DirectLimit (fun i ↦ ProjectionKZero (A i)) (projectionKZeroSystem A f) ≃+
      ProjectionKZero (CStarInductiveLimit A f) :=
  AddEquiv.ofBijective (projectionKZeroDirectLimitHom A f)
    ⟨projectionKZeroDirectLimitHom_injective, projectionKZeroDirectLimitHom_surjective⟩

@[simp]
theorem projectionKZeroDirectLimitEquiv_of (i : ι) (y : ProjectionKZero (A i)) :
    projectionKZeroDirectLimitEquiv A f (AddCommGroup.DirectLimit.of _ _ i y) =
      ProjectionKZero.map (ofClass (of A f i)) y :=
  projectionKZeroDirectLimitHom_of i y

/-- The inverse isomorphism sends the image of `y : K₀(A i)` to the class of `y`. -/
theorem projectionKZeroDirectLimitEquiv_symm_map_of (i : ι) (y : ProjectionKZero (A i)) :
    (projectionKZeroDirectLimitEquiv A f).symm (ProjectionKZero.map (ofClass (of A f i)) y) =
      AddCommGroup.DirectLimit.of _ _ i y :=
  (projectionKZeroDirectLimitEquiv A f).symm_apply_eq.2
    (projectionKZeroDirectLimitEquiv_of i y).symm

end CStarInductiveLimit

end TauCeti
