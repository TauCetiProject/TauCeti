/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Module
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.KZero.Basic

/-!
# The projection monoid of a C⋆-inductive limit is the direct limit

Let `(A i, f i j)` be a directed system of C⋆-algebras, possibly without unit and with connecting
maps that need not be injective, and `L = CStarInductiveLimit A f` its C⋆-inductive limit. The
projection monoids `V(A i) = TauCeti.ProjectionMonoid (A i)` form a directed system of commutative
monoids along the induced maps (`TauCeti.CStarInductiveLimit.projectionMonoidSystem`), and the maps
induced by the canonical maps `of i : A i → L` assemble to an isomorphism

`TauCeti.CStarInductiveLimit.projectionMonoidDirectLimitEquiv :
  AddCommGroup.DirectLimit (fun i ↦ ProjectionMonoid (A i)) _ ≃+ ProjectionMonoid L`

of commutative monoids, sending the class of `y : V(A i)` to the image of `y` under `of i`
(`AddCommGroup.DirectLimit` is the direct limit of commutative additive monoids). Surjectivity and
injectivity are the element-wise continuity statements for `V`
(`TauCeti.CStarInductiveLimit.exists_projectionMonoid_map_of_eq`,
`TauCeti.CStarInductiveLimit.exists_projectionMonoid_map_f_eq_of_map_of_eq`). Unlike the group
case, injectivity is not a kernel statement: two classes of a stage with the same image in `V(L)`
become equal at a later stage.

## Main declarations

* `TauCeti.CStarInductiveLimit.projectionMonoidSystem`: the directed system of projection monoids.
* `TauCeti.CStarInductiveLimit.projectionMonoidDirectLimitEquiv`: `lim V(A i) ≃+ V(L)`.

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
/-- The directed system of projection monoids of a directed system of C⋆-algebras, along the maps
induced by the connecting maps. -/
def projectionMonoidSystem (i j : ι) (h : i ≤ j) :
    ProjectionMonoid (A i) →+ ProjectionMonoid (A j) :=
  ProjectionMonoid.map (ofClass (f i j h))

theorem projectionMonoidSystem_apply {i j : ι} (h : i ≤ j) (y : ProjectionMonoid (A i)) :
    projectionMonoidSystem A f i j h y = ProjectionMonoid.map (ofClass (f i j h)) y :=
  (rfl)

variable [DirectedSystem A (f · · ·)]

/-- The projection monoids of a directed system of C⋆-algebras form a directed system. -/
instance directedSystem_projectionMonoidSystem :
    DirectedSystem (fun i ↦ ProjectionMonoid (A i)) (projectionMonoidSystem A f · · ·) where
  map_self i y := by
    rw [projectionMonoidSystem_apply, ofClass_f_self, ProjectionMonoid.map_id,
      AddMonoidHom.id_apply]
  map_map {i j k} hij hjk y := by
    rw [projectionMonoidSystem_apply, projectionMonoidSystem_apply, projectionMonoidSystem_apply,
      projectionMonoid_map_f_map_f]

variable [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]

variable (A f) in
/-- The homomorphism `lim V(A i) → V(L)` induced by the canonical maps `of i : A i → L`. -/
def projectionMonoidDirectLimitHom :
    AddCommGroup.DirectLimit (fun i ↦ ProjectionMonoid (A i)) (projectionMonoidSystem A f) →+
      ProjectionMonoid (CStarInductiveLimit A f) :=
  AddCommGroup.DirectLimit.lift _ _ _ (fun i ↦ ProjectionMonoid.map (ofClass (of A f i)))
    fun _ _ hij y ↦ projectionMonoid_map_of_map_f hij y

@[simp]
theorem projectionMonoidDirectLimitHom_of (i : ι) (y : ProjectionMonoid (A i)) :
    projectionMonoidDirectLimitHom A f (AddCommGroup.DirectLimit.of _ _ i y) =
      ProjectionMonoid.map (ofClass (of A f i)) y :=
  AddCommGroup.DirectLimit.lift_of _ _ _ _ _

/-- Every element of `V(L)` comes from a stage. -/
theorem projectionMonoidDirectLimitHom_surjective :
    Function.Surjective (projectionMonoidDirectLimitHom A f) := fun x ↦ by
  obtain ⟨i, y, rfl⟩ := exists_projectionMonoid_map_of_eq x
  exact ⟨_, projectionMonoidDirectLimitHom_of i y⟩

/-- Two elements of the direct limit with the same image in `V(L)` are equal: represented at a
common stage, they become equal at a later stage. -/
theorem projectionMonoidDirectLimitHom_injective :
    Function.Injective (projectionMonoidDirectLimitHom A f) := by
  intro z w hzw
  induction z using AddCommGroup.DirectLimit.induction_on with
  | ih i y =>
  induction w using AddCommGroup.DirectLimit.induction_on with
  | ih i' y' =>
  obtain ⟨k, hik, hi'k⟩ := exists_ge_ge i i'
  rw [← AddCommGroup.DirectLimit.of_f (G := fun i ↦ ProjectionMonoid (A i)) hik,
    ← AddCommGroup.DirectLimit.of_f (G := fun i ↦ ProjectionMonoid (A i)) hi'k] at hzw ⊢
  rw [projectionMonoidDirectLimitHom_of, projectionMonoidDirectLimitHom_of] at hzw
  obtain ⟨j, hkj, hj⟩ := exists_projectionMonoid_map_f_eq_of_map_of_eq hzw
  rw [← AddCommGroup.DirectLimit.of_f (G := fun i ↦ ProjectionMonoid (A i)) hkj,
    ← AddCommGroup.DirectLimit.of_f (G := fun i ↦ ProjectionMonoid (A i)) hkj]
  simp only [projectionMonoidSystem_apply] at hj ⊢
  rw [hj]

variable (A f) in
/-- **Continuity of the projection monoid.** For a directed system of C⋆-algebras with
C⋆-inductive limit `L`, the maps induced by the canonical maps `of i : A i → L` give an isomorphism
`lim V(A i) ≃+ V(L)` of commutative monoids from the direct limit of the projection monoids. -/
def projectionMonoidDirectLimitEquiv :
    AddCommGroup.DirectLimit (fun i ↦ ProjectionMonoid (A i)) (projectionMonoidSystem A f) ≃+
      ProjectionMonoid (CStarInductiveLimit A f) :=
  AddEquiv.ofBijective (projectionMonoidDirectLimitHom A f)
    ⟨projectionMonoidDirectLimitHom_injective, projectionMonoidDirectLimitHom_surjective⟩

@[simp]
theorem projectionMonoidDirectLimitEquiv_of (i : ι) (y : ProjectionMonoid (A i)) :
    projectionMonoidDirectLimitEquiv A f (AddCommGroup.DirectLimit.of _ _ i y) =
      ProjectionMonoid.map (ofClass (of A f i)) y :=
  projectionMonoidDirectLimitHom_of i y

/-- The inverse isomorphism sends the image of `y : V(A i)` to the class of `y`. -/
@[simp]
theorem projectionMonoidDirectLimitEquiv_symm_map_of (i : ι) (y : ProjectionMonoid (A i)) :
    (projectionMonoidDirectLimitEquiv A f).symm (ProjectionMonoid.map (ofClass (of A f i)) y) =
      AddCommGroup.DirectLimit.of _ _ i y :=
  (projectionMonoidDirectLimitEquiv A f).symm_apply_eq.2
    (projectionMonoidDirectLimitEquiv_of i y).symm

end CStarInductiveLimit

end TauCeti
