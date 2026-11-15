/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Completion
public import Mathlib.Algebra.Category.AlgCat.Limits
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Algebra structures on filtered ring completions

The compatible-family ring completion of an algebra is itself an algebra, with
scalar multiplication computed at each finite order. Its projections and canonical
map are algebra homomorphisms, and compatible families of algebra homomorphisms
lift uniquely. This gives an inverse limit in `AlgCat` on the same carrier as the
ring completion, for use in complete coefficient algebras.

The construction refines the existing ring completion using Mathlib's `AlgCat.sectionsSubalgebra`
and quotient-algebra interfaces, in particular `Ideal.Quotient.factorₐ`.

Adapted from `Mei/RingTheory/FilteredAlgebra/Algebra.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (F : TauCeti.AlgFiltration A)

/-- The quotient tower in the category of algebras. -/
-- The object formula must compute to give arrows their concrete quotient-algebra types.
@[expose]
def quotientAlgebraDiagram : ℕᵒᵖ ⥤ AlgCat R where
  obj k := AlgCat.of R (A ⧸ F.ideal (k.unop + 1))
  map f := AlgCat.ofHom (Ideal.Quotient.factorₐ R
    (F.antitone (Nat.add_le_add_right (leOfHom f.unop) 1)))
  map_id _ := by
    apply AlgCat.hom_ext
    apply AlgHom.toRingHom_injective
    exact Ideal.Quotient.factor_eq
  map_comp f g := by
    apply AlgCat.hom_ext
    apply AlgHom.toRingHom_injective
    exact (Ideal.Quotient.factor_comp
      (F.antitone (Nat.add_le_add_right (leOfHom f.unop) 1))
      (F.antitone (Nat.add_le_add_right (leOfHom g.unop) 1))).symm

/-- Compatible quotient families form a subalgebra of the product of quotient algebras. -/
def completionSubalgebra : Subalgebra R (∀ k : ℕᵒᵖ, A ⧸ F.ideal (k.unop + 1)) :=
  let S : Subalgebra R (∀ k : ℕᵒᵖ, A ⧸ F.ideal (k.unop + 1)) :=
    AlgCat.sectionsSubalgebra (F.quotientAlgebraDiagram (R := R))
  -- Keep the original ring carrier across the opaque module boundary.
  S.copy (F.completion : Set _) (by
    ext x
    refine (F.mem_completion_iff x).trans ?_
    constructor
    · intro hx k l f
      exact hx (leOfHom f.unop)
    · intro hx k l h
      exact hx (homOfLE h).op)

/-- Forgetting scalars recovers exactly the compatible-family ring completion. -/
@[simp]
theorem completionSubalgebra_toSubring :
    (F.completionSubalgebra (R := R)).toSubring = F.completion := (rfl)

/-- Membership in the completion subalgebra is the original ring compatibility condition. -/
@[simp]
theorem mem_completionSubalgebra_iff
    (x : ∀ k : ℕᵒᵖ, A ⧸ F.ideal (k.unop + 1)) :
    x ∈ F.completionSubalgebra (R := R) ↔ x ∈ F.completion := (Iff.rfl)

/-- The algebra structure on the ring completion is inherited from componentwise scalars. -/
-- The subalgebra was built with precisely the ring completion's carrier and operations.
instance completionAlgebra : Algebra R F.completion :=
  inferInstanceAs (Algebra R (F.completionSubalgebra (R := R)))

/-- Scalars in the completion have their usual classes in each quotient algebra. -/
@[simp]
theorem projection_algebraMap (k : ℕ) (r : R) :
    F.projection k (algebraMap R F.completion r) =
      algebraMap R (A ⧸ F.ideal (k + 1)) r := by
  rw [F.projection_apply]
  rfl

/-- The finite-order projection as an algebra homomorphism. -/
def projectionₐ (k : ℕ) : F.completion →ₐ[R] A ⧸ F.ideal (k + 1) where
  __ := F.projection k
  commutes' := F.projection_algebraMap k

/-- Forgetting scalars in an algebra projection gives the ring projection. -/
@[simp]
theorem coe_projectionₐ (k : ℕ) :
    (F.projectionₐ (R := R) k : F.completion →+* A ⧸ F.ideal (k + 1)) =
      F.projection k := (rfl)

/-- Algebra projections evaluate by the existing ring projections. -/
@[simp]
theorem projectionₐ_apply (k : ℕ) (x : F.completion) :
    F.projectionₐ (R := R) k x = F.projection k x := (rfl)

/-- The canonical map into the completion as an algebra homomorphism. -/
def toCompletionₐ : A →ₐ[R] F.completion where
  __ := F.toCompletion
  commutes' r := by
    apply F.completion_ext
    intro k
    simp

/-- Forgetting scalars in the canonical algebra map gives the canonical ring map. -/
@[simp]
theorem coe_toCompletionₐ :
    (F.toCompletionₐ (R := R) : A →+* F.completion) = F.toCompletion := (rfl)

/-- The canonical algebra map has the same values as the canonical ring map. -/
@[simp]
theorem toCompletionₐ_apply (x : A) :
    F.toCompletionₐ (R := R) x = F.toCompletion x := (rfl)

/-- The canonical map sends scalars of the algebra to scalars of the completion. -/
@[simp]
theorem toCompletion_algebraMap (r : R) :
    F.toCompletion (algebraMap R A r) = algebraMap R F.completion r := by
  rw [← toCompletionₐ_apply (R := R), AlgHom.commutes]

variable {B : Type*} [Semiring B] [Algebra R B]

/-- Lift a compatible family of algebra homomorphisms into the quotient algebras. -/
def liftₐ (f : ∀ k, B →ₐ[R] A ⧸ F.ideal (k + 1))
    (hf : ∀ {k l} (h : k ≤ l),
      (Ideal.Quotient.factorₐ R (F.antitone (Nat.add_le_add_right h 1))).comp (f l) = f k) :
    B →ₐ[R] F.completion where
  __ := F.lift (fun k => (f k).toRingHom) (fun h => congrArg AlgHom.toRingHom (hf h))
  commutes' r := by
    apply F.completion_ext
    intro k
    simp

/-- Forgetting scalars in an algebra lift gives the compatible-family ring lift. -/
@[simp]
theorem coe_liftₐ (f : ∀ k, B →ₐ[R] A ⧸ F.ideal (k + 1)) (hf) :
    (F.liftₐ f hf : B →+* F.completion) =
      F.lift (fun k => (f k).toRingHom) (fun h => congrArg AlgHom.toRingHom (hf h)) := (rfl)

/-- Finite-order components of the algebra lift are the specified homomorphisms. -/
@[simp]
theorem projection_liftₐ (f : ∀ k, B →ₐ[R] A ⧸ F.ideal (k + 1)) (hf) (k : ℕ) (x : B) :
    F.projection k (F.liftₐ f hf x) = f k x :=
  F.projection_lift _ _ k x

/-- Algebra homomorphisms into the completion are determined by all projections. -/
theorem algHom_ext {f g : B →ₐ[R] F.completion}
    (h : ∀ k, (F.projectionₐ k).comp f = (F.projectionₐ k).comp g) : f = g := by
  apply AlgHom.ext
  intro x
  exact F.completion_ext fun k => AlgHom.congr_fun (h k) x

/-- The algebra tower has the same underlying ring diagram as the ring completion. -/
@[simp]
theorem quotientAlgebraDiagram_forget :
    F.quotientAlgebraDiagram (R := R) ⋙ forget₂ (AlgCat R) RingCat =
      F.quotientDiagram := (rfl)

/-- The order-`k` algebra is the quotient by filtration order `k + 1`. -/
@[simp]
theorem quotientAlgebraDiagram_obj (k : ℕᵒᵖ) :
    (F.quotientAlgebraDiagram (R := R)).obj k =
      AlgCat.of R (A ⧸ F.ideal (k.unop + 1)) := (rfl)

/-- Arrows in the algebra tower are the canonical quotient algebra maps. -/
@[simp]
theorem quotientAlgebraDiagram_map_hom {k l : ℕᵒᵖ} (f : k ⟶ l) :
    ((F.quotientAlgebraDiagram (R := R)).map f).hom = Ideal.Quotient.factorₐ R
      (F.antitone (Nat.add_le_add_right (leOfHom f.unop) 1)) := (rfl)

/-- The completion cone in algebras has the finite-order algebra projections as legs. -/
def completionAlgebraCone : Cone (F.quotientAlgebraDiagram (R := R)) where
  pt := AlgCat.of R F.completion
  π :=
    { app := fun k => AlgCat.ofHom (F.projectionₐ k.unop)
      naturality := by
        intro k l f
        apply AlgCat.hom_ext
        apply AlgHom.ext
        intro x
        exact (F.factor_projection (leOfHom f.unop) x).symm }

/-- The point of the algebra cone is the original ring completion with its scalar action. -/
@[simp]
theorem completionAlgebraCone_pt :
    (F.completionAlgebraCone (R := R)).pt = AlgCat.of R F.completion := (rfl)

/-- Under the point and object identifications, cone legs are the algebra projections. -/
@[simp]
theorem completionAlgebraCone_π_app (k : ℕᵒᵖ) :
    (F.completionAlgebraCone (R := R)).π.app k =
      eqToHom F.completionAlgebraCone_pt ≫ AlgCat.ofHom (F.projectionₐ k.unop) ≫
        eqToHom (F.quotientAlgebraDiagram_obj k).symm := (rfl)

/-- The completion is the inverse limit of its finite-order quotients as an algebra. -/
def completionAlgebraConeIsLimit : IsLimit (F.completionAlgebraCone (R := R)) where
  lift s := AlgCat.ofHom (F.liftₐ (fun k => (s.π.app (op k)).hom) (by
    intro k l h
    exact congrArg AlgCat.Hom.hom (s.w (homOfLE h).op)))
  fac s k := by
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact F.projection_liftₐ _
      (fun h => congrArg AlgCat.Hom.hom (s.w (homOfLE h).op)) k.unop x
  uniq s m hm := by
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply F.completion_ext
    intro k
    exact (AlgHom.congr_fun (congrArg AlgCat.Hom.hom (hm (op k))) x).trans
      (F.projection_liftₐ _
        (fun h => congrArg AlgCat.Hom.hom (s.w (homOfLE h).op)) k x).symm

/-- The concrete completion is canonically isomorphic to the categorical algebra limit. -/
noncomputable def completionAlgebraIsoLimit :
    AlgCat.of R F.completion ≅ limit (F.quotientAlgebraDiagram (R := R)) :=
  F.completionAlgebraConeIsLimit.conePointUniqueUpToIso
    (limit.isLimit (F.quotientAlgebraDiagram (R := R)))

/-- The canonical algebra-limit comparison identifies the finite-order projections. -/
@[reassoc (attr := simp)]
theorem completionAlgebraIsoLimit_hom_π (k : ℕᵒᵖ) :
    (F.completionAlgebraIsoLimit (R := R)).hom ≫
      limit.π (F.quotientAlgebraDiagram (R := R)) k =
        AlgCat.ofHom (F.projectionₐ k.unop) := by
  exact F.completionAlgebraConeIsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit (F.quotientAlgebraDiagram (R := R))) k

/-- The inverse algebra-limit comparison recovers the finite quotient components. -/
@[reassoc (attr := simp)]
theorem completionAlgebraIsoLimit_inv_projection (k : ℕᵒᵖ) :
    (F.completionAlgebraIsoLimit (R := R)).inv ≫ AlgCat.ofHom (F.projectionₐ k.unop) =
      limit.π (F.quotientAlgebraDiagram (R := R)) k := by
  exact F.completionAlgebraConeIsLimit.conePointUniqueUpToIso_inv_comp
    (limit.isLimit (F.quotientAlgebraDiagram (R := R))) k

section RestrictScalars

variable {S : Type*} [CommRing S] [Algebra S R] [Algebra S A] [IsScalarTower S R A]

/-- Restricting scalars preserves the compatible-family subalgebra and its carrier. -/
@[simp]
theorem completionSubalgebra_restrictScalars :
    (F.completionSubalgebra (R := R)).restrictScalars S =
      F.completionSubalgebra (R := S) := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_completionSubalgebra_iff]

/-- Compatible scalar actions on the original algebra remain compatible on the completion. -/
instance completionIsScalarTower : IsScalarTower S R F.completion :=
  IsScalarTower.of_algebraMap_eq fun s => by
    apply F.completion_ext
    intro k
    rw [F.projection_algebraMap, F.projection_algebraMap]
    exact IsScalarTower.algebraMap_apply S R _ s

/-- Restricting scalars in a finite-order projection gives the projection over smaller scalars. -/
@[simp]
theorem projectionₐ_restrictScalars (k : ℕ) :
    (F.projectionₐ (R := R) k).restrictScalars S = F.projectionₐ (R := S) k := by
  ext x
  rfl

/-- Restricting scalars preserves the canonical algebra map into the completion. -/
@[simp]
theorem toCompletionₐ_restrictScalars :
    (F.toCompletionₐ (R := R)).restrictScalars S = F.toCompletionₐ (R := S) := by
  ext x
  rfl

variable [Algebra S B] [IsScalarTower S R B]

/-- Restricting scalars commutes with lifting compatible families of algebra maps. -/
@[simp]
theorem liftₐ_restrictScalars (f : ∀ k, B →ₐ[R] A ⧸ F.ideal (k + 1)) (hf) :
    (F.liftₐ f hf).restrictScalars S =
      F.liftₐ (fun k => (f k).restrictScalars S)
        (fun h => AlgHom.toRingHom_injective (congrArg AlgHom.toRingHom (hf h))) := by
  apply AlgHom.ext
  intro x
  apply F.completion_ext
  intro k
  simp only [AlgHom.restrictScalars_apply, F.projection_liftₐ]

end RestrictScalars

end TauCeti.AlgFiltration
