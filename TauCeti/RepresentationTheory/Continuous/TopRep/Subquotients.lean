/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# Subrepresentations and quotients in `TopRep k G`

An invariant submodule of a continuous representation inherits its topology and action, and the
quotient by an invariant submodule carries the quotient topology and descended action. The
inclusion and projection have the expected universal factorization properties.
-/

public section

namespace TopRep

open CategoryTheory

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {G : Type*} [Monoid G] {X Y Z : TopRep R G}

/-- Restrict a continuous representation to an invariant submodule, with the induced topology. -/
abbrev subrepresentation (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : TopRep R G :=
  .of (X.ρ.subrepresentation W hW)

/-- The action on a subrepresentation is the ambient action with its membership proof. -/
@[simp]
theorem subrepresentation_ρ_apply (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (g : G)
    (x : subrepresentation X W hW) :
    (subrepresentation X W hW).ρ g x = ⟨X.ρ g x.1, hW g x.1 x.2⟩ := by
  apply Subtype.ext
  exact ContRepresentation.coe_subrepresentation_apply g x

/-- The inclusion of an invariant subrepresentation into its ambient representation. -/
noncomputable def subrepresentationι (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : subrepresentation X W hW ⟶ X :=
  ofHom (X.ρ.subrepresentationInclusion ⟨W, fun g x hx ↦ hW g x hx⟩)

/-- The inclusion of a subrepresentation is the subtype map. -/
@[simp]
theorem subrepresentationι_apply (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (x : subrepresentation X W hW) :
    (subrepresentationι X W hW).hom x = x.1 := by
  simpa [subrepresentationι] using
    ContRepresentation.subrepresentationInclusion_apply X.ρ
      ⟨W, fun g x hx ↦ hW g x hx⟩ x

/-- The inclusion of a subrepresentation is injective. -/
theorem subrepresentationι_injective (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    Function.Injective (subrepresentationι X W hW).hom :=
  fun x y h ↦ Subtype.ext <| calc
    x.1 = (subrepresentationι X W hW).hom x := (subrepresentationι_apply X W hW x).symm
    _ = (subrepresentationι X W hW).hom y := h
    _ = y.1 := subrepresentationι_apply X W hW y

/-- Factor a morphism into an invariant subrepresentation when its image is contained there. -/
def subrepresentationLift (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (f : Y ⟶ X)
    (hf : ∀ y, f.hom y ∈ W) : Y ⟶ subrepresentation X W hW :=
  ofHom
    { toContinuousLinearMap := f.hom.toContinuousLinearMap.codRestrict W hf
      isIntertwining' g := by
        ext y
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_codRestrict_apply,
          ContRepresentation.coe_subrepresentation_apply]
        exact hom_comm_apply f g y }

/-- The subrepresentation factorization evaluates by the original morphism. -/
@[simp]
theorem subrepresentationLift_apply (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (f : Y ⟶ X)
    (hf : ∀ y, f.hom y ∈ W) (y : Y) :
    (subrepresentationLift X W hW f hf).hom y = ⟨f.hom y, hf y⟩ := by
  rfl

/-- Composing the subrepresentation factorization with the inclusion recovers the morphism. -/
@[reassoc (attr := simp)]
theorem subrepresentationLift_comp_ι (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (f : Y ⟶ X)
    (hf : ∀ y, f.hom y ∈ W) :
    subrepresentationLift X W hW f hf ≫ subrepresentationι X W hW = f := by
  ext y
  -- `ext` exposes categorical composition through the representation morphism's `hom` field.
  change (subrepresentationι X W hW).hom ((subrepresentationLift X W hW f hf).hom y) =
    f.hom y
  rw [subrepresentationLift_apply, subrepresentationι_apply]

/-- A morphism into a subrepresentation is determined by its composite with the inclusion. -/
theorem subrepresentationLift_unique (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (f : Y ⟶ X)
    (hf : ∀ y, f.hom y ∈ W) (g : Y ⟶ subrepresentation X W hW)
    (hg : g ≫ subrepresentationι X W hW = f) :
  g = subrepresentationLift X W hW f hf := by
  ext y
  have hy := congrArg (fun q : Y ⟶ X => q y) hg
  rw [TopRep.comp_apply, subrepresentationι_apply] at hy
  -- The morphism equality is in the ambient representation, while the goal is a subtype value.
  change (g.hom y : X) = (subrepresentationLift X W hW f hf).hom y
  rw [subrepresentationLift_apply]
  exact hy

/-- Descend a continuous representation to the quotient by an invariant submodule. -/
abbrev quotient (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : TopRep R G :=
  .of (X.ρ.quotient W hW)

/-- The operators of a quotient representation are the descended operators. -/
@[simp]
theorem quotient_ρ (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    (quotient X W hW).ρ = X.ρ.quotient W hW :=
  rfl

/-- The projection from a representation to its quotient by an invariant submodule. -/
def quotientπ (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : X ⟶ quotient X W hW :=
  ofHom
    { toContinuousLinearMap := W.mkQL
      isIntertwining' g := by
        ext x
        simp [ContRepresentation.quotient_apply_mk] }

/-- The quotient projection sends a vector to its class. -/
@[simp]
theorem quotientπ_apply (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (x : X) :
    (quotientπ X W hW).hom x = Submodule.Quotient.mk x := by
  -- `ofHom` stores the quotient linear map as `mkQL`; expose that wrapper before evaluation.
  change W.mkQL x = _
  simp [Submodule.mkQL_apply, Submodule.mkQ_apply]

/-- The quotient projection is surjective. -/
theorem quotientπ_surjective (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    Function.Surjective (quotientπ X W hW).hom :=
  Submodule.mkQ_surjective W

/-- Factor a morphism through a quotient when it vanishes on the invariant submodule. -/
def quotientDesc (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (f : X ⟶ Y)
    (hf : ∀ x ∈ W, f.hom x = 0) : quotient X W hW ⟶ Y :=
  ofHom
    { toContinuousLinearMap := W.liftQL f.hom.toContinuousLinearMap
        (fun x hx ↦ LinearMap.mem_ker.mpr (hf x hx))
      isIntertwining' g := by
        ext x
        obtain ⟨x, rfl⟩ := W.mkQ_surjective x
        simp only [ContinuousLinearMap.comp_apply, Submodule.liftQL_apply]
        rw [Submodule.mkQ_apply, ContRepresentation.quotient_apply_mk,
          Submodule.liftQ_apply, Submodule.liftQ_apply]
        exact hom_comm_apply f g x }

/-- The quotient factorization evaluated on a class is the original morphism on a representative. -/
@[simp]
theorem quotientDesc_mk (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (f : X ⟶ Y)
    (hf : ∀ x ∈ W, f.hom x = 0) (x : X) :
    (quotientDesc X W hW f hf).hom (Submodule.Quotient.mk x) = f.hom x := by
  -- Unfold `ofHom` to expose the `liftQL` map and then its quotient representative.
  change W.liftQL f.hom.toContinuousLinearMap
    (fun x hx ↦ LinearMap.mem_ker.mpr (hf x hx)) (Submodule.Quotient.mk x) = _
  rw [Submodule.liftQL_apply, Submodule.liftQ_apply]
  rfl

/-- Composing the quotient projection with the quotient factorization recovers the morphism. -/
@[reassoc (attr := simp)]
theorem quotientπ_comp_quotientDesc (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (f : X ⟶ Y)
    (hf : ∀ x ∈ W, f.hom x = 0) :
    quotientπ X W hW ≫ quotientDesc X W hW f hf = f := by
  ext x
  -- `ext` leaves the bundled morphism application; evaluate composition explicitly.
  change (quotientDesc X W hW f hf).hom ((quotientπ X W hW).hom x) = f.hom x
  rw [quotientπ_apply, quotientDesc_mk]

/-- A morphism out of a quotient is determined by its composite with the projection. -/
theorem quotientDesc_unique (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (f : X ⟶ Y)
    (hf : ∀ x ∈ W, f.hom x = 0) (g : quotient X W hW ⟶ Y)
    (hg : quotientπ X W hW ≫ g = f) :
  g = quotientDesc X W hW f hf := by
  ext x
  obtain ⟨x, rfl⟩ := W.mkQ_surjective x
  have hx := congrArg (fun q : X ⟶ Y => q x) hg
  have hx' : g.hom (Submodule.Quotient.mk x) = f.hom x := by
    -- `congrArg` evaluates the composite through `Hom.hom`, so expose that composition first.
    change g.hom ((quotientπ X W hW).hom x) = f.hom x at hx
    rw [quotientπ_apply] at hx
    exact hx
  -- `mkQ_surjective` chooses a representative; unfold the RHS evaluation at that class.
  change g.hom (Submodule.Quotient.mk x) =
    (quotientDesc X W hW f hf).hom (Submodule.Quotient.mk x)
  rw [quotientDesc_mk]
  exact hx'

end TopRep
