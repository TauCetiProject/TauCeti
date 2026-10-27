/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Spectra.SymmetricSpectrum

/-!
# Structure maps of symmetric spectra

The sphere-module action of a symmetric spectrum restricts along the Day convolution units to
iterated structure maps `S^p ∧ X_q → X_(p+q)`. Naturality in both finite bijections gives their
full block-permutation equivariance. The module unit and associativity give the corresponding
unit and iteration laws, including the reindexing associator on finite sets.

A morphism of symmetric sequences is a spectral morphism exactly when it commutes with these
maps. The converse uses the universal property of Day convolution, so checking the displayed
levelwise squares suffices to construct a spectral morphism.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

open CategoryTheory MonoidalCategory
open scoped DayFunctor ExternalProduct

namespace TauCeti.SymmetricSpectrum

noncomputable section

/-- The iterated structure map `S^p ∧ X_q → X_(p+q)`, obtained by restricting the
sphere-module action along the Day convolution unit. -/
def structureMap (X : SymmetricSpectrum) (p q : FiniteBijection) :
    SymmetricSequence.sphere.functor.obj p ⊗ X.X.functor.obj q ⟶
      X.X.functor.obj (p ⊗ q) :=
  (DayFunctor.η SymmetricSequence.sphere X.X).app (p, q) ≫
    (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X)).natTrans.app (p ⊗ q)

/-- The structure maps restrict the sphere-module action along the Day convolution units. -/
lemma structureMap_def (X : SymmetricSpectrum) (p q : FiniteBijection) :
    X.structureMap p q = (DayFunctor.η SymmetricSequence.sphere X.X).app (p, q) ≫
      (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X)).natTrans.app (p ⊗ q) := (rfl)

/-- Equivariance of the iterated structure maps for both blocks. Taking `f` and `g` to be
arbitrary permutations gives the full `Σ_p × Σ_q` equivariance law. -/
@[reassoc]
lemma structureMap_naturality (X : SymmetricSpectrum) {p p' q q' : FiniteBijection}
    (f : p ⟶ p') (g : q ⟶ q') :
    (SymmetricSequence.sphere.functor.map f ⊗ₘ X.X.functor.map g) ≫ X.structureMap p' q' =
      X.structureMap p q ≫ X.X.functor.map (f ⊗ₘ g) := by
  let τ := DayFunctor.η SymmetricSequence.sphere X.X ≫
    Functor.whiskerLeft (tensor FiniteBijection)
      (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X)).natTrans
  simpa only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
    externalProductBifunctor_obj_map, Functor.comp_map, tensor_map, tensor_obj,
    tensorHom_def, structureMap] using
    τ.naturality (CategoryTheory.Prod.mkHom f g)

/-- Acting by the zero sphere, after its unit map, is the left unitor, with the canonical
zero-plus-level reindexing. -/
-- Simplify before the sphere unit normalizes to its smash-power presentation.
@[reassoc (attr := simp↓)]
lemma structureMap_unit (X : SymmetricSpectrum) (q : FiniteBijection) :
    Functor.LaxMonoidal.ε SymmetricSequence.sphere.functor ▷ X.X.functor.obj q ≫
        X.structureMap (𝟙_ FiniteBijection) q =
      (λ_ (X.X.functor.obj q)).hom ≫ X.X.functor.map (λ_ q).inv := by
  have h := congrArg (fun f : 𝟙_ SymmetricSequence ⊗ X.X ⟶ X.X ↦
    DayFunctor.ν FiniteBijection PointedSSet ▷ X.X.functor.obj q ≫
      (DayFunctor.η (𝟙_ SymmetricSequence) X.X).app (𝟙_ FiniteBijection, q) ≫
      f.natTrans.app (𝟙_ FiniteBijection ⊗ q))
    (ModObj.one_smul_self SymmetricSequence.sphere X.X)
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at h
  simpa [structureMap, ← comp_whiskerRight_assoc] using h

/-- Concatenating two sphere blocks before acting agrees with two successive structure maps.
The final reindexing records the associator `(p + q) + r ≅ p + (q + r)`. -/
@[reassoc]
lemma structureMap_assoc (X : SymmetricSpectrum) (p q r : FiniteBijection) :
    Functor.LaxMonoidal.μ SymmetricSequence.sphere.functor p q ▷ X.X.functor.obj r ≫
        X.structureMap (p ⊗ q) r =
      (α_ _ _ _).hom ≫ SymmetricSequence.sphere.functor.obj p ◁ X.structureMap q r ≫
        X.structureMap p (q ⊗ r) ≫ X.X.functor.map (α_ p q r).inv := by
  have h := congrArg
    (fun f : (SymmetricSequence.sphere ⊗ SymmetricSequence.sphere) ⊗ X.X ⟶ X.X ↦
      (DayFunctor.η SymmetricSequence.sphere SymmetricSequence.sphere).app (p, q) ▷
        X.X.functor.obj r ≫
      (DayFunctor.η (SymmetricSequence.sphere ⊗ SymmetricSequence.sphere) X.X).app
        (p ⊗ q, r) ≫ f.natTrans.app ((p ⊗ q) ⊗ r))
    (ModObj.mul_smul_self SymmetricSequence.sphere X.X)
  simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app, tensor_obj, Category.assoc,
    selfLeftAction_actionHomRight,
    DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc,
    DayFunctor.η_app_comp_whiskerLeft_natTrans_app_assoc,
    DayFunctor.η_app_whiskerRight_comp_η_app_comp_associator_hom_natTrans_app_assoc,
    ← comp_whiskerRight_assoc, DayFunctor.η_app_comp_mul_natTrans_app,
    whiskerLeft_comp, structureMap, NatTrans.naturality, NatTrans.naturality_assoc] using h

/-- Every spectral morphism commutes with all iterated structure maps. -/
@[reassoc (attr := simp)]
lemma structureMap_hom {X Y : SymmetricSpectrum} (f : X ⟶ Y) (p q : FiniteBijection) :
    X.structureMap p q ≫ f.hom.natTrans.app (p ⊗ q) =
      SymmetricSequence.sphere.functor.obj p ◁ f.hom.natTrans.app q ≫
        Y.structureMap p q := by
  have h := congrArg (fun g : SymmetricSequence.sphere ⊗ X.X ⟶ Y.X ↦
    (DayFunctor.η SymmetricSequence.sphere X.X).app (p, q) ≫ g.natTrans.app (p ⊗ q))
    (IsModHom.smul_hom (A := SymmetricSequence.sphere) (f := f.hom))
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at h
  simpa [structureMap] using h

/-- A morphism of symmetric sequences is a spectral morphism exactly when it commutes
with the iterated structure maps at every pair of levels. -/
lemma isModHom_iff {X Y : SymmetricSpectrum} (f : X.X ⟶ Y.X) :
    IsModHom SymmetricSequence.sphere f ↔
      ∀ p q, X.structureMap p q ≫ f.natTrans.app (p ⊗ q) =
        SymmetricSequence.sphere.functor.obj p ◁ f.natTrans.app q ≫ Y.structureMap p q := by
  constructor
  · intro h
    have := h
    exact structureMap_hom (⟨f⟩ : X ⟶ Y)
  · intro h
    constructor
    apply DayFunctor.tensor_hom_ext
    intro p q
    simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app, tensor_obj, Category.assoc,
      selfLeftAction_actionHomRight,
      DayFunctor.η_app_comp_whiskerLeft_natTrans_app_assoc, structureMap] using h p q

/-- Construct a spectral morphism from a morphism of symmetric sequences and its
compatibility with the structure maps. -/
def homMk {X Y : SymmetricSpectrum} (f : X.X ⟶ Y.X)
    (h : ∀ p q, X.structureMap p q ≫ f.natTrans.app (p ⊗ q) =
      SymmetricSequence.sphere.functor.obj p ◁ f.natTrans.app q ≫ Y.structureMap p q) :
    X ⟶ Y :=
  letI := (isModHom_iff f).mpr h
  ⟨f⟩

@[simp]
lemma homMk_hom {X Y : SymmetricSpectrum} (f : X.X ⟶ Y.X)
    (h : ∀ p q, X.structureMap p q ≫ f.natTrans.app (p ⊗ q) =
      SymmetricSequence.sphere.functor.obj p ◁ f.natTrans.app q ≫ Y.structureMap p q) :
    (homMk f h).hom = f := (rfl)

end

end TauCeti.SymmetricSpectrum
