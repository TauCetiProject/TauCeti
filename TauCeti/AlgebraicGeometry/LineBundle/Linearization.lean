/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.PullHom
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.CategoryTheory.Sites.Descent.Linearization

/-!
# Linearized invertible sheaves

Let `S` be a scheme, `G` a monoid object of `S`-schemes, for instance a group scheme over `S`,
acting on an `S`-scheme `X` by `γ : G ×_S X ⟶ X`. A `G`-linearization of an `𝒪_X`-module `M` is
an isomorphism `γ^* M ≅ pr₂^* M` over `G ×_S X` satisfying the cocycle and unit conditions
(Mumford–Fogarty–Kirwan, Definition 1.6). This file specializes the linearized objects
`CategoryTheory.Pseudofunctor.LinearizedObject` of a pseudofunctor to the pseudofunctor of modules
on `S`-schemes:

* `TauCeti.AlgebraicGeometry.LinearizedModule G X`: `G`-linearized `𝒪_X`-modules;
* `TauCeti.AlgebraicGeometry.LinearizedInvertibleSheaf G X`: those whose underlying module is
  invertible, with the forgetful functor `LinearizedInvertibleSheaf.forget` to invertible sheaves
  on `X` and the pullback `LinearizedInvertibleSheaf.pullFunctor` along `G`-equivariant morphisms;
* `LinearizedInvertibleSheaf.trivial G X`: the structure sheaf with its trivial linearization, the
  pullback of `𝒪_S` (`LinearizedInvertibleSheaf.forgetObjTrivialIso`).

A morphism of linearized sheaves must respect the linearizations, so the trivial linearized sheaf
has fewer endomorphisms than `𝒪_X`: they are the multiplications by the `G`-invariant global
functions, those `r` with `γ^♯ r = pr₂^♯ r` (`LinearizedInvertibleSheaf.endTrivialMulEquiv`), and
its automorphisms are the multiplications by the invariant units
(`LinearizedInvertibleSheaf.autTrivialMulEquiv`).

## References

* D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, 3rd ed., Chapter 1, §3,
  Definition 1.6.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Equivariant quasi-coherent sheaves*.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Pseudofunctor

variable {S : Scheme.{u}} (G X : Over S) [MonObj G] [ModObj G X]

/-- `G`-linearized `𝒪_X`-modules, for a monoid object `G` of `S`-schemes acting on an `S`-scheme
`X`. -/
abbrev LinearizedModule : Type _ :=
  (Descent.modulesPseudofunctor.over S).LinearizedObject G X

namespace LinearizedModule

/-- A linearized module is invertible when its underlying `𝒪_X`-module is. -/
def isInvertible : ObjectProperty (LinearizedModule G X) :=
  (SheafOfModules.isInvertible X.left).inverseImage (LinearizedObject.forget _ G X)

end LinearizedModule

/-- `G`-linearized invertible sheaves on `X`. -/
abbrev LinearizedInvertibleSheaf : Type _ :=
  (LinearizedModule.isInvertible G X).FullSubcategory

namespace LinearizedInvertibleSheaf

instance (D : LinearizedInvertibleSheaf G X) : SheafOfModules.isInvertible X.left D.obj.obj :=
  D.property

/-- The invertible sheaf underlying a linearized invertible sheaf. -/
def forget : LinearizedInvertibleSheaf G X ⥤ InvertibleSheaf X.left :=
  ObjectProperty.lift _ ((LinearizedModule.isInvertible G X).ι ⋙
    LinearizedObject.forget _ G X) fun D ↦ D.property

/-- The structure sheaf with its trivial linearization: the pullback of `𝒪_S`. -/
def trivial : LinearizedInvertibleSheaf G X :=
  ⟨LinearizedObject.ofObj _ G X (InvertibleSheaf.trivial S).obj,
    SheafOfModules.isInvertible_pullback (hM := (InvertibleSheaf.trivial S).property) _ _⟩

/-- The invertible sheaf underlying the trivial linearized sheaf is the structure sheaf. -/
def forgetObjTrivialIso : (forget G X).obj (trivial G X) ≅ InvertibleSheaf.trivial X.left :=
  ObjectProperty.isoMk _ (InvertibleSheaf.pullbackTrivialObjIso (toUnit X).left)

/-- The global functions on `X` invariant under `G`: those with the same pullbacks along the
action and the projection `G ⊗ X ⟶ X`. Membership is `RingHom.mem_eqLocus`. -/
abbrev invariantGlobalSections : Subring Γ(X.left, ⊤) :=
  γ[G,X].left.appTop.hom.eqLocus (snd G X).left.appTop.hom

/-- An endomorphism `α` of the structure sheaf, multiplication by a global function `r`, is
compatible with the trivial linearization exactly when `r` is `G`-invariant. -/
lemma trivial_comm_iff_mem_invariantGlobalSections
    (α : (trivial G X).obj.obj ⟶ (trivial G X).obj.obj) (r : Γ(X.left, ⊤))
    (hα : α = ((forget G X).obj (trivial G X)).obj.globalSectionsSmul r) :
    ((Descent.modulesPseudofunctor.over S).map γ[G,X].op.toLoc).toFunctor.map α ≫
        (trivial G X).obj.iso.hom =
      (trivial G X).obj.iso.hom ≫
        ((Descent.modulesPseudofunctor.over S).map (snd G X).op.toLoc).toFunctor.map α ↔
    r ∈ invariantGlobalSections G X := by
  subst hα
  have : SheafOfModules.isInvertible (G ⊗ X).left
      ((Scheme.Modules.pullback (toUnit (G ⊗ X)).left).obj (InvertibleSheaf.trivial S).obj) :=
    SheafOfModules.isInvertible_pullback (hM := (InvertibleSheaf.trivial S).property) _ _
  refine (LinearizedObject.ofObj_comm_iff _ _ _ _).trans ?_
  refine (Eq.congr (LocallyDiscreteOpToCat.pullHom_toPseudofunctor_comp _ _ _ _ _ _ _ _)
    (LocallyDiscreteOpToCat.pullHom_toPseudofunctor_comp _ _ _ _ _ _ _ _)).trans ?_
  refine (Eq.congr (Scheme.Modules.pullHom_globalSectionsSmul _ _ _ _ _)
    (Scheme.Modules.pullHom_globalSectionsSmul _ _ _ _ _)).trans ?_
  exact (Scheme.Modules.globalSectionsSmul_injective _).eq_iff

/-- **Endomorphisms of the trivial linearized sheaf.** They are the multiplications by the
`G`-invariant global functions on `X`. -/
def endTrivialMulEquiv : End (trivial G X) ≃* invariantGlobalSections G X where
  toFun φ := ⟨(Scheme.Modules.globalSectionsActionRingEquiv
      ((forget G X).obj (trivial G X)).obj).symm (End.of φ.asHom.hom.hom),
      (trivial_comm_iff_mem_invariantGlobalSections G X _ _
        (Scheme.Modules.globalSectionsSmul_globalSectionsActionRingEquiv_symm
          ((forget G X).obj (trivial G X)).obj φ.asHom.hom.hom).symm).1 φ.asHom.hom.comm⟩
  invFun r := End.of (ObjectProperty.homMk
    ⟨((forget G X).obj (trivial G X)).obj.globalSectionsSmul r,
      (trivial_comm_iff_mem_invariantGlobalSections G X _ r rfl).2 r.property⟩)
  left_inv φ := by
    ext : 1
    apply ObjectProperty.hom_ext
    apply LinearizedObject.hom_ext
    exact Scheme.Modules.globalSectionsSmul_globalSectionsActionRingEquiv_symm
      ((forget G X).obj (trivial G X)).obj φ.asHom.hom.hom
  right_inv r := by
    ext : 1
    simp
  map_mul' φ ψ := Subtype.ext (by
    rw [Subring.coe_mul, ← map_mul (Scheme.Modules.globalSectionsActionRingEquiv
      ((forget G X).obj (trivial G X)).obj).symm]
    rfl)

@[simp]
lemma globalSectionsSmul_endTrivialMulEquiv (φ : End (trivial G X)) :
    ((forget G X).obj (trivial G X)).obj.globalSectionsSmul (endTrivialMulEquiv G X φ) =
      φ.asHom.hom.hom :=
  Scheme.Modules.globalSectionsSmul_globalSectionsActionRingEquiv_symm
    ((forget G X).obj (trivial G X)).obj φ.asHom.hom.hom

/-- **Automorphisms of the trivial linearized sheaf.** They are the multiplications by the
`G`-invariant units of `Γ(X, 𝒪_X)`. -/
def autTrivialMulEquiv : Aut (trivial G X) ≃* (invariantGlobalSections G X)ˣ :=
  (Aut.unitsEndEquivAut _).symm.trans (Units.mapEquiv (endTrivialMulEquiv G X))

section Pull

variable {G X} {Z : Over S} [ModObj G Z] (f : X ⟶ Z) [IsModHom G f]

/-- Pullback of linearized invertible sheaves along a `G`-equivariant morphism of `S`-schemes. -/
def pullFunctor : LinearizedInvertibleSheaf G Z ⥤ LinearizedInvertibleSheaf G X :=
  ObjectProperty.lift _ ((LinearizedModule.isInvertible G Z).ι ⋙
    LinearizedObject.pullFunctor _ G f) fun D ↦
      SheafOfModules.isInvertible_pullback f.left D.obj.obj

/-- Pulling back a linearized invertible sheaf pulls back its underlying invertible sheaf. -/
def forgetPullFunctorIso :
    pullFunctor f ⋙ forget G X ≅ forget G Z ⋙ InvertibleSheaf.pullback f.left :=
  Iso.refl _

end Pull

end LinearizedInvertibleSheaf

end TauCeti.AlgebraicGeometry
