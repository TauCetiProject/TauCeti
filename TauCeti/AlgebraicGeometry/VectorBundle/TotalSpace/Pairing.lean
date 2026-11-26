/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.FunctorOfPoints
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.Group
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.InternalHom
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.Module

/-!
# The evaluation pairing between a vector bundle and its dual

For a finite locally free sheaf `E` on a scheme `X`, let `𝕍(E) = Spec_X (Sym E^∨)` be its
geometric total space and `𝕍(E^∨)` that of its dual. This file constructs the evaluation pairing
`⟨ , ⟩ : 𝕍(E) ×_X 𝕍(E^∨) ⟶ 𝕍(𝒪_X)` over `X` (`totalSpacePairing`), with values in the total space
of the trivial line bundle, the additive group scheme `𝔾_{a,X}`. On points it is evaluation: for a
scheme `q : T ⟶ X` over `X`, a point `e` of `𝕍(E)` is a section `s : 𝒪_T ⟶ q^* E` and a point `e'`
of `𝕍(E^∨)` is a linear functional `φ : q^* E ⟶ 𝒪_T` (`totalSpaceHomEquiv`,
`totalSpaceDualHomEquiv`), and `⟨e, e'⟩` is the point of `𝕍(𝒪_X)` given by the function
`φ ∘ s = e'(e)` (`totalSpaceHomEquiv_lift_comp_totalSpacePairing`).

The pairing is bilinear for the group and module structures of the total spaces over the affine
line: it is additive in each variable (`lift_add_left_comp_totalSpacePairing`,
`lift_add_right_comp_totalSpacePairing`), vanishes when either argument lies on the zero section
(`lift_zero_left_comp_totalSpacePairing`, `lift_zero_right_comp_totalSpacePairing`) and commutes
with multiplication by functions in each variable (`lift_smul_left_comp_totalSpacePairing`,
`lift_smul_right_comp_totalSpacePairing`). It satisfies the transpose law
`⟨f e₁, e₂'⟩ = ⟨e₁, f^∨ e₂'⟩` for a morphism `f : E₁ ⟶ E₂`, on points
(`lift_comp_map_comp_totalSpacePairing`) and as an identity of morphisms
`𝕍(E₁) ×_X 𝕍(E₂^∨) ⟶ 𝕍(𝒪_X)` (`map_whiskerRight_comp_totalSpacePairing`).

The pairing defines the kernel `⟨ , ⟩^*ℒ_ψ` of the Fourier–Deligne transform on the vector
bundle `𝕍(E)`: the transform pulls a complex back along the projections of `𝕍(E) ×_X 𝕍(E^∨)`
and twists it by the pullback `⟨ , ⟩^*ℒ_ψ` along the pairing of an Artin–Schreier sheaf `ℒ_ψ`
on `𝔾_a`. The bilinearity and transpose laws are what make that kernel multiplicative and
compatible with linear maps.

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpacePairing`: the pairing `𝕍(E) ×_X 𝕍(E^∨) ⟶ 𝕍(𝒪_X)`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_lift_comp_totalSpacePairing`: on points it is
  evaluation of a linear functional at a section;
* `TauCeti.AlgebraicGeometry.lift_add_left_comp_totalSpacePairing`,
  `TauCeti.AlgebraicGeometry.lift_add_right_comp_totalSpacePairing`,
  `TauCeti.AlgebraicGeometry.lift_smul_left_comp_totalSpacePairing` and
  `TauCeti.AlgebraicGeometry.lift_smul_right_comp_totalSpacePairing`: bilinearity;
* `TauCeti.AlgebraicGeometry.map_whiskerRight_comp_totalSpacePairing`: the transpose law.

## References

* G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987), (1.2.1): the pairing and the Fourier kernel.
* N. Katz, G. Laumon, *Transformation de Fourier et majoration de sommes exponentielles*,
  Publ. Math. IHÉS 62 (1985), (2.1.1): the pairing, written `Σᵢ xᵢ x'ᵢ` in coordinates.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite AddMonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X)

/-- **The evaluation pairing of a vector bundle with its dual.** The morphism
`⟨ , ⟩ : 𝕍(E) ×_X 𝕍(E^∨) ⟶ 𝕍(𝒪_X)` over `X` sending a pair of points, a section `s` of `q^* E` and
a linear functional `φ` on `q^* E`, to the function `φ ∘ s`
(`totalSpaceHomEquiv_lift_comp_totalSpacePairing`). It is the point of `𝕍(𝒪_X)` over the product
given by the universal pair of points, the two projections. -/
def totalSpacePairing :
    (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E) ⊗
        (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E)) ⟶
      (MorphismProperty.Over.forget _ _ X).obj
        ((totalSpaceScheme X).obj (𝟙_ (FiniteLocallyFreeSheaf X))) :=
  (totalSpaceHomEquiv (𝟙_ _) _).symm
    (totalSpaceHomEquiv E _ (fst _ _) ≫ totalSpaceDualHomEquiv E _ (snd _ _) ≫
      (Scheme.Modules.pullbackObjUnitIso _).inv)

/-- **The pairing on points is evaluation.** For a scheme `q : T ⟶ X` over `X`, a point `e` of
`𝕍(E)` and a point `e'` of `𝕍(E^∨)`, the point `⟨e, e'⟩` of `𝕍(𝒪_X)` has section
`φ ∘ s : 𝒪_T ⟶ 𝒪_T ≅ q^* 𝒪_X`, where `s` is the section of `q^* E` of `e` and `φ` the linear
functional on `q^* E` of `e'`. Not a `simp` lemma: `simp` rewrites the unit object of finite
locally free sheaves in the type of the section, so the left-hand side is not in normal form. -/
theorem totalSpaceHomEquiv_lift_comp_totalSpacePairing {T : Over X}
    (e : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E))
    (e' : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) :
    totalSpaceHomEquiv (𝟙_ _) T (lift e e' ≫ totalSpacePairing E) =
      totalSpaceHomEquiv E T e ≫ totalSpaceDualHomEquiv E T e' ≫
        (Scheme.Modules.pullbackObjUnitIso T.hom).inv := by
  -- Both sides are natural in the test scheme: write `e` and `e'` as the projections precomposed
  -- with `lift e e'` and pull back the section of the pairing at the universal point.
  have h₁ := (congrArg (totalSpaceHomEquiv (dual E) T) (lift_snd e e').symm).trans
    (totalSpaceHomEquiv_comp (dual E) (lift e e') (snd _ _))
  have h₂ := (congrArg (relativeSpecSymmetricAlgebraPullbackHomEquiv
      ((toQuasicoherent X).obj (dual E)) T) (lift_fst e e').symm).trans
    (relativeSpecSymmetricAlgebraPullbackHomEquiv_comp _ (lift e e') (fst _ _))
  have hP : totalSpaceHomEquiv (𝟙_ _) _ (totalSpacePairing E) =
      totalSpaceHomEquiv (dual E) _ (snd _ _) ≫
        relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) _
          (fst _ _) ≫ (Scheme.Modules.pullbackObjUnitIso _).inv := by
    rw [totalSpacePairing, Equiv.apply_symm_apply]
    exact (totalSpaceHomEquiv_dual_comp_functional_assoc E _ _ _).symm
  rw [totalSpaceHomEquiv_comp (𝟙_ _) (lift e e') (totalSpacePairing E), hP,
    ← totalSpaceHomEquiv_dual_comp_functional_assoc, h₁, h₂]
  exact Scheme.Modules.pullbackObjUnitIso_inv_conj_comp _ _ _ _ _ _

/-- The pairing on points, through the section of `e'` and the linear functional of `e` on
`q^* E^∨`; this is the form used for the second variable. -/
private theorem totalSpaceHomEquiv_lift_comp_totalSpacePairing' {T : Over X}
    (e : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E))
    (e' : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) :
    totalSpaceHomEquiv (𝟙_ _) T (lift e e' ≫ totalSpacePairing E) =
      totalSpaceHomEquiv (dual E) T e' ≫
        relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T e ≫
          (Scheme.Modules.pullbackObjUnitIso T.hom).inv := by
  rw [totalSpaceHomEquiv_lift_comp_totalSpacePairing, totalSpaceHomEquiv_dual_comp_functional_assoc]

/-- **The pairing is additive in the first variable**: `⟨e₁ + e₂, e'⟩ = ⟨e₁, e'⟩ + ⟨e₂, e'⟩` for
the fibrewise additions of `𝕍(E)` and of `𝕍(𝒪_X)`. -/
theorem lift_add_left_comp_totalSpacePairing {T : Over X}
    (e₁ e₂ : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E))
    (e' : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) :
    lift (e₁ + e₂) e' ≫ totalSpacePairing E =
      lift e₁ e' ≫ totalSpacePairing E + lift e₂ e' ≫ totalSpacePairing E := by
  apply (totalSpaceHomAddEquiv (𝟙_ _) T).injective
  rw [map_add]
  simp only [totalSpaceHomAddEquiv_apply, totalSpaceHomEquiv_lift_comp_totalSpacePairing]
  rw [← totalSpaceHomAddEquiv_apply E, map_add, Preadditive.add_comp, totalSpaceHomAddEquiv_apply,
    totalSpaceHomAddEquiv_apply]

/-- **The pairing is additive in the second variable**: `⟨e, e'₁ + e'₂⟩ = ⟨e, e'₁⟩ + ⟨e, e'₂⟩`
for the fibrewise additions of `𝕍(E^∨)` and of `𝕍(𝒪_X)`. -/
theorem lift_add_right_comp_totalSpacePairing {T : Over X}
    (e : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E))
    (e'₁ e'₂ : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) :
    lift e (e'₁ + e'₂) ≫ totalSpacePairing E =
      lift e e'₁ ≫ totalSpacePairing E + lift e e'₂ ≫ totalSpacePairing E := by
  apply (totalSpaceHomAddEquiv (𝟙_ _) T).injective
  rw [map_add]
  simp only [totalSpaceHomAddEquiv_apply, totalSpaceHomEquiv_lift_comp_totalSpacePairing']
  rw [← totalSpaceHomAddEquiv_apply (dual E), map_add, Preadditive.add_comp,
    totalSpaceHomAddEquiv_apply, totalSpaceHomAddEquiv_apply]

/-- **The pairing is linear in the first variable**: `⟨a • e, e'⟩ = a • ⟨e, e'⟩` for a function
`a : T ⟶ 𝔸¹_X`, with the scalar actions of the affine line on `𝕍(E)` and on `𝕍(𝒪_X)`. -/
theorem lift_smul_left_comp_totalSpacePairing {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (e : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E))
    (e' : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) :
    lift (lift a e ≫ relativeSpecSymmetricAlgebraSMul ((toQuasicoherent X).obj (dual E))) e' ≫
        totalSpacePairing E =
      lift a (lift e e' ≫ totalSpacePairing E) ≫
        relativeSpecSymmetricAlgebraSMul ((toQuasicoherent X).obj (dual (𝟙_ _))) := by
  apply (totalSpaceHomEquiv (𝟙_ _) T).injective
  refine Eq.trans ?_
    (totalSpaceHomEquiv_lift_comp_smul (𝟙_ _) a (lift e e' ≫ totalSpacePairing E)).symm
  refine (totalSpaceHomEquiv_lift_comp_totalSpacePairing E _ e').trans ?_
  refine (congrArg (· ≫ _) (totalSpaceHomEquiv_lift_comp_smul E a e)).trans ?_
  rw [totalSpaceHomEquiv_lift_comp_totalSpacePairing]
  simp only [Category.assoc, Scheme.Modules.globalSectionsSmul_naturality]
  -- the two sides differ only in writing `𝒪_X` as the unit of finite locally free sheaves
  rfl

/-- **The pairing is linear in the second variable**: `⟨e, a • e'⟩ = a • ⟨e, e'⟩` for a function
`a : T ⟶ 𝔸¹_X`, with the scalar actions of the affine line on `𝕍(E^∨)` and on `𝕍(𝒪_X)`. -/
theorem lift_smul_right_comp_totalSpacePairing {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (e : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E))
    (e' : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) :
    lift e (lift a e' ≫
          relativeSpecSymmetricAlgebraSMul ((toQuasicoherent X).obj (dual (dual E)))) ≫
        totalSpacePairing E =
      lift a (lift e e' ≫ totalSpacePairing E) ≫
        relativeSpecSymmetricAlgebraSMul ((toQuasicoherent X).obj (dual (𝟙_ _))) := by
  apply (totalSpaceHomEquiv (𝟙_ _) T).injective
  refine Eq.trans ?_
    (totalSpaceHomEquiv_lift_comp_smul (𝟙_ _) a (lift e e' ≫ totalSpacePairing E)).symm
  refine (totalSpaceHomEquiv_lift_comp_totalSpacePairing' E e _).trans ?_
  refine (congrArg (· ≫ _) (totalSpaceHomEquiv_lift_comp_smul (dual E) a e')).trans ?_
  rw [totalSpaceHomEquiv_lift_comp_totalSpacePairing']
  simp only [Category.assoc, Scheme.Modules.globalSectionsSmul_naturality]
  -- the two sides differ only in writing `𝒪_X` as the unit of finite locally free sheaves
  rfl

/-- **The transpose law on points.** For a morphism `f : E₁ ⟶ E₂`, a point `e` of `𝕍(E₁)` and a
point `e'` of `𝕍(E₂^∨)`, `⟨f e, e'⟩ = ⟨e, f^∨ e'⟩`, where `f` and its dual `f^∨ : E₂^∨ ⟶ E₁^∨` act
on points through the induced maps of total spaces. -/
theorem lift_comp_map_comp_totalSpacePairing {E₁ E₂ : FiniteLocallyFreeSheaf X} (f : E₁ ⟶ E₂)
    {T : Over X}
    (e : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E₁))
    (e' : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E₂))) :
    lift (e ≫ (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map f)) e' ≫
        totalSpacePairing E₂ =
      lift e (e' ≫ (MorphismProperty.Over.forget _ _ X).map
          ((totalSpaceScheme X).map (dualFunctor.map f.op))) ≫ totalSpacePairing E₁ := by
  apply (totalSpaceHomEquiv (𝟙_ _) T).injective
  refine (totalSpaceHomEquiv_lift_comp_totalSpacePairing E₂ _ e').trans
    (Eq.trans ?_ (totalSpaceHomEquiv_lift_comp_totalSpacePairing E₁ e _).symm)
  rw [totalSpaceHomEquiv_comp_map]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (totalSpaceDualHomEquiv_comp_map f T e').symm)))

/-- **The transpose law.** For a morphism `f : E₁ ⟶ E₂`, the two morphisms
`𝕍(E₁) ×_X 𝕍(E₂^∨) ⟶ 𝕍(𝒪_X)` obtained by applying `f` to the first factor and pairing on `E₂`,
or applying the dual `f^∨ : E₂^∨ ⟶ E₁^∨` to the second factor and pairing on `E₁`, agree. -/
theorem map_whiskerRight_comp_totalSpacePairing {E₁ E₂ : FiniteLocallyFreeSheaf X}
    (f : E₁ ⟶ E₂) :
    (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map f) ▷
        (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E₂)) ≫
        totalSpacePairing E₂ =
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E₁) ◁
        (MorphismProperty.Over.forget _ _ X).map
          ((totalSpaceScheme X).map (dualFunctor.map f.op)) ≫ totalSpacePairing E₁ := by
  have h := lift_comp_map_comp_totalSpacePairing f (fst _ _) (snd _ _)
  rwa [← lift_whiskerRight, ← lift_whiskerLeft, lift_fst_snd, Category.id_comp,
    Category.id_comp] at h

/-- The pairing vanishes on the zero section of `𝕍(E)`: `⟨0, e'⟩ = 0`. -/
@[simp]
theorem lift_zero_left_comp_totalSpacePairing {T : Over X}
    (e' : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) :
    lift 0 e' ≫ totalSpacePairing E = 0 := by
  apply (totalSpaceHomAddEquiv (𝟙_ _) T).injective
  rw [map_zero, totalSpaceHomAddEquiv_apply, totalSpaceHomEquiv_lift_comp_totalSpacePairing,
    ← totalSpaceHomAddEquiv_apply E, map_zero, Limits.zero_comp]

/-- The pairing vanishes on the zero section of `𝕍(E^∨)`: `⟨e, 0⟩ = 0`. -/
@[simp]
theorem lift_zero_right_comp_totalSpacePairing {T : Over X}
    (e : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    lift e 0 ≫ totalSpacePairing E = 0 := by
  apply (totalSpaceHomAddEquiv (𝟙_ _) T).injective
  rw [map_zero, totalSpaceHomAddEquiv_apply, totalSpaceHomEquiv_lift_comp_totalSpacePairing',
    ← totalSpaceHomAddEquiv_apply (dual E), map_zero, Limits.zero_comp]

end

end TauCeti.AlgebraicGeometry
