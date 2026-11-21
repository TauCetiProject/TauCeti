/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Points
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Scalar
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LinearPoints

/-!
# Recognizing linear morphisms of affine linear spectra

For arbitrary modules `M` and `N` over a commutative ring `R`, a scheme morphism
`Spec (Sym M) ⟶ Spec (Sym N)` over `Spec R` is induced by a unique linear map `N → M`
if its action on points commutes with every scalar in every commutative test algebra.
In particular, this condition forces additivity by applying
`TauCeti.SymmetricAlgebra.linearPoints_add_of_smul` to `specSymmetricAlgebraPointsMap`;
no characteristic or finiteness hypothesis is needed. Testing only the scalars of `R`
would not suffice.

`specSymmetricAlgebraHomEquiv` (in `Points.lean`) identifies actual affine-scheme points with
linear functionals, naturally in the test algebra. The recognition theorem transports the
algebraic result `TauCeti.SymmetricAlgebra.existsUnique_linearMap_of_linearPoints_smul` along this
identification.

The same holds for the relative spectra `𝕍(F) = Spec_{Spec R} (Sym F)` of quasicoherent sheaves on
`Spec R`, with the scalar condition replaced by the module structure of `𝕍(F)` over the affine line
`𝔸¹_{Spec R}` (`modObjRelativeSpecSymmetricAlgebra`): a morphism `𝕍(F) ⟶ 𝕍(F')` over `Spec R`
commuting with the actions of `𝔸¹_{Spec R}` is the relative spectrum of `Sym a` for a unique
`a : F' ⟶ F` (`existsUnique_relativeSpec_map_of_isModHom`). Under the comparison
`Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` (`relativeSpecSymmetricAlgebraTildeIsoSpec`), points over
`Spec S` become `R`-linear maps `M → S` (the comparison lemmas of `Points.lean`) and the action of
`c ∈ S` becomes multiplication by `c`
(`specSymmetricAlgebraHomEquiv_smul_comp_relativeSpecSymmetricAlgebraTildeIsoSpec_hom` in
`Scalar.lean`), so this follows from the affine criterion above.

The morphisms `Spec_X (Sym a)` are the underlying morphisms of the morphisms of linear schemes
`(linearSpec X).obj (op F) ⟶ (linearSpec X).obj (op F')`, that is of the morphisms preserving
the gradings of the coordinate algebras, since `linearSpec X` is full (`linearSpecEquiv`). Over
`Spec R` the results here therefore identify the morphisms commuting with scalar multiplication
with the grading-preserving ones. They assume an affine base, as they are deduced from the
comparison with `Spec (Sym_R M)`.

## Main declarations

* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraPointsMap`: the action of a morphism
  `Spec (Sym_R M) ⟶ Spec (Sym_R N)` on linear points;
* `TauCeti.AlgebraicGeometry.existsUnique_specSymmetricAlgebraMap_of_smul`: a morphism
  `Spec (Sym_R M) ⟶ Spec (Sym_R N)` commuting with scalars on points is induced by a unique linear
  map `N → M`;
* `specSymmetricAlgebraPointsMap_app_smul_of_isModHom`: a morphism commuting with the actions of
  the affine line commutes with scalars on points;
* `TauCeti.AlgebraicGeometry.existsUnique_relativeSpec_map_tilde_of_isModHom` and
  `TauCeti.AlgebraicGeometry.existsUnique_relativeSpec_map_of_isModHom`: a morphism
  `Spec_{Spec R} (Sym F) ⟶ Spec_{Spec R} (Sym F')` commuting with the actions of the affine line is
  the relative spectrum of `Sym a` for a unique `a : F' ⟶ F`, and
  `TauCeti.AlgebraicGeometry.isModHom_iff_exists_relativeSpec_map` states the equivalence.

## References

* The Stacks Project, Tag 01M1 (vector bundles).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}} {M : Type u} [AddCommMonoid M] [Module R M]
  {N : Type u} [AddCommMonoid N] [Module R N]

/-- A morphism of affine linear spectra induces a natural transformation of linear point
functors, without any assumption that the morphism itself is linear. -/
def specSymmetricAlgebraPointsMap
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N)))) :
    SymmetricAlgebra.linearPoints R M ⟶ SymmetricAlgebra.linearPoints R N where
  app S := TypeCat.ofHom fun g ↦ specSymmetricAlgebraHomEquiv N S
    ((specSymmetricAlgebraHomEquiv M S).symm g ≫ ψ)
  naturality S T h := by
    apply ConcreteCategory.hom_ext
    intro g
    simp only [CategoryTheory.comp_apply, TypeCat.ofHom_apply,
      specSymmetricAlgebraHomEquiv_symm_comp,
      Category.assoc, specSymmetricAlgebraHomEquiv_map_comp]

/-- The induced transformation is computed by composing the corresponding scheme point. -/
@[simp]
theorem specSymmetricAlgebraPointsMap_app
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N))))
    (S : CommAlgCat.{u} R) (g : M →ₗ[R] S) :
    (specSymmetricAlgebraPointsMap ψ).app S g = specSymmetricAlgebraHomEquiv N S
      ((specSymmetricAlgebraHomEquiv M S).symm g ≫ ψ) :=
  (rfl)

/-- Scheme morphisms are determined by their action on affine linear-spectrum points. -/
theorem specSymmetricAlgebraPointsMap_injective :
    Function.Injective (specSymmetricAlgebraPointsMap (R := R) (M := M) (N := N)) := by
  intro ψ χ h
  let S := CommAlgCat.of R (SymmetricAlgebra R M)
  let p := specSymmetricAlgebraHomEquiv M S (𝟙 _)
  have hp : (specSymmetricAlgebraPointsMap ψ).app S p =
      (specSymmetricAlgebraPointsMap χ).app S p :=
    congrArg (fun τ : SymmetricAlgebra.linearPoints R M ⟶
      SymmetricAlgebra.linearPoints R N ↦ τ.app S p) h
  rw [specSymmetricAlgebraPointsMap_app, specSymmetricAlgebraPointsMap_app] at hp
  have hp' := (specSymmetricAlgebraHomEquiv N S).injective hp
  simpa only [p, Equiv.symm_apply_apply, Category.id_comp] using hp'

/-- The transformation induced by the spectrum of `Sym f` is precomposition with `f`. -/
@[simp]
theorem specSymmetricAlgebraPointsMap_specSymmetricAlgebraMap (f : N →ₗ[R] M) :
    specSymmetricAlgebraPointsMap (specSymmetricAlgebraMap f) =
      SymmetricAlgebra.linearPointsMap R f := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro g
  simp only [specSymmetricAlgebraPointsMap_app (R := R),
    specSymmetricAlgebraHomEquiv_comp_specSymmetricAlgebraMap (R := R),
    Equiv.apply_symm_apply, SymmetricAlgebra.linearPointsMap_app_apply R f]

/-- A scheme morphism of affine linear spectra whose action on points commutes with all
test-algebra scalars is induced by a unique linear map. In particular this criterion works
over finite and nonreduced rings, with arbitrary modules. -/
theorem existsUnique_specSymmetricAlgebraMap_of_smul
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N))))
    (hψ : ∀ (S : CommAlgCat.{u} R) (c : S) (g : M →ₗ[R] S),
      (specSymmetricAlgebraPointsMap ψ).app S (c • g) =
        c • ((specSymmetricAlgebraPointsMap ψ).app S g : N →ₗ[R] S)) :
    ∃! f : N →ₗ[R] M, ψ = specSymmetricAlgebraMap f := by
  obtain ⟨f, hf, hu⟩ := SymmetricAlgebra.existsUnique_linearMap_of_linearPoints_smul
    R (specSymmetricAlgebraPointsMap ψ) hψ
  refine ⟨f, specSymmetricAlgebraPointsMap_injective (hf.trans
    (specSymmetricAlgebraPointsMap_specSymmetricAlgebraMap f).symm), ?_⟩
  intro g hg
  apply hu
  rw [hg, specSymmetricAlgebraPointsMap_specSymmetricAlgebraMap]

/-- The scalar-equivariance criterion is equivalent to being induced by a linear map. -/
theorem specSymmetricAlgebraPointsMap_smul_iff_exists_specSymmetricAlgebraMap
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N)))) :
    (∀ (S : CommAlgCat.{u} R) (c : S) (g : M →ₗ[R] S),
      (specSymmetricAlgebraPointsMap ψ).app S (c • g) =
        c • ((specSymmetricAlgebraPointsMap ψ).app S g : N →ₗ[R] S)) ↔
      ∃ f : N →ₗ[R] M, ψ = specSymmetricAlgebraMap f := by
  constructor
  · intro h
    exact (existsUnique_specSymmetricAlgebraMap_of_smul ψ h).exists
  · rintro ⟨f, rfl⟩ S c g
    rw [specSymmetricAlgebraPointsMap_specSymmetricAlgebraMap]
    exact SymmetricAlgebra.linearPointsMap_app_smul R f S c g

end

/-! ### Relative spectra over an affine base -/

noncomputable section

open MonoidalCategory CartesianMonoidalCategory

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- **Module morphisms act linearly on points.** Under `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)`, a
morphism `Spec_{Spec R} (Sym M~) ⟶ Spec_{Spec R} (Sym N~)` over `Spec R` commuting with the actions
of the affine line becomes a morphism `Spec (Sym_R M) ⟶ Spec (Sym_R N)` whose action on points
commutes with every scalar of every commutative test algebra. -/
theorem specSymmetricAlgebraPointsMap_app_smul_of_isModHom
    (g : (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M)))) ⟶
      (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj N)))))
    [IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) g]
    (S : CommAlgCat.{u} R) (c : S) (φ : M →ₗ[R] S) :
    (specSymmetricAlgebraPointsMap ((relativeSpecSymmetricAlgebraTildeIsoSpec M).inv ≫ g ≫
        (relativeSpecSymmetricAlgebraTildeIsoSpec N).hom)).app S (c • φ) =
      c • ((specSymmetricAlgebraPointsMap ((relativeSpecSymmetricAlgebraTildeIsoSpec M).inv ≫ g ≫
        (relativeSpecSymmetricAlgebraTildeIsoSpec N).hom)).app S φ : N →ₗ[R] S) := by
  let eM := relativeSpecSymmetricAlgebraTildeIsoSpec M
  let eN := relativeSpecSymmetricAlgebraTildeIsoSpec N
  let ψ := eM.inv ≫ g ≫ eN.hom
  -- `φ` is the point `t ≫ eM.hom` and `c` the function `a` on `Spec S`, so `c • φ` is the point
  -- `(a • t) ≫ eM.hom`; then `g` commutes with `a •` because it is a module morphism
  let t := (specSymmetricAlgebraHomEquiv M S).symm φ ≫ eM.inv
  let a := (AffineSpace.homAsOverEquiv ((algSpec R).obj (op S))).symm
    fun _ : PUnit.{u + 1} ↦ (Scheme.ΓSpecIso (CommRingCat.of S)).inv c
  have ha : (Scheme.ΓSpecIso (CommRingCat.of S)).hom
      (AffineSpace.homAsOverEquiv ((algSpec R).obj (op S)) a .unit) = c :=
    (congrArg _ (congrFun (Equiv.apply_symm_apply _ _) PUnit.unit)).trans
      (Iso.inv_hom_id_apply _ _)
  -- composites are combined as terms: neither `rw` nor `simp` can reassociate across the
  -- `MorphismProperty.Over` wrapper and the cartesian monoidal structure
  have ht : t ≫ eM.hom = (specSymmetricAlgebraHomEquiv M S).symm φ := (eM.comp_inv_eq.1 rfl).symm
  have hφ : (specSymmetricAlgebraHomEquiv M S).symm (c • φ) = (a • t) ≫ eM.hom :=
    (Equiv.symm_apply_eq _).2
      ((specSymmetricAlgebraHomEquiv_smul_comp_relativeSpecSymmetricAlgebraTildeIsoSpec_hom
        M S a t).trans
          (congrArg₂ (· • ·) ha ((congrArg _ ht).trans (Equiv.apply_symm_apply _ _)))).symm
  have hsmul : ((a • t) ≫ eM.hom) ≫ ψ = (a • (t ≫ g)) ≫ eN.hom :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (eM.hom_inv_id_assoc _)).trans
      (IsModHom.map_smul_assoc g a t _))
  calc (specSymmetricAlgebraPointsMap ψ).app S (c • φ)
      = specSymmetricAlgebraHomEquiv N S ((a • (t ≫ g)) ≫ eN.hom) :=
        (congrArg (fun x ↦ specSymmetricAlgebraHomEquiv N S (x ≫ ψ)) hφ).trans
          (congrArg _ hsmul)
    _ = c • specSymmetricAlgebraHomEquiv N S ((t ≫ g) ≫ eN.hom) :=
        (specSymmetricAlgebraHomEquiv_smul_comp_relativeSpecSymmetricAlgebraTildeIsoSpec_hom
          N S a (t ≫ g)).trans (congrArg (· • _) ha)
    _ = c • ((specSymmetricAlgebraPointsMap ψ).app S φ : N →ₗ[R] S) :=
        congrArg (fun x ↦ c • specSymmetricAlgebraHomEquiv N S x)
          ((Category.assoc _ _ _).trans (Category.assoc _ _ _))

/-- **Linear morphisms of linear spectra over `Spec R`.** For `R`-modules `M` and `N`, a morphism
`Spec_{Spec R} (Sym M~) ⟶ Spec_{Spec R} (Sym N~)` over `Spec R` that commutes with the actions of
the affine line `𝔸¹_{Spec R}` is the relative spectrum of `Sym f~` for a unique linear map
`f : N ⟶ M`. -/
theorem existsUnique_relativeSpec_map_tilde_of_isModHom
    (g : (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M)))) ⟶
      (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj N)))))
    [IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) g] :
    ∃! f : N ⟶ M, g = (MorphismProperty.Over.forget _ _ (Spec R)).map ((relativeSpec (Spec R)).map
      ((symmetricAlgebra (Spec R)).map ((tildeEquiv (R := R)).functor.map f)).op) := by
  -- `g` becomes a morphism `ψ : Spec (Sym_R M) ⟶ Spec (Sym_R N)` commuting with scalars on points
  -- (`specSymmetricAlgebraPointsMap_app_smul_of_isModHom`), to which the affine criterion
  -- `existsUnique_specSymmetricAlgebraMap_of_smul` applies.
  let eM := relativeSpecSymmetricAlgebraTildeIsoSpec M
  let eN := relativeSpecSymmetricAlgebraTildeIsoSpec N
  let ψ := eM.inv ≫ g ≫ eN.hom
  obtain ⟨f, hf, hu⟩ := existsUnique_specSymmetricAlgebraMap_of_smul ψ
    (specSymmetricAlgebraPointsMap_app_smul_of_isModHom g)
  have hm (f' : N ⟶ M) :
      eM.inv ≫ (MorphismProperty.Over.forget _ _ (Spec R)).map ((relativeSpec (Spec R)).map
        ((symmetricAlgebra (Spec R)).map ((tildeEquiv (R := R)).functor.map f')).op) ≫ eN.hom =
      specSymmetricAlgebraMap f'.hom :=
    (Iso.inv_comp_eq eM).2 (relativeSpec_map_comp_relativeSpecSymmetricAlgebraTildeIsoSpec_hom f')
  refine ⟨ModuleCat.ofHom f, ?_, fun f' hf' ↦ ModuleCat.hom_ext (hu f'.hom ?_)⟩
  · have h := (hf.trans (hm (ModuleCat.ofHom f)).symm)
    exact (cancel_epi eM.inv).1 ((cancel_mono eN.hom).1
      ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)))
  · exact (congrArg (fun x ↦ eM.inv ≫ x ≫ eN.hom) hf').trans (hm f')

/-- **Linear morphisms of linear spectra over `Spec R`.** For quasicoherent sheaves `F` and `F'` on
`Spec R`, a morphism `Spec_{Spec R} (Sym F) ⟶ Spec_{Spec R} (Sym F')` over `Spec R` that commutes
with the actions of the affine line `𝔸¹_{Spec R}` is the relative spectrum of `Sym a` for a unique
`a : F' ⟶ F`. -/
theorem existsUnique_relativeSpec_map_of_isModHom {F F' : QuasicoherentSheaf (Spec R)}
    (g : (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj F))) ⟶
      (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj F'))))
    [IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) g] :
    ∃! a : F' ⟶ F, g = (MorphismProperty.Over.forget _ _ (Spec R)).map
      ((relativeSpec (Spec R)).map ((symmetricAlgebra (Spec R)).map a).op) := by
  -- transport `g` along `M~ ≅ F` and `N~ ≅ F'`, for `M` and `N` the global sections
  let e : (tildeEquiv (R := R)).functor.obj ((tildeEquiv (R := R)).inverse.obj F) ≅ F :=
    (tildeEquiv (R := R)).counitIso.app F
  let e' : (tildeEquiv (R := R)).functor.obj ((tildeEquiv (R := R)).inverse.obj F') ≅ F' :=
    (tildeEquiv (R := R)).counitIso.app F'
  let m {G G' : QuasicoherentSheaf (Spec R)} (a : G' ⟶ G) :=
    (MorphismProperty.Over.forget _ _ (Spec R)).map
      ((relativeSpec (Spec R)).map ((symmetricAlgebra (Spec R)).map a).op)
  have hm {G G' G'' : QuasicoherentSheaf (Spec R)} (a : G'' ⟶ G') (b : G' ⟶ G) :
      m (a ≫ b) = m b ≫ m a := by
    simp only [m, Functor.map_comp, op_comp]
  have hm₁ (G : QuasicoherentSheaf (Spec R)) : m (𝟙 G) = 𝟙 _ := by
    simp only [m, CategoryTheory.Functor.map_id, op_id]
  have : IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) (m e.inv) :=
    isModHom_relativeSpec_map e.inv
  have : IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) (m e'.hom) :=
    isModHom_relativeSpec_map e'.hom
  obtain ⟨f, hf, hu⟩ := existsUnique_relativeSpec_map_tilde_of_isModHom (m e.inv ≫ g ≫ m e'.hom)
  refine ⟨e'.inv ≫ (tildeEquiv (R := R)).functor.map f ≫ e.hom, ?_, fun a ha ↦ ?_⟩
  · have h₁ : m e.hom ≫ m e.inv = 𝟙 _ :=
      (hm e.inv e.hom).symm.trans ((congrArg m e.inv_hom_id).trans (hm₁ F))
    have h₂ : m e'.hom ≫ m e'.inv = 𝟙 _ :=
      (hm e'.inv e'.hom).symm.trans ((congrArg m e'.inv_hom_id).trans (hm₁ F'))
    calc g = (m e.hom ≫ m e.inv) ≫ g ≫ m e'.hom ≫ m e'.inv := by
          rw [h₁, h₂, Category.id_comp, Category.comp_id]
      _ = m e.hom ≫ (m e.inv ≫ g ≫ m e'.hom) ≫ m e'.inv := by
          simp only [Category.assoc]
      _ = m e.hom ≫ m ((tildeEquiv (R := R)).functor.map f) ≫ m e'.inv :=
          congrArg (fun x ↦ m e.hom ≫ x ≫ m e'.inv) hf
      _ = _ := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m e'.inv)
          (hm _ e.hom).symm).trans (hm e'.inv _).symm)
  · let b := e'.hom ≫ a ≫ e.inv
    have hb := (tildeEquiv (R := R)).functor.map_preimage b
    have k₁ : m e.inv ≫ g ≫ m e'.hom = m e.inv ≫ m a ≫ m e'.hom :=
      congrArg (fun x ↦ m e.inv ≫ x ≫ m e'.hom) ha
    have k₂ : m b = m e.inv ≫ m a ≫ m e'.hom := by
      simp only [b, hm, Category.assoc]
    have k₃ : m ((tildeEquiv (R := R)).functor.map ((tildeEquiv (R := R)).functor.preimage b)) =
        m b :=
      congrArg m hb
    have hf₀ := hu ((tildeEquiv (R := R)).functor.preimage b) (k₁.trans (k₂.symm.trans k₃.symm))
    rw [hf₀] at hb
    simp [hb, b]

/-- Over `Spec R`, a morphism `Spec_{Spec R} (Sym F) ⟶ Spec_{Spec R} (Sym F')` commutes with the
actions of the affine line exactly when it is the relative spectrum of `Sym a` for some
`a : F' ⟶ F`. -/
theorem isModHom_iff_exists_relativeSpec_map {F F' : QuasicoherentSheaf (Spec R)}
    (g : (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj F))) ⟶
      (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj F')))) :
    IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) g ↔
      ∃ a : F' ⟶ F, g = (MorphismProperty.Over.forget _ _ (Spec R)).map
        ((relativeSpec (Spec R)).map ((symmetricAlgebra (Spec R)).map a).op) := by
  refine ⟨fun _ ↦ (existsUnique_relativeSpec_map_of_isModHom g).exists, ?_⟩
  rintro ⟨a, rfl⟩
  infer_instance

end

end TauCeti.AlgebraicGeometry
