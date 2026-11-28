/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Category.CommAlgCat.PolynomialResolution.Augmented
public import TauCeti.RingTheory.Kaehler.Over

/-!
# The cotangent complex

For a commutative `A`-algebra `B`, apply Kähler differentials to the standard
simplicial polynomial resolution `P• → B` and extend scalars in each degree
along its augmentation. The resulting simplicial `B`-module has terms
`B ⊗[Pₙ] Ω[Pₙ⁄A]`. Its alternating face complex, placed in nonpositive
cohomological degrees, represents the cotangent complex in the derived category.
The terms are free over `B`, with basis the differentials of the variables of
the corresponding polynomial algebra.
Evaluation identifies the degree-zero homology with `Ω[B⁄A]`, sending the
class of the basis vector indexed by `x : B` to `D A B x`.

## Main declarations

* `Algebra.CotangentComplex.simplicialModel` is the standard simplicial module.
* `Algebra.CotangentComplex.cochainModel` is its alternating cochain model.
* `Algebra.CotangentComplex` is the corresponding object of the derived category.
* `Algebra.CotangentComplex.toKaehler` is evaluation on degree-zero forms.
* `Algebra.CotangentComplex.toKaehler_hom_simplicialModelBasis_zero` computes the evaluation
  comparison on degree-zero basis vectors.
* `Algebra.CotangentComplex.chainHomologyZeroIso` and
  `Algebra.CotangentComplex.homologyZeroIso` identify degree-zero homology with `Ω[B⁄A]`.

## References

* The Stacks Project, Definition 92.3.2 (Tag 08PN).
* The Stacks Project, Lemma 92.4.5 (Tag 08QF), for the computation in degree zero.
* Mathlib's `AlgebraicTopology.alternatingFaceMapComplex` and
  `KaehlerDifferential.mvPolynomialBasis`.
-/

public noncomputable section

open CategoryTheory Opposite AlgebraicTopology Module TensorProduct KaehlerDifferential

universe u w

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The simplicial module of extended differentials of the standard polynomial resolution. -/
abbrev simplicialModel : SimplicialObject (ModuleCat.{u} B) :=
  ((CommAlgCat.polynomialAugmentedResolution A).obj (CommAlgCat.of A B)).kaehlerDifferential

private abbrev polynomialResolution :=
  (CommAlgCat.polynomialAugmentedResolution A).obj (CommAlgCat.of A B)

private abbrev augmentation (n : ℕ) :=
  (polynomialResolution A B).hom.app (op (SimplexCategory.mk n))

/-- The differentials of the outer polynomial variables give a basis after extending scalars
along the augmentation. -/
def simplicialModelBasis (n : ℕ) :
    Basis (((CommAlgCat.polynomialComonad A).resolutionStage n).obj (CommAlgCat.of A B)) B
      ((simplicialModel A B).obj (op (SimplexCategory.mk n))) :=
  let σ := ((CommAlgCat.polynomialComonad A).resolutionStage n).obj (CommAlgCat.of A B)
  letI : Algebra (MvPolynomial σ A) B := (augmentation A B n).hom.toAlgebra
  ((mvPolynomialBasis A σ).baseChange B : Basis σ B (B ⊗[MvPolynomial σ A] Ω[MvPolynomial σ A⁄A]))

/-- The basis vector indexed by `x` is the differential of the corresponding variable, tensored
with `1`. -/
@[simp] lemma simplicialModelBasis_apply (n : ℕ)
    (x : ((CommAlgCat.polynomialComonad A).resolutionStage n).obj (CommAlgCat.of A B)) :
    let ε := ((CommAlgCat.polynomialAugmentedResolution A).obj (CommAlgCat.of A B)).hom.app
      (op (SimplexCategory.mk n))
    let σ := ((CommAlgCat.polynomialComonad A).resolutionStage n).obj (CommAlgCat.of A B)
    letI : Algebra (MvPolynomial σ A) B := ε.hom.toAlgebra
    let basis : Basis σ B (B ⊗[MvPolynomial σ A] Ω[MvPolynomial σ A⁄A]) :=
      simplicialModelBasis A B n
    let dx : B ⊗[MvPolynomial σ A] Ω[MvPolynomial σ A⁄A] := 1 ⊗ₜ D A _ (MvPolynomial.X x)
    basis x = dx := by
  let σ := ((CommAlgCat.polynomialComonad A).resolutionStage n).obj (CommAlgCat.of A B)
  let : Algebra (MvPolynomial σ A) B := (augmentation A B n).hom.toAlgebra
  exact (Basis.baseChange_apply B (mvPolynomialBasis A σ) x).trans
    (congrArg (fun y ↦ (1 : B) ⊗ₜ[MvPolynomial σ A] y) (mvPolynomialBasis_apply A σ x))

/-- The alternating face complex of the standard simplicial module. -/
abbrev chainModel : ChainComplex (ModuleCat.{u} B) ℕ :=
  (alternatingFaceMapComplex _).obj (simplicialModel A B)

/-- The terms of the alternating face complex are projective over the target ring. -/
instance (n : ℕ) : Projective ((chainModel A B).X n) := by
  simpa only [chainModel, alternatingFaceMapComplex_obj_X] using
    ModuleCat.projective_of_free (simplicialModelBasis A B n)

/-- The standard cotangent model in cohomological degrees `−n` for `n ≥ 0`. -/
def cochainModel : CochainComplex (ModuleCat.{u} B) ℤ :=
  (chainModel A B).extend ComplexShape.embeddingDownNat

/-- The cochain model is concentrated in nonpositive degrees. -/
instance : (cochainModel A B).IsStrictlyLE 0 := by
  unfold cochainModel
  infer_instance

/-- Each term of the standard cochain model is projective over the target ring. -/
instance (i : ℤ) : Projective ((cochainModel A B).X i) := by
  unfold cochainModel
  infer_instance

/-- The term in degree `−n` is the extended module of differentials of the resolution in
simplicial degree `n`. -/
def cochainModelXIso (n : ℕ) :
    (cochainModel A B).X (-(n : ℤ)) ≅ (simplicialModel A B).obj (op (SimplexCategory.mk n)) :=
  (chainModel A B).extendXIso ComplexShape.embeddingDownNat
    (ComplexShape.embeddingDownNat_f n)

section HomologyZero

private abbrev augmentationZero : MvPolynomial B A →ₐ[A] B :=
  (augmentation A B 0).hom

private abbrev augmentationOne : MvPolynomial (MvPolynomial B A) A →ₐ[A] B :=
  (augmentation A B 1).hom

private lemma augmentationZero_isScalarTower :
    letI : Algebra (MvPolynomial B A) B := (augmentationZero A B).toAlgebra
    IsScalarTower A (MvPolynomial B A) B := by
  let : Algebra (MvPolynomial B A) B := (augmentationZero A B).toAlgebra
  exact .of_algebraMap_eq' (augmentationZero A B).comp_algebraMap.symm

/-- The first alternating differential sends a generator indexed by a polynomial `x` to the
difference between its differential and the differential of the variable indexed by its value. -/
lemma chainModel_d_one_zero_tmul_D_X (b : B) (x : MvPolynomial B A) :
    let P := (CommAlgCat.polynomialAugmentedResolution A).obj (CommAlgCat.of A B)
    let ε₀ : MvPolynomial B A →ₐ[A] B := (P.hom.app (op (SimplexCategory.mk 0))).hom
    letI := ε₀.toAlgebra
    letI : Algebra (MvPolynomial (MvPolynomial B A) A) B :=
      (P.hom.app (op (SimplexCategory.mk 1))).hom.toAlgebra
    let dx : B ⊗[MvPolynomial (MvPolynomial B A) A] Ω[MvPolynomial (MvPolynomial B A) A⁄A] :=
      b ⊗ₜ D A _ (MvPolynomial.X x)
    ((chainModel A B).d 1 0).hom dx =
      b ⊗ₜ[MvPolynomial B A] D A _ x -
        b ⊗ₜ[MvPolynomial B A] D A _ (MvPolynomial.X (ε₀ x)) := by
  let d₀ : (chainModel A B).X 1 ⟶ (chainModel A B).X 0 := (simplicialModel A B).δ (0 : Fin 2)
  let d₁ : (chainModel A B).X 1 ⟶ (chainModel A B).X 0 := (simplicialModel A B).δ (1 : Fin 2)
  have hd : (chainModel A B).d 1 0 = d₀ - d₁ := by
    rw [sub_eq_add_neg]
    simp [d₀, d₁, chainModel, Fin.sum_univ_two]
  have hd' : ((chainModel A B).d 1 0).hom = d₀.hom - d₁.hom :=
    (congrArg ModuleCat.Hom.hom hd).trans (ModuleCat.hom_sub _ _)
  refine (LinearMap.congr_fun hd' _).trans ?_
  dsimp only [d₀, d₁, LinearMap.sub_apply, SimplicialObject.δ, simplicialModel]
  refine (congrArg₂ (· - ·)
    ((polynomialResolution A B).kaehlerDifferential_map_tmul_D
      (SimplexCategory.δ (0 : Fin 2)).op b (MvPolynomial.X x))
    ((polynomialResolution A B).kaehlerDifferential_map_tmul_D
      (SimplexCategory.δ (1 : Fin 2)).op b (MvPolynomial.X x))).trans ?_
  -- The augmented resolution's left projection is the polynomial simplicial resolution,
  -- so its algebra maps at the two simplex operators are the corresponding faces below.
  have h₀ : (((CommAlgCat.polynomialSimplicialResolution A).obj (CommAlgCat.of A B)).δ
      (0 : Fin 2)).hom (MvPolynomial.X x) = x := by
    exact (DFunLike.congr_fun
      (CommAlgCat.polynomialSimplicialResolution_δ_zero_hom A (CommAlgCat.of A B)) _).trans
        (MvPolynomial.aeval_X (R := A) (_root_.id : MvPolynomial B A → MvPolynomial B A) x)
  have h₁ : (((CommAlgCat.polynomialSimplicialResolution A).obj (CommAlgCat.of A B)).δ
      (1 : Fin 2)).hom (MvPolynomial.X x) = MvPolynomial.X (augmentationZero A B x) := by
    refine (DFunLike.congr_fun
      (CommAlgCat.polynomialSimplicialResolution_δ_one_hom A (CommAlgCat.of A B)) _).trans ?_
    exact (MvPolynomial.rename_X _ _).trans (congrArg MvPolynomial.X <| (DFunLike.congr_fun
      (CommAlgCat.polynomialAugmentedResolution_hom_app_zero_hom A (CommAlgCat.of A B)) x).symm)
  let : Algebra (MvPolynomial B A) B := (augmentationZero A B).toAlgebra
  let tensorD (y : MvPolynomial B A) : B ⊗[MvPolynomial B A] Ω[MvPolynomial B A⁄A] :=
    b ⊗ₜ D A _ y
  exact congrArg₂ (· - ·) (congrArg tensorD h₀) (congrArg tensorD h₁)

/-- The evaluation augmentation induces a map from degree zero to the differential module
of the target algebra. -/
def toKaehler : (chainModel A B).X 0 ⟶ ModuleCat.of B Ω[B⁄A] :=
  letI : Algebra (MvPolynomial B A) B := (augmentationZero A B).toAlgebra
  haveI := augmentationZero_isScalarTower A B
  (ModuleCat.ofHom (mapBaseChange A (MvPolynomial B A) B) :
    ModuleCat.of B (B ⊗[MvPolynomial B A] Ω[MvPolynomial B A⁄A]) ⟶ ModuleCat.of B Ω[B⁄A])

/-- The map on degree-zero forms applies the augmentation to the element being differentiated. -/
@[simp] lemma toKaehler_tmul_D (b : B) (x : MvPolynomial B A) :
    let ε : MvPolynomial B A →ₐ[A] B :=
      (((CommAlgCat.polynomialAugmentedResolution A).obj (CommAlgCat.of A B)).hom.app
        (op (SimplexCategory.mk 0))).hom
    letI := ε.toAlgebra
    let evaluate : (B ⊗[MvPolynomial B A] Ω[MvPolynomial B A⁄A]) →ₗ[B] Ω[B⁄A] :=
      (toKaehler A B).hom
    let dx : B ⊗[MvPolynomial B A] Ω[MvPolynomial B A⁄A] := b ⊗ₜ D A _ x
    evaluate dx = b • D A B (ε x) := by
  let : Algebra (MvPolynomial B A) B := (augmentationZero A B).toAlgebra
  have := augmentationZero_isScalarTower A B
  exact (mapBaseChange_tmul A (MvPolynomial B A) B b (D A _ x)).trans
    (congrArg (b • ·) (map_D A A (MvPolynomial B A) B x))

/-- Evaluation surjects onto the differential module of the target algebra. -/
lemma toKaehler_surjective : Function.Surjective (toKaehler A B).hom := by
  let : Algebra (MvPolynomial B A) B := (augmentationZero A B).toAlgebra
  have := augmentationZero_isScalarTower A B
  exact mapBaseChange_surjective A (MvPolynomial B A) B
    (CommAlgCat.polynomialAugmentedResolution_hom_app_zero_hom_surjective A (CommAlgCat.of A B))

/-- The degree-zero comparison sends the basis vector indexed by `x` to the universal
differential of `x`. -/
@[simp↓]
lemma toKaehler_hom_simplicialModelBasis_zero (x : B) :
    (toKaehler A B).hom (simplicialModelBasis A B 0 x) = D A B x := by
  refine (congrArg (toKaehler A B).hom (simplicialModelBasis_apply A B 0 x)).trans <|
    (toKaehler_tmul_D A B 1 (MvPolynomial.X x)).trans ?_
  exact (one_smul B _).trans <| congrArg (D A B)
    (CommAlgCat.polynomialAugmentedResolution_hom_app_zero_hom_X A (CommAlgCat.of A B) x)

/-- The degree-zero comparison kills the first differential of the cotangent complex. -/
@[reassoc]
lemma d_one_zero_comp_toKaehler : (chainModel A B).d 1 0 ≫ toKaehler A B = 0 := by
  apply ModuleCat.hom_ext
  apply (simplicialModelBasis A B 1).ext
  intro x
  let : Algebra (MvPolynomial B A) B := (augmentationZero A B).toAlgebra
  let d := ((chainModel A B).d 1 0).hom
  let g := (toKaehler A B).hom
  let dx (y : MvPolynomial B A) : B ⊗[MvPolynomial B A] Ω[MvPolynomial B A⁄A] := 1 ⊗ₜ D A _ y
  have h := (congrArg d (simplicialModelBasis_apply A B 1 x)).trans
    (chainModel_d_one_zero_tmul_D_X A B 1 x)
  calc
    _ = g (dx x - dx (MvPolynomial.X (augmentationZero A B x))) := congrArg g h
    _ = g (dx x) - g (dx (MvPolynomial.X (augmentationZero A B x))) := map_sub _ _ _
    _ = 0 := by
      refine (congrArg₂ (· - ·) (toKaehler_tmul_D A B 1 x)
        (toKaehler_tmul_D A B 1 (MvPolynomial.X (augmentationZero A B x)))).trans ?_
      exact sub_eq_zero.mpr <| (congrArg (fun y ↦ (1 : B) • D A B y)
        (CommAlgCat.polynomialAugmentedResolution_hom_app_zero_hom_X A (CommAlgCat.of A B)
          (augmentationZero A B x))).symm

/-- Every vector killed by the degree-zero comparison comes from the first differential. -/
private lemma mem_range_d_one_zero_of_toKaehler_eq_zero (z : (chainModel A B).X 0)
    (hz : (toKaehler A B).hom z = 0) :
    z ∈ Set.range ((chainModel A B).d 1 0).hom := by
  let : Algebra (MvPolynomial B A) B := (augmentationZero A B).toAlgebra
  let : Algebra (MvPolynomial (MvPolynomial B A) A) B := (augmentationOne A B).toAlgebra
  have := augmentationZero_isScalarTower A B
  have hexact := exact_kerCotangentToTensor_mapBaseChange A (MvPolynomial B A) B
    (CommAlgCat.polynomialAugmentedResolution_hom_app_zero_hom_surjective A (CommAlgCat.of A B))
  obtain ⟨z', hz'⟩ := (hexact z).mp hz
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ z'
  let dx (y : MvPolynomial B A) :
      B ⊗[MvPolynomial (MvPolynomial B A) A] Ω[MvPolynomial (MvPolynomial B A) A⁄A] :=
    1 ⊗ₜ D A _ (MvPolynomial.X y)
  -- Subtract the generator indexed by zero so both faces contributing the variable `X 0`
  -- cancel when `x` lies in the augmentation kernel.
  refine ⟨dx x.val - dx 0, ?_⟩
  have hx : augmentationZero A B x.val = 0 := RingHom.mem_ker.mp x.property
  let d := ((chainModel A B).d 1 0).hom
  have h := (map_sub d (dx x.val) (dx 0)).trans
    (congrArg₂ (· - ·) (chainModel_d_one_zero_tmul_D_X A B 1 x.val)
      (chainModel_d_one_zero_tmul_D_X A B 1 0))
  refine h.trans ?_
  let ω (y : MvPolynomial B A) : B ⊗[MvPolynomial B A] Ω[MvPolynomial B A⁄A] := 1 ⊗ₜ D A _ y
  -- Work in the concrete tensor product so the additive identities match the displayed tensors.
  change ω x.val - ω (MvPolynomial.X (augmentationZero A B x.val)) -
    (ω 0 - ω (MvPolynomial.X (augmentationZero A B 0))) =
      (z : B ⊗[MvPolynomial B A] Ω[MvPolynomial B A⁄A])
  have hω : ω x.val = z :=
    (kerCotangentToTensor_toCotangent A (MvPolynomial B A) B x).symm.trans hz'
  simpa [ω, hx, sub_neg_eq_add] using hω

/-- The kernel of the degree-zero comparison is the image of the first differential. -/
lemma toKaehler_exact :
    Function.Exact ((chainModel A B).d 1 0).hom (toKaehler A B).hom := by
  intro z
  refine ⟨mem_range_d_one_zero_of_toKaehler_eq_zero A B z, ?_⟩
  rintro ⟨y, rfl⟩
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (d_one_zero_comp_toKaehler A B)) y

/-- The cokernel of the first differential computes the degree-zero homology. -/
private abbrev chainHomologyZeroData : ((chainModel A B).sc' 1 0 0).LeftHomologyData := by
  let K := chainModel A B
  let h := ModuleCat.isColimitCokernelCofork (K.d 1 0) (toKaehler A B)
    (toKaehler_exact A B) (toKaehler_surjective A B)
  exact ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork (K.sc' 1 0 0) (by simp) _ h

/-- Degree-zero homology of the strict cotangent model is the Kähler differential module. -/
def chainHomologyZeroIso : (chainModel A B).homology 0 ≅ ModuleCat.of B Ω[B⁄A] :=
  (chainModel A B).homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    (chainHomologyZeroData A B).homologyIso

/-- The homology comparison is induced by evaluation on the degree-zero terms. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_chainHomologyZeroIso_hom :
    (chainModel A B).homologyπ 0 ≫ (chainHomologyZeroIso A B).hom =
      (chainModel A B).iCycles 0 ≫ toKaehler A B := by
  rw [chainHomologyZeroIso, Iso.trans_hom, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  have h : (chainHomologyZeroData A B).cyclesIso.hom = ((chainModel A B).sc' 1 0 0).iCycles :=
    (Category.comp_id _).symm.trans (chainHomologyZeroData A B).cyclesIso_hom_comp_i
  rw [h, ← Category.assoc, HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  dsimp only [chainHomologyZeroData]
  rw [ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_π,
    Limits.CokernelCofork.π_ofπ]

end HomologyZero

end Algebra.CotangentComplex

/-- The cotangent complex of a commutative algebra, realized by the standard polynomial
resolution and viewed in the derived category of modules over the target ring. -/
def Algebra.CotangentComplex (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)] : DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.Q.obj (Algebra.CotangentComplex.cochainModel A B)

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- The projective cochain model represents the cotangent complex in the derived category. -/
lemma eq_Q_obj_cochainModel :
    Algebra.CotangentComplex A B = DerivedCategory.Q.obj (cochainModel A B) := (rfl)

/-- The zeroth cohomology of the cotangent complex is the module of Kähler differentials. -/
def homologyZeroIso :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj (Algebra.CotangentComplex A B) ≅
      ModuleCat.of B Ω[B⁄A] :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 0).app (cochainModel A B) ≪≫
    (chainModel A B).extendHomologyIso ComplexShape.embeddingDownNat (j := 0) (by simp) ≪≫
    chainHomologyZeroIso A B

/-- Pulling the derived homology comparison back to the cycles of the cochain model gives
evaluation on the degree-zero terms. -/
@[reassoc]
lemma homologyπ_comp_homologyZeroIso_hom :
    (cochainModel A B).homologyπ 0 ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 0).app (cochainModel A B)).inv ≫
        eqToHom (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj
          (eq_Q_obj_cochainModel A B).symm) ≫
        (homologyZeroIso A B).hom =
      (cochainModel A B).iCycles 0 ≫ (cochainModelXIso A B 0).hom ≫ toKaehler A B := by
  let α := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 0).app (cochainModel A B)
  let β := (chainModel A B).extendHomologyIso ComplexShape.embeddingDownNat
    (j := 0) (j' := 0) (by simp)
  -- The transport names the definitional equality between the derived object and its model.
  -- Reduce it to the identity before cancelling the two copies of the localization isomorphism.
  change (cochainModel A B).homologyπ 0 ≫ α.inv ≫ 𝟙 _ ≫
    (α ≪≫ β ≪≫ chainHomologyZeroIso A B).hom = _
  simp only [Category.id_comp, Iso.trans_hom, Iso.inv_hom_id_assoc]
  let e := ComplexShape.embeddingDownNat
  have h : e.f 0 = 0 := ComplexShape.embeddingDownNat_f 0
  let γ := (chainModel A B).extendCyclesIso e h
  exact ((chainModel A B).homologyπ_extendHomologyIso_hom_assoc e h _).trans <|
    (congrArg (γ.hom ≫ ·) (homologyπ_comp_chainHomologyZeroIso_hom A B)).trans <|
      (chainModel A B).extendCyclesIso_hom_iCycles_assoc e h (toKaehler A B)

end Algebra.CotangentComplex
