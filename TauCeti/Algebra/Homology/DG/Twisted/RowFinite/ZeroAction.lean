/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Splitting

/-!
# Twisted complexes whose cocycle acts by zero on the coefficients

Let `m` be a row-finite twisting cocycle on generators `P` graded by `ind`, with values in a
differential graded algebra `A`, and let `M` be a DG right module over `A` on which every entry
`m x y` acts by zero. Then the twisting part `(-1)^|α| ∑_y α · m x y` of the twisted differential
vanishes, and the twisted complex `M ⊗ ⟨P⟩` is the direct sum over the generators of copies of
`M` with the differential `dM`
(`TauCeti.RowFiniteTwistingCocycle.coefficientDifferential_eq_mapRange_of_forall_op_smul_eq_zero`):
in total degree `n`, the component of a generator `x` lies in `M` in degree `n + ind x`.

For finitely many generators its cohomology is therefore the product over the generators of the
cohomology of `M`, shifted by the indices
(`TauCeti.RowFiniteTwistingCocycle.coefficientHomologyEquivOfForallOpSmulEqZero`):

`Hⁿ(M ⊗ ⟨P⟩) ≅ ∏_x H^{n + ind x}(M)`.

This happens whenever `M` is acted on through an augmentation and the entries of `m` lie in the
augmentation ideal, as for coefficients with the trivial action, or for coefficients concentrated
in one degree and entries of nonzero degree. In homological terms, the twisted homology is then
the homology of the classical complex of the generators with zero differential, tensored with the
homology of the coefficients: the twisting cocycle is invisible. For a cell structure with one
cell in each of the degrees `0` and `n` and the chains on the loop space as coefficients, this
gives `H_*(Sⁿ) ⊗ H_*(ΩSⁿ)` in place of the homology of the path space, which is that of a point.

The chain maps evaluating a coefficient vector at a generator
(`TauCeti.RowFiniteTwistingCocycle.coefficientEval`) and inserting a coefficient at a generator
(`TauCeti.RowFiniteTwistingCocycle.coefficientSingle`) exhibit the twisted complex as a biproduct
(`TauCeti.RowFiniteTwistingCocycle.coefficientBicone`), which the additive cohomology functor
preserves. The graded pieces of the index filtration split likewise, over the generators of a
single index (`TauCeti.indexGradedPieceHomologyIso`,
`TauCeti.rowFiniteIndexGradedPieceHomologyIso`); here the generators have arbitrary indices and
the whole twisted complex splits, because the cocycle acts by zero.

## Main definitions

* `TauCeti.RowFiniteTwistingCocycle.coefficientEval`: the evaluation at a generator, a morphism of
  complexes to `TauCeti.shiftedModuleComplex hM (ind x)`.
* `TauCeti.RowFiniteTwistingCocycle.coefficientSingle`: the insertion at a generator.
* `TauCeti.RowFiniteTwistingCocycle.coefficientBicone`: the twisted complex as the biproduct of
  the shifted coefficients.
* `TauCeti.RowFiniteTwistingCocycle.coefficientHomologyIsoOfForallOpSmulEqZero`: the cohomology of
  the twisted complex is the product of the shifted cohomologies of the coefficients.
* `TauCeti.RowFiniteTwistingCocycle.coefficientHomologyEquivOfForallOpSmulEqZero`: the same, with
  values in the intrinsic cohomology `H^{n + ind x}(M)`.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.coefficientDifferential_eq_mapRange_of_forall_op_smul_eq_zero`:
  the twisted differential is `dM` on every coefficient.
* `TauCeti.RowFiniteTwistingCocycle.coefficientHomologyEquivOfForallOpSmulEqZero_apply`: the
  component at `x` of a class is the class of its evaluation at `x`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 7 (the fibration
  theorem).
-/

public noncomputable section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {ind : P → ℤ}

namespace RowFiniteTwistingCocycle

variable {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}
  (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)

/-! ### The differential -/

section Differential

variable {m} (hm : ∀ x y (α : M), op (m.m x y) • α = 0)
include hm

/-- If the entries of the cocycle act by zero on the coefficients, the twisted differential of an
elementary vector `α x` is `(dM α) x`. -/
theorem coefficientDifferential_single_of_forall_op_smul_eq_zero (x : P) (α : M) :
    m.coefficientDifferential hM (Finsupp.single x α) = Finsupp.single x (dM α) := by
  classical
  induction α using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous q α =>
    rw [m.coefficientDifferential_single hM x α.property, Finsupp.sum,
      Finset.sum_eq_zero fun y _ ↦ by rw [hm, Finsupp.single_zero], smul_zero, add_zero]
  | add α β hα hβ =>
    rw [Finsupp.single_add, map_add, hα, hβ, map_add, Finsupp.single_add]

/-- **The twisted differential of a cocycle acting by zero** is the differential of the
coefficients, applied to every coefficient. -/
theorem coefficientDifferential_eq_mapRange_of_forall_op_smul_eq_zero :
    m.coefficientDifferential hM = Finsupp.mapRange.linearMap dM :=
  Finsupp.lhom_ext fun x α ↦ by
    rw [coefficientDifferential_single_of_forall_op_smul_eq_zero hM hm,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]

end Differential

/-! ### Evaluation and insertion at a generator -/

section EvalSingle

/-- The evaluation at a generator `x`, from the degree-`n` term of the twisted complex to
`ℳ (n + ind x)`. -/
def coefficientEvalX (x : P) (n : ℤ) :
    (m.coefficientCochainComplex hM).X n →ₗ[R]
      (shiftedModuleComplex.{uR, uA, uM, uP} hM (ind x)).X n :=
  (shiftedModuleComplexXEquiv hM (ind x) n).symm.toLinearMap ∘ₗ
    ((Finsupp.lapply x ∘ₗ (rowFiniteTotalGrading ℳ ind n).subtype).codRestrict
        (ℳ (n + ind x)) fun f ↦ (mem_rowFiniteTotalGrading_iff _ _).1 f.property x) ∘ₗ
    (m.coefficientCochainComplexXEquiv hM n).toLinearMap

/-- `coefficientEvalX` evaluates the coefficient vector at `x`. -/
@[simp]
theorem shiftedModuleComplexXEquiv_coefficientEvalX (x : P) (n : ℤ)
    (f : (m.coefficientCochainComplex hM).X n) :
    (shiftedModuleComplexXEquiv hM (ind x) n (m.coefficientEvalX hM x n f) : M) =
      (m.coefficientCochainComplexXEquiv hM n f : P →₀ M) x := by
  simp only [coefficientEvalX, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]
  exact LinearMap.codRestrict_apply _ _ _

/-- The insertion at a generator `x`, from `ℳ (n + ind x)` to the degree-`n` term of the twisted
complex. -/
def coefficientSingleX (x : P) (n : ℤ) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM (ind x)).X n →ₗ[R]
      (m.coefficientCochainComplex hM).X n :=
  (m.coefficientCochainComplexXEquiv hM n).symm.toLinearMap ∘ₗ
    ((Finsupp.lsingle x ∘ₗ (ℳ (n + ind x)).subtype).codRestrict _ fun α ↦
      (mem_rowFiniteTotalGrading_iff _ _).2 fun y ↦ by
        classical
        by_cases hy : x = y
        · subst hy
          simp
        · simp [hy]) ∘ₗ
    (shiftedModuleComplexXEquiv hM (ind x) n).toLinearMap

/-- `coefficientSingleX` inserts an element at `x`. -/
@[simp]
theorem coefficientCochainComplexXEquiv_coefficientSingleX (x : P) (n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (ind x)).X n) :
    (m.coefficientCochainComplexXEquiv hM n (m.coefficientSingleX hM x n α) : P →₀ M) =
      Finsupp.single x (shiftedModuleComplexXEquiv hM (ind x) n α : M) := by
  simp only [coefficientSingleX, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]
  exact LinearMap.codRestrict_apply _ _ _

variable {m} (hm : ∀ x y (α : M), op (m.m x y) • α = 0)

/-- **The evaluation at a generator** `x`, as a morphism of complexes from the twisted complex of a
cocycle acting by zero to `TauCeti.shiftedModuleComplex hM (ind x)`. -/
def coefficientEval (x : P) :
    m.coefficientCochainComplex hM ⟶ shiftedModuleComplex.{uR, uA, uM, uP} hM (ind x) where
  f n := ModuleCat.ofHom (m.coefficientEvalX hM x n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (shiftedModuleComplexXEquiv hM (ind x) (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [shiftedModuleComplexXEquiv_d, shiftedModuleComplexXEquiv_coefficientEvalX,
      shiftedModuleComplexXEquiv_coefficientEvalX, coefficientCochainComplexXEquiv_d,
      coefficientDifferential_eq_mapRange_of_forall_op_smul_eq_zero hM hm,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]

/-- `coefficientEval` evaluates the coefficient vector at `x`. -/
@[simp]
theorem shiftedModuleComplexXEquiv_coefficientEval_f (x : P) (n : ℤ)
    (f : (m.coefficientCochainComplex hM).X n) :
    (shiftedModuleComplexXEquiv hM (ind x) n (((coefficientEval hM hm x).f n).hom f) : M) =
      (m.coefficientCochainComplexXEquiv hM n f : P →₀ M) x :=
  m.shiftedModuleComplexXEquiv_coefficientEvalX hM x n f

/-- **The insertion at a generator** `x`, as a morphism of complexes from
`TauCeti.shiftedModuleComplex hM (ind x)` to the twisted complex of a cocycle acting by zero. -/
def coefficientSingle (x : P) :
    shiftedModuleComplex.{uR, uA, uM, uP} hM (ind x) ⟶ m.coefficientCochainComplex hM where
  f n := ModuleCat.ofHom (m.coefficientSingleX hM x n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun α ↦
      (m.coefficientCochainComplexXEquiv hM (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [coefficientCochainComplexXEquiv_d, coefficientCochainComplexXEquiv_coefficientSingleX,
      coefficientCochainComplexXEquiv_coefficientSingleX, shiftedModuleComplexXEquiv_d,
      coefficientDifferential_single_of_forall_op_smul_eq_zero hM hm]

/-- `coefficientSingle` inserts an element at `x`. -/
@[simp]
theorem coefficientCochainComplexXEquiv_coefficientSingle_f (x : P) (n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (ind x)).X n) :
    (m.coefficientCochainComplexXEquiv hM n (((coefficientSingle hM hm x).f n).hom α) :
        P →₀ M) = Finsupp.single x (shiftedModuleComplexXEquiv hM (ind x) n α : M) :=
  m.coefficientCochainComplexXEquiv_coefficientSingleX hM x n α

/-- Inserting at `x` and evaluating at `x` is the identity. -/
@[reassoc (attr := simp)]
theorem coefficientSingle_comp_eval_self (x : P) :
    coefficientSingle hM hm x ≫ coefficientEval hM hm x = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun α ↦
    (shiftedModuleComplexXEquiv hM (ind x) n).injective (Subtype.ext ?_))
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    shiftedModuleComplexXEquiv_coefficientEval_f,
    coefficientCochainComplexXEquiv_coefficientSingle_f, Finsupp.single_eq_same,
    HomologicalComplex.id_f, ModuleCat.id_apply]

/-- Inserting at `x` and evaluating at another generator `y` is zero. -/
theorem coefficientSingle_comp_eval_of_ne {x y : P} (hxy : x ≠ y) :
    coefficientSingle hM hm x ≫ coefficientEval hM hm y = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun α ↦
    (shiftedModuleComplexXEquiv hM (ind y) n).injective (Subtype.ext ?_))
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    shiftedModuleComplexXEquiv_coefficientEval_f,
    coefficientCochainComplexXEquiv_coefficientSingle_f, Finsupp.single_eq_of_ne' hxy]
  simp

/-- The sum over the generators of evaluating and inserting is the identity of the twisted
complex. -/
theorem sum_coefficientEval_comp_single [Fintype P] :
    ∑ x : P, coefficientEval hM hm x ≫ coefficientSingle hM hm x =
      𝟙 (m.coefficientCochainComplex hM) := by
  classical
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (m.coefficientCochainComplexXEquiv hM n).injective (Subtype.ext ?_))
  rw [← HomologicalComplex.Hom.fAddMonoidHom_apply, map_sum, ModuleCat.hom_sum,
    LinearMap.sum_apply, map_sum, Submodule.coe_sum, HomologicalComplex.id_f, ModuleCat.id_apply]
  ext y
  rw [Finsupp.finsetSum_apply]
  simp only [HomologicalComplex.Hom.fAddMonoidHom_apply, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply, coefficientCochainComplexXEquiv_coefficientSingle_f,
    shiftedModuleComplexXEquiv_coefficientEval_f, Finsupp.single_apply]
  rw [Finset.sum_eq_single y (fun x _ hx ↦ ite_eq_right hx) (fun h ↦ absurd (Finset.mem_univ _) h),
    ite_eq_left rfl]

end EvalSingle

/-! ### The cohomology -/

section Homology

variable [Fintype P] {m}
  (hm : ∀ x y (α : M), op (m.m x y) • α = 0)
include hm

omit [Fintype P] in
/-- The twisted complex of a cocycle acting by zero as a biproduct of the complexes
`TauCeti.shiftedModuleComplex hM (ind x)`, with the evaluations as projections and the insertions
as inclusions. -/
def coefficientBicone :
    Bicone fun x : P ↦ shiftedModuleComplex.{uR, uA, uM, uP} hM (ind x) where
  pt := m.coefficientCochainComplex hM
  π := coefficientEval hM hm
  ι := coefficientSingle hM hm
  ι_π x y := by
    split_ifs with hxy
    · subst hxy
      exact coefficientSingle_comp_eval_self hM hm x
    · exact coefficientSingle_comp_eval_of_ne hM hm hxy

/-- The image of `TauCeti.RowFiniteTwistingCocycle.coefficientBicone` in cohomology of degree `n`
is a biproduct: the cohomology functor is additive, and evaluating and inserting at all generators
sums to the identity. -/
def isBilimitHomologyMapCoefficientBicone (n : ℤ) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max uP uM} R) (ComplexShape.up ℤ) n).mapBicone
      (coefficientBicone hM hm)).IsBilimit :=
  isBilimitOfTotal _ <| by
    have key := (HomologicalComplex.homologyFunctor (ModuleCat.{max uP uM} R) (ComplexShape.up ℤ)
      n).map_sum (fun x : P ↦ coefficientEval hM hm x ≫ coefficientSingle hM hm x) Finset.univ
    rw [sum_coefficientEval_comp_single, CategoryTheory.Functor.map_id] at key
    exact (Finset.sum_congr rfl fun x _ ↦ (Functor.map_comp _ _ _).symm).trans key.symm

/-- **The cohomology of a twisted complex whose cocycle acts by zero**: in total degree `n` it is
the product over the generators `x` of the cohomology of `shiftedModuleComplex hM (ind x)` in
degree `n`, that is of the coefficients in degree `n + ind x`, through the evaluations and
insertions at the generators. -/
def coefficientHomologyIsoOfForallOpSmulEqZero (n : ℤ) :
    (m.coefficientCochainComplex hM).homology n ≅
      ∏ᶜ fun x : P ↦ (shiftedModuleComplex.{uR, uA, uM, uP} hM (ind x)).homology n :=
  (isBilimitHomologyMapCoefficientBicone hM hm n).isLimit.conePointUniqueUpToIso
    (limit.isLimit _)

/-- The component at a generator `x` of `coefficientHomologyIsoOfForallOpSmulEqZero` is the map in
cohomology of the evaluation at `x`. -/
@[reassoc (attr := simp)]
theorem coefficientHomologyIsoOfForallOpSmulEqZero_hom_π (n : ℤ) (x : P) :
    (coefficientHomologyIsoOfForallOpSmulEqZero hM hm n).hom ≫ Pi.π _ x =
      HomologicalComplex.homologyMap (coefficientEval hM hm x) n :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk x)

/-- The inverse of `coefficientHomologyIsoOfForallOpSmulEqZero` is the sum of the maps in
cohomology of the insertions at the generators. -/
theorem coefficientHomologyIsoOfForallOpSmulEqZero_inv (n : ℤ) :
    (coefficientHomologyIsoOfForallOpSmulEqZero hM hm n).inv = ∑ x : P,
      Pi.π _ x ≫ HomologicalComplex.homologyMap (coefficientSingle hM hm x) n :=
  (Category.comp_id _).symm.trans <| (congrArg _
    (IsBilimit.total (isBilimitHomologyMapCoefficientBicone hM hm n)).symm).trans <|
      (Preadditive.comp_sum _ _ _).trans <| Finset.sum_congr rfl fun x _ ↦
        (Category.assoc _ _ _).symm.trans <| congrArg (· ≫ _)
          (IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk x))

/-- **The cohomology of a twisted complex whose cocycle acts by zero**, read in the cohomology of
the coefficients: `Hⁿ(M ⊗ ⟨P⟩) ≅ ∏_x H^{n + ind x}(M)`. -/
def coefficientHomologyEquivOfForallOpSmulEqZero (n : ℤ) :
    (m.coefficientCochainComplex hM).homology n ≃ₗ[R]
      ((x : P) → hM.cohomologyGrading (n + ind x)) :=
  (coefficientHomologyIsoOfForallOpSmulEqZero hM hm n ≪≫ ModuleCat.piIsoPi _).toLinearEquiv ≪≫ₗ
    LinearEquiv.piCongrRight fun x ↦ shiftedModuleComplexHomologyEquiv hM (ind x) n

/-- The component at a generator `x` of `coefficientHomologyEquivOfForallOpSmulEqZero` of a class
is the class in `H^{n + ind x}(M)` of its image under the evaluation at `x`. -/
@[simp]
theorem coefficientHomologyEquivOfForallOpSmulEqZero_apply (n : ℤ)
    (c : (m.coefficientCochainComplex hM).homology n) (x : P) :
    coefficientHomologyEquivOfForallOpSmulEqZero hM hm n c x =
      shiftedModuleComplexHomologyEquiv hM (ind x) n
        ((HomologicalComplex.homologyMap (coefficientEval hM hm x) n).hom c) := by
  rw [coefficientHomologyEquivOfForallOpSmulEqZero, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, Iso.toLinearEquiv_apply, Iso.trans_hom,
    ConcreteCategory.comp_apply]
  congr 1
  exact (ModuleCat.piIsoPi_hom_ker_subtype_apply _ x _).trans <| by
    rw [← ConcreteCategory.comp_apply, coefficientHomologyIsoOfForallOpSmulEqZero_hom_π]

end Homology

end RowFiniteTwistingCocycle

end TauCeti
