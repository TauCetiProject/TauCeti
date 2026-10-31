/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import TauCeti.Algebra.Homology.DG.Twisted.Continuation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Continuation maps for row-finite twisted modules

A continuation cocycle between row-finite twisting cocycles specifies a finite row for each
source generator. Its equation says that the differential of this row is the image of the
source differential row. The DG Leibniz rule extends this generator equation to a chain map
on the entire free left module. No finiteness assumption on either generator set is needed.

Composition substitutes finite rows into finite rows, so it again has finite rows. Tensoring
with a DG right module gives continuation maps on finite-support coefficient vectors. These
maps preserve total degree and commute with the twisted coefficient differentials. This is
ordinary tensor functoriality, not a claim that the twisted modules are resolutions.

The generator equation uses `rowFiniteTwistedDifferential`, which includes the Koszul signs.
The theorem `RowFiniteContinuationCocycle.continuation_iff` expands it into the usual signed
continuation equation. For finite bases, the induced coefficient map is the existing
`continuationMap` through the finite-support/function equivalence.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4, Definition 1.10.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public noncomputable section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP uQ uS uT

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {P : Type uP} {Q : Type uQ} {S : Type uS} {T : Type uT}
  {indP : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ} {indT : T → ℤ}

/-- A row-finite continuation cocycle. The continuation equation is imposed only on generators;
the chain-map identity on all vectors follows from the DG Leibniz rule. -/
structure RowFiniteContinuationCocycle
    (mP : RowFiniteTwistingCocycle 𝒜 d P indP)
    (mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ) where
  /-- The finite row which is the image of each source generator. -/
  ν : P → Q →₀ A
  /-- A matrix entry has the degree of a degree-zero map between the shifted generators. -/
  mem_graded : ∀ x y, ν x y ∈ 𝒜 (indQ y - indP x)
  /-- The differential of an image row is the image of the source differential row. -/
  continuation : ∀ x, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (ν x) =
    Finsupp.linearCombination A ν (mP.m x)

namespace RowFiniteContinuationCocycle

variable {mP : RowFiniteTwistingCocycle 𝒜 d P indP}
  {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  {mS : RowFiniteTwistingCocycle 𝒜 d S indS}
  {mT : RowFiniteTwistingCocycle 𝒜 d T indT}

@[ext]
theorem ext {ν μ : RowFiniteContinuationCocycle mP mQ}
    (h : ∀ x y, ν.ν x y = μ.ν x y) : ν = μ := by
  cases ν
  cases μ
  congr
  funext x
  exact Finsupp.ext (h x)

/-- Expansion of the generator equation into the signed finite-row continuation equation.
The second sum has the source convention's sign `(-1)^(indP x - indQ y - 1)`. -/
theorem continuation_iff (ν : P → Q →₀ A)
    (hν : ∀ x y, ν x y ∈ 𝒜 (indQ y - indP x)) (x : P) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (ν x) =
        Finsupp.linearCombination A ν (mP.m x) ↔
      Finsupp.mapRange.linearMap d (ν x) =
        Finsupp.linearCombination A ν (mP.m x) +
          (ν x).sum (fun y a ↦ (indP x - indQ y - 1).negOnePow • (a • mQ.m y)) := by
  classical
  have hd : (∑ y ∈ (ν x).support, Finsupp.single y (d (ν x y))) =
      Finsupp.mapRange.linearMap d (ν x) := by
    conv_rhs => rw [← Finsupp.sum_single (ν x), Finsupp.sum]
    rw [map_sum]
    simp
  have hD : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (ν x) =
      Finsupp.mapRange.linearMap d (ν x) +
        (ν x).sum (fun y a ↦ (indQ y - indP x).negOnePow • (a • mQ.m y)) := by
    conv_lhs => rw [← Finsupp.sum_single (ν x), Finsupp.sum, map_sum]
    simp_rw [rowFiniteTwistedDifferential_single mQ.m _ (hν x _)]
    rw [Finset.sum_add_distrib, hd, Finsupp.sum]
  rw [hD]
  simp only [Int.negOnePow_sub_sub_one, Units.neg_smul, Finsupp.sum, Finset.sum_neg_distrib]
  constructor
  · intro heq
    rw [← heq]
    abel
  · intro heq
    rw [heq]
    abel

variable (ν : RowFiniteContinuationCocycle mP mQ)

/-- Substitution of finite continuation rows preserves total degree. -/
theorem linearCombination_mem_totalGrading {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 indP n) :
    Finsupp.linearCombination A ν.ν f ∈ rowFiniteTotalGrading 𝒜 indQ n := by
  classical
  rw [mem_rowFiniteTotalGrading_iff] at hf ⊢
  intro y
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have := SetLike.GradedMul.mul_mem (hf x) (ν.mem_graded x y)
  simp only [Finsupp.smul_apply, smul_eq_mul]
  convert this using 2; ring

/-- The generator equation extends to the entire free left module by the DG Leibniz rule. -/
theorem linearCombination_differential (hA : IsDGAlgebra 𝒜 d) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m
        (Finsupp.linearCombination A ν.ν f) =
      Finsupp.linearCombination A ν.ν
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q a =>
      rw [Finsupp.linearCombination_single,
        rowFiniteTwistedDifferential_smul mQ.m hA a.2,
        rowFiniteTwistedDifferential_single mP.m x a.2, map_add,
        Finsupp.linearCombination_single, ν.continuation x]
      simp only [map_smul, LinearMap.map_smul_of_tower]
    | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]

/-- The identity continuation cocycle has one unit entry in each row. -/
def refl (m : RowFiniteTwistingCocycle 𝒜 d P indP) (hA : IsDGAlgebra 𝒜 d) :
    RowFiniteContinuationCocycle m m where
  ν x := Finsupp.single x 1
  mem_graded x y := by
    classical
    by_cases hxy : x = y
    · subst y
      simpa using SetLike.one_mem_graded 𝒜
    · simp [Finsupp.single_eq_of_ne (Ne.symm hxy)]
  continuation x := by
    rw [m.differential_single_one hA]
    simp [Finsupp.linearCombination_apply]

@[simp]
theorem refl_ν (m : RowFiniteTwistingCocycle 𝒜 d P indP) (hA : IsDGAlgebra 𝒜 d) (x : P) :
    (refl m hA).ν x = Finsupp.single x 1 := (rfl)

/-- Composition substitutes the second finite row into each entry of the first finite row. -/
def comp (μ : RowFiniteContinuationCocycle mQ mS) (hA : IsDGAlgebra 𝒜 d) :
    RowFiniteContinuationCocycle mP mS where
  ν x := Finsupp.linearCombination A μ.ν (ν.ν x)
  mem_graded x y := by
    have hrow : ν.ν x ∈ rowFiniteTotalGrading 𝒜 indQ (-indP x) := by
      rw [mem_rowFiniteTotalGrading_iff]
      intro z
      simpa only [neg_add_eq_sub] using ν.mem_graded x z
    have hmem := μ.linearCombination_mem_totalGrading hrow
    rw [mem_rowFiniteTotalGrading_iff] at hmem
    have := hmem y
    simpa only [neg_add_eq_sub] using this
  continuation x := by
    rw [μ.linearCombination_differential hA, ν.continuation,
      Finsupp.linearCombination_linearCombination]

@[simp]
theorem comp_ν (μ : RowFiniteContinuationCocycle mQ mS) (hA : IsDGAlgebra 𝒜 d) (x : P) :
    (ν.comp μ hA).ν x = Finsupp.linearCombination A μ.ν (ν.ν x) := (rfl)

@[simp]
theorem refl_comp (hA : IsDGAlgebra 𝒜 d) : (refl mP hA).comp ν hA = ν := by
  ext x y
  simp

@[simp]
theorem comp_refl (hA : IsDGAlgebra 𝒜 d) : ν.comp (refl mQ hA) hA = ν := by
  ext x y
  simp [Finsupp.linearCombination_apply]

/-- Composition of row-finite continuation cocycles is associative. -/
theorem comp_assoc (μ : RowFiniteContinuationCocycle mQ mS)
    (κ : RowFiniteContinuationCocycle mS mT) (hA : IsDGAlgebra 𝒜 d) :
    (ν.comp μ hA).comp κ hA = ν.comp (μ.comp κ hA) hA := by
  ext x y
  simp only [comp_ν, Finsupp.linearCombination_linearCombination]
  -- The composed rows occur as an unapplied function argument to linearCombination,
  -- so the pointwise comp_ν rewrite needs function extensionality here.
  rw [show (μ.comp κ hA).ν = fun z ↦ Finsupp.linearCombination A κ.ν (μ.ν z) from
    funext fun z ↦ comp_ν μ κ hA z]

section Coefficients

open BalancedTensorProduct

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]

/-- Tensor the finite-row substitution map with the identity on right coefficients. -/
def tensorMap : BalancedTensorProduct R A M (P →₀ A) →ₗ[R]
    BalancedTensorProduct R A M (Q →₀ A) :=
  BalancedTensorProduct.map LinearMap.id ((Finsupp.linearCombination A ν.ν).restrictScalars R)
    (fun _ _ ↦ rfl) (fun a f ↦ by simp only [LinearMap.restrictScalars_apply, map_smul])

/-- On pure tensors, row substitution leaves the right coefficient unchanged. -/
@[simp]
theorem tensorMap_tmul (α : M) (g : P →₀ A) :
    ν.tensorMap (tmul R A α g) =
      tmul R A α (Finsupp.linearCombination A ν.ν g) := by
  exact BalancedTensorProduct.map_tmul ..

variable [IsScalarTower R Aᵐᵒᵖ M]

/-- Continuation on coefficient vectors, obtained by tensoring the free left-module map. -/
def coefficientMap : (P →₀ M) →ₗ[R] (Q →₀ M) :=
  (finsuppScalarRight R A M Q).toLinearMap ∘ₗ ν.tensorMap ∘ₗ
    (finsuppScalarRight R A M P).symm.toLinearMap

/-- The coefficient map is the tensor map under the free-module tensor identification. -/
@[simp]
theorem coefficientMap_finsuppScalarRight (z : BalancedTensorProduct R A M (P →₀ A)) :
    ν.coefficientMap (finsuppScalarRight R A M P z) =
      finsuppScalarRight R A M Q (ν.tensorMap z) := by
  simp [coefficientMap]

/-- On pure tensors, continuation applies row substitution only to the free left factor. -/
theorem coefficientMap_tmul (α : M) (g : P →₀ A) :
    ν.coefficientMap (finsuppScalarRight R A M P (tmul R A α g)) =
      finsuppScalarRight R A M Q (tmul R A α (Finsupp.linearCombination A ν.ν g)) := by
  rw [coefficientMap_finsuppScalarRight, tensorMap_tmul]

/-- The image of an elementary coefficient vector has precisely the specified finite row. -/
theorem coefficientMap_single (x : P) (α : M) :
    ν.coefficientMap (Finsupp.single x α) =
      (ν.ν x).sum (fun y a ↦ Finsupp.single y (op a • α)) := by
  rw [single_eq_finsuppScalarRight_tmul R A M P x α, coefficientMap_tmul]
  simp [finsuppScalarRight_tmul]

/-- The entry formula for an elementary coefficient vector, with no Koszul sign. -/
@[simp]
theorem coefficientMap_single_apply (x : P) (α : M) (y : Q) :
    ν.coefficientMap (Finsupp.single x α) y = op (ν.ν x y) • α := by
  classical
  rw [coefficientMap_single]
  simp only [Finsupp.sum_apply, Finsupp.single_apply, Finsupp.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp_all

/-- The identity continuation induces the identity on coefficient vectors. -/
@[simp]
theorem coefficientMap_refl (m : RowFiniteTwistingCocycle 𝒜 d P indP) (hA : IsDGAlgebra 𝒜 d) :
    (refl m hA).coefficientMap (M := M) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro x α
  ext y
  simp [Finsupp.single_apply, apply_ite op]

/-- Composition of row substitutions induces composition on coefficient vectors. -/
@[simp]
theorem coefficientMap_comp (μ : RowFiniteContinuationCocycle mQ mS) (hA : IsDGAlgebra 𝒜 d) :
    (ν.comp μ hA).coefficientMap (M := M) = μ.coefficientMap ∘ₗ ν.coefficientMap := by
  apply Finsupp.lhom_ext
  intro x α
  rw [single_eq_finsuppScalarRight_tmul R A M P x α, LinearMap.comp_apply,
    coefficientMap_tmul, coefficientMap_tmul,
    coefficientMap_tmul]
  simp only [Finsupp.linearCombination_single, one_smul, comp_ν]

/-- On finite bases, the actual finite-support/function equivalence recovers the original
continuation map, with the same right action and no extra sign. -/
theorem linearEquivFunOnFinite_coefficientMap [Fintype P] [Finite Q] (f : P →₀ M) :
    Finsupp.linearEquivFunOnFinite R M Q (ν.coefficientMap f) =
      continuationMap R M (fun x y ↦ ν.ν x y) (Finsupp.linearEquivFunOnFinite R M P f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x α =>
    rw [Finsupp.linearEquivFunOnFinite_single]
    ext y
    rw [continuationMap_single_apply]
    exact coefficientMap_single_apply ν x α y

variable {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

/-- The continuation map with right-module coefficients preserves total degree. -/
theorem coefficientMap_mem_totalGrading {n : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteTotalGrading ℳ indP n) :
    ν.coefficientMap f ∈ rowFiniteTotalGrading ℳ indQ n := by
  classical
  rw [mem_rowFiniteTotalGrading_iff] at hf ⊢
  intro y
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  rw [Finset.sum_apply']
  simp only [coefficientMap_single_apply]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have := op_smul_mem_of_mem_graded (ν.mem_graded x y) (hf x)
  convert this using 2; ring

variable [DirectSum.Decomposition ℳ]
  {hA : IsDGAlgebra 𝒜 d} {dM : M →ₗ[R] M} (hM : IsDGRightModule hA ℳ dM)

/-- Tensor functoriality gives the chain-map equation with arbitrary DG right coefficients. -/
theorem coefficientMap_differential (f : P →₀ M) :
    mQ.coefficientDifferential hM (ν.coefficientMap f) =
      ν.coefficientMap (mP.coefficientDifferential hM f) := by
  have hgd : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m ∘ₗ
      (Finsupp.linearCombination A ν.ν).restrictScalars R =
      (Finsupp.linearCombination A ν.ν).restrictScalars R ∘ₗ
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m := by
    apply LinearMap.ext
    intro g
    exact ν.linearCombination_differential hA g
  have hd : differential hM (mQ.isDGLeftModule_rowFiniteTwistedDifferential hA) ∘ₗ
      ν.tensorMap = ν.tensorMap ∘ₗ
        differential hM (mP.isDGLeftModule_rowFiniteTwistedDifferential hA) :=
    differential_naturality hM (mP.isDGLeftModule_rowFiniteTwistedDifferential hA)
      hM (mQ.isDGLeftModule_rowFiniteTwistedDifferential hA)
      LinearMap.id ((Finsupp.linearCombination A ν.ν).restrictScalars R)
      (fun _ _ ↦ rfl) (fun a g ↦ by simp only [LinearMap.restrictScalars_apply, map_smul])
      (LinearMap.isHomogeneous_id ℳ) rfl hgd
  rw [← (finsuppScalarRight R A M P).apply_symm_apply f,
    coefficientMap_finsuppScalarRight, mQ.coefficientDifferential_finsuppScalarRight,
    mP.coefficientDifferential_finsuppScalarRight, coefficientMap_finsuppScalarRight]
  exact congrArg (finsuppScalarRight R A M Q)
    (LinearMap.congr_fun hd ((finsuppScalarRight R A M P).symm f))

end Coefficients

end RowFiniteContinuationCocycle

namespace ContinuationCocycle

variable [Fintype P] [Fintype Q]
  {mP : TwistingCocycle 𝒜 d P indP} {mQ : TwistingCocycle 𝒜 d Q indQ}

/-- A finite continuation cocycle defines finite continuation rows for the row-finite models. -/
def toRowFinite (ν : ContinuationCocycle mP mQ) :
    RowFiniteContinuationCocycle mP.toRowFinite mQ.toRowFinite where
  ν x := (Finsupp.linearEquivFunOnFinite R A Q).symm (ν.ν x)
  mem_graded x y := ν.mem_graded x y
  continuation x := by
    apply (RowFiniteContinuationCocycle.continuation_iff _ (fun x y ↦ ν.mem_graded x y) x).mpr
    ext y
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul, TwistingCocycle.toRowFinite_m]
    rw [Finsupp.sum_fintype _ _ (by intro z; simp),
      Finsupp.sum_fintype _ _ (by intro z; simp)]
    simpa only [Finsupp.linearEquivFunOnFinite_symm_apply, TwistingCocycle.toRowFinite_m]
      using ν.continuation x y

@[simp]
theorem toRowFinite_ν (ν : ContinuationCocycle mP mQ) (x : P) (y : Q) :
    ν.toRowFinite.ν x y = ν.ν x y := (rfl)

end ContinuationCocycle

end TauCeti
