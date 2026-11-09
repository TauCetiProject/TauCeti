/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Continuation
public import TauCeti.Algebra.Homology.DG.Twisted.Homotopy
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Homotopies of row-finite twisted free modules

A finite row for each generator extends to a graded left-linear map of degree minus one
by applying the Koszul sign to its coefficient. A parametrized cocycle specifies that the
boundary of this map on generators is the difference of two continuation rows. The DG
Leibniz rule extends this equation to a chain homotopy on the entire free left module,
without any finiteness restriction on the generator sets.

This is the free-module homotopy needed to compare choices of attaching cycles in cellular
DG resolutions. It does not assert that the twisted modules are resolutions. For finite
bases, the signed map and parametrized equation recover `homotopyMap` and
`ParametrizedCocycle`, with the regular algebra as coefficients.

Tensoring with a DG right module transports the homotopy to finite-support coefficient
vectors. Since the signed row map is graded linear of odd degree, the coefficient factor
carries its Koszul sign: `α ⊗ g ↦ (-1)^|α| α ⊗ H g`. The tensor differential then turns the
free-module identity into `D ∘ H + H ∘ D = Ψ¹ - Ψ⁰` on coefficient vectors
(`RowFiniteParametrizedCocycle.coefficientHomotopy_differential`). For finite bases this
coefficient homotopy is the existing `homotopyMap`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4, Definition 1.11.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public noncomputable section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP uQ

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {P : Type uP} {Q : Type uQ} {indP : P → ℤ} {indQ : Q → ℤ}

/-- A row-finite parametrized cocycle between continuation cocycles. Its generator equation
uses the signed extension, so the full chain-homotopy identity is a consequence, not a field. -/
structure RowFiniteParametrizedCocycle
    {mP : RowFiniteTwistingCocycle 𝒜 d P indP}
    {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
    (ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ) where
  /-- The finite homotopy row at each source generator. -/
  h : P → Q →₀ A
  /-- Each entry has the degree of a homotopy between shifted free generators. -/
  mem_graded : ∀ x y, h x y ∈ 𝒜 (indQ y - indP x - 1)
  /-- The boundary equation on source generators. -/
  parametrized : ∀ x,
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (h x) +
      rowFiniteSignedMap (𝒜 := 𝒜) h (mP.m x) = ν₁.ν x - ν₀.ν x

namespace RowFiniteParametrizedCocycle

variable {mP : RowFiniteTwistingCocycle 𝒜 d P indP}
  {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ}

@[ext]
theorem ext {η θ : RowFiniteParametrizedCocycle ν₀ ν₁}
    (hh : ∀ x y, η.h x y = θ.h x y) : η = θ := by
  cases η
  cases θ
  congr
  funext x
  exact Finsupp.ext (hh x)

variable (η : RowFiniteParametrizedCocycle ν₀ ν₁)

/-- The signed map of a parametrized cocycle lowers total degree by one. -/
theorem rowFiniteSignedMap_mem_totalGrading {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 indP n) :
    rowFiniteSignedMap (𝒜 := 𝒜) η.h f ∈ rowFiniteTotalGrading 𝒜 indQ (n - 1) := by
  simpa only [sub_eq_add_neg] using
    TauCeti.rowFiniteSignedMap_mem_totalGrading η.h (k := -1)
      (fun x y ↦ by simpa only [sub_eq_add_neg] using η.mem_graded x y) hf

/-- The generator equation extends to the entire free left module: the signed row map is a
chain homotopy between the two continuation substitutions. -/
theorem rowFiniteSignedMap_differential (hA : IsDGAlgebra 𝒜 d) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m
        (rowFiniteSignedMap (𝒜 := 𝒜) η.h f) +
      rowFiniteSignedMap (𝒜 := 𝒜) η.h
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m f) =
      Finsupp.linearCombination A ν₁.ν f - Finsupp.linearCombination A ν₀.ν f := by
  have key := linearCombination_eq_add_rowFiniteSignedMap
    (mQ.isDGLeftModule_rowFiniteTwistedDifferential hA) mP.m
    (e := fun x ↦ ν₁.ν x - ν₀.ν x) (fun x ↦ (η.parametrized x).symm) f
  rw [← key]
  simp only [Finsupp.linearCombination_apply, smul_sub, Finsupp.sum_sub]

/-- A homogeneous row's Koszul contribution with an odd shifted degree has the opposite sign
from the corresponding index-difference sum. -/
private theorem signedRow_sum_eq_neg {X : Type*} (f : X →₀ A) (g : X → Q →₀ A)
    (i : X → ℤ) {k s : ℤ} (hs : Odd s) (hf : ∀ z, f z ∈ 𝒜 (i z - k + s)) :
    f.sum (fun z a ↦ (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a • g z) =
      -f.sum (fun z a ↦ (k - i z).negOnePow • (a • g z)) := by
  classical
  rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [koszulTwist_one_eq_negOnePow_smul (R := R) (hf z), Int.negOnePow_add,
    Int.negOnePow_odd _ hs, ← Int.negOnePow_neg (k - i z), neg_sub]
  simp

/-- The generator equation expanded into the signed finite-row homotopy equation. -/
theorem parametrized_iff (h : P → Q →₀ A)
    (hh : ∀ x y, h x y ∈ 𝒜 (indQ y - indP x - 1)) (x : P) :
    (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (h x) +
        rowFiniteSignedMap (𝒜 := 𝒜) h (mP.m x) = ν₁.ν x - ν₀.ν x) ↔
      Finsupp.mapRange.linearMap d (h x) = ν₁.ν x - ν₀.ν x +
        (mP.m x).sum (fun z a ↦ (indP x - indP z).negOnePow • (a • h z)) +
        (h x).sum (fun z a ↦ (indP x - indQ z).negOnePow • (a • mQ.m z)) := by
  classical
  -- Both twisting contributions move across the equality with the opposite sign.
  have hD := signedRow_sum_eq_neg (h x) mQ.m indQ (s := -1) (by decide)
    (fun z ↦ by simpa only [sub_eq_add_neg] using hh x z)
  have hH := signedRow_sum_eq_neg (mP.m x) h indP (by decide : Odd (1 : ℤ))
    (mP.mem_graded x)
  rw [rowFiniteTwistedDifferential_apply, rowFiniteSignedMap_apply, hD, hH]
  constructor
  · intro heq
    rw [← heq]
    abel
  · intro heq
    rw [heq]
    abel

section Coefficients

open BalancedTensorProduct

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

/-- The Koszul-signed pairing of a right coefficient with the signed homotopy rows is
balanced: both factors are graded linear of odd degree, and their two signs agree. -/
private theorem koszulTwist_tmul_rowFiniteSignedMap_balanced (a : A) (α : M) (g : P →₀ A) :
    tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 (op a • α))
        (rowFiniteSignedMap (𝒜 := 𝒜) η.h g) =
      tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 α)
        (rowFiniteSignedMap (𝒜 := 𝒜) η.h (a • g)) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp only [op_add, add_smul, map_add, add_tmul, tmul_add, ha, hb]
  | @homogeneous p a =>
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | add α β hα hβ => simp only [smul_add, map_add, add_tmul, hα, hβ]
    | @homogeneous q α =>
      rw [koszulTwist_one_eq_negOnePow_smul (R := R) (op_smul_mem_of_mem_graded a.2 α.2),
        koszulTwist_one_eq_negOnePow_smul (R := R) α.2, rowFiniteSignedMap_smul η.h a.2,
        Int.negOnePow_add, mul_smul]
      simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast,
        smul_tmul, tmul_smul, balance]
      exact smul_comm _ _ _

variable (ℳ) in
/-- The homotopy rows tensored with right coefficients. A coefficient passes through with its
Koszul sign, `α ⊗ g ↦ (-1)^|α| α ⊗ H g`, where `H` is the signed row map. -/
def tensorHomotopy : BalancedTensorProduct R A M (P →₀ A) →ₗ[R]
    BalancedTensorProduct R A M (Q →₀ A) :=
  lift (((BalancedTensorProduct.mk R A).comp
      ((InternalGrading.ofDecomposition ℳ).koszulTwist 1)).compl₂
      (rowFiniteSignedMap (𝒜 := 𝒜) η.h))
    (fun a α g ↦ by
      simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, mk_apply] using
        η.koszulTwist_tmul_rowFiniteSignedMap_balanced a α g)

/-- On pure tensors, the coefficient acquires its Koszul twist and the free factor its signed
homotopy row. -/
@[simp]
theorem tensorHomotopy_tmul (α : M) (g : P →₀ A) :
    η.tensorHomotopy ℳ (tmul R A α g) =
      tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 α)
        (rowFiniteSignedMap (𝒜 := 𝒜) η.h g) := by
  simp [tensorHomotopy]

/-- On a homogeneous coefficient of degree `q`, the Koszul twist is the sign `(-1)^q`. -/
theorem tensorHomotopy_tmul_of_mem {q : ℤ} {α : M} (hα : α ∈ ℳ q) (g : P →₀ A) :
    η.tensorHomotopy ℳ (tmul R A α g) =
      ((q.negOnePow : ℤ) : R) • tmul R A α (rowFiniteSignedMap (𝒜 := 𝒜) η.h g) := by
  rw [tensorHomotopy_tmul, koszulTwist_one_eq_negOnePow_smul (R := R) hα,
    negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast, smul_tmul]

variable [IsScalarTower R Aᵐᵒᵖ M] {hA : IsDGAlgebra 𝒜 d} {dM : M →ₗ[R] M}

/-- The tensored homotopy rows are a chain homotopy between the tensored continuation maps,
for the balanced tensor differentials. -/
theorem tensorHomotopy_differential (hM : IsDGRightModule hA ℳ dM)
    (z : BalancedTensorProduct R A M (P →₀ A)) :
    differential hM (mQ.isDGLeftModule_rowFiniteTwistedDifferential hA) (η.tensorHomotopy ℳ z) +
        η.tensorHomotopy ℳ (differential hM (mP.isDGLeftModule_rowFiniteTwistedDifferential hA) z) =
      ν₁.tensorMap z - ν₀.tensorMap z := by
  have key : differential hM (mQ.isDGLeftModule_rowFiniteTwistedDifferential hA) ∘ₗ
        η.tensorHomotopy ℳ +
      η.tensorHomotopy ℳ ∘ₗ differential hM (mP.isDGLeftModule_rowFiniteTwistedDifferential hA) =
      ν₁.tensorMap - ν₀.tensorMap := by
    refine hom_ext_of_mem (ℳ := ℳ) fun {q α} hα g ↦ ?_
    have hdα : dM α ∈ ℳ (q + 1) := hM.isHomogeneous.map_mem hα
    have hsub (u v : Q →₀ A) : tmul R A α (u - v) = tmul R A α u - tmul R A α v := by
      simpa only [mk_apply] using map_sub (BalancedTensorProduct.mk R A α) u v
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      RowFiniteContinuationCocycle.tensorMap_tmul]
    rw [η.tensorHomotopy_tmul_of_mem hα, map_smul, differential_tmul_of_mem hM _ hα,
      differential_tmul_of_mem hM _ hα, map_add, map_smul, η.tensorHomotopy_tmul_of_mem hdα,
      η.tensorHomotopy_tmul_of_mem hα, ← hsub, ← η.rowFiniteSignedMap_differential hA g,
      tmul_add,
      Int.negOnePow_succ]
    -- The two terms involving `dM α` cancel, and the remaining sign appears twice.
    simp only [Units.val_neg, Int.cast_neg, neg_smul, smul_add, smul_smul, ← Int.cast_mul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]
    abel
  exact LinearMap.congr_fun key z

variable (ℳ) in
/-- The chain homotopy on finite-support coefficient vectors, transported from the tensored
homotopy rows along the free-module tensor identification. -/
def coefficientHomotopy : (P →₀ M) →ₗ[R] (Q →₀ M) :=
  (finsuppScalarRight R A M Q).toLinearMap ∘ₗ η.tensorHomotopy ℳ ∘ₗ
    (finsuppScalarRight R A M P).symm.toLinearMap

/-- The coefficient homotopy is the tensored homotopy under the tensor identification. -/
@[simp]
theorem coefficientHomotopy_finsuppScalarRight (z : BalancedTensorProduct R A M (P →₀ A)) :
    η.coefficientHomotopy ℳ (finsuppScalarRight R A M P z) =
      finsuppScalarRight R A M Q (η.tensorHomotopy ℳ z) := by
  simp [coefficientHomotopy]

/-- The image of an elementary coefficient vector is its homotopy row acting on the
Koszul-twisted coefficient. -/
theorem coefficientHomotopy_single (x : P) (α : M) :
    η.coefficientHomotopy ℳ (Finsupp.single x α) =
      (η.h x).sum fun y a ↦
        Finsupp.single y (op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α) := by
  rw [single_eq_finsuppScalarRight_tmul R A M P x α, coefficientHomotopy_finsuppScalarRight,
    tensorHomotopy_tmul, rowFiniteSignedMap_single_one, finsuppScalarRight_tmul]

/-- The entry formula for an elementary coefficient vector:
`H (α ⊗ x) y = (-1)^|α| α · h x y`, with the sign given by the Koszul twist. -/
@[simp]
theorem coefficientHomotopy_single_apply (x : P) (α : M) (y : Q) :
    η.coefficientHomotopy ℳ (Finsupp.single x α) y =
      op (η.h x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α := by
  rw [single_eq_finsuppScalarRight_tmul R A M P x α, coefficientHomotopy_finsuppScalarRight,
    tensorHomotopy_tmul, rowFiniteSignedMap_single_one, finsuppScalarRight_tmul_apply]

/-- The coefficient homotopy lowers total degree by one. -/
theorem coefficientHomotopy_mem_totalGrading {n : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteTotalGrading ℳ indP n) :
    η.coefficientHomotopy ℳ f ∈ rowFiniteTotalGrading ℳ indQ (n - 1) := by
  classical
  rw [mem_rowFiniteTotalGrading_iff] at hf ⊢
  intro y
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum, Finset.sum_apply']
  simp only [coefficientHomotopy_single_apply]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have hε : (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x) ∈ ℳ (n + indP x) := by
    rw [koszulTwist_one_eq_negOnePow_smul (R := R) (hf x)]
    exact Submodule.smul_of_tower_mem _ _ (hf x)
  have := op_smul_mem_of_mem_graded (η.mem_graded x y) hε
  convert this using 2; ring

/-- **The chain homotopy with DG right coefficients.** The coefficient homotopy of a
row-finite parametrized cocycle satisfies `D ∘ H + H ∘ D = Ψ¹ - Ψ⁰` on finite-support
coefficient vectors, for an arbitrary graded basis. -/
theorem coefficientHomotopy_differential (hM : IsDGRightModule hA ℳ dM) (f : P →₀ M) :
    mQ.coefficientDifferential hM (η.coefficientHomotopy ℳ f) +
        η.coefficientHomotopy ℳ (mP.coefficientDifferential hM f) =
      ν₁.coefficientMap f - ν₀.coefficientMap f := by
  rw [← (finsuppScalarRight R A M P).apply_symm_apply f,
    coefficientHomotopy_finsuppScalarRight, mQ.coefficientDifferential_finsuppScalarRight,
    mP.coefficientDifferential_finsuppScalarRight, coefficientHomotopy_finsuppScalarRight,
    RowFiniteContinuationCocycle.coefficientMap_finsuppScalarRight,
    RowFiniteContinuationCocycle.coefficientMap_finsuppScalarRight, ← map_add, ← map_sub,
    η.tensorHomotopy_differential hM]

/-- For finite bases, the actual finite-support/function equivalence recovers the original
homotopy map, with the same right action and Koszul sign. -/
theorem linearEquivFunOnFinite_coefficientHomotopy [Fintype P] [Finite Q] (f : P →₀ M) :
    Finsupp.linearEquivFunOnFinite R M Q (η.coefficientHomotopy ℳ f) =
      homotopyMap (fun x y ↦ η.h x y) ℳ (Finsupp.linearEquivFunOnFinite R M P f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x α =>
    rw [Finsupp.linearEquivFunOnFinite_single]
    ext y
    simp [Pi.single_apply, apply_ite]

end Coefficients

end RowFiniteParametrizedCocycle

/-- For finite bases the signed extension is precisely the original homotopy map, with
regular algebra coefficients, through the actual finite-support/function equivalence. -/
theorem linearEquivFunOnFinite_rowFiniteSignedMap [Fintype P] [Finite Q]
    (h : P → Q →₀ A) (f : P →₀ A) :
    Finsupp.linearEquivFunOnFinite R A Q (rowFiniteSignedMap (𝒜 := 𝒜) h f) =
      homotopyMap (fun x y ↦ h x y) 𝒜 (Finsupp.linearEquivFunOnFinite R A P f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q a =>
      rw [rowFiniteSignedMap_single h x a.2, Finsupp.linearEquivFunOnFinite_single]
      ext y
      simp [homotopyMap_single_apply _ x a.2, MulOpposite.smul_eq_mul_unop]
    | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]

namespace ParametrizedCocycle

variable [Fintype P] [Fintype Q]
  {mP : TwistingCocycle 𝒜 d P indP} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {ν₀ ν₁ : ContinuationCocycle mP mQ}

/-- Regard a finite parametrized cocycle as finite homotopy rows on the row-finite modules. -/
def toRowFinite (η : ParametrizedCocycle ν₀ ν₁) :
    RowFiniteParametrizedCocycle ν₀.toRowFinite ν₁.toRowFinite where
  h x := (Finsupp.linearEquivFunOnFinite R A Q).symm (η.h x)
  mem_graded := η.mem_graded
  parametrized x := by
    apply (RowFiniteParametrizedCocycle.parametrized_iff _ η.mem_graded x).mpr
    ext y
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      Finsupp.add_apply, Finsupp.sub_apply, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Finsupp.sum_fintype _ _ (by intro z; simp),
      Finsupp.sum_fintype _ _ (by intro z; simp)]
    simpa only [ContinuationCocycle.toRowFinite_ν, TwistingCocycle.toRowFinite_m,
      Finsupp.linearEquivFunOnFinite_symm_apply] using η.parametrized x y

@[simp]
theorem toRowFinite_h (η : ParametrizedCocycle ν₀ ν₁) (x : P) (y : Q) :
    η.toRowFinite.h x y = η.h x y := (rfl)

end ParametrizedCocycle

end TauCeti
