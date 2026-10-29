/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Complex
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Finsupp
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Row-finite twisted complexes with DG coefficients

A row-finite twisting cocycle on an arbitrary graded basis `P` gives a twisted complex
with coefficients in any DG right module `M`. Its underlying module is `P →₀ M`, not
the unrestricted product. The differential is transported from `M ⊗_A K_m`, using the
free left DG module `K_m` and the balanced tensor differential. Thus square-zero follows
from the tensor construction, rather than a second Maurer–Cartan sign calculation.

The characteristic formula on a homogeneous elementary vector is
`D(single x α) = single x (dM α) + (-1)^|α| ∑_y single y (α · m x y)`,
where the sum is over the finite support of the row. The tensor identification preserves
total degree. For finite `P`, the finite-support/function equivalence recovers the existing
finite twisted differential with the same right action and Koszul sign.

These are ordinary tensor products; no semi-free filtration, resolution or derived
comparison is asserted.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public noncomputable section

open CategoryTheory DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {ind : P → ℤ}

namespace BalancedTensorProduct

attribute [local instance] tensorGradedRight tensorGradedLeft

local notation "coefficientGrading" => grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
  (InternalGrading.ofDecomposition (rowFiniteTotalGrading 𝒜 ind))

/-- The free-module tensor identification preserves total degree. -/
theorem finsuppScalarRight_mem_rowFiniteTotalGrading {n : ℤ}
    {z : BalancedTensorProduct R A M (P →₀ A)} (hz : z ∈ (coefficientGrading).piece n) :
    finsuppScalarRight R A M P z ∈ rowFiniteTotalGrading ℳ ind n := by
  rw [grading_piece_eq_iSup (𝒜 := 𝒜)] at hz
  refine (iSup_le fun q ↦ Submodule.map₂_le.mpr fun α hα g hg ↦ ?_ :
    _ ≤ (rowFiniteTotalGrading ℳ ind n).comap (finsuppScalarRight R A M P).toLinearMap) hz
  rw [InternalGrading.ofDecomposition_piece] at hα hg
  rw [mem_rowFiniteTotalGrading_iff] at hg
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, mk_apply, mem_rowFiniteTotalGrading_iff]
  intro y
  rw [finsuppScalarRight_tmul_apply]
  have := op_smul_mem_of_mem_graded (hg y) hα
  convert this using 2
  ring

/-- The inverse tensor identification preserves total degree, even for an infinite basis. -/
theorem finsuppScalarRight_symm_mem_grading {n : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteTotalGrading ℳ ind n) :
    (finsuppScalarRight R A M P).symm f ∈ (coefficientGrading).piece n := by
  classical
  rw [mem_rowFiniteTotalGrading_iff] at hf
  rw [finsuppScalarRight_symm_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have hsingle : Finsupp.single x (1 : A) ∈ rowFiniteTotalGrading 𝒜 ind (-ind x) := by
    rw [mem_rowFiniteTotalGrading_iff]
    intro y
    by_cases hxy : x = y
    · subst y
      simpa using SetLike.one_mem_graded 𝒜
    · simp [Finsupp.single_eq_of_ne (Ne.symm hxy)]
  have := tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
    (InternalGrading.ofDecomposition (rowFiniteTotalGrading 𝒜 ind))
    (by simpa only [InternalGrading.ofDecomposition_piece] using hf x)
    (by simpa only [InternalGrading.ofDecomposition_piece] using hsingle)
  simpa only [add_neg_cancel_right] using this

/-- The tensor grading is exactly the finite-support total grading under `finsuppScalarRight`. -/
theorem map_grading_piece_eq_rowFiniteTotalGrading (n : ℤ) :
    ((coefficientGrading).piece n).map (finsuppScalarRight R A M P).toLinearMap =
      rowFiniteTotalGrading ℳ ind n := by
  ext f
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact finsuppScalarRight_mem_rowFiniteTotalGrading hz
  · intro hf
    exact ⟨_, finsuppScalarRight_symm_mem_grading hf,
      (finsuppScalarRight R A M P).apply_symm_apply f⟩

end BalancedTensorProduct

namespace RowFiniteTwistingCocycle

open BalancedTensorProduct

variable {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}
  (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)

/-- The row-finite twisted differential with right-module coefficients, transported from
`M ⊗_A K_m` onto finite-support coefficient vectors. -/
def coefficientDifferential : (P →₀ M) →ₗ[R] (P →₀ M) :=
  (finsuppScalarRight R A M P).toLinearMap ∘ₗ
    differential hM (m.isDGLeftModule_rowFiniteTwistedDifferential hA) ∘ₗ
      (finsuppScalarRight R A M P).symm.toLinearMap

/-- The specified tensor identification intertwines the two differentials. -/
@[simp]
theorem coefficientDifferential_finsuppScalarRight (z : BalancedTensorProduct R A M (P →₀ A)) :
    m.coefficientDifferential hM (finsuppScalarRight R A M P z) =
      finsuppScalarRight R A M P
        (differential hM (m.isDGLeftModule_rowFiniteTwistedDifferential hA) z) := by
  simp [coefficientDifferential]

/-- On a homogeneous elementary vector the differential uses only its finite row, with the
right-module action and the Koszul sign of the coefficient. -/
theorem coefficientDifferential_single (x : P) {q : ℤ} {α : M} (hα : α ∈ ℳ q) :
    m.coefficientDifferential hM (Finsupp.single x α) =
      Finsupp.single x (dM α) + q.negOnePow •
        (m.m x).sum (fun y a ↦ Finsupp.single y (op a • α)) := by
  classical
  have he : Finsupp.single x α = finsuppScalarRight R A M P (tmul R A α (Finsupp.single x 1)) := by
    simp
  rw [he, coefficientDifferential_finsuppScalarRight,
    differential_tmul_of_mem hM (m.isDGLeftModule_rowFiniteTwistedDifferential hA) hα,
    m.differential_single_one hA]
  rw [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
  simp

/-- The coefficient differential squares to zero by the balanced tensor differential law. -/
@[simp]
theorem coefficientDifferential_sq_zero (f : P →₀ M) :
    m.coefficientDifferential hM (m.coefficientDifferential hM f) = 0 := by
  simp [coefficientDifferential]

/-- The coefficient differential increases total degree by one. -/
theorem isHomogeneous_coefficientDifferential :
    LinearMap.IsHomogeneous (m.coefficientDifferential hM)
      (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ ind) 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro n f hf
  rw [← (finsuppScalarRight R A M P).apply_symm_apply f,
    coefficientDifferential_finsuppScalarRight]
  exact finsuppScalarRight_mem_rowFiniteTotalGrading
    ((isHomogeneous_differential hM (m.isDGLeftModule_rowFiniteTwistedDifferential hA)).map_mem
      (finsuppScalarRight_symm_mem_grading hf))

/-- The row-finite twisted complex with coefficients in a DG right module, in total
cohomological degree. It has no finiteness restriction on its basis. -/
def coefficientCochainComplex : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (rowFiniteTotalGrading ℳ ind) (m.coefficientDifferential hM)
    (m.isHomogeneous_coefficientDifferential hM) (fun _ f ↦ m.coefficientDifferential_sq_zero hM f)

/-- The terms of the coefficient complex are the finite-support total-degree pieces. -/
@[simp]
theorem coefficientCochainComplex_X (n : ℤ) :
    (m.coefficientCochainComplex hM).X n = ModuleCat.of R (rowFiniteTotalGrading ℳ ind n) := by
  rw [coefficientCochainComplex, gradedCochainComplex_X]

/-- The complex differential is the restriction of the coefficient differential to the
appropriate total-degree pieces. -/
@[simp]
theorem coefficientCochainComplex_d (n : ℤ) :
    (m.coefficientCochainComplex hM).d n (n + 1) =
      eqToHom (m.coefficientCochainComplex_X hM n) ≫
        ModuleCat.ofHom ((m.coefficientDifferential hM).restrict
          (fun _ hf ↦ (m.isHomogeneous_coefficientDifferential hM).map_mem hf)) ≫
        eqToHom (m.coefficientCochainComplex_X hM (n + 1)).symm := by
  unfold coefficientCochainComplex
  rw [gradedCochainComplex_d]

/-- For finite `P`, the finite-support/function equivalence intertwines the coefficient
differential with the original finite twisted differential. -/
theorem linearEquivFunOnFinite_coefficientDifferential [Fintype P] (f : P →₀ M) :
    Finsupp.linearEquivFunOnFinite R M P (m.coefficientDifferential hM f) =
      twistedDifferential (fun x y ↦ m.m x y) ℳ dM
        (Finsupp.linearEquivFunOnFinite R M P f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x α =>
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous q α =>
      rw [m.coefficientDifferential_single hM x α.2, Finsupp.linearEquivFunOnFinite_single,
        twistedDifferential_single (fun x y ↦ m.m x y) dM x α.2]
      ext y
      simp [Finsupp.single_apply, Pi.single_apply, Finsupp.sum_fintype, eq_comm]
    | add α β hα hβ => simp only [Finsupp.single_add, map_add, hα, hβ]

end RowFiniteTwistingCocycle

end TauCeti
