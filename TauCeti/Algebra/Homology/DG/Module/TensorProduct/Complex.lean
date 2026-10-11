/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Differential
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# The cochain complex of a balanced tensor product of DG modules

The balanced tensor differential raises total degree by one. Together with its square-zero
law, this equips the tensor product of a right and a left DG module with an ordinary cochain
complex. Its homogeneous pure tensors have differential
`d(m ⊗ n) = dM(m) ⊗ n + (-1)^|m| m ⊗ dN(n)`.

The construction combines the quotient grading with the existing balanced differential and
`gradedCochainComplex`. It is underived and requires no flatness assumption.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

namespace TauCeti.BalancedTensorProduct

open CategoryTheory

variable {R A M N : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA} {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul 𝒜 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}

-- Use the characteristic piece equation, since `ofDecomposition` is opaque across modules.
local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition ℳ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul 𝒜 (InternalGrading.ofDecomposition 𝒩).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- The differential of the balanced tensor product has cohomological degree one. -/
theorem isHomogeneous_differential (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA 𝒩 dN) :
    LinearMap.IsHomogeneous (differential hM hN)
      (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      1 := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  rw [grading_piece_eq_iSup (𝒜 := 𝒜)] at hz
  refine (iSup_le fun q ↦ Submodule.map₂_le.mpr fun m hm n hn ↦ ?_ :
    _ ≤ ((grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece (p + 1)).comap (differential hM hN)) hz
  rw [InternalGrading.ofDecomposition_piece] at hm hn
  rw [Submodule.mem_comap, mk_apply, differential_tmul_of_mem hM hN hm]
  apply Submodule.add_mem
  · have hmem := tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hM.isHomogeneous.map_mem hm)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hn)
    simpa only [show q + 1 + (p - q) = p + 1 by omega] using hmem
  · apply Submodule.smul_mem
    have hmem := tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hm)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hN.isHomogeneous.map_mem hn)
    simpa only [show q + (p - q + 1) = p + 1 by omega] using hmem

/-- The ordinary balanced tensor product of a right and a left DG module, as a cochain
complex of ground-ring modules. -/
noncomputable def cochainComplex (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA 𝒩 dN) : CochainComplex (ModuleCat R) ℤ :=
  gradedCochainComplex
    (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece
    (differential hM hN) (isHomogeneous_differential hM hN)
    (fun _ x ↦ differential_sq_zero hM hN x)

/-- The degree-`p` term is the degree-`p` part of the balanced tensor product. -/
@[simp]
theorem cochainComplex_X (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA 𝒩 dN) (p : ℤ) :
    (cochainComplex hM hN).X p = ModuleCat.of R
      ((grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece p) := by
  rw [cochainComplex, gradedCochainComplex_X]

/-- The degree-`p` differential is the restriction of the balanced tensor differential,
transported along the canonical identifications of the complex terms. -/
@[simp]
theorem cochainComplex_d (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA 𝒩 dN) (p : ℤ) :
    (cochainComplex hM hN).d p (p + 1) =
      eqToHom (cochainComplex_X hM hN p) ≫
        ModuleCat.ofHom ((differential hM hN).restrict
          (fun _ hz ↦ (isHomogeneous_differential hM hN).map_mem hz)) ≫
        eqToHom (cochainComplex_X hM hN (p + 1)).symm := by
  unfold cochainComplex
  rw [gradedCochainComplex_d]

/-- On a homogeneous element, the complex differential is the balanced tensor differential,
using the canonical identifications of the complex terms with the grading pieces. -/
theorem cochainComplex_d_apply (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA 𝒩 dN) (p : ℤ)
    (z : (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece p) :
    ((eqToHom (cochainComplex_X hM hN (p + 1)))
      ((cochainComplex hM hN).d p (p + 1)
        ((eqToHom (cochainComplex_X hM hN p).symm) z)) :
      BalancedTensorProduct R A M N) = differential hM hN z := by
  unfold cochainComplex
  rw [gradedCochainComplex_d_apply]

end TauCeti.BalancedTensorProduct
