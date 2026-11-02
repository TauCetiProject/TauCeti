/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Differential
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading.Basic
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# The cochain complex of a balanced tensor product of DG modules

The balanced tensor differential raises total degree by one. Together with its square-zero
law, this equips the tensor product of a right and a left DG module with an ordinary cochain
complex. Its homogeneous pure tensors have differential
`d(m ⊗ n) = dM(m) ⊗ n + (-1)^|m| m ⊗ dN(n)`.

The construction combines the quotient grading with the existing balanced differential and
`gradedCochainComplex`. It is underived and requires no flatness assumption.

Equivariant degree-zero chain maps in the two factors induce a chain map of balanced tensor
complexes (`TauCeti.BalancedTensorProduct.cochainComplexMap`), sending `m ⊗ n` to `f(m) ⊗ g(n)`;
there is no Koszul sign because both maps have degree zero. The maps are supplied as ground-ring
linear maps with equivariance, degree, and differential compatibility proofs, so the
construction applies to module and bimodule morphisms alike. Identity and composition agree with
the corresponding operations on cochain complexes.

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

attribute [local instance] tensorGradedRight tensorGradedLeft

omit [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N] in
open MulOpposite in
/-- The tensor differential built from two graded Leibniz rules has cohomological degree one
when both factor differentials raise degree by one. -/
theorem isHomogeneous_leibnizDifferential
    (hM : ∀ {q : ℤ} {x : M}, x ∈ ℳ q → ∀ a : A,
      dM (op a • x) = op a • dM x + q.negOnePow • (op (dA a) • x))
    (hN : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N,
      dN (a • x) = dA a • x + p.negOnePow • (a • dN x))
    (hMd : LinearMap.IsHomogeneous dM ℳ ℳ 1) (hNd : LinearMap.IsHomogeneous dN 𝒩 𝒩 1) :
    LinearMap.IsHomogeneous (leibnizDifferential hM hN)
      (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      1 := by
  refine isHomogeneous_of_tmul (𝒜 := 𝒜) _ _ _ _ 1 fun {q p} {m n} hm hn ↦ ?_
  rw [InternalGrading.ofDecomposition_piece] at hm hn
  rw [leibnizDifferential_tmul_of_mem hM hN hm]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · have hmem := tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hMd.map_mem hm)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hn)
    simpa only [add_right_comm] using hmem
  · have hmem := tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hm)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hNd.map_mem hn)
    simpa only [add_assoc] using hmem

/-- The differential of the balanced tensor product has cohomological degree one. -/
theorem isHomogeneous_differential (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA 𝒩 dN) :
    LinearMap.IsHomogeneous (differential hM hN)
      (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      1 := by
  rw [differential_eq_leibnizDifferential]
  exact isHomogeneous_leibnizDifferential hM.leibniz hN.leibniz hM.isHomogeneous hN.isHomogeneous

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

/-! ### Maps of balanced tensor complexes -/

namespace TauCeti.BalancedTensorProduct

open CategoryTheory MulOpposite

universe uR uA u

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA}
  {M N M' N' : Type u}
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M'] [IsScalarTower R Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
  {ℳ' : ℤ → Submodule R M'} {𝒩' : ℤ → Submodule R N'}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [DirectSum.Decomposition ℳ'] [DirectSum.Decomposition 𝒩']
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul 𝒜 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ']
  [SetLike.GradedSMul 𝒜 𝒩']
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}
  {dM' : M' →ₗ[R] M'} {dN' : N' →ₗ[R] N'}
  (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA 𝒩 dN)
  (hM' : IsDGRightModule hA ℳ' dM') (hN' : IsDGLeftModule hA 𝒩' dN')

attribute [local instance] tensorGradedRight tensorGradedLeft

/-- Equivariant degree-zero chain maps induce a map of ordinary balanced tensor complexes,
sending `m ⊗ n` to `f m ⊗ g n`. -/
noncomputable def cochainComplexMap (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m) (hg : ∀ (a : A) n, g (a • n) = a • g n)
    (hf₀ : LinearMap.IsHomogeneous f ℳ ℳ' 0) (hg₀ : LinearMap.IsHomogeneous g 𝒩 𝒩' 0)
    (hfd : dM' ∘ₗ f = f ∘ₗ dM) (hgd : dN' ∘ₗ g = g ∘ₗ dN) :
    cochainComplex hM hN ⟶ cochainComplex hM' hN' :=
  gradedCochainComplexHom (map f g hf hg) (isHomogeneous_map_grading f g hf hg hf₀ hg₀)
    (differential_naturality hM hN hM' hN' f g hf hg hf₀ hfd hgd)

variable (f : M →ₗ[R] M') (g : N →ₗ[R] N')
  (hf : ∀ (a : A) m, f (op a • m) = op a • f m) (hg : ∀ (a : A) n, g (a • n) = a • g n)
  (hf₀ : LinearMap.IsHomogeneous f ℳ ℳ' 0) (hg₀ : LinearMap.IsHomogeneous g 𝒩 𝒩' 0)
  (hfd : dM' ∘ₗ f = f ∘ₗ dM) (hgd : dN' ∘ₗ g = g ∘ₗ dN)

/-- In the canonical identifications of the complex terms with their degree pieces,
the induced map acts by the ordinary balanced tensor map. -/
@[simp]
theorem cochainComplexMap_f_apply (p : ℤ)
    (z : (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece p) :
    (eqToHom (cochainComplex_X hM' hN' p)
      ((cochainComplexMap hM hN hM' hN' f g hf hg hf₀ hg₀ hfd hgd).f p
        ((eqToHom (cochainComplex_X hM hN p).symm) z)) :
      BalancedTensorProduct R A M' N') = map f g hf hg z := by
  unfold cochainComplexMap cochainComplex
  exact gradedCochainComplexHom_f_apply _ _ _ p z

/-- Tensoring the identity maps gives the identity chain map. -/
@[simp]
theorem cochainComplexMap_id :
    cochainComplexMap hM hN hM hN LinearMap.id LinearMap.id
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (LinearMap.isHomogeneous_id ℳ) (LinearMap.isHomogeneous_id 𝒩) rfl rfl =
        𝟙 (cochainComplex hM hN) := by
  unfold cochainComplexMap cochainComplex
  rw [← gradedCochainComplexHom_id]
  congr 1
  exact map_id

section Composition

variable {M'' N'' : Type u}
  [AddCommGroup M''] [Module R M''] [Module Aᵐᵒᵖ M''] [IsScalarTower R Aᵐᵒᵖ M'']
  [AddCommGroup N''] [Module R N''] [Module A N''] [IsScalarTower R A N'']
  {ℳ'' : ℤ → Submodule R M''} {𝒩'' : ℤ → Submodule R N''}
  [DirectSum.Decomposition ℳ''] [DirectSum.Decomposition 𝒩'']
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ'']
  [SetLike.GradedSMul 𝒜 𝒩'']
  {dM'' : M'' →ₗ[R] M''} {dN'' : N'' →ₗ[R] N''}
  (hM'' : IsDGRightModule hA ℳ'' dM'') (hN'' : IsDGLeftModule hA 𝒩'' dN'')
  (f' : M' →ₗ[R] M'') (g' : N' →ₗ[R] N'')
  (hf' : ∀ (a : A) m, f' (op a • m) = op a • f' m)
  (hg' : ∀ (a : A) n, g' (a • n) = a • g' n)
  (hf'₀ : LinearMap.IsHomogeneous f' ℳ' ℳ'' 0)
  (hg'₀ : LinearMap.IsHomogeneous g' 𝒩' 𝒩'' 0)
  (hf'd : dM'' ∘ₗ f' = f' ∘ₗ dM') (hg'd : dN'' ∘ₗ g' = g' ∘ₗ dN')

/-- Tensoring preserves composition of degree-zero equivariant chain maps.

The simp rule combines induced maps, so the intermediate DG-module data can be inferred
from the composition. -/
@[simp ←]
theorem cochainComplexMap_comp :
    cochainComplexMap hM hN hM'' hN'' (f' ∘ₗ f) (g' ∘ₗ g)
      (fun a m ↦ by simp only [LinearMap.comp_apply, hf, hf'])
      (fun a n ↦ by simp only [LinearMap.comp_apply, hg, hg'])
      (by simpa only [add_zero] using hf'₀.comp hf₀)
      (by simpa only [add_zero] using hg'₀.comp hg₀)
      (LinearMap.comp_comm_comp hf'd hfd) (LinearMap.comp_comm_comp hg'd hgd) =
        cochainComplexMap hM hN hM' hN' f g hf hg hf₀ hg₀ hfd hgd ≫
          cochainComplexMap hM' hN' hM'' hN'' f' g' hf' hg' hf'₀ hg'₀ hf'd hg'd := by
  unfold cochainComplexMap cochainComplex
  rw [← gradedCochainComplexHom_comp]
  congr 1
  exact map_comp f g f' g' hf hg hf' hg'

end Composition

end TauCeti.BalancedTensorProduct
