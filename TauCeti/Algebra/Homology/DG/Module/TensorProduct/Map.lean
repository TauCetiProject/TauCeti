/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Complex

/-!
# Chain maps on balanced tensor products of DG modules

Equivariant degree-zero chain maps in the two factors induce a chain map on their ordinary
balanced tensor product. This makes the balanced tensor complex functorial, with no flatness
hypothesis. The induced map sends `m ⊗ n` to `f(m) ⊗ g(n)`; there is no Koszul sign because
both maps have degree zero. Identity and composition agree with the corresponding operations
on cochain complexes.

The maps are supplied as ground-ring linear maps with equivariance, degree, and differential
compatibility proofs. Thus the construction applies to either module morphisms or bimodule
morphisms without introducing another bundled morphism type. The module carriers live in a
common universe, so the maps act on the existing, unlifted balanced tensor complexes.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.BalancedTensorProduct

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

-- Transport graded actions along the public piece formula for `ofDecomposition`.
/-- Transport the source right action to the packaged internal grading. -/
local instance mapGradedRightSource :
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (InternalGrading.ofDecomposition ℳ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Transport the source left action to the packaged internal grading. -/
local instance mapGradedLeftSource :
    SetLike.GradedSMul 𝒜 (InternalGrading.ofDecomposition 𝒩).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Transport the target right action to the packaged internal grading. -/
local instance mapGradedRightTarget :
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (InternalGrading.ofDecomposition ℳ').piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Transport the target left action to the packaged internal grading. -/
local instance mapGradedLeftTarget :
    SetLike.GradedSMul 𝒜 (InternalGrading.ofDecomposition 𝒩').piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

variable (f : M →ₗ[R] M') (g : N →ₗ[R] N')
  (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
  (hg : ∀ (a : A) n, g (a • n) = a • g n)
  (hf₀ : LinearMap.IsHomogeneous f ℳ ℳ' 0)
  (hg₀ : LinearMap.IsHomogeneous g 𝒩 𝒩' 0)
  (hfd : dM' ∘ₗ f = f ∘ₗ dM) (hgd : dN' ∘ₗ g = g ∘ₗ dN)

include hf₀ hg₀ in
omit [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N]
  [IsScalarTower R Aᵐᵒᵖ M'] [IsScalarTower R A N'] in
private theorem map_mem_piece {p : ℤ} {z : BalancedTensorProduct R A M N}
    (hz : z ∈ (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece p) :
    map f g hf hg z ∈ (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ')
      (InternalGrading.ofDecomposition 𝒩')).piece p := by
  have hf' : LinearMap.IsHomogeneous f (InternalGrading.ofDecomposition ℳ).piece
      (InternalGrading.ofDecomposition ℳ').piece 0 := by
    simpa only [InternalGrading.ofDecomposition_piece] using hf₀
  have hg' : LinearMap.IsHomogeneous g (InternalGrading.ofDecomposition 𝒩).piece
      (InternalGrading.ofDecomposition 𝒩').piece 0 := by
    simpa only [InternalGrading.ofDecomposition_piece] using hg₀
  simpa only [add_zero] using
    (isHomogeneous_map (𝒜 := 𝒜) _ _ _ _ f g hf hg hf' hg').map_mem hz

/-- Equivariant degree-zero chain maps induce a map of ordinary balanced tensor complexes. -/
noncomputable def cochainComplexMap : cochainComplex hM hN ⟶ cochainComplex hM' hN' := by
  refine CochainComplex.ofHom (fun p ↦ eqToHom (cochainComplex_X hM hN p) ≫
    ModuleCat.ofHom ((map f g hf hg).restrict
      (fun _ hz ↦ map_mem_piece f g hf hg hf₀ hg₀ hz)) ≫
    eqToHom (cochainComplex_X hM' hN' p).symm) ?_
  intro p
  simp only [cochainComplex_d, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  simp only [← Category.assoc, cancel_mono]
  simp only [Category.assoc, cancel_epi]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.coe_restrict_apply] using
    LinearMap.congr_fun (differential_naturality hM hN hM' hN' f g hf hg hf₀ hfd hgd) z

private theorem cochainComplexMap_f (p : ℤ) :
    (cochainComplexMap hM hN hM' hN' f g hf hg hf₀ hg₀ hfd hgd).f p =
      eqToHom (cochainComplex_X hM hN p) ≫
        ModuleCat.ofHom ((map f g hf hg).restrict
          (fun _ hz ↦ map_mem_piece f g hf hg hf₀ hg₀ hz)) ≫
        eqToHom (cochainComplex_X hM' hN' p).symm := (rfl)

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
  rw [cochainComplexMap_f]
  simp only [← CategoryTheory.comp_apply, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
  -- After cancelling transports, evaluation is just the subtype-valued restricted map.
  rfl

/-- Tensoring the identity maps gives the identity chain map. -/
@[simp]
theorem cochainComplexMap_id :
    cochainComplexMap hM hN hM hN LinearMap.id LinearMap.id
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (LinearMap.isHomogeneous_id ℳ) (LinearMap.isHomogeneous_id 𝒩) rfl rfl =
        𝟙 (cochainComplex hM hN) := by
  apply HomologicalComplex.hom_ext
  intro p
  have hid : ((map (A := A) (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)).restrict
        (fun _ hz ↦ map_mem_piece (𝒜 := 𝒜) (p := p) LinearMap.id LinearMap.id (fun _ _ ↦ rfl)
          (fun _ _ ↦ rfl) (LinearMap.isHomogeneous_id ℳ)
          (LinearMap.isHomogeneous_id 𝒩) hz)) = LinearMap.id := by
    ext z
    simp
  simp only [cochainComplexMap_f, hid, ModuleCat.ofHom_id, Category.id_comp,
    eqToHom_trans, eqToHom_refl, HomologicalComplex.id_f]

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
      (by rw [← LinearMap.comp_assoc, hf'd, LinearMap.comp_assoc, hfd,
        LinearMap.comp_assoc])
      (by rw [← LinearMap.comp_assoc, hg'd, LinearMap.comp_assoc, hgd,
        LinearMap.comp_assoc]) =
        cochainComplexMap hM hN hM' hN' f g hf hg hf₀ hg₀ hfd hgd ≫
          cochainComplexMap hM' hN' hM'' hN'' f' g' hf' hg' hf'₀ hg'₀ hf'd hg'd := by
  apply HomologicalComplex.hom_ext
  intro p
  simp only [HomologicalComplex.comp_f, cochainComplexMap_f, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc, cancel_mono]
  simp only [Category.assoc, cancel_epi]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.coe_restrict_apply]
  exact LinearMap.congr_fun (map_comp f g f' g' hf hg hf' hg') z

end Composition

end TauCeti.BalancedTensorProduct
