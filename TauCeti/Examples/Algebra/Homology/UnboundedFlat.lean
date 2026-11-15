/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Resolution
public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import TauCeti.Algebra.Homology.TotallyAcyclic.Basic
public import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Flat.Basic

/-!
# An unbounded acyclic free complex which is not K-flat

The complex with `ℤ/4` in every integer degree and differential multiplication by `2`
is acyclic. Nevertheless, tensoring it with the discrete module `ℤ/2` produces a complex
with `ℤ/2` in every degree and zero differential. Thus even an acyclic complex of finite
free modules need not be K-flat when it is unbounded.

We use `TauCeti.alternatingMulRightComplex` for the complex, and the existing single-row
tensor comparison to calculate its tensor with the discrete residue module. K-flat
resolutions and Koszul symmetry show that an acyclic K-flat model would give an acyclic
tensor instead.

## References

* The Stacks Project, More on Algebra, Section 15.60 (Tag 06XZ), K-flat complexes.
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.UnboundedFlat

/-- Reduction modulo `2` makes `ℤ/2` an algebra over `ℤ/4`. -/
local instance residueAlgebra : Algebra (ZMod 4) (ZMod 2) :=
  ZMod.algebra' (ZMod 2) 2 (by decide)

/-- The residue module `ℤ/2` over `ℤ/4`, with the reduction scalar action. -/
abbrev residue : ModuleCat (ZMod 4) := ModuleCat.of (ZMod 4) (ZMod 2)

/-- The unbounded complex `⋯ → ℤ/4 → ℤ/4 → ⋯` with every differential equal to `2`. -/
abbrev complex : CochainComplex (ModuleCat (ZMod 4)) ℤ :=
  alternatingMulRightComplex (2 : ZMod 4) 2 (by decide) (by decide)

-- The existing instances already recognize every term as finite free, and hence flat.
example (i : ℤ) : Module.Free (ZMod 4) (complex.X i) := inferInstance

example (i : ℤ) : Module.Finite (ZMod 4) (complex.X i) := inferInstance

example (i : ℤ) : Module.Flat (ZMod 4) (complex.X i) := inferInstance

/-- The complex is acyclic: in `ℤ/4`, the annihilator and the image of `2` coincide. -/
theorem acyclic_complex : complex.Acyclic := by
  have h : ∀ x : ZMod 4, x * 2 = 0 ↔ ∃ y, y * 2 = x := by decide
  exact (isTotallyAcyclic_alternatingMulRightComplex
    (a := (2 : ZMod 4)) (b := 2) h h
    (by simpa only [mul_comm] using h) (by simpa only [mul_comm] using h)).acyclic

/-- The termwise tensor of the complex with its residue module. -/
def residueTensor : CochainComplex (ModuleCat (ZMod 4)) ℤ :=
  ((tensorLeft residue).mapHomologicalComplex (.up ℤ)).obj complex

/-- Reduction kills every differential of the complex. -/
@[simp]
theorem residueTensor_d (i j : ℤ) : residueTensor.d i j = 0 := by
  by_cases hij : i + 1 = j
  · subst j
    rw [residueTensor, Functor.mapHomologicalComplex_obj_d,
      alternatingMulRightComplex_d _ _ rfl]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [ite_self, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      curriedTensor_obj_map, ModuleCat.hom_whiskerLeft, ModuleCat.hom_ofHom,
      ModuleCat.hom_zero, LinearMap.zero_apply]
    have hx : (2 : ZMod 4) • x = 0 := by
      exact (by decide : ∀ x : ZMod 2, (2 : ZMod 4) • x = 0) x
    rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply]
    simpa [smul_eq_mul, mul_comm, hx] using
      (TensorProduct.smul_tmul (2 : ZMod 4) x y).symm
  · rw [residueTensor.shape i j hij]

/-- The ordinary tensor has residue-field cohomology in every integer degree. -/
def residueTensorHomologyIso (i : ℤ) : residueTensor.homology i ≅ residue :=
  residueTensor.isoHomologyι i (i + 1) (by simp) (residueTensor_d _ _) ≪≫
    (residueTensor.pOpcyclesIso (i - 1) i (by simp) (residueTensor_d _ _)).symm ≪≫
    ρ_ residue

/-- The ordinary tensor is not acyclic in any degree. -/
theorem not_exactAt_residueTensor (i : ℤ) : ¬ residueTensor.ExactAt i := by
  intro h
  have hz := ((exactAt_iff_isZero_homology _ _).1 h).of_iso
    (residueTensorHomologyIso i).symm
  have h01 := congrArg (fun f : residue ⟶ residue ↦ f.hom (1 : ZMod 2))
    (hz.eq_of_src (𝟙 residue) 0)
  exact (by decide : (1 : ZMod 2) ≠ 0) h01

/-- The single-row comparison identifies the total tensor with the termwise reduction. -/
def tensorResidueIso :
    (single _ (.up ℤ) 0).obj residue ⊗ complex ≅ residueTensor :=
  ((curriedTensor (ModuleCat (ZMod 4))).mapBifunctorSingleRowZeroNatIso residue).app complex

/-- Termwise freeness of this unbounded acyclic complex does not imply K-flatness. -/
theorem not_isKFlat_complex : ¬ complex.IsKFlat := by
  intro hK
  let N := (single (ModuleCat (ZMod 4)) (.up ℤ) 0).obj residue
  obtain ⟨P, π, hπ, hP⟩ := CochainComplex.exists_quasiIso_isKFlat_moduleCat N
  have hPK : (P ⊗ complex).Acyclic :=
    CochainComplex.IsKFlat.acyclic_tensor complex acyclic_complex
  have hKP : (complex ⊗ P).Acyclic := fun i ↦
    ExactAt.of_iso (hPK i) (koszulBraiding (ModuleCat (ZMod 4)) complex P).symm
  have hKN : (complex ⊗ N).Acyclic := fun i ↦
    (exactAt_iff_of_quasiIsoAt (HomologicalComplex.tensorHom (𝟙 complex) π) i).1 (hKP i)
  have hNK : (N ⊗ complex).Acyclic := fun i ↦
    ExactAt.of_iso (hKN i) (koszulBraiding (ModuleCat (ZMod 4)) complex N)
  exact not_exactAt_residueTensor 0
    (ExactAt.of_iso (hNK 0) tensorResidueIso)

end TauCeti.UnboundedFlat
