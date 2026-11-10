/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
import Mathlib.Geometry.Manifold.Notation
import TauCeti.Geometry.Manifold.VectorBundle.Prod

/-!
# Constructions of real Cauchy–Riemann operators

Three constructions of real Cauchy–Riemann operators which leave the Fredholm index unchanged or
additive (McDuff–Salamon, proof of Theorem C.1.10, step 1).

* The direct sum `D₁ ⊕ D₂ : σ ↦ (D₁ σ.1, D₂ σ.2)` of operators on `V` and `W` is an operator on
  `V ×ᵇ W`.
* An operator `D` on `V` is transported along a fibrewise complex linear isomorphism
  `Φ x : V x ≃L[ℂ] W x` to the operator `σ ↦ Φ ∘ D (Φ⁻¹ σ)` on `W`.
* Two operators `D₀`, `D₁` on `V` are joined by the straight-line path
  `t ↦ (1 - t) • D₀ + t • D₁`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.prod`: the direct sum of real Cauchy–Riemann operators is a
  real Cauchy–Riemann operator, complex linear when both summands are
  (`TauCeti.IsComplexLinearOperator.prod`). Its complex linear part, difference and antilinear
  part are the direct sums of those of the summands
  (`TauCeti.sectionComplexLinearPart_sectionProdMap`,
  `TauCeti.IsRealCauchyRiemannOperator.difference_prod`,
  `TauCeti.IsRealCauchyRiemannOperator.antilinearPart_prod`).
* `TauCeti.IsRealCauchyRiemannOperator.transport`: the transport of a real Cauchy–Riemann operator
  along a fibrewise complex linear isomorphism preserving differentiability of sections is a real
  Cauchy–Riemann operator; it is complex linear exactly when the operator is
  (`TauCeti.isComplexLinearOperator_sectionTransport_iff`). Transport commutes with taking the
  complex linear part, the difference and the antilinear part
  (`TauCeti.sectionComplexLinearPart_sectionTransport`,
  `TauCeti.IsRealCauchyRiemannOperator.difference_transport`,
  `TauCeti.IsRealCauchyRiemannOperator.antilinearPart_transport`), is the identity along the
  identity (`TauCeti.sectionTransport_refl`) and composes (`TauCeti.sectionTransport_trans`).
* `TauCeti.IsRealCauchyRiemannOperator.lineMap`: every point `(1 - t) • D₀ + t • D₁` of the
  straight line between two real Cauchy–Riemann operators is a real Cauchy–Riemann operator,
  differing from `D₀` by `t` times the difference of `D₁` and `D₀`
  (`TauCeti.IsRealCauchyRiemannOperator.difference_lineMap`).

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, proof of Theorem C.1.10.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle G W] [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, Module ℝ (W x)] [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]

/-! ### Pointwise lemmas -/

namespace SmoothAlmostComplexStructure

variable [IsManifold I ∞ M] {j : SmoothAlmostComplexStructure I M}

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)] in
/-- A pair of one-forms is a `(0,1)`-form exactly when both components are. -/
theorem isZeroOneForm_prod_iff {x : M} {η : TangentSpace I x →L[ℝ] V x}
    {η' : TangentSpace I x →L[ℝ] W x} :
    j.IsZeroOneForm (V := V ×ᵇ W) (η.prod η') ↔ j.IsZeroOneForm η ∧ j.IsZeroOneForm η' := by
  simp only [isZeroOneForm_iff, ContinuousLinearMap.prod_apply, Prod.smul_mk, Prod.neg_mk,
    Prod.mk.injEq, forall_and]

/-- The term `(∂bar g) ⊗ ξ` of a section of a direct-sum bundle is the pair of the terms of its
components. -/
theorem dbarSMulRight_prod (g : M → ℝ) (σ : Π x : M, V x × W x) (x : M) :
    j.dbarSMulRight (V := V ×ᵇ W) g σ x =
      (j.dbarSMulRight g (fun y ↦ (σ y).1) x).prod (j.dbarSMulRight g (fun y ↦ (σ y).2) x) := by
  ext v <;> simp [dbarSMulRight_apply]

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (W x)]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)] in
/-- Composing a `(0,1)`-form with a complex linear map gives a `(0,1)`-form. -/
theorem IsZeroOneForm.restrictScalars_comp {x : M} {η : TangentSpace I x →L[ℝ] V x}
    (h : j.IsZeroOneForm η) (L : V x →L[ℂ] W x) :
    j.IsZeroOneForm ((L.restrictScalars ℝ).comp η) :=
  isZeroOneForm_iff.2 fun v ↦ by simp [isZeroOneForm_iff.1 h v]

/-- A fibrewise complex linear map commutes with the term `(∂bar g) ⊗ ξ`. -/
theorem restrictScalars_comp_dbarSMulRight (L : Π x : M, V x →L[ℂ] W x) (g : M → ℝ)
    (σ : Π x : M, V x) (x : M) :
    ((L x).restrictScalars ℝ).comp (j.dbarSMulRight g σ x) =
      j.dbarSMulRight g (fun y ↦ L y (σ y)) x := by
  ext v
  simp [dbarSMulRight_apply]

end SmoothAlmostComplexStructure

open SmoothAlmostComplexStructure

/-! ### Direct sums -/

section Prod

/-- The direct sum `D₁ ⊕ D₂` of operators on sections of `V` and of `W`, an operator on sections
of `V ×ᵇ W`: `(D₁ ⊕ D₂) σ = (D₁ σ.1, D₂ σ.2)`. -/
def sectionProdMap (D₁ : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x)
    (D₂ : (Π x : M, W x) → Π x : M, TangentSpace I x →L[ℝ] W x) (σ : Π x : M, V x × W x)
    (x : M) : TangentSpace I x →L[ℝ] V x × W x :=
  (D₁ (fun y ↦ (σ y).1) x).prod (D₂ (fun y ↦ (σ y).2) x)

variable {D₁ D₁' : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
  {D₂ D₂' : (Π x : M, W x) → Π x : M, TangentSpace I x →L[ℝ] W x}

omit [∀ x, Module ℂ (V x)] [∀ x, Module ℂ (W x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)] in
theorem sectionProdMap_apply (σ : Π x : M, V x × W x) (x : M) :
    sectionProdMap D₁ D₂ σ x = (D₁ (fun y ↦ (σ y).1) x).prod (D₂ (fun y ↦ (σ y).2) x) :=
  (rfl)

section ComplexPart

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (W x)] [∀ x, ContinuousSMul ℂ (W x)]

/-- The complex linear part of a direct sum is the direct sum of the complex linear parts. -/
theorem sectionComplexLinearPart_sectionProdMap :
    sectionComplexLinearPart (V := V ×ᵇ W) (sectionProdMap D₁ D₂) =
      sectionProdMap (sectionComplexLinearPart D₁) (sectionComplexLinearPart D₂) := by
  funext σ x
  ext v <;> simp [sectionComplexLinearPart_apply, sectionProdMap_apply] <;> rfl

/-- The direct sum of two complex linear operators is complex linear. -/
theorem IsComplexLinearOperator.prod (hD₁ : IsComplexLinearOperator F D₁)
    (hD₂ : IsComplexLinearOperator G D₂) :
    IsComplexLinearOperator (F × G) (V := V ×ᵇ W) (sectionProdMap D₁ D₂) where
  add {σ σ' x} hσ hσ' := by
    obtain ⟨h₁, h₂⟩ := mdifferentiableAt_section_prod_iff.1 hσ
    obtain ⟨h₁', h₂'⟩ := mdifferentiableAt_section_prod_iff.1 hσ'
    simp only [sectionProdMap_apply]
    rw [show (fun y ↦ ((σ + σ') y).1) = (fun y ↦ (σ y).1) + fun y ↦ (σ' y).1 from rfl,
      show (fun y ↦ ((σ + σ') y).2) = (fun y ↦ (σ y).2) + fun y ↦ (σ' y).2 from rfl,
      hD₁.add h₁ h₁', hD₂.add h₂ h₂']
    ext v <;> simp
  smul_const a {σ x} hσ := by
    obtain ⟨h₁, h₂⟩ := mdifferentiableAt_section_prod_iff.1 hσ
    simp only [sectionProdMap_apply]
    rw [show (fun y ↦ ((a • σ) y).1) = a • fun y ↦ (σ y).1 from rfl,
      show (fun y ↦ ((a • σ) y).2) = a • fun y ↦ (σ y).2 from rfl,
      hD₁.smul_const a h₁, hD₂.smul_const a h₂]
    ext v <;> simp
  complex_I_smul {σ x} hσ := by
    obtain ⟨h₁, h₂⟩ := mdifferentiableAt_section_prod_iff.1 hσ
    simp only [sectionProdMap_apply]
    rw [show (fun y ↦ ((Complex.I • σ) y).1) = Complex.I • fun y ↦ (σ y).1 from rfl,
      show (fun y ↦ ((Complex.I • σ) y).2) = Complex.I • fun y ↦ (σ y).2 from rfl,
      hD₁.complex_I_smul h₁, hD₂.complex_I_smul h₂]
    ext v <;> simp

end ComplexPart

variable [IsManifold I ∞ M] {j : SmoothAlmostComplexStructure I M}

namespace IsRealCauchyRiemannOperator

/-- The direct sum of two real Cauchy–Riemann operators is a real Cauchy–Riemann operator. -/
theorem prod (hD₁ : IsRealCauchyRiemannOperator F j D₁)
    (hD₂ : IsRealCauchyRiemannOperator G j D₂) :
    IsRealCauchyRiemannOperator (F × G) j (V := V ×ᵇ W) (sectionProdMap D₁ D₂) where
  isZeroOneForm σ x :=
    isZeroOneForm_prod_iff.2 ⟨hD₁.isZeroOneForm _ x, hD₂.isZeroOneForm _ x⟩
  add {σ σ' x} hσ hσ' := by
    obtain ⟨h₁, h₂⟩ := mdifferentiableAt_section_prod_iff.1 hσ
    obtain ⟨h₁', h₂'⟩ := mdifferentiableAt_section_prod_iff.1 hσ'
    simp only [sectionProdMap_apply]
    rw [show (fun y ↦ ((σ + σ') y).1) = (fun y ↦ (σ y).1) + fun y ↦ (σ' y).1 from rfl,
      show (fun y ↦ ((σ + σ') y).2) = (fun y ↦ (σ y).2) + fun y ↦ (σ' y).2 from rfl,
      hD₁.add h₁ h₁', hD₂.add h₂ h₂']
    ext v <;> simp
  leibniz {σ g x} hσ hg := by
    obtain ⟨h₁, h₂⟩ := mdifferentiableAt_section_prod_iff.1 hσ
    simp only [sectionProdMap_apply, dbarSMulRight_prod]
    rw [show (fun y ↦ ((g • σ) y).1) = g • fun y ↦ (σ y).1 from rfl,
      show (fun y ↦ ((g • σ) y).2) = g • fun y ↦ (σ y).2 from rfl,
      hD₁.leibniz h₁ hg, hD₂.leibniz h₂ hg]
    ext v <;> simp

section Difference

variable [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
  [VectorBundle ℝ G W] [FiniteDimensional ℝ G] [ContMDiffVectorBundle 1 G W I]

/-- The difference of two direct sums is the direct sum of the differences. -/
theorem difference_prod (hD₁ : IsRealCauchyRiemannOperator F j D₁)
    (hD₁' : IsRealCauchyRiemannOperator F j D₁') (hD₂ : IsRealCauchyRiemannOperator G j D₂)
    (hD₂' : IsRealCauchyRiemannOperator G j D₂') (x : M) (e : V x × W x) :
    (hD₁.prod hD₂).difference (hD₁'.prod hD₂') x e =
      (hD₁.difference hD₁' x e.1).prod (hD₂.difference hD₂' x e.2) := by
  have hσ := mdifferentiableAt_extend I (F × G) (V := V ×ᵇ W) e
  obtain ⟨h₁, h₂⟩ := mdifferentiableAt_section_prod_iff.1 hσ
  have k := (hD₁.prod hD₂).difference_apply (hD₁'.prod hD₂') hσ
  have k₁ := hD₁.difference_apply hD₁' h₁
  have k₂ := hD₂.difference_apply hD₂' h₂
  simp only [extend_apply_self] at k k₁ k₂
  rw [k, k₁, k₂]
  ext v <;> simp [sectionProdMap_apply]

end Difference

section ComplexPart

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (W x)] [∀ x, ContinuousSMul ℂ (W x)]
  [NormedSpace ℂ F] [VectorBundle ℂ F V] [NormedSpace ℂ G] [VectorBundle ℂ G W]
  [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
  [VectorBundle ℝ G W] [FiniteDimensional ℝ G] [ContMDiffVectorBundle 1 G W I]

/-- The antilinear part of a direct sum is the direct sum of the antilinear parts. -/
theorem antilinearPart_prod (hD₁ : IsRealCauchyRiemannOperator F j D₁)
    (hD₂ : IsRealCauchyRiemannOperator G j D₂) (x : M) (e : V x × W x) :
    (hD₁.prod hD₂).antilinearPart x e =
      (hD₁.antilinearPart x e.1).prod (hD₂.antilinearPart x e.2) := by
  have hσ := mdifferentiableAt_extend I (F × G) (V := V ×ᵇ W) e
  obtain ⟨h₁, h₂⟩ := mdifferentiableAt_section_prod_iff.1 hσ
  have k := (hD₁.prod hD₂).antilinearPart_apply hσ
  have k₁ := hD₁.antilinearPart_apply h₁
  have k₂ := hD₂.antilinearPart_apply h₂
  simp only [extend_apply_self] at k k₁ k₂
  rw [k, k₁, k₂]
  ext v <;> simp [sectionProdMap_apply] <;> rfl

end ComplexPart

end IsRealCauchyRiemannOperator

end Prod

/-! ### Transport along fibrewise complex linear isomorphisms -/

section Transport

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (W x)]
  {Φ : Π x : M, V x ≃L[ℂ] W x} {D D' : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}

variable (Φ) in
/-- The transport `σ ↦ Φ ∘ D (Φ⁻¹ σ)` of an operator `D` on sections of `V` to sections of `W`,
along a fibrewise complex linear isomorphism `Φ x : V x ≃L[ℂ] W x`. -/
def sectionTransport (D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x)
    (σ : Π x : M, W x) (x : M) : TangentSpace I x →L[ℝ] W x :=
  ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ).comp (D (fun y ↦ (Φ y).symm (σ y)) x)

variable (Φ) in
omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)] in
theorem sectionTransport_apply (σ : Π x : M, W x) (x : M) :
    sectionTransport Φ D σ x =
      ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ).comp (D (fun y ↦ (Φ y).symm (σ y)) x) :=
  (rfl)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- Transport along the identity is the identity. -/
@[simp]
theorem sectionTransport_refl :
    sectionTransport (fun x ↦ ContinuousLinearEquiv.refl ℂ (V x)) D = D := by
  funext σ x
  ext v
  simp [sectionTransport_apply]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)] in
/-- Transport along `Φ` and then along `Ψ` is transport along the composite. -/
theorem sectionTransport_trans {X : M → Type*} [∀ x, TopologicalSpace (X x)]
    [∀ x, AddCommGroup (X x)] [∀ x, Module ℂ (X x)] [∀ x, Module ℝ (X x)]
    [∀ x, IsTopologicalAddGroup (X x)] [∀ x, ContinuousSMul ℝ (X x)]
    [∀ x, IsScalarTower ℝ ℂ (X x)] (Ψ : Π x : M, W x ≃L[ℂ] X x) :
    sectionTransport Ψ (sectionTransport Φ D) =
      sectionTransport (fun x ↦ (Φ x).trans (Ψ x)) D := by
  funext σ x
  ext v
  simp [sectionTransport_apply]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)] in
/-- Transporting back along `Φ⁻¹` recovers the operator. -/
@[simp]
theorem sectionTransport_symm_sectionTransport :
    sectionTransport (fun x ↦ (Φ x).symm) (sectionTransport Φ D) = D := by
  funext σ x
  ext v
  simp [sectionTransport_apply]

section ComplexPart

variable [∀ x, ContinuousSMul ℂ (V x)] [∀ x, ContinuousSMul ℂ (W x)]

/-- Transport commutes with taking the complex linear part. -/
theorem sectionComplexLinearPart_sectionTransport :
    sectionComplexLinearPart (sectionTransport Φ D) =
      sectionTransport Φ (sectionComplexLinearPart D) := by
  funext σ x
  ext v
  simp [sectionTransport_apply, sectionComplexLinearPart_apply]
  rfl

/-- The transport of a complex linear operator along a fibrewise complex linear isomorphism
preserving differentiability of sections is complex linear. -/
theorem IsComplexLinearOperator.transport (hD : IsComplexLinearOperator F D)
    (hΦ : ∀ ⦃σ : Π x : M, W x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      MDiffAt (T% fun y ↦ (Φ y).symm (σ y)) x) :
    IsComplexLinearOperator G (sectionTransport Φ D) where
  add {σ σ' x} hσ hσ' := by
    rw [sectionTransport_apply, sectionTransport_apply, sectionTransport_apply,
      show (fun y ↦ (Φ y).symm ((σ + σ') y)) =
        (fun y ↦ (Φ y).symm (σ y)) + fun y ↦ (Φ y).symm (σ' y) from
        funext fun y ↦ map_add _ _ _, hD.add (hΦ hσ) (hΦ hσ'), ContinuousLinearMap.comp_add]
  smul_const a {σ x} hσ := by
    rw [sectionTransport_apply, sectionTransport_apply,
      show (fun y ↦ (Φ y).symm ((a • σ) y)) = a • fun y ↦ (Φ y).symm (σ y) from
        funext fun y ↦ LinearMapClass.map_smul_of_tower _ _ _, hD.smul_const a (hΦ hσ),
      ContinuousLinearMap.comp_smul]
  complex_I_smul {σ x} hσ := by
    rw [sectionTransport_apply, sectionTransport_apply,
      show (fun y ↦ (Φ y).symm ((Complex.I • σ) y)) = Complex.I • fun y ↦ (Φ y).symm (σ y) from
        funext fun y ↦ map_smul _ _ _, hD.complex_I_smul (hΦ hσ)]
    ext v
    simp

/-- An operator is complex linear exactly when its transport along a fibrewise complex linear
isomorphism preserving differentiability of sections in both directions is. -/
theorem isComplexLinearOperator_sectionTransport_iff
    (hΦ : ∀ ⦃σ : Π x : M, W x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      MDiffAt (T% fun y ↦ (Φ y).symm (σ y)) x)
    (hΦ' : ∀ ⦃σ : Π x : M, V x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      MDiffAt (T% fun y ↦ Φ y (σ y)) x) :
    IsComplexLinearOperator G (sectionTransport Φ D) ↔ IsComplexLinearOperator F D := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.transport hΦ⟩
  have := h.transport (Φ := fun x ↦ (Φ x).symm) (by simpa using hΦ')
  rwa [sectionTransport_symm_sectionTransport] at this

end ComplexPart

variable [IsManifold I ∞ M] {j : SmoothAlmostComplexStructure I M}

namespace IsRealCauchyRiemannOperator

/-- The transport of a real Cauchy–Riemann operator along a fibrewise complex linear isomorphism
preserving differentiability of sections is a real Cauchy–Riemann operator. -/
theorem transport (hD : IsRealCauchyRiemannOperator F j D)
    (hΦ : ∀ ⦃σ : Π x : M, W x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      MDiffAt (T% fun y ↦ (Φ y).symm (σ y)) x) :
    IsRealCauchyRiemannOperator G j (sectionTransport Φ D) where
  isZeroOneForm σ x := (hD.isZeroOneForm _ x).restrictScalars_comp _
  add {σ σ' x} hσ hσ' := by
    rw [sectionTransport_apply, sectionTransport_apply, sectionTransport_apply,
      show (fun y ↦ (Φ y).symm ((σ + σ') y)) =
        (fun y ↦ (Φ y).symm (σ y)) + fun y ↦ (Φ y).symm (σ' y) from
        funext fun y ↦ map_add _ _ _, hD.add (hΦ hσ) (hΦ hσ'), ContinuousLinearMap.comp_add]
  leibniz {σ g x} hσ hg := by
    rw [sectionTransport_apply, sectionTransport_apply,
      show (fun y ↦ (Φ y).symm ((g • σ) y)) = g • fun y ↦ (Φ y).symm (σ y) from
        funext fun y ↦ LinearMapClass.map_smul_of_tower _ _ _, hD.leibniz (hΦ hσ) hg,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul,
      restrictScalars_comp_dbarSMulRight (fun x ↦ (Φ x : V x →L[ℂ] W x))]
    simp

section Difference

variable [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
  [VectorBundle ℝ G W] [FiniteDimensional ℝ G] [ContMDiffVectorBundle 1 G W I]

/-- Transport commutes with the difference of two real Cauchy–Riemann operators. -/
theorem difference_transport (hD : IsRealCauchyRiemannOperator F j D)
    (hD' : IsRealCauchyRiemannOperator F j D')
    (hΦ : ∀ ⦃σ : Π x : M, W x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      MDiffAt (T% fun y ↦ (Φ y).symm (σ y)) x) (x : M) (e : W x) :
    (hD.transport hΦ).difference (hD'.transport hΦ) x e =
      ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ).comp (hD.difference hD' x ((Φ x).symm e)) := by
  have hσ := mdifferentiableAt_extend I G e
  have k := (hD.transport hΦ).difference_apply (hD'.transport hΦ) hσ
  have k' := hD.difference_apply hD' (hΦ hσ)
  simp only [extend_apply_self] at k k'
  rw [k, k', sectionTransport_apply, sectionTransport_apply, ContinuousLinearMap.comp_sub]

end Difference

section ComplexPart

variable [∀ x, ContinuousSMul ℂ (V x)] [∀ x, ContinuousSMul ℂ (W x)]
  [NormedSpace ℂ F] [VectorBundle ℂ F V] [NormedSpace ℂ G] [VectorBundle ℂ G W]
  [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
  [VectorBundle ℝ G W] [FiniteDimensional ℝ G] [ContMDiffVectorBundle 1 G W I]

/-- Transport commutes with the antilinear part of a real Cauchy–Riemann operator. -/
theorem antilinearPart_transport (hD : IsRealCauchyRiemannOperator F j D)
    (hΦ : ∀ ⦃σ : Π x : M, W x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      MDiffAt (T% fun y ↦ (Φ y).symm (σ y)) x) (x : M) (e : W x) :
    (hD.transport hΦ).antilinearPart x e =
      ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ).comp (hD.antilinearPart x ((Φ x).symm e)) := by
  have hσ := mdifferentiableAt_extend I G e
  have k := (hD.transport hΦ).antilinearPart_apply hσ
  have k' := hD.antilinearPart_apply (hΦ hσ)
  simp only [extend_apply_self] at k k'
  rw [k, k', sectionTransport_apply, sectionTransport_apply,
    show (fun y ↦ (Φ y).symm ((Complex.I • extend G e) y)) =
      Complex.I • fun y ↦ (Φ y).symm (extend G e y) from funext fun y ↦ map_smul _ _ _]
  ext v
  simp

end ComplexPart

end IsRealCauchyRiemannOperator

/-- An operator is a real Cauchy–Riemann operator exactly when its transport along a fibrewise
complex linear isomorphism preserving differentiability of sections in both directions is. -/
theorem isRealCauchyRiemannOperator_sectionTransport_iff
    (hΦ : ∀ ⦃σ : Π x : M, W x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      MDiffAt (T% fun y ↦ (Φ y).symm (σ y)) x)
    (hΦ' : ∀ ⦃σ : Π x : M, V x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      MDiffAt (T% fun y ↦ Φ y (σ y)) x) :
    IsRealCauchyRiemannOperator G j (sectionTransport Φ D) ↔ IsRealCauchyRiemannOperator F j D := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.transport hΦ⟩
  have := h.transport (Φ := fun x ↦ (Φ x).symm) (by simpa using hΦ')
  rwa [sectionTransport_symm_sectionTransport] at this

end Transport

/-! ### The straight line between two operators -/

section LineMap

variable {D₀ D₁ : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}

/-- Every point of the straight line between two complex linear operators is complex linear. -/
theorem IsComplexLinearOperator.lineMap [∀ x, IsScalarTower ℝ ℂ (V x)]
    [∀ x, ContinuousSMul ℂ (V x)] (hD₀ : IsComplexLinearOperator F D₀)
    (hD₁ : IsComplexLinearOperator F D₁) (t : ℝ) :
    IsComplexLinearOperator F fun σ x ↦ (1 - t) • D₀ σ x + t • D₁ σ x where
  add hσ hσ' := by
    simp only [hD₀.add hσ hσ', hD₁.add hσ hσ', smul_add]
    abel
  smul_const a _ _ hσ := by
    simp only [hD₀.smul_const a hσ, hD₁.smul_const a hσ, smul_add, smul_comm a]
  complex_I_smul hσ := by
    simp only [hD₀.complex_I_smul hσ, hD₁.complex_I_smul hσ, smul_add,
      smul_comm Complex.I (_ : ℝ)]

variable [IsManifold I ∞ M] {j : SmoothAlmostComplexStructure I M}

namespace IsRealCauchyRiemannOperator

/-- Every point `(1 - t) • D₀ + t • D₁` of the straight line between two real Cauchy–Riemann
operators is a real Cauchy–Riemann operator. -/
theorem lineMap [∀ x, IsScalarTower ℝ ℂ (V x)] (hD₀ : IsRealCauchyRiemannOperator F j D₀)
    (hD₁ : IsRealCauchyRiemannOperator F j D₁) (t : ℝ) :
    IsRealCauchyRiemannOperator F j fun σ x ↦ (1 - t) • D₀ σ x + t • D₁ σ x where
  isZeroOneForm σ x := isZeroOneForm_iff.2 fun v ↦ by
    simp only [add_apply, smul_apply,
      isZeroOneForm_iff.1 (hD₀.isZeroOneForm σ x) v, isZeroOneForm_iff.1 (hD₁.isZeroOneForm σ x) v,
      smul_neg, smul_add, neg_add]
    rw [smul_comm Complex.I (1 - t), smul_comm Complex.I t]
  add hσ hσ' := by
    simp only [hD₀.add hσ hσ', hD₁.add hσ hσ', smul_add]
    abel
  leibniz {σ g x} hσ hg := by
    simp only [hD₀.leibniz hσ hg, hD₁.leibniz hσ hg, smul_add, smul_comm (g x)]
    module

/-- The point `(1 - t) • D₀ + t • D₁` of the straight line differs from `D₀` by `t` times the
difference of `D₁` and `D₀`. -/
theorem difference_lineMap [∀ x, IsScalarTower ℝ ℂ (V x)] [VectorBundle ℝ F V]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
    (hD₀ : IsRealCauchyRiemannOperator F j D₀)
    (hD₁ : IsRealCauchyRiemannOperator F j D₁) (t : ℝ) (x : M) :
    (hD₀.lineMap hD₁ t).difference hD₀ x = t • hD₁.difference hD₀ x := by
  ext e : 1
  have hσ := mdifferentiableAt_extend I F e
  have k := (hD₀.lineMap hD₁ t).difference_apply hD₀ hσ
  have k' := hD₁.difference_apply hD₀ hσ
  simp only [extend_apply_self] at k k'
  rw [smul_apply, k, k']
  module

end IsRealCauchyRiemannOperator

end LineMap

end TauCeti
