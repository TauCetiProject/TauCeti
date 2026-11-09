/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Real Cauchy–Riemann operators

Let `M` be a real manifold with an almost complex structure `j`, and let `V` be a complex vector
bundle over `M`, smooth as a real vector bundle. A `(0,1)`-form with values in `V` at `x` is a real
linear map `η : T_x M → V x` which is complex antilinear for `j`: `η (j v) = -(i • η v)`, that is
`TauCeti.IsComplexAntilinear` for `j` and multiplication by `i`.

A *real Cauchy–Riemann operator* on `V` (McDuff–Salamon, Definition C.1.5) is an operator `D`
from sections of `V` to `V`-valued `(0,1)`-forms which is additive and satisfies the Leibniz rule
`D (g • ξ) = g • D ξ + (∂bar g) ⊗ ξ` for real valued functions `g`, where
`((∂bar g) ⊗ ξ) v = ½ (dg v • ξ + dg (j v) • i • ξ)`.
As for Mathlib's `IsCovariantDerivativeOn`, the operator is a map on all sections, and its
additivity and Leibniz laws are imposed at points where the sections and functions involved are
differentiable.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.difference`: two real Cauchy–Riemann operators differ by a
  zeroth-order term, a `(0,1)`-form with values in the real endomorphisms of `V`
  (`TauCeti.IsRealCauchyRiemannOperator.isZeroOneForm_difference`).
* `TauCeti.IsRealCauchyRiemannOperator.add_zeroOrder`: conversely, adding such a term to a real
  Cauchy–Riemann operator gives a real Cauchy–Riemann operator.
* `TauCeti.IsRealCauchyRiemannOperator.isRealCauchyRiemannOperator_sectionComplexLinearPart` and
  `TauCeti.IsRealCauchyRiemannOperator.isComplexLinearOperator_sectionComplexLinearPart`: the
  complex linear part `D^ℂ ξ = ½ (D ξ - i • D (i • ξ))` of a real Cauchy–Riemann operator is a
  complex linear real Cauchy–Riemann operator.
* `TauCeti.IsRealCauchyRiemannOperator.antilinearPart`: the remainder `D - D^ℂ` is a zeroth-order
  term, complex antilinear on `V`, with `D ξ = D^ℂ ξ + A (ξ x)`
  (`TauCeti.IsRealCauchyRiemannOperator.sectionComplexLinearPart_add_antilinearPart`).
* `TauCeti.sectionComplexLinearPart_eq_of_eq_add` and
  `TauCeti.IsRealCauchyRiemannOperator.antilinearPart_eq_of_eq_add`: the decomposition into a
  complex linear real Cauchy–Riemann operator and a complex antilinear zeroth-order term is unique
  (McDuff–Salamon, Exercise C.1.7).

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, Definition C.1.5 and Exercise C.1.7.
-/

@[expose] public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]

/-! ### Multiplication by complex constants on sections -/

/-- Multiplying a section of a complex vector bundle by a complex constant preserves
differentiability, where differentiability is taken for the real structure of the bundle. -/
theorem mdifferentiableAt_complex_smul_section [NormedSpace ℂ F] [VectorBundle ℂ F V] (c : ℂ)
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt (T% σ) x) : MDiffAt (T% (c • σ)) x := by
  rw [mdifferentiableAt_section] at hσ ⊢
  set e := trivializationAt F V x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  let L : F →L[ℝ] F := c • ContinuousLinearMap.id ℝ F
  refine (L.mdifferentiableAt.comp x hσ).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact (e.linear ℂ hy).map_smul c (σ y)

variable [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-! ### Complex linear operators and the complex linear part of an operator -/

section ComplexPart

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}

variable (F) in
/-- An operator from sections of a complex vector bundle `V` to `V`-valued one-forms is *complex
linear* if it commutes with multiplication by `i` on sections differentiable at a point. -/
def IsComplexLinearOperator (D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x) : Prop :=
  ∀ ⦃σ : Π x : M, V x⦄ ⦃x : M⦄, MDiffAt (T% σ) x → D (Complex.I • σ) x = Complex.I • D σ x

/-- The complex linear part `D^ℂ ξ = ½ (D ξ - i • D (i • ξ))` of an operator on sections of a
complex vector bundle. -/
def sectionComplexLinearPart (D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x)
    (σ : Π x : M, V x) (x : M) : TangentSpace I x →L[ℝ] V x :=
  (2⁻¹ : ℝ) • (D σ x - Complex.I • D (Complex.I • σ) x)

theorem sectionComplexLinearPart_apply (σ : Π x : M, V x) (x : M) :
    sectionComplexLinearPart D σ x = (2⁻¹ : ℝ) • (D σ x - Complex.I • D (Complex.I • σ) x) :=
  rfl

/-- The complex linear part of a complex linear operator is the operator itself. -/
theorem IsComplexLinearOperator.sectionComplexLinearPart_eq (hD : IsComplexLinearOperator F D)
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt (T% σ) x) :
    sectionComplexLinearPart D σ x = D σ x := by
  rw [sectionComplexLinearPart_apply, hD hσ, smul_smul Complex.I Complex.I, Complex.I_mul_I,
    neg_one_smul, sub_neg_eq_add, ← two_smul ℝ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- Uniqueness of the complex linear part (McDuff–Salamon, Exercise C.1.7): if an operator is the
sum of a complex linear operator and a complex antilinear zeroth-order term, then the complex
linear operator is its complex linear part. -/
theorem sectionComplexLinearPart_eq_of_eq_add [NormedSpace ℂ F] [VectorBundle ℂ F V]
    {D₀ : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hD₀ : IsComplexLinearOperator F D₀) (α : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (hα : ∀ x e, α x (Complex.I • e) = -(Complex.I • α x e))
    (hDeq : ∀ ⦃σ : Π x : M, V x⦄ ⦃x : M⦄, MDiffAt (T% σ) x → D σ x = D₀ σ x + α x (σ x))
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt (T% σ) x) :
    sectionComplexLinearPart D σ x = D₀ σ x := by
  have hIσ := mdifferentiableAt_complex_smul_section Complex.I hσ
  rw [sectionComplexLinearPart_apply, hDeq hσ, hDeq hIσ, hD₀ hσ, Pi.smul_apply, hα]
  simp only [smul_add, smul_neg, smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul]
  module

end ComplexPart

variable [IsManifold I ∞ M] (j : SmoothAlmostComplexStructure I M)

/-! ### `(0,1)`-forms and the term `(∂bar g) ⊗ ξ` -/

namespace SmoothAlmostComplexStructure

/-- A real linear map `η : T_x M → V x` is a `(0,1)`-form at `x` if it is complex antilinear for
the almost complex structure `j`: `η (j v) = -(i • η v)`. -/
def IsZeroOneForm {x : M} (η : TangentSpace I x →L[ℝ] V x) : Prop :=
  ∀ v, η (j x v) = -(Complex.I • η v)

/-- The `(0,1)`-part `(∂bar g) ⊗ ξ` of `dg ⊗ ξ`, for a real valued function `g` and a section `ξ` of
a complex vector bundle: `v ↦ ½ (dg v • ξ + dg (j v) • i • ξ)`. -/
def dbarSMulRight (g : M → ℝ) (σ : Π x : M, V x) (x : M) : TangentSpace I x →L[ℝ] V x :=
  (2⁻¹ : ℝ) • ((d% g x).smulRight (σ x) +
    ((d% g x).comp (j.toEndomorphism x)).smulRight (Complex.I • σ x))

variable {j}

theorem dbarSMulRight_apply (g : M → ℝ) (σ : Π x : M, V x) (x : M) (v : TangentSpace I x) :
    j.dbarSMulRight g σ x v =
      (2⁻¹ : ℝ) • (d% g x v • σ x + d% g x (j x v) • Complex.I • σ x) :=
  rfl

/-- The term `(∂bar g) ⊗ ξ` vanishes for constant `g`. -/
@[simp]
theorem dbarSMulRight_const (c : ℝ) (σ : Π x : M, V x) (x : M) :
    j.dbarSMulRight (fun _ ↦ c) σ x = 0 := by
  ext v
  simp [dbarSMulRight_apply, mvfderiv_const]

variable [∀ x, IsScalarTower ℝ ℂ (V x)]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- A `(0,1)`-form is a real linear map which is complex antilinear for `j` and multiplication by
`i`, in the sense of `TauCeti.IsComplexAntilinear`. -/
theorem isZeroOneForm_iff_isComplexAntilinear {x : M} (η : TangentSpace I x →L[ℝ] V x) :
    j.IsZeroOneForm η ↔ IsComplexAntilinear (j.toEndomorphism x).toLinearMap
      (DistribSMul.toLinearMap ℝ (V x) Complex.I) η.toLinearMap :=
  ⟨fun h ↦ isComplexAntilinear_of_apply h, fun h v ↦ h.apply v⟩

/-- The term `(∂bar g) ⊗ ξ` is a `(0,1)`-form. -/
theorem isZeroOneForm_dbarSMulRight (g : M → ℝ) (σ : Π x : M, V x) (x : M) :
    j.IsZeroOneForm (j.dbarSMulRight g σ x) := by
  intro v
  simp only [dbarSMulRight_apply, apply_apply, map_neg, neg_smul, smul_add, smul_neg,
    smul_comm Complex.I (_ : ℝ), smul_smul Complex.I Complex.I, Complex.I_mul_I, one_smul]
  abel

variable [∀ x, ContinuousSMul ℂ (V x)]

/-- The key identity of McDuff–Salamon, Exercise C.1.7:
`(∂bar g) ⊗ (i • ξ) = i • ((∂bar g) ⊗ ξ)`. -/
theorem dbarSMulRight_complex_I_smul (g : M → ℝ) (σ : Π x : M, V x) (x : M) :
    j.dbarSMulRight g (Complex.I • σ) x = Complex.I • j.dbarSMulRight g σ x := by
  ext v
  simp only [dbarSMulRight_apply, Pi.smul_apply, smul_apply, smul_add,
    smul_comm Complex.I (_ : ℝ), smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul,
    smul_neg]

end SmoothAlmostComplexStructure

open SmoothAlmostComplexStructure

/-! ### Real Cauchy–Riemann operators -/

variable (F) in
/-- An operator `D` from sections of a complex vector bundle `V` to `V`-valued one-forms is a *real
Cauchy–Riemann operator* for the almost complex structure `j` if its values are `(0,1)`-forms, it
is additive on sections differentiable at a point, and it satisfies the Leibniz rule
`D (g • ξ) = g • D ξ + (∂bar g) ⊗ ξ` for real valued `g` differentiable at that point
(McDuff–Salamon, Definition C.1.5). -/
structure IsRealCauchyRiemannOperator
    (D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x) : Prop where
  isZeroOneForm (σ : Π x : M, V x) (x : M) : j.IsZeroOneForm (D σ x)
  add {σ σ' : Π x : M, V x} {x : M} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) :
    D (σ + σ') x = D σ x + D σ' x
  leibniz {σ : Π x : M, V x} {g : M → ℝ} {x : M} (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) :
    D (g • σ) x = g x • D σ x + j.dbarSMulRight g σ x

namespace IsRealCauchyRiemannOperator

variable {j} {D D' : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}

/-- A real Cauchy–Riemann operator is real linear on sections differentiable at a point. -/
theorem smul_const (hD : IsRealCauchyRiemannOperator F j D) (a : ℝ) {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) : D (a • σ) x = a • D σ x := by
  have h := hD.leibniz (g := fun _ ↦ a) hσ mdifferentiableAt_const
  rw [dbarSMulRight_const, add_zero] at h
  exact h

theorem neg (hD : IsRealCauchyRiemannOperator F j D) {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) : D (-σ) x = -D σ x := by
  simpa using hD.smul_const (-1) hσ

/-! ### Zeroth-order terms -/

/-- Adding a zeroth-order term `α`, a `(0,1)`-form with values in the real endomorphisms of `V`, to
a real Cauchy–Riemann operator gives a real Cauchy–Riemann operator. -/
theorem add_zeroOrder (hD : IsRealCauchyRiemannOperator F j D)
    (α : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (hα : ∀ x e, j.IsZeroOneForm (α x e)) :
    IsRealCauchyRiemannOperator F j fun σ x ↦ D σ x + α x (σ x) where
  isZeroOneForm σ x v := by
    simp only [add_apply, hD.isZeroOneForm σ x v, hα x (σ x) v, smul_add, neg_add]
  add hσ hσ' := by
    simp only [hD.add hσ hσ', Pi.add_apply, map_add]
    abel
  leibniz hσ hg := by
    simp only [hD.leibniz hσ hg, Pi.smul_apply', map_smul, smul_add]
    abel

/-- The difference of two real Cauchy–Riemann operators is tensorial. -/
theorem tensorialAt_sub (hD : IsRealCauchyRiemannOperator F j D)
    (hD' : IsRealCauchyRiemannOperator F j D') (x : M) :
    TensorialAt I F (fun σ ↦ D σ x - D' σ x) x where
  smul hg hσ := by
    simp only [hD.leibniz hσ hg, hD'.leibniz hσ hg, smul_sub]
    abel
  add hσ hσ' := by
    simp only [hD.add hσ hσ', hD'.add hσ hσ']
    abel

section Difference

variable [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]

/-- The difference of two real Cauchy–Riemann operators, a zeroth-order term: a one-form with
values in the real endomorphisms of `V`, with `D ξ - D' ξ = α (ξ x)`
(`TauCeti.IsRealCauchyRiemannOperator.difference_apply`). -/
def difference (hD : IsRealCauchyRiemannOperator F j D) (hD' : IsRealCauchyRiemannOperator F j D')
    (x : M) : V x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  TensorialAt.mkHom _ x (tensorialAt_sub hD hD' x)

/-- Two real Cauchy–Riemann operators differ by the zeroth-order term `difference`. -/
theorem difference_apply (hD : IsRealCauchyRiemannOperator F j D)
    (hD' : IsRealCauchyRiemannOperator F j D') {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) : hD.difference hD' x (σ x) = D σ x - D' σ x :=
  TensorialAt.mkHom_apply (tensorialAt_sub hD hD' x) hσ

/-- The difference of two real Cauchy–Riemann operators takes values in `(0,1)`-forms. -/
theorem isZeroOneForm_difference (hD : IsRealCauchyRiemannOperator F j D)
    (hD' : IsRealCauchyRiemannOperator F j D') (x : M) (e : V x) :
    j.IsZeroOneForm (hD.difference hD' x e) := by
  intro v
  rw [difference, TensorialAt.mkHom_apply_eq_extend]
  simp only [sub_apply, hD.isZeroOneForm _ x v, hD'.isZeroOneForm _ x v, smul_sub, neg_sub_neg,
    neg_sub]

/-- A real Cauchy–Riemann operator is the sum of another one and their difference. -/
theorem eq_add_difference (hD : IsRealCauchyRiemannOperator F j D)
    (hD' : IsRealCauchyRiemannOperator F j D') {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) : D σ x = D' σ x + hD.difference hD' x (σ x) := by
  rw [hD.difference_apply hD' hσ, add_sub_cancel]

end Difference

/-! ### The complex linear and antilinear parts (McDuff–Salamon, Exercise C.1.7) -/

section ComplexPart

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

/-- The complex linear part of a real Cauchy–Riemann operator is complex linear. -/
theorem isComplexLinearOperator_sectionComplexLinearPart (hD : IsRealCauchyRiemannOperator F j D) :
    IsComplexLinearOperator F (sectionComplexLinearPart D) := by
  intro σ x hσ
  have hII : Complex.I • Complex.I • σ = -σ := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [sectionComplexLinearPart_apply, hII, hD.neg hσ, smul_sub, smul_neg,
    smul_comm Complex.I (2⁻¹ : ℝ), smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul]
  module

variable [NormedSpace ℂ F] [VectorBundle ℂ F V]

/-- The complex linear part of a real Cauchy–Riemann operator is a real Cauchy–Riemann
operator. -/
theorem isRealCauchyRiemannOperator_sectionComplexLinearPart
    (hD : IsRealCauchyRiemannOperator F j D) :
    IsRealCauchyRiemannOperator F j (sectionComplexLinearPart D) where
  isZeroOneForm σ x v := by
    simp only [sectionComplexLinearPart_apply, smul_apply, sub_apply, hD.isZeroOneForm σ x v,
      hD.isZeroOneForm (Complex.I • σ) x v, smul_neg, smul_sub, smul_comm Complex.I (2⁻¹ : ℝ)]
    abel
  add {σ σ' x} hσ hσ' := by
    have hIσ := mdifferentiableAt_complex_smul_section Complex.I hσ
    have hIσ' := mdifferentiableAt_complex_smul_section Complex.I hσ'
    simp only [sectionComplexLinearPart_apply, smul_add, hD.add hσ hσ', hD.add hIσ hIσ']
    module
  leibniz {σ g x} hσ hg := by
    have hIσ := mdifferentiableAt_complex_smul_section Complex.I hσ
    have hcomm : Complex.I • (g • σ) = g • (Complex.I • σ) := by
      ext y
      exact smul_comm Complex.I (g y) (σ y)
    simp only [sectionComplexLinearPart_apply, hcomm, hD.leibniz hσ hg, hD.leibniz hIσ hg,
      dbarSMulRight_complex_I_smul, smul_add, smul_smul Complex.I Complex.I, Complex.I_mul_I,
      neg_one_smul, smul_comm Complex.I (g x)]
    module

variable [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]

/-- The antilinear part `A = D - D^ℂ` of a real Cauchy–Riemann operator, a zeroth-order term:
`A (ξ x) = ½ (D ξ + i • D (i • ξ))` (`TauCeti.IsRealCauchyRiemannOperator.antilinearPart_apply`).
-/
def antilinearPart (hD : IsRealCauchyRiemannOperator F j D) (x : M) :
    V x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  hD.difference hD.isRealCauchyRiemannOperator_sectionComplexLinearPart x

theorem antilinearPart_apply (hD : IsRealCauchyRiemannOperator F j D) {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) :
    hD.antilinearPart x (σ x) = (2⁻¹ : ℝ) • (D σ x + Complex.I • D (Complex.I • σ) x) := by
  rw [antilinearPart, difference_apply _ _ hσ, sectionComplexLinearPart_apply]
  module

/-- A real Cauchy–Riemann operator is the sum of its complex linear part and its antilinear
part. -/
theorem sectionComplexLinearPart_add_antilinearPart (hD : IsRealCauchyRiemannOperator F j D)
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt (T% σ) x) :
    sectionComplexLinearPart D σ x + hD.antilinearPart x (σ x) = D σ x := by
  rw [antilinearPart, difference_apply _ _ hσ, add_sub_cancel]

/-- The antilinear part of a real Cauchy–Riemann operator takes values in `(0,1)`-forms. -/
theorem isZeroOneForm_antilinearPart (hD : IsRealCauchyRiemannOperator F j D) (x : M) (e : V x) :
    j.IsZeroOneForm (hD.antilinearPart x e) :=
  hD.isZeroOneForm_difference _ x e

/-- The antilinear part of a real Cauchy–Riemann operator is complex antilinear on `V`. -/
theorem antilinearPart_complex_I_smul (hD : IsRealCauchyRiemannOperator F j D) (x : M) (e : V x) :
    hD.antilinearPart x (Complex.I • e) = -(Complex.I • hD.antilinearPart x e) := by
  have hσ := mdifferentiableAt_extend I F e
  have hIσ := mdifferentiableAt_complex_smul_section Complex.I hσ
  have hII : Complex.I • Complex.I • extend F e = -extend F e := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have h₁ := hD.antilinearPart_apply hIσ
  have h₂ := hD.antilinearPart_apply hσ
  simp only [Pi.smul_apply, extend_apply_self] at h₁ h₂
  rw [h₁, h₂, hII, hD.neg hσ]
  simp only [smul_add, smul_neg, smul_comm Complex.I (2⁻¹ : ℝ), smul_smul Complex.I Complex.I,
    Complex.I_mul_I, neg_one_smul]
  module

/-- Uniqueness of the antilinear part (McDuff–Salamon, Exercise C.1.7): if a real Cauchy–Riemann
operator is the sum of a complex linear operator and a complex antilinear zeroth-order term, then
that term is its antilinear part. -/
theorem antilinearPart_eq_of_eq_add (hD : IsRealCauchyRiemannOperator F j D)
    {D₀ : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hD₀ : IsComplexLinearOperator F D₀) (α : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (hα : ∀ x e, α x (Complex.I • e) = -(Complex.I • α x e))
    (hDeq : ∀ ⦃σ : Π x : M, V x⦄ ⦃x : M⦄, MDiffAt (T% σ) x → D σ x = D₀ σ x + α x (σ x))
    (x : M) : hD.antilinearPart x = α x := by
  ext e : 1
  have hσ := mdifferentiableAt_extend I F e
  have h := hD.sectionComplexLinearPart_add_antilinearPart hσ
  rw [sectionComplexLinearPart_eq_of_eq_add hD₀ α hα hDeq hσ, hDeq hσ, add_right_inj,
    extend_apply_self] at h
  exact h

end ComplexPart

end IsRealCauchyRiemannOperator

end TauCeti
