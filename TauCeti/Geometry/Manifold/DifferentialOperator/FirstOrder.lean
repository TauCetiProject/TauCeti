/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.ComplexDerivation
public import TauCeti.Geometry.Manifold.VectorField.Derivation
public import TauCeti.RingTheory.Derivation.DifferentialOperator
public import TauCeti.RingTheory.Derivation.FirstOrder
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# First-order scalar operators on smooth functions

On a finite-dimensional Hausdorff boundaryless real manifold, a real-linear endomorphism of
smooth functions has vanishing double commutators with multiplication if and only if it has
the form `f ↦ df(X) + cf` for a unique smooth vector field `X` and smooth function `c`.
The coefficient `c` is necessarily the value of the operator on the constant function one.
No continuity of the endomorphism is assumed.

This file combines the algebraic splitting `firstOrderOperatorsEquivDerivationProd` with
`derivationEquivSmoothVectorField`. The resulting geometric splitting also shows that these
operators depend only on the value and differential of their input at each point, and in
particular are local. The commutator `[D, u]` of such an operator with multiplication by `u` is
multiplication by `du(X)`, which is the geometric principal symbol `ξ ↦ ξ(X)` evaluated at
`ξ = du`.

The same holds for complex-linear endomorphisms of the complex-valued smooth functions
`C^∞(M, ℂ)`, with complexified vector fields in place of vector fields. Composing the algebraic
splitting over `ℂ` with `complexDerivationEquivComplexifiedVectorField`, an endomorphism with
vanishing double commutators is `D = δ + c` for a unique complex derivation `δ`, corresponding to
`1 ⊗ X + i ⊗ Y ∈ ℂ ⊗[ℝ] Γ(TM)`, and the smooth function `c = D 1`. On a real smooth function `u`
it acts by `D u = X u + i Y u + u D 1`, and complex linearity determines it on `u + i v`. Its
commutator with multiplication by a complex smooth `g` is multiplication by the derivative of `g`
along `1 ⊗ X + i ⊗ Y`. For real `u` this is `du(X) + i du(Y)`, which is the symbol
`ξ ↦ ξ(X) + i ξ(Y)` (ξ applied to the complexified field `1 ⊗ X + i ⊗ Y`) evaluated at `ξ = du`.

## Main declarations

* `TauCeti.firstOrderOperatorsEquivSmoothVectorFieldProd`: the splitting `D ↦ (X, D 1)` of real
  first-order operators, linear over `C^∞(M)`.
* `LinearMap.mem_firstOrderOperators_iff_existsUnique_vectorField_mul`: vanishing double
  commutators characterize the operators `f ↦ df(X) + cf`.
* `TauCeti.complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd`: the splitting
  `D ↦ (1 ⊗ X + i ⊗ Y, D 1)` of complex first-order operators, linear over `ℂ`.
* `TauCeti.complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst_eq_iff`: the
  complexified field of `D` is `1 ⊗ X + i ⊗ Y` exactly when `D u = X u + i Y u + u D 1` for real
  smooth `u`.
* `LinearMap.mem_firstOrderOperators_iff_existsUnique_complexifiedVectorField_mul`: vanishing
  double commutators characterize the complex operators of this form.
* `TauCeti.firstOrderOperators.lie_mulLeft_apply`: the commutator with multiplication by a real
  smooth function.
* `TauCeti.complexFirstOrderOperators.lie_mulLeft_apply`,
  `TauCeti.complexFirstOrderOperators.lie_mulLeft_ofReal_apply`: the commutators with
  multiplication by a complex, respectively real, smooth function.

The same decomposition holds for operators of order at most one in Grothendieck's sense
(`TauCeti.differentialOperators`): such an operator is differentiation along a smooth vector
field plus multiplication by its value on one
(`LinearMap.eq_vectorFieldDerivation_add_mulLeft_of_mem_differentialOperators_one`).

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §3 (derivations and vector fields) and §19 (linear differential operators).
-/

public section

noncomputable section

open Filter Manifold
open scoped ContDiff Manifold Topology TensorProduct

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- A first-order scalar operator splits into a smooth vector field and multiplication by a
smooth function, linearly over smooth functions. The second coordinate is its value on one. -/
def firstOrderOperatorsEquivSmoothVectorFieldProd :
    firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯ :=
  (firstOrderOperatorsEquivDerivationProd ℝ C^∞⟮I, M; ℝ⟯).trans
    (derivationEquivSmoothVectorField.prodCongr (LinearEquiv.refl _ _))

/-- The vector-field coordinate is the field of the derivation coordinate. -/
@[simp]
theorem firstOrderOperatorsEquivSmoothVectorFieldProd_fst_apply
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) (x : M) :
    (firstOrderOperatorsEquivSmoothVectorFieldProd D).1 x =
      (firstOrderOperatorsEquivDerivationProd ℝ C^∞⟮I, M; ℝ⟯ D).1.vectorField x := by
  simp [firstOrderOperatorsEquivSmoothVectorFieldProd]

/-- The multiplication coefficient of a first-order scalar operator is its value on one. -/
@[simp]
theorem firstOrderOperatorsEquivSmoothVectorFieldProd_snd
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) :
    (firstOrderOperatorsEquivSmoothVectorFieldProd D).2 = D.val 1 := by
  simp [firstOrderOperatorsEquivSmoothVectorFieldProd]

/-- Reconstructing an operator from a field and a function adds directional differentiation
and multiplication. -/
@[simp]
theorem firstOrderOperatorsEquivSmoothVectorFieldProd_symm_apply
    (p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯) :
    ((firstOrderOperatorsEquivSmoothVectorFieldProd.symm p).val) =
      (vectorFieldDerivation p.1).toLinearMap + LinearMap.mulLeft ℝ p.2 := by
  simp [firstOrderOperatorsEquivSmoothVectorFieldProd]

/-- The geometric splitting acts by `D f = df(X) + cf`. -/
theorem firstOrderOperators.apply_eq_mvfderiv_add_mul
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    D.val f x =
      mvfderiv I f x ((firstOrderOperatorsEquivSmoothVectorFieldProd D).1 x) +
        f x * D.val 1 x := by
  simp [mul_comm]

/-- Differentiating along the vector-field coordinate subtracts the multiplication part. -/
theorem mvfderiv_firstOrderOperatorsEquivSmoothVectorFieldProd_fst
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    mvfderiv I f x ((firstOrderOperatorsEquivSmoothVectorFieldProd D).1 x) =
      D.val f x - f x * D.val 1 x :=
  eq_sub_iff_add_eq.mpr (firstOrderOperators.apply_eq_mvfderiv_add_mul D f x).symm

/-- Vanishing double commutators characterize the unique expression of a scalar operator as
a smooth vector field plus multiplication. -/
theorem _root_.LinearMap.mem_firstOrderOperators_iff_existsUnique_vectorField_mul
    (D : Module.End ℝ C^∞⟮I, M; ℝ⟯) :
    D ∈ firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯ ↔
      ∃! p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯,
        ∀ (f : C^∞⟮I, M; ℝ⟯) (x : M),
          D f x = mvfderiv I f x (p.1 x) + f x * p.2 x := by
  have hrep (p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; ℝ⟯) :
      (∀ (f : C^∞⟮I, M; ℝ⟯) (x : M),
        D f x = mvfderiv I f x (p.1 x) + f x * p.2 x) ↔
      D = (firstOrderOperatorsEquivSmoothVectorFieldProd.symm p).val := by
    rw [firstOrderOperatorsEquivSmoothVectorFieldProd_symm_apply]
    constructor
    · intro h
      ext f x
      simpa [mul_comm] using h f x
    · intro h f x
      simp [h, mul_comm]
  constructor
  · intro hD
    let d : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯ := ⟨D, hD⟩
    refine ⟨firstOrderOperatorsEquivSmoothVectorFieldProd d, ?_, ?_⟩
    · exact (hrep _).mpr (by simp [d])
    · intro p hp
      apply firstOrderOperatorsEquivSmoothVectorFieldProd.symm.injective
      apply Subtype.ext
      simpa [d] using ((hrep p).mp hp).symm
  · rintro ⟨p, hp, -⟩
    rw [(hrep p).mp hp]
    exact (firstOrderOperatorsEquivSmoothVectorFieldProd.symm p).property

/-- An operator of order at most one is differentiation along its vector field plus multiplication
by its value on `1`. -/
theorem _root_.LinearMap.eq_vectorFieldDerivation_add_mulLeft_of_mem_differentialOperators_one
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 1) :
    D = (vectorFieldDerivation (derivationEquivSmoothVectorField
      (D.derivationOfMemDifferentialOperatorsOne hD)) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) +
        LinearMap.mulLeft ℝ (D 1) := by
  rw [← ContMDiffSection.derivationEquivSmoothVectorField_symm_apply, LinearEquiv.symm_apply_apply]
  ext f x
  simp [mul_comm]

namespace firstOrderOperators

/-- A first-order scalar operator depends only on the value and differential of its input. -/
theorem apply_eq_of_apply_eq_of_mvfderiv_eq
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) {f g : C^∞⟮I, M; ℝ⟯} {x : M}
    (hvalue : f x = g x) (hdifferential : mvfderiv I f x = mvfderiv I g x) :
    D.val f x = D.val g x := by
  rw [apply_eq_mvfderiv_add_mul D f,
    apply_eq_mvfderiv_add_mul D g, hvalue, hdifferential]

/-- First-order scalar operators are local: inputs with the same germ have the same output
at the point. -/
theorem apply_eq_of_eventuallyEq
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) {f g : C^∞⟮I, M; ℝ⟯} {x : M}
    (h : (f : M → ℝ) =ᶠ[𝓝 x] g) : D.val f x = D.val g x :=
  apply_eq_of_apply_eq_of_mvfderiv_eq D h.eq_of_nhds h.mvfderiv_eq

end firstOrderOperators

/-- A first-order scalar operator is multiplication precisely when its vector-field part
vanishes. -/
theorem firstOrderOperatorsEquivSmoothVectorFieldProd_fst_eq_zero_iff
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) :
    (firstOrderOperatorsEquivSmoothVectorFieldProd D).1 = 0 ↔
      D.val = LinearMap.mulLeft ℝ (D.val 1) := by
  constructor
  · intro h
    have heq : D = firstOrderOperatorsEquivSmoothVectorFieldProd.symm (0, D.val 1) := by
      apply firstOrderOperatorsEquivSmoothVectorFieldProd.injective
      simpa using Prod.ext h (firstOrderOperatorsEquivSmoothVectorFieldProd_snd D)
    simpa using congrArg Subtype.val heq
  · intro h
    have heq : D = firstOrderOperatorsEquivSmoothVectorFieldProd.symm (0, D.val 1) := by
      apply Subtype.ext
      simpa using h
    rw [heq, LinearEquiv.apply_symm_apply]

/-- The commutator of a first-order scalar operator with multiplication by `u` is multiplication by
the derivative of `u` along its vector-field part. -/
theorem firstOrderOperators.lie_mulLeft_apply
    (D : firstOrderOperators ℝ C^∞⟮I, M; ℝ⟯) (u f : C^∞⟮I, M; ℝ⟯) (x : M) :
    ⁅D.val, LinearMap.mulLeft ℝ u⁆ f x =
      mvfderiv I u x ((firstOrderOperatorsEquivSmoothVectorFieldProd D).1 x) * f x := by
  rw [LinearMap.lie_mulLeft_eq_mulLeft_derivationOfDoubleCommutator _
      ((LinearMap.mem_firstOrderOperators _).mp D.property),
    mvfderiv_firstOrderOperatorsEquivSmoothVectorFieldProd_fst]
  simp [mul_comm]

section Complex

/-- **First-order complex scalar operators.** A complex-linear endomorphism of `C^∞(M, ℂ)` with
vanishing double commutators splits complex-linearly into a complexified smooth vector field
`1 ⊗ X + i ⊗ Y` and multiplication by a complex smooth function. The second coordinate is its
value on one. -/
def complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd :
    firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℂ]
      (ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ((firstOrderOperatorsEquivDerivationProd ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).restrictScalars ℂ).trans
    (complexDerivationEquivComplexifiedVectorField.prodCongr (LinearEquiv.refl ℂ _))

/-- The complexified vector-field coordinate is the complexified field of the derivation part. -/
@[simp]
theorem complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst
    (D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd D).1 =
      complexDerivationEquivComplexifiedVectorField
        (firstOrderOperatorsEquivDerivationProd ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ D).1 := by
  simp [complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd]

/-- The complexified vector field of a first-order complex scalar operator is `1 ⊗ X + i ⊗ Y`,
where `X` and `Y` are the vector fields of the real and imaginary parts of its derivation part. -/
theorem complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst_eq
    (D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd D).1 =
      1 ⊗ₜ derivationEquivSmoothVectorField
          (firstOrderOperatorsEquivDerivationProd ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ D).1.re +
        Complex.I ⊗ₜ derivationEquivSmoothVectorField
          (firstOrderOperatorsEquivDerivationProd ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ D).1.im := by
  rw [complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst,
    complexDerivationEquivComplexifiedVectorField_apply]

/-- The multiplication coefficient of a first-order complex scalar operator is its value on one. -/
@[simp]
theorem complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_snd
    (D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd D).2 = D.val 1 := by
  simp [complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd]

/-- Reconstructing a complex operator from a complexified field and a function adds the complex
derivation of the field and multiplication. -/
@[simp]
theorem complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_symm_apply
    (p : (ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd.symm p).val =
      (complexDerivationEquivComplexifiedVectorField.symm p.1).toLinearMap +
        LinearMap.mulLeft ℂ p.2 := by
  simp [complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd]

/-- The complexified vector field of a first-order complex scalar operator `D` is `1 ⊗ X + i ⊗ Y`
exactly when `D u = X u + i Y u + u D 1` for every real smooth function `u`. -/
theorem complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst_eq_iff
    {D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    {X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} :
    (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd D).1 =
        1 ⊗ₜ X + Complex.I ⊗ₜ Y ↔
      ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M), D.val (ContMDiffMap.ofReal u) x =
        (mvfderiv I u x (X x) : ℂ) + (mvfderiv I u x (Y x) : ℂ) * Complex.I +
          (u x : ℂ) * D.val 1 x := by
  rw [complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst,
    complexDerivationEquivComplexifiedVectorField_eq_iff]
  refine forall₂_congr fun u x ↦ ?_
  rw [firstOrderOperatorsEquivDerivationProd_fst_apply]
  simp only [ContMDiffMap.coe_sub, ContMDiffMap.coe_mul, Pi.sub_apply, Pi.mul_apply,
    ContMDiffMap.ofReal_apply]
  rw [sub_eq_iff_eq_add, mul_comm ((D : Module.End ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) 1 x)]

/-- **The splitting on all inputs.** If the complexified vector field of `D` is `1 ⊗ X + i ⊗ Y`,
then `D` acts on `f = u + i v` by `X u - Y v + i (Y u + X v) + f D 1`. -/
theorem complexFirstOrderOperators.apply_eq_mvfderiv_add_mul
    {D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    {X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h : (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd D).1 =
      1 ⊗ₜ X + Complex.I ⊗ₜ Y)
    (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    D.val f x =
      ((mvfderiv I f.re x (X x) - mvfderiv I f.im x (Y x) : ℝ) : ℂ) +
        ((mvfderiv I f.re x (Y x) + mvfderiv I f.im x (X x) : ℝ) : ℂ) * Complex.I +
          f x * D.val 1 x := by
  have hD : D = complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd.symm
      (1 ⊗ₜ X + Complex.I ⊗ₜ Y, D.val 1) := by
    rw [LinearEquiv.eq_symm_apply]
    exact Prod.ext h (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_snd D)
  conv_lhs => rw [hD]
  simp only [complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_symm_apply,
    LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply, Derivation.coeFn_coe,
    LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
  rw [complexDerivationEquivComplexifiedVectorField_symm_apply_apply, mul_comm (D.val 1 x)]

/-- Vanishing double commutators characterize the unique expression of a complex scalar operator
as a complexified smooth vector field plus multiplication: `D u = X u + i Y u + u c` for real
smooth `u`. Complex linearity extends this to all complex inputs. -/
theorem _root_.LinearMap.mem_firstOrderOperators_iff_existsUnique_complexifiedVectorField_mul
    (D : Module.End ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    D ∈ firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ↔
      ∃! p : (Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ ×
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M), D (ContMDiffMap.ofReal u) x =
          (mvfderiv I u x (p.1.1 x) : ℂ) + (mvfderiv I u x (p.1.2 x) : ℂ) * Complex.I +
            (u x : ℂ) * p.2 x := by
  -- The coefficient `c` is forced to be `D 1`, since the derivatives of the constant one vanish.
  have hc {p : (Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ ×
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
      (hp : ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M), D (ContMDiffMap.ofReal u) x =
        (mvfderiv I u x (p.1.1 x) : ℂ) + (mvfderiv I u x (p.1.2 x) : ℂ) * Complex.I +
          (u x : ℂ) * p.2 x) : p.2 = D 1 := by
    ext x
    have h1 := hp 1 x
    have hd1 : mvfderiv I (⇑(1 : C^∞⟮I, M; ℝ⟯)) x = 0 := by
      rw [ContMDiffMap.coe_one]
      exact mvfderiv_const 1
    rw [map_one] at h1
    rw [h1, hd1]
    simp
  constructor
  · intro hD
    let d : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ := ⟨D, hD⟩
    have hXY := complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst_eq d
    have hd := complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst_eq_iff.mp hXY
    refine ⟨((_, _), D 1), hd, fun p hp ↦ ?_⟩
    obtain ⟨⟨X', Y'⟩, c'⟩ := p
    obtain rfl : c' = D 1 := hc hp
    have hXY' :=
      (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst_eq_iff (D := d)).mpr hp
    obtain ⟨rfl, rfl⟩ := (one_tmul_add_I_tmul_inj _).mp (hXY'.symm.trans hXY)
    rfl
  · rintro ⟨⟨⟨X, Y⟩, c⟩, hp, -⟩
    obtain rfl : c = D 1 := hc hp
    let D' := complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd.symm
      (1 ⊗ₜ X + Complex.I ⊗ₜ Y, D 1)
    have hD' : (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd D').1 =
        1 ⊗ₜ X + Complex.I ⊗ₜ Y := by
      simp [D']
    have h1 : D'.val 1 = D 1 := by
      simp [D']
    have hreal (u : C^∞⟮I, M; ℝ⟯) : D (ContMDiffMap.ofReal u) = D'.val (ContMDiffMap.ofReal u) :=
      ContMDiffMap.ext fun x ↦ by
        rw [hp u x,
          complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst_eq_iff.mp hD' u x, h1]
    have heq : D = D'.val := ContMDiffMap.linearMap_ext_ofReal hreal
    exact heq ▸ D'.property

namespace complexFirstOrderOperators

/-- A first-order complex scalar operator depends only on the value and differential of its
input. -/
theorem apply_eq_of_apply_eq_of_mvfderiv_eq
    (D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) {f g : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} {x : M}
    (hvalue : f x = g x) (hdifferential : mvfderiv I f x = mvfderiv I g x) :
    D.val f x = D.val g x := by
  have hXY := complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd_fst_eq D
  have hre : mvfderiv I f.re x = mvfderiv I g.re x := by
    rw [ContMDiffMap.mvfderiv_re _ (by simp), ContMDiffMap.mvfderiv_re _ (by simp), hdifferential]
  have him : mvfderiv I f.im x = mvfderiv I g.im x := by
    rw [ContMDiffMap.mvfderiv_im _ (by simp), ContMDiffMap.mvfderiv_im _ (by simp), hdifferential]
  rw [apply_eq_mvfderiv_add_mul hXY f x, apply_eq_mvfderiv_add_mul hXY g x, hvalue, hre, him]

/-- First-order complex scalar operators are local: inputs with the same germ have the same
output at the point. -/
theorem apply_eq_of_eventuallyEq
    (D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) {f g : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} {x : M}
    (h : (f : M → ℂ) =ᶠ[𝓝 x] g) : D.val f x = D.val g x :=
  apply_eq_of_apply_eq_of_mvfderiv_eq D h.eq_of_nhds h.mvfderiv_eq

/-- The commutator of a first-order complex scalar operator with multiplication by a complex smooth
function `g = u + i v` is multiplication by `X u - Y v + i (Y u + X v)`, its complexified field
applied to `g`. -/
theorem lie_mulLeft_apply
    {D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    {X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h : (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd D).1 =
      1 ⊗ₜ X + Complex.I ⊗ₜ Y)
    (g f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    ⁅D.val, LinearMap.mulLeft ℂ g⁆ f x =
      (((mvfderiv I g.re x (X x) - mvfderiv I g.im x (Y x) : ℝ) : ℂ) +
        ((mvfderiv I g.re x (Y x) + mvfderiv I g.im x (X x) : ℝ) : ℂ) * Complex.I) * f x := by
  rw [LinearMap.lie_mulLeft_eq_mulLeft_derivationOfDoubleCommutator _
    ((LinearMap.mem_firstOrderOperators _).mp D.property)]
  simp only [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
    LinearMap.derivationOfDoubleCommutator_apply, ContMDiffMap.coe_sub, Pi.sub_apply]
  rw [apply_eq_mvfderiv_add_mul h g x]
  ring

/-- The commutator of a first-order complex scalar operator with multiplication by a real smooth
function `u` is multiplication by the complexified derivative `X u + i Y u`. -/
theorem lie_mulLeft_ofReal_apply
    {D : firstOrderOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    {X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h : (complexFirstOrderOperatorsEquivComplexifiedVectorFieldProd D).1 =
      1 ⊗ₜ X + Complex.I ⊗ₜ Y)
    (u : C^∞⟮I, M; ℝ⟯) (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    ⁅D.val, LinearMap.mulLeft ℂ (ContMDiffMap.ofReal u)⁆ f x =
      ((mvfderiv I u x (X x) : ℂ) + (mvfderiv I u x (Y x) : ℂ) * Complex.I) * f x := by
  rw [lie_mulLeft_apply h]
  push_cast [mvfderiv_zero]
  simp

end complexFirstOrderOperators

end Complex

end TauCeti
