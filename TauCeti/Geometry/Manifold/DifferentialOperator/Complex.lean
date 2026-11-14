/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Complex
public import TauCeti.Geometry.Manifold.VectorField.ComplexDerivation
public import TauCeti.RingTheory.Derivation.FirstOrder
public import TauCeti.RingTheory.Derivation.PrincipalSymbol
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# Differential operators on complex-valued smooth functions

Let `M` be a finite-dimensional Hausdorff real manifold and `A_ℂ = C^∞(M, ℂ)` the complex algebra
of complex-valued (real-)smooth functions on `M`. A complex-linear endomorphism `D` of `A_ℂ` is a
differential operator of order at most `m` in Grothendieck's sense
(`TauCeti.differentialOperators ℂ A_ℂ A_ℂ A_ℂ m`) when all its `(m + 1)`-fold commutators with
multiplication operators vanish; no continuity of `D` is assumed. Operators with complex
coefficients, such as the Cauchy–Riemann operator `(∂ₓ + i ∂_y) / 2` on `ℂ`, are of this kind.

This file constructs the principal symbol of such an operator, the complex counterpart of
`TauCeti.smoothPrincipalSymbol`. The `m`-fold commutator `[⋯[D, f₁], …, fₘ]` is multiplication by
the function `[⋯[D, f₁], …, fₘ] 1`, whose value at an interior point `x` depends only on the
differentials `(df₁)ₓ, …, (dfₘ)ₓ`. These differentials are complex-valued real-linear covectors
`T_x M →L[ℝ] ℂ`, and the dependence is complex-multilinear and symmetric. This gives the
**commutator symbol** of `D` at `x`,

`TauCeti.complexSmoothCommutatorSymbol hx D : (T_x M →L[ℝ] ℂ)ᵐ → ℂ`,
`(df₁(x), …, dfₘ(x)) ↦ ([⋯[D, f₁], …, fₘ] 1)(x)`
(`TauCeti.complexSmoothCommutatorSymbol_mvfderiv`),

and the **principal symbol** in the geometric convention, without factors of `i`,

`TauCeti.complexSmoothPrincipalSymbol I hx D ξ = (1 / m!) σ(ξ, …, ξ)`,

so that `σ_geom(D)(df_x) = (1 / m!) ([⋯[D, f], …, f] 1)(x)`
(`TauCeti.complexSmoothPrincipalSymbol_mvfderiv`). Both are instances of the point symbols
`TauCeti.pointCommutatorSymbol` and `TauCeti.pointPrincipalSymbol` of evaluation at `x`, read
through `I_x / I_x² ≃ (T_x M →L[ℝ] ℂ)` (`TauCeti.complexSmoothCotangentEquiv`), exactly as their
real counterparts. Since the commutator symbol is
complex-multilinear on the complex-valued covectors `T_x M →L[ℝ] ℂ`, it is the complex-multilinear
extension of its restriction to real covectors, which enter as `Complex.ofRealCLM ∘ ξ`. The
Fourier principal symbol of an operator of order `m`, in which `∂ⱼ` has symbol `i ξⱼ`, is `i ^ m`
times the geometric one.

The second part of the file splits the operators of order at most one. On a boundaryless
manifold, a complex-linear endomorphism `D` of `A_ℂ` has vanishing double commutators with
multiplication operators if and only if

`D f = df(X) + i df(Y) + f D(1)`

for unique smooth real vector fields `X`, `Y`
(`TauCeti.mem_differentialOperators_one_iff_existsUnique_vectorField_mul`). As complex vector
spaces these operators are the product of the complexified vector fields `ℂ ⊗[ℝ] Γ(TM)` with
`A_ℂ` (`TauCeti.differentialOperatorsOneEquivComplexifiedVectorFieldProd`), the operator above
corresponding to `(1 ⊗ X + i ⊗ Y, D 1)`. Its principal symbol is `ξ ↦ ξ(X_x) + i ξ(Y_x)`
(`complexSmoothPrincipalSymbol_differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm`),
so its Fourier principal symbol is `ξ ↦ i ξ(X_x) - ξ(Y_x)`.

## Main definitions

* `TauCeti.complexSmoothCommutatorSymbol`: the commutator symbol at an interior point, a symmetric
  complex-multilinear form on `T_x M →L[ℝ] ℂ`.
* `TauCeti.complexSmoothPrincipalSymbol`: the principal symbol at an interior point, a homogeneous
  function of degree `m` on `T_x M →L[ℝ] ℂ`.
* `TauCeti.differentialOperatorsOneEquivComplexifiedVectorFieldProd`: the splitting of operators of
  order at most one into a complexified vector field and multiplication by a function.

## Main results

* `TauCeti.complexSmoothCommutatorSymbol_mvfderiv`, `TauCeti.complexSmoothPrincipalSymbol_mvfderiv`:
  the values at differentials of functions are the iterated commutators.
* `TauCeti.complexSmoothCommutatorSymbol_comp_perm`: the commutator symbol is symmetric.
* `TauCeti.mk_algebraMap_complexSmoothCommutatorSymbol`: comparison with the cotangent symbol of
  the complex vanishing ideal.
* `TauCeti.complexSmoothCommutatorSymbol_eq_zero_of_mem_differentialOperators`,
  `TauCeti.complexSmoothPrincipalSymbol_eq_zero_of_mem_differentialOperators`: an operator of order
  at most `m`, viewed as one of order at most `m + 1`, has vanishing commutator and principal
  symbols.
* `TauCeti.forall_complexSmoothCommutatorSymbol_eq_zero_iff`: on a boundaryless manifold, an
  operator of order at most `m + 1` has vanishing commutator symbol at every point exactly when it
  has order at most `m`.
* `TauCeti.complexSmoothPrincipalSymbol_smul_covector`: the principal symbol is homogeneous of
  degree `m` under complex scalars.
* `TauCeti.complexSmoothPrincipalSymbol_comp`: principal symbols multiply under composition.
* `TauCeti.complexSmoothPrincipalSymbol_one_mvfderiv`,
  `TauCeti.complexSmoothPrincipalSymbol_derivation_mvfderiv`: an operator `D` of order at most one
  has principal symbol `df_x ↦ (D f)(x) - f(x) (D 1)(x)`, and a derivation `δ` has principal symbol
  `df_x ↦ (δ f)(x)`.
* `TauCeti.coe_differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm_apply`: the operator
  corresponding to `(v, c)` is the derivation of `v` plus multiplication by `c`.
* `TauCeti.differentialOperators_one_apply_eq_mvfderiv_add_I_mul_mvfderiv_add_mul`,
  `TauCeti.mem_differentialOperators_one_iff_existsUnique_vectorField_mul`: an operator of order at
  most one acts by `f ↦ df(X) + i df(Y) + c f`, with unique `X`, `Y` and `c`, and every such
  expression has order at most one.
* `complexSmoothPrincipalSymbol_differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm`,
  `TauCeti.complexSmoothPrincipalSymbol_derivation`: the operator `f ↦ df(X) + i df(Y) + c f`, and
  the derivation with complexified vector field `1 ⊗ X + i ⊗ Y`, have principal symbol
  `ξ ↦ ξ(X_x) + i ξ(Y_x)`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§12, 19.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open scoped ContDiff Manifold TensorProduct

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {x : M}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem ker_complexEvalAlgHom (x : M) :
    RingHom.ker (ContMDiffMap.complexEvalAlgHom x : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₐ[ℂ] ℂ) =
      complexSmoothVanishingIdeal I x :=
  Ideal.ext fun _ ↦ by simp

/-! ### The commutator symbol -/

variable (I) in
/-- The commutator symbol of a differential operator `D` of order at most `m` on complex smooth
functions at an interior point `x`: the complex-multilinear form on the complex-valued covectors
`T_x M →L[ℝ] ℂ` sending `(df₁(x), …, dfₘ(x))` to the value at `x` of the iterated commutator
`[⋯[D, f₁], …, fₘ] 1` (`TauCeti.complexSmoothCommutatorSymbol_mvfderiv`). It is the point
commutator symbol `TauCeti.pointCommutatorSymbol` of evaluation at `x`, read through
`I_x / I_x² ≃ (T_x M →L[ℝ] ℂ)`. It is symmetric (`TauCeti.complexSmoothCommutatorSymbol_comp_perm`)
and `m!` times the polarization of the principal symbol `TauCeti.complexSmoothPrincipalSymbol`. -/
def complexSmoothCommutatorSymbol (hx : I.IsInteriorPoint x) {m : ℕ} :
    differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
        C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun _ : Fin m ↦ TangentSpace I x →L[ℝ] ℂ) ℂ :=
  pointCommutatorSymbol (ContMDiffMap.complexEvalAlgHom x) (complexSmoothCotangentEquiv hx)

/-- The commutator symbol at `x`, evaluated on the differentials at `x` of complex smooth
functions `f₁, …, fₘ`, is the value at `x` of the iterated commutator `[⋯[D, f₁], …, fₘ] 1`. -/
theorem complexSmoothCommutatorSymbol_mvfderiv (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (f : Fin m → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexSmoothCommutatorSymbol I hx D (fun i ↦ mvfderiv I (f i) x) =
      commutatorSymbol ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
        C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m D f 1 x := by
  -- The differential of `fᵢ` is that of `fᵢ - fᵢ(x)`, which lies in `I_x`.
  have hc (c : ℂ) : ⇑(algebraMap ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ c) = fun _ ↦ c := funext fun _ ↦ by simp
  have hd (i : Fin m) : mvfderiv I (f i) x = complexSmoothCotangentEquiv hx
      ((complexSmoothVanishingIdeal I x).toCotangent
        ⟨f i + algebraMap ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ (-f i x), by simp⟩) := by
    rw [complexSmoothCotangentEquiv_toCotangent, ContMDiffMap.coe_add, hc,
      mvfderiv_add ((f i).contMDiff.mdifferentiable (by simp) x) mdifferentiableAt_const,
      mvfderiv_const, add_zero]
  simp only [hd]
  rw [complexSmoothCommutatorSymbol,
    pointCommutatorSymbol_toCotangent _ (ker_complexEvalAlgHom x).ge,
    commutatorSymbol_add_algebraMap, ContMDiffMap.complexEvalAlgHom_apply]

/-- The commutator symbol is symmetric. -/
theorem complexSmoothCommutatorSymbol_comp_perm (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℂ) (σ : Equiv.Perm (Fin m)) :
    complexSmoothCommutatorSymbol I hx D (ξ ∘ σ) = complexSmoothCommutatorSymbol I hx D ξ :=
  pointCommutatorSymbol_comp_perm _ (ker_complexEvalAlgHom x).ge D ξ σ

/-- **Comparison with the cotangent symbol.** The commutator symbol at `x` is the cotangent symbol
`TauCeti.cotangentSymbol` of the complex vanishing ideal `I_x`, read through the identification
`I_x / I_x² ≃ (T_x M →L[ℝ] ℂ)` and evaluation at `x`: the class modulo `I_x` of the constant
function with value `σ(u₁, …, uₘ)` is the image of the class of `1` under the cotangent symbol at
`(u₁, …, uₘ)`. -/
theorem mk_algebraMap_complexSmoothCommutatorSymbol (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (u : Fin m → (complexSmoothVanishingIdeal I x).Cotangent) :
    Submodule.Quotient.mk
        (p := (complexSmoothVanishingIdeal I x • ⊤ : Submodule C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ _))
        (algebraMap ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
          (complexSmoothCommutatorSymbol I hx D fun i ↦ complexSmoothCotangentEquiv hx (u i))) =
      cotangentSymbol ℂ (complexSmoothVanishingIdeal I x) D u (Submodule.Quotient.mk 1) :=
  mk_algebraMap_pointCommutatorSymbol _ (ker_complexEvalAlgHom x) D u

/-- The commutator symbol of an operator of order at most `m + 1` on complex smooth functions
vanishes at every interior point if the operator has order at most `m`. -/
theorem complexSmoothCommutatorSymbol_eq_zero_of_mem_differentialOperators
    (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ (m + 1))
    (hD : (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) ∈
      differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
        C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m) :
    complexSmoothCommutatorSymbol I hx D = 0 :=
  pointCommutatorSymbol_eq_zero_of_mem_differentialOperators _ (ker_complexEvalAlgHom x).ge D hD

/-- On a boundaryless manifold, an operator of order at most `m + 1` on complex smooth functions
has vanishing commutator symbol at every point if and only if it has order at most `m`. -/
theorem forall_complexSmoothCommutatorSymbol_eq_zero_iff [BoundarylessManifold I M] {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ (m + 1)) :
    (∀ x : M,
        complexSmoothCommutatorSymbol I (BoundarylessManifold.isInteriorPoint (x := x)) D = 0) ↔
      (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) ∈
        differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
          C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m := by
  rw [← commutatorSymbol_eq_zero_iff]
  constructor
  · intro h
    -- The iterated commutators are linear over the complex smooth functions, so it suffices that
    -- their values at `1` vanish at every point.
    refine MultilinearMap.ext fun f ↦ LinearMap.ext_ring <| ContMDiffMap.ext fun y ↦ ?_
    rw [← complexSmoothCommutatorSymbol_mvfderiv BoundarylessManifold.isInteriorPoint, h y]
    simp
  · exact fun h x ↦ complexSmoothCommutatorSymbol_eq_zero_of_mem_differentialOperators _ D
      ((commutatorSymbol_eq_zero_iff D).1 h)

/-! ### The principal symbol -/

variable (I) in
/-- The principal symbol of a differential operator `D` of order at most `m` on complex smooth
functions at an interior point `x`, in the geometric convention: the homogeneous function of
degree `m` on the complex-valued covectors `T_x M →L[ℝ] ℂ` given by
`σ_geom(D)(df_x) = (1 / m!) ([⋯[D, f], …, f] 1)(x)`, with `m` copies of `f`
(`TauCeti.complexSmoothPrincipalSymbol_mvfderiv`). Its polarization is `1 / m!` times the
commutator symbol `TauCeti.complexSmoothCommutatorSymbol`. -/
def complexSmoothPrincipalSymbol (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℂ) : ℂ :=
  pointPrincipalSymbol (ContMDiffMap.complexEvalAlgHom x) (complexSmoothCotangentEquiv hx) D ξ

theorem complexSmoothPrincipalSymbol_def (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I hx D ξ =
      (m.factorial : ℂ)⁻¹ * complexSmoothCommutatorSymbol I hx D fun _ ↦ ξ :=
  pointPrincipalSymbol_def _ _ D ξ

/-- The principal symbol at the differential of `f` is `1 / m!` times the value at `x` of the
`m`-fold commutator `[⋯[D, f], …, f] 1`. -/
theorem complexSmoothPrincipalSymbol_mvfderiv (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexSmoothPrincipalSymbol I hx D (mvfderiv I f x) =
      (m.factorial : ℂ)⁻¹ * (smulCommutator ℂ f ^ m)
        (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) 1 x := by
  rw [complexSmoothPrincipalSymbol_def, complexSmoothCommutatorSymbol_mvfderiv hx D fun _ ↦ f,
    commutatorSymbol_const_apply]

@[simp]
theorem complexSmoothPrincipalSymbol_zero (hx : I.IsInteriorPoint x) {m : ℕ}
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I hx
      (0 : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
        C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m) ξ = 0 :=
  pointPrincipalSymbol_zero _ _ ξ

@[simp]
theorem complexSmoothPrincipalSymbol_add (hx : I.IsInteriorPoint x) {m : ℕ}
    (D₁ D₂ : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I hx (D₁ + D₂) ξ =
      complexSmoothPrincipalSymbol I hx D₁ ξ + complexSmoothPrincipalSymbol I hx D₂ ξ :=
  pointPrincipalSymbol_add _ _ D₁ D₂ ξ

@[simp]
theorem complexSmoothPrincipalSymbol_smul (hx : I.IsInteriorPoint x) {m : ℕ} (c : ℂ)
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I hx (c • D) ξ = c * complexSmoothPrincipalSymbol I hx D ξ :=
  pointPrincipalSymbol_smul _ _ c D ξ

/-- The principal symbol of an operator of order at most `m` is homogeneous of degree `m` under
complex scalars. -/
theorem complexSmoothPrincipalSymbol_smul_covector (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m) (c : ℂ)
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I hx D (c • ξ) =
      c ^ m * complexSmoothPrincipalSymbol I hx D ξ :=
  pointPrincipalSymbol_smul_covector _ _ D c ξ

/-- The principal symbol of an operator of order at most `m + 1` on complex smooth functions
vanishes if the operator has order at most `m`. -/
theorem complexSmoothPrincipalSymbol_eq_zero_of_mem_differentialOperators
    (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ (m + 1))
    (hD : (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) ∈
      differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
        C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I hx D ξ = 0 :=
  pointPrincipalSymbol_eq_zero_of_mem_differentialOperators _ (ker_complexEvalAlgHom x).ge D hD ξ

/-- **Principal symbols multiply under composition.** For operators `P` and `Q` on complex smooth
functions of orders at most `m` and `k`, the principal symbol of `P ∘ Q`, as an operator of order
at most `m + k`, is the product of the principal symbols. -/
theorem complexSmoothPrincipalSymbol_comp (hx : I.IsInteriorPoint x) {m k : ℕ}
    (P : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ m)
    (Q : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ k)
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I hx
        ⟨(P : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) ∘ₗ
            (Q : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯),
          comp_mem_differentialOperators P.2 Q.2⟩ ξ =
      complexSmoothPrincipalSymbol I hx P ξ * complexSmoothPrincipalSymbol I hx Q ξ :=
  pointPrincipalSymbol_comp _ (ker_complexEvalAlgHom x).ge P Q ξ

/-! ### First-order operators -/

/-- The principal symbol of an operator `D` of order at most one at `df_x` is
`(D f)(x) - f(x) (D 1)(x)`. -/
theorem complexSmoothPrincipalSymbol_one_mvfderiv (hx : I.IsInteriorPoint x)
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ 1)
    (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexSmoothPrincipalSymbol I hx D (mvfderiv I f x) =
      (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) f x -
        f x * (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) 1 x := by
  rw [complexSmoothPrincipalSymbol_def, Nat.factorial_one, Nat.cast_one, inv_one, one_mul,
    complexSmoothCommutatorSymbol_mvfderiv hx _ fun _ ↦ f, ← Matrix.vec_single_eq_const f,
    commutatorSymbol_one_apply, one_smul, smul_eq_mul, ContMDiffMap.coe_sub, Pi.sub_apply,
    ContMDiffMap.coe_mul, Pi.mul_apply]

/-- The principal symbol of a derivation `δ` of the complex smooth functions at `df_x` is
`(δ f)(x)`. -/
theorem complexSmoothPrincipalSymbol_derivation_mvfderiv (hx : I.IsInteriorPoint x)
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexSmoothPrincipalSymbol I hx ⟨δ, δ.mem_differentialOperators_one⟩ (mvfderiv I f x) =
      δ f x := by
  rw [complexSmoothPrincipalSymbol_one_mvfderiv]
  simp

variable [BoundarylessManifold I M]

/-- **Operators of order at most one on complex smooth functions.** On a finite-dimensional,
Hausdorff, boundaryless real manifold, a complex-linear endomorphism of `C^∞(M, ℂ)` of order at most
one, that is with vanishing double commutators with multiplication operators, splits into a
complexified vector field and multiplication by a function, linearly over `ℂ`: the operator
`f ↦ df(X) + i df(Y) + c f` corresponds to `(1 ⊗ X + i ⊗ Y, c)`
(`TauCeti.differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm_apply_apply`). The second
coordinate is the value of the operator on one. -/
def differentialOperatorsOneEquivComplexifiedVectorFieldProd :
    differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
        C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ 1 ≃ₗ[ℂ]
      (ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  (differentialOperatorsOneEquiv ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).trans
    (complexDerivationEquivComplexifiedVectorField.prodCongr (LinearEquiv.refl _ _))

/-- The complexified vector field of an operator of order at most one is that of its derivation
part `f ↦ D f - f D(1)`. -/
theorem differentialOperatorsOneEquivComplexifiedVectorFieldProd_apply_fst
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ 1) :
    (differentialOperatorsOneEquivComplexifiedVectorFieldProd D).1 =
      complexDerivationEquivComplexifiedVectorField
        (differentialOperatorsOneEquiv ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ D).1 :=
  (rfl)

/-- The multiplication coefficient of an operator of order at most one is its value on one. -/
@[simp]
theorem differentialOperatorsOneEquivComplexifiedVectorFieldProd_apply_snd
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ 1) :
    (differentialOperatorsOneEquivComplexifiedVectorFieldProd D).2 =
      (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) 1 := by
  simp [differentialOperatorsOneEquivComplexifiedVectorFieldProd]

/-- The operator corresponding to `(v, c)` is the derivation corresponding to `v` plus
multiplication by `c`. -/
@[simp]
theorem coe_differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm_apply
    (p : (ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (differentialOperatorsOneEquivComplexifiedVectorFieldProd.symm p :
        C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) =
      (complexDerivationEquivComplexifiedVectorField.symm p.1).toLinearMap +
        LinearMap.mulLeft ℂ p.2 := by
  ext f : 1
  simp [differentialOperatorsOneEquivComplexifiedVectorFieldProd, mul_comm]

/-- The operator corresponding to `(1 ⊗ X + i ⊗ Y, c)` acts by `f ↦ df(X) + i df(Y) + c f`. -/
theorem differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm_apply_apply
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (c f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    (differentialOperatorsOneEquivComplexifiedVectorFieldProd.symm
        (1 ⊗ₜ X + Complex.I ⊗ₜ Y, c) : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) f x =
      mvfderiv I f x (X x) + Complex.I * mvfderiv I f x (Y x) + f x * c x := by
  rw [coe_differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm_apply, LinearMap.add_apply,
    Derivation.coeFn_coe, ContMDiffMap.coe_add, Pi.add_apply,
    complexDerivationEquivComplexifiedVectorField_symm_apply_eq_mvfderiv]
  simp [mul_comm]

/-- **The splitting of operators of order at most one.** An operator of order at most one on
complex smooth functions acts by `f ↦ df(X) + i df(Y) + f D(1)`, where `1 ⊗ X + i ⊗ Y` is its
complexified vector field. -/
theorem differentialOperators_one_apply_eq_mvfderiv_add_I_mul_mvfderiv_add_mul
    (D : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ 1)
    (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) f x =
      mvfderiv I f x (realPart _ (differentialOperatorsOneEquivComplexifiedVectorFieldProd D).1 x) +
        Complex.I * mvfderiv I f x
          (imaginaryPart _ (differentialOperatorsOneEquivComplexifiedVectorFieldProd D).1 x) +
          f x * (D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) 1 x := by
  conv_lhs => rw [← differentialOperatorsOneEquivComplexifiedVectorFieldProd.symm_apply_apply D,
    coe_differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm_apply]
  simp [complexDerivationEquivComplexifiedVectorField_symm_apply_eq_mvfderiv, mul_comm]

/-- Vanishing double commutators characterize the unique expression of a complex-linear operator
on complex smooth functions as `f ↦ df(X) + i df(Y) + c f`, for smooth vector fields `X`, `Y` and
a complex smooth function `c`. -/
theorem mem_differentialOperators_one_iff_existsUnique_vectorField_mul
    {D : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} :
    D ∈ differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
        C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ 1 ↔
      ∃! p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ ×
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∀ (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M),
          D f x = mvfderiv I f x (p.1 x) + Complex.I * mvfderiv I f x (p.2.1 x) +
            f x * p.2.2 x := by
  set e := differentialOperatorsOneEquivComplexifiedVectorFieldProd (I := I) (M := M)
  have hrep (p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ ×
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
      (∀ (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M),
        D f x = mvfderiv I f x (p.1 x) + Complex.I * mvfderiv I f x (p.2.1 x) +
          f x * p.2.2 x) ↔
      D = e.symm (1 ⊗ₜ p.1 + Complex.I ⊗ₜ p.2.1, p.2.2) := by
    constructor
    · intro h
      ext f x
      rw [h f x, differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm_apply_apply]
    · intro h f x
      rw [h, differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm_apply_apply]
  constructor
  · intro hD
    let d : differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯
      C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ 1 := ⟨D, hD⟩
    refine ⟨(realPart _ (e d).1, imaginaryPart _ (e d).1, D 1),
      differentialOperators_one_apply_eq_mvfderiv_add_I_mul_mvfderiv_add_mul d, ?_⟩
    rintro ⟨X, Y, c⟩ hp
    have h := congrArg e (Subtype.ext ((hrep _).mp hp) : d = _)
    rw [LinearEquiv.apply_symm_apply, Prod.ext_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    simp only at h₁ h₂
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [h₁]
    · simp [h₁]
    · rw [← h₂]
      exact differentialOperatorsOneEquivComplexifiedVectorFieldProd_apply_snd d
  · rintro ⟨p, hp, -⟩
    rw [(hrep p).mp hp]
    exact (e.symm _).property

/-- The principal symbol of the operator of order at most one corresponding to `(v, c)` is
`ξ ↦ ξ(X_x) + i ξ(Y_x)`, where `v = 1 ⊗ X + i ⊗ Y`. -/
@[simp]
theorem complexSmoothPrincipalSymbol_differentialOperatorsOneEquivComplexifiedVectorFieldProd_symm
    (p : (ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) × C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I BoundarylessManifold.isInteriorPoint
        (differentialOperatorsOneEquivComplexifiedVectorFieldProd.symm p) ξ =
      ξ (realPart _ p.1 x) + Complex.I * ξ (imaginaryPart _ p.1 x) := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℂ) ξ
  rw [complexSmoothPrincipalSymbol_one_mvfderiv]
  simp [complexDerivationEquivComplexifiedVectorField_symm_apply_eq_mvfderiv, mul_comm]

/-- On a boundaryless manifold, a derivation `δ` of the complex smooth functions has principal
symbol `ξ ↦ ξ(X_x) + i ξ(Y_x)`, where `1 ⊗ X + i ⊗ Y` is its complexified vector field. -/
@[simp]
theorem complexSmoothPrincipalSymbol_derivation
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (ξ : TangentSpace I x →L[ℝ] ℂ) :
    complexSmoothPrincipalSymbol I BoundarylessManifold.isInteriorPoint
        ⟨δ, δ.mem_differentialOperators_one⟩ ξ =
      ξ (realPart _ (complexDerivationEquivComplexifiedVectorField δ) x) +
        Complex.I * ξ (imaginaryPart _ (complexDerivationEquivComplexifiedVectorField δ) x) := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℂ) ξ
  rw [complexSmoothPrincipalSymbol_derivation_mvfderiv,
    ← complexDerivationEquivComplexifiedVectorField_symm_apply_eq_mvfderiv,
    LinearEquiv.symm_apply_apply]

end TauCeti
