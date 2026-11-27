/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.PrincipalSymbol
public import TauCeti.Geometry.Manifold.DifferentialOperator.Elliptic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ComplexModule
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# The principal symbol of a differential operator between vector bundles

Let `M` be a manifold modelled on `ℝⁿ`, and let `E` and `F` be smooth complex vector bundles over
`M` with finite-dimensional model fibres, whose real structures are the restrictions of their
complex ones. A complex-linear operator `P : Γ(E) → Γ(F)` which is a differential operator of
order at most `k` in Grothendieck's sense, for commutators with multiplication by complex-valued
smooth functions, has two principal symbols at a covector `ξ ∈ T*ₓM`:

* as a classical pseudodifferential operator of order `k` between the bundles
  (`TauCeti.mem_sectionClassicalPseudodifferentialOperators_of_mem_differentialOperators`), its
  principal symbol `σ_k(P)(x, ξ) : E_x → F_x` (`TauCeti.sectionClassicalPrincipalSymbol`), read off
  from the principal symbols of its scalar matrix entries in frames;
* as a real differential operator of order at most `k` for commutators with real-valued functions
  (`TauCeti.restrictScalars_mem_differentialOperators_real`), its geometric principal symbol
  `σ_geom(P)(ξ) : E_x → F_x` (`TauCeti.sectionPrincipalSymbol`), defined by
  `σ_geom(P)(df_x) s(x) = (1 / k!) ([⋯[P, f], …, f] s)(x)` with `k` commutators.

This file shows that they agree up to the factor of the Fourier convention: at every nonzero
covector,

`σ_k(P)(x, ξ) = i ^ k σ_geom(P)(ξ)`

(`TauCeti.sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators`). This is the bundle
version of `TauCeti.classicalPrincipalSymbol_complexifyLinearMap`. Both sides are read from the
`k`-fold commutator of `P` with a real function `f` at `ξ = df_x`:
`σ_k(P)(x, df_x) (s x) = (i ^ k / k!) ([⋯[P, f], …, f] s)(x)`
(`TauCeti.sectionClassicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators`), and the
commutators of `P` as a real operator with `f` are those of `P` with `f` viewed as a complex
function (`TauCeti.smulCommutator_pow_restrictScalars_ofReal`). Since `i ^ k` is invertible,
`P` is elliptic as a classical pseudodifferential operator exactly when it is elliptic as a
differential operator (`TauCeti.isSectionClassicalEllipticAt_iff_isSectionEllipticAt`,
`TauCeti.isSectionClassicalElliptic_iff_isSectionElliptic`), so results on elliptic
pseudodifferential operators between bundles apply to elliptic differential operators.

## Main results

* `TauCeti.sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators`:
  `σ_k(P)(x, ξ) = i ^ k σ_geom(P)(ξ)` at nonzero covectors.
* `TauCeti.isSectionClassicalEllipticAt_iff_isSectionEllipticAt`,
  `TauCeti.isSectionClassicalElliptic_iff_isSectionElliptic`: the two notions of ellipticity
  agree.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (the principal
  symbol of a differential operator between sections of vector bundles).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §12.
-/

public section

noncomputable section

open Bundle Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle V E] [VectorBundle ℝ V E] [VectorBundle ℂ V E]
  [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, IsScalarTower ℝ ℂ (F x)]
  [∀ x, TopologicalSpace (F x)] [FiberBundle W F] [VectorBundle ℝ W F] [VectorBundle ℂ W F]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {k : ℕ}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

variable (hP : P ∈ differentialOperators ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯
  Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ k)

include hP

/-- **The principal symbol of a differential operator between bundles.** Let
`P : Γ(E) → Γ(F)` be a complex-linear differential operator of order at most `k` in Grothendieck's
sense, for commutators with multiplication by complex-valued smooth functions. At every nonzero
covector `ξ ∈ T*ₓM`, its principal symbol of order `k` as a classical pseudodifferential operator
between the bundles is `i ^ k` times its geometric principal symbol `σ_geom(P)(ξ)`
(`TauCeti.sectionPrincipalSymbol`), that of `P` as a real differential operator:
`σ_k(P)(x, ξ) = i ^ k σ_geom(P)(ξ)`. This is the angular-frequency convention `σ(∂ⱼ) = i ξⱼ`. -/
theorem sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators (x : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) (u : E x) :
    sectionClassicalPrincipalSymbol k P x ξ u = Complex.I ^ k •
      sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
        ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_real hP⟩ ξ u := by
  set t := trivializationAt V E x
  have hxt : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt V E x
  -- A bump function `ψ`, equal to `1` at `x` and supported in the base set of `t`.
  obtain ⟨ψ₀, -, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
    (I := 𝓘(ℝ, CoordinateSpace n)) x).mem_iff.1 (t.open_baseSet.mem_nhds hxt)
  set ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ := ⟨ψ₀, ψ₀.contMDiff⟩
  have hψx : ψ x = 1 := ψ₀.eq_one
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := 𝓘(ℝ, CoordinateSpace n)) x (0 : ℝ) ξ
  obtain ⟨v, rfl⟩ : ∃ v, t.symm x v = u := ⟨_, t.symm_apply_apply_mk hxt u⟩
  -- The frame section `s = ψ t⁻¹ v` takes the value `t⁻¹ₓ v` at `x`; both principal symbols at
  -- `df_x`, applied to `s(x)`, are read from the `k`-fold commutator of `P` with `f`.
  have hs : t.cutoffFrameSection ψ hψ v x = t.symm x v := by simp [hψx]
  rw [← hs, sectionClassicalPrincipalSymbol_mvfderiv_of_mem_differentialOperators hP f hξ,
    sectionPrincipalSymbol_mvfderiv, Subtype.coe_mk, smulCommutator_pow_restrictScalars_ofReal,
    LinearMap.restrictScalars_apply, ← algebraMap_smul ℂ (k.factorial : ℝ)⁻¹, smul_smul]
  congr 1
  simp [div_eq_mul_inv]

/-- **Ellipticity of differential operators between bundles.** A complex-linear differential
operator `P : Γ(E) → Γ(F)` of order at most `k`, for commutators with complex-valued smooth
functions, is elliptic at `x` as a classical pseudodifferential operator of order `k` exactly when
it is elliptic at `x` as a real differential operator (`TauCeti.IsSectionEllipticAt`): the two
principal symbols differ by the invertible factor `i ^ k`. -/
theorem isSectionClassicalEllipticAt_iff_isSectionEllipticAt (x : M) :
    IsSectionClassicalEllipticAt k P x ↔ IsSectionEllipticAt
      ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_real hP⟩ x := by
  have hu : IsUnit (Complex.I ^ k) := (IsUnit.pow k (isUnit_iff_ne_zero.2 Complex.I_ne_zero))
  -- Multiplication by the unit `i ^ k` is a bijection of the fibre `F_x`.
  have hbij : Function.Bijective fun w : F x ↦ Complex.I ^ k • w := by
    have h := MulAction.bijective (β := F x) hu.unit
    simp only [Units.smul_def, IsUnit.unit_spec] at h
    exact h
  have heq (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
      ⇑(sectionClassicalPrincipalSymbol k P x ξ) = (fun w : F x ↦ Complex.I ^ k • w) ∘
        sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
          ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_real hP⟩ ξ :=
    funext (sectionClassicalPrincipalSymbol_apply_of_mem_differentialOperators hP x hξ)
  rw [isSectionClassicalEllipticAt_iff, isSectionEllipticAt_iff]
  refine ⟨fun h hx ξ hξ ↦ ?_, fun h ξ hξ ↦ ?_⟩
  · rw [← Function.Bijective.of_comp_iff' hbij, ← heq ξ hξ]
    exact h ξ hξ
  · rw [heq ξ hξ, Function.Bijective.of_comp_iff' hbij]
    exact h _ ξ hξ

/-- **Ellipticity of differential operators between bundles.** A complex-linear differential
operator `P : Γ(E) → Γ(F)` of order at most `k`, for commutators with complex-valued smooth
functions, is elliptic as a classical pseudodifferential operator of order `k` exactly when it is
elliptic as a real differential operator (`TauCeti.IsSectionElliptic`). -/
theorem isSectionClassicalElliptic_iff_isSectionElliptic :
    IsSectionClassicalElliptic k P ↔ IsSectionElliptic
      ⟨P.restrictScalars ℝ, restrictScalars_mem_differentialOperators_real hP⟩ := by
  rw [isSectionClassicalElliptic_iff, isSectionElliptic_iff]
  exact forall_congr' fun x ↦ isSectionClassicalEllipticAt_iff_isSectionEllipticAt hP x

end TauCeti
