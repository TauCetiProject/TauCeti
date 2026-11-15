/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# Laplace-type operators on smooth functions

Let `M` be a finite-dimensional Hausdorff manifold with a Riemannian metric. A differential
operator `D` of order at most two on the smooth functions `C^∞(M)`, in Grothendieck's sense
(`TauCeti.differentialOperators`), is of *Laplace type* with constant `c > 0` if its principal
symbol in the Fourier convention is `ξ ↦ c ‖ξ‖²`, where `‖ξ‖` is the norm the metric induces on
the cotangent space. Since `∂ⱼ` has Fourier symbol `i ξⱼ`, for a second-order operator this is the
condition `σ_geom(D)(ξ) = -(c ‖ξ‖²)` on the geometric principal symbol
`TauCeti.smoothPrincipalSymbol`, defined by iterated commutators with multiplication operators.
These are the second-order operators whose heat kernel and elliptic theory is modelled on that of
the Laplacian.

The model example is the Laplace–Beltrami operator `Δ = div ∘ grad`
(`TauCeti.Manifold.laplaceBeltrami`). Its Leibniz rule
`Δ (f h) = f Δh + 2 ⟪grad f, grad h⟫ + h Δf` shows that its commutator with multiplication by `f`
is `h ↦ h Δf + 2 ⟪grad f, grad h⟫` and that its double commutators are multiplication by
`2 ⟪grad f, grad g⟫`. Hence it has order at most two and principal symbol `ξ ↦ ‖ξ‖²`, so that
`-Δ` is of Laplace type with constant `1`. No continuity of operators is assumed anywhere.

## Main definitions

* `TauCeti.smoothLaplaceBeltrami I M`: the Laplace–Beltrami operator of a smooth metric as a
  real-linear endomorphism of `C^∞(M)`.
* `TauCeti.IsLaplaceType D c`: `D` is of Laplace type with constant `c`.

## Main results

* `TauCeti.smulCommutator_smulCommutator_smoothLaplaceBeltrami_apply`: the double commutators
  `[[Δ, f], g] h = 2 ⟪grad f, grad g⟫ h`.
* `TauCeti.smoothLaplaceBeltrami_mem_differentialOperators_two`: `Δ` has order at most two.
* `TauCeti.smoothPrincipalSymbol_smoothLaplaceBeltrami`: `σ_geom(Δ)(ξ) = ‖ξ‖²`.
* `TauCeti.isLaplaceType_neg_smoothLaplaceBeltrami`: `-Δ` is of Laplace type with constant `1`,
  whereas `Δ` itself is not of Laplace type in positive dimension
  (`TauCeti.not_isLaplaceType_smoothLaplaceBeltrami`).
* `TauCeti.IsLaplaceType.smul`: positive rescaling multiplies the constant.
* `TauCeti.IsLaplaceType.add_of_mem_differentialOperators_one`: perturbations of order at most one,
  such as potentials `-Δ + V`, keep the Laplace type.
* `TauCeti.IsLaplaceType.unique`: in positive dimension the constant is determined by the operator.
* `TauCeti.IsLaplaceType.conjDifferentialOperators`: the Laplace type is invariant under
  transport along diffeomorphisms which are Riemannian isometries.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (generalized Laplacians, Definition 2.2).
* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2 (operators of Laplace type).
-/

public section

open Bundle TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-! ### Laplace-type operators -/

section IsLaplaceType

variable [T2Space M]

/-- A differential operator `D` of order at most two on the smooth functions of a Riemannian
manifold is of **Laplace type** with constant `c` if `0 < c` and, at every interior point `x`, its
principal symbol in the Fourier convention is `ξ ↦ c ‖ξ‖²`, the norm being the one the metric
induces on `T_x*M`. The Fourier symbol of `∂ⱼ` is `i ξⱼ`, so for operators of order two the
Fourier principal symbol is `-1` times the geometric one `TauCeti.smoothPrincipalSymbol`, and the
condition reads `σ_geom(D)(ξ) = -(c ‖ξ‖²)`. For example `-Δ` is of Laplace type with constant `1`
(`TauCeti.isLaplaceType_neg_smoothLaplaceBeltrami`). -/
def IsLaplaceType (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 2)
    (c : ℝ) : Prop :=
  0 < c ∧ ∀ (x : M) (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ),
    smoothPrincipalSymbol I hx D ξ = -(c * ‖ξ‖ ^ 2)

variable {D Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 2} {c c' : ℝ}

theorem isLaplaceType_iff : IsLaplaceType D c ↔ 0 < c ∧ ∀ (x : M) (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ), smoothPrincipalSymbol I hx D ξ = -(c * ‖ξ‖ ^ 2) :=
  Iff.rfl

/-- The constant of an operator of Laplace type is positive. -/
theorem IsLaplaceType.pos (hD : IsLaplaceType D c) : 0 < c :=
  hD.1

/-- The geometric principal symbol of an operator of Laplace type with constant `c` is
`ξ ↦ -(c ‖ξ‖²)` at every interior point. -/
theorem IsLaplaceType.smoothPrincipalSymbol_eq (hD : IsLaplaceType D c) {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx D ξ = -(c * ‖ξ‖ ^ 2) :=
  hD.2 x hx ξ

/-- A positive multiple of an operator of Laplace type is of Laplace type, with the constant
multiplied accordingly. -/
theorem IsLaplaceType.smul (hD : IsLaplaceType D c) {t : ℝ} (ht : 0 < t) :
    IsLaplaceType (t • D) (t * c) :=
  ⟨mul_pos ht hD.pos, fun x hx ξ ↦ by
    rw [smoothPrincipalSymbol_smul, hD.smoothPrincipalSymbol_eq]
    ring⟩

/-- Adding an operator of order at most one does not change the Laplace type. -/
theorem IsLaplaceType.add_of_mem_differentialOperators_one (hD : IsLaplaceType D c)
    (hQ : (Q : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 1) :
    IsLaplaceType (D + Q) c :=
  ⟨hD.pos, fun x hx ξ ↦ by
    rw [smoothPrincipalSymbol_add, hD.smoothPrincipalSymbol_eq,
      smoothPrincipalSymbol_eq_zero_of_mem_differentialOperators hx Q hQ, add_zero]⟩

/-- On a manifold of positive dimension the constant of an operator of Laplace type is unique,
as soon as there is an interior point. -/
theorem IsLaplaceType.unique [Nontrivial E] {x : M} (hx : I.IsInteriorPoint x)
    (hD : IsLaplaceType D c) (hD' : IsLaplaceType D c') : c = c' := by
  -- `TangentSpace I x` is `E`, so it is nontrivial and carries a nonzero covector.
  have : Nontrivial (TangentSpace I x) := inferInstanceAs (Nontrivial E)
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : TangentSpace I x →L[ℝ] ℝ)
  have hξ := (norm_pos_iff (E := TangentSpace I x →L[ℝ] ℝ)).2 hξ
  have h := (hD.smoothPrincipalSymbol_eq hx ξ).symm.trans (hD'.smoothPrincipalSymbol_eq hx ξ)
  exact mul_right_cancel₀ (pow_pos hξ 2).ne' (neg_inj.1 h)

section Isometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- **Invariance under isometries.** Transporting an operator of Laplace type along a
diffeomorphism `φ : N → M` which is a Riemannian isometry, by conjugation with the pullback
`f ↦ f ∘ φ` of functions, gives an operator of Laplace type with the same constant. -/
theorem IsLaplaceType.conjDifferentialOperators (hD : IsLaplaceType D c) (φ : N ≃ₘ⟮J, I⟯ M)
    (hφ : IsLocalRiemannianIsometry J I φ) :
    IsLaplaceType ((φ.compRightAlgEquiv ℝ ℝ).conjDifferentialOperators 2 D) c := by
  refine ⟨hD.pos, fun y hy η ↦ ?_⟩
  have hx : I.IsInteriorPoint (φ y) :=
    ((φ.isLocalDiffeomorph y).isInteriorPoint_iff (by simp)).1 hy
  -- Write `η` as the pullback `η' ∘ dφ_y` of the covector `η' = η ∘ (dφ_y)⁻¹`, which has the same
  -- norm since `dφ_y` is a linear isometric equivalence.
  obtain ⟨e, he⟩ := hφ.exists_linearIsometryEquiv_eq_mfderiv y
  have hη : η = (η.comp (e.symm : TangentSpace I (φ y) →L[ℝ] TangentSpace J y)).comp
      (mfderiv J I φ y) := by
    ext v
    simp [← he v]
  conv_lhs => rw [hη]
  rw [smoothPrincipalSymbol_conjDifferentialOperators φ hy hx, hD.smoothPrincipalSymbol_eq hx,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end Isometry

end IsLaplaceType

/-! ### The Laplace–Beltrami operator on smooth functions -/

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The Laplace–Beltrami operator `Δ = div ∘ grad` (`TauCeti.Manifold.laplaceBeltrami`) of a
smooth Riemannian metric, as a real-linear endomorphism of the smooth functions. -/
def smoothLaplaceBeltrami : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun f := ⟨laplaceBeltrami I f,
    contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp) f.contMDiff⟩
  map_add' f g := ContMDiffMap.ext fun x ↦
    laplaceBeltrami_add I (f.contMDiff.of_le (by simp)) (g.contMDiff.of_le (by simp)) x
  map_smul' c f := ContMDiffMap.ext fun x ↦
    laplaceBeltrami_smul I c (f.contMDiff.of_le (by simp)) x

@[simp]
theorem smoothLaplaceBeltrami_apply (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    smoothLaplaceBeltrami I M f x = laplaceBeltrami I f x :=
  (rfl)

/-- The commutator of the Laplace–Beltrami operator with multiplication by `f`:
`[Δ, f] h = h Δf + 2 ⟪grad f, grad h⟫`. -/
theorem smulCommutator_smoothLaplaceBeltrami_apply (f h : C^∞⟮I, M; ℝ⟯) (x : M) :
    smulCommutator ℝ f (smoothLaplaceBeltrami I M) h x =
      h x * laplaceBeltrami I f x + 2 * inner ℝ (mgradient I f x) (mgradient I h x) := by
  have hf : ContMDiff I 𝓘(ℝ) 2 f := f.contMDiff.of_le (by simp)
  have hh : ContMDiff I 𝓘(ℝ) 2 h := h.contMDiff.of_le (by simp)
  simp only [smulCommutator_apply_apply, smul_eq_mul, ContMDiffMap.coe_sub, ContMDiffMap.coe_mul,
    Pi.sub_apply, Pi.mul_apply, smoothLaplaceBeltrami_apply, laplaceBeltrami_mul I hf hh]
  ring

/-- The double commutator of the Laplace–Beltrami operator is multiplication by twice the inner
product of the gradients: `[[Δ, f], g] h = 2 ⟪grad f, grad g⟫ h`. -/
theorem smulCommutator_smulCommutator_smoothLaplaceBeltrami_apply (f g h : C^∞⟮I, M; ℝ⟯)
    (x : M) :
    smulCommutator ℝ g (smulCommutator ℝ f (smoothLaplaceBeltrami I M)) h x =
      2 * inner ℝ (mgradient I f x) (mgradient I g x) * h x := by
  have hg : MDifferentiable I 𝓘(ℝ) g := g.contMDiff.mdifferentiable (by simp)
  have hh : MDifferentiable I 𝓘(ℝ) h := h.contMDiff.mdifferentiable (by simp)
  simp only [smulCommutator_apply_apply (a := g), ContMDiffMap.coe_sub, Pi.sub_apply, smul_eq_mul,
    ContMDiffMap.coe_mul, Pi.mul_apply, smulCommutator_smoothLaplaceBeltrami_apply,
    mgradient_mul hg hh, inner_add_right, real_inner_smul_right]
  ring

/-- The Laplace–Beltrami operator is a differential operator of order at most two. -/
theorem smoothLaplaceBeltrami_mem_differentialOperators_two :
    smoothLaplaceBeltrami I M ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 2 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦ mem_differentialOperators_succ_iff.2
    fun g ↦ mem_differentialOperators_zero_iff.2 fun a h ↦ ContMDiffMap.ext fun x ↦ ?_
  simp only [smulCommutator_smulCommutator_smoothLaplaceBeltrami_apply, smul_eq_mul,
    ContMDiffMap.coe_mul, Pi.mul_apply]
  ring

/-- The principal symbol of the Laplace–Beltrami operator `Δ = div ∘ grad` is the squared norm
`ξ ↦ ‖ξ‖²` of covectors. -/
@[simp]
theorem smoothPrincipalSymbol_smoothLaplaceBeltrami [T2Space M] {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx
      ⟨smoothLaplaceBeltrami I M, smoothLaplaceBeltrami_mem_differentialOperators_two⟩ ξ =
        ‖ξ‖ ^ 2 := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
  rw [smoothPrincipalSymbol_mvfderiv, pow_two (smulCommutator ℝ f), mul_apply_eq_comp,
    smulCommutator_smulCommutator_smoothLaplaceBeltrami_apply, real_inner_self_eq_norm_sq,
    norm_mgradient_eq_norm_mvfderiv]
  simp [Nat.factorial]

/-- The negative `-Δ` of the Laplace–Beltrami operator is of Laplace type with constant `1`. -/
theorem isLaplaceType_neg_smoothLaplaceBeltrami [T2Space M] :
    IsLaplaceType
      (-⟨smoothLaplaceBeltrami I M, smoothLaplaceBeltrami_mem_differentialOperators_two⟩) 1 :=
  ⟨one_pos, fun x hx ξ ↦ by
    rw [← neg_one_smul ℝ (⟨_, _⟩ : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ _ _ 2),
      smoothPrincipalSymbol_smul, smoothPrincipalSymbol_smoothLaplaceBeltrami]
    ring⟩

/-- On a manifold of positive dimension with an interior point, the Laplace–Beltrami operator
`Δ = div ∘ grad` itself is not of Laplace type: its Fourier principal symbol is `-‖ξ‖²`. -/
theorem not_isLaplaceType_smoothLaplaceBeltrami [T2Space M] [Nontrivial E] {x : M}
    (hx : I.IsInteriorPoint x) (c : ℝ) :
    ¬IsLaplaceType ⟨smoothLaplaceBeltrami I M, smoothLaplaceBeltrami_mem_differentialOperators_two⟩
      c := by
  intro hD
  -- `TangentSpace I x` is `E`, so it is nontrivial and carries a nonzero covector.
  have : Nontrivial (TangentSpace I x) := inferInstanceAs (Nontrivial E)
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : TangentSpace I x →L[ℝ] ℝ)
  have hξ := (norm_pos_iff (E := TangentSpace I x →L[ℝ] ℝ)).2 hξ
  have h := hD.smoothPrincipalSymbol_eq hx ξ
  rw [smoothPrincipalSymbol_smoothLaplaceBeltrami] at h
  nlinarith [hD.pos, pow_pos hξ 2]

end TauCeti
