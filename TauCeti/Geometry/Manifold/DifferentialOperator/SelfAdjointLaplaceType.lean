/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType
public import TauCeti.Geometry.Manifold.DifferentialOperator.Transpose.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# Formally self-adjoint operators of Laplace type on smooth functions

Let `M` be a Riemannian manifold without boundary, with its Riemannian volume `dV`
(`TauCeti.riemannianVolume`). By Green's second identity the Laplace–Beltrami operator
`Δ = div ∘ grad` is formally self-adjoint with respect to `dV`: `∫ (Δf) g dV = ∫ f (Δg) dV`
whenever `f` or `g` has compact support (`TauCeti.isFormalTranspose_smoothLaplaceBeltrami`).

An operator `D` of Laplace type with constant `c` (`TauCeti.IsLaplaceType`) and `-c Δ` have the
same principal symbol `ξ ↦ -(c ‖ξ‖²)` in the geometric convention, so `D + c Δ` has order at most
one (`TauCeti.forall_smoothPrincipalSymbol_eq_zero_iff`). In general this
first-order part contains a derivation, the term that the Bochner connection of `D` absorbs. If
`D` is formally self-adjoint for `dV`, then so is `D + c Δ`, and a formally self-adjoint operator
of order at most one has order zero
(`LinearMap.IsFormalTranspose.mem_differentialOperators_two_mul_of_self`). Hence a formally
self-adjoint operator of Laplace type is a Schrödinger operator `D = -c Δ + V` with potential
`V = D 1`, and conversely (`TauCeti.IsLaplaceType.isFormalTranspose_self_iff`). For scalar
functions this is the statement that the Bochner connection of such an operator is the trivial
connection `d`, which is metric, with zeroth-order remainder given by the potential.

The statement depends on the measure: it is the Riemannian volume for which `Δ` itself is
formally self-adjoint. For a weighted measure `e^w dV`, the formally self-adjoint operators of
Laplace type with constant `1` include `-Δ - dw(grad ·)`, whose first-order part is nonzero
unless `w` is locally constant.

## Main results

* `TauCeti.isFormalTranspose_smoothLaplaceBeltrami`: `Δ` is formally self-adjoint for the
  Riemannian volume.
* `TauCeti.IsLaplaceType.isFormalTranspose_self_iff`: an operator `D` of Laplace type with
  constant `c` is formally self-adjoint for the Riemannian volume if and only if
  `D = -c Δ + D 1`.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2, Lemma 2.1 and the paragraph following it (the Bochner
  connection of an operator of Laplace type, and its metric compatibility for formally
  self-adjoint operators).
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **Green's second identity as formal self-adjointness.** The Laplace–Beltrami operator
`Δ = div ∘ grad` on the smooth functions of a manifold without boundary is formally self-adjoint
for the Riemannian volume: `∫ (Δf) g dV = ∫ f (Δg) dV` whenever `f` or `g` has compact support. -/
theorem isFormalTranspose_smoothLaplaceBeltrami :
    (smoothLaplaceBeltrami I M).IsFormalTranspose (smoothLaplaceBeltrami I M)
      (riemannianVolume I M) := by
  rw [LinearMap.isFormalTranspose_iff]
  rintro f g (hf | hg)
  · simpa using (Manifold.integral_mul_laplaceBeltrami_right_eq_left
      (f.contMDiff.of_le (by simp)) hf (g.contMDiff.of_le (by simp))).symm
  · have h := Manifold.integral_mul_laplaceBeltrami_right_eq_left
      (g.contMDiff.of_le (by simp)) hg (f.contMDiff.of_le (by simp))
    simp only [smoothLaplaceBeltrami_apply]
    simpa only [mul_comm] using h

variable {D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 2} {c : ℝ}

/-- **Formally self-adjoint operators of Laplace type are Schrödinger operators.** On a Riemannian
manifold without boundary, an operator `D` of Laplace type with constant `c` is formally
self-adjoint for the Riemannian volume if and only if `D = -c Δ + V` for the potential `V = D 1`,
where `Δ = div ∘ grad`. -/
theorem IsLaplaceType.isFormalTranspose_self_iff (hD : IsLaplaceType D c) :
    (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D (riemannianVolume I M) ↔
      (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) =
        -c • smoothLaplaceBeltrami I M +
          LinearMap.mulLeft ℝ ((D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) 1) := by
  have hΔ := smoothLaplaceBeltrami_mem_differentialOperators_two (I := I) (M := M)
  have hsΔ (a : ℝ) := tsupport_differentialOperators_apply_subset (Submodule.smul_mem _ a hΔ)
  have hsD := tsupport_differentialOperators_apply_subset D.property
  constructor
  · intro h
    -- The first-order part `P = D + c Δ` has vanishing principal symbol and is formally
    -- self-adjoint, hence it has order zero.
    set P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 2 :=
      D + c • ⟨smoothLaplaceBeltrami I M, hΔ⟩ with hP
    have hP1 := (forall_smoothPrincipalSymbol_eq_zero_iff P).1 fun x ξ ↦ by
      rw [hP, smoothPrincipalSymbol_add, smoothPrincipalSymbol_smul, hD.smoothPrincipalSymbol_eq,
        smoothPrincipalSymbol_smoothLaplaceBeltrami]
      ring
    have hP0 := (h.add (isFormalTranspose_smoothLaplaceBeltrami.smul c) hsD (hsΔ c) hsD
      (hsΔ c)).mem_differentialOperators_two_mul_of_self (k := 0) hP1
    -- An operator of order zero is multiplication by its value at `1`, and `Δ 1 = 0`.
    refine LinearMap.ext fun f ↦ ContMDiffMap.ext fun x ↦ ?_
    have hPf := congr($(mem_differentialOperators_zero_iff.1 hP0 f 1) x)
    have hΔ1 : Manifold.laplaceBeltrami I (⇑(1 : C^∞⟮I, M; ℝ⟯)) x = 0 :=
      Manifold.laplaceBeltrami_const I 1 x
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply,
      ContMDiffMap.coe_add, ContMDiffMap.coe_smul, ContMDiffMap.coe_mul, Pi.add_apply,
      Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_one, smoothLaplaceBeltrami_apply, hΔ1]
      at hPf ⊢
    linarith
  · intro h
    rw [h]
    have hV := LinearMap.mulLeft_mem_differentialOperators_zero (R := ℝ)
      ((D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) 1)
    exact (isFormalTranspose_smoothLaplaceBeltrami.smul (-c)).add
      (LinearMap.isFormalTranspose_mulLeft _) (hsΔ (-c))
      (tsupport_differentialOperators_apply_subset hV) (hsΔ (-c))
      (tsupport_differentialOperators_apply_subset hV)

end TauCeti
