/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Basic
public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Analyticity of rational functions on the general linear group

A rational function on `GLₙ(𝕜)` over a complete nontrivially normed field, expressed as a
polynomial in matrix entries divided by a power of the determinant, is analytic in the native
open-submanifold structure.

## Main results

* `TauCeti.Matrix.GeneralLinearGroup.contMDiff_of_mem_rationalFunctions`: analyticity of every
  rational function on `GL n 𝕜`.

## References

* `Mathlib.Analysis.Analytic.Polynomial`, for polynomial analyticity over complete normed fields.

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III, §8, Proposition (8.6), pp.154–155: algebraic matrix coefficients are holomorphic.
-/

public section

open Matrix Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator
attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace TauCeti.Matrix.GeneralLinearGroup

/-- Rational functions on the general linear group over a complete normed field are analytic. -/
theorem contMDiff_of_mem_rationalFunctions {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ} {f : GL (Fin n) 𝕜 → 𝕜}
    (hf : f ∈ rationalFunctions 𝕜 n) :
    let _ : CompleteSpace (Matrix (Fin n) (Fin n) 𝕜) := FiniteDimensional.complete 𝕜 _
    ContMDiff 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜) 𝓘(𝕜) ω f := by
  let _ : CompleteSpace (Matrix (Fin n) (Fin n) 𝕜) := FiniteDimensional.complete 𝕜 _
  dsimp only
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions_iff_inv.mp hf
  have hev (Q : MvPolynomial (Fin n × Fin n) 𝕜) :
      ContMDiff 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜) 𝓘(𝕜) ω
        (fun g : GL (Fin n) 𝕜 ↦ MvPolynomial.eval
          (fun ij ↦ (g : Matrix (Fin n) (Fin n) 𝕜) ij.1 ij.2) Q) := by
    let c : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] ((Fin n × Fin n) → 𝕜) :=
      LinearMap.pi fun ij ↦ Matrix.entryLinearMap 𝕜 𝕜 ij.1 ij.2
    have hc : ContDiff 𝕜 ω (fun M ↦ MvPolynomial.eval (c M) Q) :=
      (AnalyticOnNhd.eval_linearMap c Q).contDiff
    exact hc.contMDiff.comp Units.contMDiff_val
  have hd : ContMDiff 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜) 𝓘(𝕜) ω
      (fun g : GL (Fin n) 𝕜 ↦ (g : Matrix (Fin n) (Fin n) 𝕜).det) := by
    simpa only [eval_entries_det_mvPolynomialX] using hev
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) 𝕜))
  have hnonzero (g : GL (Fin n) 𝕜) : (g : Matrix (Fin n) (Fin n) 𝕜).det ^ m ≠ 0 :=
    pow_ne_zero m (Matrix.GeneralLinearGroup.det_ne_zero g)
  exact (((hd.pow m).inv₀ hnonzero).mul (hev P)).congr fun g ↦ by
    simpa only [Pi.mul_apply] using hP g

end TauCeti.Matrix.GeneralLinearGroup
