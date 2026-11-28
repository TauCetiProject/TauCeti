/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomials as holomorphic functions

`TauCeti.ComplexAnalyticSpace.polynomialToHolomorphic` evaluates polynomials in the coordinate
sections of the holomorphic structure sheaf using `MvPolynomial.aeval`.
`MvPolynomial.polynomialToHolomorphic_apply` computes the resulting function at a point.
-/

public noncomputable section

open CategoryTheory Opposite TauCeti TopologicalSpace
open scoped Manifold
open scoped ContDiff

variable {n : ℕ}

local notation "𝒫" => MvPolynomial (Fin n) ℂ
local notation "𝒰" => (⊤ : Opens (Fin n → ℂ))

namespace TauCeti.ComplexAnalyticSpace

/-- Polynomial evaluation as global holomorphic functions on complex affine space. -/
def polynomialToHolomorphic (n : ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ]
      (holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (⊤ : Opens (Fin n → ℂ))).presheaf.obj (op ⊤) :=
  MvPolynomial.aeval fun i ↦
    holomorphicStructureSheaf.ofContMDiff (fun x ↦ x.val.val i)
      (((ContinuousLinearMap.proj (R := ℂ) i : (Fin n → ℂ) →L[ℂ] ℂ).contDiff.contMDiff).comp
        (contMDiff_subtypeVal.comp contMDiff_subtypeVal))

end TauCeti.ComplexAnalyticSpace

open TauCeti.ComplexAnalyticSpace

namespace MvPolynomial

/-- The holomorphic section attached to a polynomial evaluates to its value at each point. -/
-- Index on evaluation across the unexposed section carrier and its dependent opens.
@[simp]
theorem polynomialToHolomorphic_apply (p : 𝒫) (x : 𝒰) :
    holomorphicStructureSheaf.toFun (no_index 𝓘(ℂ, Fin n → ℂ)) (no_index 𝒰) (no_index (op ⊤))
      (no_index (polynomialToHolomorphic n p)) (no_index ⟨x, trivial⟩) =
        MvPolynomial.eval x.val p := by
  rw [← holomorphicStructureSheaf.evalAlgHom_apply, polynomialToHolomorphic,
    MvPolynomial.comp_aeval_apply, ← MvPolynomial.aeval_eq_eval]
  apply congrArg (fun coords : Fin n → ℂ ↦ MvPolynomial.aeval coords p)
  exact funext fun _ ↦ (holomorphicStructureSheaf.evalAlgHom_apply _ _).trans
    (holomorphicStructureSheaf.ofContMDiff_apply _ _ _)

end MvPolynomial
