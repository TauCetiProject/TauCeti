/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Symplectic.WittExtension

/-!
# Symplectic forms from continuous alternating two-forms

`SymplecticForm.ofContinuousAlternatingMap` reads a nondegenerate continuous alternating
map in two variables as an algebraic symplectic form. Nondegeneracy need only be checked
in the left variable, since alternation supplies the corresponding right-variable condition.
The evaluation lemma identifies the resulting bilinear form with the original two-form.
Over finite-dimensional spaces, Witt's extension theorem then gives a continuous linear
automorphism of `E × N` fixing `E × {0}` and carrying one nondegenerate two-form to another with
the same restriction to `E × {0}`.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A continuous alternating two-form with trivial left kernel gives an algebraic symplectic
form. No finite-dimensionality assumption is needed. -/
def ofContinuousAlternatingMap (ω : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hnd : ∀ v, (∀ w, ω ![v, w] = 0) → v = 0) : SymplecticForm V where
  toBilinForm := ω.toAlternatingMap.toMultilinearMap.toBilinMap
  isAlt := ω.toAlternatingMap.isAlt_toBilinMap
  nondegenerate := ω.toAlternatingMap.isAlt_toBilinMap.isRefl.nondegenerate_iff_separatingLeft.mpr
    (fun v hv ↦ hnd v fun w ↦ (MultilinearMap.toBilinMap_apply _ v w).symm.trans (hv w))

/-- The symplectic form constructed from a continuous two-form has the same evaluations. -/
@[simp]
theorem ofContinuousAlternatingMap_apply (ω : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hnd : ∀ v, (∀ w, ω ![v, w] = 0) → v = 0) (v w : V) :
    ofContinuousAlternatingMap ω hnd v w = ω ![v, w] :=
  MultilinearMap.toBilinMap_apply _ v w

end TauCeti.SymplecticForm

namespace TauCeti

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

/-- **Witt's extension theorem for the zero section.** If two alternating forms `a₀`, `a₁` on
`E × N` are nondegenerate and have the same restriction to `E × {0}`, then some continuous linear
automorphism `A` of `E × N` fixes `E × {0}` pointwise and carries `a₀` to `a₁`. -/
theorem exists_continuousLinearEquiv_fix_inl_of_compContinuousLinearMap_inl_eq
    {a₀ a₁ : (E × N) [⋀^Fin 2]→L[ℝ] ℝ} (hnd₀ : ∀ v, (∀ w, a₀ ![v, w] = 0) → v = 0)
    (hnd₁ : ∀ v, (∀ w, a₁ ![v, w] = 0) → v = 0)
    (htan : a₁.compContinuousLinearMap (.inl ℝ E N) = a₀.compContinuousLinearMap (.inl ℝ E N)) :
    ∃ A : (E × N) ≃L[ℝ] (E × N),
      (∀ v w : E × N, a₁ ![A v, A w] = a₀ ![v, w]) ∧ ∀ q : E, A (q, 0) = (q, 0) := by
  -- Witt's extension theorem: the identity of the zero section extends to a linear
  -- symplectomorphism `A` from `a₀` to `a₁`.
  let S : Submodule ℝ (E × N) := LinearMap.range (LinearMap.inl ℝ E N)
  obtain ⟨e, he, heS⟩ := SymplecticForm.exists_isSymplectomorphism_extend
    (SymplecticForm.ofContinuousAlternatingMap _ hnd₀)
    (SymplecticForm.ofContinuousAlternatingMap _ hnd₁) rfl S.subtype S.injective_subtype
    fun x y ↦ by
      obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      have h := congrArg (fun c ↦ c ![a, b]) htan
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
      simp only [SymplecticForm.ofContinuousAlternatingMap_apply, Submodule.coe_subtype, ← ha,
        ← hb]
      convert h using 2 <;> ext i <;> fin_cases i <;> rfl
  refine ⟨e.toContinuousLinearEquiv, fun v w ↦ ?_, fun q ↦ heS ⟨(q, 0), q, rfl⟩⟩
  exact ((SymplecticForm.ofContinuousAlternatingMap_apply _ hnd₁ (e v) (e w)).symm.trans
    (he.apply v w)).trans (SymplecticForm.ofContinuousAlternatingMap_apply _ hnd₀ v w)

end TauCeti
