/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalProperties.Submodule
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut

/-!
# Determinant invariance under matrix-algebra endomorphisms

`AlgHom.det_apply_matrix` states that a matrix-algebra endomorphism over a commutative ring
preserves the determinant. The local innerness theorem
`AlgHom.exists_span_eq_top_forall_map_eq_innerAut` reduces this to `Matrix.det_units_conj`
after localization at each maximal ideal. This argument detects equality even over nonreduced
rings, as needed when comparing matrix splittings of an Azumaya algebra in the construction
of the reduced norm (Grothendieck, *Le groupe de Brauer I*, §5.13).
-/

public section

/-- An algebra endomorphism of a square matrix algebra over a commutative ring preserves the
determinant. In particular, the determinant is independent of the choice of matrix splitting
isomorphism over a fixed coefficient ring. -/
@[simp]
theorem AlgHom.det_apply_matrix {A n : Type*} [CommRing A] [Fintype n] [DecidableEq n]
    (σ : AlgHom A (Matrix n n A) (Matrix n n A)) (M : Matrix n n A) : (σ M).det = M.det := by
  obtain ⟨s, hs, hinner⟩ := σ.exists_span_eq_top_forall_map_eq_innerAut
  refine Module.eq_of_localization_maximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap A (Localization.AtPrime P)) _ _ fun P _ ↦ ?_
  obtain ⟨c, hc, hcP⟩ : ∃ c ∈ s, c ∉ P := by
    by_contra! h
    have hle : Ideal.span (s : Set A) ≤ P := Ideal.span_le.mpr h
    exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) (top_le_iff.mp (hs ▸ hle))
  let φ := algebraMap A (Localization.AtPrime P)
  have hu : IsUnit (φ c) := IsLocalization.map_units _ (⟨c, hcP⟩ : P.primeCompl)
  obtain ⟨g, hg⟩ := hinner c hc φ hu
  calc
    φ (σ M).det = ((σ M).map φ).det := φ.map_det _
    _ = (M.map φ).det := by
      rw [hg M, Matrix.GeneralLinearGroup.innerAut_apply]
      exact Matrix.det_units_conj g _
    _ = φ M.det := (φ.map_det _).symm
