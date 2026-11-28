/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut

/-!
# Determinant invariance under matrix-algebra endomorphisms

`TauCeti.det_apply_matrix` states that a matrix-algebra endomorphism over a commutative ring
preserves the determinant. The simp rule applies to both algebra homomorphisms and algebra
equivalences through `AlgHomClass`. The local innerness theorem
`AlgHom.exists_span_eq_top_forall_map_eq_innerAut` reduces this to `Matrix.det_units_conj`
on a principal-open cover, where `Localization.algebraMap_injective_of_span_eq_top` detects
equality.
This argument works over nonreduced rings, as needed when comparing matrix splittings of an
Azumaya algebra in the construction of the reduced norm (Grothendieck, *Le groupe de Brauer I*,
§5.13).
-/

public section

/-- An algebra endomorphism of a square matrix algebra over a commutative ring preserves the
determinant. In particular, two splittings into the same matrix algebra, after reindexing
if needed, give the same determinant. -/
@[simp]
theorem TauCeti.det_apply_matrix {A n F : Type*} [CommRing A] [Fintype n] [DecidableEq n]
    [FunLike F (Matrix n n A) (Matrix n n A)] [AlgHomClass F A (Matrix n n A) (Matrix n n A)]
    (σ : F) (M : Matrix n n A) : (σ M).det = M.det := by
  obtain ⟨s, hs, hinner⟩ := (AlgHom.ofClass σ).exists_span_eq_top_forall_map_eq_innerAut
  apply Localization.algebraMap_injective_of_span_eq_top (s : Set A) hs
  funext c
  simp only [Pi.algebraMap_apply]
  let φ := algebraMap A (Localization.Away c.val)
  have hu : IsUnit (φ c.val) := IsLocalization.Away.algebraMap_isUnit c.val
  obtain ⟨g, hg⟩ := hinner c.val c.property φ hu
  calc
    φ (σ M).det = ((σ M).map φ).det := φ.map_det _
    _ = (M.map φ).det := by
      have hM := hg M
      rw [AlgHom.coe_ofClass] at hM
      rw [hM, Matrix.GeneralLinearGroup.innerAut_apply]
      exact Matrix.det_units_conj g _
    _ = φ M.det := (φ.map_det _).symm
