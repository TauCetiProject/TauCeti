/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic
public import Mathlib.LinearAlgebra.Matrix.Cartan.Realisation
-- Access the canonical construction for its projection lemmas and matrix conversion.
import all Mathlib.LinearAlgebra.Matrix.Cartan.Realisation

/-!
# Finite-type comparison of Cartan realizations

Mathlib's `CartanMatrix.Realisation` gives a realization in this sense by using its perfect
pairing to regard roots as functionals. Its matrix convention is the transpose of ours:
Mathlib indexes rows by roots, whereas `TauCeti.CartanRealization` indexes rows by coroots.
Every minimal realization of a finite Cartan matrix `A` in our coroot-row convention agrees
uniquely with the conversion of Mathlib's canonical realization of `A.transpose`.

The mathematical source is V. G. Kac, *Infinite-dimensional Lie algebras*, third edition,
§1.1, Proposition 1.1, specialized to nonsingular matrices. The finite-type comparison uses
Mathlib's `CartanMatrix.Realisation` and `Matrix.IsFiniteCartan.toRealisation`.
-/

public section

open Module

namespace CartanMatrix.Realisation

variable {I K M N : Type*} [Fintype I] [DecidableEq I] [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (rl : Realisation I K M N)

/-- Regard Mathlib's roots as functionals using its perfect pairing. The transpose accounts
for the convention that a `CartanRealization` has coroots as rows and roots as columns. -/
def toCartanRealization :
    TauCeti.CartanRealization (rl.matrix.transpose.map (Int.cast : ℤ → K)) N where
  coroot := rl.sCoroot
  root := rl.pairing ∘ rl.sRoot
  coroot_linearIndependent := rl.lin_ind_sCoroot
  root_linearIndependent := rl.lin_ind_sRoot.map' rl.pairing
    (LinearMap.ker_eq_bot.mpr rl.pairing.toPerfPair.injective)
  root_coroot i j := rl.pairingMatrix j i

@[simp]
theorem toCartanRealization_coroot (i : I) :
    rl.toCartanRealization.coroot i = rl.sCoroot i := (rfl)

@[simp]
theorem toCartanRealization_root_apply (i : I) (h : N) :
    rl.toCartanRealization.root i h = rl.pairing (rl.sRoot i) h := (rfl)

/-- Conversion retains the actual coroot span, rather than identifying it with the whole
ambient space. -/
@[simp]
theorem toCartanRealization_corootSpan :
    rl.toCartanRealization.corootSpan = Submodule.span K (Set.range rl.sCoroot) := by
  rw [TauCeti.CartanRealization.corootSpan_def]
  rfl

/-- A Mathlib finite Cartan realization gives a minimal realization precisely when its
coroots span; the perfect pairing alone does not impose this spanning condition. -/
theorem isMinimal_toCartanRealization_iff :
    rl.toCartanRealization.IsMinimal ↔ Submodule.span K (Set.range rl.sCoroot) = ⊤ := by
  rw [← rl.toCartanRealization_corootSpan]
  exact rl.toCartanRealization.isMinimal_iff_corootSpan_eq_top
    (rl.isCartan.transpose.isUnit_map K)

end CartanMatrix.Realisation

namespace Matrix.IsFiniteCartan

variable {I K : Type*} [Fintype I] [DecidableEq I]
  {A : Matrix I I ℤ}

section Projections

variable [CommRing K] (hA : A.IsFiniteCartan)

/-- The canonical Mathlib realization has the prescribed Cartan matrix. -/
@[simp]
theorem toRealisation_matrix (hAI : Invertible (A.map (Int.cast : ℤ → K))) :
    (hA.toRealisation hAI).matrix = A := (rfl)

/-- The canonical Mathlib realization uses the standard coordinate simple roots. -/
@[simp]
theorem toRealisation_sRoot (hAI : Invertible (A.map (Int.cast : ℤ → K))) (i : I) :
    (hA.toRealisation hAI).sRoot i = Pi.single i 1 := (rfl)

/-- The canonical Mathlib realization uses the standard coordinate simple coroots. -/
@[simp]
theorem toRealisation_sCoroot (hAI : Invertible (A.map (Int.cast : ℤ → K))) (i : I) :
    (hA.toRealisation hAI).sCoroot i = Pi.single i 1 := (rfl)

/-- The canonical pairing evaluates roots against the matrix applied to coroot coordinates. -/
@[simp]
theorem toRealisation_pairing_apply (hAI : Invertible (A.map (Int.cast : ℤ → K)))
    (x y : I → K) :
    (hA.toRealisation hAI).pairing x y = (A.map (Int.cast : ℤ → K) *ᵥ y) ⬝ᵥ x := (rfl)

end Projections

variable [Field K] [CharZero K] (hA : A.IsFiniteCartan)

/-- Mathlib's canonical finite Cartan realization has no additional central directions. -/
theorem isMinimal_toRealisation_toCartanRealization
    (hAI : Invertible (A.map (Int.cast : ℤ → K))) :
    (hA.toRealisation hAI).toCartanRealization.IsMinimal := by
  rw [CartanMatrix.Realisation.isMinimal_toCartanRealization_iff]
  have hb : (hA.toRealisation hAI).sCoroot = Pi.basisFun K I := by
    ext i j
    simp [Pi.basisFun_apply]
  rw [hb, Basis.span_eq]

/-- Mathlib's canonical realization of the transposed matrix, converted to the coroot-row
convention. Its Cartan matrix is `A`, not `A.transpose`. -/
noncomputable def toCartanRealization :
    TauCeti.CartanRealization (A.map (Int.cast : ℤ → K)) (I → K) :=
  -- toRealisation_matrix identifies the canonical matrix with A.transpose, and the second
  -- transpose introduced by the conversion cancels it definitionally.
  (hA.transpose.toRealisation
    (hA.transpose.isUnit_map K).invertible).toCartanRealization

/-- The canonical coroot-row realization has the standard coordinate coroots. -/
@[simp]
theorem toCartanRealization_coroot (i : I) :
    (hA.toCartanRealization (K := K)).coroot i = Pi.single i 1 := by
  simp only [toCartanRealization, CartanMatrix.Realisation.toCartanRealization_coroot,
    toRealisation_sCoroot]

/-- Roots of the canonical coroot-row realization evaluate via the transposed matrix. -/
@[simp]
theorem toCartanRealization_root_apply (i : I) (h : I → K) :
    (hA.toCartanRealization (K := K)).root i h =
      (A.transpose.map (Int.cast : ℤ → K) *ᵥ h) i := by
  simp only [toCartanRealization, CartanMatrix.Realisation.toCartanRealization_root_apply,
    toRealisation_sRoot, toRealisation_pairing_apply, dotProduct_single_one]

/-- The canonical coroot-row realization is minimal. -/
theorem isMinimal_toCartanRealization :
    (hA.toCartanRealization (K := K)).IsMinimal :=
  hA.transpose.isMinimal_toRealisation_toCartanRealization _

/-- Every minimal realization of a finite Cartan matrix agrees uniquely with the conversion
of Mathlib's canonical realization of the transpose to the coroot-row convention. -/
theorem existsUnique_linearEquiv_toCartanRealization
    {H : Type*} [AddCommGroup H] [Module K H]
    (R : TauCeti.CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hR : R.IsMinimal) :
    ∃! e : H ≃ₗ[K] (I → K), R.map e = hA.toCartanRealization :=
  R.existsUnique_linearEquiv_of_isMinimal _ (hA.isUnit_map K) hR hA.isMinimal_toCartanRealization

end Matrix.IsFiniteCartan
