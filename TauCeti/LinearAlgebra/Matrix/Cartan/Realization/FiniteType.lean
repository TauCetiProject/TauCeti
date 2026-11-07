/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic
public import Mathlib.LinearAlgebra.Matrix.Cartan.Realisation
-- Access the canonical construction only to supply its missing projection lemmas.
import all Mathlib.LinearAlgebra.Matrix.Cartan.Realisation

/-!
# Nonsingular realizations and the finite-type comparison

For a nonsingular matrix, a realization is minimal exactly when its simple coroots span the
ambient space. Such realizations are uniquely isomorphic by an equivalence preserving roots
and coroots. This uniqueness is specific to the nonsingular case.

Mathlib's `CartanMatrix.Realisation` gives a realization in this sense by using its perfect
pairing to regard roots as functionals. Its matrix convention is the transpose of ours:
Mathlib indexes rows by roots, whereas `TauCeti.CartanRealization` indexes rows by coroots.
The canonical Mathlib realization is minimal, so every minimal finite-type realization agrees
with it by the unique root- and coroot-preserving equivalence.

The mathematical source is V. G. Kac, *Infinite-dimensional Lie algebras*, third edition,
§1.1, Proposition 1.1, specialized to nonsingular matrices. The finite-type comparison uses
Mathlib's `CartanMatrix.Realisation` and `Matrix.IsFiniteCartan.toRealisation`.
-/

public section

open Module

namespace TauCeti.CartanRealization

variable {I K H H' : Type*} [Fintype I] [DecidableEq I] [Field K]
  [AddCommGroup H] [Module K H] [AddCommGroup H'] [Module K H']
  {A : Matrix I I K} (R : CartanRealization A H)

/-- A finite-dimensional realization of a nonsingular matrix is minimal exactly when the
simple coroots span its ambient space. -/
theorem isMinimal_iff_corootSpan_eq_top [FiniteDimensional K H] (hA : IsUnit A) :
    R.IsMinimal ↔ R.corootSpan = ⊤ := by
  classical
  have hrank := Matrix.rank_of_isUnit A hA
  rw [R.isMinimal_iff, hrank]
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [R.finrank_corootSpan]
    omega
  · intro h
    have hd := R.finrank_corootSpan
    rw [h, finrank_top] at hd
    omega

/-- Minimal realizations of a nonsingular matrix have a unique root- and coroot-preserving
isomorphism. Singular matrices need not have uniqueness. -/
theorem existsUnique_equiv_of_isMinimal
    (S : CartanRealization A H') (hA : IsUnit A) (hR : R.IsMinimal) (hS : S.IsMinimal) :
    ∃! e : H ≃ₗ[K] H', (∀ i, e (R.coroot i) = S.coroot i) ∧
      ∀ i h, S.root i (e h) = R.root i h := by
  let := hR.finiteDimensional
  let := hS.finiteDimensional
  exact R.existsUnique_equiv_of_corootSpan_eq_top S
    ((R.isMinimal_iff_corootSpan_eq_top hA).mp hR)
    ((S.isMinimal_iff_corootSpan_eq_top hA).mp hS)

end TauCeti.CartanRealization

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
theorem isMinimal_toCartanRealization_iff [FiniteDimensional K N] :
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

/-- Every minimal realization of a finite Cartan matrix agrees with Mathlib's canonical
realization. Transpose the input matrix to match the coroot-row convention. -/
theorem existsUnique_equiv_toRealisation {H : Type*} [AddCommGroup H] [Module K H]
    (R : TauCeti.CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hR : R.IsMinimal) :
    ∃! e : H ≃ₗ[K] (I → K),
      (∀ i, e (R.coroot i) = Pi.single i 1) ∧
      ∀ i h, (hA.transpose.toRealisation (hA.transpose.isUnit_map K).invertible).pairing
        (Pi.single i 1) (e h) = R.root i h := by
  let S := (hA.transpose.toRealisation
    (hA.transpose.isUnit_map K).invertible).toCartanRealization
  have hS : S.IsMinimal := hA.transpose.isMinimal_toRealisation_toCartanRealization _
  simpa only [S, CartanMatrix.Realisation.toCartanRealization_coroot,
    CartanMatrix.Realisation.toCartanRealization_root_apply, toRealisation_sCoroot,
    toRealisation_sRoot] using
    R.existsUnique_equiv_of_isMinimal S (hA.isUnit_map K) hR hS

end Matrix.IsFiniteCartan
