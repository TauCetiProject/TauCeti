/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Cochain and chain complexes matched in complementary degrees

Let `C` be a cochain complex and `D` a chain complex, both indexed by `ℕ`, and let `n : ℕ`.
Suppose given maps `φ i k : C.X i ⟶ D.X k` that carry the differential of `C` from degree `i` to
degree `i + 1` to the differential of `D` from degree `k + 1` to degree `k`, and that are
isomorphisms on the antidiagonal `i + k = n`. If moreover `C.X (n + 1)` and `D.X (n + 1)` are zero,
then the cohomology of `C` in degree `i` is isomorphic to the homology of `D` in degree `k` whenever
`i + k = n` (`CochainComplex.homologyIsoOfAntidiagonal`), and the isomorphism sends the class of a
cocycle `x` to the class of the cycle `φ i k x`
(`CochainComplex.homologyπ_comp_homologyIsoOfAntidiagonal_hom`). Only the (co)homology in degrees
at most `n` is identified: the hypotheses say nothing about `φ` off the antidiagonal nor about the
objects in degrees above `n + 1`.

This is the homological algebra behind the Morse-theoretic proof of Poincaré duality, where `C` is
the Morse cochain complex of a function `f` and `D` the Morse chain complex of `-f`.

## Main declarations

* `CochainComplex.iCycles_comp_comp_d_of_comm`: such maps send cocycles of `C` to cycles of `D`.
* `CochainComplex.homologyIsoOfAntidiagonal`: the cohomology of `C` in degree `i` is the homology
  of `D` in degree `k`, for `i + k = n`.
* `CochainComplex.homologyπ_comp_homologyIsoOfAntidiagonal_hom`: the isomorphism on classes.
-/

public section

open CategoryTheory Limits

namespace CochainComplex

variable {V : Type*} [Category V] [HasZeroMorphisms V] (C : CochainComplex V ℕ)
  (D : ChainComplex V ℕ) (φ : ∀ i k, C.X i ⟶ D.X k)

section Cycles

variable [CategoryWithHomology V]

/-- Maps from a cochain complex `C` to a chain complex `D` that carry the differential of `C` from
degree `i` to degree `i + 1` to the differential of `D` from degree `k + 1` to degree `k` send the
cocycles of `C` to cycles of `D`. -/
theorem iCycles_comp_comp_d_of_comm
    (comm : ∀ i k, C.d i (i + 1) ≫ φ (i + 1) k = φ i (k + 1) ≫ D.d (k + 1) k) (i k : ℕ) :
    (C.iCycles i ≫ φ i k) ≫ D.d k (k - 1) = 0 := by
  rcases k with _ | k
  · rw [D.shape _ _ (by simp), comp_zero]
  · rw [Category.assoc, Nat.add_sub_cancel, ← comm, C.iCycles_d_assoc, zero_comp]

end Cycles

variable {n : ℕ}

/-- The morphism of short complexes, from the differentials of `C` into and out of degree `i` to
the differentials of `D` into and out of degree `k`, given by `φ`. At the ends `i = 0` and `k = 0`
it uses that `D.X (n + 1)` and `C.X (n + 1)` are zero. -/
private noncomputable def scMapOfAntidiagonal
    (comm : ∀ i k, C.d i (i + 1) ≫ φ (i + 1) k = φ i (k + 1) ≫ D.d (k + 1) k)
    (hC : IsZero (C.X (n + 1))) (hD : IsZero (D.X (n + 1))) {i k : ℕ} (hik : i + k = n) :
    C.sc' (i - 1) i (i + 1) ⟶ D.sc' (k + 1) k (k - 1) where
  τ₁ := φ (i - 1) (k + 1)
  τ₂ := φ i k
  τ₃ := φ (i + 1) (k - 1)
  comm₁₂ := by
    rcases i with _ | i
    · -- At `i = 0` no differential of `C` enters degree `0`, and `D.X (n + 1)` is zero.
      obtain rfl : k = n := by omega
      have hd : (C.sc' (0 - 1) 0 (0 + 1)).f = 0 := C.shape _ _ (by simp)
      rw [hd, zero_comp, hD.eq_of_tgt (φ (0 - 1) (k + 1)) 0, zero_comp]
    · exact (comm i k).symm
  comm₂₃ := by
    rcases k with _ | k
    · -- At `k = 0` no differential of `D` leaves degree `0`, and `C.X (n + 1)` is zero.
      obtain rfl : i = n := by omega
      have hd : (D.sc' (0 + 1) 0 (0 - 1)).g = 0 := D.shape _ _ (by simp)
      rw [hd, comp_zero, hC.eq_of_src (φ (i + 1) (0 - 1)) 0, comp_zero]
    · exact (comm i k).symm

variable [CategoryWithHomology V]

/-- **Cochain and chain complexes matched in complementary degrees have the same (co)homology.**
Let `φ i k : C.X i ⟶ D.X k` carry the differential of the cochain complex `C` from degree `i` to
degree `i + 1` to the differential of the chain complex `D` from degree `k + 1` to degree `k`, and
be an isomorphism when `i + k = n`. If `C.X (n + 1)` and `D.X (n + 1)` are zero, then for
`i + k = n` the cohomology of `C` in degree `i` is isomorphic to the homology of `D` in degree
`k`. -/
noncomputable def homologyIsoOfAntidiagonal
    (comm : ∀ i k, C.d i (i + 1) ≫ φ (i + 1) k = φ i (k + 1) ≫ D.d (k + 1) k)
    (iso : ∀ i k, i + k = n → IsIso (φ i k)) (hC : IsZero (C.X (n + 1)))
    (hD : IsZero (D.X (n + 1))) {i k : ℕ} (hik : i + k = n) :
    C.homology i ≅ D.homology k :=
  haveI : Epi (scMapOfAntidiagonal C D φ comm hC hD hik).τ₁ := by
    rcases i with _ | i
    · obtain rfl : k = n := by omega
      exact hD.epi _
    · -- `τ₁` is `φ (i + 1 - 1) (k + 1)`, and `i + 1 - 1` reduces to `i` by definition.
      have := iso i (k + 1) (by omega)
      exact inferInstanceAs (Epi (φ i (k + 1)))
  haveI : IsIso (scMapOfAntidiagonal C D φ comm hC hD hik).τ₂ := iso i k hik
  haveI : Mono (scMapOfAntidiagonal C D φ comm hC hD hik).τ₃ := by
    rcases k with _ | k
    · obtain rfl : i = n := by omega
      exact hC.mono _
    · -- `τ₃` is `φ (i + 1) (k + 1 - 1)`, and `k + 1 - 1` reduces to `k` by definition.
      have := iso (i + 1) k (by omega)
      exact inferInstanceAs (Mono (φ (i + 1) k))
  C.homologyIsoSc' (i - 1) i (i + 1) (by rcases i with _ | i <;> simp) (by simp) ≪≫
    asIso (ShortComplex.homologyMap (scMapOfAntidiagonal C D φ comm hC hD hik)) ≪≫
    (D.homologyIsoSc' (k + 1) k (k - 1) (by simp) (by rcases k with _ | k <;> simp)).symm

/-- **The identification of the cohomology of `C` with the homology of `D` on classes.** For
`i + k = n`, `CochainComplex.homologyIsoOfAntidiagonal` sends the class of a cocycle `x` of `C` of
degree `i` to the class of the cycle `φ i k x` of `D` of degree `k`. -/
@[reassoc (attr := simp)]
theorem homologyπ_comp_homologyIsoOfAntidiagonal_hom
    (comm : ∀ i k, C.d i (i + 1) ≫ φ (i + 1) k = φ i (k + 1) ≫ D.d (k + 1) k)
    (iso : ∀ i k, i + k = n → IsIso (φ i k)) (hC : IsZero (C.X (n + 1)))
    (hD : IsZero (D.X (n + 1))) {i k : ℕ} (hik : i + k = n) :
    C.homologyπ i ≫ (C.homologyIsoOfAntidiagonal D φ comm iso hC hD hik).hom =
      D.liftCycles (C.iCycles i ≫ φ i k) (k - 1) (by rcases k with _ | k <;> simp)
          (C.iCycles_comp_comp_d_of_comm D φ comm i k) ≫ D.homologyπ k := by
  -- Each step of the composite is induced on cycles, where it acts as `φ i k`.
  simp only [homologyIsoOfAntidiagonal, Iso.trans_hom, asIso_hom, Iso.symm_hom]
  rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (D.iCycles k)]
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    ShortComplex.cyclesMap_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc,
    HomologicalComplex.liftCycles_i]
  -- The middle component of `scMapOfAntidiagonal` is `φ i k`.
  simp [scMapOfAntidiagonal]

end CochainComplex
