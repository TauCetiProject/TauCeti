/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import Mathlib.RingTheory.Unramified.Basic
import TauCeti.LinearAlgebra.LinearMap.Avoidance
import TauCeti.RingTheory.Derivation.FormallyEtale

/-!
# Simultaneous separating lifts in a prescribed congruence class

Let `R` be an infinite ring embedded in a field `K` (hence a domain), and let `A` be an
`R`-algebra. Suppose finitely many formally unramified `A`-algebras `Fᵢ` (for example
localizations of `A`) are finitely generated transcendental field extensions of `K` with
one-dimensional Kähler differentials. For any `a : A` and nonzero
`π : R`, there is a perturbation `a + π • b` that is a separating transcendental in every
`Fᵢ`. Thus a lift of a function on the special fibre of a model over a discrete valuation
ring can be made separating on all generic components without changing its reduction.
No perfectness assumption on `K` is needed, and `A` need not be a domain.

The proof uses the differential criterion for a separating element. A nonzero derivation
of a formally unramified `A`-algebra cannot vanish on `A`. One can then avoid the finitely many
kernels on the coset `a + πA`, because `R` is infinite and the differential modules are
torsion-free over `R`.

This supplies the generic-fibre part of choosing coordinates for finite normalization;
it does not assert that the chosen coordinate is quasi-finite on the special fibre.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 4.1.2 (normalization).
* The Stacks Project, Lemma 55.8.2, https://stacks.math.columbia.edu/tag/0C2T.
-/

public section

noncomputable section

open KaehlerDifferential
open scoped IntermediateField

namespace TauCeti

variable {R K A ι : Type*} [CommRing R] [Infinite R]
  [Field K] [Algebra R K] [FaithfulSMul R K] [CommRing A] [Algebra R A]
  [Finite ι] (F : ι → Type*) [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)] [∀ i, Algebra R (F i)] [∀ i, IsScalarTower R K (F i)]
  [∀ i, Algebra A (F i)] [∀ i, IsScalarTower R A (F i)]
  [∀ i, Algebra.EssFiniteType K (F i)] [∀ i, Algebra.Transcendental K (F i)]

/-- Let `R` be an infinite ring embedded in a field `K`, and let finitely many formally
unramified `A`-algebras `F i` (for example localizations of `A`) be finitely generated
transcendental field extensions of `K` with one-dimensional Kähler differentials `Ω[F i⁄K]`.
Then in a prescribed congruence class `a + π • A` modulo a nonzero `π : R` there is an element
whose image in every `F i` is transcendental and separating over `K`. This applies to the
generic component fields of an affine chart `Spec A` of a model of a smooth curve over a
discrete valuation ring. -/
theorem exists_forall_transcendental_and_isSeparable_adjoin_add_smul
    [∀ i, Algebra.FormallyUnramified A (F i)]
    (hdim : ∀ i, Module.finrank (F i) Ω[F i⁄K] = 1) (a : A) {π : R} (hπ : π ≠ 0) :
    ∃ b : A, ∀ i, Transcendental K (algebraMap A (F i) (a + π • b)) ∧
      Algebra.IsSeparable K⟮algebraMap A (F i) (a + π • b)⟯ (F i) := by
  have := IsDomain.of_faithfulSMul R K
  have (i : ι) : Module.IsTorsionFree R Ω[F i⁄K] := by
    have : Module.IsTorsionFree R (F i) :=
      Module.IsTorsionFree.trans K
    exact Module.IsTorsionFree.trans (F i)
  let f (i : ι) : A →ₗ[R] Ω[F i⁄K] :=
    ((D K (F i)).toLinearMap.restrictScalars R).comp
      (IsScalarTower.toAlgHom R A (F i)).toLinearMap
  -- `f i` is `D K (F i)` precomposed with the structure map `A → F i`.
  have hf (i : ι) (x : A) : f i x = D K (F i) (algebraMap A (F i) x) := rfl
  have hnonzero (i : ι) : ∃ x : A, f i x ≠ 0 := by
    by_contra! h
    have hzero : D K (F i) = 0 :=
      Derivation.eq_of_formallyUnramified (S := A) fun x ↦ (hf i x).symm.trans (h x)
    obtain ⟨y, hy, hsep⟩ := finrank_kaehlerDifferential_eq_one_iff.mp (hdim i)
    exact D_ne_zero_of_separating hy (DFunLike.congr_fun hzero y)
  let U := LinearMap.range (LinearMap.lsmul R A π)
  have hU (i : ι) : ∃ x ∈ U, f i x ≠ 0 := by
    obtain ⟨x, hx⟩ := hnonzero i
    exact ⟨π • x, ⟨x, LinearMap.lsmul_apply π x⟩,
      by simpa only [map_smul] using smul_ne_zero hπ hx⟩
  obtain ⟨x, ⟨b, rfl⟩, hx⟩ := LinearMap.exists_mem_forall_apply_add_ne_zero f U hU a
  refine ⟨b, fun i ↦ transcendental_and_isSeparable_adjoin_of_D_ne_zero (hdim i) ?_⟩
  rw [← LinearMap.lsmul_apply, ← hf]
  exact hx i

end TauCeti
