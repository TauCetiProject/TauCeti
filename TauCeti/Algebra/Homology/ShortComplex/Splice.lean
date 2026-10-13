/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Splicing short exact sequences

A bi-infinite sequence `Zⁿ → Pⁿ → Zⁿ⁺¹` of short complexes gives a cochain complex on the
middle terms. Its differential is the projection of one short complex followed by the
inclusion of the next. When the short complexes are short exact, the resulting complex is
acyclic and its cycles are the first terms of the short complexes. This construction turns
successive presentations and copresentations into complete resolutions.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.2.

## Implementation notes

The constructor is an exposed abbreviation, like Mathlib's `CochainComplex.of`: its terms
must reduce to the prescribed middle objects for the statements of `splice_d`,
`spliceCyclesIso_hom_iCycles`, and `spliceCyclesIso_inv_f` to typecheck. The equality
`splice_X` does not provide this definitional equality; an unexposed constructor would require
transporting the morphisms along that equality in these statements.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (S : ℤ → ShortComplex C) (e : ∀ n, (S n).X₃ ≅ (S (n + 1)).X₁)

/-- Splice successive short complexes along the specified identifications of their end terms.
The objects are their middle terms and the differential is `g ≫ e.hom ≫ f`. -/
noncomputable abbrev splice : CochainComplex C ℤ :=
  CochainComplex.of (fun n ↦ (S n).X₂)
    (fun n ↦ (S n).g ≫ (e n).hom ≫ (S (n + 1)).f)
    (fun n ↦ by simp [Category.assoc, (S (n + 1)).zero_assoc])

/-- The term in degree `n` of the spliced complex is the middle term of the `n`-th short complex. -/
@[simp]
theorem splice_X (n : ℤ) : (splice S e).X n = (S n).X₂ := (rfl)

/-- The differential of the spliced complex is the projection followed by the connecting
isomorphism and the next inclusion. -/
theorem splice_d (n : ℤ) :
    (splice S e).d n (n + 1) = (S n).g ≫ (e n).hom ≫ (S (n + 1)).f := by
  simp [splice]

end CochainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ℤ → ShortComplex C) (e : ∀ n, (S n).X₃ ≅ (S (n + 1)).X₁)
  (hS : ∀ n, (S n).ShortExact)

include hS in
/-- Splicing short exact sequences produces an acyclic cochain complex. -/
theorem acyclic_splice : (splice S e).Acyclic := by
  intro n
  have := (hS (n - 1)).epi_g
  have := (hS (n + 1)).mono_f
  let T := ShortComplex.mk (S n).f ((S n).g ≫ (e n).hom ≫ (S (n + 1)).f)
    (by simp [(S n).zero_assoc])
  have hT : T.Exact := by
    let φ : S n ⟶ T :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := (e n).hom ≫ (S (n + 1)).f
        comm₁₂ := by simp [T]
        comm₂₃ := by simp [T] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp (hS n).exact
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  let U := ShortComplex.mk ((splice S e).d (n - 1) n) ((splice S e).d n (n + 1))
    ((splice S e).d_comp_d _ _ _)
  let φ : U ⟶ T :=
    { τ₁ := (S (n - 1)).g ≫ (e (n - 1)).hom ≫ eqToHom (by simp [T])
      τ₂ := 𝟙 ((S n).X₂), τ₃ := 𝟙 ((S (n + 1)).X₂)
      comm₁₂ := by simp [U, T, splice, CochainComplex.of.d, Category.assoc]
      comm₂₃ := by simp [U, T, splice, CochainComplex.of.d] }
  have : Epi φ.τ₁ := by dsimp [φ, T, U]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hT

/-- The cycles of the spliced complex identify with the first term of each short exact sequence.
The isomorphism is oriented from the prescribed cycle object into the categorical cycles. -/
noncomputable def spliceCyclesIso (n : ℤ) : (S n).X₁ ≅ (splice S e).cycles n := by
  have := (hS (n + 1)).mono_f
  let hk := isKernelCompMono (hS n).fIsKernel ((e n).hom ≫ (S (n + 1)).f)
    (splice_d S e n)
  exact IsLimit.conePointUniqueUpToIso hk ((splice S e).cyclesIsKernel n (n + 1) (by simp))

/-- The cycles comparison identifies the given inclusion with the categorical cycle inclusion. -/
@[reassoc (attr := simp)]
theorem spliceCyclesIso_hom_iCycles (n : ℤ) :
    (spliceCyclesIso S e hS n).hom ≫ (splice S e).iCycles n = (S n).f := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The inverse cycles comparison recovers the categorical cycle inclusion. -/
@[reassoc (attr := simp)]
theorem spliceCyclesIso_inv_f (n : ℤ) :
    (spliceCyclesIso S e hS n).inv ≫ (S n).f = (splice S e).iCycles n := by
  exact (Iso.inv_comp_eq (spliceCyclesIso S e hS n)).mpr
    (spliceCyclesIso_hom_iCycles S e hS n).symm

end CochainComplex
