/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.Periodic.Compression.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Preadditive

/-!
# Compression detects acyclicity

A strictly bounded cochain complex `K` is acyclic exactly when its `n`-periodic compression
`Δₙ K` is acyclic (`TauCeti.PeriodicComplex.compression_acyclic_iff`); the direction from `Δₙ K`
to `K` holds for every complex with a compression
(`TauCeti.PeriodicComplex.acyclic_of_compression_acyclic`). The homology of `Δₙ K` in
residue `r` is the direct sum of the homology objects of `K` in the degrees congruent to `r`; we
do not construct this decomposition, but only the finite sum decomposition of the identity of the
short complex of `Δₙ K` at `r` through the short complexes of `K` that it rests on. The summand
inclusions and projections are morphisms of short complexes because the differential of `Δₙ K` is
induced summand by summand by the differential of `K`, and the identity is the finite sum of their
composites because `K` has only finitely many nonzero terms. Conversely, each short complex of `K`
is a retract of a short complex of `Δₙ K`.

This is the input needed to descend compression from bounded homotopy categories to bounded and
periodic derived categories: compression preserves and reflects quasi-isomorphisms of bounded
complexes.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] (n : ℕ) (K : CochainComplex C ℤ)
  [HasCompression n K]

/-- The short complex of the compression at residue `r`, with explicit neighbouring residues. -/
private noncomputable abbrev compressionSc (r : ZMod n) : ShortComplex C :=
  (compression n K).sc' (r - 1) r (r + 1)

/-- The short complex of `K` at degree `i`, with explicit neighbouring degrees. -/
private noncomputable abbrev complexSc (i : ℤ) : ShortComplex C :=
  K.sc' (i - 1) i (i + 1)

/-- The projection of the short complex of the compression at `r` onto the short complex of `K`
at `i`. -/
private noncomputable def compressionScπ (r : ZMod n) (i : ℤ) :
    compressionSc n K r ⟶ complexSc K i where
  τ₁ := πCompression n K (r - 1) (i - 1)
  τ₂ := πCompression n K r i
  τ₃ := πCompression n K (r + 1) (i + 1)
  comm₁₂ := (d_πCompression n K _ _ (sub_add_cancel r 1) _ _ (sub_add_cancel i 1)).symm
  comm₂₃ := (d_πCompression n K _ _ rfl _ _ rfl).symm

/-- The inclusion of the short complex of `K` at `i` into the short complex of the compression at
`r`. -/
private noncomputable def compressionScι (r : ZMod n) (i : ℤ) :
    complexSc K i ⟶ compressionSc n K r where
  τ₁ := ιCompressionOrZero n K (i - 1) (r - 1)
  τ₂ := ιCompressionOrZero n K i r
  τ₃ := ιCompressionOrZero n K (i + 1) (r + 1)
  comm₁₂ := ιCompressionOrZero_d n K _ _ (sub_add_cancel r 1) _ _ (sub_add_cancel i 1)
  comm₂₃ := ιCompressionOrZero_d n K _ _ rfl _ _ rfl

/-- The identity of the short complex of the compression at `r` is the sum over the degrees in
`[a - 1, b + 1]` of the projections onto the short complexes of `K` followed by the inclusions. -/
private lemma sum_compressionScπ_compressionScι (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (r : ZMod n) :
    ∑ i ∈ Finset.Icc (a - 1) (b + 1), compressionScπ n K r i ≫ compressionScι n K r i = 𝟙 _ := by
  have hK (s : ZMod n) (T : Finset ℤ) (hT : ∀ i : ℤ, a ≤ i → i ≤ b → i ∈ T) :
      ∑ j ∈ T, πCompression n K s j ≫ ιCompressionOrZero n K j s = 𝟙 _ :=
    sum_πCompression_ιCompressionOrZero n K s T fun i _ hi ↦
      K.isZero_X_of_notMem_Icc a b fun h ↦ hi (hT i (Finset.mem_Icc.mp h).1
        (Finset.mem_Icc.mp h).2)
  -- In each position, reindex the sum to the degrees of that position and compare with `hK`.
  ext
  · refine ((ShortComplex.π₁ : ShortComplex C ⥤ C).map_sum _ _).trans
      ((Finset.sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ fun _ _ ↦ rfl).trans
        (hK _ (Finset.Icc (a - 2) b) ?_)) <;>
    · intros
      simp only [Finset.mem_Icc] at *
      omega
  · refine ((ShortComplex.π₂ : ShortComplex C ⥤ C).map_sum _ _).trans (hK _ _ fun i _ _ ↦ ?_)
    simp only [Finset.mem_Icc]
    omega
  · refine ((ShortComplex.π₃ : ShortComplex C ⥤ C).map_sum _ _).trans
      ((Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ fun _ _ ↦ rfl).trans
        (hK _ (Finset.Icc a (b + 2)) ?_)) <;>
    · intros
      simp only [Finset.mem_Icc] at *
      omega

/-- The short complex of `K` at `i` is a retract of the short complex of the compression at the
residue of `i`. -/
private lemma compressionScι_compressionScπ (i : ℤ) :
    compressionScι n K i i ≫ compressionScπ n K i i = 𝟙 _ := by
  ext
  · exact ιCompressionOrZero_πCompression n K _ _ (by rw [Int.cast_sub, Int.cast_one])
  · exact ιCompressionOrZero_πCompression n K _ _ rfl
  · exact ιCompressionOrZero_πCompression n K _ _ (by rw [Int.cast_add, Int.cast_one])

variable [CategoryWithHomology C]

/-- A cochain complex is acyclic when its `n`-periodic compression is acyclic. -/
theorem acyclic_of_compression_acyclic (h : (compression n K).Acyclic) : K.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology_sc' _ (i - 1) i (i + 1) (by simp) (by simp),
    IsZero.iff_id_eq_zero]
  have hZ : IsZero ((ShortComplex.homologyFunctor C).obj (compressionSc n K i)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology_sc' _ _ _ _ (by simp) (by simp)).mp (h _)
  have := congrArg (ShortComplex.homologyFunctor C).map (compressionScι_compressionScπ n K i)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    hZ.eq_of_tgt ((ShortComplex.homologyFunctor C).map (compressionScι n K i i)) 0,
    zero_comp] at this
  exact this.symm

/-- A strictly bounded cochain complex is acyclic exactly when its `n`-periodic compression is
acyclic. -/
theorem compression_acyclic_iff (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    (compression n K).Acyclic ↔ K.Acyclic := by
  refine ⟨acyclic_of_compression_acyclic n K, fun h r ↦ ?_⟩
  rw [HomologicalComplex.exactAt_iff_isZero_homology_sc' _ (r - 1) r (r + 1) (by simp) (by simp),
    IsZero.iff_id_eq_zero]
  have := (ShortComplex.homologyFunctor C).map_sum
    (fun i ↦ compressionScπ n K r i ≫ compressionScι n K r i) (Finset.Icc (a - 1) (b + 1))
  rw [sum_compressionScπ_compressionScι n K a b r, CategoryTheory.Functor.map_id] at this
  refine this.trans (Finset.sum_eq_zero fun i _ ↦ ?_)
  have hZ : IsZero ((ShortComplex.homologyFunctor C).obj (complexSc K i)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology_sc' _ _ _ _ (by simp) (by simp)).mp (h _)
  rw [CategoryTheory.Functor.map_comp,
    hZ.eq_of_tgt ((ShortComplex.homologyFunctor C).map (compressionScπ n K r i)) 0, zero_comp]

end TauCeti.PeriodicComplex
