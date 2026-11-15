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

In a preadditive category with homology, a strictly bounded cochain complex `K` is acyclic exactly
when its `n`-periodic compression `Δₙ K` is acyclic
(`TauCeti.PeriodicComplex.compression_acyclic_iff`). Exactness of the compression at the residue
of `i` implies exactness of `K` at `i`, assuming only zero morphisms, a compression, and homology
of `K` at `i` (`TauCeti.PeriodicComplex.exactAt_of_compression_exactAt`). Reflection of acyclicity
follows degreewise (`TauCeti.PeriodicComplex.acyclic_of_compression_acyclic`).
Both directions rest on the short complexes of `K` and of `Δₙ K`. The summand inclusions and
projections are morphisms of short complexes
(`TauCeti.PeriodicComplex.compressionScι`, `TauCeti.PeriodicComplex.compressionScπ`) because the
differential of `Δₙ K` is induced summand by summand by the differential of `K`. Each short
complex of `K` is a retract of the short complex of `Δₙ K` at its residue, the retractions of
different degrees are orthogonal, and for a strictly bounded `K` the identity of the short complex
of `Δₙ K` is the finite sum of their composites. The resulting decomposition of the homology of
`Δₙ K` as a direct sum of homology objects of `K` is in
`TauCeti.Algebra.Homology.Periodic.Compression.Homology`.

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

variable {C : Type u} [Category.{v} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] (n : ℕ) (K : CochainComplex C ℤ) [HasCompression n K]

/-- The projection of the short complex of the compression at `r`, with explicit neighbouring
residues, onto the short complex of `K` at `i`, with explicit neighbouring degrees. It is zero
when `i` does not lie in the residue class `r`. -/
noncomputable def compressionScπ (r : ZMod n) (i : ℤ) :
    (compression n K).sc' (r - 1) r (r + 1) ⟶ K.sc' (i - 1) i (i + 1) where
  τ₁ := πCompression n K (r - 1) (i - 1)
  τ₂ := πCompression n K r i
  τ₃ := πCompression n K (r + 1) (i + 1)
  comm₁₂ := (d_πCompression n K _ _ (sub_add_cancel r 1) _ _ (sub_add_cancel i 1)).symm
  comm₂₃ := (d_πCompression n K _ _ rfl _ _ rfl).symm

/-- The inclusion of the short complex of `K` at `i`, with explicit neighbouring degrees, into the
short complex of the compression at `r`, with explicit neighbouring residues. It is zero when `i`
does not lie in the residue class `r`. -/
noncomputable def compressionScι (r : ZMod n) (i : ℤ) :
    K.sc' (i - 1) i (i + 1) ⟶ (compression n K).sc' (r - 1) r (r + 1) where
  τ₁ := ιCompressionOrZero n K (i - 1) (r - 1)
  τ₂ := ιCompressionOrZero n K i r
  τ₃ := ιCompressionOrZero n K (i + 1) (r + 1)
  comm₁₂ := ιCompressionOrZero_d n K _ _ (sub_add_cancel r 1) _ _ (sub_add_cancel i 1)
  comm₂₃ := ιCompressionOrZero_d n K _ _ rfl _ _ rfl

/-- The projection of the short complex of the compression onto that of `K` vanishes in degrees
outside the residue class. -/
@[simp]
lemma compressionScπ_eq_zero (r : ZMod n) (i : ℤ) (hi : (i : ZMod n) ≠ r) :
    compressionScπ n K r i = 0 := by
  ext
  · exact πCompression_eq_zero n K _ _ fun h ↦ hi (by simpa using h)
  · exact πCompression_eq_zero n K _ _ hi
  · exact πCompression_eq_zero n K _ _ fun h ↦ hi (by simpa using h)

/-- The inclusion of the short complex of `K` into that of the compression vanishes in degrees
outside the residue class. -/
@[simp]
lemma compressionScι_eq_zero (r : ZMod n) (i : ℤ) (hi : (i : ZMod n) ≠ r) :
    compressionScι n K r i = 0 := by
  ext
  · exact ιCompressionOrZero_eq_zero n K _ _ fun h ↦ hi (by simpa using h)
  · exact ιCompressionOrZero_eq_zero n K _ _ hi
  · exact ιCompressionOrZero_eq_zero n K _ _ fun h ↦ hi (by simpa using h)

/-- The short complex of `K` at `i` is a retract of the short complex of the compression at the
residue of `i`. -/
@[reassoc]
lemma compressionScι_compressionScπ (r : ZMod n) (i : ℤ) (hi : (i : ZMod n) = r) :
    compressionScι n K r i ≫ compressionScπ n K r i = 𝟙 _ := by
  subst hi
  ext
  · exact ιCompressionOrZero_πCompression n K _ _ (by rw [Int.cast_sub, Int.cast_one])
  · exact ιCompressionOrZero_πCompression n K _ _ rfl
  · exact ιCompressionOrZero_πCompression n K _ _ (by rw [Int.cast_add, Int.cast_one])

/-- The retractions of the short complexes of `K` in two different degrees onto the short complex
of the compression are orthogonal. -/
@[reassoc]
lemma compressionScι_compressionScπ_of_ne (r : ZMod n) {i j : ℤ} (hij : i ≠ j) :
    compressionScι n K r i ≫ compressionScπ n K r j = 0 := by
  ext
  · exact ιCompressionOrZero_πCompression_of_ne n K _ (by omega)
  · exact ιCompressionOrZero_πCompression_of_ne n K _ hij
  · exact ιCompressionOrZero_πCompression_of_ne n K _ (by omega)

/-- A cochain complex with homology at `i` is exact there when its `n`-periodic compression
is exact at the residue of `i`. This holds in any category with zero morphisms. -/
theorem exactAt_of_compression_exactAt (i : ℤ) [K.HasHomology i]
    (h : (compression n K).ExactAt (i : ZMod n)) : K.ExactAt i := by
  have : (K.sc' (i - 1) i (i + 1)).HasHomology :=
    ShortComplex.hasHomology_of_iso (K.isoSc' (i - 1) i (i + 1) (by simp) (by simp))
  have hE : ((compression n K).sc' (i - 1 : ZMod n) i (i + 1)).Exact :=
    (HomologicalComplex.exactAt_iff' _ _ _ _ (by simp) (by simp)).mp h
  have := hE.hasHomology
  rw [HomologicalComplex.exactAt_iff_isZero_homology_sc' _ (i - 1) i (i + 1) (by simp) (by simp),
    IsZero.iff_id_eq_zero]
  have hZ := (ShortComplex.exact_iff_isZero_homology _).mp hE
  have := congrArg (fun f ↦ ShortComplex.homologyMap f) (compressionScι_compressionScπ n K i i rfl)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_id,
    hZ.eq_of_tgt (ShortComplex.homologyMap (compressionScι n K i i)) 0, zero_comp] at this
  exact this.symm

/-- A cochain complex with homology in every degree is acyclic when its `n`-periodic
compression is acyclic. This holds in any category with zero morphisms. -/
theorem acyclic_of_compression_acyclic [∀ i, K.HasHomology i]
    (h : (compression n K).Acyclic) : K.Acyclic :=
  fun i ↦ exactAt_of_compression_exactAt n K i (h _)

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] (n : ℕ) (K : CochainComplex C ℤ) [HasCompression n K]

/-- The identity of the short complex of the compression at `r` is the sum over the degrees in
`[a - 1, b + 1]` of the projections onto the short complexes of `K` followed by the inclusions. -/
lemma sum_compressionScπ_compressionScι (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
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

variable [CategoryWithHomology C]

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
  have hZ : IsZero ((ShortComplex.homologyFunctor C).obj (K.sc' (i - 1) i (i + 1))) :=
    (HomologicalComplex.exactAt_iff_isZero_homology_sc' _ _ _ _ (by simp) (by simp)).mp (h _)
  rw [CategoryTheory.Functor.map_comp,
    hZ.eq_of_tgt ((ShortComplex.homologyFunctor C).map (compressionScπ n K r i)) 0, zero_comp]

end Preadditive

end TauCeti.PeriodicComplex
