/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.Algebra.Homology.Periodic.Compression.Basic

/-!
# Compression detects acyclicity

A strictly bounded cochain complex `K` is acyclic exactly when its `n`-periodic compression
`Δₙ K` is acyclic (`TauCeti.PeriodicComplex.compression_acyclic_iff`). The homology of `Δₙ K` in
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

/-- The projection of the term of residue `r` of the compression onto the term of degree `j`
of `K`; it is zero when `j` does not lie in the residue class `r`. -/
private noncomputable def πCompression (r : ZMod n) (j : ℤ) :
    (compression n K).X r ⟶ K.X j :=
  compressionDesc n K fun i _ ↦ if h : i = j then eqToHom (congrArg K.X h) else 0

/-- The inclusion of the term of degree `j` of `K` into the term of residue `r` of the
compression; it is zero when `j` does not lie in the residue class `r`. -/
-- This is `GradedObject.ιMapObjOrZero` for the coproducts defining the compression, restated
-- through `ιCompression` because the terms of `compression` are not exposed as those coproducts.
private noncomputable def ιCompressionOrZero (j : ℤ) (r : ZMod n) :
    K.X j ⟶ (compression n K).X r :=
  if h : (j : ZMod n) = r then ιCompression n K j r h else 0

private lemma ιCompressionOrZero_eq (j : ℤ) (r : ZMod n) (h : (j : ZMod n) = r) :
    ιCompressionOrZero n K j r = ιCompression n K j r h := by
  simp [ιCompressionOrZero, h]

private lemma ιCompressionOrZero_eq_zero (j : ℤ) (r : ZMod n) (h : (j : ZMod n) ≠ r) :
    ιCompressionOrZero n K j r = 0 := by
  simp [ιCompressionOrZero, h]

@[reassoc]
private lemma ιCompression_πCompression (i : ℤ) (r : ZMod n) (hi : (i : ZMod n) = r) (j : ℤ) :
    ιCompression n K i r hi ≫ πCompression n K r j =
      if h : i = j then eqToHom (congrArg K.X h) else 0 :=
  ιCompression_compressionDesc n K _ i hi

private lemma ιCompressionOrZero_πCompression (j : ℤ) (r : ZMod n) (hj : (j : ZMod n) = r) :
    ιCompressionOrZero n K j r ≫ πCompression n K r j = 𝟙 _ := by
  rw [ιCompressionOrZero_eq n K j r hj]
  exact (ιCompression_πCompression n K j r hj j).trans (by simp)

/-- The projections onto the summands of degrees `i` and `j = i + 1` intertwine the differentials
of the compression and of `K`. -/
@[reassoc]
private lemma d_πCompression (r s : ZMod n) (hrs : r + 1 = s) (i j : ℤ) (hij : i + 1 = j) :
    (compression n K).d r s ≫ πCompression n K s j =
      πCompression n K r i ≫ K.d i j := by
  ext k hk
  have hk' : ((k + 1 : ℤ) : ZMod n) = s := by push_cast; rw [hk, hrs]
  rw [ιCompression_d_assoc n K k (k + 1) rfl r s hk hk',
    ιCompression_πCompression, ιCompression_πCompression_assoc]
  by_cases hki : k = i
  · subst hki hij
    simp
  · have hkj : k + 1 ≠ j := by omega
    simp [hki, hkj]

/-- The inclusions of the summands of degrees `i` and `j = i + 1` intertwine the differentials
of `K` and of the compression. -/
@[reassoc]
private lemma ιCompressionOrZero_d (r s : ZMod n) (hrs : r + 1 = s) (i j : ℤ) (hij : i + 1 = j) :
    ιCompressionOrZero n K i r ≫ (compression n K).d r s =
      K.d i j ≫ ιCompressionOrZero n K j s := by
  by_cases hi : (i : ZMod n) = r
  · have hj : (j : ZMod n) = s := by rw [← hij, ← hrs, ← hi]; push_cast; rfl
    rw [ιCompressionOrZero_eq n K i r hi, ιCompressionOrZero_eq n K j s hj]
    exact ιCompression_d n K i j hij r s hi hj
  · have hj : (j : ZMod n) ≠ s := fun hj ↦ hi (by
      rw [← hij, ← hrs] at hj
      push_cast at hj
      exact add_right_cancel hj)
    rw [ιCompressionOrZero_eq_zero n K i r hi, ιCompressionOrZero_eq_zero n K j s hj, zero_comp,
      comp_zero]

/-- If every nonzero term of `K` in the residue class `r` has degree in `T`, the identity of the
term of residue `r` of the compression is the sum over `T` of the composites of the projections
and inclusions. -/
private lemma sum_πCompression_ιCompressionOrZero (r : ZMod n) (T : Finset ℤ)
    (hT : ∀ i : ℤ, (i : ZMod n) = r → i ∉ T → IsZero (K.X i)) :
    ∑ j ∈ T, πCompression n K r j ≫ ιCompressionOrZero n K j r = 𝟙 _ := by
  ext i hi
  rw [Preadditive.comp_sum, Category.comp_id]
  by_cases hiT : i ∈ T
  · rw [Finset.sum_eq_single i (fun j _ hji ↦ by
        simp [ιCompression_πCompression_assoc, Ne.symm hji])
      (fun h ↦ absurd hiT h), ιCompression_πCompression_assoc, ιCompressionOrZero_eq n K i r hi]
    simp
  · exact (hT i hi hiT).eq_of_src _ _

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
  -- Each component of a sum of morphisms of short complexes is the sum of the components.
  have h₁ : (ShortComplex.π₁ : ShortComplex C ⥤ C).Additive := ⟨rfl⟩
  have h₂ : (ShortComplex.π₂ : ShortComplex C ⥤ C).Additive := ⟨rfl⟩
  have h₃ : (ShortComplex.π₃ : ShortComplex C ⥤ C).Additive := ⟨rfl⟩
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
  · exact ιCompressionOrZero_πCompression n K _ _ (by push_cast; rfl)
  · exact ιCompressionOrZero_πCompression n K _ _ rfl
  · exact ιCompressionOrZero_πCompression n K _ _ (by push_cast; rfl)

variable [CategoryWithHomology C]

/-- A strictly bounded cochain complex is acyclic exactly when its `n`-periodic compression is
acyclic. -/
theorem compression_acyclic_iff (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    (compression n K).Acyclic ↔ K.Acyclic := by
  have hΔ (r : ZMod n) : (compression n K).ExactAt r ↔ (compressionSc n K r).Exact :=
    HomologicalComplex.exactAt_iff' _ _ _ _ (by simp) (by simp)
  have hK (i : ℤ) : K.ExactAt i ↔ (complexSc K i).Exact :=
    HomologicalComplex.exactAt_iff' _ _ _ _ (by simp) (by simp)
  refine ⟨fun h i ↦ ?_, fun h r ↦ ?_⟩
  · rw [hK, ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    have hZ : IsZero ((ShortComplex.homologyFunctor C).obj (compressionSc n K i)) :=
      (ShortComplex.exact_iff_isZero_homology _).mp ((hΔ _).mp (h _))
    have := congrArg (ShortComplex.homologyFunctor C).map (compressionScι_compressionScπ n K i)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      hZ.eq_of_tgt ((ShortComplex.homologyFunctor C).map (compressionScι n K i i)) 0,
      zero_comp] at this
    exact this.symm
  · rw [hΔ, ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    have := (ShortComplex.homologyFunctor C).map_sum
      (fun i ↦ compressionScπ n K r i ≫ compressionScι n K r i) (Finset.Icc (a - 1) (b + 1))
    rw [sum_compressionScπ_compressionScι n K a b r, CategoryTheory.Functor.map_id] at this
    refine this.trans (Finset.sum_eq_zero fun i _ ↦ ?_)
    have hZ : IsZero ((ShortComplex.homologyFunctor C).obj (complexSc K i)) :=
      (ShortComplex.exact_iff_isZero_homology _).mp ((hK _).mp (h _))
    rw [CategoryTheory.Functor.map_comp,
      hZ.eq_of_tgt ((ShortComplex.homologyFunctor C).map (compressionScπ n K r i)) 0, zero_comp]

end TauCeti.PeriodicComplex
