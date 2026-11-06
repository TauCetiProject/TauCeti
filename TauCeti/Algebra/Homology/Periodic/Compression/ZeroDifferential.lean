/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Compression.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential

/-!
# Bounded lifts of periodic complexes with zero differential

For positive `n`, a `ZMod n`-graded family has a bounded integer-graded lift: put its term of
residue `r` in degree `r.val` and put zero in all other degrees. Equip this lift with zero
differential. Its compression is canonically isomorphic to the original family with zero
differential. Thus every periodic complex with zero differential is gradable, already at the
level of complexes, not just up to homotopy or quasi-isomorphism.

These are the gradable layers in projective flags. They provide the starting objects for
generation of periodic derived categories by compressions of bounded complexes. No abelianity or
global-dimension assumption is needed for this starting step; positivity of the period ensures
the lift has finite support.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Sections 3.3–4, especially Theorem 4.3.
-/

public section

open CategoryTheory Limits HomologicalComplex ZeroObject

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {n : ℕ} [NeZero n]

/-- The bounded lift of a cyclic graded family with zero differential. The term of residue `r`
is placed in integer degree `r.val`, and every other degree is zero. -/
noncomputable def boundedGradedLift (E : ZMod n → C) : CochainComplex.Bounded C := by
  classical
  let K := graded (ComplexShape.up ℤ) fun i ↦
    if i = ((i : ZMod n).val : ℤ) then E (i : ZMod n) else 0
  refine ⟨K, (CochainComplex.bounded_iff C K).mpr ⟨0, n, ?_, ?_⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have h : i ≠ ((i : ZMod n).val : ℤ) := by omega
    simpa only [K, graded_X, ite_eq_right h] using isZero_zero C
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have hv := (i : ZMod n).val_lt
    have h : i ≠ ((i : ZMod n).val : ℤ) := by omega
    simpa only [K, graded_X, ite_eq_right h] using isZero_zero C

/-- All differentials of the bounded graded lift vanish. -/
@[simp]
lemma boundedGradedLift_d (E : ZMod n → C) (i j : ℤ) :
    (boundedGradedLift E).obj.d i j = 0 := (rfl)

/-- The lift is zero away from the chosen representative of a residue class. -/
lemma isZero_boundedGradedLift_X (E : ZMod n → C) (i : ℤ)
    (hi : i ≠ ((i : ZMod n).val : ℤ)) : IsZero ((boundedGradedLift E).obj.X i) := by
  classical
  simpa only [boundedGradedLift, graded_X, ite_eq_right hi] using isZero_zero C

/-- In the representative degree `r.val`, the bounded lift recovers `E r`. -/
noncomputable def boundedGradedLiftXIso (E : ZMod n → C) (r : ZMod n) :
    (boundedGradedLift E).obj.X r.val ≅ E r :=
  eqToIso (by simp [boundedGradedLift])

variable [HasFiniteCoproducts C]

/-- The componentwise identification of the compressed bounded lift with its original family.
All summands except the one in degree `r.val` vanish. -/
private noncomputable def compressionBoundedGradedLiftXIso (E : ZMod n → C) (r : ZMod n) :
    (compression n (boundedGradedLift E).obj).X r ≅ E r := by
  classical
  let K := (boundedGradedLift E).obj
  let e := boundedGradedLiftXIso E r
  have hr : ((r.val : ℤ) : ZMod n) = r := by simp
  let f : (compression n K).X r ⟶ E r := compressionDesc n K fun i hi ↦
    if h : i = (r.val : ℤ) then (K.XIsoOfEq h).hom ≫ e.hom else 0
  refine ⟨f, e.inv ≫ ιCompression n K r.val r hr, ?_, ?_⟩
  · apply compression_hom_ext
    intro i hi
    by_cases h : i = (r.val : ℤ)
    · subst i
      dsimp only [f, K]
      simp only [ιCompression_compressionDesc_assoc, dite_eq_left rfl, XIsoOfEq_rfl,
        Iso.refl_hom, Category.id_comp, Iso.hom_inv_id_assoc, Category.comp_id]
    · have hz : IsZero (K.X i) := isZero_boundedGradedLift_X E i (by simpa [hi] using h)
      exact hz.eq_of_src _ _
  · simp [f]

/-- Compressing the bounded lift of a cyclic graded family recovers that family with zero
differential. -/
noncomputable def compressionBoundedGradedLiftIso (E : ZMod n → C) :
    compression n (boundedGradedLift E).obj ≅ graded (ComplexShape.up (ZMod n)) E :=
  HomologicalComplex.Hom.isoOfComponents (compressionBoundedGradedLiftXIso E) (by
    intro r s hrs
    apply compression_hom_ext
    intro i hi
    have hj : ((i + 1 : ℤ) : ZMod n) = s := by
      simpa [hi] using hrs
    rw [ιCompression_d_assoc n _ i (i + 1) rfl r s hi hj]
    simp)

/-- On the representative summand, the compression comparison is the original term
identification. -/
@[reassoc (attr := simp)]
lemma ιCompression_compressionBoundedGradedLiftIso_hom_f (E : ZMod n → C) (r : ZMod n) :
    ιCompression n (boundedGradedLift E).obj r.val r (by simp) ≫
        (compressionBoundedGradedLiftIso E).hom.f r = (boundedGradedLiftXIso E r).hom := by
  simp [compressionBoundedGradedLiftIso, compressionBoundedGradedLiftXIso]

/-- The inverse comparison includes the original term in its representative summand. -/
@[simp]
lemma compressionBoundedGradedLiftIso_inv_f (E : ZMod n → C) (r : ZMod n) :
    (compressionBoundedGradedLiftIso E).inv.f r =
      (boundedGradedLiftXIso E r).inv ≫
        ιCompression n (boundedGradedLift E).obj r.val r (by simp) := (rfl)

end TauCeti.PeriodicComplex

namespace CochainComplex

open TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {n : ℕ} [NeZero n] [HasFiniteCoproducts C]

/-- Every positive-period complex with zero differential is isomorphic to the compression of a
bounded complex with zero differential. -/
noncomputable def compressionIsoOfDEqZero (K : CochainComplex C (ZMod n))
    (hd : ∀ i j, K.d i j = 0) : compression n (boundedGradedLift K.X).obj ≅ K :=
  compressionBoundedGradedLiftIso K.X ≪≫
    HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by simp [hd])

/-- On the representative summand, the zero-differential comparison is the original term
identification. -/
@[reassoc (attr := simp)]
lemma ιCompression_compressionIsoOfDEqZero_hom_f (K : CochainComplex C (ZMod n))
    (hd : ∀ i j, K.d i j = 0) (r : ZMod n) :
    ιCompression n (boundedGradedLift K.X).obj r.val r (by simp) ≫
        (K.compressionIsoOfDEqZero hd).hom.f r = (boundedGradedLiftXIso K.X r).hom := by
  simp [compressionIsoOfDEqZero]

/-- The inverse zero-differential comparison includes each term in its representative summand. -/
@[simp]
lemma compressionIsoOfDEqZero_inv_f (K : CochainComplex C (ZMod n))
    (hd : ∀ i j, K.d i j = 0) (r : ZMod n) :
    (K.compressionIsoOfDEqZero hd).inv.f r =
      (boundedGradedLiftXIso K.X r).inv ≫
        ιCompression n (boundedGradedLift K.X).obj r.val r (by simp) := by
  simp [compressionIsoOfDEqZero]

end CochainComplex
