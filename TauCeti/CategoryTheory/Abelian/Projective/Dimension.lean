/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Comparing projective dimensions, and subobjects of projectives

The projective dimension of an object `Y` is at most that of an object `X`, possibly in a
different abelian category, exactly when every bound `HasProjectiveDimensionLT X n` implies the
same bound on `Y` (`CategoryTheory.projectiveDimension_le_projectiveDimension_iff`). This compares
projective dimensions degree by degree without unfolding their definition as an infimum.

In an abelian category with enough projectives, every object has projective dimension at most one
if and only if every subobject of a projective object is projective. This is the hereditary
condition, expressed using Mathlib's existing projective-dimension predicate.

A morphism `f` of projective objects shifts dimension by two between its kernel and its cokernel
(`CategoryTheory.hasProjectiveDimensionLT_cokernel_iff_kernel`).

If a morphism `g : X ⟶ Y` has projective kernel and projective target, and its cokernel has
projective dimension at most one, for instance in a hereditary abelian category, then `X` is
projective (`Quiver.Hom.projective_of_projective_kernel_of_hasProjectiveDimensionLE_one`).

The chosen projective presentation `0 ⟶ ker π ⟶ P ⟶ X ⟶ 0` of an object is short exact
(`CategoryTheory.Projective.kernelShortComplex_shortExact`).

When coproducts indexed by `ι` are exact, for instance for direct sums of modules, a coproduct of
objects of projective dimension at most `n` has projective dimension at most `n`
(`CategoryTheory.hasProjectiveDimensionLT_of_isColimit_cofan`). The index type is arbitrary, so
this also covers countable direct sums in a category of modules in any universe.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 4.2 (hereditary rings).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- The projective dimension of `Y` is at most that of `X` exactly when every bound on the
projective dimension of `X` is also a bound for `Y`. The objects may lie in different abelian
categories. -/
theorem projectiveDimension_le_projectiveDimension_iff {D : Type*} [Category* D] [Abelian D]
    {X : C} {Y : D} :
    projectiveDimension Y ≤ projectiveDimension X ↔
      ∀ n : ℕ, HasProjectiveDimensionLT X n → HasProjectiveDimensionLT Y n :=
  ⟨fun h _ hX ↦ projectiveDimension_lt_iff.1 (h.trans_lt (projectiveDimension_lt_iff.2 hX)),
    fun h ↦ by
      unfold projectiveDimension
      refine sInf_le_sInf fun d hd ↦ ?_
      simp only [Set.mem_ofPred_eq] at hd ⊢
      exact fun i hi ↦ h i (hd i hi)⟩

/-- If `g : X ⟶ Y` has projective kernel and projective target, and its cokernel has projective
dimension at most one (for instance in an abelian category of projective dimension at most one),
then `X` is projective. -/
theorem _root_.Quiver.Hom.projective_of_projective_kernel_of_hasProjectiveDimensionLE_one
    {X Y : C} (g : X ⟶ Y) [Projective (kernel g)] [Projective Y]
    [HasProjectiveDimensionLE (cokernel g) 1] : Projective X := by
  -- The image of `g` is a subobject of `Y` with quotient the cokernel of `g`, so it is projective,
  -- and `X` is an extension of it by `kernel g`.
  have : Projective (image g) := projective_iff_hasProjectiveDimensionLT_one.mpr
    ((ShortComplex.shortExact_image_ι_cokernel_π g).hasProjectiveDimensionLT_X₁ 1
      inferInstance inferInstance)
  have hS := ShortComplex.kernelSequence_exact g
  exact projective_iff_hasProjectiveDimensionLT_one.mpr
    (hS.shortExact_factorThruImage.hasProjectiveDimensionLT_X₂ 1
      (inferInstanceAs (HasProjectiveDimensionLT (kernel g) 1))
      (inferInstanceAs (HasProjectiveDimensionLT (image g) 1)))

/-- A subobject of a projective object is projective if its quotient has projective dimension
at most one. -/
theorem projective_of_mono_of_hasProjectiveDimensionLE_one {X Y : C} (f : X ⟶ Y)
    [Mono f] [Projective Y] [HasProjectiveDimensionLE (cokernel f) 1] : Projective X :=
  have : Projective (kernel f) := (isZero_kernel_of_mono f).projective
  f.projective_of_projective_kernel_of_hasProjectiveDimensionLE_one

/-- **Dimension shifting along a morphism of projectives.** For a morphism `f : P ⟶ Q` of
projective objects, the exact sequence `0 ⟶ ker f ⟶ P ⟶ Q ⟶ coker f ⟶ 0` lowers the projective
dimension of `coker f` by two: it is less than `n + 3` exactly when that of `ker f` is less than
`n + 1`. -/
theorem hasProjectiveDimensionLT_cokernel_iff_kernel {P Q : C} (f : P ⟶ Q) [Projective P]
    [Projective Q] (n : ℕ) :
    HasProjectiveDimensionLT (cokernel f) (n + 3) ↔
      HasProjectiveDimensionLT (kernel f) (n + 1) := by
  have hz : kernel.ι f ≫ Abelian.factorThruImage f = 0 := by
    simp [← cancel_mono (Abelian.image.ι f)]
  have h₁ : (ShortComplex.mk _ _ hz).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (isKernelOfComp (Abelian.image.ι f) f (kernelIsKernel f) hz (by simp)) }
  have h₂ : (ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
      (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
  exact (h₂.hasProjectiveDimensionLT_X₃_iff (n + 1) ‹_›).trans
    (h₁.hasProjectiveDimensionLT_X₃_iff n ‹_›)

variable (C) [EnoughProjectives C]

variable {C} in
/-- The short complex `ker π ⟶ P ⟶ X` of the chosen projective presentation `π : P ⟶ X`. -/
noncomputable abbrev Projective.kernelShortComplex (X : C) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (Projective.π X)) (Projective.π X) (kernel.condition _)

variable {C} in
/-- The chosen projective presentation `0 ⟶ ker π ⟶ P ⟶ X ⟶ 0` is short exact. -/
theorem Projective.kernelShortComplex_shortExact (X : C) :
    (Projective.kernelShortComplex X).ShortExact :=
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }

instance (X : C) : Projective (Projective.kernelShortComplex X).X₂ :=
  inferInstanceAs (Projective (Projective.over X))

/-- Every object has projective dimension at most one precisely when every monomorphism into a
projective object has projective source. -/
theorem forall_hasProjectiveDimensionLE_one_iff_projective_of_mono :
    (∀ X : C, HasProjectiveDimensionLE X 1) ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [Mono f] [Projective Y], Projective X :=
  ⟨fun h _ _ f _ _ ↦ have := h (cokernel f); projective_of_mono_of_hasProjectiveDimensionLE_one f,
    fun h X ↦
      -- Name both instances, so that instance search does not try the local hypothesis `h`.
      have : Projective (Projective.over X) := Projective.projective_over X
      have : Projective (kernel (Projective.π X)) := h (kernel.ι _)
      (Projective.kernelShortComplex_shortExact X).hasProjectiveDimensionLT_X₃ 1
        inferInstance inferInstance⟩

section Coproducts

variable {C} {ι : Type*} [HasColimitsOfShape (Discrete ι) C]
  [HasExactColimitsOfShape (Discrete ι) C]

/-- When coproducts indexed by `ι` are exact, the point of a colimit cofan of objects of
projective dimension `< n` has projective dimension `< n`. -/
theorem hasProjectiveDimensionLT_of_isColimit_cofan {X : ι → C} {c : Cofan X} (hc : IsColimit c)
    (n : ℕ) (h : ∀ i, HasProjectiveDimensionLT (X i) n) : HasProjectiveDimensionLT c.pt n := by
  induction n generalizing X c with
  | zero =>
    simp only [hasProjectiveDimensionLT_zero_iff_isZero] at h ⊢
    exact (IsZero.iff_id_eq_zero _).2 (Cofan.IsColimit.hom_ext hc _ _ fun i ↦ (h i).eq_of_src _ _)
  | succ n ih =>
    rcases n with _ | n
    · have (i : ι) : Projective (X i) := projective_iff_hasProjectiveDimensionLT_one.2 (h i)
      exact projective_iff_hasProjectiveDimensionLT_one.1 (Projective.of_isColimit_cofan hc)
    -- Cover every summand by a projective object; the kernels have projective dimension `< n + 1`.
    have hK (i : ι) := Projective.kernelShortComplex_shortExact (X i)
    let T : ShortComplex (Discrete ι ⥤ C) :=
      ShortComplex.mk (X₁ := Discrete.functor fun i ↦ kernel (Projective.π (X i)))
        (X₂ := Discrete.functor fun i ↦ Projective.over (X i)) (X₃ := Discrete.functor X)
        (Discrete.natTrans fun i ↦ kernel.ι (Projective.π (X i.as)))
        (Discrete.natTrans fun i ↦ Projective.π (X i.as)) (by ext; simp)
    have hT : T.ShortExact := ShortComplex.shortExact_of_forall_evaluation T fun i ↦ hK i.as
    -- Taking coproducts gives a short exact sequence `∐ ker ⟶ ∐ P ⟶ ∐ X`.
    have h₁ : HasProjectiveDimensionLT (colimit T.X₁) (n + 1) :=
      ih (colimit.isColimit _) fun i ↦
        (hK i).hasProjectiveDimensionLT_X₁ (n + 1) inferInstance (h i)
    have : Projective (colimit T.X₂) := Projective.of_isColimit_cofan (colimit.isColimit
      (Discrete.functor fun i ↦ Projective.over (X i)))
    have : HasProjectiveDimensionLT (colimit (Discrete.functor X)) (n + 2) :=
      (hT.map_of_exact colim).hasProjectiveDimensionLT_X₃ (n + 1) h₁
        (hasProjectiveDimensionLT_of_ge (colimit T.X₂) 1 _ (by lia))
    exact hasProjectiveDimensionLT_of_iso (colimit.isoColimitCocone ⟨c, hc⟩) _

/-- When coproducts indexed by `ι` are exact, a coproduct of objects of projective dimension
`< n` has projective dimension `< n`. -/
instance (X : ι → C) (n : ℕ) [∀ i, HasProjectiveDimensionLT (X i) n] :
    HasProjectiveDimensionLT (∐ X) n :=
  hasProjectiveDimensionLT_of_isColimit_cofan (coproductIsCoproduct X) n inferInstance

end Coproducts

end CategoryTheory
