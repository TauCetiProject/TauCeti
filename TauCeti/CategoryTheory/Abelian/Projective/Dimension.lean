/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import TauCeti.CategoryTheory.Abelian.LeftDerived

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Comparing projective dimensions, and subobjects of projectives

If every bound `HasProjectiveDimensionLT X n` on one object implies the same bound on another
object `Y`, possibly in a different abelian category, then the projective dimension of `Y` is at
most that of `X`. This compares projective dimensions degree by degree without unfolding their
definition as an infimum.

In an abelian category with enough projectives, every object has projective dimension at most one
if and only if every subobject of a projective object is projective. This is the hereditary
condition, expressed using Mathlib's existing projective-dimension predicate.

A morphism `f` of projective objects shifts dimension by two between its kernel and its cokernel
(`CategoryTheory.hasProjectiveDimensionLT_cokernel_iff_kernel`).

When every object has projective dimension at most one, the criterion shows that the cycles and
boundaries of a complex of projective objects are projective. Surjections onto these boundaries
then split, so the cycles split off the terms.

The chosen projective presentation `0 ⟶ ker π ⟶ P ⟶ X ⟶ 0` of an object is short exact
(`CategoryTheory.Projective.kernelShortComplex_shortExact`).

When coproducts indexed by `ι` are exact, for instance for direct sums of modules, a coproduct of
objects of projective dimension at most `n` has projective dimension at most `n`
(`CategoryTheory.hasProjectiveDimensionLT_of_isColimit_cofan`). The index type is arbitrary, so
this also covers countable direct sums in a category of modules in any universe.

A right exact additive functor `F` preserving projective objects preserves the bound
`HasProjectiveDimensionLT X n` whenever its positive left derived functors below degree `n` vanish
at `X` (`CategoryTheory.Functor.hasProjectiveDimensionLT_obj_of_isZero_leftDerived`). For an
adjunction `L ⊣ R` whose right adjoint is fully faithful and preserves epimorphisms, the counit
`L(R(Y)) ≅ Y` transfers projective-dimension bounds from `R(Y)` to `Y` whenever the corresponding
left derived functors of `L` vanish at `R(Y)`
(`CategoryTheory.Adjunction.hasProjectiveDimensionLT_of_isZero_leftDerived`).

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 4.1 (projective dimension) and
  Section 4.2 (hereditary rings).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- If every bound on the projective dimension of `X` is also a bound for `Y`, then the projective
dimension of `Y` is at most that of `X`. The objects may lie in different abelian categories. -/
theorem projectiveDimension_le_of_hasProjectiveDimensionLT {D : Type*} [Category* D] [Abelian D]
    {X : C} {Y : D}
    (h : ∀ n : ℕ, HasProjectiveDimensionLT X n → HasProjectiveDimensionLT Y n) :
    projectiveDimension Y ≤ projectiveDimension X :=
  sInf_le_sInf fun _ hd i hi ↦ h i (hd i hi)

/-- A subobject of a projective object is projective if its quotient has projective dimension
at most one. -/
theorem projective_of_mono_of_hasProjectiveDimensionLE_one {X Y : C} (f : X ⟶ Y)
    [Mono f] [Projective Y] [HasProjectiveDimensionLE (cokernel f) 1] : Projective X := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
  exact projective_iff_hasProjectiveDimensionLT_one.mpr
    (hS.hasProjectiveDimensionLT_X₁ 1 inferInstance inferInstance)

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

/-- In an abelian category of projective dimension at most one, if `0 ⟶ X₁ ⟶ X₂ ⟶ X₃` is exact
with `X₁` and `X₃` projective, then `X₂` is projective: the image of `X₂ ⟶ X₃` is a subobject of
`X₃`, hence projective, so `X₂` is an extension of projective objects. -/
theorem _root_.CategoryTheory.ShortComplex.Exact.projective_X₂_of_mono_f
    [∀ X : C, HasProjectiveDimensionLE X 1] {S : ShortComplex C} (hS : S.Exact) [Mono S.f]
    [Projective S.X₁] [Projective S.X₃] : Projective S.X₂ := by
  have : Projective (image S.g) := projective_of_mono_of_hasProjectiveDimensionLE_one (image.ι S.g)
  have hS' : (ShortComplex.mk S.f (factorThruImage S.g)
      (comp_factorThruImage_eq_zero S.zero)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ hS.isColimitImage }
  exact projective_iff_hasProjectiveDimensionLT_one.mpr
    (hS'.hasProjectiveDimensionLT_X₂ 1
      (projective_iff_hasProjectiveDimensionLT_one.mp ‹_›)
      (projective_iff_hasProjectiveDimensionLT_one.mp ‹_›))

variable (C) [EnoughProjectives C]

/-- Every object has projective dimension at most one precisely when every monomorphism into a
projective object has projective source. -/
theorem forall_hasProjectiveDimensionLE_one_iff_projective_of_mono :
    (∀ X : C, HasProjectiveDimensionLE X 1) ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [Mono f] [Projective Y], Projective X := by
  constructor
  · intro h X Y f _ _
    have := h (cokernel f)
    exact projective_of_mono_of_hasProjectiveDimensionLE_one f
  · intro h X
    obtain ⟨P⟩ := EnoughProjectives.presentation X
    have : Projective P.p := P.projective
    have : Epi P.f := P.epi
    have : Projective (kernel P.f) := h (kernel.ι P.f)
    have hS : (ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel P.f) }
    exact hS.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

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
    have hT : T.ShortExact := by
      have hP : JointlyReflectIsomorphisms fun i : Discrete ι ↦ (evaluation _ C).obj i :=
        ⟨fun f h ↦ have : ∀ i, IsIso (f.app i) := h; NatIso.isIso_of_isIso_app f⟩
      exact (hP.shortExact_iff T).2 fun i ↦ hK i.as
    -- Taking coproducts gives a short exact sequence `∐ ker ⟶ ∐ P ⟶ ∐ X`.
    have h₁ : HasProjectiveDimensionLT (colimit T.X₁) (n + 1) :=
      ih (colimit.isColimit _) fun i ↦ (hK i).hasProjectiveDimensionLT_X₁ (n + 1)
        (hasProjectiveDimensionLT_of_ge _ 1 _ (by lia)) (h i)
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

section LeftDerived

variable {C} {D : Type*} [Category* D] [Abelian D]

/-- **Transport of projective dimension along a right exact functor.** Let `F : C ⥤ D` be a
right exact additive functor preserving projective objects. If `X` has projective dimension `< n`
and `(L_{i+1}F)(X) = 0` for every `i` with `i + 1 < n`, then `F.obj X` has projective dimension
`< n`. -/
theorem Functor.hasProjectiveDimensionLT_obj_of_isZero_leftDerived (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] (X : C) (n : ℕ)
    [hX : HasProjectiveDimensionLT X n]
    (h : ∀ i, i + 1 < n → IsZero ((F.leftDerived (i + 1)).obj X)) :
    HasProjectiveDimensionLT (F.obj X) n := by
  induction n generalizing X with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero] at hX ⊢
    exact F.map_isZero hX
  | succ n ih =>
    cases n with
    | zero =>
      have : Projective X := projective_iff_hasProjectiveDimensionLT_one.mpr hX
      exact projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
    | succ n =>
      -- Shift along the chosen projective presentation `0 ⟶ ker π ⟶ P ⟶ X ⟶ 0`.
      have hK := Projective.kernelShortComplex_shortExact X
      have : HasProjectiveDimensionLT (Projective.kernelShortComplex X).X₁ (n + 1) :=
        hK.hasProjectiveDimensionLT_X₁ (n + 1)
          (hasProjectiveDimensionLT_of_ge _ 1 _ (by lia)) hX
      have hmap : ((Projective.kernelShortComplex X).map F).ShortExact :=
        (hK.shortExact_map_iff_isZero_leftDerived_one F).mpr (h 0 (by lia))
      have hF₁ : HasProjectiveDimensionLT (F.obj (Projective.kernelShortComplex X).X₁) (n + 1) :=
        ih _ fun i hi ↦ (hK.isZero_leftDerived_add_two_iff F i).mp (h (i + 1) (by lia))
      exact hmap.hasProjectiveDimensionLT_X₃ (n + 1) hF₁
        (hasProjectiveDimensionLT_of_ge (F.obj (Projective.kernelShortComplex X).X₂) 1 _ (by lia))

/-- If `F : C ⥤ D` is right exact, additive and preserves projective objects, `X` has projective
dimension `≤ d`, and `(L_{i+1}F)(X) = 0` for every `i < d`, then `F.obj X` has projective
dimension `≤ d`. -/
theorem Functor.hasProjectiveDimensionLE_obj_of_isZero_leftDerived (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] (X : C) (d : ℕ)
    [HasProjectiveDimensionLE X d]
    (h : ∀ i < d, IsZero ((F.leftDerived (i + 1)).obj X)) :
    HasProjectiveDimensionLE (F.obj X) d :=
  F.hasProjectiveDimensionLT_obj_of_isZero_leftDerived X (d + 1) fun i hi ↦
    h i (Nat.lt_of_succ_lt_succ hi)

/-- If `F : C ⥤ D` is right exact, additive and preserves projective objects, and all positive
left derived functors of `F` vanish at `X`, then `projectiveDimension (F.obj X) ≤
projectiveDimension X`. -/
theorem Functor.projectiveDimension_obj_le_of_isZero_leftDerived (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] (X : C)
    (h : ∀ i, IsZero ((F.leftDerived (i + 1)).obj X)) :
    projectiveDimension (F.obj X) ≤ projectiveDimension X :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun n _ ↦
    F.hasProjectiveDimensionLT_obj_of_isZero_leftDerived X n fun i _ ↦ h i

/-- **Transport of projective dimension along a reflective adjunction.** Let `adj : L ⊣ R` be an
adjunction between abelian categories with `L` additive and `R` fully faithful and preserving
epimorphisms. If `R.obj Y` has projective dimension `< n` and `(L_{i+1}L)(R.obj Y) = 0` for every
`i` with `i + 1 < n`, then `Y` has projective dimension `< n`. -/
theorem Adjunction.hasProjectiveDimensionLT_of_isZero_leftDerived {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.Additive] [R.Full] [R.Faithful] [R.PreservesEpimorphisms] (Y : D) (n : ℕ)
    [HasProjectiveDimensionLT (R.obj Y) n]
    (h : ∀ i, i + 1 < n → IsZero ((L.leftDerived (i + 1)).obj (R.obj Y))) :
    HasProjectiveDimensionLT Y n := by
  have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L := PreservesColimitsOfSize.preservesFiniteColimits L
  have := Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms adj
  have := counit_isIso_of_R_fully_faithful adj
  have : HasProjectiveDimensionLT ((R ⋙ L).obj Y) n :=
    L.hasProjectiveDimensionLT_obj_of_isZero_leftDerived (R.obj Y) n h
  exact hasProjectiveDimensionLT_of_iso (asIso (adj.counit.app Y)) n

/-- For `adj : L ⊣ R` with `L` additive and `R` fully faithful and preserving epimorphisms, if
`R.obj Y` has projective dimension `≤ d` and `(L_{i+1}L)(R.obj Y) = 0` for every `i < d`, then
`Y` has projective dimension `≤ d`. -/
theorem Adjunction.hasProjectiveDimensionLE_of_isZero_leftDerived {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.Additive] [R.Full] [R.Faithful] [R.PreservesEpimorphisms] (Y : D) (d : ℕ)
    [HasProjectiveDimensionLE (R.obj Y) d]
    (h : ∀ i < d, IsZero ((L.leftDerived (i + 1)).obj (R.obj Y))) :
    HasProjectiveDimensionLE Y d :=
  adj.hasProjectiveDimensionLT_of_isZero_leftDerived Y (d + 1) fun i hi ↦
    h i (Nat.lt_of_succ_lt_succ hi)

/-- For `adj : L ⊣ R` with `L` additive and `R` fully faithful and preserving epimorphisms, if all
positive left derived functors of `L` vanish at `R.obj Y`, then
`projectiveDimension Y ≤ projectiveDimension (R.obj Y)`. -/
theorem Adjunction.projectiveDimension_le_of_isZero_leftDerived {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.Additive] [R.Full] [R.Faithful] [R.PreservesEpimorphisms] (Y : D)
    (h : ∀ i, IsZero ((L.leftDerived (i + 1)).obj (R.obj Y))) :
    projectiveDimension Y ≤ projectiveDimension (R.obj Y) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun n _ ↦
    adj.hasProjectiveDimensionLT_of_isZero_leftDerived Y n fun i _ ↦ h i

end LeftDerived

end CategoryTheory
