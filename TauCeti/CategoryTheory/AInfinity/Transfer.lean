/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.CategoryTheory.AInfinity.Basic

/-!
# Homological transfer for A-infinity categories

Let `𝒞` be an `A∞` category on a graded linear quiver `C`, and let `D` be a graded linear quiver
whose objects correspond to those of `C` through a bijection `e : D ≃ C`.  A special contraction
`(i, p, h)` of the total module of morphisms of `C`, with the differential `m₁`, onto the total
module of morphisms of `D` is **compatible with the hom modules**
(`TauCeti.LinearSpecialContraction.IsHomCompatible`) when `i` sends morphisms `X ⟶ Y` to morphisms
`e X ⟶ e Y`, `p` sends morphisms `U ⟶ V` to morphisms `e⁻¹ U ⟶ e⁻¹ V`, and `h` preserves every hom
module.  This is the shape of a contraction assembled from special contractions of the individual
Hom complexes of `𝒞`.

Homological transfer of the total `A∞` algebra of `𝒞` along such a contraction
(`TauCeti.AInfinityAlgebra.transfer`) gives an `A∞` structure on the total module of morphisms of
`D`, and this structure is again an `A∞` category, the **transferred `A∞` category**
`TauCeti.AInfinityCategory.transfer`.  Indeed, every operator entering the transfer preserves the
composable words from `U` to `V` and the non-composable words of the bar construction: the higher
bar differential of `𝒞`, because the Taylor map of `𝒞` is path-compatible; the tensor-trick
homotopy `K`, because it acts letter by letter through `h`, `i p` and Koszul twists, which preserve
every hom module; and therefore the perturbation operator `X = (1 + δ K)⁻¹ δ`, which is a pointwise
finite geometric series in them.  The letterwise inclusion and projection carry composable words
along `e` and `e⁻¹`, and non-composable words to non-composable words since `e` is injective.  So
the Taylor map `d_D + p X i` of the transferred structure is path-compatible.  The transferred
differential is `d_D` and the transferred composition is `g ∘ f = p m₂(i g, i f)`.

The Taylor maps of the extending morphism `i' = i - K X i` and of the projection morphism
`p' = p - p X K` of the transfer are path-compatible along `e` and along `e⁻¹` respectively
(`TauCeti.AInfinityCategory.isWordPathCompatible_taylor_transferInclusion` and
`TauCeti.AInfinityCategory.isWordPathCompatible_taylor_transferProjection`): they send composable
words to morphisms between the corresponding objects, as the components of an `A∞` functor must.

## Main definitions

* `TauCeti.LinearSpecialContraction.IsHomCompatible`: a special contraction of total modules of
  morphisms compatible with the hom modules along a bijection of objects.
* `TauCeti.AInfinityCategory.transfer`: the transferred `A∞` category.

## Main results

* `TauCeti.LinearSpecialContraction.reducedTensorWordsHomotopy_mem_composableWords` and
  `TauCeti.LinearSpecialContraction.reducedTensorWordsHomotopy_mem_nonComposableWords`: the
  tensor-trick homotopy preserves composable and non-composable words.
* `TauCeti.AInfinityCategory.higherBarDifferential_mem_composableWords` and
  `TauCeti.AInfinityCategory.higherBarDifferential_mem_nonComposableWords`: so does the higher bar
  differential of an `A∞` category.
* `TauCeti.AInfinityCategory.isWordPathCompatible_taylor_transfer`: the transferred operations are
  path-compatible.
* `TauCeti.AInfinityCategory.homInclusion_homDifferential_transfer` and
  `TauCeti.AInfinityCategory.homInclusion_comp_transfer`: the differential and the composition of
  the transferred category.
* `TauCeti.AInfinityCategory.isWordPathCompatible_taylor_transferInclusion` and
  `TauCeti.AInfinityCategory.isWordPathCompatible_taylor_transferProjection`: the Taylor maps of
  the extending and projection morphisms are path-compatible along `e` and `e⁻¹`.

## References

* P. Seidel, *Fukaya categories and Picard--Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, EMS, 2008, Section (1i), for homological perturbation of `A∞` categories along
  contractions of the morphism spaces.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 7.
-/

public section

namespace TauCeti

open GradedLinearQuiver ReducedTensorWords

universe u₁ u₂ v₁ v₂ w

variable {R : Type w} [CommRing R] {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]

/-! ### Contractions compatible with the hom modules -/

namespace LinearSpecialContraction

variable {dC : Module.End R (TotalHom R C)} {dD : Module.End R (TotalHom R D)}

section TensorTrick

variable {N : Type*} [AddCommGroup N] [Module R N] {dN : Module.End R N}
  (c : LinearSpecialContraction dC dN)
  (hh : ∀ (U V : C) (f : homModule (R := R) U V),
    c.homotopy (homInclusion U V f) ∈ LinearMap.range (homInclusion (R := R) U V))
  (hip : ∀ (U V : C) (f : homModule (R := R) U V),
    c.incl (c.proj (homInclusion U V f)) ∈ LinearMap.range (homInclusion (R := R) U V))
include hh hip

/-- The letter maps of the tensor-trick homotopy, a Koszul twist of a shift of the total grading,
the homotopy and the idempotent `i p`, preserve every hom module. -/
private theorem ite_mem_range (s : ℤ) {i j : ℕ} {U V : C} {u : TotalHom R C}
    (hu : u ∈ LinearMap.range (homInclusion (R := R) U V)) :
    (if i < j then ((totalGrading R C).shift s).koszulTwist 1 u
      else if i = j then c.homotopy u else c.incl (c.proj u)) ∈
      LinearMap.range (homInclusion (R := R) U V) := by
  obtain ⟨f, rfl⟩ := hu
  split_ifs
  · exact koszulTwist_shift_mem_range s 1 (LinearMap.mem_range_self _ _)
  · exact hh U V f
  · exact hip U V f

/-- **The tensor-trick homotopy preserves composable words** from `U` to `V`, for every shift of
the total grading, when the homotopy and the idempotent `i p` preserve every hom module: on a word
it is a sum of words obtained by applying a Koszul twist, the homotopy or `i p` to each letter. -/
theorem reducedTensorWordsHomotopy_mem_composableWords (s : ℤ) {U V : C}
    {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ composableWords R U V) :
    c.reducedTensorWordsHomotopy ((totalGrading R C).shift s) w ∈ composableWords R U V := by
  refine composableWords_induction (fun n hn a b z hz hab ha hb ↦ ?_) (by simp)
    (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun r x hx ↦ by rw [map_smul]; exact Submodule.smul_mem _ r hx) hw
  subst ha hb
  rw [reducedTensorWordsHomotopy_of_tprod]
  exact Submodule.sum_mem _ fun j _ ↦ of_tprod_mem_composableWords hn
    (z := fun i ↦ if i < j then ((totalGrading R C).shift s).koszulTwist 1 (z i)
      else if i = j then c.homotopy (z i) else c.incl (c.proj (z i)))
    (fun i hi ↦ ite_mem_range c hh hip s (hz i hi)) hab

/-- **The tensor-trick homotopy preserves non-composable words**, for every shift of the total
grading, when the homotopy and the idempotent `i p` preserve every hom module. -/
theorem reducedTensorWordsHomotopy_mem_nonComposableWords (s : ℤ)
    {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ nonComposableWords R C) :
    c.reducedTensorWordsHomotopy ((totalGrading R C).shift s) w ∈ nonComposableWords R C := by
  refine nonComposableWords_induction (fun n hn a b z hz hab ↦ ?_) (by simp)
    (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun r x hx ↦ by rw [map_smul]; exact Submodule.smul_mem _ r hx) hw
  rw [reducedTensorWordsHomotopy_of_tprod]
  exact Submodule.sum_mem _ fun j _ ↦ of_tprod_mem_nonComposableWords hn
    (z := fun i ↦ if i < j then ((totalGrading R C).shift s).koszulTwist 1 (z i)
      else if i = j then c.homotopy (z i) else c.incl (c.proj (z i)))
    (fun i hi ↦ ite_mem_range c hh hip s (hz i hi)) hab

end TensorTrick

/-- A special contraction of the total module of morphisms of `C` onto that of `D` is
**compatible with the hom modules** along a bijection of objects `e : D ≃ C` when its inclusion
sends morphisms `X ⟶ Y` to morphisms `e X ⟶ e Y`, its projection sends morphisms `U ⟶ V` to
morphisms `e⁻¹ U ⟶ e⁻¹ V`, and its homotopy sends morphisms `U ⟶ V` to morphisms `U ⟶ V`.
This is the shape of a contraction assembled from contractions of the individual hom modules. -/
structure IsHomCompatible (e : D ≃ C) (c : LinearSpecialContraction dC dD) : Prop where
  /-- The inclusion sends morphisms `X ⟶ Y` to morphisms `e X ⟶ e Y`. -/
  incl_homInclusion_mem (X Y : D) (f : homModule (R := R) X Y) :
    c.incl (homInclusion X Y f) ∈ LinearMap.range (homInclusion (R := R) (e X) (e Y))
  /-- The projection sends morphisms `U ⟶ V` to morphisms `e⁻¹ U ⟶ e⁻¹ V`. -/
  proj_homInclusion_mem (U V : C) (f : homModule (R := R) U V) :
    c.proj (homInclusion U V f) ∈ LinearMap.range (homInclusion (R := R) (e.symm U) (e.symm V))
  /-- The homotopy sends morphisms `U ⟶ V` to morphisms `U ⟶ V`. -/
  homotopy_homInclusion_mem (U V : C) (f : homModule (R := R) U V) :
    c.homotopy (homInclusion U V f) ∈ LinearMap.range (homInclusion (R := R) U V)

namespace IsHomCompatible

variable {e : D ≃ C} {c : LinearSpecialContraction dC dD} (hc : c.IsHomCompatible e)
include hc

/-- The idempotent `i p` of a contraction compatible with the hom modules preserves every hom
module. -/
theorem incl_proj_homInclusion_mem (U V : C) (f : homModule (R := R) U V) :
    c.incl (c.proj (homInclusion U V f)) ∈ LinearMap.range (homInclusion (R := R) U V) := by
  obtain ⟨g, hg⟩ := hc.proj_homInclusion_mem U V f
  have h := hc.incl_homInclusion_mem _ _ g
  rwa [hg, e.apply_symm_apply, e.apply_symm_apply] at h

/-- The projection sends morphisms `e X ⟶ e Y` to morphisms `X ⟶ Y`. -/
theorem proj_mem_range {X Y : D} {u : TotalHom R C}
    (hu : u ∈ LinearMap.range (homInclusion (R := R) (e X) (e Y))) :
    c.proj u ∈ LinearMap.range (homInclusion (R := R) X Y) := by
  obtain ⟨f, rfl⟩ := hu
  have h := hc.proj_homInclusion_mem (e X) (e Y) f
  rwa [e.symm_apply_apply, e.symm_apply_apply] at h

/-- Applied letter by letter, the inclusion sends composable words from `X` to `Y` to composable
words from `e X` to `e Y`. -/
theorem map_incl_mem_composableWords {X Y : D} {w : ReducedTensorWords R (TotalHom R D)}
    (hw : w ∈ composableWords R X Y) :
    ReducedTensorWords.map (R := R) c.incl w ∈ composableWords R (e X) (e Y) :=
  map_mem_composableWords hc.incl_homInclusion_mem hw

/-- Applied letter by letter, the inclusion sends non-composable words to non-composable words. -/
theorem map_incl_mem_nonComposableWords {w : ReducedTensorWords R (TotalHom R D)}
    (hw : w ∈ nonComposableWords R D) :
    ReducedTensorWords.map (R := R) c.incl w ∈ nonComposableWords R C :=
  map_mem_nonComposableWords hc.incl_homInclusion_mem e.injective hw

/-- Applied letter by letter, the projection sends composable words from `U` to `V` to composable
words from `e⁻¹ U` to `e⁻¹ V`. -/
theorem map_proj_mem_composableWords {U V : C} {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ composableWords R U V) :
    ReducedTensorWords.map (R := R) c.proj w ∈ composableWords R (e.symm U) (e.symm V) :=
  map_mem_composableWords hc.proj_homInclusion_mem hw

/-- Applied letter by letter, the projection sends non-composable words to non-composable
words. -/
theorem map_proj_mem_nonComposableWords {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ nonComposableWords R C) :
    ReducedTensorWords.map (R := R) c.proj w ∈ nonComposableWords R D :=
  map_mem_nonComposableWords hc.proj_homInclusion_mem e.symm.injective hw

end IsHomCompatible

end LinearSpecialContraction

namespace AInfinityCategory

/-! ### The higher bar differential of an `A∞` category -/

section HigherBarDifferential

variable (𝒞 : AInfinityCategory R C)

/-- The higher bar differential is the bar differential minus its letterwise part `m₁`. -/
private theorem higherBarDifferential_apply (w : ReducedTensorWords R (TotalHom R C)) :
    𝒞.higherBarDifferential w =
      gradedCoderiv ((totalGrading R C).shift 1) 𝒞.taylor 1 w -
        gradedCoderiv ((totalGrading R C).shift 1) (𝒞.differential ∘ₗ letter R (TotalHom R C)) 1
          w := by
  have h := LinearMap.congr_fun 𝒞.barDifferential_eq_unary_add_higher w
  rw [LinearMap.add_apply] at h
  rw [← 𝒞.grading_eq, ← AInfinityAlgebra.barDifferential_def,
    ← AInfinityAlgebra.unaryBarDifferential_eq_gradedCoderiv]
  exact eq_sub_of_add_eq' h.symm

/-- The higher bar differential of an `A∞` category preserves composable words from `X` to `Y`. -/
theorem higherBarDifferential_mem_composableWords {X Y : C}
    {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ composableWords R X Y) :
    𝒞.higherBarDifferential w ∈ composableWords R X Y := by
  rw [higherBarDifferential_apply]
  exact Submodule.sub_mem _
    (𝒞.isWordPathCompatible_taylor.gradedCoderiv_mem_composableWords 1 1 hw)
    (𝒞.isWordPathCompatible_differential_comp_letter.gradedCoderiv_mem_composableWords 1 1 hw)

/-- The higher bar differential of an `A∞` category preserves non-composable words. -/
theorem higherBarDifferential_mem_nonComposableWords {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ nonComposableWords R C) : 𝒞.higherBarDifferential w ∈ nonComposableWords R C := by
  rw [higherBarDifferential_apply]
  exact Submodule.sub_mem _
    (𝒞.isWordPathCompatible_taylor.gradedCoderiv_mem_nonComposableWords 1 1 hw)
    (𝒞.isWordPathCompatible_differential_comp_letter.gradedCoderiv_mem_nonComposableWords 1 1 hw)

end HigherBarDifferential

/-! ### The transferred `A∞` category -/

section Transfer

variable (𝒞 : AInfinityCategory R C) (e : D ≃ C) {dD : Module.End R (TotalHom R D)}
  (c : LinearSpecialContraction 𝒞.differential dD)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒞.grading.piece 𝒞.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl (totalGrading R D).piece 𝒞.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒞.grading.piece (totalGrading R D).piece 0)
  (hc : c.IsHomCompatible e)

include hc

/-- The differential of the retract preserves every hom module, being `p m₁ i`. -/
private theorem differential_retract_mem {X Y : D} {u : TotalHom R D}
    (hu : u ∈ LinearMap.range (homInclusion (R := R) X Y)) :
    dD u ∈ LinearMap.range (homInclusion (R := R) X Y) := by
  obtain ⟨f, rfl⟩ := hu
  have h₁ := LinearMap.congr_fun c.proj_comp_incl (homInclusion X Y f)
  have h₂ := LinearMap.congr_fun c.proj_comp_dM (c.incl (homInclusion X Y f))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h₁ h₂
  obtain ⟨g, hg⟩ := 𝒞.differential_mem_range (hc.incl_homInclusion_mem X Y f)
  rw [← h₁, ← h₂, ← hg]
  exact hc.proj_mem_range (LinearMap.mem_range_self _ _)

/-- The tensor-trick homotopy of the bar construction of `𝒞` preserves a submodule of composable or
non-composable words. -/
private theorem reducedTensorWordsHomotopy_mem
    {S : Submodule R (ReducedTensorWords R (TotalHom R C))}
    (hS : S = nonComposableWords R C ∨ ∃ X Y, S = composableWords R X Y)
    {z : ReducedTensorWords R (TotalHom R C)} (hz : z ∈ S) :
    c.reducedTensorWordsHomotopy (𝒞.grading.shift 1) z ∈ S := by
  rw [𝒞.grading_eq]
  rcases hS with rfl | ⟨X, Y, rfl⟩
  · exact c.reducedTensorWordsHomotopy_mem_nonComposableWords hc.homotopy_homInclusion_mem
      hc.incl_proj_homInclusion_mem 1 hz
  · exact c.reducedTensorWordsHomotopy_mem_composableWords hc.homotopy_homInclusion_mem
      hc.incl_proj_homInclusion_mem 1 hz

/-- The perturbation operator of the transfer preserves a submodule of composable or
non-composable words. -/
private theorem perturbationSeries_mem
    {S : Submodule R (ReducedTensorWords R (TotalHom R C))}
    (hS : S = nonComposableWords R C ∨ ∃ X Y, S = composableWords R X Y)
    {z : ReducedTensorWords R (TotalHom R C)} (hz : z ∈ S) :
    (𝒞.barTensorTrick c hh hincl hproj).perturbationSeries 𝒞.higherBarDifferential z ∈ S := by
  have hδ : ∀ y ∈ S, 𝒞.higherBarDifferential y ∈ S := by
    rcases hS with rfl | ⟨X, Y, rfl⟩
    · exact fun y hy ↦ 𝒞.higherBarDifferential_mem_nonComposableWords hy
    · exact fun y hy ↦ 𝒞.higherBarDifferential_mem_composableWords hy
  obtain ⟨k, hk⟩ := 𝒞.exists_pow_higherBarDifferential_comp_homotopy_eq_zero c
    (𝒞.higherBarDifferential z)
  refine LinearSpecialContraction.perturbationSeries_mem _ _
    (𝒞.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)
    (S := S.toAddSubgroup) hδ (fun y hy ↦ ?_) hz (k := k) ?_
  · rw [AInfinityAlgebra.barTensorTrick_homotopy]
    exact 𝒞.reducedTensorWordsHomotopy_mem e c hc hS hy
  · rwa [AInfinityAlgebra.barTensorTrick_homotopy, Module.End.mul_eq_comp]

/-- **The transferred operations are path-compatible.**  The Taylor map of the structure
transferred from `𝒞` along a contraction compatible with the hom modules sends composable words of
`D` from `X` to `Y` to morphisms `X ⟶ Y`, and non-composable words to zero. -/
theorem isWordPathCompatible_taylor_transfer :
    IsWordPathCompatible id (𝒞.toAInfinityAlgebra.transfer c hh hincl hproj).taylor where
  mem_range_of_mem_composableWords {X Y} {w} hw := by
    rw [AInfinityAlgebra.transfer_taylor, LinearMap.comp_apply,
      AInfinityAlgebra.letter_transferBarDifferential]
    refine add_mem ?_ ?_
    · exact 𝒞.differential_retract_mem e c hc
        (isWordPathCompatible_letter.mem_range_of_mem_composableWords hw)
    · have h := isWordPathCompatible_letter.mem_range_of_mem_composableWords
        (𝒞.perturbationSeries_mem e c hh hincl hproj hc (Or.inr ⟨_, _, rfl⟩)
          (hc.map_incl_mem_composableWords hw))
      exact hc.proj_mem_range h
  eq_zero_of_mem_nonComposableWords hw := by
    rw [AInfinityAlgebra.transfer_taylor, LinearMap.comp_apply,
      AInfinityAlgebra.letter_transferBarDifferential,
      isWordPathCompatible_letter.eq_zero_of_mem_nonComposableWords hw, map_zero, zero_add,
      isWordPathCompatible_letter.eq_zero_of_mem_nonComposableWords
        (𝒞.perturbationSeries_mem e c hh hincl hproj hc (Or.inl rfl)
          (hc.map_incl_mem_nonComposableWords hw)), map_zero]

/-- The **transferred `A∞` category**: the `A∞` structure transferred from the total algebra of
morphisms of `𝒞` along a special contraction onto the total module of morphisms of `D` which is
compatible with the hom modules along a bijection of objects `e : D ≃ C`.  Its differential is the
differential `d_D` of the retract (`homInclusion_homDifferential_transfer`), its composition is
`g ∘ f = p m₂(i g, i f)` (`homInclusion_comp_transfer`), and its higher operations are those of the
transferred `A∞` algebra. -/
noncomputable def transfer : AInfinityCategory R D where
  toAInfinityAlgebra := 𝒞.toAInfinityAlgebra.transfer c hh hincl hproj
  grading_eq := AInfinityAlgebra.transfer_grading ..
  isPathCompatible_m_of_pos :=
    (AInfinityAlgebra.isWordPathCompatible_taylor_iff (AInfinityAlgebra.transfer_grading ..)).1
      (𝒞.isWordPathCompatible_taylor_transfer e c hh hincl hproj hc)

/-- The total algebra of morphisms of the transferred category is the transferred `A∞` algebra. -/
@[simp]
theorem transfer_toAInfinityAlgebra :
    (𝒞.transfer e c hh hincl hproj hc).toAInfinityAlgebra =
      𝒞.toAInfinityAlgebra.transfer c hh hincl hproj := (rfl)

/-- The differential of the transferred category is the differential of the retract. -/
theorem homInclusion_homDifferential_transfer (X Y : D) (f : homModule (R := R) X Y) :
    homInclusion X Y ((𝒞.transfer e c hh hincl hproj hc).homDifferential X Y f) =
      dD (homInclusion X Y f) := by
  rw [homInclusion_homDifferential, transfer_toAInfinityAlgebra,
    AInfinityAlgebra.differential_transfer]

/-- The composition of the transferred category is `g ∘ f = p m₂(i g, i f)`. -/
theorem homInclusion_comp_transfer (X Y Z : D) (g : homModule (R := R) Y Z)
    (f : homModule (R := R) X Y) :
    homInclusion X Z ((𝒞.transfer e c hh hincl hproj hc).comp X Y Z g f) =
      c.proj (𝒞.m 2 ![c.incl (homInclusion Y Z g), c.incl (homInclusion X Y f)]) := by
  rw [homInclusion_comp, transfer_toAInfinityAlgebra, AInfinityAlgebra.mul_transfer,
    AInfinityAlgebra.mul_apply]

/-! ### The extending and projection morphisms -/

/-- **The extending morphism of the transfer is path-compatible along `e`**: its Taylor map sends
composable words of `D` from `X` to `Y` to morphisms `e X ⟶ e Y` of `C`, and non-composable words
to zero. -/
theorem isWordPathCompatible_taylor_transferInclusion :
    IsWordPathCompatible e (𝒞.toAInfinityAlgebra.transferInclusion c hh hincl hproj).taylor where
  mem_range_of_mem_composableWords {X Y} {w} hw := by
    have hi := hc.map_incl_mem_composableWords hw
    rw [AInfinityHom.taylor_def, LinearMap.comp_apply, AInfinityAlgebra.barMap_transferInclusion,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    exact isWordPathCompatible_letter.mem_range_of_mem_composableWords <| Submodule.sub_mem _ hi <|
      𝒞.reducedTensorWordsHomotopy_mem e c hc (Or.inr ⟨_, _, rfl⟩) <|
        𝒞.perturbationSeries_mem e c hh hincl hproj hc (Or.inr ⟨_, _, rfl⟩) hi
  eq_zero_of_mem_nonComposableWords {w} hw := by
    have hi := hc.map_incl_mem_nonComposableWords hw
    rw [AInfinityHom.taylor_def, LinearMap.comp_apply, AInfinityAlgebra.barMap_transferInclusion,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    exact isWordPathCompatible_letter.eq_zero_of_mem_nonComposableWords <| Submodule.sub_mem _ hi <|
      𝒞.reducedTensorWordsHomotopy_mem e c hc (Or.inl rfl) <|
        𝒞.perturbationSeries_mem e c hh hincl hproj hc (Or.inl rfl) hi

/-- **The projection morphism of the transfer is path-compatible along `e⁻¹`**: its Taylor map
sends composable words of `C` from `U` to `V` to morphisms `e⁻¹ U ⟶ e⁻¹ V` of `D`, and
non-composable words to zero. -/
theorem isWordPathCompatible_taylor_transferProjection :
    IsWordPathCompatible e.symm
      (𝒞.toAInfinityAlgebra.transferProjection c hh hincl hproj).taylor where
  mem_range_of_mem_composableWords {U V} {w} hw := by
    rw [AInfinityHom.taylor_def, LinearMap.comp_apply, AInfinityAlgebra.barMap_transferProjection,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_sub]
    exact isWordPathCompatible_letter.mem_range_of_mem_composableWords <|
      hc.map_proj_mem_composableWords <| Submodule.sub_mem _ hw <|
        𝒞.perturbationSeries_mem e c hh hincl hproj hc (Or.inr ⟨_, _, rfl⟩) <|
          𝒞.reducedTensorWordsHomotopy_mem e c hc (Or.inr ⟨_, _, rfl⟩) hw
  eq_zero_of_mem_nonComposableWords {w} hw := by
    rw [AInfinityHom.taylor_def, LinearMap.comp_apply, AInfinityAlgebra.barMap_transferProjection,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_sub]
    exact isWordPathCompatible_letter.eq_zero_of_mem_nonComposableWords <|
      hc.map_proj_mem_nonComposableWords <| Submodule.sub_mem _ hw <|
        𝒞.perturbationSeries_mem e c hh hincl hproj hc (Or.inl rfl) <|
          𝒞.reducedTensorWordsHomotopy_mem e c hc (Or.inl rfl) hw

end Transfer

end AInfinityCategory

end TauCeti
