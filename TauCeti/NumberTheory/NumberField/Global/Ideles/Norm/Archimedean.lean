/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm

/-!
# Archimedean weights of norm-one ideles of CM fields

At each infinite place of a CM field the relative norm to the maximal real subfield is the
squared complex absolute value. Thus the archimedean part of a norm-one idele is a tuple of
points of the unit circle. Every such tuple occurs with trivial finite part, so testing on these
ideles isolates the archimedean contributions to a character with prescribed tame part.

The weight convention uses integer exponents on the circle coordinates, as in
`New.AutChar.HasWeight` in `Lib/ClassField/HeckeCharacter/Basic.lean` of lsernau/grh-lean
at `72fead1`. A weight is expressed relative to the representatives `InfinitePlace.embedding`;
reversing the representative at a place reverses the exponent there.
-/

public section

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.IsCMField
open NumberField.InfinitePlace.Completion

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

open TauCeti.GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

local notation "E⁺" => maximalRealSubfield E
local notation "U" => MonoidHom.ker (ContinuousMonoidHom.toMonoidHom (ideleNormMap E⁺ E))

namespace NumberField.InfinitePlace

/-- Every archimedean coordinate of a CM norm-one idele has complex absolute value one. -/
theorem norm_extensionEmbedding_ideleInfiniteCoord (w : InfinitePlace E) (x : U) :
    ‖extensionEmbedding w (w.ideleInfiniteCoord x.val : w.Completion)‖ = 1 := by
  let v := w.comap (algebraMap E⁺ E)
  have hnorm : ideleNormMap E⁺ E x.val = 1 := x.property
  have hcoord := congrArg v.ideleInfiniteCoord hnorm
  rw [ideleInfiniteCoord_ideleNormMap, map_one,
    finprod_eq_single _ ⟨w, liesOver_iff_comap_eq.mpr rfl⟩] at hcoord
  · have h := congrArg (fun a : v.Completionˣ ↦
      extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (a : v.Completion)) hcoord
    rw [Units.val_one, map_one, TauCeti.Algebra.coe_normUnits,
      extensionEmbeddingOfIsReal_norm_of_isRamified
        (isRamified_iff.mpr ⟨IsTotallyComplex.isComplex w, IsTotallyReal.isReal v⟩),
      Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (extensionEmbedding w (w.ideleInfiniteCoord x.val : w.Completion))]
  · intro a ha
    exact (ha (Subtype.ext ((equivInfinitePlace E).injective
      (liesOver_iff_comap_eq.mp a.property)))).elim

/-- The circle coordinate at a complex place, oriented by the representative embedding chosen
by `InfinitePlace.embedding`. -/
def normOneCircleCoord (w : InfinitePlace E) : U →ₜ* Circle where
  toFun x := ⟨extensionEmbedding w (w.ideleInfiniteCoord x.val : w.Completion),
    mem_sphere_zero_iff_norm.mpr (norm_extensionEmbedding_ideleInfiniteCoord w x)⟩
  map_one' := Circle.ext (by simp)
  map_mul' x y := Circle.ext (by
    -- Forget the circle membership proofs before rewriting the idele coordinates.
    change extensionEmbedding w (w.ideleInfiniteCoord (x * y).val : w.Completion) =
      extensionEmbedding w (w.ideleInfiniteCoord x.val : w.Completion) *
      extensionEmbedding w (w.ideleInfiniteCoord y.val : w.Completion)
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, map_mul])
  continuous_toFun := by
    refine Continuous.subtype_mk (?_ : Continuous fun x : U ↦
      extensionEmbedding w (w.ideleInfiniteCoord x.val : w.Completion)) _
    simp only [coe_ideleInfiniteCoord]
    exact (isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp (continuous_fst.comp
        (Units.continuous_val.comp continuous_subtypeVal)))

/-- Read the circle coordinate in `ℂ` using the embedding of the completion. -/
theorem coe_normOneCircleCoord (w : InfinitePlace E) (x : U) :
    (normOneCircleCoord w x : ℂ) = extensionEmbedding w
      (w.ideleInfiniteCoord x.val : w.Completion) := (rfl)

end NumberField.InfinitePlace

namespace TauCeti.GlobalNumberFields

/-- A prescribed tuple of circle coordinates is realized by a norm-one idele whose finite
part is trivial. -/
theorem exists_normOneCircleCoord_eq (z : InfinitePlace E → Circle) :
    ∃ x : U, IdeleGroup.toFiniteIdele (𝓞 E) E x.val = 1 ∧
      ∀ w, w.normOneCircleCoord x = z w := by
  classical
  let u (w : InfinitePlace E) : w.Completionˣ := Units.map
    (ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.toMonoidHom
    (Circle.toUnits (z w))
  have hu (w : InfinitePlace E) : extensionEmbedding w (u w : w.Completion) = (z w : ℂ) := by
    simp [u, ← ringEquivComplexOfIsComplex_apply (IsTotallyComplex.isComplex w)]
  have hnorm (w : InfinitePlace E) :
      ideleNormMap E⁺ E (IdeleGroup.ofCompletion (𝓞 E) E w (u w)) = 1 := by
    let v := w.comap (algebraMap E⁺ E)
    have : w.LiesOver v := liesOver_iff_comap_eq.mpr rfl
    rw [ideleNormMap_ofCompletion v w]
    have hn : Algebra.normUnits v.Completion (u w) = 1 := by
      apply Units.ext
      apply (extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).injective
      rw [Units.val_one, map_one, Algebra.coe_normUnits,
        extensionEmbeddingOfIsReal_norm_of_isRamified
          (isRamified_iff.mpr ⟨IsTotallyComplex.isComplex w, IsTotallyReal.isReal v⟩),
        hu, Circle.normSq_coe]
    rw [hn, map_one]
  let x : IdeleGroup (𝓞 E) E := ∏ w, IdeleGroup.ofCompletion (𝓞 E) E w (u w)
  have hx : ideleNormMap E⁺ E x = 1 := by simp only [x, map_prod, hnorm, Finset.prod_const_one]
  refine ⟨⟨x, hx⟩, ?_, fun w ↦ Circle.ext ?_⟩
  · simp [x, map_prod, IdeleGroup.toFiniteIdele_ofCompletion]
  · have hcoord : w.ideleInfiniteCoord x = u w := by
      dsimp only [x]
      rw [ideleInfiniteCoord_prod_ofCompletion]
      simp
    exact (coe_normOneCircleCoord w ⟨x, hx⟩).trans
      ((congrArg (fun a : w.Completionˣ ↦ extensionEmbedding w (a : w.Completion))
        hcoord).trans (hu w))

/-- The continuous archimedean character of weight `e` on the norm-one ideles. -/
def normOneWeightCharacter (e : InfinitePlace E → ℤ) : U →ₜ* Circle :=
  ∏ w, normOneCircleCoord w ^ e w

/-- The weight character is the product of the indicated powers of the circle coordinates. -/
theorem normOneWeightCharacter_apply (e : InfinitePlace E → ℤ) (x : U) :
    normOneWeightCharacter e x = ∏ w, normOneCircleCoord w x ^ e w := by
  let ev : (U →ₜ* Circle) →* Circle := ⟨⟨fun k ↦ k x, rfl⟩, fun _ _ ↦ rfl⟩
  calc
    _ = ev (∏ w, normOneCircleCoord w ^ e w) := (rfl)
    _ = ∏ w, ev (normOneCircleCoord w ^ e w) := map_prod ev _ _
    _ = _ := Finset.prod_congr rfl fun w _ ↦ map_zpow ev _ _

/-- Adding two weights multiplies their archimedean characters. -/
@[simp] theorem normOneWeightCharacter_add (e f : InfinitePlace E → ℤ) :
    normOneWeightCharacter (e + f) = normOneWeightCharacter e * normOneWeightCharacter f := by
  apply ContinuousMonoidHom.ext
  intro x
  rw [ContinuousMonoidHom.mul_apply, normOneWeightCharacter_apply (e + f) x,
    normOneWeightCharacter_apply e x, normOneWeightCharacter_apply f x, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ ↦ zpow_add _ _ _

/-- Weight zero is the trivial archimedean character. -/
@[simp] theorem normOneWeightCharacter_zero :
    normOneWeightCharacter (0 : InfinitePlace E → ℤ) = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  rw [normOneWeightCharacter_apply (0 : InfinitePlace E → ℤ) x]
  simp

/-- At a rational norm-one point the archimedean character is the product of the powers
of the corresponding field embeddings. This is the infinite factor of the compatibility
condition for extending a prescribed character of the integral ideles. -/
theorem coe_normOneWeightCharacter_unitEmbedding (e : InfinitePlace E → ℤ) (a : Eˣ)
    (ha : TauCeti.Algebra.normUnits E⁺ a = 1) :
    (normOneWeightCharacter e
      ⟨IdeleGroup.unitEmbedding (𝓞 E) E a, by
        exact (ideleNormMap_unitEmbedding E⁺ E a).trans (by rw [ha, map_one])⟩ : ℂ) =
      ∏ w, w.embedding (a : E) ^ e w := by
  let x : U := ⟨IdeleGroup.unitEmbedding (𝓞 E) E a,
    (ideleNormMap_unitEmbedding E⁺ E a).trans (by rw [ha, map_one])⟩
  calc
    _ = Circle.coeHom (normOneWeightCharacter e x) := (rfl)
    _ = _ := by
      rw [normOneWeightCharacter_apply, map_prod]
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      have hcoord : (w.normOneCircleCoord x : ℂ) = w.embedding (a : E) :=
        (coe_normOneCircleCoord w x).trans (by
          have h : w.ideleInfiniteCoord x.val = Units.map (algebraMap E w.Completion) a :=
            ideleInfiniteCoord_unitEmbedding w a
          rw [h, Units.coe_map, MonoidHom.coe_ofClass, Completion.algebraMap_apply_eq_coe]
          exact (extensionEmbedding_coe w ((WithAbs.equiv w.val).symm (a : E))).trans
            (congrArg w.embedding ((WithAbs.equiv w.val).apply_symm_apply _)))
      rw [map_zpow]
      exact congrArg (· ^ e w) hcoord

end TauCeti.GlobalNumberFields
