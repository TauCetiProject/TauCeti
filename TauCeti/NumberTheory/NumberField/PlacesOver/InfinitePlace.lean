/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import TauCeti.Analysis.AbsoluteValue.Archimedean
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Absolute values above an infinite place

Let `F` be a field extension of a field `K` and `v` an infinite place of `K`. Every absolute value
`w : AbsoluteValue F ℝ` lying over `v` is itself an infinite place of `F`: it is the norm of a
complex embedding of `F` (`NumberField.isInfinitePlace_of_liesOver`). No finiteness or
algebraicity of the extension is needed. Consequently the absolute values of `F` over `v` are
exactly the underlying absolute values of the infinite places of `F` over `v`
(`NumberField.setOf_liesOver_infinitePlace_eq_image`), so a statement about an absolute value
over an infinite place, as Diophantine approximation with algebraic targets requires, never has
to mention a completion.

The argument runs in the completion `F_w`. Since `w` restricts to `v` on `K`, the completion
`K_v` embeds isometrically into `F_w` (`AbsoluteValue.Completion.isometry_map`), and `K_v` is
`ℝ` or `ℂ` (`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal`,
`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex`). So `F_w` is a normed field
containing an isometric copy of `ℝ`, that is, a normed `ℝ`-algebra, and it embeds isometrically
into `ℂ` by `NormedAlgebra.Real.exists_algHom_complex_isometry`, a strengthening of
Gelfand–Mazur. Composing with `F → F_w` gives the complex embedding. Gelfand–Mazur asks neither
for the completeness of `F_w` nor for its finite dimension over `K_v`.

## Main results

* `NumberField.isInfinitePlace_of_liesOver`: an absolute value lying over an infinite place is an
  infinite place.
* `NumberField.setOf_liesOver_infinitePlace_eq_image`: the absolute values over an infinite place
  are the infinite places over it.
* `NumberField.exists_injective_infinitePlace_eq_of_liesOver`: absolute values over distinct
  infinite places are distinct infinite places, with multiplicity at least that of the place
  below.
* `NumberField.finite_setOf_liesOver_infinitePlace` and
  `NumberField.nonempty_setOf_liesOver_infinitePlace`: there are finitely many of them over a
  number field, and at least one over an algebraic extension.
* `NumberField.InfinitePlace.exists_liesOver_of_liesOver`: an absolute value over an infinite
  place extends to every algebraic extension.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.3, Proposition 1.3.1.
-/

public section

open AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Absolute values above an infinite place** (Bombieri–Gubler, Proposition 1.3.1): an
absolute value of a field extension `F` lying over an infinite place of `K` is an infinite place
of `F`, the norm of a complex embedding. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  -- `K_v` is `ℝ` or `ℂ`, so it contains an isometric copy of `ℝ`.
  obtain ⟨j, hj⟩ : ∃ j : ℝ →+* v.Completion, ∀ r, ‖j r‖ = ‖r‖ := by
    rcases v.isReal_or_isComplex with hv | hv
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
      refine ⟨e.symm.toRingHom, fun r ↦ ?_⟩
      have h := (AddMonoidHomClass.isometry_iff_norm _).mp
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv) (e.symm r)
      rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply] at h
      exact h.symm
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
      refine ⟨e.symm.toRingHom.comp Complex.ofRealHom, fun r ↦ ?_⟩
      have h := (AddMonoidHomClass.isometry_iff_norm _).mp
        (InfinitePlace.Completion.isometry_extensionEmbedding v) (e.symm r)
      rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv,
        RingEquiv.apply_symm_apply] at h
      simpa using h.symm
  -- The copy of `ℝ` in `K_v` maps isometrically into `F_w`, making `F_w` a normed `ℝ`-algebra.
  let ι : ℝ →+* w.Completion := (Completion.map v.1 w).comp j
  have hι (r : ℝ) : ‖ι r‖ = ‖r‖ := by
    rw [RingHom.comp_apply,
      (AddMonoidHomClass.isometry_iff_norm _).mp (Completion.isometry_map v.1 w), hj]
  let : NormedAlgebra ℝ w.Completion :=
    { ι.toAlgebra with
      norm_smul_le r x := by
        rw [RingHom.smul_toAlgebra, norm_mul, hι] }
  obtain ⟨ψ, hψ⟩ := NormedAlgebra.Real.exists_algHom_complex_isometry w.Completion
  refine ⟨(ψ : w.Completion →+* ℂ).comp (algebraMap F w.Completion), AbsoluteValue.ext fun x ↦ ?_⟩
  simp [place_apply, (AddMonoidHomClass.isometry_iff_norm _).mp hψ, Completion.algebraMap_def,
    Completion.norm_coe, WithAbs.algebraMap_right_apply]

/-- Absolute values over distinct infinite places of the base are distinct infinite places of the
extension, each with multiplicity at least that of the place below. This permits comparing
products of local factors without counting an infinite place of the extension twice. -/
theorem exists_injective_infinitePlace_eq_of_liesOver
    (S : Set (InfinitePlace K)) (w : S → AbsoluteValue F ℝ)
    (hw : ∀ v, (w v).LiesOver v.val.1) :
    ∃ W : S → InfinitePlace F, Function.Injective W ∧
      ∀ v, (W v).1 = w v ∧ v.val.mult ≤ (W v).mult := by
  let W (v : S) : InfinitePlace F := ⟨w v, have := hw v; isInfinitePlace_of_liesOver v.val (w v)⟩
  have hcomap (v : S) : (W v).comap (algebraMap K F) = v.val :=
    have := hw v; InfinitePlace.LiesOver.comap_eq (W v) v.val
  refine ⟨W, fun v u h ↦ Subtype.ext ?_, fun v ↦ ⟨rfl, ?_⟩⟩
  · rw [← hcomap v, ← hcomap u, h]
  · simpa only [hcomap] using InfinitePlace.mult_comap_le (algebraMap K F) (W v)

variable (F) in
/-- The absolute values of `F` lying over an infinite place `v` of `K` are exactly the underlying
absolute values of the infinite places of `F` over `v`. -/
theorem setOf_liesOver_infinitePlace_eq_image (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1} =
      Subtype.val '' InfinitePlace.placesOver F v := by
  ext w
  refine ⟨fun (hw : w.LiesOver v.1) ↦ ⟨⟨w, isInfinitePlace_of_liesOver v w⟩, hw, rfl⟩, ?_⟩
  rintro ⟨w', hw', rfl⟩
  exact hw'

variable (F) in
/-- A number field has only finitely many absolute values lying over a given infinite place. -/
theorem finite_setOf_liesOver_infinitePlace [NumberField F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  rw [setOf_liesOver_infinitePlace_eq_image]
  exact (Set.toFinite (InfinitePlace.placesOver F v)).image _

variable (F) in
/-- Every infinite place of `K` has an absolute value of an algebraic extension lying over it. -/
theorem nonempty_setOf_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := F) v
  exact ⟨w.1, InfinitePlace.liesOver_iff_comap_eq.mpr hw⟩

/-- An absolute value lying over an infinite place extends to every algebraic extension. -/
theorem InfinitePlace.exists_liesOver_of_liesOver {E : Type*} [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] (v : InfinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  obtain ⟨u, hu⟩ := nonempty_setOf_liesOver_infinitePlace E
    (⟨w, isInfinitePlace_of_liesOver v w⟩ : InfinitePlace F)
  exact ⟨u, hu⟩

end NumberField
