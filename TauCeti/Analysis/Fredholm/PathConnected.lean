/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.IndexRange
import Mathlib.Tactic.Abel
import TauCeti.Analysis.InnerProductSpace.Polar.Connected

/-!
# Norm-path classification of Fredholm operators

Two Fredholm operators from a complete complex inner-product space `E` to a complex normed space `F`
are joined by a continuous path through Fredholm operators exactly when their indices agree.
All paths use the native operator-norm topology, and the two spaces may differ. No separability,
dimension, nontriviality, or completeness assumption on `F` is imposed (any Fredholm operator out
of complete `E` automatically forces `F` to be complete by
`ContinuousLinearMap.IsFredholm.completeSpace_iff`).

A fixed parametrix reduces the converse to completing the finite-dimensional defect of
an index-zero Fredholm operator. An affine compact perturbation followed by composition
with an invertible path connects the original endpoints. Index invariance along the path
is supplied by `Path.index_eq`.

Consequently, for `ZerothHomotopy.fredholmIndex` (defined in
`TauCeti.Analysis.Fredholm.ContinuousFamily`, which also establishes path connectedness in finite
dimensions):

* over `RCLike 𝕜`, when `E` is an infinite-dimensional Hilbert space and `F` is a normed space with
  nonempty Fredholm locus `{T : E →L[𝕜] F // T.IsFredholm}`, `ZerothHomotopy.fredholmIndex` is
  surjective (`ZerothHomotopy.fredholmIndex_surjective`);
* from a complex Hilbert space `E` to a complex normed space `F`, `ZerothHomotopy.fredholmIndex` is
  always injective (`ZerothHomotopy.fredholmIndex_injective`), so when `E` is infinite-dimensional
  and the Fredholm locus is nonempty (in particular for `F = E` or whenever `E ≃L[ℂ] F`), it
  identifies `ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm}` bijectively with `ℤ`
  (`ZerothHomotopy.fredholmIndexEquiv`).

The path construction is adapted from
[AtiyahSinger/Analysis/FredholmPaths.lean][fredholm-paths] in Lean-Atiyah-Singer.
Its finite-defect and parametrix argument is supplementary to Lawson--Michelsohn,
*Spin Geometry*, Chapter III, §7, Lemmas 7.6--7.7 and Theorem 7.8, pp. 203--204, which prove the
same path-component classification by first making the Fredholm endpoints surjective.

## Main declarations

* `ContinuousLinearMap.IsFredholm.exists_path_of_index_eq`,
  `ContinuousLinearMap.nonempty_path_iff_index_eq`: two Fredholm operators from a complex Hilbert
  space to a complex normed space are joined by a norm-continuous Fredholm path if and only if
  their indices agree.
* `ContinuousLinearMap.zerothHomotopy_mk_eq_mk_iff_index_eq`,
  `ZerothHomotopy.fredholmIndex_injective`, `ZerothHomotopy.fredholmIndex_surjective`,
  `ZerothHomotopy.fredholmIndex_bijective`: injectivity, surjectivity, and bijectivity of the
  Fredholm index on path components.
* `ZerothHomotopy.fredholmIndexEquiv`: the canonical bijection
  `ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm} ≃ ℤ` when `E` is an infinite-dimensional complex
  Hilbert space, `F` is a complex normed space, and the Fredholm locus is nonempty.

## References

* D. S. Freed, *The Atiyah--Singer index theorem*, Bull. Amer. Math. Soc. **58** (2021), 517--566,
  arXiv:2107.03557, display (3.13).
* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §7, Lemmas 7.6--7.7 and Theorem 7.8, pp. 203--204,
  [DOI](https://doi.org/10.1515/9781400883912).

[fredholm-paths]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/FredholmPaths.lean
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped unitInterval

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Out of an infinite-dimensional real or complex Hilbert space `E` into a normed space `F` with
nonempty Fredholm locus, `ZerothHomotopy.fredholmIndex` surjects onto `ℤ`. -/
theorem ZerothHomotopy.fredholmIndex_surjective [Nonempty {T : E →L[𝕜] F // T.IsFredholm}]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    Function.Surjective (ZerothHomotopy.fredholmIndex (𝕜 := 𝕜) (E := E) (F := F)) :=
  fun n ↦ by
    obtain ⟨T, hT⟩ := ContinuousLinearMap.index_isFredholm_surjective (F := F) hE n
    exact ⟨.mk T, by simp [hT]⟩

end RCLike

section Hilbert

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Equal-index Fredholm operators from a complex Hilbert space to a complex normed space are
joined by an operator-norm continuous path consisting entirely of Fredholm operators. -/
theorem ContinuousLinearMap.IsFredholm.exists_path_of_index_eq {T₀ T₁ : E →L[ℂ] F}
    (hT₀ : T₀.IsFredholm) (hT₁ : T₁.IsFredholm) (hind : T₀.index = T₁.index) :
    ∃ γ : Path T₀ T₁, ∀ t, (γ t).IsFredholm := by
  have : CompleteSpace F := hT₀.completeSpace_iff.mp inferInstance
  -- A parametrix for T₁ reduces equality of indices to an index-zero operator on E.
  obtain ⟨Q, hQT, hTQ⟩ := hT₁.exists_isCompactOperator_comp_sub_one
  have hQ : Q.IsFredholm := .of_isCompactOperator_comp_sub_one hTQ hQT
  have hQindex : Q.index = -T₁.index :=
    ContinuousLinearMap.index_eq_neg_of_isCompactOperator_comp_sub_one hQT hTQ
  have hindex : (Q.comp T₀).index = 0 := by
    have hcomp := hQ.index_comp hT₀
    rw [← ContinuousLinearMap.index_def, ← ContinuousLinearMap.index_def,
      ← ContinuousLinearMap.index_def, hQindex, hind] at hcomp
    simpa only [neg_add_cancel] using hcomp
  obtain ⟨C, hC, hK⟩ :=
    (hQ.comp hT₀).exists_isInvertible_sub_isCompactOperator_of_index_eq_zero hindex
  -- Both terms in T₁(C - QT₀) + (T₁Q - 1)T₀ are compact.
  have hdiff : IsCompactOperator (T₁.comp C - T₀) := by
    have hleft := hK.clm_comp T₁
    have hright := hTQ.comp_clm T₀
    convert hleft.add hright using 1
    ext x
    simp only [Pi.add_apply, sub_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, one_apply_eq_self,
      map_sub]
    abel
  have hpath₀ := hT₀.joinedIn_of_isCompactOperator_sub hdiff
  obtain ⟨γC, hγC⟩ := hC.joinedIn (T := ContinuousLinearMap.id ℂ E)
    ⟨ContinuousLinearEquiv.refl ℂ E, rfl⟩
  let γ₁ : Path (T₁.comp C) T₁ :=
    (γC.map (f := fun A ↦ T₁.comp A)
      (continuous_const.clm_comp continuous_id)).cast rfl T₁.comp_id.symm
  have hγ₁ : ∀ t, (γ₁ t).IsFredholm := fun t ↦ hT₁.comp (hγC t).isFredholm
  exact hpath₀.trans ⟨γ₁, hγ₁⟩

/-- Two elements of the Fredholm locus are connected by a norm-continuous path precisely
when their indices agree. The topology is the subtype topology of `E →L[ℂ] F`. -/
@[simp]
theorem ContinuousLinearMap.nonempty_path_iff_index_eq
    (S T : {T : E →L[ℂ] F // T.IsFredholm}) :
    Nonempty (Path S T) ↔ S.val.index = T.val.index := by
  constructor
  · rintro ⟨γ⟩
    exact (γ.map continuous_subtypeVal).index_eq fun t ↦ (γ t).property
  · intro hind
    exact (joinedIn_iff_joined (F := {U : E →L[ℂ] F | U.IsFredholm})
      (x := S.val) (y := T.val) S.property T.property).mp
      (S.property.exists_path_of_index_eq T.property hind)

/-- Two Fredholm operators from a complex Hilbert space to a complex normed space define the same
path component in `ZerothHomotopy` if and only if they have the same Fredholm index. -/
@[simp]
theorem ContinuousLinearMap.zerothHomotopy_mk_eq_mk_iff_index_eq
    (S T : {T : E →L[ℂ] F // T.IsFredholm}) :
    ZerothHomotopy.mk S = ZerothHomotopy.mk T ↔ S.val.index = T.val.index :=
  ⟨fun h ↦ by simpa using congrArg ZerothHomotopy.fredholmIndex h,
    fun h ↦ let ⟨γ⟩ := (ContinuousLinearMap.nonempty_path_iff_index_eq S T).mpr h
      ZerothHomotopy.sound γ⟩

/-- From a complex Hilbert space `E` to a complex normed space `F`, the Fredholm index is injective
on the path components of the Fredholm locus. -/
theorem ZerothHomotopy.fredholmIndex_injective :
    Function.Injective (ZerothHomotopy.fredholmIndex (𝕜 := ℂ) (E := E) (F := F)) :=
  ZerothHomotopy.rec fun S ↦ ZerothHomotopy.rec fun T h ↦
    (ContinuousLinearMap.zerothHomotopy_mk_eq_mk_iff_index_eq S T).mpr (by simpa using h)

/-- From an infinite-dimensional complex Hilbert space `E` to a complex normed space `F` with
nonempty Fredholm locus, `ZerothHomotopy.fredholmIndex` is bijective onto `ℤ`. -/
theorem ZerothHomotopy.fredholmIndex_bijective [Nonempty {T : E →L[ℂ] F // T.IsFredholm}]
    (hE : ¬ FiniteDimensional ℂ E) :
    Function.Bijective (ZerothHomotopy.fredholmIndex (𝕜 := ℂ) (E := E) (F := F)) :=
  ⟨ZerothHomotopy.fredholmIndex_injective, ZerothHomotopy.fredholmIndex_surjective hE⟩

/-- When `E` is an infinite-dimensional complex Hilbert space, `F` is a complex normed space, and
the Fredholm locus `{T : E →L[ℂ] F // T.IsFredholm}` is nonempty (in particular for `F = E` or
whenever `E ≃L[ℂ] F`), the Fredholm index identifies the norm-path components of the Fredholm locus
bijectively with `ℤ`. -/
def ZerothHomotopy.fredholmIndexEquiv [Nonempty {T : E →L[ℂ] F // T.IsFredholm}]
    (hE : ¬ FiniteDimensional ℂ E) :
    ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm} ≃ ℤ :=
  Equiv.ofBijective ZerothHomotopy.fredholmIndex (ZerothHomotopy.fredholmIndex_bijective hE)

/-- Coercing `ZerothHomotopy.fredholmIndexEquiv` to a function gives `ZerothHomotopy.fredholmIndex`.
-/
@[simp]
theorem ZerothHomotopy.coe_fredholmIndexEquiv [Nonempty {T : E →L[ℂ] F // T.IsFredholm}]
    (hE : ¬ FiniteDimensional ℂ E) :
    ⇑(ZerothHomotopy.fredholmIndexEquiv (F := F) hE) = ZerothHomotopy.fredholmIndex :=
  Equiv.coe_ofBijective _ _

/-- Forward application of `ZerothHomotopy.fredholmIndexEquiv` is the Fredholm index on path
components. -/
theorem ZerothHomotopy.fredholmIndexEquiv_apply [Nonempty {T : E →L[ℂ] F // T.IsFredholm}]
    (hE : ¬ FiniteDimensional ℂ E) (c : ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm}) :
    ZerothHomotopy.fredholmIndexEquiv hE c = c.fredholmIndex := by
  simp

/-- The inverse of `ZerothHomotopy.fredholmIndexEquiv` sends `n : ℤ` to the path component of
Fredholm index `n`. -/
@[simp]
theorem ZerothHomotopy.fredholmIndex_fredholmIndexEquiv_symm
    [Nonempty {T : E →L[ℂ] F // T.IsFredholm}] (hE : ¬ FiniteDimensional ℂ E) (n : ℤ) :
    ((ZerothHomotopy.fredholmIndexEquiv (F := F) hE).symm n).fredholmIndex = n := by
  rw [← ZerothHomotopy.fredholmIndexEquiv_apply hE, Equiv.apply_symm_apply]

/-- Left-inverse simp lemma for `ZerothHomotopy.fredholmIndexEquiv.symm` on `c.fredholmIndex`. -/
@[simp]
theorem ZerothHomotopy.fredholmIndexEquiv_symm_fredholmIndex
    [Nonempty {T : E →L[ℂ] F // T.IsFredholm}] (hE : ¬ FiniteDimensional ℂ E)
    (c : ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm}) :
    (ZerothHomotopy.fredholmIndexEquiv hE).symm c.fredholmIndex = c := by
  rw [← ZerothHomotopy.fredholmIndexEquiv_apply hE, Equiv.symm_apply_apply]

/-- Left-inverse simp lemma for `ZerothHomotopy.fredholmIndexEquiv.symm` on the index `T.val.index`
of a Fredholm operator `T`. -/
@[simp]
theorem ZerothHomotopy.fredholmIndexEquiv_symm_index
    [Nonempty {T : E →L[ℂ] F // T.IsFredholm}] (hE : ¬ FiniteDimensional ℂ E)
    (T : {T : E →L[ℂ] F // T.IsFredholm}) :
    (ZerothHomotopy.fredholmIndexEquiv hE).symm T.val.index = .mk T := by
  rw [← ZerothHomotopy.fredholmIndex_mk, ZerothHomotopy.fredholmIndexEquiv_symm_fredholmIndex]

end Hilbert
