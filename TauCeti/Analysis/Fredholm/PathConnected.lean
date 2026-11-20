/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.InnerProductSpace.UnitaryPath
import Mathlib.Tactic.Abel

/-!
# Norm-path classification of Fredholm operators

Two Fredholm operators between complete complex inner-product spaces are joined by a
continuous path through Fredholm operators exactly when their indices agree. All paths
use the native operator-norm topology, and the two spaces may differ. No separability,
dimension or nontriviality assumption is imposed.

A fixed parametrix reduces the converse to completing the finite-dimensional defect of
an index-zero Fredholm operator. An affine compact perturbation followed by composition
with an invertible path connects the original endpoints. Index invariance along the path
is supplied by `Path.index_eq`.

The proof is adapted from
[AtiyahSinger/Analysis/FredholmPaths.lean][fredholm-paths] in Lean-Atiyah-Singer.
Its finite-defect and parametrix argument is supplementary to Lawson--Michelsohn,
*Spin Geometry*, Chapter III, §7, Lemmas 7.6--7.7, p. 203, which prove the same path
connectedness statements by first making the Fredholm endpoints surjective.

## References

* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §7, Lemmas 7.6--7.7, p. 203,
  [DOI](https://doi.org/10.1515/9781400883912).

[fredholm-paths]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/FredholmPaths.lean
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped unitInterval

section Hilbert

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Equal-index Fredholm operators between complex Hilbert spaces are joined by an
operator-norm continuous path consisting entirely of Fredholm operators. -/
theorem ContinuousLinearMap.IsFredholm.exists_path_of_index_eq {T₀ T₁ : E →L[ℂ] F}
    (hT₀ : T₀.IsFredholm) (hT₁ : T₁.IsFredholm) (hind : T₀.index = T₁.index) :
    ∃ γ : Path T₀ T₁, ∀ t, (γ t).IsFredholm := by
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
  obtain ⟨γC, hγC⟩ := hC.exists_path_to_id
  let γ₁ : Path (T₁.comp C) T₁ :=
    (γC.map (f := fun A ↦ T₁.comp A)
      (continuous_const.clm_comp continuous_id)).cast rfl T₁.comp_id.symm
  have hγ₁ : ∀ t, (γ₁ t).IsFredholm := by
    intro t
    simpa only [γ₁, Path.cast_coe, Path.map_coe, Function.comp_apply] using
      hT₁.comp (hγC t).isFredholm
  exact hpath₀.trans ⟨γ₁, hγ₁⟩

/-- Two elements of the Fredholm locus are connected by a norm-continuous path precisely
when their indices agree. The topology is the subtype topology of `E →L[ℂ] F`. -/
@[simp]
theorem ContinuousLinearMap.nonempty_path_iff_index_eq
    (S T : {T : E →L[ℂ] F // T.IsFredholm}) :
    Nonempty (Path S T) ↔ S.val.index = T.val.index := by
  constructor
  · rintro ⟨γ⟩
    exact (γ.map continuous_subtype_val).index_eq fun t ↦ (γ t).property
  · intro hind
    exact (joinedIn_iff_joined (F := {U : E →L[ℂ] F | U.IsFredholm})
      (x := S.val) (y := T.val) S.property T.property).mp
      (S.property.exists_path_of_index_eq T.property hind)

end Hilbert
