/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The weight spaces of a tensor power of the standard representation: their span by the monomial
-- basis, their independence, and their preservation by the symmetric-group action.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.TensorPower
-- The Weyl module and the two halves of its vanishing criterion on a monomial basis vector.
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Basic
-- Weight spaces are nonzero along the whole Weyl-group orbit.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Weyl

/-!
# The highest weight of a Weyl module

The Weyl module of a `μ`-tableau `t` is the image of the Young symmetrizer `c_t` acting on the
tensor power `(kⁿ)^{⊗|μ|}` of the standard representation of `GL n k`.  The tensor power is the
internal direct sum of its weight spaces, which are the coordinate subspaces spanned by the
monomial basis vectors of a given content, and `c_t` preserves each of them, so the Weyl module
inherits a weight decomposition. This file proves that decomposition, bounds the surviving weights
from above, and shows that the shape weight attains the bound.

The answer is the **dominance bound**: writing `r` for the row filling of `t`
(`TauCeti.YoungTableau.rowFilling`, the filling of the labels by their row indices), every weight
`l` of the Weyl module satisfies

`∑_{j < m} l j ≤ ∑_{j < m} μ.rowLen j`

for every bound `m`. The same bound holds for the weakly decreasing rearrangement
`TauCeti.dominantWeightOf l`, and the right-hand side is the weight `TauCeti.weightOfShape n μ`
of the shape itself. Over a field that is a `ℚ`-algebra, when `μ.colLen 0 ≤ n`, this weight occurs
and is the highest weight of the Weyl module in the dominance order, carried by the image of the
monomial basis vector `e_r`.
When `n < μ.colLen 0`, the Weyl module is zero (`TauCeti.YoungTableau.weylModule_eq_bot`).

Both halves come from the vanishing criterion of
`TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Basic`, read one monomial basis vector at
a time.  The symmetrizer annihilates `e_p` as soon as the filling `p` gives two labels of one
column the same basis index; so a filling whose basis vector survives is injective on columns, and
such a filling takes small values no more often than the row index does
(`TauCeti.YoungTableau.card_filter_lt_le_card_filter_rowIndex_lt`), which is the displayed
inequality once both counts are read as partial sums of contents.  Conversely, when
`μ.colLen 0 ≤ n`, `e_r` itself has content the row lengths of `μ` and is not annihilated,
so the bound is attained.

The dominance bound is proved over a field that is a `ℚ`-algebra: it has characteristic zero,
so it is infinite and its weight characters separate weights, which is the hypothesis under which
the weight spaces of the tensor power are its coordinate subspaces. The occurrence of the shape
weight only requires a nontrivial commutative `ℚ`-algebra.

## Main results

* `TauCeti.YoungTableau.weightOfMultiset_ofFn_rowFilling`: **the content of the row filling is the
  weight of the shape.**
* `TauCeti.YoungTableau.weightSpace_weylRep_eq_bot_of_card_filter_lt`: **a weight whose partial
  sums exceed those of the row lengths does not occur in the Weyl module**, with
  `TauCeti.YoungTableau.weylModule_toSubmodule_inf_weightSpace_eq_bot` its form inside the tensor
  power.
* `TauCeti.YoungTableau.sum_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot`: **the partial
  sums of each weight are bounded by those of the shape**, and
  `TauCeti.YoungTableau.sum_dominantWeightOf_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot`:
  the same bound for its dominant representative.
* `TauCeti.YoungTableau.nonneg_and_sum_eq_of_weightSpace_weylRep_ne_bot`: the weights are
  nonnegative of total degree `|μ|`, so the bounds give the dominance comparison.
* `TauCeti.YoungTableau.weightSpace_weylRep_weightOfShape_ne_bot`: **when `μ.colLen 0 ≤ n`,
  the weight of the shape occurs in the Weyl module**, so over a field it is the highest weight.
* `TauCeti.isInternal_weightSpace_weylRepOfShape`: the inherited weight decomposition of the
  shape-indexed Weyl module.
* `TauCeti.weightSpace_weylRepOfShape_eq_bot_iff`: transfers vanishing between the shape-indexed
  Weyl module and its row-superstandard tableau.
* `TauCeti.sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot`,
  `TauCeti.sum_dominantWeightOf_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot`, and
  `TauCeti.nonneg_and_sum_eq_of_weightSpace_weylRepOfShape_ne_bot`: the bounds and total degree for
  the shape-indexed Weyl module, hence for `TauCeti.schurFunctor`.
* `TauCeti.weightSpace_weylRepOfShape_weightOfShape_ne_bot`: occurrence in the shape-indexed Weyl
  module when `μ.colLen 0 ≤ n`.

## Implementation notes

The weight spaces of the Weyl module are spelled `weightSpace (W := _) (weylRep k n t) l`, with the
carrier supplied.  `TauCeti.weightSpace` asks for an additive *group*, while a subrepresentation
carries the additive monoid structure of a submodule, and the elaborator will not invert
`AddCommGroup.toAddCommMonoid` while the carrier is still a metavariable; naming the carrier lets
instance search produce the group structure first.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lectures 6 and 15.
-/

public section

open Matrix

universe u

namespace TauCeti

namespace YoungTableau

variable {k : Type u} {n : ℕ} {μ : YoungDiagram}

section CommRing

variable [CommRing k] [Algebra ℚ k]

/-! ## The content of the row filling -/

/-- **The content of the row filling is the weight of the shape**: the number of labels of a
`μ`-tableau lying in row `j` is the length of that row. -/
theorem weightOfMultiset_ofFn_rowFilling (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n) :
    weightOfMultiset (Sym.ofFn (rowFilling t hn) : Multiset (Fin n)) = (weightOfShape n μ).1 := by
  classical
  funext j
  have hset : (Finset.univ.filter fun x => rowFilling t hn x = j)
      = Finset.univ.filter fun y => rowIndex t y = (j : ℕ) :=
    Finset.filter_congr fun x _ => rowFilling_eq_iff t hn x j
  rw [weightOfMultiset_ofFn_apply, weightOfShape_apply, hset, card_filter_rowIndex_eq]

/-! ## The dominance bound -/

/-- **The symmetrizer annihilates a monomial basis vector whose filling takes small values too
often.**  If more labels satisfy `p x < m` than lie in the first `m` rows of `t`, then `p` is not
injective on the columns of `t`, so two labels of one column carry the same basis index. -/
private theorem
    permTensorActionAlgHom_youngSymmetrizerOver_tensorPowerBasis_eq_zero_of_card_filter_lt
    (t : YoungTableau μ) {p : Fin μ.card → Fin n} {m : ℕ}
    (h : (Finset.univ.filter fun x => rowIndex t x < m).card <
      (Finset.univ.filter fun x => (p x : ℕ) < m).card) :
    permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
        (tensorPowerBasis k n μ.card p) = 0 := by
  classical
  by_cases hp : Function.Injective fun x => ((p x : ℕ), colIndex t x)
  · exact absurd (card_filter_lt_le_card_filter_rowIndex_lt t hp m) (not_le.mpr h)
  · obtain ⟨a, b, hfab, hab⟩ := Function.not_injective_iff.mp hp
    rw [Prod.mk.injEq] at hfab
    exact permTensorActionAlgHom_youngSymmetrizerOver_tensorPowerBasis_eq_zero t hfab.2 hab
      (Fin.val_injective hfab.1)

end CommRing

section Field

variable [Field k] [Algebra ℚ k]

/-- **The symmetrizer annihilates a weight space whose partial sum `∑_{j < m} l j` exceeds the
number of labels in the first `m` rows of `t`.** The weight space is spanned by the monomial basis
vectors of content `l`, and the partial sums of a content count the places at which the filling
takes a small value. -/
private theorem weightSpace_tensorPowerRep_le_ker_of_card_filter_lt (t : YoungTableau μ)
    {l : Fin n → ℤ} {m : ℕ}
    (h : ((Finset.univ.filter fun x => rowIndex t x < m).card : ℤ) <
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l j) :
    weightSpace (tensorPowerRep k n μ.card) l ≤
      LinearMap.ker (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)) := by
  classical
  rw [weightSpace_tensorPowerRep_eq_span_image (weightChar_injective_of_algebraRat k) l]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨p, hp, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  refine permTensorActionAlgHom_youngSymmetrizerOver_tensorPowerBasis_eq_zero_of_card_filter_lt
    t (m := m) ?_
  have hl : ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l j =
      ((Finset.univ.filter fun x => (p x : ℕ) < m).card : ℤ) := by
    rw [← hp, sum_weightOfMultiset_ofFn_filter_val_lt]
  rw [hl] at h
  exact Nat.cast_lt.mp h

/-- **The Weyl module meets a weight space trivially when its partial sum `∑_{j < m} l j`
exceeds the number of labels in the first `m` rows of `t`.** The tensor power is spanned by its
weight spaces and the symmetrizer preserves each of them, so the image of the symmetrizer lies in
the sum of the weight spaces away from `l`, which is disjoint from the weight space at `l`. -/
theorem weylModule_toSubmodule_inf_weightSpace_eq_bot (t : YoungTableau μ)
    {l : Fin n → ℤ} {m : ℕ}
    (h : ((Finset.univ.filter fun x => rowIndex t x < m).card : ℤ) <
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l j) :
    (weylModule k n t).toSubmodule ⊓ weightSpace (tensorPowerRep k n μ.card) l = ⊥ := by
  classical
  have hker := weightSpace_tensorPowerRep_le_ker_of_card_filter_lt (k := k) t h
  have hrange : LinearMap.range (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)) ≤
      ⨆ l' ≠ l, weightSpace (tensorPowerRep k n μ.card) l' := by
    rw [← Submodule.map_top, ← iSup_weightSpace_tensorPowerRep_eq_top (k := k) (n := n)
      (d := μ.card), Submodule.map_iSup]
    refine iSup_le fun l' => ?_
    by_cases hl' : l' = l
    · subst hl'
      refine le_trans (Submodule.map_le_iff_le_comap.mpr ?_) bot_le
      rw [Submodule.comap_bot]
      exact hker
    · exact (map_weightSpace_tensorPowerRep_permTensorActionAlgHom_le _ l').trans (le_biSup _ hl')
  rw [weylModule_toSubmodule, ← le_bot_iff]
  calc LinearMap.range (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)) ⊓
        weightSpace (tensorPowerRep k n μ.card) l
      ≤ (⨆ l' ≠ l, weightSpace (tensorPowerRep k n μ.card) l') ⊓
          weightSpace (tensorPowerRep k n μ.card) l := inf_le_inf_right _ hrange
    _ = ⊥ := by
        rw [inf_comm]
        exact disjoint_iff.mp
          (iSupIndep_weightSpace (weightChar_injective_of_algebraRat k) _ l)

/-- **A weight whose partial sums exceed those of the row lengths does not occur in the Weyl
module.** -/
theorem weightSpace_weylRep_eq_bot_of_card_filter_lt (t : YoungTableau μ)
    {l : Fin n → ℤ} {m : ℕ}
    (h : ((Finset.univ.filter fun x => rowIndex t x < m).card : ℤ) <
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l j) :
    weightSpace (W := (weylModule k n t).toSubmodule) (weylRep k n t) l = ⊥ :=
  ((weylModule k n t).weightSpace_toRepresentation_eq_bot_iff l).mpr
    (weylModule_toSubmodule_inf_weightSpace_eq_bot t h)

/-- **The weights of the Weyl module are dominated by the weight of its shape**: every weight `l`
of the Weyl module satisfies the dominance inequalities

`∑_{j < m} l j ≤ ∑_{j < m} μ.rowLen j`,

the right-hand side being the corresponding partial sum of `TauCeti.weightOfShape n μ`. -/
theorem sum_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot (t : YoungTableau μ)
    {l : Fin n → ℤ}
    (hl : weightSpace (W := (weylModule k n t).toSubmodule) (weylRep k n t) l ≠ ⊥) (m : ℕ) :
    ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, (weightOfShape n μ).1 j := by
  classical
  rcases le_or_gt (μ.colLen 0) n with hn | hn
  · have hsum : ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, (weightOfShape n μ).1 j =
        ((Finset.univ.filter fun x => rowIndex t x < m).card : ℤ) := by
      rw [← weightOfMultiset_ofFn_rowFilling t hn, sum_weightOfMultiset_ofFn_filter_val_lt]
      simp only [val_rowFilling]
    by_contra hcon
    rw [hsum] at hcon
    exact hl (weightSpace_weylRep_eq_bot_of_card_filter_lt t (not_le.mp hcon))
  · exact (hl (by
      rw [Subrepresentation.weightSpace_toRepresentation_eq_bot_iff, weylModule_eq_bot t hn,
        Subrepresentation.toSubmodule_bot, bot_inf_eq])).elim

/-- **The dominant representative of every Weyl-module weight is dominated by the shape weight**:
permuting the coordinates preserves occurrence, so the partial-sum bound applies after sorting. -/
theorem sum_dominantWeightOf_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot
    (t : YoungTableau μ) {l : Fin n → ℤ}
    (hl : weightSpace (W := (weylModule k n t).toSubmodule) (weylRep k n t) l ≠ ⊥) (m : ℕ) :
    ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, (dominantWeightOf l).1 j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, (weightOfShape n μ).1 j := by
  exact sum_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot t
    (fun hbot => hl ((weightSpace_eq_bot_dominantWeightOf_iff
      (W := (weylModule k n t).toSubmodule) (weylRep k n t) l).mp hbot)) m

/-- **The weights of the Weyl module are nonnegative and of total degree `|μ|`**: a weight of a
subrepresentation is a weight of the ambient tensor power, whose weights are the exponent vectors
of the degree-`|μ|` monomials in `n` variables.  Together with the dominance bound this is the
statement that every weight of the Weyl module is dominated by `TauCeti.weightOfShape n μ` in the
dominance order on the weights of degree `|μ|`. -/
theorem nonneg_and_sum_eq_of_weightSpace_weylRep_ne_bot (t : YoungTableau μ) {l : Fin n → ℤ}
    (hl : weightSpace (W := (weylModule k n t).toSubmodule) (weylRep k n t) l ≠ ⊥) :
    (∀ i, 0 ≤ l i) ∧ ∑ i, l i = μ.card := by
  exact nonneg_and_sum_eq_of_weightSpace_tensorPowerRep_subrepresentation_ne_bot
    (weightChar_injective_of_algebraRat k) (weylModule k n t) hl

end Field

/-! ## The highest weight -/

section CommRing

variable [CommRing k] [Algebra ℚ k]

/-- The monomial basis vector of the row filling has the weight of the shape. -/
private theorem tensorPowerBasis_rowFilling_mem_weightSpace {R : Type u} [CommRing R]
    (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n) :
    tensorPowerBasis R n μ.card (rowFilling t hn) ∈
      weightSpace (tensorPowerRep R n μ.card) (weightOfShape n μ).1 := by
  rw [← weightOfMultiset_ofFn_rowFilling t hn]
  exact basis_mem_weightSpace_tensorPowerRep _

/-- **When `μ.colLen 0 ≤ n`, the weight of the shape occurs in the Weyl module**: the image under
the symmetrizer of the monomial basis vector of the row filling is a nonzero vector of that weight.

Over a field, together with
`TauCeti.YoungTableau.sum_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot`, this says that
`TauCeti.weightOfShape n μ` is the highest weight, in the dominance order, of the Weyl module of
any `μ`-tableau whose shape satisfies `μ.colLen 0 ≤ n`. -/
theorem weightSpace_weylRep_weightOfShape_ne_bot [Nontrivial k] (t : YoungTableau μ)
    (hn : μ.colLen 0 ≤ n) :
    weightSpace (W := (weylModule k n t).toSubmodule) (weylRep k n t)
      (weightOfShape n μ).1 ≠ ⊥ := by
  intro hbot
  have hbot' := ((weylModule k n t).weightSpace_toRepresentation_eq_bot_iff
    (weightOfShape n μ).1).mp hbot
  refine permTensorActionAlgHom_youngSymmetrizerOver_tensorPowerBasis_rowFilling_ne_zero
    (k := k) t hn ?_
  have hmem : permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
      (tensorPowerBasis k n μ.card (rowFilling t hn)) ∈
      (weylModule k n t).toSubmodule ⊓
        weightSpace (tensorPowerRep k n μ.card) (weightOfShape n μ).1 := by
    refine ⟨?_, map_weightSpace_tensorPowerRep_permTensorActionAlgHom_le _ _
      (Submodule.mem_map_of_mem (tensorPowerBasis_rowFilling_mem_weightSpace t hn))⟩
    exact permTensorActionAlgHom_youngSymmetrizerOver_tensorPowerBasis_mem_weylModule t _
  rw [hbot', Submodule.mem_bot] at hmem
  exact hmem

end CommRing

end YoungTableau

/-! ## The Weyl module of a shape -/

variable {k : Type u} {n : ℕ}

variable (k) (n) in
/-- Over a field that is a `ℚ`-algebra, the integer weight spaces of a Weyl module form an
internal direct sum. The rational algebra structure is required to define the Weyl module. -/
theorem isInternal_weightSpace_weylRepOfShape [Field k] [Algebra ℚ k] (μ : YoungDiagram) :
    DirectSum.IsInternal fun l : Fin n → ℤ =>
      weightSpace (W := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ) l := by
  classical
  let a := YoungTableau.youngSymmetrizerOver k
    (StandardYoungTableau.rowSuperstandard μ).toTableau
  let A := permTensorActionAlgHom k n μ.card a
  let q : Representation.IntertwiningMap (tensorPowerRep k n μ.card)
      (weylRepOfShape k n μ) :=
    { toLinearMap := A.codRestrict (weylModuleOfShape k n μ).toSubmodule (fun v => by
        rw [weylModuleOfShape_toSubmodule]
        exact LinearMap.mem_range.mpr ⟨v, rfl⟩)
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, weylRepOfShape_apply_coe]
        exact congrArg (fun f : Module.End k _ => f v)
          (commute_permTensorActionAlgHom_tensorPowerRep k n μ.card a g).eq }
  have hq : Function.Surjective q := by
    intro w
    have hw : w.val ∈ LinearMap.range A := by
      simpa only [weylModuleOfShape_toSubmodule] using w.property
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩
  exact isInternal_weightSpace_of_iSup_eq_top (weightChar_injective_of_algebraRat k)
    (q.iSup_weightSpace_eq_top_of_surjective hq iSup_weightSpace_tensorPowerRep_eq_top)

/-- A shape-indexed Weyl weight space vanishes exactly when the corresponding weight space for
its row-superstandard tableau vanishes. -/
theorem weightSpace_weylRepOfShape_eq_bot_iff [CommRing k] [Algebra ℚ k]
    (μ : YoungDiagram) (l : Fin n → ℤ) :
    weightSpace (W := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ) l = ⊥ ↔
      weightSpace
        (W := (YoungTableau.weylModule k n
          (StandardYoungTableau.rowSuperstandard μ).toTableau).toSubmodule)
        (YoungTableau.weylRep k n (StandardYoungTableau.rowSuperstandard μ).toTableau) l = ⊥ := by
  rw [Subrepresentation.weightSpace_toRepresentation_eq_bot_iff,
    Subrepresentation.weightSpace_toRepresentation_eq_bot_iff,
    weylModuleOfShape_toSubmodule, YoungTableau.weylModule_toSubmodule]

section Field

variable [Field k] [Algebra ℚ k]

/-- **The weights of the Weyl module of a shape are dominated by the weight of that shape**: the
shape-indexed form of `TauCeti.YoungTableau.sum_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot`
at the row-superstandard tableau. -/
theorem sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot {μ : YoungDiagram}
    {l : Fin n → ℤ}
    (hl : weightSpace (W := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ) l ≠ ⊥)
    (m : ℕ) :
    ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, (weightOfShape n μ).1 j := by
  exact YoungTableau.sum_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot (k := k)
    (StandardYoungTableau.rowSuperstandard μ).toTableau
    (fun hbot => hl ((weightSpace_weylRepOfShape_eq_bot_iff μ l).mpr hbot)) m

/-- **The dominant representatives of shape-indexed Weyl-module weights are dominated by the
shape weight**, by the bound for the row-superstandard tableau. -/
theorem sum_dominantWeightOf_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot
    {μ : YoungDiagram} {l : Fin n → ℤ}
    (hl : weightSpace (W := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ) l ≠ ⊥)
    (m : ℕ) :
    ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, (dominantWeightOf l).1 j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, (weightOfShape n μ).1 j := by
  exact YoungTableau.sum_dominantWeightOf_le_sum_weightOfShape_of_weightSpace_weylRep_ne_bot
    (k := k) (StandardYoungTableau.rowSuperstandard μ).toTableau
    (fun hbot => hl ((weightSpace_weylRepOfShape_eq_bot_iff μ l).mpr hbot)) m

/-- **The weights of the shape-indexed Weyl module are nonnegative of total degree `|μ|`**,
since it is a subrepresentation of that tensor power of the standard representation. -/
theorem nonneg_and_sum_eq_of_weightSpace_weylRepOfShape_ne_bot {μ : YoungDiagram} {l : Fin n → ℤ}
    (hl : weightSpace (W := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ) l ≠ ⊥) :
    (∀ i, 0 ≤ l i) ∧ ∑ i, l i = μ.card := by
  exact YoungTableau.nonneg_and_sum_eq_of_weightSpace_weylRep_ne_bot (k := k)
    (StandardYoungTableau.rowSuperstandard μ).toTableau
    (fun hbot => hl ((weightSpace_weylRepOfShape_eq_bot_iff μ l).mpr hbot))

end Field

section CommRing

variable [CommRing k] [Algebra ℚ k] [Nontrivial k]

/-- **When `μ.colLen 0 ≤ n`, the weight of a shape occurs in the Weyl module of that shape.**
Over a field it is therefore the highest weight of `TauCeti.weylRepOfShape` — and hence, over `ℂ`,
of `TauCeti.schurFunctor` — in the dominance order. -/
theorem weightSpace_weylRepOfShape_weightOfShape_ne_bot {μ : YoungDiagram}
    (hn : μ.colLen 0 ≤ n) :
    weightSpace (W := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ)
      (weightOfShape n μ).1 ≠ ⊥ := by
  exact fun hbot => YoungTableau.weightSpace_weylRep_weightOfShape_ne_bot (k := k)
    (StandardYoungTableau.rowSuperstandard μ).toTableau hn
    ((weightSpace_weylRepOfShape_eq_bot_iff μ _).mp hbot)

end CommRing

end TauCeti
