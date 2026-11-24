/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.GeneralPosition
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproxProd

import TauCeti.Algebra.Order.BigOperators.GroupWithZero.Finset
import TauCeti.Analysis.AbsoluteValue.LinearForms
import TauCeti.Data.Finset.Max
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# The approximation product of forms in general position

Vojta's form of the Subspace Theorem allows any number of linear forms at each place, provided
they are in general position. Let `K` be a number field, `F` a field extension of `K`, and at
each place `v` in finite sets `Sinf` of infinite and `Sfin` of finite places fix an absolute value
`w v` of `F` and the forms `L v k`, `k ∈ B v`, for a finset `B v` of a common index type `κ`. The
**general approximation product** `NumberField.generalProd Sinf Sfin w B L x` is the product, over
the places, of

`∏ k ∈ B v, w v (L v k x) / ⨆ j, v (x j)`,

raised to the power `mult v` at an infinite place. With exactly `card ι` forms at every place it is
the approximation product `NumberField.approxProd` (`NumberField.generalProd_univ_eq_approxProd`),
and like it, it is invariant under scaling the point (`NumberField.generalProd_smul`).

The main result reduces the general product to finitely many approximation products of systems of
`card ι` linearly independent forms, losing only a constant factor:
`NumberField.exists_finset_forall_approxProd_le_mul_generalProd`. If the forms at each place are in
general position (`Module.Dual.IsGeneralPosition`), there are finitely many such systems and a
constant `C` such that every nonzero point `x` has, for one of the systems `L'`,
`approxProd Sinf Sfin w L' x ≤ C * generalProd Sinf Sfin w B L x`. At a place with at least
`card ι` forms the system keeps the `card ι` forms of smallest value at `x`. They are a basis of
the dual, so they bound every coordinate of `x` by a constant times the largest of them, and each
discarded value is at least the local sup norm over that constant. At a place with fewer forms
the system completes them by coordinate forms, whose factors are at most `1`. The Subspace Theorem
for forms in general position follows by applying the Subspace Theorem with coefficients in `F` to
each of the finitely many systems, with half the exponent.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Definition 7.2.8 and
  Theorem 7.2.9.
* P. Vojta, *Diophantine approximations and value distribution theory*, Lecture Notes in Math.
  1239 (1987).
-/

public section

open AbsoluteValue Finset Module Module.Dual

namespace NumberField

variable {K F ι κ : Type*} [Field K] [Field F] [Algebra K F]

section Local

variable [Fintype ι]

/-- At an absolute value `w`, `card ι` linearly independent forms `l k`, `k ∈ t`, bound every
coordinate of a point by a constant times any common bound on their values. The constant comes from
`AbsoluteValue.exists_one_le_forall_apply_le_mul`; the hypotheses sit inside the existential so
that the constant can be chosen for every `t` at once. -/
private theorem exists_one_le_forall_apply_le_mul (w : AbsoluteValue F ℝ)
    (l : κ → Dual F (ι → F)) (t : Finset κ) :
    ∃ D : ℝ, 1 ≤ D ∧ (LinearIndepOn F l (t : Set κ) → #t = Fintype.card ι →
      ∀ (y : ι → F) (j : ι) (M : ℝ), (∀ k ∈ t, w (l k y) ≤ M) → w (y j) ≤ D * M) := by
  by_cases ht : LinearIndepOn F l (t : Set κ) ∧ #t = Fintype.card ι
  swap
  · exact ⟨1, le_rfl, fun h₁ h₂ ↦ (ht ⟨h₁, h₂⟩).elim⟩
  let e : ι ≃ t := Fintype.equivOfCardEq (by rw [Fintype.card_coe, ht.2])
  obtain ⟨D, hD1, hD⟩ := w.exists_one_le_forall_apply_le_mul (l := fun i ↦ l (e i))
    ((ht.1.comp e e.injective).span_eq_top_of_card_eq_finrank'
      (by simp [Subspace.dual_finrank_eq]))
  exact ⟨D, hD1, fun _ _ y j M hM ↦
    hD ((apply_nonneg _ _).trans (hM _ (e j).property)) (fun i ↦ hM _ (e i).property) j⟩

/-- Completing forms `l k`, `k ∈ t`, by coordinate forms does not increase the local factor at an
absolute value `w` lying over `v`: the factor of a coordinate form is at most `1`. -/
private theorem prod_sumElim_proj_le (v : AbsoluteValue K ℝ) (w : AbsoluteValue F ℝ)
    [w.LiesOver v] (l : κ → Dual F (ι → F)) {t : Finset κ} {u : Finset ι} (e : ι ≃ t ⊕ u)
    (x : ι → K) :
    ∏ i, w ((Sum.elim (fun k : t ↦ l k) fun j : u ↦ (LinearMap.proj (j : ι) : Dual F (ι → F)))
        (e i) fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤
      ∏ k ∈ t, w (l k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  set y : ι → F := fun j ↦ algebraMap K F (x j)
  set S : ℝ := ⨆ j, v (x j)
  have hS : 0 ≤ S := Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
  have hyS (j : ι) : w (y j) ≤ S := by
    rw [LiesOver.apply_algebraMap v]
    exact le_ciSup (Finite.bddAbove_range fun j ↦ v (x j)) j
  rw [e.prod_comp fun a ↦ w (Sum.elim (fun k : t ↦ l k)
    (fun j : u ↦ (LinearMap.proj (j : ι) : Dual F (ι → F))) a y) / S, Fintype.prod_sum_type,
    ← prod_coe_sort t]
  simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.proj_apply]
  refine mul_le_of_le_one_right (prod_nonneg fun _ _ ↦ div_nonneg (apply_nonneg _ _) hS) ?_
  exact prod_le_one₀ (fun _ _ ↦ div_nonneg (apply_nonneg _ _) hS)
    fun j _ ↦ div_le_one_of_le₀ (hyS j) hS

/-- **One place.** At an absolute value `w` lying over `v`, let the forms `l k`, `k ∈ B`, be in
general position. There is `C ≥ 1` such that every nonzero point `x` has a system `l'` of
`card ι` linearly independent forms, each a form `l k` with `k ∈ B` or a coordinate form, whose
local factor at `x` is at most `C` times the local factor of the forms `l k`, `k ∈ B`. -/
private theorem exists_forall_exists_prod_le_mul_prod (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] {l : κ → Dual F (ι → F)} {B : Finset κ}
    (hl : IsGeneralPosition fun k : B ↦ l k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ι → K, x ≠ 0 → ∃ l' : ι → Dual F (ι → F),
      LinearIndependent F l' ∧
      (∀ i, l' i ∈ l '' B ∪ Set.range fun j : ι ↦ (LinearMap.proj j : Dual F (ι → F))) ∧
      ∏ i, w (l' i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤
        C * ∏ k ∈ B, w (l k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  classical
  rw [isGeneralPosition_subtype_iff] at hl
  choose D hD1 hD using exists_one_le_forall_apply_le_mul w l
  set C : ℝ := 1 + ∑ t ∈ B.powerset, D t
  have hDC (t : Finset κ) (ht : t ⊆ B) : D t ≤ C :=
    (single_le_sum (fun t _ ↦ zero_le_one.trans (hD1 t)) (mem_powerset.mpr ht)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hC1 : 1 ≤ C := le_add_of_nonneg_right (sum_nonneg fun t _ ↦ zero_le_one.trans (hD1 t))
  refine ⟨C ^ #B, one_le_pow₀ hC1, fun x hx ↦ ?_⟩
  set y : ι → F := fun j ↦ algebraMap K F (x j)
  set S : ℝ := ⨆ j, v (x j)
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨j₀⟩
  have hS : 0 < S :=
    (v.pos hj₀).trans_le (le_ciSup (Finite.bddAbove_range fun j ↦ v (x j)) j₀)
  -- Keep the `min (card ι) #B` forms of smallest value and complete them by coordinate forms.
  obtain ⟨t, htB, htcard, hmin⟩ :=
    B.exists_subset_card_eq_forall_le (fun k ↦ w (l k y)) (min_le_right (Fintype.card ι) #B)
  obtain ⟨u, hli, hcard⟩ :=
    LinearIndependent.exists_linearIndependent_sumElim_proj
      (hl t htB (htcard.trans_le (min_le_left _ _)))
  let e : ι ≃ t ⊕ u :=
    Fintype.equivOfCardEq (by rw [Fintype.card_sum, Fintype.card_coe u]; exact hcard.symm)
  let g : t ⊕ u → Dual F (ι → F) :=
    Sum.elim (fun k : t ↦ l k) fun j : u ↦ (LinearMap.proj (j : ι) : Dual F (ι → F))
  refine ⟨g ∘ e, hli.comp e e.injective, fun i ↦ ?_, ?_⟩
  · rw [Function.comp_apply]
    rcases e i with k | j
    · exact Or.inl ⟨k, htB k.property, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
  -- Every discarded form has value at least the sup norm over `C`.
  have hdisc : ∀ k ∈ B \ t, 1 ≤ C * (w (l k y) / S) := by
    intro k hk
    rw [mem_sdiff] at hk
    have htn : #t = Fintype.card ι := by
      by_contra hne
      have htB' : t = B := eq_of_subset_of_card_le htB (by omega)
      exact hk.2 (htB' ▸ hk.1)
    have hSk : S ≤ D t * w (l k y) := ciSup_le fun j ↦ by
      rw [← LiesOver.apply_algebraMap (w := w) v]
      exact hD t (hl t htB htn.le) htn y j _ fun k' hk' ↦ hmin k' hk' k hk.1 hk.2
    rw [← mul_div_assoc, one_le_div hS]
    exact hSk.trans (mul_le_mul_of_nonneg_right (hDC t htB) (apply_nonneg _ _))
  have hf : ∀ k ∈ B, 0 ≤ w (l k y) / S := fun _ _ ↦ div_nonneg (apply_nonneg _ _) hS.le
  refine (prod_sumElim_proj_le v w l e x).trans <|
    (prod_le_pow_card_sdiff_mul_prod htB (fun k hk ↦ hf k (htB hk)) hdisc).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 (card_le_card sdiff_subset))
    (prod_nonneg hf)

end Local

variable [NumberField K]

/-- The **general approximation product** of a point `x : ι → K` with respect to linear forms
`L v k`, `k ∈ B v`, with coefficients in `F`, at the places of `K` in `Sinf` and `Sfin`, each
measured by an absolute value `w v` of `F`: the product over `v ∈ Sinf` of
`(∏ k ∈ B v, w v (L v k x) / ⨆ j, v (x j)) ^ mult v`, times the product over `v ∈ Sfin` of
`∏ k ∈ B v, w v (L v k x) / ⨆ j, v (x j)`, where `x` is mapped into `F`.

The forms at all places are indexed by one type `κ`, and the finset `B v` selects those at `v`.
The data `w`, `B` and `L` are indexed by the underlying absolute value of a place, and their values
off `Sinf ∪ Sfin` play no role. -/
noncomputable def generalProd (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v ∈ Sinf, (∏ k ∈ B v.val, w v.val (L v.val k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^
      v.mult) *
    ∏ v ∈ Sfin, ∏ k ∈ B v.val, w v.val (L v.val k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)

theorem generalProd_def (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (x : ι → K) :
    generalProd Sinf Sfin w B L x =
      (∏ v ∈ Sinf,
          (∏ k ∈ B v.val, w v.val (L v.val k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^
            v.mult) *
        ∏ v ∈ Sfin,
          ∏ k ∈ B v.val, w v.val (L v.val k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  rw [generalProd]

/-- With all `card ι` forms at every place, the general approximation product is the approximation
product. -/
theorem generalProd_univ_eq_approxProd [Fintype ι] (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) :
    generalProd Sinf Sfin w (fun _ ↦ univ) L x = approxProd Sinf Sfin w L x := by
  rw [generalProd_def, approxProd_def]

variable {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
  {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {B : AbsoluteValue K ℝ → Finset κ}
  {L : AbsoluteValue K ℝ → κ → Dual F (ι → F)}

/-- The general approximation product is nonnegative. -/
theorem generalProd_nonneg (x : ι → K) : 0 ≤ generalProd Sinf Sfin w B L x := by
  have h (v : AbsoluteValue K ℝ) :
      0 ≤ ∏ k ∈ B v, w v (L v k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) :=
    prod_nonneg fun _ _ ↦ div_nonneg (apply_nonneg _ _) (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
  simp only [generalProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  exact mul_nonneg (prod_nonneg fun v _ ↦ pow_nonneg (h v.val) _) (prod_nonneg fun v _ ↦ h v.val)

/-- The general approximation product is invariant under scaling the point by a nonzero element of
`K`, provided that each absolute value `w v` lies over `v`. -/
theorem generalProd_smul (hwInf : ∀ v ∈ Sinf, (w v.val).LiesOver v.val)
    (hwFin : ∀ v ∈ Sfin, (w v.val).LiesOver v.val) {c : K} (hc : c ≠ 0) (x : ι → K) :
    generalProd Sinf Sfin w B L (c • x) = generalProd Sinf Sfin w B L x := by
  simp only [generalProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  congr 1
  · refine prod_congr rfl fun v hv ↦ ?_
    have := hwInf v hv
    simp only [apply_div_iSup_smul _ hc]
  · refine prod_congr rfl fun v hv ↦ ?_
    have := hwFin v hv
    simp only [apply_div_iSup_smul _ hc]

/-- Products of local factors over `Sinf` (with the exponents `mult v`) and `Sfin` are compared
place by place: local bounds `0 ≤ a v ≤ C v * b v` multiply. -/
private theorem prod_pow_mul_prod_le_mul {a b C : AbsoluteValue K ℝ → ℝ}
    (hInf : ∀ v ∈ Sinf, 0 ≤ a v.val ∧ a v.val ≤ C v.val * b v.val)
    (hFin : ∀ v ∈ Sfin, 0 ≤ a v.val ∧ a v.val ≤ C v.val * b v.val) :
    (∏ v ∈ Sinf, a v.val ^ v.mult) * ∏ v ∈ Sfin, a v.val ≤
      ((∏ v ∈ Sinf, C v.val ^ v.mult) * ∏ v ∈ Sfin, C v.val) *
        ((∏ v ∈ Sinf, b v.val ^ v.mult) * ∏ v ∈ Sfin, b v.val) := by
  calc (∏ v ∈ Sinf, a v.val ^ v.mult) * ∏ v ∈ Sfin, a v.val
      ≤ (∏ v ∈ Sinf, (C v.val * b v.val) ^ v.mult) * ∏ v ∈ Sfin, C v.val * b v.val := by
        refine mul_le_mul (prod_le_prod₀ (fun v hv ↦ pow_nonneg (hInf v hv).1 _)
          fun v hv ↦ pow_le_pow_left₀ (hInf v hv).1 (hInf v hv).2 _)
          (prod_le_prod₀ (fun v hv ↦ (hFin v hv).1) fun v hv ↦ (hFin v hv).2)
          (prod_nonneg fun v hv ↦ (hFin v hv).1) ?_
        exact prod_nonneg fun v hv ↦ pow_nonneg ((hInf v hv).1.trans (hInf v hv).2) _
    _ = ((∏ v ∈ Sinf, C v.val ^ v.mult) * ∏ v ∈ Sfin, C v.val) *
          ((∏ v ∈ Sinf, b v.val ^ v.mult) * ∏ v ∈ Sfin, b v.val) := by
        simp only [mul_pow, prod_mul_distrib]
        ring

omit [NumberField K] in
/-- The construction of `exists_forall_exists_prod_le_mul_prod` at every place of a finite set
`P` of absolute values, chosen as functions of the place and of the point. -/
private theorem exists_forall_exists_prod_le_mul_prod_of_mem [Fintype ι]
    (P : Finset (AbsoluteValue K ℝ))
    (hP : ∀ v ∈ P, (w v).LiesOver v ∧ IsGeneralPosition fun k : B v ↦ L v k) :
    ∃ (C : AbsoluteValue K ℝ → ℝ) (l' : AbsoluteValue K ℝ → (ι → K) → ι → Dual F (ι → F)),
      (∀ v, 1 ≤ C v) ∧ ∀ v ∈ P, ∀ x : ι → K, x ≠ 0 → LinearIndependent F (l' v x) ∧
        (∀ i, l' v x i ∈ L v '' B v ∪ Set.range fun j : ι ↦ (LinearMap.proj j : Dual F (ι → F))) ∧
        ∏ i, w v (l' v x i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤
          C v * ∏ k ∈ B v, w v (L v k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  classical
  have hloc (v : AbsoluteValue K ℝ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ι → K, ∃ l' : ι → Dual F (ι → F),
      v ∈ P → x ≠ 0 → LinearIndependent F l' ∧
        (∀ i, l' i ∈ L v '' B v ∪ Set.range fun j : ι ↦ (LinearMap.proj j : Dual F (ι → F))) ∧
        ∏ i, w v (l' i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤
          C * ∏ k ∈ B v, w v (L v k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
    by_cases hv : v ∈ P
    · have := (hP v hv).1
      obtain ⟨C, hC1, hC⟩ := exists_forall_exists_prod_le_mul_prod v (w v) (hP v hv).2
      refine ⟨C, hC1, fun x ↦ ?_⟩
      by_cases hx : x = 0
      · exact ⟨0, fun _ h ↦ (h hx).elim⟩
      exact (hC x hx).imp fun _ h _ _ ↦ h
    · exact ⟨1, le_rfl, fun _ ↦ ⟨0, fun h ↦ (hv h).elim⟩⟩
  choose C hC1 l' hl' using hloc
  exact ⟨C, l', hC1, fun v hv x hx ↦ hl' v x hv hx⟩

/-- **Reduction of forms in general position to bases.** Let the forms `L v k`, `k ∈ B v`, be in
general position at every place of `Sinf` and `Sfin`, each measured by an absolute value `w v`
lying over `v`. There are finitely many systems `L'` of forms, each linearly independent at every
place of `Sinf` and `Sfin`, and a constant `C > 0` such that every nonzero point `x` satisfies
`approxProd Sinf Sfin w L' x ≤ C * generalProd Sinf Sfin w B L x` for one of them.

The statement does not say which forms the systems consist of. The proof builds them at each place
from forms `L v k`, `k ∈ B v`, completed by coordinate forms when `B v` has fewer than `card ι`
members. -/
theorem exists_finset_forall_approxProd_le_mul_generalProd [Fintype ι]
    (hwInf : ∀ v ∈ Sinf, (w v.val).LiesOver v.val) (hwFin : ∀ v ∈ Sfin, (w v.val).LiesOver v.val)
    (hLInf : ∀ v ∈ Sinf, IsGeneralPosition fun k : B v.val ↦ L v.val k)
    (hLFin : ∀ v ∈ Sfin, IsGeneralPosition fun k : B v.val ↦ L v.val k) :
    ∃ (T : Finset (AbsoluteValue K ℝ → ι → Dual F (ι → F))) (C : ℝ), 0 < C ∧
      (∀ L' ∈ T, (∀ v ∈ Sinf, LinearIndependent F (L' v.val)) ∧
        ∀ v ∈ Sfin, LinearIndependent F (L' v.val)) ∧
      ∀ x : ι → K, x ≠ 0 → ∃ L' ∈ T,
        approxProd Sinf Sfin w L' x ≤ C * generalProd Sinf Sfin w B L x := by
  classical
  set P : Finset (AbsoluteValue K ℝ) := Sinf.image (·.val) ∪ Sfin.image (·.val)
  have hinfP (v : InfinitePlace K) (hv : v ∈ Sinf) : v.val ∈ P :=
    mem_union_left _ (mem_image_of_mem _ hv)
  have hfinP (v : FinitePlace K) (hv : v ∈ Sfin) : v.val ∈ P :=
    mem_union_right _ (mem_image_of_mem _ hv)
  have hP (v : AbsoluteValue K ℝ) (hv : v ∈ P) :
      (w v).LiesOver v ∧ IsGeneralPosition fun k : B v ↦ L v k := by
    rcases mem_union.mp hv with h | h <;> obtain ⟨u, hu, rfl⟩ := mem_image.mp h
    exacts [⟨hwInf u hu, hLInf u hu⟩, ⟨hwFin u hu, hLFin u hu⟩]
  obtain ⟨C, l', hC1, hl'⟩ := exists_forall_exists_prod_le_mul_prod_of_mem P hP
  -- A system is a choice, at each place of `P`, of `card ι` forms among the given forms at the
  -- places of `P` and the coordinate forms; there are finitely many.
  set Fs : Finset (Dual F (ι → F)) :=
    P.biUnion (fun v ↦ (B v).image (L v)) ∪ univ.image fun j ↦ LinearMap.proj j
  have hFs (v : AbsoluteValue K ℝ) (hv : v ∈ P) (f : Dual F (ι → F))
      (hf : f ∈ L v '' B v ∪ Set.range fun j : ι ↦ (LinearMap.proj j : Dual F (ι → F))) :
      f ∈ Fs := by
    rcases hf with ⟨k, hk, rfl⟩ | ⟨j, rfl⟩
    · exact mem_union_left _ (mem_biUnion.mpr ⟨v, hv, mem_image_of_mem _ hk⟩)
    · exact mem_union_right _ (mem_image_of_mem _ (mem_univ j))
  let encode : (P → ι → Fs) → AbsoluteValue K ℝ → ι → Dual F (ι → F) := fun φ v ↦
    if h : v ∈ P then fun i ↦ φ ⟨v, h⟩ i else fun i ↦ LinearMap.proj i
  refine ⟨(univ.image encode).filter fun L' ↦ (∀ v ∈ Sinf, LinearIndependent F (L' v.val)) ∧
      ∀ v ∈ Sfin, LinearIndependent F (L' v.val),
    (∏ v ∈ Sinf, C v.val ^ v.mult) * ∏ v ∈ Sfin, C v.val,
    mul_pos (prod_pos fun v _ ↦ pow_pos (one_pos.trans_le (hC1 _)) _)
      (prod_pos fun v _ ↦ one_pos.trans_le (hC1 _)),
    fun L' hL' ↦ (mem_filter.mp hL').2, fun x hx ↦ ?_⟩
  let φ : P → ι → Fs := fun v i ↦ ⟨l' v x i, hFs v v.property _ ((hl' v v.property x hx).2.1 i)⟩
  have hφ (v : AbsoluteValue K ℝ) (hv : v ∈ P) : encode φ v = l' v x := by
    simp only [encode, φ, hv, ↓reduceDIte]
  refine ⟨encode φ, mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _), fun v hv ↦ ?_,
    fun v hv ↦ ?_⟩, ?_⟩
  · exact hφ _ (hinfP v hv) ▸ (hl' _ (hinfP v hv) x hx).1
  · exact hφ _ (hfinP v hv) ▸ (hl' _ (hfinP v hv) x hx).1
  rw [approxProd_congr (L' := fun v ↦ l' v x) (fun v hv ↦ hφ _ (hinfP v hv))
    (fun v hv ↦ hφ _ (hfinP v hv))]
  simp only [approxProd_def, generalProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  exact prod_pow_mul_prod_le_mul (C := C)
    (a := fun v ↦ ∏ i, w v (l' v x i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
    (b := fun v ↦ ∏ k ∈ B v, w v (L v k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
    (fun v hv ↦ ⟨prod_div_iSup_nonneg _ _ _ x, (hl' _ (hinfP v hv) x hx).2.2⟩)
    (fun v hv ↦ ⟨prod_div_iSup_nonneg _ _ _ x, (hl' _ (hfinP v hv) x hx).2.2⟩)

end NumberField
