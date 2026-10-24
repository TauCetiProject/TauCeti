/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import TauCeti.KnotTheory.Khovanov.EnhancedState
public import TauCeti.KnotTheory.Khovanov.QuantumGrading
public import TauCeti.RingTheory.PiTensorProduct.FiberwiseMul

/-!
# Circle tensors and merge maps

A resolution of a link diagram is a finite set `ι` of circles, and Khovanov's chain group of that
resolution is the tensor product `⨂_{i : ι} V` of one copy of the rank-two Frobenius algebra
`V = R[ε]` per circle (with `X = ε`). This file constructs that circle tensor
`TauCeti.Khovanov.CircleTensor R ι`, its basis indexed by the labellings `ι → Bool` of the circles
by `1` (`false`) and `X` (`true`), and its quantum grading, in which a labelling has degree
`#{1-labels} - #{X-labels}`.

For a state `s` of a PD-code `D`, the labellings `D.ResolvedCircle s → Bool` are exactly the
enhanced states over `s` (`TauCeti.PDCode.EnhancedState`), and the quantum degree of an enhanced
state is the quantum shift of its state plus the degree of its labelling
(`TauCeti.OrientedPDCode.enhancedQuantumDegree_def`). So the basis
`TauCeti.Khovanov.circleBasis` identifies the circle tensor of a resolution with the free module on
the enhanced states over it, its `Finsupp` model.

A map `f : σ → τ` of circle sets acts by `PiTensorProduct.fiberwiseMul`, which multiplies the labels
on each fibre of `f` and puts `1` on the circles of `τ` outside the range of `f`. When `f` merges
two circles and is a bijection on the others, this is the merge map of the Khovanov differential:
multiplication `m` on the two merged factors and the identity on the rest. Empty fibres give the
unit `η`, as for a circle born from nothing. The map depends only on `f`, so it is independent of
any ordering of the circles or parenthesization of the tensor product, and it is functorial in `f`
(`PiTensorProduct.fiberwiseMul_comp`).

## Main definitions

* `TauCeti.Khovanov.labelBasis`: the basis `1, ε` of `R[ε]` indexed by the labels `false, true`.
* `TauCeti.Khovanov.CircleTensor`: the tensor product of one copy of `R[ε]` per circle.
* `TauCeti.Khovanov.circleBasis`: its basis indexed by labellings.
* `TauCeti.Khovanov.circleQuantumGrading`: the quantum grading of the circle tensor.

## Main results

* `TauCeti.Khovanov.tprod_mem_circleQuantumGrading_piece`: a tensor of homogeneous elements of
  `R[ε]` is homogeneous of the total degree.
* `TauCeti.Khovanov.fiberwiseMul_circleBasis`: the merge map along `f` sends a labelling to the
  labelling marking `X` on each circle whose fibre carries one `X`, and to `0` when some fibre
  carries two `X`s.
* `TauCeti.Khovanov.isHomogeneous_fiberwiseMul`: the merge map along `f : σ → τ` has quantum
  degree `|τ| - |σ|`; in particular merging two circles into one has degree `-1`.
* `TauCeti.Khovanov.isHomogeneous_reindex`: relabelling the circle factors preserves quantum
  degree.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §1.
-/

public section

open DualNumber TrivSqZeroExt PiTensorProduct Finset
open scoped TensorProduct

namespace TauCeti

namespace Khovanov

universe u

section Basis

variable (R : Type u) [CommSemiring R]

/-- The basis `1, ε` of the dual numbers `R[ε]` indexed by the labels of a circle: `false` stands
for the generator `1` and `true` for the generator `X = ε`. It is `TauCeti.dualNumberBasis`
reindexed along `finTwoEquiv`. -/
noncomputable def labelBasis : Module.Basis Bool R R[ε] :=
  (dualNumberBasis R).reindex finTwoEquiv

/-- The label `false` is the generator `1`. -/
@[simp]
theorem labelBasis_false : labelBasis R false = 1 := by
  -- `finTwoEquiv` sends `b` back to `bif b then 1 else 0`.
  simp [labelBasis, show finTwoEquiv.symm false = 0 from rfl]

/-- The label `true` is the generator `X = ε`. -/
@[simp]
theorem labelBasis_true : labelBasis R true = ε := by
  -- `finTwoEquiv` sends `b` back to `bif b then 1 else 0`.
  simp [labelBasis, show finTwoEquiv.symm true = 1 from rfl]

variable {R}

/-- The coordinate of a dual number along the label `false` is its scalar part. -/
@[simp]
theorem labelBasis_repr_false (x : R[ε]) : (labelBasis R).repr x false = x.fst := by
  -- `finTwoEquiv` sends `b` back to `bif b then 1 else 0`.
  simp [labelBasis, show finTwoEquiv.symm false = 0 from rfl]

/-- The coordinate of a dual number along the label `true` is its `ε`-part. -/
@[simp]
theorem labelBasis_repr_true (x : R[ε]) : (labelBasis R).repr x true = x.snd := by
  -- `finTwoEquiv` sends `b` back to `bif b then 1 else 0`.
  simp [labelBasis, show finTwoEquiv.symm true = 1 from rfl]

/-- A product of labels is `ε` raised to the number of `X`-labels. -/
theorem prod_labelBasis {ι : Type*} (s : Finset ι) (l : ι → Bool) :
    ∏ i ∈ s, labelBasis R (l i) = ε ^ #{i ∈ s | l i = true} := by
  rw [Finset.card_filter, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ ↦ by cases l i <;> simp

variable (R) (ι : Type*)

/-- The **circle tensor** of a finite set `ι` of circles: the tensor product of one copy of the
Khovanov Frobenius algebra `R[ε]` for each circle. It is a commutative `R`-algebra. -/
abbrev CircleTensor : Type _ :=
  ⨂[R] _ : ι, R[ε]

/-- The basis of the circle tensor indexed by the labellings `ι → Bool` of the circles by `1`
(`false`) and `X` (`true`): the labelling `l` gives the pure tensor `⨂ₜ i, labelBasis R (l i)`. -/
noncomputable def circleBasis [Finite ι] : Module.Basis (ι → Bool) R (CircleTensor R ι) :=
  Basis.piTensorProduct fun _ ↦ labelBasis R

variable {R ι}

/-- The basis vector of a labelling is the pure tensor of the labels. -/
@[simp]
theorem circleBasis_apply [Finite ι] (l : ι → Bool) :
    circleBasis R ι l = ⨂ₜ[R] i, labelBasis R (l i) :=
  Basis.piTensorProduct_apply _ l

/-- The coordinate of a pure tensor along a labelling is the product of the coordinates of its
factors along the labels. -/
@[simp]
theorem circleBasis_repr_tprod [Fintype ι] (x : ι → R[ε]) (l : ι → Bool) :
    (circleBasis R ι).repr (tprod R x) l = ∏ i, (labelBasis R).repr (x i) (l i) :=
  Basis.piTensorProduct_repr_tprod_apply _ x l

/-- Reindexing circle factors transports their labellings along the inverse bijection. -/
@[simp↓]
theorem reindex_circleBasis {σ τ : Type*} [Finite σ] [Finite τ] (e : σ ≃ τ)
    (l : σ → Bool) :
    reindex R (fun _ ↦ R[ε]) e (circleBasis R σ l) =
      circleBasis R τ (l ∘ e.symm) := by
  simp only [circleBasis_apply, reindex_tprod, Function.comp_apply]

section Merge

variable {σ τ : Type*} [Fintype σ] [DecidableEq τ]

/-- The merge map along `f` sends the basis vector of a labelling `l` to the pure tensor carrying,
on each circle `j`, the power of `ε` counting the `X`-labels of `l` on the fibre of `j`. -/
theorem fiberwiseMul_circleBasis_eq_tprod [Finite τ] (f : σ → τ) (l : σ → Bool) :
    fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f (circleBasis R σ l) =
      ⨂ₜ[R] j, (ε : R[ε]) ^ #{i | f i = j ∧ l i = true} := by
  rw [circleBasis_apply, fiberwiseMul_tprod_eq_tprod_prod]
  congr 1
  funext j
  rw [prod_labelBasis, Finset.filter_filter]

/-- **The merge map on the labelling basis.** Along `f`, the basis vector of a labelling `l` goes to
`0` if some fibre of `f` carries two `X`-labels. Otherwise it goes to the basis vector of the
labelling that marks `X` exactly on the circles whose fibre carries an `X`-label. -/
theorem fiberwiseMul_circleBasis [Fintype τ] (f : σ → τ) (l : σ → Bool) :
    fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f (circleBasis R σ l) =
      if ∀ j, #{i | f i = j ∧ l i = true} ≤ 1 then
        circleBasis R τ fun j ↦ decide (∃ i, f i = j ∧ l i = true)
      else 0 := by
  rw [fiberwiseMul_circleBasis_eq_tprod]
  split_ifs with h
  · rw [circleBasis_apply]
    congr 1
    funext j
    by_cases hj : ∃ i, f i = j ∧ l i = true
    · obtain ⟨i, hi⟩ := hj
      have hpos : 0 < #{i | f i = j ∧ l i = true} := Finset.card_pos.mpr ⟨i, by simpa using hi⟩
      have hcard : #{i | f i = j ∧ l i = true} = 1 := by have := h j; omega
      rw [hcard, decide_eq_true ⟨i, hi⟩]
      simp
    · rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun i _ hi ↦ hj ⟨i, hi⟩),
        decide_eq_false hj]
      simp
  · obtain ⟨j, hj⟩ := not_forall.mp h
    exact MultilinearMap.map_coord_zero _ j (pow_eq_zero_of_le (by omega) eps_pow_two)

end Merge

end Basis

section Grading

variable (R : Type u) [CommRing R] (ι : Type*) [Fintype ι]

/-- The **quantum grading** of the circle tensor: the basis vector of a labelling `l` spans its
degree `TauCeti.Khovanov.labelingQuantumDegree ι l`. It is the grading of the free module on the
labellings, transported along `TauCeti.Khovanov.circleBasis`. -/
noncomputable def circleQuantumGrading : InternalGrading R (CircleTensor R ι) :=
  (InternalGrading.finsupp R (labelingQuantumDegree ι)).map (circleBasis R ι).repr.symm

variable {R ι}

/-- An element of the circle tensor has quantum degree `p` exactly when its coordinates along the
labellings of other degrees vanish. -/
theorem mem_circleQuantumGrading_piece_iff {p : ℤ} {x : CircleTensor R ι} :
    x ∈ (circleQuantumGrading R ι).piece p ↔
      ∀ l, (circleBasis R ι).repr x l ≠ 0 → labelingQuantumDegree ι l = p := by
  rw [circleQuantumGrading, InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
    InternalGrading.mem_finsupp_piece_iff]

/-- The basis vector of a labelling is homogeneous of the degree of the labelling. -/
theorem circleBasis_mem_circleQuantumGrading_piece (l : ι → Bool) :
    circleBasis R ι l ∈ (circleQuantumGrading R ι).piece (labelingQuantumDegree ι l) := by
  rw [← Module.Basis.repr_symm_single_one, circleQuantumGrading,
    InternalGrading.apply_mem_map_piece_iff]
  exact InternalGrading.single_mem_finsupp_piece _ _

/-- The pure tensor of the labels of a labelling is homogeneous of the degree of the labelling.
This is the simp-normal form of `TauCeti.Khovanov.circleBasis_mem_circleQuantumGrading_piece`. -/
@[simp]
theorem tprod_labelBasis_mem_circleQuantumGrading_piece (l : ι → Bool) :
    (⨂ₜ[R] i, labelBasis R (l i)) ∈ (circleQuantumGrading R ι).piece (labelingQuantumDegree ι l) :=
  circleBasis_apply (R := R) l ▸ circleBasis_mem_circleQuantumGrading_piece l

/-- **A tensor of homogeneous elements is homogeneous**: if each factor `x i` of `R[ε]` has quantum
degree `d i`, then `⨂ₜ x` has quantum degree `∑ i, d i`. -/
theorem tprod_mem_circleQuantumGrading_piece {d : ι → ℤ} {x : ι → R[ε]}
    (hx : ∀ i, x i ∈ (quantumGrading R).piece (d i)) :
    tprod R x ∈ (circleQuantumGrading R ι).piece (∑ i, d i) := by
  rw [mem_circleQuantumGrading_piece_iff]
  intro l hl
  rw [circleBasis_repr_tprod] at hl
  rw [labelingQuantumDegree_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := mem_quantumGrading_piece_iff.mp (hx i)
  have hli : (labelBasis R).repr (x i) (l i) ≠ 0 := fun h ↦ hl (Finset.prod_eq_zero (mem_univ i) h)
  cases h : l i <;> rw [h] at hli <;> simp_all

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

/-- **The merge map along `f : σ → τ` has quantum degree `|τ| - |σ|`.** Merging two circles into
one has degree `-1`, and the birth of a circle (a point of `τ` outside the range of `f`) has
degree `+1`. -/
theorem isHomogeneous_fiberwiseMul (f : σ → τ) :
    TauCeti.LinearMap.IsHomogeneous (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f).toLinearMap
      (circleQuantumGrading R σ).piece (circleQuantumGrading R τ).piece
      (Fintype.card τ - Fintype.card σ) := by
  classical
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rw [mem_circleQuantumGrading_piece_iff] at hx
  rw [← (circleBasis R σ).sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun l _ ↦ ?_
  rw [map_smul]
  by_cases hl : (circleBasis R σ).repr x l = 0
  · rw [hl, zero_smul]
    exact zero_mem _
  refine Submodule.smul_mem _ _ ?_
  rw [AlgHom.toLinearMap_apply, fiberwiseMul_circleBasis]
  split_ifs with h
  · rw [← hx l hl, ← labelingQuantumDegree_merge h]
    exact circleBasis_mem_circleQuantumGrading_piece _
  · exact zero_mem _

omit [DecidableEq τ] in
/-- Reindexing the circle factors preserves their total quantum degree. -/
theorem isHomogeneous_reindex (e : σ ≃ τ) :
    TauCeti.LinearMap.IsHomogeneous (reindex R (fun _ ↦ R[ε]) e).toLinearMap
      (circleQuantumGrading R σ).piece (circleQuantumGrading R τ).piece 0 := by
  classical
  simpa only [toLinearMap_fiberwiseMul_equiv, Fintype.card_congr e, sub_self] using
    (isHomogeneous_fiberwiseMul (R := R) e)

end Grading

end Khovanov

end TauCeti
