/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Order.Fin.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Plucker

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Exterior powers of a system of linear forms

For `p` linear forms `l 0, …, l (p - 1)` on `R^ι`, the wedge `l 0 ∧ ⋯ ∧ l (p - 1)` is a linear form
on `⋀^p R^ι`. Here the exterior power is read in Plücker coordinates, as the space
`Set.powersetCard ι p → R` of `TauCeti.plucker`, so the wedge is the linear form whose coefficient
at a `p`-subset `s` is the Plücker coordinate at `s` of the rows of coefficients of the `l a`. On
the Plücker vector of `p` vectors it is the determinant of the matrix of values,
**Laplace's identity**, which is the Cauchy–Binet formula
`TauCeti.det_mul_transpose_eq_sum_plucker_mul`.

A family of forms indexed by a linearly ordered type `κ` gives a family of wedges indexed by the
`p`-subsets of `κ`. Biorthogonality passes to the wedges: if `l i (y j) = δ i j`, then the wedge of
the forms indexed by `T` takes the value `δ T T'` on the Plücker vector of the vectors indexed by
`T'`. Over a field this shows that the wedges of linearly independent forms are linearly
independent, and so are the Plücker vectors of the `p`-subfamilies of a linearly independent
family of vectors.

For a basis `x 0, …, x (N - 1)` of `K^ι` and `k + p = N`, the span `TauCeti.wedgeSpan k p x` of the
Plücker vectors of the `p`-subfamilies of `x` that meet the first `k` indices depends only on the
span of `x 0, …, x (k - 1)`, and determines it. It is the kernel of the wedge of the last `p`
coordinate forms of the basis, a hyperplane that misses the Plücker vector of the top block
`x k, …, x (N - 1)`.

These are the exterior powers of a system of forms on which Schmidt's Subspace Theorem runs its
argument in `⋀^p`: an approximation domain of the forms `l` gives one of the wedges, and the
subspace found in `⋀^p` is converted back to a subspace of `K^ι` through `wedgeSpan`.

## Main definitions

* `TauCeti.wedgeForm l`: the wedge of `p` linear forms, a linear form on Plücker coordinates.
* `TauCeti.wedgeForms l p`: the wedges of a family of forms, indexed by the `p`-subsets.
* `TauCeti.wedgeSpan k p x`: the span of the Plücker vectors of the `p`-subfamilies of `x` that
  meet the first `k` indices.
* `TauCeti.topBlock h`: for `h : k + p = N`, the top block `{k, …, N - 1}` as a `p`-subset.

## Main results

* `TauCeti.wedgeForm_plucker`: Laplace's identity
  `(l 0 ∧ ⋯ ∧ l (p - 1)) (y 0 ∧ ⋯ ∧ y (p - 1)) = det (l a (y b))`.
* `TauCeti.wedgeForms_plucker_comp_eq_ite`: biorthogonality passes to the wedges.
* `TauCeti.linearIndependent_wedgeForms` and `TauCeti.linearIndependent_plucker_comp`: the wedges
  of independent forms, and of independent vectors, are independent.
* `TauCeti.mem_span_iff_forall_plucker_mem_wedgeSpan` and `TauCeti.wedgeSpan_eq_wedgeSpan_iff`:
  the span of the wedges meeting the first `k` indices determines, and is determined by, the span
  of the first `k` vectors.
* `TauCeti.wedgeSpan_eq_ker`, `TauCeti.plucker_topBlock_notMem_wedgeSpan` and
  `TauCeti.finrank_wedgeSpan_add_one`: it is the kernel of the wedge of the last `p` coordinate
  forms, a hyperplane missing the wedge of the top block.

## Implementation notes

The exterior power is read in coordinates because the geometry of numbers downstream works with
forms on a coordinate space `κ → K`; Mathlib's pairing of `⋀[R]^p M` with `⋀[R]^p (Dual R M)`
enters only through the Cauchy–Binet formula. The determinant of the system of wedges (the
Sylvester–Franke theorem) is not needed: independence comes from a biorthogonal family. The
description of `wedgeSpan` uses no pairing between `⋀^p` and `⋀^k` either: if a coordinate form
`f j₀` with `j₀ ≥ k` does not vanish on `u`, putting `u` in place of `x j₀` in the top block gives
a wedge on which the kernel form takes the value `f j₀ u`, by Cramer's rule.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.2, (7.16), 7.5.30 and Lemma 7.5.33.

The definitions, statements and proofs follow Ralf Stephan's
`DiophantineApproximation/WedgeForm.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/09835cb23557ae5ae0cf55a9c4ab9055f5d60338/DiophantineApproximation/WedgeForm.lean),
commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0), restated for Tau Ceti's
`TauCeti.plucker`, over a commutative ring where the argument allows and for forms and vectors
indexed by an arbitrary linearly ordered type.
-/

public section

open Module Set Set.powersetCard

namespace TauCeti

variable {R : Type*} [CommRing R] {ι κ : Type*} [LinearOrder ι] [LinearOrder κ] {p : ℕ}

/-! ### The wedge of `p` forms -/

section Fintype

variable [Fintype ι]

/-- **The wedge of `p` linear forms** `l 0 ∧ ⋯ ∧ l (p - 1)`, as a linear form on the Plücker
coordinates `powersetCard ι p → R`: its coefficient at a `p`-subset `s` is the Plücker coordinate
at `s` of the rows of coefficients `l a (Pi.single j 1)` of the forms. -/
noncomputable def wedgeForm (l : Fin p → Dual R (ι → R)) : Dual R (powersetCard ι p → R) :=
  ∑ s, plucker (fun a j ↦ l a (Pi.single j 1)) s • LinearMap.proj s

/-- The wedge of `p` forms evaluated on a vector of Plücker coordinates. -/
theorem wedgeForm_apply (l : Fin p → Dual R (ι → R)) (z : powersetCard ι p → R) :
    wedgeForm l z = ∑ s, plucker (fun a j ↦ l a (Pi.single j 1)) s * z s := by
  simp [wedgeForm]

/-- **Laplace's identity** (Bombieri–Gubler (7.16)): the wedge of `p` forms takes the value
`det (l a (y b))` on the Plücker vector of `p` vectors `y`. -/
@[simp]
theorem wedgeForm_plucker (l : Fin p → Dual R (ι → R)) (y : Fin p → ι → R) :
    wedgeForm l (plucker y) = (Matrix.of fun a b ↦ l a (y b)).det := by
  rw [wedgeForm_apply, ← det_mul_transpose_eq_sum_plucker_mul]
  congr 1
  ext a b
  conv_rhs => rw [Matrix.of_apply, ← (Pi.basisFun R ι).sum_repr (y b)]
  simp [Matrix.mul_apply, mul_comm]

/-! ### The wedges of a family of forms -/

/-- **The wedges of a family of forms**: for each `p`-subset `T` of the index type `κ`, the wedge
of the forms indexed by `T`, taken in increasing order. -/
noncomputable def wedgeForms (l : κ → Dual R (ι → R)) (p : ℕ) :
    powersetCard κ p → Dual R (powersetCard ι p → R) :=
  fun T ↦ wedgeForm (l ∘ ofFinEmbEquiv.symm T)

/-- The wedge of the forms indexed by `T` is the wedge of the subfamily `l ∘ T`, with `T`
enumerated in increasing order. -/
theorem wedgeForms_apply (l : κ → Dual R (ι → R)) (p : ℕ) (T : powersetCard κ p) :
    wedgeForms l p T = wedgeForm (l ∘ ofFinEmbEquiv.symm T) := (rfl)

/-- Laplace's identity for the wedges of a family of forms. -/
@[simp]
theorem wedgeForms_plucker (l : κ → Dual R (ι → R)) (p : ℕ) (T : powersetCard κ p)
    (y : Fin p → ι → R) :
    wedgeForms l p T (plucker y) = (Matrix.of fun a b ↦ l (ofFinEmbEquiv.symm T a) (y b)).det := by
  simp [wedgeForms_apply]

/-- **Biorthogonality passes to the wedges**: if `l i (y j) = δ i j`, then the wedge of the forms
indexed by `T` takes the value `δ T T'` on the Plücker vector of the vectors indexed by `T'`. -/
theorem wedgeForms_plucker_comp_eq_ite {l : κ → Dual R (ι → R)} {y : κ → ι → R}
    (h : ∀ i j, l i (y j) = if i = j then 1 else 0) (p : ℕ) (T T' : powersetCard κ p) :
    wedgeForms l p T (plucker (y ∘ ofFinEmbEquiv.symm T')) = if T = T' then 1 else 0 := by
  rw [wedgeForms_plucker]
  split_ifs with hT
  · subst hT
    convert Matrix.det_one (R := R) (n := Fin p)
    ext a b
    simp [h, Matrix.one_apply, (ofFinEmbEquiv.symm T).injective.eq_iff]
  · -- an index of `T` outside `T'` gives a zero row
    obtain ⟨t, htT, htT'⟩ := (exists_mem_notMem_iff_ne T T').1 hT
    obtain ⟨a, ha⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem T t).2 htT
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b ↦ ?_
    rw [Matrix.of_apply, Function.comp_apply, h, ha, ite_eq_right_iff]
    rintro rfl
    exact (htT' ((mem_range_ofFinEmbEquiv_symm_iff_mem T' _).1 ⟨b, rfl⟩)).elim

section Field

variable {K : Type*} [Field K]

/-- **The wedges of linearly independent forms are linearly independent** (Bombieri–Gubler
7.5.30). -/
theorem linearIndependent_wedgeForms {l : κ → Dual K (ι → K)} (hl : LinearIndependent K l)
    (p : ℕ) : LinearIndependent K (wedgeForms l p) := by
  obtain ⟨y, hy⟩ := hl.exists_forall_apply_eq_ite_of_dual
  refine .of_pairwise_dual_eq_zero_one _
    (fun T ↦ Dual.eval K _ (plucker (y ∘ ofFinEmbEquiv.symm T))) (fun T T' hTT' ↦ ?_) fun T ↦ ?_
  · simp [Dual.eval_apply, wedgeForms_plucker_comp_eq_ite hy, hTT'.symm]
  · simp [Dual.eval_apply, wedgeForms_plucker_comp_eq_ite hy]

end Field

end Fintype

/-- **The wedges of linearly independent vectors are linearly independent**: for a linearly
independent family `x`, the Plücker vectors of its `p`-subfamilies. -/
theorem linearIndependent_plucker_comp [Finite ι] {K : Type*} [Field K] {x : κ → ι → K}
    (hx : LinearIndependent K x) (p : ℕ) :
    LinearIndependent K fun J : powersetCard κ p ↦ plucker (x ∘ ofFinEmbEquiv.symm J) := by
  have := Fintype.ofFinite ι
  obtain ⟨f, hf⟩ := hx.exists_dual_forall_apply_eq_ite
  refine .of_pairwise_dual_eq_zero_one _ (wedgeForms f p) (fun T T' hTT' ↦ ?_) fun T ↦ ?_
  · simp [wedgeForms_plucker_comp_eq_ite hf, hTT']
  · simp [wedgeForms_plucker_comp_eq_ite hf]

/-! ### The wedges of a basis that meet the first `k` indices -/

section WedgeSpan

variable {N : ℕ}

/-- **The span of the wedges that meet the first `k` indices** (Bombieri–Gubler, Lemma 7.5.33):
for a family `x` of `N` vectors, the span of the Plücker vectors of the `p`-subfamilies `x ∘ J`
whose index set `J` contains an index below `k`. -/
noncomputable def wedgeSpan (k p : ℕ) (x : Fin N → ι → R) : Submodule R (powersetCard ι p → R) :=
  Submodule.span R ((fun J ↦ plucker (x ∘ ofFinEmbEquiv.symm J)) ''
    {J : powersetCard (Fin N) p | ∃ j ∈ J, (j : ℕ) < k})

/-- The Plücker vector of a `p`-subfamily meeting the first `k` indices lies in `wedgeSpan`. -/
theorem plucker_comp_mem_wedgeSpan {k : ℕ} (x : Fin N → ι → R) {J : powersetCard (Fin N) p}
    (hJ : ∃ j ∈ J, (j : ℕ) < k) : plucker (x ∘ ofFinEmbEquiv.symm J) ∈ wedgeSpan k p x :=
  Submodule.subset_span ⟨J, hJ, rfl⟩

/-- `wedgeSpan` is contained in a submodule exactly when every Plücker vector of a `p`-subfamily
meeting the first `k` indices is. -/
theorem wedgeSpan_le_iff {k : ℕ} {x : Fin N → ι → R} {U : Submodule R (powersetCard ι p → R)} :
    wedgeSpan k p x ≤ U ↔
      ∀ J : powersetCard (Fin N) p, (∃ j ∈ J, (j : ℕ) < k) →
        plucker (x ∘ ofFinEmbEquiv.symm J) ∈ U := by
  rw [wedgeSpan, Submodule.span_le, Set.image_subset_iff]
  exact Iff.rfl

/-- **The top block** `{k, …, N - 1}` of the indices of `Fin N`, for `k + p = N`, as a
`p`-subset. -/
def topBlock {k : ℕ} (h : k + p = N) : powersetCard (Fin N) p :=
  ofFinEmbEquiv ((Fin.natAddOrderEmb k).trans (Fin.castOrderIso h).toOrderEmbedding)

/-- The `a`-th index of the top block, in increasing order, is `k + a`. -/
@[simp]
theorem val_ofFinEmbEquiv_symm_topBlock {k : ℕ} (h : k + p = N) (a : Fin p) :
    (ofFinEmbEquiv.symm (topBlock h) a : ℕ) = k + a := by
  simp [topBlock]

/-- An index lies in the top block exactly when it is at least `k`. -/
theorem mem_topBlock {k : ℕ} (h : k + p = N) {j : Fin N} : j ∈ topBlock h ↔ k ≤ (j : ℕ) := by
  rw [← mem_range_ofFinEmbEquiv_symm_iff_mem]
  refine ⟨?_, fun hj ↦ ⟨⟨j - k, by omega⟩, Fin.ext ?_⟩⟩
  · rintro ⟨a, rfl⟩
    simp
  · simp only [val_ofFinEmbEquiv_symm_topBlock]
    omega

/-- **A `p`-subset other than the top block meets the first `k` indices.** -/
theorem exists_lt_of_ne_topBlock {k : ℕ} (h : k + p = N) {J : powersetCard (Fin N) p}
    (hJ : J ≠ topBlock h) : ∃ j ∈ J, (j : ℕ) < k := by
  by_contra! hc
  exact hJ (eq_iff_subset.2 fun j hj ↦ (mem_topBlock h).2 (hc j hj))

variable [Fintype ι] {K : Type*} [Field K] {x : Fin (Fintype.card ι) → ι → K}
  {f : Fin (Fintype.card ι) → Dual K (ι → K)}

omit [LinearOrder ι] in
private theorem card_powersetCard_fin (p : ℕ) :
    Fintype.card (powersetCard (Fin (Fintype.card ι)) p) = Fintype.card (powersetCard ι p) := by
  simp only [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]

/-- **The span of the wedges meeting the first `k` indices is a hyperplane**: for a basis `x` with
biorthogonal forms `f`, it is the kernel of the wedge of the last `p` forms `f k, …, f (N - 1)`. -/
theorem wedgeSpan_eq_ker (hx : LinearIndependent K x)
    (hf : ∀ i j, f i (x j) = if i = j then 1 else 0) {k : ℕ} (h : k + p = Fintype.card ι) :
    wedgeSpan k p x = LinearMap.ker (wedgeForms f p (topBlock h)) := by
  refine le_antisymm (wedgeSpan_le_iff.2 fun J ⟨j, hjJ, hjk⟩ ↦ ?_) fun z hz ↦ ?_
  · rw [LinearMap.mem_ker, wedgeForms_plucker_comp_eq_ite hf, ite_eq_right_iff]
    rintro rfl
    exact absurd ((mem_topBlock h).1 hjJ) (by omega)
  · -- expand `z` in the basis of Plücker vectors; the coefficient of the top block vanishes
    have hsp := (linearIndependent_plucker_comp hx p).span_eq_top_of_card_eq_finrank'
      (by rw [card_powersetCard_fin, Module.finrank_fintype_fun_eq_card])
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
      (hsp ▸ Submodule.mem_top : z ∈ Submodule.span K (Set.range _))
    have hc₀ : c (topBlock h) = 0 := by
      simpa [map_sum, wedgeForms_plucker_comp_eq_ite hf] using hz
    refine Submodule.sum_mem _ fun J _ ↦ ?_
    obtain rfl | hJ := eq_or_ne J (topBlock h)
    · simp [hc₀]
    · exact Submodule.smul_mem _ _ (plucker_comp_mem_wedgeSpan x (exists_lt_of_ne_topBlock h hJ))

/-- For a basis `x` with biorthogonal forms `f`, a vector lies in the span of the first `k`
vectors exactly when the wedge of the last `p` forms kills every wedge of `p` vectors through it. -/
private theorem mem_span_iff_forall_wedgeForms_eq_zero (hx : LinearIndependent K x)
    (hf : ∀ i j, f i (x j) = if i = j then 1 else 0) {k : ℕ} (h : k + p = Fintype.card ι)
    (u : ι → K) :
    u ∈ Submodule.span K (x '' {j | (j : ℕ) < k}) ↔
      ∀ (ω : Fin p → ι → K) (b : Fin p), ω b = u →
        wedgeForms f p (topBlock h) (plucker ω) = 0 := by
  -- the last `p` forms vanish on the span of the first `k` vectors
  have hvan (a : Fin p) : Submodule.span K (x '' {j | (j : ℕ) < k}) ≤
      LinearMap.ker (f (ofFinEmbEquiv.symm (topBlock h) a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hf, ite_eq_right_iff]
    intro hja
    have := val_ofFinEmbEquiv_symm_topBlock h a
    rw [hja] at this
    simp only [Set.mem_ofPred_eq] at hj
    omega
  refine ⟨fun hu ω b hb ↦ ?_, fun H ↦ ?_⟩
  · rw [wedgeForms_plucker]
    refine Matrix.det_eq_zero_of_column_eq_zero b fun a ↦ ?_
    rw [Matrix.of_apply, hb]
    exact LinearMap.mem_ker.1 (hvan a hu)
  · -- otherwise a coordinate `f j₀ u` with `j₀ ≥ k` is nonzero
    by_contra hu
    let B := basisOfLinearIndependentOfCardEqFinrank' x hx (by simp)
    have hB : ⇑B = x := coe_basisOfLinearIndependentOfCardEqFinrank' x hx _
    have hfB (i : Fin (Fintype.card ι)) : f i = B.coord i := B.ext fun j ↦ by
      rw [Basis.coord_apply, B.repr_self, Finsupp.single_apply, hB, hf]
      exact if_congr eq_comm rfl rfl
    obtain ⟨j₀, hj₀k, hj₀⟩ : ∃ j₀ : Fin (Fintype.card ι), k ≤ (j₀ : ℕ) ∧ f j₀ u ≠ 0 := by
      by_contra! hc
      refine hu ?_
      rw [← B.sum_repr u]
      refine Submodule.sum_mem _ fun j _ ↦ ?_
      by_cases hj : (j : ℕ) < k
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, by rw [hB]⟩)
      · simp [← Basis.coord_apply, ← hfB, hc j (by omega)]
    -- put `u` in place of `x j₀` in the top block: the matrix of values is the identity with
    -- one column replaced, and Cramer's rule reads off its determinant `f j₀ u`
    obtain ⟨a₀, ha₀⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem (topBlock h) j₀).2
      ((mem_topBlock h).2 hj₀k)
    have H₀ := H (Function.update (x ∘ ofFinEmbEquiv.symm (topBlock h)) a₀ u) a₀
      (Function.update_self _ _ _)
    set t := ofFinEmbEquiv.symm (topBlock h)
    have hmat : (Matrix.of fun a b ↦ f (t a) (Function.update (x ∘ t) a₀ u b)) =
        (1 : Matrix (Fin p) (Fin p) K).updateCol a₀ fun a ↦ f (t a) u := by
      ext a b
      obtain rfl | hb := eq_or_ne b a₀
      · simp
      · simp [Function.update_of_ne hb, Matrix.updateCol_ne hb, hf, Matrix.one_apply,
          t.injective.eq_iff]
    rw [wedgeForms_plucker, hmat, ← Matrix.cramer_apply, Matrix.cramer_one, Module.End.one_apply,
      ha₀] at H₀
    exact hj₀ H₀

/-- **The wedges meeting the first `k` indices determine the span of the first `k` vectors**
(Bombieri–Gubler, Lemma 7.5.33): for a basis `x` and `k + p = #ι`, a vector lies in the span of
`x 0, …, x (k - 1)` exactly when the Plücker vector of every family of `p` vectors containing it
lies in `wedgeSpan k p x`. -/
theorem mem_span_iff_forall_plucker_mem_wedgeSpan (hx : LinearIndependent K x) {k : ℕ}
    (h : k + p = Fintype.card ι) (u : ι → K) :
    u ∈ Submodule.span K (x '' {j | (j : ℕ) < k}) ↔
      ∀ (ω : Fin p → ι → K) (b : Fin p), ω b = u → plucker ω ∈ wedgeSpan k p x := by
  obtain ⟨f, hf⟩ := hx.exists_dual_forall_apply_eq_ite
  rw [wedgeSpan_eq_ker hx hf h]
  exact mem_span_iff_forall_wedgeForms_eq_zero hx hf h u

/-- **The span of the wedges meeting the first `k` indices depends only on the span of the first
`k` vectors, and determines it** (Bombieri–Gubler, Lemma 7.5.33): for two bases `x` and `x'` and
`k + p = #ι`, the two `wedgeSpan`s agree exactly when `x` and `x'` have the same first `k`-span. -/
theorem wedgeSpan_eq_wedgeSpan_iff {x' : Fin (Fintype.card ι) → ι → K}
    (hx : LinearIndependent K x) (hx' : LinearIndependent K x') {k : ℕ}
    (h : k + p = Fintype.card ι) :
    wedgeSpan k p x = wedgeSpan k p x' ↔
      Submodule.span K (x '' {j | (j : ℕ) < k}) = Submodule.span K (x' '' {j | (j : ℕ) < k}) := by
  refine ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩
  · ext u
    rw [mem_span_iff_forall_plucker_mem_wedgeSpan hx h, hW,
      mem_span_iff_forall_plucker_mem_wedgeSpan hx' h]
  · -- each generator of one `wedgeSpan` has a vector in the common span, so lies in the other
    have key {y y' : Fin (Fintype.card ι) → ι → K} (hy' : LinearIndependent K y')
        (hyy' : Submodule.span K (y '' {j | (j : ℕ) < k}) =
          Submodule.span K (y' '' {j | (j : ℕ) < k})) :
        wedgeSpan k p y ≤ wedgeSpan k p y' := by
      refine wedgeSpan_le_iff.2 fun J ⟨j, hjJ, hjk⟩ ↦ ?_
      obtain ⟨b, hb⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem J j).2 hjJ
      refine (mem_span_iff_forall_plucker_mem_wedgeSpan hy' h (y j)).1 ?_ _ b
        (by rw [Function.comp_apply, hb])
      rw [← hyy']
      exact Submodule.subset_span ⟨j, hjk, rfl⟩
    exact le_antisymm (key hx' hW) (key hx hW.symm)

/-- **The wedge of the top block is not in the span of the others**: in particular `wedgeSpan` is
a proper subspace. -/
theorem plucker_topBlock_notMem_wedgeSpan (hx : LinearIndependent K x) {k : ℕ}
    (h : k + p = Fintype.card ι) :
    plucker (x ∘ ofFinEmbEquiv.symm (topBlock h)) ∉ wedgeSpan k p x := by
  obtain ⟨f, hf⟩ := hx.exists_dual_forall_apply_eq_ite
  rw [wedgeSpan_eq_ker hx hf h, LinearMap.mem_ker, wedgeForms_plucker_comp_eq_ite hf]
  simp

/-- **The span of the wedges meeting the first `k` indices has codimension one.** -/
theorem finrank_wedgeSpan_add_one (hx : LinearIndependent K x) {k : ℕ}
    (h : k + p = Fintype.card ι) :
    finrank K (wedgeSpan k p x) + 1 = Fintype.card (powersetCard ι p) := by
  obtain ⟨f, hf⟩ := hx.exists_dual_forall_apply_eq_ite
  rw [wedgeSpan_eq_ker hx hf h]
  have hrange : LinearMap.range (wedgeForms f p (topBlock h)) = ⊤ :=
    LinearMap.range_eq_top.2 fun a ↦ ⟨a • plucker (x ∘ ofFinEmbEquiv.symm (topBlock h)),
      by simp [wedgeForms_plucker_comp_eq_ite hf]⟩
  have := LinearMap.finrank_range_add_finrank_ker (wedgeForms f p (topBlock h))
  rw [hrange, finrank_top, finrank_self, finrank_fintype_fun_eq_card] at this
  omega

end WedgeSpan

/-! ### Examples -/

/-- Laplace's identity pins the orientation: in two variables the wedge of two forms on the wedge
of two vectors is the `2 × 2` determinant with the forms along the rows. -/
example [Fintype ι] (l : Fin 2 → Dual R (ι → R)) (y : Fin 2 → ι → R) :
    wedgeForm l (plucker y) = l 0 (y 0) * l 1 (y 1) - l 0 (y 1) * l 1 (y 0) := by
  simp [Matrix.det_fin_two]

/-- In `ℚ³` with `k = 1`, the wedge `e₀ ∧ (e₁ + e₂)` has a factor in the span of `e₀`, so it lies
in the span of the wedges meeting the first index, while the top wedge `e₁ ∧ e₂` does not. A span
of the wedges *contained in* the first `k` indices would be `0` here. -/
example :
    let e : Fin (Fintype.card (Fin 3)) → Fin 3 → ℚ :=
      Pi.basisFun ℚ (Fin 3) ∘ Fin.cast (Fintype.card_fin 3)
    plucker ![e 0, e 1 + e 2] ∈ wedgeSpan 1 2 e ∧ plucker ![e 1, e 2] ∉ wedgeSpan 1 2 e := by
  intro e
  have he : LinearIndependent ℚ e :=
    (Pi.basisFun ℚ (Fin 3)).linearIndependent.comp _ (Fin.cast_injective _)
  have h : 1 + 2 = Fintype.card (Fin 3) := by simp
  refine ⟨(mem_span_iff_forall_plucker_mem_wedgeSpan he h (e 0)).1
    (Submodule.subset_span ⟨0, by simp, rfl⟩) _ 0 rfl, ?_⟩
  have htop : e ∘ ofFinEmbEquiv.symm (topBlock h) = ![e 1, e 2] := by
    have hidx (a : Fin 2) : ofFinEmbEquiv.symm (topBlock h) a = Fin.cast h (Fin.natAdd 1 a) :=
      Fin.ext (by simp)
    funext a
    -- `simp` leaves `Fin.cast` of a numeral, which is that numeral since `#(Fin 3)` reduces to `3`
    fin_cases a <;> simp [e, hidx] <;> rfl
  rw [← htop]
  exact plucker_topBlock_notMem_wedgeSpan he h

end TauCeti
