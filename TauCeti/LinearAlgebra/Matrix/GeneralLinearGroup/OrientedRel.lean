/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.elementarySubgroup`, `TauCeti.fromBlocksGL` and the block unipotent matrices occur in
-- the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
-- `Ideal.Quotient.mk` occurs in the statements below.
public import Mathlib.RingTheory.Ideal.Quotient.Defs
-- Non-public: `Matrix.det_one_add_mul_comm` is used only in a proof below.
import Mathlib.LinearAlgebra.Matrix.SchurComplement
-- Non-public: `Matrix.GeneralLinearGroup.mem_ker_map_quotientMk_iff` is used only in proofs.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
-- Non-public: `TauCeti.transvectionWeylElement_mem_elementarySubgroup` is used only in a proof.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary.Permutation

/-!
# The oriented relation of Bass–Milnor–Serre

Let `A` be a commutative ring, `I` an ideal, `i₀` a distinguished index and `t ∈ A`. Write
`D = diag(1, …, t, …, 1)` for the diagonal matrix scaling the `i₀`-th coordinate by `t`. Two
square matrices `g` and `h` are in **oriented relation** `I.OrientedRel i₀ t g h` when

`g = 1 + U D` and `h = 1 + D U`

for a matrix `U` whose `(i₀, i₀)` entry lies in `I`. Entrywise (`Ideal.orientedRel_iff`), `g`
and `h` have the same diagonal entry `1 + t s` at `i₀`, with `s ∈ I`, and the same entries off
the `i₀`-th row and column, while the off-diagonal entries of the `i₀`-th column of `g` are `t`
times those of `h`, and the off-diagonal entries of the `i₀`-th row of `h` are `t` times those of
`g`. Thus the factor `t` moves from the column to the row; for `t = 1` the relation is equality
together with the congruence `g i₀ i₀ ≡ 1 (mod I)` (`Ideal.orientedRel_one_iff`), and for `t = 0`
it is neither reflexive nor symmetric.

This is the relation by which Bass, Milnor and Serre formulate the hypotheses of their extension
theorem for homomorphisms `κ : GLₙ(A, I) → C`: `κ g = κ h` whenever `g` and `h` are in oriented
relation with `t ∈ I`. The results here are the properties of the relation used there:

* `Ideal.OrientedRel.det_eq`: related matrices have the same determinant, by
  `det (1 + U D) = det (1 + D U)`.
* `Ideal.OrientedRel.mul`: the relation is preserved by products, provided the first matrix has
  its `i₀`-th row congruent to the standard row modulo `I` off the diagonal.
* `Ideal.OrientedRel.fromBlocksGL_inv_mul_mem_commutator`: if `g` and `h` are invertible and
  congruent to `1` modulo `I`, then after one stabilization `g⁻¹ h` lies in the commutator
  `⁅E_{n+1}(A), GL_{n+1}(A, I)⁆` of the elementary subgroup with the principal congruence
  subgroup. Hence `g` and `h` have the same class in every quotient of `GL_{n+1}(A, I)` by a
  subgroup containing this commutator, and in particular in relative `K₁`.

The stabilization statement rests on the explicit identity, in `GL (ι ⊕ Unit) A`,
`h ⊕ 1 = w x₋(t) u (g ⊕ 1) x₋(t)⁻¹ x₊(s)⁻¹ w⁻¹ v`, where `s = U i₀ i₀`, `x₊` and `x₋` are the
elementary matrices between `i₀` and the new coordinate, `w` is the Weyl element they generate,
`u` is the block unipotent matrix carrying the `i₀`-th column of `U` into the new column, and `v`
the one carrying the off-diagonal part of the `i₀`-th row of `U` into the new row. Neither `t ∈ I`
nor a stable range hypothesis is needed. The factors `u` and `v` lie in `⁅E(A), GL(A, I)⁆` by
`Matrix.upperBlockGL_mem_commutator_elementarySubgroup_ker` and its lower analogue, and `x₊(s)` by
`TauCeti.transvectionUnit_mem_commutator_elementarySubgroup_ker`.

## References

* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §8, condition (8.4) and Lemma 8.8.
-/

public section

open Matrix TauCeti

open scoped commutatorElement

/-! ## The oriented relation -/

namespace Ideal

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] {I : Ideal A} {i₀ : ι} {t : A}
  {g h g' h' : Matrix ι ι A}

/-- The **oriented relation** of Bass, Milnor and Serre: `g = 1 + U D` and `h = 1 + D U` for a
matrix `U` with `U i₀ i₀ ∈ I`, where `D` is the diagonal matrix scaling the `i₀`-th coordinate by
`t`. Thus `g` carries the factor `t` in its `i₀`-th column and `h` in its `i₀`-th row
(`Ideal.orientedRel_iff`). -/
def OrientedRel (I : Ideal A) (i₀ : ι) (t : A) (g h : Matrix ι ι A) : Prop :=
  ∃ U : Matrix ι ι A, U i₀ i₀ ∈ I ∧ 1 + U * diagonal (Pi.mulSingle i₀ t) = g ∧
    1 + diagonal (Pi.mulSingle i₀ t) * U = h

/-- The defining witness of the oriented relation. -/
theorem orientedRel_def :
    I.OrientedRel i₀ t g h ↔ ∃ U : Matrix ι ι A, U i₀ i₀ ∈ I ∧
      1 + U * diagonal (Pi.mulSingle i₀ t) = g ∧ 1 + diagonal (Pi.mulSingle i₀ t) * U = h :=
  Iff.rfl

/-- The witness constructor: `1 + U D` and `1 + D U` are in oriented relation as soon as
`U i₀ i₀ ∈ I`. -/
theorem orientedRel_one_add_mul {U : Matrix ι ι A} (hU : U i₀ i₀ ∈ I) :
    I.OrientedRel i₀ t (1 + U * diagonal (Pi.mulSingle i₀ t))
      (1 + diagonal (Pi.mulSingle i₀ t) * U) :=
  ⟨U, hU, rfl, rfl⟩

/-- The entries of `1 + U D`. -/
private theorem one_add_mul_diagonal_apply (U : Matrix ι ι A) (i j : ι) :
    (1 + U * diagonal (Pi.mulSingle i₀ t)) i j =
      (1 : Matrix ι ι A) i j + U i j * if j = i₀ then t else 1 := by
  simp [Pi.mulSingle_apply]

/-- The entries of `1 + D U`. -/
private theorem one_add_diagonal_mul_apply (U : Matrix ι ι A) (i j : ι) :
    (1 + diagonal (Pi.mulSingle i₀ t) * U) i j =
      (1 : Matrix ι ι A) i j + (if i = i₀ then t else 1) * U i j := by
  simp [Pi.mulSingle_apply]

/-- **Entrywise form of the oriented relation.** The matrices `g` and `h` are in oriented relation
exactly when they have the same entry `1 + t s` at `(i₀, i₀)` for some `s ∈ I`, the `i₀`-th column
of `g` is `t` times that of `h` off the diagonal, the `i₀`-th row of `h` is `t` times that of `g`
off the diagonal, and `g` and `h` agree away from the `i₀`-th row and column. -/
theorem orientedRel_iff :
    I.OrientedRel i₀ t g h ↔ (∃ s ∈ I, g i₀ i₀ = 1 + t * s ∧ h i₀ i₀ = 1 + t * s) ∧
      (∀ i, i ≠ i₀ → g i i₀ = t * h i i₀) ∧ (∀ j, j ≠ i₀ → h i₀ j = t * g i₀ j) ∧
      ∀ i j, i ≠ i₀ → j ≠ i₀ → g i j = h i j := by
  constructor
  · rintro ⟨U, hU, rfl, rfl⟩
    refine ⟨⟨U i₀ i₀, hU, ?_, ?_⟩, fun i hi ↦ ?_, fun j hj ↦ ?_, fun i j hi hj ↦ ?_⟩ <;>
      simp only [one_add_mul_diagonal_apply, one_add_diagonal_mul_apply, Matrix.one_apply] <;>
      simp [*, Ne.symm, mul_comm]
  · rintro ⟨⟨s, hs, hg, hh⟩, hcol, hrow, hrest⟩
    refine ⟨of fun i j ↦ if i = i₀ then (if j = i₀ then s else g i₀ j)
      else if j = i₀ then h i i₀ else g i j - (1 : Matrix ι ι A) i j, by simpa using hs, ?_, ?_⟩
    · ext i j
      rw [one_add_mul_diagonal_apply, Matrix.of_apply]
      by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;>
        simp_all [Matrix.one_apply, mul_comm, eq_comm]
    · ext i j
      rw [one_add_diagonal_mul_apply, Matrix.of_apply]
      by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;>
        simp_all [Matrix.one_apply, mul_comm, eq_comm]

/-- For `t = 1` the oriented relation is equality, together with the congruence of the
`(i₀, i₀)` entry to `1`. -/
@[simp]
theorem orientedRel_one_iff : I.OrientedRel i₀ 1 g h ↔ g = h ∧ g i₀ i₀ - 1 ∈ I := by
  constructor
  · rintro ⟨U, hU, rfl, rfl⟩
    simpa using hU
  · rintro ⟨rfl, hg⟩
    exact ⟨g - 1, by simpa using hg, by simp, by simp⟩

namespace OrientedRel

/-- **Related matrices have the same determinant**: `det (1 + U D) = det (1 + D U)`. -/
theorem det_eq (hR : I.OrientedRel i₀ t g h) : g.det = h.det := by
  obtain ⟨U, -, rfl, rfl⟩ := hR
  exact det_one_add_mul_comm U _

/-- **The oriented relation is preserved by products**, provided the off-diagonal entries of the
`i₀`-th row of the left factor `g` lie in `I`: then `1 + U D` times `1 + U' D` is
`1 + (U + U' + U D U') D`, and `1 + D U` times `1 + D U'` is `1 + D (U + U' + U D U')`. -/
theorem mul (hR : I.OrientedRel i₀ t g h) (hR' : I.OrientedRel i₀ t g' h')
    (hg : ∀ j, j ≠ i₀ → g i₀ j ∈ I) : I.OrientedRel i₀ t (g * g') (h * h') := by
  obtain ⟨U, hU, rfl, rfl⟩ := hR
  obtain ⟨U', hU', rfl, rfl⟩ := hR'
  set D := diagonal (Pi.mulSingle i₀ t)
  refine ⟨U + U' + U * D * U', ?_, by noncomm_ring, by noncomm_ring⟩
  -- The `(i₀, i₀)` entry of `U D U'` is `∑ⱼ U i₀ j D j j U' j i₀`; every term lies in `I`.
  refine add_mem (add_mem hU hU') ?_
  rw [Matrix.mul_apply]
  refine I.sum_mem fun j _ ↦ ?_
  rw [mul_diagonal]
  by_cases hj : j = i₀
  · subst hj
    exact mul_mem_right _ _ (mul_mem_right _ _ hU)
  · have : U i₀ j ∈ I := by
      simpa [D, Pi.mulSingle_apply, Matrix.one_apply_ne' hj, hj] using hg j hj
    exact mul_mem_right _ _ (mul_mem_right _ _ this)

end OrientedRel

/-! ## The oriented relation after one stabilization -/

section Stabilization

/-- The matrix of `w x₋(t)`, where `w` is the Weyl element exchanging the `i₀`-th coordinate with
the new last one and `x₋(t)` adds `t` times the `i₀`-th coordinate to the new last one: the scaling
by `t` at `i₀`, bordered by the Weyl element. -/
private theorem coe_transvectionWeylElement_mul_transvectionUnit (i₀ : ι) (t : A) :
    ((transvectionWeylElement (Sum.inl_ne_inr (a := i₀) (b := ())) *
        transvectionUnit (Sum.inr_ne_inl (a := i₀) (b := ())) t : GL (ι ⊕ Unit) A) :
        Matrix (ι ⊕ Unit) (ι ⊕ Unit) A) =
      fromBlocks (diagonal (Pi.mulSingle i₀ t)) (single i₀ () 1) (single () i₀ (-1)) 0 := by
  simp only [transvectionWeylElement_def, ← upperBlockGL_single, ← lowerBlockGL_single,
    Units.val_mul, coe_upperBlockGL, coe_lowerBlockGL, fromBlocks_multiply]
  congr 1 <;> ext i j <;>
    simp [Matrix.mul_apply, single_apply, Pi.mulSingle_apply, Matrix.one_apply, diagonal_apply] <;>
    grind

/-- The matrix of `x₋(t)⁻¹ x₊(s)⁻¹`, where `x₊(s)` adds `s` times the new last coordinate to the
`i₀`-th one. -/
private theorem coe_transvectionUnit_inv_mul_transvectionUnit_inv (i₀ : ι) (s t : A) :
    (((transvectionUnit (Sum.inr_ne_inl (a := i₀) (b := ())) t)⁻¹ *
        (transvectionUnit (Sum.inl_ne_inr (a := i₀) (b := ())) s)⁻¹ : GL (ι ⊕ Unit) A) :
        Matrix (ι ⊕ Unit) (ι ⊕ Unit) A) =
      fromBlocks 1 (single i₀ () (-s)) (single () i₀ (-t)) (of fun _ _ ↦ 1 + t * s) := by
  simp only [← upperBlockGL_single, ← lowerBlockGL_single, upperBlockGL_inv, lowerBlockGL_inv,
    Units.val_mul, coe_upperBlockGL, coe_lowerBlockGL, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [single_apply, add_comm] <;> split_ifs <;> simp

/-- The matrix of `w⁻¹`. -/
private theorem coe_transvectionWeylElement_inv (i₀ : ι) :
    (((transvectionWeylElement (Sum.inl_ne_inr (a := i₀) (b := ())))⁻¹ : GL (ι ⊕ Unit) A) :
        Matrix (ι ⊕ Unit) (ι ⊕ Unit) A) =
      fromBlocks (1 - single i₀ i₀ 1) (single i₀ () (-1)) (single () i₀ 1) 0 := by
  rw [transvectionWeylElement_inv, coe_transvectionWeylElement]
  ext (i | i) (j | j) <;> simp [single_apply, Matrix.one_apply, neg_ite]

/-- The explicit factorization behind the stabilization theorem: with `s = U i₀ i₀`,
`(1 + D U) ⊕ 1 = w x₋(t) u ((1 + U D) ⊕ 1) x₋(t)⁻¹ x₊(s)⁻¹ w⁻¹ v`. -/
private theorem fromBlocks_one_add_diagonal_mul_eq (U : Matrix ι ι A) :
    fromBlocks (1 + diagonal (Pi.mulSingle i₀ t) * U) 0 0 (1 : Matrix Unit Unit A) =
      fromBlocks (diagonal (Pi.mulSingle i₀ t)) (single i₀ () 1) (single () i₀ (-1)) 0 *
        fromBlocks 1 (of fun i (_ : Unit) ↦ U i i₀) 0 1 *
        fromBlocks (1 + U * diagonal (Pi.mulSingle i₀ t)) 0 0 (1 : Matrix Unit Unit A) *
        fromBlocks 1 (single i₀ () (-U i₀ i₀)) (single () i₀ (-t))
          (of fun _ _ ↦ 1 + t * U i₀ i₀) *
        fromBlocks (1 - single i₀ i₀ 1) (single i₀ () (-1)) (single () i₀ 1) 0 *
        fromBlocks 1 0 (of fun (_ : Unit) j ↦ if j = i₀ then 0 else U i₀ j) 1 := by
  simp only [fromBlocks_multiply]
  congr 1 <;> ext i j <;>
    simp [Matrix.mul_apply, single_apply, Pi.mulSingle_apply, Matrix.one_apply, diagonal_apply,
      Finset.sum_add_distrib, add_mul, mul_add, mul_sub, Finset.sum_sub_distrib, ite_and] <;>
    grind

/-- The group-theoretic step of the stabilization theorem: if `h = w l u g l⁻¹ x⁻¹ w⁻¹ v` with
`g ∈ K`, `w, l ∈ E` and `u, x, v ∈ ⁅E, K⁆`, then `g⁻¹ h ∈ ⁅E, K⁆`, because
`g⁻¹ h = ⁅g⁻¹, w l⁆ · (w l) (g⁻¹ u g) (w l)⁻¹ · w x⁻¹ w⁻¹ · v`. -/
private theorem inv_mul_mem_commutator_of_eq {G : Type*} [Group G] {E K : Subgroup G}
    {g h w l u x v : G} (hg : g ∈ K) (hw : w ∈ E) (hl : l ∈ E) (hu : u ∈ ⁅E, K⁆)
    (hx : x ∈ ⁅E, K⁆) (hv : v ∈ ⁅E, K⁆) (hh : h = w * l * u * g * (l⁻¹ * x⁻¹) * w⁻¹ * v) :
    g⁻¹ * h ∈ ⁅E, K⁆ := by
  have hE := Subgroup.normalizer_commutator_ge_left E K
  have hK := Subgroup.normalizer_commutator_ge_right E K
  have hprod : g⁻¹ * h =
      ⁅g⁻¹, w * l⁆ * (w * l * (g⁻¹ * u * g) * (w * l)⁻¹) * (w * x⁻¹ * w⁻¹ * v) := by
    rw [hh, commutatorElement_def]
    group
  rw [hprod]
  refine mul_mem (mul_mem ?_ ?_) (mul_mem ?_ hv)
  · rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (inv_mem hg) (mul_mem hw hl)
  · refine (Subgroup.mem_normalizer_iff.1 (hE (mul_mem hw hl)) _).1 ?_
    simpa using (Subgroup.mem_normalizer_iff.1 (hK (inv_mem hg)) _).1 hu
  · exact (Subgroup.mem_normalizer_iff.1 (hE hw) _).1 (inv_mem hx)

/-- The factorization `h ⊕ 1 = w x₋(t) u (g ⊕ 1) x₋(t)⁻¹ x₊(s)⁻¹ w⁻¹ v` in `GL (ι ⊕ Unit) A`, for
`g = 1 + U D`, `h = 1 + D U` and `s = U i₀ i₀`. -/
private theorem fromBlocksGL_eq_mul {g h : GL ι A} {U : Matrix ι ι A}
    (hgU : 1 + U * diagonal (Pi.mulSingle i₀ t) = g)
    (hhU : 1 + diagonal (Pi.mulSingle i₀ t) * U = h) :
    fromBlocksGL (h, (1 : GL Unit A)) =
      transvectionWeylElement (Sum.inl_ne_inr (a := i₀) (b := ())) *
      transvectionUnit (Sum.inr_ne_inl (a := i₀) (b := ())) t *
      upperBlockGL (of fun i (_ : Unit) ↦ U i i₀) * fromBlocksGL (g, 1) *
      ((transvectionUnit (Sum.inr_ne_inl (a := i₀) (b := ())) t)⁻¹ *
        (transvectionUnit (Sum.inl_ne_inr (a := i₀) (b := ())) (U i₀ i₀))⁻¹) *
      (transvectionWeylElement (Sum.inl_ne_inr (a := i₀) (b := ())))⁻¹ *
      lowerBlockGL (of fun (_ : Unit) j ↦ if j = i₀ then 0 else U i₀ j) := by
  ext : 1
  -- The grouped factors `w x₋(t)` and `x₋(t)⁻¹ x₊(s)⁻¹` are rewritten as pre-lemmas (`↓`), before
  -- `Units.val_mul` would split them into their elementary factors.
  simp only [Units.val_mul, ↓coe_transvectionWeylElement_mul_transvectionUnit,
    ↓coe_transvectionUnit_inv_mul_transvectionUnit_inv, coe_transvectionWeylElement_inv,
    coe_upperBlockGL, coe_lowerBlockGL, coe_fromBlocksGL, ← hgU, ← hhU]
  exact fromBlocks_one_add_diagonal_mul_eq U

namespace OrientedRel

/-- **After one stabilization, related matrices differ by an element of the commutator subgroup
`⁅E(A), GL(A, I)⁆`.** If `g` and `h` are invertible, congruent to `1` modulo `I` and in
oriented relation, then `(g⁻¹ h) ⊕ 1` lies in `⁅E_{n+1}(A), GL_{n+1}(A, I)⁆`. No hypothesis on
`t` is needed. -/
theorem fromBlocksGL_inv_mul_mem_commutator {g h : GL ι A}
    (hR : I.OrientedRel i₀ t g h)
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).ker)
    (hh : h ∈ (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).ker) :
    fromBlocksGL (g⁻¹ * h, (1 : GL Unit A)) ∈ ⁅elementarySubgroup (ι ⊕ Unit) A,
      (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).ker⁆ := by
  set E := elementarySubgroup (ι ⊕ Unit) A
  set K := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) :
    GL (ι ⊕ Unit) A →* GL (ι ⊕ Unit) (A ⧸ I)).ker
  obtain ⟨U, hU, hgU, hhU⟩ := hR
  -- Over a single index there is nothing to move: `g = h`.
  rcases subsingleton_or_nontrivial ι with hι | hι
  · have : g = h := by
      ext i j
      rw [← hgU, ← hhU, Subsingleton.elim i i₀, Subsingleton.elim j i₀]
      simp [mul_comm]
    rw [this, inv_mul_cancel, Prod.mk_one_one, map_one]
    exact one_mem _
  have hn : 3 ≤ Fintype.card (ι ⊕ Unit) := by
    rw [Fintype.card_sum, Fintype.card_unit]
    have := Fintype.one_lt_card_iff_nontrivial.2 hι
    omega
  -- The `i₀`-th row and column of `U` have entries in `I`, so the block unipotent factors of the
  -- factorization `fromBlocksGL_eq_mul` lie in `⁅E, K⁆`.
  have hu : upperBlockGL (of fun i (_ : Unit) ↦ U i i₀) ∈ ⁅E, K⁆ :=
    upperBlockGL_mem_commutator_elementarySubgroup_ker hn fun i _ ↦ by
      by_cases hi : i = i₀
      · exact hi ▸ hU
      · simpa [← hhU, Pi.mulSingle_apply, hi, Matrix.one_apply_ne hi] using
          (Matrix.GeneralLinearGroup.mem_ker_map_quotientMk_iff I).1 hh i i₀
  have hv : lowerBlockGL (of fun (_ : Unit) j ↦ if j = i₀ then 0 else U i₀ j) ∈ ⁅E, K⁆ :=
    lowerBlockGL_mem_commutator_elementarySubgroup_ker hn fun _ j ↦ by
      by_cases hj : j = i₀
      · simp [hj]
      · simpa [← hgU, Pi.mulSingle_apply, hj, Matrix.one_apply_ne' hj] using
          (Matrix.GeneralLinearGroup.mem_ker_map_quotientMk_iff I).1 hg i₀ j
  obtain ⟨j, hj⟩ := exists_ne i₀
  have hs := transvectionUnit_mem_commutator_elementarySubgroup_ker (I := I)
    (Sum.inl_ne_inr (a := i₀) (b := ())) (Sum.inl_injective.ne hj.symm) Sum.inl_ne_inr hU
  have : ((g⁻¹ * h, 1) : GL ι A × GL Unit A) = (g, 1)⁻¹ * (h, 1) := by simp
  rw [this, map_mul, map_inv]
  exact inv_mul_mem_commutator_of_eq (fromBlocksGL_mem_ker_iff.2 ⟨hg, one_mem _⟩)
    (transvectionWeylElement_mem_elementarySubgroup _)
    (transvectionUnit_mem_elementarySubgroup _ _) hu hs hv (fromBlocksGL_eq_mul hgU hhU)

end OrientedRel

end Stabilization

end Ideal
