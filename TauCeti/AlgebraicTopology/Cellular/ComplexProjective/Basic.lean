/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Dimension
public import TauCeti.AlgebraicTopology.Cellular.Lacunary
public import TauCeti.Topology.CWComplex.Classical.ComplexProjective

/-!
# The singular homology of complex projective space

The CW structure `TauCeti.ComplexProjectiveSpace.cwComplex` on `CPⁿ` has one cell in each even
dimension `0, 2, …, 2n` and none in odd dimensions. Hence, with coefficients `R` in any abelian
category with coproducts, its cellular chain complex has a copy of `R` in each even degree
`2i ≤ 2n` (`TauCeti.cellularChainGroupIso`) and zero in every other degree, so all of its
differentials vanish, since one end of each differential is zero
(`TauCeti.cellularChainComplex_d_eq_zero_of_isEmpty_or`). Transporting the cellular homology
(`TauCeti.cellularHomologyIsoSigma`) along the cellular–singular comparison
`TauCeti.cellularSingularHomologyIsoUniv` computes the singular homology of `CPⁿ`: it is `R` in the
degrees `0, 2, …, 2n` and zero otherwise.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.cellularChainComplex_d_eq_zero`: every differential of the
  cellular chain complex of `CPⁿ` vanishes.
* `TauCeti.ComplexProjectiveSpace.singularHomologyIso`: for `i ≤ n`, `H₂ᵢ(CPⁿ; R) ≅ R`.
* `TauCeti.ComplexProjectiveSpace.isZero_singularHomology_of_odd`: `Hₖ(CPⁿ; R) = 0` for odd `k`.
* `TauCeti.ComplexProjectiveSpace.isZero_singularHomology_of_lt`: `Hₖ(CPⁿ; R) = 0` for `k > 2n`,
  as is the cellular chain group
  (`TauCeti.ComplexProjectiveSpace.isZero_cellularChainComplex_X_of_lt`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the cellular homology of `CPⁿ` after Theorem 2.35.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

universe v u

namespace TauCeti.ComplexProjectiveSpace

attribute [local instance] cwComplex Abelian.hasFiniteBiproducts

variable {n : ℕ} {A : Type u} [Category.{v} A] [HasCoproducts.{0} A] [Abelian A] (R : A)

/-- The cells of `CPⁿ` in each dimension form a finite type. -/
instance (m : ℕ) : Finite (cell (univ : Set (ComplexProjectiveSpace n)) m) :=
  have := finite_cwComplex (n := n)
  FiniteType.finite_cell m

/-- In odd dimensions `CPⁿ` has no cells. -/
private lemma isEmpty_cell_of_odd {k : ℕ} (hk : Odd k) :
    IsEmpty (cell (univ : Set (ComplexProjectiveSpace n)) k) :=
  Finite.card_eq_zero_iff.1 <| by
    rw [nat_card_cell_cwComplex, ite_eq_right_iff]
    exact fun h ↦ absurd h.1 (Nat.not_even_iff_odd.2 hk)

/-- Above dimension `2n`, `CPⁿ` has no cells. -/
private lemma isEmpty_cell_of_lt {k : ℕ} (hk : 2 * n < k) :
    IsEmpty (cell (univ : Set (ComplexProjectiveSpace n)) k) :=
  Finite.card_eq_zero_iff.1 <| by
    rw [nat_card_cell_cwComplex, ite_eq_right_iff]
    exact fun h ↦ absurd h.2 (by omega)

/-- For `i ≤ n`, `CPⁿ` has exactly one cell of dimension `2i`. -/
@[instance_reducible]
private def uniqueCell {i : ℕ} (hi : i ≤ n) :
    Unique (cell (univ : Set (ComplexProjectiveSpace n)) (2 * i)) :=
  have h := Nat.card_eq_one_iff_unique.1 <| by
    rw [nat_card_cell_cwComplex, ite_eq_left_iff]
    exact fun h ↦ absurd ⟨even_two_mul i, by omega⟩ h
  { default := h.2.some
    uniq := fun _ ↦ h.1.elim _ _ }

/-- Of any two consecutive dimensions, `CPⁿ` has no cells in one of them. -/
private lemma isEmpty_cell_or_isEmpty_cell_add_one (k : ℕ) :
    IsEmpty (cell (univ : Set (ComplexProjectiveSpace n)) k) ∨
      IsEmpty (cell (univ : Set (ComplexProjectiveSpace n)) (k + 1)) :=
  (Nat.even_or_odd k).symm.imp isEmpty_cell_of_odd fun hk ↦ isEmpty_cell_of_odd hk.add_one

/-- The cellular chain complex of `CPⁿ` with coefficients in `R`. -/
local notation "K" => cellularChainComplex (univ : Set (ComplexProjectiveSpace n)) R

/-- **The cellular differential of `CPⁿ` vanishes.** Every differential of the cellular chain
complex of `CPⁿ` is zero: the cells of `CPⁿ` all have even dimension, so one of the two chain
groups it connects is zero. -/
@[simp]
theorem cellularChainComplex_d_eq_zero (j k : ℕ) : (K).d j k = 0 := by
  by_cases hjk : j = k + 1
  · subst hjk
    exact cellularChainComplex_d_eq_zero_of_isEmpty_or _ R
      (isEmpty_cell_or_isEmpty_cell_add_one k).symm
  · exact (K).shape j k fun h ↦ hjk h.symm

/-- The singular homology of `CPⁿ` in each degree is the coproduct of one copy of `R` for each cell
of that degree, since all the cellular differentials vanish. -/
private def singularHomologyIsoSigma (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
        (TopCat.of (ComplexProjectiveSpace n)) ≅
      ∐ fun _ : cell (univ : Set (ComplexProjectiveSpace n)) k ↦ R :=
  have := finite_cwComplex (n := n)
  (cellularSingularHomologyIsoUniv R k).symm ≪≫
    cellularHomologyIsoSigma _ R k (isEmpty_cell_or_isEmpty_cell_add_one k)
      fun m hm ↦ hm ▸ isEmpty_cell_or_isEmpty_cell_add_one m

/-- **The even-degree homology of complex projective space.** For `i ≤ n`, `H₂ᵢ(CPⁿ; R) ≅ R`.
The isomorphism is the cellular–singular comparison `TauCeti.cellularSingularHomologyIsoUniv`
followed by the identification `TauCeti.cellularHomologyIsoSigma` of the cellular homology with
the coproduct over the unique `2i`-cell. -/
def singularHomologyIso {i : ℕ} (hi : i ≤ n) :
    ((AlgebraicTopology.singularHomologyFunctor A (2 * i)).obj R).obj
        (TopCat.of (ComplexProjectiveSpace n)) ≅ R :=
  letI := uniqueCell hi
  singularHomologyIsoSigma R (2 * i) ≪≫ coproductUniqueIso _

/-- **The odd-degree homology of complex projective space vanishes.** `Hₖ(CPⁿ; R) = 0` for odd
`k`. -/
theorem isZero_singularHomology_of_odd {k : ℕ} (hk : Odd k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n))) :=
  have := finite_cwComplex (n := n)
  have := isEmpty_cell_of_odd (n := n) hk
  (Homeomorph.Set.univ _).symm.toHomotopyEquiv.isZero_singularHomology_of_isEmpty_cell R k

/-- The cellular chain complex of `CPⁿ` vanishes above degree `2n`. -/
theorem isZero_cellularChainComplex_X_of_lt {k : ℕ} (hk : 2 * n < k) : IsZero ((K).X k) := by
  have := isEmpty_cell_of_lt (n := n) hk
  rw [cellularChainComplex_X]
  exact isZero_cellularChainGroup _ k R

/-- The singular homology of `CPⁿ` vanishes above degree `2n`. -/
theorem isZero_singularHomology_of_lt {k : ℕ} (hk : 2 * n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n))) :=
  have := finite_cwComplex (n := n)
  isZero_singularHomology_univ_of_isEmpty_cell_gt _ R (fun _ hm ↦ isEmpty_cell_of_lt hm) hk

end TauCeti.ComplexProjectiveSpace
