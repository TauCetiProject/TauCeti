/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Cellular.Coproduct
public import TauCeti.Topology.CWComplex.Classical.ComplexProjective

/-!
# The singular homology of complex projective space

The CW structure `TauCeti.ComplexProjectiveSpace.cwComplex` on `CPⁿ` has one cell in each even
dimension `0, 2, …, 2n` and none in odd dimensions. Hence, with coefficients `R` in any abelian
category with coproducts, its cellular chain complex has a copy of `R` in each even degree
`2i ≤ 2n` (`TauCeti.cellularChainGroupIso`) and zero in every other degree, so all of its
differentials vanish, since one end of each differential is zero. Transporting the cellular
homology along the cellular–singular comparison `TauCeti.cellularSingularHomologyIsoUniv` computes
the singular homology of `CPⁿ`: it is `R` in the degrees `0, 2, …, 2n` and zero otherwise.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.cellularChainComplex_d_eq_zero`: every differential of the
  cellular chain complex of `CPⁿ` vanishes.
* `TauCeti.ComplexProjectiveSpace.singularHomologyIso`: for `i ≤ n`, `H₂ᵢ(CPⁿ; R) ≅ R`.
* `TauCeti.ComplexProjectiveSpace.isZero_singularHomology_of_odd`: `Hₖ(CPⁿ; R) = 0` for odd `k`.
* `TauCeti.ComplexProjectiveSpace.isZero_singularHomology_of_lt`: `Hₖ(CPⁿ; R) = 0` for `k > 2n`.

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
private instance (m : ℕ) : Finite (cell (univ : Set (ComplexProjectiveSpace n)) m) :=
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

/-- The cellular chain complex of `CPⁿ` with coefficients in `R`. -/
local notation "K" => cellularChainComplex (univ : Set (ComplexProjectiveSpace n)) R

/-- The cellular chain complex of `CPⁿ` vanishes in degrees carrying no cells. -/
private lemma isZero_X_of_isEmpty {k : ℕ}
    [IsEmpty (cell (univ : Set (ComplexProjectiveSpace n)) k)] : IsZero ((K).X k) := by
  rw [cellularChainComplex_X]
  exact isZero_cellularChainGroup _ k R

/-- The cellular chain complex of `CPⁿ` vanishes in odd degrees. -/
private lemma isZero_X_of_odd {k : ℕ} (hk : Odd k) : IsZero ((K).X k) :=
  have := isEmpty_cell_of_odd (n := n) hk
  isZero_X_of_isEmpty R

/-- **The cellular differential of `CPⁿ` vanishes.** Every differential of the cellular chain
complex of `CPⁿ` is zero: the cells of `CPⁿ` all have even dimension, so one of the two chain
groups it connects is zero. -/
@[simp]
theorem cellularChainComplex_d_eq_zero (j k : ℕ) : (K).d j k = 0 := by
  by_cases hjk : j = k + 1
  · subst hjk
    rcases Nat.even_or_odd k with hk | hk
    · exact (isZero_X_of_odd R (n := n) hk.add_one).eq_of_src _ _
    · exact (isZero_X_of_odd R (n := n) hk).eq_of_tgt _ _
  · exact (K).shape j k fun h ↦ hjk h.symm

/-- The cellular homology of `CPⁿ` in each degree is the cellular chain group, since all the
cellular differentials vanish. -/
private def cellularHomologyIsoX (k : ℕ) : (K).homology k ≅ (K).X k :=
  ((K).isoHomologyπ _ k rfl (cellularChainComplex_d_eq_zero R _ k)).symm ≪≫
    (K).iCyclesIso k _ rfl (cellularChainComplex_d_eq_zero R k _)

/-- The singular homology of `CPⁿ` in each degree is its cellular chain group, since all the
cellular differentials vanish. -/
private def singularHomologyIsoX (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
        (TopCat.of (ComplexProjectiveSpace n)) ≅ (K).X k :=
  have := finite_cwComplex (n := n)
  (cellularSingularHomologyIsoUniv R k).symm ≪≫ cellularHomologyIsoX R k

/-- **The even-degree homology of complex projective space.** For `i ≤ n`, `H₂ᵢ(CPⁿ; R) ≅ R`.
The isomorphism is the cellular–singular comparison `TauCeti.cellularSingularHomologyIsoUniv`
followed by the identification `TauCeti.cellularChainGroupIso` of the cellular chain group of the
unique `2i`-cell with `R`. -/
def singularHomologyIso {i : ℕ} (hi : i ≤ n) :
    ((AlgebraicTopology.singularHomologyFunctor A (2 * i)).obj R).obj
        (TopCat.of (ComplexProjectiveSpace n)) ≅ R :=
  letI := uniqueCell hi
  singularHomologyIsoX R (2 * i) ≪≫ eqToIso (cellularChainComplex_X _ R (2 * i)) ≪≫
    cellularChainGroupIso _ R (2 * i) ≪≫ coproductUniqueIso _

/-- **The odd-degree homology of complex projective space vanishes.** `Hₖ(CPⁿ; R) = 0` for odd
`k`. -/
theorem isZero_singularHomology_of_odd {k : ℕ} (hk : Odd k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n))) :=
  (isZero_X_of_odd R hk).of_iso (singularHomologyIsoX R k)

/-- The singular homology of `CPⁿ` vanishes above degree `2n`. -/
theorem isZero_singularHomology_of_lt {k : ℕ} (hk : 2 * n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n))) :=
  have := isEmpty_cell_of_lt (n := n) hk
  (isZero_X_of_isEmpty R).of_iso (singularHomologyIsoX R k)

end TauCeti.ComplexProjectiveSpace
