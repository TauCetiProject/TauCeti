/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.OddStructure
-- Non-public: the anisotropic orthogonal spanning list carrying the volume element, and the
-- one-dimensionality of the centre of a central algebra, are used only inside proofs.
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.Algebra.Subalgebra.Center

/-!
# The centre of an odd-dimensional Clifford algebra

In even dimension the Clifford algebra of a polarized quadratic space is the endomorphism algebra
of its spinor module, so its centre is the base field
(`TauCeti.SpinPolarizationData.isCentral_cliffordAlgebra`). In **odd** dimension that fails, and
this file measures by how much: the centre is a **rank-two** subalgebra, spanned by `1` and the
**volume element** `ω = ι Q v₁ ⋯ ι Q vₙ` of an orthogonal basis.

One inclusion is already general Clifford-algebra theory: the volume element of an orthogonal
spanning list of odd length is central
(`CliffordAlgebra.prod_map_ι_mem_center_of_odd_length`). The other is where the Fock model comes
in, after the `ℤ/2`-grading has split the problem in two: the even and the odd part of a central
element are each central (`CliffordAlgebra.mem_center_of_mem_evenOdd_of_add_mem_center`), so it is
enough to describe the central elements of each parity.

* A **central even** element is a scalar. The odd structure theorem
  `TauCeti.SpinPolarizationData.evenCliffordEquivEnd` identifies `even Q` with
  `Module.End F (⋀·W)`, whose centre is `F`, so `even Q` is a central algebra over `F`
  (`TauCeti.SpinPolarizationData.isCentral_even`). This is where odd dimension enters: in even
  dimension `even Q` is a *product* of two endomorphism algebras and has a two-dimensional centre
  instead.
* A **central odd** element is a multiple of `ω`. Multiplying by `ω` turns it into a central even
  element, hence into a scalar, and `ω * ω = c` with `c ≠ 0` lets that be divided back out.

The two halves together are
`TauCeti.SpinPolarizationData.center_toSubmodule_eq_span_prod_map_ι`, and the rank-two count it
yields, `TauCeti.SpinPolarizationData.finrank_center_eq_two`, no longer mentions the orthogonal
basis: `1` and `ω` are independent because they are nonzero and of opposite parity.

Rank two is the sharp obstruction to the even-dimensional picture, and the last section records it
as such: the odd-dimensional Clifford algebra is **not** central over `F`
(`TauCeti.SpinPolarizationData.not_isCentral_cliffordAlgebra`), since the centre of a central
algebra is one-dimensional instead (`TauCeti.finrank_center_of_isCentral`).

Which rank-two algebra the centre is turns only on the scalar
`ω * ω = (-1) ^ (n.choose 2) ∏ᵢ Q vᵢ` (`CliffordAlgebra.prod_map_ι_sq_scalar`), and under a
polarization that scalar is always a square: with `n = 2 * m + 1`, the hyperbolic part `W ⊕ W'` is
`m` copies of `⟨1, -1⟩` and so contributes `(-1) ^ m` modulo squares, the orthogonal remainder
contributes a square because `TauCeti.SpinPolarizationData.lineCoordinate_sq` makes its form the
square of a coordinate, and the sign `(-1) ^ (n.choose 2) = (-1) ^ m` cancels the first of these
against the second. A polarized odd
form is split in this sense and its centre is `F × F`, which over a separably closed field is what
the two-block splitting
`CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one` reads off. A quadratic
field *extension* arises only for an odd form admitting no polarization at all — an anisotropic one,
say: `⟨1, 1, 1⟩` over `ℚ` has `ω * ω = -1`, so its centre is `ℚ[X] / (X ^ 2 + 1)`. Either way only
the rank is claimed here, never a decomposition.

A polarization is a hypothesis throughout rather than a conclusion, exactly as in
`TauCeti/RepresentationTheory/Spin/OddStructure.lean`: over a general field a nondegenerate form
need not be split, and `TauCeti.SpinPolarizationData.ofNondegenerate` builds a polarization only
over a separably closed field. The field-level statement
`CliffordAlgebra.finrank_center_eq_two_of_odd_finrank` therefore carries `IsSepClosed`, while
everything proved from a given polarization needs nothing of the field beyond characteristic not
two.

## Main results

* `TauCeti.SpinPolarizationData.isCentral_even`: in odd dimension the even Clifford subalgebra is
  central over the base field.
* `TauCeti.SpinPolarizationData.exists_algebraMap_of_mem_even_of_mem_center`: a central element of
  even parity is a scalar.
* `TauCeti.SpinPolarizationData.center_toSubmodule_eq_span_prod_map_ι`: the centre is spanned by
  `1` and the volume element of an anisotropic orthogonal spanning list, and
  `TauCeti.SpinPolarizationData.exists_mem_evenOdd_one_center_toSubmodule_eq_span` discharges the
  choice of that list.
* `TauCeti.SpinPolarizationData.center_eq_adjoin_prod_map_ι`: the same statement as an equality of
  subalgebras, the centre being the quadratic algebra `F[ω]`.
* `TauCeti.SpinPolarizationData.finrank_center_eq_two` and
  `CliffordAlgebra.finrank_center_eq_two_of_odd_finrank`: the centre has dimension two.
* `TauCeti.SpinPolarizationData.not_isCentral_cliffordAlgebra`: an odd-dimensional Clifford algebra
  is not central over the base field.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Chapter I,
  Proposition 1.7 and Theorem 4.3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1.
-/

public section

open CliffordAlgebra Module

universe u v

namespace TauCeti.SpinPolarizationData

variable {F : Type u} [Field F] [NeZero (2 : F)]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
  (P : SpinPolarizationData Q) (hodd : Odd (finrank F V))

omit [NeZero (2 : F)] [FiniteDimensional F V] in
/-- The product of the values of a quadratic form along a list of non-isotropic vectors is nonzero.
The scalar `ω * ω` and the unitality of `ω` both need it, so it is factored out. -/
private theorem prod_map_ne_zero_of_forall {l : List V} (hQl : ∀ v ∈ l, Q v ≠ 0) :
    (l.map Q).prod ≠ 0 :=
  List.prod_ne_zero fun hmem => by
    obtain ⟨v, hv, hv0⟩ := List.mem_map.mp hmem
    exact hQl v hv hv0

include P hodd

/-! ### Central elements of even parity are scalars -/

/-- **The even subalgebra of an odd-dimensional Clifford algebra is central over the base field.**
The Fock action identifies it with the endomorphism algebra of the spinor module, whose centre is
the scalars.

This is the odd-dimensional analogue of
`TauCeti.SpinPolarizationData.isCentral_cliffordAlgebra`, one grade down, and it is false in even
dimension: there `even Q` is the product of the two half-spin endomorphism algebras
(`TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd`), with a two-dimensional centre. -/
theorem isCentral_even : Algebra.IsCentral F ↥(even Q) :=
  Algebra.IsCentral.of_algEquiv F _ _ (P.evenCliffordEquivEnd hodd).symm

/-- **A central element of even parity is a scalar**, in odd dimension. An element of `even Q`
commuting with all of `CliffordAlgebra Q` in particular commutes with all of `even Q`, so it lies
in the centre of the even subalgebra, which `TauCeti.SpinPolarizationData.isCentral_even` says is
the base field. -/
theorem exists_algebraMap_of_mem_even_of_mem_center {x : CliffordAlgebra Q} (hx : x ∈ even Q)
    (hxc : x ∈ Subalgebra.center F (CliffordAlgebra Q)) :
    ∃ a : F, x = algebraMap F (CliffordAlgebra Q) a := by
  have := P.isCentral_even hodd
  have hmem : (⟨x, hx⟩ : ↥(even Q)) ∈ Subalgebra.center F ↥(even Q) := by
    rw [Subalgebra.mem_center_iff]
    intro b
    exact Subtype.ext (Subalgebra.mem_center_iff.mp hxc (b : CliffordAlgebra Q))
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff F).1 hmem
  exact ⟨a, by simpa using congrArg (fun y : ↥(even Q) => (y : CliffordAlgebra Q)) ha⟩

/-! ### The centre is spanned by `1` and the volume element -/

/-- **The centre of an odd-dimensional Clifford algebra is spanned by `1` and the volume element.**
For a polarized quadratic space of odd dimension over a field of characteristic not two, and a list
`l` of pairwise orthogonal, non-isotropic vectors spanning `V` whose length is `finrank F V`, the
centre of `CliffordAlgebra Q` is the span of `1` and `ω = ι Q v₁ ⋯ ι Q vₙ`.

The inclusion of the span is `CliffordAlgebra.prod_map_ι_mem_center_of_odd_length`. The reverse
inclusion splits a central element into its two graded parts, which are again central
(`CliffordAlgebra.mem_center_of_mem_evenOdd_of_add_mem_center`): the even part is a scalar, and the
odd part becomes a scalar after multiplication by the odd central `ω`, which is invertible because
`ω * ω` is a nonzero scalar. -/
theorem center_toSubmodule_eq_span_prod_map_ι {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (hlen : l.length = finrank F V) (hspan : Submodule.span F {x : V | x ∈ l} = ⊤)
    (hQl : ∀ v ∈ l, Q v ≠ 0) :
    Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q)) =
      Submodule.span F {1, (l.map (ι Q)).prod} := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  set ω : CliffordAlgebra Q := (l.map (ι Q)).prod
  have hlodd : Odd l.length := hlen ▸ hodd
  have hωodd : ω ∈ evenOdd Q 1 := prod_map_ι_mem_evenOdd_one_of_odd_length hlodd
  have hωcentre : ω ∈ Subalgebra.center F (CliffordAlgebra Q) :=
    prod_map_ι_mem_center_of_odd_length hl hlodd hspan
  set c : F := (-1 : F) ^ l.length.choose 2 * (l.map Q).prod
  have hc : c ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (prod_map_ne_zero_of_forall hQl)
  have hsq : ω * ω = algebraMap F (CliffordAlgebra Q) c := prod_map_ι_sq_scalar hl
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [Subalgebra.mem_toSubmodule] at hx
    -- Split `x` into its even and its odd part; both are central.
    obtain ⟨x₀, h₀, x₁, h₁, rfl⟩ := Submodule.mem_sup.1
      (((evenOdd_isCompl (Q := Q)).sup_eq_top).ge Submodule.mem_top :
        x ∈ evenOdd Q 0 ⊔ evenOdd Q 1)
    obtain ⟨hx₀, hx₁⟩ := mem_center_of_mem_evenOdd_of_add_mem_center h₀ h₁ hx
    -- The even part is a scalar.
    obtain ⟨a, ha⟩ := P.exists_algebraMap_of_mem_even_of_mem_center hodd
      (by rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule]) hx₀
    -- Multiplying the odd part by `ω` makes it even and central, hence a scalar.
    have hmul : x₁ * ω ∈ even Q := by
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
      have h := SetLike.mul_mem_graded h₁ hωodd
      rwa [CharTwo.add_self_eq_zero] at h
    obtain ⟨b, hb⟩ := P.exists_algebraMap_of_mem_even_of_mem_center hodd hmul
      (Subalgebra.mul_mem _ hx₁ hωcentre)
    have hkey : algebraMap F (CliffordAlgebra Q) c * x₁ =
        algebraMap F (CliffordAlgebra Q) b * ω := by
      rw [Algebra.commutes, ← hsq, ← mul_assoc, hb]
    have hx₁eq : x₁ = (c⁻¹ * b) • ω := by
      have hsmul : c • x₁ = b • ω := by
        simpa [Algebra.smul_def] using hkey
      rw [mul_smul, ← hsmul, inv_smul_smul₀ hc]
    rw [ha, hx₁eq, Algebra.algebraMap_eq_smul_one]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact Subalgebra.one_mem _
    · exact hωcentre

/-- **The centre of an odd-dimensional Clifford algebra is the subalgebra generated by the volume
element.** The subalgebra form of
`TauCeti.SpinPolarizationData.center_toSubmodule_eq_span_prod_map_ι`: since `ω * ω` is a scalar, the
span of `1` and `ω` is already closed under multiplication, so the centre is `F[ω]`, a quadratic
algebra over `F`.

Which quadratic algebra it is is already settled by the polarization: `ω * ω` is the scalar
`(-1) ^ (n.choose 2) ∏ᵢ Q vᵢ` (`CliffordAlgebra.prod_map_ι_sq_scalar`), a polarized odd form is
split, and so that scalar is a square and `F[ω]` is `F × F`. A quadratic field extension can occur
only for an odd form carrying no polarization; see the module docstring. -/
theorem center_eq_adjoin_prod_map_ι {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (hlen : l.length = finrank F V) (hspan : Submodule.span F {x : V | x ∈ l} = ⊤)
    (hQl : ∀ v ∈ l, Q v ≠ 0) :
    Subalgebra.center F (CliffordAlgebra Q) = Algebra.adjoin F {(l.map (ι Q)).prod} := by
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le (Set.singleton_subset_iff.mpr
    (prod_map_ι_mem_center_of_odd_length hl (hlen ▸ hodd) hspan)))
  have hmem : x ∈ Submodule.span F {(1 : CliffordAlgebra Q), (l.map (ι Q)).prod} := by
    rw [← P.center_toSubmodule_eq_span_prod_map_ι hodd hl hlen hspan hQl]
    exact hx
  have hle : Submodule.span F {(1 : CliffordAlgebra Q), (l.map (ι Q)).prod} ≤
      Subalgebra.toSubmodule (Algebra.adjoin F {(l.map (ι Q)).prod}) := by
    rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact Subalgebra.one_mem _
    · exact Algebra.self_mem_adjoin_singleton F _
  exact hle hmem

/-! ### The centre has dimension two -/

/-- **The centre of an odd-dimensional Clifford algebra is spanned by `1` and a nonzero odd
element.** This is
`TauCeti.SpinPolarizationData.center_toSubmodule_eq_span_prod_map_ι` with the choice of orthogonal
basis discharged: the witness is the volume element of an anisotropic orthogonal basis, which
exists because a polarized quadratic form is nondegenerate, and which is nonzero because it is a
unit (`CliffordAlgebra.isUnit_prod_map_ι`).

The two recorded properties of the witness are what the centre's size and the failure of centrality
both rest on: being odd and nonzero, it is not a scalar. -/
theorem exists_mem_evenOdd_one_center_toSubmodule_eq_span :
    ∃ ω : CliffordAlgebra Q, ω ∈ evenOdd Q 1 ∧ ω ≠ 0 ∧
      Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q)) =
        Submodule.span F {1, ω} := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have _ : Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial
  obtain ⟨l, hl, hlen, hspan, hQl⟩ :=
    (P.nondegenerate ((isUnit_of_invertible (2 : F)).isSMulRegular F)).exists_list_pairwise_isOrtho
  refine ⟨(l.map (ι Q)).prod,
    prod_map_ι_mem_evenOdd_one_of_odd_length (hlen ▸ hodd), ?_,
    P.center_toSubmodule_eq_span_prod_map_ι hodd hl hlen hspan hQl⟩
  intro hzero
  exact zero_ne_one (isUnit_zero_iff.mp
    (hzero ▸ isUnit_prod_map_ι (isUnit_iff_ne_zero.mpr (prod_map_ne_zero_of_forall hQl))))

/-- **The centre of an odd-dimensional Clifford algebra has dimension two over the base field.**
It is spanned by `1` and the volume element of an orthogonal basis, and the two are linearly
independent: `1` is even, the volume element is odd, and the two graded pieces meet only in `0`, so
a vanishing combination has both of its terms zero, while both spanning vectors are nonzero.

Unlike `TauCeti.SpinPolarizationData.center_toSubmodule_eq_span_prod_map_ι`, this statement
mentions neither a choice of orthogonal basis nor the volume element. -/
theorem finrank_center_eq_two :
    finrank F ↥(Subalgebra.center F (CliffordAlgebra Q)) = 2 := by
  have _ : Nontrivial (CliffordAlgebra Q) := by
    have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
    exact (equivExterior Q).symm.injective.nontrivial
  obtain ⟨ω, hωodd, hω0, hspan⟩ := P.exists_mem_evenOdd_one_center_toSubmodule_eq_span hodd
  have hli : LinearIndependent F ![(1 : CliffordAlgebra Q), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t • ω ∈ evenOdd Q 1 := Submodule.smul_mem _ _ hωodd
    have hboth : s • (1 : CliffordAlgebra Q) ∈ evenOdd Q 0 ⊓ evenOdd Q 1 :=
      ⟨Submodule.smul_mem _ _ (one_le_evenOdd_zero Q (Submodule.mem_one.mpr ⟨1, by simp⟩)),
        by rw [eq_neg_of_add_eq_zero_left hst]; exact Submodule.neg_mem _ ht⟩
    rw [(evenOdd_isCompl (Q := Q)).inf_eq_bot, Submodule.mem_bot] at hboth
    have hs0 : s = 0 := by simpa using hboth
    refine ⟨hs0, ?_⟩
    rw [hs0, zero_smul, zero_add, smul_eq_zero] at hst
    exact hst.resolve_right hω0
  have hfin : finrank F
      ↥(Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q))) = 2 := by
    rw [hspan, ← Matrix.range_cons_cons_empty (1 : CliffordAlgebra Q) ω Matrix.vecEmpty,
      finrank_span_eq_card hli, Fintype.card_fin]
  exact hfin

/-! ### The odd-dimensional Clifford algebra is not central -/

/-- **An odd-dimensional Clifford algebra is not central over the base field.** Its centre is
two-dimensional (`TauCeti.SpinPolarizationData.finrank_center_eq_two`), whereas the centre of a
central algebra is the base field and hence one-dimensional
(`TauCeti.finrank_center_of_isCentral`).

This is the sharp contrast with the even-dimensional
`TauCeti.SpinPolarizationData.isCentral_cliffordAlgebra`, and the reason the odd-dimensional
structure theorem produces a *product* of two matrix algebras rather than a single one. -/
theorem not_isCentral_cliffordAlgebra : ¬ Algebra.IsCentral F (CliffordAlgebra Q) := by
  intro _
  have _ : Nontrivial (CliffordAlgebra Q) := by
    have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
    exact (equivExterior Q).symm.injective.nontrivial
  have h : 2 = 1 :=
    (P.finrank_center_eq_two hodd).symm.trans (finrank_center_of_isCentral F (CliffordAlgebra Q))
  omega

end TauCeti.SpinPolarizationData

namespace CliffordAlgebra

open TauCeti

variable {F : Type u} [Field F] [NeZero (2 : F)]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-- **The centre of an odd-dimensional Clifford algebra is two-dimensional**, over a separably
closed field of characteristic not two and for a nondegenerate form. This is the field-level form
of `TauCeti.SpinPolarizationData.finrank_center_eq_two`: separable closedness is used only to
produce a polarization, through
`TauCeti.SpinPolarizationData.ofNondegenerate`.

The two-block splitting
`CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one` reads this centre as
`F × F`; over a general field it can instead be a quadratic field extension, according to whether
the square of the volume element is a square in `F` — which for a form carrying a polarization it
always is, so this happens only where `TauCeti.SpinPolarizationData.ofNondegenerate` does not
apply. -/
theorem finrank_center_eq_two_of_odd_finrank [IsSepClosed F] (hQ : Q.Nondegenerate)
    (hodd : Odd (finrank F V)) :
    finrank F ↥(Subalgebra.center F (CliffordAlgebra Q)) = 2 :=
  (SpinPolarizationData.ofNondegenerate Q hQ).finrank_center_eq_two hodd

end CliffordAlgebra
