/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.OddStructure
-- Non-public: the anisotropic orthogonal spanning list carrying the volume element, the fact that
-- a spanning family of the right size is a basis, the one-dimensionality of the centre of a central
-- algebra, and the base change of a nondegenerate form to a separable closure, are used only inside
-- proofs.
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# The centre of an odd-dimensional Clifford algebra

In even dimension the Clifford algebra of a polarized quadratic space is the endomorphism algebra
of its spinor module, so its centre is the base field
(`TauCeti.SpinPolarizationData.isCentral_cliffordAlgebra`). In **odd** dimension that fails, and
this file measures by how much: for a nondegenerate quadratic form over a field of characteristic
not two the centre is a **rank-two** subalgebra, spanned by `1` and the **volume element**
`ω = ι Q v₁ ⋯ ι Q vₙ` of an anisotropic orthogonal basis. Nothing of the field beyond
characteristic not two, and no polarization, is assumed: a `TauCeti.SpinPolarizationData` appears
only inside the proofs, where it is available after base change to a separable closure.

Rank two is the sharp obstruction to the even-dimensional picture, and one section records it as
such: the odd-dimensional Clifford algebra is **not** central over `F`
(`CliffordAlgebra.not_isCentral_of_odd_finrank`), since the centre of a central algebra is
one-dimensional instead (`TauCeti.finrank_center_of_isCentral`).

## The two bounds on the rank

Two is a lower bound with no polarization in sight: the volume element of an orthogonal spanning
list of odd length is central (`CliffordAlgebra.prod_map_ι_mem_center_of_odd_length`) and, the
basis being anisotropic, a unit; so `1` and `ω` lie in the two complementary halves of the
`ℤ/2`-grading, are therefore independent, and span two dimensions of the centre.

Two is an upper bound by descent from a separable closure `L`, where
`TauCeti.SpinPolarizationData.ofNondegenerate` does build a polarization:
`QuadraticForm.Nondegenerate.baseChange` keeps `Q.baseChange L` nondegenerate,
`Module.finrank_baseChange` keeps the dimension odd, and the base change to `L` of the centre
embeds `L`-linearly in the centre of `L ⊗[F] CliffordAlgebra Q ≃ₐ[L] CliffordAlgebra (Q.baseChange
L)` (Mathlib's `CliffordAlgebra.equivBaseChange`), so a centre of rank three or more over `F` would
force one over `L`.

Over `L` the count is the Fock model's, and the `ℤ/2`-grading splits the work in two: the even and
the odd part of a central element are each central
(`CliffordAlgebra.mem_center_of_mem_evenOdd_of_add_mem_center`), so it is enough to describe the
central elements of each parity.

* A **central even** element is a scalar. The odd structure theorem
  `TauCeti.SpinPolarizationData.evenCliffordEquivEnd` identifies `even Q` with
  `Module.End F (⋀·W)`, whose centre is `F`, so `even Q` is a central algebra over `F`. This is
  where odd dimension enters: in even dimension `even Q` is a *product* of two endomorphism
  algebras and has a two-dimensional centre instead.
* A **central odd** element is a multiple of `ω`. Multiplying by `ω` turns it into a central even
  element, hence into a scalar, and `ω * ω = c` with `c ≠ 0` lets that be divided back out.

## From the rank back to the span

The count is sharp enough to recover the span description over the base field, with no polarization
left: the span of `1` and `ω` sits inside the centre and both are two-dimensional, so they are
equal (`CliffordAlgebra.center_toSubmodule_eq_span_prod_map_ι`). The two conclusions that the
polarized argument reached directly follow in turn — a central element of even parity is a scalar
(`CliffordAlgebra.exists_algebraMap_of_mem_even_of_mem_center`), since the odd coordinate of an even
element vanishes, and `even Q` is itself central over `F` (`CliffordAlgebra.isCentral_even`), since
every odd element is `ω` times an even one.

## Which rank-two algebra

Which rank-two algebra the centre is turns only on the scalar
`ω * ω = (-1) ^ (n.choose 2) ∏ᵢ Q vᵢ` (`CliffordAlgebra.prod_map_ι_sq_scalar`), and under a
polarization that scalar is always a square: with `n = 2 * m + 1`, the hyperbolic part `W ⊕ W'` is
`m` copies of `⟨1, -1⟩` and so contributes `(-1) ^ m` modulo squares, the orthogonal remainder
contributes a square because `TauCeti.SpinPolarizationData.lineCoordinate_sq` makes its form the
square of a coordinate, and the sign `(-1) ^ (n.choose 2) = (-1) ^ m` cancels the first of these
against the second. A polarized odd form is split in this sense and its centre is `F × F`, which
over a separably closed field is what the two-block splitting
`CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one` reads off. A quadratic
field *extension* arises only for an odd form admitting no polarization at all, `⟨1, 1, 1⟩` over `ℚ`
for instance: there `ω * ω = -1`, so the centre is `ℚ[X] / (X ^ 2 + 1)`. Either way only the rank
is claimed here, never a decomposition.

## Main results

* `CliffordAlgebra.finrank_center_eq_two_of_odd_finrank`: the centre has dimension two.
* `CliffordAlgebra.center_toSubmodule_eq_span_prod_map_ι`: the centre is spanned by `1` and the
  volume element of an orthogonal spanning list, and
  `CliffordAlgebra.exists_mem_evenOdd_one_center_toSubmodule_eq_span` discharges the choice of that
  list.
* `CliffordAlgebra.center_eq_adjoin_prod_map_ι`: the same statement as an equality of subalgebras,
  the centre being the quadratic algebra `F[ω]`.
* `CliffordAlgebra.exists_algebraMap_of_mem_even_of_mem_center`: a central element of even parity
  is a scalar, and `CliffordAlgebra.isCentral_even`: the even subalgebra is central over the base
  field.
* `CliffordAlgebra.not_isCentral_of_odd_finrank`: an odd-dimensional Clifford algebra is not
  central over the base field.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Chapter I,
  Proposition 1.7 and Theorem 4.3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1.
-/

public section

open CliffordAlgebra Module
open scoped TensorProduct

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

omit [FiniteDimensional F V] in
/-- **A pairwise orthogonal spanning list of length the dimension of a nondegenerate quadratic
space is anisotropic.** This is the given-list counterpart of
`QuadraticMap.Nondegenerate.exists_orthogonal_basis`, which instead produces a basis of its own: it
lets the theorems below take anisotropy of a supplied orthogonal basis for free rather than assume
it. Such a list is a basis, and an isotropic member of it would be orthogonal to every member,
hence to all of `V`, hence zero. -/
private theorem apply_ne_zero_of_pairwise_isOrtho (hQ : Q.Nondegenerate) {l : List V}
    (hl : l.Pairwise Q.IsOrtho) (hlen : l.length = finrank F V)
    (hspan : Submodule.span F {x : V | x ∈ l} = ⊤) : ∀ v ∈ l, Q v ≠ 0 := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have hrange : Set.range (fun i : Fin l.length => l[(i : ℕ)]) = {x : V | x ∈ l} := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨i, rfl⟩
      exact List.getElem_mem _
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exact ⟨⟨i, hi⟩, rfl⟩
  -- A spanning list of length the dimension is a basis, so none of its members is zero.
  have hli : LinearIndependent F (fun i : Fin l.length => l[(i : ℕ)]) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (hrange ▸ hspan.ge)
      (by simpa using hlen)
  rw [List.pairwise_iff_getElem] at hl
  intro v hv hv0
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  -- An isotropic member is orthogonal to every member of the list, hence to its span.
  refine hQ.polarBilin_ne_zero (by simpa using hli.ne_zero ⟨i, hi⟩)
    (LinearMap.ext_on hspan fun w hw => ?_)
  by_cases hwv : w = l[i]
  · subst hwv
    simp [QuadraticMap.polar_self, hv0]
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    rcases (Ne.lt_or_gt fun h : i = j => hwv (by cases h; rfl)) with hij | hij
    · simpa using (hl i j hi hj hij).polar_eq_zero
    · simpa [QuadraticMap.polar_comm] using (hl j i hj hi hij).polar_eq_zero

omit [FiniteDimensional F V] in
/-- The span of `1` and a nonzero element of odd parity is two-dimensional. The two elements lie in
the two complementary halves of the `ℤ/2`-grading, so neither is a multiple of the other; both rank
counts of the centre below consume this. -/
private theorem finrank_span_one_eq_two {ω : CliffordAlgebra Q} (hωodd : ω ∈ evenOdd Q 1)
    (hω0 : ω ≠ 0) : finrank F ↥(Submodule.span F {(1 : CliffordAlgebra Q), ω}) = 2 := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
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
  rw [← Matrix.range_cons_cons_empty (1 : CliffordAlgebra Q) ω Matrix.vecEmpty,
    finrank_span_eq_card hli, Fintype.card_fin]

include P hodd

/-! ### The Fock-model count, for a polarized form

Everything in this section assumes a polarization, which is what makes the Fock model available.
It is the engine of the rank count below and nothing more: the statements it proves reappear over
an arbitrary field, with no polarization, in the `CliffordAlgebra` namespace. -/

/-- The even subalgebra of a polarized odd-dimensional quadratic space is central over the base
field: the odd structure theorem identifies it with an endomorphism algebra. -/
private theorem isCentral_even : Algebra.IsCentral F ↥(even Q) :=
  Algebra.IsCentral.of_algEquiv F _ _ (P.evenCliffordEquivEnd hodd).symm

/-- A central element of even parity is a scalar: commuting with all of `CliffordAlgebra Q`
restricts to commuting with all of `even Q`, whose centre `isCentral_even` identifies with the base
field. -/
private theorem exists_algebraMap_of_mem_even_of_mem_center {x : CliffordAlgebra Q}
    (hx : x ∈ even Q) (hxc : x ∈ Subalgebra.center F (CliffordAlgebra Q)) :
    ∃ a : F, x = algebraMap F (CliffordAlgebra Q) a := by
  have := isCentral_even P hodd
  have hmem : (⟨x, hx⟩ : ↥(even Q)) ∈ Subalgebra.center F ↥(even Q) := by
    rw [Subalgebra.mem_center_iff]
    intro b
    exact Subtype.ext (Subalgebra.mem_center_iff.mp hxc (b : CliffordAlgebra Q))
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff F).1 hmem
  exact ⟨a, by simpa using congrArg (fun y : ↥(even Q) => (y : CliffordAlgebra Q)) ha⟩

/-- The centre of a polarized odd-dimensional Clifford algebra is spanned by `1` and the volume
element of an orthogonal spanning list. -/
private theorem center_toSubmodule_eq_span_prod_map_ι {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (hlen : l.length = finrank F V) (hspan : Submodule.span F {x : V | x ∈ l} = ⊤) :
    Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q)) =
      Submodule.span F {1, (l.map (ι Q)).prod} := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have hQl : ∀ v ∈ l, Q v ≠ 0 := apply_ne_zero_of_pairwise_isOrtho
    (P.nondegenerate ((isUnit_of_invertible (2 : F)).isSMulRegular F)) hl hlen hspan
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
    obtain ⟨a, ha⟩ := exists_algebraMap_of_mem_even_of_mem_center P hodd
      (by rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule]) hx₀
    -- Multiplying the odd part by `ω` makes it even and central, hence a scalar.
    have hmul : x₁ * ω ∈ even Q := by
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
      have h := SetLike.mul_mem_graded h₁ hωodd
      rwa [CharTwo.add_self_eq_zero] at h
    obtain ⟨b, hb⟩ := exists_algebraMap_of_mem_even_of_mem_center P hodd hmul
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

/-- The centre of a polarized odd-dimensional Clifford algebra has dimension two: it is the span of
`1` and the volume element of an anisotropic orthogonal basis, which is a unit and of odd parity,
hence independent of `1`. -/
private theorem finrank_center_eq_two :
    finrank F ↥(Subalgebra.center F (CliffordAlgebra Q)) = 2 := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have _ : Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial
  obtain ⟨l, hl, hlen, hspan, hQl⟩ :=
    (P.nondegenerate ((isUnit_of_invertible (2 : F)).isSMulRegular F)).exists_list_pairwise_isOrtho
  have hω0 : (l.map (ι Q)).prod ≠ 0 := fun hzero => zero_ne_one (isUnit_zero_iff.mp
    (hzero ▸ isUnit_prod_map_ι (isUnit_iff_ne_zero.mpr (prod_map_ne_zero_of_forall hQl))))
  have hfin : finrank F
      ↥(Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q))) = 2 := by
    rw [center_toSubmodule_eq_span_prod_map_ι P hodd hl hlen hspan]
    exact finrank_span_one_eq_two (prod_map_ι_mem_evenOdd_one_of_odd_length (hlen ▸ hodd)) hω0
  exact hfin

end TauCeti.SpinPolarizationData

namespace CliffordAlgebra

open TauCeti

variable {F : Type u} [Field F] [NeZero (2 : F)]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-! ### The centre has dimension two -/

section Extension

variable [Invertible (2 : F)]

omit [NeZero (2 : F)] in
/-- The centre of the Clifford algebra of a nondegenerate form of odd dimension is at most
two-dimensional, as witnessed over a separably closed extension field. -/
private theorem finrank_center_le_two_of_isSepClosed {L : Type u} [Field L] [Algebra F L]
    [NeZero (2 : L)] [IsSepClosed L] (hQ : Q.Nondegenerate) (hodd : Odd (finrank F V)) :
    finrank F ↥(Subalgebra.center F (CliffordAlgebra Q)) ≤ 2 := by
  -- Over `L` the base-changed form is nondegenerate and carries a polarization, so its centre is
  -- two-dimensional.
  have hQL : (Q.baseChange L).Nondegenerate := QuadraticForm.Nondegenerate.baseChange hQ
  have hoddL : Odd (finrank L (L ⊗[F] V)) :=
    (Module.finrank_baseChange (R := L) (S := F) (M' := V)) ▸ hodd
  have h : finrank L ↥(Subalgebra.center L (CliffordAlgebra (Q.baseChange L))) = 2 :=
    SpinPolarizationData.finrank_center_eq_two
      (SpinPolarizationData.ofNondegenerate (Q.baseChange L) hQL) hoddL
  have h2 : finrank L ↥(Subalgebra.center L (L ⊗[F] CliffordAlgebra Q)) = 2 := by
    rw [← h]
    exact ((centerCongr (equivBaseChange L Q)).toLinearEquiv.finrank_eq).symm
  -- The base change of the centre of `CliffordAlgebra Q` embeds in the centre of `L ⊗[F] Cℓ(Q)`.
  set C : Submodule F (CliffordAlgebra Q) :=
    Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q))
  set f : (L ⊗[F] ↥C) →ₗ[L] (L ⊗[F] CliffordAlgebra Q) := LinearMap.baseChange L C.subtype with hf
  have hinj : Function.Injective f := by
    rw [hf, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype C)
  have hrange : LinearMap.range f ≤
      Subalgebra.toSubmodule (Subalgebra.center L (L ⊗[F] CliffordAlgebra Q)) := by
    rintro x ⟨y, rfl⟩
    induction y with
    | tmul a c =>
        rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff]
        intro b
        induction b with
        | tmul a' b' =>
            have hc : (c : CliffordAlgebra Q) ∈ Subalgebra.center F (CliffordAlgebra Q) := by
              simp
            have hcb : (b' : CliffordAlgebra Q) * (c : CliffordAlgebra Q) =
                (c : CliffordAlgebra Q) * b' := Subalgebra.mem_center_iff.mp hc b'
            simp only [hf, LinearMap.baseChange_tmul, Submodule.subtype_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_comm a' a, hcb]
        | add p q hp hq => simp [mul_add, add_mul, hp, hq]
    | add p q hp hq => simp only [map_add]; exact Submodule.add_mem _ hp hq
  calc finrank F ↥C = finrank L (L ⊗[F] ↥C) := Module.finrank_baseChange.symm
    _ = finrank L ↥(LinearMap.range f) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ finrank L ↥(Subalgebra.toSubmodule (Subalgebra.center L (L ⊗[F] CliffordAlgebra Q))) :=
        Submodule.finrank_mono hrange
    _ = 2 := h2

end Extension

/-- The centre of the Clifford algebra of a nondegenerate form of odd dimension is at least
two-dimensional: it contains `1` and the volume element of an anisotropic orthogonal basis. -/
private theorem two_le_finrank_center (hQ : Q.Nondegenerate) (hodd : Odd (finrank F V)) :
    2 ≤ finrank F ↥(Subalgebra.center F (CliffordAlgebra Q)) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have _ : Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial
  obtain ⟨l, hl, hlen, hspan, hQl⟩ := hQ.exists_list_pairwise_isOrtho
  set ω : CliffordAlgebra Q := (l.map (ι Q)).prod
  have hωodd : ω ∈ evenOdd Q 1 := prod_map_ι_mem_evenOdd_one_of_odd_length (hlen ▸ hodd)
  have hωc : ω ∈ Subalgebra.center F (CliffordAlgebra Q) :=
    prod_map_ι_mem_center_of_odd_length hl (hlen ▸ hodd) hspan
  have hunit : IsUnit ω := isUnit_prod_map_ι
    (isUnit_iff_ne_zero.mpr (SpinPolarizationData.prod_map_ne_zero_of_forall hQl))
  have hω0 : ω ≠ 0 := fun hzero => zero_ne_one (isUnit_zero_iff.mp (hzero ▸ hunit))
  have hle : Submodule.span F {(1 : CliffordAlgebra Q), ω} ≤
      Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q)) := by
    rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact Subalgebra.one_mem _
    · exact hωc
  calc 2 = finrank F ↥(Submodule.span F {(1 : CliffordAlgebra Q), ω}) :=
        (SpinPolarizationData.finrank_span_one_eq_two hωodd hω0).symm
    _ ≤ finrank F ↥(Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q))) :=
        Submodule.finrank_mono hle

/-- **The centre of an odd-dimensional Clifford algebra is two-dimensional**, over any field of
characteristic not two and for a nondegenerate form. Two is a lower bound because `1` and the
volume element of an anisotropic orthogonal basis are independent, and an upper bound by descent
from a separable closure, where a polarization makes the Fock model available.

Which rank-two algebra the centre is depends on the field: over a separably closed field, where
`CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one` reads it off as the
two blocks of the odd structure theorem, it is `F × F`, while for a form whose volume element has
a non-square square — `⟨1, 1, 1⟩` over `ℚ`, where `ω * ω = -1` — it is a quadratic field
extension. -/
theorem finrank_center_eq_two_of_odd_finrank (hQ : Q.Nondegenerate)
    (hodd : Odd (finrank F V)) :
    finrank F ↥(Subalgebra.center F (CliffordAlgebra Q)) = 2 := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  -- A separable closure of `F` is a field of characteristic not two over which `Q` is polarizable.
  have h2 : (2 : SeparableClosure F) ≠ 0 := by
    have h : (algebraMap F (SeparableClosure F)) 2 = 2 := map_ofNat _ 2
    rw [← h]
    exact (map_ne_zero_iff _ (algebraMap F (SeparableClosure F)).injective).2 (NeZero.ne (2 : F))
  have _ : NeZero (2 : SeparableClosure F) := ⟨h2⟩
  exact le_antisymm (finrank_center_le_two_of_isSepClosed (L := SeparableClosure F) hQ hodd)
    (two_le_finrank_center hQ hodd)

/-! ### The centre is spanned by `1` and the volume element -/

/-- **The centre of an odd-dimensional Clifford algebra is spanned by `1` and the volume element.**
For a nondegenerate quadratic form of odd dimension over a field of characteristic not two, and a
list `l` of pairwise orthogonal vectors spanning `V` whose length is `finrank F V`, the centre of
`CliffordAlgebra Q` is the span of `1` and `ω = ι Q v₁ ⋯ ι Q vₙ`. -/
theorem center_toSubmodule_eq_span_prod_map_ι (hQ : Q.Nondegenerate) (hodd : Odd (finrank F V))
    {l : List V} (hl : l.Pairwise Q.IsOrtho) (hlen : l.length = finrank F V)
    (hspan : Submodule.span F {x : V | x ∈ l} = ⊤) :
    Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q)) =
      Submodule.span F {1, (l.map (ι Q)).prod} := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have _ : Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial
  have hQl : ∀ v ∈ l, Q v ≠ 0 :=
    SpinPolarizationData.apply_ne_zero_of_pairwise_isOrtho hQ hl hlen hspan
  have hω0 : (l.map (ι Q)).prod ≠ 0 := fun hzero => zero_ne_one (isUnit_zero_iff.mp
    (hzero ▸ isUnit_prod_map_ι
      (isUnit_iff_ne_zero.mpr (SpinPolarizationData.prod_map_ne_zero_of_forall hQl))))
  have hle : Submodule.span F {(1 : CliffordAlgebra Q), (l.map (ι Q)).prod} ≤
      Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q)) := by
    rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact Subalgebra.one_mem _
    · exact prod_map_ι_mem_center_of_odd_length hl (hlen ▸ hodd) hspan
  -- Both submodules are two-dimensional — the span because `1` and `ω` have opposite parity, the
  -- centre by the rank count — so the inclusion is an equality.
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [SpinPolarizationData.finrank_span_one_eq_two
    (prod_map_ι_mem_evenOdd_one_of_odd_length (hlen ▸ hodd)) hω0]
  exact (finrank_center_eq_two_of_odd_finrank hQ hodd).symm

/-- **The centre of an odd-dimensional Clifford algebra is the subalgebra generated by the volume
element.** The subalgebra form of `CliffordAlgebra.center_toSubmodule_eq_span_prod_map_ι`, the
centre being the quadratic algebra `F[ω]` over `F`.

Which quadratic algebra it is depends on the field; see the module docstring. -/
theorem center_eq_adjoin_prod_map_ι (hQ : Q.Nondegenerate) (hodd : Odd (finrank F V))
    {l : List V} (hl : l.Pairwise Q.IsOrtho) (hlen : l.length = finrank F V)
    (hspan : Submodule.span F {x : V | x ∈ l} = ⊤) :
    Subalgebra.center F (CliffordAlgebra Q) = Algebra.adjoin F {(l.map (ι Q)).prod} := by
  -- Since `ω * ω` is a scalar, the span of `1` and `ω` is already closed under multiplication, so
  -- the span description of the centre suffices.
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le (Set.singleton_subset_iff.mpr
    (prod_map_ι_mem_center_of_odd_length hl (hlen ▸ hodd) hspan)))
  have hmem : x ∈ Submodule.span F {(1 : CliffordAlgebra Q), (l.map (ι Q)).prod} := by
    rw [← center_toSubmodule_eq_span_prod_map_ι hQ hodd hl hlen hspan]
    exact hx
  have hle : Submodule.span F {(1 : CliffordAlgebra Q), (l.map (ι Q)).prod} ≤
      Subalgebra.toSubmodule (Algebra.adjoin F {(l.map (ι Q)).prod}) := by
    rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact Subalgebra.one_mem _
    · exact Algebra.self_mem_adjoin_singleton F _
  exact hle hmem

/-- **The centre of an odd-dimensional Clifford algebra is spanned by `1` and a nonzero odd
element.** This is `CliffordAlgebra.center_toSubmodule_eq_span_prod_map_ι` with the choice of
orthogonal basis discharged: the witness is the volume element of an anisotropic orthogonal basis,
which is a unit. It is the form of the statement that the two conclusions below consume. -/
theorem exists_mem_evenOdd_one_center_toSubmodule_eq_span (hQ : Q.Nondegenerate)
    (hodd : Odd (finrank F V)) :
    ∃ ω : CliffordAlgebra Q, ω ∈ evenOdd Q 1 ∧ ω ≠ 0 ∧
      Subalgebra.toSubmodule (Subalgebra.center F (CliffordAlgebra Q)) =
        Submodule.span F {1, ω} := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have _ : Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial
  obtain ⟨l, hl, hlen, hspan, hQl⟩ := hQ.exists_list_pairwise_isOrtho
  refine ⟨(l.map (ι Q)).prod,
    prod_map_ι_mem_evenOdd_one_of_odd_length (hlen ▸ hodd), ?_,
    center_toSubmodule_eq_span_prod_map_ι hQ hodd hl hlen hspan⟩
  intro hzero
  exact zero_ne_one (isUnit_zero_iff.mp
    (hzero ▸ isUnit_prod_map_ι
      (isUnit_iff_ne_zero.mpr (SpinPolarizationData.prod_map_ne_zero_of_forall hQl))))

/-! ### Central elements of even parity are scalars -/

/-- **A central element of even parity is a scalar**, in odd dimension. In the span description of
the centre an even element has no room for a multiple of the odd volume element, so only the scalar
coordinate survives. -/
theorem exists_algebraMap_of_mem_even_of_mem_center (hQ : Q.Nondegenerate)
    (hodd : Odd (finrank F V)) {x : CliffordAlgebra Q} (hx : x ∈ even Q)
    (hxc : x ∈ Subalgebra.center F (CliffordAlgebra Q)) :
    ∃ a : F, x = algebraMap F (CliffordAlgebra Q) a := by
  obtain ⟨ω, hωodd, hω0, hspan⟩ := exists_mem_evenOdd_one_center_toSubmodule_eq_span hQ hodd
  have hmem : x ∈ Submodule.span F {(1 : CliffordAlgebra Q), ω} := by
    rw [← hspan, Subalgebra.mem_toSubmodule]
    exact hxc
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  have hx0 : x ∈ evenOdd Q 0 := by rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hx
  -- The odd coordinate lies in both halves of the grading, hence vanishes.
  have hbω : b • ω = 0 := by
    have h1 : a • (1 : CliffordAlgebra Q) ∈ evenOdd Q 0 :=
      Submodule.smul_mem _ _ (one_le_evenOdd_zero Q (Submodule.mem_one.mpr ⟨1, by simp⟩))
    have heq : b • ω = x - a • (1 : CliffordAlgebra Q) := by rw [← hab]; abel
    have hboth : b • ω ∈ evenOdd Q 0 ⊓ evenOdd Q 1 :=
      ⟨by rw [heq]; exact Submodule.sub_mem _ hx0 h1, Submodule.smul_mem _ _ hωodd⟩
    rwa [(evenOdd_isCompl (Q := Q)).inf_eq_bot, Submodule.mem_bot] at hboth
  exact ⟨a, by rw [← hab, hbω, add_zero, Algebra.algebraMap_eq_smul_one]⟩

/-- **The even subalgebra of an odd-dimensional Clifford algebra is central over the base field.**
This is the odd-dimensional analogue of
`TauCeti.SpinPolarizationData.isCentral_cliffordAlgebra`, one grade down, and it is false in even
dimension: there `even Q` is the product of the two half-spin endomorphism algebras
(`TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd`), with a two-dimensional centre. -/
theorem isCentral_even (hQ : Q.Nondegenerate) (hodd : Odd (finrank F V)) :
    Algebra.IsCentral F ↥(even Q) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  obtain ⟨l, hl, hlen, hspan, hQl⟩ := hQ.exists_list_pairwise_isOrtho
  have hωodd : (l.map (ι Q)).prod ∈ evenOdd Q 1 :=
    prod_map_ι_mem_evenOdd_one_of_odd_length (hlen ▸ hodd)
  have hωc : (l.map (ι Q)).prod ∈ Subalgebra.center F (CliffordAlgebra Q) :=
    prod_map_ι_mem_center_of_odd_length hl (hlen ▸ hodd) hspan
  have hsq : (l.map (ι Q)).prod * (l.map (ι Q)).prod = algebraMap F (CliffordAlgebra Q)
      ((-1 : F) ^ l.length.choose 2 * (l.map Q).prod) := prod_map_ι_sq_scalar hl
  have hc : (-1 : F) ^ l.length.choose 2 * (l.map Q).prod ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (SpinPolarizationData.prod_map_ne_zero_of_forall hQl)
  set ω : CliffordAlgebra Q := (l.map (ι Q)).prod
  set c : F := (-1 : F) ^ l.length.choose 2 * (l.map Q).prod
  refine ⟨fun z hz => ?_⟩
  have heven : ∀ w ∈ even Q, w * (z : CliffordAlgebra Q) = (z : CliffordAlgebra Q) * w := by
    intro w hw
    exact congrArg Subtype.val (Subalgebra.mem_center_iff.mp hz ⟨w, hw⟩)
  -- `z` commutes with `even Q` by assumption and with the central `ω`. Every odd element becomes
  -- even after multiplication by `ω`, and `ω * ω` is an invertible scalar, so `z` commutes with
  -- the odd part too and is central in all of `CliffordAlgebra Q`.
  have hzc : (z : CliffordAlgebra Q) ∈ Subalgebra.center F (CliffordAlgebra Q) := by
    rw [Subalgebra.mem_center_iff]
    intro y
    obtain ⟨y₀, h₀, y₁, h₁, rfl⟩ := Submodule.mem_sup.1
      (((evenOdd_isCompl (Q := Q)).sup_eq_top).ge Submodule.mem_top :
        y ∈ evenOdd Q 0 ⊔ evenOdd Q 1)
    have h0 : y₀ * (z : CliffordAlgebra Q) = (z : CliffordAlgebra Q) * y₀ :=
      heven y₀ (by rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule])
    have h1 : y₁ * (z : CliffordAlgebra Q) = (z : CliffordAlgebra Q) * y₁ := by
      have hmul : y₁ * ω ∈ even Q := by
        rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
        have h := SetLike.mul_mem_graded h₁ hωodd
        rwa [CharTwo.add_self_eq_zero] at h
      have hcomm := heven _ hmul
      have hzω := Subalgebra.mem_center_iff.mp hωc (z : CliffordAlgebra Q)
      have key : y₁ * (z : CliffordAlgebra Q) * (ω * ω) =
          (z : CliffordAlgebra Q) * y₁ * (ω * ω) := by
        rw [← mul_assoc (y₁ * (z : CliffordAlgebra Q)), mul_assoc y₁ (z : CliffordAlgebra Q),
          hzω, ← mul_assoc y₁, hcomm, ← mul_assoc (z : CliffordAlgebra Q) y₁,
          mul_assoc ((z : CliffordAlgebra Q) * y₁)]
      have hsmul : c • (y₁ * (z : CliffordAlgebra Q)) = c • ((z : CliffordAlgebra Q) * y₁) := by
        rw [Algebra.smul_def, Algebra.smul_def, Algebra.commutes, Algebra.commutes, ← hsq]
        exact key
      calc y₁ * (z : CliffordAlgebra Q) = c⁻¹ • c • (y₁ * (z : CliffordAlgebra Q)) :=
            (inv_smul_smul₀ hc _).symm
        _ = c⁻¹ • c • ((z : CliffordAlgebra Q) * y₁) := by rw [hsmul]
        _ = (z : CliffordAlgebra Q) * y₁ := inv_smul_smul₀ hc _
    rw [add_mul, mul_add, h0, h1]
  obtain ⟨a, ha⟩ := exists_algebraMap_of_mem_even_of_mem_center hQ hodd z.2 hzc
  rw [Algebra.mem_bot]
  exact ⟨a, Subtype.ext ha.symm⟩

/-! ### The odd-dimensional Clifford algebra is not central -/

/-- **An odd-dimensional Clifford algebra is not central over the base field.** This is the sharp
contrast with the even-dimensional
`TauCeti.SpinPolarizationData.isCentral_cliffordAlgebra`, and the reason the odd-dimensional
structure theorem produces a *product* of two matrix algebras rather than a single one. -/
theorem not_isCentral_of_odd_finrank (hQ : Q.Nondegenerate) (hodd : Odd (finrank F V)) :
    ¬ Algebra.IsCentral F (CliffordAlgebra Q) := by
  intro _
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have _ : Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial
  have h : 2 = 1 := (finrank_center_eq_two_of_odd_finrank hQ hodd).symm.trans
    (finrank_center_of_isCentral F (CliffordAlgebra Q))
  omega

end CliffordAlgebra
