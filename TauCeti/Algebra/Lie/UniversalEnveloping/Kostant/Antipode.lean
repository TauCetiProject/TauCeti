/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.RingTheory.Binomial

/-!
# The Kostant integral form is stable under the antipode

Let `L` be a Lie algebra over `ℚ`, let `e : ι → L` be root vectors and `h : κ → L` Cartan vectors,
and let `kostantForm e h` be the subring of `UniversalEnvelopingAlgebra ℚ L` they generate in the
sense of `TauCeti.UniversalEnvelopingAlgebra.kostantForm`. This file proves that the antipode maps
that subring into itself, and packages the restriction as a ring anti-automorphism of the form.

The antipode negates each Lie generator, so the question is what negating the argument does to the
two families of generators. For a root vector the answer is a sign: `(-x)⁽ⁿ⁾ = (-1)ⁿ x⁽ⁿ⁾`, and a
subring is closed under negation. For a Cartan vector it is not, because `(-x choose n)` is not a
multiple of `(x choose n)`; it is instead the Chu--Vandermonde combination
`TauCeti.Ring.choose_neg_mem` supplies, an integer combination of the coefficients
`(x choose k)` for `k ≤ n`. That is the one substantive point, and it is what makes the Cartan
generators behave.

The enveloping algebra is not commutative, so the antipode is only an *anti*-homomorphism. Nothing
is lost: a subring is closed under multiplication in either order, so the elements the antipode
sends into a given subring form a subring themselves, which is what
`UniversalEnvelopingAlgebra.antipodeComap` records and what the universal property of the
form is applied to. The packaged equivalence then lands in the opposite ring.

Together with the comultiplication and counit of the same generators this is one of the Hopf
operations that must restrict to the integral form before it can define the pinned
Chevalley--Demazure group scheme; the comultiplication is not proved here.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.antipode_mem_kostantForm` and
  `TauCeti.UniversalEnvelopingAlgebra.antipode_mem_kostantForm_iff`: the antipode maps the Kostant
  integral form into itself, and membership is unchanged by it.
* `TauCeti.UniversalEnvelopingAlgebra.map_antipodeEquiv_kostantForm`: the image of the form under
  the opposite-valued antipode is exactly the opposite subring, so the inclusion above is an
  equality of subrings.
* `TauCeti.UniversalEnvelopingAlgebra.kostantFormAntipode`: the restriction of the antipode to the
  form, as a ring equivalence onto the opposite of the form.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped UniversalEnvelopingAlgebra

universe u w

/-! ## Stability of the integral form -/

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}

attribute [local instance] TauCeti.moduleNNRat

section KostantForm

variable (e : ι → L) (h : κ → L)

/-- The antipode of a divided power of a designated root vector lies in the Kostant integral
form. -/
theorem antipode_dividedPower_mem_kostantForm (i : ι) (n : ℕ) :
    _root_.UniversalEnvelopingAlgebra.antipode ℚ
        (Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ∈
      kostantForm e h := by
  rw [UniversalEnvelopingAlgebra.antipode_dividedPower,
    _root_.UniversalEnvelopingAlgebra.antipode_ι,
    Associative.dividedPower_neg]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, one_smul]
    exact dividedPower_mem_kostantForm e h i n
  · rw [hn.neg_one_pow, neg_one_smul]
    exact neg_mem (dividedPower_mem_kostantForm e h i n)

/-- The antipode of a generalized binomial coefficient of a designated Cartan vector lies in the
Kostant integral form. -/
theorem antipode_ringChoose_mem_kostantForm (j : κ) (n : ℕ) :
    _root_.UniversalEnvelopingAlgebra.antipode ℚ
        (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) n) ∈
      kostantForm e h := by
  rw [UniversalEnvelopingAlgebra.antipode_ringChoose, _root_.UniversalEnvelopingAlgebra.antipode_ι]
  exact Ring.choose_neg_mem fun k _ => ringChoose_mem_kostantForm e h j k

/-- **The Kostant integral form is stable under the antipode.** -/
theorem antipode_mem_kostantForm {a : _root_.UniversalEnvelopingAlgebra ℚ L}
    (ha : a ∈ kostantForm e h) :
    _root_.UniversalEnvelopingAlgebra.antipode ℚ a ∈ kostantForm e h :=
  (_root_.UniversalEnvelopingAlgebra.mem_antipodeComap ℚ).mp <|
  (kostantForm_le_iff e h
    (_root_.UniversalEnvelopingAlgebra.antipodeComap ℚ (kostantForm e h))).mpr
    ⟨fun i n => (_root_.UniversalEnvelopingAlgebra.mem_antipodeComap ℚ).mpr
      (antipode_dividedPower_mem_kostantForm e h i n),
      fun j n => (_root_.UniversalEnvelopingAlgebra.mem_antipodeComap ℚ).mpr
        (antipode_ringChoose_mem_kostantForm e h j n)⟩ ha

/-- Membership in the Kostant integral form is unchanged by the antipode, since the antipode is
involutive. -/
@[simp]
theorem antipode_mem_kostantForm_iff {a : _root_.UniversalEnvelopingAlgebra ℚ L} :
    _root_.UniversalEnvelopingAlgebra.antipode ℚ a ∈ kostantForm e h ↔
      a ∈ kostantForm e h := by
  refine ⟨fun ha => ?_, antipode_mem_kostantForm e h⟩
  simpa using antipode_mem_kostantForm e h ha

/-- The antipode maps the Kostant integral form *onto* itself: the image of the form under the
opposite-valued antipode is the opposite subring, not merely contained in it. -/
theorem map_antipodeEquiv_kostantForm :
    (kostantForm e h).map
        ((_root_.UniversalEnvelopingAlgebra.antipodeEquiv (L := L) ℚ).toRingEquiv.toRingHom) =
      Subring.op (kostantForm e h) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    simpa [_root_.UniversalEnvelopingAlgebra.antipode_apply] using antipode_mem_kostantForm e h ha
  · intro b hb
    refine ⟨_root_.UniversalEnvelopingAlgebra.antipode ℚ b.unop,
      antipode_mem_kostantForm e h (Subring.mem_op.mp hb), ?_⟩
    apply MulOpposite.unop_injective
    simpa [_root_.UniversalEnvelopingAlgebra.antipode_apply] using
      _root_.UniversalEnvelopingAlgebra.antipode_antipode ℚ b.unop

/-- The antipode restricted to the Kostant integral form, as a ring equivalence onto the opposite
ring of the form. This is the anti-automorphism a Hopf order carries. -/
noncomputable def kostantFormAntipode :
    kostantForm e h ≃+* (kostantForm e h)ᵐᵒᵖ :=
  ((RingEquiv.subringMap (s := kostantForm e h)
      (_root_.UniversalEnvelopingAlgebra.antipodeEquiv (L := L) ℚ).toRingEquiv).trans
      (RingEquiv.subringCongr (map_antipodeEquiv_kostantForm e h))).trans
    (Subring.mopRingEquivOp (kostantForm e h)).symm

/-- The restricted antipode acts by the antipode on underlying elements. -/
@[simp]
theorem coe_unop_kostantFormAntipode_apply (a : kostantForm e h) :
    ((kostantFormAntipode e h a).unop : _root_.UniversalEnvelopingAlgebra ℚ L) =
      _root_.UniversalEnvelopingAlgebra.antipode ℚ
        (a : _root_.UniversalEnvelopingAlgebra ℚ L) := by
  -- `Subring.mopRingEquivOp` and `RingEquiv.subringMap` are stated for the underlying
  -- subsemiring, whose carrier is only definitionally the carrier of the subring, so their
  -- computation rules are recorded as explicit coercion equations instead of being rewritten.
  have hmop : ∀ b : (kostantForm e h)ᵐᵒᵖ,
      ((Subring.mopRingEquivOp (kostantForm e h) b : Subring.op (kostantForm e h)) :
        (_root_.UniversalEnvelopingAlgebra ℚ L)ᵐᵒᵖ) =
        MulOpposite.op ((b.unop : kostantForm e h) :
          _root_.UniversalEnvelopingAlgebra ℚ L) :=
    fun b => Subring.mopRingEquivOp_apply_coe _ _
  have hsub : ∀ x : kostantForm e h,
      ((RingEquiv.subringMap (s := kostantForm e h)
          (_root_.UniversalEnvelopingAlgebra.antipodeEquiv (L := L) ℚ).toRingEquiv x :
        (kostantForm e h).map
          (_root_.UniversalEnvelopingAlgebra.antipodeEquiv (L := L) ℚ).toRingEquiv.toRingHom) :
        (_root_.UniversalEnvelopingAlgebra ℚ L)ᵐᵒᵖ) =
        _root_.UniversalEnvelopingAlgebra.antipodeEquiv ℚ
          (x : _root_.UniversalEnvelopingAlgebra ℚ L) :=
    fun x => RingEquiv.subsemiringMap_apply_coe _ _ _
  apply MulOpposite.op_injective
  rw [← hmop, kostantFormAntipode]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
    RingEquiv.coe_subringCongr_apply]
  rw [hsub, _root_.UniversalEnvelopingAlgebra.antipodeEquiv_apply,
    _root_.UniversalEnvelopingAlgebra.antipode_apply, MulOpposite.op_unop]

/-- The inverse of the restricted antipode acts by the antipode on underlying elements. -/
@[simp]
theorem coe_unop_kostantFormAntipode_symm_apply (b : (kostantForm e h)ᵐᵒᵖ) :
    (((kostantFormAntipode e h).symm b : kostantForm e h) :
        _root_.UniversalEnvelopingAlgebra ℚ L) =
      _root_.UniversalEnvelopingAlgebra.antipode ℚ
        (b.unop : _root_.UniversalEnvelopingAlgebra ℚ L) := by
  have happ := congrArg (_root_.UniversalEnvelopingAlgebra.antipode ℚ)
    (coe_unop_kostantFormAntipode_apply e h ((kostantFormAntipode e h).symm b))
  simpa only [RingEquiv.apply_symm_apply,
    _root_.UniversalEnvelopingAlgebra.antipode_antipode] using happ.symm

end KostantForm

end TauCeti.UniversalEnvelopingAlgebra
