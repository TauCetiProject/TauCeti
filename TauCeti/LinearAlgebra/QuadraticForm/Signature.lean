/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
-- Mathlib does not expose the finite-set definition needed for scalar invariance.
import all Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.BilinearForm.PosSemidef
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.Submodule.Prod
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Definiteness and the signature of a quadratic form

This file characterizes positive and negative semidefiniteness by the vanishing of the
opposite index of inertia. It also characterizes positive-definiteness by the negative
index and the radical. These are convenient consequences of Sylvester's law of inertia which
complement Mathlib's definitions of `QuadraticMap.PosDef`, `sigPos`, and `sigNeg`.

It also proves that restriction to a subspace cannot increase either index of inertia, that an
orthogonal family of vectors of positive (or negative) square bounds the corresponding index, that
quotienting a quadratic form by its radical preserves both indices, and that multiplication by a
positive scalar preserves both indices while multiplication by a negative scalar exchanges them; a
form which a linear automorphism negates has equal indices.
Finally, both indices are additive under orthogonal products, and an orthogonal family of vectors
of positive (negative) square has at most as many members as the positive (negative) index.

## Main results

* `QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero`: nonnegativity is characterized by
  vanishing negative index of inertia.
* `QuadraticForm.forall_nonpos_iff_sigPos_eq_zero`: nonpositivity is characterized by
  vanishing positive index of inertia.
* `QuadraticForm.sigPos_restrict_le`: restriction to a subspace cannot increase the
  positive index of inertia.
* `QuadraticForm.sigNeg_restrict_le`: restriction to a subspace cannot increase the
  negative index of inertia.
* `QuadraticForm.card_le_sigPos_of_isOrthoᵢ` and `QuadraticForm.card_le_sigNeg_of_isOrthoᵢ`: a
  family of pairwise orthogonal vectors of positive (resp. negative) square bounds the positive
  (resp. negative) index of inertia from below.
* `QuadraticForm.sigPos_smul_of_pos` and `QuadraticForm.sigNeg_smul_of_pos`: positive scaling
  preserves both indices.
* `QuadraticForm.sigPos_smul_of_neg` and `QuadraticForm.sigNeg_smul_of_neg`: negative scaling
  exchanges the two indices.
* `QuadraticForm.sigNeg_eq_sigPos_of_comp_eq_neg`: a form negated by a linear automorphism has
  equal indices of inertia.
* `QuadraticForm.sigNeg_eq_sigPos_of_isCompl`: a form vanishing on two complementary submodules
  has equal indices of inertia.
* `QuadraticForm.sigPos_lift_radical`: quotienting by the radical preserves the positive
  index of inertia.
* `QuadraticForm.sigNeg_lift_radical`: quotienting by the radical preserves the negative
  index of inertia.
* `QuadraticForm.sigPos_lift` and `QuadraticForm.sigNeg_lift`: more generally, quotienting by any
  subspace of the radical preserves both indices of inertia.
* `QuadraticForm.sigPos_prod` and `QuadraticForm.sigNeg_prod`: the indices of
  inertia are additive under orthogonal products.
* `QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot`: positive-definiteness
  is characterized by vanishing negative index and trivial radical.
* `QuadraticForm.sigPos_add_sigNeg_of_nondegenerate`: the two indices of inertia of a
  nondegenerate quadratic form add up to the dimension.
* `QuadraticForm.sigPos_eq_finrank_of_isCompl` and `QuadraticForm.sigNeg_eq_finrank_of_isCompl`:
  a nondegenerate form vanishing on two complementary subspaces `A` and `B` has both indices of
  inertia equal to `dim A`.
* `LinearMap.BilinForm.card_le_sigPos_toQuadraticMap_of_iIsOrtho` and
  `LinearMap.BilinForm.card_le_sigNeg_toQuadraticMap_of_iIsOrtho`: an orthogonal family of
  vectors of positive (negative) square has at most `sigPos` (`sigNeg`) members.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Finset QuadraticMap

namespace QuadraticForm

section CommRing

variable {R M : Type*} [CommRing R] [LinearOrder R] [AddCommGroup M] [Module R M]

/-- If a linear automorphism `e` negates a quadratic form, `Q (e v) = -Q v`, then `Q` and `-Q` are
equivalent, so the two indices of inertia of `Q` agree. For example, the real part of a complex
quadratic form is negated by multiplication by `I`. -/
theorem sigNeg_eq_sigPos_of_comp_eq_neg (Q : _root_.QuadraticForm R M) (e : M ≃ₗ[R] M)
    (he : ∀ v, Q (e v) = -Q v) : sigNeg Q = sigPos Q := by
  rw [← sigPos_neg]
  exact (QuadraticMap.Equivalent.sigPos_eq ⟨⟨e, fun v ↦ by simp [he]⟩⟩).symm

/-- A quadratic form vanishing on two complementary submodules `A` and `B` has equal indices of
inertia: the automorphism `a + b ↦ a - b` negates it, since `Q (a + b)` is the polar pairing of
`a` and `b`. -/
theorem sigNeg_eq_sigPos_of_isCompl (Q : _root_.QuadraticForm R M) {A B : Submodule R M}
    (hAB : IsCompl A B) (hA : Q.IsTotallyIsotropic A) (hB : Q.IsTotallyIsotropic B) :
    sigNeg Q = sigPos Q := by
  let e : M ≃ₗ[R] M := (Submodule.prodEquivOfIsCompl A B hAB).symm ≪≫ₗ
    (LinearEquiv.refl R A).prodCongr (LinearEquiv.neg R) ≪≫ₗ Submodule.prodEquivOfIsCompl A B hAB
  refine sigNeg_eq_sigPos_of_comp_eq_neg Q e fun v ↦ ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A B hAB).surjective v
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    LinearEquiv.neg_apply, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_neg]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right]
  simp [hA.apply_eq_zero a.2, hB.apply_eq_zero b.2]

variable [IsStrictOrderedRing R]

/-- Multiplication by a positive scalar preserves the positive index of inertia. -/
@[simp]
theorem sigPos_smul_of_pos (Q : _root_.QuadraticForm R M) {a : R} (ha : 0 < a) :
    sigPos (a • Q) = sigPos Q := by
  classical
  unfold sigPos
  congr 1
  ext r
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hr, U, hU, hpos⟩
    exact ⟨hr, U, hU, (QuadraticMap.posDef_smul_iff_of_pos (Q.restrict U) ha).mp hpos⟩
  · rintro ⟨hr, U, hU, hpos⟩
    exact ⟨hr, U, hU, (QuadraticMap.posDef_smul_iff_of_pos (Q.restrict U) ha).mpr hpos⟩

/-- Multiplication by a positive scalar preserves the negative index of inertia. -/
@[simp]
theorem sigNeg_smul_of_pos (Q : _root_.QuadraticForm R M) {a : R} (ha : 0 < a) :
    sigNeg (a • Q) = sigNeg Q := by
  calc
    sigNeg (a • Q) = sigPos (-(a • Q)) := (sigPos_neg (Q := a • Q)).symm
    _ = sigPos (a • (-Q)) := by rw [smul_neg]
    _ = sigPos (-Q) := sigPos_smul_of_pos (-Q) ha
    _ = sigNeg Q := sigPos_neg

/-- Multiplication by a negative scalar exchanges the positive and negative indices of inertia. -/
@[simp]
theorem sigPos_smul_of_neg (Q : _root_.QuadraticForm R M) {a : R} (ha : a < 0) :
    sigPos (a • Q) = sigNeg Q := by
  have hpos : 0 < -a := neg_pos.mpr ha
  have hform : a • Q = (-a) • (-Q) := by simp
  rw [hform, sigPos_smul_of_pos (-Q) hpos, sigPos_neg]

/-- Multiplication by a negative scalar exchanges the negative and positive indices of inertia. -/
@[simp]
theorem sigNeg_smul_of_neg (Q : _root_.QuadraticForm R M) {a : R} (ha : a < 0) :
    sigNeg (a • Q) = sigPos Q := by
  have hpos : 0 < -a := neg_pos.mpr ha
  calc
    sigNeg (a • Q) = sigPos (-(a • Q)) := (sigPos_neg (Q := a • Q)).symm
    _ = sigPos ((-a) • Q) := congrArg sigPos (neg_smul a Q).symm
    _ = sigPos Q := sigPos_smul_of_pos Q hpos

end CommRing

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- A quadratic form is nonnegative exactly when its negative index of inertia vanishes. -/
theorem forall_nonneg_iff_sigNeg_eq_zero (Q : _root_.QuadraticForm K M) :
    (∀ x, 0 ≤ Q x) ↔ sigNeg Q = 0 := by
  constructor
  · intro hQ
    have h := sigPos_add_finrank_le_of_nonpos (Q := -Q) (V := ⊤) (fun x _ ↦ by
      simp only [neg_apply]
      exact neg_nonpos.mpr (hQ x))
    rw [sigPos_neg, finrank_top] at h
    omega
  · intro hsig x
    by_contra hlt
    have hQx : 0 < -Q x := neg_pos.mpr (not_le.mp hlt)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, neg_zero] at hQx
      exact lt_irrefl 0 hQx
    have hpos : ((-Q).restrict (Submodule.span K {x})).PosDef := by
      rintro ⟨v, hv⟩ hv0
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hv0 (by simp)
      rw [restrict_apply, neg_apply, Q.map_smul, smul_eq_mul]
      have : -(c * c * Q x) = (c * c) * -Q x := by ring
      rw [this]
      exact mul_pos (mul_self_pos.mpr hc0) hQx
    have hrank : Module.finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx0
    have hle := le_sigNeg_of_negDef (Q := Q) hpos
    rw [hrank, hsig] at hle
    omega

/-- A quadratic form is nonpositive exactly when its positive index of inertia vanishes. -/
theorem forall_nonpos_iff_sigPos_eq_zero (Q : _root_.QuadraticForm K M) :
    (∀ x, Q x ≤ 0) ↔ sigPos Q = 0 := by
  simpa only [neg_apply, neg_nonneg, sigNeg_neg] using forall_nonneg_iff_sigNeg_eq_zero (-Q)

omit [IsStrictOrderedRing K] in
/-- Restricting a quadratic form to a subspace cannot increase its positive index. -/
theorem sigPos_restrict_le (Q : _root_.QuadraticForm K M) (W : Subspace K M) :
    sigPos (Q.restrict W) ≤ sigPos Q := by
  obtain ⟨U, hUrank, hUpos⟩ := exists_finrank_eq_sigPos_and_posDef (Q.restrict W)
  rw [← hUrank, ← Submodule.finrank_map_subtype_eq W U]
  apply le_sigPos_of_posDef (V := U.map W.subtype)
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ hx0
  rw [restrict_apply]
  exact hUpos ⟨x, hx⟩ (by simpa using hx0)

omit [IsStrictOrderedRing K] in
/-- Restricting a quadratic form to a subspace cannot increase its negative index. -/
theorem sigNeg_restrict_le (Q : _root_.QuadraticForm K M) (W : Subspace K M) :
    sigNeg (Q.restrict W) ≤ sigNeg Q := by
  have hneg : (-Q).restrict W = -(Q.restrict W) := by
    ext x
    simp only [QuadraticMap.restrict_apply, neg_apply]
  simpa only [hneg, sigPos_neg] using sigPos_restrict_le (-Q) W

/-- A finite family of pairwise orthogonal vectors on which a quadratic form is positive spans a
positive-definite subspace, so its size is at most the positive index of inertia. -/
theorem card_le_sigPos_of_isOrthoᵢ {ι : Type*} [Fintype ι] {Q : _root_.QuadraticForm K M}
    {v : ι → M} (hv : Q.polarBilin.IsOrthoᵢ v) (hpos : ∀ i, 0 < Q (v i)) :
    Fintype.card ι ≤ sigPos Q := by
  classical
  have hli : LinearIndependent K v :=
    LinearMap.linearIndependent_of_isOrthoᵢ hv fun i ↦ by
      rw [polarBilin_apply_apply, polar_self, two_nsmul]
      exact (add_pos (hpos i) (hpos i)).ne'
  rw [← finrank_span_eq_card hli]
  refine le_sigPos_of_posDef Q fun ⟨x, hx⟩ hx0 ↦ ?_
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  -- The cross terms of `Q (∑ i, c i • v i)` vanish by orthogonality.
  have hcross : ∑ ij ∈ univ.sym2 with ¬ij.IsDiag,
      polarSym2 Q (ij.map fun i ↦ c i • v i) = 0 := by
    refine Finset.sum_eq_zero fun ij hij ↦ ?_
    induction ij using Sym2.ind with
    | h i j =>
      have hij' : i ≠ j := by simpa using (Finset.mem_filter.1 hij).2
      simp [← polarBilin_apply_apply, hv hij']
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! h
    exact hx0 (by simp [h])
  rw [restrict_apply, Q.map_sum, hcross, add_zero]
  simp only [QuadraticMap.map_smul, smul_eq_mul]
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (mul_self_nonneg _) (hpos j).le)
    ⟨i, mem_univ _, mul_pos (mul_self_pos.2 hi) (hpos i)⟩

/-- A finite family of pairwise orthogonal vectors on which a quadratic form is negative spans a
negative-definite subspace, so its size is at most the negative index of inertia. -/
theorem card_le_sigNeg_of_isOrthoᵢ {ι : Type*} [Fintype ι] {Q : _root_.QuadraticForm K M}
    {v : ι → M} (hv : Q.polarBilin.IsOrthoᵢ v) (hneg : ∀ i, Q (v i) < 0) :
    Fintype.card ι ≤ sigNeg Q := by
  rw [← sigPos_neg]
  refine card_le_sigPos_of_isOrthoᵢ (fun i j hij ↦ ?_) fun i ↦ neg_pos.2 (hneg i)
  simpa [polar_neg] using hv hij

section Prod

variable {M' : Type*} [AddCommGroup M'] [Module K M'] [FiniteDimensional K M']

/-- The sum of the positive indices of two quadratic forms is a lower bound for the positive
index of their orthogonal product. -/
private theorem add_sigPos_le_sigPos_prod (Q : _root_.QuadraticForm K M)
    (Q' : _root_.QuadraticForm K M') :
    sigPos Q + sigPos Q' ≤ sigPos (Q.prod Q') := by
  obtain ⟨U, hUrank, hUpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
  obtain ⟨W, hWrank, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q'
  have hprod : ((Q.prod Q').restrict (U.prod W)).PosDef := by
    rintro ⟨⟨u, w⟩, hu, hw⟩ hp
    simpa only [QuadraticMap.restrict_apply, QuadraticMap.prod_apply] using
      (hUpos.prod hWpos) (⟨u, hu⟩, ⟨w, hw⟩)
        (by simpa only [ne_eq, Subtype.ext_iff, Prod.mk_eq_zero, Submodule.coe_zero] using hp)
  calc
    sigPos Q + sigPos Q' = Module.finrank K U + Module.finrank K W := by
      rw [hUrank, hWrank]
    _ = Module.finrank K (U × W) := Module.finrank_prod.symm
    _ = Module.finrank K (U.prod W) := LinearEquiv.finrank_eq (Submodule.prodEquiv U W).symm
    _ ≤ sigPos (Q.prod Q') := le_sigPos_of_posDef (Q := Q.prod Q') hprod

/-- The sum of the negative indices of two quadratic forms is a lower bound for the negative
index of their orthogonal product. -/
private theorem add_sigNeg_le_sigNeg_prod (Q : _root_.QuadraticForm K M)
    (Q' : _root_.QuadraticForm K M') :
    sigNeg Q + sigNeg Q' ≤ sigNeg (Q.prod Q') := by
  have hneg : (-Q).prod (-Q') = -(Q.prod Q') := by
    ext p
    simp only [QuadraticMap.prod_apply, neg_apply, neg_add]
  simpa only [← sigPos_neg, hneg] using add_sigPos_le_sigPos_prod (-Q) (-Q')

/-- The positive index of inertia is additive under orthogonal products. -/
@[simp]
theorem sigPos_prod (Q : _root_.QuadraticForm K M) (Q' : _root_.QuadraticForm K M') :
    sigPos (Q.prod Q') = sigPos Q + sigPos Q' := by
  have hpos := add_sigPos_le_sigPos_prod Q Q'
  have hneg := add_sigNeg_le_sigNeg_prod Q Q'
  have hsum := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q.prod Q')
  have hsumQ := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have hsumQ' := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q')
  have hrad : Module.finrank K (Q.prod Q').radical =
      Module.finrank K Q.radical + Module.finrank K Q'.radical := by
    let _ : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
    rw [QuadraticMap.radical_prod, ← LinearEquiv.finrank_eq
      (Submodule.prodEquiv Q.radical Q'.radical).symm,
      Module.finrank_prod]
  rw [hrad, Module.finrank_prod] at hsum
  omega

/-- The negative index of inertia is additive under orthogonal products. -/
@[simp]
theorem sigNeg_prod (Q : _root_.QuadraticForm K M) (Q' : _root_.QuadraticForm K M') :
    sigNeg (Q.prod Q') = sigNeg Q + sigNeg Q' := by
  have hneg : (-Q).prod (-Q') = -(Q.prod Q') := by
    ext p
    simp only [QuadraticMap.prod_apply, neg_apply, neg_add]
  rw [← sigPos_neg, ← hneg, sigPos_prod, sigPos_neg, sigPos_neg]

end Prod

end QuadraticForm

namespace QuadraticForm

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M]
  [Module K M] [FiniteDimensional K M]

/-- Quotienting a quadratic form by its radical preserves its positive index of inertia. -/
theorem sigPos_lift_radical (Q : _root_.QuadraticForm K M) :
    sigPos (Q.lift Q.radical le_rfl) = sigPos Q := by
  rw [QuadraticMap.Equivalent.sigPos_eq ⟨(IsometryEquiv.prodRadicalLift Q).symm⟩, sigPos_prod,
    (forall_nonpos_iff_sigPos_eq_zero (0 : _root_.QuadraticForm K Q.radical)).mp fun _ => le_rfl,
    zero_add]

/-- Quotienting a quadratic form by a subspace of its radical preserves its positive index of
inertia. -/
theorem sigPos_lift (Q : _root_.QuadraticForm K M) (N : Subspace K M) (hN : N ≤ Q.radical) :
    sigPos (Q.lift N hN) = sigPos Q := by
  -- Quotienting `Q.lift N hN` by its radical `Q.radical.map N.mkQ` recovers `Q.lift Q.radical`.
  have hR := QuadraticMap.radical_lift Q hN
  have hlift : ∀ (R : Subspace K (M ⧸ N)) (hR : R = (Q.lift N hN).radical),
      sigPos ((Q.lift N hN).lift R hR.le) = sigPos (Q.lift N hN) := by
    rintro _ rfl
    exact sigPos_lift_radical _
  have hequiv : ((Q.lift N hN).lift (Q.radical.map N.mkQ) hR.ge).Equivalent
      (Q.lift Q.radical le_rfl) :=
    ⟨{ Submodule.quotientQuotientEquivQuotient N Q.radical hN with
      map_app' := fun x => by
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          induction x using Submodule.Quotient.induction_on with
          | H x => rfl }⟩
  rw [← hlift _ hR.symm, hequiv.sigPos_eq, sigPos_lift_radical]

/-- Quotienting a quadratic form by a subspace of its radical preserves its negative index of
inertia. -/
theorem sigNeg_lift (Q : _root_.QuadraticForm K M) (N : Subspace K M) (hN : N ≤ Q.radical) :
    sigNeg (Q.lift N hN) = sigNeg Q := by
  have hlift : (-Q).lift N ((radical_neg Q).symm ▸ hN) = -(Q.lift N hN) := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      simp only [QuadraticMap.lift_mk, neg_apply]
  rw [← sigPos_neg, ← hlift, sigPos_lift, sigPos_neg]

/-- Quotienting a quadratic form by its radical preserves its negative index of inertia. -/
theorem sigNeg_lift_radical (Q : _root_.QuadraticForm K M) :
    sigNeg (Q.lift Q.radical le_rfl) = sigNeg Q :=
  sigNeg_lift Q Q.radical le_rfl

/-- A quadratic form is positive-definite exactly when its negative index vanishes and its
radical is trivial. -/
@[grind =]
theorem posDef_iff_sigNeg_eq_zero_and_radical_eq_bot (Q : _root_.QuadraticForm K M) :
    Q.PosDef ↔ sigNeg Q = 0 ∧ Q.radical = ⊥ := by
  constructor
  · intro hQ
    refine ⟨(forall_nonneg_iff_sigNeg_eq_zero Q).mp hQ.nonneg, ?_⟩
    exact QuadraticMap.Anisotropic.radical_eq_bot hQ.anisotropic
  · rintro ⟨hneg, hrad⟩
    obtain ⟨W, hWrank, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
    have hsig := sigPos_add_sigNeg_add_radical (Q := Q)
    rw [hneg, hrad] at hsig
    have hsig' : sigPos Q = Module.finrank K M := by
      simpa only [add_zero, finrank_bot] using hsig
    have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (hWrank.trans hsig')
    intro x hx
    have hxW : x ∈ W := hWtop.symm ▸ Submodule.mem_top
    exact hWpos ⟨x, hxW⟩ (by simpa only [ne_eq, Submodule.mk_eq_zero])

/-- The positive and negative indices of inertia of a nondegenerate quadratic form add up to the
dimension of the space. -/
theorem sigPos_add_sigNeg_of_nondegenerate (Q : _root_.QuadraticForm K M) (hQ : Q.Nondegenerate) :
    sigPos Q + sigNeg Q = Module.finrank K M := by
  have hsig := sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hQ.radical_eq_bot] at hsig
  simpa only [finrank_bot, add_zero] using hsig

/-- A nondegenerate quadratic form vanishing on two complementary subspaces `A` and `B` has
positive index of inertia `dim A`; swapping the roles gives `dim A = dim B`. For example, the real
intersection form on `H²(S¹ × Y)`, for a closed oriented three-manifold `Y`, vanishes on `p*H²(Y)`
and on `[ds] ∪ p*H¹(Y)`, which Poincaré duality pairs perfectly, so its positive index is
`dim H²(Y) = b₁(Y)`. Combine with `QuadraticMap.nondegenerate_of_isCompl` when nondegeneracy
comes from a perfect pairing of `A` with `B`. -/
theorem sigPos_eq_finrank_of_isCompl (Q : _root_.QuadraticForm K M) (hQ : Q.Nondegenerate)
    {A B : Subspace K M} (hAB : IsCompl A B) (hA : Q.IsTotallyIsotropic A)
    (hB : Q.IsTotallyIsotropic B) :
    sigPos Q = Module.finrank K A := by
  have hsum := sigPos_add_sigNeg_of_nondegenerate Q hQ
  rw [sigNeg_eq_sigPos_of_isCompl Q hAB hA hB] at hsum
  have hdim := Submodule.finrank_add_eq_of_isCompl hAB
  have hleA := sigPos_add_finrank_le_of_nonpos (V := A) fun _ hx ↦ (hA.apply_eq_zero hx).le
  have hleB := sigPos_add_finrank_le_of_nonpos (V := B) fun _ hx ↦ (hB.apply_eq_zero hx).le
  omega

/-- A nondegenerate quadratic form vanishing on two complementary subspaces `A` and `B` has
negative index of inertia `dim A`. -/
theorem sigNeg_eq_finrank_of_isCompl (Q : _root_.QuadraticForm K M) (hQ : Q.Nondegenerate)
    {A B : Subspace K M} (hAB : IsCompl A B) (hA : Q.IsTotallyIsotropic A)
    (hB : Q.IsTotallyIsotropic B) :
    sigNeg Q = Module.finrank K A := by
  rw [sigNeg_eq_sigPos_of_isCompl Q hAB hA hB, sigPos_eq_finrank_of_isCompl Q hQ hAB hA hB]

end QuadraticForm

namespace LinearMap.BilinForm

open _root_.QuadraticForm

/-- The negative index of a bilinear form agrees with that of its Gram matrix in any basis. -/
@[simp]
theorem sigNeg_toMatrix {R M I : Type*} [CommRing R] [LinearOrder R] [AddCommGroup M]
    [Module R M] [Fintype I] [DecidableEq I] (b : Module.Basis I R M)
    (B : LinearMap.BilinForm R M) :
    _root_.sigNeg ((B.toMatrix b).toQuadraticForm') = _root_.sigNeg B.toQuadraticMap := by
  apply QuadraticMap.Equivalent.sigNeg_eq
  refine ⟨{
    toLinearEquiv := b.equivFun.symm
    map_app' := fun v ↦ ?_ }⟩
  rw [Matrix.toQuadraticForm'_apply, LinearMap.BilinMap.toQuadraticMap_apply]
  exact (B.dotProduct_toMatrix_mulVec b v v).symm

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- A symmetric bilinear form is positive-semidefinite if and only if the negative index of its
associated quadratic form vanishes. -/
@[grind =]
theorem isPosSemidef_iff_sigNeg_eq_zero (B : LinearMap.BilinForm K M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ _root_.sigNeg B.toQuadraticMap = 0 := by
  rw [isPosSemidef_iff_forall_nonneg B hB]
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using
    QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero B.toQuadraticMap

/-- A family of pairwise orthogonal vectors of positive square spans a positive-definite subspace
of dimension its cardinality, so that cardinality is at most the positive index of inertia. -/
theorem card_le_sigPos_toQuadraticMap_of_iIsOrtho {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm K M) {v : ι → M} (hv : B.iIsOrtho v)
    (hpos : ∀ i, 0 < B (v i) (v i)) :
    Fintype.card ι ≤ _root_.sigPos B.toQuadraticMap := by
  classical
  rw [← finrank_span_eq_card (linearIndependent_of_iIsOrtho hv fun i ↦ (hpos i).ne')]
  apply le_sigPos_of_posDef
  rintro ⟨x, hx⟩ hx0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx0 (by simp)
  have hcv : B.iIsOrtho fun j ↦ c j • v j :=
    iIsOrtho_def.mpr fun j k hjk ↦ by simp [iIsOrtho_def.mp hv j k hjk]
  rw [QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply, hcv.apply_sum_sum]
  refine ((QuadraticMap.posDef_weightedSumSquares_iff _).2 hpos c hc).trans_eq ?_
  rw [QuadraticMap.weightedSumSquares_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [smul_left, smul_right, smul_eq_mul]
  ring

/-- A family of pairwise orthogonal vectors of negative square has at most as many members as
the negative index of inertia. -/
theorem card_le_sigNeg_toQuadraticMap_of_iIsOrtho {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm K M) {v : ι → M} (hv : B.iIsOrtho v)
    (hneg : ∀ i, B (v i) (v i) < 0) :
    Fintype.card ι ≤ _root_.sigNeg B.toQuadraticMap := by
  have h := card_le_sigPos_toQuadraticMap_of_iIsOrtho (-B) (v := v)
    (iIsOrtho_def.mpr fun i j hij ↦ by simp [iIsOrtho_def.mp hv i j hij])
    fun i ↦ by simpa using hneg i
  rwa [LinearMap.BilinMap.toQuadraticMap_neg, sigPos_neg] at h

/-- The quadratic form of a symmetric bilinear form is positive-definite if and only if the
bilinear form is positive-semidefinite and nondegenerate. -/
@[grind =]
theorem posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate (B : LinearMap.BilinForm K M)
    (hB : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ B.IsPosSemidef ∧ B.Nondegenerate := by
  have _ : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  rw [isPosSemidef_iff_sigNeg_eq_zero B hB,
    QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    _root_.LinearMap.BilinForm.radical_toQuadraticMap B hB]

/-- The quadratic form of a symmetric bilinear form is positive-definite if and only if the
kernel of the bilinear form and the negative index of the quadratic form both vanish. -/
@[grind =]
theorem posDef_toQuadraticMap_iff_finrank_ker_eq_zero_and_sigNeg_eq_zero
    (B : LinearMap.BilinForm K M) (hB : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ Module.finrank K B.ker = 0 ∧ _root_.sigNeg B.toQuadraticMap = 0 := by
  rw [posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate B hB,
    isPosSemidef_iff_sigNeg_eq_zero B hB,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    Submodule.finrank_eq_zero, and_comm]

end LinearMap.BilinForm
