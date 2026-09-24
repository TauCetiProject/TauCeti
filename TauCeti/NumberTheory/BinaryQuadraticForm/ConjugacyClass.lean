/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.GroupTheory.GroupAction.Stabilizer
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct
public import TauCeti.NumberTheory.BinaryQuadraticForm.OfMatrix
public import TauCeti.NumberTheory.HurwitzClassNumber
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.NumberTheory.BinaryQuadraticForm.Reduction

/-!
# Conjugacy classes of integer matrices and classes of binary quadratic forms

For `t n : ℤ`, the group `SL(2, ℤ)` acts by conjugation on the integer matrices of trace `t` and
determinant `n`, and the form `Q_M = c x² + (d - a) x y - b y²` of `M = !![a, b; c, d]`
(`TauCeti.BinaryQuadraticForm.ofMatrix`) turns this action into the action of `SL(2, ℤ)` on the
forms of discriminant `t² - 4 n`: `Q_{γ M γ⁻¹} = γ • Q_M`, and `M ↦ Q_M` is a bijection between the
two sets (`TauCeti.BinaryQuadraticForm.ofMatrixEquiv`). This file passes to the orbits, in the
elliptic case `t² - 4 n = -D < 0`, and compares the stabilisers.

*Automorphism weights.* The centraliser of `M` in `SL(2, ℤ)` and the stabiliser of `Q_M` have the
same order: conjugation preserves the trace, and a matrix is determined by its trace and its form
(`TauCeti.BinaryQuadraticForm.ofMatrix_inj_of_trace_eq`). The weight `2 / |Z_SL(M)|` of a
conjugacy class is therefore the weight `2 / |Stab(Q_M)|` with which
`TauCeti.hurwitzClassNumber_eq_finsum` counts a class of forms. Since `±1` centralise every
matrix, it is also Popa and Zagier's weight `1 / |Γ_M|` for `Γ = PSL(2, ℤ)`.

*Orientation.* A matrix `M` of trace `t` and determinant `n` is elliptic (`Matrix.IsElliptic`), so
its lower left entry `c` is not zero (`Matrix.IsElliptic.c_ne_zero`), and `Q_M`, a form of negative
discriminant, is positive definite exactly when `c > 0`. The adjugate
`adjugate M = !![d, -b; -c, a]`, which for a matrix of trace `t` is `t • 1 - M`
(`Matrix.adjugate_fin_two_eq_trace_smul_one_sub`), has the same trace and determinant as `M`,
commutes with conjugation, and has form `⟨-c, a - d, b⟩`, the negative of `Q_M`. So it exchanges
the classes with `c > 0` and those with `c < 0`, and each of the two orientations contributes one
copy of the classes of positive definite forms of discriminant `-D`.

Together these give the matrix form of Popa and Zagier's class number identity, equation (2) of
their §1: the sum over the `SL(2, ℤ)`-conjugacy classes of integer matrices of trace `t` and
determinant `n` of `2 / |Z_SL(M)|` is `2 H(4 n - t²)`, where `H` is the Hurwitz class number.
Popa and Zagier state it for matrices modulo `±1`, summing over the classes of trace `±t`; for
`t ≠ 0` those are the classes of trace `t` here.

## Main definitions

* `TauCeti.BinaryQuadraticForm.orbitRelQuotientTraceDetFiberEquiv`: for `t² - 4 n = -D < 0`, the
  conjugacy classes of `TauCeti.traceDetFiber (Fin 2) t n` are two copies of the
  classes of `posDef D`: the classes with `c > 0` through `M ↦ Q_M`, and those with `c < 0`
  through `M ↦ Q_{adjugate M}`, with
  `TauCeti.BinaryQuadraticForm.orbitRelQuotientTraceDetFiberEquiv_mk_of_mem` and
  `TauCeti.BinaryQuadraticForm.orbitRelQuotientTraceDetFiberEquiv_mk_of_adjugate_mem` its
  evaluation lemmas, and `TauCeti.BinaryQuadraticForm.orbitRelQuotientTraceDetFiberEquiv_symm_inl`
  and `TauCeti.BinaryQuadraticForm.orbitRelQuotientTraceDetFiberEquiv_symm_inr` those of its
  inverse.

## Main results

* `TauCeti.BinaryQuadraticForm.ofMatrix_conjAct_smul`: `Q_{γ M γ⁻¹} = γ • Q_M`, for the conjugation
  action.
* `TauCeti.BinaryQuadraticForm.card_stabilizer_ofMatrix`: the stabiliser of `Q_M` has the order of
  the centraliser of `M` in `SL(2, ℤ)`.
* `TauCeti.BinaryQuadraticForm.apply_one_zero_ne_zero_of_mem_traceDetFiber`: in an elliptic fibre,
  the lower left entry `c` of `M` is not zero.
* `TauCeti.BinaryQuadraticForm.ofMatrix_mem_posDef_iff`: in an elliptic fibre, `Q_M` is positive
  definite exactly when `c > 0`.
* `TauCeti.BinaryQuadraticForm.cardStabilizerOnOrbit_orbitRelQuotientTraceDetFiberEquiv_symm`:
  the correspondence of classes preserves the stabiliser orders.
* `TauCeti.BinaryQuadraticForm.finite_orbitRel_quotient_traceDetFiber`: in an elliptic fibre there
  are finitely many conjugacy classes.
* `TauCeti.BinaryQuadraticForm.finsum_traceDetFiber_eq_two_mul_hurwitzClassNumber`: the sum of
  `2 / |Z_SL(M)|` over the conjugacy classes of trace `t` and determinant `n` is `2 H(4 n - t²)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1, equation (2).
-/

public section

open Matrix MulAction ConjAct
open scoped MatrixGroups

namespace TauCeti

namespace BinaryQuadraticForm

section CommRing

variable {R : Type*} [CommRing R]

/-- `M ↦ Q_M` is equivariant for the conjugation action of `SL(2, R)` on matrices:
`Q_{γ M γ⁻¹} = γ • Q_M`. -/
@[simp]
theorem ofMatrix_conjAct_smul (g : ConjAct SL(2, R)) (M : Matrix (Fin 2) (Fin 2) R) :
    ofMatrix (g • M) = ofConjAct g • ofMatrix M :=
  ofMatrix_conj (ofConjAct g) M

end CommRing

/-- **The automorphism weights agree**: the stabiliser of `Q_M` in `SL(2, ℤ)` has the order of the
centraliser of `M` in `SL(2, ℤ)`, that is of its stabiliser under conjugation. -/
theorem card_stabilizer_ofMatrix (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Nat.card (stabilizer SL(2, ℤ) (ofMatrix M)) = Nat.card (stabilizer (ConjAct SL(2, ℤ)) M) :=
  -- conjugation preserves the trace, and a matrix is determined by its trace and its form, so
  -- `γ` centralises `M` exactly when it fixes `Q_M`
  card_stabilizer_congr (ofConjAct (G := SL(2, ℤ))) M (ofMatrix_conjAct_smul · M) fun g ↦
    (ofMatrix_inj_of_trace_eq (trace_specialLinearGroup_smul g M)).1

variable {t n : ℤ} {D : ℕ} [NeZero D]

/-- **The orientation is defined**: if `t² - 4 n = -D < 0`, a matrix of trace `t` and
determinant `n` has non-zero lower left entry `c`. -/
theorem apply_one_zero_ne_zero_of_mem_traceDetFiber (h : t ^ 2 - 4 * n = -D)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ traceDetFiber (Fin 2) t n) : M 1 0 ≠ 0 :=
  -- `M` is elliptic: its discriminant is `t² - 4 n = -D < 0`
  IsElliptic.c_ne_zero <| by
    simp [IsElliptic, discr_fin_two, (mem_traceDetFiber.1 hM).1, (mem_traceDetFiber.1 hM).2, h,
      NeZero.pos D]

/-- If `t² - 4 n = -D < 0`, the form `Q_M` of a matrix of trace `t` and determinant `n` is positive
definite exactly when the lower left entry `c` of `M` is positive. -/
theorem ofMatrix_mem_posDef_iff (h : t ^ 2 - 4 * n = -D) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M ∈ traceDetFiber (Fin 2) t n) : ofMatrix M ∈ posDef D ↔ 0 < M 1 0 := by
  simp [(mem_traceDetFiber.1 hM).1, (mem_traceDetFiber.1 hM).2, h]

/-- The matrix of trace `t` and determinant `n` whose form is `f`, for `f ∈ posDef D`. -/
private def toFiber (h : t ^ 2 - 4 * n = -D) (f : posDef D) : traceDetFiber (Fin 2) t n :=
  ⟨_, mem_traceDetFiber.2 ((ofMatrixEquiv t n).symm ⟨f, (mem_posDef.1 f.2).1.trans h.symm⟩).2⟩

private theorem ofMatrix_toFiber (h : t ^ 2 - 4 * n = -D) (f : posDef D) :
    ofMatrix (toFiber h f : Matrix (Fin 2) (Fin 2) ℤ) = f :=
  (coe_ofMatrixEquiv_apply _).symm.trans <| congrArg Subtype.val <| Equiv.apply_symm_apply _ _

/-- `M ↦ Q_M` is injective on the fibre of trace `t` and determinant `n`. -/
private theorem ofMatrix_coe_injective :
    Function.Injective fun M : traceDetFiber (Fin 2) t n ↦
      ofMatrix (M : Matrix (Fin 2) (Fin 2) ℤ) :=
  fun M N hMN ↦ Subtype.ext <| (ofMatrix_inj_of_trace_eq <|
    (mem_traceDetFiber.1 M.2).1.trans (mem_traceDetFiber.1 N.2).1.symm).1 hMN

private theorem toFiber_ofMatrix (h : t ^ 2 - 4 * n = -D) (M : traceDetFiber (Fin 2) t n)
    (hM : ofMatrix (M : Matrix (Fin 2) (Fin 2) ℤ) ∈ posDef D) : toFiber h ⟨_, hM⟩ = M :=
  ofMatrix_coe_injective (ofMatrix_toFiber h _)

private theorem toFiber_injective (h : t ^ 2 - 4 * n = -D) : Function.Injective (toFiber h) :=
  fun f g hfg ↦ Subtype.ext <| (ofMatrix_toFiber h f).symm.trans <|
    (congrArg (fun M : traceDetFiber (Fin 2) t n ↦ ofMatrix (M : Matrix _ _ ℤ)) hfg).trans
      (ofMatrix_toFiber h g)

private theorem toFiber_smul (h : t ^ 2 - 4 * n = -D) (g : SL(2, ℤ)) (f : posDef D) :
    toFiber h (g • f) = toConjAct g • toFiber h f :=
  ofMatrix_coe_injective <| by simp [ofMatrix_toFiber]

private def adjugateFiber (M : traceDetFiber (Fin 2) t n) : traceDetFiber (Fin 2) t n :=
  ⟨adjugate M, adjugate_mem_traceDetFiber M.2⟩

private theorem adjugateFiber_involutive :
    Function.Involutive (adjugateFiber : traceDetFiber (Fin 2) t n → _) :=
  fun M ↦ Subtype.ext <| by simp [adjugateFiber, adjugate_adjugate']

private theorem sumElim_toFiber_bijective (h : t ^ 2 - 4 * n = -D) :
    Function.Bijective (Sum.elim (toFiber h) (adjugateFiber ∘ toFiber h)) := by
  refine ⟨(toFiber_injective h).sumElim (adjugateFiber_involutive.injective.comp
    (toFiber_injective h)) fun f g hfg ↦ ?_, fun M ↦ ?_⟩
  · -- the two sides have lower left entries `f.a > 0` and `-g.a < 0`
    have : f.1.a = -g.1.a := by
      simpa [adjugateFiber, adjugate_fin_two, toFiber] using congr($hfg.1 1 0)
    exact lt_asymm (neg_pos.1 ((mem_posDef.1 f.2).2.trans_eq this)) (mem_posDef.1 g.2).2
  · -- by the sign of `c`, `M` comes from `Q_{adjugate M}` in the second copy or `Q_M` in the first
    rcases (apply_one_zero_ne_zero_of_mem_traceDetFiber h M.2).lt_or_gt with hM | hM
    · exact ⟨.inr ⟨_, (ofMatrix_mem_posDef_iff h (adjugateFiber M).2).2 <| by
        simpa [adjugateFiber, adjugate_fin_two]⟩,
        (congrArg adjugateFiber (toFiber_ofMatrix h _ _)).trans (adjugateFiber_involutive M)⟩
    · exact ⟨.inl ⟨_, (ofMatrix_mem_posDef_iff h M.2).2 hM⟩, toFiber_ofMatrix h M _⟩

/-- The two copies of the positive definite forms of discriminant `-D` sent bijectively onto the
fibre: the first by `f ↦ M_f`, the matrix with `Q_{M_f} = f`, the second by `f ↦ adjugate M_f`. -/
private noncomputable def fromSumEquiv (h : t ^ 2 - 4 * n = -D) :
    posDef D ⊕ posDef D ≃ traceDetFiber (Fin 2) t n :=
  .ofBijective _ (sumElim_toFiber_bijective h)

private theorem fromSumEquiv_smul (h : t ^ 2 - 4 * n = -D) (g : SL(2, ℤ))
    (s : posDef D ⊕ posDef D) : fromSumEquiv h (g • s) = toConjAct g • fromSumEquiv h s := by
  cases s <;> simp [fromSumEquiv, adjugateFiber, toFiber_smul]

/-- **Conjugacy classes of matrices and classes of forms**: if `t² - 4 n = -D < 0`, the
`SL(2, ℤ)`-conjugacy classes of integer matrices of trace `t` and determinant `n` are two copies of
the `SL(2, ℤ)`-classes of positive definite forms of discriminant `-D`. The class of `M` with lower
left entry `c > 0` goes to the class of `Q_M` in the first copy
(`orbitRelQuotientTraceDetFiberEquiv_mk_of_mem`), and the class of `M` with `c < 0` to the class
of `Q_{adjugate M}` in the second (`orbitRelQuotientTraceDetFiberEquiv_mk_of_adjugate_mem`). The
stabiliser orders match (`cardStabilizerOnOrbit_orbitRelQuotientTraceDetFiberEquiv_symm`). -/
noncomputable def orbitRelQuotientTraceDetFiberEquiv (h : t ^ 2 - 4 * n = -D) :
    orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n) ≃
      orbitRel.Quotient SL(2, ℤ) (posDef D) ⊕ orbitRel.Quotient SL(2, ℤ) (posDef D) :=
  -- `G` is named because `toConjAct` alone leaves it undetermined while the instances are solved
  (MulAction.orbitRelQuotientCongr (toConjAct (G := SL(2, ℤ))) (fromSumEquiv h)
    (fromSumEquiv_smul h)).symm.trans MulAction.orbitRelQuotientSumEquiv

/-- The class of a matrix `M` whose form `Q_M` is positive definite, that is whose lower left entry
is positive (`ofMatrix_mem_posDef_iff`), goes to the class of `Q_M` in the first copy. -/
theorem orbitRelQuotientTraceDetFiberEquiv_mk_of_mem (h : t ^ 2 - 4 * n = -D)
    (M : traceDetFiber (Fin 2) t n) (hM : ofMatrix (M : Matrix (Fin 2) (Fin 2) ℤ) ∈ posDef D) :
    orbitRelQuotientTraceDetFiberEquiv h (Quotient.mk'' M) = .inl (Quotient.mk'' ⟨_, hM⟩) := by
  have : (fromSumEquiv h).symm M = .inl ⟨_, hM⟩ :=
    (Equiv.symm_apply_eq _).2 (toFiber_ofMatrix h M hM).symm
  simp [orbitRelQuotientTraceDetFiberEquiv, this]

/-- The class of a matrix `M` whose form `Q_{adjugate M}` is positive definite, that is whose lower
left entry is negative, goes to the class of `Q_{adjugate M}` in the second copy. -/
theorem orbitRelQuotientTraceDetFiberEquiv_mk_of_adjugate_mem (h : t ^ 2 - 4 * n = -D)
    (M : traceDetFiber (Fin 2) t n)
    (hM : ofMatrix (adjugate (M : Matrix (Fin 2) (Fin 2) ℤ)) ∈ posDef D) :
    orbitRelQuotientTraceDetFiberEquiv h (Quotient.mk'' M) = .inr (Quotient.mk'' ⟨_, hM⟩) := by
  have : (fromSumEquiv h).symm M = .inr ⟨_, hM⟩ :=
    (Equiv.symm_apply_eq _).2 <|
      adjugateFiber_involutive.eq_iff.1 (toFiber_ofMatrix h (adjugateFiber M) hM).symm
  simp [orbitRelQuotientTraceDetFiberEquiv, this]

/-- The inverse of `orbitRelQuotientTraceDetFiberEquiv h` sends the class of `f` in the first copy
to the class of the matrix `M_f` of trace `t` and determinant `n` with `Q_{M_f} = f`, the preimage
of `f` under `ofMatrixEquiv t n`. -/
theorem orbitRelQuotientTraceDetFiberEquiv_symm_inl (h : t ^ 2 - 4 * n = -D) (f : posDef D) :
    (orbitRelQuotientTraceDetFiberEquiv h).symm (.inl (Quotient.mk'' f)) = Quotient.mk''
      ⟨_, mem_traceDetFiber.2
        ((ofMatrixEquiv t n).symm ⟨f, (mem_posDef.1 f.2).1.trans h.symm⟩).2⟩ := by
  simp [orbitRelQuotientTraceDetFiberEquiv, fromSumEquiv, toFiber]

/-- The inverse of `orbitRelQuotientTraceDetFiberEquiv h` sends the class of `f` in the second copy
to the class of the adjugate of the matrix `M_f` with `Q_{M_f} = f`, whose form is `-f`. -/
theorem orbitRelQuotientTraceDetFiberEquiv_symm_inr (h : t ^ 2 - 4 * n = -D) (f : posDef D) :
    (orbitRelQuotientTraceDetFiberEquiv h).symm (.inr (Quotient.mk'' f)) = Quotient.mk''
      ⟨_, adjugate_mem_traceDetFiber <| mem_traceDetFiber.2
        ((ofMatrixEquiv t n).symm ⟨f, (mem_posDef.1 f.2).1.trans h.symm⟩).2⟩ := by
  simp [orbitRelQuotientTraceDetFiberEquiv, fromSumEquiv, adjugateFiber, toFiber]

/-- **The correspondence of classes preserves the automorphism weights**: a conjugacy class of
matrices and the class of forms it corresponds to have stabilisers of the same order. -/
@[simp]
theorem cardStabilizerOnOrbit_orbitRelQuotientTraceDetFiberEquiv_symm (h : t ^ 2 - 4 * n = -D)
    (s : orbitRel.Quotient SL(2, ℤ) (posDef D) ⊕ orbitRel.Quotient SL(2, ℤ) (posDef D)) :
    cardStabilizerOnOrbit ((orbitRelQuotientTraceDetFiberEquiv h).symm s) =
      s.elim cardStabilizerOnOrbit cardStabilizerOnOrbit := by
  simp [orbitRelQuotientTraceDetFiberEquiv]

/-- If `t² - 4 n = -D < 0`, there are finitely many `SL(2, ℤ)`-conjugacy classes of integer
matrices of trace `t` and determinant `n`. -/
theorem finite_orbitRel_quotient_traceDetFiber (h : t ^ 2 - 4 * n = -D) :
    Finite (orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n)) :=
  .of_equiv _ (orbitRelQuotientTraceDetFiberEquiv h).symm

/-- **The class number identity for integer matrices**: if `t² - 4 n = -D < 0`, the sum over the
`SL(2, ℤ)`-conjugacy classes of integer matrices of trace `t` and determinant `n` of
`2 / |Z_SL(M)|`, for the centraliser `Z_SL(M)` of any `M` in the class, is `2 H(D)`. The weight
`2 / |Z_SL(M)|` is Popa and Zagier's `1 / |Γ_M|` for `Γ = PSL(2, ℤ)`, since `±1` centralise every
matrix. -/
theorem finsum_traceDetFiber_eq_two_mul_hurwitzClassNumber (h : t ^ 2 - 4 * n = -D) :
    ∑ᶠ X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n),
      2 / (cardStabilizerOnOrbit X : ℚ) = 2 * hurwitzClassNumber D := by
  -- each of the two orientations `c > 0` and `c < 0` of `M` contributes `H(D)`
  rw [← finsum_comp_equiv (orbitRelQuotientTraceDetFiberEquiv h).symm,
    finsum_sum_type _ (Set.toFinite _) (Set.toFinite _)]
  simp [hurwitzClassNumber_eq_finsum, two_mul]

end BinaryQuadraticForm

end TauCeti
