/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.Hom
public import TauCeti.Analysis.Fredholm.Compression
public import TauCeti.NoncommutativeGeometry.FredholmModule.Basic
public import TauCeti.RingTheory.Idempotents.SquareRootOne

/-!
# The index pairing of Fredholm modules with idempotents and invertibles

A Fredholm module over `A` pairs with the K-theory of `A` through Fredholm indices of
compressions of its operator `F`. This file constructs both pairings at the level of
representatives, that is of idempotents and invertible elements of `A`.

**Even pairing.** Let `M` be an even Fredholm module with representation `π`, operator `F` and
grading `γ`, and let `H⁺` and `H⁻` be the `±1`-eigenspaces of `γ`, the ranges of the
projections `(1 ± γ) / 2` (`TauCeti.halfOneAdd ℂ (±γ)`). For an idempotent `e` of `A`
the operator `π(e)` commutes with `γ`, and `F` exchanges `H⁺` and `H⁻`, so the compression
`π(e) F π(e)` maps `π(e) H⁺` to `π(e) H⁻` (`EvenFredholmModule.indexCompression`). The idempotent
`e` need not be self-adjoint, so `π(e) H⁺` is the range of an idempotent that need not be an
orthogonal projection. This compression is Fredholm: the compression of `F` from `π(e) H⁻` back to
`π(e) H⁺` inverts it modulo the compact operators `π(e) F [π(e), F] π(e)` and
`π(e) (F² - 1) π(e)`. No normalization `F² = 1` is needed. The **index pairing**
`EvenFredholmModule.indexPairing M e` is its Fredholm index. It vanishes at `e = 0`, is invariant
under unitary equivalence and under the relatively compact perturbations of `F` of
`EvenFredholmModule.perturb`, and on a finite-dimensional Hilbert space it is
`dim π(e) H⁺ - dim π(e) H⁻`.

**Odd pairing.** Let `M` be a Fredholm module over a unital algebra `A` whose operator satisfies
`F² = 1`, so that `P = (1 + F) / 2` (`TauCeti.halfOneAdd ℂ F`) is the projection onto the
`+1`-eigenspace of `F`. The representation may be nonunital; an element `a` acts through
`π(a) + 1 - π(1)`, which is multiplicative and unital (`FredholmModule.unitizedRep`, the
unitization `MulHom.unitize` of `π`), so an
invertible `u` of `A` acts by an invertible operator commuting with `P` modulo compact operators.
Its compression `P (π(u) + 1 - π(1)) P` to the range of `P` (`FredholmModule.oddIndexCompression`)
is therefore Fredholm, and the **odd index pairing** `FredholmModule.oddIndexPairing M u` is its
index. It is a homomorphism from the group of units of `A` to `ℤ`
(`FredholmModule.oddIndexPairing_mul`), and it is invariant under unitary equivalence.

These pairings are the analytic side of the index theorem for the Chern character of a finitely
summable Fredholm module, which identifies them with the cyclic pairings
`TauCeti.cyclicCohomology.evenPairing` and `TauCeti.cyclicCohomology.oddPairing`.

## Main definitions

* `TauCeti.EvenFredholmModule.indexCompression`, `TauCeti.EvenFredholmModule.indexPairing`: the
  compression `π(e) F π(e) : π(e) H⁺ → π(e) H⁻` and its index.
* `TauCeti.FredholmModule.unitizedRep`: the unital multiplicative map `a ↦ π(a) + 1 - π(1)`.
* `TauCeti.FredholmModule.oddIndexCompression`, `TauCeti.FredholmModule.oddIndexPairing`: the
  compression `P (π(u) + 1 - π(1)) P` and its index.

## Main results

* `TauCeti.EvenFredholmModule.operator_mul_halfOneAdd_grading`: `F` maps `H⁺` to `H⁻`.
* `TauCeti.EvenFredholmModule.isFredholm_indexCompression`: the even compression is Fredholm.
* `TauCeti.EvenFredholmModule.indexPairing_perturb`, `TauCeti.EvenFredholmModule.indexPairing_conj`:
  invariance of the even pairing under relatively compact perturbations and unitary equivalence.
* `TauCeti.EvenFredholmModule.indexPairing_eq_finrank_sub`: the even pairing in finite dimension.
* `TauCeti.FredholmModule.isFredholm_oddIndexCompression`: the odd compression is Fredholm.
* `TauCeti.FredholmModule.oddIndexPairing_mul`, `TauCeti.FredholmModule.oddIndexPairing_one`,
  `TauCeti.FredholmModule.oddIndexPairing_inv`: the odd pairing is a group homomorphism.
* `TauCeti.FredholmModule.oddIndexPairing_conj`: invariance of the odd pairing under unitary
  equivalence.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part I,
  Appendix 2, Proposition 5.
* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §1, Proposition 4.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), §8.7.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap

variable {A H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Compactness of the defect of a compressed Fredholm operator -/

/-- For an idempotent `E` of a ring, `E F E F E - E` is `E F (E F - F E) E + E (F² - 1) E`. -/
private theorem mul_operator_mul_sq_sub_eq {R : Type*} [Ring R] {E F : R}
    (hE : IsIdempotentElem E) :
    E * F * E * F * E - E = E * F * (E * F - F * E) * E + E * ((F * F - 1) * E) := by
  rw [show E * F * (E * F - F * E) * E + E * ((F * F - 1) * E) =
      E * F * E * F * E - E * F * F * (E * E) + E * F * F * E - E * E by noncomm_ring, hE.eq]
  abel

namespace FredholmModule

variable [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A] (M : FredholmModule A H)

/-- The commutator `[π(a), F]` is compact. -/
private theorem isCompactOperator_rep_mul_operator_sub (a : A) :
    IsCompactOperator (M.rep a * M.operator - M.operator * M.rep a) :=
  isCompactOperator_sub_comm.1 (M.isCompactOperator_commutator a)

/-- The commutator of `(1 + F) / 2` with `π(a)` is half that of `F`, hence compact. -/
theorem isCompactOperator_halfOneAdd_operator_commutator (a : A) :
    IsCompactOperator (halfOneAdd ℂ M.operator * M.rep a - M.rep a * halfOneAdd ℂ M.operator) := by
  have h : halfOneAdd ℂ M.operator * M.rep a - M.rep a * halfOneAdd ℂ M.operator =
      (⅟2 : ℂ) • (M.operator * M.rep a - M.rep a * M.operator) := by
    rw [halfOneAdd_def, smul_mul_assoc, mul_smul_comm, ← smul_sub, add_mul, mul_add, one_mul,
      mul_one, add_sub_add_left_eq_sub]
  rw [h]
  exact (M.isCompactOperator_commutator a).smul _

/-- For an idempotent `e`, the operator `π(e) F π(e)` squares to `π(e)` modulo compact
operators. -/
private theorem isCompactOperator_rep_mul_operator_mul_rep_mul_operator_mul_rep_sub {e : A}
    (he : IsIdempotentElem e) :
    IsCompactOperator (M.rep e * M.operator * M.rep e * M.operator * M.rep e - M.rep e) := by
  rw [mul_operator_mul_sq_sub_eq (he.map M.rep)]
  exact (((M.isCompactOperator_rep_mul_operator_sub e).mul_left _).mul_right _).add
    ((M.isCompactOperator_mul_self_sub_one_mul e).mul_left _)

end FredholmModule

/-! ### The even index pairing -/

/-- For idempotents `E P` and `E Q`, where `P` commutes with `E` and `F` carries the range of `P`
to that of `Q`, the defect of the compressed operator `(E P) F (E Q) F (E P) - E P` is
`P (E F E F E - E) P`. -/
private theorem mul_mul_mul_mul_mul_sub_eq {R : Type*} [Ring R] {E F P Q : R}
    (hP : IsIdempotentElem P) (hEP : Commute E P) (hQF : Q * F = F * P) :
    E * P * F * (E * Q) * F * (E * P) - E * P = P * (E * F * E * F * E - E) * P := by
  have h₁ : E * P * F * (E * Q) * F * (E * P) = P * (E * F * E * F * E) * P := by
    have hQ : Q * (F * (E * P)) = F * (P * (E * P)) := by rw [← mul_assoc, hQF, mul_assoc]
    have hPEP : P * (E * P) = E * P := by rw [← mul_assoc, ← hEP.eq, mul_assoc, hP.eq]
    simp only [mul_assoc]
    rw [hQ, hPEP]
    exact (hEP.symm.left_comm _).symm
  have h₂ : E * P = P * E * P := by
    rw [← hEP.eq, mul_assoc, hP.eq]
  rw [h₁, h₂, mul_sub, sub_mul]

namespace EvenFredholmModule

variable [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A] (M : EvenFredholmModule A H)

/-- `F` anticommutes with the grading, so it exchanges the projections `(1 ± γ) / 2`:
`F (1 + γ) / 2 = (1 - γ) / 2 F`. -/
theorem operator_mul_halfOneAdd_grading :
    M.operator * halfOneAdd ℂ M.grading = halfOneAdd ℂ (-M.grading) * M.operator :=
  mul_halfOneAdd_eq_halfOneAdd_neg_mul ℂ M.grading_mul_operator

/-- `F (1 - γ) / 2 = (1 + γ) / 2 F`. -/
theorem operator_mul_halfOneAdd_neg_grading :
    M.operator * halfOneAdd ℂ (-M.grading) = halfOneAdd ℂ M.grading * M.operator := by
  simpa only [neg_neg] using mul_halfOneAdd_eq_halfOneAdd_neg_mul ℂ
    (by rw [neg_mul, mul_neg, M.grading_mul_operator] : -M.grading * M.operator =
      -(M.operator * -M.grading))

/-- For an idempotent `e` and a square root of one `ω` commuting with `π(e)`, the operator
`π(e) (1 + ω) / 2` is idempotent. -/
private theorem isIdempotentElem_rep_mul_halfOneAdd {e : A} (he : IsIdempotentElem e)
    {ω : H →L[ℂ] H} (hω : ω * ω = 1) (hc : Commute ω (M.rep e)) :
    IsIdempotentElem (M.rep e * halfOneAdd ℂ ω) :=
  (he.map M.rep).mul_of_commute (commute_halfOneAdd ℂ hc).symm (isIdempotentElem_halfOneAdd ℂ hω)

/-- The idempotent `π(e) (1 + γ) / 2`, whose range is `π(e) H⁺`. -/
theorem isIdempotentElem_rep_mul_halfOneAdd_grading {e : A} (he : IsIdempotentElem e) :
    IsIdempotentElem (M.rep e * halfOneAdd ℂ M.grading) :=
  M.isIdempotentElem_rep_mul_halfOneAdd he M.grading_mul_grading (M.commute_grading_rep e)

/-- The idempotent `π(e) (1 - γ) / 2`, whose range is `π(e) H⁻`. -/
theorem isIdempotentElem_rep_mul_halfOneAdd_neg_grading {e : A}
    (he : IsIdempotentElem e) : IsIdempotentElem (M.rep e * halfOneAdd ℂ (-M.grading)) :=
  M.isIdempotentElem_rep_mul_halfOneAdd he (by rw [neg_mul_neg, M.grading_mul_grading])
    (M.commute_grading_rep e).neg_left

/-- The **index compression** of an even Fredholm module at `e : A`: the operator
`π(e) F π(e)` from `π(e) H⁺`, the range of `π(e) (1 + γ) / 2`, to `π(e) H⁻`, the range of
`π(e) (1 - γ) / 2`. -/
def indexCompression (e : A) :
    (M.rep e * halfOneAdd ℂ M.grading).range →L[ℂ]
      (M.rep e * halfOneAdd ℂ (-M.grading)).range :=
  compress (M.rep e * halfOneAdd ℂ M.grading) (M.rep e * halfOneAdd ℂ (-M.grading)) M.operator

/-- The index compression is the compression of `F` by `π(e) (1 + γ) / 2` and
`π(e) (1 - γ) / 2`. -/
theorem indexCompression_eq_compress (e : A) :
    M.indexCompression e =
      compress (M.rep e * halfOneAdd ℂ M.grading) (M.rep e * halfOneAdd ℂ (-M.grading))
        M.operator :=
  (rfl)

/-- The index compression acts by `x ↦ π(e) F x`. -/
theorem coe_indexCompression_apply (e : A) (x : (M.rep e * halfOneAdd ℂ M.grading).range) :
    (M.indexCompression e x : H) = M.rep e (M.operator x) := by
  obtain ⟨y, hy⟩ := x.property
  have hP := (isIdempotentElem_halfOneAdd ℂ M.grading_mul_grading).eq
  have hc := (commute_halfOneAdd ℂ (M.commute_grading_rep e)).eq
  -- As operators, `π(e) (1 - γ)/2 F π(e) (1 + γ)/2 = π(e) F π(e) (1 + γ)/2`.
  have h : M.rep e * halfOneAdd ℂ (-M.grading) * M.operator * (M.rep e * halfOneAdd ℂ M.grading) =
      M.rep e * M.operator * (M.rep e * halfOneAdd ℂ M.grading) :=
    calc _ = M.rep e * (halfOneAdd ℂ (-M.grading) * M.operator) * M.rep e *
          halfOneAdd ℂ M.grading := by simp only [mul_assoc]
      _ = M.rep e * M.operator * M.rep e * (halfOneAdd ℂ M.grading * halfOneAdd ℂ M.grading) := by
        rw [← operator_mul_halfOneAdd_grading]
        simp only [mul_assoc, hc]
      _ = M.rep e * M.operator * (M.rep e * halfOneAdd ℂ M.grading) := by
        rw [hP]
        simp only [mul_assoc]
  have hx : (x : H) = (M.rep e * halfOneAdd ℂ M.grading) y := hy.symm
  rw [indexCompression_eq_compress, coe_compress_apply, hx]
  simpa only [mul_apply_eq_comp] using congr($h y)

/-- **The even compression is Fredholm.** For an idempotent `e` of `A`, the compression
`π(e) F π(e) : π(e) H⁺ → π(e) H⁻` is a Fredholm operator. -/
theorem isFredholm_indexCompression {e : A} (he : IsIdempotentElem e) :
    (M.indexCompression e).IsFredholm := by
  have hX :=
    M.toFredholmModule.isCompactOperator_rep_mul_operator_mul_rep_mul_operator_mul_rep_sub he
  refine isFredholm_compress (S := M.operator) (M.isIdempotentElem_rep_mul_halfOneAdd_grading he)
    (M.isIdempotentElem_rep_mul_halfOneAdd_neg_grading he) ?_ ?_
  · rw [mul_mul_mul_mul_mul_sub_eq (isIdempotentElem_halfOneAdd ℂ M.grading_mul_grading)
      (commute_halfOneAdd ℂ (M.commute_grading_rep e)).symm
      M.operator_mul_halfOneAdd_grading.symm]
    exact (hX.mul_left _).mul_right _
  · rw [mul_mul_mul_mul_mul_sub_eq (isIdempotentElem_halfOneAdd_neg ℂ M.grading_mul_grading)
      (commute_halfOneAdd ℂ (M.commute_grading_rep e).neg_left).symm
      M.operator_mul_halfOneAdd_neg_grading.symm]
    exact (hX.mul_left _).mul_right _

/-- The **index pairing** of an even Fredholm module with `e : A`: the Fredholm index of the
compression `π(e) F π(e) : π(e) H⁺ → π(e) H⁻`. It is meaningful for idempotent `e`, where that
compression is Fredholm (`EvenFredholmModule.isFredholm_indexCompression`). -/
def indexPairing (e : A) : ℤ :=
  (M.indexCompression e).index

/-- The even index pairing is the index of the index compression. -/
theorem indexPairing_eq_index (e : A) : M.indexPairing e = (M.indexCompression e).index :=
  (rfl)

/-- The index pairing with the zero idempotent vanishes. -/
@[simp]
theorem indexPairing_zero : M.indexPairing 0 = 0 := by
  have : Subsingleton (M.rep 0 * halfOneAdd ℂ M.grading).range := by
    rw [map_zero, zero_mul, toLinearMap_zero, LinearMap.range_zero]
    infer_instance
  have : Subsingleton (M.rep 0 * halfOneAdd ℂ (-M.grading)).range := by
    rw [map_zero, zero_mul, toLinearMap_zero, LinearMap.range_zero]
    infer_instance
  exact index_eq_zero_of_bijective _
    ⟨Function.injective_of_subsingleton _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The even index pairing in finite dimension**: on a finite-dimensional Hilbert space it is
`dim π(e) H⁺ - dim π(e) H⁻`. -/
theorem indexPairing_eq_finrank_sub [FiniteDimensional ℂ H] (e : A) :
    M.indexPairing e = (Module.finrank ℂ (M.rep e * halfOneAdd ℂ M.grading).range : ℤ) -
      Module.finrank ℂ (M.rep e * halfOneAdd ℂ (-M.grading)).range :=
  index_eq_of_finiteDimensional _

/-- **Invariance under relatively compact perturbations.** Replacing `F` by `F + K`, for a
self-adjoint `K` anticommuting with the grading with `K π(a)` compact for every `a`, does not
change the index pairing with an idempotent. -/
theorem indexPairing_perturb (K : H →L[ℂ] H) (hK : IsSelfAdjoint K)
    (hKc : ∀ a, IsCompactOperator (K * M.rep a)) (hγK : M.grading * K = -(K * M.grading))
    {e : A} (he : IsIdempotentElem e) :
    (M.perturb K hK hKc hγK).indexPairing e = M.indexPairing e := by
  have hKp : IsCompactOperator (K * (M.rep e * halfOneAdd ℂ M.grading)) := by
    rw [← mul_assoc]
    exact (hKc e).mul_right _
  rw [indexPairing_eq_index, indexPairing_eq_index, indexCompression_eq_compress,
    indexCompression_eq_compress, perturb_toFredholmModule, FredholmModule.perturb_rep,
    FredholmModule.perturb_operator, perturb_grading]
  exact index_compress_add_of_isCompactOperator
    (M.isIdempotentElem_rep_mul_halfOneAdd_grading he)
    (M.isIdempotentElem_rep_mul_halfOneAdd_neg_grading he)
    (M.isFredholm_indexCompression he) hKp

/-- **Invariance under unitary equivalence.** Transporting an even Fredholm module along a
unitary does not change its index pairing. -/
@[simp]
theorem indexPairing_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') (e : A) :
    (M.conj U).indexPairing e = M.indexPairing e := by
  -- The compressing idempotents of `M.conj U` are the conjugates by `U` of those of `M`.
  have hP (ω : H →L[ℂ] H) : (M.conj U).rep e * halfOneAdd ℂ (U.conjStarAlgEquiv ω) =
      U.conjStarAlgEquiv (M.rep e * halfOneAdd ℂ ω) := by
    rw [map_mul, map_halfOneAdd, conj_toFredholmModule, FredholmModule.conj_rep_apply]
  rw [indexPairing_eq_index, indexPairing_eq_index, indexCompression_eq_compress,
    indexCompression_eq_compress, conj_grading, ← map_neg, hP, hP, conj_toFredholmModule,
    FredholmModule.conj_operator, index_compress_conjStarAlgEquiv]

end EvenFredholmModule

/-! ### The odd index pairing -/

namespace FredholmModule

variable [Semiring A] [Module ℂ A] [Star A] (M : FredholmModule A H)

/-- The **unitized representation** `a ↦ π(a) + 1 - π(1)`, the unitization `MulHom.unitize` of
`π`: it agrees with `π` on `π(1) H` and is the identity on the complement `(1 - π(1)) H`, so it is
multiplicative and unital even when `π` is not. -/
def unitizedRep : A →* H →L[ℂ] H :=
  MulHom.unitize M.rep

/-- The unitized representation of `a` is `π(a) + 1 - π(1)`. -/
@[simp]
theorem unitizedRep_apply (a : A) : M.unitizedRep a = M.rep a + (1 - M.rep 1) := by
  rw [unitizedRep, MulHom.unitize_apply, MulHom.coe_coe]

/-- The unitized representation commutes with `(1 + F) / 2` modulo compact operators. -/
theorem isCompactOperator_halfOneAdd_operator_unitizedRep_commutator (a : A) :
    IsCompactOperator (halfOneAdd ℂ M.operator * M.unitizedRep a -
      M.unitizedRep a * halfOneAdd ℂ M.operator) := by
  have h : halfOneAdd ℂ M.operator * M.unitizedRep a - M.unitizedRep a * halfOneAdd ℂ M.operator =
      (halfOneAdd ℂ M.operator * M.rep a - M.rep a * halfOneAdd ℂ M.operator) -
        (halfOneAdd ℂ M.operator * M.rep 1 - M.rep 1 * halfOneAdd ℂ M.operator) := by
    rw [unitizedRep_apply]
    noncomm_ring
  rw [h]
  exact (M.isCompactOperator_halfOneAdd_operator_commutator a).sub
    (M.isCompactOperator_halfOneAdd_operator_commutator 1)

/-- The **odd index compression** of a Fredholm module at a unit `u` of `A`: the operator
`P (π(u) + 1 - π(1)) P` on the range of `P = (1 + F) / 2`. -/
def oddIndexCompression (u : Aˣ) :
    (halfOneAdd ℂ M.operator).range →L[ℂ] (halfOneAdd ℂ M.operator).range :=
  compress (halfOneAdd ℂ M.operator) (halfOneAdd ℂ M.operator) (M.unitizedRep u)

/-- The odd index compression is the compression of `π(u) + 1 - π(1)` by `(1 + F) / 2`. -/
theorem oddIndexCompression_eq_compress (u : Aˣ) :
    M.oddIndexCompression u =
      compress (halfOneAdd ℂ M.operator) (halfOneAdd ℂ M.operator) (M.unitizedRep u) :=
  (rfl)

/-- The odd index compression acts by `x ↦ P (π(u) + 1 - π(1)) x`. -/
@[simp]
theorem coe_oddIndexCompression_apply (u : Aˣ) (x : (halfOneAdd ℂ M.operator).range) :
    (M.oddIndexCompression u x : H) = halfOneAdd ℂ M.operator (M.unitizedRep u x) :=
  coe_compress_apply _ _ _ x

/-- **The odd compression is Fredholm.** If `F² = 1`, then for every unit `u` of `A` the
compression `P (π(u) + 1 - π(1)) P` to the range of `P = (1 + F) / 2` is a Fredholm operator. -/
theorem isFredholm_oddIndexCompression (hF : M.operator * M.operator = 1) (u : Aˣ) :
    (M.oddIndexCompression u).IsFredholm :=
  isFredholm_compress_self (isIdempotentElem_halfOneAdd ℂ hF)
    (S := M.unitizedRep ↑u⁻¹) (by rw [← map_mul, Units.inv_mul, map_one])
    (by rw [← map_mul, Units.mul_inv, map_one])
    (M.isCompactOperator_halfOneAdd_operator_unitizedRep_commutator u)

/-- The **odd index pairing** of a Fredholm module with a unit `u` of `A`: the Fredholm index of the
compression `P (π(u) + 1 - π(1)) P` to the range of `P = (1 + F) / 2`. It is meaningful when
`F² = 1`, where that compression is Fredholm (`FredholmModule.isFredholm_oddIndexCompression`). -/
def oddIndexPairing (u : Aˣ) : ℤ :=
  (M.oddIndexCompression u).index

/-- The odd index pairing is the index of the odd index compression. -/
theorem oddIndexPairing_eq_index (u : Aˣ) :
    M.oddIndexPairing u = (M.oddIndexCompression u).index :=
  (rfl)

/-- When `F² = 1`, the index pairing with the unit `1` vanishes. -/
theorem oddIndexPairing_one (hF : M.operator * M.operator = 1) : M.oddIndexPairing 1 = 0 := by
  rw [oddIndexPairing_eq_index, oddIndexCompression_eq_compress, Units.val_one, map_one,
    compress_one (isIdempotentElem_halfOneAdd ℂ hF)]
  exact index_id

/-- **The odd index pairing is multiplicative.** When `F² = 1`, the index pairing with a product
of units is the sum of the index pairings. -/
theorem oddIndexPairing_mul (hF : M.operator * M.operator = 1) (u v : Aˣ) :
    M.oddIndexPairing (u * v) = M.oddIndexPairing u + M.oddIndexPairing v := by
  simp only [oddIndexPairing_eq_index, oddIndexCompression_eq_compress, Units.val_mul, map_mul]
  exact index_compress_mul (isIdempotentElem_halfOneAdd ℂ hF)
    (M.isFredholm_oddIndexCompression hF u) (M.isFredholm_oddIndexCompression hF v)
    (isCompactOperator_sub_comm.1
      (M.isCompactOperator_halfOneAdd_operator_unitizedRep_commutator v))

/-- When `F² = 1`, the index pairing with the inverse of a unit is the negative of the index
pairing with the unit. -/
theorem oddIndexPairing_inv (hF : M.operator * M.operator = 1) (u : Aˣ) :
    M.oddIndexPairing u⁻¹ = -M.oddIndexPairing u := by
  have h := M.oddIndexPairing_mul hF u⁻¹ u
  rw [inv_mul_cancel, M.oddIndexPairing_one hF] at h
  omega

/-- **Invariance under unitary equivalence.** Transporting a Fredholm module along a unitary does
not change its index pairing. -/
@[simp]
theorem oddIndexPairing_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') (u : Aˣ) :
    (M.conj U).oddIndexPairing u = M.oddIndexPairing u := by
  have hT : (M.conj U).unitizedRep u = U.conjStarAlgEquiv (M.unitizedRep u) := by
    rw [unitizedRep_apply, unitizedRep_apply, conj_rep_apply, conj_rep_apply, map_add, map_sub,
      map_one U.conjStarAlgEquiv]
  rw [oddIndexPairing_eq_index, oddIndexPairing_eq_index, oddIndexCompression_eq_compress,
    oddIndexCompression_eq_compress, conj_operator, ← map_halfOneAdd, hT,
    index_compress_conjStarAlgEquiv]

end FredholmModule

end TauCeti
