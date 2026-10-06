/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Ring.Fin
public import TauCeti.Algebra.Star.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Center
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four
public import TauCeti.RingTheory.Idempotents.Corner

/-!
# Four-dimensional Spin groups with split centre

Suppose the centre of the even Clifford algebra of a regular four-dimensional quadratic space is
identified with `K × K`. The two coordinate idempotents pull back to a complete orthogonal pair of
central idempotents in the even Clifford algebra. They cut that algebra into two central corners,
and Clifford reversal restricts to an involution on each corner because it fixes the centre
pointwise in dimension four.

This file constructs the resulting algebra equivalence with the product of the corners and proves
that it carries reversal to componentwise star. The low-rank equality between Spin and the even
unitary carrier then identifies the Spin group with the product of the two corner unitary groups.
Forward and inverse equations expose the corner projections and their reconstruction inside the
Clifford algebra, while the component equations record both reverse norms.

The construction does not assume a model for either corner. In applications, identifying the two
corners as quaternion algebras turns their unitary groups into the corresponding norm-one groups.

## Main definitions and results

* `CliffordAlgebra.splitCenterIdempotent` is the pair of central idempotents selected by a centre
  equivalence with `K × K`.
* `CliffordAlgebra.splitEvenCorner` is either central corner of the even Clifford algebra, equipped
  with the reversal star in dimension four.
* `CliffordAlgebra.evenAlgEquivSplitCenterCorners` decomposes the even Clifford algebra as the
  product of its two central corners and preserves reversal.
* `CliffordAlgebra.spinGroupEquivSplitCenterCorners` identifies the Spin group with the product of
  the two corner unitary groups.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open Module

namespace CliffordAlgebra

universe u v

section CentralIdempotents

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The two central idempotents selected by an algebra equivalence from the centre of the even
Clifford algebra to `R × R`. The index `0` is the preimage of `(1, 0)` and `1` is the preimage of
`(0, 1)`. -/
noncomputable def splitCenterIdempotent (Q : QuadraticForm R M)
    (e : Subalgebra.center R (even Q) ≃ₐ[R] R × R) (i : Fin 2) : even Q :=
  (Subalgebra.val (Subalgebra.center R (even Q))).toRingHom
    (e.symm.toRingEquiv.toRingHom
      ((RingEquiv.piFinTwo (fun _ : Fin 2 ↦ R)).toRingHom (Pi.single i 1)))

/-- The two idempotents selected by a split centre form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_splitCenterIdempotent (Q : QuadraticForm R M)
    (e : Subalgebra.center R (even Q) ≃ₐ[R] R × R) :
    CompleteOrthogonalIdempotents (splitCenterIdempotent Q e) := by
  have h₀ := CompleteOrthogonalIdempotents.single (fun _ : Fin 2 ↦ R)
  have h₁ := h₀.map (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ R)).toRingHom
  have h₂ := h₁.map e.symm.toRingEquiv.toRingHom
  have h₃ := h₂.map (Subalgebra.val (Subalgebra.center R (even Q))).toRingHom
  (convert h₃ using 1; rfl)

/-- Each idempotent selected by a split centre is central in the even Clifford algebra. -/
theorem isMulCentral_splitCenterIdempotent (Q : QuadraticForm R M)
    (e : Subalgebra.center R (even Q) ≃ₐ[R] R × R) (i : Fin 2) :
    IsMulCentral (splitCenterIdempotent Q e i) := by
  apply Semigroup.mem_center_iff.mpr
  exact Subalgebra.mem_center_iff.mp
    (e.symm (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ R) (Pi.single i 1))).2

end CentralIdempotents

section DimensionFour

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- A central corner of the even Clifford algebra selected by one factor of a split centre.

The nondegeneracy and dimension proofs index the canonical star instance, which restricts
Clifford reversal to the corner. -/
abbrev splitEvenCorner (Q : QuadraticForm K V) (_hQ : Q.Nondegenerate)
    (_hV : finrank K V = 4) (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) (i : Fin 2) :=
  ((completeOrthogonalIdempotents_splitCenterIdempotent Q e).idem i).Corner

/-- In dimension four, reversal fixes the central idempotents selected by a split centre. -/
@[simp]
theorem reverseEven_splitCenterIdempotent (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV : finrank K V = 4) (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) (i : Fin 2) :
    reverseEven Q (splitCenterIdempotent Q e i) = splitCenterIdempotent Q e i := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  exact TauCeti.CliffordAlgebra.reverseEven_eq_self_of_mem_center_of_finrank_eq_four hQ hV
    ((e.symm (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ K) (Pi.single i 1))).2)

/-- Clifford reversal restricts to a star operation on either central corner. -/
noncomputable instance splitEvenCornerStar (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV : finrank K V = 4) (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) (i : Fin 2) :
    Star (splitEvenCorner Q hQ hV e i) where
  star x := ⟨reverseEven Q x.1, by
    apply (Subsemigroup.mem_corner_iff
      ((completeOrthogonalIdempotents_splitCenterIdempotent Q e).idem i)).2
    have hx := (Subsemigroup.mem_corner_iff
      ((completeOrthogonalIdempotents_splitCenterIdempotent Q e).idem i)).1 x.2
    constructor
    · have hr := congrArg (reverseEven Q) hx.2
      simpa only [reverseEven_mul,
        reverseEven_splitCenterIdempotent Q hQ hV e i] using hr
    · have hr := congrArg (reverseEven Q) hx.1
      simpa only [reverseEven_mul,
        reverseEven_splitCenterIdempotent Q hQ hV e i] using hr⟩

/-- On either central corner, the restricted reversal is involutive and reverses products. -/
noncomputable instance splitEvenCornerStarMul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV : finrank K V = 4) (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) (i : Fin 2) :
    StarMul (splitEvenCorner Q hQ hV e i) where
  star_involutive x := by
    apply Subtype.ext
    exact reverseEven_reverseEven x.1
  star_mul x y := by
    apply Subtype.ext
    exact reverseEven_mul x.1 y.1

/-- A split centre decomposes the even Clifford algebra into its two central corners. -/
noncomputable def evenAlgEquivSplitCenterCorners (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) :
    even Q ≃ₐ[K] splitEvenCorner Q hQ hV e 0 × splitEvenCorner Q hQ hV e 1 := by
  let re := ((completeOrthogonalIdempotents_splitCenterIdempotent Q e).ringEquivOfIsMulCentral
    (isMulCentral_splitCenterIdempotent Q e)).trans
      (RingEquiv.piFinTwo (splitEvenCorner Q hQ hV e))
  have hre (x : even Q) :
      ((re x).1.1, (re x).2.1) =
        (splitCenterIdempotent Q e 0 * x * splitCenterIdempotent Q e 0,
          splitCenterIdempotent Q e 1 * x * splitCenterIdempotent Q e 1) := rfl
  refine { re with commutes' := ?_ }
  intro r
  change re (algebraMap K (even Q) r) =
    algebraMap K (splitEvenCorner Q hQ hV e 0 × splitEvenCorner Q hQ hV e 1) r
  apply Prod.ext <;> apply Subtype.ext
  · have h : (re (algebraMap K (even Q) r)).1.1 =
        splitCenterIdempotent Q e 0 * algebraMap K (even Q) r *
          splitCenterIdempotent Q e 0 := by
      simpa only [Prod.fst] using congrArg Prod.fst (hre (algebraMap K (even Q) r))
    rw [h]
    change splitCenterIdempotent Q e 0 * algebraMap K (even Q) r *
      splitCenterIdempotent Q e 0 =
        algebraMap K (even Q) r * splitCenterIdempotent Q e 0
    rw [(isMulCentral_splitCenterIdempotent Q e 0).comm, mul_assoc,
      (completeOrthogonalIdempotents_splitCenterIdempotent Q e).idem 0 |>.eq]
  · have h : (re (algebraMap K (even Q) r)).2.1 =
        splitCenterIdempotent Q e 1 * algebraMap K (even Q) r *
          splitCenterIdempotent Q e 1 := by
      simpa only [Prod.snd] using congrArg Prod.snd (hre (algebraMap K (even Q) r))
    rw [h]
    change splitCenterIdempotent Q e 1 * algebraMap K (even Q) r *
      splitCenterIdempotent Q e 1 =
        algebraMap K (even Q) r * splitCenterIdempotent Q e 1
    rw [(isMulCentral_splitCenterIdempotent Q e 1).comm, mul_assoc,
      (completeOrthogonalIdempotents_splitCenterIdempotent Q e).idem 1 |>.eq]

omit [Invertible (2 : K)] in
/-- The two coordinates of the central-corner decomposition are the corresponding corner
projections. -/
@[simp]
theorem evenAlgEquivSplitCenterCorners_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) (x : even Q) :
    (((evenAlgEquivSplitCenterCorners Q hQ hV e x).1).1,
      ((evenAlgEquivSplitCenterCorners Q hQ hV e x).2).1) =
      (splitCenterIdempotent Q e 0 * x * splitCenterIdempotent Q e 0,
        splitCenterIdempotent Q e 1 * x * splitCenterIdempotent Q e 1) := by
  rfl

omit [Invertible (2 : K)] in
/-- The inverse central-corner decomposition reconstructs an even Clifford element by adding its
two corner values. -/
@[simp]
theorem evenAlgEquivSplitCenterCorners_symm_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K)
    (x : splitEvenCorner Q hQ hV e 0 × splitEvenCorner Q hQ hV e 1) :
    (evenAlgEquivSplitCenterCorners Q hQ hV e).symm x = (x.1.1 + x.2.1 : even Q) := by
  let re := ((completeOrthogonalIdempotents_splitCenterIdempotent Q e).ringEquivOfIsMulCentral
    (isMulCentral_splitCenterIdempotent Q e)).trans
      (RingEquiv.piFinTwo (splitEvenCorner Q hQ hV e))
  have h : (evenAlgEquivSplitCenterCorners Q hQ hV e).symm x = re.symm x := rfl
  let f := (RingEquiv.piFinTwo (splitEvenCorner Q hQ hV e)).symm x
  calc
    (evenAlgEquivSplitCenterCorners Q hQ hV e).symm x =
        ((completeOrthogonalIdempotents_splitCenterIdempotent Q e).ringEquivOfIsMulCentral
          (isMulCentral_splitCenterIdempotent Q e)).symm f := by
      rw [h, show re = _ from rfl, RingEquiv.symm_trans_apply]
    _ = ∑ i, (f i).1 := rfl
    _ = x.1.1 + x.2.1 := by
      simp [f, RingEquiv.piFinTwo_symm_apply, piFinTwoEquiv_symm_apply]

/-- The central-corner decomposition carries reversal to componentwise star. -/
theorem evenAlgEquivSplitCenterCorners_reverseEven (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) (x : even Q) :
    evenAlgEquivSplitCenterCorners Q hQ hV e (reverseEven Q x) =
      star (evenAlgEquivSplitCenterCorners Q hQ hV e x) := by
  apply Prod.ext <;> apply Subtype.ext
  · change splitCenterIdempotent Q e 0 * reverseEven Q x * splitCenterIdempotent Q e 0 =
      reverseEven Q (splitCenterIdempotent Q e 0 * x * splitCenterIdempotent Q e 0)
    rw [reverseEven_mul, reverseEven_mul,
      reverseEven_splitCenterIdempotent Q hQ hV e 0, mul_assoc]
  · change splitCenterIdempotent Q e 1 * reverseEven Q x * splitCenterIdempotent Q e 1 =
      reverseEven Q (splitCenterIdempotent Q e 1 * x * splitCenterIdempotent Q e 1)
    rw [reverseEven_mul, reverseEven_mul,
      reverseEven_splitCenterIdempotent Q hQ hV e 1, mul_assoc]

/-- In dimension four, a split centre identifies Spin with the product of the reverse-unitary
groups of the two central corners. -/
noncomputable def spinGroupEquivSplitCenterCorners (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) :
    spinGroup Q ≃* unitary (splitEvenCorner Q hQ hV e 0) ×
      unitary (splitEvenCorner Q hQ hV e 1) :=
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  (spinGroupEquivEvenUnitaryOfFinrankLeFour Q hQ (by omega) (by omega)).trans <|
    (evenUnitaryGroupEquivUnitaryOfAlgEquiv Q (evenAlgEquivSplitCenterCorners Q hQ hV e)
      (evenAlgEquivSplitCenterCorners_reverseEven Q hQ hV e)).trans <|
        Unitary.prodEquiv (splitEvenCorner Q hQ hV e 0) (splitEvenCorner Q hQ hV e 1)

/-- The split-centre Spin equivalence evaluates as the two corner projections of the underlying
even Clifford element. -/
@[simp]
theorem spinGroupEquivSplitCenterCorners_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) (s : spinGroup Q) :
    ((((spinGroupEquivSplitCenterCorners Q hQ hV e s).1 :
        splitEvenCorner Q hQ hV e 0)).1,
      (((spinGroupEquivSplitCenterCorners Q hQ hV e s).2 :
        splitEvenCorner Q hQ hV e 1)).1) =
      (splitCenterIdempotent Q e 0 * evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s) *
          splitCenterIdempotent Q e 0,
        splitCenterIdempotent Q e 1 * evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s) *
          splitCenterIdempotent Q e 1) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  rw [spinGroupEquivSplitCenterCorners, MulEquiv.trans_apply, MulEquiv.trans_apply,
    spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  have h := Unitary.coe_prodEquiv_apply
    (splitEvenCorner Q hQ hV e 0) (splitEvenCorner Q hQ hV e 1)
    (evenUnitaryGroupEquivUnitaryOfAlgEquiv Q (evenAlgEquivSplitCenterCorners Q hQ hV e)
      (evenAlgEquivSplitCenterCorners_reverseEven Q hQ hV e) (spinGroupToEvenUnitary Q s))
  rw [coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply] at h
  exact (congrArg (fun p ↦ (p.1.1, p.2.1)) h).trans
    (evenAlgEquivSplitCenterCorners_apply Q hQ hV e _)

/-- The inverse split-centre Spin equivalence reconstructs the Clifford value by adding the two
corner values. -/
@[simp]
theorem coe_spinGroupEquivSplitCenterCorners_symm_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K)
    (q : unitary (splitEvenCorner Q hQ hV e 0) ×
      unitary (splitEvenCorner Q hQ hV e 1)) :
    ((spinGroupEquivSplitCenterCorners Q hQ hV e).symm q : CliffordAlgebra Q) =
      (((q.1 : splitEvenCorner Q hQ hV e 0).1 +
        (q.2 : splitEvenCorner Q hQ hV e 1).1 : even Q) : CliffordAlgebra Q) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let s := (spinGroupEquivSplitCenterCorners Q hQ hV e).symm q
  have hs : evenAlgEquivSplitCenterCorners Q hQ hV e
      (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) =
        ((q.1 : splitEvenCorner Q hQ hV e 0),
          (q.2 : splitEvenCorner Q hQ hV e 1)) := by
    have h := congrArg
      (fun p : unitary (splitEvenCorner Q hQ hV e 0) ×
        unitary (splitEvenCorner Q hQ hV e 1) ↦
          ((p.1 : splitEvenCorner Q hQ hV e 0),
            (p.2 : splitEvenCorner Q hQ hV e 1)))
      ((spinGroupEquivSplitCenterCorners Q hQ hV e).apply_symm_apply q)
    rw [spinGroupEquivSplitCenterCorners, MulEquiv.trans_apply, MulEquiv.trans_apply,
      spinGroupEquivEvenUnitaryOfFinrankLeFour_apply, Unitary.coe_prodEquiv_apply,
      coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply] at h
    exact h
  have h := congrArg (fun x : even Q ↦ (x : CliffordAlgebra Q))
    ((evenAlgEquivSplitCenterCorners Q hQ hV e).symm_apply_eq.mpr hs.symm)
  rw [evenAlgEquivSplitCenterCorners_symm_apply] at h
  simpa [s] using h.symm

/-- Both components of the split-centre Spin equivalence have reverse norm one. -/
theorem spinGroupEquivSplitCenterCorners_norm (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (e : Subalgebra.center K (even Q) ≃ₐ[K] K × K) (s : spinGroup Q) :
    star ((spinGroupEquivSplitCenterCorners Q hQ hV e s).1 :
        splitEvenCorner Q hQ hV e 0) *
        (spinGroupEquivSplitCenterCorners Q hQ hV e s).1 = 1 ∧
      star ((spinGroupEquivSplitCenterCorners Q hQ hV e s).2 :
        splitEvenCorner Q hQ hV e 1) *
        (spinGroupEquivSplitCenterCorners Q hQ hV e s).2 = 1 := by
  exact ⟨Unitary.star_mul_self_of_mem (spinGroupEquivSplitCenterCorners Q hQ hV e s).1.2,
    Unitary.star_mul_self_of_mem (spinGroupEquivSplitCenterCorners Q hQ hV e s).2.2⟩

end DimensionFour

end CliffordAlgebra
