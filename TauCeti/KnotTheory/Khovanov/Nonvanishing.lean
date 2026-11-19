/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic
public import TauCeti.KnotTheory.Khovanov.Parity
public import TauCeti.KnotTheory.PDCode.ChangeCrossing
public import TauCeti.KnotTheory.PDCode.Oriented.VertexResolution

/-!
# The enhanced-state Euler sum and nonvanishing of Khovanov homology

This file evaluates the normalized enhanced-state Euler sum
`TauCeti.OrientedPDCode.enhancedStateEulerSum` (defined in
`TauCeti.KnotTheory.Khovanov.EnhancedState` as the `q = 1` specialization of
`TauCeti.OrientedPDCode.enhancedStateSum`):

`E(D) = ∑_s (-1) ^ (|s| + n₋) 2 ^ k(s)`,

where `|s| = #{i | s i = false}` is the number of `B`-smoothings selected by `s`, `n₋` is the
number of negative crossings of `D`, and `k(s)` is the number of resolved circles of `s`.

Without any planarity hypothesis, `E(D)` is invariant under crossing changes: flipping the
smoothing bit at `i` via `TauCeti.PDCode.flipStateEquiv` preserves `k(s)` on `D.changeCrossing i`
while preserving the parity of `|s| + n₋`
(`TauCeti.OrientedPDCode.enhancedStateEulerSum_changeCrossing`).

When `D` is planar with `c` link components, the quantum-grading parity theorem
`TauCeti.OrientedPDCode.stateQuantumShift_add_stateLoopCount_mod_two` shows two things:

* `E(D)` depends only on the underlying unoriented planar diagram, so reorienting any subset of
  components leaves `E(D)` unchanged
  (`TauCeti.OrientedPDCode.enhancedStateEulerSum_congr_toPDCode`);
* resolving any crossing `c₀` into planar oriented diagrams `D_A` and `D_B` (with any choice of
  component orientations on the two smoothings) satisfies the normalized parity recurrence
  `E(D) = -(-1) ^ c * ((-1) ^ c_A * E(D_A) + (-1) ^ c_B * E(D_B))`
  (`TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing`).

By the same parity theorem every state contributes `(-1) ^ (n + c) (-2) ^ k(s)` to `E(D)`, and the
unoriented state sum `∑ₛ (-2) ^ k(s)` is `(-1) ^ (n + c) 2 ^ c`
(`TauCeti.PDCode.sum_neg_two_pow_stateLoopCount`), so `E(D) = 2 ^ c` for every planar oriented
diagram (`TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_two_pow_componentCount`).

Consequently, over every Noetherian commutative ring `R` satisfying rank-nullity—and in particular
over `ℤ` and `ℚ`—the graded Euler characteristic `χ_q Kh(D; R)` evaluates to `2 ^ c` at `q = 1`,
hence is nonzero, so `Khⁱʲ(D; R)` is nonzero in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` for every planar link diagram, including the empty diagram.

## Main results

* `TauCeti.OrientedPDCode.enhancedStateEulerSum_changeCrossing`: crossing-change invariance of
  `E(D)`.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_congr_toPDCode`: reorientation invariance of `E(D)`
  for planar diagrams.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing` and
  `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_resolveCrossingOriented`: the normalized parity
  recurrence across arbitrary oriented smoothings of a crossing.
* `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_two_pow_componentCount`: `E(D) = 2 ^ c` for
  every planar oriented code `D` with `c` components.
* `TauCeti.OrientedPDCode.eval₂_neg_one_jonesPolynomial`: for a nonempty planar code, evaluating
  the Jones polynomial at `t ^ (1/2) = -1` gives `2 ^ (c - 1)`.
* `TauCeti.OrientedPDCode.eval₂_one_khovanovEulerChar` and
  `TauCeti.OrientedPDCode.khovanovEulerChar_ne_zero`: over any Noetherian commutative ring `R`
  satisfying rank-nullity, `χ_q Kh(D; R)` evaluates to `2 ^ c` at `q = 1` and is nonzero,
  including for the empty diagram.
* `TauCeti.OrientedPDCode.exists_finrank_khovanovHomology_pos` and
  `TauCeti.OrientedPDCode.exists_not_isZero_khovanovHomology` (with explicit specializations to `ℤ`
  and `ℚ`): Khovanov homology is nonzero for every planar oriented link diagram, including the
  empty diagram.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, Theorems 14–15 (p. 107).
-/

public section

open CategoryTheory CategoryTheory.Limits Finset LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ}

/-! ### Crossing-change invariance -/

/-- **Crossing-change invariance of `E(D)`.** Switching crossing `i` between over and under leaves
`E(D)` unchanged, without any planarity assumption. -/
@[simp] theorem enhancedStateEulerSum_changeCrossing (D : OrientedPDCode n) (i : Fin n) :
    (D.changeCrossing i).enhancedStateEulerSum = D.enhancedStateEulerSum := by
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def,
    ← Equiv.sum_comp (PDCode.flipStateEquiv i)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hmod := D.card_false_flipStateEquiv_add_negativeCrossingCount_changeCrossing_mod_two i s
  rw [neg_one_pow_eq_pow_mod_two, hmod, ← neg_one_pow_eq_pow_mod_two, toPDCode_changeCrossing,
    D.toPDCode.stateLoopCount_changeCrossing_flipStateEquiv i s]

/-! ### Planar parity, reorientation invariance, and the normalized recurrence -/

/-- **Reorientation invariance of `E(D)` for planar diagrams.** Two oriented PD-codes sharing the
same underlying planar PD-code have the same enhanced-state Euler sum. -/
theorem enhancedStateEulerSum_congr_toPDCode {D₁ D₂ : OrientedPDCode n}
    (hD₁ : D₁.toPDCode.IsPlanar) (h : D₁.toPDCode = D₂.toPDCode) :
    D₁.enhancedStateEulerSum = D₂.enhancedStateEulerSum := by
  have hmod := negativeCrossingCount_mod_two_congr_toPDCode hD₁ h
  rw [enhancedStateEulerSum_def, enhancedStateEulerSum_def]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [h]
  congr 1
  exact neg_one_pow_congr (by simp only [Nat.even_iff]; omega)

/-- At a single smoothing branch `t : Bool` of crossing `c` of a planar diagram `D`, the signed
state sum over states sending `c ↦ t` equals
`-(-1) ^ D.componentCount * (-1) ^ E.componentCount * E.enhancedStateEulerSum` for **any**
orientation `E` of `D.toPDCode.resolveCrossing c t`. -/
private theorem sum_insertNth_eq_of_toPDCode_resolveCrossing
    (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1)) (t : Bool)
    {E : OrientedPDCode n} (hE : E.toPDCode = D.toPDCode.resolveCrossing c t) :
    (∑ s : Fin n → Bool,
        (-1 : ℤ) ^ (#{j | Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s) j = false} +
            D.negativeCrossingCount) *
          2 ^ D.toPDCode.stateLoopCount (Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s))) =
      -(-1 : ℤ) ^ D.componentCount * ((-1 : ℤ) ^ E.componentCount * E.enhancedStateEulerSum) := by
  have hE_planar : E.toPDCode.IsPlanar := by
    rw [hE]
    exact PDCode.IsPlanar.resolveCrossing D.toPDCode c t hD
  rw [E.enhancedStateEulerSum_def, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hpD := D.stateQuantumShift_add_stateLoopCount_mod_two hD
    (Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s))
  have hpE := E.stateQuantumShift_add_stateLoopCount_mod_two hE_planar s
  have hcD := D.positiveCrossingCount_add_negativeCrossingCount
  have hcE := E.positiveCrossingCount_add_negativeCrossingCount
  have hloop : D.toPDCode.stateLoopCount (Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s)) =
      E.toPDCode.stateLoopCount s := by
    rw [Fin.insertNthEquiv_apply, hE, D.toPDCode.stateLoopCount_insertNth c t s]
  rw [stateQuantumShift_def] at hpD hpE
  have hsign : (-1 : ℤ) ^ (#{j | Fin.insertNthEquiv (fun _ ↦ Bool) c (t, s) j = false} +
        D.negativeCrossingCount) =
      (-1 : ℤ) ^ (1 + D.toPDCode.componentCount + E.toPDCode.componentCount +
        (#{j | s j = false} + E.negativeCrossingCount)) :=
    neg_one_pow_congr (by simp only [Nat.even_iff]; omega)
  rw [hsign, hloop, pow_add, pow_add, pow_add, pow_one]
  ring

/-- **Normalized parity recurrence for `E(D)` across arbitrary oriented smoothings.** For any
planar oriented diagram `D` with `n + 1` crossings, any crossing `c`, and any oriented diagrams
`D_A` and `D_B` whose underlying unoriented codes are the `A`- and `B`-resolutions of `c`
(regardless of how their components are reoriented),
`E(D) = -(-1) ^ D.componentCount * ((-1) ^ D_A.componentCount * E(D_A) +`
`(-1) ^ D_B.componentCount * E(D_B))`. -/
theorem enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing
    (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1))
    {D_A D_B : OrientedPDCode n}
    (hA : D_A.toPDCode = D.toPDCode.resolveCrossing c true)
    (hB : D_B.toPDCode = D.toPDCode.resolveCrossing c false) :
    D.enhancedStateEulerSum =
      -(-1 : ℤ) ^ D.componentCount *
        ((-1 : ℤ) ^ D_A.componentCount * D_A.enhancedStateEulerSum +
          (-1 : ℤ) ^ D_B.componentCount * D_B.enhancedStateEulerSum) := by
  rw [D.enhancedStateEulerSum_def, ← (Fin.insertNthEquiv (fun _ ↦ Bool) c).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_bool,
    D.sum_insertNth_eq_of_toPDCode_resolveCrossing hD c true hA,
    D.sum_insertNth_eq_of_toPDCode_resolveCrossing hD c false hB, mul_add]

/-- Specialization of `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing`
to `TauCeti.OrientedPDCode.resolveCrossingOriented`. -/
theorem enhancedStateEulerSum_eq_resolveCrossingOriented
    (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1))
    (detachedA : Multiset Bool) (hA : detachedA.card = D.toPDCode.detachedCircleCount c true)
    (detachedB : Multiset Bool) (hB : detachedB.card = D.toPDCode.detachedCircleCount c false) :
    D.enhancedStateEulerSum =
      -(-1 : ℤ) ^ D.componentCount *
        ((-1 : ℤ) ^ (D.resolveCrossingOriented c true detachedA hA).componentCount *
            (D.resolveCrossingOriented c true detachedA hA).enhancedStateEulerSum +
          (-1 : ℤ) ^ (D.resolveCrossingOriented c false detachedB hB).componentCount *
            (D.resolveCrossingOriented c false detachedB hB).enhancedStateEulerSum) :=
  D.enhancedStateEulerSum_eq_of_toPDCode_resolveCrossing hD c
    (D.toPDCode_resolveCrossingOriented c true detachedA hA)
    (D.toPDCode_resolveCrossingOriented c false detachedB hB)

/-! ### Closed form `E(D) = 2 ^ c` and evaluations -/

/-- On a planar code, the state `s` with `B`-smoothing set `S` and `k` circles contributes
`(-1) ^ (n + c) (-2) ^ k` to `E(D)`, by the component parity of the quantum grading. -/
private theorem neg_one_pow_mul_two_pow_stateLoopCount (D : OrientedPDCode n)
    (hD : D.toPDCode.IsPlanar) (s : Fin n → Bool) :
    (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) *
        2 ^ D.toPDCode.stateLoopCount s =
      (-1) ^ (n + D.componentCount) * (-2) ^ D.toPDCode.stateLoopCount s := by
  have hpar := D.stateQuantumShift_add_stateLoopCount_mod_two hD s
  have hcount := D.positiveCrossingCount_add_negativeCrossingCount
  have hsign : (D.stateCochainDegree s).negOnePow =
      ((n + D.componentCount + D.toPDCode.stateLoopCount s : ℕ) : ℤ).negOnePow := by
    rw [Int.negOnePow_eq_iff, Int.even_iff, stateCochainDegree_def]
    rw [stateQuantumShift_def] at hpar
    push_cast at hpar ⊢
    omega
  rw [← D.coe_negOnePow_stateCochainDegree, hsign, Int.coe_negOnePow_natCast, neg_pow (2 : ℤ)]
  ring

/-- **For every planar oriented PD-code `D` with `c` link components, `E(D) = 2 ^ c`.** Every state
contributes `(-1) ^ (n + c) (-2) ^ k(s)` by the component parity of the quantum grading, and the
unoriented state sum `∑ₛ (-2) ^ k(s)` is `(-1) ^ (n + c) 2 ^ c`
(`TauCeti.PDCode.sum_neg_two_pow_stateLoopCount`). -/
theorem enhancedStateEulerSum_eq_two_pow_componentCount (D : OrientedPDCode n)
    (hD : D.toPDCode.IsPlanar) : D.enhancedStateEulerSum = (2 : ℤ) ^ D.componentCount := by
  rw [enhancedStateEulerSum_def]
  simp_rw [D.neg_one_pow_mul_two_pow_stateLoopCount hD]
  rw [← Finset.mul_sum, D.toPDCode.sum_neg_two_pow_stateLoopCount, ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨_, rfl⟩, one_mul]

/-- **Evaluating the enhanced state sum of a planar diagram at `q = 1` gives `2 ^ c`.** -/
theorem eval₂_one_enhancedStateSum_eq_two_pow (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) :
    eval₂ (RingHom.id ℤ) 1 D.enhancedStateSum = (2 : ℤ) ^ D.componentCount := by
  rw [D.eval₂_one_enhancedStateSum, D.enhancedStateEulerSum_eq_two_pow_componentCount hD]

/-- **Evaluating the Jones polynomial of a nonempty planar diagram at `t ^ (1/2) = -1` gives
`2 ^ (c - 1)`** (Jones 1985, Theorems 14–15; Lickorish 1997, Chapter 3). -/
theorem eval₂_neg_one_jonesPolynomial (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
    (hpos : 0 < D.toPDCode.componentCount) :
    eval₂ (RingHom.id ℤ) (-1 : ℤˣ) D.jonesPolynomial = (2 : ℤ) ^ (D.componentCount - 1) := by
  have hsum := congrArg (eval₂ (RingHom.id ℤ) (1 : ℤˣ))
    (D.enhancedStateSum_eq_mul_eval₂_jonesPolynomial hpos)
  rw [D.eval₂_one_enhancedStateSum_eq_two_pow hD, map_mul, map_add, eval₂_T, eval₂_T,
    LaurentPolynomial.hom_eval₂] at hsum
  have hhom : (eval₂ (RingHom.id ℤ) (1 : ℤˣ)).comp (Int.castRingHom ℤ[T;T⁻¹]) =
      RingHom.id ℤ := Subsingleton.elim _ _
  have hunit : Units.map (eval₂ (RingHom.id ℤ) (1 : ℤˣ) : ℤ[T;T⁻¹] →* ℤ) (-genericUnit ℤ) =
      (-1 : ℤˣ) := by
    ext
    simp
  rw [hhom, hunit] at hsum
  obtain ⟨k, hk⟩ : ∃ k, D.toPDCode.componentCount = k + 1 := ⟨D.toPDCode.componentCount - 1, by
    omega⟩
  rw [hk, pow_succ'] at hsum
  rw [hk, Nat.add_sub_cancel]
  norm_num at hsum
  omega

/-! ### Graded Euler characteristic and nonvanishing of Khovanov homology -/

section Homology

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- **At `q = 1`, the graded Euler characteristic `χ_q Kh(D; R)` equals `2 ^ c`**, for every
planar oriented diagram over any Noetherian commutative ring `R` satisfying rank-nullity. -/
theorem eval₂_one_khovanovEulerChar :
    eval₂ (RingHom.id ℤ) 1 (D.khovanovEulerChar hD R) = (2 : ℤ) ^ D.componentCount := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R, D.eval₂_one_enhancedStateSum_eq_two_pow hD]

/-- **The graded Euler characteristic of Khovanov homology is nonzero** for every planar oriented
diagram (including the empty diagram) over any Noetherian commutative ring `R` satisfying
rank-nullity. -/
theorem khovanovEulerChar_ne_zero : D.khovanovEulerChar hD R ≠ 0 := by
  intro hzero
  have heval := D.eval₂_one_khovanovEulerChar hD R
  rw [hzero, map_zero] at heval
  exact (by positivity : (0 : ℤ) < (2 : ℤ) ^ D.componentCount).ne heval

/-- **Khovanov homology has positive rank in at least one bidegree `(i, j)` with `i ∈ [-n₋, n₊]`**,
for every planar oriented diagram (including the empty diagram) over any Noetherian commutative
ring `R` satisfying rank-nullity. -/
theorem exists_finrank_khovanovHomology_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  by_contra h
  refine D.khovanovEulerChar_ne_zero hD R
    (AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun j ↦ ?_)
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hzero : Module.finrank R (D.khovanovHomology hD R i j) = 0 :=
    Nat.eq_zero_of_not_pos fun hpos ↦ h ⟨i, hi, j, hpos⟩
  simp [hzero]

/-- **Nonvanishing of Khovanov homology**: for every planar oriented diagram (including the empty
diagram) over any Noetherian commutative ring `R` satisfying rank-nullity, `Khⁱʲ(D; R)` is nonzero
in at least one bidegree `(i, j)` with `i ∈ [-n₋, n₊]`. -/
theorem exists_not_isZero_khovanovHomology :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  exact ⟨i, hi, j, fun hz ↦ hpos.ne' (ModuleCat.finrank_eq_zero_of_isZero hz)⟩

end Homology

section IntAndRat

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)

/-- **Integral Khovanov homology has positive free rank in some bidegree `(i, j)`**, for every
planar oriented diagram including the empty diagram. -/
theorem exists_finrank_khovanovHomology_int_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank ℤ (D.khovanovHomology hD ℤ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℤ

/-- **Integral Khovanov homology is nonzero** for every planar oriented diagram, including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_int :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD ℤ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℤ

/-- **Rational Khovanov homology has positive dimension in some bidegree `(i, j)`**, for every
planar oriented diagram including the empty diagram. -/
theorem exists_finrank_khovanovHomology_rat_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank ℚ (D.khovanovHomology hD ℚ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℚ

/-- **Rational Khovanov homology is nonzero** for every planar oriented diagram, including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_rat :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD ℚ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℚ

end IntAndRat

end TauCeti.OrientedPDCode
