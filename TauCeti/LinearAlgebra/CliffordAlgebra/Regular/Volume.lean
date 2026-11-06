/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Regular.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis

/-!
# Volume operators on real regular Clifford spinors

The external opposite-sign action on a regular Clifford module is parity-twisted right
multiplication. For an orthogonal ordered list of vectors, its product is ordinary right
multiplication by the corresponding Clifford product in even length, and parity followed
by right multiplication in odd length. In particular the positive external volume on
negative regular spinors is right multiplication by the raw negative volume in even rank.

In rank divisible by four the raw negative volume squares to one. Left and right
multiplication by it recover the grade involution. These identities distinguish the
external volume signs from complex chirality; in rank four chirality is minus the raw
left volume, whereas in rank eight it is the raw left volume.

The action is the existing `CliffordAlgebra.parityTwistedRightAction`; the volume
is `CliffordAlgebra.volumeElement`, defined through the Clifford/exterior equivalence.
No global norm, star or Clifford module instance is introduced. The ordered-product
statements work over any commutative ring, including in characteristic two.

## Main results

* `CliffordAlgebra.parityTwistedRightAction_prod_map_ι`: the action of an arbitrary
  ordered product, with its reversal and crossing signs.
* `CliffordAlgebra.parityTwistedRightAction_volumeElement`: the frame-independent
  formula for the external volume in every rank.
* `CliffordAlgebra.parityTwistedRightAction_volumeElement_of_involute_eq_self` and
  `CliffordAlgebra.parityTwistedRightAction_volumeElement_of_involute_eq_neg`: the
  left-volume comparison on the two parity sectors in even rank.
* `CliffordAlgebra.ofBaseChangeAux_parityTwistedRightAction_volumeElement_of_involute_eq_self`:
  the complex chirality comparison, including its rank-four and rank-eight signs.

## References

* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules* (1964), §1.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- On an ordered product, the external action is reversal followed by right multiplication,
with the crossing sign and one grade involution for each vector. No orthogonality is needed. -/
theorem parityTwistedRightAction_prod_map_ι (l : List M) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (l.map (ι (-Q))).prod s =
      (-1 : R) ^ l.length.choose 2 •
        ((involute : CliffordAlgebra Q → CliffordAlgebra Q)^[l.length] s *
          reverse (l.map (ι Q)).prod) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp,
      parityTwistedRightAction_ι, parityTwistedRight_apply, ih]
    -- The new vector crosses all previous factors, adding their length to the sign exponent.
    have hchoose : (l.length + 1).choose 2 = l.length + l.length.choose 2 := by
      simp [Nat.choose_succ_succ]
    simp only [map_smul, map_mul, ← reverse_involute, involute_prod_map_ι,
      mul_smul_comm, smul_mul_assoc, smul_smul, List.map_cons, List.prod_cons,
      reverse.map_mul, reverse_ι, List.length_cons, Function.iterate_succ_apply',
      hchoose, pow_add, mul_assoc]
    rw [mul_comm ((-1 : R) ^ l.length.choose 2)]

/-- For an orthogonal ordered product the reversal and crossing signs cancel. -/
theorem parityTwistedRightAction_prod_map_ι_of_pairwise_isOrtho {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (l.map (ι (-Q))).prod s =
      (involute : CliffordAlgebra Q → CliffordAlgebra Q)^[l.length] s *
        (l.map (ι Q)).prod := by
  rw [parityTwistedRightAction_prod_map_ι, reverse_prod_map_ι_of_pairwise_isOrtho hl,
    mul_smul_comm, smul_smul, ← mul_pow]
  simp

/-- An even orthogonal product in the external algebra acts by right multiplication
by the same ordered product in the original algebra. -/
theorem parityTwistedRightAction_prod_map_ι_of_even {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (hlen : Even l.length) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (l.map (ι (-Q))).prod s = s * (l.map (ι Q)).prod := by
  rw [parityTwistedRightAction_prod_map_ι_of_pairwise_isOrtho Q hl,
    involute_involutive.iterate_even hlen, Function.id_def]

/-- An odd orthogonal product in the external algebra acts by parity followed by right
multiplication by the same ordered product in the original algebra. -/
theorem parityTwistedRightAction_prod_map_ι_of_odd {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (hlen : Odd l.length) (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (l.map (ι (-Q))).prod s = involute s * (l.map (ι Q)).prod := by
  rw [parityTwistedRightAction_prod_map_ι_of_pairwise_isOrtho Q hl,
    involute_involutive.iterate_odd hlen]

section Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n)]
  (Q : QuadraticForm ℝ V) (o : Orientation ℝ V (Fin n))

/-- The external volume acts by the raw right volume, preceded by parity in odd rank.
This formula includes either signed orientation in rank zero and does not require a
negative definite form. -/
theorem parityTwistedRightAction_volumeElement (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (volumeElement (-Q) o) s =
      (involute : CliffordAlgebra Q → CliffordAlgebra Q)^[n] s * volumeElement Q o := by
  obtain ⟨b, hb⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm ℝ Q)
  have hb' : (QuadraticMap.associated (-Q)).IsOrthoᵢ b := by
    intro i j hij
    simpa using hb hij
  have hpair : (Finset.univ.sort.map b).Pairwise Q.IsOrtho :=
    List.pairwise_map.mpr <| (Finset.univ.sort_nodup _).imp fun hij ↦
      QuadraticMap.associated_isOrtho.mp (hb hij)
  rw [volumeElement_eq_inv_smul_basis o b, volumeElement_eq_inv_smul_basis o b,
    basis_eq_prod_map_sort hb', basis_eq_prod_map_sort hb, map_smul,
    LinearMap.smul_apply, parityTwistedRightAction_prod_map_ι_of_pairwise_isOrtho Q hpair,
    mul_smul_comm]
  simp only [List.length_map, Finset.length_sort, Finset.card_univ, Fintype.card_fin,
    Fact.out (p := Module.finrank ℝ V = n)]

/-- In even rank, the external positive volume on negative regular spinors is ordinary
right multiplication by the negative volume. The equality holds for any real form. -/
theorem parityTwistedRightAction_volumeElement_of_even (hn : Even n)
    (s : CliffordAlgebra Q) :
    parityTwistedRightAction Q (volumeElement (-Q) o) s = s * volumeElement Q o := by
  rw [parityTwistedRightAction_volumeElement, involute_involutive.iterate_even hn,
    Function.id_def]

/-- On the even sector in even rank, the external opposite-sign volume and the
left original volume agree. No definiteness hypothesis is needed. -/
theorem parityTwistedRightAction_volumeElement_of_involute_eq_self
    (hn : Even n) {s : CliffordAlgebra Q} (hs : involute s = s) :
    parityTwistedRightAction Q (volumeElement (-Q) o) s = volumeElement Q o * s := by
  rw [parityTwistedRightAction_volumeElement_of_even Q o hn,
    volumeElement_mul_eq_involute_mul o hn, hs]

/-- On the odd sector in even rank, the external opposite-sign volume is minus the
left original volume. Thus the comparison of the two volume signs depends on parity. -/
theorem parityTwistedRightAction_volumeElement_of_involute_eq_neg
    (hn : Even n) {s : CliffordAlgebra Q} (hs : involute s = -s) :
    parityTwistedRightAction Q (volumeElement (-Q) o) s = -(volumeElement Q o * s) := by
  rw [parityTwistedRightAction_volumeElement_of_even Q o hn,
    volumeElement_mul_eq_involute_mul o hn, hs, neg_mul, neg_neg]

/-- On even regular spinors in even rank, scalar extension identifies the external raw
volume with `(-i)^((n+1)/2)` times left complex chirality. In rank four the coefficient
is `-1`, and in rank eight it is `1`. -/
theorem ofBaseChangeAux_parityTwistedRightAction_volumeElement_of_involute_eq_self
    (hn : Even n) {s : CliffordAlgebra Q} (hs : involute s = s) :
    ofBaseChangeAux ℂ Q (parityTwistedRightAction Q (volumeElement (-Q) o) s) =
      (-Complex.I) ^ ((n + 1) / 2) •
        (complexVolume Q o * ofBaseChangeAux ℂ Q s) := by
  rw [parityTwistedRightAction_volumeElement_of_involute_eq_self Q o hn hs,
    complexVolume_def, smul_mul_assoc, ← map_mul, smul_smul, ← mul_pow]
  simp

end Real

end CliffordAlgebra
