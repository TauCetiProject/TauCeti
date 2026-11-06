/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Regular.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis

/-!
# Volume operators on real regular Clifford spinors

The external opposite-sign action on a regular Clifford module is parity-twisted right
multiplication. The ordered-product formulas in
`TauCeti.LinearAlgebra.CliffordAlgebra.Regular.Basic` identify the action of an orthogonal
product with right multiplication in even length, and parity followed by right multiplication
in odd length. Here these formulas show that the positive external volume on negative regular
spinors is right multiplication by the raw negative volume in even rank.

In rank divisible by four, `CliffordAlgebra.volumeElement_mul_self` and
`CliffordAlgebra.involute_eq_volumeElement_mul_mul` in
`TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Oriented` show that the raw negative
volume squares to one and its left and right multiplication recover the grade involution.
Here we compare the external volume with complex chirality: in rank four chirality is minus
the raw left volume, whereas in rank eight it is the raw left volume.

The action is the existing `CliffordAlgebra.parityTwistedRightAction`; the volume
is `CliffordAlgebra.volumeElement`, defined through the Clifford/exterior equivalence.
No global norm, star or Clifford module instance is introduced.

## Main results

* `CliffordAlgebra.parityTwistedRightAction_volumeElement`: the frame-independent
  formula for the external volume in every rank.
* `CliffordAlgebra.parityTwistedRightAction_volumeElement_of_even`: in even rank, the
  external volume acts by ordinary right multiplication by the original volume.
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
