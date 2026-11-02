/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Golay.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionB.Minimum
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality

/-!
# The Construction B lattice of the extended binary Golay code

Construction B applied to the extended binary Golay code is the lattice of integer vectors in
`ℚ^(Fin 24)` reducing to a Golay codeword modulo two and having coordinate sum divisible by four,
with the halved dot product. It is the kernel of half the coordinate sum modulo two on the
unimodular Golay Construction A lattice, so it has index two there and discriminant four. It is
positive definite, even, and of rank `24`.

This is the half-lattice of the Construction B model of the Leech lattice: the Leech lattice is
the union of it and one odd shifted coset. Every nonzero vector of the half-lattice has norm at
least `4`. Under the congruence conditions describing the Leech lattice in the coordinates
`x = a / 2`, every nonzero admissible integer vector `a` has `∑ aᵢ² ≥ 32`. Both bounds use the
minimum distance `8` of the Golay code; the second also uses the divisibility of its weights by
four.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11, and
  Chapter 10, §1.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti.BinaryGolay

/-- **The Construction B lattice of the extended binary Golay code**: the integer vectors of
`ℚ^(Fin 24)` reducing to a Golay codeword modulo two whose coordinate sum is divisible by four,
with the dot product halved. -/
noncomputable def constructionBLattice : IntegralLattice (Fin 24 → ℚ) :=
  ConstructionB.integralLattice code isDoublyEven_code.isSelfOrthogonal

/-- The Golay Construction B carrier is the Construction B carrier of the Golay code. -/
@[simp]
theorem constructionBLattice_carrier :
    constructionBLattice.carrier = ConstructionB.lattice code :=
  ConstructionB.integralLattice_carrier _ _

/-- The Golay Construction B form is the halved coordinate dot product. -/
@[simp]
theorem constructionBLattice_form : constructionBLattice.form = ConstructionA.form 2 :=
  ConstructionB.integralLattice_form _ _

/-- The Golay Construction B lattice is a sublattice of the Golay Construction A lattice. -/
theorem constructionBLattice_carrier_le :
    constructionBLattice.carrier ≤ constructionALattice.carrier := by
  rw [constructionBLattice_carrier, constructionALattice_carrier]
  exact ConstructionB.lattice_le code

/-- **The Golay Construction B lattice has index two in the Golay Construction A lattice.** -/
theorem relIndex_constructionBLattice :
    constructionBLattice.carrier.toAddSubgroup.relIndex
      constructionALattice.carrier.toAddSubgroup = 2 := by
  rw [constructionBLattice_carrier, constructionALattice_carrier]
  exact ConstructionB.relIndex_lattice code isDoublyEven_code.isEven

/-- The Golay Construction B lattice is nondegenerate. -/
instance instIsNondegenerateConstructionBLattice : constructionBLattice.IsNondegenerate :=
  ConstructionB.isNondegenerate_integralLattice _ _

/-- The Golay Construction B lattice has rank `24`. -/
@[simp]
theorem finrank_constructionBLattice : Module.finrank ℤ constructionBLattice = 24 := by
  rw [constructionBLattice, ConstructionB.finrank_integralLattice, Fintype.card_fin]

/-- The Golay Construction B lattice is positive definite. -/
theorem isPosDef_constructionBLattice : constructionBLattice.IsPosDef :=
  ConstructionB.isPosDef_integralLattice _ _

/-- **The Golay Construction B lattice is even.** -/
theorem isEven_constructionBLattice : constructionBLattice.IsEven :=
  ConstructionB.isEven_integralLattice isDoublyEven_code

/-- **The Golay Construction B lattice has discriminant four**, being of index two in the
unimodular Golay Construction A lattice. -/
@[simp]
theorem discriminant_constructionBLattice : constructionBLattice.discriminant = 4 := by
  rw [constructionBLattice, ConstructionB.discriminant_integralLattice,
    ← constructionALattice_eq_integralLattice,
    constructionALattice.isUnimodular_iff_discriminant_eq_one.mp
      isUnimodular_constructionALattice]

/-- The discriminant group of the Golay Construction B lattice has order four. -/
@[simp]
theorem natCard_discriminantGroup_constructionBLattice :
    Nat.card constructionBLattice.DiscriminantGroup = 4 := by
  rw [IntegralLattice.natCard_discriminantGroup, discriminant_constructionBLattice]

/-- **The Golay Construction B lattice has no nonzero vector of norm less than four**, since the
Golay code has minimum distance eight. -/
theorem four_le_norm_constructionBLattice {x : Fin 24 → ℚ}
    (hx : x ∈ constructionBLattice.carrier) (hne : x ≠ 0) : 4 ≤ constructionBLattice.norm x := by
  rw [IntegralLattice.norm_apply, constructionBLattice_form]
  rw [constructionBLattice_carrier] at hx
  exact ConstructionB.four_le_form_self (fun _ ↦ eight_le_hammingNorm) hx hne

/-- **The norm bound for the Leech lattice in congruence coordinates.** Let `m ∈ {0, 1}` and let
`b` be an integer vector reducing to a Golay codeword modulo two, and put `a = 2b + m 𝟙`. If
`∑ aᵢ ≡ 4m (mod 8)` and `a ≠ 0`, then `∑ aᵢ² ≥ 32`. These are the congruence conditions that
describe the Leech lattice in the coordinates `x = a / 2`, in which the halved dot product of `x`
with itself is `∑ aᵢ² / 8`; so the bound says that such an `x` has norm at least `4`. -/
theorem thirtyTwo_le_sum_sq {m : ℤ} (hm : m = 0 ∨ m = 1) {b : Fin 24 → ℤ}
    (hb : (fun i ↦ (b i : ZMod 2)) ∈ code) (hsum : ∑ i, (2 * b i + m) ≡ 4 * m [ZMOD 8])
    (hne : (fun i ↦ 2 * b i + m) ≠ 0) : 32 ≤ ∑ i, (2 * b i + m) ^ 2 := by
  rcases hm with rfl | rfl
  · -- The even coset: `b` is a nonzero Construction B vector.
    simp only [add_zero, mul_zero] at hsum hne ⊢
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hne (funext fun i ↦ by simp)
    have h4 : 4 ∣ ∑ i, b i := by
      rw [← Finset.mul_sum, Int.ModEq] at hsum
      omega
    have h8 := ConstructionB.eight_le_sum_sq (fun _ ↦ eight_le_hammingNorm) hb h4 hb0
    simp_rw [mul_pow, ← Finset.mul_sum]
    omega
  · -- The odd coset, of length `24`.
    simp only [mul_one] at hsum ⊢
    simpa using ConstructionB.card_add_eight_le_sum_sq isDoublyEven_code (by simp) hb hsum

end TauCeti.BinaryGolay
