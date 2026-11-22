/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs.ModTwo
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.AntipodalPairs
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Isometry

/-!
# Leech minimal pairs in the mod-two module

The type-2 classes of the Leech lattice are the classes in `Λ / 2Λ` represented by vectors
of norm four. They form the set `leechLattice.normClassesModTwo 4`, not a second model
of the mod-two module. The minimum-norm bound identifies these classes with the 98280
antipodal pairs of minimal vectors: the class of a vector determines precisely its sign pair.

`leechAntipodalPairsEquivModTwo` gives this identification and intertwines the full
lattice-isometry action with its existing reduction homomorphism. In particular, the two
actions have the same stabilizers under this equivalence. No quotient of the isometry
group or identification with a sporadic presentation is assumed here.

An isometry acting trivially on `Λ / 2Λ` therefore fixes every minimal pair, so it is identity
or negation by `TauCeti.ker_antipodalPairsHom_leechLattice`. Thus the congruence subgroup of
level two is `{±1}` (`TauCeti.congruenceSubgroup_two_leechLattice`), which makes the induced
action of `Co₁` on `Λ / 2Λ` faithful.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

open IntegralLattice

/-- Twice the norm of every nonzero Leech vector exceeds the minimal norm `4`, as the mod-two
comparison of minimal vectors requires. -/
private theorem four_lt_two_mul_norm_leechLattice (z : leechLattice) (hz : z ≠ 0) :
    (4 : ℚ) < 2 * leechLattice.norm z := by
  have := four_le_norm_leechLattice z.property fun h ↦ hz (Subtype.ext h)
  linarith

/-- The antipodal minimal-vector pairs of the Leech lattice identify with its type-2 residue
classes modulo twice the lattice. -/
noncomputable def leechAntipodalPairsEquivModTwo :
    leechLattice.antipodalPairs 4 ≃ leechLattice.normClassesModTwo 4 :=
  leechLattice.antipodalPairsEquivModTwo four_lt_two_mul_norm_leechLattice

/-- The Leech identification is the sign-independent pair-to-residue map. -/
theorem leechAntipodalPairsEquivModTwo_apply (p : leechLattice.antipodalPairs 4) :
    leechAntipodalPairsEquivModTwo p = leechLattice.antipodalPairsToModTwo 4 p := by
  unfold leechAntipodalPairsEquivModTwo
  rw [antipodalPairsEquivModTwo_apply]

/-- Evaluate the Leech identification on an explicit minimal pair. -/
@[simp]
theorem coe_leechAntipodalPairsEquivModTwo_mk (x : leechLattice)
    (hp : s(x, -x) ∈ leechLattice.antipodalPairs 4) :
    (leechAntipodalPairsEquivModTwo ⟨s(x, -x), hp⟩ :
      QuotSMulTop (2 : ℤ) leechLattice) = Submodule.Quotient.mk x := by
  rw [leechAntipodalPairsEquivModTwo_apply, coe_antipodalPairsToModTwo_mk]

/-- The inverse Leech identification recovers the sign pair of a minimal representative. -/
@[simp]
theorem leechAntipodalPairsEquivModTwo_symm_mk (x : leechLattice)
    (hx : x ∈ leechLattice.vectorsOfNorm 4)
    (hc : (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) leechLattice) ∈
      leechLattice.normClassesModTwo 4) :
    leechAntipodalPairsEquivModTwo.symm ⟨Submodule.Quotient.mk x, hc⟩ =
      ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ := by
  apply leechAntipodalPairsEquivModTwo.symm_apply_eq.mpr
  exact Subtype.ext (coe_leechAntipodalPairsEquivModTwo_mk x _).symm

/-- There are exactly 98280 type-2 classes in the Leech mod-two module. -/
theorem ncard_normClassesModTwo_four_leechLattice :
    (leechLattice.normClassesModTwo 4).ncard = 98280 :=
  (Set.ncard_congr' leechAntipodalPairsEquivModTwo).symm.trans
    ncard_antipodalPairs_four_leechLattice

/-- The identification of minimal pairs with type-2 classes is equivariant for the actual
Leech lattice isometry group and its reduction on `Λ / 2Λ`. -/
theorem coe_leechAntipodalPairsEquivModTwo_antipodalPairsEquiv
    (g : Isometry leechLattice leechLattice)
    (p : leechLattice.antipodalPairs 4) :
    (leechAntipodalPairsEquivModTwo (g.antipodalPairsEquiv 4 p) :
      QuotSMulTop (2 : ℤ) leechLattice) =
      Isometry.reductionHom leechLattice 2 g (leechAntipodalPairsEquivModTwo p) := by
  simpa only [leechAntipodalPairsEquivModTwo_apply] using
    leechLattice.coe_antipodalPairsToModTwo_antipodalPairsEquiv 4 g p

/-- A Leech isometry carries one minimal pair to another exactly when its reduction carries
their type-2 classes. Taking the same pair on both sides compares the actual stabilizers. -/
theorem antipodalPairsEquiv_four_leechLattice_eq_iff
    (g : Isometry leechLattice leechLattice) (p q : leechLattice.antipodalPairs 4) :
    g.antipodalPairsEquiv 4 p = q ↔
      Isometry.reductionHom leechLattice 2 g (leechAntipodalPairsEquivModTwo p) =
        (leechAntipodalPairsEquivModTwo q : QuotSMulTop (2 : ℤ) leechLattice) := by
  simpa only [leechAntipodalPairsEquivModTwo_apply] using
    leechLattice.antipodalPairsEquiv_eq_iff four_lt_two_mul_norm_leechLattice g p q

/-- **The kernel of the Leech mod-two action.** The isometries of the Leech lattice acting
trivially on `Λ / 2Λ` are exactly identity and negation: such an isometry fixes every minimal
pair, because the type-2 class of a minimal vector determines its sign pair. -/
theorem congruenceSubgroup_two_leechLattice :
    Isometry.congruenceSubgroup leechLattice 2 = Subgroup.zpowers (Isometry.neg leechLattice) :=
  le_antisymm
    ((Isometry.congruenceSubgroup_two_le_ker_antipodalPairsHom
      four_lt_two_mul_norm_leechLattice).trans ker_antipodalPairsHom_leechLattice.le)
    (Isometry.zpowers_neg_le_congruenceSubgroup_two leechLattice)

/-- A Leech isometry acts trivially on `Λ / 2Λ` exactly when it is identity or negation. -/
@[simp]
theorem reductionHom_two_leechLattice_eq_one_iff {e : Isometry leechLattice leechLattice} :
    Isometry.reductionHom leechLattice 2 e = 1 ↔ e = 1 ∨ e = Isometry.neg leechLattice := by
  rw [← MonoidHom.mem_ker, ← Isometry.congruenceSubgroup_eq_ker,
    congruenceSubgroup_two_leechLattice, Isometry.mem_zpowers_neg_iff]

end TauCeti
