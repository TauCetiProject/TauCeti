/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs.ModTwo
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.AntipodalPairs
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group

/-!
# Leech minimal-vector pairs in the mod-two module

The antipodal pairs of minimal vectors of the canonical Construction-B Leech lattice
identify with the classes represented by norm-four vectors in `Λ / 2Λ` (the type-2 classes).
There are 98280 such classes. The bijection sends `{v, -v}` to the actual residue of `v`,
not to an arbitrarily numbered set of the same size.

The comparison intertwines the full lattice-isometry action on pairs with its reduction
modulo two, and therefore identifies the corresponding point stabilizers. No identification
of this isometry group or a stabilizer with a sporadic presentation is assumed.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

open IntegralLattice

private theorem leech_minimal_bound (z : leechLattice) (hz : z ≠ 0) :
    (4 : ℚ) ≤ leechLattice.norm (z : Fin 24 → ℚ) :=
  four_le_norm_leechLattice z.property (fun h ↦ hz (Subtype.ext h))

/-- The minimal-vector antipodal pairs of the Leech lattice are its norm-four residue
classes modulo twice the lattice. -/
noncomputable def leechAntipodalPairsEquivModTwo :
    leechLattice.antipodalPairs 4 ≃ leechLattice.normClassesModTwo 4 :=
  antipodalPairsEquivNormClassesModTwo (by norm_num) leech_minimal_bound

/-- The bijection reduces an actual minimal vector modulo twice the Leech lattice. -/
@[simp]
theorem leechAntipodalPairsEquivModTwo_mk (x : leechLattice)
    (hx : x ∈ leechLattice.vectorsOfNorm 4) :
    (leechAntipodalPairsEquivModTwo
      ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ : QuotSMulTop (2 : ℤ) leechLattice) =
      Submodule.Quotient.mk x := by
  rw [leechAntipodalPairsEquivModTwo, coe_antipodalPairsEquivNormClassesModTwo_apply,
    antipodalPairModTwo_mk x hx]

/-- There are exactly 98280 classes in `Λ / 2Λ` represented by minimal vectors. -/
theorem natCard_normClassesModTwo_four_leechLattice :
    Nat.card (leechLattice.normClassesModTwo 4) = 98280 := by
  rw [← Nat.card_congr leechAntipodalPairsEquivModTwo]
  exact ncard_antipodalPairs_four_leechLattice

/-- The minimal-class identification intertwines the isometry action on antipodal pairs
with the native reduction homomorphism on `Λ / 2Λ`. -/
theorem leechAntipodalPairsEquivModTwo_isometry
    (g : Isometry leechLattice leechLattice) (p : leechLattice.antipodalPairs 4) :
    (leechAntipodalPairsEquivModTwo (g.antipodalPairsEquiv 4 p) :
        QuotSMulTop (2 : ℤ) leechLattice) =
      Isometry.reductionHom leechLattice 2 g (leechAntipodalPairsEquivModTwo p) := by
  rw [leechAntipodalPairsEquivModTwo, coe_antipodalPairsEquivNormClassesModTwo_apply,
    coe_antipodalPairsEquivNormClassesModTwo_apply, antipodalPairModTwo_isometry]
  exact Submodule.Quotient.induction_on _ (antipodalPairModTwo p) fun x ↦ by
    rw [QuotSMulTop.map_apply_mk, Isometry.reductionHom_apply_mk]
    rfl

/-- An isometry fixes a minimal-vector pair exactly when it fixes the corresponding class
modulo twice the Leech lattice. -/
theorem leech_antipodalPair_fixed_iff_mod_two_fixed
    (g : Isometry leechLattice leechLattice) (p : leechLattice.antipodalPairs 4) :
    g.antipodalPairsEquiv 4 p = p ↔
      Isometry.reductionHom leechLattice 2 g (leechAntipodalPairsEquivModTwo p) =
        (leechAntipodalPairsEquivModTwo p : QuotSMulTop (2 : ℤ) leechLattice) := by
  rw [← leechAntipodalPairsEquivModTwo_isometry]
  exact ⟨fun h ↦ congrArg (fun q ↦ (leechAntipodalPairsEquivModTwo q :
      QuotSMulTop (2 : ℤ) leechLattice)) h,
    fun h ↦ leechAntipodalPairsEquivModTwo.injective (Subtype.ext h)⟩

end TauCeti
