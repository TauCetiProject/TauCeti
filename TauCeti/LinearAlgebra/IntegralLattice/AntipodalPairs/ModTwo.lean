/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.RingTheory.QuotSMulTop

/-!
# Minimal-vector pairs modulo twice a lattice

Two vectors of minimum positive norm in an integral lattice have the same residue modulo
`2L` exactly when they differ by sign. Indeed, if `x - y = 2z`, then `z` and `y + z`
belong to the lattice and their norms sum to the minimum. They cannot both be nonzero.
Thus antipodal pairs of minimal vectors identify with the residue classes represented by
minimal vectors. This identification intertwines lattice isometries and reduction modulo two.

The sign-independent map exists on every norm shell; only its injectivity requires the
minimum bound. No unimodularity or enumeration of the lattice is needed.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The residue classes modulo `2L` represented by vectors of norm `n`. -/
def normClassesModTwo (n : ℚ) : Set (QuotSMulTop (2 : ℤ) L) :=
  Submodule.Quotient.mk '' L.vectorsOfNorm n

/-- A residue class lies in the norm shell image exactly when it has a representative there. -/
@[simp]
theorem mem_normClassesModTwo {n : ℚ} {c : QuotSMulTop (2 : ℤ) L} :
    c ∈ L.normClassesModTwo n ↔
      ∃ x ∈ L.vectorsOfNorm n, Submodule.Quotient.mk x = c := Iff.rfl

/-- Minimal vectors are congruent modulo `2L` exactly when they differ by sign. -/
theorem mk_modTwo_eq_iff_of_minimum {n : ℚ} (hn : 0 < n)
    (hmin : ∀ z : L, z ≠ 0 → n ≤ L.norm z) {x y : L}
    (hx : x ∈ L.vectorsOfNorm n) (hy : y ∈ L.vectorsOfNorm n) :
    (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) L) = Submodule.Quotient.mk y ↔
      x = y ∨ x = -y := by
  constructor
  · intro h
    obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists
      (x - y) (2 : ℤ) (⊤ : Submodule ℤ L)).mp ((Submodule.Quotient.eq _).mp h)
    have hx' : x = y + (2 : ℤ) • z := by rw [hz]; abel
    by_cases hz0 : z = 0
    · exact Or.inl (by simpa [hz0] using hx')
    by_cases hyz : y + z = 0
    · right
      have hz' : z = -y := eq_neg_of_add_eq_zero_right hyz
      simp [hx', hz', two_zsmul]
    have h₁ := hmin z hz0
    have h₂ := hmin (y + z) hyz
    have hxnorm := mem_vectorsOfNorm.mp hx
    have hynorm := mem_vectorsOfNorm.mp hy
    -- Work on ambient vectors only to use the rational norm's polarization identities.
    have hxambient : (x : V) = (y : V) + ((z : V) + z) := by
      simpa only [two_zsmul, Submodule.coe_add] using congrArg Subtype.val hx'
    rw [hxambient, L.norm_add, L.norm_add, map_add,
      L.norm_apply (z : V)] at hxnorm
    rw [Submodule.coe_add, L.norm_add] at h₂
    linarith [L.norm_apply (z : V)]
  · rintro (rfl | rfl)
    · rfl
    · simp

/-- Send an antipodal pair to its common residue modulo `2L`. -/
noncomputable def antipodalPairsToModTwo (n : ℚ) (p : L.antipodalPairs n) :
    L.normClassesModTwo n :=
  ⟨Submodule.Quotient.mk (mem_antipodalPairs.mp p.property).choose,
    ⟨(mem_antipodalPairs.mp p.property).choose,
      (mem_antipodalPairs.mp p.property).choose_spec.1, rfl⟩⟩

/-- The residue of a pair is the residue of either of its vector representatives. -/
@[simp]
theorem antipodalPairsToModTwo_mk {n : ℚ} (x : L) (hx : x ∈ L.vectorsOfNorm n) :
    (L.antipodalPairsToModTwo n ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ :
      QuotSMulTop (2 : ℤ) L) = Submodule.Quotient.mk x := by
  unfold antipodalPairsToModTwo
  have hp := (mem_antipodalPairs.mp ((mk_mem_antipodalPairs_iff x).mpr hx)).choose_spec.2
  rcases Sym2.eq_iff.mp hp with ⟨h, -⟩ | ⟨h, -⟩
  · exact congrArg Submodule.Quotient.mk h
  · exact (congrArg (fun z : L ↦
      (Submodule.Quotient.mk z : QuotSMulTop (2 : ℤ) L)) h).trans (by simp)

/-- Every residue class represented on the shell is the image of an antipodal pair. -/
theorem antipodalPairsToModTwo_surjective (n : ℚ) :
    Function.Surjective (L.antipodalPairsToModTwo n) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, rfl⟩ := L.mem_normClassesModTwo.mp hc
  exact ⟨⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩,
    Subtype.ext (L.antipodalPairsToModTwo_mk x hx)⟩

/-- Reduction modulo two separates antipodal pairs on a minimal positive norm shell. -/
theorem antipodalPairsToModTwo_injective {n : ℚ} (hn : 0 < n)
    (hmin : ∀ z : L, z ≠ 0 → n ≤ L.norm z) :
    Function.Injective (L.antipodalPairsToModTwo n) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ h
  obtain ⟨x, hx, rfl⟩ := mem_antipodalPairs.mp hp
  obtain ⟨y, hy, rfl⟩ := mem_antipodalPairs.mp hq
  have hxy := congrArg Subtype.val h
  rw [L.antipodalPairsToModTwo_mk x hx, L.antipodalPairsToModTwo_mk y hy] at hxy
  rcases (L.mk_modTwo_eq_iff_of_minimum hn hmin hx hy).mp hxy with rfl | rfl <;>
    apply Subtype.ext <;> simp [Sym2.eq_swap]

/-- Antipodal pairs of minimal vectors identify with their actual residue classes modulo `2L`. -/
noncomputable def antipodalPairsEquivModTwo {n : ℚ} (hn : 0 < n)
    (hmin : ∀ z : L, z ≠ 0 → n ≤ L.norm z) :
    L.antipodalPairs n ≃ L.normClassesModTwo n :=
  Equiv.ofBijective (L.antipodalPairsToModTwo n)
    ⟨L.antipodalPairsToModTwo_injective hn hmin, L.antipodalPairsToModTwo_surjective n⟩

/-- The equivalence sends a pair to the residue of either representative. -/
@[simp]
theorem antipodalPairsEquivModTwo_apply {n : ℚ} (hn : 0 < n)
    (hmin : ∀ z : L, z ≠ 0 → n ≤ L.norm z) (p : L.antipodalPairs n) :
    L.antipodalPairsEquivModTwo hn hmin p = L.antipodalPairsToModTwo n p := (rfl)

/-- The pair-to-residue map intertwines the pair action with reduction of a lattice isometry. -/
theorem antipodalPairsToModTwo_isometry (n : ℚ) (g : Isometry L L)
    (p : L.antipodalPairs n) :
    (L.antipodalPairsToModTwo n (g.antipodalPairsEquiv n p) : QuotSMulTop (2 : ℤ) L) =
      Isometry.reductionHom L 2 g (L.antipodalPairsToModTwo n p) := by
  rcases p with ⟨p, hp⟩
  obtain ⟨x, hx, rfl⟩ := mem_antipodalPairs.mp hp
  have hgx := (g.carrierEquiv_mem_vectorsOfNorm_iff x n).mpr hx
  have hpair : g.antipodalPairsEquiv n ⟨s(x, -x), hp⟩ =
      ⟨s(g.carrierEquiv x, -g.carrierEquiv x), (mk_mem_antipodalPairs_iff _).mpr hgx⟩ := by
    apply Subtype.ext
    simp
  rw [hpair, L.antipodalPairsToModTwo_mk _ hgx, L.antipodalPairsToModTwo_mk x hx,
    Isometry.reductionHom_apply_mk]

end TauCeti.IntegralLattice
