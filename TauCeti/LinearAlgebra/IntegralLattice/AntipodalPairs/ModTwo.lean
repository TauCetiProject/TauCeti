/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs.Basic
public import TauCeti.RingTheory.QuotSMulTop

/-!
# Minimal vectors modulo twice a lattice

Two minimal vectors in the same class modulo twice a lattice differ only by sign.
Consequently the antipodal pairs of minimal vectors identify with their image in `L / 2L`.
The minimum bound, not unimodularity or an order calculation, supplies injectivity.
The construction commutes with lattice isometries through the native quotient maps.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
-/

public section

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} {n : ℚ}

/-- Congruent minimal vectors modulo twice the lattice agree up to sign. -/
theorem eq_or_eq_neg_of_minimal_of_mod_two_eq (hn : 0 < n)
    (hmin : ∀ z : L, z ≠ 0 → n ≤ L.norm (z : V))
    {x y : L} (hx : x ∈ L.vectorsOfNorm n) (hy : y ∈ L.vectorsOfNorm n)
    (hxy : (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) L) =
      Submodule.Quotient.mk y) : x = y ∨ x = -y := by
  rw [Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists] at hxy
  obtain ⟨z, -, hz⟩ := hxy
  -- Here `z = (x - y)/2` and `y + z = (x + y)/2`. If neither vanishes, their
  -- norms are both at least `n`, although the sum of their norms is `n`.
  have hsplit : x = y + (z + z) := by
    calc
      x = y + (x - y) := by abel
      _ = y + (z + z) := by rw [← hz]; simp [two_smul]
  by_cases hz0 : z = 0
  · exact Or.inl (by simpa [hz0] using hsplit)
  by_cases hw0 : y + z = 0
  · right
    rw [hsplit]
    have hyz : y = -z := eq_neg_of_add_eq_zero_left hw0
    simp [hyz]
  have hzmin := hmin z hz0
  have hwmin := hmin (y + z) hw0
  have hxnorm := mem_vectorsOfNorm.mp hx
  have hynorm := mem_vectorsOfNorm.mp hy
  rw [hsplit] at hxnorm
  simp only [Submodule.coe_add, L.norm_add, map_add] at hxnorm hwmin
  rw [← L.norm_apply] at hxnorm
  linarith

/-- The residue classes modulo twice the lattice represented by vectors of norm `n`. -/
def normClassesModTwo (L : IntegralLattice V) (n : ℚ) : Set (QuotSMulTop (2 : ℤ) L) :=
  Submodule.Quotient.mk '' L.vectorsOfNorm n

/-- Membership records an actual norm-`n` representative in the lattice. -/
theorem mem_normClassesModTwo {c : QuotSMulTop (2 : ℤ) L} :
    c ∈ L.normClassesModTwo n ↔
      ∃ x ∈ L.vectorsOfNorm n, Submodule.Quotient.mk x = c := Iff.rfl

/-- Reduction modulo twice the lattice, independent of the sign of an antipodal pair. -/
noncomputable def antipodalPairModTwo (p : L.antipodalPairs n) : QuotSMulTop (2 : ℤ) L :=
  Submodule.Quotient.mk (mem_antipodalPairs.mp p.property).choose

/-- The reduction of the antipodal pair represented by `x` is the class of `x`. -/
@[simp]
theorem antipodalPairModTwo_mk (x : L) (hx : x ∈ L.vectorsOfNorm n) :
    antipodalPairModTwo ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ =
      Submodule.Quotient.mk x := by
  let p : L.antipodalPairs n := ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩
  have hp := (mem_antipodalPairs.mp p.property).choose_spec.2
  rw [antipodalPairModTwo]
  rcases Sym2.eq_iff.mp hp with ⟨h, -⟩ | ⟨h, -⟩
  · exact congrArg Submodule.Quotient.mk h
  · simpa only [Submodule.Quotient.mk_neg, QuotSMulTop.neg_eq_self_two] using
      congrArg (fun v : L ↦ (Submodule.Quotient.mk v : QuotSMulTop (2 : ℤ) L)) h

/-- Every norm class is attained by reduction of an antipodal pair. -/
theorem range_antipodalPairModTwo (L : IntegralLattice V) (n : ℚ) :
    Set.range (antipodalPairModTwo (L := L) (n := n)) = L.normClassesModTwo n := by
  ext c
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(mem_antipodalPairs.mp p.property).choose,
      (mem_antipodalPairs.mp p.property).choose_spec.1, by rw [antipodalPairModTwo]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩, antipodalPairModTwo_mk x hx⟩

/-- Reduction on antipodal pairs is injective on a minimal positive norm shell. -/
theorem antipodalPairModTwo_injective (hn : 0 < n)
    (hmin : ∀ z : L, z ≠ 0 → n ≤ L.norm (z : V)) :
    Function.Injective (antipodalPairModTwo (L := L) (n := n)) := by
  intro p q hpq
  obtain ⟨x, hx, hxp⟩ := mem_antipodalPairs.mp p.property
  obtain ⟨y, hy, hyq⟩ := mem_antipodalPairs.mp q.property
  have hp : p = ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ := Subtype.ext hxp.symm
  have hq : q = ⟨s(y, -y), (mk_mem_antipodalPairs_iff y).mpr hy⟩ := Subtype.ext hyq.symm
  rw [hp, hq, antipodalPairModTwo_mk x hx, antipodalPairModTwo_mk y hy] at hpq
  rcases eq_or_eq_neg_of_minimal_of_mod_two_eq hn hmin hx hy hpq with rfl | rfl
  · exact Subtype.ext (hxp.symm.trans hyq)
  · apply Subtype.ext
    rw [← hxp, ← hyq]
    simp [Sym2.eq_swap]

/-- Antipodal pairs of minimal vectors are precisely the classes they represent modulo `2L`. -/
noncomputable def antipodalPairsEquivNormClassesModTwo (hn : 0 < n)
    (hmin : ∀ z : L, z ≠ 0 → n ≤ L.norm (z : V)) :
    L.antipodalPairs n ≃ L.normClassesModTwo n :=
  Equiv.ofBijective
    (fun p ↦ ⟨antipodalPairModTwo p, (range_antipodalPairModTwo L n).le ⟨p, rfl⟩⟩)
    ⟨fun _ _ h ↦ antipodalPairModTwo_injective hn hmin (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨p, hp⟩ := (range_antipodalPairModTwo L n).ge hc
      exact ⟨p, Subtype.ext hp⟩⟩

/-- The equivalence has the canonical pair-reduction map as its underlying function. -/
@[simp]
theorem coe_antipodalPairsEquivNormClassesModTwo_apply (hn : 0 < n)
    (hmin : ∀ z : L, z ≠ 0 → n ≤ L.norm (z : V)) (p : L.antipodalPairs n) :
    (antipodalPairsEquivNormClassesModTwo hn hmin p : QuotSMulTop (2 : ℤ) L) =
      antipodalPairModTwo p := (rfl)

/-- Reducing an isometric image of a pair agrees with applying the induced quotient map. -/
theorem antipodalPairModTwo_isometry (e : Isometry L M) (p : L.antipodalPairs n) :
    antipodalPairModTwo (e.antipodalPairsEquiv n p) =
      QuotSMulTop.map (2 : ℤ) (e.carrierEquiv : L →ₗ[ℤ] M) (antipodalPairModTwo p) := by
  obtain ⟨x, hx, hxp⟩ := mem_antipodalPairs.mp p.property
  have hp : p = ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ := Subtype.ext hxp.symm
  rw [hp, antipodalPairModTwo_mk x hx, QuotSMulTop.map_apply_mk]
  have he : e.antipodalPairsEquiv n ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ =
      ⟨s(e.carrierEquiv x, -e.carrierEquiv x),
        (mk_mem_antipodalPairs_iff _).mpr ((e.carrierEquiv_mem_vectorsOfNorm_iff x n).mpr hx)⟩ := by
    apply Subtype.ext
    simp
  rw [he, antipodalPairModTwo_mk _ ((e.carrierEquiv_mem_vectorsOfNorm_iff x n).mpr hx)]
  rfl

end TauCeti.IntegralLattice
