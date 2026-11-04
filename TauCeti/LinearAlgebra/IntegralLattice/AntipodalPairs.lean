/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Norm
public import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.Card

/-!
# Antipodal pairs in a lattice norm shell

The antipodal pairs of norm `n` are the unordered pairs `s(x, -x)` of lattice vectors of
norm `n`. They are represented in Mathlib's `Sym2`, so the choice of sign is forgotten.
For nonzero `n`, negation has no fixed point in the shell and each pair has exactly two
representatives. Consequently a finite shell has twice as many vectors as antipodal pairs.

An integral-lattice isometry transports these pairs by applying its carrier equivalence to
both entries. Such pairs provide the domain for a projective lattice-isometry action.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
-/

public section

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {W : Type v} [AddCommGroup W] [Module ℚ W]

/-- Unordered antipodal pairs of lattice vectors of norm `n`. -/
def antipodalPairs (L : IntegralLattice V) (n : ℚ) : Set (Sym2 L) :=
  (fun x : L ↦ s(x, -x)) '' L.vectorsOfNorm n

/-- A pair belongs to the antipodal shell exactly when it has a representative of norm `n`. -/
theorem mem_antipodalPairs {L : IntegralLattice V} {n : ℚ} {p : Sym2 L} :
    p ∈ L.antipodalPairs n ↔ ∃ x ∈ L.vectorsOfNorm n, s(x, -x) = p :=
  Iff.rfl

-- Keep the existential membership rule explicit so that `simp` uses the vector and isometry
-- normal forms below without expanding arbitrary pairs into representatives.

/-- The pair of a vector and its negative belongs to precisely the same norm shell as the
vector. No nonzero-norm hypothesis is needed here. -/
@[simp]
theorem mk_mem_antipodalPairs_iff {L : IntegralLattice V} {n : ℚ} (x : L) :
    s(x, -x) ∈ L.antipodalPairs n ↔ x ∈ L.vectorsOfNorm n := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact hy
    · exact (neg_mem_vectorsOfNorm_iff y).mpr hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Either entry of an antipodal pair has the prescribed norm. -/
theorem mem_vectorsOfNorm_of_mem_antipodalPairs {L : IntegralLattice V} {n : ℚ}
    {p : Sym2 L} (hp : p ∈ L.antipodalPairs n) {x : L} (hx : x ∈ p) :
    x ∈ L.vectorsOfNorm n := by
  obtain ⟨y, hy, rfl⟩ := hp
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact hy
  · exact (neg_mem_vectorsOfNorm_iff y).mpr hy

/-- Negation has no fixed point on a shell of nonzero norm. -/
theorem neg_ne_self_of_mem_vectorsOfNorm {L : IntegralLattice V} {n : ℚ} (hn : n ≠ 0)
    {x : L} (hx : x ∈ L.vectorsOfNorm n) : -x ≠ x := by
  intro h
  have hz : (2 : ℚ) • (x : V) = 0 := by
    calc
      (2 : ℚ) • (x : V) = (x : V) + x := two_smul ℚ (x : V)
      _ = -(x : V) + x := congrArg (· + (x : V)) (congrArg Subtype.val h).symm
      _ = 0 := neg_add_cancel _
  have hx0 : x = 0 := Subtype.ext ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  exact hn (by simpa [hx0] using (mem_vectorsOfNorm.mp hx).symm)

/-- Every antipodal pair on a shell of nonzero norm has distinct entries. -/
theorem not_isDiag_of_mem_antipodalPairs {L : IntegralLattice V} {n : ℚ} (hn : n ≠ 0)
    {p : Sym2 L} (hp : p ∈ L.antipodalPairs n) : ¬ p.IsDiag := by
  obtain ⟨x, hx, rfl⟩ := hp
  rw [Sym2.mk_isDiag_iff]
  exact (neg_ne_self_of_mem_vectorsOfNorm hn hx).symm

/-- A finite norm shell has finitely many antipodal pairs. -/
theorem finite_antipodalPairs {L : IntegralLattice V} {n : ℚ}
    (h : (L.vectorsOfNorm n).Finite) : (L.antipodalPairs n).Finite :=
  h.image _

/-- A finite shell of nonzero norm has exactly twice as many vectors as antipodal pairs. -/
theorem ncard_vectorsOfNorm_eq_two_mul_ncard_antipodalPairs {L : IntegralLattice V} {n : ℚ}
    (hn : n ≠ 0) (hfin : (L.vectorsOfNorm n).Finite) :
    (L.vectorsOfNorm n).ncard = 2 * (L.antipodalPairs n).ncard := by
  classical
  let f : L.vectorsOfNorm n → L.antipodalPairs n :=
    fun x ↦ ⟨s(x.1, -x.1), (mk_mem_antipodalPairs_iff x.1).mpr x.2⟩
  let := hfin.fintype
  let := (finite_antipodalPairs hfin).fintype
  have hfiber (p : L.antipodalPairs n) : Nat.card {x // f x = p} = 2 := by
    obtain ⟨x, hx, hp⟩ := p.2
    let a : {x // f x = p} := ⟨⟨x, hx⟩, Subtype.ext hp⟩
    let b : {x // f x = p} :=
      ⟨⟨-x, (neg_mem_vectorsOfNorm_iff x).mpr hx⟩,
        Subtype.ext (by simpa only [f, neg_neg, Sym2.eq_swap] using hp)⟩
    apply Nat.card_eq_two_iff.mpr
    refine ⟨a, b, ?_, ?_⟩
    · intro hab
      exact neg_ne_self_of_mem_vectorsOfNorm hn hx
        (congrArg (fun z : {x // f x = p} ↦ z.1.1) hab).symm
    · apply Set.eq_univ_iff_forall.mpr
      intro z
      have hz : s(z.1.1, -z.1.1) = s(x, -x) :=
        (congrArg Subtype.val z.2).trans hp.symm
      rcases Sym2.eq_iff.mp hz with ⟨h, -⟩ | ⟨h, -⟩
      · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext (Subtype.ext h)))
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
          (Subtype.ext (Subtype.ext h))))
  calc
    (L.vectorsOfNorm n).ncard = Nat.card (Σ p, {x // f x = p}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = 2 * (L.antipodalPairs n).ncard := by
      rw [Nat.card_sigma]
      simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, mul_comm]

/-- The number of antipodal pairs is half the number of vectors on a finite nonzero shell. -/
theorem ncard_antipodalPairs {L : IntegralLattice V} {n : ℚ} (hn : n ≠ 0)
    (hfin : (L.vectorsOfNorm n).Finite) :
    (L.antipodalPairs n).ncard = (L.vectorsOfNorm n).ncard / 2 := by
  rw [ncard_vectorsOfNorm_eq_two_mul_ncard_antipodalPairs hn hfin]
  omega

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W}

/-- Applying a lattice isometry to both entries transports antipodal pairs. -/
@[simp]
theorem map_mem_antipodalPairs_iff (e : Isometry L M) (n : ℚ) (p : Sym2 L) :
    Sym2.map e.carrierEquiv p ∈ M.antipodalPairs n ↔ p ∈ L.antipodalPairs n := by
  constructor
  · rintro ⟨y, hy, hp⟩
    refine ⟨e.carrierEquiv.symm y, ?_, ?_⟩
    · exact (e.carrierEquiv_mem_vectorsOfNorm_iff _ n).mp (by simpa using hy)
    · apply Sym2.map.injective e.carrierEquiv.injective
      simpa using hp
  · rintro ⟨x, hx, rfl⟩
    simpa using (mk_mem_antipodalPairs_iff (e.carrierEquiv x)).mpr
      ((e.carrierEquiv_mem_vectorsOfNorm_iff x n).mpr hx)

/-- A lattice isometry induces an equivalence of antipodal norm shells. -/
def antipodalPairsEquiv (e : Isometry L M) (n : ℚ) :
    L.antipodalPairs n ≃ M.antipodalPairs n where
  toFun p := ⟨Sym2.map e.carrierEquiv p, (e.map_mem_antipodalPairs_iff n p).mpr p.2⟩
  invFun p := ⟨Sym2.map e.carrierEquiv.symm p,
    (e.map_mem_antipodalPairs_iff n _).mp (by
      simp [Sym2.map_map])⟩
  left_inv p := Subtype.ext (by simp [Sym2.map_map])
  right_inv p := Subtype.ext (by simp [Sym2.map_map])

/-- Transport applies the carrier equivalence to both entries. -/
@[simp]
theorem coe_antipodalPairsEquiv_apply (e : Isometry L M) (n : ℚ)
    (p : L.antipodalPairs n) :
    (e.antipodalPairsEquiv n p : Sym2 M) = Sym2.map e.carrierEquiv p :=
  (rfl)

/-- Inverse transport applies the inverse carrier equivalence to both entries. -/
@[simp]
theorem coe_antipodalPairsEquiv_symm_apply (e : Isometry L M) (n : ℚ)
    (p : M.antipodalPairs n) :
    ((e.antipodalPairsEquiv n).symm p : Sym2 L) = Sym2.map e.carrierEquiv.symm p :=
  (rfl)

end Isometry

end TauCeti.IntegralLattice
