/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.CharacterLift
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ZModFourLift
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.RankParity

/-!
# The cup squares of a Demushkin group at `p = 2` vanish exactly when `q ≠ 2`

Let `G` be a Demushkin group at `p = 2`. The cup square of a class of `H¹(G, 𝔽₂)` vanishes exactly
when the corresponding character `G → 𝔽₂` lifts to a continuous character `G → ℤ/4`
(`TauCeti.cupFp_self_eq_zero_iff_exists_zmodFourReductionClass_eq`, the Bockstein description of
the cup square). Characters with values in `𝔽₂` or `ℤ/4` factor through the topological
abelianization `G^{ab} ≅ ℤ_2^{n-1} × ℤ_2 ⧸ (q)`, where `q = q(G)` is Labute's invariant, so the
question becomes one about this abelian pro-`2` group. If `q ≠ 2`, then `4 ∣ q`, including
`q = 0`, and every character lifts, so every cup square vanishes: the cup form is alternating. If
`q = 2`, the projection onto the torsion factor `ℤ_2 ⧸ (2) = 𝔽₂` does not lift, because an element
of order two cannot map to an odd element of `ℤ/4`, so some cup square is nonzero: the cup form is
symmetric but not alternating.

This is the invariant-theoretic content of the trichotomy in Labute's classification: the cup
form of a Demushkin group is alternating exactly when `q ≠ 2`, at every prime, since for odd `p`
every cup square vanishes by graded commutativity. It decides which of Labute's normal forms the
relator of `G` can be brought to: the alternating form `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` when
`q ≠ 2`, and the dyadic forms with a square `x₁²` when `q = 2`. In particular a Demushkin group
with `q ≠ 2` has even rank, at every prime, and one of odd rank has `q = 2`.

## Main results

* `TauCeti.IsDemushkin.forall_exists_zmodFourReduction_eq_iff_demushkinQ_ne_two`: every continuous
  character `G → 𝔽₂` of a Demushkin group at `p = 2` lifts to `ℤ/4` exactly when `q(G) ≠ 2`.
* `TauCeti.IsDemushkin.forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two`: **every cup square on
  `H¹(G, 𝔽₂)` vanishes exactly when `q(G) ≠ 2`.**
* `TauCeti.IsDemushkin.exists_cupFp_self_ne_zero_iff_demushkinQ_eq_two`: some cup square is
  nonzero exactly when `q(G) = 2`.
* `TauCeti.IsDemushkin.even_demushkinRank_of_demushkinQ_ne_two`,
  `TauCeti.IsDemushkin.demushkinQ_eq_two_of_odd_demushkinRank`: at every prime, `q(G) ≠ 2` forces
  the rank to be even, and an odd rank forces `q(G) = 2`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §1
  and §3.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter III, §9.
-/

public section

namespace TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-! ### Demushkin groups at `p = 2` -/

section Two

variable (hG : IsDemushkin 2 G)
include hG

namespace IsDemushkin

/-- **Every continuous character `G → 𝔽₂` of a Demushkin group at `p = 2` lifts to `ℤ/4` exactly
when `q(G) ≠ 2`.** Through `G^{ab} ≅ ℤ_2^{n-1} × ℤ_2 ⧸ (q)`: if `q ≠ 2` then `4 ∣ q` and every
character lifts coordinatewise, while if `q = 2` the projection onto the torsion factor
`ℤ_2 ⧸ (2) = 𝔽₂` does not lift. -/
theorem forall_exists_zmodFourReduction_eq_iff_demushkinQ_ne_two :
    (∀ χ : continuousZModDual 2 G, ∃ φ : G →ₜ* Multiplicative (ZMod 4),
      φ.zmodFourReduction = χ) ↔ demushkinQ hG ≠ 2 := by
  obtain ⟨e⟩ := hG.nonempty_continuousMulEquiv_topologicalAbelianization
  rw [forall_exists_zmodFourReduction_eq_iff_of_topologicalAbelianization e]
  refine ⟨fun h hq ↦ ?_, fun hq χ ↦ ?_⟩
  · rw [hq, Nat.cast_ofNat] at h
    obtain ⟨φ, hφ⟩ := h (PadicInt.piProdQuotientSpanToZMod (q := (2 : ℤ_[2])) (dvd_refl _))
    obtain ⟨a, ha⟩ := PadicInt.exists_castHom_toAdd_ne_toAdd_piProdQuotientSpanToZMod φ
    exact ha (hφ a)
  · refine PadicInt.exists_forall_castHom_toAdd_eq_toAdd_of_pow_two_dvd ?_ χ
    rcases eq_or_ne (demushkinQ hG) 0 with h0 | h0
    · rw [h0, Nat.cast_zero]
      exact dvd_zero _
    · obtain ⟨k, hk2, hqk⟩ := hG.exists_two_le_demushkinQ_eq_pow_of_ne h0 hq
      rw [hqk, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_dvd_pow _ hk2

/-- **The cup form of a Demushkin group at `p = 2` is alternating exactly when `q(G) ≠ 2`**: every
cup square on `H¹(G, 𝔽₂)` vanishes if and only if `q(G) ≠ 2`. -/
theorem forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two :
    (∀ a : cohomFp 2 G 1, cupFp 2 G a a = 0) ↔ demushkinQ hG ≠ 2 :=
  forall_cupFp_self_eq_zero_iff_forall_exists_zmodFourReduction_eq.trans
    hG.forall_exists_zmodFourReduction_eq_iff_demushkinQ_ne_two

/-- **The cup form of a Demushkin group at `p = 2` is not alternating exactly when `q(G) = 2`**:
some cup square on `H¹(G, 𝔽₂)` is nonzero if and only if `q(G) = 2`. -/
theorem exists_cupFp_self_ne_zero_iff_demushkinQ_eq_two :
    (∃ a : cohomFp 2 G 1, cupFp 2 G a a ≠ 0) ↔ demushkinQ hG = 2 := by
  simpa [not_forall] using hG.forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two.not

end IsDemushkin

end Two

/-! ### Every prime -/

namespace IsDemushkin

variable {p : ℕ} [Fact p.Prime] (hG : IsDemushkin p G)
include hG

/-- **A Demushkin group with `q(G) ≠ 2` has even rank**, at every prime `p`: its cup form is then a
nondegenerate alternating form on `H¹(G, 𝔽_p)`. At an odd prime every Demushkin group has even
rank (`TauCeti.IsDemushkin.even_demushkinRank_of_ne_two`); at `p = 2` the cup squares vanish
exactly when `q(G) ≠ 2`. -/
theorem even_demushkinRank_of_demushkinQ_ne_two (hq : demushkinQ hG ≠ 2) :
    Even (demushkinRank hG) := by
  rcases eq_or_ne p 2 with rfl | hp
  · exact hG.even_demushkinRank_of_forall_cupFp_self_eq_zero
      (hG.forall_cupFp_self_eq_zero_iff_demushkinQ_ne_two.2 hq)
  · exact hG.even_demushkinRank_of_ne_two hp

/-- A Demushkin group of odd rank has `q(G) = 2`, at every prime `p`; at an odd prime there is no
Demushkin group of odd rank. -/
theorem demushkinQ_eq_two_of_odd_demushkinRank (hn : Odd (demushkinRank hG)) :
    demushkinQ hG = 2 :=
  by_contra fun hq ↦ (Nat.not_even_iff_odd.2 hn) (hG.even_demushkinRank_of_demushkinQ_ne_two hq)

end IsDemushkin

end TauCeti
