/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension
public import TauCeti.GroupTheory.FreeGroup.MaximalExponent

/-!
# Root reduction for centralizer extensions

Every nonidentity element of a residually free group has a positive root which is not a
proper power. In a fully residually free group, this root has the same full centralizer as
the original element. Thus extending the centralizer of any nonidentity parameter in positive
rank is isomorphic, over the base group and preserving the new letters, to an admissible step.
No finite-generation or nonabelianity assumption is needed for this reduction.

Root exponents are bounded by the reduced-word length of one nonidentity free image. This
uses `FreeGroup.le_norm_of_pow_eq` and generalizes the maximal-exponent argument of
`FreeGroup.exists_root_maximal_exponent`; it does not require a limit-group embedding theorem
or finite generation of centralizers. Equality of centralizers uses commutation transitivity,
not the false assertion that centralizers of fully residually free groups are cyclic.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5 (extensions at non-proper-power parameters).
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually
  free groups: algorithmic problems*, Contemp. Math. 360 (2004), §5 (roots and centralizers).
-/

public section

namespace TauCeti.LimitGroup

open Group Subgroup

variable {G : Type*} [Group G]

/-- Positive root exponents of a nonidentity element in a residually free group are bounded.
A single free image not killing the element supplies a bound for every root. -/
theorem IsResiduallyFree.bddAbove_root_exponents (hG : IsResiduallyFree G) {u : G}
    (hu : u ≠ 1) : BddAbove {n : ℕ | ∃ r : G, r ^ n = u} := by
  classical
  obtain ⟨ι, φ, hφ⟩ := isResiduallyFree_def.mp hG u hu
  refine ⟨FreeGroup.norm (φ u), ?_⟩
  rintro n ⟨r, hr⟩
  exact FreeGroup.le_norm_of_pow_eq hφ (by simpa only [map_pow] using congrArg φ hr)

/-- Every nonidentity element of a residually free group is a positive power of an element
which is not a proper power. Full residual freeness is not needed for this existence result. -/
theorem IsResiduallyFree.exists_root_not_isProperPower (hG : IsResiduallyFree G) {u : G}
    (hu : u ≠ 1) : ∃ r : G, ∃ d : ℕ, 0 < d ∧ r ^ d = u ∧ ¬IsProperPower r := by
  let s : Set ℕ := {n | ∃ r : G, r ^ n = u}
  have hs : s.Nonempty := ⟨1, u, pow_one u⟩
  have hb : BddAbove s := hG.bddAbove_root_exponents hu
  obtain ⟨r, hr⟩ := Nat.sSup_mem hs hb
  have hd : 0 < sSup s := by
    by_contra h
    have hz : sSup s = 0 := by omega
    exact hu (by simpa only [hz, pow_zero] using hr.symm)
  refine ⟨r, sSup s, hd, hr, ?_⟩
  intro hp
  obtain ⟨y, m, hm, hym⟩ := isProperPower_iff.mp hp
  have hroot : y ^ (m * sSup s) = u := by rw [pow_mul, ← hym, hr]
  have hle : m * sSup s ≤ sSup s := le_csSup hb ⟨y, hroot⟩
  have hlt : sSup s < m * sSup s := by
    simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right (by omega : 1 < m) hd
  omega

/-- Root reduction preserves the full centralizer in a fully residually free group: every
nonidentity parameter is a positive power of a non-proper-power with the same centralizer. -/
theorem centralizerExt_root_reduction (hG : IsFullyResiduallyFree G) {u : G} (hu : u ≠ 1) :
    ∃ r : G, ∃ d : ℕ, 0 < d ∧ r ^ d = u ∧ ¬IsProperPower r ∧
      centralizer {u} = centralizer {r} := by
  obtain ⟨r, d, hd, hr, hp⟩ := hG.isResiduallyFree.exists_root_not_isProperPower hu
  refine ⟨r, d, hd, hr, hp, ?_⟩
  subst u
  exact hG.isCommTransitive.centralizer_singleton_pow hu

/-- Every positive-rank centralizer extension at a nonidentity parameter in a fully residually
free group is isomorphic to an admissible extension. The isomorphism fixes the base group and
preserves each new letter. -/
theorem CentralizerExt.exists_equiv_admissible (hG : IsFullyResiduallyFree G) {u : G}
    (hu : u ≠ 1) {n : ℕ} (hn : 0 < n) :
    ∃ r : G, IsAdmissibleCentralizerStep r n ∧
      ∃ e : CentralizerExt u n ≃* CentralizerExt r n,
        (∀ g : G, e (of g) = of g) ∧ (∀ i : Fin n, e (t i) = t i) := by
  obtain ⟨r, _, _, _, hp, hc⟩ := centralizerExt_root_reduction hG hu
  exact ⟨r, isAdmissibleCentralizerStep_iff.mpr ⟨hp, hn⟩, equivOfCentralizerEq hc,
    equivOfCentralizerEq_of hc, equivOfCentralizerEq_t hc⟩

end TauCeti.LimitGroup
