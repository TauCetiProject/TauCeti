/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.CharacterImage
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant

/-!
# The image of the canonical character of a Demushkin group

Let `G` be a Demushkin group with canonical character `χ : G → ℤ_pˣ`
(`TauCeti.demushkinCharacter`) and `q`-invariant `q = q(G)` (`TauCeti.demushkinQ`), the order of the
torsion subgroup of `G^{ab}`, or `0` when `G^{ab}` is torsion-free. The two invariants are tied
together: `χ` is congruent to `1` modulo `q` and to nothing finer,

`χ(G) ≤ 1 + p^k ℤ_p  ↔  p^k ∣ q`   for every `k`

(`TauCeti.range_demushkinCharacter_le_unitsPrincipal_iff`). In particular `χ` is trivial exactly
when `q = 0` (`TauCeti.range_demushkinCharacter_eq_bot_iff`), and when `q ≠ 2` the image of `χ` is
the principal unit group `1 + qℤ_p` (`TauCeti.range_demushkinCharacter_eq_unitsPrincipal`), because
every nontrivial closed subgroup of `1 + pℤ_p` for odd `p`, and of `1 + 4ℤ_2`, is a principal unit
group. For
`q = 2` the equivalence only says that `χ` is not congruent to `1` modulo `4`: the image is then a
closed subgroup of `ℤ_2ˣ` not contained in `1 + 4ℤ_2`, and `q` does not determine which one.

The equivalence is a statement about any one-relator pro-`p` group `⟨X ∣ r⟩` with finite `X`
and `r ∈ Φ(F)` whose
relator has nondegenerate degree-one form, and it is proved there
(`TauCeti.HasPrescriptionProperty.range_le_unitsPrincipal_iff_forall_pow_dvd_exponentSum`): the
character with the prescription property is `≡ 1 mod p^k` on the generators exactly when every
exponent sum of `r` is divisible by `p^k`. One direction compares, for each generator `x_j`, the
exponent sum at `x_j`, a crossed homomorphism for the trivial character, with the crossed
homomorphism for `χ` taking the same values on the generators; the latter vanishes at `r` by the
prescription property, and the two are congruent modulo `p^k` when `χ ≡ 1 mod p^k`. For the other
direction, the first-order expansion of a crossed homomorphism in its character
(`TauCeti.IsCrossedHom.pow_succ_dvd_sub_sub_sum_degreeOneForm`) turns `χ ≡ 1 mod p^k` and
`p^(k+1) ∣ exponent sums` into the vanishing modulo `p` of the degree-one form of `r` against the
vector `(χ(x_i) - 1) / p^k`, so nondegeneracy raises the congruence to `p^(k+1)`. The exponent sums
of `r` in turn compute `q`, through the abelianization `G^{ab} ≅ ℤ_p^{n-1} × ℤ_p ⧸ (q)`.

## Main results

* `TauCeti.HasPrescriptionProperty.range_le_unitsPrincipal_iff_forall_pow_dvd_exponentSum`: for a
  one-relator pro-`p` group on finitely many generators whose relator has nondegenerate degree-one
  form, the character with the prescription property lands in `1 + p^kℤ_p` exactly when `p^k`
  divides every exponent sum of the relator.
* `TauCeti.range_demushkinCharacter_le_unitsPrincipal_iff`: **the canonical character of a
  Demushkin group lands in `1 + p^kℤ_p` exactly when `p^k ∣ q(G)`.**
* `TauCeti.range_demushkinCharacter_eq_bot_iff`: the canonical character is trivial exactly when
  `q(G) = 0`.
* `TauCeti.range_demushkinCharacter_eq_unitsPrincipal`: **for `q(G) = p^s ≠ 2` the image of the
  canonical character is `1 + p^sℤ_p = 1 + q(G)ℤ_p`** (Labute, corollary to Theorem 4).

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Theorem 4 and its corollary.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63).
-/

public section

namespace TauCeti

open freeProP

universe u v

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the degree-one
-- form is stated against the module structure of `ZMod p` on itself, as in its nondegeneracy.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime]


section Demushkin

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (hG : IsDemushkin p G)
include hG

/-- **The canonical character of a Demushkin group is congruent to `1` modulo `q(G)`, and modulo no
higher power of `p`**: it takes values in `1 + p^kℤ_p` exactly when `p^k` divides the `q`-invariant.
For `q(G) = 0` this holds for every `k`. -/
@[simp] theorem range_demushkinCharacter_le_unitsPrincipal_iff (k : ℕ) :
    (↑(demushkinCharacter hG) : G →* ℤ_[p]ˣ).range ≤ unitsPrincipal p k ↔
      p ^ k ∣ demushkinQ hG := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP
    (ULift.{v} (Fin (demushkinRank hG))) (by simp)
  have hP := IsDemushkin.of_equiv p hG e.symm
  -- Pull the canonical character back to the presented group; its image does not change.
  have hrange : ((demushkinCharacter hG).comp
      (e : presentedProP p (ULift.{v} (Fin (demushkinRank hG))) {r} →ₜ* G)).toMonoidHom.range =
      (demushkinCharacter hG).toMonoidHom.range :=
    (MonoidHom.range_comp _ _).trans (by
      rw [MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top])
  have hχ := (hasPrescriptionProperty_demushkinCharacter hG).comp_equiv (e := e)
  -- The character's coercion to a monoid homomorphism is definitionally `toMonoidHom`, whose
  -- range is the form used by `hrange` and the presentation theorem below.
  change (demushkinCharacter hG).toMonoidHom.range ≤ unitsPrincipal p k ↔
    p ^ k ∣ demushkinQ hG
  rw [← hrange, hχ.range_le_unitsPrincipal_iff_forall_pow_dvd_exponentSum hr
    (hG.nondegenerate_degreeOneForm hr e), demushkinQ_congr hG hP e.symm]
  -- Read `q` off the exponent vector `q • w` of the relator, with `w x₀ = 1`.
  have : Nonempty (ULift.{v} (Fin (demushkinRank hG))) := ⟨⟨⟨0, hG.demushkinRank_pos⟩⟩⟩
  obtain ⟨x₀, hx₀⟩ := PreValuationRing.exists_forall_dvd (exponentSum p _ r).toAdd
  obtain ⟨w, hw, hv⟩ := exists_eq_smul_of_forall_dvd hx₀
  have hpq := dvd_exponentSum_of_mem_proPFrattini p _ hr x₀
  have hall : (∀ x, (p : ℤ_[p]) ^ k ∣ (exponentSum p _ r).toAdd x) ↔
      (p : ℤ_[p]) ^ k ∣ (exponentSum p _ r).toAdd x₀ :=
    ⟨fun h ↦ h x₀, fun h x ↦ h.trans (hx₀ x)⟩
  rw [hall]
  by_cases hq : (exponentSum p _ r).toAdd x₀ = 0
  · rw [(demushkinQ_presentedProP_eq_zero_iff hw hv hP hpq).2 hq, hq]
    simp
  · rw [demushkinQ_presentedProP_eq_pow_valuation hw hv hP hpq hq,
      Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt, ← Ideal.mem_span_singleton,
      PadicInt.mem_span_pow_iff_le_valuation _ hq]

/-- **The canonical character of a Demushkin group is trivial exactly when `q(G) = 0`**, that is
when the abelianization of `G` is torsion-free. -/
@[simp] theorem range_demushkinCharacter_eq_bot_iff :
    (↑(demushkinCharacter hG) : G →* ℤ_[p]ˣ).range = ⊥ ↔ demushkinQ hG = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_bot_iff.2 ?_⟩
  · have hdvd := (range_demushkinCharacter_le_unitsPrincipal_iff hG (demushkinQ hG)).1
      (h ▸ bot_le)
    exact Nat.eq_zero_of_dvd_of_lt hdvd (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)
  · rw [← iInf_unitsPrincipal_eq_bot p]
    exact le_iInf fun k ↦ (range_demushkinCharacter_le_unitsPrincipal_iff hG k).2 (h ▸ dvd_zero _)

/-- **The image of the canonical character is `1 + qℤ_p` when `q ≠ 2`** (Labute, corollary to
Theorem 4). If the `q`-invariant of a Demushkin group is `q(G) = p^s ≠ 2`, then the canonical
character maps `G` onto the principal unit group `1 + p^sℤ_p`. The case `q(G) = 0` is
`TauCeti.range_demushkinCharacter_eq_bot_iff`. -/
theorem range_demushkinCharacter_eq_unitsPrincipal {s : ℕ} (hs : demushkinQ hG = p ^ s)
    (h2 : demushkinQ hG ≠ 2) :
    (demushkinCharacter hG).toMonoidHom.range = unitsPrincipal p s := by
  have hp : p.Prime := Fact.out
  have hs0 : 0 < s := Nat.pos_of_ne_zero fun h ↦ hp.not_dvd_one (by
    simpa [h, hs] using hG.prime_dvd_demushkinQ)
  have hs2 : p = 2 → 2 ≤ s := fun hp2 ↦ by
    by_contra! hlt
    have hs1 : s = 1 := by omega
    exact h2 (by rw [hs, hp2, hs1, pow_one])
  have hne : (demushkinCharacter hG).toMonoidHom.range ≠ ⊥ := fun h ↦
    pow_ne_zero s hp.ne_zero (hs ▸ (range_demushkinCharacter_eq_bot_iff hG).1 h)
  obtain ⟨f, hsf, hf⟩ := exists_eq_unitsPrincipal_of_isClosed hs0 hs2
    (isClosed_range_demushkinCharacter hG)
    ((range_demushkinCharacter_le_unitsPrincipal_iff hG s).2 (hs ▸ dvd_rfl)) hne
  -- The level `f` cannot exceed `s`, since `p^(s+1)` does not divide `q(G) = p^s`.
  obtain rfl | hlt := hsf.eq_or_lt
  · exact hf
  · have hle := (range_demushkinCharacter_le_unitsPrincipal_iff hG (s + 1)).1
      (hf.le.trans (unitsPrincipal_antitone p hlt))
    rw [hs, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hle
    omega

end Demushkin

end TauCeti
