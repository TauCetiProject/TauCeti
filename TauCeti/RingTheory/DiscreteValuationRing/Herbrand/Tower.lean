/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Quotient
import TauCeti.RingTheory.Invariant.Galois

/-!
# Tower transitivity and upper-numbering Herbrand's theorem for DVRs

Building on Herbrand's lower-numbering theorem in
`TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Quotient`, this file proves — for any finite
group `G` acting on a discrete valuation ring `B` over a local ring `A` with normal subgroup
`H ⊴ G` and separable residue extension `𝓀(B) / 𝓀(A)`, without completeness, residue finiteness,
faithfulness, or `A = B^G`:

* **Tower transitivity**: `φ_G = φ_{G ⧸ H} ∘ φ_H`, `ψ_G = ψ_H ∘ ψ_{G ⧸ H}`, and
  `ψℕ_G = ψℕ_H ∘ ψℕ_{G ⧸ H}`.
* **Herbrand's theorem in the upper numbering**: `(G ⧸ H)^v = G^v H / H` for all `v : ℝ`.
* **Upper numbering of a normal subgroup**: `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for all `v : ℝ`.
* **Upper breaks in a tower**: `v` is an upper break of `G` iff it is an upper break of `G ⧸ H`
  or `ψ_{G ⧸ H}(v)` is an upper break of `H`.

The analytic and group-theoretic propagation from `(G_u).map π = G'_{φ_H(u)}` is first isolated for
arbitrary finite groups acting on local rings so that both the DVR API (`FixedPoints.subalgebra`,
`FixedPoints.subring`, and `integralClosure` / `IntermediateField.fixedField`) and the
nonarchimedean local-field API (`TauCeti.NumberTheory.LocalField.Herbrand.{Tower,UpperQuotient}`)
share the same proofs.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_eq_comp_of_map_ramificationGroupReal_eq`,
  `TauCeti.IsLocalRing.map_upperRamificationGroup_of_map_ramificationGroupReal_eq`,
  `TauCeti.IsLocalRing.comap_upperRamificationGroup_of_map_ramificationGroupReal_eq`,
  `TauCeti.IsLocalRing.upperJump_iff_or_of_map_ramificationGroupReal_eq`: abstract local-ring
  deductions from Herbrand's lower-numbering theorem.
* `TauCeti.IsLocalRing.herbrandFun_tower`, `TauCeti.IsLocalRing.inverseHerbrandFun_tower`,
  `TauCeti.IsLocalRing.psiNat_tower`: tower transitivity on `FixedPoints.subalgebra A B H`.
* `TauCeti.IsLocalRing.upperRamificationGroup_quotient_eq_map`,
  `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_quotient`,
  `TauCeti.IsLocalRing.upperJump_iff_upperJump_quotient_or`: upper numbering and upper breaks on
  `FixedPoints.subalgebra A B H` (plus `FixedPoints.subring` and Galois field corollaries).

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Propositions 14 and 15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Propositions 3 and 4.
-/

public section
noncomputable section

namespace TauCeti.IsLocalRing

/-! ### Abstract local-ring propagation from Herbrand's lower-numbering theorem -/

section AbstractTower

private theorem ramificationGroupReal_eq_top_of_le_neg_one (G : Type*) [Group G] (S : Type*)
    [CommRing S] [_root_.IsLocalRing S] [MulSemiringAction G S] {w : ℝ} (hw : w ≤ -1) :
    ramificationGroupReal G S w = ⊤ := by
  rw [ramificationGroupReal_def]
  exact ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by simpa using hw))

variable {C B : Type*} [CommRing C] [_root_.IsLocalRing C] [CommRing B] [_root_.IsLocalRing B]
  {G G' H : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [Group G'] [Finite G'] [MulSemiringAction G' C]
  [Group H] [Finite H] [MulSemiringAction H B]

omit [Finite G] [Finite G'] in
/-- If `(G_u).map π = G'_{φ_H(u)}` holds for all `u ≥ -1`, then it holds for all `u : ℝ`, since
both lower filtrations are constantly `⊤` on `(-∞, -1]`. -/
theorem map_ramificationGroupReal_of_forall_neg_one_le (π : G →* G')
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    (u : ℝ) :
    (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u) := by
  rcases le_or_gt (-1) u with hu | hu
  · exact hmap u hu
  have hφ : herbrandFun H B u ≤ -1 := by
    rw [← herbrandFun_neg_one H B]
    exact (herbrandFun_strictMono H B).monotone hu.le
  rw [ramificationGroupReal_eq_top_of_le_neg_one G B hu.le,
    ramificationGroupReal_eq_top_of_le_neg_one G' C hφ,
    ← ramificationGroupReal_eq_top_of_le_neg_one G B (w := -1) le_rfl, hmap (-1) le_rfl,
    herbrandFun_neg_one, ramificationGroupReal_eq_top_of_le_neg_one G' C le_rfl]

omit [Finite G] [Finite G'] [Finite H] in
/-- **Abstract counting form of Herbrand's theorem**: `#G'_{φ_H(u)} · #H_u = #G_u`. -/
theorem natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq
    (π : G →* G') (ι : H →* G) (hι : Function.Injective ι)
    (hι_smul : ∀ (τ : H) (b : B), ι τ • b = τ • b) (hexact : ι.range = π.ker) {u : ℝ}
    (hu : (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u)) :
    Nat.card (ramificationGroupReal G' C (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) := by
  have hcomap : (ramificationGroupReal G B u).comap ι = ramificationGroupReal H B u :=
    (ramificationGroupReal_eq_comap_of_ringEquiv ι (RingEquiv.refl B)
      (fun τ b ↦ (hι_smul τ b).symm) u).symm
  rw [← hu, ← MonoidHom.domRestrict_range, ← Subgroup.card_map_of_injective hι, ← hcomap,
    Subgroup.map_comap_eq, hexact, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype,
    ← MonoidHom.ker_domRestrict, mul_comm, Subgroup.card_ker_mul_card_range]

omit [Finite G] [Finite G'] in
/-- If `G_s` is constant on `(a, b]`, then `G'_t` is constant on `(φ_H(a), φ_H(b)]`. -/
theorem ramificationGroupReal_eq_of_forall_eq_of_map_eq (π : G →* G')
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    {a b t : ℝ} (ht₁ : herbrandFun H B a < t) (ht₂ : t ≤ herbrandFun H B b)
    (hG : ∀ s : ℝ, a < s → s ≤ b → ramificationGroupReal G B s = ramificationGroupReal G B b) :
    ramificationGroupReal G' C t = ramificationGroupReal G' C (herbrandFun H B b) := by
  have hmap' := map_ramificationGroupReal_of_forall_neg_one_le π hmap
  have hs₁ : a < inverseHerbrandFun H B t := by
    simpa only [inverseHerbrandFun_herbrandFun] using inverseHerbrandFun_strictMono H B ht₁
  have hs₂ : inverseHerbrandFun H B t ≤ b := by
    simpa only [inverseHerbrandFun_herbrandFun] using
      (inverseHerbrandFun_strictMono H B).monotone ht₂
  rw [← herbrandFun_inverseHerbrandFun H B t, ← hmap', ← hmap', hG _ hs₁ hs₂]

/-- Propagating `φ_G = φ_{G'} ∘ φ_H` from the left endpoint `m` of `[m, m + 1]` across the
interval. -/
private theorem herbrandFun_eq_comp_of_mem_Icc_of_eq
    (π : G →* G') (ι : H →* G) (hι : Function.Injective ι)
    (hι_smul : ∀ (τ : H) (b : B), ι τ • b = τ • b) (hexact : ι.range = π.ker)
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1)
    (hm : herbrandFun G B m = herbrandFun G' C (herbrandFun H B m)) :
    herbrandFun G B u = herbrandFun G' C (herbrandFun H B u) := by
  have hmap' := map_ramificationGroupReal_of_forall_neg_one_le π hmap
  have hG : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      ramificationGroupReal G B t = ramificationGroupReal G B u := fun _ _ _ ↦ by
    rw [ramificationGroupReal_eq_of_sub_one_lt_of_le G B (i := (m + 1 : ℕ))
        (by push_cast; linarith) (by push_cast; linarith),
      ramificationGroupReal_eq_of_sub_one_lt_of_le G B (i := (m + 1 : ℕ))
        (by push_cast; linarith) (by push_cast; linarith)]
  have hH : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      ramificationGroupReal H B t = ramificationGroupReal H B u := fun _ _ _ ↦ by
    rw [ramificationGroupReal_eq_of_sub_one_lt_of_le H B (i := (m + 1 : ℕ))
        (by push_cast; linarith) (by push_cast; linarith),
      ramificationGroupReal_eq_of_sub_one_lt_of_le H B (i := (m + 1 : ℕ))
        (by push_cast; linarith) (by push_cast; linarith)]
  have hGdiff := herbrandFun_sub_herbrandFun_of_forall_eq G B h₁ hG
  have hHdiff := herbrandFun_sub_herbrandFun_of_forall_eq H B h₁ hH
  have hQdiff := herbrandFun_sub_herbrandFun_of_forall_eq G' C
    ((herbrandFun_strictMono H B).monotone h₁) fun _ ht₁ ht₂ ↦
      ramificationGroupReal_eq_of_forall_eq_of_map_eq π hmap ht₁ ht₂ hG
  have hcard : (Nat.card (ramificationGroupReal G' C (herbrandFun H B u)) : ℝ) *
      Nat.card (ramificationGroupReal H B u) = Nat.card (ramificationGroupReal G B u) := by
    exact_mod_cast natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq
      π ι hι hι_smul hexact (hmap' u)
  have hcard₀ : (Nat.card (ramificationGroup G' C 0) : ℝ) *
      Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
    have h0 := natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq
      π ι hι hι_smul hexact (hmap' 0)
    rw [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
      ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h0
    exact_mod_cast h0
  have hslope : (Nat.card (ramificationGroupReal G B u) : ℝ) / Nat.card (ramificationGroup G B 0) =
      (Nat.card (ramificationGroupReal H B u) / Nat.card (ramificationGroup H B 0)) *
        (Nat.card (ramificationGroupReal G' C (herbrandFun H B u)) /
          Nat.card (ramificationGroup G' C 0)) := by
    rw [div_mul_div_comm, ← hcard, ← hcard₀,
      mul_comm (Nat.card (ramificationGroupReal H B u) : ℝ),
      mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]
  rw [hslope] at hGdiff
  rw [hHdiff] at hQdiff
  linear_combination hGdiff - hQdiff + hm

/-- **Abstract tower transitivity of the Herbrand function**: `φ_G = φ_{G'} ∘ φ_H`. -/
theorem herbrandFun_eq_comp_of_map_ramificationGroupReal_eq
    (π : G →* G') (ι : H →* G) (hι : Function.Injective ι)
    (hι_smul : ∀ (τ : H) (b : B), ι τ • b = τ • b) (hexact : ι.range = π.ker)
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    (u : ℝ) :
    herbrandFun G B u = herbrandFun G' C (herbrandFun H B u) := by
  have hmap' := map_ramificationGroupReal_of_forall_neg_one_le π hmap
  rcases le_or_gt u (-1) with hu1 | hu1
  · have hφH : herbrandFun H B u ≤ -1 := by
      rw [← herbrandFun_neg_one H B]
      exact (herbrandFun_strictMono H B).monotone hu1
    rw [herbrandFun_of_le_neg_one G B hu1, herbrandFun_of_le_neg_one G' C hφH,
      herbrandFun_of_le_neg_one H B hu1]
    have hcardG : (Nat.card G' : ℝ) * Nat.card H = Nat.card G := by
      have hm1 := natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq
        π ι hι hι_smul hexact (hmap' (-1))
      rw [herbrandFun_neg_one, ramificationGroupReal_eq_top_of_le_neg_one _ _ le_rfl,
        ramificationGroupReal_eq_top_of_le_neg_one _ _ le_rfl,
        ramificationGroupReal_eq_top_of_le_neg_one _ _ le_rfl,
        Subgroup.card_top, Subgroup.card_top, Subgroup.card_top] at hm1
      exact_mod_cast hm1
    have hcard₀ : (Nat.card (ramificationGroup G' C 0) : ℝ) *
        Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
      have h0 := natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq
        π ι hι hι_smul hexact (hmap' 0)
      rw [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
        ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h0
      exact_mod_cast h0
    have hratio : (Nat.card G : ℝ) / Nat.card (ramificationGroup G B 0) =
        ((Nat.card H : ℝ) / Nat.card (ramificationGroup H B 0)) *
          ((Nat.card G' : ℝ) / Nat.card (ramificationGroup G' C 0)) := by
      rw [div_mul_div_comm, ← hcardG, ← hcard₀, mul_comm (Nat.card H : ℝ),
        mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]
    rw [hratio]
    ring
  · rcases le_or_gt u 0 with hu0 | hu0
    · rw [herbrandFun_eq_self_of_mem_Icc H B ⟨hu1.le, hu0⟩,
        herbrandFun_eq_self_of_mem_Icc G' C ⟨hu1.le, hu0⟩,
        herbrandFun_eq_self_of_mem_Icc G B ⟨hu1.le, hu0⟩]
    · have hind : ∀ m : ℕ, ∀ x : ℝ, (m : ℝ) ≤ x → x ≤ m + 1 →
          herbrandFun G B x = herbrandFun G' C (herbrandFun H B x) := by
        intro m
        induction m with
        | zero =>
          exact fun _ hx₁ hx₂ ↦ herbrandFun_eq_comp_of_mem_Icc_of_eq
            π ι hι hι_smul hexact hmap 0 hx₁ hx₂ (by simp)
        | succ k ih =>
          exact fun _ hx₁ hx₂ ↦ herbrandFun_eq_comp_of_mem_Icc_of_eq
            π ι hι hι_smul hexact hmap (k + 1) hx₁ hx₂
            (ih _ (by push_cast; linarith) (by push_cast; linarith))
      exact hind ⌊u⌋₊ u (Nat.floor_le hu0.le) (Nat.lt_floor_add_one u).le

/-- **Abstract tower transitivity of the inverse Herbrand function**:
`ψ_G = ψ_H ∘ ψ_{G'}`. -/
theorem inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq
    (π : G →* G') (ι : H →* G) (hι : Function.Injective ι)
    (hι_smul : ∀ (τ : H) (b : B), ι τ • b = τ • b) (hexact : ι.range = π.ker)
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    (v : ℝ) :
    inverseHerbrandFun G B v = inverseHerbrandFun H B (inverseHerbrandFun G' C v) := by
  apply (herbrandFun_strictMono G B).injective
  rw [herbrandFun_inverseHerbrandFun,
    herbrandFun_eq_comp_of_map_ramificationGroupReal_eq π ι hι hι_smul hexact hmap,
    herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun]

/-- **Abstract tower transitivity of `psiNat`**: `ψℕ_G = ψℕ_H ∘ ψℕ_{G'}`. -/
theorem psiNat_eq_comp_of_map_ramificationGroupReal_eq
    (π : G →* G') (ι : H →* G) (hι : Function.Injective ι)
    (hι_smul : ∀ (τ : H) (b : B), ι τ • b = τ • b) (hexact : ι.range = π.ker)
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat G' C n) := by
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, coe_psiNat, coe_psiNat,
    inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq π ι hι hι_smul hexact hmap]

/-- **Abstract Herbrand's theorem in the upper numbering**: `(G^v).map π = (G')^v`. -/
theorem map_upperRamificationGroup_of_map_ramificationGroupReal_eq
    (π : G →* G') (ι : H →* G) (hι : Function.Injective ι)
    (hι_smul : ∀ (τ : H) (b : B), ι τ • b = τ • b) (hexact : ι.range = π.ker)
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    (v : ℝ) :
    (upperRamificationGroup G B v).map π = upperRamificationGroup G' C v := by
  rw [upperRamificationGroup_def, map_ramificationGroupReal_of_forall_neg_one_le π hmap,
    inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq π ι hι hι_smul hexact hmap,
    herbrandFun_inverseHerbrandFun, ← upperRamificationGroup_def]

/-- **Abstract upper numbering of a normal subgroup**: `(G^v).comap ι = H^{ψ_{G'}(v)}`. -/
theorem comap_upperRamificationGroup_of_map_ramificationGroupReal_eq
    (π : G →* G') (ι : H →* G) (hι : Function.Injective ι)
    (hι_smul : ∀ (τ : H) (b : B), ι τ • b = τ • b) (hexact : ι.range = π.ker)
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    (v : ℝ) :
    (upperRamificationGroup G B v).comap ι =
      upperRamificationGroup H B (inverseHerbrandFun G' C v) := by
  have hcomap (u : ℝ) : (ramificationGroupReal G B u).comap ι = ramificationGroupReal H B u :=
    (ramificationGroupReal_eq_comap_of_ringEquiv ι (RingEquiv.refl B)
      (fun τ b ↦ (hι_smul τ b).symm) u).symm
  rw [upperRamificationGroup_def, hcomap,
    inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq π ι hι hι_smul hexact hmap,
    ← upperRamificationGroup_def]

omit [Finite G'] [Finite H] in
/-- If `(G^w).map π = (G')^w` for all `w ≥ v`, any upper break `v` of `G'` is an upper break of
`G`. -/
theorem UpperJump.of_map_upperRamificationGroup_eq {π : G →* G'} {v : ℝ}
    (hupper : ∀ w : ℝ, v ≤ w → (upperRamificationGroup G B w).map π = upperRamificationGroup G' C w)
    (hv : UpperJump G' C v) :
    UpperJump G B v := by
  refine (upperJump_iff G B v).2 fun w hvw ↦
    lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦
      ((upperJump_iff G' C v).1 hv w hvw).ne ?_
  rw [← hupper w hvw.le, heq, hupper v le_rfl]

/-- **Abstract upper breaks in a tower**: `v` is an upper break of `G` iff it is an upper break of
`G'` or `ψ_{G'}(v)` is an upper break of `H`. -/
theorem upperJump_iff_or_of_map_ramificationGroupReal_eq
    (π : G →* G') (ι : H →* G) (hι : Function.Injective ι)
    (hι_smul : ∀ (τ : H) (b : B), ι τ • b = τ • b) (hexact : ι.range = π.ker)
    (hmap : ∀ u : ℝ, -1 ≤ u →
      (ramificationGroupReal G B u).map π = ramificationGroupReal G' C (herbrandFun H B u))
    (v : ℝ) :
    UpperJump G B v ↔ UpperJump G' C v ∨ UpperJump H B (inverseHerbrandFun G' C v) := by
  have hupper := map_upperRamificationGroup_of_map_ramificationGroupReal_eq
    π ι hι hι_smul hexact hmap
  have hcomap := comap_upperRamificationGroup_of_map_ramificationGroupReal_eq
    π ι hι hι_smul hexact hmap
  constructor
  · intro hv
    refine or_iff_not_imp_left.2 fun hG' ↦ (upperJump_iff H B _).2 fun x hx ↦ ?_
    obtain ⟨w₀, hvw₀, hw₀⟩ : ∃ w₀, v < w₀ ∧
        upperRamificationGroup G' C w₀ = upperRamificationGroup G' C v := by
      simp only [upperJump_iff, not_forall] at hG'
      obtain ⟨w₀, hvw₀, hlt⟩ := hG'
      exact ⟨w₀, hvw₀, (upperRamificationGroup_antitone G' C hvw₀.le).eq_of_not_lt hlt⟩
    set w := min w₀ (herbrandFun G' C x)
    have hvw : v < w := lt_min hvw₀ <| by
      simpa only [herbrandFun_inverseHerbrandFun] using herbrandFun_strictMono G' C hx
    have hw : upperRamificationGroup G' C w = upperRamificationGroup G' C v :=
      le_antisymm (upperRamificationGroup_antitone G' C hvw.le)
        (hw₀ ▸ upperRamificationGroup_antitone G' C (min_le_left _ _))
    have hxw : inverseHerbrandFun G' C w ≤ x := by
      simpa only [inverseHerbrandFun_herbrandFun] using
        (inverseHerbrandFun_strictMono G' C).monotone (min_le_right w₀ (herbrandFun G' C x))
    refine (upperRamificationGroup_antitone H B hxw).trans_lt ?_
    rw [← hcomap w, ← hcomap v]
    refine lt_of_le_of_ne (Subgroup.comap_mono (upperRamificationGroup_antitone G B hvw.le))
      fun heq ↦ ((upperJump_iff G B v).1 hv w hvw).not_ge fun σ hσ ↦ ?_
    obtain ⟨τ, hτ, hτσ⟩ : π σ ∈ (upperRamificationGroup G B w).map π := by
      rw [hupper w, hw, ← hupper v]
      exact Subgroup.mem_map_of_mem _ hσ
    obtain ⟨ρ, hρ⟩ : τ⁻¹ * σ ∈ ι.range := by
      rw [hexact, MonoidHom.mem_ker, map_mul, map_inv, hτσ, inv_mul_cancel]
    have hρw : ρ ∈ (upperRamificationGroup G B w).comap ι := by
      rw [heq, Subgroup.mem_comap, hρ]
      exact mul_mem (inv_mem (upperRamificationGroup_antitone G B hvw.le hτ)) hσ
    rw [Subgroup.mem_comap, hρ] at hρw
    simpa only [mul_inv_cancel_left] using mul_mem hτ hρw
  · rintro (hG' | hH)
    · exact hG'.of_map_upperRamificationGroup_eq fun w _ ↦ hupper w
    · refine (upperJump_iff G B v).2 fun w hvw ↦
        lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ ?_
      have hlt := (upperJump_iff H B _).1 hH _ (inverseHerbrandFun_strictMono G' C hvw)
      rw [← hcomap w, ← hcomap v, heq] at hlt
      exact hlt.ne rfl

end AbstractTower

/-! ### Tower and upper-numbering theorems for `FixedPoints.subalgebra A B H` -/

section Subalgebra

variable (A B : Type*) [CommRing A] [_root_.IsLocalRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField B)]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (H : Subgroup G) [H.Normal]

/-- **Counting form of Herbrand's lemma** for `FixedPoints.subalgebra A B H`:
`#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u` for every `u : ℝ`. -/
theorem natCard_ramificationGroupReal_quotient_mul (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) :=
  natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H u).symm

/-- **Tower transitivity of the Herbrand function** for `FixedPoints.subalgebra A B H`:
`φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every `u : ℝ`. -/
theorem herbrandFun_tower (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) :=
  herbrandFun_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) u

/-- **Tower transitivity of the inverse Herbrand function** for `FixedPoints.subalgebra A B H`:
`ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))` for every `v : ℝ`. -/
theorem inverseHerbrandFun_tower (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) :=
  inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) v

/-- **Tower transitivity of `psiNat`** for `FixedPoints.subalgebra A B H`:
`ψℕ_G(n) = ψℕ_H(ψℕ_{G ⧸ H}(n))`. -/
theorem psiNat_tower (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) n) :=
  psiNat_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) n

/-- **Herbrand's theorem in the upper numbering** for `FixedPoints.subalgebra A B H`:
`(G ⧸ H)^v = G^v H / H` for every `v : ℝ`. -/
theorem upperRamificationGroup_quotient_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) :=
  (map_upperRamificationGroup_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) v).symm

/-- **Upper numbering of a normal subgroup** for `FixedPoints.subalgebra A B H`:
`H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for every `v : ℝ`. -/
theorem subgroupOf_upperRamificationGroup_quotient (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) :=
  comap_upperRamificationGroup_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) v

/-- **Upper breaks in a quotient** for `FixedPoints.subalgebra A B H`: `v` is an upper break of
`G` iff it is an upper break of `G ⧸ H` or `ψ_{G ⧸ H}(v)` is an upper break of `H`. -/
theorem upperJump_iff_upperJump_quotient_or (v : ℝ) :
    UpperJump G B v ↔
      UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v ∨
        UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) :=
  upperJump_iff_or_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_herbrandFun_eq_map A B G H w).symm) v

end Subalgebra

/-! ### Base-free corollaries for `FixedPoints.subring B H` -/

section Subring

variable (B G : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Group G] [Finite G] [MulSemiringAction G B]
  (H : Subgroup G) [H.Normal]
  [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
    (_root_.IsLocalRing.ResidueField B)]

/-- **Counting form of Herbrand's lemma** for `B^H`: `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u`. -/
theorem natCard_ramificationGroupReal_quotient_subring_mul (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) :=
  natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H u).symm

/-- **Tower transitivity of the Herbrand function** for `B^H`:
`φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every `u : ℝ`. -/
theorem herbrandFun_tower_subring (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) :=
  herbrandFun_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) u

/-- **Tower transitivity of the inverse Herbrand function** for `B^H`:
`ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))` for every `v : ℝ`. -/
theorem inverseHerbrandFun_tower_subring (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subring B H) v) :=
  inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) v

/-- **Tower transitivity of `psiNat`** for `B^H`: `ψℕ_G(n) = ψℕ_H(ψℕ_{G ⧸ H}(n))`. -/
theorem psiNat_tower_subring (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat (G ⧸ H) (FixedPoints.subring B H) n) :=
  psiNat_eq_comp_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) n

/-- **Herbrand's theorem in the upper numbering** for `B^H`:
`(G ⧸ H)^v = G^v H / H` for every `v : ℝ`. -/
theorem upperRamificationGroup_quotient_subring_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subring B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) :=
  (map_upperRamificationGroup_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) v).symm

/-- **Upper numbering of a normal subgroup** for `B^H`:
`H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for every `v : ℝ`. -/
theorem subgroupOf_upperRamificationGroup_subring (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subring B H) v) :=
  comap_upperRamificationGroup_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) v

/-- **Upper breaks in a quotient** for `B^H`. -/
theorem upperJump_iff_upperJump_quotient_subring_or (v : ℝ) :
    UpperJump G B v ↔
      UpperJump (G ⧸ H) (FixedPoints.subring B H) v ∨
        UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subring B H) v) :=
  upperJump_iff_or_of_map_ramificationGroupReal_eq (QuotientGroup.mk' H) H.subtype
    Subtype.val_injective (fun _ _ ↦ rfl)
    ((Subgroup.range_subtype H).trans (QuotientGroup.ker_mk' H).symm)
    (fun w _ ↦ (ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H w).symm) v

end Subring

/-! ### Field / integral-closure form -/

section FieldForm

variable (A K L : Type*) [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- If `integralClosure A L` is a DVR and `H ≤ Gal(L/K)` is finite, then
`integralClosure A (IntermediateField.fixedField H)` is also a DVR. -/
instance isDiscreteValuationRing_integralClosure_fixedField
    [IsDiscreteValuationRing (integralClosure A L)] (H : Subgroup (L ≃ₐ[K] L)) [Finite H] :
    IsDiscreteValuationRing (integralClosure A (IntermediateField.fixedField H)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (TauCeti.fixedPointsIntegralClosureEquivFixedField A K L H)

section GaloisField

variable [_root_.IsLocalRing A] [FiniteDimensional K L] [IsGalois K L]
  [IsDiscreteValuationRing (integralClosure A L)] [IsLocalHom (algebraMap A (integralClosure A L))]
  [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A)
    (_root_.IsLocalRing.ResidueField (integralClosure A L))]
  (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

/-- **Herbrand's theorem in field form** via `IsGalois.normalAutEquivQuotient`:
`IsGalois.normalAutEquivQuotient H` maps `G^v H / H` onto `Gal(L^H / K)^v` for every `v : ℝ`. -/
theorem upperRamificationGroup_fixedField_eq_map_normalAutEquivQuotient (v : ℝ) :
    ((upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map (QuotientGroup.mk' H)).map
        (IsGalois.normalAutEquivQuotient H).toMonoidHom =
      upperRamificationGroup
        (IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H)
        (integralClosure A (IntermediateField.fixedField H)) v := by
  rw [← upperRamificationGroup_quotient_eq_map A (integralClosure A L) (L ≃ₐ[K] L) H v]
  exact upperRamificationGroup_map_of_ringEquiv (IsGalois.normalAutEquivQuotient H)
    ((TauCeti.FixedPoints.subalgebraEquivSubring A (integralClosure A L) H).trans
      (TauCeti.fixedPointsIntegralClosureEquivFixedField A K L H))
    (fun q x ↦ by
      simp only [RingEquiv.trans_apply, TauCeti.FixedPoints.subalgebraEquivSubring_smul]
      exact TauCeti.fixedPointsIntegralClosureEquivFixedField_smul A K L H q _)
    v

/-- **Herbrand's theorem in field form** via `AlgEquiv.restrictNormalHom`: restriction from `L` to
`L^H` maps `Gal(L / K)^v` onto `Gal(L^H / K)^v` for every `v : ℝ`. -/
theorem map_restrictNormalHom_upperRamificationGroup_fixedField (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H)) =
      upperRamificationGroup
        (IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H)
        (integralClosure A (IntermediateField.fixedField H)) v := by
  have hcomp : (IsGalois.normalAutEquivQuotient H).toMonoidHom.comp (QuotientGroup.mk' H) =
      AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) :=
    MonoidHom.ext (IsGalois.normalAutEquivQuotient_apply H)
  rw [← hcomp, ← Subgroup.map_map]
  exact upperRamificationGroup_fixedField_eq_map_normalAutEquivQuotient A K L H v

end GaloisField

end FieldForm

end TauCeti.IsLocalRing
