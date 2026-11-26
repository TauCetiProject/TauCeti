/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.Herbrand

/-!
# Abstract local-ring propagation of Herbrand's theorem in a tower

Let finite groups `G`, `G'`, and `H` act by ring automorphisms on local rings `B` and `C`, linked
by an exact sequence `1 → H → G → G'` (with `ι : H →* G` injective, `H`-equivariant on `B`, and
`ι(H) = ker π` for `π : G →* G'`). Once Herbrand's lower-numbering identity
`(G_u).map π = G'_{φ_H(u)}` is known for `u ≥ -1`, all tower properties of the Herbrand functions
and upper ramification groups follow purely from the step-function and order-isomorphism properties
of `φ` and `ψ` on local rings, without any discrete-valuation hypothesis:

* **Counting form**: `#G'_{φ_H(u)} · #H_u = #G_u`.
* **Tower transitivity**: `φ_G = φ_{G'} ∘ φ_H`, `ψ_G = ψ_H ∘ ψ_{G'}`, and `ψℕ_G = ψℕ_H ∘ ψℕ_{G'}`.
* **Upper-numbering quotient and subgroup compatibilities**: `(G^v).map π = (G')^v` and
  `(G^v).comap ι = H^{ψ_{G'}(v)}`.
* **Upper breaks in a tower**: `v` is an upper break of `G` iff it is an upper break of `G'` or
  `ψ_{G'}(v)` is an upper break of `H`.

Isolating this layer in `TauCeti.RingTheory.LocalRing.Herbrand.Tower` allows both the DVR API
(`TauCeti.RingTheory.DiscreteValuationRing.Herbrand.Tower`) and the nonarchimedean local-field API
(`TauCeti.NumberTheory.LocalField.Herbrand.{Tower,UpperQuotient}`) to specialize these theorems
without importing DVR quotient machinery.

## Main results

* `TauCeti.IsLocalRing.map_ramificationGroupReal_of_forall_neg_one_le`: extends
  `(G_u).map π = G'_{φ_H(u)}` from `[-1, ∞)` to all of `ℝ`.
* `TauCeti.IsLocalRing.natCard_ramificationGroupReal_herbrandFun_mul_of_map_eq`: counting form
  `#G'_{φ_H(u)} · #H_u = #G_u`.
* `TauCeti.IsLocalRing.herbrandFun_eq_comp_of_map_ramificationGroupReal_eq`,
  `TauCeti.IsLocalRing.inverseHerbrandFun_eq_comp_of_map_ramificationGroupReal_eq`,
  `TauCeti.IsLocalRing.psiNat_eq_comp_of_map_ramificationGroupReal_eq`: tower transitivity of `φ`,
  `ψ`, and `ψℕ`.
* `TauCeti.IsLocalRing.map_upperRamificationGroup_of_map_ramificationGroupReal_eq`,
  `TauCeti.IsLocalRing.comap_upperRamificationGroup_of_map_ramificationGroupReal_eq`: upper
  ramification groups of quotients and normal subgroups.
* `TauCeti.IsLocalRing.UpperJump.of_map_upperRamificationGroup_eq`,
  `TauCeti.IsLocalRing.upperJump_iff_or_of_map_ramificationGroupReal_eq`: upper breaks in a tower.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Propositions 14 and 15.
-/

public section
noncomputable section

namespace TauCeti.IsLocalRing

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
    ← ramificationGroupReal_eq_top_of_le_neg_one G B (u := -1) le_rfl, hmap (-1) le_rfl,
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

end TauCeti.IsLocalRing
