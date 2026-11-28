/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Inertia
public import TauCeti.RingTheory.DiscreteValuationRing.LowerIndex
public import TauCeti.RingTheory.LocalRing.Herbrand.Jump
import TauCeti.Algebra.Group.Subgroup.Finite
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.RingTheory.LocalRing.FixedPoints.ResidueField

/-!
# Herbrand's theorem and tower transitivity over discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B` by `A`-algebra
automorphisms over a local ring `A` with separable residue extension, and let `H` be a normal
subgroup. `G ⧸ H` acts on the fixed ring `B^H = FixedPoints.subalgebra A B H`, again a discrete
valuation ring; for a finite Galois extension `L/K` with group `G` and integer ring `B`, this is
the action of `Gal(L^H/K)` on the integer ring of `L^H`. Write `φ_G`, `ψ_G` and `G^v` for the
Herbrand function, its inverse and the upper numbering of `G` acting on `B`
(`TauCeti.IsLocalRing.herbrandFun`), and likewise for `H` acting on `B` and for `G ⧸ H` acting on
`B^H`.

The lower numbering does not pass to the quotient, but **Herbrand's theorem** says how it fails:

`(G/H)_{φ_H(u)} = G_u H / H`.

It follows from Serre's quotient formula for the lower index
(`TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_sum_card`) and the equality
`#H_0 = e(B/B^H)` of the order of the inertia group with the ramification index
(`TauCeti.IsLocalRing.natCard_ramificationGroup_zero_fixedPoints`). Comparing orders, with
`H_u = H ∩ G_u`, gives `#(G/H)_{φ_H(u)} · #H_u = #G_u`, so that the slopes of `φ_G` and of
`φ_{G/H} ∘ φ_H` agree, which is the **transitivity of the Herbrand functions**

`φ_G = φ_{G/H} ∘ φ_H`  and  `ψ_G = ψ_H ∘ ψ_{G/H}`.

Together these give the compatibility of the upper numbering with quotients,

`(G/H)^v = G^v H / H`,

which is what makes the upper numbering pass to infinite Galois extensions, the trace of the upper
filtration on `H`, `H ∩ G^v = H^{ψ_{G/H}(v)}`, and the decomposition of upper breaks
(`upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun`). All statements hold for every
real index; only indices in `[-1, ∞)` carry arithmetic meaning. Neither completeness of `A` nor
finiteness of its residue field is assumed.

On nonarchimedean local fields these are
`TauCeti.LocalFieldsRamification.map_restrictNormalHom_lowerRamificationGroupReal`,
`TauCeti.LocalFieldsRamification.herbrand_tower`,
`TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`, and
`TauCeti.LocalFieldsRamification.upperJump_iff_upperJump_or_upperJump_inverseHerbrand` (adapting
`TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient` for the upper-break decomposition).

## Main results

* `TauCeti.IsLocalRing.map_mk'_ramificationGroupReal`: **Herbrand's theorem**
  `(G/H)_{φ_H(u)} = G_u H / H`.
* `TauCeti.IsLocalRing.natCard_ramificationGroupReal_herbrandFun_mul`: its counting form
  `#(G/H)_{φ_H(u)} · #H_u = #G_u`.
* `TauCeti.IsLocalRing.herbrandFun_tower`, `TauCeti.IsLocalRing.inverseHerbrandFun_tower`,
  `TauCeti.IsLocalRing.herbrandOrderIso_tower`, `TauCeti.IsLocalRing.psiNat_tower`:
  `φ_G = φ_{G/H} ∘ φ_H` and `ψ_G = ψ_H ∘ ψ_{G/H}`.
* `TauCeti.IsLocalRing.map_mk'_upperRamificationGroup`: `(G/H)^v = G^v H / H`.
* `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun`:
  `H ∩ G^v = H^{ψ_{G/H}(v)}`.
* `TauCeti.IsLocalRing.upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun`: upper
  breaks in a quotient.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Corollary to Proposition 4, and §3,
  Lemma 5 and Propositions 14 and 15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, pp. 127–128.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti.IsLocalRing

attribute [local instance] fixedPointsSubalgebraAlgebra isScalarTower_fixedPoints_subalgebra
  faithfulSMul_fixedPoints_subalgebra isLocalHom_algebraMap_fixedPoints_subalgebra
  FixedPoints.moduleFinite_subalgebra_of_isDiscreteValuationRing
  FixedPoints.moduleFinite_subalgebra_of_le
  isSeparable_residueField_fixedPoints_subalgebra
  isSeparable_residueField_fixedPoints_subalgebra_of_le

variable {A B : Type*} [CommRing A] [IsLocalRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [FaithfulSMul G B]
  (H : Subgroup G) [H.Normal]

/-! ### Herbrand's theorem in the lower numbering -/

private theorem herbrandFun_lowerIndex_sub_one_mk' {σ : G} {j : ℕ}
    (hj : lowerIndex B σ = j)
    (hσ : ∀ τ ∈ (QuotientGroup.mk' H).ker, lowerIndex B (σ * τ) ≤ lowerIndex B σ) :
    herbrandFun H B ((j : ℝ) - 1) =
      ((lowerIndex (FixedPoints.subalgebra A B H) ((QuotientGroup.mk' H) σ)).toNat : ℝ) - 1 := by
  have hsum := ramificationIdx_mul_lowerIndex_mk_eq_sum_card A B G H hj
    (by simpa only [QuotientGroup.ker_mk'] using hσ)
  rw [← natCard_ramificationGroup_zero_fixedPoints A B H] at hsum
  exact herbrandFun_sub_one_of_card_mul_eq_sum H B
    (lowerIndex_ne_top_of_forall_mem_ker_le (π := QuotientGroup.mk' H)
      (hj ▸ ENat.natCast_ne_top j) hσ) hsum

variable (A) in
/-- If `σ` has the largest lower index in its coset `σ H`, then its class lies in the lower
ramification group of `G ⧸ H` at `φ_H(u)` exactly when `σ` lies in `G_u`. By Serre's lemma
`e · i_{G/H}(σ H) = ∑_{k < i_G(σ)} #H_k` with `e = #H_0`, the lower indices satisfy
`i_{G/H}(σ H) - 1 = φ_H(i_G(σ) - 1)`. -/
theorem mk_mem_ramificationGroupReal_herbrandFun_iff {σ : G}
    (hσ : ∀ τ ∈ H, lowerIndex B (σ * τ) ≤ lowerIndex B σ) (u : ℝ) :
    (σ : G ⧸ H) ∈
        ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) ↔
      σ ∈ ramificationGroupReal G B u := by
  have hσ' : ∀ τ ∈ (QuotientGroup.mk' H).ker, lowerIndex B (σ * τ) ≤ lowerIndex B σ := by
    simpa only [QuotientGroup.ker_mk'] using hσ
  exact apply_mem_ramificationGroupReal_iff (π := QuotientGroup.mk' H)
    (herbrandFun_strictMono H B) (fun hj ↦ lowerIndex_ne_top_of_forall_mem_ker_le hj hσ')
    (fun hj ↦ herbrandFun_lowerIndex_sub_one_mk' (A := A) H hj hσ') u

variable (A) in
/-- **Herbrand's theorem.** The image of the lower ramification group `G_u` in `G ⧸ H` is the
lower ramification group of `G ⧸ H` acting on `B^H` at `φ_H(u)`:
`(G/H)_{φ_H(u)} = G_u H / H`. -/
theorem map_mk'_ramificationGroupReal (u : ℝ) :
    (ramificationGroupReal G B u).map (QuotientGroup.mk' H) =
      ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) :=
  map_ramificationGroupReal_eq_of_surjective (QuotientGroup.mk'_surjective H)
    (herbrandFun_strictMono H B)
    (fun _ hσ hj ↦ lowerIndex_ne_top_of_forall_mem_ker_le hj hσ)
    (fun _ hσ _ hj ↦ herbrandFun_lowerIndex_sub_one_mk' (A := A) H hj hσ) u

variable (A) in
/-- **Herbrand's theorem in counting form**: `#(G/H)_{φ_H(u)} · #H_u = #G_u`. The kernel of
`G_u → G ⧸ H` is `H ∩ G_u = H_u`. -/
theorem natCard_ramificationGroupReal_herbrandFun_mul (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) := by
  set Gu := ramificationGroupReal G B u
  -- `G_u H / H` is the range of `G_u → G ⧸ H`, whose kernel is `H ∩ G_u`, read in `G_u`.
  have hker : ((QuotientGroup.mk' H).domRestrict Gu).ker = H.subgroupOf Gu := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  rw [← map_mk'_ramificationGroupReal A H u, ← MonoidHom.domRestrict_range,
    ← subgroupOf_ramificationGroupReal, Subgroup.card_subgroupOf_comm, ← hker, mul_comm,
    Subgroup.card_ker_mul_card_range]

/-! ### Transitivity of the Herbrand functions -/

/-- On an interval `[a, b]` over which the lower filtration of `G` is constant, the increments of
`φ_G` and of `φ_{G/H} ∘ φ_H` agree: both are affine there, and Herbrand's theorem in counting form
identifies their slopes. -/
private theorem herbrandFun_sub_eq_herbrandFun_herbrandFun_sub {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal G B t = ramificationGroupReal G B b) :
    herbrandFun G B b - herbrandFun G B a =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B b) -
        herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B a) := by
  -- The filtrations of `H` and of `G ⧸ H` are constant on `(a, b]` and `(φ_H(a), φ_H(b)]`.
  have hH : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal H B t = ramificationGroupReal H B b :=
    fun t ht₁ ht₂ ↦ by
      rw [← subgroupOf_ramificationGroupReal, ← subgroupOf_ramificationGroupReal, h t ht₁ ht₂]
  have hQ : ∀ s : ℝ, herbrandFun H B a < s → s ≤ herbrandFun H B b →
      ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) s =
        ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B b) :=
    fun s hs₁ hs₂ ↦ by
      rw [← herbrandFun_inverseHerbrandFun H B s, ← map_mk'_ramificationGroupReal,
        ← map_mk'_ramificationGroupReal, h _ (lt_inverseHerbrandFun_iff.2 hs₁)
          (inverseHerbrandFun_le_iff.2 hs₂)]
  have hcard : (Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H)
      (herbrandFun H B b)) : ℝ) * Nat.card (ramificationGroupReal H B b) =
        Nat.card (ramificationGroupReal G B b) := by
    exact_mod_cast natCard_ramificationGroupReal_herbrandFun_mul A H b
  have hcard₀ : (Nat.card (ramificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) 0) : ℝ) *
      Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
    have h₀ := natCard_ramificationGroupReal_herbrandFun_mul (B := B) A H 0
    rw [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
      ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h₀
    exact_mod_cast h₀
  rw [herbrandFun_sub_herbrandFun_of_forall_eq _ _ ((herbrandFun_strictMono H B).monotone hab) hQ,
    herbrandFun_sub_herbrandFun_of_forall_eq _ _ hab hH,
    herbrandFun_sub_herbrandFun_of_forall_eq _ _ hab h, ← hcard, ← hcard₀]
  ring

variable (A) in
/-- **Transitivity of the Herbrand function**: `φ_G = φ_{G/H} ∘ φ_H`, that is
`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}` for `L = M^H`. -/
@[simp]
theorem herbrandFun_tower (u : ℝ) :
    herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) = herbrandFun G B u := by
  set F : ℝ → ℝ := fun x ↦
    herbrandFun G B x - herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B x)
  -- `F` is constant on every interval `[i - 1, i]` with `i : ℤ`.
  have hstep {i : ℤ} {x : ℝ} (h₁ : (i : ℝ) - 1 ≤ x) (h₂ : x ≤ i) : F x = F ((i : ℝ) - 1) := by
    have := herbrandFun_sub_eq_herbrandFun_herbrandFun_sub (A := A) H h₁ fun t ht₁ ht₂ ↦ by
      rw [ramificationGroupReal_eq_of_sub_one_lt_of_le G B ht₁ (ht₂.trans h₂),
        ramificationGroupReal_eq_of_sub_one_lt_of_le G B (ht₁.trans_le ht₂) h₂]
    simp only [F]
    linarith
  -- Hence `F` is constant, and it vanishes at `0`.
  have h := apply_eq_apply_zero_of_forall_mem_Icc_intCast_sub_one
    (fun i x hx ↦ hstep (i := i) (x := x) hx.1 hx.2) u
  simp only [F, herbrandFun_zero, sub_self] at h
  linarith

variable (A) in
/-- **Transitivity of the inverse Herbrand function**: `ψ_G = ψ_H ∘ ψ_{G/H}`, that is
`ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}` for `L = M^H`. -/
@[simp]
theorem inverseHerbrandFun_tower (v : ℝ) :
    inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) =
      inverseHerbrandFun G B v := by
  refine (herbrandFun_strictMono G B).injective ?_
  rw [← herbrandFun_tower A H, herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun,
    herbrandFun_inverseHerbrandFun]

variable (A) in
/-- **Transitivity of the bundled Herbrand order isomorphisms** on `ℝ`. -/
theorem herbrandOrderIso_tower : herbrandOrderIso G B =
    (herbrandOrderIso H B).trans (herbrandOrderIso (G ⧸ H) (FixedPoints.subalgebra A B H)) :=
  OrderIso.ext <| funext fun u ↦ by simp

variable (A) in
/-- **Transitivity of the integral inverse Herbrand function**: `ψℕ_G = ψℕ_H ∘ ψℕ_{G ⧸ H}`. -/
theorem psiNat_tower :
    psiNat G B = psiNat H B ∘ psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) :=
  funext fun _ ↦ Nat.cast_injective (R := ℝ) <| by simp

/-! ### The upper numbering and upper breaks -/

variable (A) in
/-- **Herbrand's theorem in the upper numbering.** The image of the upper ramification group
`G^v` in `G ⧸ H` is the upper ramification group of `G ⧸ H` acting on `B^H` at the same index:
`(G/H)^v = G^v H / H`. -/
theorem map_mk'_upperRamificationGroup (v : ℝ) :
    (upperRamificationGroup G B v).map (QuotientGroup.mk' H) =
      upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v := by
  rw [upperRamificationGroup_def, map_mk'_ramificationGroupReal A H,
    ← inverseHerbrandFun_tower A H, herbrandFun_inverseHerbrandFun, upperRamificationGroup_def]

variable (A) in
/-- The trace of the upper filtration of `G` on the normal subgroup `H` is the upper filtration of
`H`, reindexed by the inverse Herbrand function of the quotient: `H ∩ G^v = H^{ψ_{G/H}(v)}`, that
is `Gal(M/L) ∩ Gal(M/K)^v = Gal(M/L)^{ψ_{L/K}(v)}` for `L = M^H`. -/
theorem subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B
        (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [subgroupOf_upperRamificationGroup, ← inverseHerbrandFun_tower A H,
    herbrandFun_inverseHerbrandFun]

variable {H} in
/-- An upper break of `G ⧸ H` on `B^H` is an upper break of `G` on `B`. -/
theorem UpperJump.of_quotient {v : ℝ} (hv : UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v) :
    UpperJump G B v := by
  rw [upperJump_iff] at hv ⊢
  intro w hvw
  refine lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ (hv w hvw).ne ?_
  rw [← map_mk'_upperRamificationGroup A H, heq, map_mk'_upperRamificationGroup A H]

variable {H} in
/-- If `ψ_{G ⧸ H}(v)` is an upper break of `H` on `B`, then `v` is an upper break of `G` on `B`. -/
theorem UpperJump.of_inverseHerbrandFun {v : ℝ}
    (hv : UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v)) :
    UpperJump G B v := by
  rw [upperJump_iff] at hv ⊢
  intro w hvw
  refine lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦
    (hv _ (inverseHerbrandFun_strictMono (G ⧸ H) (FixedPoints.subalgebra A B H) hvw)).ne ?_
  rw [← subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun A H,
    ← subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun A H, heq]

/-- **Upper breaks in a quotient**: `UpperJump G B v` iff `UpperJump (G ⧸ H) B^H v` or
`UpperJump H B (ψ_{G ⧸ H}(v))`. -/
theorem upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun (v : ℝ) :
    UpperJump G B v ↔ UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v ∨
      UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  let C := FixedPoints.subalgebra A B H
  refine ⟨fun hv ↦ or_iff_not_imp_left.2 fun hQ ↦ ?_,
    fun h ↦ h.elim UpperJump.of_quotient UpperJump.of_inverseHerbrandFun⟩
  rw [upperJump_iff] at hv ⊢
  intro x hx
  simp only [upperJump_iff, not_forall] at hQ
  obtain ⟨w₀, hvw₀, hlt⟩ := hQ
  have hw₀ := (upperRamificationGroup_antitone (G ⧸ H) C hvw₀.le).eq_of_not_lt hlt
  set w := min w₀ (herbrandFun (G ⧸ H) C x)
  have hvw : v < w := lt_min hvw₀ (inverseHerbrandFun_lt_iff.1 hx)
  have hw : upperRamificationGroup (G ⧸ H) C w = upperRamificationGroup (G ⧸ H) C v :=
    le_antisymm (upperRamificationGroup_antitone (G ⧸ H) C hvw.le)
      (hw₀ ▸ upperRamificationGroup_antitone (G ⧸ H) C (min_le_left _ _))
  refine (upperRamificationGroup_antitone H B
    ((inverseHerbrandFun_le_iff (G := G ⧸ H) (S := C)).2 (min_le_right w₀ _))).trans_lt ?_
  rw [← subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun A H,
    ← subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun A H]
  refine lt_of_le_of_ne (Subgroup.comap_mono (upperRamificationGroup_antitone G B hvw.le))
    fun heq ↦ (QuotientGroup.strictMono_comap_prod_map H (hv w hvw)).ne (Prod.ext heq ?_)
  simpa only [map_mk'_upperRamificationGroup A H] using hw

end TauCeti.IsLocalRing
