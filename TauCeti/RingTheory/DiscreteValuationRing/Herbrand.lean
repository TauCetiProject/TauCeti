/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.LowerIndex
public import TauCeti.RingTheory.LocalRing.Herbrand
import TauCeti.Algebra.Group.Subgroup.Finite
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
import TauCeti.RingTheory.LocalRing.RingHom

/-!
# Herbrand's theorem over discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B` by `A`-algebra
automorphisms, with invariants the discrete valuation ring `A` and separable residue extension,
and let `H` be a normal subgroup. Mathlib makes `G ⧸ H` act on the fixed ring
`B^H = FixedPoints.subalgebra A B H`, again a discrete valuation ring; for a finite Galois
extension `L/K` with group `G` and integer ring `B`, this is the action of `Gal(L^H/K)` on the
integer ring of `L^H`. Write `φ_G`, `ψ_G` and `G^v` for the Herbrand function, its inverse and the
upper numbering of `G` acting on `B` (`TauCeti.IsLocalRing.herbrandFun`), and likewise for `H`
acting on `B` and for `G ⧸ H` acting on `B^H`.

The lower numbering does not pass to the quotient, but **Herbrand's theorem** says how it fails:

`(G/H)_{φ_H(u)} = G_u H / H`.

It follows from Serre's quotient formula for the lower index
(`TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_sum_card`) and the equality
`#H_0 = e(B/B^H)` of the order of the inertia group with the ramification index. Comparing orders,
with `H_u = H ∩ G_u`, gives `#(G/H)_{φ_H(u)} · #H_u = #G_u`, so that the slopes of `φ_G` and of
`φ_{G/H} ∘ φ_H` agree, which is the **transitivity of the Herbrand functions**

`φ_G = φ_{G/H} ∘ φ_H`  and  `ψ_G = ψ_H ∘ ψ_{G/H}`.

Together these give the compatibility of the upper numbering with quotients,

`(G/H)^v = G^v H / H`,

which is what makes the upper numbering pass to infinite Galois extensions, and the trace of the
upper filtration on `H`, `H ∩ G^v = H^{ψ_{G/H}(v)}`. All statements hold for every real index;
only indices in `[-1, ∞)` carry arithmetic meaning. Neither completeness of `A` nor finiteness of
its residue field is assumed. Separability of the residue extension cannot be dropped: it is what
makes `B` and `B^H` monogenic over `A`, on which the quotient formula rests.

On nonarchimedean local fields these are
`TauCeti.LocalFieldsRamification.map_restrictNormalHom_lowerRamificationGroupReal`,
`TauCeti.LocalFieldsRamification.herbrand_tower` and
`TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`.

## Main results

* `TauCeti.IsLocalRing.natCard_ramificationGroup_zero`: `#G_0 = e(B/A)`.
* `TauCeti.IsLocalRing.map_mk'_ramificationGroupReal`: **Herbrand's theorem**
  `(G/H)_{φ_H(u)} = G_u H / H`.
* `TauCeti.IsLocalRing.natCard_ramificationGroupReal_herbrandFun_mul`: its counting form
  `#(G/H)_{φ_H(u)} · #H_u = #G_u`.
* `TauCeti.IsLocalRing.herbrandFun_tower`, `TauCeti.IsLocalRing.inverseHerbrandFun_tower`:
  `φ_G = φ_{G/H} ∘ φ_H` and `ψ_G = ψ_H ∘ ψ_{G/H}`.
* `TauCeti.IsLocalRing.map_mk'_upperRamificationGroup`: `(G/H)^v = G^v H / H`.
* `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun`:
  `H ∩ G^v = H^{ψ_{G/H}(v)}`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Corollary to Proposition 4, and §3,
  Lemma 5 and Propositions 14 and 15.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti.IsLocalRing

section Inertia

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]

/-- **The inertia group has order the ramification index.** Let a finite group `G` act faithfully
on the discrete valuation ring `B` by `A`-algebra automorphisms, with invariants the discrete
valuation ring `A` and separable residue extension. Then `#G_0 = e(B/A)`. -/
theorem natCard_ramificationGroup_zero [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Nat.card (ramificationGroup G B 0) = (maximalIdeal B).ramificationIdx A := by
  have := Algebra.IsInvariant.isIntegral A B G
  have := IsDiscreteValuationRing.faithfulSMul_of_isIntegral (R := A) (S := B)
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have := IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G A B
  -- The residue fields are the quotients by the maximal ideals.
  have : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B) :=
    ‹Algebra.IsSeparable (ResidueField A) (ResidueField B)›
  rw [ramificationGroup_zero_eq_inertia,
    Ideal.card_inertia_eq_ramificationIdxIn_of_isSeparable (G := G) (maximalIdeal A),
    Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) G]

end Inertia

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]
  (H : Subgroup G) [H.Normal]

/-! ### Herbrand's theorem in the lower numbering -/

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
  rcases eq_or_ne (lowerIndex B σ) ⊤ with htop | htop
  · -- `i_G(σ) = ⊤` means `σ = 1`, and both sides hold.
    rw [lowerIndex_eq_top_iff] at htop
    subst htop
    exact iff_of_true (one_mem _) (one_mem _)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 htop
  have hsum := ramificationIdx_mul_lowerIndex_mk_eq_sum_card A H hj.symm hσ
  -- The ramification index of `B` over `B^H` is `#H_0`.
  have := Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A)
    (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B)
  rw [← natCard_ramificationGroup_zero (FixedPoints.subalgebra A B H) B H] at hsum
  -- Hence `i_{G/H}(σ H)` is a natural number `n` with `#H_0 · n = ∑_{k < j} #H_k`.
  have h0 : Nat.card (ramificationGroup H B 0) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 <|
    show lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) ≠ ⊤ from fun h ↦ by
      rw [h, ENat.mul_top (by exact_mod_cast h0), ← Nat.cast_sum] at hsum
      exact ENat.natCast_ne_top _ hsum.symm
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj] at hsum
  -- It remains to show `φ_H(j - 1) = n - 1`.
  have hφ : herbrandFun H B ((j : ℝ) - 1) = (n : ℝ) - 1 := by
    have h0R : (Nat.card (ramificationGroup H B 0) : ℝ) ≠ 0 := by exact_mod_cast h0
    rcases j with _ | m
    · simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, h0, false_or] at hsum
      simp [hsum]
    · rw [Nat.cast_add_one, add_sub_cancel_right, herbrandFun_natCast, div_eq_iff h0R]
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
        zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
      have hsumR : (Nat.card (ramificationGroup H B 0) : ℝ) * n =
          Nat.card (ramificationGroup H B 0) +
            ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup H B i) : ℝ) := by
        exact_mod_cast hsum
      linear_combination -hsumR
  rw [mem_ramificationGroupReal_iff_of_lowerIndex_eq hn.symm,
    mem_ramificationGroupReal_iff_of_lowerIndex_eq hj.symm, ← hφ]
  exact (herbrandFun_strictMono H B).le_iff_le

variable (A) in
/-- **Herbrand's theorem.** The image of the lower ramification group `G_u` in `G ⧸ H` is the
lower ramification group of `G ⧸ H` acting on `B^H` at `φ_H(u)`:
`(G/H)_{φ_H(u)} = G_u H / H`. -/
theorem map_mk'_ramificationGroupReal (u : ℝ) :
    (ramificationGroupReal G B u).map (QuotientGroup.mk' H) =
      ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  ext q
  induction q using QuotientGroup.induction_on with | H σ =>
  -- Replace `σ` by an element `σ τ₀` of largest lower index in its coset.
  obtain ⟨τ₀, hτ₀H, hτ₀⟩ := H.exists_mem_forall_lowerIndex_mul_le (S := B) σ
  have hmk : ((σ * τ₀ : G) : G ⧸ H) = σ := QuotientGroup.mk_mul_of_mem σ hτ₀H
  rw [← hmk, mk_mem_ramificationGroupReal_herbrandFun_iff A H hτ₀, Subgroup.mem_map]
  constructor
  · rintro ⟨σ', hσ', hσ'σ⟩
    -- `σ' = σ τ₀ τ` with `τ ∈ H`, and `i(σ') ≤ i(σ τ₀)`.
    obtain ⟨τ, hτ, rfl⟩ : ∃ τ ∈ H, σ * τ₀ * τ = σ' :=
      ⟨(σ * τ₀)⁻¹ * σ', QuotientGroup.eq.1 hσ'σ.symm, mul_inv_cancel_left _ _⟩
    rw [ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex] at hσ' ⊢
    exact hσ'.trans (hτ₀ τ hτ)
  · exact fun h ↦ ⟨σ * τ₀, h, rfl⟩

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
  -- Hence `F` vanishes at every integer, since it vanishes at `0`.
  have hint (i : ℤ) : F i = 0 := by
    induction i using Int.induction_on with
    | zero => simp [F]
    | succ i ih =>
      have h := hstep (i := i + 1) (x := ((i + 1 : ℤ) : ℝ)) (by linarith) le_rfl
      push_cast at h ih ⊢
      rw [h, add_sub_cancel_right, ih]
    | pred i ih =>
      have h := hstep (i := -i) (x := ((-i : ℤ) : ℝ)) (by linarith) le_rfl
      push_cast at h ih ⊢
      rw [← h, ih]
  have h := hstep (by linarith [Int.ceil_lt_add_one u]) (Int.le_ceil u)
  rw [← Int.cast_one, ← Int.cast_sub, hint] at h
  simp only [F] at h
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

/-! ### The upper numbering -/

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

end TauCeti.IsLocalRing
