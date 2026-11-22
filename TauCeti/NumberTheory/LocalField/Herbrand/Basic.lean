/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationGroup
public import TauCeti.RingTheory.LocalRing.Herbrand.Basic
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# The Herbrand function and the upper numbering

Let `L/K` be a finite Galois extension of nonarchimedean local fields, with lower ramification
groups `G_u = G_{⌈u⌉}` of `G = Gal(L/K)` indexed by real `u ≥ -1`. The **Herbrand function** is

`φ_{L/K}(u) = ∫_0^u dt / [G_0 : G_t]`,

for `u ≥ -1`. Since `G_t` is a subgroup of `G_0` for `t > -1`, the integrand is
`#G_t / #G_0`; it equals `1` on `(-1, 0]`, so `φ(u) = u` for `-1 ≤ u ≤ 0`. On each interval
`[m, m + 1]` with `m : ℕ` the function `φ` is affine of slope `#G_{m+1} / #G_0`, which gives the
finite-sum formula

`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`.

The integrand is positive and bounded below by `1 / #G_0`, so `φ` is a strictly increasing
continuous bijection of `[-1, ∞)` onto itself. This file packages it as an order isomorphism
`herbrandOrderIso K L` of the domain `RamificationIndexDomain = [-1, ∞)`, whose forward map is
`herbrand K L` and whose inverse is the inverse Herbrand function `inverseHerbrand K L`, usually
written `ψ_{L/K}`. Keeping the domain in the type means that no statement concerns a value
below `-1`.

Although `φ` may take non-integral values at integers, `ψ` maps natural numbers to natural numbers.
The resulting **integral inverse Herbrand function** `psiNat K L : ℕ → ℕ`, written `ψℕ_{L/K}`, is
the form in which Herbrand values serve as depths of the unit filtration, for instance when
`N_{L/K}(U(L, ψℕ(i)))` is compared with `U(K, i)`. It is characterized arithmetically by
`ψℕ(n) = m ↔ #G_1 + ⋯ + #G_m = n · #G_0`.

The **upper numbering** of the ramification groups is `G^v = G_{ψ(v)}`, so that
`G^{φ(u)} = G_u`. Its point is the compatibility with quotients, `(G/H)^v = G^v H / H` for `H`
normal, which the lower numbering lacks; that theorem is not proved here.

The Herbrand function and the upper numbering are defined only for Galois `L/K`: for a
non-Galois extension the automorphism group does not carry the ramification of `L/K`, and the
classical `φ_{L/K}` is instead defined through a Galois closure.

## Main definitions

* `TauCeti.LocalFieldsRamification.RamificationIndexDomain`: the interval `[-1, ∞)`.
* `TauCeti.LocalFieldsRamification.herbrandOrderIso`: the Herbrand function as an order
  automorphism of `[-1, ∞)`.
* `TauCeti.LocalFieldsRamification.herbrand`, `TauCeti.LocalFieldsRamification.inverseHerbrand`:
  its forward map `φ_{L/K}` and its inverse `ψ_{L/K}`.
* `TauCeti.LocalFieldsRamification.psiNat`: the inverse Herbrand function at natural numbers,
  `ψℕ_{L/K} : ℕ → ℕ`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup`: the upper-numbering ramification
  group `G^v = G_{ψ(v)}`.

## Main results

* `TauCeti.LocalFieldsRamification.coe_herbrand`: the integral formula defining `φ`.
* `TauCeti.LocalFieldsRamification.coe_herbrand_of_mem_Icc` and
  `TauCeti.LocalFieldsRamification.coe_herbrand_of_coe_eq_natCast`: the finite-sum formula.
* `TauCeti.LocalFieldsRamification.herbrand_of_coe_le_zero` and
  `TauCeti.LocalFieldsRamification.inverseHerbrand_of_coe_le_zero`: `φ` and `ψ` are the identity
  on `[-1, 0]`.
* `TauCeti.LocalFieldsRamification.herbrand_inverseHerbrand` and
  `TauCeti.LocalFieldsRamification.inverseHerbrand_herbrand`: `φ ∘ ψ = id` and `ψ ∘ φ = id`.
* `TauCeti.LocalFieldsRamification.coe_herbrand_sub_coe_herbrand_of_forall_eq`: `φ` is affine
  of slope `#G_b / #G_0` on an interval `[a, b]` where the filtration is constant.
* `TauCeti.LocalFieldsRamification.herbrand_slope_anti_adjacent`: `φ` is concave.
* `TauCeti.LocalFieldsRamification.continuous_herbrand`,
  `TauCeti.LocalFieldsRamification.herbrand_strictMono` and their counterparts for `ψ`.
* `TauCeti.LocalFieldsRamification.coe_psiNat`: `ψℕ(n) = ψ(n)` for `n : ℕ`, and
  `TauCeti.LocalFieldsRamification.psiNat_eq_iff`: `ψℕ(n) = m ↔ #G_1 + ⋯ + #G_m = n · #G_0`.
* `TauCeti.LocalFieldsRamification.psiNat_strictMono`,
  `TauCeti.LocalFieldsRamification.self_le_psiNat`: `ψℕ` is strictly increasing and `n ≤ ψℕ(n)`.
* `TauCeti.LocalFieldsRamification.psiNat_le_iff_le_floor_herbrand`:
  `ψℕ(n) ≤ i ↔ n ≤ ⌊φ(i)⌋`.
* `TauCeti.LocalFieldsRamification.psiNat_eq_self_iff`,
  `TauCeti.LocalFieldsRamification.psiNat_eq_add_card_mul_sub`: `ψℕ(v) = v` exactly when
  `G_v = G_0`, and `ψℕ(v) = t + #G_0 (v - t)` for `v ≥ t` when the filtration is
  constant through `t` and trivial afterward.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_herbrand` and
  `TauCeti.LocalFieldsRamification.upperRamificationGroup_eq_of_herbrand_lt_of_le`:
  `G^{φ(u)} = G_u`, and `G^v = G_{i+1}` on `(φ(i), φ(i + 1)]`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_antitone`: the upper filtration
  decreases, and each `G^v` is normal.
* `TauCeti.LocalFieldsRamification.exists_forall_upperRamificationGroup_natCast_eq_bot`:
  `G^n = 1` for every large enough natural number `n`.
* `TauCeti.LocalFieldsRamification.herbrand_eq_of_vle_iff`,
  `TauCeti.LocalFieldsRamification.inverseHerbrand_eq_of_vle_iff`,
  `TauCeti.LocalFieldsRamification.comap_algAutCongr_upperRamificationGroup_of_vle_iff`,
  `TauCeti.LocalFieldsRamification.map_algAutCongr_upperRamificationGroup`, and
  `TauCeti.LocalFieldsRamification.map_autCongr_upperRamificationGroup`: invariance of `φ` and `ψ`
  and transport of the upper filtration along valuation-preserving or base-continuous ring
  equivalences and `K`-algebra equivalences.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section
noncomputable section

open MeasureTheory Set intervalIntegral ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]


/-! ### The Herbrand function and its inverse -/

/-- The **Herbrand function** `φ_{L/K}(u) = ∫_0^u dt / [G_0 : G_t]` of a finite Galois extension
of local fields, as an order automorphism of `[-1, ∞)`. Its inverse is the inverse Herbrand function
`ψ_{L/K}`. The integral formula is `coe_herbrand`. The construction does not use `IsGalois`;
the hypothesis restricts the Herbrand function to the Galois case, where it is meaningful. -/
def herbrandOrderIso [_hGal : IsGalois K L] : RamificationIndexDomain ≃o RamificationIndexDomain :=
  TauCeti.IsLocalRing.herbrandOrderIso (L ≃ₐ[K] L) 𝒪[L]

variable [IsGalois K L]

/-- The **Herbrand function** `φ_{L/K}`, the forward map of `herbrandOrderIso K L`. -/
def herbrand (u : RamificationIndexDomain) : RamificationIndexDomain :=
  herbrandOrderIso K L u

/-- The **inverse Herbrand function** `ψ_{L/K}`, the inverse of `herbrandOrderIso K L`. -/
def inverseHerbrand (v : RamificationIndexDomain) : RamificationIndexDomain :=
  (herbrandOrderIso K L).symm v

@[simp]
theorem herbrandOrderIso_apply (u : RamificationIndexDomain) :
    herbrandOrderIso K L u = herbrand K L u :=
  (rfl)

@[simp]
theorem herbrandOrderIso_symm_apply (v : RamificationIndexDomain) :
    (herbrandOrderIso K L).symm v = inverseHerbrand K L v :=
  (rfl)

/-- `herbrand` agrees with `TauCeti.IsLocalRing.herbrandFun` on `𝒪[L]`. -/
theorem coe_herbrand_eq_herbrandFun (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = TauCeti.IsLocalRing.herbrandFun (L ≃ₐ[K] L) 𝒪[L] u :=
  TauCeti.IsLocalRing.coe_herbrandOrderIso_apply (L ≃ₐ[K] L) 𝒪[L] u
/-- `inverseHerbrand` agrees with `TauCeti.IsLocalRing.inverseHerbrandFun` on `𝒪[L]`. -/
theorem coe_inverseHerbrand_eq_inverseHerbrandFun (v : RamificationIndexDomain) :
    (inverseHerbrand K L v : ℝ) = TauCeti.IsLocalRing.inverseHerbrandFun (L ≃ₐ[K] L) 𝒪[L] v :=
  TauCeti.IsLocalRing.coe_herbrandOrderIso_symm_apply (L ≃ₐ[K] L) 𝒪[L] v

/-- The integral formula for the Herbrand function:
`φ_{L/K}(u) = ∫_0^u #G_t / #G_0 dt`. For `t > -1` the group `G_t` is a subgroup of `G_0` and
`#G_t / #G_0 = 1 / [G_0 : G_t]`, so this holds almost everywhere on the interval of integration. -/
theorem coe_herbrand (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = ∫ t in (0 : ℝ)..u,
      (Nat.card (lowerRamificationGroupReal K L t) : ℝ) /
        Nat.card (lowerRamificationGroup K L 0) := by
  simp_rw [coe_herbrand_eq_herbrandFun, lowerRamificationGroupReal_eq_ramificationGroupReal,
    lowerRamificationGroup_def]
  exact TauCeti.IsLocalRing.herbrandFun_def (L ≃ₐ[K] L) 𝒪[L] u

/-- The Herbrand function undoes its inverse: `φ(ψ(v)) = v`. -/
@[simp]
theorem herbrand_inverseHerbrand (v : RamificationIndexDomain) :
    herbrand K L (inverseHerbrand K L v) = v :=
  (herbrandOrderIso K L).apply_symm_apply v

/-- The inverse Herbrand function undoes the Herbrand function: `ψ(φ(u)) = u`. -/
@[simp]
theorem inverseHerbrand_herbrand (u : RamificationIndexDomain) :
    inverseHerbrand K L (herbrand K L u) = u :=
  (herbrandOrderIso K L).symm_apply_apply u

/-- The Herbrand function is strictly increasing. -/
theorem herbrand_strictMono : StrictMono (herbrand K L) :=
  (herbrandOrderIso K L).strictMono

/-- The inverse Herbrand function is strictly increasing. -/
theorem inverseHerbrand_strictMono : StrictMono (inverseHerbrand K L) :=
  (herbrandOrderIso K L).symm.strictMono

/-- The Herbrand function is continuous. -/
@[fun_prop]
theorem continuous_herbrand : Continuous (herbrand K L) :=
  (herbrandOrderIso K L).continuous

/-- The inverse Herbrand function is continuous. -/
@[fun_prop]
theorem continuous_inverseHerbrand : Continuous (inverseHerbrand K L) :=
  (herbrandOrderIso K L).symm.continuous

/-- The Herbrand function is **concave**: its slopes over two adjacent intervals decrease. -/
theorem herbrand_slope_anti_adjacent {u v w : RamificationIndexDomain} (huv : u < v)
    (hvw : v < w) :
    ((herbrand K L w : ℝ) - herbrand K L v) / ((w : ℝ) - v) ≤
      ((herbrand K L v : ℝ) - herbrand K L u) / ((v : ℝ) - u) := by
  simp_rw [coe_herbrand_eq_herbrandFun]
  exact TauCeti.IsLocalRing.herbrandFun_slope_anti_adjacent (L ≃ₐ[K] L) 𝒪[L] huv hvw

/-- The Herbrand function is the identity on `[-1, 0]`. -/
@[simp]
theorem herbrand_of_coe_le_zero {u : RamificationIndexDomain} (hu : (u : ℝ) ≤ 0) :
    herbrand K L u = u :=
  Subtype.ext <| (coe_herbrand_eq_herbrandFun K L u).trans <|
    TauCeti.IsLocalRing.herbrandFun_eq_self_of_neg_one_le_of_nonpos (L ≃ₐ[K] L) 𝒪[L] u.property hu

/-- On an interval `[a, b]` over which the lower ramification filtration is constant, that is
`G_t = G_b` for every `a < t ≤ b`, the Herbrand function is affine of slope `#G_b / #G_0`:
`φ(b) - φ(a) = (b - a) · #G_b / #G_0`. -/
theorem coe_herbrand_sub_coe_herbrand_of_forall_eq {a b : RamificationIndexDomain} (hab : a ≤ b)
    (h : ∀ t : ℝ, (a : ℝ) < t → t ≤ b →
      lowerRamificationGroupReal K L t = lowerRamificationGroupReal K L b) :
    (herbrand K L b : ℝ) - herbrand K L a =
      ((b : ℝ) - a) * (Nat.card (lowerRamificationGroupReal K L b) /
        Nat.card (lowerRamificationGroup K L 0)) := by
  simp_rw [coe_herbrand_eq_herbrandFun, lowerRamificationGroupReal_eq_ramificationGroupReal,
    lowerRamificationGroup_def] at h ⊢
  exact TauCeti.IsLocalRing.herbrandFun_sub_of_forall_eq (L ≃ₐ[K] L) 𝒪[L] hab h

/-- The Herbrand function is the identity as long as the lower ramification filtration is
constant from `0` through `u`. For `u ≤ 0` the hypothesis is vacuous and the conclusion is
`herbrand_of_coe_le_zero`. -/
theorem herbrand_eq_self_of_forall_eq {u : RamificationIndexDomain}
    (h : ∀ t : ℝ, 0 < t → t ≤ u →
      lowerRamificationGroupReal K L t = lowerRamificationGroup K L 0) :
    herbrand K L u = u := by
  by_cases hu : (u : ℝ) ≤ 0
  · exact herbrand_of_coe_le_zero K L hu
  replace hu : 0 ≤ (u : ℝ) := le_of_not_ge hu
  apply Subtype.ext
  rw [coe_herbrand]
  have hcard : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hfun : (∫ t in (0 : ℝ)..u,
      (Nat.card (lowerRamificationGroupReal K L t) : ℝ) /
        Nat.card (lowerRamificationGroup K L 0)) = ∫ _ in (0 : ℝ)..u, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall fun t ht ↦ by
      obtain ⟨ht0, htu⟩ := Set.uIoc_of_le hu ▸ ht
      rw [h t ht0 htu]
      exact div_self hcard
  rw [hfun]
  simp

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
@[simp]
theorem inverseHerbrand_of_coe_le_zero {v : RamificationIndexDomain} (hv : (v : ℝ) ≤ 0) :
    inverseHerbrand K L v = v :=
  (herbrandOrderIso K L).symm_apply_eq.2 (herbrand_of_coe_le_zero K L hv).symm

variable {K L} in
/-- If the inverse Herbrand function sends `u` to `-1`, then `u = -1`. -/
theorem coe_eq_neg_one_of_inverseHerbrand_eq_neg_one {u : RamificationIndexDomain}
    (hinverse : inverseHerbrand K L u = ⟨(-1 : ℝ), le_rfl⟩) : (u : ℝ) = -1 := by
  have hinverse_neg_one :
      inverseHerbrand K L ⟨(-1 : ℝ), le_rfl⟩ = ⟨(-1 : ℝ), le_rfl⟩ :=
    inverseHerbrand_of_coe_le_zero K L (by norm_num)
  have hu_eq : u = ⟨(-1 : ℝ), le_rfl⟩ :=
    (inverseHerbrand_strictMono K L).injective <| hinverse.trans hinverse_neg_one.symm
  exact congrArg Subtype.val hu_eq

/-- The **finite-sum formula** for the Herbrand function: for `m : ℕ` and `m ≤ u ≤ m + 1`,
`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem coe_herbrand_of_mem_Icc (m : ℕ) {u : RamificationIndexDomain} (h₁ : (m : ℝ) ≤ u)
    (h₂ : (u : ℝ) ≤ m + 1) :
    (herbrand K L u : ℝ) =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (lowerRamificationGroup K L i) : ℝ) +
        (u - m) * Nat.card (lowerRamificationGroup K L (m + 1 : ℕ))) /
        Nat.card (lowerRamificationGroup K L 0) := by
  simp_rw [coe_herbrand_eq_herbrandFun, lowerRamificationGroup_def]
  exact TauCeti.IsLocalRing.herbrandFun_of_natCast_le_of_le_add_one (L ≃ₐ[K] L) 𝒪[L] m h₁ h₂

/-- The Herbrand function at a natural number `m`: `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. -/
theorem coe_herbrand_of_coe_eq_natCast (m : ℕ) {u : RamificationIndexDomain} (hu : (u : ℝ) = m) :
    (herbrand K L u : ℝ) =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (lowerRamificationGroup K L i) : ℝ)) /
        Nat.card (lowerRamificationGroup K L 0) := by
  simp_rw [coe_herbrand_eq_herbrandFun, hu, lowerRamificationGroup_def]
  exact TauCeti.IsLocalRing.herbrandFun_natCast (L ≃ₐ[K] L) 𝒪[L] m

/-! ### The upper numbering -/

/-- The **upper-numbering ramification group** `G^v = G_{ψ(v)}` of a finite Galois extension of
local fields, for `v ≥ -1`, where `ψ = inverseHerbrand K L`. -/
def upperRamificationGroup (v : RamificationIndexDomain) : Subgroup (L ≃ₐ[K] L) :=
  lowerRamificationGroupReal K L (inverseHerbrand K L v)

theorem upperRamificationGroup_def (v : RamificationIndexDomain) :
    upperRamificationGroup K L v = lowerRamificationGroupReal K L (inverseHerbrand K L v) :=
  (rfl)

/-- `upperRamificationGroup` agrees with `TauCeti.IsLocalRing.upperRamificationGroup` on `𝒪[L]`. -/
theorem upperRamificationGroup_eq_isLocalRingUpperRamificationGroup (v : RamificationIndexDomain) :
    upperRamificationGroup K L v =
      TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [upperRamificationGroup_def, lowerRamificationGroupReal_eq_ramificationGroupReal,
    coe_inverseHerbrand_eq_inverseHerbrandFun, TauCeti.IsLocalRing.upperRamificationGroup_def]

variable {K L} in
/-- Membership in the upper ramification groups: `σ ∈ G^v ↔ σ ∈ G_{ψ(v)}`. -/
@[simp]
theorem mem_upperRamificationGroup_iff {v : RamificationIndexDomain} {σ : L ≃ₐ[K] L} :
    σ ∈ upperRamificationGroup K L v ↔
      σ ∈ lowerRamificationGroupReal K L (inverseHerbrand K L v) := by
  rw [upperRamificationGroup_def]

/-- The upper and lower numberings are related by `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrand (u : RamificationIndexDomain) :
    upperRamificationGroup K L (herbrand K L u) = lowerRamificationGroupReal K L u := by
  rw [upperRamificationGroup_def, inverseHerbrand_herbrand]

/-- On `[-1, 0]` the upper and lower numberings agree. -/
@[simp]
theorem upperRamificationGroup_of_coe_le_zero {v : RamificationIndexDomain} (hv : (v : ℝ) ≤ 0) :
    upperRamificationGroup K L v = lowerRamificationGroupReal K L v := by
  rw [upperRamificationGroup_def, inverseHerbrand_of_coe_le_zero K L hv]

/-- The upper ramification filtration is decreasing. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup K L) :=
  fun _ _ h ↦ lowerRamificationGroupReal_antitone K L ((inverseHerbrand_strictMono K L).monotone h)

/-- Every upper ramification group is normal in the automorphism group. -/
instance instNormalUpperRamificationGroup (v : RamificationIndexDomain) :
    (upperRamificationGroup K L v).Normal := by
  rw [upperRamificationGroup_def]
  infer_instance

/-! ### Herbrand values at natural numbers

The Herbrand function may take non-integral values at integers, but its inverse does not:
`ψ(n)` is a natural number for every natural number `n`, because `#G_{m+1}` divides `#G_i` for
`i ≤ m + 1`.
This section packages these values as `psiNat K L : ℕ → ℕ`. -/

/-- The **integral inverse Herbrand function** `ψℕ_{L/K} : ℕ → ℕ`: the value `ψ_{L/K}(n)` of the
inverse Herbrand function at a natural number `n`, which is itself a natural number
(`coe_psiNat`). These are the unit depths at which the norm of `L/K` is compared with the unit
filtration of `K`. -/
def psiNat (n : ℕ) : ℕ :=
  ⌊(inverseHerbrand K L ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ : ℝ)⌋₊

/-- `psiNat` agrees with `TauCeti.IsLocalRing.psiNat` on `𝒪[L]`. -/
theorem psiNat_eq_isLocalRingPsiNat (n : ℕ) :
    psiNat K L n = TauCeti.IsLocalRing.psiNat (L ≃ₐ[K] L) 𝒪[L] n := by
  rw [psiNat, coe_inverseHerbrand_eq_inverseHerbrandFun, TauCeti.IsLocalRing.psiNat_def]

/-- The integral inverse Herbrand function computes the inverse Herbrand function:
`ψℕ_{L/K}(n) = ψ_{L/K}(n)`. -/
@[simp]
theorem coe_psiNat (n : ℕ) :
    (psiNat K L n : ℝ) =
      (inverseHerbrand K L
        ⟨(n : ℝ), le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Nat.cast_nonneg n)⟩ : ℝ) := by
  rw [psiNat_eq_isLocalRingPsiNat, coe_inverseHerbrand_eq_inverseHerbrandFun]
  exact TauCeti.IsLocalRing.coe_psiNat (L ≃ₐ[K] L) 𝒪[L] n

/-- `ψℕ_{L/K}(n) = m` exactly when `#G_1 + ⋯ + #G_m = n · #G_0`, that is when `φ_{L/K}(m) = n`. -/
theorem psiNat_eq_iff {n m : ℕ} :
    psiNat K L n = m ↔
      ∑ i ∈ Finset.Icc 1 m, Nat.card (lowerRamificationGroup K L i) =
        n * Nat.card (lowerRamificationGroup K L 0) := by
  simp_rw [psiNat_eq_isLocalRingPsiNat, lowerRamificationGroup_def]
  exact TauCeti.IsLocalRing.psiNat_eq_iff (L ≃ₐ[K] L) 𝒪[L]

/-- `ψℕ_{L/K}(0) = 0`. -/
@[simp]
theorem psiNat_zero : psiNat K L 0 = 0 :=
  (psiNat_eq_iff K L).2 (by simp)

/-- The integral inverse Herbrand function is strictly increasing. -/
theorem psiNat_strictMono : StrictMono (psiNat K L) := fun _ _ h ↦ by
  simp_rw [psiNat_eq_isLocalRingPsiNat]
  exact TauCeti.IsLocalRing.psiNat_strictMono (L ≃ₐ[K] L) 𝒪[L] h

/-- `n ≤ ψℕ_{L/K}(n)`: the inverse Herbrand function never lowers a unit depth. -/
theorem self_le_psiNat (n : ℕ) : n ≤ psiNat K L n := by
  exact (psiNat_strictMono K L).id_le n

/-- `ψℕ_{L/K}(n) ≤ i` exactly when `n ≤ ⌊φ_{L/K}(i)⌋`: on natural numbers the integral inverse
Herbrand function is the lower adjoint of `i ↦ ⌊φ_{L/K}(i)⌋`. In particular
`ψℕ_{L/K}(⌊φ_{L/K}(i)⌋) ≤ i`, which converts the Herbrand-shifted depths `ψℕ_{L/K}(n)` back into
unshifted ones. -/
@[simp]
theorem psiNat_le_iff_le_floor_herbrand {n i : ℕ} :
    psiNat K L n ≤ i ↔
      n ≤ ⌊(herbrand K L ⟨i, Nat.cast_mem_ramificationIndexDomain i⟩ : ℝ)⌋₊ := by
  rw [psiNat_eq_isLocalRingPsiNat, coe_herbrand_eq_herbrandFun,
    Nat.le_floor_iff ((TauCeti.IsLocalRing.herbrandFun_nonneg_iff (L ≃ₐ[K] L) 𝒪[L]).2
      (Nat.cast_nonneg i))]
  exact TauCeti.IsLocalRing.psiNat_le_iff (L ≃ₐ[K] L) 𝒪[L]

/-- `ψℕ_{L/K}(v) = v` exactly when `G_v = G_0`, that is when the lower filtration is constant
through `v`. -/
@[simp]
theorem psiNat_eq_self_iff {v : ℕ} :
    psiNat K L v = v ↔ lowerRamificationGroup K L v = lowerRamificationGroup K L 0 := by
  simp_rw [psiNat_eq_isLocalRingPsiNat, lowerRamificationGroup_def]
  exact TauCeti.IsLocalRing.psiNat_eq_self_iff (L ≃ₐ[K] L) 𝒪[L]

/-- If the lower filtration is constant through `t` and trivial after `t`, that is `G_t = G_0`
and `G_{t+1} = 1`, then `ψℕ_{L/K}(v) = t + #G_0 · (v - t)` for every `v ≥ t`. For a totally
ramified cyclic extension of prime degree `ℓ` with jump `t`, this is
`ψℕ(v) = t + ℓ (v - t)`. -/
theorem psiNat_eq_add_card_mul_sub {t v : ℕ}
    (ht : lowerRamificationGroup K L t = lowerRamificationGroup K L 0)
    (ht' : lowerRamificationGroup K L (t + 1 : ℕ) = ⊥) (hv : t ≤ v) :
    psiNat K L v = t + Nat.card (lowerRamificationGroup K L 0) * (v - t) := by
  set g₀ := Nat.card (lowerRamificationGroup K L 0)
  -- `#G_1 + ⋯ + #G_m = t #G_0 + (m - t)` for `m ≥ t`.
  have hsum : ∀ m, t ≤ m →
      ∑ i ∈ Finset.Icc 1 m, Nat.card (lowerRamificationGroup K L i) = t * g₀ + (m - t) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      rw [(psiNat_eq_iff K L).1 ((psiNat_eq_self_iff K L).2 ht), Nat.sub_self, add_zero]
    | succ m hm ih =>
      have hbot : lowerRamificationGroup K L (m + 1 : ℕ) = ⊥ := le_bot_iff.1 <|
        (lowerRamificationGroup_antitone K L (by push_cast; omega)).trans ht'.le
      rw [Finset.sum_Icc_succ_top (by omega), ih, hbot, Subgroup.card_bot]
      omega
  refine (psiNat_eq_iff K L).2 ((hsum _ (by omega)).trans ?_)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hv
  simp only [Nat.add_sub_cancel_left]
  ring

/-- At a natural number `n`, the upper ramification group is the lower ramification group at the
natural number `ψℕ_{L/K}(n)`: `G^n = G_{ψ(n)}`. -/
@[simp]
theorem upperRamificationGroup_natCast (n : ℕ) :
    upperRamificationGroup K L ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ =
      lowerRamificationGroup K L (psiNat K L n) := by
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast,
    lowerRamificationGroupReal_intCast]

/-- For `v ∈ (φ_{L/K}(i), φ_{L/K}(i + 1)]` (`i : ℕ`), the upper ramification group `G^v` equals
the lower ramification group `G_{i + 1}`. -/
theorem upperRamificationGroup_eq_of_herbrand_lt_of_le {i : ℕ}
    {v : RamificationIndexDomain}
    (hv₁ : herbrand K L ⟨i, Nat.cast_mem_ramificationIndexDomain i⟩ < v)
    (hv₂ : v ≤ herbrand K L ⟨((i + 1 : ℕ) : ℝ),
      Nat.cast_mem_ramificationIndexDomain (i + 1)⟩) :
    upperRamificationGroup K L v = lowerRamificationGroup K L ((i + 1 : ℕ) : ℤ) := by
  have h₁ := inverseHerbrand_strictMono K L hv₁
  have h₂ := (inverseHerbrand_strictMono K L).monotone hv₂
  rw [inverseHerbrand_herbrand] at h₁ h₂
  rw [upperRamificationGroup_def]
  exact lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K L (i := ((i + 1 : ℕ) : ℤ))
    (by have := Subtype.coe_lt_coe.2 h₁; push_cast; linarith)
    (by exact_mod_cast Subtype.coe_le_coe.2 h₂)

/-- The upper ramification filtration of a finite Galois extension of local fields is trivial at
every large enough natural index. -/
theorem exists_forall_upperRamificationGroup_natCast_eq_bot :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      upperRamificationGroup K L ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ = ⊥ := by
  obtain ⟨N, hN⟩ := exists_forall_lowerRamificationGroup_natCast_eq_bot K L
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [upperRamificationGroup_natCast]
  exact hN _ (hn.trans (self_le_psiNat K L n))

/-! ### Transport along ring and algebra equivalences -/

section Transport

section RingEquiv

variable {K L} {K' L' : Type*}
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Field L'] [ValuativeRel L'] [TopologicalSpace L'] [IsNonarchimedeanLocalField L']
  [Algebra K' L'] [ValuativeExtension K' L'] [Module.Finite K' L'] [IsGalois K' L']

/-- **Invariance of the Herbrand function under a valuation-preserving ring isomorphism.** -/
theorem herbrand_eq_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (u : RamificationIndexDomain) :
    herbrand K L u = herbrand K' L' u := by
  have hcard (i : ℤ) :
      Nat.card (lowerRamificationGroup K L i) = Nat.card (lowerRamificationGroup K' L' i) := by
    rw [← map_algAutCongr_lowerRamificationGroup_of_vle_iff e he eL heL i]
    exact Nat.card_congr
      ((e.algAutCongr eL heL).subgroupMap (lowerRamificationGroup K L i)).toEquiv
  apply Subtype.ext
  rw [coe_herbrand, coe_herbrand]
  congr 1 with t
  rw [lowerRamificationGroupReal_def, lowerRamificationGroupReal_def, hcard, hcard]

/-- **Invariance of the inverse Herbrand function under a valuation-preserving ring
isomorphism.** -/
theorem inverseHerbrand_eq_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    inverseHerbrand K L v = inverseHerbrand K' L' v := by
  apply (herbrand_strictMono K' L').injective
  rw [herbrand_inverseHerbrand, ← herbrand_eq_of_vle_iff e he eL heL, herbrand_inverseHerbrand]

/-- **Transport of upper ramification groups along a valuation-preserving ring isomorphism.** -/
theorem comap_algAutCongr_upperRamificationGroup_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    (upperRamificationGroup K' L' v).comap (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      upperRamificationGroup K L v := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    ← inverseHerbrand_eq_of_vle_iff e he eL heL v, lowerRamificationGroupReal_def,
    lowerRamificationGroupReal_def, comap_algAutCongr_lowerRamificationGroup_of_vle_iff e he eL heL]

/-- Image form of `comap_algAutCongr_upperRamificationGroup_of_vle_iff`. -/
theorem map_algAutCongr_upperRamificationGroup_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    (upperRamificationGroup K L v).map (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      upperRamificationGroup K' L' v := by
  rw [← comap_algAutCongr_upperRamificationGroup_of_vle_iff e he eL heL v,
    Subgroup.map_comap_eq_self_of_surjective (e.algAutCongr eL heL).surjective]

/-- **Invariance of the Herbrand function under a base-continuous ring isomorphism.** -/
theorem herbrand_eq_of_ringEquiv (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (u : RamificationIndexDomain) :
    herbrand K L u = herbrand K' L' u :=
  herbrand_eq_of_vle_iff e (e.toRingHom.map_vle_map_iff_of_continuous he) eL heL u

/-- **Invariance of the inverse Herbrand function under a base-continuous ring isomorphism.** -/
theorem inverseHerbrand_eq_of_ringEquiv (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    inverseHerbrand K L v = inverseHerbrand K' L' v :=
  inverseHerbrand_eq_of_vle_iff e (e.toRingHom.map_vle_map_iff_of_continuous he) eL heL v

/-- **Transport of upper ramification groups along a base-continuous ring isomorphism.** -/
theorem comap_algAutCongr_upperRamificationGroup (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    (upperRamificationGroup K' L' v).comap (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      upperRamificationGroup K L v :=
  comap_algAutCongr_upperRamificationGroup_of_vle_iff e
    (e.toRingHom.map_vle_map_iff_of_continuous he) eL heL v

/-- Image form of `comap_algAutCongr_upperRamificationGroup`. -/
theorem map_algAutCongr_upperRamificationGroup (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    (upperRamificationGroup K L v).map (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      upperRamificationGroup K' L' v :=
  map_algAutCongr_upperRamificationGroup_of_vle_iff e
    (e.toRingHom.map_vle_map_iff_of_continuous he) eL heL v

end RingEquiv

section AlgEquiv

variable {K L} {L' : Type*}
  [Field L'] [ValuativeRel L'] [TopologicalSpace L'] [IsNonarchimedeanLocalField L']
  [Algebra K L'] [ValuativeExtension K L'] [Module.Finite K L'] [IsGalois K L']

/-- **Invariance of the Herbrand function along a `K`-algebra isomorphism `φ : L ≃ₐ[K] L'`.** -/
theorem herbrand_eq_of_algEquiv (φ : L ≃ₐ[K] L') (u : RamificationIndexDomain) :
    herbrand K L u = herbrand K L' u :=
  herbrand_eq_of_ringEquiv (RingEquiv.refl K) continuous_id (φ : L ≃+* L') φ.commutes u

/-- **Invariance of the inverse Herbrand function along a `K`-algebra isomorphism
`φ : L ≃ₐ[K] L'`.** -/
theorem inverseHerbrand_eq_of_algEquiv (φ : L ≃ₐ[K] L') (v : RamificationIndexDomain) :
    inverseHerbrand K L v = inverseHerbrand K L' v :=
  inverseHerbrand_eq_of_ringEquiv (RingEquiv.refl K) continuous_id (φ : L ≃+* L') φ.commutes v

/-- **Transport of upper ramification groups along a `K`-algebra isomorphism `φ : L ≃ₐ[K] L'`.** -/
theorem comap_autCongr_upperRamificationGroup (φ : L ≃ₐ[K] L') (v : RamificationIndexDomain) :
    (upperRamificationGroup K L' v).comap (AlgEquiv.autCongr φ : (L ≃ₐ[K] L) →* (L' ≃ₐ[K] L')) =
      upperRamificationGroup K L v := by
  rw [← RingEquiv.algAutCongr_refl_toRingEquiv φ φ.commutes]
  exact comap_algAutCongr_upperRamificationGroup (RingEquiv.refl K) continuous_id
    (φ : L ≃+* L') φ.commutes v

/-- Image form of `comap_autCongr_upperRamificationGroup`. -/
theorem map_autCongr_upperRamificationGroup (φ : L ≃ₐ[K] L') (v : RamificationIndexDomain) :
    (upperRamificationGroup K L v).map (AlgEquiv.autCongr φ : (L ≃ₐ[K] L) →* (L' ≃ₐ[K] L')) =
      upperRamificationGroup K L' v := by
  rw [← comap_autCongr_upperRamificationGroup φ v,
    Subgroup.map_comap_eq_self_of_surjective (AlgEquiv.autCongr φ).surjective]

end AlgEquiv

end Transport

section IntegralClosure

open TauCeti.IsLocalRing in
/-- For a tower `K₀ ⊆ K ⊆ L` of nonarchimedean local fields, `herbrand K L` agrees with
`TauCeti.IsLocalRing.herbrandFun` on `integralClosure 𝒪[K₀] L`. -/
theorem coe_herbrand_eq_herbrandFun_integralClosure (K₀ K L : Type*)
    [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀] [IsNonarchimedeanLocalField K₀]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K₀ K] [Algebra K L] [Algebra K₀ L] [ValuativeExtension K₀ L] [ValuativeExtension K L]
    [Module.Finite K L] [IsGalois K L] [Algebra.IsAlgebraic K₀ L]
    [IsScalarTower 𝒪[K₀] K L] [IsLocalRing (integralClosure 𝒪[K₀] L)]
    (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = herbrandFun (L ≃ₐ[K] L) (integralClosure 𝒪[K₀] L) u := by
  rw [coe_herbrand_eq_herbrandFun]
  exact herbrandFun_eq_of_ramificationGroup_eq_comap (φ := MonoidHom.id (L ≃ₐ[K] L))
    Function.bijective_id (fun i ↦ by simpa only [Subgroup.comap_id] using
      ramificationGroup_integerRing_eq_integralClosure K₀ K L i) u

open TauCeti.IsLocalRing in
/-- For a tower `K₀ ⊆ K ⊆ L` of nonarchimedean local fields, `inverseHerbrand K L` agrees with
`TauCeti.IsLocalRing.inverseHerbrandFun` on `integralClosure 𝒪[K₀] L`. -/
theorem coe_inverseHerbrand_eq_inverseHerbrandFun_integralClosure (K₀ K L : Type*)
    [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀] [IsNonarchimedeanLocalField K₀]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K₀ K] [Algebra K L] [Algebra K₀ L] [ValuativeExtension K₀ L] [ValuativeExtension K L]
    [Module.Finite K L] [IsGalois K L] [Algebra.IsAlgebraic K₀ L]
    [IsScalarTower 𝒪[K₀] K L] [IsLocalRing (integralClosure 𝒪[K₀] L)]
    (v : RamificationIndexDomain) :
    (inverseHerbrand K L v : ℝ) =
      inverseHerbrandFun (L ≃ₐ[K] L) (integralClosure 𝒪[K₀] L) v := by
  rw [coe_inverseHerbrand_eq_inverseHerbrandFun]
  exact inverseHerbrandFun_eq_of_ramificationGroup_eq_comap (φ := MonoidHom.id (L ≃ₐ[K] L))
    Function.bijective_id (fun i ↦ by simpa only [Subgroup.comap_id] using
      ramificationGroup_integerRing_eq_integralClosure K₀ K L i) v

open TauCeti.IsLocalRing in
/-- For a tower `K₀ ⊆ K ⊆ L` of nonarchimedean local fields, `upperRamificationGroup K L` agrees
with `TauCeti.IsLocalRing.upperRamificationGroup` on `integralClosure 𝒪[K₀] L`. -/
theorem upperRamificationGroup_eq_isLocalRingUpperRamificationGroup_integralClosure (K₀ K L : Type*)
    [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀] [IsNonarchimedeanLocalField K₀]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K₀ K] [Algebra K L] [Algebra K₀ L] [ValuativeExtension K₀ L] [ValuativeExtension K L]
    [Module.Finite K L] [IsGalois K L] [Algebra.IsAlgebraic K₀ L]
    [IsScalarTower 𝒪[K₀] K L] [IsLocalRing (integralClosure 𝒪[K₀] L)]
    (v : RamificationIndexDomain) :
    upperRamificationGroup K L v =
      TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) (integralClosure 𝒪[K₀] L) v := by
  rw [upperRamificationGroup_eq_isLocalRingUpperRamificationGroup]
  simpa only [Subgroup.comap_id] using
    upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap
      (φ := MonoidHom.id (L ≃ₐ[K] L)) Function.bijective_id
      (fun i ↦ by simpa only [Subgroup.comap_id] using
        ramificationGroup_integerRing_eq_integralClosure K₀ K L i) v

end IntegralClosure

end TauCeti.LocalFieldsRamification
