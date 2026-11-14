/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Wohlfahrt
import TauCeti.Data.Int.CongrAllPrimes
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# The congruence closure of a subgroup of `SL₂(ℤ)`

The **congruence closure** `Γ.congruenceClosure` of `Γ ≤ SL(2, ℤ)` is the intersection of all
congruence subgroups of `SL(2, ℤ)` containing `Γ`. It forms a Moore closure operator on
`Subgroup SL(2, ℤ)` commuting with conjugation and with adjoining `-I` (`Subgroup.withCenter`).

When `Γ` has nonzero strict level — in particular, whenever `Γ` has finite index — the strict form
of Wohlfahrt's theorem identifies this intersection in finite terms: every congruence subgroup
containing `Γ` has strict level dividing `Γ.strictLevel` and therefore contains
`Γ(Γ.strictLevel)`, while `Γ ⊔ Γ(Γ.strictLevel)` is itself a congruence subgroup containing `Γ`.
Thus `Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)` (`Subgroup.congruenceClosure_eq_sup_Gamma`),
it is the preimage in `SL(2, ℤ)` of the image of `Γ` in `SL(2, ZMod N)` at `N = Γ.strictLevel`
and at every nonzero multiple of `Γ.strictLevel`
(`Subgroup.congruenceClosure_eq_comap_map_intCast_zmod`,
`Subgroup.congruenceClosure_eq_comap_map_intCast_zmod_of_dvd`), and `Γ` is a congruence subgroup
if and only if `Γ.congruenceClosure = Γ` (`Subgroup.congruenceClosure_eq_self_iff`).

Two extreme cases occur among noncongruence subgroups:
* `Γ.congruenceClosure = ⊤` holds if and only if `Γ` surjects onto `SL(2, ZMod N)` for any nonzero
  multiple `N` of `Γ.strictLevel` (`Subgroup.congruenceClosure_eq_top_iff_of_dvd`,
  `Subgroup.congruenceClosure_eq_top_iff`), in which case `Γ` surjects onto `SL(2, ZMod N)` at
  every nonzero modulus `N` (`Subgroup.map_map_intCast_zmod_eq_top_of_congruenceClosure_eq_top`);
* if `Γ·{±I}` is a congruence subgroup while `Γ` itself is not (a noncongruence lift of a
  projective congruence group), then `Γ.congruenceClosure = Γ·{±I}`
  (`Subgroup.congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup`).

## Main definitions and results

* `Subgroup.congruenceClosure`: the intersection of all congruence subgroups containing `Γ`.
* `Subgroup.le_congruenceClosure`, `Subgroup.congruenceClosure_le`,
  `Subgroup.congruenceClosure_le_iff`, `Subgroup.congruenceClosure_mono`,
  `Subgroup.congruenceClosure_congruenceClosure`, `Subgroup.le_congruenceClosure_iff`: Moore
  closure properties on `Subgroup SL(2, ℤ)`.
* `Subgroup.pointwise_smul_congruenceClosure`, `Subgroup.instNormalCongruenceClosure`,
  `Subgroup.congruenceClosure_withCenter`: compatibility with conjugation, normality, and
  adjoining `{±I}`.
* `Subgroup.congruenceClosure_eq_sup_Gamma_of_dvd`, `Subgroup.congruenceClosure_eq_sup_Gamma`:
  `Γ.congruenceClosure = Γ ⊔ Γ(N)` for every nonzero multiple `N` of `Γ.strictLevel`, and in
  particular `Γ ⊔ Γ(Γ.strictLevel)` when `[NeZero Γ.strictLevel]`.
* `Subgroup.isCongruenceSubgroup_congruenceClosure`, `Subgroup.instFiniteIndexCongruenceClosure`,
  `Subgroup.congruenceClosure_eq_self_iff`: for `[NeZero Γ.strictLevel]`, the congruence closure is
  a congruence subgroup (hence of finite index), and equals `Γ` iff `Γ` is congruence.
* `Subgroup.map_map_intCast_zmod_congruenceClosure`,
  `Subgroup.congruenceClosure_eq_comap_map_intCast_zmod_of_dvd`,
  `Subgroup.congruenceClosure_eq_comap_map_intCast_zmod`: `Γ` and `Γ.congruenceClosure` have
  identical images in `SL(2, ZMod N)` for every nonzero `N`, and the closure is the preimage of
  that image whenever `Γ.strictLevel ∣ N`.
* `Subgroup.map_map_intCast_zmod_eq_top_of_congruenceClosure_eq_top`,
  `Subgroup.congruenceClosure_eq_top_iff_of_dvd`, `Subgroup.congruenceClosure_eq_top_iff`,
  `Subgroup.congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup`,
  `Subgroup.congruenceClosure_eq_self_or_withCenter`: characterizations of full congruence closure
  and of congruence closures of lifts of projective congruence groups.
* `Subgroup.congruenceClosure_bot`, `Subgroup.congruenceClosure_eq_bot_iff`,
  `CongruenceSubgroup.congruenceClosure_Gamma`, `CongruenceSubgroup.congruenceClosure_Gamma0`,
  `CongruenceSubgroup.congruenceClosure_Gamma1`,
  `Subgroup.congruenceClosure_normalClosure_T_pow`: evaluations on `⊥`, `Γ(N)`, `Γ₀(N)`, `Γ₁(N)`
  and `normalClosure {T ^ N}` at every `N : ℕ` (`0` included).

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
* I. Kiming, M. Schütt and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. 83 (2011), 96–120, §3.
* G. Berger, *Hecke operators on noncongruence subgroups*, C. R. Acad. Sci. Paris Sér. I 319
  (1994), 915–919.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups Pointwise

namespace Subgroup

/-- The **congruence closure** of `Γ ≤ SL(2, ℤ)`: the intersection of all congruence subgroups of
`SL(2, ℤ)` containing `Γ`. -/
def congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  ⨅ (Δ : Subgroup SL(2, ℤ)) (_ : IsCongruenceSubgroup Δ) (_ : Γ ≤ Δ), Δ

/-- Unfolding lemma for `Subgroup.congruenceClosure`. -/
theorem congruenceClosure_def (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure =
      ⨅ (Δ : Subgroup SL(2, ℤ)) (_ : IsCongruenceSubgroup Δ) (_ : Γ ≤ Δ), Δ := (rfl)

/-- An element of `SL(2, ℤ)` belongs to `Γ.congruenceClosure` if and only if it belongs to every
congruence subgroup containing `Γ`. -/
theorem mem_congruenceClosure_iff {Γ : Subgroup SL(2, ℤ)} {γ : SL(2, ℤ)} :
    γ ∈ Γ.congruenceClosure ↔
      ∀ Δ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Δ → Γ ≤ Δ → γ ∈ Δ := by
  simp [congruenceClosure_def]

/-- Every subgroup of `SL(2, ℤ)` is contained in its congruence closure. -/
theorem le_congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Γ ≤ Γ.congruenceClosure :=
  fun _ hγ ↦ mem_congruenceClosure_iff.mpr fun _ _ hle ↦ hle hγ

/-- The congruence closure of `Γ` is contained in every congruence subgroup containing `Γ`. -/
theorem congruenceClosure_le {Γ Δ : Subgroup SL(2, ℤ)} (hΔ : IsCongruenceSubgroup Δ)
    (hle : Γ ≤ Δ) : Γ.congruenceClosure ≤ Δ :=
  fun _ hγ ↦ mem_congruenceClosure_iff.mp hγ Δ hΔ hle

/-- For a congruence subgroup `Δ`, `Γ.congruenceClosure ≤ Δ` holds if and only if `Γ ≤ Δ`. -/
theorem congruenceClosure_le_iff {Γ Δ : Subgroup SL(2, ℤ)} (hΔ : IsCongruenceSubgroup Δ) :
    Γ.congruenceClosure ≤ Δ ↔ Γ ≤ Δ :=
  ⟨Γ.le_congruenceClosure.trans, congruenceClosure_le hΔ⟩

/-- A congruence subgroup equals its own congruence closure. -/
theorem _root_.CongruenceSubgroup.IsCongruenceSubgroup.congruenceClosure_eq
    {Γ : Subgroup SL(2, ℤ)} (hΓ : IsCongruenceSubgroup Γ) : Γ.congruenceClosure = Γ :=
  le_antisymm (congruenceClosure_le hΓ le_rfl) Γ.le_congruenceClosure

/-- `Subgroup.congruenceClosure` is monotone. -/
@[gcongr]
theorem congruenceClosure_mono {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} (h : Γ₁ ≤ Γ₂) :
    Γ₁.congruenceClosure ≤ Γ₂.congruenceClosure :=
  fun _ hγ ↦ mem_congruenceClosure_iff.mpr fun Δ hΔ hle ↦
    mem_congruenceClosure_iff.mp hγ Δ hΔ (h.trans hle)

/-- Taking the congruence closure is idempotent, unconditionally on `Γ`. -/
@[simp]
theorem congruenceClosure_congruenceClosure (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.congruenceClosure = Γ.congruenceClosure := by
  refine le_antisymm (fun _ h ↦ ?_) Γ.congruenceClosure.le_congruenceClosure
  exact mem_congruenceClosure_iff.mpr fun Δ hΔ hle ↦
    mem_congruenceClosure_iff.mp h Δ hΔ (congruenceClosure_le hΔ hle)

/-- A subgroup lies in the congruence closure of another if and only if its congruence closure
does. -/
theorem le_congruenceClosure_iff {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} :
    Γ₁ ≤ Γ₂.congruenceClosure ↔ Γ₁.congruenceClosure ≤ Γ₂.congruenceClosure :=
  ⟨fun h ↦ congruenceClosure_congruenceClosure Γ₂ ▸ congruenceClosure_mono h,
    Γ₁.le_congruenceClosure.trans⟩

/-- The congruence closure of an intersection lies in the intersection of the congruence
closures. -/
theorem congruenceClosure_inf_le (Γ₁ Γ₂ : Subgroup SL(2, ℤ)) :
    (Γ₁ ⊓ Γ₂).congruenceClosure ≤ Γ₁.congruenceClosure ⊓ Γ₂.congruenceClosure :=
  le_inf (congruenceClosure_mono inf_le_left) (congruenceClosure_mono inf_le_right)

/-- The strict level of `Γ.congruenceClosure` divides the strict level of `Γ`. -/
theorem strictLevel_congruenceClosure_dvd (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.strictLevel ∣ Γ.strictLevel :=
  strictLevel_dvd_of_le Γ.le_congruenceClosure

/-! ### Conjugation, normality, and adjoining `{±I}` -/

private lemma pointwise_smul_congruenceClosure_le (g : ConjAct SL(2, ℤ))
    (Γ : Subgroup SL(2, ℤ)) : g • Γ.congruenceClosure ≤ (g • Γ).congruenceClosure := by
  rw [congruenceClosure_def]
  exact le_iInf fun Δ ↦ le_iInf₂ fun hΔ hle ↦
    pointwise_smul_subset_iff.mpr
      (congruenceClosure_le (conj_cong_is_cong g⁻¹ Δ hΔ) (pointwise_smul_subset_iff.mp hle))

/-- Conjugation in `SL(2, ℤ)` commutes with `Subgroup.congruenceClosure`. -/
theorem pointwise_smul_congruenceClosure (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ)) :
    g • Γ.congruenceClosure = (g • Γ).congruenceClosure := by
  refine le_antisymm (pointwise_smul_congruenceClosure_le g Γ) ?_
  simpa using (pointwise_smul_le_pointwise_smul_iff (a := g)).mpr
    (pointwise_smul_congruenceClosure_le g⁻¹ (g • Γ))

/-- The congruence closure of a normal subgroup of `SL(2, ℤ)` is normal. -/
instance instNormalCongruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.Normal] :
    Γ.congruenceClosure.Normal where
  conj_mem γ hγ g := by
    have hact : ConjAct.toConjAct g • Γ.congruenceClosure = Γ.congruenceClosure := by
      rw [pointwise_smul_congruenceClosure, Normal.conjAct ‹Γ.Normal›]
    rw [← hact]
    exact smul_mem_pointwise_smul γ (ConjAct.toConjAct g) _ hγ

private lemma mem_congruenceClosure_of_mem_withCenter_of_mem
    {Γ Δ₀ : Subgroup SL(2, ℤ)} (hΔ₀ : IsCongruenceSubgroup Δ₀) (hle₀ : Γ ≤ Δ₀)
    (hneg₀ : (-1 : SL(2, ℤ)) ∉ Δ₀) {x : SL(2, ℤ)}
    (hx : x ∈ Γ.withCenter.congruenceClosure) (hx₀ : x ∈ Δ₀) :
    x ∈ Γ.congruenceClosure := by
  refine mem_congruenceClosure_iff.mpr fun Δ hΔ hle ↦ ?_
  have hwc : Γ.withCenter ≤ (Δ ⊓ Δ₀).withCenter :=
    withCenter_le_iff.mpr ⟨(le_inf hle hle₀).trans (Δ ⊓ Δ₀).le_withCenter, center_le_withCenter _⟩
  obtain ⟨y, hy, rfl | hxy⟩ := mem_withCenter_iff_exists_eq_or_eq_neg.mp
    (mem_congruenceClosure_iff.mp hx _ (hΔ.inf hΔ₀).withCenter hwc)
  · exact hy.1
  · exact absurd (by simpa [hxy] using mul_mem hx₀ (inv_mem hy.2)) hneg₀

/-- Adjoining `{±I}` commutes with `Subgroup.congruenceClosure`, unconditionally on `Γ`. -/
@[simp]
theorem congruenceClosure_withCenter (Γ : Subgroup SL(2, ℤ)) :
    Γ.withCenter.congruenceClosure = Γ.congruenceClosure.withCenter := by
  refine le_antisymm (fun γ hγ ↦ ?_)
    (withCenter_le_iff.mpr
      ⟨congruenceClosure_mono Γ.le_withCenter,
        Γ.center_le_withCenter.trans Γ.withCenter.le_congruenceClosure⟩)
  by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ.congruenceClosure
  · refine Γ.congruenceClosure.le_withCenter (mem_congruenceClosure_iff.mpr fun Δ hΔ hle ↦ ?_)
    refine mem_congruenceClosure_iff.mp hγ Δ hΔ (withCenter_le_iff.mpr ⟨hle, fun z hz ↦ ?_⟩)
    rcases mem_center_iff_eq_one_or_eq_neg_one.mp hz with rfl | rfl
    · exact one_mem Δ
    · exact mem_congruenceClosure_iff.mp hneg Δ hΔ hle
  · rw [mem_congruenceClosure_iff] at hneg
    push Not at hneg
    obtain ⟨Δ₀, hΔ₀, hle₀, hneg₀⟩ := hneg
    have hwc₀ : Γ.withCenter ≤ Δ₀.withCenter :=
      withCenter_le_iff.mpr ⟨hle₀.trans Δ₀.le_withCenter, Δ₀.center_le_withCenter⟩
    obtain ⟨δ, hδ, rfl | rfl⟩ := mem_withCenter_iff_exists_eq_or_eq_neg.mp
      (mem_congruenceClosure_iff.mp hγ _ hΔ₀.withCenter hwc₀)
    · exact Γ.congruenceClosure.le_withCenter
        (mem_congruenceClosure_of_mem_withCenter_of_mem hΔ₀ hle₀ hneg₀ hγ hδ)
    · have hneg_mem : (-1 : SL(2, ℤ)) ∈ Γ.withCenter.congruenceClosure :=
        Γ.withCenter.le_congruenceClosure (Γ.center_le_withCenter
          (mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)))
      have hδ' : δ ∈ Γ.withCenter.congruenceClosure := by simpa using mul_mem hneg_mem hγ
      exact mem_withCenter_iff_exists_eq_or_eq_neg.mpr
        ⟨δ, mem_congruenceClosure_of_mem_withCenter_of_mem hΔ₀ hle₀ hneg₀ hδ' hδ, Or.inr rfl⟩

/-! ### Explicit Wohlfahrt description of the congruence closure -/

/-- **Explicit formula for the congruence closure**: for every nonzero multiple `N` of
`Γ.strictLevel`, `Γ.congruenceClosure` equals `Γ ⊔ Γ(N)`. -/
theorem congruenceClosure_eq_sup_Gamma_of_dvd {Γ : Subgroup SL(2, ℤ)} {N : ℕ} [NeZero N]
    (hdvd : Γ.strictLevel ∣ N) : Γ.congruenceClosure = Γ ⊔ Gamma N := by
  refine le_antisymm
    (congruenceClosure_le
      (isCongruenceSubgroup_trans _ _ le_sup_right (Gamma_is_cong_sub N)) le_sup_left)
    (sup_le Γ.le_congruenceClosure fun γ hγ ↦ mem_congruenceClosure_iff.mpr fun Δ hΔ hle ↦ ?_)
  exact hΔ.Gamma_strictLevel_le
    (Gamma_le_Gamma_of_dvd ((strictLevel_dvd_of_le hle).trans hdvd) hγ)

/-- When `Γ` has nonzero strict level (in particular, when `Γ` has finite index), its congruence
closure is `Γ ⊔ Γ(Γ.strictLevel)`. -/
theorem congruenceClosure_eq_sup_Gamma (Γ : Subgroup SL(2, ℤ)) [NeZero Γ.strictLevel] :
    Γ.congruenceClosure = Γ ⊔ Gamma Γ.strictLevel :=
  congruenceClosure_eq_sup_Gamma_of_dvd dvd_rfl

/-- When `Γ` has nonzero strict level (in particular, when `Γ` has finite index),
`Γ.congruenceClosure` is a congruence subgroup. -/
@[simp]
theorem isCongruenceSubgroup_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [NeZero Γ.strictLevel] :
    IsCongruenceSubgroup Γ.congruenceClosure := by
  rw [congruenceClosure_eq_sup_Gamma]
  exact isCongruenceSubgroup_trans _ _ le_sup_right (Gamma_is_cong_sub Γ.strictLevel)

/-- When `Γ` has nonzero strict level, `Γ.congruenceClosure` has finite index in `SL(2, ℤ)`. -/
instance instFiniteIndexCongruenceClosure (Γ : Subgroup SL(2, ℤ)) [NeZero Γ.strictLevel] :
    Γ.congruenceClosure.FiniteIndex :=
  (isCongruenceSubgroup_congruenceClosure Γ).finiteIndex

/-- For `Γ` of nonzero strict level (in particular, of finite index), `Γ` equals its congruence
closure if and only if `Γ` is a congruence subgroup. The hypothesis `[NeZero Γ.strictLevel]` is
genuine: `⊥`, `Γ₀(0)` and `Γ₁(0)` equal their congruence closures while having strict level `0`
and infinite index. -/
theorem congruenceClosure_eq_self_iff (Γ : Subgroup SL(2, ℤ)) [NeZero Γ.strictLevel] :
    Γ.congruenceClosure = Γ ↔ IsCongruenceSubgroup Γ :=
  ⟨fun h ↦ h ▸ isCongruenceSubgroup_congruenceClosure Γ, IsCongruenceSubgroup.congruenceClosure_eq⟩

/-- When `Γ₁` has nonzero strict level, `Subgroup.congruenceClosure` distributes over binary
suprema. -/
theorem congruenceClosure_sup (Γ₁ Γ₂ : Subgroup SL(2, ℤ)) [NeZero Γ₁.strictLevel] :
    (Γ₁ ⊔ Γ₂).congruenceClosure = Γ₁.congruenceClosure ⊔ Γ₂.congruenceClosure :=
  le_antisymm
    (congruenceClosure_le
      (isCongruenceSubgroup_trans _ _ le_sup_left (isCongruenceSubgroup_congruenceClosure Γ₁))
      (sup_le_sup Γ₁.le_congruenceClosure Γ₂.le_congruenceClosure))
    (sup_le (congruenceClosure_mono le_sup_left) (congruenceClosure_mono le_sup_right))

/-! ### Reduction modulo `N` -/

/-- Any subgroup `Γ ≤ SL(2, ℤ)` and its congruence closure have the exact same image in
`SL(2, ZMod N)` for every nonzero modulus `N`. -/
@[simp]
theorem map_map_intCast_zmod_congruenceClosure (Γ : Subgroup SL(2, ℤ)) (N : ℕ) [NeZero N] :
    Γ.congruenceClosure.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) =
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) := by
  refine le_antisymm (map_le_iff_le_comap.mpr ?_) (map_mono Γ.le_congruenceClosure)
  rw [comap_map_eq, ker_map_intCast_zmod]
  exact congruenceClosure_le
    (isCongruenceSubgroup_trans _ _ le_sup_right (Gamma_is_cong_sub N)) le_sup_left

/-- For every nonzero multiple `N` of `Γ.strictLevel`, `Γ.congruenceClosure` is the preimage in
`SL(2, ℤ)` of the image of `Γ` in `SL(2, ZMod N)`. -/
theorem congruenceClosure_eq_comap_map_intCast_zmod_of_dvd {Γ : Subgroup SL(2, ℤ)} {N : ℕ}
    [NeZero N] (hdvd : Γ.strictLevel ∣ N) :
    Γ.congruenceClosure =
      (Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)))).comap
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) := by
  rw [comap_map_eq, ker_map_intCast_zmod, congruenceClosure_eq_sup_Gamma_of_dvd hdvd]

/-- When `Γ` has nonzero strict level, `Γ.congruenceClosure` is the preimage in `SL(2, ℤ)` of the
image of `Γ` in `SL(2, ZMod Γ.strictLevel)`. -/
theorem congruenceClosure_eq_comap_map_intCast_zmod (Γ : Subgroup SL(2, ℤ))
    [NeZero Γ.strictLevel] :
    Γ.congruenceClosure =
      (Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel)))).comap
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) :=
  congruenceClosure_eq_comap_map_intCast_zmod_of_dvd dvd_rfl

/-! ### Extreme behaviours: full congruence closure and noncongruence lifts -/

/-- If `Γ.congruenceClosure = ⊤`, then `Γ` surjects onto `SL(2, ZMod N)` at every nonzero modulus
`N`. -/
theorem map_map_intCast_zmod_eq_top_of_congruenceClosure_eq_top {Γ : Subgroup SL(2, ℤ)}
    (h : Γ.congruenceClosure = ⊤) (N : ℕ) [NeZero N] :
    Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) = ⊤ := by
  rw [← map_map_intCast_zmod_congruenceClosure, h]
  exact map_top_of_surjective _ map_intCast_zmod_surjective

/-- For every nonzero multiple `N` of `Γ.strictLevel`, `Γ.congruenceClosure = ⊤` holds if and only
if `Γ` surjects onto `SL(2, ZMod N)`. -/
theorem congruenceClosure_eq_top_iff_of_dvd {Γ : Subgroup SL(2, ℤ)} {N : ℕ} [NeZero N]
    (hdvd : Γ.strictLevel ∣ N) :
    Γ.congruenceClosure = ⊤ ↔
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) = ⊤ :=
  ⟨fun h ↦ map_map_intCast_zmod_eq_top_of_congruenceClosure_eq_top h N, fun h ↦ by
    rw [congruenceClosure_eq_comap_map_intCast_zmod_of_dvd hdvd, h, comap_top]⟩

/-- When `Γ` has nonzero strict level, its congruence closure is all of `SL(2, ℤ)` if and only if
`Γ` surjects onto `SL(2, ZMod Γ.strictLevel)`. -/
theorem congruenceClosure_eq_top_iff (Γ : Subgroup SL(2, ℤ)) [NeZero Γ.strictLevel] :
    Γ.congruenceClosure = ⊤ ↔
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) = ⊤ :=
  congruenceClosure_eq_top_iff_of_dvd dvd_rfl

/-- **Congruence closure of a noncongruence lift**: if `Γ·{±I}` is a congruence subgroup while `Γ`
itself is not, then `Γ.congruenceClosure = Γ·{±I}`. -/
theorem congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup {Γ : Subgroup SL(2, ℤ)}
    (hwith : IsCongruenceSubgroup Γ.withCenter) (hnot : ¬ IsCongruenceSubgroup Γ) :
    Γ.congruenceClosure = Γ.withCenter := by
  have : NeZero Γ.strictLevel :=
    ⟨ne_zero_of_dvd_ne_zero (mul_ne_zero two_ne_zero hwith.strictLevel_ne_zero)
      Γ.strictLevel_dvd_two_mul_strictLevel_withCenter⟩
  have hle : Γ.congruenceClosure ≤ Γ.withCenter := congruenceClosure_le hwith Γ.le_withCenter
  refine le_antisymm hle (withCenter_le_iff.mpr ⟨Γ.le_congruenceClosure, fun z hz ↦ ?_⟩)
  rcases mem_center_iff_eq_one_or_eq_neg_one.mp hz with rfl | rfl
  · exact one_mem _
  · by_contra hneg
    have heq : Γ.congruenceClosure = Γ := by
      have hinf := inf_withCenter_eq_of_le Γ.le_congruenceClosure fun h ↦ absurd h hneg
      rwa [inf_eq_left.mpr hle] at hinf
    exact hnot (heq ▸ isCongruenceSubgroup_congruenceClosure Γ)

/-- Any lift `Γ` of a projective congruence group (that is, `IsCongruenceSubgroup Γ.withCenter`)
has congruence closure equal either to `Γ` (when `Γ` is congruence) or to `Γ·{±I}` (when `Γ` is
noncongruence). -/
theorem congruenceClosure_eq_self_or_withCenter {Γ : Subgroup SL(2, ℤ)}
    (hwith : IsCongruenceSubgroup Γ.withCenter) :
    Γ.congruenceClosure = Γ ∨ Γ.congruenceClosure = Γ.withCenter := by
  by_cases h : IsCongruenceSubgroup Γ
  · exact Or.inl h.congruenceClosure_eq
  · exact Or.inr (congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup hwith h)

/-! ### Evaluations on standard subgroups -/

/-- The congruence closure of `SL(2, ℤ)` is `SL(2, ℤ)`. -/
@[simp]
theorem congruenceClosure_top : (⊤ : Subgroup SL(2, ℤ)).congruenceClosure = ⊤ :=
  top_unique (le_congruenceClosure ⊤)

/-- The congruence closure of the trivial subgroup is trivial, because `SL(2, ℤ)` is residually
finite with respect to principal congruence subgroups
(`CongruenceSubgroup.iInf_Gamma_ne_zero_eq_bot`). -/
@[simp]
theorem congruenceClosure_bot : (⊥ : Subgroup SL(2, ℤ)).congruenceClosure = ⊥ := by
  have hle : (⊥ : Subgroup SL(2, ℤ)).congruenceClosure ≤ ⨅ (N : ℕ) (_ : N ≠ 0), Gamma N :=
    le_iInf₂ fun N hN ↦
      have : NeZero N := ⟨hN⟩
      congruenceClosure_le (Gamma_is_cong_sub N) bot_le
  rwa [CongruenceSubgroup.iInf_Gamma_ne_zero_eq_bot, le_bot_iff] at hle

/-- The congruence closure of `Γ` is trivial if and only if `Γ` is trivial. -/
@[simp]
theorem congruenceClosure_eq_bot_iff {Γ : Subgroup SL(2, ℤ)} :
    Γ.congruenceClosure = ⊥ ↔ Γ = ⊥ :=
  ⟨fun h ↦ le_bot_iff.mp (h ▸ Γ.le_congruenceClosure), fun h ↦ h ▸ congruenceClosure_bot⟩

/-- The congruence closure of the normal closure of `T ^ N` in `SL(2, ℤ)` is `Γ(N)`, at every
`N : ℕ` (`0` included). -/
@[simp]
theorem congruenceClosure_normalClosure_T_pow (N : ℕ) :
    (normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ))).congruenceClosure = Gamma N := by
  rcases eq_or_ne N 0 with rfl | hN
  · have hbot : normalClosure ({ModularGroup.T ^ 0} : Set SL(2, ℤ)) = ⊥ :=
      le_bot_iff.mp (normalClosure_le_normal (by simp))
    rw [hbot, congruenceClosure_bot, Gamma_zero_bot]
  · have : NeZero (normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ))).strictLevel := by
      rw [strictLevel_normalClosure_T_pow]
      exact ⟨hN⟩
    rw [congruenceClosure_eq_sup_Gamma, strictLevel_normalClosure_T_pow]
    exact sup_eq_right.mpr (normalClosure_T_pow_le_Gamma N)

end Subgroup

namespace CongruenceSubgroup

/-- Unconditional congruence test via `Subgroup.congruenceClosure`: `Γ` is a congruence subgroup if
and only if it has nonzero strict level and equals its congruence closure. -/
theorem isCongruenceSubgroup_iff_strictLevel_ne_zero_and_congruenceClosure_eq
    {Γ : Subgroup SL(2, ℤ)} :
    IsCongruenceSubgroup Γ ↔ Γ.strictLevel ≠ 0 ∧ Γ.congruenceClosure = Γ :=
  ⟨fun h ↦ ⟨h.strictLevel_ne_zero, h.congruenceClosure_eq⟩,
    fun ⟨hne, heq⟩ ↦ have : NeZero Γ.strictLevel := ⟨hne⟩;
      (Subgroup.congruenceClosure_eq_self_iff Γ).mp heq⟩

/-- `Γ(N)` equals its congruence closure at every `N : ℕ` (`0` included). -/
@[simp]
theorem congruenceClosure_Gamma (N : ℕ) : (Gamma N).congruenceClosure = Gamma N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [Gamma_zero_bot]
  · have : NeZero N := ⟨hN⟩
    exact (Gamma_is_cong_sub N).congruenceClosure_eq

/-- `Γ₀(N)` equals its congruence closure at every `N : ℕ` (`0` included). -/
@[simp]
theorem congruenceClosure_Gamma0 (N : ℕ) : (Gamma0 N).congruenceClosure = Gamma0 N := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine le_antisymm (fun γ hγ ↦ mem_Gamma0_iff_dvd.mpr ?_) (Gamma0 0).le_congruenceClosure
    have h0 : γ 1 0 = 0 :=
      Int.eq_zero_of_eventually_prime_dvd (Filter.Eventually.of_forall fun p hp ↦ by
        have : NeZero p := ⟨hp.ne_zero⟩
        exact mem_Gamma0_iff_dvd.mp (Subgroup.mem_congruenceClosure_iff.mp hγ (Gamma0 p)
          (Gamma0_is_congruence p) (Gamma0_le_Gamma0_of_dvd (dvd_zero p))))
    simp [h0]
  · have : NeZero N := ⟨hN⟩
    exact (Gamma0_is_congruence N).congruenceClosure_eq

/-- `Γ₁(N)` equals its congruence closure at every `N : ℕ` (`0` included). -/
@[simp]
theorem congruenceClosure_Gamma1 (N : ℕ) : (Gamma1 N).congruenceClosure = Gamma1 N := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine le_antisymm (fun γ hγ ↦ mem_Gamma1_iff_dvd_lowerRow.mpr ?_)
      (Gamma1 0).le_congruenceClosure
    have hmem : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ 1 0 ∧ (p : ℤ) ∣ γ 1 1 - 1 := fun p hp ↦ by
      have : NeZero p := ⟨hp.ne_zero⟩
      exact mem_Gamma1_iff_dvd_lowerRow.mp (Subgroup.mem_congruenceClosure_iff.mp hγ (Gamma1 p)
        (Gamma1_is_congruence p) (Gamma1_le_Gamma1_of_dvd (dvd_zero p)))
    have h10 : γ 1 0 = 0 :=
      Int.eq_zero_of_eventually_prime_dvd (Filter.Eventually.of_forall fun p hp ↦ (hmem p hp).1)
    have h11 : γ 1 1 - 1 = 0 :=
      Int.eq_zero_of_eventually_prime_dvd (Filter.Eventually.of_forall fun p hp ↦ (hmem p hp).2)
    simp [h10, h11]
  · have : NeZero N := ⟨hN⟩
    exact (Gamma1_is_congruence N).congruenceClosure_eq

example : (-1 : SL(2, ℤ)) ∉ (Gamma 3).congruenceClosure := by
  rw [congruenceClosure_Gamma, Gamma_mem]
  decide

end CongruenceSubgroup

end
