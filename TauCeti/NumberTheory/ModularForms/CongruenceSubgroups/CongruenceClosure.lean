/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Wohlfahrt
import TauCeti.Data.ZMod.Divisibility
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# The congruence closure of a subgroup of `SL₂(ℤ)`

For an arbitrary subgroup `Γ ≤ SL(2, ℤ)`, its **congruence closure** `Γ.congruenceClosure` is the
intersection of all congruence subgroups of `SL(2, ℤ)` containing `Γ` — equivalently, the closure
of `Γ` in the congruence topology on `SL(2, ℤ)`.

Because congruence subgroups are closed under binary intersection (`Γ(lcm M N) = Γ(M) ⊓ Γ(N)`), the
congruence closure is an idempotent, conjugation-equivariant closure operator commuting with
adjoining the centre `{±I}` (`Subgroup.congruenceClosure_withCenter`), and every congruence subgroup
containing `Γ` has strict level dividing `Γ.strictLevel`, hence contains `Γ(Γ.strictLevel)` by the
strict Wohlfahrt theorem (`Subgroup.Gamma_strictLevel_le_congruenceClosure`).

When `Γ.strictLevel ≠ 0` — in particular for every finite-index subgroup `Γ ≤ SL(2, ℤ)` — the join
`Γ ⊔ Γ(Γ.strictLevel)` is itself a congruence subgroup, giving the explicit formula
`Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)` (`Subgroup.congruenceClosure_eq_sup_Gamma_strictLevel`)
and showing that `Γ.congruenceClosure` is the least congruence subgroup containing `Γ`. A
finite-index subgroup `Γ` is therefore congruence if and only if `Γ.congruenceClosure = Γ`
(`Subgroup.congruenceClosure_eq_self_iff`), and `Γ.congruenceClosure` has the same image as `Γ`
under reduction to `SL(2, ZMod Γ.strictLevel)`
(`Subgroup.map_intCast_zmod_strictLevel_congruenceClosure`). Note that
`Γ.congruenceClosure.strictLevel` divides `Γ.strictLevel`
(`Subgroup.strictLevel_congruenceClosure_dvd`) and can be strictly smaller whenever
`Γ ⊔ Γ(Γ.strictLevel)` acquires smaller cusp widths, for instance when `Γ` surjects onto
`SL(2, ZMod Γ.strictLevel)` and `Γ.congruenceClosure = ⊤`.

Both hypotheses `Γ.strictLevel ≠ 0` and `Γ.FiniteIndex` are sharp where they appear:
* At `Γ = ⊥`, `⊥.congruenceClosure = ⊥` (`Subgroup.congruenceClosure_bot`) is not a congruence
  subgroup, so `Subgroup.congruenceClosure_eq_self_iff` requires `Γ.FiniteIndex`.
* Thin infinite-index subgroups such as Sanov's group `⟨T ^ 4, S T ^ 4 S⁻¹⟩` miss rational cusps
  and thus have `strictLevel = 0` (`Γ ⊔ Γ(0) = Γ` of infinite index), while every congruence
  subgroup containing them has finite index; hence
  `Subgroup.congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero` requires
  `Γ.strictLevel ≠ 0`.

Finally, the file records the two extreme noncongruence behaviours used in the trace factorization
of Hecke operators: `Γ.congruenceClosure = ⊤` precisely when `Γ` surjects onto
`SL(2, ZMod Γ.strictLevel)`
(`Subgroup.congruenceClosure_eq_top_iff_map_intCast_zmod_strictLevel_eq_top`), whereas any
noncongruence subgroup `Γ` whose projective lift `Γ.withCenter = ±Γ` is congruence has
`Γ.congruenceClosure = Γ.withCenter`
(`Subgroup.congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup`).

## Main definitions

* `Subgroup.congruenceClosure`: the intersection of all congruence subgroups of `SL(2, ℤ)`
  containing `Γ`.

## Main results

* `CongruenceSubgroup.not_isCongruenceSubgroup_bot`: the trivial subgroup `⊥ ≤ SL(2, ℤ)` is not a
  congruence subgroup.
* `Subgroup.le_congruenceClosure`, `Subgroup.congruenceClosure_le`,
  `Subgroup.congruenceClosure_le_iff`, `Subgroup.congruenceClosure_mono`,
  `Subgroup.congruenceClosure_idem`: universal and closure-operator properties.
* `Subgroup.congruenceClosure_pointwise_smul`, `Subgroup.instNormalCongruenceClosure`,
  `Subgroup.congruenceClosure_withCenter`: conjugation equivariance, preservation of normality, and
  commutation with adjoining `{±I}`.
* `Subgroup.Gamma_strictLevel_le_congruenceClosure`,
  `Subgroup.congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero`,
  `Subgroup.congruenceClosure_eq_sup_Gamma_strictLevel`: explicit description as
  `Γ ⊔ Γ(Γ.strictLevel)`.
* `Subgroup.isCongruenceSubgroup_congruenceClosure`, `Subgroup.congruenceClosure_eq_self_iff`:
  `Γ.congruenceClosure` is a congruence subgroup for finite-index `Γ`, and equals `Γ` iff `Γ` is a
  congruence subgroup.
* `Subgroup.map_intCast_zmod_strictLevel_congruenceClosure`,
  `Subgroup.congruenceClosure_eq_top_iff_map_intCast_zmod_strictLevel_eq_top`: reduction modulo
  `Γ.strictLevel` and the full-closure criterion `Γ.congruenceClosure = ⊤`.
* `Subgroup.congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup`: a noncongruence lift `Γ`
  of a congruence subgroup `±Γ` has congruence closure `±Γ`.
* `CongruenceSubgroup.congruenceClosure_Gamma`, `CongruenceSubgroup.congruenceClosure_Gamma0`,
  `CongruenceSubgroup.congruenceClosure_Gamma1`, `Subgroup.congruenceClosure_bot`,
  `Subgroup.congruenceClosure_top`: fixed points of `congruenceClosure` at every level `N : ℕ`
  (`N = 0` included).

## References

* G. Berger, *Hecke operators on noncongruence subgroups*, C. R. Acad. Sci. Paris Sér. I Math. 319
  (1994), 915–919.
* L. Long, *Finite index subgroups of the modular group and their modular forms*, in *Modular Forms
  and String Duality*, Fields Inst. Commun. 54, Amer. Math. Soc. (2008), 83–102, §3.
* I. Kiming, M. Schütt and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. (2) 83 (2011), 96–120, §§3, 5.
* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
-/

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise

namespace CongruenceSubgroup

/-- The trivial subgroup `⊥ ≤ SL(2, ℤ)` is not a congruence subgroup. -/
@[simp]
theorem not_isCongruenceSubgroup_bot : ¬ IsCongruenceSubgroup ⊥ :=
  fun h ↦ h.strictLevel_ne_zero (by simpa [Gamma_zero_bot] using strictLevel_Gamma 0)

end CongruenceSubgroup

namespace Subgroup

/-- The **congruence closure** of a subgroup `Γ ≤ SL(2, ℤ)`: the intersection of all congruence
subgroups of `SL(2, ℤ)` containing `Γ`. -/
def congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  sInf {Δ : Subgroup SL(2, ℤ) | CongruenceSubgroup.IsCongruenceSubgroup Δ ∧ Γ ≤ Δ}

/-- Unfolding: `Γ.congruenceClosure` is the infimum of all congruence subgroups containing `Γ`. -/
theorem congruenceClosure_def (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure =
      sInf {Δ : Subgroup SL(2, ℤ) | CongruenceSubgroup.IsCongruenceSubgroup Δ ∧ Γ ≤ Δ} := (rfl)

/-- An element of `SL(2, ℤ)` belongs to `Γ.congruenceClosure` if and only if it belongs to every
congruence subgroup containing `Γ`. -/
theorem mem_congruenceClosure_iff {Γ : Subgroup SL(2, ℤ)} {γ : SL(2, ℤ)} :
    γ ∈ Γ.congruenceClosure ↔
      ∀ Δ : Subgroup SL(2, ℤ), CongruenceSubgroup.IsCongruenceSubgroup Δ → Γ ≤ Δ → γ ∈ Δ := by
  simp [congruenceClosure, Subgroup.mem_sInf]

/-- Every subgroup `Γ ≤ SL(2, ℤ)` is contained in its congruence closure. -/
theorem le_congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Γ ≤ Γ.congruenceClosure :=
  le_sInf fun _ h ↦ h.2

/-- `Γ.congruenceClosure` is contained in every congruence subgroup containing `Γ`. -/
theorem congruenceClosure_le {Γ Δ : Subgroup SL(2, ℤ)}
    (hΔ : CongruenceSubgroup.IsCongruenceSubgroup Δ) (h : Γ ≤ Δ) :
    Γ.congruenceClosure ≤ Δ :=
  sInf_le ⟨hΔ, h⟩

/-- Universal property of `Subgroup.congruenceClosure` against congruence targets: for a congruence
subgroup `Δ`, `Γ.congruenceClosure ≤ Δ` if and only if `Γ ≤ Δ`. -/
theorem congruenceClosure_le_iff {Γ Δ : Subgroup SL(2, ℤ)}
    (hΔ : CongruenceSubgroup.IsCongruenceSubgroup Δ) :
    Γ.congruenceClosure ≤ Δ ↔ Γ ≤ Δ :=
  ⟨Γ.le_congruenceClosure.trans, congruenceClosure_le hΔ⟩

/-- Congruence closure is monotone with respect to subgroup inclusion. -/
@[gcongr]
theorem congruenceClosure_mono {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} (h : Γ₁ ≤ Γ₂) :
    Γ₁.congruenceClosure ≤ Γ₂.congruenceClosure :=
  le_sInf fun _ ⟨hΔ, h₂⟩ ↦ congruenceClosure_le hΔ (h.trans h₂)

/-- Congruence closure is idempotent on all subgroups of `SL(2, ℤ)`. -/
@[simp]
theorem congruenceClosure_idem (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.congruenceClosure = Γ.congruenceClosure :=
  le_antisymm (le_sInf fun _ ⟨hΔ, h⟩ ↦ congruenceClosure_le hΔ (congruenceClosure_le hΔ h))
    Γ.congruenceClosure.le_congruenceClosure

/-- The congruence closure of `⊤` is `⊤`. -/
@[simp]
theorem congruenceClosure_top : (⊤ : Subgroup SL(2, ℤ)).congruenceClosure = ⊤ :=
  eq_top_iff.mpr (le_congruenceClosure ⊤)

/-- The congruence closure of a finite-index subgroup of `SL(2, ℤ)` has finite index. -/
instance instFiniteIndexCongruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure.FiniteIndex :=
  Subgroup.finiteIndex_of_le Γ.le_congruenceClosure

/-- Congruence closure commutes with conjugation in `SL(2, ℤ)`. -/
@[simp]
theorem congruenceClosure_pointwise_smul (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ)) :
    (g • Γ).congruenceClosure = g • Γ.congruenceClosure := by
  have aux : ∀ (a : ConjAct SL(2, ℤ)) (H : Subgroup SL(2, ℤ)),
      a • H.congruenceClosure ≤ (a • H).congruenceClosure := fun a H ↦
    le_sInf fun Δ ⟨hΔ, hHΔ⟩ ↦ by
      have hHΔ' : H ≤ a⁻¹ • Δ := by
        simpa using (pointwise_smul_le_pointwise_smul_iff (a := a⁻¹)).mpr hHΔ
      simpa using (pointwise_smul_le_pointwise_smul_iff (a := a)).mpr
        (congruenceClosure_le (CongruenceSubgroup.conj_cong_is_cong a⁻¹ Δ hΔ) hHΔ')
  refine le_antisymm ?_ (aux g Γ)
  simpa using (pointwise_smul_le_pointwise_smul_iff (a := g)).mpr (aux g⁻¹ (g • Γ))

/-- The congruence closure of a normal subgroup of `SL(2, ℤ)` is normal. -/
instance instNormalCongruenceClosure (Γ : Subgroup SL(2, ℤ)) [h : Γ.Normal] :
    Γ.congruenceClosure.Normal where
  conj_mem x hx g := by
    have heq : ConjAct.toConjAct g • Γ.congruenceClosure = Γ.congruenceClosure := by
      rw [← congruenceClosure_pointwise_smul, h.conjAct]
    rw [← heq]
    simpa [ConjAct.toConjAct_smul] using
      smul_mem_pointwise_smul x (ConjAct.toConjAct g) Γ.congruenceClosure hx

/-- Congruence closure commutes unconditionally with adjoining `{±I}`. -/
@[simp]
theorem congruenceClosure_withCenter (Γ : Subgroup SL(2, ℤ)) :
    Γ.withCenter.congruenceClosure = Γ.congruenceClosure.withCenter := by
  refine le_antisymm (fun γ hγ ↦ ?_)
    (withCenter_le_iff.mpr ⟨congruenceClosure_mono Γ.le_withCenter,
      Γ.center_le_withCenter.trans Γ.withCenter.le_congruenceClosure⟩)
  by_contra hnot
  have h1 : γ ∉ Γ.congruenceClosure := fun h ↦ hnot (Γ.congruenceClosure.le_withCenter h)
  have h2 : -γ ∉ Γ.congruenceClosure := fun h ↦
    hnot (mem_withCenter_iff_exists_eq_or_eq_neg.mpr ⟨-γ, h, Or.inr (neg_neg γ).symm⟩)
  rw [mem_congruenceClosure_iff] at h1 h2
  push Not at h1 h2
  obtain ⟨Δ₁, hΔ₁, hΓ₁, hγ₁⟩ := h1
  obtain ⟨Δ₂, hΔ₂, hΓ₂, hγ₂⟩ := h2
  have hmem : γ ∈ (Δ₁ ⊓ Δ₂).withCenter :=
    mem_congruenceClosure_iff.mp hγ (Δ₁ ⊓ Δ₂).withCenter (hΔ₁.inf hΔ₂).withCenter
      (withCenter_le_iff.mpr ⟨(le_inf hΓ₁ hΓ₂).trans (Δ₁ ⊓ Δ₂).le_withCenter,
        (Δ₁ ⊓ Δ₂).center_le_withCenter⟩)
  obtain ⟨δ, hδ, rfl | rfl⟩ := mem_withCenter_iff_exists_eq_or_eq_neg.mp hmem
  · exact hγ₁ hδ.1
  · exact hγ₂ (by simpa using hδ.2)

/-- The principal congruence subgroup `Γ(Γ.strictLevel)` is contained in `Γ.congruenceClosure`. -/
theorem Gamma_strictLevel_le_congruenceClosure (Γ : Subgroup SL(2, ℤ)) :
    CongruenceSubgroup.Gamma Γ.strictLevel ≤ Γ.congruenceClosure :=
  le_sInf fun _ ⟨hΔ, hΓΔ⟩ ↦
    (CongruenceSubgroup.Gamma_le_Gamma_of_dvd (strictLevel_dvd_of_le hΓΔ)).trans
      hΔ.Gamma_strictLevel_le

/-- The strict level of `Γ.congruenceClosure` divides `Γ.strictLevel`. -/
theorem strictLevel_congruenceClosure_dvd (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.strictLevel ∣ Γ.strictLevel :=
  strictLevel_dvd_of_le Γ.le_congruenceClosure

/-- **Explicit formula for the congruence closure** when `Γ.strictLevel ≠ 0`:
`Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)`.

Needs `Γ.strictLevel ≠ 0`: for a thin infinite-index subgroup `Γ` missing rational cusps (such as
`⟨T ^ 4, S T ^ 4 S⁻¹⟩`), `Γ.strictLevel = 0` gives `Γ ⊔ Γ(0) = Γ` of infinite index, whereas every
congruence subgroup containing `Γ` has finite index. -/
theorem congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero {Γ : Subgroup SL(2, ℤ)}
    (h : Γ.strictLevel ≠ 0) :
    Γ.congruenceClosure = Γ ⊔ CongruenceSubgroup.Gamma Γ.strictLevel := by
  have : NeZero Γ.strictLevel := ⟨h⟩
  exact le_antisymm
    (congruenceClosure_le (CongruenceSubgroup.Gamma_is_cong_sub Γ.strictLevel).sup_right
      le_sup_left)
    (sup_le Γ.le_congruenceClosure Γ.Gamma_strictLevel_le_congruenceClosure)

/-- **Explicit formula for the congruence closure** of a finite-index subgroup `Γ ≤ SL(2, ℤ)`:
`Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)`. -/
theorem congruenceClosure_eq_sup_Gamma_strictLevel (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure = Γ ⊔ CongruenceSubgroup.Gamma Γ.strictLevel :=
  congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero Γ.strictLevel_pos.ne'

/-- When `Γ.strictLevel ≠ 0`, `Γ.congruenceClosure` is a congruence subgroup.

Needs `Γ.strictLevel ≠ 0`: at `Γ = ⊥`, `⊥.congruenceClosure = ⊥` is not a congruence subgroup. -/
theorem isCongruenceSubgroup_congruenceClosure_of_strictLevel_ne_zero {Γ : Subgroup SL(2, ℤ)}
    (h : Γ.strictLevel ≠ 0) :
    CongruenceSubgroup.IsCongruenceSubgroup Γ.congruenceClosure := by
  have : NeZero Γ.strictLevel := ⟨h⟩
  rw [congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero h]
  exact (CongruenceSubgroup.Gamma_is_cong_sub Γ.strictLevel).sup_right

/-- For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, `Γ.congruenceClosure` is a congruence subgroup. -/
theorem isCongruenceSubgroup_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    CongruenceSubgroup.IsCongruenceSubgroup Γ.congruenceClosure :=
  isCongruenceSubgroup_congruenceClosure_of_strictLevel_ne_zero Γ.strictLevel_pos.ne'

/-- When `Γ₁.strictLevel ≠ 0`, congruence closure distributes over a binary join `Γ₁ ⊔ Γ₂`. -/
theorem congruenceClosure_sup_of_strictLevel_ne_zero {Γ₁ Γ₂ : Subgroup SL(2, ℤ)}
    (h : Γ₁.strictLevel ≠ 0) :
    (Γ₁ ⊔ Γ₂).congruenceClosure = Γ₁.congruenceClosure ⊔ Γ₂.congruenceClosure :=
  le_antisymm
    (congruenceClosure_le (isCongruenceSubgroup_congruenceClosure_of_strictLevel_ne_zero h).sup_left
      (sup_le_sup Γ₁.le_congruenceClosure Γ₂.le_congruenceClosure))
    (sup_le (congruenceClosure_mono le_sup_left) (congruenceClosure_mono le_sup_right))

/-- When `Γ₁` has finite index, congruence closure distributes over `Γ₁ ⊔ Γ₂`. -/
theorem congruenceClosure_sup (Γ₁ Γ₂ : Subgroup SL(2, ℤ)) [Γ₁.FiniteIndex] :
    (Γ₁ ⊔ Γ₂).congruenceClosure = Γ₁.congruenceClosure ⊔ Γ₂.congruenceClosure :=
  congruenceClosure_sup_of_strictLevel_ne_zero Γ₁.strictLevel_pos.ne'

/-- A finite-index subgroup `Γ ≤ SL(2, ℤ)` equals its congruence closure if and only if it is a
congruence subgroup.

Needs `Γ.FiniteIndex`: at `Γ = ⊥`, `⊥.congruenceClosure = ⊥` while `⊥` is not a congruence
subgroup. -/
theorem congruenceClosure_eq_self_iff {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] :
    Γ.congruenceClosure = Γ ↔ CongruenceSubgroup.IsCongruenceSubgroup Γ :=
  ⟨fun h ↦ h ▸ Γ.isCongruenceSubgroup_congruenceClosure,
    fun h ↦ le_antisymm (congruenceClosure_le h le_rfl) Γ.le_congruenceClosure⟩

/-- When `Γ.strictLevel ≠ 0`, `Γ.congruenceClosure` and `Γ` have the same image under reduction to
`SL(2, ZMod Γ.strictLevel)`. -/
theorem map_intCast_zmod_strictLevel_congruenceClosure_of_strictLevel_ne_zero
    {Γ : Subgroup SL(2, ℤ)} (h : Γ.strictLevel ≠ 0) :
    Γ.congruenceClosure.map
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) =
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) := by
  let φ : SL(2, ℤ) →* SL(2, ZMod Γ.strictLevel) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))
  have hker : (CongruenceSubgroup.Gamma Γ.strictLevel).map φ = ⊥ := Subgroup.map_ker_self φ
  rw [congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero h, Subgroup.map_sup,
    hker, sup_bot_eq]

/-- For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, `Γ.congruenceClosure` and `Γ` have the same image
in `SL(2, ZMod Γ.strictLevel)`. -/
@[simp]
theorem map_intCast_zmod_strictLevel_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure.map
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) =
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) :=
  map_intCast_zmod_strictLevel_congruenceClosure_of_strictLevel_ne_zero Γ.strictLevel_pos.ne'

/-- When `Γ.strictLevel ≠ 0`, `Γ.congruenceClosure = ⊤` if and only if `Γ` surjects onto
`SL(2, ZMod Γ.strictLevel)`. -/
theorem congruenceClosure_eq_top_iff_map_intCast_zmod_strictLevel_eq_top_of_strictLevel_ne_zero
    {Γ : Subgroup SL(2, ℤ)} (h : Γ.strictLevel ≠ 0) :
    Γ.congruenceClosure = ⊤ ↔
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) = ⊤ := by
  let φ : SL(2, ℤ) →* SL(2, ZMod Γ.strictLevel) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))
  have htop_map : (⊤ : Subgroup SL(2, ℤ)).map φ = ⊤ :=
    Subgroup.map_top_of_surjective φ Matrix.SpecialLinearGroup.map_intCast_zmod_surjective
  rw [← map_intCast_zmod_strictLevel_congruenceClosure_of_strictLevel_ne_zero h, ← htop_map]
  exact ⟨fun htop ↦ congr_arg (Subgroup.map φ) htop,
    Subgroup.map_injective_of_ker_le φ Γ.Gamma_strictLevel_le_congruenceClosure le_top⟩

/-- For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, `Γ.congruenceClosure = ⊤` if and only if `Γ`
surjects onto `SL(2, ZMod Γ.strictLevel)`. -/
theorem congruenceClosure_eq_top_iff_map_intCast_zmod_strictLevel_eq_top
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] :
    Γ.congruenceClosure = ⊤ ↔
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) = ⊤ :=
  congruenceClosure_eq_top_iff_map_intCast_zmod_strictLevel_eq_top_of_strictLevel_ne_zero
    Γ.strictLevel_pos.ne'

/-- **Congruence closure of a noncongruence lift**: if `Γ.withCenter = ±Γ` is a congruence subgroup
while `Γ` itself is not, then `Γ.congruenceClosure = Γ.withCenter`. -/
theorem congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup {Γ : Subgroup SL(2, ℤ)}
    (hcong : CongruenceSubgroup.IsCongruenceSubgroup Γ.withCenter)
    (hnc : ¬ CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    Γ.congruenceClosure = Γ.withCenter := by
  have hneg : (-1 : SL(2, ℤ)) ∉ Γ := by
    intro h1
    have hcenter : center SL(2, ℤ) ≤ Γ := fun z hz ↦ by
      rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hz with rfl | rfl
      · exact Γ.one_mem
      · exact h1
    exact hnc (withCenter_eq_self_iff.mpr hcenter ▸ hcong)
  have hfiw := hcong.finiteIndex
  have : Γ.FiniteIndex := ⟨by
    rw [TauCeti.ModularForm.index_eq_two_mul_index_withCenter_of_neg_one_notMem hneg]
    exact mul_ne_zero two_ne_zero hfiw.index_ne_zero⟩
  have hle : Γ.congruenceClosure ≤ Γ.withCenter := congruenceClosure_le hcong Γ.le_withCenter
  have hmul : Γ.relIndex Γ.congruenceClosure * Γ.congruenceClosure.relIndex Γ.withCenter = 2 :=
    (relIndex_mul_relIndex Γ Γ.congruenceClosure Γ.withCenter Γ.le_congruenceClosure hle).trans
      (TauCeti.ModularForm.relIndex_withCenter_eq_two_of_neg_one_notMem hneg)
  have hne1 : Γ.relIndex Γ.congruenceClosure ≠ 1 := by
    rw [ne_eq, relIndex_eq_one]
    intro hle'
    exact hnc (congruenceClosure_eq_self_iff.mp (le_antisymm hle' Γ.le_congruenceClosure))
  have hdvd : Γ.relIndex Γ.congruenceClosure ∣ 2 := ⟨_, hmul.symm⟩
  have hrel2 : Γ.relIndex Γ.congruenceClosure = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne1
  rw [hrel2] at hmul
  have hrel1 : Γ.congruenceClosure.relIndex Γ.withCenter = 1 := by omega
  exact le_antisymm hle (relIndex_eq_one.mp hrel1)

end Subgroup

namespace CongruenceSubgroup

/-- Every congruence subgroup equals its congruence closure. -/
theorem IsCongruenceSubgroup.congruenceClosure_eq_self {Γ : Subgroup SL(2, ℤ)}
    (h : IsCongruenceSubgroup Γ) : Γ.congruenceClosure = Γ :=
  le_antisymm (Subgroup.congruenceClosure_le h le_rfl) Γ.le_congruenceClosure

/-- `Γ(N)` equals its congruence closure at every level `N : ℕ` (`N = 0` included). -/
@[simp]
theorem congruenceClosure_Gamma (N : ℕ) : (Gamma N).congruenceClosure = Gamma N := by
  rcases ne_or_eq N 0 with hN | rfl
  · have : NeZero N := ⟨hN⟩
    exact (Gamma_is_cong_sub N).congruenceClosure_eq_self
  · refine le_antisymm (fun γ hγ ↦ Gamma_mem.mpr ?_) (Gamma 0).le_congruenceClosure
    have hmem (p k : ℕ) (hp : p.Prime) (hpk : p ^ k ∣ 0) : γ ∈ Gamma (p ^ k) := by
      have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
      exact Subgroup.mem_congruenceClosure_iff.mp hγ (Gamma (p ^ k)) (Gamma_is_cong_sub (p ^ k))
        (Gamma_le_Gamma_of_dvd hpk)
    refine ⟨ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_,
      ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_,
      ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_,
      ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_⟩
    · simpa [ZMod.cast_intCast hpk] using (Gamma_mem.mp (hmem p k hp hpk)).1
    · simpa [ZMod.cast_intCast hpk] using (Gamma_mem.mp (hmem p k hp hpk)).2.1
    · simpa [ZMod.cast_intCast hpk] using (Gamma_mem.mp (hmem p k hp hpk)).2.2.1
    · simpa [ZMod.cast_intCast hpk] using (Gamma_mem.mp (hmem p k hp hpk)).2.2.2

/-- `Γ₀(N)` equals its congruence closure at every level `N : ℕ` (`N = 0` included). -/
@[simp]
theorem congruenceClosure_Gamma0 (N : ℕ) : (Gamma0 N).congruenceClosure = Gamma0 N := by
  rcases ne_or_eq N 0 with hN | rfl
  · have : NeZero N := ⟨hN⟩
    exact (Gamma0_is_congruence N).congruenceClosure_eq_self
  · refine le_antisymm (fun γ hγ ↦ Gamma0_mem.mpr ?_) (Gamma0 0).le_congruenceClosure
    refine ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_
    have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
    have hmem : γ ∈ Gamma0 (p ^ k) :=
      Subgroup.mem_congruenceClosure_iff.mp hγ (Gamma0 (p ^ k)) (Gamma0_is_congruence (p ^ k))
        (Gamma0_le_Gamma0_of_dvd hpk)
    simpa [ZMod.cast_intCast hpk] using Gamma0_mem.mp hmem

/-- `Γ₁(N)` equals its congruence closure at every level `N : ℕ` (`N = 0` included). -/
@[simp]
theorem congruenceClosure_Gamma1 (N : ℕ) : (Gamma1 N).congruenceClosure = Gamma1 N := by
  rcases ne_or_eq N 0 with hN | rfl
  · have : NeZero N := ⟨hN⟩
    exact (Gamma1_is_congruence N).congruenceClosure_eq_self
  · refine le_antisymm (fun γ hγ ↦ (Gamma1_mem 0 γ).mpr ?_) (Gamma1 0).le_congruenceClosure
    have hmem (p k : ℕ) (hp : p.Prime) (hpk : p ^ k ∣ 0) : γ ∈ Gamma1 (p ^ k) := by
      have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
      exact Subgroup.mem_congruenceClosure_iff.mp hγ (Gamma1 (p ^ k)) (Gamma1_is_congruence (p ^ k))
        (Gamma1_le_Gamma1_of_dvd hpk)
    refine ⟨ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_,
      ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_,
      ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_⟩
    · simpa [ZMod.cast_intCast hpk] using ((Gamma1_mem (p ^ k) γ).mp (hmem p k hp hpk)).1
    · simpa [ZMod.cast_intCast hpk] using ((Gamma1_mem (p ^ k) γ).mp (hmem p k hp hpk)).2.1
    · simpa [ZMod.cast_intCast hpk] using ((Gamma1_mem (p ^ k) γ).mp (hmem p k hp hpk)).2.2

end CongruenceSubgroup

namespace Subgroup

/-- The trivial subgroup `⊥ ≤ SL(2, ℤ)` is closed in the congruence topology: its congruence closure
is `⊥`. -/
@[simp]
theorem congruenceClosure_bot : (⊥ : Subgroup SL(2, ℤ)).congruenceClosure = ⊥ :=
  CongruenceSubgroup.Gamma_zero_bot ▸ CongruenceSubgroup.congruenceClosure_Gamma 0

end Subgroup
