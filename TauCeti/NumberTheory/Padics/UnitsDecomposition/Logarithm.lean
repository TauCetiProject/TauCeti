/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import TauCeti.NumberTheory.Padics.PrincipalUnits
import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
import TauCeti.NumberTheory.LocalField.DeepUnits.Basic
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.ExpLog
import TauCeti.NumberTheory.Padics.UnitsDecomposition.Basic

/-!
# The logarithmic decomposition `ℤ_pˣ ≃ (ℤ/qℤ)ˣ × ℤ_p`

Put `q = p` for odd `p` and `q = 4` for `p = 2`; here `q = p ^ k` with
`k = TauCeti.padicUnitsDepth p`. The `p`-adic logarithm identifies the principal units
`1 + qℤ_p` with the additive group `qℤ_p`, with the exponential as inverse, and dividing by `q`
gives a topological isomorphism

`TauCeti.unitsPrincipalLogEquiv p : 1 + qℤ_p ≃ₜ* ℤ_p`,  `u ↦ log u / q`,  `s ↦ exp (q s)`.

The element `γ = exp q` (`TauCeti.padicUnitsGenerator p`) corresponds to `1`; it has exact level
`k`, so it topologically generates `1 + qℤ_p`.

Reduction modulo `q` maps `ℤ_pˣ` onto `Δ = (ℤ/qℤ)ˣ` with kernel `1 + qℤ_p`. It has a unique
multiplicative section `ω : Δ → ℤ_pˣ` (`TauCeti.padicUnitsSection p`), whose values are
`φ(q)`-th roots of unity: `(p - 1)`-st roots of unity for odd `p`, as for the Teichmüller
section, and signs `±1` for `p = 2`. Together these give the continuous decomposition

`TauCeti.padicIntUnitsEquivZModUnitsProd p : ℤ_pˣ ≃ₜ* Δ × ℤ_p`,
`x ↦ (x mod q, log (x / ω(x mod q)) / q)`,

with inverse `(δ, s) ↦ ω(δ) exp(q s)`, sending `γ` to `(1, 1)`. It is the only continuous
decomposition whose first component is reduction modulo `q` and which sends `γ` to an element
with second component `1`.

At `p = 2` the modulus `q = 4` cannot be lowered to `2`: `-1` has order two, so
`1 + 2ℤ_2 = ℤ_2ˣ` is not torsion-free and cannot be isomorphic to `ℤ_2`.

## Main declarations

* `TauCeti.padicUnitsDepth p`: the exponent `k` with `q = p ^ k`.
* `TauCeti.unitsPrincipalLogEquiv p`: the logarithm `1 + qℤ_p ≃ₜ* ℤ_p`, `u ↦ log u / q`.
* `TauCeti.padicUnitsGenerator p`: the unit `γ = exp q`, with
  `TauCeti.topologicalClosure_zpowers_padicUnitsGenerator`.
* `TauCeti.padicUnitsSection p`: the section `ω`, with `TauCeti.eq_padicUnitsSection` and
  `TauCeti.padicUnitsSection_pow_totient`.
* `TauCeti.padicIntUnitsEquivZModUnitsProd p`: the decomposition `ℤ_pˣ ≃ₜ* (ℤ/qℤ)ˣ × ℤ_p`, with
  `TauCeti.padicIntUnitsEquivZModUnitsProd_padicUnitsGenerator` and the uniqueness theorem
  `TauCeti.eq_padicIntUnitsEquivZModUnitsProd`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Propositions (5.5) and (5.7).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3–4.
-/

public section

open NormedSpace ValuativeRel

namespace TauCeti

variable (p : ℕ)

/-- The exponent `k` with `q = p ^ k`, the modulus of the principal units `1 + qℤ_p` on which the
`p`-adic logarithm is an isomorphism onto `qℤ_p`: `k = 1`, so `q = p`, for odd `p`, and
`k = 2`, so `q = 4`, for `p = 2`. -/
def padicUnitsDepth : ℕ := if p = 2 then 2 else 1

@[simp]
theorem padicUnitsDepth_two : padicUnitsDepth 2 = 2 := by
  simp [padicUnitsDepth]

theorem padicUnitsDepth_of_ne_two {p : ℕ} (hp : p ≠ 2) : padicUnitsDepth p = 1 := by
  simp [padicUnitsDepth, hp]

theorem padicUnitsDepth_pos : 0 < padicUnitsDepth p := by
  unfold padicUnitsDepth
  split_ifs <;> omega

/-- For `p = 2` the depth is at least `2`, the range in which the principal units of `ℤ_2` are
procyclic and torsion-free. -/
private theorem two_le_padicUnitsDepth {p : ℕ} (h : p = 2) : 2 ≤ padicUnitsDepth p := by
  subst h
  simp

variable {p} [hp : Fact p.Prime]

/-- The depths `k + j` are in the convergence range `1 < (p - 1) * i` of the exponential and the
logarithm on `ℚ_[p]`. -/
private theorem one_lt_sub_one_mul_padicUnitsDepth_add (j : ℕ) :
    1 < (p - 1) * (padicUnitsDepth p + j) := by
  have := hp.out.two_le
  by_cases h : p = 2
  · subst h
    rw [padicUnitsDepth_two]
    omega
  · rw [padicUnitsDepth_of_ne_two h]
    exact lt_of_lt_of_le (by norm_num)
      (Nat.mul_le_mul (by omega : 2 ≤ p - 1) (by omega : 1 ≤ 1 + j))

private theorem one_lt_sub_one_mul_padicUnitsDepth : 1 < (p - 1) * padicUnitsDepth p :=
  one_lt_sub_one_mul_padicUnitsDepth_add 0

private theorem norm_coe_sub_one (u : ℤ_[p]ˣ) :
    ‖((u : ℤ_[p]) : ℚ_[p]) - 1‖ = ‖(u : ℤ_[p]) - 1‖ := by
  rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]

private theorem norm_coe_sub_one_le (u : unitsPrincipal p (padicUnitsDepth p)) :
    ‖(((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(padicUnitsDepth p : ℤ)) := by
  rw [norm_coe_sub_one]
  exact mem_unitsPrincipal_iff_norm.mp u.2

private theorem norm_q : ‖(p : ℚ_[p]) ^ padicUnitsDepth p‖ = (p : ℝ) ^ (-(padicUnitsDepth p : ℤ)) :=
  Padic.norm_p_pow _

private theorem q_ne_zero : (p : ℚ_[p]) ^ padicUnitsDepth p ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)

private theorem norm_q_mul_le (s : ℤ_[p]) :
    ‖(p : ℚ_[p]) ^ padicUnitsDepth p * s‖ ≤ (p : ℝ) ^ (-(padicUnitsDepth p : ℤ)) := by
  rw [norm_mul, norm_q]
  exact mul_le_of_le_one_right (zpow_pos (by exact_mod_cast hp.out.pos) _).le
    (PadicInt.norm_le_one s)

/-! ### The logarithm on `1 + qℤ_p` -/

/-- An element within `p ^ (-k)` of `1` has norm `1`. -/
private theorem norm_eq_one_of_norm_sub_one_le {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ) ^ (-(padicUnitsDepth p : ℤ))) : ‖x‖ = 1 := by
  refine (Padic.norm_eq_of_norm_sub_lt_right (hx.trans_lt ?_)).trans norm_one
  rw [norm_one]
  exact zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt)
    (by simpa using padicUnitsDepth_pos p)

variable (p) in
/-- The principal units `1 + qℤ_p` are the unit filtration `U(ℚ_p,k)`, `q = p ^ k`. -/
private noncomputable def unitsPrincipalEquivUnitFiltration :
    unitsPrincipal p (padicUnitsDepth p) ≃ₜ* unitFiltration ℚ_[p] (padicUnitsDepth p) :=
  have hmem (x : unitFiltration ℚ_[p] (padicUnitsDepth p)) :
      ‖((x : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(padicUnitsDepth p : ℤ)) :=
    (Padic.mem_unitFiltration_iff_norm_sub_one_le (padicUnitsDepth_pos p).ne').mp x.2
  let e : unitsPrincipal p (padicUnitsDepth p) ≃* unitFiltration ℚ_[p] (padicUnitsDepth p) :=
    { toFun u := ⟨Units.map PadicInt.Coe.ringHom.toMonoidHom u,
        (Padic.mem_unitFiltration_iff_norm_sub_one_le (padicUnitsDepth_pos p).ne').mpr
          (norm_coe_sub_one_le u)⟩
      invFun x := ⟨PadicInt.mkUnits (norm_eq_one_of_norm_sub_one_le (hmem x)), by
        rw [mem_unitsPrincipal_iff_norm, ← norm_coe_sub_one]
        exact hmem x⟩
      left_inv _ := Subtype.ext (Units.ext rfl)
      right_inv _ := Subtype.ext (Units.ext rfl)
      map_mul' _ _ := rfl }
  have he : Continuous e :=
    ((Continuous.units_map _ continuous_subtype_val).comp continuous_subtype_val).subtype_mk _
  -- A continuous bijection from a compact space to a Hausdorff space is a homeomorphism.
  ContinuousMulEquiv.mk e he (he.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv))

/-- `x / q` for `x ∈ 𝓂 ^ k`, as an element of `ℤ_[p]`. -/
private noncomputable def divQ (x : (𝓂[ℚ_[p]] ^ padicUnitsDepth p : Ideal 𝒪[ℚ_[p]])) : ℤ_[p] :=
  ⟨((x : 𝒪[ℚ_[p]]) : ℚ_[p]) / (p : ℚ_[p]) ^ padicUnitsDepth p, by
    rw [PadicInt.mem_subring_iff, norm_div, norm_q,
      div_le_one (zpow_pos (by exact_mod_cast hp.out.pos) _)]
    exact TauCeti.Padic.mem_maximalIdeal_pow_iff_norm_le.mp x.2⟩

private theorem coe_divQ (x : (𝓂[ℚ_[p]] ^ padicUnitsDepth p : Ideal 𝒪[ℚ_[p]])) :
    (divQ x : ℚ_[p]) = ((x : 𝒪[ℚ_[p]]) : ℚ_[p]) / (p : ℚ_[p]) ^ padicUnitsDepth p :=
  rfl

/-- `q s` for `s ∈ ℤ_[p]`, as an element of `𝓂 ^ k`. -/
private noncomputable def mulQ (s : ℤ_[p]) : (𝓂[ℚ_[p]] ^ padicUnitsDepth p : Ideal 𝒪[ℚ_[p]]) :=
  ⟨⟨(p : ℚ_[p]) ^ padicUnitsDepth p * s, by
    rw [Padic.integerRing_eq_subring, PadicInt.mem_subring_iff]
    exact (norm_q_mul_le s).trans
      (zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by simp))⟩,
    TauCeti.Padic.mem_maximalIdeal_pow_iff_norm_le.mpr (norm_q_mul_le s)⟩

private theorem coe_mulQ (s : ℤ_[p]) :
    ((mulQ s : 𝒪[ℚ_[p]]) : ℚ_[p]) = (p : ℚ_[p]) ^ padicUnitsDepth p * s :=
  rfl

variable (p) in
/-- Division by `q = p ^ k` identifies the additive group `𝓂 ^ k` of `ℚ_[p]` with `ℤ_p`. -/
private noncomputable def maximalIdealPowEquiv :
    Multiplicative (𝓂[ℚ_[p]] ^ padicUnitsDepth p : Ideal 𝒪[ℚ_[p]]) ≃ₜ*
      Multiplicative ℤ_[p] where
  toFun x := .ofAdd (divQ x.toAdd)
  invFun s := .ofAdd (mulQ s.toAdd)
  left_inv x := by
    refine Multiplicative.toAdd.injective (Subtype.ext (Subtype.ext ?_))
    rw [toAdd_ofAdd, coe_mulQ, toAdd_ofAdd, coe_divQ, mul_div_cancel₀ _ q_ne_zero]
  right_inv s := by
    refine Multiplicative.toAdd.injective (PadicInt.ext ?_)
    rw [toAdd_ofAdd, coe_divQ, toAdd_ofAdd, coe_mulQ, mul_div_cancel_left₀ _ q_ne_zero]
  map_mul' x y := by
    refine Multiplicative.toAdd.injective (PadicInt.ext ?_)
    simp only [toAdd_mul, toAdd_ofAdd, PadicInt.coe_add, coe_divQ, Submodule.coe_add,
      Subring.coe_add, add_div]
  continuous_toFun := continuous_ofAdd.comp <| Continuous.subtype_mk
    ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_toAdd)).div_const _) _
  continuous_invFun := by
    refine continuous_ofAdd.comp (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _)
    exact continuous_const.mul
      ((continuous_subtype_val : Continuous ((↑) : ℤ_[p] → ℚ_[p])).comp continuous_toAdd)

variable (p) in
/-- **The `p`-adic logarithm on `1 + qℤ_p`.** The logarithm identifies the principal units
`1 + qℤ_p`, `q = p ^ padicUnitsDepth p`, with `ℤ_p` as topological groups by `u ↦ log u / q`;
the inverse is `s ↦ exp (q s)`. It is the deep-unit logarithm `TauCeti.deepUnitExpLogEquiv`
on `U(ℚ_p,k)`, followed by division by `q`. -/
noncomputable def unitsPrincipalLogEquiv :
    unitsPrincipal p (padicUnitsDepth p) ≃ₜ* Multiplicative ℤ_[p] :=
  ((unitsPrincipalEquivUnitFiltration p).trans (deepUnitExpLogEquiv ℚ_[p]
    (by rw [absoluteRamificationIndex_padic]; exact one_lt_sub_one_mul_padicUnitsDepth))).trans
    (maximalIdealPowEquiv p)

@[simp]
theorem coe_unitsPrincipalLogEquiv_apply (u : unitsPrincipal p (padicUnitsDepth p)) :
    ((unitsPrincipalLogEquiv p u).toAdd : ℚ_[p]) =
      log (((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ padicUnitsDepth p := by
  rw [unitsPrincipalLogEquiv, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply]
  exact congrArg (· / (p : ℚ_[p]) ^ padicUnitsDepth p) (coe_deepUnitExpLogEquiv_apply _ _)

@[simp]
theorem coe_unitsPrincipalLogEquiv_symm_apply (s : Multiplicative ℤ_[p]) :
    ((((unitsPrincipalLogEquiv p).symm s : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) =
      exp ((p : ℚ_[p]) ^ padicUnitsDepth p * s.toAdd) := by
  rw [unitsPrincipalLogEquiv, ContinuousMulEquiv.symm_trans_apply,
    ContinuousMulEquiv.symm_trans_apply]
  exact coe_deepUnitExpLogEquiv_symm_apply _ _

/-! ### The generator `γ = exp q` -/

variable (p) in
/-- **The generator `γ = exp q` of `1 + qℤ_p`**, the unit corresponding to `1` under the
logarithm: `exp p` for odd `p` and `exp 4` for `p = 2`. -/
noncomputable def padicUnitsGenerator : ℤ_[p]ˣ :=
  (unitsPrincipalLogEquiv p).symm (.ofAdd 1)

@[simp]
theorem coe_padicUnitsGenerator :
    ((padicUnitsGenerator p : ℤ_[p]) : ℚ_[p]) = exp ((p : ℚ_[p]) ^ padicUnitsDepth p) := by
  simp [padicUnitsGenerator]

theorem padicUnitsGenerator_mem_unitsPrincipal :
    padicUnitsGenerator p ∈ unitsPrincipal p (padicUnitsDepth p) :=
  ((unitsPrincipalLogEquiv p).symm (.ofAdd 1)).2

@[simp]
theorem unitsPrincipalLogEquiv_padicUnitsGenerator :
    unitsPrincipalLogEquiv p ⟨padicUnitsGenerator p, padicUnitsGenerator_mem_unitsPrincipal⟩ =
      .ofAdd 1 :=
  (unitsPrincipalLogEquiv p).apply_symm_apply _

/-- `γ = exp q` has exact level `padicUnitsDepth p`: it is not congruent to `1` modulo `p q`. -/
theorem padicUnitsGenerator_notMem_unitsPrincipal_succ :
    padicUnitsGenerator p ∉ unitsPrincipal p (padicUnitsDepth p + 1) := by
  intro h
  have hu := mem_unitsPrincipal_iff_norm.mp h
  rw [← norm_coe_sub_one, coe_padicUnitsGenerator] at hu
  -- `log γ = q` has norm `p ^ (-k)`, while a unit of level `k + 1` has logarithm of norm at
  -- most `p ^ (-(k + 1))`.
  have hlog := Padic.norm_log (one_lt_sub_one_mul_padicUnitsDepth_add 1) hu
  rw [Padic.log_exp one_lt_sub_one_mul_padicUnitsDepth norm_q.le, norm_q] at hlog
  have := hlog.trans_le hu
  rw [zpow_le_zpow_iff_right₀ (by exact_mod_cast hp.out.one_lt)] at this
  omega

/-- **`γ = exp q` topologically generates `1 + qℤ_p`.** -/
theorem topologicalClosure_zpowers_padicUnitsGenerator :
    (Subgroup.zpowers (padicUnitsGenerator p)).topologicalClosure =
      unitsPrincipal p (padicUnitsDepth p) :=
  topologicalClosure_zpowers_eq_unitsPrincipal (padicUnitsDepth_pos p)
    two_le_padicUnitsDepth padicUnitsGenerator_mem_unitsPrincipal
    padicUnitsGenerator_notMem_unitsPrincipal_succ

/-! ### The section `ω` of reduction modulo `q` -/

variable (p) in
/-- Reduction modulo `q` on `ℤ_pˣ` has a multiplicative section: its kernel `1 + qℤ_p` has a
complement, the `(p - 1)`-st roots of unity for odd `p` and `{±1}` for `p = 2`. -/
private theorem exists_section :
    ∃ ω : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ,
      ∀ δ, PadicInt.unitsToZModPow (padicUnitsDepth p) (ω δ) = δ := by
  obtain ⟨A, hdisj, hsup⟩ : ∃ A : Subgroup ℤ_[p]ˣ,
      Disjoint A (unitsPrincipal p (padicUnitsDepth p)) ∧
        A ⊔ unitsPrincipal p (padicUnitsDepth p) = ⊤ := by
    by_cases h : p = 2
    · subst h
      refine ⟨Subgroup.zpowers (-1), (disjoint_unitsPrincipal_zpowers_neg_one le_rfl).symm, ?_⟩
      rw [sup_comm, padicUnitsDepth_two, ← unitsPlusMinus_def]
      exact unitsPlusMinus_two
    · rw [padicUnitsDepth_of_ne_two h]
      exact ⟨_, (isComplement'_rootsOfUnity_unitsPrincipal_one p).disjoint,
        (isComplement'_rootsOfUnity_unitsPrincipal_one p).sup_eq_top⟩
  -- Reduction modulo `q` restricts to an isomorphism from the complement `A` onto `(ℤ/qℤ)ˣ`.
  let f := (PadicInt.unitsToZModPow (p := p) (padicUnitsDepth p)).toMonoidHom.comp A.subtype
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_one f).mpr fun a ha ↦ Subtype.ext ?_, fun δ ↦ ?_⟩
    · exact Subgroup.disjoint_def.mp hdisj a.2 (unitsToZModPow_eq_one_iff.mp ha)
    · obtain ⟨g, rfl⟩ := PadicInt.unitsToZModPow_surjective (p := p) (padicUnitsDepth p) δ
      obtain ⟨a, ha, n, hn, rfl⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top g)
      exact ⟨⟨a, ha⟩, by simp [f, unitsToZModPow_eq_one_iff.mpr hn]⟩
  exact ⟨A.subtype.comp (MulEquiv.ofBijective f hf).symm.toMonoidHom,
    (MulEquiv.ofBijective f hf).apply_symm_apply⟩

variable (p) in
/-- **The multiplicative section `ω : (ℤ/qℤ)ˣ → ℤ_pˣ` of reduction modulo `q`.** It is unique
(`TauCeti.eq_padicUnitsSection`), and its values are `φ(q)`-th roots of unity
(`TauCeti.padicUnitsSection_pow_totient`): `(p - 1)`-st roots of unity for odd `p`, as for the
Teichmüller section, and `±1` for `p = 2`. -/
noncomputable def padicUnitsSection : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ :=
  (exists_section p).choose

@[simp]
theorem unitsToZModPow_padicUnitsSection (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    PadicInt.unitsToZModPow (padicUnitsDepth p) (padicUnitsSection p δ) = δ :=
  (exists_section p).choose_spec δ

/-- The values of `ω` are `φ(q)`-th roots of unity. -/
theorem padicUnitsSection_pow_totient (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    padicUnitsSection p δ ^ (p ^ padicUnitsDepth p).totient = 1 := by
  rw [← map_pow, ZMod.pow_totient, map_one]

/-- **Uniqueness of `ω`**: it is the only multiplicative section of reduction modulo `q`, since
two sections differ by torsion elements of the torsion-free group `1 + qℤ_p`. -/
theorem eq_padicUnitsSection {ω : (ZMod (p ^ padicUnitsDepth p))ˣ →* ℤ_[p]ˣ}
    (hω : ∀ δ, PadicInt.unitsToZModPow (padicUnitsDepth p) (ω δ) = δ) :
    ω = padicUnitsSection p := by
  ext1 δ
  by_contra hne
  have hmem : (padicUnitsSection p δ)⁻¹ * ω δ ∈ unitsPrincipal p (padicUnitsDepth p) := by
    rw [← unitsToZModPow_eq_one_iff, map_mul, map_inv, hω, unitsToZModPow_padicUnitsSection,
      inv_mul_cancel]
  have hδ : IsOfFinOrder δ := isOfFinOrder_of_finite δ
  exact not_isOfFinOrder_of_mem_unitsPrincipal (padicUnitsDepth_pos p)
    two_le_padicUnitsDepth hmem (by rwa [ne_eq, inv_mul_eq_one, eq_comm])
    (((padicUnitsSection p).isOfFinOrder hδ).inv.mul (ω.isOfFinOrder hδ))

/-! ### The decomposition `ℤ_pˣ ≃ (ℤ/qℤ)ˣ × ℤ_p` -/

/-- Dividing a unit by the section of its residue modulo `q` lands in `1 + qℤ_p`. -/
private theorem inv_padicUnitsSection_mul_mem (x : ℤ_[p]ˣ) :
    (padicUnitsSection p (PadicInt.unitsToZModPow (padicUnitsDepth p) x))⁻¹ * x ∈
      unitsPrincipal p (padicUnitsDepth p) := by
  rw [← unitsToZModPow_eq_one_iff, map_mul, map_inv, unitsToZModPow_padicUnitsSection,
    inv_mul_cancel]

variable (p) in
/-- The decomposition of `ℤ_pˣ`, as a multiplicative equivalence. -/
private noncomputable def padicIntUnitsMulEquivZModUnitsProd :
    ℤ_[p]ˣ ≃* (ZMod (p ^ padicUnitsDepth p))ˣ × Multiplicative ℤ_[p] where
  toFun x := (PadicInt.unitsToZModPow (padicUnitsDepth p) x,
    unitsPrincipalLogEquiv p ⟨_, inv_padicUnitsSection_mul_mem x⟩)
  invFun y := padicUnitsSection p y.1 * ((unitsPrincipalLogEquiv p).symm y.2 : ℤ_[p]ˣ)
  left_inv x := by
    simp only [ContinuousMulEquiv.symm_apply_apply, mul_inv_cancel_left]
  right_inv := by
    rintro ⟨δ, s⟩
    have hr : PadicInt.unitsToZModPow (padicUnitsDepth p)
        (padicUnitsSection p δ * ((unitsPrincipalLogEquiv p).symm s : ℤ_[p]ˣ)) = δ := by
      rw [map_mul, unitsToZModPow_padicUnitsSection,
        unitsToZModPow_eq_one_iff.mpr ((unitsPrincipalLogEquiv p).symm s).2, mul_one]
    refine Prod.ext hr ?_
    convert (unitsPrincipalLogEquiv p).apply_symm_apply s using 2
    exact Subtype.ext (by simp only [hr, inv_mul_cancel_left])
  map_mul' x y := by
    refine Prod.ext (map_mul _ x y) ?_
    simp only [Prod.snd_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp only [map_mul, mul_inv, Subgroup.coe_mul, mul_mul_mul_comm])

variable (p) in
/-- **The decomposition `ℤ_pˣ ≃ₜ* (ℤ/qℤ)ˣ × ℤ_p`.** A unit `x` goes to its residue `x mod q`
together with `log (x / ω(x mod q)) / q`, where `ω` is `TauCeti.padicUnitsSection p`; the inverse
is `(δ, s) ↦ ω(δ) exp(q s)`. -/
noncomputable def padicIntUnitsEquivZModUnitsProd :
    ℤ_[p]ˣ ≃ₜ* (ZMod (p ^ padicUnitsDepth p))ˣ × Multiplicative ℤ_[p] :=
  have he : Continuous (padicIntUnitsMulEquivZModUnitsProd p) := by
    have hr := (PadicInt.unitsToZModPow (p := p) (padicUnitsDepth p)).continuous
    refine hr.prodMk ((unitsPrincipalLogEquiv p).continuous.comp (Continuous.subtype_mk ?_ _))
    exact ((continuous_of_discreteTopology (f := padicUnitsSection p)).comp hr).inv.mul
      continuous_id
  -- A continuous bijection from a compact space to a Hausdorff space is a homeomorphism.
  ContinuousMulEquiv.mk (padicIntUnitsMulEquivZModUnitsProd p) he
    (he.continuous_symm_of_equiv_compact_to_t2
      (f := (padicIntUnitsMulEquivZModUnitsProd p).toEquiv))

@[simp]
theorem padicIntUnitsEquivZModUnitsProd_apply_fst (x : ℤ_[p]ˣ) :
    (padicIntUnitsEquivZModUnitsProd p x).1 = PadicInt.unitsToZModPow (padicUnitsDepth p) x :=
  (rfl)

@[simp]
theorem coe_padicIntUnitsEquivZModUnitsProd_apply_snd (x : ℤ_[p]ˣ) :
    ((padicIntUnitsEquivZModUnitsProd p x).2.toAdd : ℚ_[p]) =
      log ((((padicUnitsSection p (PadicInt.unitsToZModPow (padicUnitsDepth p) x))⁻¹ * x :
        ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ padicUnitsDepth p :=
  coe_unitsPrincipalLogEquiv_apply _

@[simp]
theorem padicIntUnitsEquivZModUnitsProd_symm_apply
    (y : (ZMod (p ^ padicUnitsDepth p))ˣ × Multiplicative ℤ_[p]) :
    (padicIntUnitsEquivZModUnitsProd p).symm y =
      padicUnitsSection p y.1 * ((unitsPrincipalLogEquiv p).symm y.2 : ℤ_[p]ˣ) :=
  (rfl)

/-- **The decomposition sends `γ = exp q` to `(1, 1)`.** -/
@[simp]
theorem padicIntUnitsEquivZModUnitsProd_padicUnitsGenerator :
    padicIntUnitsEquivZModUnitsProd p (padicUnitsGenerator p) = (1, .ofAdd 1) := by
  rw [← (padicIntUnitsEquivZModUnitsProd p).apply_symm_apply (1, .ofAdd 1),
    padicIntUnitsEquivZModUnitsProd_symm_apply, map_one, one_mul, padicUnitsGenerator]

/-- **Uniqueness of the decomposition.** A continuous homomorphism
`ℤ_pˣ → (ℤ/qℤ)ˣ × ℤ_p` whose first component is reduction modulo `q` and which sends
`γ = exp q` to an element with second component `1` is `padicIntUnitsEquivZModUnitsProd p`. -/
theorem eq_padicIntUnitsEquivZModUnitsProd
    (e : ℤ_[p]ˣ →ₜ* (ZMod (p ^ padicUnitsDepth p))ˣ × Multiplicative ℤ_[p])
    (he : ∀ x, (e x).1 = PadicInt.unitsToZModPow (padicUnitsDepth p) x)
    (hγ : (e (padicUnitsGenerator p)).2 = .ofAdd 1) :
    ⇑e = padicIntUnitsEquivZModUnitsProd p := by
  set E := padicIntUnitsEquivZModUnitsProd p
  let φ : ℤ_[p]ˣ →* Multiplicative ℤ_[p] := (MonoidHom.snd _ _).comp e.toMonoidHom
  let ψ : ℤ_[p]ˣ →* Multiplicative ℤ_[p] := (MonoidHom.snd _ _).comp E.toMonoidHom
  have hφ : Continuous φ := continuous_snd.comp e.continuous
  have hψ : Continuous ψ := continuous_snd.comp E.continuous
  -- The second components agree on `γ`, hence on the closed subgroup `1 + qℤ_p` it generates.
  have hU : ∀ u ∈ unitsPrincipal p (padicUnitsDepth p), φ u = ψ u := by
    have h : Set.EqOn φ ψ (Subgroup.zpowers (padicUnitsGenerator p)) := by
      rintro _ ⟨n, rfl⟩
      simp [φ, ψ, E, hγ]
    have h' := h.closure hφ hψ
    rw [← Subgroup.topologicalClosure_coe, topologicalClosure_zpowers_padicUnitsGenerator] at h'
    exact fun u hu ↦ h' hu
  -- Every unit has a power in `1 + qℤ_p`, and `ℤ_[p]` is torsion-free.
  funext x
  refine Prod.ext (by rw [he, padicIntUnitsEquivZModUnitsProd_apply_fst]) ?_
  have hx : x ^ Nat.card (ZMod (p ^ padicUnitsDepth p))ˣ ∈
      unitsPrincipal p (padicUnitsDepth p) := by
    rw [← unitsToZModPow_eq_one_iff, map_pow, pow_card_eq_one']
  have h := hU _ hx
  rw [map_pow, map_pow] at h
  replace h := congrArg Multiplicative.toAdd h
  rw [toAdd_pow, toAdd_pow] at h
  exact Multiplicative.toAdd.injective
    (nsmul_right_injective (Nat.card_pos (α := (ZMod (p ^ padicUnitsDepth p))ˣ)).ne' h)

end TauCeti
