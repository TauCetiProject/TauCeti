/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.ConstantTerm
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO
import Mathlib.Analysis.Normed.Group.Tannery
import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis

/-!
# Constant terms of primitive residue-class Eisenstein series

Mathlib's `eisensteinSeries` sums over primitive integer pairs in a specified residue class.
The main result is `disjoint_primitiveEisensteinSubspace_cuspFormSubmodule`; the span has the
generator introduction rule `mem_primitiveEisensteinSubspace` and the finite-sum
characterization `mem_primitiveEisensteinSubspace_iff`.

Only the pairs `(0, 1)` and `(0, -1)` survive at infinity. Consequently its constant term at
the cusp represented by `γ` detects the residue of the bottom row of `γ⁻¹`, with the sign
`(-1)^k` for its negative. These constant terms show that every cuspidal element of the
primitive Eisenstein span is zero.

This gives the directness input for cusp–Eisenstein decompositions without choosing cusp
representatives or assuming that the Eisenstein series span the noncuspidal quotient.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §4.2.

The convergence argument uses Chris Birkbeck's Mathlib Eisenstein-series summability and
vertical-strip estimates, and the summand limit in `EisensteinSeries.ConstantTerm`.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup Filter Complex
open UpperHalfPlane hiding I
open _root_.EisensteinSeries
open scoped MatrixGroups Topology

namespace TauCeti.EisensteinSeries

variable {N : ℕ} {k : ℤ}

private lemma primitive_row_tsum (a : Fin 2 → ZMod N) :
    (∑' x : gammaSet N 1 a, if x.1 0 = 0 then (x.1 1 : ℂ) ^ (-k) else 0) =
      (if a = ![0, 1] then 1 else 0) +
        (if a = ![0, -1] then (-1 : ℂ) ^ k else 0) := by
  classical
  have hpos : ((↑) ∘ (![0, 1] : Fin 2 → ℤ) : Fin 2 → ZMod N) = ![0, 1] := by
    ext i; fin_cases i <;> simp
  have hneg : ((↑) ∘ (![0, -1] : Fin 2 → ℤ) : Fin 2 → ZMod N) = ![0, -1] := by
    ext i; fin_cases i <;> simp
  rw [tsum_subtype (gammaSet N 1 a) (fun x : Fin 2 → ℤ ↦
    if x 0 = 0 then (x 1 : ℂ) ^ (-k) else 0)]
  have hfun : (fun x : Fin 2 → ℤ ↦
      if x ∈ gammaSet N 1 a then
        if x 0 = 0 then (x 1 : ℂ) ^ (-k) else 0 else 0) =
      fun x ↦ (if x = ![0, 1] then (if a = ![0, 1] then 1 else 0) else 0) +
        (if x = ![0, -1] then (if a = ![0, -1] then (-1 : ℂ) ^ k else 0) else 0) := by
    funext x
    by_cases hx : x ∈ gammaSet N 1 a
    · by_cases h0 : x 0 = 0
      · have h1 : x 1 = 1 ∨ x 1 = -1 := by
          have hg := hx.2
          simp only [h0, Int.gcd_zero_left] at hg
          exact Int.natAbs_eq_iff.mp hg
        rcases h1 with h1 | h1
        all_goals
          have heq : x = ![0, x 1] := by ext i; fin_cases i <;> simp [h0]
          have ha := hx.1
          rw [heq, h1] at ha ⊢
          first | rw [hpos] at ha | rw [hneg] at ha
          rw [← ha]
          simp [gammaSet, hpos, hneg, zpow_neg, ← inv_zpow]
      · have hp : x ≠ ![0, 1] := fun h ↦ h0 (by simp [h])
        have hm : x ≠ ![0, -1] := fun h ↦ h0 (by simp [h])
        simp [hx, h0, hp, hm]
    · by_cases hp : x = ![0, 1]
      · subst x
        have ha : a ≠ ![0, 1] := by simpa [gammaSet, hpos, hneg, eq_comm] using hx
        simp [hx, ha]
      · by_cases hm : x = ![0, -1]
        · subst x
          have ha : a ≠ ![0, -1] := by simpa [gammaSet, hpos, hneg, eq_comm] using hx
          simp [hx, ha]
        · simp [hx, hp, hm]
  simp only [Set.indicator_apply]
  rw [hfun, tsum_eq_sum (s := {![0, 1], ![0, -1]}) (by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [hb.1, hb.2])]
  simp

variable [NeZero N]

/-- The underlying function of the bundled primitive residue-class Eisenstein series. -/
@[simp]
theorem coe_eisensteinSeriesMF (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ⇑(eisensteinSeriesMF hk a) = eisensteinSeries a k := (rfl)

/-- At infinity, a primitive residue-class Eisenstein series has constant term `1` for the
residue `(0, 1)` and `(-1)^k` for `(0, -1)`, adding both if the residues coincide. -/
theorem tendsto_eisensteinSeries_atImInfty (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    Tendsto (eisensteinSeries a k) atImInfty
      (𝓝 ((if a = ![0, 1] then 1 else 0) +
        (if a = ![0, -1] then (-1 : ℂ) ^ k else 0))) := by
  classical
  have hk' : (2 : ℝ) < k := by exact_mod_cast (by omega : (2 : ℤ) < k)
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hkpos : 0 < k := by omega
  have hlim := TauCeti.ModularFormClass.tendsto_valueAtInfty
    (eisensteinSeriesMF hk a) hN (by simp)
  rw [coe_eisensteinSeriesMF] at hlim
  have hrow : Tendsto (fun t : ℝ ↦ eisensteinSeries a k (ofComplex (I * t))) atTop
      (𝓝 (∑' x : gammaSet N 1 a, if x.1 0 = 0 then (x.1 1 : ℂ) ^ (-k) else 0)) := by
    simp only [eisensteinSeries]
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun x : gammaSet N 1 a ↦ r ⟨⟨0, 1⟩, one_pos⟩ ^ (-k : ℝ) *
        ‖x.1‖ ^ (-k : ℝ))
      (((summable_one_div_norm_rpow hk').subtype _).mul_left _)
      (fun x ↦ tendsto_eisSummand_ofComplex_I_mul hkpos x.1) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht x
    have hz : (ofComplex (I * t) : ℍ) ∈ verticalStrip 0 1 := by
      rw [ofComplex_apply_of_im_pos (by simpa using zero_lt_one.trans_le ht)]
      simpa [verticalStrip] using ht
    simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
      Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) x.1 one_pos hz
  rw [primitive_row_tsum a] at hrow
  have hvalue := tendsto_nhds_unique hrow
    (hlim.comp tendsto_ofComplex_I_mul_atTop_atImInfty)
  exact hvalue ▸ hlim

/-- The value at infinity of a primitive residue-class Eisenstein series. -/
@[simp]
theorem valueAtInfty_eisensteinSeries (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    valueAtInfty (eisensteinSeries a k) =
      (if a = ![0, 1] then 1 else 0) +
        (if a = ![0, -1] then (-1 : ℂ) ^ k else 0) :=
  (tendsto_eisensteinSeries_atImInfty hk a).limUnder_eq

/-- The constant term at an arbitrary cusp is determined by the residue of the bottom row
of the inverse cusp representative. -/
theorem constantTermAt_eisensteinSeriesMF (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
    (γ : SL(2, ℤ)) :
    constantTermAt γ (eisensteinSeriesMF hk a) =
      (if a ᵥ* γ = ![0, 1] then 1 else 0) +
        (if a ᵥ* γ = ![0, -1] then (-1 : ℂ) ^ k else 0) := by
  have h : eisensteinSeries a k ∣[k] mapGL ℝ γ = eisensteinSeries a k ∣[k] γ :=
    (SL_slash _ γ).symm
  rw [constantTermAt_eq_valueAtInfty, coe_translate, coe_eisensteinSeriesMF]
  rw [h]
  rw [eisensteinSeries_slash_apply, valueAtInfty_eisensteinSeries hk]

/-- Negating the residue class multiplies the primitive Eisenstein series by `(-1)^k`. -/
@[simp]
theorem eisensteinSeriesMF_neg (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    eisensteinSeriesMF hk (-a) = (-1 : ℂ) ^ k • eisensteinSeriesMF hk a := by
  have h := eisensteinSeries_slash_apply a k (-1 : SL(2, ℤ))
  have hGL : toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) (-1 : SL(2, ℤ))) = -1 :=
    Matrix.SpecialLinearGroup.mapGL_neg_one
  have hres : a ᵥ* (-1 : SL(2, ℤ)) = -a := by
    ext i
    fin_cases i <;> simp [vecMul, dotProduct]
  rw [SL_slash, hGL, ModularForm.slash_neg_one, hres] at h
  apply DFunLike.coe_injective
  simpa only [FunLike.coe_smul, coe_eisensteinSeriesMF] using h.symm

/-- A residue class with no primitive integral lift has zero Eisenstein series. -/
@[simp]
theorem eisensteinSeriesMF_eq_zero_of_isEmpty (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
    [IsEmpty (gammaSet N 1 a)] : eisensteinSeriesMF hk a = 0 := by
  ext z
  simp only [coe_eisensteinSeriesMF, FunLike.coe_zero, Pi.zero_apply,
    eisensteinSeries, tsum_empty]

private lemma coefficient_relation_of_cuspidal (hk : 3 ≤ k)
    (c : (Fin 2 → ZMod N) → ℂ)
    (hc : (∑ a, c a • eisensteinSeriesMF hk a) ∈ cuspFormSubmodule Γ(N) k)
    (a : Fin 2 → ZMod N) (ha : Nonempty (gammaSet N 1 a)) :
    c a + (-1 : ℂ) ^ k * c (-a) = 0 := by
  classical
  obtain ⟨x, hx⟩ := ha
  obtain ⟨σ, hσ0, hσ1⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr hx.2).exists_SL2_row 1
  have hpos : (![0, 1] : Fin 2 → ZMod N) ᵥ* σ = a := by
    ext i
    fin_cases i <;> simpa [vecMul, dotProduct, hσ0, hσ1] using congrFun hx.1 _
  have hneg : (![0, -1] : Fin 2 → ZMod N) ᵥ* σ = -a := by
    have hsign : (![0, -1] : Fin 2 → ZMod N) = -![0, 1] := by
      ext i; fin_cases i <;> simp
    rw [hsign, neg_vecMul, hpos]
  let τ := SpecialLinearGroup.map (Int.castRingHom (ZMod N)) σ
  have hmul (v : Fin 2 → ZMod N) : (v ᵥ* (↑(τ⁻¹) : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      (↑τ : Matrix (Fin 2) (Fin 2) (ZMod N)) = v := by
    calc
      (v ᵥ* (↑(τ⁻¹) : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
          (↑τ : Matrix (Fin 2) (Fin 2) (ZMod N)) =
          v ᵥ* ((τ⁻¹ * τ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) :=
        vecMul_vecMul _ _ _
      _ = v := by simp
  have hinj : Function.Injective (fun v : Fin 2 → ZMod N ↦
      v ᵥ* (↑τ : Matrix (Fin 2) (Fin 2) (ZMod N))) :=
    Matrix.vecMul_injective_of_isUnit ⟨toGL τ, rfl⟩
  have hiffτ (b y : Fin 2 → ZMod N) :
      b ᵥ* (↑(τ⁻¹) : Matrix (Fin 2) (Fin 2) (ZMod N)) = y ↔
        b = y ᵥ* (↑τ : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    exact ⟨fun h ↦ by rw [← hmul b, h], fun h ↦ hinj ((hmul b).trans h)⟩
  have hiff (b y : Fin 2 → ZMod N) :
      b ᵥ* (σ⁻¹ : SL(2, ℤ)) = y ↔ b = y ᵥ* σ := by
    simpa only [map_inv] using hiffτ b y
  have H := (mem_cuspFormSubmodule_iff_constantTermAt_eq_zero _).mp hc σ⁻¹
  simp only [map_sum, map_smul, constantTermAt_eisensteinSeriesMF,
    hiff, hpos, hneg, smul_eq_mul, mul_add] at H
  simpa [Finset.sum_add_distrib, mul_comm] using H

/-- The span of Mathlib's primitive residue-class Eisenstein series of level `Γ(N)` and
weight `k ≥ 3`. -/
def primitiveEisensteinSubspace (N : ℕ) [NeZero N] (hk : 3 ≤ k) :
    Submodule ℂ (ModularForm Γ(N) k) :=
  Submodule.span ℂ (Set.range (eisensteinSeriesMF hk))

/-- The defining span of the primitive Eisenstein subspace. -/
theorem primitiveEisensteinSubspace_def (hk : 3 ≤ k) :
    primitiveEisensteinSubspace N hk =
      Submodule.span ℂ (Set.range (eisensteinSeriesMF hk)) := (rfl)

/-- Each primitive residue-class series belongs to the primitive Eisenstein span. -/
theorem mem_primitiveEisensteinSubspace (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    eisensteinSeriesMF hk a ∈ primitiveEisensteinSubspace N hk := by
  rw [primitiveEisensteinSubspace_def]
  exact Submodule.subset_span ⟨a, rfl⟩

/-- Membership in the primitive Eisenstein span is equivalent to a finite sum indexed by
residue pairs modulo `N`. -/
theorem mem_primitiveEisensteinSubspace_iff (hk : 3 ≤ k) (f : ModularForm Γ(N) k) :
    f ∈ primitiveEisensteinSubspace N hk ↔
      ∃ c : (Fin 2 → ZMod N) → ℂ, ∑ a, c a • eisensteinSeriesMF hk a = f := by
  rw [primitiveEisensteinSubspace_def]
  exact Submodule.mem_span_range_iff_exists_fun ℂ

/-- A subspace containing every primitive residue-class Eisenstein series contains their span. -/
theorem primitiveEisensteinSubspace_le (hk : 3 ≤ k)
    {V : Submodule ℂ (ModularForm Γ(N) k)}
    (hV : ∀ a : Fin 2 → ZMod N, eisensteinSeriesMF hk a ∈ V) :
    primitiveEisensteinSubspace N hk ≤ V := by
  rw [primitiveEisensteinSubspace_def, Submodule.span_le, Set.range_subset_iff]
  exact hV

/-- A cuspidal linear combination of primitive residue-class Eisenstein series is zero. -/
private theorem eq_zero_of_mem_primitiveEisensteinSubspace_of_cuspidal (hk : 3 ≤ k)
    {f : ModularForm Γ(N) k} (hf : f ∈ primitiveEisensteinSubspace N hk)
    (hc : f ∈ cuspFormSubmodule Γ(N) k) : f = 0 := by
  classical
  obtain ⟨c, rfl⟩ := (mem_primitiveEisensteinSubspace_iff hk f).mp hf
  have hterm (a : Fin 2 → ZMod N) :
      (c a + (-1 : ℂ) ^ k * c (-a)) • eisensteinSeriesMF hk a = 0 := by
    rcases isEmpty_or_nonempty (gammaSet N 1 a) with ha | ha
    · let := ha
      rw [eisensteinSeriesMF_eq_zero_of_isEmpty, smul_zero]
    · rw [coefficient_relation_of_cuspidal hk c hc a ha, zero_smul]
  have hsum : ∑ a, c (-a) • eisensteinSeriesMF hk (-a) =
      ∑ a, c a • eisensteinSeriesMF hk a :=
    Fintype.sum_equiv (Equiv.neg (Fin 2 → ZMod N)) _ _ (fun _ ↦ rfl)
  have H := Finset.sum_eq_zero (s := Finset.univ) (fun a _ ↦ hterm a)
  simp only [add_smul, mul_smul, Finset.sum_add_distrib,
    smul_comm ((-1 : ℂ) ^ k), ← eisensteinSeriesMF_neg] at H
  rw [hsum] at H
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  rw [← two_smul ℂ, smul_eq_zero_iff_right htwo] at H
  exact H

/-- The primitive Eisenstein span and the cusp-form submodule have zero intersection. -/
theorem disjoint_primitiveEisensteinSubspace_cuspFormSubmodule (hk : 3 ≤ k) :
    Disjoint (primitiveEisensteinSubspace N hk) (cuspFormSubmodule Γ(N) k) := by
  rw [Submodule.disjoint_def]
  intro f hf hc
  exact eq_zero_of_mem_primitiveEisensteinSubspace_of_cuspidal hk hf hc

end TauCeti.EisensteinSeries
