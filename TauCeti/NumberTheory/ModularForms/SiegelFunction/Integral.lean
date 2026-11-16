/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.QExpansion
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.LinearAlgebra.Matrix.RationalVector
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.Cyclotomic.Adjoin
import TauCeti.NumberTheory.ModularForms.LevelOne.Invariant
import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO
import TauCeti.RingTheory.HahnSeries.Multiplication
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integrality of Siegel functions over `ℤ[j]`

For any positive level `N`, the `(12 N)`-th powers `g_{v/N}^{12 N}` attached to the nonzero
row vectors `v ∈ (ℤ/Nℤ)² \ {0}` are permuted by `SL₂(ℤ)`, multiply to the constant `N^{12 N}`,
and form the roots of a monic polynomial over `ℤ[j]`. Consequently, whenever the modular invariant
`j` (or its value `j(τ)` at a point `τ ∈ ℍ`) is integral over a commutative ring `R`, every
rational-parameter Siegel function `g_r` (`r ∈ ℚ²`) and every scaled reciprocal `N / g_{a/N}`
(`N : ℕ`, `a ∈ ℤ²`) is integral over `R`, both in the ring `ℍ → ℂ` of functions on the upper
half-plane and pointwise in `ℂ`. At integral parameters `r ∈ ℤ²` (or `N = 0`), `g_r` and
`N / g_{a/N}` vanish identically on `ℍ`, so no non-integrality side condition is needed.

The proof combines three ingredients from `SiegelFunction.QExpansion` and `LevelOne`:
* On `S = (ℤ/Nℤ)² \ {0}`, the sum of the `q_N`-orders `siegelCuspOrder N v = 6 N² B₂({v₀ / N})`
  vanishes and the leading `q_N`-coefficients multiply to `N^{12 N}`, so the holomorphic
  `SL₂(ℤ)`-invariant product `∏_{v ∈ S} g_{v/N}^{12 N}` tends to `N^{12 N}` at `i∞` and is
  therefore equal to `N^{12 N}` (`levelOne_eq_of_tendsto_atImInfty`).
* Every elementary symmetric function of `{g_{v/N}^{12 N} | v ∈ S}` is holomorphic on `ℍ`,
  `SL₂(ℤ)`-invariant, and meromorphic at `i∞`. Its `q_N`-expansion coefficients lie in `ℤ[ζ_N]`
  and are fixed under `ζ_N ↦ ζ_N^u` (`u ∈ (ℤ/Nℤ)ˣ`) because `v ↦ (v₀, u v₁)` permutes `S`, so
  cyclotomic Galois descent lands them in `ℤ`; `exists_aeval_j_eq` then expresses each elementary
  symmetric function as a polynomial in `j` over `ℤ`.
* From the resulting monic equation over `ℤ[j]`, integrality of `g_{a/N}` follows by taking
  `(12 N)`-th roots, while `(N / g_{v/N})^{12 N} = ∏_{w ∈ S \ {v}} g_{w/N}^{12 N}` gives the
  integrality of `N / g_{a/N}` directly from the product identity. Pointwise integrality at
  `τ ∈ ℍ` descends uniformly from function-level integrality over `ℤ[j]` via
  `isIntegral_apply_of_isIntegral_adjoin_j`.

The level-two specializations for `g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}`, and
`g₂ = g_{(1/2, 1/2)}` and their scaled reciprocals `2 / gᵢ` are recorded at the end of the file.

## Main results

* `TauCeti.ModularForm.prod_siegelFunction_div_pow_twelve_mul_eq`:
  `∏_{v ∈ (ℤ/Nℤ)² \ {0}} g_{v/N}(τ)^{12 N} = N^{12 N}`.
* `TauCeti.ModularForm.exists_monic_map_aeval_j_eq_prod_X_sub_C_siegelFunction_div_pow_twelve_mul`:
  existence of a monic polynomial `Φ ∈ (ℤ[X])[X]` whose specialization at `j(τ)` equals
  `∏_{v ∈ (ℤ/Nℤ)² \ {0}} (X - g_{v/N}(τ)^{12 N})`.
* `TauCeti.ModularForm.isIntegral_siegelFunction_div`,
  `TauCeti.ModularForm.isIntegral_siegelFunction_ratCast`,
  `TauCeti.ModularForm.isIntegral_natCast_div_siegelFunction_div`: integrality of `g_{a/N}`, `g_r`
  (`r ∈ ℚ²`), and `N / g_{a/N}` as functions on `ℍ` over any ring over which `j` is integral.
* `TauCeti.ModularForm.isIntegral_apply_of_isIntegral_adjoin_j`,
  `TauCeti.ModularForm.isIntegral_siegelFunction_div_apply`,
  `TauCeti.ModularForm.isIntegral_siegelFunction_ratCast_apply`,
  `TauCeti.ModularForm.isIntegral_natCast_div_siegelFunction_div_apply`: evaluation descent from
  integrality over `ℤ[j]` and the corresponding pointwise integrality results at `τ ∈ ℍ` over any
  ring over which `j(τ)` is integral.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §§1–2 (integrality of Siegel functions over `ℤ[j]` and the product of division
  values).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 5.
* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber functions).
-/

public section

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real Matrix MatrixGroups Manifold ModularForm Polynomial

namespace TauCeti.ModularForm

/-! ### `SL₂(ℤ)`-permutation of division indices and the full-level product identity -/

/-- `g_{v/N}^{12 N}` packaged as an element of `UpperHalfPlane.meromorphicAtCuspSubring N`. -/
private noncomputable def siegelPowerMem (N : ℕ) (v : Fin 2 → ZMod N) :
    UpperHalfPlane.meromorphicAtCuspSubring N :=
  ⟨fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N), by
    simpa only [UpperHalfPlane.mem_meromorphicAtCuspSubring, one_smul, Int.cast_natCast] using
      meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N
        (fun i ↦ ((v i).val : ℤ)) 1⟩

@[simp]
private theorem siegelPowerMem_coe (N : ℕ) (v : Fin 2 → ZMod N) :
    (siegelPowerMem N v : ℍ → ℂ) =
      fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) :=
  rfl

private theorem mem_erase_zero_of_map_zero {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Zero α] [Zero β] (e : α ≃ β) (h0 : e 0 = 0) (x : α) :
    x ∈ (Finset.univ : Finset α).erase 0 ↔ e x ∈ (Finset.univ : Finset β).erase 0 := by
  rw [Finset.mem_erase, Finset.mem_erase]
  simp only [Finset.mem_univ, and_true]
  exact ⟨fun hx h ↦ hx (e.injective (h.trans h0.symm)), fun hx h ↦ hx (h ▸ h0)⟩

private theorem siegelFunction_zmod_pow_twelve_mul_smul {N k : ℕ} [NeZero N] (hk : N ∣ 6 * k)
    (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    siegelFunction (fun i ↦ ((v i).val : ℝ) / N) ↑(γ • τ) ^ (12 * k) =
      siegelFunction (fun i ↦
        (((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).vecMulEquiv v i).val :
          ℝ) / N) τ ^ (12 * k) := by
  set a : Fin 2 → ℤ := fun i ↦ (v i).val
  have ha : (fun i ↦ ((v i).val : ℝ) / N) = fun i ↦ (a i : ℝ) / N := by
    ext i; simp [a]
  have hzmod : ∀ j, ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ZMod N) =
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).vecMulEquiv v j := fun j ↦ by
    simp [a, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [ha, siegelFunction_div_pow_twelve_mul_smul_eq_zmod hk a γ τ]
  congr 3
  ext j
  rw [hzmod j]

private theorem prod_leadingCoeff_zero_first {N : ℕ} [NeZero N] :
    ∏ v ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).filter (fun v ↦ v 0 = 0),
        (cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
          (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1)) =
      (N : ℂ) ^ (12 * N) := by
  set ζ := cexp (2 * π * I / N)
  have hbij :
      ∏ v ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).filter (fun v ↦ v 0 = 0),
          (ζ ^ (6 * (v 0).val * (v 1).val) *
            (if v 0 = 0 then (1 - ζ ^ (v 1).val) ^ (12 * N) else 1)) =
        ∏ y ∈ (Finset.univ : Finset (ZMod N)).erase 0, (1 - ζ ^ y.val) ^ (12 * N) := by
    symm
    refine Finset.prod_bij (fun y _ ↦ ![0, y]) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨fun h0 ↦ (Finset.mem_erase.mp hy).1 ?_, Finset.mem_univ _⟩, rfl⟩
      simpa using congrFun h0 1
    · intro y₁ _ y₂ _ h
      simpa using congrFun h 1
    · intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvS, hv0⟩
      refine ⟨v 1, Finset.mem_erase.mpr ⟨fun hv1 ↦ (Finset.mem_erase.mp hvS).1 ?_,
        Finset.mem_univ _⟩, ?_⟩
      · ext i; fin_cases i <;> assumption
      · ext i; fin_cases i <;> simp [hv0]
    · intro y _; simp
  rw [hbij, Finset.prod_pow]
  have hfin : ∏ y ∈ (Finset.univ : Finset (ZMod N)).erase 0, (1 - ζ ^ y.val) =
      ∏ k ∈ Finset.range (N - 1), (1 - ζ ^ (k + 1)) := by
    rw [← Finset.prod_equiv (ZMod.finEquiv N).toEquiv
      (s := (Finset.univ : Finset (Fin N)).erase 0)
      (t := (Finset.univ : Finset (ZMod N)).erase 0)
      (f := fun k : Fin N ↦ 1 - ζ ^ (k : ℕ))
      (fun k ↦ mem_erase_zero_of_map_zero (ZMod.finEquiv N).toEquiv (map_zero (ZMod.finEquiv N)) k)
      (fun k _ ↦ by simp [ZMod.val_natCast_of_lt k.isLt])]
    symm
    refine Finset.prod_bij
      (fun k hk ↦ (⟨k + 1, by
        have := Finset.mem_range.mp hk
        have := NeZero.pos N
        omega⟩ : Fin N)) ?_ ?_ ?_ ?_
    · intro k _; simp [Fin.ext_iff]
    · intro k₁ _ k₂ _ h; exact Nat.succ.inj (congrArg Fin.val h)
    · intro y hy
      have hy0 : 0 < y.val := Nat.pos_of_ne_zero fun h ↦
        (Finset.mem_erase.mp hy).1 (Fin.ext h)
      exact ⟨y.val - 1, Finset.mem_range.mpr (by have := y.isLt; omega),
        Fin.ext (by dsimp; omega)⟩
    · intro k _; rfl
  rw [hfin]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rw [Nat.succ_sub_one, Nat.succ_eq_add_one,
    (Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)).prod_one_sub_pow_eq_order]
  push_cast
  rfl

private theorem prod_leadingCoeff_ne_zero_first {N : ℕ} [NeZero N] :
    ∏ v ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).filter (fun v ↦ ¬v 0 = 0),
        (cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
          (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1)) =
      1 := by
  set ζ := cexp (2 * π * I / N)
  have hbij :
      ∏ v ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).filter (fun v ↦ ¬v 0 = 0),
          (ζ ^ (6 * (v 0).val * (v 1).val) *
            (if v 0 = 0 then (1 - ζ ^ (v 1).val) ^ (12 * N) else 1)) =
        ∏ x ∈ (Finset.univ : Finset (ZMod N)).erase 0,
          ∏ y : ZMod N, ζ ^ (6 * x.val * y.val) := by
    rw [← Finset.prod_product']
    symm
    refine Finset.prod_bij (fun p _ ↦ ![p.1, p.2]) ?_ ?_ ?_ ?_
    · intro p hp
      have hp1 : p.1 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h0 ↦ hp1 ?_, Finset.mem_univ _⟩, ?_⟩
      · simpa using congrFun h0 0
      · simpa using hp1
    · intro p₁ _ p₂ _ h
      exact Prod.ext (by simpa using congrFun h 0) (by simpa using congrFun h 1)
    · intro v hv
      have hv0 : v 0 ≠ 0 := (Finset.mem_filter.mp hv).2
      exact ⟨(v 0, v 1), Finset.mem_product.mpr
        ⟨Finset.mem_erase.mpr ⟨hv0, Finset.mem_univ _⟩, Finset.mem_univ _⟩,
        by ext i; fin_cases i <;> rfl⟩
    · intro p hp
      have hp1 : p.1 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1
      simp [hp1]
  rw [hbij]
  refine Finset.prod_eq_one fun x _ ↦ ?_
  rw [Finset.prod_pow_eq_pow_sum]
  have hexp : (∑ y : ZMod N, 6 * x.val * y.val) = N * (3 * x.val * (N - 1)) := by
    rw [← Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      (fun k : Fin N ↦ 6 * x.val * (k : ℕ))
      (fun y : ZMod N ↦ 6 * x.val * y.val)
      (fun k ↦ by
        simp [ZMod.val_natCast_of_lt k.isLt]),
      Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ 6 * x.val * k) N, ← Finset.mul_sum]
    calc 6 * x.val * ∑ k ∈ Finset.range N, k
        = 3 * x.val * ((∑ k ∈ Finset.range N, k) * 2) := by ring
      _ = 3 * x.val * (N * (N - 1)) := by rw [Finset.sum_range_id_mul_two]
      _ = N * (3 * x.val * (N - 1)) := by ring
  rw [hexp, pow_mul, (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).pow_eq_one, one_pow]

private theorem analyticAt_and_coeff_zero_prod_siegelPower {N : ℕ} [NeZero N] :
    AnalyticAt ℂ (cuspFunction N
      (∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0, siegelPowerMem N v).1) 0 ∧
      (UpperHalfPlane.laurentQExpansion N
        (∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0, siegelPowerMem N v).1).coeff 0 =
        (N : ℂ) ^ (12 * N) := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set FM : UpperHalfPlane.meromorphicAtCuspSubring N := ∏ v ∈ S, siegelPowerMem N v
  have hFM_mer : MeromorphicAt (cuspFunction N FM.1) 0 :=
    UpperHalfPlane.mem_meromorphicAtCuspSubring.mp FM.2
  have hL : UpperHalfPlane.laurentQExpansion N FM.1 =
      ∏ v ∈ S, UpperHalfPlane.laurentQExpansionRingHom N (siegelPowerMem N v) := by
    rw [← UpperHalfPlane.laurentQExpansionRingHom_apply]
    exact map_prod (UpperHalfPlane.laurentQExpansionRingHom N) (siegelPowerMem N) S
  have hfactor_ord : ∀ v ∈ S,
      (UpperHalfPlane.laurentQExpansionRingHom N (siegelPowerMem N v)).orderTop =
        siegelCuspOrder N v := by
    intro v hv
    have hv0 : (fun i ↦ (((v i).val : ℤ) : ZMod N)) ≠ 0 := by
      simpa [ZMod.natCast_zmod_val] using (Finset.mem_erase.mp hv).1
    have hm := meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul hv0 1
    simp only [one_smul, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one,
      ZMod.natCast_zmod_val, Int.cast_natCast] at hm
    rw [UpperHalfPlane.laurentQExpansionRingHom_apply]
    exact (UpperHalfPlane.orderTop_laurentQExpansion
      (UpperHalfPlane.mem_meromorphicAtCuspSubring.mp (siegelPowerMem N v).2)).trans hm
  have hord : meromorphicOrderAt (cuspFunction N FM.1) 0 = 0 := by
    rw [← UpperHalfPlane.orderTop_laurentQExpansion hFM_mer, hL, HahnSeries.orderTop_prod,
      Finset.sum_congr rfl hfactor_ord, ← WithTop.coe_sum, sum_siegelCuspOrder_erase_zero N,
      WithTop.coe_zero]
  have han : AnalyticAt ℂ (cuspFunction N FM.1) 0 := by
    simpa using UpperHalfPlane.analyticAt_cuspFunction_qParam_pow_mul hFM_mer
      (k := 0) (by simp [hord])
  refine ⟨han, ?_⟩
  have hne : UpperHalfPlane.laurentQExpansion N FM.1 ≠ 0 := by
    rw [← HahnSeries.orderTop_ne_top, UpperHalfPlane.orderTop_laurentQExpansion hFM_mer, hord]
    exact WithTop.zero_ne_top
  have ho0 : (UpperHalfPlane.laurentQExpansion N FM.1).order = 0 :=
    WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero hne).trans
      ((UpperHalfPlane.orderTop_laurentQExpansion hFM_mer).trans hord))
  rw [← ho0, ← HahnSeries.leadingCoeff_eq, hL, HahnSeries.leadingCoeff_prod]
  have hfac : ∀ v ∈ S,
      (UpperHalfPlane.laurentQExpansionRingHom N (siegelPowerMem N v)).leadingCoeff =
        cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
          (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1) := by
    intro v hv
    have hne_v : UpperHalfPlane.laurentQExpansionRingHom N (siegelPowerMem N v) ≠ 0 := by
      rw [← HahnSeries.orderTop_ne_top, hfactor_ord v hv]; exact WithTop.coe_ne_top
    have hov : (UpperHalfPlane.laurentQExpansionRingHom N (siegelPowerMem N v)).order =
        siegelCuspOrder N v :=
      WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero hne_v).trans
        (hfactor_ord v hv))
    rw [HahnSeries.leadingCoeff_eq, hov, UpperHalfPlane.laurentQExpansionRingHom_apply,
      siegelPowerMem_coe]
    exact laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_siegelCuspOrder v
  rw [Finset.prod_congr rfl hfac, ← Finset.prod_filter_mul_prod_filter_not S (fun v ↦ v 0 = 0),
    prod_leadingCoeff_zero_first, prod_leadingCoeff_ne_zero_first, mul_one]

/-- **Product of all nonzero level-`N` Siegel `(12 N)`-th powers.** For every positive integer `N`
and `τ ∈ ℍ`, `∏_{v ∈ (ℤ/Nℤ)² \ {0}} g_{v/N}(τ)^{12 N} = N^{12 N}`. -/
theorem prod_siegelFunction_div_pow_twelve_mul_eq (N : ℕ) [NeZero N] (τ : ℍ) :
    ∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
        siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) =
      (N : ℂ) ^ (12 * N) := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set FM : UpperHalfPlane.meromorphicAtCuspSubring N := ∏ v ∈ S, siegelPowerMem N v
  have hFM_val (z : ℍ) :
      FM.1 z = ∏ v ∈ S, siegelFunction (fun i ↦ ((v i).val : ℝ) / N) z ^ (12 * N) := by
    simp [FM]
  have hFM_mdiff : MDiff FM.1 := by
    have hfun : FM.1 = ∏ v ∈ S, fun z : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) z ^
        (12 * N) := funext fun z ↦ by simpa [Finset.prod_apply] using hFM_val z
    rw [hfun]
    exact MDifferentiable.prod fun v _ ↦ (mdifferentiable_siegelFunction _).pow (12 * N)
  have hinv (γ : SL(2, ℤ)) (z : ℍ) : FM.1 (γ • z) = FM.1 z := by
    rw [hFM_val, hFM_val]
    set e := (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).vecMulEquiv
    exact Finset.prod_equiv e
      (mem_erase_zero_of_map_zero e (Matrix.SpecialLinearGroup.vecMulEquiv_zero _))
      fun v _ ↦ siegelFunction_zmod_pow_twelve_mul_smul (dvd_mul_left N 6) v γ z
  obtain ⟨han, hlead⟩ := analyticAt_and_coeff_zero_prod_siegelPower (N := N)
  have hper1 : Function.Periodic (FM.1 ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun z ↦ by
      rw [← modular_T_smul]
      exact hinv _ z
  have hperN : Function.Periodic (FM.1 ∘ ofComplex) N := by
    simpa using hper1.nat_mul N
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have htend : Tendsto FM.1 atImInfty (𝓝 ((N : ℂ) ^ (12 * N))) := by
    rw [← hlead, UpperHalfPlane.laurentQExpansion_coeff_zero_of_analyticAt han,
      UpperHalfPlane.cuspFunction_apply_zero hNpos han hperN]
    exact TauCeti.UpperHalfPlane.tendsto_valueAtInfty hNpos hperN han
  rw [← hFM_val τ]
  exact levelOne_eq_of_tendsto_atImInfty hFM_mdiff hinv htend τ

/-! ### The monic polynomial over `ℤ[j]` and general integrality -/

/-- Permutation `v ↦ (v₀, u v₁)` of `(ℤ/Nℤ)²` induced by `u ∈ (ℤ/Nℤ)ˣ`. -/
private def diagSecondEquiv {N : ℕ} (u : (ZMod N)ˣ) :
    (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod N) where
  toFun v := ![v 0, (u : ZMod N) * v 1]
  invFun v := ![v 0, (↑u⁻¹ : ZMod N) * v 1]
  left_inv v := by ext i; fin_cases i <;> simp [← mul_assoc]
  right_inv v := by ext i; fin_cases i <;> simp [← mul_assoc]

private theorem diagSecondEquiv_zero {N : ℕ} (u : (ZMod N)ˣ) : diagSecondEquiv u 0 = 0 := by
  ext i; fin_cases i <;> simp [diagSecondEquiv]

private theorem laurentQExpansion_siegelPolyCoeff_mem_range_intCast {N : ℕ} [NeZero N]
    (k : ℕ) (m : ℤ) :
    (UpperHalfPlane.laurentQExpansion N
      (((∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
        (Polynomial.X - Polynomial.C (siegelPowerMem N v))) :
          (UpperHalfPlane.meromorphicAtCuspSubring N)[X]).coeff k).1).coeff m ∈
      (Int.castRingHom ℂ).range := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set Ω : (HahnSeries ℤ ℤ[X])[X] :=
    ∏ v ∈ S, (Polynomial.X - Polynomial.C (siegelPowerLaurentSeries N v))
  set ζ := cexp (2 * π * I / N)
  have hmap (d : ℕ) :
      Ω.map (HahnSeries.mapRingHom (Polynomial.aeval (ζ ^ d)).toRingHom) =
        ∏ v ∈ S, (Polynomial.X - Polynomial.C
          (UpperHalfPlane.laurentQExpansionRingHom N
            (siegelPowerMem N ![v 0, (d : ZMod N) * v 1]))) := by
    simp only [Ω, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [UpperHalfPlane.laurentQExpansionRingHom_apply, siegelPowerMem_coe,
      mapRingHom_aeval_exp_pow_siegelPowerLaurentSeries]
  have hmap1 :
      Ω.map (HahnSeries.mapRingHom (Polynomial.aeval ζ).toRingHom) =
        (∏ v ∈ S, (Polynomial.X - Polynomial.C (siegelPowerMem N v))).map
          (UpperHalfPlane.laurentQExpansionRingHom N) := by
    have h1 := hmap 1
    simp only [pow_one, Nat.cast_one, one_mul, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C] at h1 ⊢
    refine h1.trans (Finset.prod_congr rfl fun v _ ↦ ?_)
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rw [hv]
  have heq : (UpperHalfPlane.laurentQExpansion N
      (((∏ v ∈ S, (Polynomial.X - Polynomial.C (siegelPowerMem N v))) :
        (UpperHalfPlane.meromorphicAtCuspSubring N)[X]).coeff k).1).coeff m =
      Polynomial.aeval ζ ((Ω.coeff k).coeff m) := by
    rw [← UpperHalfPlane.laurentQExpansionRingHom_apply, ← Polynomial.coeff_map, ← hmap1,
      Polynomial.coeff_map, HahnSeries.coeff_mapRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [heq]
  refine (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).aeval_mem_range_intCast
    ((Ω.coeff k).coeff m) fun u ↦ ?_
  have hu : Ω.map (HahnSeries.mapRingHom (Polynomial.aeval (ζ ^ (u : ZMod N).val)).toRingHom) =
      Ω.map (HahnSeries.mapRingHom (Polynomial.aeval ζ).toRingHom) := by
    rw [hmap (u : ZMod N).val, hmap1]
    simp only [ZMod.natCast_zmod_val, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    exact Finset.prod_equiv (diagSecondEquiv u)
      (mem_erase_zero_of_map_zero (diagSecondEquiv u) (diagSecondEquiv_zero u)) fun _ _ ↦ rfl
  simpa only [Polynomial.coeff_map, HahnSeries.coeff_mapRingHom, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] using congrArg (fun P : (LaurentSeries ℂ)[X] ↦ (P.coeff k).coeff m) hu

private theorem mdifferentiable_coeff_prod_X_sub_C {ι : Type*} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, MDiff (f i)) (k : ℕ) :
    MDiff (fun τ : ℍ ↦ ((∏ i ∈ s, (Polynomial.X - Polynomial.C (f i τ))) : ℂ[X]).coeff k) := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    exact mdifferentiable_const
  | cons a t ha ih =>
    have hfa : MDiff (f a) := hf a (Finset.mem_cons_self a t)
    have hft : ∀ i ∈ t, MDiff (f i) := fun i hi ↦ hf i (Finset.mem_cons_of_mem hi)
    cases k with
    | zero =>
      have heq : (fun τ : ℍ ↦ ((∏ i ∈ Finset.cons a t ha,
            (Polynomial.X - Polynomial.C (f i τ))) : ℂ[X]).coeff 0) =
          -(f a * fun τ : ℍ ↦
            ((∏ i ∈ t, (Polynomial.X - Polynomial.C (f i τ))) : ℂ[X]).coeff 0) := by
        funext τ
        simp [Finset.prod_cons, sub_mul]
      rw [heq]
      exact (hfa.mul (ih hft 0)).neg
    | succ k =>
      have heq : (fun τ : ℍ ↦ ((∏ i ∈ Finset.cons a t ha,
            (Polynomial.X - Polynomial.C (f i τ))) : ℂ[X]).coeff (k + 1)) =
          (fun τ : ℍ ↦ ((∏ i ∈ t, (Polynomial.X - Polynomial.C (f i τ))) : ℂ[X]).coeff k) -
            f a * fun τ : ℍ ↦
              ((∏ i ∈ t, (Polynomial.X - Polynomial.C (f i τ))) : ℂ[X]).coeff (k + 1) := by
        funext τ
        simp [Finset.prod_cons, sub_mul, Polynomial.coeff_X_mul]
      rw [heq]
      exact (ih hft k).sub (hfa.mul (ih hft (k + 1)))

private theorem exists_aeval_j_siegelPolyCoeff {N : ℕ} [NeZero N] (k : ℕ) :
    ∃ P : ℤ[X], ∀ τ : ℍ, Polynomial.aeval (j τ) P =
      (((∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
        (Polynomial.X - Polynomial.C (siegelPowerMem N v))) :
          (UpperHalfPlane.meromorphicAtCuspSubring N)[X]).coeff k).1 τ := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set Ψ : (UpperHalfPlane.meromorphicAtCuspSubring N)[X] :=
    ∏ v ∈ S, (Polynomial.X - Polynomial.C (siegelPowerMem N v))
  have hΨ_eval (τ : ℍ) :
      Ψ.map ((Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp
        (UpperHalfPlane.meromorphicAtCuspSubring N).subtype) =
        ∏ v ∈ S, (Polynomial.X - Polynomial.C
          (siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))) := by
    simp [Ψ, Polynomial.map_prod]
  have hΨ_mdiff : MDiff (Ψ.coeff k).1 := by
    have hfun : (Ψ.coeff k).1 =
        fun τ : ℍ ↦ (∏ v ∈ S, (Polynomial.X - Polynomial.C
          (siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)))).coeff k := by
      funext τ
      simpa only [Polynomial.coeff_map, RingHom.comp_apply, Subring.coe_subtype,
        Pi.evalRingHom_apply] using congrArg (fun Q : ℂ[X] ↦ Q.coeff k) (hΨ_eval τ)
    rw [hfun]
    exact mdifferentiable_coeff_prod_X_sub_C S
      (fun v _ ↦ (mdifferentiable_siegelFunction _).pow (12 * N)) k
  have hinv (γ : SL(2, ℤ)) (τ : ℍ) : (Ψ.coeff k).1 (γ • τ) = (Ψ.coeff k).1 τ := by
    have hpoly :
        Ψ.map ((Pi.evalRingHom (fun _ : ℍ ↦ ℂ) (γ • τ)).comp
          (UpperHalfPlane.meromorphicAtCuspSubring N).subtype) =
          Ψ.map ((Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp
            (UpperHalfPlane.meromorphicAtCuspSubring N).subtype) := by
      rw [hΨ_eval, hΨ_eval]
      set e := (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).vecMulEquiv
      refine Finset.prod_equiv e
        (mem_erase_zero_of_map_zero e (Matrix.SpecialLinearGroup.vecMulEquiv_zero _))
        fun v _ ↦ ?_
      rw [siegelFunction_zmod_pow_twelve_mul_smul (dvd_mul_left N 6)]
    simpa only [Polynomial.coeff_map, RingHom.comp_apply, Subring.coe_subtype,
      Pi.evalRingHom_apply] using congrArg (fun Q : ℂ[X] ↦ Q.coeff k) hpoly
  have hper : Function.Periodic ((Ψ.coeff k).1 ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
      rw [← modular_T_smul]
      exact hinv _ τ
  have hmer1 : MeromorphicAt (cuspFunction 1 (Ψ.coeff k).1) 0 :=
    UpperHalfPlane.meromorphicAt_cuspFunction_of_nat_mul one_pos hΨ_mdiff hper (d := N)
      (by simpa only [mul_one] using UpperHalfPlane.mem_meromorphicAtCuspSubring.mp (Ψ.coeff k).2)
  refine exists_aeval_j_eq (R := ℤ) hΨ_mdiff hinv hmer1 fun n _ ↦ ?_
  rw [UpperHalfPlane.laurentQExpansion_coeff_eq_nat_mul hper hmer1 (d := N) n, mul_one,
    algebraMap_int_eq]
  exact laurentQExpansion_siegelPolyCoeff_mem_range_intCast k ((N : ℤ) * n)

/-- **The `(12 N)`-th powers of the nonzero level-`N` Siegel functions satisfy a monic polynomial
over `ℤ[j]`.** There exists a monic polynomial `Φ ∈ (ℤ[X])[X]` whose coefficientwise evaluation
at `j(τ)` equals `∏_{v ∈ (ℤ/Nℤ)² \ {0}} (X - g_{v/N}(τ)^{12 N})` for every `τ ∈ ℍ`. -/
theorem exists_monic_map_aeval_j_eq_prod_X_sub_C_siegelFunction_div_pow_twelve_mul
    (N : ℕ) [NeZero N] :
    ∃ Φ : (ℤ[X])[X], Φ.Monic ∧ ∀ τ : ℍ,
      Φ.map (Polynomial.aeval (j τ)).toRingHom =
        ∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
          (Polynomial.X - Polynomial.C
            (siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))) := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set Ψ : (UpperHalfPlane.meromorphicAtCuspSubring N)[X] :=
    ∏ v ∈ S, (Polynomial.X - Polynomial.C (siegelPowerMem N v))
  choose P hP using fun k : ℕ ↦ exists_aeval_j_siegelPolyCoeff (N := N) k
  set Φ : (ℤ[X])[X] :=
    Polynomial.X ^ S.card + ∑ k ∈ Finset.range S.card, Polynomial.C (P k) * Polynomial.X ^ k
  have hΦ_monic : Φ.Monic :=
    Polynomial.monic_X_pow_add
      (by simp_rw [← Fin.sum_univ_eq_sum_range, Polynomial.degree_sum_fin_lt])
  refine ⟨Φ, hΦ_monic, fun τ ↦ ?_⟩
  set Q := Ψ.map ((Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp
    (UpperHalfPlane.meromorphicAtCuspSubring N).subtype)
  have hQ : Q = ∏ v ∈ S, (Polynomial.X - Polynomial.C
      (siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))) := by
    simp [Q, Ψ, Polynomial.map_prod]
  rw [← hQ]
  have hQ_monic : Q.Monic := by
    rw [hQ]
    exact Polynomial.monic_prod_of_monic _ _ fun v _ ↦ Polynomial.monic_X_sub_C _
  have hQ_deg : Q.natDegree = S.card := by
    rw [hQ, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  ext m
  have hlhs : (Φ.map (Polynomial.aeval (j τ)).toRingHom).coeff m =
      (if m = S.card then 1 else 0) +
        ∑ k ∈ Finset.range S.card, if m = k then (Ψ.coeff k).1 τ else 0 := by
    simp only [Φ, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, hP, mul_ite, mul_one, mul_zero]
    rfl
  rw [hlhs]
  rcases lt_trichotomy m S.card with hm | rfl | hm
  · simp [hm.ne, Finset.mem_range.mpr hm, Q]
  · simp only [↓reduceIte, Finset.sum_ite_eq, Finset.notMem_range_self, add_zero]
    rw [← hQ_deg, ← Polynomial.leadingCoeff, hQ_monic.leadingCoeff]
  · have hm_not : m ∉ Finset.range S.card := by simp [hm.le]
    simp only [hm.ne', ↓reduceIte, Finset.sum_ite_eq, hm_not, add_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hQ_deg.symm ▸ hm)).symm

private theorem rat_eq_div_den_mul (r : Fin 2 → ℚ) :
    (fun i ↦ (r i : ℝ)) =
      fun i ↦
        (![(r 0).num * (r 1).den, (r 1).num * (r 0).den] i : ℝ) /
          (((r 0).den * (r 1).den : ℕ) : ℝ) := by
  have h0 : ((r 0).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (r 0).den_nz
  have h1 : ((r 1).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (r 1).den_nz
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Rat.cast_def]
    push_cast
    exact (mul_div_mul_right ((r 0).num : ℝ) ((r 0).den : ℝ) h1).symm
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Rat.cast_def]
    push_cast
    rw [mul_comm ((r 0).den : ℝ)]
    exact (mul_div_mul_right ((r 1).num : ℝ) ((r 1).den : ℝ) h0).symm

private theorem natCast_div_siegelFunction_div_pow_twelve_mul_eq_prod_erase {N : ℕ} [NeZero N]
    {a : Fin 2 → ℤ} (hv : (fun i ↦ (a i : ZMod N)) ≠ 0) (τ : ℍ) :
    ((N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) ^ (12 * N) =
      ∏ w ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).erase (fun i ↦ (a i : ZMod N)),
        siegelFunction (fun i ↦ ((w i).val : ℝ) / N) τ ^ (12 * N) := by
  set v : Fin 2 → ZMod N := fun i ↦ (a i : ZMod N)
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  have hvS : v ∈ S := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩
  have hne : siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) ≠ 0 := by
    refine pow_ne_zero _ (mt (siegelFunction_div_eq_zero_iff (fun i ↦ ((v i).val : ℤ))
      τ.im_pos).mp ?_)
    simpa [ZMod.natCast_zmod_val] using hv
  rw [div_pow, siegelFunction_div_pow_twelve_mul_eq_zmod (dvd_mul_left N 6) a τ.im_pos,
    ← prod_siegelFunction_div_pow_twelve_mul_eq N τ, ← Finset.mul_prod_erase S _ hvS,
    mul_div_cancel_left₀ _ hne]

/-! ### General integrality of Siegel functions (as functions on `ℍ`) -/

section GeneralFunctions

variable {R : Type*} [CommRing R] [Algebra R (ℍ → ℂ)]

/-- **Every level-`N` Siegel function `g_{a/N}` is integral over any ring over which `j` is
integral.** Take `R = Algebra.adjoin ℤ {j}` for integrality over `ℤ[j]`. -/
theorem isIntegral_siegelFunction_div (N : ℕ) (a : Fin 2 → ℤ) (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have h0 : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / (0 : ℕ)) τ) = 0 := by
      funext τ; simp [div_zero, ← Pi.zero_def]
    rw [h0]; exact isIntegral_zero
  have : NeZero N := ⟨hN⟩
  set v : Fin 2 → ZMod N := fun i ↦ (a i : ZMod N)
  by_cases hv : v = 0
  · obtain ⟨s, hs⟩ := (TauCeti.exists_div_eq_intCast_iff_zmod_eq_zero (K := ℝ) hN a).mpr hv
    have h0 : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ) = 0 := by
      funext τ; rw [hs]; exact siegelFunction_intCast s τ
    rw [h0]; exact isIntegral_zero
  · obtain ⟨Φ, hmon, hΦ⟩ :=
      exists_monic_map_aeval_j_eq_prod_X_sub_C_siegelFunction_div_pow_twelve_mul N
    refine IsIntegral.of_pow (by positivity : 0 < 12 * N) ?_
    have hpow : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ) ^ (12 * N) =
        fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) :=
      funext fun τ ↦ siegelFunction_div_pow_twelve_mul_eq_zmod (dvd_mul_left N 6) a τ.im_pos
    rw [hpow]
    refine TauCeti.isIntegral_of_eval_map_aeval_eq_zero hmon hj ?_
    funext τ
    have hcomp : (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp (Polynomial.aeval j).toRingHom =
        (Polynomial.aeval (j τ)).toRingHom :=
      Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
    rw [Pi.zero_apply, ← Pi.evalRingHom_apply (fun _ : ℍ ↦ ℂ) τ (Polynomial.eval _ _),
      Polynomial.eval_map, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval_map, hΦ τ,
      Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)
      (by simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        Pi.evalRingHom_apply, sub_self])

/-- **Every rational-parameter Siegel function `g_r` (`r ∈ ℚ²`) is integral over any ring over
which `j` is integral.** -/
theorem isIntegral_siegelFunction_ratCast (r : Fin 2 → ℚ) (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction (fun i ↦ (r i : ℝ)) τ) := by
  rw [rat_eq_div_den_mul r]
  exact isIntegral_siegelFunction_div ((r 0).den * (r 1).den)
    ![(r 0).num * (r 1).den, (r 1).num * (r 0).den] hj

/-- **Scaled reciprocal integrality**: `N / g_{a/N}` is integral over any ring over which `j` is
integral. -/
theorem isIntegral_natCast_div_siegelFunction_div (N : ℕ) (a : Fin 2 → ℤ) (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ (N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have h0 : (fun τ : ℍ ↦ ((0 : ℕ) : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / (0 : ℕ)) τ) = 0 :=
      funext fun _ ↦ by simp
    rw [h0]; exact isIntegral_zero
  have : NeZero N := ⟨hN⟩
  set v : Fin 2 → ZMod N := fun i ↦ (a i : ZMod N)
  by_cases hv : v = 0
  · obtain ⟨s, hs⟩ := (TauCeti.exists_div_eq_intCast_iff_zmod_eq_zero (K := ℝ) hN a).mpr hv
    have h0 : (fun τ : ℍ ↦ (N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) = 0 := by
      funext τ; rw [hs, siegelFunction_intCast s τ, div_zero]; rfl
    rw [h0]; exact isIntegral_zero
  · set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
    refine IsIntegral.of_pow (by positivity : 0 < 12 * N) ?_
    have hpow : (fun τ : ℍ ↦ (N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) ^ (12 * N) =
        ∏ w ∈ S.erase v,
          (fun τ : ℍ ↦ siegelFunction (fun i ↦ ((w i).val : ℝ) / N) τ) ^ (12 * N) := by
      funext τ
      simpa only [Pi.pow_apply, Finset.prod_apply] using
        natCast_div_siegelFunction_div_pow_twelve_mul_eq_prod_erase hv τ
    rw [hpow]
    exact IsIntegral.prod _ fun w _ ↦
      (by simpa using (isIntegral_siegelFunction_div N (fun i ↦ ((w i).val : ℤ)) hj).pow (12 * N))

end GeneralFunctions

/-! ### General integrality of Siegel values at `τ ∈ ℍ` -/

private theorem isIntegral_adjoin_j : IsIntegral (Algebra.adjoin ℤ ({j} : Set (ℍ → ℂ))) j :=
  isIntegral_algebraMap
    (x := (⟨j, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin ℤ ({j} : Set (ℍ → ℂ))))

section GeneralValues

variable {R : Type*} [CommRing R] [Algebra R ℂ]

/-- **Pointwise integrality from function-level integrality over `ℤ[j]`.** If `F : ℍ → ℂ` is
integral over `ℤ[j]` and `j(τ)` is integral over `R`, then `F(τ)` is integral over `R`. -/
theorem isIntegral_apply_of_isIntegral_adjoin_j {F : ℍ → ℂ}
    (hF : IsIntegral (Algebra.adjoin ℤ ({j} : Set (ℍ → ℂ))) F) (τ : ℍ)
    (hj : IsIntegral R (j τ)) : IsIntegral R (F τ) :=
  TauCeti.isIntegral_map_of_isIntegral_adjoin_singleton hF
    (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) (RingHom.ext_int _ _) hj

/-- **Pointwise integrality of `g_{a/N}(τ)`**: if `j(τ)` is integral over `R`, then so is
`g_{a/N}(τ)`. In particular, if `j(τ)` is an algebraic integer (`R = ℤ`), then every `g_{a/N}(τ)`
is an algebraic integer. -/
theorem isIntegral_siegelFunction_div_apply (N : ℕ) (a : Fin 2 → ℤ) (τ : ℍ)
    (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction (fun i ↦ (a i : ℝ) / N) τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_siegelFunction_div N a isIntegral_adjoin_j) τ hj

/-- **Pointwise integrality of `g_r(τ)` for `r ∈ ℚ²`**: if `j(τ)` is integral over `R`, then so is
`g_r(τ)`. -/
theorem isIntegral_siegelFunction_ratCast_apply (r : Fin 2 → ℚ) (τ : ℍ) (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction (fun i ↦ (r i : ℝ)) τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_siegelFunction_ratCast r isIntegral_adjoin_j) τ hj

/-- **Pointwise integrality of `N / g_{a/N}(τ)`**: if `j(τ)` is integral over `R`, then so is
`N / g_{a/N}(τ)`. In particular, when `j(τ)` is an algebraic integer and `a ∉ N ℤ²`, `g_{a/N}(τ)`
divides `N` in the ring of algebraic integers. -/
theorem isIntegral_natCast_div_siegelFunction_div_apply (N : ℕ) (a : Fin 2 → ℤ) (τ : ℍ)
    (hj : IsIntegral R (j τ)) :
    IsIntegral R ((N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_natCast_div_siegelFunction_div N a isIntegral_adjoin_j) τ hj

end GeneralValues

/-! ### Level-two specializations -/

private theorem div_two_vec (a b : ℤ) :
    (fun i ↦ (![a, b] i : ℝ) / ((2 : ℕ) : ℝ)) = ![(a : ℝ) / 2, (b : ℝ) / 2] := by
  ext i; fin_cases i <;> simp

section Functions

variable {R : Type*} [CommRing R] [Algebra R (ℍ → ℂ)]

/-- The level-two Siegel function `g₀` is integral over any coefficient ring over which `j`
is integral. Take `R = Algebra.adjoin ℤ {j}` for integrality over `ℤ[j]`. -/
theorem isIntegral_siegelFunction_zero_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![0, 1 / 2] τ) := by
  have h := isIntegral_siegelFunction_div 2 ![0, 1] hj
  rwa [div_two_vec, Int.cast_zero, zero_div, Int.cast_one] at h

/-- The level-two Siegel function `g₁` is integral over any coefficient ring over which `j`
is integral. -/
theorem isIntegral_siegelFunction_half_zero (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![1 / 2, 0] τ) := by
  have h := isIntegral_siegelFunction_div 2 ![1, 0] hj
  rwa [div_two_vec, Int.cast_one, Int.cast_zero, zero_div] at h

/-- The level-two Siegel function `g₂` is integral over any coefficient ring over which `j`
is integral. -/
theorem isIntegral_siegelFunction_half_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![1 / 2, 1 / 2] τ) := by
  have h := isIntegral_siegelFunction_div 2 ![1, 1] hj
  rwa [div_two_vec, Int.cast_one] at h

/-- Twice the inverse of `g₀` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_zero_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![0, 1 / 2] τ) := by
  have h := isIntegral_natCast_div_siegelFunction_div 2 ![0, 1] hj
  rwa [div_two_vec, Int.cast_zero, zero_div, Int.cast_one, Nat.cast_ofNat] at h

/-- Twice the inverse of `g₁` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_half_zero (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![1 / 2, 0] τ) := by
  have h := isIntegral_natCast_div_siegelFunction_div 2 ![1, 0] hj
  rwa [div_two_vec, Int.cast_one, Int.cast_zero, zero_div, Nat.cast_ofNat] at h

/-- Twice the inverse of `g₂` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_half_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![1 / 2, 1 / 2] τ) := by
  have h := isIntegral_natCast_div_siegelFunction_div 2 ![1, 1] hj
  rwa [div_two_vec, Int.cast_one, Nat.cast_ofNat] at h

end Functions

/-! ### Level-two algebraic-integer values -/

section Values

variable {R : Type*} [CommRing R] [Algebra R ℂ] (τ : ℍ)

/-- If `j(τ)` is integral over `R`, so is `g₀(τ)`. In particular this applies with `R = ℤ`. -/
theorem isIntegral_siegelFunction_zero_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![0, 1 / 2] τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_siegelFunction_zero_half isIntegral_adjoin_j) τ hj

/-- If `j(τ)` is integral over `R`, so is `g₁(τ)`. -/
theorem isIntegral_siegelFunction_half_zero_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![1 / 2, 0] τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_siegelFunction_half_zero isIntegral_adjoin_j) τ hj

/-- If `j(τ)` is integral over `R`, so is `g₂(τ)`. -/
theorem isIntegral_siegelFunction_half_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![1 / 2, 1 / 2] τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_siegelFunction_half_half isIntegral_adjoin_j) τ hj

/-- If `j(τ)` is integral over `R`, so is `2 / g₀(τ)`. -/
theorem isIntegral_two_div_siegelFunction_zero_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![0, 1 / 2] τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_two_div_siegelFunction_zero_half isIntegral_adjoin_j) τ hj

/-- If `j(τ)` is integral over `R`, so is `2 / g₁(τ)`. -/
theorem isIntegral_two_div_siegelFunction_half_zero_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![1 / 2, 0] τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_two_div_siegelFunction_half_zero isIntegral_adjoin_j) τ hj

/-- If `j(τ)` is integral over `R`, so is `2 / g₂(τ)`. -/
theorem isIntegral_two_div_siegelFunction_half_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![1 / 2, 1 / 2] τ) :=
  isIntegral_apply_of_isIntegral_adjoin_j
    (isIntegral_two_div_siegelFunction_half_half isIntegral_adjoin_j) τ hj

end Values

end TauCeti.ModularForm
