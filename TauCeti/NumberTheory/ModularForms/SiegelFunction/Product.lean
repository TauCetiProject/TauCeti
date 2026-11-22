/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.QExpansion
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import TauCeti.Algebra.BigOperators.Finset.Erase
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.NumberTheory.ModularForms.LevelOne.Invariant
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO
import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# Product identity for level-`N` Siegel functions

For every positive integer `N` and every `τ ∈ ℍ`, the product of the `(12 N)`-th powers of the
nonzero level-`N` Siegel functions equals `N^{12 N}`:
`∏_{v ∈ (ℤ/Nℤ)² \ {0}} g_{v/N}(τ)^{12 N} = N^{12 N}`.
This `SL₂(ℤ)`-invariant holomorphic function is proved constant by showing that its `q_N`-order
at `i∞` is `0` (via `sum_siegelPowerCuspExponent_erase_zero`) and evaluating the constant term
from `∏_{k=1}^{N-1} (1 - ζ_N^k) = N`. Consequently, for `a ∉ N ℤ²`, `(N / g_{a/N}(τ))^{12 N}`
equals the complementary product `∏_{w ∈ ((ℤ/Nℤ)² \ {0}) \ {a mod N}} g_{w/N}(τ)^{12 N}`.

## Main results

* `TauCeti.ModularForm.prod_siegelFunction_zmod_pow_twelve_mul_eq`:
  `∏_{v ∈ (ℤ/Nℤ)² \ {0}} g_{v/N}(τ)^{12 N} = N^{12 N}`.
* `TauCeti.ModularForm.natCast_div_siegelFunction_div_pow_twelve_mul_eq_prod_erase`:
  complementary-product formula for `(N / g_{a/N}(τ))^{12 N}` when `a ∉ N ℤ²`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, GTM 244, Chapter 2, §§1–2.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Filter Topology
open UpperHalfPlane hiding I
open TauCeti.UpperHalfPlane
open scoped Real Matrix MatrixGroups Manifold

namespace TauCeti.ModularForm

private theorem prod_leadingCoeff_zero_first {N : ℕ} [NeZero N] :
    ∏ v ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).filter (fun v ↦ v 0 = 0),
        (cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
          (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1)) =
      (N : ℂ) ^ (12 * N) := by
  set ζ := cexp (2 * π * I / N)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  trans (∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1))) ^ (12 * (n + 1))
  · rw [← Finset.prod_pow]; symm
    refine Finset.prod_bij (fun k _ ↦ ![0, ((k + 1 : ℕ) : ZMod (n + 1))]) (fun k hk ↦ ?_)
      (fun k₁ hk₁ k₂ hk₂ h ↦ ?_) (fun v hv ↦ ?_) (fun k hk ↦ ?_)
    · have hlt : k + 1 < n + 1 := by have := Finset.mem_range.mp hk; omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h0 ↦ ?_, Finset.mem_univ _⟩, rfl⟩
      have hv := congrArg ZMod.val (congrFun h0 1)
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, ZMod.val_natCast_of_lt hlt,
        Pi.zero_apply, ZMod.val_zero] at hv; omega
    · have h1 : k₁ + 1 < n + 1 := by have := Finset.mem_range.mp hk₁; omega
      have h2 : k₂ + 1 < n + 1 := by have := Finset.mem_range.mp hk₂; omega
      have hv := congrArg (fun v : Fin 2 → ZMod (n + 1) ↦ (v 1).val) h
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, ZMod.val_natCast_of_lt h1,
        ZMod.val_natCast_of_lt h2] at hv; omega
    · rcases Finset.mem_filter.mp hv with ⟨hvS, hv0⟩
      have hpos : 0 < (v 1).val := Nat.pos_of_ne_zero <| mt (ZMod.val_eq_zero _).mp fun h1 ↦
        (Finset.mem_erase.mp hvS).1 (by ext i; fin_cases i <;> assumption)
      refine ⟨(v 1).val - 1, Finset.mem_range.mpr (by have := (v 1).val_lt; omega), ?_⟩
      ext i; fin_cases i
      · simp [hv0]
      · simp [Nat.sub_add_cancel hpos]
    · have hlt : k + 1 < n + 1 := by have := Finset.mem_range.mp hk; omega
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        ZMod.val_natCast_of_lt hlt]; simp
  · rw [(Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)).prod_one_sub_pow_eq_order]
    simp only [Nat.cast_succ]

private theorem prod_leadingCoeff_ne_zero_first {N : ℕ} [NeZero N] :
    ∏ v ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).filter (fun v ↦ ¬v 0 = 0),
        (cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
          (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1)) =
      1 := by
  set ζ := cexp (2 * π * I / N)
  trans ∏ x ∈ (Finset.univ : Finset (ZMod N)).erase 0, ∏ y : ZMod N, ζ ^ (6 * x.val * y.val)
  · rw [← Finset.prod_product']; symm
    refine Finset.prod_bij (fun p _ ↦ ![p.1, p.2]) (fun p hp ↦ ?_)
      (fun _ _ _ _ h ↦ Prod.ext (by simpa using congrFun h 0) (by simpa using congrFun h 1))
      (fun v hv ↦ ⟨(v 0, v 1), Finset.mem_product.mpr ⟨Finset.mem_erase.mpr
        ⟨(Finset.mem_filter.mp hv).2, Finset.mem_univ _⟩, Finset.mem_univ _⟩,
        by ext i; fin_cases i <;> rfl⟩)
      (fun p hp ↦ by simp [(Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1])
    have hp1 : p.1 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨fun h0 ↦ hp1 (by simpa using congrFun h0 0), Finset.mem_univ _⟩,
        by simpa using hp1⟩
  · refine Finset.prod_eq_one fun x _ ↦ ?_
    rw [Finset.prod_pow_eq_pow_sum]
    have hexp : (∑ y : ZMod N, 6 * x.val * y.val) = N * (3 * x.val * (N - 1)) := by
      have hsum : (∑ y : ZMod N, 6 * x.val * y.val) = 6 * x.val * ∑ k ∈ Finset.range N, k := by
        rw [← Fintype.sum_equiv (ZMod.finEquiv N).toEquiv (fun k : Fin N ↦ 6 * x.val * k) _
            (fun k ↦ by simp [ZMod.val_natCast_of_lt k.isLt]),
          Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ 6 * x.val * k) N, ← Finset.mul_sum]
      have hdouble : 6 * x.val * ∑ k ∈ Finset.range N, k =
          3 * x.val * ((∑ k ∈ Finset.range N, k) * 2) := by ring
      rw [hsum, hdouble, Finset.sum_range_id_mul_two]
      ring
    rw [hexp, pow_mul, (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).pow_eq_one, one_pow]

private theorem analyticAt_and_coeff_zero_prod_siegelPower {N : ℕ} [NeZero N] :
    AnalyticAt ℂ (cuspFunction N
      (∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
        fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))) 0 ∧
      (laurentQExpansion N
        (∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
          fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))).coeff 0 =
        (N : ℂ) ^ (12 * N) := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set f : (Fin 2 → ZMod N) → ℍ → ℂ :=
    fun v τ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)
  have hf_mer (v : Fin 2 → ZMod N) : MeromorphicAt (cuspFunction N (f v)) 0 := by
    simpa only [f, one_smul, Int.cast_natCast] using
      meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N
        (fun i ↦ ((v i).val : ℤ)) 1
  have hF_mer : MeromorphicAt (cuspFunction N (∏ v ∈ S, f v)) 0 :=
    meromorphicAt_cuspFunction_prod S fun v _ ↦ hf_mer v
  have hfactor_ord (v : Fin 2 → ZMod N) (hv : v ∈ S) :
      meromorphicOrderAt (cuspFunction N (f v)) 0 = siegelPowerCuspExponent N v := by
    have hv0 : (fun i ↦ (((v i).val : ℤ) : ZMod N)) ≠ 0 := by
      simpa [ZMod.natCast_zmod_val] using (Finset.mem_erase.mp hv).1
    have hm := meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul hv0 1
    simpa only [f, one_smul, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one,
      ZMod.natCast_zmod_val, Int.cast_natCast] using hm
  have hord : meromorphicOrderAt (cuspFunction N (∏ v ∈ S, f v)) 0 = 0 := by
    rw [meromorphicOrderAt_cuspFunction_prod S fun v _ ↦ hf_mer v,
      Finset.sum_congr rfl hfactor_ord, ← WithTop.coe_sum,
      sum_siegelPowerCuspExponent_erase_zero N, WithTop.coe_zero]
  have han : AnalyticAt ℂ (cuspFunction N (∏ v ∈ S, f v)) 0 := by
    convert analyticAt_cuspFunction_qParam_pow_mul hF_mer (k := 0) (by simp [hord]) using 2
    ext τ
    simp
  refine ⟨han, ?_⟩
  have hL : laurentQExpansion N (∏ v ∈ S, f v) = ∏ v ∈ S, laurentQExpansion N (f v) :=
    laurentQExpansion_prod S fun v _ ↦ hf_mer v
  have hord_eq {x : LaurentSeries ℂ} {k : ℤ} (h : x.orderTop = k) : x.order = k :=
    WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero
      (HahnSeries.orderTop_ne_top.mp (by rw [h]; exact WithTop.coe_ne_top))).trans h)
  rw [← hord_eq ((orderTop_laurentQExpansion hF_mer).trans hord), ← HahnSeries.leadingCoeff_eq,
    hL, HahnSeries.leadingCoeff_prod]
  have hfac (v : Fin 2 → ZMod N) (hv : v ∈ S) :
      (laurentQExpansion N (f v)).leadingCoeff =
        cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
          (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1) := by
    rw [HahnSeries.leadingCoeff_eq,
      hord_eq ((orderTop_laurentQExpansion (hf_mer v)).trans (hfactor_ord v hv))]
    exact laurentQExpansion_siegelFunction_zmod_pow_twelve_mul_coeff_siegelPowerCuspExponent v
  rw [Finset.prod_congr rfl hfac, ← Finset.prod_filter_mul_prod_filter_not S (fun v ↦ v 0 = 0),
    prod_leadingCoeff_zero_first, prod_leadingCoeff_ne_zero_first, mul_one]

/-- **Product of all nonzero level-`N` Siegel `(12 N)`-th powers.** For every positive integer `N`
and `τ ∈ ℍ`, `∏_{v ∈ (ℤ/Nℤ)² \ {0}} g_{v/N}(τ)^{12 N} = N^{12 N}`. -/
theorem prod_siegelFunction_zmod_pow_twelve_mul_eq (N : ℕ) [NeZero N] (τ : ℍ) :
    ∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
        siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) =
      (N : ℂ) ^ (12 * N) := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set F : ℍ → ℂ :=
    ∏ v ∈ S, fun z : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) z ^ (12 * N)
  have hF_val (z : ℍ) :
      F z = ∏ v ∈ S, siegelFunction (fun i ↦ ((v i).val : ℝ) / N) z ^ (12 * N) := by
    simp [F]
  have hF_mdiff : MDiff F :=
    MDifferentiable.prod fun v _ ↦ (mdifferentiable_siegelFunction _).pow (12 * N)
  have hinv (γ : SL(2, ℤ)) (z : ℍ) : F (γ • z) = F z := by
    rw [hF_val, hF_val]
    set e := (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).vecMulEquiv
    exact Finset.prod_univ_erase_equiv e (Matrix.SpecialLinearGroup.vecMulEquiv_zero _)
      (fun v ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) ↑(γ • z) ^ (12 * N))
      (fun w ↦ siegelFunction (fun i ↦ ((w i).val : ℝ) / N) z ^ (12 * N))
      fun v _ ↦ siegelFunction_zmod_pow_twelve_mul_smul (dvd_mul_left N 6) v γ z
  obtain ⟨han, hlead⟩ := analyticAt_and_coeff_zero_prod_siegelPower (N := N)
  have hper1 : Function.Periodic (F ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun z ↦ by rw [← modular_T_smul]; exact hinv _ z
  have hperN : Function.Periodic (F ∘ ofComplex) N := by simpa using hper1.nat_mul N
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have htend : Tendsto F atImInfty (𝓝 ((N : ℂ) ^ (12 * N))) := by
    rw [← hlead, laurentQExpansion_coeff_zero_of_analyticAt han,
      _root_.UpperHalfPlane.cuspFunction_apply_zero hNpos han hperN]
    exact tendsto_valueAtInfty hNpos hperN han
  rw [← hF_val τ]
  exact levelOne_eq_of_tendsto_atImInfty hF_mdiff hinv htend τ

/-- **Complementary product identity for `(N / g_{a/N})^{12 N}`**: for `0 < N` and `a ∉ N ℤ²`,
`(N / g_{a/N}(τ))^{12 N}` equals the product of `g_{w/N}(τ)^{12 N}` over all
`w ∈ ((ℤ/Nℤ)² \ {0}) \ {a mod N}`. -/
theorem natCast_div_siegelFunction_div_pow_twelve_mul_eq_prod_erase {N : ℕ} [NeZero N]
    {a : Fin 2 → ℤ} (hv : (fun i ↦ (a i : ZMod N)) ≠ 0) (τ : ℍ) :
    ((N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) ^ (12 * N) =
      ∏ w ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).erase (fun i ↦ (a i : ZMod N)),
        siegelFunction (fun i ↦ ((w i).val : ℝ) / N) τ ^ (12 * N) := by
  set v : Fin 2 → ZMod N := fun i ↦ (a i : ZMod N)
  have hne : siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) ≠ 0 :=
    pow_ne_zero _ (mt (siegelFunction_div_eq_zero_iff (fun i ↦ ((v i).val : ℤ)) τ.im_pos).mp
      (by simpa [ZMod.natCast_zmod_val] using hv))
  rw [div_pow, siegelFunction_div_pow_twelve_mul_eq_zmod (dvd_mul_left N 6) a τ.im_pos,
    ← prod_siegelFunction_zmod_pow_twelve_mul_eq N τ,
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩),
    mul_div_cancel_left₀ _ hne]

end TauCeti.ModularForm
