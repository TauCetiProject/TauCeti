/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.QExpansion
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import TauCeti.Algebra.BigOperators.Finset.Erase
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Data.Rat.ZMultiples
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.NumberTheory.Cyclotomic.Aut
import TauCeti.NumberTheory.ModularForms.LevelOne.Invariant
import TauCeti.NumberTheory.ModularForms.LevelOne.JIntegral
import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO
import TauCeti.RingTheory.HahnSeries.Multiplication
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integrality of Siegel functions over `ℤ[j]`

For `0 < N`, the `(12 N)`-th powers `g_{v/N}^{12 N}` (`v ∈ S := (ℤ/Nℤ)² \ {0}`) are permuted by
`SL₂(ℤ)`, multiply to `N^{12 N}`, and are the roots of a monic polynomial over `ℤ[j]`. Hence,
whenever `j` (or `j(τ)`) is integral over a commutative ring `R`, every `g_r` (`r ∈ ℚ²`) and
`N / g_{a/N}` (`N : ℕ`, `a ∈ ℤ²`) is integral over `R` both in `ℍ → ℂ` and pointwise at `τ ∈ ℍ`
(at `r ∈ ℤ²` or `N = 0`, both vanish identically).

## Main results

* `TauCeti.ModularForm.prod_siegelFunction_zmod_pow_twelve_mul_eq`,
  `natCast_div_siegelFunction_div_pow_twelve_mul_eq_prod_erase`:
  `∏_{v ∈ (ℤ/Nℤ)² \ {0}} g_{v/N}(τ)^{12 N} = N^{12 N}` and the complementary-product formula for
  `(N / g_{a/N}(τ))^{12 N}`.
* `TauCeti.ModularForm.exists_monic_map_aeval_j_eq_prod_X_sub_C_siegelFunction_zmod_pow_twelve_mul`:
  monic `Φ ∈ (ℤ[X])[X]` specializing at `j(τ)` to `∏_{v ∈ S} (X - g_{v/N}(τ)^{12 N})`, obtained via
  `SL₂(ℤ)`-invariance, cyclotomic descent on `ℤ[ζ_N]`, and `exists_aeval_j_eq`.
* `TauCeti.ModularForm.isIntegral_siegelFunction_div`, `isIntegral_siegelFunction_ratCast`,
  `isIntegral_natCast_div_siegelFunction_div`: function-level integrality over any ring over which
  `j` is integral (via `(12 N)`-th roots and `(N / g_{v/N})^{12 N} = ∏_{w ≠ v} g_{w/N}^{12 N}`).
* `TauCeti.ModularForm.isIntegral_siegelFunction_div_apply`,
  `isIntegral_siegelFunction_ratCast_apply`, `isIntegral_natCast_div_siegelFunction_div_apply`:
  pointwise integrality at `τ ∈ ℍ`, plus level-two specializations.

## References

* D. S. Kubert, S. Lang, *Modular Units*, GTM 244, Chapter 2, §§1–2.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 5.
* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber functions).
-/

public section

open Complex Filter Topology
open UpperHalfPlane hiding I
open TauCeti.UpperHalfPlane
open scoped Real Matrix MatrixGroups Manifold ModularForm Polynomial

namespace TauCeti.ModularForm

/-! ### `SL₂(ℤ)`-permutation of division indices and the full-level product identity -/

/-- `g_{v/N}^{12 N}` packaged as an element of `UpperHalfPlane.meromorphicAtCuspSubring N`. -/
private noncomputable def siegelPowerMem (N : ℕ) (v : Fin 2 → ZMod N) :
    meromorphicAtCuspSubring N :=
  ⟨fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N), by
    simpa only [mem_meromorphicAtCuspSubring, one_smul, Int.cast_natCast] using
      meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N
        (fun i ↦ ((v i).val : ℤ)) 1⟩

@[simp]
private theorem siegelPowerMem_coe (N : ℕ) (v : Fin 2 → ZMod N) :
    (siegelPowerMem N v : ℍ → ℂ) =
      fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) :=
  rfl

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
      (∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0, siegelPowerMem N v).val) 0 ∧
      (laurentQExpansion N
        (∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0, siegelPowerMem N v).val).coeff 0 =
        (N : ℂ) ^ (12 * N) := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set FM : meromorphicAtCuspSubring N := ∏ v ∈ S, siegelPowerMem N v
  have hFM_mer : MeromorphicAt (cuspFunction N FM.val) 0 :=
    mem_meromorphicAtCuspSubring.mp FM.property
  have hL : laurentQExpansion N FM.val =
      ∏ v ∈ S, laurentQExpansionRingHom N (siegelPowerMem N v) := by
    rw [← laurentQExpansionRingHom_apply]
    exact map_prod (laurentQExpansionRingHom N) (siegelPowerMem N) S
  have hfactor_ord (v : Fin 2 → ZMod N) (hv : v ∈ S) :
      (laurentQExpansionRingHom N (siegelPowerMem N v)).orderTop =
        siegelPowerCuspExponent N v := by
    have hv0 : (fun i ↦ (((v i).val : ℤ) : ZMod N)) ≠ 0 := by
      simpa [ZMod.natCast_zmod_val] using (Finset.mem_erase.mp hv).1
    have hm := meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul hv0 1
    simp only [one_smul, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one,
      ZMod.natCast_zmod_val, Int.cast_natCast] at hm
    rw [laurentQExpansionRingHom_apply]
    exact (orderTop_laurentQExpansion
      (mem_meromorphicAtCuspSubring.mp (siegelPowerMem N v).property)).trans hm
  have hord : meromorphicOrderAt (cuspFunction N FM.val) 0 = 0 := by
    rw [← orderTop_laurentQExpansion hFM_mer, hL, HahnSeries.orderTop_prod,
      Finset.sum_congr rfl hfactor_ord, ← WithTop.coe_sum,
      sum_siegelPowerCuspExponent_erase_zero N, WithTop.coe_zero]
  refine ⟨by simpa using analyticAt_cuspFunction_qParam_pow_mul hFM_mer (k := 0) (by simp [hord]),
    ?_⟩
  have hord_eq {x : LaurentSeries ℂ} {k : ℤ} (h : x.orderTop = k) : x.order = k :=
    WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero
      (HahnSeries.orderTop_ne_top.mp (by rw [h]; exact WithTop.coe_ne_top))).trans h)
  rw [← hord_eq ((orderTop_laurentQExpansion hFM_mer).trans hord), ← HahnSeries.leadingCoeff_eq,
    hL, HahnSeries.leadingCoeff_prod]
  have hfac (v : Fin 2 → ZMod N) (hv : v ∈ S) :
      (laurentQExpansionRingHom N (siegelPowerMem N v)).leadingCoeff =
        cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
          (if v 0 = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1) := by
    rw [HahnSeries.leadingCoeff_eq, hord_eq (hfactor_ord v hv), laurentQExpansionRingHom_apply,
      siegelPowerMem_coe]
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
  set FM : meromorphicAtCuspSubring N := ∏ v ∈ S, siegelPowerMem N v
  have hFM_val (z : ℍ) :
      FM.val z = ∏ v ∈ S, siegelFunction (fun i ↦ ((v i).val : ℝ) / N) z ^ (12 * N) := by
    simp [FM]
  have hFM_mdiff : MDiff FM.val := by
    have hfun : FM.val = ∏ v ∈ S, fun z : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) z ^
        (12 * N) := funext fun z ↦ by simpa [Finset.prod_apply] using hFM_val z
    rw [hfun]; exact MDifferentiable.prod fun v _ ↦ (mdifferentiable_siegelFunction _).pow (12 * N)
  have hinv (γ : SL(2, ℤ)) (z : ℍ) : FM.val (γ • z) = FM.val z := by
    rw [hFM_val, hFM_val]
    set e := (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).vecMulEquiv
    exact Finset.prod_univ_erase_equiv e (Matrix.SpecialLinearGroup.vecMulEquiv_zero _)
      (fun v ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) ↑(γ • z) ^ (12 * N))
      (fun w ↦ siegelFunction (fun i ↦ ((w i).val : ℝ) / N) z ^ (12 * N))
      fun v _ ↦ siegelFunction_zmod_pow_twelve_mul_smul (dvd_mul_left N 6) v γ z
  obtain ⟨han, hlead⟩ := analyticAt_and_coeff_zero_prod_siegelPower (N := N)
  have hper1 : Function.Periodic (FM.val ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun z ↦ by rw [← modular_T_smul]; exact hinv _ z
  have hperN : Function.Periodic (FM.val ∘ ofComplex) N := by simpa using hper1.nat_mul N
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have htend : Tendsto FM.val atImInfty (𝓝 ((N : ℂ) ^ (12 * N))) := by
    rw [← hlead, laurentQExpansion_coeff_zero_of_analyticAt han,
      _root_.UpperHalfPlane.cuspFunction_apply_zero hNpos han hperN]
    exact tendsto_valueAtInfty hNpos hperN han
  rw [← hFM_val τ]
  exact levelOne_eq_of_tendsto_atImInfty hFM_mdiff hinv htend τ

/-! ### The monic polynomial over `ℤ[j]` and general integrality -/

/-- Permutation `v ↦ (v₀, u v₁)` of `(ℤ/Nℤ)²` induced by `u ∈ (ℤ/Nℤ)ˣ`. -/
private def diagSecondEquiv {N : ℕ} (u : (ZMod N)ˣ) :
    (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod N) :=
  (piFinTwoEquiv fun _ ↦ ZMod N).trans <|
    ((Equiv.refl (ZMod N)).prodCongr (LinearEquiv.smulOfUnit u).toEquiv).trans
      (piFinTwoEquiv fun _ ↦ ZMod N).symm

/-- The monic polynomial `∏_{v ≠ 0} (X - g_{v/N}^{12 N})` over `meromorphicAtCuspSubring N`. -/
private noncomputable def siegelPowerPoly (N : ℕ) [NeZero N] : (meromorphicAtCuspSubring N)[X] :=
  ∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
    (Polynomial.X - Polynomial.C (siegelPowerMem N v))

private theorem siegelPowerPoly_map_eval (N : ℕ) [NeZero N] (τ : ℍ) :
    (siegelPowerPoly N).map
        ((Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp (meromorphicAtCuspSubring N).subtype) =
      ∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
        (Polynomial.X - Polynomial.C
          (siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))) := by
  simp [siegelPowerPoly, Polynomial.map_prod]

private theorem siegelPowerPoly_coeff_eval (N k : ℕ) [NeZero N] (τ : ℍ) :
    ((siegelPowerPoly N).coeff k).val τ =
      (∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
        (Polynomial.X - Polynomial.C
          (siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)))).coeff k := by
  rw [← siegelPowerPoly_map_eval N τ, Polynomial.coeff_map]
  simp only [RingHom.comp_apply, Subring.coe_subtype, Pi.evalRingHom_apply]

private theorem laurentQExpansion_siegelPolyCoeff_mem_range_intCast {N : ℕ} [NeZero N]
    (k : ℕ) (m : ℤ) :
    (laurentQExpansion N (((siegelPowerPoly N).coeff k).val)).coeff m ∈
      (Int.castRingHom ℂ).range := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  set Ω : (HahnSeries ℤ ℤ[X])[X] :=
    ∏ v ∈ S, (Polynomial.X - Polynomial.C (siegelPowerLaurentSeries N v))
  set ζ := cexp (2 * π * I / N)
  have hmap (d : ℕ) :
      Ω.map (HahnSeries.mapRingHom (Polynomial.aeval (ζ ^ d)).toRingHom) =
        ∏ v ∈ S, (Polynomial.X - Polynomial.C
          (laurentQExpansionRingHom N (siegelPowerMem N ![v 0, (d : ZMod N) * v 1]))) := by
    simp only [Ω, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [laurentQExpansionRingHom_apply, siegelPowerMem_coe,
      mapRingHom_aeval_exp_pow_siegelPowerLaurentSeries]
  have hmap1 : Ω.map (HahnSeries.mapRingHom (Polynomial.aeval ζ).toRingHom) =
      (siegelPowerPoly N).map (laurentQExpansionRingHom N) := by
    simp only [Ω, siegelPowerPoly, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [laurentQExpansionRingHom_apply, siegelPowerMem_coe,
      mapRingHom_aeval_exp_siegelPowerLaurentSeries]
  have heq : (laurentQExpansion N (((siegelPowerPoly N).coeff k).val)).coeff m =
      Polynomial.aeval ζ ((Ω.coeff k).coeff m) := by
    rw [← laurentQExpansionRingHom_apply, ← Polynomial.coeff_map, ← hmap1,
      Polynomial.coeff_map, HahnSeries.coeff_mapRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [heq]
  refine (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).aeval_mem_range_intCast
    ((Ω.coeff k).coeff m) fun u ↦ ?_
  have hu : Ω.map (HahnSeries.mapRingHom (Polynomial.aeval (ζ ^ (u : ZMod N).val)).toRingHom) =
      Ω.map (HahnSeries.mapRingHom (Polynomial.aeval ζ).toRingHom) := by
    rw [hmap (u : ZMod N).val, hmap1]
    simp only [siegelPowerPoly, ZMod.natCast_zmod_val, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    exact Finset.prod_univ_erase_equiv (diagSecondEquiv u)
      (by ext i; fin_cases i <;> simp [diagSecondEquiv, LinearEquiv.smulOfUnit])
      (fun v ↦ Polynomial.X - Polynomial.C
        (laurentQExpansionRingHom N (siegelPowerMem N ![v 0, (u : ZMod N) * v 1])))
      (fun w ↦ Polynomial.X - Polynomial.C (laurentQExpansionRingHom N (siegelPowerMem N w)))
      fun v _ ↦ by
        have hv : diagSecondEquiv u v = ![v 0, (u : ZMod N) * v 1] := by
          ext i; fin_cases i <;> simp [diagSecondEquiv, LinearEquiv.smulOfUnit, Units.smul_def]
        rw [hv]
  simpa only [Polynomial.coeff_map, HahnSeries.coeff_mapRingHom, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] using congrArg (fun P : (LaurentSeries ℂ)[X] ↦ (P.coeff k).coeff m) hu

private theorem exists_aeval_j_siegelPolyCoeff {N : ℕ} [NeZero N] (k : ℕ) :
    ∃ P : ℤ[X], ∀ τ : ℍ, Polynomial.aeval (j τ) P = ((siegelPowerPoly N).coeff k).val τ := by
  set S := (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0
  have hΨ_mdiff : MDiff ((siegelPowerPoly N).coeff k).val := by
    rw [funext (siegelPowerPoly_coeff_eval N k)]
    exact mdifferentiable_coeff_prod_X_sub_C S
      (fun v _ ↦ (mdifferentiable_siegelFunction _).pow (12 * N)) k
  have hinv (γ : SL(2, ℤ)) (τ : ℍ) :
      ((siegelPowerPoly N).coeff k).val (γ • τ) = ((siegelPowerPoly N).coeff k).val τ := by
    have hpoly :
        (siegelPowerPoly N).map
            ((Pi.evalRingHom (fun _ : ℍ ↦ ℂ) (γ • τ)).comp (meromorphicAtCuspSubring N).subtype) =
          (siegelPowerPoly N).map
            ((Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp (meromorphicAtCuspSubring N).subtype) := by
      rw [siegelPowerPoly_map_eval, siegelPowerPoly_map_eval]
      set e := (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).vecMulEquiv
      exact Finset.prod_univ_erase_equiv e (Matrix.SpecialLinearGroup.vecMulEquiv_zero _)
        (fun v ↦ Polynomial.X - Polynomial.C
          (siegelFunction (fun i ↦ ((v i).val : ℝ) / N) ↑(γ • τ) ^ (12 * N)))
        (fun w ↦ Polynomial.X - Polynomial.C
          (siegelFunction (fun i ↦ ((w i).val : ℝ) / N) τ ^ (12 * N)))
        fun v _ ↦ by rw [siegelFunction_zmod_pow_twelve_mul_smul (dvd_mul_left N 6)]
    simpa only [Polynomial.coeff_map, RingHom.comp_apply, Subring.coe_subtype,
      Pi.evalRingHom_apply] using congrArg (fun Q : ℂ[X] ↦ Q.coeff k) hpoly
  have hper : Function.Periodic (((siegelPowerPoly N).coeff k).val ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by rw [← modular_T_smul]; exact hinv _ τ
  have hmer1 : MeromorphicAt (cuspFunction 1 ((siegelPowerPoly N).coeff k).val) 0 :=
    meromorphicAt_cuspFunction_of_nat_mul one_pos hΨ_mdiff hper (d := N)
      (by simpa only [mul_one] using
        mem_meromorphicAtCuspSubring.mp ((siegelPowerPoly N).coeff k).property)
  refine exists_aeval_j_eq (R := ℤ) hΨ_mdiff hinv hmer1 fun n _ ↦ ?_
  rw [hper.laurentQExpansion_coeff_eq_coeff_nat_mul hmer1 (d := N) n, mul_one, algebraMap_int_eq]
  exact laurentQExpansion_siegelPolyCoeff_mem_range_intCast k ((N : ℤ) * n)

/-- **The `(12 N)`-th powers of the nonzero level-`N` Siegel functions satisfy a monic polynomial
over `ℤ[j]`.** There exists a monic polynomial `Φ ∈ (ℤ[X])[X]` whose coefficientwise evaluation
at `j(τ)` equals `∏_{v ∈ (ℤ/Nℤ)² \ {0}} (X - g_{v/N}(τ)^{12 N})` for every `τ ∈ ℍ`. -/
theorem exists_monic_map_aeval_j_eq_prod_X_sub_C_siegelFunction_zmod_pow_twelve_mul
    (N : ℕ) [NeZero N] :
    ∃ Φ : (ℤ[X])[X], Φ.Monic ∧ ∀ τ : ℍ,
      Φ.map (Polynomial.aeval (j τ)).toRingHom =
        ∏ v ∈ (Finset.univ : Finset (Fin 2 → ZMod N)).erase 0,
          (Polynomial.X - Polynomial.C
            (siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))) := by
  set Ψ : (ℍ → ℂ)[X] := (siegelPowerPoly N).map (meromorphicAtCuspSubring N).subtype
  have hΨ_monic : Ψ.Monic :=
    (Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _).map _
  have hcomp (τ : ℍ) :
      (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp (Polynomial.aeval (R := ℤ) j).toRingHom =
        (Polynomial.aeval (j τ)).toRingHom :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  have hΨ_lifts : Ψ ∈ Polynomial.lifts (Polynomial.aeval (R := ℤ) j).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    obtain ⟨P, hP⟩ := exists_aeval_j_siegelPolyCoeff (N := N) k
    refine ⟨P, funext fun τ ↦ ?_⟩
    have hev : Polynomial.aeval (R := ℤ) j P τ = Polynomial.aeval (j τ) P := by
      simpa using RingHom.congr_fun (hcomp τ) P
    simpa [Ψ, Polynomial.coeff_map, hev] using hP τ
  obtain ⟨Φ, hΦ_map, -, hΦ_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hΨ_lifts hΨ_monic
  refine ⟨Φ, hΦ_monic, fun τ ↦ ?_⟩
  rw [← hcomp τ, ← Polynomial.map_map, hΦ_map, Polynomial.map_map, siegelPowerPoly_map_eval]

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

/-! ### General integrality of Siegel functions (as functions on `ℍ`) -/

private theorem siegelFunction_div_pow_twelve_mul_eq_zmod_fun (N : ℕ) (a : Fin 2 → ℤ) :
    (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ) ^ (12 * N) =
      fun τ : ℍ ↦ siegelFunction (fun i ↦ (((a i : ZMod N).val : ℝ) / N)) τ ^ (12 * N) :=
  funext fun τ ↦ siegelFunction_div_pow_twelve_mul_eq_zmod (dvd_mul_left N 6) a τ.im_pos

section GeneralFunctions

variable {R : Type*} [CommRing R] [Algebra R (ℍ → ℂ)]

/-- **Every level-`N` Siegel function `g_{a/N}` is integral over any ring over which `j` is
integral.** Take `R = Algebra.adjoin ℤ {j}` for integrality over `ℤ[j]`. -/
theorem isIntegral_siegelFunction_div (N : ℕ) (a : Fin 2 → ℤ) (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have h0 : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / (0 : ℕ)) τ) = 0 :=
      funext fun _ ↦ by simp [div_zero, ← Pi.zero_def]
    rw [h0]; exact isIntegral_zero
  have : NeZero N := ⟨hN⟩
  set v : Fin 2 → ZMod N := fun i ↦ (a i : ZMod N)
  by_cases hv : v = 0
  · have hzero : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ) = 0 :=
      funext fun τ ↦ (siegelFunction_div_eq_zero_iff a τ.im_pos).mpr hv
    rw [hzero]; exact isIntegral_zero
  obtain ⟨Φ, hmon, hΦ⟩ :=
    exists_monic_map_aeval_j_eq_prod_X_sub_C_siegelFunction_zmod_pow_twelve_mul N
  refine IsIntegral.of_pow (by positivity : 0 < 12 * N) ?_
  rw [siegelFunction_div_pow_twelve_mul_eq_zmod_fun N a]
  refine TauCeti.isIntegral_of_eval_map_aeval_eq_zero hmon hj (funext fun τ ↦ ?_)
  have hcomp : (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ).comp (Polynomial.aeval j).toRingHom =
      (Polynomial.aeval (j τ)).toRingHom := Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  rw [Pi.zero_apply, ← Pi.evalRingHom_apply (fun _ : ℍ ↦ ℂ) τ (Polynomial.eval _ _),
    Polynomial.eval_map, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval_map, hΦ τ,
    Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩) (by simp [v])

/-- **Every rational-parameter Siegel function `g_r` (`r ∈ ℚ²`) is integral over any ring over
which `j` is integral.** -/
theorem isIntegral_siegelFunction_ratCast (r : Fin 2 → ℚ) (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction (fun i ↦ (r i : ℝ)) τ) := by
  obtain ⟨D, -, hD⟩ := Rat.exists_forall_mem_zmultiples_inv_natCast r
  choose a ha using fun i ↦ AddSubgroup.mem_zmultiples_iff.mp (hD i)
  have hr : (fun i ↦ (r i : ℝ)) = fun i ↦ (a i : ℝ) / D := funext fun i ↦ by
    rw [← ha i, zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast, Rat.cast_inv, Rat.cast_natCast,
      div_eq_mul_inv]
  rw [hr]
  exact isIntegral_siegelFunction_div D a hj

/-- **Scaled reciprocal integrality**: `N / g_{a/N}` is integral over any ring over which `j` is
integral. -/
theorem isIntegral_natCast_div_siegelFunction_div (N : ℕ) (a : Fin 2 → ℤ) (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ (N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have h0 : (fun τ : ℍ ↦ ((0 : ℕ) : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / (0 : ℕ)) τ) =
        0 := funext fun _ ↦ by simp
    rw [h0]; exact isIntegral_zero
  have : NeZero N := ⟨hN⟩
  set v : Fin 2 → ZMod N := fun i ↦ (a i : ZMod N)
  by_cases hv : v = 0
  · have hzero : (fun τ : ℍ ↦ (N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) = 0 :=
      funext fun τ ↦ by simp [(siegelFunction_div_eq_zero_iff a τ.im_pos).mpr hv]
    rw [hzero]; exact isIntegral_zero
  refine IsIntegral.of_pow (by positivity : 0 < 12 * N) ?_
  have hprod : (fun τ : ℍ ↦ (N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) ^ (12 * N) =
      ∏ w ∈ ((Finset.univ : Finset (Fin 2 → ZMod N)).erase 0).erase v,
        (fun τ : ℍ ↦ siegelFunction (fun i ↦ ((w i).val : ℝ) / N) τ) ^ (12 * N) := funext fun τ ↦
    by simpa only [Pi.pow_apply, Finset.prod_apply] using
      natCast_div_siegelFunction_div_pow_twelve_mul_eq_prod_erase hv τ
  rw [hprod]
  exact IsIntegral.prod _ fun w _ ↦
    (by simpa using (isIntegral_siegelFunction_div N (fun i ↦ ((w i).val : ℤ)) hj).pow (12 * N))

end GeneralFunctions

/-! ### General integrality of Siegel values at `τ ∈ ℍ` -/

section GeneralValues

variable {R : Type*} [CommRing R] [Algebra R ℂ]

/-- **Pointwise integrality of `g_{a/N}(τ)`**: if `j(τ)` is integral over `R`, then so is
`g_{a/N}(τ)`. In particular, if `j(τ)` is an algebraic integer (`R = ℤ`), then every `g_{a/N}(τ)`
is an algebraic integer. -/
theorem isIntegral_siegelFunction_div_apply (N : ℕ) (a : Fin 2 → ℤ) (τ : ℍ)
    (hj : IsIntegral R (j τ)) : IsIntegral R (siegelFunction (fun i ↦ (a i : ℝ) / N) τ) :=
  (isIntegral_siegelFunction_div N a isIntegral_adjoin_j).eval_of_adjoin_j τ hj

/-- **Pointwise integrality of `g_r(τ)` for `r ∈ ℚ²`**: if `j(τ)` is integral over `R`, then so is
`g_r(τ)`. -/
theorem isIntegral_siegelFunction_ratCast_apply (r : Fin 2 → ℚ) (τ : ℍ) (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction (fun i ↦ (r i : ℝ)) τ) :=
  (isIntegral_siegelFunction_ratCast r isIntegral_adjoin_j).eval_of_adjoin_j τ hj

/-- **Pointwise integrality of `N / g_{a/N}(τ)`**: if `j(τ)` is integral over `R`, then so is
`N / g_{a/N}(τ)`. In particular, when `j(τ)` is an algebraic integer and `a ∉ N ℤ²`, `g_{a/N}(τ)`
divides `N` in the ring of algebraic integers. -/
theorem isIntegral_natCast_div_siegelFunction_div_apply (N : ℕ) (a : Fin 2 → ℤ) (τ : ℍ)
    (hj : IsIntegral R (j τ)) :
    IsIntegral R ((N : ℂ) / siegelFunction (fun i ↦ (a i : ℝ) / N) τ) :=
  (isIntegral_natCast_div_siegelFunction_div N a isIntegral_adjoin_j).eval_of_adjoin_j τ hj

end GeneralValues

/-! ### Level-two specializations -/

section Functions

variable {R : Type*} [CommRing R] [Algebra R (ℍ → ℂ)]

private theorem isIntegral_siegelFunction_vecCons_div_two (a b : ℤ) (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![(a : ℝ) / 2, (b : ℝ) / 2] τ) := by
  have hmap : ![(a : ℝ) / 2, (b : ℝ) / 2] = fun i ↦ ((![a, b] i : ℤ) : ℝ) / (2 : ℕ) :=
    FinVec.map_eq (fun x : ℤ ↦ (x : ℝ) / (2 : ℕ)) ![a, b]
  simpa only [hmap] using isIntegral_siegelFunction_div 2 ![a, b] hj

private theorem isIntegral_two_div_siegelFunction_vecCons_div_two (a b : ℤ)
    (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![(a : ℝ) / 2, (b : ℝ) / 2] τ) := by
  have hmap : ![(a : ℝ) / 2, (b : ℝ) / 2] = fun i ↦ ((![a, b] i : ℤ) : ℝ) / (2 : ℕ) :=
    FinVec.map_eq (fun x : ℤ ↦ (x : ℝ) / (2 : ℕ)) ![a, b]
  simpa only [hmap, Nat.cast_ofNat] using
    isIntegral_natCast_div_siegelFunction_div 2 ![a, b] hj

/-- The level-two Siegel function `g₀` is integral over any coefficient ring over which `j`
is integral. Take `R = Algebra.adjoin ℤ {j}` for integrality over `ℤ[j]`. -/
theorem isIntegral_siegelFunction_zero_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![0, 1 / 2] τ) := by
  simpa only [Int.cast_zero, zero_div, Int.cast_one] using
    isIntegral_siegelFunction_vecCons_div_two 0 1 hj

/-- The level-two Siegel function `g₁` is integral over any coefficient ring over which `j`
is integral. -/
theorem isIntegral_siegelFunction_half_zero (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![1 / 2, 0] τ) := by
  simpa only [Int.cast_zero, zero_div, Int.cast_one] using
    isIntegral_siegelFunction_vecCons_div_two 1 0 hj

/-- The level-two Siegel function `g₂` is integral over any coefficient ring over which `j`
is integral. -/
theorem isIntegral_siegelFunction_half_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ siegelFunction ![1 / 2, 1 / 2] τ) := by
  simpa only [Int.cast_one] using isIntegral_siegelFunction_vecCons_div_two 1 1 hj

/-- Twice the inverse of `g₀` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_zero_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![0, 1 / 2] τ) := by
  simpa only [Int.cast_zero, zero_div, Int.cast_one] using
    isIntegral_two_div_siegelFunction_vecCons_div_two 0 1 hj

/-- Twice the inverse of `g₁` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_half_zero (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![1 / 2, 0] τ) := by
  simpa only [Int.cast_zero, zero_div, Int.cast_one] using
    isIntegral_two_div_siegelFunction_vecCons_div_two 1 0 hj

/-- Twice the inverse of `g₂` is integral over any coefficient ring over which `j` is integral. -/
theorem isIntegral_two_div_siegelFunction_half_half (hj : IsIntegral R j) :
    IsIntegral R (fun τ : ℍ ↦ 2 / siegelFunction ![1 / 2, 1 / 2] τ) := by
  simpa only [Int.cast_one] using isIntegral_two_div_siegelFunction_vecCons_div_two 1 1 hj

end Functions

/-! ### Level-two algebraic-integer values -/

section Values

variable {R : Type*} [CommRing R] [Algebra R ℂ] (τ : ℍ)

/-- If `j(τ)` is integral over `R`, so is `g₀(τ)`. In particular this applies with `R = ℤ`. -/
theorem isIntegral_siegelFunction_zero_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![0, 1 / 2] τ) :=
  (isIntegral_siegelFunction_zero_half isIntegral_adjoin_j).eval_of_adjoin_j τ hj

/-- If `j(τ)` is integral over `R`, so is `g₁(τ)`. -/
theorem isIntegral_siegelFunction_half_zero_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![1 / 2, 0] τ) :=
  (isIntegral_siegelFunction_half_zero isIntegral_adjoin_j).eval_of_adjoin_j τ hj

/-- If `j(τ)` is integral over `R`, so is `g₂(τ)`. -/
theorem isIntegral_siegelFunction_half_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (siegelFunction ![1 / 2, 1 / 2] τ) :=
  (isIntegral_siegelFunction_half_half isIntegral_adjoin_j).eval_of_adjoin_j τ hj

/-- If `j(τ)` is integral over `R`, so is `2 / g₀(τ)`. -/
theorem isIntegral_two_div_siegelFunction_zero_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![0, 1 / 2] τ) :=
  (isIntegral_two_div_siegelFunction_zero_half isIntegral_adjoin_j).eval_of_adjoin_j τ hj

/-- If `j(τ)` is integral over `R`, so is `2 / g₁(τ)`. -/
theorem isIntegral_two_div_siegelFunction_half_zero_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![1 / 2, 0] τ) :=
  (isIntegral_two_div_siegelFunction_half_zero isIntegral_adjoin_j).eval_of_adjoin_j τ hj

/-- If `j(τ)` is integral over `R`, so is `2 / g₂(τ)`. -/
theorem isIntegral_two_div_siegelFunction_half_half_apply (hj : IsIntegral R (j τ)) :
    IsIntegral R (2 / siegelFunction ![1 / 2, 1 / 2] τ) :=
  (isIntegral_two_div_siegelFunction_half_half isIntegral_adjoin_j).eval_of_adjoin_j τ hj

end Values

end TauCeti.ModularForm
