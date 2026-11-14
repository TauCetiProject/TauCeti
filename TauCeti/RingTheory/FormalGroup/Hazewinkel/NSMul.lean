/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Arithmetic
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral
import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Dvd
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The `p`-series of Hazewinkel's formal group law

Let `p` be a prime and let `F_v` (`TauCeti.hazewinkelIntegralFormalGroup p v`) be Hazewinkel's
integral formal group law specialized at `v = (v₁, v₂, …)` in a commutative ring `R`. Over a
`ℚ`-algebra `K`, `F_v` agrees with `TauCeti.hazewinkelFormalGroup p v`, whose logarithm is
`f_v(X) = ∑_{n ≥ 0} mₙ(v) X^(pⁿ)` with `m₀(v) = 1` and
`p mₙ(v) = ∑_{0 ≤ i < n} mᵢ(v) v_(n - i)^(pⁱ)`.

This file establishes three structural properties of `F_v` and its `[p]`-series `[p]_(F_v)(X)`:
1. **Zero specialization and truncation.** At `v = 0`, `F_0 = 𝔾ₐ`. If `v` and `w` agree on
   `1 ≤ i ≤ N`, then `F_v` and `[m]_(F_v)` agree with `F_w` and `[m]_(F_w)` below `p^(N + 1)`.
2. **Leading coefficient modulo `(v₁, …, v_(n - 1))`.** If `vᵢ = 0` for `i < n`, then `[m]_(F_v)(X)`
   agrees with `m X` below degree `pⁿ` and `coeff (pⁿ) [p]_(F_v) = (1 - p^(pⁿ - 1)) vₙ`.
3. **Ravenel's modulo-`p` `[p]`-series formula.** When `v` is supported in `s`,
   `p f_v(X) - ∑_{j ∈ s} f_v(vⱼ X^(pʲ)) = p X` over `ℚ`-algebras, so `p` divides
   `[p]_(F_v)(X) - ∑^F_{j ∈ s} (vⱼ X^(pʲ))` over any commutative ring `R` (with equality in
   characteristic `p`), and truncating `v` at `N` gives the congruence below degree `p^(N + 1)`.

## Main results

* `TauCeti.hazewinkelFormalGroup_zero`, `TauCeti.hazewinkelIntegralFormalGroup_zero`
* `TauCeti.coeff_hazewinkelIntegralFormalGroup_congr`,
  `TauCeti.coeff_nsmulSeries_hazewinkelIntegralFormalGroup_congr`
* `TauCeti.coeff_nsmulSeries_hazewinkelIntegralFormalGroup_mem_span`,
  `TauCeti.coeff_pow_nsmulSeries_hazewinkelIntegralFormalGroup_sub_mem_span`
* `TauCeti.natCast_dvd_nsmulSeries_hazewinkelIntegralFormalGroup_sub_of_support`,
  `TauCeti.nsmulSeries_hazewinkelIntegralFormalGroup_eq_of_support`,
  `TauCeti.natCast_dvd_coeff_nsmulSeries_hazewinkelIntegralFormalGroup_sub`,
  `TauCeti.coeff_nsmulSeries_hazewinkelIntegralFormalGroup_eq_of_charP`

## References

* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §§2–5.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1 (A2.1.27).
-/

public section

open Finset MvPowerSeries

namespace TauCeti

/-! ### Specialization at the zero family -/

section Zero

variable {K R : Type*} [CommRing K] [Algebra ℚ K] [CommRing R]

/-- For `v = 0`, every positive-index Hazewinkel logarithm coefficient `m_(n + 1)(0)` vanishes. -/
@[simp]
theorem hazewinkelLogCoeff_zero_succ (p n : ℕ) :
    hazewinkelLogCoeff p (0 : ℕ+ → K) (n + 1) = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hazewinkelLogCoeff_succ]
  · simp [hazewinkelLogCoeff_succ, zero_pow (pow_ne_zero _ hp)]

/-- For `v = 0`, `mₙ(0)` is `1` when `n = 0` and `0` otherwise. -/
theorem hazewinkelLogCoeff_zero_eq_ite (p n : ℕ) :
    hazewinkelLogCoeff p (0 : ℕ+ → K) n = if n = 0 then 1 else 0 := by
  rcases n with _ | n <;> simp

/-- At `v = 0`, Hazewinkel's logarithm is the identity formal coordinate `X`. -/
@[simp]
theorem hazewinkelLog_zero (p : ℕ) : hazewinkelLog p (0 : ℕ+ → K) = 1 := by
  ext k
  by_cases hk : ∃ n, p ^ n = k
  · obtain ⟨_ | n, rfl⟩ := hk
    · simp
    · rcases lt_or_ge 1 p with hp | hp
      · rw [coeff_hazewinkelLog_pow _ hp, hazewinkelLogCoeff_zero_succ,
          FormalCoordinate.toPowerSeries_one, PowerSeries.coeff_X,
          ite_eq_right (Nat.one_lt_pow n.succ_ne_zero hp).ne']
      · rcases p with _ | _ | p
        · rw [zero_pow n.succ_ne_zero, FormalCoordinate.toPowerSeries_one, PowerSeries.coeff_zero_X,
            PowerSeries.coeff_zero_eq_constantCoeff_apply,
            (hazewinkelLog 0 (0 : ℕ+ → K)).constantCoeff_toPowerSeries]
        · simp
        · omega
  · push Not at hk
    rw [coeff_hazewinkelLog_eq_zero _ hk, FormalCoordinate.toPowerSeries_one, PowerSeries.coeff_X,
      ite_eq_right fun h1 ↦ hk 0 (by simp [h1])]

/-- Over a `ℚ`-algebra, Hazewinkel's formal group law at `v = 0` is `FormalGroup.𝔾ₐ`. -/
@[simp]
theorem hazewinkelFormalGroup_zero (p : ℕ) :
    hazewinkelFormalGroup p (0 : ℕ+ → K) = FormalGroup.𝔾ₐ := by
  rw [hazewinkelFormalGroup_def, hazewinkelLog_zero, inv_one, one_smul]

/-- Over any commutative ring `R`, Hazewinkel's integral formal group law at `v = 0` is
`FormalGroup.𝔾ₐ`. -/
@[simp]
theorem hazewinkelIntegralFormalGroup_zero (p : ℕ) [Fact p.Prime] :
    hazewinkelIntegralFormalGroup p (0 : ℕ+ → R) = FormalGroup.𝔾ₐ := by
  have hZ : hazewinkelIntegralFormalGroup p (0 : ℕ+ → ℤ) = FormalGroup.𝔾ₐ :=
    FormalGroup.map_injective (f := Int.castRingHom ℚ) Int.cast_injective <| by
      dsimp only
      rw [map_hazewinkelIntegralFormalGroup, show (Int.castRingHom ℚ) ∘ (0 : ℕ+ → ℤ) = 0 from
        funext fun _ ↦ map_zero _, hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
        hazewinkelFormalGroup_zero, FormalGroup.map_𝔾ₐ]
  rw [show (0 : ℕ+ → R) = (Int.castRingHom R) ∘ (0 : ℕ+ → ℤ) from funext fun _ ↦ (map_zero _).symm,
    ← map_hazewinkelIntegralFormalGroup, hZ, FormalGroup.map_𝔾ₐ]

end Zero

/-! ### Truncation invariance -/

section Truncation

variable {K R : Type*} [CommRing K] [Algebra ℚ K] [CommRing R]

/-- Hazewinkel's logarithm coefficients `m₀(v), …, m_N(v)` depend only on `v₁, …, v_N`. -/
theorem hazewinkelLogCoeff_congr {p : ℕ} {v w : ℕ+ → K} {N k : ℕ}
    (hv : ∀ i : ℕ+, (i : ℕ) ≤ N → v i = w i) (hk : k ≤ N) :
    hazewinkelLogCoeff p v k = hazewinkelLogCoeff p w k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | m
    · simp
    · rw [hazewinkelLogCoeff_succ, hazewinkelLogCoeff_succ]
      exact congrArg _ (sum_congr rfl fun i hi ↦ by
        rw [mem_range] at hi
        rw [ih i (by omega) (by omega), hv (m - i).succPNat (by simp; omega)])

/-- The coefficients of Hazewinkel's logarithm below degree `p^(N + 1)` depend only on
`v₁, …, v_N`. -/
theorem coeff_hazewinkelLog_congr {p : ℕ} {v w : ℕ+ → K} {N k : ℕ}
    (hv : ∀ i : ℕ+, (i : ℕ) ≤ N → v i = w i) (hk : k < p ^ (N + 1)) :
    PowerSeries.coeff k (hazewinkelLog p v).toPowerSeries =
      PowerSeries.coeff k (hazewinkelLog p w).toPowerSeries := by
  by_cases hpow : ∃ n, p ^ n = k
  · obtain ⟨n, rfl⟩ := hpow
    rcases lt_or_ge 1 p with hp | hp
    · rw [coeff_hazewinkelLog_pow v hp, coeff_hazewinkelLog_pow w hp]
      exact hazewinkelLogCoeff_congr hv (Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right hp).mp hk))
    · rcases p with _ | _ | p <;> [simp at hk; simp; omega]
  · push Not at hpow
    rw [coeff_hazewinkelLog_eq_zero v hpow, coeff_hazewinkelLog_eq_zero w hpow]

omit [Algebra ℚ K] in
private theorem subst_inv_smul_𝔾ₐ_toPowerSeries (φ : FormalCoordinate K) :
    φ.toPowerSeries.subst (φ⁻¹ • (FormalGroup.𝔾ₐ : FormalGroup K)).toPowerSeries =
      φ.toPowerSeries.subst (X 0) + φ.toPowerSeries.subst (X 1) := by
  have hX : MvPowerSeries.HasSubst
      ![φ.toPowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K),
        φ.toPowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K)] :=
    hasSubst_of_constantCoeff_zero <| Fin.forall_fin_two.mpr
      ⟨PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 0) _ φ.constantCoeff_toPowerSeries,
       PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 1) _ φ.constantCoeff_toPowerSeries⟩
  rw [FormalGroup.subst_toPowerSeries_eq_subst_smul_toPowerSeries, smul_inv_smul,
    FormalGroup.𝔾ₐ_toPowerSeries, MvPowerSeries.subst_add hX, MvPowerSeries.subst_X hX,
    MvPowerSeries.subst_X hX]; rfl

omit [Algebra ℚ K] in
private theorem le_order_inv_smul_𝔾ₐ_sub {f g : FormalCoordinate K} {M : ℕ}
    (hfg : (M : ℕ∞) ≤ (f.toPowerSeries - g.toPowerSeries).order) :
    (M : ℕ∞) ≤ ((f⁻¹ • (FormalGroup.𝔾ₐ : FormalGroup K)).toPowerSeries -
      (g⁻¹ • (FormalGroup.𝔾ₐ : FormalGroup K)).toPowerSeries).order := by
  set F := f⁻¹ • (FormalGroup.𝔾ₐ : FormalGroup K)
  set G := g⁻¹ • (FormalGroup.𝔾ₐ : FormalGroup K)
  have hsub (u : MvPowerSeries (Fin 2) K) (hu : constantCoeff u = 0) :
      (M : ℕ∞) ≤ (f.toPowerSeries.subst u - g.toPowerSeries.subst u).order := by
    rw [show f.toPowerSeries.subst u - g.toPowerSeries.subst u =
        (f.toPowerSeries - g.toPowerSeries).subst u by
      simpa only [PowerSeries.coe_substAlgHom] using
        (map_sub (PowerSeries.substAlgHom (.of_constantCoeff_zero hu))
          f.toPowerSeries g.toPowerSeries).symm]
    exact hfg.trans (PowerSeries.le_order_subst_left hu)
  have hord : (M : ℕ∞) ≤
      (f.toPowerSeries.subst F.toPowerSeries - f.toPowerSeries.subst G.toPowerSeries).order := by
    rw [show f.toPowerSeries.subst F.toPowerSeries - f.toPowerSeries.subst G.toPowerSeries =
        (f.toPowerSeries.subst (X 0) - g.toPowerSeries.subst (X 0)) +
          (f.toPowerSeries.subst (X 1) - g.toPowerSeries.subst (X 1)) -
          (f.toPowerSeries.subst G.toPowerSeries - g.toPowerSeries.subst G.toPowerSeries) by
      rw [subst_inv_smul_𝔾ₐ_toPowerSeries f, subst_inv_smul_𝔾ₐ_toPowerSeries g]; ring]
    exact le_order_sub (le_order_add (hsub (X 0) (constantCoeff_X 0))
      (hsub (X 1) (constantCoeff_X 1))) (hsub G.toPowerSeries G.zero_constantCoeff)
  have hF₀ := PowerSeries.constantCoeff_subst_eq_zero F.zero_constantCoeff _
    f.constantCoeff_toPowerSeries
  have hG₀ := PowerSeries.constantCoeff_subst_eq_zero G.zero_constantCoeff _
    f.constantCoeff_toPowerSeries
  have hinv := MvPowerSeries.le_order_subst_sub_subst (H := f⁻¹.toPowerSeries) (k := 1)
    (one_le_order_iff_constCoeff_eq_zero.mpr f⁻¹.constantCoeff_toPowerSeries)
    (hasSubst_of_constantCoeff_zero fun _ : Unit ↦ hF₀)
    (hasSubst_of_constantCoeff_zero fun _ : Unit ↦ hG₀)
    (fun _ ↦ hF₀) (fun _ ↦ hG₀) (fun _ ↦ hord)
  rwa [Nat.add_sub_cancel, ← PowerSeries.subst_def, ← PowerSeries.subst_def,
    f.subst_inv_subst (.of_constantCoeff_zero F.zero_constantCoeff),
    f.subst_inv_subst (.of_constantCoeff_zero G.zero_constantCoeff)] at hinv

/-- Over a `ℚ`-algebra, the coefficients of `hazewinkelFormalGroup p v` in total degrees below
`p^(N + 1)` depend only on `v₁, …, v_N`. -/
theorem coeff_hazewinkelFormalGroup_congr {p : ℕ} {v w : ℕ+ → K} {N : ℕ}
    (hv : ∀ i : ℕ+, (i : ℕ) ≤ N → v i = w i) {d : Fin 2 →₀ ℕ} (hd : d.degree < p ^ (N + 1)) :
    coeff d (hazewinkelFormalGroup p v).toPowerSeries =
      coeff d (hazewinkelFormalGroup p w).toPowerSeries := by
  have hlog : ((p ^ (N + 1) : ℕ) : ℕ∞) ≤
      ((hazewinkelLog p v).toPowerSeries - (hazewinkelLog p w).toPowerSeries).order :=
    PowerSeries.nat_le_order _ _ fun k hk ↦ by
      rw [map_sub, coeff_hazewinkelLog_congr hv hk, sub_self]
  rw [hazewinkelFormalGroup_def, hazewinkelFormalGroup_def, ← sub_eq_zero, ← map_sub]
  exact coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le (le_order_inv_smul_𝔾ₐ_sub hlog))

private theorem le_order_subst_pair_sub {F G : FormalGroup R} {M : ℕ}
    (hFG : (M : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order)
    {a₁ a₂ b₁ b₂ : PowerSeries R}
    (ha₁ : PowerSeries.constantCoeff a₁ = 0) (ha₂ : PowerSeries.constantCoeff a₂ = 0)
    (hb₁ : PowerSeries.constantCoeff b₁ = 0) (hb₂ : PowerSeries.constantCoeff b₂ = 0)
    (h₁ : (M : ℕ∞) ≤ MvPowerSeries.order (a₁ - b₁ : PowerSeries R))
    (h₂ : (M : ℕ∞) ≤ MvPowerSeries.order (a₂ - b₂ : PowerSeries R)) :
    (M : ℕ∞) ≤ MvPowerSeries.order
      (subst ![a₁, a₂] F.toPowerSeries - subst ![b₁, b₂] G.toPowerSeries : PowerSeries R) := by
  have ha := PowerSeries.hasSubst_pair ha₁ ha₂
  have hb := PowerSeries.hasSubst_pair hb₁ hb₂
  have ha' : ∀ i : Fin 2, constantCoeff (![a₁, a₂] i : PowerSeries R) = 0 :=
    Fin.forall_fin_two.mpr ⟨by rwa [← PowerSeries.constantCoeff_eq],
      by rwa [← PowerSeries.constantCoeff_eq]⟩
  have hb' : ∀ i : Fin 2, constantCoeff (![b₁, b₂] i : PowerSeries R) = 0 :=
    Fin.forall_fin_two.mpr ⟨by rwa [← PowerSeries.constantCoeff_eq],
      by rwa [← PowerSeries.constantCoeff_eq]⟩
  rw [show subst ![a₁, a₂] F.toPowerSeries - subst ![b₁, b₂] G.toPowerSeries =
      subst ![a₁, a₂] (F.toPowerSeries - G.toPowerSeries) +
        (subst ![a₁, a₂] G.toPowerSeries - subst ![b₁, b₂] G.toPowerSeries) by
    rw [subst_sub ha]; ring]
  refine le_order_add (le_order fun e he ↦ ?_) ?_
  · rw [coeff_subst ha]
    refine finsum_eq_zero_of_forall_eq_zero fun d ↦ ?_
    rcases lt_or_ge d.degree M with hdM | hdM
    · rw [coeff_of_lt_order ((Nat.cast_lt.mpr hdM).trans_le hFG), zero_smul]
    · rw [coeff_of_lt_order (he.trans_le ((Nat.cast_le.mpr hdM).trans
        (degree_le_order_prod_pow ha' d))), smul_zero]
  · simpa only [Nat.add_sub_cancel] using MvPowerSeries.le_order_subst_sub_subst
      (H := G.toPowerSeries) (k := 1) (one_le_order_iff_constCoeff_eq_zero.mpr G.zero_constantCoeff)
      ha hb ha' hb' (Fin.forall_fin_two.mpr ⟨h₁, h₂⟩)

private theorem le_order_nsmulSeries_sub {F G : FormalGroup R} {M : ℕ}
    (hFG : (M : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order) (m : ℕ) :
    (M : ℕ∞) ≤ MvPowerSeries.order (F.nsmulSeries m - G.nsmulSeries m : PowerSeries R) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [F.nsmulSeries_succ, G.nsmulSeries_succ]
    exact le_order_subst_pair_sub hFG (F.constantCoeff_nsmulSeries m) PowerSeries.constantCoeff_X
      (G.constantCoeff_nsmulSeries m) PowerSeries.constantCoeff_X ih (by simp)

/-- The coefficients of `hazewinkelIntegralFormalGroup p v` in total degrees below `p^(N + 1)`
depend only on `v₁, …, v_N`. -/
theorem coeff_hazewinkelIntegralFormalGroup_congr (p : ℕ) [Fact p.Prime] {v w : ℕ+ → R} {N : ℕ}
    (hv : ∀ i : ℕ+, (i : ℕ) ≤ N → v i = w i) {d : Fin 2 →₀ ℕ} (hd : d.degree < p ^ (N + 1)) :
    coeff d (hazewinkelIntegralFormalGroup p v).toPowerSeries =
      coeff d (hazewinkelIntegralFormalGroup p w).toPowerSeries := by
  let truncVar : ℕ+ → MvPolynomial ℕ+ ℤ := fun i ↦ if (i : ℕ) ≤ N then MvPolynomial.X i else 0
  have huniv : coeff d (universalHazewinkelIntegralFormalGroup p).toPowerSeries =
      coeff d (hazewinkelIntegralFormalGroup p truncVar).toPowerSeries := by
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [← coeff_map, ← FormalGroup.map_toPowerSeries,
      map_intCast_universalHazewinkelIntegralFormalGroup, ← coeff_map,
      ← FormalGroup.map_toPowerSeries, map_hazewinkelIntegralFormalGroup,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
    exact coeff_hazewinkelFormalGroup_congr (fun i hi ↦ by simp [truncVar, hi]) hd
  have heval (u : ℕ+ → R) : coeff d (hazewinkelIntegralFormalGroup p u).toPowerSeries =
      coeff d (hazewinkelIntegralFormalGroup p
        (fun i : ℕ+ ↦ if (i : ℕ) ≤ N then u i else 0)).toPowerSeries := by
    rw [hazewinkelIntegralFormalGroup_def p, FormalGroup.map_toPowerSeries, coeff_map, huniv,
      ← coeff_map, ← FormalGroup.map_toPowerSeries, map_hazewinkelIntegralFormalGroup]
    congr 3; funext i; dsimp only [Function.comp_apply, truncVar]; split_ifs <;> simp
  rw [heval v, heval w]
  congr 3; funext i; split_ifs with hi <;> [exact hv i hi; rfl]

/-- The coefficients of `[m]_(F_v)(X)` below degree `p^(N + 1)` depend only on `v₁, …, v_N`. -/
theorem coeff_nsmulSeries_hazewinkelIntegralFormalGroup_congr (p : ℕ) [Fact p.Prime]
    {v w : ℕ+ → R} {N k : ℕ} (hv : ∀ i : ℕ+, (i : ℕ) ≤ N → v i = w i)
    (hk : k < p ^ (N + 1)) (m : ℕ) :
    PowerSeries.coeff k ((hazewinkelIntegralFormalGroup p v).nsmulSeries m) =
      PowerSeries.coeff k ((hazewinkelIntegralFormalGroup p w).nsmulSeries m) := by
  have hFG : ((p ^ (N + 1) : ℕ) : ℕ∞) ≤
      ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries).order :=
    le_order fun d hd ↦ by
      rw [map_sub, coeff_hazewinkelIntegralFormalGroup_congr p hv (by exact_mod_cast hd), sub_self]
  rw [← sub_eq_zero, ← map_sub]
  refine PowerSeries.coeff_of_lt_order k ?_
  rw [PowerSeries.order_eq_order]
  exact (Nat.cast_lt.mpr hk).trans_le (le_order_nsmulSeries_sub hFG m)

end Truncation

/-! ### Vanishing of the first `n - 1` generators and congruences modulo `(v₁, …, v_(n - 1))` -/

section LeadingCoeff

variable {K R : Type*} [CommRing K] [Algebra ℚ K] [CommRing R]

/-- If `v₁ = ⋯ = v_(n - 1) = 0`, then `mₖ(v) = 0` for `1 ≤ k < n`. -/
theorem hazewinkelLogCoeff_eq_zero_of_forall_lt {p : ℕ} {v : ℕ+ → K} {n k : ℕ}
    (hv : ∀ i : ℕ+, (i : ℕ) < n → v i = 0) (hk₁ : 1 ≤ k) (hkn : k < n) :
    hazewinkelLogCoeff p v k = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [hazewinkelLogCoeff_congr (w := 0) (N := n - 1) (fun i hi ↦ hv i (by omega)) (by omega),
    hazewinkelLogCoeff_zero_succ]

/-- If `v₁ = ⋯ = v_(n - 1) = 0`, then `mₙ(v) = p⁻¹ vₙ`. -/
theorem hazewinkelLogCoeff_eq_of_forall_lt {p : ℕ} {v : ℕ+ → K} (n : ℕ+)
    (hv : ∀ i < n, v i = 0) :
    hazewinkelLogCoeff p v n = (p : ℚ)⁻¹ • v n := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero n.ne_zero
  rw [hm, hazewinkelLogCoeff_succ, sum_eq_single 0]
  · simp [show m.succPNat = n from PNat.eq (by rw [Nat.succPNat_coe, ← hm])]
  · intro i hi hi0; rw [mem_range] at hi
    rw [hazewinkelLogCoeff_eq_zero_of_forall_lt (n := (n : ℕ)) hv (by omega) (by omega), zero_mul]
  · simp

/-- If `v₁ = ⋯ = v_(n - 1) = 0`, Hazewinkel's logarithm has no nonlinear terms below degree
`pⁿ`. -/
theorem coeff_hazewinkelLog_eq_zero_of_forall_lt {p : ℕ} {v : ℕ+ → K} {n k : ℕ}
    (hv : ∀ i : ℕ+, (i : ℕ) < n → v i = 0) (hk₂ : 2 ≤ k) (hk : k < p ^ n) :
    PowerSeries.coeff k (hazewinkelLog p v).toPowerSeries = 0 := by
  rcases n with _ | m
  · simp at hk; omega
  · rw [coeff_hazewinkelLog_congr (w := 0) (N := m) (fun i hi ↦ hv i (by omega)) hk,
      hazewinkelLog_zero, FormalCoordinate.toPowerSeries_one, PowerSeries.coeff_X,
      ite_eq_right (by omega)]

/-- Over a `ℚ`-algebra, if `v₁ = ⋯ = v_(n - 1) = 0`, then the coefficient of `X^(pⁿ)` in
`[p]_(F_v)(X)` is `(1 - p^(pⁿ - 1)) vₙ`. -/
theorem coeff_pow_nsmulSeries_hazewinkelFormalGroup_of_forall_lt {p : ℕ} [hp : Fact p.Prime]
    {v : ℕ+ → K} (n : ℕ+) (hv : ∀ i < n, v i = 0) :
    PowerSeries.coeff (p ^ (n : ℕ)) ((hazewinkelFormalGroup p v).nsmulSeries p) =
      (1 - (p : K) ^ (p ^ (n : ℕ) - 1)) * v n := by
  set F := hazewinkelFormalGroup p v
  set f := (hazewinkelLog p v).toPowerSeries
  set g := F.nsmulSeries p
  have hp1 : 1 < p ^ (n : ℕ) := Nat.one_lt_pow n.ne_zero hp.out.one_lt
  have hford : ((p ^ (n : ℕ) : ℕ) : ℕ∞) ≤ (f - PowerSeries.X).order :=
    PowerSeries.nat_le_order _ _ fun k hk ↦ by
      rcases k with _ | _ | k'
      · rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply,
          (hazewinkelLog p v).constantCoeff_toPowerSeries, PowerSeries.coeff_zero_X, sub_zero]
      · rw [map_sub, coeff_one_hazewinkelLog, PowerSeries.coeff_one_X, sub_self]
      · rw [map_sub, coeff_hazewinkelLog_eq_zero_of_forall_lt (n := (n : ℕ)) hv (by omega) hk,
          PowerSeries.coeff_X, ite_eq_right (by omega), sub_zero]
  have hsplit : g + (f - PowerSeries.X).subst g = p • f := by
    have hg' : PowerSeries.HasSubst g := .of_constantCoeff_zero' (F.constantCoeff_nsmulSeries p)
    simpa [F, f, g, PowerSeries.subst_sub hg', PowerSeries.subst_X hg'] using
      F.subst_nsmulSeries_log p
  have hkey := congrArg (PowerSeries.coeff (p ^ (n : ℕ))) hsplit
  rw [map_add, PowerSeries.coeff_subst_eq_mul_pow (F.constantCoeff_nsmulSeries p) hford,
    Algebra.algebraMap_self, RingHom.id_apply, map_sub, coeff_hazewinkelLog_pow v hp.out.one_lt,
    hazewinkelLogCoeff_eq_of_forall_lt n hv, PowerSeries.coeff_X, ite_eq_right hp1.ne', sub_zero,
    F.coeff_one_nsmulSeries, map_nsmul, nsmul_eq_mul, coeff_hazewinkelLog_pow v hp.out.one_lt,
    hazewinkelLogCoeff_eq_of_forall_lt n hv] at hkey
  have hcancel : (p : K) * ((p : ℚ)⁻¹ • v n) = v n := by
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_inv_smul₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero)]
  have hpow : (p : K) ^ p ^ (n : ℕ) = (p : K) * (p : K) ^ (p ^ (n : ℕ) - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hp1.le, pow_succ']
  have hmul : ((p : ℚ)⁻¹ • v n) * (p : K) ^ p ^ (n : ℕ) = (p : K) ^ (p ^ (n : ℕ) - 1) * v n := by
    rw [hpow, show ((p : ℚ)⁻¹ • v n) * ((p : K) * (p : K) ^ (p ^ (n : ℕ) - 1)) =
      (p : K) ^ (p ^ (n : ℕ) - 1) * ((p : K) * ((p : ℚ)⁻¹ • v n)) by ring, hcancel]
  rw [hmul, hcancel] at hkey; linear_combination hkey

/-- If `v₁ = ⋯ = v_(n - 1) = 0`, then `[m]_(F_v)(X)` has no nonlinear terms below degree `pⁿ`. -/
theorem coeff_nsmulSeries_hazewinkelIntegralFormalGroup_eq_zero_of_forall_lt (p : ℕ) [Fact p.Prime]
    {v : ℕ+ → R} {n k : ℕ} (hv : ∀ i : ℕ+, (i : ℕ) < n → v i = 0)
    (hk₂ : 2 ≤ k) (hk : k < p ^ n) (m : ℕ) :
    PowerSeries.coeff k ((hazewinkelIntegralFormalGroup p v).nsmulSeries m) = 0 := by
  rcases n with _ | n'
  · simp at hk; omega
  · rw [coeff_nsmulSeries_hazewinkelIntegralFormalGroup_congr p (v := v) (w := 0) (N := n')
      (fun i hi ↦ hv i (by omega)) hk m, hazewinkelIntegralFormalGroup_zero,
      FormalGroup.nsmulSeries_𝔾ₐ, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_X,
      ite_eq_right (by omega), mul_zero]

/-- Over any commutative ring `R`, if `v₁ = ⋯ = v_(n - 1) = 0`, then the coefficient of
`X^(pⁿ)` in `[p]_(F_v)(X)` is `(1 - p^(pⁿ - 1)) vₙ`. -/
theorem coeff_pow_nsmulSeries_hazewinkelIntegralFormalGroup_of_forall_lt (p : ℕ) [Fact p.Prime]
    {v : ℕ+ → R} (n : ℕ+) (hv : ∀ i < n, v i = 0) :
    PowerSeries.coeff (p ^ (n : ℕ)) ((hazewinkelIntegralFormalGroup p v).nsmulSeries p) =
      (1 - (p : R) ^ (p ^ (n : ℕ) - 1)) * v n := by
  let killBelow : ℕ+ → MvPolynomial ℕ+ ℤ := fun i ↦ if i < n then 0 else MvPolynomial.X i
  have huniv : PowerSeries.coeff (p ^ (n : ℕ))
      ((hazewinkelIntegralFormalGroup p killBelow).nsmulSeries p) =
      (1 - (p : MvPolynomial ℕ+ ℤ) ^ (p ^ (n : ℕ) - 1)) * MvPolynomial.X n := by
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [← FormalGroup.coeff_nsmulSeries_map, map_hazewinkelIntegralFormalGroup,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
      coeff_pow_nsmulSeries_hazewinkelFormalGroup_of_forall_lt n
        (fun i hi ↦ by simp [killBelow, hi])]
    simp [killBelow]
  have hmap := FormalGroup.coeff_nsmulSeries_map (hazewinkelIntegralFormalGroup p killBelow)
    (MvPolynomial.eval₂Hom (Int.castRingHom R) v) p (p ^ (n : ℕ))
  rw [map_hazewinkelIntegralFormalGroup, show (MvPolynomial.eval₂Hom (Int.castRingHom R) v) ∘
      killBelow = v from funext fun i ↦ by
    dsimp only [Function.comp_apply, killBelow]; split_ifs with hi
    exacts [(map_zero _).trans (hv i hi).symm, MvPolynomial.eval₂Hom_X' _ _ _]] at hmap
  rw [hmap, huniv, map_mul, map_sub, map_one, map_pow, map_natCast, MvPolynomial.eval₂Hom_X']

/-- For any family `v : ℕ+ → R`, the nonlinear coefficients of `[m]_(F_v)(X)` below degree `pⁿ` lie
in the ideal generated by `v₁, …, v_(n - 1)`. -/
theorem coeff_nsmulSeries_hazewinkelIntegralFormalGroup_mem_span (p : ℕ) [Fact p.Prime]
    (v : ℕ+ → R) {n k : ℕ} (hk₂ : 2 ≤ k) (hk : k < p ^ n) (m : ℕ) :
    PowerSeries.coeff k ((hazewinkelIntegralFormalGroup p v).nsmulSeries m) ∈
      Ideal.span (v '' {i : ℕ+ | (i : ℕ) < n}) := by
  set J := Ideal.span (v '' {i : ℕ+ | (i : ℕ) < n})
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← FormalGroup.coeff_nsmulSeries_map,
    map_hazewinkelIntegralFormalGroup]
  exact coeff_nsmulSeries_hazewinkelIntegralFormalGroup_eq_zero_of_forall_lt p
    (v := Ideal.Quotient.mk J ∘ v)
    (fun i hi ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, hi, rfl⟩)) hk₂ hk m

/-- For any family `v : ℕ+ → R` and `n : ℕ+`, the coefficient of `X^(pⁿ)` in `[p]_(F_v)(X)` is
congruent to `(1 - p^(pⁿ - 1)) vₙ` modulo `(v₁, …, v_(n - 1))`. -/
theorem coeff_pow_nsmulSeries_hazewinkelIntegralFormalGroup_sub_mem_span (p : ℕ) [Fact p.Prime]
    (v : ℕ+ → R) (n : ℕ+) :
    PowerSeries.coeff (p ^ (n : ℕ)) ((hazewinkelIntegralFormalGroup p v).nsmulSeries p) -
        (1 - (p : R) ^ (p ^ (n : ℕ) - 1)) * v n ∈
      Ideal.span (v '' {i : ℕ+ | (i : ℕ) < n}) := by
  set J := Ideal.span (v '' {i : ℕ+ | (i : ℕ) < n})
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← FormalGroup.coeff_nsmulSeries_map,
    map_hazewinkelIntegralFormalGroup,
    coeff_pow_nsmulSeries_hazewinkelIntegralFormalGroup_of_forall_lt p n
      (v := Ideal.Quotient.mk J ∘ v)
      fun i hi ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, hi, rfl⟩)]
  simp

end LeadingCoeff

/-! ### Ravenel's modulo-`p` `[p]`-series formula -/

section RatModP

variable {K : Type*} [CommRing K] [Algebra ℚ K]

private theorem coeff_pow_subst_smul_X_pow_hazewinkelLog {p : ℕ} (hp : 1 < p) (v : ℕ+ → K)
    (j : ℕ+) (n : ℕ) :
    PowerSeries.coeff (p ^ n) ((hazewinkelLog p v).toPowerSeries.subst
        (v j • (PowerSeries.X : PowerSeries K) ^ p ^ (j : ℕ))) =
      if (j : ℕ) ≤ n then
        hazewinkelLogCoeff p v (n - (j : ℕ)) * v j ^ p ^ (n - (j : ℕ))
      else 0 := by
  have hc₀ : constantCoeff (v j • (PowerSeries.X : PowerSeries K) ^ p ^ (j : ℕ)) = 0 := by
    rw [← PowerSeries.constantCoeff_eq]
    simp [zero_pow (pow_ne_zero (j : ℕ) (by omega : p ≠ 0))]
  rw [← PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_subst_eq_sum_range_degree hc₀]
  have hterm (r : ℕ) : coeff (Finsupp.single () (p ^ n))
      ((v j • (PowerSeries.X : PowerSeries K) ^ p ^ (j : ℕ)) ^ r) =
      if p ^ n = p ^ (j : ℕ) * r then v j ^ r else 0 := by
    rw [smul_pow, ← pow_mul, PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_smul,
      PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp_rw [hterm, smul_eq_mul, mul_ite, mul_zero]
  split_ifs with hjn
  · rw [sum_eq_single (p ^ (n - (j : ℕ)))]
    · rw [ite_eq_left (by rw [← pow_add, Nat.add_sub_of_le hjn]), coeff_hazewinkelLog_pow v hp]
    · intro r _ hr
      refine ite_eq_right fun heq ↦
        hr (Nat.mul_left_cancel (pow_pos (by omega : 0 < p) (j : ℕ)) ?_).symm
      rw [← pow_add, Nat.add_sub_of_le hjn, heq]
    · intro hmem; exfalso; apply hmem
      rw [mem_range, Finsupp.degree_single]
      exact Nat.lt_succ_of_le (Nat.pow_le_pow_right (by omega) (Nat.sub_le n (j : ℕ)))
  · refine sum_eq_zero fun r _ ↦ ite_eq_right fun heq ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · exact absurd heq (pow_ne_zero n (by omega))
    · exact absurd heq ((Nat.pow_lt_pow_right hp (not_le.mp hjn)).trans_le
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hr0))).ne

private theorem coeff_subst_smul_X_pow_hazewinkelLog_eq_zero {p : ℕ} (hp : p ≠ 0) (v : ℕ+ → K)
    (j : ℕ+) {k : ℕ} (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k ((hazewinkelLog p v).toPowerSeries.subst
        (v j • (PowerSeries.X : PowerSeries K) ^ p ^ (j : ℕ))) = 0 := by
  have hc₀ : constantCoeff (v j • (PowerSeries.X : PowerSeries K) ^ p ^ (j : ℕ)) = 0 := by
    rw [← PowerSeries.constantCoeff_eq]; simp [zero_pow (pow_ne_zero (j : ℕ) hp)]
  rw [← PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_subst_eq_sum_range_degree hc₀]
  refine sum_eq_zero fun r _ ↦ ?_
  rw [smul_pow, ← pow_mul, PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_smul,
    PowerSeries.coeff_X_pow]
  split_ifs with heq
  · rw [coeff_hazewinkelLog_eq_zero v fun i hi ↦ hk ((j : ℕ) + i) (by rw [pow_add, hi, heq]),
      zero_smul]
  · simp

private theorem sum_hazewinkelLogCoeff_mul_pow_of_support {p : ℕ} (hp : p ≠ 0) {v : ℕ+ → K}
    {s : Finset ℕ+} (hv : ∀ j ∉ s, v j = 0) (m : ℕ) :
    (∑ j ∈ s, if (j : ℕ) ≤ m + 1 then
        hazewinkelLogCoeff p v (m + 1 - (j : ℕ)) * v j ^ p ^ (m + 1 - (j : ℕ)) else 0) =
      ∑ i ∈ range (m + 1), hazewinkelLogCoeff p v i * v (m - i).succPNat ^ p ^ i := by
  let g : ℕ+ → K := fun j ↦ if (j : ℕ) ≤ m + 1 then
    hazewinkelLogCoeff p v (m + 1 - (j : ℕ)) * v j ^ p ^ (m + 1 - (j : ℕ)) else 0
  let t : Finset ℕ+ := (range (m + 1)).map ⟨Nat.succPNat, Nat.succPNat_injective⟩
  have hst₁ : ∑ j ∈ s, g j = ∑ j ∈ s ∪ t, g j := sum_subset subset_union_left fun j _ hjs ↦ by
    dsimp only [g]; split_ifs <;> [rw [hv j hjs, zero_pow (pow_ne_zero _ hp), mul_zero]; rfl]
  have hst₂ : ∑ j ∈ t, g j = ∑ j ∈ s ∪ t, g j := sum_subset subset_union_right fun j _ hjt ↦
    ite_eq_right fun hjm ↦ hjt <| mem_map.mpr
      ⟨j.natPred, mem_range.mpr (by have := PNat.natPred_add_one j; omega), j.succPNat_natPred⟩
  rw [hst₁, ← hst₂, sum_map, ← sum_range_reflect]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [mem_range] at hi; dsimp only [Function.Embedding.coeFn_mk, g]
  rw [Nat.add_sub_cancel, ite_eq_left (by simp),
    show m + 1 - ((m - i).succPNat : ℕ) = i by simp; omega]

/-- Over a `ℚ`-algebra, when `v` vanishes outside a finite set `s`, Hazewinkel's logarithm
satisfies `p f_v(X) - ∑_{j ∈ s} f_v(vⱼ X^(pʲ)) = p X`. -/
theorem nsmul_hazewinkelLog_sub_sum_subst {p : ℕ} (hp : 1 < p) {v : ℕ+ → K}
    {s : Finset ℕ+} (hv : ∀ j ∉ s, v j = 0) :
    p • (hazewinkelLog p v).toPowerSeries -
      ∑ j ∈ s, (hazewinkelLog p v).toPowerSeries.subst
        (v j • (PowerSeries.X : PowerSeries K) ^ p ^ (j : ℕ)) =
      (p : K) • PowerSeries.X := by
  ext k
  rw [map_sub, map_sum, map_nsmul, nsmul_eq_mul, PowerSeries.coeff_smul, smul_eq_mul]
  by_cases hk : ∃ n, p ^ n = k
  · obtain ⟨_ | m, rfl⟩ := hk <;> simp_rw [coeff_pow_subst_smul_X_pow_hazewinkelLog hp v _ _]
    · simp only [pow_zero, coeff_one_hazewinkelLog, mul_one, PowerSeries.coeff_one_X]
      rw [sum_eq_zero fun j _ ↦ ite_eq_right (not_le.mpr j.pos), sub_zero]
    · rw [coeff_hazewinkelLog_pow v hp, natCast_mul_hazewinkelLogCoeff_succ v (by omega),
        PowerSeries.coeff_X, ite_eq_right (Nat.one_lt_pow m.succ_ne_zero hp).ne', mul_zero,
        sum_hazewinkelLogCoeff_mul_pow_of_support (by omega) hv m, sub_self]
  · push Not at hk
    rw [coeff_hazewinkelLog_eq_zero v hk, mul_zero, PowerSeries.coeff_X,
      ite_eq_right fun h1 ↦ hk 0 (by simp [h1]), mul_zero,
      sum_eq_zero fun j _ ↦ coeff_subst_smul_X_pow_hazewinkelLog_eq_zero (by omega) v j hk,
      sub_zero]

private theorem subst_hazewinkelLog_curve_sub_eq_smul_X {p : ℕ} (hp : 1 < p) {v : ℕ+ → K}
    {s : Finset ℕ+} (hv : ∀ j ∉ s, v j = 0) :
    (hazewinkelLog p v).toPowerSeries.subst
      (p • (hazewinkelFormalGroup p v).tautologicalCurve -
        ∑ j ∈ s, (hazewinkelFormalGroup p v).monomialCurve (p ^ (j : ℕ))
          (pow_ne_zero _ (by omega)) (v j)).toPowerSeries =
      (p : K) • PowerSeries.X := by
  let FQ := hazewinkelFormalGroup p v
  let L : FQ.Curve →+ PowerSeries K :=
    FormalGroup.Curve.additiveToPowerSeriesHom.comp FQ.logHom.mapCurve
  have hL (γ : FQ.Curve) : L γ = (hazewinkelLog p v).toPowerSeries.subst γ.toPowerSeries := by
    rw [AddMonoidHom.comp_apply, FormalGroup.Curve.additiveToPowerSeriesHom_apply,
      FormalGroupHom.toPowerSeries_mapCurve, FormalGroup.logHom_toPowerSeries,
      log_hazewinkelFormalGroup]
  rw [← hL, map_sub, map_nsmul, map_sum, hL, FormalGroup.toPowerSeries_tautologicalCurve,
    PowerSeries.X_subst]
  simp_rw [hL, FormalGroup.toPowerSeries_monomialCurve]
  exact nsmul_hazewinkelLog_sub_sum_subst hp hv

end RatModP

section IntegralModP

variable {R : Type*} [CommRing R]

private theorem exists_coeff_eq_natCast_mul_of_subst_hazewinkelLog (p : ℕ) [hp : Fact p.Prime]
    {vs : ℕ+ → MvPolynomial ℕ+ ℤ} (hvs : ∀ j, vs j = MvPolynomial.X j ∨ vs j = 0)
    {δ : PowerSeries (MvPolynomial ℕ+ ℚ)} (hδ₀ : PowerSeries.constantCoeff δ = 0)
    (hlog : (hazewinkelLog p (MvPolynomial.map (Int.castRingHom ℚ) ∘ vs)).toPowerSeries.subst δ =
      (p : MvPolynomial ℕ+ ℚ) • PowerSeries.X) (k : ℕ) :
    ∃ g : MvPolynomial ℕ+ ℤ, PowerSeries.coeff k δ =
      (p : MvPolynomial ℕ+ ℚ) * MvPolynomial.map (Int.castRingHom ℚ) g := by
  let ι : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let vsQ : ℕ+ → MvPolynomial ℕ+ ℚ := ι ∘ vs
  let σ : MvPolynomial ℕ+ ℚ →+* MvPolynomial ℕ+ ℚ := (MvPolynomial.expand p).toRingHom
  have hσA : Set.MapsTo σ ι.range ι.range := by
    rintro _ ⟨g, rfl⟩; exact ⟨MvPolynomial.expand p g, MvPolynomial.map_expand p _ g⟩
  have hsA (i : ℕ) : (p : MvPolynomial ℕ+ ℚ) * hazewinkelFunctionalCoeff p vsQ i ∈ ι.range := by
    rcases i with _ | i
    · simp
    · rw [show i + 1 = (i.succPNat : ℕ) from rfl, hazewinkelFunctionalCoeff_pos, mul_smul_comm,
        inv_natCast_smul_natCast_mul hp.out.ne_zero]
      exact ⟨vs i.succPNat, rfl⟩
  have hσv (j : ℕ+) : σ (vsQ j) = vsQ j ^ p := by
    rcases hvs j with hj | hj <;> simp [vsQ, ι, σ, hj, zero_pow hp.out.ne_zero]
  have hf := satisfiesFunctionalEquation_hazewinkelLog vsQ hp.out.one_lt σ hσv ι.range
  have hsubst (d : Unit →₀ ℕ) : ∃ b ∈ ι.range, coeff d ((hazewinkelLog p vsQ).toPowerSeries.subst
      (δ : MvPowerSeries Unit (MvPolynomial ℕ+ ℚ))) = (p : MvPolynomial ℕ+ ℚ) * b := by
    rw [Finsupp.unique_single d, PowerSeries.coeff_coeToMvPowerSeries, hlog,
      PowerSeries.coeff_smul, PowerSeries.coeff_X, smul_eq_mul]
    split_ifs <;> [exact ⟨1, ι.range.one_mem, rfl⟩; exact ⟨0, ι.range.zero_mem, rfl⟩]
  obtain ⟨_, ⟨g, rfl⟩, ha⟩ := (hf.exists_coeff_subst_eq_mul_iff hσA hsA
    (hazewinkelLog p vsQ).constantCoeff_toPowerSeries ⟨1, ι.range.one_mem, by simp⟩
    (by rwa [← PowerSeries.constantCoeff_eq])).mp hsubst (Finsupp.single () k)
  exact ⟨g, by rwa [← PowerSeries.coeff_coeToMvPowerSeries]⟩

private theorem toPowerSeries_sum_monomialCurve_map {A B : Type*} [CommRing A] [CommRing B]
    {F : FormalGroup A} {G : FormalGroup B} [F.IsComm] [G.IsComm]
    (φ : A →+* B) (hFG : F.map φ = G) (s : Finset ℕ+) (e : ℕ+ → ℕ) (he : ∀ j, e j ≠ 0)
    (u : ℕ+ → A) (v : ℕ+ → B) (huv : ∀ j, φ (u j) = v j) :
    PowerSeries.map φ (∑ j ∈ s, F.monomialCurve (e j) (he j) (u j)).toPowerSeries =
      (∑ j ∈ s, G.monomialCurve (e j) (he j) (v j)).toPowerSeries := by
  subst hFG; simp_rw [← huv, ← FormalGroup.Curve.toPowerSeries_map, map_sum,
    FormalGroup.map_monomialCurve]

private theorem natCast_dvd_nsmulSeries_sub_universal (p : ℕ) [hp : Fact p.Prime] (s : Finset ℕ+) :
    let vs : ℕ+ → MvPolynomial ℕ+ ℤ := fun j ↦ if j ∈ s then MvPolynomial.X j else 0
    let Fs := hazewinkelIntegralFormalGroup p vs
    ((p : ℕ) : PowerSeries (MvPolynomial ℕ+ ℤ)) ∣
      Fs.nsmulSeries p - (∑ j ∈ s, Fs.monomialCurve (p ^ (j : ℕ))
        (pow_ne_zero _ hp.out.ne_zero) (vs j)).toPowerSeries := by
  intro vs Fs
  let hpow (j : ℕ+) : p ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  let γ : Fs.Curve := ∑ j ∈ s, Fs.monomialCurve (p ^ (j : ℕ)) (hpow j) (vs j)
  let ι : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  have hι : Function.Injective ι := MvPolynomial.map_injective _ Int.cast_injective
  let FQ := hazewinkelFormalGroup p (ι ∘ vs)
  have hFQ : Fs.map ι = FQ := by
    rw [map_hazewinkelIntegralFormalGroup, hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  have hdvd (k : ℕ) : (p : MvPolynomial ℕ+ ℤ) ∣
      PowerSeries.coeff k (p • Fs.tautologicalCurve - γ).toPowerSeries := by
    let δQ : FQ.Curve :=
      p • FQ.tautologicalCurve - ∑ j ∈ s, FQ.monomialCurve (p ^ (j : ℕ)) (hpow j) (ι (vs j))
    have hlog := subst_hazewinkelLog_curve_sub_eq_smul_X (v := ι ∘ vs) (s := s) hp.out.one_lt
      fun j hj ↦ by dsimp only [vs, Function.comp_apply]; rw [ite_eq_right hj, map_zero]
    obtain ⟨g, hg⟩ := exists_coeff_eq_natCast_mul_of_subst_hazewinkelLog p
      (fun j ↦ by dsimp only [vs]; split_ifs <;> simp) δQ.constantCoeff_toPowerSeries hlog k
    refine ⟨g, hι ?_⟩
    rw [map_mul, map_natCast, ← hg, ← PowerSeries.coeff_map]
    congr 1
    have hmap : ∀ {G : FormalGroup (MvPolynomial ℕ+ ℚ)} [G.IsComm], Fs.map ι = G →
        PowerSeries.map ι (p • Fs.tautologicalCurve - γ).toPowerSeries =
        (p • G.tautologicalCurve -
          ∑ j ∈ s, G.monomialCurve (p ^ (j : ℕ)) (hpow j) (ι (vs j))).toPowerSeries := by
      rintro G _ rfl
      rw [← FormalGroup.Curve.toPowerSeries_map, map_sub, map_nsmul,
        FormalGroup.map_tautologicalCurve, map_sum]
      simp only [FormalGroup.map_monomialCurve]
    exact hmap hFQ
  set I := Ideal.span {(p : MvPolynomial ℕ+ ℤ)}
  set q := Ideal.Quotient.mk I
  have hzero : FormalGroup.Curve.map q (p • Fs.tautologicalCurve - γ) = 0 := by
    ext k
    rw [FormalGroup.Curve.toPowerSeries_map, PowerSeries.coeff_map,
      FormalGroup.Curve.toPowerSeries_zero, map_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact hdvd k
  have heq : FormalGroup.Curve.map q (p • Fs.tautologicalCurve) = FormalGroup.Curve.map q γ :=
    sub_eq_zero.mp (by rwa [map_sub] at hzero)
  rw [← map_natCast PowerSeries.C, PowerSeries.C_dvd_iff_dvd_coeff]
  intro k
  rw [map_sub, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  simpa only [Function.comp_apply, FormalGroup.Curve.toPowerSeries_map, PowerSeries.coeff_map,
    FormalGroup.Curve.toPowerSeries_nsmul, FormalGroup.toPowerSeries_tautologicalCurve,
    PowerSeries.X_subst] using congrArg (PowerSeries.coeff k ∘ FormalGroup.Curve.toPowerSeries) heq

/-- **Ravenel's modulo-`p` `[p]`-series formula (finite support).** Over any commutative ring `R`,
if `v` vanishes outside a finite set `s`, then `p` divides every coefficient of
`[p]_(F_v)(X) - ∑^F_{j ∈ s} (vⱼ X^(pʲ))`. -/
theorem natCast_dvd_nsmulSeries_hazewinkelIntegralFormalGroup_sub_of_support (p : ℕ)
    [hp : Fact p.Prime] {v : ℕ+ → R} {s : Finset ℕ+} (hv : ∀ j ∉ s, v j = 0) :
    ((p : ℕ) : PowerSeries R) ∣
      (hazewinkelIntegralFormalGroup p v).nsmulSeries p -
        (∑ j ∈ s, (hazewinkelIntegralFormalGroup p v).monomialCurve
          (p ^ (j : ℕ)) (pow_ne_zero _ hp.out.ne_zero) (v j)).toPowerSeries := by
  let vs : ℕ+ → MvPolynomial ℕ+ ℤ := fun j ↦ if j ∈ s then MvPolynomial.X j else 0
  let ev := MvPolynomial.eval₂Hom (Int.castRingHom R) v
  have hcomp : ev ∘ vs = v := funext fun j ↦ by
    dsimp only [Function.comp_apply, vs]; split_ifs with hj
    exacts [MvPolynomial.eval₂Hom_X' _ _ _, (map_zero _).trans (hv j hj).symm]
  have hFG : (hazewinkelIntegralFormalGroup p vs).map ev = hazewinkelIntegralFormalGroup p v := by
    rw [map_hazewinkelIntegralFormalGroup, hcomp]
  have hdvd := map_dvd (PowerSeries.map ev) (natCast_dvd_nsmulSeries_sub_universal p s)
  rwa [map_natCast, map_sub, FormalGroup.map_nsmulSeries, hFG,
    toPowerSeries_sum_monomialCurve_map ev hFG s _ _ vs v (congrFun hcomp)] at hdvd

/-- In characteristic `p`, if `v` vanishes outside `s`, then `[p]_(F_v)(X)` is equal to the
formal-group sum `∑^F_{j ∈ s} (vⱼ X^(pʲ))`. -/
theorem nsmulSeries_hazewinkelIntegralFormalGroup_eq_of_support (p : ℕ) [hp : Fact p.Prime]
    [CharP R p] {v : ℕ+ → R} {s : Finset ℕ+} (hv : ∀ j ∉ s, v j = 0) :
    (hazewinkelIntegralFormalGroup p v).nsmulSeries p =
      (∑ j ∈ s, (hazewinkelIntegralFormalGroup p v).monomialCurve
        (p ^ (j : ℕ)) (pow_ne_zero _ hp.out.ne_zero) (v j)).toPowerSeries := by
  have hdvd := natCast_dvd_nsmulSeries_hazewinkelIntegralFormalGroup_sub_of_support p hv
  rwa [← map_natCast PowerSeries.C, CharP.cast_eq_zero R p, map_zero, zero_dvd_iff,
    sub_eq_zero] at hdvd

private theorem le_order_sum_curve_sub {ι : Type*} {F G : FormalGroup R} [F.IsComm] [G.IsComm]
    {M : ℕ} (hFG : (M : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order)
    (I : Finset ι) (γ : ι → F.Curve) (δ : ι → G.Curve)
    (hγδ : ∀ i ∈ I, (γ i).toPowerSeries = (δ i).toPowerSeries) :
    (M : ℕ∞) ≤ MvPowerSeries.order
      ((∑ i ∈ I, γ i).toPowerSeries - (∑ i ∈ I, δ i).toPowerSeries : PowerSeries R) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a J haJ ih =>
    rw [sum_insert haJ, sum_insert haJ, FormalGroup.Curve.toPowerSeries_add,
      FormalGroup.Curve.toPowerSeries_add]
    exact le_order_subst_pair_sub hFG
      (γ a).constantCoeff_toPowerSeries (∑ i ∈ J, γ i).constantCoeff_toPowerSeries
      (δ a).constantCoeff_toPowerSeries (∑ i ∈ J, δ i).constantCoeff_toPowerSeries
      (by simp [hγδ a (mem_insert_self a J)]) (ih fun i hi ↦ hγδ i (mem_insert_of_mem hi))

/-- **Ravenel's modulo-`p` `[p]`-series formula (truncated).** For any family `v : ℕ+ → R` and any
`N`, in every degree `k < p^(N + 1)` the prime `p` divides the difference between `[p]_(F_v)(X)`
and the formal-group sum `∑^F_{1 ≤ j ≤ N} (vⱼ X^(pʲ))`. -/
theorem natCast_dvd_coeff_nsmulSeries_hazewinkelIntegralFormalGroup_sub (p : ℕ)
    [hp : Fact p.Prime] (v : ℕ+ → R) {N k : ℕ} (hk : k < p ^ (N + 1)) :
    (p : R) ∣ PowerSeries.coeff k
      ((hazewinkelIntegralFormalGroup p v).nsmulSeries p -
        (∑ i ∈ range N, (hazewinkelIntegralFormalGroup p v).monomialCurve
          (p ^ (i + 1)) (pow_ne_zero _ hp.out.ne_zero) (v i.succPNat)).toPowerSeries) := by
  let v' : ℕ+ → R := fun j ↦ if (j : ℕ) ≤ N then v j else 0
  let s : Finset ℕ+ := (range N).map ⟨Nat.succPNat, Nat.succPNat_injective⟩
  have hv_eq (j : ℕ+) (hj : (j : ℕ) ≤ N) : v j = v' j := (ite_eq_left hj).symm
  have hv' (j : ℕ+) (hjs : j ∉ s) : v' j = 0 := ite_eq_right fun hjN ↦ hjs <| mem_map.mpr
    ⟨j.natPred, mem_range.mpr (by have := PNat.natPred_add_one j; omega), j.succPNat_natPred⟩
  have hFG : ((p ^ (N + 1) : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p v').toPowerSeries).order :=
    le_order fun d hd ↦ by
      rw [map_sub, coeff_hazewinkelIntegralFormalGroup_congr p hv_eq (by exact_mod_cast hd),
        sub_self]
  have hsum : PowerSeries.coeff k (∑ i ∈ range N, (hazewinkelIntegralFormalGroup p v).monomialCurve
        (p ^ (i + 1)) (pow_ne_zero _ hp.out.ne_zero) (v i.succPNat)).toPowerSeries =
      PowerSeries.coeff k (∑ j ∈ s, (hazewinkelIntegralFormalGroup p v').monomialCurve
        (p ^ (j : ℕ)) (pow_ne_zero _ hp.out.ne_zero) (v' j)).toPowerSeries := by
    rw [sum_map, ← sub_eq_zero, ← map_sub]
    refine PowerSeries.coeff_of_lt_order k ?_
    rw [PowerSeries.order_eq_order]
    refine (Nat.cast_lt.mpr hk).trans_le (le_order_sum_curve_sub hFG (range N) _ _ fun i hi ↦ ?_)
    rw [mem_range] at hi
    simp [Nat.succPNat_coe, hv_eq i.succPNat (by simp; omega)]
  rw [map_sub, coeff_nsmulSeries_hazewinkelIntegralFormalGroup_congr p hv_eq hk p, hsum, ← map_sub]
  exact (PowerSeries.C_dvd_iff_dvd_coeff (p : R) _).mp
    (by simpa only [map_natCast] using
      natCast_dvd_nsmulSeries_hazewinkelIntegralFormalGroup_sub_of_support p hv') k

/-- In characteristic `p`, for any family `v : ℕ+ → R` and any `k < p^(N + 1)`, the degree-`k`
coefficient of `[p]_(F_v)(X)` agrees with that of `∑^F_{1 ≤ j ≤ N} (vⱼ X^(pʲ))`. -/
theorem coeff_nsmulSeries_hazewinkelIntegralFormalGroup_eq_of_charP (p : ℕ) [hp : Fact p.Prime]
    [CharP R p] (v : ℕ+ → R) {N k : ℕ} (hk : k < p ^ (N + 1)) :
    PowerSeries.coeff k ((hazewinkelIntegralFormalGroup p v).nsmulSeries p) =
      PowerSeries.coeff k
        (∑ i ∈ range N, (hazewinkelIntegralFormalGroup p v).monomialCurve
          (p ^ (i + 1)) (pow_ne_zero _ hp.out.ne_zero) (v i.succPNat)).toPowerSeries := by
  have hdvd := natCast_dvd_coeff_nsmulSeries_hazewinkelIntegralFormalGroup_sub p v hk
  rwa [CharP.cast_eq_zero R p, zero_dvd_iff, map_sub, sub_eq_zero] at hdvd

end IntegralModP

end TauCeti
