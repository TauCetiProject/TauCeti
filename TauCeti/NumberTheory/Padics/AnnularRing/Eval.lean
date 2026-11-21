/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.NumberTheory.Padics.AnnularRing.Gauge
public import TauCeti.NumberTheory.Padics.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.Analysis.Normed.Group.NullFamily
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.Padics.Complex.Valuation
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Annulus evaluations on `ℤ_p⟦T, p/T⟧` and `H[1/T]`

Let `H = TauCeti.AnnularRing p` be the integral annular coefficient ring `ℤ_p⟦T, p/T⟧` and `A` be
any localization of `H` away from `T`. For any complete normed ring `K`, any bounded ring
homomorphism `f : ℤ_[p] →+* K` (satisfying `∃ C, ∀ a, ‖f a‖ ≤ C * ‖a‖`), and any unit `t : Kˣ` in
the open annulus `‖t‖ < 1` and `‖t⁻¹‖ < p`, the two-sided series `∑_{m ∈ ℤ} f(d_m) t ^ m`
converges absolutely in `K` for every `x ∈ H` and defines a ring homomorphism
`TauCeti.AnnularRing.eval₂ : AnnularRing p →+* K` sending `T ↦ t` and `U ↦ p t⁻¹`. Since `t` is a
unit, it extends uniquely to `TauCeti.AnnularRing.localizedEval₂ : A →+* K`. When `K` is
ultrametric, `eval₂` is uniformly bounded by `C` on `H` (`TauCeti.AnnularRing.norm_eval₂_le`).

We specialize this construction in two directions:
* `TauCeti.AnnularRing.eval` and `TauCeti.AnnularRing.localizedEvalAlgHom` as `ℤ_[p]`-algebra
  homomorphisms when `[Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]`.
* `TauCeti.AnnularRing.evalAt` and `TauCeti.AnnularRing.localizedEvalAt` for any complete normed
  division ring extension `K` of `ℚ_[p]` (such as `ℂ_[p]`) and any `t : K` with `p⁻¹ < ‖t‖ < 1`.

Every annulus evaluation is continuous for the `T`-adic topology on `H[1/T]`
(`TauCeti.AnnularRing.continuous_localizedEval₂`). Nevertheless, for the `T`-adic Tate gauge of
radius `α ∈ (0, 1)`, evaluation at `t` in a complete normed division ring `K / ℚ_[p]` is Lipschitz
(equivalently bounded by a constant multiple of the norm) if and only if `α = ‖t‖`
(`TauCeti.AnnularRing.not_lipschitzWith_localizedEvalAt_of_ne`): for `α < ‖t‖` the powers `T ^ n`
blow up `(‖t‖ / α) ^ n`, while for `‖t‖ < α` the negative powers `T ^ (-n)` blow up
`(α / ‖t‖) ^ n`.

The open annulus `p⁻¹ < ‖t‖ < 1` has no points in `ℚ_[p]`
(`TauCeti.AnnularRing.not_exists_padic_annulus`), since the value group of `ℚ_[p]` is `p ^ ℤ`.
Over `ℂ_[p]`, whose value group is `p ^ ℚ`, the family of evaluations at all `t : ℂ_[p]` with
`p⁻¹ < ‖t‖ < 1` is jointly injective on both `H` and `H[1/T]`
(`TauCeti.AnnularRing.eq_of_forall_evalAt_padicComplex_eq`,
`TauCeti.AnnularRing.eq_of_forall_localizedEvalAt_padicComplex_eq`).

## Main definitions

* `TauCeti.AnnularRing.eval₂`, `TauCeti.AnnularRing.localizedEval₂`: evaluation ring homomorphisms
  on `H` and `H[1/T]` into any complete normed ring `K`.
* `TauCeti.AnnularRing.eval`, `TauCeti.AnnularRing.localizedEvalAlgHom`: `ℤ_[p]`-algebra
  evaluations under `[Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]`.
* `TauCeti.AnnularRing.evalAt`, `TauCeti.AnnularRing.localizedEvalAt`: evaluations at `t : K` with
  `p⁻¹ < ‖t‖ < 1` in any complete normed division ring `K` over `ℚ_[p]`.

## Main results

* `TauCeti.AnnularRing.summable_norm_eval₂`, `TauCeti.AnnularRing.summable_eval₂`: absolute
  convergence of the bilateral evaluation series on `H`.
* `TauCeti.AnnularRing.hasSum_eval₂`, `TauCeti.AnnularRing.hasSum_localizedEval₂`: bilateral series
  expansions of evaluations on `H` and `H[1/T]`.
* `TauCeti.AnnularRing.eval₂_ofPowerSeriesT`, `TauCeti.AnnularRing.eval₂_ofPowerSeriesU`:
  evaluations of power series in `T` and `U = p / T`.
* `TauCeti.AnnularRing.continuous_localizedEval₂`: continuity for the `T`-adic topology on `H[1/T]`.
* `TauCeti.AnnularRing.norm_localizedEvalAt_le_of_eq`,
  `TauCeti.AnnularRing.not_exists_bound_localizedEvalAt_of_ne`,
  `TauCeti.AnnularRing.not_lipschitzWith_localizedEvalAt_of_ne`: exact comparison with the
  `α`-gauge.
* `TauCeti.AnnularRing.not_exists_padic_annulus`: `ℚ_[p]` contains no points of `p⁻¹ < ‖t‖ < 1`.
* `TauCeti.AnnularRing.eq_of_forall_evalAt_padicComplex_eq`,
  `TauCeti.AnnularRing.eq_of_forall_localizedEvalAt_padicComplex_eq`: joint injectivity of
  `ℂ_[p]`-evaluations on the open annulus.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.AnnularRing

private theorem one_lt_p {p : ℕ} [Fact p.Prime] : (1 : ℝ) < p :=
  mod_cast (Fact.out : p.Prime).one_lt

private theorem p_pos {p : ℕ} [Fact p.Prime] : (0 : ℝ) < p :=
  zero_lt_one.trans one_lt_p

/-! ### General annulus evaluations into complete normed rings -/

section LiftAway

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Ring K]

/-- Factor a ring homomorphism `g : H →+* K` through the commutative subring
`Subring.center (Subring.centralizer (Set.range g))`. -/
private def ringHomToCenter (g : AnnularRing p →+* K) :
    AnnularRing p →+* Subring.center (Subring.centralizer (Set.range g)) where
  toFun a := ⟨⟨g a, Subring.mem_centralizer_iff.mpr fun _ ⟨b, hb⟩ ↦ by
      rw [← hb, ← map_mul, mul_comm b a, map_mul]⟩,
    Subring.mem_center_iff.mpr fun ⟨_, hc⟩ ↦
      Subtype.ext (Subring.mem_centralizer_iff.mp hc (g a) ⟨a, rfl⟩).symm⟩
  map_one' := Subtype.ext (Subtype.ext g.map_one)
  map_mul' a b := Subtype.ext (Subtype.ext (g.map_mul a b))
  map_zero' := Subtype.ext (Subtype.ext g.map_zero)
  map_add' a b := Subtype.ext (Subtype.ext (g.map_add a b))

private theorem isUnit_ringHomToCenter_T (g : AnnularRing p →+* K) (hg : IsUnit (g T)) :
    IsUnit (ringHomToCenter g T) := by
  have hinv_mem : ((hg.unit⁻¹ : Kˣ) : K) ∈ Subring.centralizer (Set.range g) :=
    Subring.mem_centralizer_iff.mpr fun _ ⟨b, hb⟩ ↦ by
      have hcomm : Commute (g b) (hg.unit : K) := by
        rw [commute_iff_eq, IsUnit.unit_spec, ← map_mul, mul_comm b T, map_mul]
      rw [← hb]
      exact hcomm.units_inv_right.eq
  refine ⟨⟨ringHomToCenter g T, ⟨⟨((hg.unit⁻¹ : Kˣ) : K), hinv_mem⟩,
      Subring.mem_center_iff.mpr fun ⟨c, hc⟩ ↦ Subtype.ext <| by
        have hcomm : Commute (hg.unit : K) c := by
          rw [commute_iff_eq, IsUnit.unit_spec]
          exact Subring.mem_centralizer_iff.mp hc (g T) ⟨T, rfl⟩
        exact hcomm.units_inv_left.eq.symm⟩,
    Subtype.ext (Subtype.ext hg.mul_val_inv), Subtype.ext (Subtype.ext hg.val_inv_mul)⟩, rfl⟩

/-- Lift a ring homomorphism `g : H →+* K` (into a possibly non-commutative ring `K`) along
`IsLocalization.Away T A` when `g T` is a unit. -/
private def liftAwayOfIsUnit {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] (g : AnnularRing p →+* K) (hg : IsUnit (g T)) :
    A →+* K :=
  ((Subring.centralizer (Set.range g)).subtype.comp
    (Subring.center (Subring.centralizer (Set.range g))).subtype).comp
    (IsLocalization.Away.lift (x := (T : AnnularRing p)) (isUnit_ringHomToCenter_T g hg))

private theorem liftAwayOfIsUnit_algebraMap {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] (g : AnnularRing p →+* K) (hg : IsUnit (g T))
    (a : AnnularRing p) :
    liftAwayOfIsUnit (A := A) g hg (algebraMap (AnnularRing p) A a) = g a := by
  simp only [liftAwayOfIsUnit, RingHom.comp_apply, Subring.coe_subtype,
    IsLocalization.Away.lift_eq]
  rfl

end LiftAway

section Eval₂

variable {p : ℕ} [Fact p.Prime]

/-- Any constant `C` satisfying `∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖` is nonnegative. -/
private theorem bound_nonneg {K : Type*} [SeminormedRing K] {f : ℤ_[p] →+* K} {C : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) : 0 ≤ C := by
  have h := hC 1
  simp only [norm_one, mul_one] at h
  exact (norm_nonneg _).trans h

/-- Uniform geometric bound on every term `f(d_m) t ^ m` for `x ∈ H`. -/
private theorem norm_term_le {K : Type*} [SeminormedRing K] {f : ℤ_[p] →+* K} {C : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) (t : Kˣ) (x : AnnularRing p) (m : ℤ) :
    ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖ ≤
      C * (max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)) ^ m.natAbs := by
  have hC0 : 0 ≤ C := bound_nonneg hC
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  rcases lt_trichotomy m 0 with hneg | rfl | hpos
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m by omega)
    have hm_eq : m = -(n : ℤ) := by omega
    have hnpos : 0 < n := by omega
    have habs : m.natAbs = n := by omega
    have hcoeff : ‖x.coeff m‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      have h := x.norm_coeff_le m
      rw [min_eq_right hneg.le, hm_eq, zpow_neg, zpow_natCast, ← inv_pow] at h
      rwa [hm_eq]
    have htpow : ‖((t ^ m : Kˣ) : K)‖ ≤ ‖((t⁻¹ : Kˣ) : K)‖ ^ n := by
      rw [hm_eq, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
      exact norm_pow_le' _ hnpos
    calc ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖
        ≤ ‖f (x.coeff m)‖ * ‖((t ^ m : Kˣ) : K)‖ := norm_mul_le _ _
      _ ≤ (C * ‖x.coeff m‖) * ‖((t⁻¹ : Kˣ) : K)‖ ^ n :=
          mul_le_mul (hC _) htpow (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
      _ ≤ (C * ((p : ℝ)⁻¹) ^ n) * ‖((t⁻¹ : Kˣ) : K)‖ ^ n := by gcongr
      _ = C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ n := by
          rw [mul_assoc, ← mul_pow, div_eq_inv_mul]
      _ ≤ C * ρ ^ m.natAbs := by rw [habs]; gcongr; exact le_max_right _ _
  · simpa using (hC (x.coeff 0)).trans (mul_le_of_le_one_right hC0 (PadicInt.norm_le_one _))
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hpos.le
    have hnpos : 0 < n := by omega
    have habs : m.natAbs = n := by omega
    have htpow : ‖((t ^ m : Kˣ) : K)‖ ≤ ‖(t : K)‖ ^ n := by
      rw [hn, zpow_natCast, Units.val_pow_eq_pow_val]
      exact norm_pow_le' _ hnpos
    calc ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖
        ≤ ‖f (x.coeff m)‖ * ‖((t ^ m : Kˣ) : K)‖ := norm_mul_le _ _
      _ ≤ (C * ‖x.coeff m‖) * ‖(t : K)‖ ^ n :=
          mul_le_mul (hC _) htpow (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
      _ ≤ (C * 1) * ‖(t : K)‖ ^ n := by gcongr; exact PadicInt.norm_le_one _
      _ = C * ‖(t : K)‖ ^ n := by rw [mul_one]
      _ ≤ C * ρ ^ m.natAbs := by rw [habs]; gcongr; exact le_max_left _ _

/-- The norms `‖f(x.coeff m) * t ^ m‖` are summable over `ℤ` whenever `f` is bounded and
`‖t‖ < 1`, `‖t⁻¹‖ < p`. -/
theorem summable_norm_eval₂ {K : Type*} [SeminormedRing K] (f : ℤ_[p] →+* K)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (x : AnnularRing p) :
    Summable fun m : ℤ ↦ ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖ := by
  obtain ⟨C, hC⟩ := hf
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρ1 : ρ < 1 := max_lt ht ((div_lt_one (p_pos (p := p))).2 htinv)
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_le hC t x)
    (summable_mul_pow_natAbs hρ0 hρ1)

/-- The bilateral series `∑_{m ∈ ℤ} f(x.coeff m) * t ^ m` converges in `K` whenever `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
theorem summable_eval₂ {K : Type*} [SeminormedRing K] [CompleteSpace K] (f : ℤ_[p] →+* K)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (x : AnnularRing p) :
    Summable fun m : ℤ ↦ f (x.coeff m) * ((t ^ m : Kˣ) : K) :=
  (summable_norm_eval₂ f hf t ht htinv x).of_norm

variable {K : Type*} [NormedRing K] [CompleteSpace K]

/-- Multiplicativity of the bilateral evaluation series on `AnnularRing p`. -/
private theorem eval₂_mul (f : ℤ_[p] →+* K) (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (x y : AnnularRing p) :
    (∑' m : ℤ, f ((x * y).coeff m) * ((t ^ m : Kˣ) : K)) =
      (∑' i : ℤ, f (x.coeff i) * ((t ^ i : Kˣ) : K)) *
        (∑' j : ℤ, f (y.coeff j) * ((t ^ j : Kˣ) : K)) := by
  obtain ⟨C, hC⟩ := hf
  have hfx := summable_norm_eval₂ f ⟨C, hC⟩ t ht htinv x
  have hfy := summable_norm_eval₂ f ⟨C, hC⟩ t ht htinv y
  rw [tsum_mul_tsum_of_summable_norm hfx hfy]
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun mi ↦ (mi.2, mi.1 - mi.2)
      invFun := fun ij ↦ (ij.1 + ij.2, ij.1)
      left_inv := fun ⟨m, i⟩ ↦ Prod.ext (by ring) rfl
      right_inv := fun ⟨i, j⟩ ↦ Prod.ext rfl (by ring) }
  have hprod : Summable fun mi : ℤ × ℤ ↦
      (f (x.coeff mi.2) * ((t ^ mi.2 : Kˣ) : K)) *
        (f (y.coeff (mi.1 - mi.2)) * ((t ^ (mi.1 - mi.2) : Kˣ) : K)) :=
    e.summable_iff.mpr (summable_mul_of_summable_norm hfx hfy)
  rw [← e.tsum_eq]
  dsimp only [e, Equiv.coe_fn_mk]
  rw [hprod.tsum_prod' (fun m ↦ hprod.comp_injective fun _ _ h ↦ (Prod.mk.inj h).2)]
  refine tsum_congr fun m ↦ ?_
  let g : ℤ_[p] →+ K := (AddMonoidHom.mulRight ((t ^ m : Kˣ) : K)).comp f.toAddMonoidHom
  have hf_cont : Continuous f := AddMonoidHomClass.continuous_of_bound f C hC
  have hg : Continuous g := (continuous_mul_const ((t ^ m : Kˣ) : K)).comp hf_cont
  have hg_apply (a : ℤ_[p]) : g a = f a * ((t ^ m : Kˣ) : K) := by
    simp [g]
  have hsum : HasSum (fun i : ℤ ↦ g (x.coeff i * y.coeff (m - i))) (g ((x * y).coeff m)) :=
    (hasSum_coeff_mul x y m).map g hg
  rw [← hg_apply]
  refine (hsum.congr_fun fun i ↦ ?_).tsum_eq.symm
  rw [hg_apply]
  have ht_add : ((t ^ i : Kˣ) : K) * ((t ^ (m - i) : Kˣ) : K) = ((t ^ m : Kˣ) : K) := by
    rw [← Units.val_mul, ← zpow_add, add_sub_cancel]
  have hcomm : ((t ^ i : Kˣ) : K) * f (y.coeff (m - i)) =
      f (y.coeff (m - i)) * ((t ^ i : Kˣ) : K) :=
    (PadicInt.commute_ringHom_of_continuous hf_cont (y.coeff (m - i)) ((t ^ i : Kˣ) : K)).symm
  rw [map_mul, ← ht_add, mul_assoc, ← mul_assoc ((t ^ i : Kˣ) : K), hcomm, mul_assoc, mul_assoc]

/-- The evaluation ring homomorphism `H = ℤ_p⟦T, p/T⟧ →+* K` sending `∑ d_m T ^ m` to
`∑ f(d_m) t ^ m`, for any bounded `f : ℤ_[p] →+* K` and any unit `t : Kˣ` with `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
def eval₂ (f : ℤ_[p] →+* K) (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) : AnnularRing p →+* K where
  toFun x := ∑' m : ℤ, f (x.coeff m) * ((t ^ m : Kˣ) : K)
  map_zero' := by simp
  map_one' := by
    rw [tsum_eq_single (0 : ℤ) (fun m hm ↦ by simp [coeff_one, hm])]
    simp
  map_add' x y := by
    simp only [coeff_add, map_add, add_mul]
    exact (summable_eval₂ f hf t ht htinv x).tsum_add (summable_eval₂ f hf t ht htinv y)
  map_mul' := eval₂_mul f hf t ht htinv

variable (f : ℤ_[p] →+* K) (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
  (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)

theorem eval₂_apply (x : AnnularRing p) :
    eval₂ f hf t ht htinv x = ∑' m : ℤ, f (x.coeff m) * ((t ^ m : Kˣ) : K) := (rfl)

theorem hasSum_eval₂ (x : AnnularRing p) :
    HasSum (fun m : ℤ ↦ f (x.coeff m) * ((t ^ m : Kˣ) : K)) (eval₂ f hf t ht htinv x) :=
  (summable_eval₂ f hf t ht htinv x).hasSum

@[simp] theorem eval₂_algebraMap (c : ℤ_[p]) :
    eval₂ f hf t ht htinv (algebraMap ℤ_[p] (AnnularRing p) c) = f c := by
  rw [eval₂_apply, tsum_eq_single (0 : ℤ) (fun m hm ↦ by simp [hm])]
  simp

@[simp] theorem eval₂_T : eval₂ f hf t ht htinv T = (t : K) := by
  rw [eval₂_apply, tsum_eq_single (1 : ℤ) (fun m hm ↦ by simp [coeff_T, hm])]
  simp [coeff_T]

@[simp] theorem eval₂_U : eval₂ f hf t ht htinv U = (p : K) * ((t⁻¹ : Kˣ) : K) := by
  rw [eval₂_apply, tsum_eq_single (-1 : ℤ) (fun m hm ↦ by simp [coeff_U, hm])]
  simp [coeff_U]

/-- Evaluating a power series `g(T) ∈ H` gives the convergent power series `∑_{n ≥ 0} f(a_n) t ^ n`
in `K`. -/
theorem eval₂_ofPowerSeriesT (g : PowerSeries ℤ_[p]) :
    eval₂ f hf t ht htinv (ofPowerSeriesT g) =
      ∑' n : ℕ, f (PowerSeries.coeff n g) * (t : K) ^ n := by
  rw [eval₂_apply]
  refine tsum_eq_tsum_of_ne_zero_bij (fun n ↦ (n.1 : ℤ))
    (fun _ _ h ↦ Subtype.ext (by dsimp only at h; omega)) (fun m hm ↦ ?_) fun n ↦ ?_
  · by_cases hneg : m < 0
    · exfalso; exact hm (by simp [coeff_ofPowerSeriesT_of_neg g hneg])
    · refine ⟨⟨m.toNat, ?_⟩, by dsimp only; omega⟩
      have hm_eq : (m.toNat : ℤ) = m := by omega
      rw [Function.mem_support, ← hm_eq, coeff_ofPowerSeriesT_natCast, zpow_natCast,
        Units.val_pow_eq_pow_val] at hm
      exact hm
  · simp [coeff_ofPowerSeriesT_natCast]

/-- Evaluating a power series `g(U) ∈ H` gives the convergent power series
`∑_{n ≥ 0} f(b_n) (p t⁻¹) ^ n` in `K`. -/
theorem eval₂_ofPowerSeriesU (g : PowerSeries ℤ_[p]) :
    eval₂ f hf t ht htinv (ofPowerSeriesU g) =
      ∑' n : ℕ, f (PowerSeries.coeff n g) * ((p : K) * ((t⁻¹ : Kˣ) : K)) ^ n := by
  have hmul_pow (n : ℕ) : ((p : K) * ((t⁻¹ : Kˣ) : K)) ^ n =
      (p : K) ^ n * ((t⁻¹ : Kˣ) : K) ^ n :=
    (Nat.cast_commute p ((t⁻¹ : Kˣ) : K)).mul_pow n
  have hterm (n : ℕ) :
      f ((p : ℤ_[p]) ^ n * PowerSeries.coeff n g) * ((t ^ (-(n : ℤ)) : Kˣ) : K) =
        f (PowerSeries.coeff n g) * ((p : K) * ((t⁻¹ : Kˣ) : K)) ^ n := by
    rw [map_mul, map_pow, map_natCast, zpow_neg, zpow_natCast, ← inv_pow,
      Units.val_pow_eq_pow_val, hmul_pow, ← mul_assoc,
      (Nat.cast_commute p (f (PowerSeries.coeff n g))).pow_left n, mul_assoc]
  rw [eval₂_apply]
  refine tsum_eq_tsum_of_ne_zero_bij (fun n ↦ -(n.1 : ℤ))
    (fun _ _ h ↦ Subtype.ext (by dsimp only at h; omega))
    (fun m hm ↦ ?_) fun n ↦ ?_
  · by_cases hpos : 0 < m
    · exfalso; exact hm (by simp [coeff_ofPowerSeriesU_of_pos g hpos])
    · refine ⟨⟨(-m).toNat, ?_⟩, by dsimp only; omega⟩
      have hm_eq : -((-m).toNat : ℤ) = m := by omega
      rw [Function.mem_support, ← hm_eq, coeff_ofPowerSeriesU_neg_natCast, hterm] at hm
      exact hm
  · rw [coeff_ofPowerSeriesU_neg_natCast, hterm]

/-- Uniform ultrametric bound on `eval₂` over the integral ring `H`: if `‖f a‖ ≤ C * ‖a‖` for all
`a ∈ ℤ_p`, then `‖eval₂ x‖ ≤ C` for every `x ∈ H`. -/
theorem norm_eval₂_le [IsUltrametricDist K] {C : ℝ} (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (x : AnnularRing p) : ‖eval₂ f hf t ht htinv x‖ ≤ C := by
  have hC0 : 0 ≤ C := bound_nonneg hC
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρ1 : ρ < 1 := max_lt ht ((div_lt_one (p_pos (p := p))).2 htinv)
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 fun m ↦ ?_
  exact (norm_term_le hC t x m).trans (mul_le_of_le_one_right hC0 (pow_le_one₀ hρ0 hρ1.le))

/-! ### Extension to `H[1/T]` and `T`-adic continuity -/

section LocalizedEval₂

variable {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- The unique extension of `eval₂` to any localization `A = H[1/T]` away from `T`. -/
def localizedEval₂ : A →+* K :=
  liftAwayOfIsUnit (eval₂ f hf t ht htinv) <| by
    rw [eval₂_T]
    exact t.isUnit

@[simp] theorem localizedEval₂_algebraMap (a : AnnularRing p) :
    localizedEval₂ f hf t ht htinv (algebraMap (AnnularRing p) A a) = eval₂ f hf t ht htinv a :=
  liftAwayOfIsUnit_algebraMap _ _ a

theorem localizedEval₂_T :
    localizedEval₂ f hf t ht htinv (algebraMap (AnnularRing p) A T) = (t : K) := by
  rw [localizedEval₂_algebraMap, eval₂_T]

theorem localizedEval₂_U :
    localizedEval₂ f hf t ht htinv (algebraMap (AnnularRing p) A U) =
      (p : K) * ((t⁻¹ : Kˣ) : K) := by
  rw [localizedEval₂_algebraMap, eval₂_U]

/-- On integer powers of the unit `T` in `H[1/T]`, `localizedEval₂` evaluates `T ^ k` to `t ^ k`. -/
@[simp] theorem localizedEval₂_T_zpow (k : ℤ) :
    localizedEval₂ f hf t ht htinv
        (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A) =
      ((t ^ k : Kˣ) : K) := by
  have hu : Units.map (localizedEval₂ (A := A) f hf t ht htinv).toMonoidHom
      (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit = t := by
    ext
    exact localizedEval₂_T f hf t ht htinv
  calc localizedEval₂ f hf t ht htinv
        (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A)
      = ((Units.map (localizedEval₂ (A := A) f hf t ht htinv).toMonoidHom
          ((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k) : Kˣ) : K) := rfl
    _ = ((t ^ k : Kˣ) : K) := by rw [map_zpow, hu]

/-- For every `x ∈ H[1/T]`, the bilateral series `∑_{m ∈ ℤ} f(localizedCoeff p x m) * t ^ m`
converges to `localizedEval₂ x`. -/
theorem hasSum_localizedEval₂ (x : A) :
    HasSum (fun m : ℤ ↦ f (localizedCoeff p x m) * ((t ^ m : Kˣ) : K))
      (localizedEval₂ f hf t ht htinv x) := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have hx : localizedEval₂ f hf t ht htinv x =
      eval₂ f hf t ht htinv a * ((t ^ (-(k : ℤ)) : Kˣ) : K) := by
    have h := congr_arg (localizedEval₂ f hf t ht htinv) ha
    rw [map_mul, map_pow, localizedEval₂_T, localizedEval₂_algebraMap] at h
    calc localizedEval₂ f hf t ht htinv x
        = localizedEval₂ f hf t ht htinv x * ((t : K) ^ k * ((t ^ (-(k : ℤ)) : Kˣ) : K)) := by
          rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← Units.val_mul, ← zpow_add,
            add_neg_cancel, zpow_zero, Units.val_one, mul_one]
      _ = eval₂ f hf t ht htinv a * ((t ^ (-(k : ℤ)) : Kˣ) : K) := by rw [← mul_assoc, h]
  have hmul : HasSum
      (fun m : ℤ ↦ (f (a.coeff m) * ((t ^ m : Kˣ) : K)) * ((t ^ (-(k : ℤ)) : Kˣ) : K))
      (localizedEval₂ f hf t ht htinv x) := by
    rw [hx]
    exact (hasSum_eval₂ f hf t ht htinv a).mul_right _
  refine ((Equiv.addRight (k : ℤ)).hasSum_iff.mpr hmul).congr_fun fun m ↦ ?_
  simp only [Function.comp_apply, Equiv.coe_addRight, mul_assoc, ← Units.val_mul, ← zpow_add,
    add_neg_cancel_right]
  rw [localizedCoeff_eq_of_mul_pow ha m]

theorem localizedEval₂_eq_tsum (x : A) :
    localizedEval₂ f hf t ht htinv x =
      ∑' m : ℤ, f (localizedCoeff p x m) * ((t ^ m : Kˣ) : K) :=
  (hasSum_localizedEval₂ f hf t ht htinv x).tsum_eq.symm

/-- On the basic `T`-adic neighbourhood `T ^ N H`, the ultrametric evaluation `localizedEval₂` is
bounded by `C * ‖t‖ ^ N`. -/
theorem norm_localizedEval₂_le_of_mem_awayNhd [IsUltrametricDist K] {C : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) {N : ℕ} {x : A}
    (hx : x ∈ Huber.awayNhd (T : AnnularRing p) A N) :
    ‖localizedEval₂ f hf t ht htinv x‖ ≤ C * ‖(t : K)‖ ^ N := by
  obtain ⟨a, rfl⟩ := Huber.mem_awayNhd.mp hx
  rcases eq_or_ne N 0 with rfl | hN
  · simpa using norm_eval₂_le f hf t ht htinv hC a
  · rw [localizedEval₂_algebraMap, map_mul, map_pow, eval₂_T]
    calc ‖(t : K) ^ N * eval₂ f hf t ht htinv a‖
        ≤ ‖(t : K) ^ N‖ * ‖eval₂ f hf t ht htinv a‖ := norm_mul_le _ _
      _ ≤ ‖(t : K)‖ ^ N * C :=
          mul_le_mul (norm_pow_le' _ (Nat.pos_of_ne_zero hN)) (norm_eval₂_le f hf t ht htinv hC a)
            (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      _ = C * ‖(t : K)‖ ^ N := mul_comm _ _

/-- Every annulus evaluation `H[1/T] →+* K` is continuous for any `T`-adic topology on `H[1/T]`
whose neighbourhoods of zero have basis `T ^ n H`. -/
theorem continuous_localizedEval₂ [TopologicalSpace A] [IsTopologicalAddGroup A]
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A)) :
    Continuous (localizedEval₂ f hf t ht htinv (A := A)) := by
  have ⟨C, hC⟩ := hf
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρ1 : ρ < 1 := max_lt ht ((div_lt_one (p_pos (p := p))).2 htinv)
  have hgeom := summable_mul_pow_natAbs (C := C) hρ0 hρ1
  set M : ℝ := ∑' m : ℤ, C * ρ ^ m.natAbs
  have hbound (a : AnnularRing p) : ‖eval₂ f hf t ht htinv a‖ ≤ M :=
    (norm_tsum_le_tsum_norm (summable_norm_eval₂ f hf t ht htinv a)).trans <|
      (summable_norm_eval₂ f hf t ht htinv a).tsum_le_tsum (norm_term_le hC t a) hgeom
  refine continuous_of_continuousAt_zero (localizedEval₂ f hf t ht htinv).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ ↦ ‖(t : K)‖ ^ (N + 1) * M) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ht).comp
        (tendsto_add_atTop_nat 1)).mul_const M
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  filter_upwards [hb.mem_of_mem (i := N + 1) trivial] with x hx
  obtain ⟨a, rfl⟩ := Huber.mem_awayNhd.mp hx
  rw [dist_zero_right, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    localizedEval₂_algebraMap, map_mul, map_pow, eval₂_T]
  calc ‖(t : K) ^ (N + 1) * eval₂ f hf t ht htinv a‖
      ≤ ‖(t : K) ^ (N + 1)‖ * ‖eval₂ f hf t ht htinv a‖ := norm_mul_le _ _
    _ ≤ ‖(t : K)‖ ^ (N + 1) * M :=
        mul_le_mul (norm_pow_le' _ (Nat.succ_pos N)) (hbound a) (norm_nonneg _)
          (pow_nonneg (norm_nonneg _) _)
    _ < ε := hN

/-- Every annulus evaluation `H[1/T] →+* K` is continuous for the `T`-adic Tate gauge of any radius
`α ∈ (0, 1)`. -/
theorem continuous_localizedEval₂_awayNormedCommRing {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    letI := awayNormedCommRing p A hα₀ hα₁
    Continuous (localizedEval₂ f hf t ht htinv (A := A)) := by
  let := awayNormedCommRing p A hα₀ hα₁
  exact continuous_localizedEval₂ f hf t ht htinv
    (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁)

end LocalizedEval₂

end Eval₂

/-! ### `ℤ_p`-algebra evaluations under `[IsBoundedSMul ℤ_[p] K]` -/

section EvalAlgHom

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedRing K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K]

private theorem exists_norm_algebraMap_le :
    ∃ C : ℝ, ∀ a : ℤ_[p], ‖algebraMap ℤ_[p] K a‖ ≤ C * ‖a‖ :=
  ⟨‖(1 : K)‖, fun a ↦ by
    rw [Algebra.algebraMap_eq_smul_one, mul_comm]
    exact norm_smul_le a 1⟩

variable [CompleteSpace K]

/-- The `ℤ_p`-algebra evaluation `H →ₐ[ℤ_[p]] K` at a unit `t : Kˣ` with `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
def eval (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    AnnularRing p →ₐ[ℤ_[p]] K :=
  { eval₂ (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv with
    commutes' := eval₂_algebraMap (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv }

theorem eval_apply (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
    (x : AnnularRing p) :
    eval t ht htinv x = ∑' m : ℤ, algebraMap ℤ_[p] K (x.coeff m) * ((t ^ m : Kˣ) : K) := (rfl)

@[simp] theorem eval_T (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    eval t ht htinv T = (t : K) :=
  eval₂_T (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv

@[simp] theorem eval_U (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    eval t ht htinv U = (p : K) * ((t⁻¹ : Kˣ) : K) :=
  eval₂_U (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv

/-- The `ℤ_p`-algebra evaluation `H[1/T] →ₐ[ℤ_[p]] K` at a unit `t : Kˣ` with `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
def localizedEvalAlgHom {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] [Algebra ℤ_[p] A]
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) : A →ₐ[ℤ_[p]] K :=
  { localizedEval₂ (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv with
    commutes' := fun c ↦ by
      have hmap : algebraMap ℤ_[p] A c =
          algebraMap (AnnularRing p) A (algebraMap ℤ_[p] (AnnularRing p) c) :=
        DFunLike.congr_fun (ringHom_padicInt_eq (algebraMap ℤ_[p] A)) c
      rw [RingHom.toFun_eq_coe, hmap, localizedEval₂_algebraMap, eval₂_algebraMap] }

@[simp] theorem localizedEvalAlgHom_algebraMap {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] [Algebra ℤ_[p] A]
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (a : AnnularRing p) :
    localizedEvalAlgHom (A := A) t ht htinv (algebraMap (AnnularRing p) A a) =
      eval t ht htinv a :=
  localizedEval₂_algebraMap (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv a

end EvalAlgHom

/-! ### Evaluations into complete normed division rings over `ℚ_p` -/

section EvalAt

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedDivisionRing K]

private theorem ne_zero_of_inv_p_lt {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) : t ≠ 0 :=
  norm_pos_iff.mp ((inv_pos.2 (p_pos (p := p))).trans ht₀)

private theorem norm_mk0_lt_one {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    ‖((Units.mk0 t (ne_zero_of_inv_p_lt ht₀) : Kˣ) : K)‖ < 1 := by
  simpa using ht₁

private theorem norm_mk0_inv_lt_p {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) :
    ‖(((Units.mk0 t (ne_zero_of_inv_p_lt ht₀))⁻¹ : Kˣ) : K)‖ < p := by
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv]
  exact inv_lt_of_inv_lt₀ (p_pos (p := p)) ht₀

variable [NormedAlgebra ℚ_[p] K]

private theorem exists_norm_padicIntAlgebraMap_le :
    ∃ C : ℝ, ∀ a : ℤ_[p], ‖padicIntAlgebraMap p K a‖ ≤ C * ‖a‖ :=
  ⟨1, fun a ↦ by rw [one_mul, norm_padicIntAlgebraMap]⟩

variable [CompleteSpace K]

/-- Evaluation `H →+* K` at a point `t` in the open annulus `p⁻¹ < ‖t‖ < 1` of a complete normed
division ring `K` over `ℚ_[p]` (such as `ℂ_[p]`). -/
def evalAt (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) : AnnularRing p →+* K :=
  eval₂ (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)

theorem evalAt_apply (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    evalAt t ht₀ ht₁ x = ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m := by
  rw [evalAt, eval₂_apply]
  congr 1 with m
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem hasSum_evalAt (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m) (evalAt t ht₀ ht₁ x) := by
  have h := hasSum_eval₂ (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) x
  exact h.congr_fun fun m ↦ by rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

@[simp] theorem evalAt_T (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    evalAt t ht₀ ht₁ T = t :=
  eval₂_T (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)

@[simp] theorem evalAt_U (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    evalAt t ht₀ ht₁ U = (p : K) / t := by
  rw [evalAt, eval₂_U, Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_mul_inv]

/-- Every element of `H` has absolute value at most `1` at every point `t` of the open annulus
`p⁻¹ < ‖t‖ < 1`. -/
theorem norm_evalAt_le_one (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    ‖evalAt t ht₀ ht₁ x‖ ≤ 1 := by
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  exact norm_eval₂_le (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)
    (fun a ↦ by rw [one_mul, norm_padicIntAlgebraMap]) x

section LocalizedEvalAt

variable {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- Evaluation `H[1/T] →+* K` at a point `t` in the open annulus `p⁻¹ < ‖t‖ < 1` of a complete
normed division ring `K` over `ℚ_[p]`. -/
def localizedEvalAt (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) : A →+* K :=
  localizedEval₂ (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)

@[simp] theorem localizedEvalAt_algebraMap (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    (a : AnnularRing p) :
    localizedEvalAt (A := A) t ht₀ ht₁ (algebraMap (AnnularRing p) A a) = evalAt t ht₀ ht₁ a :=
  localizedEval₂_algebraMap (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) a

theorem localizedEvalAt_T (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    localizedEvalAt (A := A) t ht₀ ht₁ (algebraMap (AnnularRing p) A T) = t := by
  rw [localizedEvalAt_algebraMap, evalAt_T]

@[simp] theorem localizedEvalAt_T_zpow (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (k : ℤ) :
    localizedEvalAt (A := A) t ht₀ ht₁
        (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A) =
      t ^ k := by
  rw [localizedEvalAt, localizedEval₂_T_zpow, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem hasSum_localizedEvalAt (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : A) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (localizedCoeff p x m) * t ^ m)
      (localizedEvalAt t ht₀ ht₁ x) := by
  have h := hasSum_localizedEval₂ (A := A) (padicIntAlgebraMap p K)
    exists_norm_padicIntAlgebraMap_le (Units.mk0 t (ne_zero_of_inv_p_lt ht₀))
    (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) x
  exact h.congr_fun fun m ↦ by rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- Sharp bound: every element of `T ^ N H` has norm at most `‖t‖ ^ N` under evaluation at `t`. -/
theorem norm_localizedEvalAt_le_pow_of_mem_awayNhd (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    {N : ℕ} {x : A} (hx : x ∈ Huber.awayNhd (T : AnnularRing p) A N) :
    ‖localizedEvalAt t ht₀ ht₁ x‖ ≤ ‖t‖ ^ N := by
  obtain ⟨a, rfl⟩ := Huber.mem_awayNhd.mp hx
  rw [localizedEvalAt_algebraMap, map_mul, map_pow, evalAt_T, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (norm_evalAt_le_one t ht₀ ht₁ a)

/-- Evaluation at `t` is continuous for any `T`-adic topology on `H[1/T]`. -/
theorem continuous_localizedEvalAt [TopologicalSpace A] [IsTopologicalAddGroup A]
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A))
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    Continuous (localizedEvalAt (A := A) t ht₀ ht₁) :=
  continuous_localizedEval₂ (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) hb

/-- When the `T`-gauge radius equals `‖t‖`, evaluation at `t` is contractive:
`‖localizedEvalAt t x‖ ≤ ‖x‖`. -/
theorem norm_localizedEvalAt_le_of_eq (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : A) :
    letI := awayNormedCommRing p A
      ((inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)).trans ht₀) ht₁
    ‖localizedEvalAt t ht₀ ht₁ x‖ ≤ ‖x‖ := by
  have htpos : 0 < ‖t‖ := (inv_pos.2 (p_pos (p := p))).trans ht₀
  let := awayNormedCommRing p A htpos ht₁
  rw [norm_awayNormedCommRing]
  set d := tateNormDatum (hasBasis_nhds_zero_awayNormedCommRing p A htpos ht₁) htpos ht₁
  refine le_of_forall_gt fun r hr ↦ ?_
  rw [Huber.tateNorm_apply,
    Huber.tateGauge_lt_iff (zero_le_one.trans d.one_lt_radius_inv.le) (d.exists_zpow_mul_mem x)]
    at hr
  obtain ⟨n, hmem, hnr⟩ := hr
  rw [tateNormDatum_pseudoUniformizer, tateNormDatum_ringOfDefinition] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hx : x = (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ n : Aˣ) : A) *
      algebraMap (AnnularRing p) A a := by
    rw [ha, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul]
  have hr' : ‖t‖ ^ n < r := by simpa [d, inv_zpow'] using hnr
  calc ‖localizedEvalAt t ht₀ ht₁ x‖
      = ‖t ^ n * evalAt t ht₀ ht₁ a‖ := by
        rw [hx, map_mul, localizedEvalAt_T_zpow, localizedEvalAt_algebraMap]
    _ = ‖t‖ ^ n * ‖evalAt t ht₀ ht₁ a‖ := by rw [norm_mul, norm_zpow]
    _ ≤ ‖t‖ ^ n := mul_le_of_le_one_right (zpow_nonneg (norm_nonneg _) _)
        (norm_evalAt_le_one t ht₀ ht₁ a)
    _ < r := hr'

/-- For any `T`-gauge radius `α ∈ (0, 1)` different from `‖t‖`, evaluation at `t` is not bounded
by any constant multiple of the `α`-gauge norm (even though it is continuous for the `T`-adic
topology): positive powers `T ^ n` witness unboundedness when `α < ‖t‖`, and negative powers
`T ^ (-n)` witness it when `‖t‖ < α`. -/
theorem not_exists_bound_localizedEvalAt_of_ne {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (hne : α ≠ ‖t‖) :
    letI := awayNormedCommRing p A hα₀ hα₁
    ¬ ∃ C : ℝ, ∀ x : A, ‖localizedEvalAt t ht₀ ht₁ x‖ ≤ C * ‖x‖ := by
  let := awayNormedCommRing p A hα₀ hα₁
  have : NormOneClass A := normOneClass_awayNormedCommRing p A hα₀ hα₁
  rintro ⟨C, hC⟩
  have htpos : 0 < ‖t‖ := (inv_pos.2 (p_pos (p := p))).trans ht₀
  have hpow (k : ℤ) : ‖t‖ ^ k ≤ C * α ^ k := by
    set u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
    have hnorm_u : ‖((u ^ k : Aˣ) : A)‖ = α ^ k := by
      have h1 := norm_T_zpow_mul_awayNormedCommRing p A hα₀ hα₁ k 1
      rw [mul_one, norm_one, mul_one] at h1
      exact h1
    have hc := hC ((u ^ k : Aˣ) : A)
    rw [hnorm_u, show localizedEvalAt (A := A) t ht₀ ht₁ ((u ^ k : Aˣ) : A) = t ^ k from
      localizedEvalAt_T_zpow t ht₀ ht₁ k, norm_zpow] at hc
    exact hc
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hα₀).2 hlt)).eventually_gt_atTop C).exists
    have hle : (‖t‖ / α) ^ n ≤ C := by
      rw [div_pow, div_le_iff₀ (pow_pos hα₀ n)]
      simpa only [zpow_natCast] using hpow (n : ℤ)
    exact hn.not_ge hle
  · obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div htpos).2 hgt)).eventually_gt_atTop C).exists
    have h := hpow (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast] at h
    have hle : (α / ‖t‖) ^ n ≤ C := calc
      (α / ‖t‖) ^ n = α ^ n * (‖t‖ ^ n)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ ≤ α ^ n * (C * (α ^ n)⁻¹) := mul_le_mul_of_nonneg_left h (pow_nonneg hα₀.le n)
      _ = C := by field_simp
    exact hn.not_ge hle

/-- In particular, evaluation at `t` is not Lipschitz for the `α`-gauge whenever `α ≠ ‖t‖`. -/
theorem not_lipschitzWith_localizedEvalAt_of_ne {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (hne : α ≠ ‖t‖) :
    letI := awayNormedCommRing p A hα₀ hα₁
    ¬ ∃ L : NNReal, LipschitzWith L (localizedEvalAt (A := A) t ht₀ ht₁) := by
  let := awayNormedCommRing p A hα₀ hα₁
  rintro ⟨L, hL⟩
  refine not_exists_bound_localizedEvalAt_of_ne (A := A) hα₀ hα₁ t ht₀ ht₁ hne ⟨(L : ℝ), fun x ↦ ?_⟩
  have := hL.dist_le_mul x 0
  simpa only [map_zero, dist_zero_right] using this

end LocalizedEvalAt

end EvalAt

/-! ### Emptiness over `ℚ_p` and joint injectivity over `ℂ_p` -/

section PadicAndComplex

variable {p : ℕ} [Fact p.Prime]

/-- The open annulus `p⁻¹ < ‖t‖ < 1` has no points in `ℚ_[p]`, because every nonzero element of
`ℚ_[p]` has norm in `p ^ ℤ`. -/
theorem not_exists_padic_annulus : ¬ ∃ t : ℚ_[p], (p : ℝ)⁻¹ < ‖t‖ ∧ ‖t‖ < 1 := by
  rintro ⟨t, ht₀, ht₁⟩
  have ht : t ≠ 0 := norm_pos_iff.mp ((inv_pos.2 (p_pos (p := p))).trans ht₀)
  rw [Padic.norm_eq_zpow_neg_valuation ht] at ht₀ ht₁
  have h1 : (p : ℝ) ^ (-1 : ℤ) < (p : ℝ) ^ (-t.valuation) := by simpa using ht₀
  have h2 : (p : ℝ) ^ (-t.valuation) < (p : ℝ) ^ (0 : ℤ) := by simpa using ht₁
  rw [zpow_lt_zpow_iff_right₀ (one_lt_p (p := p))] at h1 h2
  omega

/-- On the sub-annulus `q ∈ [1/4, 3/4]` (where `r = p ^ (-q)`), every term `‖x.coeff m‖ * r ^ m`
is uniformly bounded by `(p ^ (-1/4)) ^ |m|`. -/
private theorem norm_coeff_mul_rpow_le_of_mem_Icc (x : AnnularRing p) {q : ℚ}
    (hq₁ : (1 / 4 : ℚ) ≤ q) (hq₂ : q ≤ 3 / 4) (m : ℤ) :
    ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m ≤ ((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ m.natAbs := by
  have hp0 : (0 : ℝ) ≤ p := (p_pos (p := p)).le
  have hq₁' : (1 / 4 : ℝ) ≤ (q : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₁
  have hq₂' : (q : ℝ) ≤ 3 / 4 := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₂
  rw [← Real.rpow_intCast, ← Real.rpow_mul hp0, ← Real.rpow_natCast, ← Real.rpow_mul hp0]
  rcases le_or_gt 0 m with hm | hm
  · have habs : (m.natAbs : ℝ) = (m : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hm]
    have _ : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    calc ‖x.coeff m‖ * (p : ℝ) ^ (-(q : ℝ) * (m : ℝ))
        ≤ 1 * (p : ℝ) ^ (-(q : ℝ) * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (Real.rpow_nonneg hp0 _)
      _ = (p : ℝ) ^ (-(q : ℝ) * (m : ℝ)) := one_mul _
      _ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ) * (m.natAbs : ℝ)) := by
          rw [habs]
          exact Real.rpow_le_rpow_of_exponent_le (one_lt_p (p := p)).le (by nlinarith)
  · have habs : (m : ℝ) = -(m.natAbs : ℝ) := by
      have : m = -(m.natAbs : ℤ) := by omega
      exact_mod_cast this
    have hcoeff : ‖x.coeff m‖ ≤ (p : ℝ) ^ (m : ℝ) := by
      have := x.norm_coeff_le m
      rwa [min_eq_right hm.le, ← Real.rpow_intCast] at this
    calc ‖x.coeff m‖ * (p : ℝ) ^ (-(q : ℝ) * (m : ℝ))
        ≤ (p : ℝ) ^ (m : ℝ) * (p : ℝ) ^ (-(q : ℝ) * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hp0 _)
      _ = (p : ℝ) ^ ((m : ℝ) + -(q : ℝ) * (m : ℝ)) := (Real.rpow_add (p_pos (p := p)) _ _).symm
      _ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ) * (m.natAbs : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (one_lt_p (p := p)).le ?_
          rw [habs]
          nlinarith

/-- Uniform positive lower bound on `‖x.coeff m₀‖ * (p ^ (-q)) ^ m₀` over `q ∈ [1/4, 3/4]`. -/
private theorem min_rpow_le_rpow_zpow {q : ℚ} (hq₁ : (1 / 4 : ℚ) ≤ q) (hq₂ : q ≤ 3 / 4) (m : ℤ) :
    min (((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ m) (((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ m) ≤
      ((p : ℝ) ^ (-(q : ℝ))) ^ m := by
  have hp0 : (0 : ℝ) ≤ p := (p_pos (p := p)).le
  have h1p : (1 : ℝ) < p := one_lt_p (p := p)
  have hq₁' : (1 / 4 : ℝ) ≤ (q : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₁
  have hq₂' : (q : ℝ) ≤ 3 / 4 := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₂
  rcases le_or_gt 0 m with hm | hm
  · refine (min_le_left _ _).trans ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul hp0, ← Real.rpow_intCast, ← Real.rpow_mul hp0]
    have _ : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    exact Real.rpow_le_rpow_of_exponent_le h1p.le (by nlinarith)
  · refine (min_le_right _ _).trans ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul hp0, ← Real.rpow_intCast, ← Real.rpow_mul hp0]
    have _ : (m : ℝ) ≤ 0 := by exact_mod_cast hm.le
    exact Real.rpow_le_rpow_of_exponent_le h1p.le (by nlinarith)

/-- Two distinct degrees `m ≠ n` (with nonzero coefficient at `m`) can yield equal term norms
`‖x.coeff m‖ * (p ^ (-q)) ^ m = ‖x.coeff n‖ * (p ^ (-q)) ^ n` for at most one rational `q`. -/
private theorem subsingleton_eq_norm_coeff_mul_rpow (x : AnnularRing p) {m n : ℤ} (hmn : m ≠ n) :
    {q : ℚ | x.coeff m ≠ 0 ∧
      ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m =
        ‖x.coeff n‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ n}.Subsingleton := by
  rintro q₁ ⟨hm, h₁⟩ q₂ ⟨-, h₂⟩
  have hp : (0 : ℝ) < p := p_pos (p := p)
  have hm_pos : 0 < ‖x.coeff m‖ := norm_pos_iff.mpr hm
  have hrel (q : ℚ) (hq : ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m =
      ‖x.coeff n‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ n) :
      ‖x.coeff m‖ / ‖x.coeff n‖ = (p : ℝ) ^ ((q : ℝ) * ((m : ℝ) - (n : ℝ))) := by
    have hn_pos : 0 < ‖x.coeff n‖ := by
      by_contra h
      have hn0 : ‖x.coeff n‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      rw [hn0, zero_mul] at hq
      exact (mul_pos hm_pos (zpow_pos (Real.rpow_pos_of_pos hp _) m)).ne' hq
    rw [← Real.rpow_intCast, ← Real.rpow_mul hp.le, ← Real.rpow_intCast,
      ← Real.rpow_mul hp.le] at hq
    rw [div_eq_iff hn_pos.ne', ← mul_left_inj' (Real.rpow_pos_of_pos hp (-(q : ℝ) * (m : ℝ))).ne',
      hq, mul_assoc, mul_left_comm _ ‖x.coeff n‖, ← Real.rpow_add hp]
    congr 2
    ring
  have heq : (p : ℝ) ^ ((q₁ : ℝ) * ((m : ℝ) - (n : ℝ))) =
      (p : ℝ) ^ ((q₂ : ℝ) * ((m : ℝ) - (n : ℝ))) :=
    (hrel q₁ h₁).symm.trans (hrel q₂ h₂)
  have hexp := (Real.rpow_right_inj hp (one_lt_p (p := p)).ne').mp heq
  have hsub : ((m : ℝ) - (n : ℝ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  exact Rat.cast_injective (mul_right_cancel₀ hsub hexp)

/-- Given a finite set `S : Finset ℤ`, there exists `q ∈ [1/4, 3/4]` at which no two distinct
degrees `m ≠ n` in `S` (with `x.coeff m ≠ 0`) have equal term norms `‖x.coeff m‖ * p ^ (-q m)`. -/
private theorem exists_rat_Icc_distinct_term_norms (x : AnnularRing p) (S : Finset ℤ) :
    ∃ q : ℚ, (1 / 4 : ℚ) ≤ q ∧ q ≤ 3 / 4 ∧
      ∀ m ∈ S, ∀ n ∈ S, m ≠ n → x.coeff m ≠ 0 →
        ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m ≠
          ‖x.coeff n‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ n := by
  set P : Finset (ℤ × ℤ) := (S ×ˢ S).filter fun mn ↦ mn.1 ≠ mn.2
  set bad : Set ℚ := ⋃ mn ∈ P, {q : ℚ | x.coeff mn.1 ≠ 0 ∧
    ‖x.coeff mn.1‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ mn.1 =
      ‖x.coeff mn.2‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ mn.2}
  have hbad : bad.Finite :=
    P.finite_toSet.biUnion fun mn hmn ↦
      (subsingleton_eq_norm_coeff_mul_rpow x (Finset.mem_filter.mp hmn).2).finite
  obtain ⟨q, ⟨hq₁, hq₂⟩, hq_good⟩ := ((Set.Icc_infinite (by norm_num : (1 / 4 : ℚ) < 3 / 4)).sdiff
    hbad).nonempty
  refine ⟨q, hq₁, hq₂, fun m hm n hn hmn hxm heq ↦ hq_good ?_⟩
  exact Set.mem_iUnion₂.mpr ⟨(m, n),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm, hn⟩, hmn⟩, hxm, heq⟩

/-- Every rational `q ∈ [1/4, 3/4]` is realized as the valuation of a point `t ∈ ℂ_[p]` in the
open annulus `p⁻¹ < ‖t‖ < 1`. -/
private theorem exists_padicComplex_norm_eq_rpow {q : ℚ}
    (hq₁ : (1 / 4 : ℚ) ≤ q) (hq₂ : q ≤ 3 / 4) :
    ∃ t : ℂ_[p], ‖t‖ = (p : ℝ) ^ (-(q : ℝ)) ∧ (p : ℝ)⁻¹ < ‖t‖ ∧ ‖t‖ < 1 := by
  obtain ⟨t, htval⟩ := PadicComplex.addValuation_surjective (p := p) (q : WithTop ℚ)
  have htnorm : ‖t‖ = (p : ℝ) ^ (-(q : ℝ)) := PadicComplex.addValuation_eq_coe_iff.mp htval
  have hq₁' : (1 / 4 : ℝ) ≤ (q : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₁
  have hq₂' : (q : ℝ) ≤ 3 / 4 := by simpa using (Rat.cast_le (K := ℝ)).mpr hq₂
  have h1p : (1 : ℝ) < p := one_lt_p (p := p)
  refine ⟨t, htnorm, ?_, ?_⟩
  · rw [htnorm, ← Real.rpow_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_lt h1p (by linarith)
  · rw [htnorm]
    exact Real.rpow_lt_one_of_one_lt_of_neg h1p (by linarith)

/-- **Joint injectivity on `H`**: an element of `AnnularRing p` that vanishes at every point
`t ∈ ℂ_[p]` of the open annulus `p⁻¹ < ‖t‖ < 1` is zero. -/
theorem eq_zero_of_forall_evalAt_padicComplex_eq_zero {x : AnnularRing p}
    (hx : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1), evalAt t ht₀ ht₁ x = 0) :
    x = 0 := by
  by_contra hne
  obtain ⟨m₀, hm₀⟩ : ∃ m : ℤ, x.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (AnnularRing.ext (funext h))
  have hp : (0 : ℝ) < p := p_pos (p := p)
  set δ : ℝ := ‖x.coeff m₀‖ *
    min (((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ m₀) (((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ m₀)
  have hδ : 0 < δ := mul_pos (norm_pos_iff.mpr hm₀)
    (lt_min (zpow_pos (Real.rpow_pos_of_pos hp _) _) (zpow_pos (Real.rpow_pos_of_pos hp _) _))
  set ρ : ℝ := (p : ℝ) ^ (-(1 / 4 : ℝ))
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hp _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (one_lt_p (p := p)) (by norm_num)
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt_of_lt_one hδ hρ1
  set M : ℕ := max M₀ m₀.natAbs
  set S : Finset ℤ := Finset.Icc (-(M : ℤ)) M
  have hm₀S : m₀ ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨q, hq₁, hq₂, hq_dist⟩ := exists_rat_Icc_distinct_term_norms x S
  obtain ⟨t, htnorm, ht₀, ht₁⟩ := exists_padicComplex_norm_eq_rpow (p := p) hq₁ hq₂
  let term (m : ℤ) : ℂ_[p] := padicIntAlgebraMap p ℂ_[p] (x.coeff m) * t ^ m
  have hterm_norm (m : ℤ) : ‖term m‖ = ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m := by
    simp [term, htnorm]
  obtain ⟨m₁, hm₁S, hm₁max⟩ := S.exists_max_image (fun m ↦ ‖term m‖) ⟨m₀, hm₀S⟩
  have hδ_le_m₁ : δ ≤ ‖term m₁‖ :=
    (mul_le_mul_of_nonneg_left (min_rpow_le_rpow_zpow hq₁ hq₂ m₀) (norm_nonneg _)).trans
      ((hterm_norm m₀).symm.le.trans (hm₁max m₀ hm₀S))
  have hm₁_ne : x.coeff m₁ ≠ 0 := fun h0 ↦ by
    have : ‖term m₁‖ = 0 := by simp [term, h0]
    linarith
  have hdom : ∀ m : ℤ, m ≠ m₁ → ‖term m‖ < ‖term m₁‖ := fun m hm ↦ by
    by_cases hmS : m ∈ S
    · refine lt_of_le_of_ne (hm₁max m hmS) fun heq ↦
        hq_dist m₁ hm₁S m hmS hm.symm hm₁_ne ?_
      simpa only [hterm_norm] using heq.symm
    · have hMlt : M₀ ≤ m.natAbs := by
        simp only [S, Finset.mem_Icc, not_and_or, not_le] at hmS
        omega
      calc ‖term m‖ = ‖x.coeff m‖ * ((p : ℝ) ^ (-(q : ℝ))) ^ m := hterm_norm m
        _ ≤ ρ ^ m.natAbs := norm_coeff_mul_rpow_le_of_mem_Icc x hq₁ hq₂ m
        _ ≤ ρ ^ M₀ := pow_le_pow_of_le_one hρ0.le hρ1.le hMlt
        _ < δ := hM₀
        _ ≤ ‖term m₁‖ := hδ_le_m₁
  have heval_norm := (hasSum_evalAt t ht₀ ht₁ x).norm_eq_of_forall_norm_lt m₁ hdom
  rw [hx t ht₀ ht₁, norm_zero] at heval_norm
  linarith

/-- Two elements of `AnnularRing p` that agree at every point `t ∈ ℂ_[p]` of the open annulus
`p⁻¹ < ‖t‖ < 1` are equal. -/
theorem eq_of_forall_evalAt_padicComplex_eq {x y : AnnularRing p}
    (hxy : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      evalAt t ht₀ ht₁ x = evalAt t ht₀ ht₁ y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_evalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [map_sub, hxy t ht₀ ht₁, sub_self]

/-- **Joint injectivity on `H[1/T]`**: an element of `H[1/T]` that vanishes at every point
`t ∈ ℂ_[p]` of the open annulus `p⁻¹ < ‖t‖ < 1` is zero. -/
theorem eq_zero_of_forall_localizedEvalAt_padicComplex_eq_zero {A : Type*} [CommRing A]
    [Algebra (AnnularRing p) A] [IsLocalization.Away (T : AnnularRing p) A] {x : A}
    (hx : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      localizedEvalAt t ht₀ ht₁ x = 0) : x = 0 := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have ha0 : a = 0 := eq_zero_of_forall_evalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [← localizedEvalAt_algebraMap (A := A), ← ha, map_mul, hx t ht₀ ht₁, zero_mul]
  rw [ha0, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).pow k).mul_left_eq_zero.mp ha

/-- Two elements of `H[1/T]` that agree at every point `t ∈ ℂ_[p]` of the open annulus
`p⁻¹ < ‖t‖ < 1` are equal. -/
theorem eq_of_forall_localizedEvalAt_padicComplex_eq {A : Type*} [CommRing A]
    [Algebra (AnnularRing p) A] [IsLocalization.Away (T : AnnularRing p) A] {x y : A}
    (hxy : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      localizedEvalAt t ht₀ ht₁ x = localizedEvalAt t ht₀ ht₁ y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_localizedEvalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [map_sub, hxy t ht₀ ht₁, sub_self]

end PadicAndComplex

end TauCeti.AnnularRing
