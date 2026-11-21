/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FundamentalGroup
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Tower
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.GroupTheory.GroupAction.Closure

/-!
# Peripheral monodromy of the polylogarithm tower

This file constructs the unipotent polynomial monodromy representation of `π₁(ℂ \ {0, 1}, 1/2)` on
the polylogarithm tower and proves equivariance of its universal-cover branch in every height `N`.
Here `periph0` and `periph1` are the classes of the counterclockwise loops `γ0` around `0` and `γ1`
around `1` based at `1 / 2`; since `UniversalCover`'s left action prepends inverse loops
(`UniversalCover.smul_mk`), `(periph0⁻¹ • ·)` and `(periph1⁻¹ • ·)` prepend `γ0` and `γ1`, so the
counterclockwise continuation shifts are assigned to `periph0⁻¹` and `periph1⁻¹`.

* `TauCeti.Polylog.polylogMonodromy`: representation of `π₁(ℂ \ {0, 1}, 1/2)` via
  `peripheralBasis.lift`, with `MvPolynomial` witnesses, holomorphy, truncation, ODE invariance,
  and weight-two noncommutativity `4π²` (`polylogMonodromy_periph1_inv_periph0_inv_sub_two`).
* `TauCeti.Polylog.IsPolylogTowerGerm`: germ-level `γ0`/`γ1` monodromy and universal-cover
  equivariance at `1 / 2` normalized by `F (1 / 2) 0 = Complex.log (1 / 2)`.
* `TauCeti.Polylog.continuesInside_polylogTower`, `TauCeti.Polylog.polylogBranch`,
  `TauCeti.Polylog.polylogBranch_eq_polylog_of_one_sub_mem_slitPlane`,
  `TauCeti.Polylog.polylogBranch_smul`, `TauCeti.Polylog.exists_polylogBranch_monodromy`: all-height
  continuation, universal-cover branch, principal-domain comparison, and polynomial
  `π₁`-equivariance of `polylogTower N`.

## References

* J. Oesterlé, *Polylogarithmes*, Astérisque 216 (1993), §2; D. Zagier, *The dilogarithm function*.
-/

public section

namespace TauCeti.Polylog

open Filter Metric Set ThricePuncturedSphere Topology unitInterval

private def shiftLog (N : ℕ) (c : ℂ) (v : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun i => v i + if (i : ℕ) = 0 then c else 0

private noncomputable def shiftPolylog (N : ℕ) (c : ℂ) (v : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun i => v i + if (i : ℕ) = 0 then 0 else c * v 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)

private def shiftLogEquiv (N : ℕ) (c : ℂ) : Equiv.Perm (Fin (N + 1) → ℂ) where
  toFun := shiftLog N c
  invFun := shiftLog N (-c)
  left_inv v := by ext i; by_cases hi : (i : ℕ) = 0 <;> simp [shiftLog, hi]
  right_inv v := by ext i; by_cases hi : (i : ℕ) = 0 <;> simp [shiftLog, hi]

private noncomputable def shiftPolylogEquiv (N : ℕ) (c : ℂ) : Equiv.Perm (Fin (N + 1) → ℂ) where
  toFun := shiftPolylog N c
  invFun := shiftPolylog N (-c)
  left_inv v := by ext i; by_cases hi : (i : ℕ) = 0 <;> simp [shiftPolylog, hi]; ring
  right_inv v := by ext i; by_cases hi : (i : ℕ) = 0 <;> simp [shiftPolylog, hi]; ring

/-- **Peripheral monodromy of the polylogarithm tower.** Since `periph0`, `periph1` are the classes
of `γ0`, `γ1` while `UniversalCover.smul_mk` prepends inverse loops, `(periph0⁻¹ • ·)` adds `2πi`
to entry `0` and `(periph1⁻¹ • ·)` subtracts `2πi · w₀^(i-1) / (i-1)!` from entries `i ≥ 1`. -/
noncomputable def polylogMonodromy (N : ℕ) :
    FundamentalGroup ThricePuncturedSphere basePt →* Equiv.Perm (Fin (N + 1) → ℂ) :=
  peripheralBasis.lift
    ![shiftLogEquiv N (-(2 * Real.pi * Complex.I)), shiftPolylogEquiv N (2 * Real.pi * Complex.I)]

private theorem polylogMonodromy_periph0_eq (N : ℕ) :
    ⇑(polylogMonodromy N periph0) = shiftLog N (-(2 * Real.pi * Complex.I)) := by
  simp [polylogMonodromy, ← peripheralBasis_zero]; rfl

private theorem polylogMonodromy_periph0_inv_eq (N : ℕ) :
    ⇑(polylogMonodromy N periph0⁻¹) = shiftLog N (2 * Real.pi * Complex.I) := by
  simp [polylogMonodromy, ← peripheralBasis_zero, Equiv.Perm.inv_def, shiftLogEquiv]

private theorem polylogMonodromy_periph1_eq (N : ℕ) :
    ⇑(polylogMonodromy N periph1) = shiftPolylog N (2 * Real.pi * Complex.I) := by
  simp [polylogMonodromy, ← peripheralBasis_one]; rfl

private theorem polylogMonodromy_periph1_inv_eq (N : ℕ) :
    ⇑(polylogMonodromy N periph1⁻¹) = shiftPolylog N (-(2 * Real.pi * Complex.I)) := by
  simp [polylogMonodromy, ← peripheralBasis_one, Equiv.Perm.inv_def]; rfl

/-- Action of `periph0⁻¹` (the deck element prepending `γ0` around `0`) under `polylogMonodromy`. -/
theorem polylogMonodromy_periph0_inv (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N periph0⁻¹ w i = w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 :=
  congrFun (congrFun (polylogMonodromy_periph0_inv_eq N) w) i

/-- Simp normal form (`map_inv` + `Equiv.Perm.coe_inv`) of `polylogMonodromy_periph0_inv`. -/
@[simp] theorem polylogMonodromy_periph0_symm (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    (polylogMonodromy N periph0).symm w i =
      w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  rw [← Equiv.Perm.inv_def, ← map_inv, polylogMonodromy_periph0_inv]

/-- Action of `periph0` under `polylogMonodromy N`. -/
@[simp] theorem polylogMonodromy_periph0 (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N periph0 w i = w i - if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  rw [polylogMonodromy_periph0_eq]; simp [shiftLog, sub_eq_add_neg]; split_ifs <;> ring

/-- Action of `periph1⁻¹` (the deck element prepending `γ1` around `1`) under `polylogMonodromy`. -/
theorem polylogMonodromy_periph1_inv (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N periph1⁻¹ w i = w i - if (i : ℕ) = 0 then 0 else
      2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  rw [polylogMonodromy_periph1_inv_eq]; by_cases hi : (i : ℕ) = 0 <;> simp [shiftPolylog, hi]; ring

/-- Simp normal form (`map_inv` + `Equiv.Perm.coe_inv`) of `polylogMonodromy_periph1_inv`. -/
@[simp] theorem polylogMonodromy_periph1_symm (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    (polylogMonodromy N periph1).symm w i = w i - if (i : ℕ) = 0 then 0 else
      2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  rw [← Equiv.Perm.inv_def, ← map_inv, polylogMonodromy_periph1_inv]

/-- Action of `periph1` under `polylogMonodromy N`. -/
@[simp] theorem polylogMonodromy_periph1 (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N periph1 w i = w i + if (i : ℕ) = 0 then 0 else
      2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  rw [polylogMonodromy_periph1_eq]; rfl

private theorem exists_mvPolynomial_shiftLog (N : ℕ) (c : ℂ) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, shiftLog N c w i = MvPolynomial.eval w P :=
  ⟨MvPolynomial.X i + MvPolynomial.C (if (i : ℕ) = 0 then c else 0), fun _ => by simp [shiftLog]⟩

private theorem exists_mvPolynomial_shiftPolylog (N : ℕ) (c : ℂ) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, shiftPolylog N c w i = MvPolynomial.eval w P :=
  ⟨MvPolynomial.X i + if (i : ℕ) = 0 then 0 else
      MvPolynomial.C (c / (((i : ℕ) - 1).factorial : ℂ)) * MvPolynomial.X 0 ^ ((i : ℕ) - 1),
    fun _ => by by_cases hi : (i : ℕ) = 0 <;> simp [shiftPolylog, hi, div_mul_eq_mul_div]⟩

/-- **Polynomiality of `polylogMonodromy`.** -/
theorem exists_mvPolynomial_polylogMonodromy (N : ℕ)
    (g : FundamentalGroup ThricePuncturedSphere basePt) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, polylogMonodromy N g w i = MvPolynomial.eval w P := by
  let HasPoly (Φ : (Fin (N + 1) → ℂ) → Fin (N + 1) → ℂ) : Prop :=
    ∀ j, ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, Φ w j = MvPolynomial.eval w P
  have hcomp : ∀ {Φ Ψ}, HasPoly Φ → HasPoly Ψ → HasPoly (Φ ∘ Ψ) := fun {Φ Ψ} hΦ hΨ j => by
    choose Q hQ using hΨ; obtain ⟨P, hP⟩ := hΦ j; refine ⟨MvPolynomial.aeval Q P, fun w => ?_⟩
    have hQw : (fun k => MvPolynomial.eval w (Q k)) = Ψ w := funext fun k => (hQ k w).symm
    simp only [MvPolynomial.eval] at hQw hP ⊢
    have hcomp_id : (MvPolynomial.eval₂Hom (RingHom.id ℂ) w).comp
        (algebraMap ℂ (MvPolynomial (Fin (N + 1)) ℂ)) = RingHom.id ℂ := by
      ext c; simp
    rw [Function.comp_apply, hP, MvPolynomial.map_aeval, hcomp_id, hQw]
  refine Subgroup.closure_induction'' (p := fun x _ => HasPoly (polylogMonodromy N x))
    (by rintro _ (rfl | rfl) <;>
          simp only [polylogMonodromy_periph0_eq, polylogMonodromy_periph1_eq]
        exacts [exists_mvPolynomial_shiftLog N _, exists_mvPolynomial_shiftPolylog N _])
    (by rintro _ (rfl | rfl) <;>
          simp only [polylogMonodromy_periph0_inv_eq, polylogMonodromy_periph1_inv_eq]
        exacts [exists_mvPolynomial_shiftLog N _, exists_mvPolynomial_shiftPolylog N _])
    (fun j => ⟨MvPolynomial.X j, by simp⟩)
    (fun _ _ _ _ ihx ihy => by simpa [MonoidHom.map_mul, Equiv.Perm.coe_mul] using hcomp ihx ihy)
    (closure_periph0_periph1 ▸ Subgroup.mem_top g) i

/-- Pointwise complex analyticity of `polylogMonodromy N g` at `w`. -/
theorem analyticAt_polylogMonodromy (N : ℕ) (g : FundamentalGroup ThricePuncturedSphere basePt)
    (w : Fin (N + 1) → ℂ) : AnalyticAt ℂ (polylogMonodromy N g) w :=
  AnalyticAt.pi fun i => by
    obtain ⟨P, hP⟩ := exists_mvPolynomial_polylogMonodromy N g i
    simpa [← funext hP] using AnalyticOnNhd.eval_mvPolynomial P w (mem_univ w)

/-- Every monodromy operator `polylogMonodromy N g` is complex analytic on any set `s`. -/
theorem analyticOnNhd_polylogMonodromy (N : ℕ) (g : FundamentalGroup ThricePuncturedSphere basePt)
    (s : Set (Fin (N + 1) → ℂ)) : AnalyticOnNhd ℂ (polylogMonodromy N g) s :=
  fun w _ => analyticAt_polylogMonodromy N g w

/-- `polylogMonodromy` commutes with truncating the tower along `Fin.castLE h`. -/
@[simp] theorem polylogMonodromy_castLE {M N : ℕ} (h : M + 1 ≤ N + 1)
    (g : FundamentalGroup ThricePuncturedSphere basePt) (w : Fin (N + 1) → ℂ) (i : Fin (M + 1)) :
    polylogMonodromy N g w (Fin.castLE h i) =
      polylogMonodromy M g (fun j => w (Fin.castLE h j)) i := by
  let _ := MulAction.compHom (Fin (N + 1) → ℂ) (polylogMonodromy N)
  let _ := MulAction.compHom (Fin (M + 1) → ℂ) (polylogMonodromy M)
  let π : (Fin (N + 1) → ℂ) → Fin (M + 1) → ℂ := fun v j => v (Fin.castLE h j)
  exact congrFun (TauCeti.apply_smul_eq_of_mem_closure (f := π)
    (fun x hx v => by rcases hx with rfl | rfl <;> ext j <;> simp [π, MulAction.compHom_smul_def])
    (closure_periph0_periph1 ▸ Subgroup.mem_top g) w) i

/-- **Noncommutativity of the peripheral monodromy at weight two (`Li₂`).** -/
theorem polylogMonodromy_periph1_inv_periph0_inv_sub_two {N : ℕ} (hN : 2 ≤ N)
    (w : Fin (N + 1) → ℂ) :
    polylogMonodromy N periph1⁻¹ (polylogMonodromy N periph0⁻¹ w) ⟨2, Nat.succ_lt_succ hN⟩ -
      polylogMonodromy N periph0⁻¹ (polylogMonodromy N periph1⁻¹ w) ⟨2, Nat.succ_lt_succ hN⟩ =
      4 * (Real.pi : ℂ) ^ 2 := by
  simp only [polylogMonodromy_periph1_inv, polylogMonodromy_periph0_inv, Fin.val_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero]; norm_num; ring_nf; simp [Complex.I_sq]

private theorem half_mem_slitPlane : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))

private theorem sub_half_mem_slitPlane : 1 - (1 / 2 : ℂ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))

namespace IsPolylogTowerGerm

private theorem shiftLog_comp {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w) (k : ℤ) :
    IsPolylogTowerGerm N (shiftLog N ((k : ℂ) * (2 * Real.pi * Complex.I)) ∘ F) w where
  analyticAt := AnalyticAt.pi fun i => (analyticAt_pi_iff.1 hF.analyticAt i).add analyticAt_const
  eventually_exp_zero := hF.eventually_exp_zero.mono fun _ hexp => by
    simp [shiftLog, Complex.exp_add, hexp, Complex.exp_int_mul_two_pi_mul_I]
  eventually_deriv_succ i := hF.eventually_deriv_succ i |>.mono fun z hode => by
    have hsucc : (fun u => (shiftLog N ((k : ℂ) * (2 * Real.pi * Complex.I)) ∘ F) u i.succ) =
        fun u => F u i.succ := by ext u; simp [shiftLog]
    rw [hsucc]; by_cases hi : (i : ℕ) = 0 <;> simpa [hi, shiftLog] using hode

private theorem shiftPolylog_comp {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w) (c : ℂ) :
    IsPolylogTowerGerm N (shiftPolylog N c ∘ F) w where
  analyticAt := AnalyticAt.pi fun i => by
    obtain ⟨P, hP⟩ := exists_mvPolynomial_shiftPolylog N c i
    exact ((AnalyticOnNhd.eval_mvPolynomial P (F w) (mem_univ _)).comp hF.analyticAt).congr
      (Eventually.of_forall fun z => (hP (F z)).symm)
  eventually_exp_zero := hF.eventually_exp_zero.mono fun _ h => by simpa [shiftPolylog] using h
  eventually_deriv_succ i := by
    filter_upwards [hF.eventually_deriv_succ i, hF.eventually_deriv_zero,
      (analyticAt_pi_iff.1 hF.analyticAt 0).eventually_analyticAt,
      (analyticAt_pi_iff.1 hF.analyticAt i.succ).eventually_analyticAt] with z hode hd0 hz0 hzs
    rcases i with ⟨_ | m, hm⟩
    · simp only [Fin.succ_mk, Fin.castSucc_mk] at hode ⊢
      have hfn : (fun u => (shiftPolylog N c ∘ F) u ⟨1, Nat.succ_lt_succ hm⟩) =
          fun u => F u ⟨1, Nat.succ_lt_succ hm⟩ + c := by ext u; simp [shiftPolylog]
      rwa [hfn, deriv_add_const]
    · simp only [Fin.succ_mk, Fin.castSucc_mk, Nat.succ_ne_zero, ↓reduceIte] at hzs hode ⊢
      have hfn : (fun u => (shiftPolylog N c ∘ F) u ⟨m + 2, Nat.succ_lt_succ hm⟩) = fun u =>
          F u ⟨m + 2, Nat.succ_lt_succ hm⟩ + c / ((m + 1).factorial : ℂ) * (F u 0) ^ (m + 1) := by
        ext u; simp [shiftPolylog, div_mul_eq_mul_div]
      have hhd_term : HasDerivAt (fun u => c / ((m + 1).factorial : ℂ) * (F u 0) ^ (m + 1))
          (c / ((m + 1).factorial : ℂ) *
            (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z)) z :=
        (hz0.differentiableAt.hasDerivAt.pow (m + 1)).const_mul _
      have hd_sum : deriv (fun u => (shiftPolylog N c ∘ F) u ⟨m + 2, Nat.succ_lt_succ hm⟩) z =
          deriv (fun u => F u ⟨m + 2, Nat.succ_lt_succ hm⟩) z + c / ((m + 1).factorial : ℂ) *
            (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z) := by
        rw [hfn]; exact (hzs.differentiableAt.hasDerivAt.add hhd_term).deriv
      rw [hd_sum, mul_add, hode]
      simp only [Function.comp_apply, shiftPolylog, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel]; congr 1
      calc z * (c / ((m + 1).factorial : ℂ) *
              (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z))
          = (c * ((m + 1 : ℕ) : ℂ) * (F z 0) ^ m / (((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ))) *
              (z * deriv (fun u => F u 0) z) := by rw [Nat.factorial_succ, Nat.cast_mul]; ring
        _ = c * (F z 0) ^ m / (m.factorial : ℂ) := by
              rw [hd0, mul_one]; field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)]

/-- **Monodromy invariance of the polylogarithm tower differential system.** -/
theorem polylogMonodromy_comp {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w) (g : FundamentalGroup ThricePuncturedSphere basePt) :
    IsPolylogTowerGerm N (polylogMonodromy N g ∘ F) w := by
  refine Subgroup.closure_induction''
    (p := fun x _ => ∀ G : ℂ → Fin (N + 1) → ℂ, IsPolylogTowerGerm N G w →
      IsPolylogTowerGerm N (polylogMonodromy N x ∘ G) w)
    (by rintro _ (rfl | rfl) _ hG
        · rw [polylogMonodromy_periph0_eq]; simpa using hG.shiftLog_comp (-1)
        · rw [polylogMonodromy_periph1_eq]; exact hG.shiftPolylog_comp _)
    (by rintro _ (rfl | rfl) _ hG
        · rw [polylogMonodromy_periph0_inv_eq]; simpa using hG.shiftLog_comp 1
        · rw [polylogMonodromy_periph1_inv_eq]; exact hG.shiftPolylog_comp _)
    (fun _ hG => by simpa using hG)
    (fun _ _ _ _ ihx ihy G hG => by
      rw [MonoidHom.map_mul, Equiv.Perm.coe_mul, Function.comp_assoc]; exact ihx _ (ihy G hG))
    (closure_periph0_periph1 ▸ Subgroup.mem_top g) F hF

/-- If `hF : IsPolylogTowerGerm N F (1 / 2)` has `F (1 / 2) 0 = log (1 / 2)`, `F · 0 =ᶠ log`. -/
theorem eventuallyEq_log_half {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (1 / 2)) (hF0 : F (1 / 2) 0 = Complex.log (1 / 2)) :
    (fun z => F z 0) =ᶠ[𝓝 (1 / 2 : ℂ)] Complex.log := by
  have heq := ((hF.castLE (Nat.succ_le_succ (Nat.zero_le N))).eventuallyEq_iff_eq
    (isPolylogTowerGerm_polylogTower 0 half_mem_slitPlane (fun h => (h rfl).elim))).mpr
      (by ext i; fin_cases i; simpa [polylogTower_zero] using hF0)
  exact heq.mono fun z hz => by simpa [polylogTower_zero] using congrFun hz 0

end IsPolylogTowerGerm

private noncomputable def logCont0 (t : I) (z : ℂ) : ℂ :=
  Complex.log (z * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ)))) +
    2 * Real.pi * Complex.I * (t : ℂ)

private theorem γ0_mul_exp_neg (t : I) :
    (γ0 t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) = 1 / 2 := by
  rw [coe_γ0_eq_exp, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

private theorem logCont0_zero : logCont0 0 = Complex.log := by ext z; simp [logCont0]

private theorem logCont0_one (z : ℂ) : logCont0 1 z = Complex.log z + 2 * Real.pi * Complex.I := by
  have h1 : (((1 : I) : ℝ) : ℂ) = 1 := by simp
  rw [logCont0, h1, mul_one, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

private theorem exp_logCont0 (t : I) {z : ℂ} (hz : z ≠ 0) : Complex.exp (logCont0 t z) = z := by
  rw [logCont0, Complex.exp_add, Complex.exp_log (mul_ne_zero hz (Complex.exp_ne_zero _)),
    mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

private theorem isAnalyticContinuationAlong_logCont0 :
    IsAnalyticContinuationAlong logCont0 (fun t => (γ0 t : ℂ)) univ where
  continuousOn := (continuous_subtypeVal.comp γ0.continuous).continuousOn
  analyticAt t _ := by
    have hval : (γ0 t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) ∈
        Complex.slitPlane := (γ0_mul_exp_neg t).symm ▸ half_mem_slitPlane
    exact ((analyticAt_id.mul analyticAt_const).clog hval).add analyticAt_const
  locallyEq t _ := by
    let rot : I × ℂ → ℂ := fun p => p.2 * Complex.exp (-(2 * Real.pi * Complex.I * ((p.1 : ℝ) : ℂ)))
    have hrot_val : rot (t, (γ0 t : ℂ)) ∈ Complex.slitPlane := by
      dsimp only [rot]; exact (γ0_mul_exp_neg t).symm ▸ half_mem_slitPlane
    have hcont1 : ContinuousAt (fun p : I × ℂ => logCont0 p.1 p.2) (t, (γ0 t : ℂ)) :=
      ((by fun_prop : Continuous rot).continuousAt.clog hrot_val).add (by fun_prop)
    have hcont2 : ContinuousAt (fun p : I × ℂ => logCont0 t p.2) (t, (γ0 t : ℂ)) :=
      ((continuous_snd.mul continuous_const).continuousAt.clog hrot_val).add continuousAt_const
    have hlt : ∀ᶠ p : I × ℂ in 𝓝 (t, (γ0 t : ℂ)), ‖logCont0 p.1 p.2 - logCont0 t p.2‖ < 1 := by
      simpa using Metric.tendsto_nhds.mp (hcont1.sub hcont2) 1 zero_lt_one
    have hmem : {p : I × ℂ | ‖logCont0 p.1 p.2 - logCont0 t p.2‖ < 1 ∧ p.2 ≠ 0} ∈
        𝓝 t ×ˢ 𝓝 (γ0 t : ℂ) := by
      rw [← nhds_prod_eq]; exact hlt.and (continuous_snd.continuousAt.eventually
        (eventually_ne_nhds (ThricePuncturedSphere.ne_zero _)))
    obtain ⟨V, hV, W', hW', hVW'⟩ := Filter.mem_prod_iff.mp hmem
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW'
    filter_upwards [nhdsWithin_le_nhds (Filter.inter_mem hV
      ((continuous_subtypeVal.comp γ0.continuous).continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds (mem_ball_self hε))))] with u ⟨huV, huW⟩
    filter_upwards [isOpen_ball.mem_nhds huW] with z hzW
    obtain ⟨hnorm, hz0⟩ := hVW' (mk_mem_prod huV (hεW hzW))
    exact Complex.eq_of_exp_eq_of_norm_sub_lt
      ((exp_logCont0 u hz0).trans (exp_logCont0 t hz0).symm)
      (hnorm.trans (by linarith [Real.two_le_pi]))

private noncomputable def li1Cont1 (t : I) (z : ℂ) : ℂ := -logCont0 t (1 - z)

private theorem one_sub_γ1 (t : I) : 1 - (γ1 t : ℂ) = (γ0 t : ℂ) := by
  rw [coe_γ1_eq_exp, coe_γ0_eq_exp]; ring

private theorem li1Cont1_zero : li1Cont1 0 = polylog 1 := by ext z; simp [li1Cont1, logCont0_zero]

private theorem li1Cont1_one (z : ℂ) : li1Cont1 1 z = polylog 1 z - 2 * Real.pi * Complex.I := by
  simp [li1Cont1, logCont0_one]; ring

private theorem isAnalyticContinuationAlong_li1Cont1 :
    IsAnalyticContinuationAlong li1Cont1 (fun t => (γ1 t : ℂ)) univ where
  continuousOn := (continuous_subtypeVal.comp γ1.continuous).continuousOn
  analyticAt t _ := (((one_sub_γ1 t).symm ▸ isAnalyticContinuationAlong_logCont0.analyticAt t
    (mem_univ t)).comp (analyticAt_const.sub analyticAt_id)).neg
  locallyEq t _ := by
    filter_upwards [isAnalyticContinuationAlong_logCont0.locallyEq t (mem_univ t)] with u hu
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) (γ1 u : ℂ) :=
      continuousAt_const.sub continuousAt_id
    filter_upwards [hcont.eventually ((one_sub_γ1 u).symm ▸ hu)] with z hz; simp [li1Cont1, hz]

private noncomputable def logSing1 (N : ℕ) (w z : ℂ) : Fin (N + 1) → ℂ :=
  fun i => if (i : ℕ) = 0 then 0 else
    w * (Complex.log z) ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)

private theorem analyticAt_logSing1 (N : ℕ) {w : ℂ → ℂ} {z : ℂ} (hw : AnalyticAt ℂ w z)
    (hz : z ∈ Complex.slitPlane) : AnalyticAt ℂ (fun u => logSing1 N (w u) u) z :=
  AnalyticAt.pi fun i => by
    by_cases hi : (i : ℕ) = 0
    · simp [logSing1, hi, analyticAt_const]
    · simp only [logSing1, hi, ↓reduceIte]
      exact (hw.mul ((analyticAt_id.clog hz).pow _)).div analyticAt_const
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

private theorem analyticAt_add_logSing1 {N : ℕ} {A : ℂ → Fin (N + 1) → ℂ}
    (hAan : AnalyticOnNhd ℂ A (ball 1 (3 / 4))) :
    AnalyticAt ℂ (fun z => A z + logSing1 N (polylog 1 z) z) (1 / 2) :=
  (hAan _ (by rw [mem_ball, dist_eq_norm]; norm_num)).add
    (analyticAt_logSing1 N (analyticAt_polylog 1 sub_half_mem_slitPlane) half_mem_slitPlane)

private theorem eventually_deriv_last_logSing1 {K : ℕ} {g a : ℂ → ℂ}
    (haderiv : ∀ z ∈ ball (1 : ℂ) (3 / 4), HasDerivAt a
      (g z / z + dslope (fun u => (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) 1 z) z) :
    ∀ᶠ z in 𝓝 (1 / 2 : ℂ), z * deriv (fun u => a u +
        polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) z =
      g z + polylog 1 z * (Complex.log z) ^ K / (K.factorial : ℂ) := by
  let B : ℂ → ℂ := fun u => (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)
  filter_upwards [isOpen_ball.mem_nhds (by rw [mem_ball, dist_eq_norm]; norm_num :
      (1 / 2 : ℂ) ∈ ball 1 (3 / 4)), Complex.isOpen_slitPlane.mem_nhds half_mem_slitPlane,
    Complex.isOpen_setOf_one_sub_mem_slitPlane.mem_nhds sub_half_mem_slitPlane] with z hzb hz0 hz1
  have hz_ne : z ≠ 0 := Complex.slitPlane_ne_zero hz0
  have h1z_ne : 1 - z ≠ 0 := Complex.slitPlane_ne_zero hz1
  have hd_B : HasDerivAt B ((Complex.log z) ^ K / (K.factorial : ℂ) / z) z := by
    convert ((Complex.hasDerivAt_log hz0).pow (K + 1)).div_const ((K + 1).factorial : ℂ) using 1
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, div_div]
    field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero K), hz_ne]
  have hB_eq : B z = -(1 - z) * dslope B 1 z := by
    have hsub := sub_smul_dslope B 1 z
    rw [(by simp [B] : B 1 = 0), sub_zero, smul_eq_mul] at hsub; rw [← hsub]; ring
  have hfun : (fun u => a u + polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) =
      fun u => a u + polylog 1 u * B u := by ext u; dsimp [B]; ring
  have hd_tot : HasDerivAt (fun u => a u + polylog 1 u * B u) _ z :=
    (haderiv z hzb).add ((hasDerivAt_polylog_one hz1).mul hd_B)
  rw [hfun, hd_tot.deriv, hB_eq, neg_mul, mul_neg, inv_mul_cancel_left₀ h1z_ne]
  field_simp [hz_ne]; ring

private theorem exists_analyticOnNhd_ball_one_succ {K : ℕ} {A' : ℂ → Fin (K + 2) → ℂ}
    (hA'an : AnalyticOnNhd ℂ A' (ball 1 (3 / 4)))
    (hG' : IsPolylogTowerGerm (K + 1) (fun z => A' z + logSing1 (K + 1) (polylog 1 z) z) (1 / 2))
    (c : ℂ) : ∃ A : ℂ → Fin (K + 3) → ℂ, AnalyticOnNhd ℂ A (ball 1 (3 / 4)) ∧
      (A (1 / 2) + logSing1 (K + 2) (polylog 1 (1 / 2)) (1 / 2)) =
        Fin.lastCases c (A' (1 / 2) + logSing1 (K + 1) (polylog 1 (1 / 2)) (1 / 2)) ∧
      IsPolylogTowerGerm (K + 2) (fun z => A z + logSing1 (K + 2) (polylog 1 z) z) (1 / 2) := by
  have hslit : ∀ z ∈ ball (1 : ℂ) (3 / 4), z ∈ Complex.slitPlane := fun _ hz =>
    Complex.ball_one_subset_slitPlane (ball_subset_ball (by norm_num) hz)
  let B : ℂ → ℂ := fun z => (Complex.log z) ^ (K + 1) / ((K + 1).factorial : ℂ)
  have hBan : AnalyticOnNhd ℂ B (ball 1 (3 / 4)) := fun z hz =>
    ((analyticAt_id.clog (hslit z hz)).pow (K + 1)).div analyticAt_const
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hdslope : AnalyticOnNhd ℂ (dslope B 1) (ball 1 (3 / 4)) :=
    ((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))).mpr
      hBan.differentiableOn).analyticOnNhd isOpen_ball
  have hrhs : AnalyticOnNhd ℂ (fun z => A' z (Fin.last (K + 1)) / z + dslope B 1 z)
      (ball 1 (3 / 4)) := fun z hz =>
    ((analyticAt_pi_iff.1 (hA'an z hz) _).div analyticAt_id
      (Complex.slitPlane_ne_zero (hslit z hz))).add (hdslope z hz)
  obtain ⟨a, ha_val, haderiv⟩ := (hrhs.differentiableOn.isExactOn_ball).with_val_at (1 / 2)
    (c - polylog 1 (1 / 2) * B (1 / 2))
  have ha_an : AnalyticOnNhd ℂ a (ball 1 (3 / 4)) := DifferentiableOn.analyticOnNhd
    (fun z hz => (haderiv z hz).differentiableAt.differentiableWithinAt) isOpen_ball
  let A : ℂ → Fin (K + 3) → ℂ := fun z => Fin.lastCases (a z) (A' z)
  have hAan : AnalyticOnNhd ℂ A (ball 1 (3 / 4)) := fun z hz => AnalyticAt.pi <|
    Fin.lastCases (by simpa [A, Fin.lastCases_last] using ha_an z hz)
      fun j => by simpa [A, Fin.lastCases_castSucc] using analyticAt_pi_iff.1 (hA'an z hz) j
  have hGcast : ∀ u (j : Fin (K + 2)), (A u + logSing1 (K + 2) (polylog 1 u) u) j.castSucc =
      (A' u + logSing1 (K + 1) (polylog 1 u) u) j :=
    fun u j => by simp [A, logSing1, Fin.lastCases_castSucc]
  have h0cast : (0 : Fin (K + 3)) = (0 : Fin (K + 2)).castSucc := rfl
  refine ⟨A, hAan, ?_, analyticAt_add_logSing1 hAan,
    hG'.eventually_exp_zero.mono fun z hz => by rwa [h0cast, hGcast z 0],
    Fin.lastCases ?_ fun j => ?_⟩
  · ext i; refine Fin.lastCases ?_ (fun j => by rw [hGcast (1 / 2) j, Fin.lastCases_castSucc]) i
    have hk : K + 2 - 1 = K + 1 := rfl
    simp only [A, Pi.add_apply, logSing1, Fin.val_last, Nat.succ_ne_zero, ↓reduceIte, hk,
      Fin.lastCases_last, ha_val, B]; ring
  · have hlast : (fun u => (A u + logSing1 (K + 2) (polylog 1 u) u) (Fin.last (K + 1)).succ) =
        fun u => a u + polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ) := by
      ext u; rw [(Fin.ext rfl : (Fin.last (K + 1)).succ = Fin.last (K + 2)), Pi.add_apply]
      dsimp only [A, logSing1]; rw [Fin.lastCases_last]; simp
    filter_upwards [eventually_deriv_last_logSing1 haderiv] with z hz
    rw [hlast, hGcast z (Fin.last (K + 1))]; simpa [Fin.val_last, logSing1] using hz
  · have hs : (fun u => (A u + logSing1 (K + 2) (polylog 1 u) u) (Fin.castSucc j).succ) =
        fun u => (A' u + logSing1 (K + 1) (polylog 1 u) u) j.succ :=
      funext fun u => (congrArg _ (Fin.ext rfl : j.castSucc.succ = j.succ.castSucc)).trans
        (hGcast u j.succ)
    exact (hG'.eventually_deriv_succ j).mono fun z hz => by rwa [hs, hGcast z j.castSucc]

private theorem exists_analyticOnNhd_ball_one_add_logSing1 :
    ∀ (N : ℕ) (v : Fin (N + 1) → ℂ), v 0 = Complex.log (1 / 2) →
      ∃ A : ℂ → Fin (N + 1) → ℂ, AnalyticOnNhd ℂ A (ball 1 (3 / 4)) ∧
        (A (1 / 2) + logSing1 N (polylog 1 (1 / 2)) (1 / 2)) = v ∧
        IsPolylogTowerGerm N (fun z => A z + logSing1 N (polylog 1 z) z) (1 / 2)
  | 0, v, hv0 => by
    refine ⟨polylogTower 0, fun z hz => AnalyticAt.pi fun i => ?_,
      by ext i; fin_cases i; simp [logSing1, hv0],
      (isPolylogTowerGerm_polylogTower 0 half_mem_slitPlane (fun h => (h rfl).elim)).congr
        (Eventually.of_forall fun z => by ext i; fin_cases i; simp [logSing1])⟩
    fin_cases i; simpa [polylogTower_zero] using
      analyticAt_id.clog (Complex.ball_one_subset_slitPlane (ball_subset_ball (by norm_num) hz))
  | 1, v, hv0 =>
    let c₁ : ℂ := v 1 - polylog 1 (1 / 2)
    ⟨fun z => ![Complex.log z, c₁], fun z hz => AnalyticAt.pi <| Fin.cases
      (analyticAt_id.clog (Complex.ball_one_subset_slitPlane (ball_subset_ball (by norm_num) hz)))
      (fun _ => analyticAt_const), by ext i; fin_cases i <;> simp [c₁, logSing1, hv0],
      ((isPolylogTowerGerm_polylogTower 1 half_mem_slitPlane
        (fun _ => sub_half_mem_slitPlane)).shiftPolylog_comp c₁).congr <| .of_forall fun z => by
        ext i; fin_cases i <;> simp [c₁, shiftPolylog, logSing1, polylogTower_apply]; ring⟩
  | K + 2, v, hv0 => by
    obtain ⟨A', hA'an, hA'val, hG'⟩ :=
      exists_analyticOnNhd_ball_one_add_logSing1 (K + 1) (fun j => v j.castSucc) hv0
    obtain ⟨A, hAan, hAval, hG⟩ := exists_analyticOnNhd_ball_one_succ hA'an hG' (v (.last (K + 2)))
    refine ⟨A, hAan, hAval.trans (funext <| Fin.lastCases Fin.lastCases_last fun j => ?_), hG⟩
    exact (Fin.lastCases_castSucc j).trans (congrFun hA'val j)

namespace IsPolylogTowerGerm

/-- **Germ-level `γ0`-monodromy** for an `IsPolylogTowerGerm` at `1 / 2` normalized by
`F (1 / 2) 0 = Complex.log (1 / 2)` whose positive weights extend analytically to `ball 0 1`. -/
theorem eventuallyEq_periph0_inv_comp_of_γ0 {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (1 / 2)) (hF0 : F (1 / 2) 0 = Complex.log (1 / 2))
    {G : ℂ → Fin N → ℂ} (hGan : AnalyticOnNhd ℂ G (ball 0 1))
    (hFG : ∀ i : Fin N, (fun z => F z i.succ) =ᶠ[𝓝 (1 / 2 : ℂ)] fun z => G z i)
    {f : I → ℂ → Fin (N + 1) → ℂ} (hf : IsAnalyticContinuationAlong f (fun t => (γ0 t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (1 / 2 : ℂ)] F) : f 1 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogMonodromy N periph0⁻¹ ∘ F := by
  have hF0_eq := hF.eventuallyEq_log_half hF0
  let g : I → ℂ → Fin (N + 1) → ℂ := fun t z => Fin.cases (logCont0 t z) (fun i => G z i)
  have hγ0_ball : ∀ t : I, (γ0 t : ℂ) ∈ ball 0 1 := fun t => by
    rw [mem_ball, dist_zero_right, norm_coe_γ0]; norm_num
  have hg : IsAnalyticContinuationAlong g (fun t => (γ0 t : ℂ)) univ :=
    ⟨(continuous_subtypeVal.comp γ0.continuous).continuousOn, fun t _ => AnalyticAt.pi <| Fin.cases
      (isAnalyticContinuationAlong_logCont0.analyticAt t (mem_univ t))
      (fun i => analyticAt_pi_iff.1 (hGan _ (hγ0_ball t)) i), fun t _ =>
      (isAnalyticContinuationAlong_logCont0.locallyEq t (mem_univ t)).mono fun _ hu =>
        hu.mono fun _ hz => funext (Fin.cases hz fun _ => rfl)⟩
  have hg0 : g 0 =ᶠ[𝓝 (1 / 2 : ℂ)] F := (eventually_all.mpr <| Fin.cases
    (hF0_eq.symm.mono fun z hz => by simp [g, logCont0_zero, hz])
    (fun i => (hFG i).symm.mono fun z hz => by simp [g, hz])).mono fun _ => funext
  have hg1 : g 1 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogMonodromy N periph0⁻¹ ∘ F :=
    (eventually_all.mpr <| Fin.cases (hF0_eq.mono fun z hz => by simp [g, logCont0_one, hz])
      (fun i => (hFG i).mono fun z hz => by simp [g, ← hz])).mono fun _ => funext
  exact ((by rw [Path.target, coe_basePt] : (γ0 1 : ℂ) = 1 / 2) ▸
    hf.eventuallyEq hg isPreconnected_univ (mem_univ 0) (mem_univ 1)
      ((by rw [Path.source, coe_basePt] : (γ0 0 : ℂ) = 1 / 2).symm ▸ hf0.trans hg0.symm)).trans hg1

/-- **Germ-level `γ1`-monodromy** for an `IsPolylogTowerGerm` at `1 / 2` normalized by
`F (1 / 2) 0 = Complex.log (1 / 2)` (without assuming `ball 0 1` analyticity). -/
theorem eventuallyEq_periph1_inv_comp_of_γ1 {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (1 / 2)) (hF0 : F (1 / 2) 0 = Complex.log (1 / 2))
    {f : I → ℂ → Fin (N + 1) → ℂ} (hf : IsAnalyticContinuationAlong f (fun t => (γ1 t : ℂ)) univ)
    (hf0 : f 0 =ᶠ[𝓝 (1 / 2 : ℂ)] F) : f 1 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogMonodromy N periph1⁻¹ ∘ F := by
  obtain ⟨A, hAan, hAval, hG⟩ := exists_analyticOnNhd_ball_one_add_logSing1 N (F (1 / 2)) hF0
  have hGF : (fun z => A z + logSing1 N (polylog 1 z) z) =ᶠ[𝓝 (1 / 2 : ℂ)] F :=
    (hG.eventuallyEq_iff_eq hF).mpr hAval
  have hF0_eq := hF.eventuallyEq_log_half hF0
  let g : I → ℂ → Fin (N + 1) → ℂ := fun t z => A z + logSing1 N (li1Cont1 t z) z
  have hγ1_ball : ∀ t : I, (γ1 t : ℂ) ∈ ball (1 : ℂ) (3 / 4) := fun t => by
    rw [mem_ball, dist_eq_norm, norm_coe_γ1_sub_one]; norm_num
  have hγ1_slit : ∀ t : I, (γ1 t : ℂ) ∈ Complex.slitPlane := fun t =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (mem_rightOpen.1 (γ1_mem_rightOpen t)))
  have hg : IsAnalyticContinuationAlong g (fun t => (γ1 t : ℂ)) univ :=
    ⟨(continuous_subtypeVal.comp γ1.continuous).continuousOn, fun t _ => (hAan _ (hγ1_ball t)).add
      (analyticAt_logSing1 N (isAnalyticContinuationAlong_li1Cont1.analyticAt t (mem_univ t))
        (hγ1_slit t)), fun t _ =>
      (isAnalyticContinuationAlong_li1Cont1.locallyEq t (mem_univ t)).mono fun _ hu =>
        hu.mono fun z hz => by ext i; simp [g, logSing1, hz]⟩
  have hg0 : g 0 =ᶠ[𝓝 (1 / 2 : ℂ)] F := by simpa [g, li1Cont1_zero] using hGF
  have hg1 : g 1 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogMonodromy N periph1⁻¹ ∘ F := by
    filter_upwards [hGF, hF0_eq] with z hz hz0; ext i
    if hi : (i : ℕ) = 0 then simp [g, logSing1, hi, ← hz]
    else rw [Function.comp_apply, polylogMonodromy_periph1_inv, hz0, ← hz]
         simp only [g, Pi.add_apply, logSing1, hi, ↓reduceIte, li1Cont1_one]; ring
  exact ((by rw [Path.target, coe_basePt] : (γ1 1 : ℂ) = 1 / 2) ▸
    hf.eventuallyEq hg isPreconnected_univ (mem_univ 0) (mem_univ 1)
      ((by rw [Path.source, coe_basePt] : (γ1 0 : ℂ) = 1 / 2).symm ▸ hf0.trans hg0.symm)).trans hg1

/-- **`periph0⁻¹`-monodromy on the universal cover** for `IsPolylogTowerGerm` at `basePt = 1 / 2`
with `F (1 / 2) 0 = Complex.log (1 / 2)` whose positive weights are analytic on `ball 0 1`. -/
theorem universalCoverBranch_periph0_inv_smul_of_analyticOnNhd_ball {N : ℕ}
    {F : ℂ → Fin (N + 1) → ℂ} (hF : IsPolylogTowerGerm N F (basePt : ℂ))
    (hF0 : F (1 / 2) 0 = Complex.log (1 / 2)) {G : ℂ → Fin N → ℂ}
    (hGan : AnalyticOnNhd ℂ G (ball 0 1))
    (hFG : ∀ i : Fin N, (fun z => F z i.succ) =ᶠ[𝓝 (1 / 2 : ℂ)] fun z => G z i)
    (p : UniversalCover basePt) :
    hF.continuesInside.universalCoverBranch (periph0⁻¹ • p) =
      polylogMonodromy N periph0⁻¹ (hF.continuesInside.universalCoverBranch p) := by
  obtain ⟨f, hf, hf0, -⟩ :=
    hF.continuesInside.exists_isAnalyticContinuationAlong_universalCoverBranch γ0
  have hf1 : f 1 =ᶠ[𝓝 (basePt : ℂ)] polylogMonodromy N periph0⁻¹ ∘ F := coe_basePt.symm ▸
    (coe_basePt ▸ hF).eventuallyEq_periph0_inv_comp_of_γ0 hF0 hGan hFG hf (coe_basePt ▸ hf0)
  exact periph0_def ▸ hF.continuesInside.universalCoverBranch_inv_smul_of_loop hf hf0
    (analyticOnNhd_polylogMonodromy N periph0⁻¹ univ) hf1 p

/-- **`periph1⁻¹`-monodromy on the universal cover** for `IsPolylogTowerGerm` at `basePt = 1 / 2`
normalized by `F (1 / 2) 0 = Complex.log (1 / 2)` (without assuming `ball 0 1` analyticity). -/
theorem universalCoverBranch_periph1_inv_smul {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (basePt : ℂ)) (hF0 : F (1 / 2) 0 = Complex.log (1 / 2))
    (p : UniversalCover basePt) :
    hF.continuesInside.universalCoverBranch (periph1⁻¹ • p) =
      polylogMonodromy N periph1⁻¹ (hF.continuesInside.universalCoverBranch p) := by
  obtain ⟨f, hf, hf0, -⟩ :=
    hF.continuesInside.exists_isAnalyticContinuationAlong_universalCoverBranch γ1
  have hf1 : f 1 =ᶠ[𝓝 (basePt : ℂ)] polylogMonodromy N periph1⁻¹ ∘ F := coe_basePt.symm ▸
    (coe_basePt ▸ hF).eventuallyEq_periph1_inv_comp_of_γ1 hF0 hf (coe_basePt ▸ hf0)
  exact periph1_def ▸ hF.continuesInside.universalCoverBranch_inv_smul_of_loop hf hf0
    (analyticOnNhd_polylogMonodromy N periph1⁻¹ univ) hf1 p

/-- **Full `π₁`-equivariance** for the universal-cover branch of an `IsPolylogTowerGerm` at
`basePt = 1 / 2` with `F (1 / 2) 0 = Complex.log (1 / 2)` and `ball 0 1`-analytic weights. -/
theorem universalCoverBranch_smul_of_analyticOnNhd_ball {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (basePt : ℂ)) (hF0 : F (1 / 2) 0 = Complex.log (1 / 2))
    {G : ℂ → Fin N → ℂ} (hGan : AnalyticOnNhd ℂ G (ball 0 1))
    (hFG : ∀ i : Fin N, (fun z => F z i.succ) =ᶠ[𝓝 (1 / 2 : ℂ)] fun z => G z i)
    (g : FundamentalGroup ThricePuncturedSphere basePt) (p : UniversalCover basePt) :
    hF.continuesInside.universalCoverBranch (g • p) =
      polylogMonodromy N g (hF.continuesInside.universalCoverBranch p) := by
  let _ := MulAction.compHom (Fin (N + 1) → ℂ) (polylogMonodromy N)
  refine TauCeti.apply_smul_eq_of_mem_closure (f := hF.continuesInside.universalCoverBranch)
    (fun x hx q => ?_) (closure_periph0_periph1 ▸ Subgroup.mem_top g) p
  have hinv : ∀ r, hF.continuesInside.universalCoverBranch (x⁻¹ • r) =
      x⁻¹ • hF.continuesInside.universalCoverBranch r := fun r => by
    rcases hx with rfl | rfl
    · exact hF.universalCoverBranch_periph0_inv_smul_of_analyticOnNhd_ball hF0 hGan hFG r
    · exact hF.universalCoverBranch_periph1_inv_smul hF0 r
  rw [← smul_inv_smul x (hF.continuesInside.universalCoverBranch (x • q)), ← hinv (x • q),
    inv_smul_smul]

end IsPolylogTowerGerm

/-- `polylogTower N` satisfies `IsPolylogTowerGerm N` at `basePt = 1 / 2` in every height `N`. -/
theorem isPolylogTowerGerm_polylogTower_basePt (N : ℕ) :
    IsPolylogTowerGerm N (polylogTower N) (basePt : ℂ) :=
  isPolylogTowerGerm_polylogTower N (coe_basePt.symm ▸ half_mem_slitPlane)
    (fun _ => coe_basePt.symm ▸ sub_half_mem_slitPlane)

/-- `polylogTower N` continues inside `{z : ℂ | z ≠ 0 ∧ z ≠ 1}` from `basePt` in every height. -/
theorem continuesInside_polylogTower (N : ℕ) :
    ContinuesInside (polylogTower N) {z : ℂ | z ≠ 0 ∧ z ≠ 1} (basePt : ℂ) :=
  (isPolylogTowerGerm_polylogTower_basePt N).continuesInside

/-- The coherent universal-cover branch of `polylogTower N` over `ThricePuncturedSphere`. -/
noncomputable def polylogBranch (N : ℕ) : UniversalCover basePt → Fin (N + 1) → ℂ :=
  (continuesInside_polylogTower N).universalCoverBranch

/-- Unfolding characterization of `polylogBranch N`. -/
theorem polylogBranch_def (N : ℕ) :
    polylogBranch N = (continuesInside_polylogTower N).universalCoverBranch := (rfl)

/-- `polylogBranch N` is continuous on the universal cover. -/
@[fun_prop] theorem continuous_polylogBranch (N : ℕ) : Continuous (polylogBranch N) :=
  (continuesInside_polylogTower N).continuous_universalCoverBranch

/-- Every path `γ` from `basePt = 1 / 2` in `ThricePuncturedSphere` admits a continuation of
`polylogTower N` whose endpoint value is `polylogBranch N ⟨z, ⟦γ⟧⟩`. -/
theorem exists_isAnalyticContinuationAlong_polylogBranch (N : ℕ) {z : ThricePuncturedSphere}
    (γ : Path basePt z) : ∃ f : I → ℂ → Fin (N + 1) → ℂ,
      IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ ∧
      (f 0 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogTower N) ∧
      polylogBranch N ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ) := by
  simpa [coe_basePt, polylogBranch_def] using
    (continuesInside_polylogTower N).exists_isAnalyticContinuationAlong_universalCoverBranch γ

/-- Along a path `γ` from `basePt = 1 / 2` in `ThricePuncturedSphere` staying in the principal
polylogarithm domain `{z | 1 - z ∈ Complex.slitPlane}` (without needing `γ t ∈ Complex.slitPlane`
for entry `0`), every positive-weight coordinate `i` (`(i : ℕ) ≠ 0`) of `polylogBranch N` agrees
at the endpoint with the principal polylogarithm `polylog (i : ℕ) (z : ℂ)`. -/
theorem polylogBranch_eq_polylog_of_one_sub_mem_slitPlane (N : ℕ) {z : ThricePuncturedSphere}
    (γ : Path basePt z) (hγ : ∀ t : I, 1 - (γ t : ℂ) ∈ Complex.slitPlane)
    {i : Fin (N + 1)} (hi : (i : ℕ) ≠ 0) :
    polylogBranch N ⟨z, Path.Homotopic.Quotient.mk γ⟩ i = polylog (i : ℕ) (z : ℂ) := by
  obtain ⟨f, hf, hf0, hval⟩ := exists_isAnalyticContinuationAlong_polylogBranch N γ
  have hcont : IsAnalyticContinuationAlong (fun _ => polylog (i : ℕ)) (fun t => (γ t : ℂ)) univ :=
    .const (continuous_subtypeVal.comp γ.continuous).continuousOn
      fun t _ => analyticAt_polylog (i : ℕ) (hγ t)
  have h0 : (fun w => f 0 w i) =ᶠ[𝓝 (γ 0 : ℂ)] polylog (i : ℕ) := by
    rw [Path.source, coe_basePt]
    exact hf0.mono fun w hw => by simp [hw, polylogTower_apply_of_ne_zero w hi]
  have heq := (hf.eval i).eventuallyEq hcont isPreconnected_univ (mem_univ 0) (mem_univ 1) h0
  rw [Path.target] at heq
  exact (congrFun hval i).trans heq.eq_of_nhds

/-- Truncating `polylogBranch N` along `Fin.castLE h` agrees with `polylogBranch M`. -/
@[simp] theorem polylogBranch_castLE {M N : ℕ} (h : M + 1 ≤ N + 1) (p : UniversalCover basePt)
    (i : Fin (M + 1)) : polylogBranch N p (Fin.castLE h i) = polylogBranch M p i := by
  rw [polylogBranch_def, polylogBranch_def,
    ← (isPolylogTowerGerm_polylogTower_basePt N).universalCoverBranch_castLE h p i,
    ContinuesInside.universalCoverBranch_congr _
      (.of_forall fun z => funext (polylogTower_castLE h z))]

/-- **Equivariance of `polylogBranch N` under `π₁(ℂ \ {0, 1}, 1/2)` in every height `N`.** -/
theorem polylogBranch_smul (N : ℕ) (g : FundamentalGroup ThricePuncturedSphere basePt)
    (p : UniversalCover basePt) :
    polylogBranch N (g • p) = polylogMonodromy N g (polylogBranch N p) :=
  (isPolylogTowerGerm_polylogTower_basePt N).universalCoverBranch_smul_of_analyticOnNhd_ball
    (polylogTower_zero N (1 / 2)) (G := fun z i => polylog (i.succ : ℕ) z)
    (fun z hz => AnalyticAt.pi fun i => analyticAt_polylog (i.succ : ℕ)
      (sub_eq_add_neg (1 : ℂ) z ▸ Complex.mem_slitPlane_of_norm_lt_one (by simpa using hz)))
    (fun i => Eventually.of_forall fun z => polylogTower_succ N z i) g p

/-- **Coherent universal-cover branch and polynomial monodromy of `polylogTower N`.** -/
theorem exists_polylogBranch_monodromy (N : ℕ) :
    ∃ (B : UniversalCover basePt → Fin (N + 1) → ℂ)
      (ρ : FundamentalGroup ThricePuncturedSphere basePt →* Equiv.Perm (Fin (N + 1) → ℂ)),
      (∀ (z : ThricePuncturedSphere) (γ : Path basePt z),
        ∃ f : I → ℂ → Fin (N + 1) → ℂ, IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ ∧
          (f 0 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogTower N) ∧
          B ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ)) ∧
      (∀ g i, ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, ρ g w i = MvPolynomial.eval w P) ∧
      (∀ w i, ρ periph0⁻¹ w i = w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0) ∧
      (∀ w i, ρ periph1⁻¹ w i = w i - if (i : ℕ) = 0 then 0 else
        2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)) ∧
      (∀ g p, B (g • p) = ρ g (B p)) :=
  ⟨polylogBranch N, polylogMonodromy N, fun _ => exists_isAnalyticContinuationAlong_polylogBranch N,
    exists_mvPolynomial_polylogMonodromy N, polylogMonodromy_periph0_inv N,
    polylogMonodromy_periph1_inv N, polylogBranch_smul N⟩

/-- At the constant path class at `basePt`, `polylogBranch N` equals `polylogTower N (1 / 2)`. -/
@[simp] theorem polylogBranch_refl (N : ℕ) :
    polylogBranch N ⟨basePt, Path.Homotopic.Quotient.refl basePt⟩ = polylogTower N (1 / 2) := by
  rw [polylogBranch_def, ContinuesInside.universalCoverBranch_mk_refl, coe_basePt]

/-- At `basepointLift`, `polylogBranch N` evaluates to `polylogTower N (1 / 2)`. -/
theorem polylogBranch_basepointLift (N : ℕ) :
    polylogBranch N (UniversalCover.basepointLift basePt) = polylogTower N (1 / 2) := by simp

/-- Prepending `γ0` (`periph0⁻¹ • basepointLift`) adds `2πi` to `Log` and fixes `Li₁, …, Li_N`. -/
theorem polylogBranch_periph0_inv_smul_basepointLift (N : ℕ) (i : Fin (N + 1)) :
    polylogBranch N (periph0⁻¹ • (UniversalCover.basepointLift basePt : UniversalCover basePt)) i =
      polylogTower N (1 / 2) i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  rw [polylogBranch_smul, polylogBranch_basepointLift, polylogMonodromy_periph0_inv]

/-- Prepending `γ1` shifts entries `i ≥ 1` by `-2πi · (-Real.log 2)^(i-1) / (i-1)!`. -/
theorem polylogBranch_periph1_inv_smul_basepointLift (N : ℕ) (i : Fin (N + 1)) :
    polylogBranch N (periph1⁻¹ • (UniversalCover.basepointLift basePt : UniversalCover basePt)) i =
      polylogTower N (1 / 2) i - if (i : ℕ) = 0 then 0 else
        2 * Real.pi * Complex.I * (-(Real.log 2 : ℂ)) ^ ((i : ℕ) - 1) /
          (((i : ℕ) - 1).factorial : ℂ) := by
  rw [polylogBranch_smul, polylogBranch_basepointLift, polylogMonodromy_periph1_inv,
    polylogTower_half_zero]

end TauCeti.Polylog
