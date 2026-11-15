/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FundamentalGroup
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Tower
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Peripheral monodromy of the polylogarithm tower

This file constructs the unipotent polynomial monodromy representation of
`FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt` (`π₁(ℂ \ {0, 1}, 1/2)`) on
the polylogarithm tower and proves equivariance of its universal-cover branch:

* `TauCeti.Polylog.polylogMonodromy`: the representation of `π₁(ℂ \ {0, 1}, 1/2)` on
  `Fin (N + 1) → ℂ` prescribed by `periph0⁻¹` and `periph1⁻¹`, with coordinate `MvPolynomial`
  witnesses (`exists_mvPolynomial_polylogMonodromy`), holomorphy (`analyticOnNhd_polylogMonodromy`),
  truncation compatibility (`polylogMonodromy_castLE`), ODE invariance
  (`IsPolylogTowerGerm.comp_polylogMonodromy`), and weight-two commutator `4π²`
  (`polylogMonodromy_commutator_two`).
* `TauCeti.Polylog.universalCoverBranch_periph0_inv_smul_of_analyticOnNhd_ball`,
  `TauCeti.Polylog.IsPolylogTowerGerm.universalCoverBranch_periph1_inv_smul`,
  `TauCeti.Polylog.IsPolylogTowerGerm.universalCoverBranch_smul_of_analyticOnNhd_ball`:
  all-height peripheral and full-`π₁` universal-cover monodromy.
* `TauCeti.Polylog.polylogOneBranch`, `TauCeti.Polylog.exists_polylogBranch_monodromy_zero`,
  `TauCeti.Polylog.exists_polylogBranch_monodromy_one`: unconditional height-`0` and height-`1`
  universal-cover branches and monodromy theorems.

## References

* J. Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993), §2.
* D. Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*
  (2007), Part I, §1–§2.
-/

public section

namespace TauCeti.Polylog

open Filter Metric Set Topology unitInterval

/-! ### The polynomial monodromy representation of `π₁(ℂ \ {0, 1}, 1/2)` -/

private def shiftLog (N : ℕ) (c : ℂ) (v : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun i => v i + if (i : ℕ) = 0 then c else 0

private noncomputable def shiftPolylog (N : ℕ) (c : ℂ) (v : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun i => v i + if (i : ℕ) = 0 then 0 else
    c * v 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)

private def shiftLogEquiv (N : ℕ) (c : ℂ) : Equiv.Perm (Fin (N + 1) → ℂ) where
  toFun := shiftLog N c
  invFun := shiftLog N (-c)
  left_inv v := by ext i; by_cases hi : (i : ℕ) = 0 <;> simp [shiftLog, hi]
  right_inv v := by ext i; by_cases hi : (i : ℕ) = 0 <;> simp [shiftLog, hi]

private noncomputable def shiftPolylogEquiv (N : ℕ) (c : ℂ) : Equiv.Perm (Fin (N + 1) → ℂ) where
  toFun := shiftPolylog N c
  invFun := shiftPolylog N (-c)
  left_inv v := by
    ext i; if hi : (i : ℕ) = 0 then simp [shiftPolylog, hi] else simp [shiftPolylog, hi]; ring
  right_inv v := by
    ext i; if hi : (i : ℕ) = 0 then simp [shiftPolylog, hi] else simp [shiftPolylog, hi]; ring

/-- **The peripheral monodromy representation of the polylogarithm tower.** On the free generators
`periph0` and `periph1` of `FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt`,
`periph0⁻¹` adds `2πi` to entry `0` and fixes entries `1, …, N`, while `periph1⁻¹` fixes entry `0`
and subtracts `2πi · w₀^(i-1) / (i-1)!` from entry `i ≥ 1`. -/
noncomputable def polylogMonodromy (N : ℕ) :
    FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt →*
      Equiv.Perm (Fin (N + 1) → ℂ) :=
  (FreeGroup.lift ![shiftLogEquiv N (-(2 * Real.pi * Complex.I)),
      shiftPolylogEquiv N (2 * Real.pi * Complex.I)]).comp
    ThricePuncturedSphere.fundamentalGroupMulEquivFreeGroup.toMonoidHom

/-- Action of `periph0⁻¹` (counterclockwise loop `γ0` around `0`) under `polylogMonodromy N`. -/
theorem polylogMonodromy_periph0_inv (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ w i =
      w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  simp [polylogMonodromy, shiftLogEquiv, shiftLog, Equiv.Perm.inv_def]

/-- Simp normal form (`map_inv` + `Equiv.Perm.coe_inv`) of `polylogMonodromy_periph0_inv`. -/
@[simp]
theorem polylogMonodromy_periph0_symm (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    (polylogMonodromy N ThricePuncturedSphere.periph0).symm w i =
      w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  rw [← Equiv.Perm.inv_def, ← map_inv, polylogMonodromy_periph0_inv]

/-- Action of `periph0` under `polylogMonodromy N`. -/
@[simp]
theorem polylogMonodromy_periph0 (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N ThricePuncturedSphere.periph0 w i =
      w i - if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hi : (i : ℕ) = 0 <;> simp [polylogMonodromy, shiftLogEquiv, shiftLog, hi, sub_eq_add_neg]

/-- Action of `periph1⁻¹` (counterclockwise loop `γ1` around `1`) under `polylogMonodromy N`. -/
theorem polylogMonodromy_periph1_inv (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N ThricePuncturedSphere.periph1⁻¹ w i =
      w i - if (i : ℕ) = 0 then 0 else
        2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  if hi : (i : ℕ) = 0 then
    simp [polylogMonodromy, shiftPolylogEquiv, shiftPolylog, Equiv.Perm.inv_def, hi]
  else
    simp [polylogMonodromy, shiftPolylogEquiv, shiftPolylog, Equiv.Perm.inv_def, hi]; ring

/-- Simp normal form (`map_inv` + `Equiv.Perm.coe_inv`) of `polylogMonodromy_periph1_inv`. -/
@[simp]
theorem polylogMonodromy_periph1_symm (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    (polylogMonodromy N ThricePuncturedSphere.periph1).symm w i =
      w i - if (i : ℕ) = 0 then 0 else
        2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  rw [← Equiv.Perm.inv_def, ← map_inv, polylogMonodromy_periph1_inv]

/-- Action of `periph1` under `polylogMonodromy N`. -/
@[simp]
theorem polylogMonodromy_periph1 (N : ℕ) (w : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    polylogMonodromy N ThricePuncturedSphere.periph1 w i =
      w i + if (i : ℕ) = 0 then 0 else
        2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ) := by
  simp [polylogMonodromy, shiftPolylogEquiv, shiftPolylog]

private theorem exists_mvPolynomial_shiftLog (N : ℕ) (c : ℂ) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, shiftLog N c w i = MvPolynomial.eval w P :=
  ⟨MvPolynomial.X i + MvPolynomial.C (if (i : ℕ) = 0 then c else 0), fun _ => by simp [shiftLog]⟩

private theorem exists_mvPolynomial_shiftPolylog (N : ℕ) (c : ℂ) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, shiftPolylog N c w i = MvPolynomial.eval w P :=
  ⟨MvPolynomial.X i + if (i : ℕ) = 0 then 0 else
      MvPolynomial.C (c / (((i : ℕ) - 1).factorial : ℂ)) * MvPolynomial.X 0 ^ ((i : ℕ) - 1),
    fun _ => by by_cases hi : (i : ℕ) = 0 <;> simp [shiftPolylog, hi, div_mul_eq_mul_div]⟩

/-- **Polynomiality of `polylogMonodromy`.** Every `g ∈ π₁(ℂ \ {0, 1}, 1/2)` acts on
`Fin (N + 1) → ℂ` by `MvPolynomial (Fin (N + 1)) ℂ` in each coordinate. -/
theorem exists_mvPolynomial_polylogMonodromy (N : ℕ)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt) (i : Fin (N + 1)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ,
      ∀ w, polylogMonodromy N g w i = MvPolynomial.eval w P := by
  let HasPoly (Φ : (Fin (N + 1) → ℂ) → Fin (N + 1) → ℂ) : Prop :=
    ∀ j, ∃ P : MvPolynomial (Fin (N + 1)) ℂ, ∀ w, Φ w j = MvPolynomial.eval w P
  have hcomp : ∀ {Φ Ψ}, HasPoly Φ → HasPoly Ψ → HasPoly (Φ ∘ Ψ) := fun {Φ Ψ} hΦ hΨ j => by
    choose Q hQ using hΨ
    obtain ⟨P, hP⟩ := hΦ j
    refine ⟨MvPolynomial.bind₁ Q P, fun w => ?_⟩
    have hQw : (fun k => MvPolynomial.eval w (Q k)) = Ψ w := funext fun k => (hQ k w).symm
    simp only [MvPolynomial.eval] at hQw hP ⊢
    rw [Function.comp_apply, hP, MvPolynomial.eval₂Hom_bind₁, hQw]
  suffices hboth : HasPoly (polylogMonodromy N g) ∧ HasPoly (polylogMonodromy N g⁻¹) from hboth.1 i
  have hmem : g ∈ Subgroup.closure {ThricePuncturedSphere.periph0, ThricePuncturedSphere.periph1} :=
    ThricePuncturedSphere.closure_periph0_periph1 ▸ Subgroup.mem_top g
  refine Subgroup.closure_induction (fun x hx => ?_)
    ⟨fun j => ⟨MvPolynomial.X j, by simp⟩, fun j => ⟨MvPolynomial.X j, by simp⟩⟩
    (fun x y _ _ ihx ihy =>
      ⟨by simpa [MonoidHom.map_mul, Equiv.Perm.coe_mul] using hcomp ihx.1 ihy.1,
        by simpa [mul_inv_rev, MonoidHom.map_mul, Equiv.Perm.coe_mul] using hcomp ihy.2 ihx.2⟩)
    (fun _ _ ih => ⟨ih.2, by simpa using ih.1⟩) hmem
  rcases hx with rfl | rfl
  · exact ⟨by simpa [polylogMonodromy, shiftLogEquiv, HasPoly] using
        exists_mvPolynomial_shiftLog N (-(2 * Real.pi * Complex.I)),
      by simpa [polylogMonodromy, shiftLogEquiv, Equiv.Perm.inv_def, HasPoly] using
        exists_mvPolynomial_shiftLog N (2 * Real.pi * Complex.I)⟩
  · exact ⟨by simpa [polylogMonodromy, shiftPolylogEquiv, HasPoly] using
        exists_mvPolynomial_shiftPolylog N (2 * Real.pi * Complex.I),
      by simpa [polylogMonodromy, shiftPolylogEquiv, Equiv.Perm.inv_def, HasPoly] using
        exists_mvPolynomial_shiftPolylog N (-(2 * Real.pi * Complex.I))⟩

/-- Every monodromy operator `polylogMonodromy N g` is complex analytic on `Set.univ`. -/
theorem analyticOnNhd_polylogMonodromy (N : ℕ)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt) :
    AnalyticOnNhd ℂ (polylogMonodromy N g) univ := fun w _ =>
  AnalyticAt.pi fun i => by
    obtain ⟨P, hP⟩ := exists_mvPolynomial_polylogMonodromy N g i
    simpa [← funext hP] using AnalyticOnNhd.eval_mvPolynomial P w (mem_univ w)

/-- `polylogMonodromy` commutes with truncating the tower from height `N` to height `M ≤ N`. -/
theorem polylogMonodromy_castLE {M N : ℕ} (hMN : M ≤ N)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt)
    (w : Fin (N + 1) → ℂ) (i : Fin (M + 1)) :
    polylogMonodromy N g w (Fin.castLE (Nat.add_le_add_right hMN 1) i) =
      polylogMonodromy M g (fun j => w (Fin.castLE (Nat.add_le_add_right hMN 1) j)) i := by
  let π : (Fin (N + 1) → ℂ) → Fin (M + 1) → ℂ :=
    fun v j => v (Fin.castLE (Nat.add_le_add_right hMN 1) j)
  suffices hboth : (π ∘ polylogMonodromy N g = polylogMonodromy M g ∘ π) ∧
      (π ∘ polylogMonodromy N g⁻¹ = polylogMonodromy M g⁻¹ ∘ π) from
    congrFun (congrFun hboth.1 w) i
  have hmem : g ∈ Subgroup.closure {ThricePuncturedSphere.periph0, ThricePuncturedSphere.periph1} :=
    ThricePuncturedSphere.closure_periph0_periph1 ▸ Subgroup.mem_top g
  refine Subgroup.closure_induction (fun x hx => ?_) ⟨by ext; simp [π], by ext; simp [π]⟩
    (fun x y _ _ ihx ihy => ⟨?_, ?_⟩) (fun _ _ ih => ⟨ih.2, by simpa using ih.1⟩) hmem
  · rcases hx with rfl | rfl <;> constructor <;> ext v j <;> simp [π]
  · simp only [MonoidHom.map_mul, Equiv.Perm.coe_mul]
    rw [← Function.comp_assoc, ihx.1, Function.comp_assoc, ihy.1, ← Function.comp_assoc]
  · simp only [mul_inv_rev, MonoidHom.map_mul, Equiv.Perm.coe_mul]
    rw [← Function.comp_assoc, ihy.2, Function.comp_assoc, ihx.2, ← Function.comp_assoc]

/-- **Noncommutativity of the peripheral monodromy at weight two (`Li₂`).** -/
theorem polylogMonodromy_commutator_two {N : ℕ} (hN : 2 ≤ N) (w : Fin (N + 1) → ℂ) :
    polylogMonodromy N ThricePuncturedSphere.periph1⁻¹
        (polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ w) ⟨2, Nat.succ_lt_succ hN⟩ -
      polylogMonodromy N ThricePuncturedSphere.periph0⁻¹
        (polylogMonodromy N ThricePuncturedSphere.periph1⁻¹ w) ⟨2, Nat.succ_lt_succ hN⟩ =
      4 * (Real.pi : ℂ) ^ 2 := by
  simp only [polylogMonodromy_periph1_inv, polylogMonodromy_periph0_inv, Fin.val_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero]
  norm_num; ring_nf; simp [Complex.I_sq]

namespace IsPolylogTowerGerm

private theorem comp_shiftLog {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w) (k : ℤ) :
    IsPolylogTowerGerm N (shiftLog N ((k : ℂ) * (2 * Real.pi * Complex.I)) ∘ F) w where
  analyticAt := AnalyticAt.pi fun i =>
    (analyticAt_pi_iff.1 hF.analyticAt i).add analyticAt_const
  eventually_exp_zero := hF.eventually_exp_zero.mono fun _ hexp => by
    simp [shiftLog, Complex.exp_add, hexp, Complex.exp_int_mul_two_pi_mul_I]
  eventually_deriv_succ i := hF.eventually_deriv_succ i |>.mono fun z hode => by
    have hsucc : (fun u => (shiftLog N ((k : ℂ) * (2 * Real.pi * Complex.I)) ∘ F) u i.succ) =
        fun u => F u i.succ := by ext u; simp [shiftLog]
    rw [hsucc]
    by_cases hi : (i : ℕ) = 0 <;> simpa [hi, shiftLog] using hode

private theorem comp_shiftPolylog {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w) (c : ℂ) :
    IsPolylogTowerGerm N (shiftPolylog N c ∘ F) w where
  analyticAt := AnalyticAt.pi fun i => by
    obtain ⟨P, hP⟩ := exists_mvPolynomial_shiftPolylog N c i
    exact ((AnalyticOnNhd.eval_mvPolynomial P (F w) (mem_univ _)).comp hF.analyticAt).congr
      (Eventually.of_forall fun z => (hP (F z)).symm)
  eventually_exp_zero := hF.eventually_exp_zero.mono fun _ hexp => by
    simpa [shiftPolylog] using hexp
  eventually_deriv_succ i := by
    have han0 := analyticAt_pi_iff.1 hF.analyticAt 0
    have hans := analyticAt_pi_iff.1 hF.analyticAt i.succ
    filter_upwards [hF.eventually_deriv_succ i, hF.eventually_deriv_zero,
      han0.eventually_analyticAt, hans.eventually_analyticAt] with z hode hd0 hz0 hzs
    rcases i with ⟨_ | m, hm⟩
    · simp only [Fin.succ_mk, Fin.castSucc_mk] at hode ⊢
      have hfn : (fun u => (shiftPolylog N c ∘ F) u ⟨1, Nat.succ_lt_succ hm⟩) =
          fun u => F u ⟨1, Nat.succ_lt_succ hm⟩ + c := by ext u; simp [shiftPolylog]
      rwa [hfn, deriv_add_const]
    · simp only [Fin.succ_mk, Fin.castSucc_mk, Nat.succ_ne_zero, ↓reduceIte] at hzs hode ⊢
      have hfn : (fun u => (shiftPolylog N c ∘ F) u ⟨m + 2, Nat.succ_lt_succ hm⟩) =
          fun u => F u ⟨m + 2, Nat.succ_lt_succ hm⟩ +
            c / ((m + 1).factorial : ℂ) * (F u 0) ^ (m + 1) := by
        ext u; simp [shiftPolylog, div_mul_eq_mul_div]
      have hhd_term : HasDerivAt (fun u => c / ((m + 1).factorial : ℂ) * (F u 0) ^ (m + 1))
          (c / ((m + 1).factorial : ℂ) *
            (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z)) z :=
        (hz0.differentiableAt.hasDerivAt.pow (m + 1)).const_mul _
      have hd_sum : deriv (fun u => (shiftPolylog N c ∘ F) u ⟨m + 2, Nat.succ_lt_succ hm⟩) z =
          deriv (fun u => F u ⟨m + 2, Nat.succ_lt_succ hm⟩) z +
            c / ((m + 1).factorial : ℂ) *
              (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z) := by
        rw [hfn]; exact (hzs.differentiableAt.hasDerivAt.add hhd_term).deriv
      have hfac_ne : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      rw [hd_sum, mul_add, hode]
      simp only [Function.comp_apply, shiftPolylog, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel]
      congr 1
      calc z * (c / ((m + 1).factorial : ℂ) *
              (((m + 1 : ℕ) : ℂ) * (F z 0) ^ m * deriv (fun u => F u 0) z))
          = (c * ((m + 1 : ℕ) : ℂ) * (F z 0) ^ m / (((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ))) *
              (z * deriv (fun u => F u 0) z) := by rw [Nat.factorial_succ, Nat.cast_mul]; ring
        _ = c * (F z 0) ^ m / (m.factorial : ℂ) := by rw [hd0, mul_one]; field_simp [hfac_ne]

/-- **Monodromy invariance of the polylogarithm tower differential system.** -/
theorem comp_polylogMonodromy {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ} {w : ℂ}
    (hF : IsPolylogTowerGerm N F w)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt) :
    IsPolylogTowerGerm N (polylogMonodromy N g ∘ F) w := by
  suffices hboth : (∀ G : ℂ → Fin (N + 1) → ℂ, IsPolylogTowerGerm N G w →
        IsPolylogTowerGerm N (polylogMonodromy N g ∘ G) w) ∧
      (∀ G : ℂ → Fin (N + 1) → ℂ, IsPolylogTowerGerm N G w →
        IsPolylogTowerGerm N (polylogMonodromy N g⁻¹ ∘ G) w) from hboth.1 F hF
  have hmem : g ∈ Subgroup.closure {ThricePuncturedSphere.periph0, ThricePuncturedSphere.periph1} :=
    ThricePuncturedSphere.closure_periph0_periph1 ▸ Subgroup.mem_top g
  refine Subgroup.closure_induction (fun x hx => ?_)
    ⟨fun _ hG => by simpa using hG, fun _ hG => by simpa using hG⟩
    (fun x y _ _ ihx ihy => ⟨fun G hG => by
        rw [MonoidHom.map_mul, Equiv.Perm.coe_mul, Function.comp_assoc]; exact ihx.1 _ (ihy.1 G hG),
      fun G hG => by
        rw [mul_inv_rev, MonoidHom.map_mul, Equiv.Perm.coe_mul, Function.comp_assoc]
        exact ihy.2 _ (ihx.2 G hG)⟩)
    (fun _ _ ih => ⟨ih.2, by simpa using ih.1⟩) hmem
  rcases hx with rfl | rfl
  · exact ⟨fun G hG => by simpa [polylogMonodromy, shiftLogEquiv] using hG.comp_shiftLog (-1),
      fun G hG => by
        simpa [polylogMonodromy, shiftLogEquiv, Equiv.Perm.inv_def] using hG.comp_shiftLog 1⟩
  · exact ⟨fun G hG => by
        simpa [polylogMonodromy, shiftPolylogEquiv] using
          hG.comp_shiftPolylog (2 * Real.pi * Complex.I),
      fun G hG => by
        simpa [polylogMonodromy, shiftPolylogEquiv, Equiv.Perm.inv_def] using
          hG.comp_shiftPolylog (-(2 * Real.pi * Complex.I))⟩

end IsPolylogTowerGerm

/-! ### Explicit winding continuations around `0` and `1` and universal-cover monodromy -/

private theorem half_mem_slitPlane : (1 / 2 : ℂ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))

private theorem sub_half_mem_slitPlane : 1 - (1 / 2 : ℂ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))

private theorem eventuallyEq_log_half {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (1 / 2)) (hF0 : F (1 / 2) 0 = Complex.log (1 / 2)) :
    (fun z => F z 0) =ᶠ[𝓝 (1 / 2 : ℂ)] Complex.log := by
  have heq := ((hF.castLE (Nat.zero_le N)).eventuallyEq_iff_eq
    (isPolylogTowerGerm_polylogTower_zero half_mem_slitPlane)).mpr
      (by ext i; fin_cases i; simpa [polylogTower_zero] using hF0)
  exact heq.mono fun z hz => by simpa [polylogTower_zero] using congrFun hz 0

private noncomputable def logCont0 (t : I) (z : ℂ) : ℂ :=
  Complex.log (z * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ)))) +
    2 * Real.pi * Complex.I * (t : ℂ)

private theorem γ0_mul_exp_neg (t : I) :
    (ThricePuncturedSphere.γ0 t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) =
      1 / 2 := by
  rw [ThricePuncturedSphere.coe_γ0_eq_exp, mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, mul_one]

private theorem logCont0_zero : logCont0 0 = Complex.log := by ext z; simp [logCont0]

private theorem logCont0_one (z : ℂ) : logCont0 1 z = Complex.log z + 2 * Real.pi * Complex.I := by
  have h1 : (((1 : I) : ℝ) : ℂ) = 1 := by simp
  rw [logCont0, h1, mul_one, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

private theorem exp_logCont0 (t : I) {z : ℂ} (hz : z ≠ 0) : Complex.exp (logCont0 t z) = z := by
  have hrot : z * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) ≠ 0 :=
    mul_ne_zero hz (Complex.exp_ne_zero _)
  rw [logCont0, Complex.exp_add, Complex.exp_log hrot, mul_assoc, ← Complex.exp_add,
    neg_add_cancel, Complex.exp_zero, mul_one]

private theorem eq_of_exp_eq_of_norm_sub_lt_one' {a b : ℂ}
    (hexp : Complex.exp a = Complex.exp b) (hnorm : ‖a - b‖ < 1) : a = b := by
  have hexp_sub : Complex.exp (a - b) = 1 := by
    rw [Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero b)]
  have him : |(a - b).im| < Real.pi := by linarith [Complex.abs_im_le_norm (a - b), Real.two_le_pi]
  have hlog := Complex.log_exp (x := a - b) (neg_lt_of_abs_lt him) (le_of_lt (lt_of_abs_lt him))
  rw [hexp_sub, Complex.log_one] at hlog
  exact sub_eq_zero.mp hlog.symm

private theorem isAnalyticContinuationAlong_logCont0 :
    IsAnalyticContinuationAlong logCont0 (fun t => (ThricePuncturedSphere.γ0 t : ℂ)) univ where
  continuousOn := (continuous_subtype_val.comp ThricePuncturedSphere.γ0.continuous).continuousOn
  analyticAt t _ := by
    have hval : (ThricePuncturedSphere.γ0 t : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) ∈ Complex.slitPlane :=
      (γ0_mul_exp_neg t).symm ▸ half_mem_slitPlane
    exact ((analyticAt_id.mul analyticAt_const).clog hval).add analyticAt_const
  locallyEq t _ := by
    let rot : I × ℂ → ℂ := fun p =>
      p.2 * Complex.exp (-(2 * Real.pi * Complex.I * ((p.1 : ℝ) : ℂ)))
    have hrot_cont : Continuous rot := by fun_prop
    have hrot_val : rot (t, (ThricePuncturedSphere.γ0 t : ℂ)) ∈ Complex.slitPlane := by
      dsimp only [rot]; exact (γ0_mul_exp_neg t).symm ▸ half_mem_slitPlane
    have hcont1 : ContinuousAt (fun p : I × ℂ => logCont0 p.1 p.2)
        (t, (ThricePuncturedSphere.γ0 t : ℂ)) :=
      (hrot_cont.continuousAt.clog hrot_val).add (by fun_prop)
    have hcont2 : ContinuousAt (fun p : I × ℂ => logCont0 t p.2)
        (t, (ThricePuncturedSphere.γ0 t : ℂ)) :=
      ((continuous_snd.mul continuous_const).continuousAt.clog hrot_val).add continuousAt_const
    have hlt : ∀ᶠ p : I × ℂ in 𝓝 (t, (ThricePuncturedSphere.γ0 t : ℂ)),
        ‖logCont0 p.1 p.2 - logCont0 t p.2‖ < 1 := by
      simpa using Metric.tendsto_nhds.mp (hcont1.sub hcont2) 1 zero_lt_one
    have hmem : {p : I × ℂ | ‖logCont0 p.1 p.2 - logCont0 t p.2‖ < 1 ∧ p.2 ≠ 0} ∈
        𝓝 t ×ˢ 𝓝 (ThricePuncturedSphere.γ0 t : ℂ) := by
      rw [← nhds_prod_eq]
      exact hlt.and (continuous_snd.continuousAt.eventually
        (eventually_ne_nhds (ThricePuncturedSphere.ne_zero _)))
    obtain ⟨V, hV, W', hW', hVW'⟩ := Filter.mem_prod_iff.mp hmem
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW'
    have hγcont : Continuous (fun u : I => (ThricePuncturedSphere.γ0 u : ℂ)) :=
      continuous_subtype_val.comp ThricePuncturedSphere.γ0.continuous
    filter_upwards [nhdsWithin_le_nhds (Filter.inter_mem hV
      (hγcont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hε))))]
      with u ⟨huV, huW⟩
    filter_upwards [isOpen_ball.mem_nhds huW] with z hzW
    obtain ⟨hnorm, hz0⟩ := hVW' (mk_mem_prod huV (hεW hzW))
    exact eq_of_exp_eq_of_norm_sub_lt_one'
      ((exp_logCont0 u hz0).trans (exp_logCont0 t hz0).symm) hnorm

private noncomputable def li1Cont1 (t : I) (z : ℂ) : ℂ := -logCont0 t (1 - z)

private theorem one_sub_γ1 (t : I) :
    1 - (ThricePuncturedSphere.γ1 t : ℂ) = (ThricePuncturedSphere.γ0 t : ℂ) := by
  rw [ThricePuncturedSphere.coe_γ1_eq_exp, ThricePuncturedSphere.coe_γ0_eq_exp]; ring

private theorem li1Cont1_zero : li1Cont1 0 = polylog 1 := by ext z; simp [li1Cont1, logCont0_zero]

private theorem li1Cont1_one (z : ℂ) : li1Cont1 1 z = polylog 1 z - 2 * Real.pi * Complex.I := by
  simp [li1Cont1, logCont0_one]; ring

private theorem isAnalyticContinuationAlong_li1Cont1 :
    IsAnalyticContinuationAlong li1Cont1 (fun t => (ThricePuncturedSphere.γ1 t : ℂ)) univ where
  continuousOn := (continuous_subtype_val.comp ThricePuncturedSphere.γ1.continuous).continuousOn
  analyticAt t _ := by
    have han := isAnalyticContinuationAlong_logCont0.analyticAt t (mem_univ t)
    have hsub : AnalyticAt ℂ (fun z : ℂ => 1 - z) (ThricePuncturedSphere.γ1 t : ℂ) :=
      analyticAt_const.sub analyticAt_id
    exact (((one_sub_γ1 t).symm ▸ han).comp hsub).neg
  locallyEq t _ := by
    filter_upwards [isAnalyticContinuationAlong_logCont0.locallyEq t (mem_univ t)] with u hu
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) (ThricePuncturedSphere.γ1 u : ℂ) :=
      continuousAt_const.sub continuousAt_id
    have hu' : logCont0 u =ᶠ[𝓝 (1 - (ThricePuncturedSphere.γ1 u : ℂ))] logCont0 t :=
      (one_sub_γ1 u).symm ▸ hu
    filter_upwards [hcont.eventually hu'] with z hz
    simp [li1Cont1, hz]

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
    AnalyticAt ℂ (fun z => A z + logSing1 N (polylog 1 z) z) (1 / 2) := by
  have hli1 : AnalyticAt ℂ (polylog 1) (1 / 2) := by
    rw [funext polylog_one]
    exact ((analyticAt_const.sub analyticAt_id).clog sub_half_mem_slitPlane).neg
  exact (hAan _ (by rw [mem_ball, dist_eq_norm]; norm_num)).add
    (analyticAt_logSing1 N hli1 half_mem_slitPlane)

private theorem eventually_deriv_last_logSing1 {K : ℕ} {g a : ℂ → ℂ}
    (haderiv : ∀ z ∈ ball (1 : ℂ) (3 / 4), HasDerivAt a
      (g z / z + dslope (fun u => (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) 1 z) z) :
    ∀ᶠ z in 𝓝 (1 / 2 : ℂ),
      z * deriv (fun u => a u +
        polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) z =
      g z + polylog 1 z * (Complex.log z) ^ K / (K.factorial : ℂ) := by
  let B : ℂ → ℂ := fun u => (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)
  have hB1 : B 1 = 0 := by simp [B]
  have hball : ball (1 : ℂ) (3 / 4) ∈ 𝓝 (1 / 2 : ℂ) :=
    isOpen_ball.mem_nhds (by rw [mem_ball, dist_eq_norm]; norm_num)
  have hslit1 : {z : ℂ | 1 - z ∈ Complex.slitPlane} ∈ 𝓝 (1 / 2 : ℂ) :=
    (Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)).mem_nhds
      sub_half_mem_slitPlane
  filter_upwards [hball, Complex.isOpen_slitPlane.mem_nhds half_mem_slitPlane, hslit1]
    with z hzb hz0 hz1
  have hz_ne : z ≠ 0 := Complex.slitPlane_ne_zero hz0
  have h1z_ne : 1 - z ≠ 0 := Complex.slitPlane_ne_zero hz1
  have hd_li1 : HasDerivAt (polylog 1) ((1 - z)⁻¹) z := by
    convert (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).clog hz1).neg using 1
    · ext u; exact polylog_one u
    · dsimp; rw [zero_sub, neg_div, neg_neg, one_div]
  have hd_B : HasDerivAt B ((Complex.log z) ^ K / (K.factorial : ℂ) / z) z := by
    convert ((Complex.hasDerivAt_log hz0).pow (K + 1)).div_const ((K + 1).factorial : ℂ) using 1
    have hne : ((K + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero K)
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, div_div]
    field_simp [hne, hz_ne]
  have hB_eq : B z = -(1 - z) * dslope B 1 z := by
    have hsub := sub_smul_dslope B 1 z
    rw [hB1, sub_zero, smul_eq_mul] at hsub; rw [← hsub]; ring
  have hfun : (fun u => a u + polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ)) =
      fun u => a u + polylog 1 u * B u := by ext u; dsimp [B]; ring
  have hd_tot : HasDerivAt (fun u => a u + polylog 1 u * B u)
      ((g z / z + dslope B 1 z) + ((1 - z)⁻¹ * B z +
        polylog 1 z * ((Complex.log z) ^ K / (K.factorial : ℂ) / z))) z :=
    (haderiv z hzb).add (hd_li1.mul hd_B)
  rw [hfun, hd_tot.deriv, hB_eq, neg_mul, mul_neg, inv_mul_cancel_left₀ h1z_ne]
  field_simp [hz_ne]; ring

private theorem exists_analyticOnNhd_ball_one_succ {K : ℕ}
    {A' : ℂ → Fin (K + 2) → ℂ} (hA'an : AnalyticOnNhd ℂ A' (ball 1 (3 / 4)))
    (hG' : IsPolylogTowerGerm (K + 1) (fun z => A' z + logSing1 (K + 1) (polylog 1 z) z) (1 / 2))
    (c : ℂ) :
    ∃ A : ℂ → Fin (K + 3) → ℂ,
      AnalyticOnNhd ℂ A (ball 1 (3 / 4)) ∧
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
  · have hidx : (Fin.last (K + 1)).succ = Fin.last (K + 2) := Fin.ext rfl
    have hlast : (fun u => (A u + logSing1 (K + 2) (polylog 1 u) u) (Fin.last (K + 1)).succ) =
        fun u => a u + polylog 1 u * (Complex.log u) ^ (K + 1) / ((K + 1).factorial : ℂ) := by
      ext u; rw [hidx, Pi.add_apply]; dsimp only [A, logSing1]; rw [Fin.lastCases_last]; simp
    filter_upwards [eventually_deriv_last_logSing1 haderiv] with z hz
    rw [hlast, hGcast z (Fin.last (K + 1))]; simpa [Fin.val_last, logSing1] using hz
  · have hidx : (Fin.castSucc j).succ = Fin.castSucc j.succ := Fin.ext rfl
    have hs : (fun u => (A u + logSing1 (K + 2) (polylog 1 u) u) (Fin.castSucc j).succ) =
        fun u => (A' u + logSing1 (K + 1) (polylog 1 u) u) j.succ :=
      funext fun u => (congrArg _ hidx).trans (hGcast u j.succ)
    filter_upwards [hG'.eventually_deriv_succ j] with z hz
    rw [hs, hGcast z j.castSucc]; simpa using hz

private theorem exists_analyticOnNhd_ball_one_add_logSing1 :
    ∀ (N : ℕ) (v : Fin (N + 1) → ℂ), v 0 = Complex.log (1 / 2) →
      ∃ A : ℂ → Fin (N + 1) → ℂ,
        AnalyticOnNhd ℂ A (ball 1 (3 / 4)) ∧
        (A (1 / 2) + logSing1 N (polylog 1 (1 / 2)) (1 / 2)) = v ∧
        IsPolylogTowerGerm N (fun z => A z + logSing1 N (polylog 1 z) z) (1 / 2)
  | 0, v, hv0 => by
    refine ⟨polylogTower 0, fun z hz => AnalyticAt.pi fun i => ?_,
      by ext i; fin_cases i; simp [logSing1, hv0],
      (isPolylogTowerGerm_polylogTower_zero half_mem_slitPlane).congr
        (Eventually.of_forall fun z => by ext i; fin_cases i; simp [logSing1])⟩
    fin_cases i
    simpa [polylogTower_zero] using
      analyticAt_id.clog (Complex.ball_one_subset_slitPlane (ball_subset_ball (by norm_num) hz))
  | 1, v, hv0 => by
    let c₁ : ℂ := v 1 - polylog 1 (1 / 2)
    let A : ℂ → Fin 2 → ℂ := fun z => Fin.cases (Complex.log z) (fun _ => c₁)
    refine ⟨A, fun z hz => AnalyticAt.pi <|
      Fin.cases (analyticAt_id.clog
        (Complex.ball_one_subset_slitPlane (ball_subset_ball (by norm_num) hz)))
        (fun _ => analyticAt_const), ?_, ?_⟩
    · ext i; refine Fin.cases (by simp [A, logSing1, hv0]) (fun j => ?_) i
      dsimp only [A, Pi.add_apply]; rw [Fin.cases_succ]; fin_cases j; simp [c₁, logSing1]
    · refine ((isPolylogTowerGerm_polylogTower_one half_mem_slitPlane
          sub_half_mem_slitPlane).comp_shiftPolylog c₁).congr
        (Eventually.of_forall fun z => ?_)
      ext i
      refine Fin.cases (by simp [A, shiftPolylog, logSing1, polylogTower_zero]) (fun j => ?_) i
      dsimp only [A, Pi.add_apply, Function.comp_apply]; rw [Fin.cases_succ]
      fin_cases j; simp [shiftPolylog, logSing1, polylogTower_apply]; ring
  | K + 2, v, hv0 => by
    obtain ⟨A', hA'an, hA'val, hG'⟩ :=
      exists_analyticOnNhd_ball_one_add_logSing1 (K + 1) (fun j => v j.castSucc) hv0
    obtain ⟨A, hAan, hAval, hG⟩ :=
      exists_analyticOnNhd_ball_one_succ hA'an hG' (v (Fin.last (K + 2)))
    refine ⟨A, hAan, hAval.trans ?_, hG⟩
    ext i
    exact Fin.lastCases Fin.lastCases_last
      (fun j => (Fin.lastCases_castSucc j).trans (congrFun hA'val j)) i

/-- **`γ0`-monodromy for any tower germ analytic on the open unit disc in positive weights.** -/
theorem universalCoverBranch_periph0_inv_smul_of_analyticOnNhd_ball {N : ℕ}
    {F : ℂ → Fin (N + 1) → ℂ}
    (H : ContinuesInside F {z : ℂ | z ≠ 0 ∧ z ≠ 1} (ThricePuncturedSphere.basePt : ℂ))
    (hF0 : (fun z => F z 0) =ᶠ[𝓝 (1 / 2 : ℂ)] Complex.log)
    {G : ℂ → Fin N → ℂ} (hGan : AnalyticOnNhd ℂ G (ball 0 1))
    (hFG : ∀ i : Fin N, (fun z => F z i.succ) =ᶠ[𝓝 (1 / 2 : ℂ)] fun z => G z i)
    (p : UniversalCover ThricePuncturedSphere.basePt) :
    H.universalCoverBranch (ThricePuncturedSphere.periph0⁻¹ • p) =
      polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ (H.universalCoverBranch p) := by
  let f : I → ℂ → Fin (N + 1) → ℂ := fun t z => Fin.cases (logCont0 t z) (fun i => G z i)
  have hγ0_ball : ∀ t : I, (ThricePuncturedSphere.γ0 t : ℂ) ∈ ball 0 1 := fun t => by
    rw [mem_ball, dist_zero_right, ThricePuncturedSphere.norm_coe_γ0]; norm_num
  have hf : IsAnalyticContinuationAlong f (fun t => (ThricePuncturedSphere.γ0 t : ℂ)) univ := by
    refine ⟨(continuous_subtype_val.comp ThricePuncturedSphere.γ0.continuous).continuousOn,
      fun t _ => AnalyticAt.pi <| Fin.cases
        (isAnalyticContinuationAlong_logCont0.analyticAt t (mem_univ t))
        (fun i => analyticAt_pi_iff.1 (hGan _ (hγ0_ball t)) i),
      fun t _ => ?_⟩
    filter_upwards [isAnalyticContinuationAlong_logCont0.locallyEq t (mem_univ t)] with u hu
    exact hu.mono fun _ hz => funext (Fin.cases hz fun _ => rfl)
  have hf0 : f 0 =ᶠ[𝓝 (ThricePuncturedSphere.basePt : ℂ)] F := by
    rw [ThricePuncturedSphere.coe_basePt]
    exact (eventually_all.mpr <| Fin.cases
      (hF0.symm.mono fun z hz => by simp [f, logCont0_zero, hz])
      (fun i => (hFG i).symm.mono fun z hz => by simp [f, hz])).mono fun _ => funext
  have hf1 : f 1 =ᶠ[𝓝 (ThricePuncturedSphere.basePt : ℂ)]
      polylogMonodromy N ThricePuncturedSphere.periph0⁻¹ ∘ F := by
    rw [ThricePuncturedSphere.coe_basePt]
    exact (eventually_all.mpr <| Fin.cases
      (hF0.mono fun z hz => by simp [f, logCont0_one, hz])
      (fun i => (hFG i).mono fun z hz => by simp [f, ← hz])).mono fun _ => funext
  have hloop := H.universalCoverBranch_inv_smul_of_loop hf hf0
    (analyticOnNhd_polylogMonodromy N ThricePuncturedSphere.periph0⁻¹) hf1 p
  have hp0 : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ThricePuncturedSphere.γ0) =
      ThricePuncturedSphere.periph0 := ThricePuncturedSphere.periph0_def.symm
  rwa [hp0] at hloop

namespace IsPolylogTowerGerm

/-- **`γ1`-monodromy in arbitrary height `N` from the tower differential system alone.** -/
theorem universalCoverBranch_periph1_inv_smul {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (ThricePuncturedSphere.basePt : ℂ))
    (hF0 : F (1 / 2) 0 = Complex.log (1 / 2))
    (p : UniversalCover ThricePuncturedSphere.basePt) :
    hF.continuesInside.universalCoverBranch (ThricePuncturedSphere.periph1⁻¹ • p) =
      polylogMonodromy N ThricePuncturedSphere.periph1⁻¹
        (hF.continuesInside.universalCoverBranch p) := by
  have hF_half : IsPolylogTowerGerm N F (1 / 2) := ThricePuncturedSphere.coe_basePt ▸ hF
  obtain ⟨A, hAan, hAval, hG⟩ := exists_analyticOnNhd_ball_one_add_logSing1 N (F (1 / 2)) hF0
  have hGF : (fun z => A z + logSing1 N (polylog 1 z) z) =ᶠ[𝓝 (1 / 2 : ℂ)] F :=
    (hG.eventuallyEq_iff_eq hF_half).mpr hAval
  have hF0_eq := eventuallyEq_log_half hF_half hF0
  let f : I → ℂ → Fin (N + 1) → ℂ := fun t z => A z + logSing1 N (li1Cont1 t z) z
  have hγ1_ball : ∀ t : I, (ThricePuncturedSphere.γ1 t : ℂ) ∈ ball (1 : ℂ) (3 / 4) := fun t => by
    rw [mem_ball, dist_eq_norm, ThricePuncturedSphere.norm_coe_γ1_sub_one]; norm_num
  have hγ1_slit : ∀ t : I, (ThricePuncturedSphere.γ1 t : ℂ) ∈ Complex.slitPlane := fun t =>
    Complex.mem_slitPlane_iff.mpr
      (Or.inl (ThricePuncturedSphere.mem_rightOpen.1 (ThricePuncturedSphere.γ1_mem_rightOpen t)))
  have hf : IsAnalyticContinuationAlong f (fun t => (ThricePuncturedSphere.γ1 t : ℂ)) univ := by
    refine ⟨(continuous_subtype_val.comp ThricePuncturedSphere.γ1.continuous).continuousOn,
      fun t _ => (hAan _ (hγ1_ball t)).add
        (analyticAt_logSing1 N (isAnalyticContinuationAlong_li1Cont1.analyticAt t (mem_univ t))
          (hγ1_slit t)),
      fun t _ => ?_⟩
    filter_upwards [isAnalyticContinuationAlong_li1Cont1.locallyEq t (mem_univ t)] with u hu
    exact hu.mono fun z hz => by ext i; simp [f, logSing1, hz]
  have hf0 : f 0 =ᶠ[𝓝 (ThricePuncturedSphere.basePt : ℂ)] F := by
    rw [ThricePuncturedSphere.coe_basePt]; simpa [f, li1Cont1_zero] using hGF
  have hf1 : f 1 =ᶠ[𝓝 (ThricePuncturedSphere.basePt : ℂ)]
      polylogMonodromy N ThricePuncturedSphere.periph1⁻¹ ∘ F := by
    rw [ThricePuncturedSphere.coe_basePt]
    filter_upwards [hGF, hF0_eq] with z hz hz0
    ext i
    by_cases hi : (i : ℕ) = 0
    · simp [f, logSing1, hi, ← hz]
    · rw [Function.comp_apply, polylogMonodromy_periph1_inv, hz0, ← hz]
      simp only [f, Pi.add_apply, logSing1, hi, ↓reduceIte, li1Cont1_one]; ring
  have hloop := hF.continuesInside.universalCoverBranch_inv_smul_of_loop hf hf0
    (analyticOnNhd_polylogMonodromy N ThricePuncturedSphere.periph1⁻¹) hf1 p
  have hp1 : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ThricePuncturedSphere.γ1) =
      ThricePuncturedSphere.periph1 := ThricePuncturedSphere.periph1_def.symm
  rwa [hp1] at hloop

/-- **Full `π₁(ℂ \ {0, 1}, 1/2)`-equivariance in arbitrary height `N`.** -/
theorem universalCoverBranch_smul_of_analyticOnNhd_ball {N : ℕ} {F : ℂ → Fin (N + 1) → ℂ}
    (hF : IsPolylogTowerGerm N F (ThricePuncturedSphere.basePt : ℂ))
    (hF0 : F (1 / 2) 0 = Complex.log (1 / 2))
    {G : ℂ → Fin N → ℂ} (hGan : AnalyticOnNhd ℂ G (ball 0 1))
    (hFG : ∀ i : Fin N, (fun z => F z i.succ) =ᶠ[𝓝 (1 / 2 : ℂ)] fun z => G z i)
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt)
    (p : UniversalCover ThricePuncturedSphere.basePt) :
    hF.continuesInside.universalCoverBranch (g • p) =
      polylogMonodromy N g (hF.continuesInside.universalCoverBranch p) := by
  have hF0_eq := eventuallyEq_log_half (ThricePuncturedSphere.coe_basePt ▸ hF) hF0
  refine hF.continuesInside.universalCoverBranch_smul_of_closure
    ThricePuncturedSphere.closure_periph0_periph1 (fun x hx q => ?_) g p
  rcases hx with rfl | rfl
  · exact universalCoverBranch_periph0_inv_smul_of_analyticOnNhd_ball
      hF.continuesInside hF0_eq hGan hFG q
  · exact hF.universalCoverBranch_periph1_inv_smul hF0 q

end IsPolylogTowerGerm

/-- `polylogTower 0` continues inside `{z : ℂ | z ≠ 0 ∧ z ≠ 1}` from `basePt = 1 / 2`. -/
theorem continuesInside_polylogTower_zero :
    ContinuesInside (polylogTower 0) {z : ℂ | z ≠ 0 ∧ z ≠ 1}
      (ThricePuncturedSphere.basePt : ℂ) :=
  (isPolylogTowerGerm_polylogTower_zero
    (ThricePuncturedSphere.coe_basePt.symm ▸ half_mem_slitPlane)).continuesInside

/-- `polylogTower 1` continues inside `{z : ℂ | z ≠ 0 ∧ z ≠ 1}` from `basePt = 1 / 2`. -/
theorem continuesInside_polylogTower_one :
    ContinuesInside (polylogTower 1) {z : ℂ | z ≠ 0 ∧ z ≠ 1}
      (ThricePuncturedSphere.basePt : ℂ) :=
  (isPolylogTowerGerm_polylogTower_one (ThricePuncturedSphere.coe_basePt.symm ▸ half_mem_slitPlane)
    (ThricePuncturedSphere.coe_basePt.symm ▸ sub_half_mem_slitPlane)).continuesInside

/-- The universal-cover branch of `polylogTower 1 = (Log, Li₁)` over the thrice-punctured sphere
based at `1 / 2`. -/
noncomputable def polylogOneBranch :
    UniversalCover ThricePuncturedSphere.basePt → Fin 2 → ℂ :=
  continuesInside_polylogTower_one.universalCoverBranch

/-- Equivariance of `polylogOneBranch` under the full fundamental group `π₁(ℂ \ {0, 1}, 1/2)`. -/
theorem polylogOneBranch_smul
    (g : FundamentalGroup ThricePuncturedSphere ThricePuncturedSphere.basePt)
    (p : UniversalCover ThricePuncturedSphere.basePt) :
    polylogOneBranch (g • p) = polylogMonodromy 1 g (polylogOneBranch p) := by
  have h1 := isPolylogTowerGerm_polylogTower_one
    (ThricePuncturedSphere.coe_basePt.symm ▸ half_mem_slitPlane)
    (ThricePuncturedSphere.coe_basePt.symm ▸ sub_half_mem_slitPlane)
  refine h1.universalCoverBranch_smul_of_analyticOnNhd_ball (polylogTower_zero 1 (1 / 2))
    (G := fun z _ => polylog 1 z) (fun z hz => AnalyticAt.pi fun _ => ?_)
    (fun i => by fin_cases i; exact Eventually.of_forall fun z => polylogTower_succ 1 z 0) g p
  have h1z : 1 - z ∈ Complex.slitPlane :=
    sub_eq_add_neg (1 : ℂ) z ▸ Complex.mem_slitPlane_of_norm_lt_one (by simpa using hz)
  rw [funext polylog_one]
  exact ((analyticAt_const.sub analyticAt_id).clog h1z).neg

/-- **Coherent universal-cover branch and polynomial monodromy at height `0` (`Log`).** -/
theorem exists_polylogBranch_monodromy_zero :
    ∃ (B : UniversalCover ThricePuncturedSphere.basePt → Fin 1 → ℂ)
      (ρ : FundamentalGroup ThricePuncturedSphere
        ThricePuncturedSphere.basePt →* Equiv.Perm (Fin 1 → ℂ)),
      (∀ (z : ThricePuncturedSphere) (γ : Path ThricePuncturedSphere.basePt z),
        ∃ f : I → ℂ → Fin 1 → ℂ,
          IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ ∧
          (f 0 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogTower 0) ∧
          B ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ)) ∧
      (∀ g i, ∃ P : MvPolynomial (Fin 1) ℂ, ∀ w, ρ g w i = MvPolynomial.eval w P) ∧
      (∀ w i, ρ ThricePuncturedSphere.periph0⁻¹ w i =
        w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0) ∧
      (∀ w i, ρ ThricePuncturedSphere.periph1⁻¹ w i =
        w i - if (i : ℕ) = 0 then 0 else
          2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)) ∧
      (∀ g p, B (g • p) = ρ g (B p)) := by
  refine ⟨fun p i => polylogOneBranch p (Fin.castLE (by decide) i), polylogMonodromy 0,
    fun z γ => ?_, exists_mvPolynomial_polylogMonodromy 0,
    polylogMonodromy_periph0_inv 0, polylogMonodromy_periph1_inv 0, fun g p => ?_⟩
  · obtain ⟨f, hf, hf0, hval⟩ :=
      continuesInside_polylogTower_one.exists_isAnalyticContinuationAlong_universalCoverBranch γ
    let π : (Fin 2 → ℂ) → (Fin 1 → ℂ) := fun v i => v (Fin.castLE (by decide) i)
    refine ⟨fun t z => π (f t z), hf.comp_analyticAt fun _ _ =>
      AnalyticAt.pi fun i => analyticAt_pi_iff.1 analyticAt_id _, ?_, ?_⟩
    · rw [ThricePuncturedSphere.coe_basePt] at hf0
      exact (hf0.fun_comp π).trans
        (Eventually.of_forall fun u => funext (polylogTower_castLE (Nat.zero_le 1) u))
    · simp [polylogOneBranch, π, hval]
  · ext i; fin_cases i
    simpa using (congrFun (polylogOneBranch_smul g p) 0).trans
      (polylogMonodromy_castLE (Nat.zero_le 1) g (polylogOneBranch p) 0)

/-- **Coherent universal-cover branch and polynomial monodromy at height `1` (`(Log, Li₁)`).** -/
theorem exists_polylogBranch_monodromy_one :
    ∃ (B : UniversalCover ThricePuncturedSphere.basePt → Fin 2 → ℂ)
      (ρ : FundamentalGroup ThricePuncturedSphere
        ThricePuncturedSphere.basePt →* Equiv.Perm (Fin 2 → ℂ)),
      (∀ (z : ThricePuncturedSphere) (γ : Path ThricePuncturedSphere.basePt z),
        ∃ f : I → ℂ → Fin 2 → ℂ,
          IsAnalyticContinuationAlong f (fun t => (γ t : ℂ)) univ ∧
          (f 0 =ᶠ[𝓝 (1 / 2 : ℂ)] polylogTower 1) ∧
          B ⟨z, Path.Homotopic.Quotient.mk γ⟩ = f 1 (z : ℂ)) ∧
      (∀ g i, ∃ P : MvPolynomial (Fin 2) ℂ, ∀ w, ρ g w i = MvPolynomial.eval w P) ∧
      (∀ w i, ρ ThricePuncturedSphere.periph0⁻¹ w i =
        w i + if (i : ℕ) = 0 then 2 * Real.pi * Complex.I else 0) ∧
      (∀ w i, ρ ThricePuncturedSphere.periph1⁻¹ w i =
        w i - if (i : ℕ) = 0 then 0 else
          2 * Real.pi * Complex.I * w 0 ^ ((i : ℕ) - 1) / (((i : ℕ) - 1).factorial : ℂ)) ∧
      (∀ g p, B (g • p) = ρ g (B p)) :=
  ⟨polylogOneBranch, polylogMonodromy 1,
    fun _ γ => by
      obtain ⟨f, hf, hf0, hval⟩ :=
        continuesInside_polylogTower_one.exists_isAnalyticContinuationAlong_universalCoverBranch γ
      rw [ThricePuncturedSphere.coe_basePt] at hf0
      exact ⟨f, hf, hf0, hval⟩,
    exists_mvPolynomial_polylogMonodromy 1, polylogMonodromy_periph0_inv 1,
    polylogMonodromy_periph1_inv 1, polylogOneBranch_smul⟩

/-- At `basepointLift`, `polylogOneBranch` evaluates to `(-Real.log 2, Real.log 2)`. -/
theorem polylogOneBranch_basepointLift :
    polylogOneBranch (UniversalCover.basepointLift ThricePuncturedSphere.basePt) =
      ![-(Real.log 2 : ℂ), (Real.log 2 : ℂ)] := by
  rw [polylogOneBranch, ContinuesInside.universalCoverBranch_basepointLift,
    ThricePuncturedSphere.coe_basePt]
  ext i; fin_cases i
  · exact polylogTower_half_zero 1
  · exact polylogTower_half_one le_rfl

/-- After one counterclockwise loop `γ0` around `0` from `1 / 2`, `Log` becomes
`-Real.log 2 + 2πi` while `Li₁` stays `Real.log 2`. -/
theorem polylogOneBranch_periph0_inv_smul_basepointLift :
    polylogOneBranch (ThricePuncturedSphere.periph0⁻¹ •
        (UniversalCover.basepointLift ThricePuncturedSphere.basePt :
          UniversalCover ThricePuncturedSphere.basePt)) =
      ![-(Real.log 2 : ℂ) + 2 * Real.pi * Complex.I, (Real.log 2 : ℂ)] := by
  rw [polylogOneBranch_smul, polylogOneBranch_basepointLift]
  ext i; fin_cases i <;> simp

/-- After one counterclockwise loop `γ1` around `1` from `1 / 2`, `Log` stays `-Real.log 2` while
`Li₁` becomes `Real.log 2 - 2πi`. -/
theorem polylogOneBranch_periph1_inv_smul_basepointLift :
    polylogOneBranch (ThricePuncturedSphere.periph1⁻¹ •
        (UniversalCover.basepointLift ThricePuncturedSphere.basePt :
          UniversalCover ThricePuncturedSphere.basePt)) =
      ![-(Real.log 2 : ℂ), (Real.log 2 : ℂ) - 2 * Real.pi * Complex.I] := by
  rw [polylogOneBranch_smul, polylogOneBranch_basepointLift]
  ext i; fin_cases i <;> simp

end TauCeti.Polylog
