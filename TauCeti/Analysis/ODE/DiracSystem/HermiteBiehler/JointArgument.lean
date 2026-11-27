/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Analysis.Complex.ContinuousLog.Basic
import TauCeti.Analysis.ODE.DiracSystem.ZeroFree
import TauCeti.Analysis.ODE.Propagator.ParameterContinuity

/-!
# The argument of the Dirac Hermite–Biehler function as a function of `(t, x)`

Let `q` be a potential, locally integrable on `[0, ∞)`, with Dirac fundamental matrix
`M_q(t, z)` (`TauCeti.diracFundamentalMatrix`) and Hermite–Biehler function
`E(t, z) = A(t, z) - i C(t, z)` (`TauCeti.diracHermiteBiehler`).

## Main results

* `TauCeti.continuousOn_diracFundamentalMatrix_apply_prod`: every entry of `M_q(t, z)` is jointly
  continuous in `(t, z)` on `[0, T] × ℂ` when `q` is integrable on `[0, T]`; hence so is `E`
  (`TauCeti.continuousOn_diracHermiteBiehler_prod`).
* `TauCeti.exists_continuousOn_diracHermiteBiehler_eq_norm_mul_exp_prod`: `E(t, x)` has an
  argument `φ(t, x)`, jointly continuous on `[0, ∞) × ℝ`, with `φ(0, x) = 0` and
  `E(t, x) = |E(t, x)| e^{iφ(t, x)}`.
* `TauCeti.eqOn_of_diracHermiteBiehler_eq_norm_mul_exp_prod`: this argument is unique.

## Implementation notes

Joint continuity is `TauCeti.continuousOn_propagator_parameter`, since the Dirac coefficient is
affine in `z`. `E(t, x)` does not vanish for real `x`
(`TauCeti.diracFundamentalMatrix_sub_I_mul_ne_zero`), so the continuous function
`(t, x) ↦ E(max t 0, x)` on the simply connected plane has a continuous logarithm `L`
(`Complex.exists_continuousOn_eqOn_exp_comp`). As `E(0, x) = 1`, the imaginary part of
`L(t, x) - L(0, x)` is the argument.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open MeasureTheory Set Matrix Complex Filter Topology

namespace TauCeti

variable {q : ℝ → ℂ} {T : ℝ}

/-- **Joint continuity of the fundamental matrix.** If `q` is integrable on `[0, T]`, every entry
of `M_q(t, z)` is continuous in `(t, z)` on `[0, T] × ℂ`. -/
theorem continuousOn_diracFundamentalMatrix_apply_prod (hq : IntegrableOn q (Icc 0 T))
    (i j : Fin 2) :
    ContinuousOn (fun p : ℝ × ℂ ↦ diracFundamentalMatrix q p.1 p.2 i j) (Icc 0 T ×ˢ univ) := by
  rcases lt_or_ge T 0 with hT | hT
  · simp [Icc_eq_empty_of_lt hT]
  set Tm := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  set P : ℝ → ℂ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun t z ↦ Tm (diracCoeff q z t)
  -- The coefficient is `P t 0 + z • G` for the constant operator `G = -Ω`.
  set G : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) := Tm !![0, -1; 1, 0]
  have hP (t : ℝ) (z : ℂ) : P t z = P t 0 + z • G := by
    simp only [P, G, ← map_smul, ← map_add]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;> simp [diracCoeff_def] <;> ring
  have hint : IntegrableOn (fun t ↦ P t 0) (Icc 0 T) :=
    integrableOn_toEuclideanCLM_diracCoeff hq 0
  have hcont := continuousOn_propagator_parameter (P := P) (U := univ) (a := 0) (b := T)
    (fun z _ ↦ (integrableOn_toEuclideanCLM_diracCoeff hq z).aestronglyMeasurable)
    (ae_of_all _ fun t _ ↦ (continuous_const.add
      (continuous_id.smul continuous_const)).continuousOn.congr fun z _ ↦ hP t z)
    (fun K _ hK ↦ by
      obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
      refine ⟨fun t ↦ ‖P t 0‖ + R * ‖G‖, hint.norm.add (integrableOn_const
        measure_Icc_lt_top.ne), fun z hz ↦ ae_of_all _ fun t _ ↦ ?_⟩
      rw [hP t z]
      refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hR z hz) (norm_nonneg _))
  -- The entry functional `X ↦ (X e_j)_i` on operators.
  let L : (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) →L[ℂ] ℂ :=
    (EuclideanSpace.proj i).comp
      (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace.single j 1))
  have hL (A : Matrix (Fin 2) (Fin 2) ℂ) : L (Tm A) = A i j := by simp [L, Tm]
  have hM : (fun p : ℝ × ℂ ↦ diracFundamentalMatrix q p.1 p.2 i j) =
      fun p ↦ L (propagator (fun t ↦ P t p.2) p.1 0) := by
    ext1 p
    change _ = L (propagator (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q p.2 s))
      p.1 0)
    rw [← toEuclideanCLM_diracFundamentalMatrix, hL]
  rw [hM]
  refine L.continuous.comp_continuousOn
    ((hcont.comp (f := fun p : ℝ × ℂ ↦ ((p.1, (0 : ℝ)), p.2)) (by fun_prop) fun p hp ↦ ?_))
  exact ⟨⟨hp.1, ⟨le_rfl, hT⟩⟩, mem_univ _⟩

/-- **Joint continuity of `E`.** If `q` is integrable on `[0, T]`, `E(t, z)` is continuous in
`(t, z)` on `[0, T] × ℂ`. -/
theorem continuousOn_diracHermiteBiehler_prod (hq : IntegrableOn q (Icc 0 T)) :
    ContinuousOn (fun p : ℝ × ℂ ↦ diracHermiteBiehler q p.1 p.2) (Icc 0 T ×ˢ univ) := by
  simp_rw [diracHermiteBiehler_def]
  exact (continuousOn_diracFundamentalMatrix_apply_prod hq 0 0).sub
    (continuousOn_const.mul (continuousOn_diracFundamentalMatrix_apply_prod hq 1 0))

/-- The function `(t, x) ↦ E(max t 0, x)` is continuous on the plane. -/
private theorem continuous_diracHermiteBiehler_max (hq : LocallyIntegrableOn q (Ici 0)) :
    Continuous fun p : ℝ × ℝ ↦ diracHermiteBiehler q (max p.1 0) p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  set T := max p₀.1 0 + 1
  have hqT : IntegrableOn q (Icc 0 T) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  have hon : ContinuousOn (fun p : ℝ × ℝ ↦ diracHermiteBiehler q (max p.1 0) p.2)
      {p | p.1 < T} :=
    (continuousOn_diracHermiteBiehler_prod hqT).comp
      (f := fun p : ℝ × ℝ ↦ (max p.1 0, (p.2 : ℂ)))
      ((continuous_fst.max continuous_const).prodMk
        (continuous_ofReal.comp continuous_snd)).continuousOn fun p hp ↦
      ⟨⟨le_max_right _ _, max_le hp.le (by positivity)⟩, mem_univ _⟩
  refine hon.continuousAt (isOpen_lt continuous_fst continuous_const |>.mem_nhds ?_)
  simp only [mem_ofPred_eq, T]
  linarith [le_max_left p₀.1 0]

/-- The plane `ℝ × ℝ` is simply connected. -/
private theorem isSimplyConnected_univ_prod : IsSimplyConnected (univ : Set (ℝ × ℝ)) :=
  have : ContractibleSpace (univ : Set (ℝ × ℝ)) :=
    Convex.contractibleSpace convex_univ univ_nonempty
  SimplyConnectedSpace.ofContractible _

/-- **A jointly continuous argument of `E` on the real axis.** For `q` locally integrable on
`[0, ∞)`, there is `φ : ℝ × ℝ → ℝ`, continuous on `[0, ∞) × ℝ`, with `φ(0, x) = 0` and
`E(t, x) = |E(t, x)| e^{iφ(t, x)}` for `t ≥ 0` and real `x`. -/
theorem exists_continuousOn_diracHermiteBiehler_eq_norm_mul_exp_prod
    (hq : LocallyIntegrableOn q (Ici 0)) :
    ∃ φ : ℝ × ℝ → ℝ, ContinuousOn φ (Ici 0 ×ˢ univ) ∧ (∀ x, φ (0, x) = 0) ∧
      ∀ t, 0 ≤ t → ∀ x : ℝ,
        diracHermiteBiehler q t x = ‖diracHermiteBiehler q t x‖ * exp (I * φ (t, x)) := by
  set g : ℝ × ℝ → ℂ := fun p ↦ diracHermiteBiehler q (max p.1 0) p.2
  have hg0 : 0 ∉ g '' univ := by
    rintro ⟨p, -, hp⟩
    simp only [g, diracHermiteBiehler_def] at hp
    exact diracFundamentalMatrix_sub_I_mul_ne_zero hq (le_max_right p.1 0)
      (z := (p.2 : ℂ)) (by simp) 0 hp
  obtain ⟨L, hLc, hLg⟩ := exists_continuousOn_eqOn_exp_comp isSimplyConnected_univ_prod
    isOpen_univ (continuous_diracHermiteBiehler_max hq).continuousOn hg0
  have hLc' : Continuous L := continuousOn_univ.1 hLc
  have hexp (p : ℝ × ℝ) : exp (L p) = g p := hLg (mem_univ p)
  refine ⟨fun p ↦ (L p).im - (L (0, p.2)).im, (Complex.continuous_im.comp hLc' |>.sub
    (Complex.continuous_im.comp (hLc'.comp (by fun_prop)))).continuousOn, fun x ↦ sub_self _,
    fun t ht x ↦ ?_⟩
  -- `exp (L (0, x)) = E(0, x) = 1`, so `L (0, x) = i Im L (0, x)` and `exp (i Im L (0, x)) = 1`.
  have h0 : exp (L (0, x)) = 1 := by simp [hexp, g, diracHermiteBiehler_zero]
  have hre0 : (L (0, x)).re = 0 := by
    have := congrArg norm h0
    rwa [norm_exp, norm_one, Real.exp_eq_one_iff] at this
  have hI0 : exp (I * (L (0, x)).im) = 1 := by
    rw [← h0]; congr 1; apply Complex.ext <;> simp [hre0]
  have hgt : g (t, x) = diracHermiteBiehler q t x := by simp [g, max_eq_left ht]
  rw [← hgt, ← hexp, norm_exp, ofReal_sub, mul_sub, exp_sub, hI0, div_one, ofReal_exp,
    ← exp_add]
  congr 1
  apply Complex.ext <;> simp

/-- **Uniqueness of the argument.** For `q` locally integrable on `[0, ∞)`, two functions
continuous on `[0, ∞) × ℝ`, vanishing at `t = 0` and arguments of `E(t, x)` there, agree on
`[0, ∞) × ℝ`. -/
theorem eqOn_of_diracHermiteBiehler_eq_norm_mul_exp_prod (hq : LocallyIntegrableOn q (Ici 0))
    {φ ψ : ℝ × ℝ → ℝ} (hφ : ContinuousOn φ (Ici 0 ×ˢ univ)) (hψ : ContinuousOn ψ (Ici 0 ×ˢ univ))
    (hφ0 : ∀ x, φ (0, x) = 0) (hψ0 : ∀ x, ψ (0, x) = 0)
    (hφE : ∀ t, 0 ≤ t → ∀ x : ℝ,
      diracHermiteBiehler q t x = ‖diracHermiteBiehler q t x‖ * exp (I * φ (t, x)))
    (hψE : ∀ t, 0 ≤ t → ∀ x : ℝ,
      diracHermiteBiehler q t x = ‖diracHermiteBiehler q t x‖ * exp (I * ψ (t, x))) :
    EqOn φ ψ (Ici 0 ×ˢ univ) := by
  set S : Set (ℝ × ℝ) := Ici 0 ×ˢ univ
  set w : ℝ × ℝ → ℂ := fun p ↦ I * ((ψ p : ℂ) - φ p)
  have hS : IsPreconnected S := ((convex_Ici 0).prod convex_univ).isPreconnected
  have hw : ContinuousOn w S :=
    continuousOn_const.mul ((continuous_ofReal.comp_continuousOn hψ).sub
      (continuous_ofReal.comp_continuousOn hφ))
  have h1 : ∀ v ∈ w '' S, exp v = 1 := by
    rintro _ ⟨⟨t, x⟩, hp, rfl⟩
    have hE : diracHermiteBiehler q t x ≠ 0 := by
      rw [diracHermiteBiehler_def]
      exact diracFundamentalMatrix_sub_I_mul_ne_zero hq hp.1 (z := (x : ℂ)) (by simp) 0
    have hnorm : (‖diracHermiteBiehler q t x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hE
    have h := (hφE t hp.1 x).symm.trans (hψE t hp.1 x)
    rw [mul_right_inj' hnorm] at h
    simp only [w, mul_sub, exp_sub, ← h, div_self (exp_ne_zero _)]
  intro p hp
  have h0 : ((0 : ℝ), p.2) ∈ S := ⟨le_rfl, mem_univ _⟩
  have := eq_of_isPreconnected_of_forall_exp_eq_one (hS.image w hw) h1 (mem_image_of_mem w hp)
    (mem_image_of_mem w h0)
  simp only [w, hφ0, hψ0, sub_self, mul_zero, mul_eq_zero, I_ne_zero, false_or, sub_eq_zero] at this
  exact_mod_cast this.symm

end TauCeti
