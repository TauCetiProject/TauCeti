/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.BirthDeath.NormalForm
public import TauCeti.Analysis.Calculus.Morse.Fredholm
import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Fredholm regularity of linearized trajectory operators in the birth–death model

For `s > 0`, this file establishes the `W^{1,2} → L²` Fredholm regularity of the linearized
trajectory operator `D_γ ξ = ξ' + Hess f(γ) ξ` along any newborn connecting trajectory:

* **In one dimension (`TauCeti.birthDeathPotential s`):** along any negative gradient trajectory `γ`
  from `-√s` to `√s`, `D_γ` is Fredholm of index `1`, surjective, with one-dimensional kernel
  spanned by `deriv γ`, trivial kernel for `D_{-Hess}` (hence injective formal adjoint
  `-d/ds + Hess f(γ)`), and bijective constant operators at `±√s`.
* **With a `C²` transverse function `g : F → ℝ`:** above a nondegenerate critical point `y` on a
  real Hilbert space `F`, every trajectory `z` from `(-√s, y)` to `(√s, y)` stays at `y` in `F`, so
  `D_{-Hess}` has trivial kernel on `W^{1,2}`
  (`TauCeti.ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot`); when `F` is
  finite dimensional, `D_z` is Fredholm of index `1`, surjective, with kernel spanned by `deriv z`.
* **For `TauCeti.birthDeathNormalForm s`:** `D_{-Hess}` has trivial kernel on `W^{1,2}` on arbitrary
  real Hilbert spaces `Eₛ, Eᵤ`, and on finite-dimensional spaces `D_γ` is Fredholm of index `1`,
  surjective, with kernel spanned by `deriv γ` and bijective endpoint operators.

## Main declarations

* `TauCeti.isFredholm_trajectoryOperator_birthDeathPotential`,
  `TauCeti.index_trajectoryOperator_birthDeathPotential`,
  `TauCeti.surjective_trajectoryOperator_birthDeathPotential`,
  `TauCeti.exists_ker_trajectoryOperator_birthDeathPotential_eq_span`.
* `TauCeti.ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot`,
  `TauCeti.surjective_trajectoryOperator_separatedSum_birthDeathPotential`,
  `TauCeti.exists_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_span`.
* `TauCeti.ker_trajectoryOperator_neg_birthDeathNormalForm_eq_bot`,
  `TauCeti.index_trajectoryOperator_birthDeathNormalForm`,
  `TauCeti.surjective_trajectoryOperator_birthDeathNormalForm`,
  `TauCeti.exists_ker_trajectoryOperator_birthDeathNormalForm_eq_span`.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173.
* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2.
-/

public section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Topology

namespace TauCeti

/-! ### One-dimensional Fredholm regularity -/

section OneDimensional

open TauCeti.WeakDerivStep

variable {s : ℝ} {γ : ℝ → ℝ}
  {AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- Along a negative gradient trajectory of `birthDeathPotential s` (`s > 0`) from `-√s` to `√s`,
the linearized operator `ξ ↦ ξ' + 2 γ ξ` from `W^{1,2}(ℝ, ℝ)` to `L²(ℝ, ℝ)` is Fredholm. -/
theorem isFredholm_trajectoryOperator_birthDeathPotential (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  hγ.isFredholm_trajectoryOperator_hessianOperator (contDiff_birthDeathPotential s)
    (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs)
    (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs) hbot htop hAL

/-- **The linearized birth–death trajectory operator has Fredholm index `1`.** -/
theorem index_trajectoryOperator_birthDeathPotential (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [hγ.index_trajectoryOperator_hessianOperator (contDiff_birthDeathPotential s)
    (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs)
    (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs) hbot htop hAL,
    morseIndex_birthDeathPotential_neg_sqrt hs, morseIndex_birthDeathPotential_sqrt hs]
  simp

/-- **The kernel of the linearized birth–death trajectory operator is one-dimensional.** -/
theorem finrank_ker_trajectoryOperator_birthDeathPotential_eq_one (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker = 1 :=
  hγ.finrank_ker_trajectoryOperator_hessianOperator_eq_one (Module.finrank_self ℝ)
    (contDiff_birthDeathPotential s) hbot htop (by linarith [Real.sqrt_pos.2 hs]) hAL

/-- **The kernel of the linearized birth–death trajectory operator is spanned by `γ'`.** -/
theorem exists_ker_trajectoryOperator_birthDeathPotential_eq_span (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv γ ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u :=
  hγ.exists_ker_trajectoryOperator_hessianOperator_eq_span (Module.finrank_self ℝ)
    (contDiff_birthDeathPotential s) hbot htop (by linarith [Real.sqrt_pos.2 hs]) hAL

/-- **Transversality of the newborn connecting trajectory in one dimension.** -/
theorem surjective_trajectoryOperator_birthDeathPotential (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) :=
  (hγ.surjective_trajectoryOperator_hessianOperator_iff (Module.finrank_self ℝ)
    (contDiff_birthDeathPotential s)
    (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs)
    (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs) hbot htop
    (by linarith [Real.sqrt_pos.2 hs]) hAL).2
    (by rw [morseIndex_birthDeathPotential_neg_sqrt hs, morseIndex_birthDeathPotential_sqrt hs])

/-- **Triviality of the kernel of `D_{-Hess}` in one dimension** (formal-adjoint injectivity). -/
theorem ker_trajectoryOperator_neg_birthDeathPotential_eq_bot (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    (trajectoryOperator (p := 2) (-AL)).ker = ⊥ :=
  (hγ.surjective_trajectoryOperator_hessianOperator_iff_ker_neg_eq_bot
    (contDiff_birthDeathPotential s)
    (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs)
    (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs) hbot htop hAL).1
    (surjective_trajectoryOperator_birthDeathPotential hs hγ hbot htop hAL)

/-- Along any negative gradient trajectory of `birthDeathPotential s` (`s > 0`) from `-√s` to `√s`,
the adjoint ODE `v' - 2 γ v = 0` has no nonzero square-integrable solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_birthDeathPotential_eq_bot (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s)) :
    squareIntegrableSolutions (fun t ↦ -hessianOperator (birthDeathPotential s) (γ t)) = ⊥ := by
  have hmem : MemLp (fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    (contDiff_birthDeathPotential s).memLp_top_hessianOperator_comp hγ.continuous hbot htop _
  exact (hγ.ker_trajectoryOperator_neg_hessianOperator_eq_bot_iff
    (contDiff_birthDeathPotential s) hmem.coeFn_toLp).1
    (ker_trajectoryOperator_neg_birthDeathPotential_eq_bot hs hγ hbot htop hmem.coeFn_toLp)

/-- At the constant trajectory `-√s` (`s > 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_birthDeathPotential_neg_sqrt (hs : 0 < s)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (birthDeathPotential s) (-√s)) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt
    hs).bijective_trajectoryOperator_hessianOperator hAL

/-- At the constant trajectory `√s` (`s > 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_birthDeathPotential_sqrt (hs : 0 < s)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (birthDeathPotential s) √s) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  (isNondegenerateCriticalPoint_birthDeathPotential_sqrt
    hs).bijective_trajectoryOperator_hessianOperator hAL

end OneDimensional

/-! ### Fredholm regularity with an arbitrary `C²` transverse function -/

section SeparatedSumHilbert

open TauCeti.WeakDerivStep

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {s : ℝ} {g : F → ℝ} {y : F} {z : ℝ → WithLp 2 (ℝ × F)}
  {AL : Lp (WithLp 2 (ℝ × F) →L[ℝ] WithLp 2 (ℝ × F)) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- On any real Hilbert space `F`, along a negative gradient trajectory `z` of
`separatedSum (birthDeathPotential s) g` (`s > 0`) from `(-√s, y)` to `(√s, y)` above a
nondegenerate critical point `y` of a `C²` function `g`, the adjoint ODE
`v' - Hess (separatedSum (birthDeathPotential s) g)(z) v = 0` has no nonzero `L²` solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_separatedSum_birthDeathPotential_eq_bot
    (hs : 0 < s) (hg : ContDiff ℝ 2 g) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y)))) :
    squareIntegrableSolutions
      (fun t ↦ -hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) = ⊥ := by
  have hgd : Differentiable ℝ g := hg.differentiable two_ne_zero
  obtain ⟨h₁, -⟩ := (isIntegralCurve_separatedSum_iff
    (fun _ ↦ differentiable_birthDeathPotential s _) fun _ ↦ hgd _).1 hz
  obtain ⟨τ, hτ⟩ := (existsUnique_eq_birthDeathOrbit_separatedSum hs (fun _ ↦ hgd _)
    hgd.continuous.continuousAt hz hbot htop).exists
  have hsnd : ∀ t, (z t).snd = y := fun t ↦ by simpa using congrArg WithLp.snd (congrFun hτ t)
  have hfst := (WithLp.fstL 2 ℝ ℝ F).continuous.tendsto
  exact squareIntegrableSolutions_eq_bot_of_withLp
    (A₁ := fun t ↦ -hessianOperator (birthDeathPotential s) (z t).fst)
    (A₂ := fun _ ↦ -hessianOperator g y)
    (fun t w ↦ by
      rw [neg_apply, hessianOperator_separatedSum_apply
        (contDiff_birthDeathPotential s).contDiffAt hg.contDiffAt, hsnd t]
      exact WithLp.prod_ext (by simp) (by simp))
    (squareIntegrableSolutions_neg_hessianOperator_birthDeathPotential_eq_bot hs h₁
      (by simpa [Function.comp_def] using (hfst _).comp hbot)
      (by simpa [Function.comp_def] using (hfst _).comp htop))
    hy.squareIntegrableSolutions_neg_hessianOperator_const_eq_bot

/-- **Formal-adjoint injectivity in the birth–death model with transverse directions:** on any real
Hilbert space `F`, `ξ ↦ ξ' - Hess (separatedSum (birthDeathPotential s) g)(z) ξ` (minus the formal
adjoint) has trivial kernel on `W^{1,2}`. -/
theorem ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot
    (hs : 0 < s) (hg : ContDiff ℝ 2 g) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    (trajectoryOperator (p := 2) (-AL)).ker = ⊥ :=
  (hz.ker_trajectoryOperator_neg_hessianOperator_eq_bot_iff
    ((contDiff_birthDeathPotential s).separatedSum hg) hAL).2
    (squareIntegrableSolutions_neg_hessianOperator_separatedSum_birthDeathPotential_eq_bot
      hs hg hy hz hbot htop)

end SeparatedSumHilbert

section SeparatedSumFiniteDimensional

open TauCeti.WeakDerivStep

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {s : ℝ} {g : F → ℝ} {y : F} {z : ℝ → WithLp 2 (ℝ × F)}
  {AL : Lp (WithLp 2 (ℝ × F) →L[ℝ] WithLp 2 (ℝ × F)) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- Along any negative gradient trajectory `z` of `separatedSum (birthDeathPotential s) g` (`s > 0`)
from `(-√s, y)` to `(√s, y)` above a nondegenerate critical point `y` of `g`, `D_z` is Fredholm. -/
theorem isFredholm_trajectoryOperator_separatedSum_birthDeathPotential
    (hs : 0 < s) (hg : ContDiff ℝ 2 g) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  hz.isFredholm_trajectoryOperator_hessianOperator
    ((contDiff_birthDeathPotential s).separatedSum hg)
    ((isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs).separatedSum hy)
    ((isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs).separatedSum hy)
    hbot htop hAL

/-- **The linearized operator along the newborn connecting trajectory has Fredholm index `1`.** -/
theorem index_trajectoryOperator_separatedSum_birthDeathPotential
    (hs : 0 < s) (hg : ContDiff ℝ 2 g) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [hz.index_trajectoryOperator_hessianOperator
      ((contDiff_birthDeathPotential s).separatedSum hg)
      ((isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs).separatedSum hy)
      ((isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs).separatedSum hy)
      hbot htop hAL,
    morseIndex_separatedSum_birthDeathPotential_neg_sqrt hs hy,
    morseIndex_separatedSum_birthDeathPotential_sqrt hs hy]
  push_cast; ring

/-- **Transversality of the newborn connecting trajectory with transverse directions.** -/
theorem surjective_trajectoryOperator_separatedSum_birthDeathPotential
    (hs : 0 < s) (hg : ContDiff ℝ 2 g) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) :=
  (hz.surjective_trajectoryOperator_hessianOperator_iff_ker_neg_eq_bot
    ((contDiff_birthDeathPotential s).separatedSum hg)
    ((isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs).separatedSum hy)
    ((isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs).separatedSum hy)
    hbot htop hAL).2
    (ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot hs hg hy hz hbot htop hAL)

/-- **The kernel of `D_z` along the newborn connecting trajectory is one-dimensional.** -/
theorem finrank_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_one
    (hs : 0 < s) (hg : ContDiff ℝ 2 g) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker = 1 := by
  have hidx := index_trajectoryOperator_separatedSum_birthDeathPotential hs hg hy hz hbot htop hAL
  rw [ContinuousLinearMap.index_of_surjective _
    (surjective_trajectoryOperator_separatedSum_birthDeathPotential hs hg hy hz hbot htop hAL)]
    at hidx
  omega

/-- **The kernel of `D_z` along the newborn connecting trajectory is spanned by `z'`.** -/
theorem exists_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_span
    (hs : 0 < s) (hg : ContDiff ℝ 2 g) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ
          (Lp (WithLp 2 (ℝ × F)) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ
          (Lp (WithLp 2 (ℝ × F)) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv z ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u := by
  have hpq : (WithLp.toLp 2 (-√s, y) : WithLp 2 (ℝ × F)) ≠ WithLp.toLp 2 (√s, y) := fun h ↦ by
    have h1 := congrArg WithLp.fst h
    simp only [WithLp.toLp_fst] at h1
    linarith [Real.sqrt_pos.2 hs]
  exact hz.exists_ker_trajectoryOperator_hessianOperator_eq_span_of_finrank_eq_one
    ((contDiff_birthDeathPotential s).separatedSum hg) hbot htop hpq hAL
    (finrank_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_one hs hg hy hz hbot
      htop hAL)

/-- At the constant trajectory `(-√s, y)` (`s > 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_separatedSum_birthDeathPotential_neg_sqrt
    (hs : 0 < s) (hy : IsNondegenerateCriticalPoint g y)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (-√s, y))) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  ((isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt
    hs).separatedSum hy).bijective_trajectoryOperator_hessianOperator hAL

/-- At the constant trajectory `(√s, y)` (`s > 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_separatedSum_birthDeathPotential_sqrt
    (hs : 0 < s) (hy : IsNondegenerateCriticalPoint g y)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (√s, y))) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  ((isNondegenerateCriticalPoint_birthDeathPotential_sqrt
    hs).separatedSum hy).bijective_trajectoryOperator_hessianOperator hAL

end SeparatedSumFiniteDimensional

/-! ### Formal-adjoint injectivity on arbitrary Hilbert spaces and Cerf normal form corollaries -/

section NormalFormHilbert

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ] [CompleteSpace Eₛ]
  [NormedAddCommGroup Eᵤ] [InnerProductSpace ℝ Eᵤ] [CompleteSpace Eᵤ]
  {s : ℝ} {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
  {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
    (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- On any pair of real Hilbert spaces, `w' - Hess splitQuadratic(0) w = 0` has no nonzero `L²`
solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_splitQuadratic_eq_bot :
    squareIntegrableSolutions
      (fun _ : ℝ ↦ -hessianOperator (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0) = ⊥ :=
  IsNondegenerateCriticalPoint.squareIntegrableSolutions_neg_hessianOperator_const_eq_bot
    isNondegenerateCriticalPoint_splitQuadratic_zero

/-- On any pair of real Hilbert spaces, along a negative gradient trajectory of
`birthDeathNormalForm s` (`s > 0`) from `birthDeathUpper s` to `birthDeathLower s`, the adjoint ODE
`v' - Hess F_s(γ) v = 0` has no nonzero `L²` solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_birthDeathNormalForm_eq_bot (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower s))) :
    squareIntegrableSolutions (fun t ↦ -hessianOperator (birthDeathNormalForm s) (γ t)) = ⊥ := by
  rw [birthDeathNormalForm_def] at hγ ⊢
  exact squareIntegrableSolutions_neg_hessianOperator_separatedSum_birthDeathPotential_eq_bot hs
    contDiff_splitQuadratic isNondegenerateCriticalPoint_splitQuadratic_zero hγ
    (by rwa [birthDeathUpper_def] at hbot) (by rwa [birthDeathLower_def] at htop)

/-- **Hilbert-space formal-adjoint injectivity along a newborn connecting trajectory:** on arbitrary
real Hilbert spaces `Eₛ, Eᵤ`, for `s > 0` and any trajectory `γ` from `birthDeathUpper s` to
`birthDeathLower s`, `ξ ↦ ξ' - Hess (birthDeathNormalForm s)(γ) ξ` (minus the formal adjoint
`-d/dt + Hess (birthDeathNormalForm s)(γ)`) has trivial kernel on `W^{1,2}`. -/
theorem ker_trajectoryOperator_neg_birthDeathNormalForm_eq_bot (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower s)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathNormalForm s) (γ t)) :
    (WeakDerivStep.trajectoryOperator (p := 2) (-AL)).ker = ⊥ := by
  rw [birthDeathNormalForm_def] at hγ hAL
  exact ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot hs
    contDiff_splitQuadratic isNondegenerateCriticalPoint_splitQuadratic_zero hγ
    (by rwa [birthDeathUpper_def] at hbot) (by rwa [birthDeathLower_def] at htop) hAL

end NormalFormHilbert

section NormalFormFiniteDimensional

open TauCeti.WeakDerivStep

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
  [FiniteDimensional ℝ Eₛ] [NormedAddCommGroup Eᵤ] [InnerProductSpace ℝ Eᵤ]
  [FiniteDimensional ℝ Eᵤ] {s : ℝ} {γ : ℝ → WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))}
  {AL : Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ)) →L[ℝ] WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) ∞
    (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- Along any negative gradient trajectory of `birthDeathNormalForm s` (`s > 0`) from
`birthDeathUpper s` to `birthDeathLower s`, `D_γ` on `W^{1,2}` is Fredholm. -/
theorem isFredholm_trajectoryOperator_birthDeathNormalForm (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower s)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathNormalForm s) (γ t)) :
    (trajectoryOperator (p := 2) AL).IsFredholm := by
  rw [birthDeathNormalForm_def] at hγ hAL
  exact isFredholm_trajectoryOperator_separatedSum_birthDeathPotential hs contDiff_splitQuadratic
    isNondegenerateCriticalPoint_splitQuadratic_zero hγ
    (by rwa [birthDeathUpper_def] at hbot) (by rwa [birthDeathLower_def] at htop) hAL

/-- **The linearized operator along the newborn Cerf connecting trajectory has Fredholm index `1`.**
-/
theorem index_trajectoryOperator_birthDeathNormalForm (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower s)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathNormalForm s) (γ t)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [birthDeathNormalForm_def] at hγ hAL
  exact index_trajectoryOperator_separatedSum_birthDeathPotential hs contDiff_splitQuadratic
    isNondegenerateCriticalPoint_splitQuadratic_zero hγ
    (by rwa [birthDeathUpper_def] at hbot) (by rwa [birthDeathLower_def] at htop) hAL

/-- **Transversality of the newborn Cerf connecting trajectory in arbitrary finite dimension.** -/
theorem surjective_trajectoryOperator_birthDeathNormalForm (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower s)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathNormalForm s) (γ t)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) := by
  rw [birthDeathNormalForm_def] at hγ hAL
  exact surjective_trajectoryOperator_separatedSum_birthDeathPotential hs contDiff_splitQuadratic
    isNondegenerateCriticalPoint_splitQuadratic_zero hγ
    (by rwa [birthDeathUpper_def] at hbot) (by rwa [birthDeathLower_def] at htop) hAL

/-- **The kernel of `D_γ` along the newborn Cerf connecting trajectory is one-dimensional.** -/
theorem finrank_ker_trajectoryOperator_birthDeathNormalForm_eq_one (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower s)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathNormalForm s) (γ t)) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker = 1 := by
  rw [birthDeathNormalForm_def] at hγ hAL
  exact finrank_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_one hs
    contDiff_splitQuadratic isNondegenerateCriticalPoint_splitQuadratic_zero hγ
    (by rwa [birthDeathUpper_def] at hbot) (by rwa [birthDeathLower_def] at htop) hAL

/-- **The kernel of `D_γ` along the newborn Cerf connecting trajectory is spanned by `γ'`.** -/
theorem exists_ker_trajectoryOperator_birthDeathNormalForm_eq_span (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ z ↦ -∇ (birthDeathNormalForm s) z))
    (hbot : Tendsto γ atBot (𝓝 (birthDeathUpper s)))
    (htop : Tendsto γ atTop (𝓝 (birthDeathLower s)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathNormalForm s) (γ t)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ
          (Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ
          (Lp (WithLp 2 (ℝ × WithLp 2 (Eₛ × Eᵤ))) 2
            (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv γ ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u := by
  rw [birthDeathNormalForm_def] at hγ hAL
  exact exists_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_span hs
    contDiff_splitQuadratic isNondegenerateCriticalPoint_splitQuadratic_zero hγ
    (by rwa [birthDeathUpper_def] at hbot) (by rwa [birthDeathLower_def] at htop) hAL

/-- At the constant trajectory `birthDeathUpper s` (`s > 0`), `D` is bijective on `W^{1,2}`. -/
theorem bijective_trajectoryOperator_birthDeathNormalForm_upper (hs : 0 < s)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (birthDeathNormalForm s) (birthDeathUpper s)) :
    Function.Bijective (trajectoryOperator (p := 2) AL) := by
  rw [birthDeathNormalForm_def, birthDeathUpper_def] at hAL
  exact bijective_trajectoryOperator_separatedSum_birthDeathPotential_neg_sqrt hs
    isNondegenerateCriticalPoint_splitQuadratic_zero hAL

/-- At the constant trajectory `birthDeathLower s` (`s > 0`), `D` is bijective on `W^{1,2}`. -/
theorem bijective_trajectoryOperator_birthDeathNormalForm_lower (hs : 0 < s)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (birthDeathNormalForm s) (birthDeathLower s)) :
    Function.Bijective (trajectoryOperator (p := 2) AL) := by
  rw [birthDeathNormalForm_def, birthDeathLower_def] at hAL
  exact bijective_trajectoryOperator_separatedSum_birthDeathPotential_sqrt hs
    isNondegenerateCriticalPoint_splitQuadratic_zero hAL

end NormalFormFiniteDimensional

end TauCeti

end
