/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Frame
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# The asymptotic operator in a unitary trivialization

Along a Hamiltonian orbit the asymptotic operator `A ζ = J_t (ζ' - S_t ζ)` involves the loop of
complex structures `J_t` (`TauCeti.Floer.asymptoticOperator`). Its spectral theory is done for a
fixed complex structure `J₀` on a model space `W`. This file reads `A` in a path of frames
`Φ(t) : W → V` with `J_t Φ(t) = Φ(t) J₀`. If `ζ = Φ η`, then `ζ' = Φ' η + Φ η'`, so

`A (Φ η) = Φ (J₀ (η' - S'_t η))`,  `S'_t = Φ(t)⁻¹ (S_t Φ(t) - Φ'(t))`

(`TauCeti.Floer.asymptoticOperator_frame_apply`), where `S'` is `TauCeti.Floer.frameLoop Φ S`. So in
the frame, `A` is the asymptotic operator of the constant structure `J₀` and the loop `S'`. If
every `Φ(t)` carries a symplectic form `ω₀` of `W` to `ω` and every `S_t` is infinitesimally
`ω`-symplectic, then every `S'_t` is infinitesimally `ω₀`-symplectic
(`TauCeti.Floer.frameLoop_apply_add_apply_eq_zero`); `S'` is continuous when `Φ` is a `C¹` path
of invertible frames and `S` is continuous (`TauCeti.Floer.continuous_frameLoop`), and periodic
when `Φ` and `S` are (`TauCeti.Floer.frameLoop_periodic`). These are the hypotheses on the loop
under which the asymptotic operator of `J₀` is symmetric
(`TauCeti.CircleSobolev.real_inner_I_smul_loopOperator_comm`, when `J₀` is the multiplication by
`i` of a complex inner product space). Its eigenbasis
(`TauCeti.CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`) also needs the loop
operator of `S'` to be invertible, which follows from nondegeneracy of the orbit.

The unitary frames `Ψ_{J_t}` of `TauCeti.SymplecticForm.unitaryFrame` supply such a path for every
`C¹` loop of compatible structures `J_t`, when the inner product is the metric of `J₀`
(`TauCeti.Floer.asymptoticOperator_unitaryFrame_apply`,
`TauCeti.Floer.frameLoop_unitaryFrame_apply_add_apply_eq_zero`). Since the frames involve no
choices, they are periodic when `J_t` is. Composed with a frame `Φ` of `J₀` from a complex inner
product space, they give loops that are infinitesimally symplectic for `Im ⟪·, ·⟫`
(`TauCeti.Floer.im_inner_frameLoop_add_im_inner_frameLoop_eq_zero`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the asymptotic operator in a unitary trivialization).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Section 3.1 (unitary trivializations of real Cauchy–Riemann operators).
-/

public section

noncomputable section

open Function ContinuousLinearMap Filter
open scoped RealInnerProductSpace Topology

namespace TauCeti.Floer

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {Φ : ℝ → W →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {t : ℝ}

variable (Φ S) in
/-- The loop `S` read in a path of frames `Φ(t) : W → V`: `S'_t = Φ(t)⁻¹ (S_t Φ(t) - Φ'(t))`,
a loop of operators on the model space `W`. When every `Φ(t)` intertwines the complex structures,
the asymptotic operator of `J_t` and `S` is carried by `Φ` from the asymptotic operator of the
constant structure and `S'` (`TauCeti.Floer.asymptoticOperator_frame_apply`). -/
def frameLoop (t : ℝ) : W →L[ℝ] W :=
  (Φ t).inverse ∘L (S t ∘L Φ t - deriv Φ t)

theorem frameLoop_apply (v : W) :
    frameLoop Φ S t v = (Φ t).inverse (S t (Φ t v) - deriv Φ t v) :=
  (rfl)

/-- The frame carries the loop `S'` to `S` up to the derivative of the frame:
`Φ S' = S Φ - Φ'`. -/
theorem apply_frameLoop (hΦ : (Φ t).IsInvertible) (v : W) :
    Φ t (frameLoop Φ S t v) = S t (Φ t v) - deriv Φ t v :=
  hΦ.self_apply_inverse _

/-- `S'_t` is the unique operator `T` with `Φ T = S Φ - Φ'`. -/
theorem frameLoop_eq_iff (hΦ : (Φ t).IsInvertible) {T : W →L[ℝ] W} :
    frameLoop Φ S t = T ↔ ∀ v, Φ t (T v) = S t (Φ t v) - deriv Φ t v := by
  refine ⟨fun h v ↦ h ▸ apply_frameLoop hΦ v, fun h ↦ ext fun v ↦ hΦ.injective ?_⟩
  rw [apply_frameLoop hΦ, h]

/-- **The asymptotic operator in a frame.** If `Φ(t)` is invertible, differentiable in `t` and
intertwines `J₀` with `J_t`, then `A_{J, S} (Φ η) = Φ (A_{J₀, S'} η)` at `t`, for the loop
`S' = TauCeti.Floer.frameLoop Φ S`. -/
theorem asymptoticOperator_frame_apply {J : ℝ → AlmostComplexStructure V}
    {J₀ : AlmostComplexStructure W} {η : ℝ → W} (hΦd : DifferentiableAt ℝ Φ t)
    (hη : DifferentiableAt ℝ η t) (hΦ : (Φ t).IsInvertible)
    (hJ : ∀ v, J t (Φ t v) = Φ t (J₀ v)) :
    asymptoticOperator J S (fun s ↦ Φ s (η s)) t =
      Φ t (asymptoticOperator (fun _ ↦ J₀) (frameLoop Φ S) η t) := by
  rw [asymptoticOperator_def, asymptoticOperator_def,
    (hΦd.hasDerivAt.clm_apply hη.hasDerivAt).deriv, ← hJ, map_sub (Φ t), apply_frameLoop hΦ]
  congr 1
  abel

/-- **The loop in a symplectic frame is infinitesimally symplectic.** If every `Φ(s)` carries
`ω₀` to `ω`, `Φ` is differentiable at `t` and `S_t` is infinitesimally `ω`-symplectic, then
`S'_t` is infinitesimally `ω₀`-symplectic. -/
theorem frameLoop_apply_add_apply_eq_zero [FiniteDimensional ℝ V]
    {ω : SymplecticForm V} {ω₀ : SymplecticForm W}
    (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible)
    (hΦω : ∀ s u v, ω (Φ s u) (Φ s v) = ω₀ u v) (hS : ∀ u v, ω (S t u) v + ω u (S t v) = 0)
    (u v : W) : ω₀ (frameLoop Φ S t u) v + ω₀ u (frameLoop Φ S t v) = 0 := by
  -- Differentiating `ω(Φ u, Φ v) = ω₀(u, v)` gives `ω(Φ' u, Φ v) + ω(Φ u, Φ' v) = 0`.
  have hd (a : W) : HasDerivAt (fun s ↦ Φ s a) (deriv Φ t a) t := by
    simpa using hΦd.hasDerivAt.clm_apply (hasDerivAt_const t a)
  have h' := ω.toBilinForm.toContinuousBilinearMap.apply_add_apply_eq_zero_of_const (hd u) (hd v)
    fun s ↦ hΦω s u v
  rw [← hΦω t (frameLoop Φ S t u), ← hΦω t u (frameLoop Φ S t v), apply_frameLoop hΦ,
    apply_frameLoop hΦ]
  have h := hS (Φ t u) (Φ t v)
  simp only [LinearMap.toContinuousBilinearMap_apply] at h'
  simp only [map_sub, LinearMap.sub_apply]
  linarith

/-- The loop in a `C¹` path of invertible frames is continuous when `S` is. -/
theorem continuous_frameLoop [CompleteSpace W] (hΦ : ContDiff ℝ 1 Φ)
    (hinv : ∀ t, (Φ t).IsInvertible) (hS : Continuous S) : Continuous (frameLoop Φ S) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have hi : ContinuousAt (fun s ↦ (Φ s).inverse) t :=
    ((hinv t).contDiffAt_map_inverse (n := 0)).continuousAt.comp hΦ.continuous.continuousAt
  exact hi.clm_comp ((hS.clm_comp hΦ.continuous).sub (hΦ.continuous_deriv le_rfl)).continuousAt

/-- The loop in a periodic path of frames is periodic when `S` is. -/
theorem frameLoop_periodic {c : ℝ} (hΦ : Periodic Φ c) (hS : Periodic S c) :
    Periodic (frameLoop Φ S) c := fun t ↦ by
  simp only [frameLoop, hΦ t, hS t, hΦ.deriv t]

/-- **Nondegeneracy in a path of frames.** Let `Θ(t) : E → V` be a differentiable one-periodic
path of invertible frames from a finite-dimensional complex space, and let `S` be such that the only
one-periodic solution of `ζ' = S ζ` is zero. Then the loop operator `η ↦ η' - S' η` of the loop
`S'` of `S` in the frames `Θ` is invertible from `H¹` to `H⁰`: `η' = S' η` exactly when `ζ = Θ η`
solves `ζ' = S ζ`. -/
theorem isInvertible_loopOperator_frameLoop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {Θ : ℝ → E →L[ℝ] V}
    (hΘd : Differentiable ℝ Θ) (hΘp : Periodic Θ 1) (hΘinv : ∀ s, (Θ s).IsInvertible)
    (hnd : ∀ ζ : ℝ → V, Periodic ζ 1 → (∀ t, HasDerivAt ζ (S t (ζ t)) t) → ζ = 0)
    {S' : C(AddCircle (1 : ℝ), E →L[ℝ] E)} (hS' : ∀ t : ℝ, S' t = frameLoop Θ S t) :
    (CircleSobolev.loopOperator 1 S').IsInvertible := by
  refine (CircleSobolev.isInvertible_loopOperator_iff 1 S').2 fun η hη ↦ ?_
  -- `ζ = Θ η` solves `ζ' = S ζ`.
  set ζ : ℝ → V := fun s ↦ Θ s (η s) with hζ
  have hζd (s : ℝ) : HasDerivAt ζ (S s (ζ s)) s := by
    have h := (hΘd s).hasDerivAt.clm_apply (hη s)
    rwa [hS', apply_frameLoop (hΘinv s), add_sub_cancel] at h
  have hζp : Periodic ζ 1 := fun s ↦ by
    simp only [hζ, hΘp s, AddCircle.coe_add_period]
  have hζ0 : ζ = 0 := hnd ζ hζp hζd
  ext x
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact (hΘinv s).injective (by simpa [hζ] using congrFun hζ0 s)

section UnitaryFrame

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {J : ℝ → AlmostComplexStructure V}
  {S : ℝ → V →L[ℝ] V} {t : ℝ}

/-- **The asymptotic operator in the unitary frames.** For a family `J_t` of structures that are
compatible near `t` and differentiable at `t`, when the inner product is the metric of `J₀`, the
unitary frames `Ψ_t` of `J_t` carry the asymptotic operator of `J₀` and the loop
`S' = TauCeti.Floer.frameLoop Ψ S` to the asymptotic operator of `J` and `S` at `t`:
`A_{J, S} (Ψ η) = Ψ (A_{J₀, S'} η)`. -/
theorem asymptoticOperator_unitaryFrame_apply (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hJc : ∀ᶠ s in 𝓝 t, ω.Compatible (J s))
    (hJ : DifferentiableAt ℝ (fun s ↦ LinearMap.toContinuousLinearMap (J s).toLinearMap) t)
    {η : ℝ → V} (hη : DifferentiableAt ℝ η t) :
    asymptoticOperator J S (fun s ↦ ω.unitaryFrame (J s) (η s)) t =
      ω.unitaryFrame (J t)
        (asymptoticOperator (fun _ ↦ J₀) (frameLoop (fun s ↦ ω.unitaryFrame (J s)) S) η t) :=
  asymptoticOperator_frame_apply (hJ.unitaryFrame hJc) hη
    hJc.self_of_nhds.isInvertible_unitaryFrame fun v ↦ hJc.self_of_nhds.apply_unitaryFrame hg v

/-- The loop of an infinitesimally symplectic `S` in the unitary frames of a family of compatible
structures is infinitesimally symplectic at every `t` where the family is differentiable. -/
theorem frameLoop_unitaryFrame_apply_add_apply_eq_zero (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hJc : ∀ s, ω.Compatible (J s))
    (hJ : DifferentiableAt ℝ (fun s ↦ LinearMap.toContinuousLinearMap (J s).toLinearMap) t)
    (hS : ∀ u v, ω (S t u) v + ω u (S t v) = 0) (u v : V) :
    ω (frameLoop (fun s ↦ ω.unitaryFrame (J s)) S t u) v +
      ω u (frameLoop (fun s ↦ ω.unitaryFrame (J s)) S t v) = 0 :=
  frameLoop_apply_add_apply_eq_zero (hJ.unitaryFrame (.of_forall hJc))
    (hJc t).isInvertible_unitaryFrame (fun s ↦ (hJc s).apply_unitaryFrame_unitaryFrame hg) hS u v

/-- **The loop in the frames `Ψ_t Φ` is infinitesimally symplectic for `Im ⟪·, ·⟫`.** Let the
inner product of `V` be the metric `ω(·, J₀ ·)`, let `Φ : F ≃ V` satisfy
`ω (Φ x) (Φ y) = Im ⟪x, y⟫`, and let `Ψ_s` be the unitary frames of a family `J_s` of compatible
structures, differentiable at `t`. If `S_t` is infinitesimally `ω`-symplectic, then the loop `S'_t`
of `S` in the frames `Ψ_s Φ` is infinitesimally symplectic for `Im ⟪·, ·⟫`. -/
theorem im_inner_frameLoop_add_im_inner_frameLoop_eq_zero {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] {Φ : F ≃L[ℝ] V} (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hΦω : ∀ x y, ω (Φ x) (Φ y) = (inner ℂ x y).im) (hJc : ∀ s, ω.Compatible (J s))
    (hJ : DifferentiableAt ℝ (fun s ↦ LinearMap.toContinuousLinearMap (J s).toLinearMap) t)
    (hS : ∀ u v, ω (S t u) v + ω u (S t v) = 0) (u v : F) :
    (inner ℂ (frameLoop (fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V)) S t u) v).im +
      (inner ℂ u (frameLoop (fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V)) S t v)).im =
      0 := by
  -- Pull `ω` back to `F` along `Φ`; it is `Im ⟪·, ·⟫`, and every `Ψ_s Φ` carries it to `ω`.
  let ω₀ : SymplecticForm F := ω.transport (Φ.symm : V ≃ₗ[ℝ] F)
  have hω₀ (x y : F) : ω₀ x y = (inner ℂ x y).im := by
    simpa [ω₀, SymplecticForm.transport_apply] using hΦω x y
  have h := frameLoop_apply_add_apply_eq_zero (ω₀ := ω₀)
    (Φ := fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V))
    ((hJ.unitaryFrame (.of_forall hJc)).clm_comp (differentiableAt_const _))
    ((hJc t).isInvertible_unitaryFrame.comp ⟨Φ, rfl⟩)
    (fun s x y ↦ by simp [(hJc s).apply_unitaryFrame_unitaryFrame hg, hΦω, hω₀]) hS u v
  rwa [hω₀, hω₀] at h

/-- The loop of a continuous `S` in the unitary frames of a `C¹` family of compatible structures
is continuous. -/
theorem continuous_frameLoop_unitaryFrame (hJc : ∀ s, ω.Compatible (J s))
    (hJ : ContDiff ℝ 1 fun s ↦ LinearMap.toContinuousLinearMap (J s).toLinearMap)
    (hS : Continuous S) : Continuous (frameLoop (fun s ↦ ω.unitaryFrame (J s)) S) :=
  have := FiniteDimensional.completeSpace ℝ V
  continuous_frameLoop (hJ.unitaryFrame hJc) (fun s ↦ (hJc s).isInvertible_unitaryFrame) hS

end UnitaryFrame

end TauCeti.Floer
