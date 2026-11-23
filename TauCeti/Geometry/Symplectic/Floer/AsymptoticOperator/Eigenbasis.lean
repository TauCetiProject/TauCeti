/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Frame
import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# The eigenbasis of the asymptotic operator for a loop of compatible structures

Along a one-periodic Hamiltonian orbit the asymptotic operator is `A ζ = J_t (ζ' - S_t ζ)`
(`TauCeti.Floer.asymptoticOperator`), for a loop `J_t` of almost complex structures and the
linearized Hamiltonian vector field `S_t`. Its spectral theory is known for the constant structure
`i` of a finite-dimensional complex inner product space `F`
(`TauCeti.CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`): at a nondegenerate loop
it has a real orthonormal eigenbasis with eigenvalues bounded away from `0`. This file transfers
that theorem to a `C¹` loop of `ω`-compatible structures `J_t` on a real inner product space `V`
whose inner product is the metric `ω(·, J₀ ·)` of a reference structure `J₀`.

The transfer is through a path of frames `Θ_t = Ψ_t Φ : F → V`. Here `Φ : F ≃ V` is a frame of
the reference structure, with `Φ (i x) = J₀ (Φ x)` and `ω (Φ x) (Φ y) = Im ⟪x, y⟫`, and `Ψ_t` is
the unitary frame of `J_t` (`TauCeti.SymplecticForm.unitaryFrame`), with `J_t Ψ_t = Ψ_t J₀`. Such a
`Φ` exists with `F = ℂⁿ`: `TauCeti.AlmostComplexStructure.exists_linearIsometryEquiv_euclideanSpace`
gives a real linear isometry turning `i` into `J₀`, and for it
`TauCeti.SymplecticForm.apply_map_map_eq_im_inner` identifies `ω` with `Im ⟪·, ·⟫`. In the frames
`Θ_t` the asymptotic operator of `J_t` and `S` becomes the asymptotic operator of `i` and the loop
`S'_t = Θ_t⁻¹ (S_t Θ_t - Θ_t')` (`TauCeti.Floer.frameLoop`,
`TauCeti.Floer.asymptoticOperator_frame_apply`), so the theorem for `F` applies once `S'` meets its
hypotheses:

* `S'_t` is infinitesimally symplectic for `Im ⟪·, ·⟫` when `S_t` is for `ω`
  (`TauCeti.Floer.im_inner_frameLoop_add_im_inner_frameLoop_eq_zero`);
* the loop operator `η ↦ η' - S' η` on `H¹` is invertible when the orbit is nondegenerate, that is,
  when the only one-periodic loop in the kernel of `A`, a solution of `ζ' = S ζ`
  (`TauCeti.Floer.asymptoticOperator_eq_zero_iff`), is zero
  (`TauCeti.Floer.isInvertible_loopOperator_frameLoop`): `η' = S' η` exactly when `ζ = Θ η` solves
  `ζ' = S ζ`.

The result (`TauCeti.Floer.exists_hilbertBasis_asymptoticOperator_eq_smul`) is a Hilbert basis
`(b_i)` of `H⁰(F)` and eigenvalues `λ_i` with `|λ_i| ≥ c > 0`. The continuous representatives
`η_i` of the `b_i` give classical eigenfunctions `ζ_i(t) = Θ_t (η_i(t))` of the actual operator,
`A ζ_i = λ_i ζ_i`. The frames are unitary: `Φ` carries `Re ⟪x, y⟫ = Im ⟪x, i y⟫` to
`ω (Φ x) (J₀ (Φ y))`, the inner product of `V`, and `Ψ_t` carries the inner product to the metric
`g_t = ω(·, J_t ·)` (`TauCeti.SymplecticForm.Compatible.apply_unitaryFrame_apply_unitaryFrame`),
so `Θ_t` carries `Re ⟪·, ·⟫` to `g_t`.
With Parseval's identity (`TauCeti.CircleSobolev.real_inner_ofContinuousMap`), the orthonormality
of the `b_i` is therefore orthonormality of the `ζ_i` for the mean of `g_t(·, ·)` over the circle,
the pairing for which `A` is symmetric
(`TauCeti.Floer.integral_associatedBilinForm_asymptoticOperator_comm`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the asymptotic operator in a unitary trivialization and its
  spectrum).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Section 3.1 (unitary trivializations of real Cauchy–Riemann operators).
-/

public section

noncomputable section

open Complex Function
open scoped RealInnerProductSpace

universe u

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {J : ℝ → AlmostComplexStructure V}
  {S : ℝ → V →L[ℝ] V} {Φ : F ≃L[ℝ] V}

/-- **The eigenbasis of the asymptotic operator of a loop of compatible structures.** Let the inner
product of `V` be the metric `ω(·, J₀ ·)`, and let `Φ : F ≃ V` be a frame of `J₀` from a
finite-dimensional complex inner product space, `Φ (i x) = J₀ (Φ x)` and
`ω (Φ x) (Φ y) = Im ⟪x, y⟫`. Let `J_t` be a `C¹` one-periodic family of `ω`-compatible structures
with unitary frames `Ψ_t`, and `S` a continuous one-periodic loop of infinitesimally
`ω`-symplectic maps, nondegenerate in the sense that the only differentiable one-periodic loop in
the kernel of `A ζ = J_t (ζ' - S_t ζ)` is zero. Then `H⁰(F)` has a Hilbert basis `b` with
eigenvalues `λ_i`, `|λ_i| ≥ c > 0`, such that each `b_i` lies in `H¹(F)` and its continuous
representative `η_i` gives a differentiable one-periodic eigenfunction `ζ_i(t) = Ψ_t (Φ (η_i(t)))`
of the asymptotic operator: `A ζ_i = λ_i ζ_i`. -/
theorem exists_hilbertBasis_asymptoticOperator_eq_smul [FiniteDimensional ℂ F]
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hΦ : ∀ x, Φ (I • x) = J₀ (Φ x))
    (hΦω : ∀ x y, ω (Φ x) (Φ y) = (inner ℂ x y).im) (hJc : ∀ s, ω.Compatible (J s))
    (hJ : ContDiff ℝ 1 fun s ↦ LinearMap.toContinuousLinearMap (J s).toLinearMap)
    (hJp : Periodic J 1) (hSc : Continuous S) (hSp : Periodic S 1)
    (hS : ∀ t u v, ω (S t u) v + ω u (S t v) = 0)
    (hnd : ∀ ζ : ℝ → V, Differentiable ℝ ζ → Periodic ζ 1 →
      (∀ t, asymptoticOperator J S ζ t = 0) → ζ = 0) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ (CircleSobolev 0 F)) (a : ι → CircleSobolev 1 F)
      (lam : ι → ℝ) (c : ℝ), 0 < c ∧ ∀ i, CircleSobolev.inclusion zero_le_one (a i) = b i ∧
        c ≤ |lam i| ∧
        Differentiable ℝ (fun s : ℝ ↦
          ω.unitaryFrame (J s) (Φ (CircleSobolev.toContinuousMap 1 (by norm_num) (a i) s))) ∧
        ∀ t : ℝ, asymptoticOperator J S (fun s : ℝ ↦
          ω.unitaryFrame (J s) (Φ (CircleSobolev.toContinuousMap 1 (by norm_num) (a i) s))) t =
            lam i • ω.unitaryFrame (J t)
              (Φ (CircleSobolev.toContinuousMap 1 (by norm_num) (a i) t)) := by
  have := FiniteDimensional.completeSpace ℂ F
  set Θ : ℝ → F →L[ℝ] V := fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V) with hΘ
  have hΘ1 : ContDiff ℝ 1 Θ := (hJ.unitaryFrame hJc).clm_comp contDiff_const
  have hΘinv (s : ℝ) : (Θ s).IsInvertible := (hJc s).isInvertible_unitaryFrame.comp ⟨Φ, rfl⟩
  have hΘp : Periodic Θ 1 := fun s ↦ by simp only [hΘ, hJp s]
  -- The loop `S'` of `S` in the frames `Θ`, as a continuous loop on the circle.
  have hper := frameLoop_periodic hΘp hSp
  let S' : C(AddCircle (1 : ℝ), F →L[ℝ] F) :=
    ⟨hper.lift, continuous_coinduced_dom.2 (continuous_frameLoop hΘ1 hΘinv hSc)⟩
  have hS' (t : ℝ) : S' t = frameLoop Θ S t := hper.lift_coe t
  have hSs : ∀ t v w, (inner ℂ (S' t v) w).im + (inner ℂ v (S' t w)).im = 0 := by
    intro x v w
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    have h := im_inner_frameLoop_add_im_inner_frameLoop_eq_zero hg hΦω hJc
      (hJ.differentiable one_ne_zero t) (hS t) v w
    rwa [← hS' t] at h
  obtain ⟨ι, b, a, lam, c, hc, hab⟩ := CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul
    1 S' hSs (isInvertible_loopOperator_frameLoop (hΘ1.differentiable one_ne_zero) hΘp hΘinv
      (fun ζ hζp hζd ↦ hnd ζ (fun t ↦ (hζd t).differentiableAt) hζp fun t ↦
        (asymptoticOperator_eq_zero_iff (hζd t).differentiableAt).2 (hζd t)) hS')
  refine ⟨ι, b, a, lam, c, hc, fun i ↦ ?_⟩
  obtain ⟨hai, hlam, hev⟩ := hab i
  -- The continuous representative `η` of `a i` solves `η' = S' η - λ i η` classically.
  set η : ℝ → F := fun s ↦ CircleSobolev.toContinuousMap 1 (by norm_num) (a i) s with hη
  have hηd (t : ℝ) : HasDerivAt η (frameLoop Θ S t (η t) - lam i • I • η t) t := by
    rw [← hS']
    exact (CircleSobolev.I_smul_loopOperator_eq_smul_iff 1 S' (a i) (lam i)).1
      (hai ▸ hev) t
  have hζd : Differentiable ℝ fun s ↦ Θ s (η s) := fun t ↦
    ((hΘ1.differentiable one_ne_zero t).hasDerivAt.clm_apply (hηd t)).differentiableAt
  refine ⟨hai, hlam, hζd, fun t ↦ ?_⟩
  -- Multiplication by `i` on `F`, the structure that `Θ_t` carries to `J_t`.
  let JF := AlmostComplexStructure.ofComplexModule F
  have hJF (v : F) : J t (Θ t v) = Θ t (JF v) := by
    simp [hΘ, JF, (hJc t).apply_unitaryFrame hg, hΦ]
  have h := asymptoticOperator_frame_apply (J₀ := JF) (S := S)
    (hΘ1.differentiable one_ne_zero t) (hηd t).differentiableAt (hΘinv t) hJF
  -- In the frame, `A_{i, S'} η = i (η' - S' η) = i (-λ i η) = λ η`.
  have hA : asymptoticOperator (fun _ ↦ JF) (frameLoop Θ S) η t = lam i • η t := by
    rw [asymptoticOperator_def, (hηd t).deriv]
    simp [JF, smul_smul, smul_comm (lam i) I]
  rw [hA] at h
  simpa [hΘ, hη] using h

end TauCeti.Floer
