/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Frame

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
  when the only one-periodic loop in the kernel of `A` is zero
  (`TauCeti.Floer.isInvertible_loopOperator_frameLoop`): `η' = S' η` exactly when `ζ = Θ η` solves
  `ζ' = S ζ`.

The result (`TauCeti.Floer.exists_hilbertBasis_asymptoticOperator_eq_smul`) is a Hilbert basis
`(b_i)` of `H⁰(F)` and eigenvalues `λ_i` with `|λ_i| ≥ c > 0`. The continuous representatives
`η_i` of the `b_i` give classical eigenfunctions `ζ_i(t) = Θ_t (η_i(t))` of the actual operator,
`A ζ_i = λ_i ζ_i`. The frames are unitary: `Θ_t` carries `Re ⟪·, ·⟫` to the metric
`g_t = ω(·, J_t ·)`
(`TauCeti.SymplecticForm.Compatible.apply_unitaryFrame_apply_unitaryFrame_eq_re_inner`).
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

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ω : SymplecticForm V} {J₀ J : AlmostComplexStructure V} {Φ : F ≃L[ℝ] V}

/-- **The frames `Ψ Φ` are unitary.** Let the inner product of `V` be the metric `ω(·, J₀ ·)` and
let `Φ : F ≃ V` satisfy `Φ (i x) = J₀ (Φ x)` and `ω (Φ x) (Φ y) = Im ⟪x, y⟫`. Then the unitary frame
`Ψ` of an `ω`-compatible `J` carries the real part of the Hermitian product of `F` to the metric
`ω(·, J ·)`: `ω (Ψ (Φ x)) (J (Ψ (Φ y))) = Re ⟪x, y⟫`. -/
theorem Compatible.apply_unitaryFrame_apply_unitaryFrame_eq_re_inner (hJ : ω.Compatible J)
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hΦ : ∀ x, Φ (I • x) = J₀ (Φ x))
    (hΦω : ∀ x y, ω (Φ x) (Φ y) = (inner ℂ x y).im) (x y : F) :
    ω (ω.unitaryFrame J (Φ x)) (J (ω.unitaryFrame J (Φ y))) = (inner ℂ x y).re := by
  rw [hJ.apply_unitaryFrame hg, ← hΦ, hJ.apply_unitaryFrame_unitaryFrame hg, hΦω,
    inner_smul_right]
  simp

end TauCeti.SymplecticForm

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {J : ℝ → AlmostComplexStructure V}
  {S : ℝ → V →L[ℝ] V} {Φ : F ≃L[ℝ] V}

/-- **The loop in the frames `Ψ_t Φ` is infinitesimally symplectic for `Im ⟪·, ·⟫`.** Let the
inner product of `V` be the metric `ω(·, J₀ ·)`, let `Φ : F ≃ V` satisfy
`ω (Φ x) (Φ y) = Im ⟪x, y⟫`, and let `Ψ_s` be the unitary frames of a family `J_s` of compatible
structures, differentiable at `t`. If `S_t` is infinitesimally `ω`-symplectic, then the loop `S'_t`
of `S` in the frames `Ψ_s Φ` is infinitesimally symplectic for `Im ⟪·, ·⟫`. -/
theorem im_inner_frameLoop_add_im_inner_frameLoop_eq_zero (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hΦω : ∀ x y, ω (Φ x) (Φ y) = (inner ℂ x y).im) (hJc : ∀ s, ω.Compatible (J s)) {t : ℝ}
    (hJ : DifferentiableAt ℝ (fun s ↦ LinearMap.toContinuousLinearMap (J s).toLinearMap) t)
    (hS : ∀ u v, ω (S t u) v + ω u (S t v) = 0) (u v : F) :
    (inner ℂ (frameLoop (fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V)) S t u) v).im +
      (inner ℂ u (frameLoop (fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V)) S t v)).im =
      0 := by
  -- Pull `ω` back to `F` along `Φ`; it is `Im ⟪·, ·⟫`, and every `Ψ_s Φ` carries it to `ω`.
  let ω₀ : SymplecticForm F := ω.transport (Φ.symm : V ≃ₗ[ℝ] F)
  have hω₀ (x y : F) : ω₀ x y = (inner ℂ x y).im := hΦω x y
  have h := frameLoop_apply_add_apply_eq_zero (ω₀ := ω₀)
    (Φ := fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V))
    ((hJ.unitaryFrame (.of_forall hJc)).clm_comp (differentiableAt_const _))
    ((hJc t).isInvertible_unitaryFrame.comp ⟨Φ, rfl⟩)
    (fun s x y ↦ by simp [(hJc s).apply_unitaryFrame_unitaryFrame hg, hΦω, hω₀]) hS u v
  rwa [hω₀, hω₀] at h

/-- **Nondegeneracy in the frames `Ψ_t Φ`.** Let `J_t` be a `C¹` one-periodic family of compatible
structures and `S` a continuous one-periodic loop such that the only differentiable one-periodic
loop in the kernel of the asymptotic operator `A ζ = J_t (ζ' - S_t ζ)` is zero. Then the loop
operator `η ↦ η' - S' η` of the loop `S'` of `S` in the frames `Ψ_t Φ` is invertible from `H¹` to
`H⁰`. -/
theorem isInvertible_loopOperator_frameLoop [FiniteDimensional ℂ F] (hJc : ∀ s, ω.Compatible (J s))
    (hJ : ContDiff ℝ 1 fun s ↦ LinearMap.toContinuousLinearMap (J s).toLinearMap)
    (hJp : Periodic J 1)
    (hnd : ∀ ζ : ℝ → V, Differentiable ℝ ζ → Periodic ζ 1 →
      (∀ t, asymptoticOperator J S ζ t = 0) → ζ = 0)
    {S' : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS' : ∀ t : ℝ, S' t = frameLoop (fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V)) S t) :
    (CircleSobolev.loopOperator 1 S').IsInvertible := by
  set Θ : ℝ → F →L[ℝ] V := fun s ↦ ω.unitaryFrame (J s) ∘L (Φ : F →L[ℝ] V) with hΘ
  have hΘd : Differentiable ℝ Θ :=
    ((hJ.unitaryFrame hJc).differentiable one_ne_zero).clm_comp (differentiable_const _)
  have hΘinv (s : ℝ) : (Θ s).IsInvertible := (hJc s).isInvertible_unitaryFrame.comp ⟨Φ, rfl⟩
  refine (CircleSobolev.isInvertible_loopOperator_iff 1 S').2 fun η hη ↦ ?_
  -- `ζ = Θ η` solves `ζ' = S ζ`, so it lies in the kernel of `A`.
  set ζ : ℝ → V := fun s ↦ Θ s (η s) with hζ
  have hζd (s : ℝ) : HasDerivAt ζ (S s (ζ s)) s := by
    have h := (hΘd s).hasDerivAt.clm_apply (hη s)
    rwa [hS', apply_frameLoop (hΘinv s), add_sub_cancel] at h
  have hζp : Periodic ζ 1 := fun s ↦ by
    simp only [hζ, hΘ, hJp s, AddCircle.coe_add_period]
  have hζ0 : ζ = 0 := hnd ζ (fun s ↦ (hζd s).differentiableAt) hζp fun s ↦
    (asymptoticOperator_eq_zero_iff (hζd s).differentiableAt).2 (hζd s)
  ext x
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact (hΘinv s).injective (by simpa [hζ] using congrFun hζ0 s)

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
    rw [show ((t : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) from rfl, hS' t]
    exact im_inner_frameLoop_add_im_inner_frameLoop_eq_zero hg hΦω hJc
      (hJ.differentiable one_ne_zero t) (hS t) v w
  obtain ⟨ι, b, a, lam, c, hc, hab⟩ := CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul
    1 S' hSs (isInvertible_loopOperator_frameLoop hJc hJ hJp hnd hS')
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
  let JF : AlmostComplexStructure F :=
    ⟨(I • LinearMap.id : F →ₗ[ℂ] F).restrictScalars ℝ, by ext v; simp [smul_smul]⟩
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
