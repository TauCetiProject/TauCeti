/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Diffeomorphic lifts to symplectizations

The lift of a diffeomorphism `F` with conformal multiplier `f` is
`(t, x) ↦ (t - log f(x), F(x))`. We bundle the existing `TauCeti.symplectizationLift`
as a diffeomorphism and prove its identity, composition and inverse laws. For a positive
multiplier with `F*α' = f α`, the lift preserves the tautological one-form `eᵗ α`,
and hence its exterior derivative.

If `α` vanishes nowhere, preservation of the tautological form determines this lift uniquely
among all smooth maps covering `F`. In particular, no arbitrary translation in `t` is allowed.
Homogeneity need not be assumed in the uniqueness theorem; it follows from the formula.
Contactness and finite dimensionality are unnecessary for these form identities.

The form-preservation calculation extends
`TauCeti.SmoothForm.mpullback_symplectizationLift_symplectization` to an arbitrary map
covering `F`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (symplectization and lifted contactomorphisms).
-/

public section

noncomputable section

open scoped Manifold ContDiff

open TauCeti

variable {E H M E' H' N E'' H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P] [ChartedSpace H'' P]

namespace Diffeomorph

/-- The diffeomorphism `(t, x) ↦ (t - log f(x), e(x))`.
For a positive conformal multiplier this is the lift to symplectizations. -/
def symplectizationLift (e : M ≃ₘ⟮I, J⟯ N) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, f x ≠ 0) :
    (ℝ × M) ≃ₘ⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod J⟯ (ℝ × N) where
  toFun := TauCeti.symplectizationLift e f
  invFun p := (p.1 + Real.log (f (e.symm p.2)), e.symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := contMDiff_symplectizationLift e.contMDiff hf hf₀
  contMDiff_invFun :=
    (contMDiff_fst.add (((hf.log hf₀).comp e.symm.contMDiff).comp contMDiff_snd)).prodMk
      (e.symm.contMDiff.comp contMDiff_snd)

/-- Evaluation of the lifted diffeomorphism. -/
@[simp]
theorem symplectizationLift_apply (e : M ≃ₘ⟮I, J⟯ N) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, f x ≠ 0) (p : ℝ × M) :
    e.symplectizationLift f hf hf₀ p = (p.1 - Real.log (f p.2), e p.2) :=
  TauCeti.symplectizationLift_apply e f p

/-- Evaluation of the inverse lift. -/
@[simp]
theorem symplectizationLift_symm_apply (e : M ≃ₘ⟮I, J⟯ N) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, f x ≠ 0) (p : ℝ × N) :
    (e.symplectizationLift f hf hf₀).symm p =
      (p.1 + Real.log (f (e.symm p.2)), e.symm p.2) :=
  (rfl)

/-- The lift of the identity with multiplier one is the identity. -/
@[simp]
theorem symplectizationLift_refl :
    (Diffeomorph.refl I M ∞).symplectizationLift (fun _ ↦ 1) contMDiff_const
      (fun _ ↦ one_ne_zero) = Diffeomorph.refl (𝓘(ℝ).prod I) (ℝ × M) ∞ := by
  ext p <;> simp

/-- Conformal multipliers multiply under composition, with the second pulled back by the first
base diffeomorphism. -/
theorem symplectizationLift_trans (e : M ≃ₘ⟮I, J⟯ N) (e' : N ≃ₘ⟮J, K⟯ P)
    {f : M → ℝ} {g : N → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hg : ContMDiff J 𝓘(ℝ) ∞ g) (hf₀ : ∀ x, f x ≠ 0) (hg₀ : ∀ y, g y ≠ 0) :
    (e.symplectizationLift f hf hf₀).trans (e'.symplectizationLift g hg hg₀) =
      (e.trans e').symplectizationLift (fun x ↦ f x * g (e x))
        (by exact hf.mul (hg.comp e.contMDiff)) (fun x ↦ mul_ne_zero (hf₀ x) (hg₀ (e x))) := by
  ext p <;> simp [Real.log_mul (hf₀ p.2) (hg₀ (e p.2)), sub_sub]

/-- The inverse lift has multiplier `1 / f` transported by the inverse base map. -/
theorem symplectizationLift_symm (e : M ≃ₘ⟮I, J⟯ N) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, f x ≠ 0) :
    (e.symplectizationLift f hf hf₀).symm =
      e.symm.symplectizationLift (fun y ↦ (f (e.symm y))⁻¹)
        ((hf.comp e.symm.contMDiff).inv₀ fun y ↦ hf₀ (e.symm y))
        (fun y ↦ inv_ne_zero (hf₀ (e.symm y))) := by
  ext p <;> simp

end Diffeomorph

namespace TauCeti.SmoothForm

variable [IsManifold I ∞ M] [IsManifold J ∞ N]
  {α : SmoothForm I M ℝ 1} {β : SmoothForm J N ℝ 1}

/-- Pulling back a symplectization form along a map covering `F` depends on its real component
only through its exponential. No derivative of that component occurs. -/
theorem mpullback_symplectization_apply_of_snd_eq {F : M → N}
    (hF : ContMDiff I J ∞ F) {f : M → ℝ}
    (hα : ∀ x, (mpullback F hF β).1 x = f x • α.1 x)
    {Ψ : ℝ × M → ℝ × N} (hΨ : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) ∞ Ψ)
    (hcover : ∀ p, (Ψ p).2 = F p.2) (p : ℝ × M)
    (v : TangentSpace (𝓘(ℝ).prod I) p) :
    (mpullback Ψ hΨ β.symplectization).1 p ![v] =
      Real.exp (Ψ p).1 * f p.2 * α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2] := by
  have hcomp : TauCeti.mpullback (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) Ψ
      (mpullback Prod.snd contMDiff_snd β).1 =
        TauCeti.mpullback (𝓘(ℝ).prod I) I Prod.snd (mpullback F hF β).1 := by
    rw [coe_mpullback, coe_mpullback,
      ← TauCeti.mpullback_comp (hΨ.mdifferentiable (by simp)) mdifferentiable_snd,
      ← TauCeti.mpullback_comp mdifferentiable_snd (hF.mdifferentiable (by simp))]
    exact congrArg (fun G ↦ TauCeti.mpullback (𝓘(ℝ).prod I) J G β.1) (funext hcover)
  have h := congrArg (fun φ ↦ φ p ![v]) hcomp
  rw [← coe_mpullback Prod.snd contMDiff_snd, mpullback_snd_apply, hα p.2] at h
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    Matrix.vec_single_eq_const] at h
  simp only [coe_mpullback, TauCeti.mpullback_apply, coe_symplectization,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h ⊢
  simp only [Matrix.vec_single_eq_const] at h ⊢
  rw [h]
  ring

/-- **Uniqueness of the tautological-form-preserving lift.** For a nowhere vanishing `α` and
`F*β = f α` with `f > 0`, every smooth map covering `F` and preserving `eᵗ α` is the canonical
lift. Neither invertibility of `F` nor homogeneity of the map is assumed. -/
theorem eq_symplectizationLift_of_mpullback_eq {F : M → N}
    (hF : ContMDiff I J ∞ F) {f : M → ℝ} (hf₀ : ∀ x, 0 < f x)
    (hα₀ : ∀ x, α.1 x ≠ 0)
    (hα : ∀ x, (mpullback F hF β).1 x = f x • α.1 x)
    {Ψ : ℝ × M → ℝ × N} (hΨ : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) ∞ Ψ)
    (hcover : ∀ p, (Ψ p).2 = F p.2)
    (hpres : mpullback Ψ hΨ β.symplectization = α.symplectization) :
    Ψ = TauCeti.symplectizationLift F f := by
  funext p
  obtain ⟨u, hu⟩ : ∃ u : TangentSpace I p.2, α.1 p.2 ![u] ≠ 0 := by
    by_contra! h
    apply hα₀ p.2
    ext v
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    rw [hv]
    exact h (v 0)
  let v : TangentSpace (𝓘(ℝ).prod I) p :=
    (Manifold.tangentSpaceProdEquiv p).symm (0, u)
  have h := mpullback_symplectization_apply_of_snd_eq hF hα hΨ hcover p v
  rw [hpres, symplectization_apply] at h
  simp only [v, ContinuousLinearEquiv.apply_symm_apply] at h
  have hexp : Real.exp (Ψ p).1 * f p.2 = Real.exp p.1 := mul_right_cancel₀ hu h.symm
  have ht : (Ψ p).1 = p.1 - Real.log (f p.2) := by
    apply Real.exp_injective
    rw [Real.exp_sub, Real.exp_log (hf₀ p.2), ← hexp]
    exact (mul_div_cancel_right₀ _ (hf₀ p.2).ne').symm
  rw [TauCeti.symplectizationLift_apply]
  exact Prod.ext ht (hcover p)

end TauCeti.SmoothForm

namespace Diffeomorph

variable [IsManifold I ∞ M] [IsManifold J ∞ N]
  {α : SmoothForm I M ℝ 1} {β : SmoothForm J N ℝ 1}

open TauCeti.SmoothForm

/-- The lifted diffeomorphism preserves the tautological one-form for a positive conformal
multiplier. -/
theorem mpullback_symplectizationLift_symplectization (e : M ≃ₘ⟮I, J⟯ N) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, 0 < f x)
    (hα : ∀ x, (mpullback e e.contMDiff β).1 x = f x • α.1 x) :
    mpullback (e.symplectizationLift f hf fun x ↦ (hf₀ x).ne')
      (e.symplectizationLift f hf fun x ↦ (hf₀ x).ne').contMDiff β.symplectization =
        α.symplectization :=
  TauCeti.SmoothForm.mpullback_symplectizationLift_symplectization e.contMDiff hf hf₀ hα

/-- Consequently the lifted diffeomorphism preserves `d(eᵗ α)`, the symplectic form when `α`
is contact. -/
theorem mpullback_symplectizationLift_mextDerivₗ_symplectization (e : M ≃ₘ⟮I, J⟯ N)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, 0 < f x)
    (hα : ∀ x, (mpullback e e.contMDiff β).1 x = f x • α.1 x) :
    mpullback (e.symplectizationLift f hf fun x ↦ (hf₀ x).ne')
      (e.symplectizationLift f hf fun x ↦ (hf₀ x).ne').contMDiff
        (mextDerivₗ (𝓘(ℝ).prod J) 1 β.symplectization) =
      mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization := by
  rw [← mextDerivₗ_mpullback, mpullback_symplectizationLift_symplectization e hf hf₀ hα]

/-- **Existence and uniqueness of the lifted diffeomorphism.** A diffeomorphism pulling back
`β` to a positive multiple of the nowhere vanishing form `α` has exactly one lift preserving
the tautological forms. -/
theorem existsUnique_mpullback_symplectization_eq (e : M ≃ₘ⟮I, J⟯ N) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, 0 < f x) (hα₀ : ∀ x, α.1 x ≠ 0)
    (hα : ∀ x, (mpullback e e.contMDiff β).1 x = f x • α.1 x) :
    ∃! Ψ : (ℝ × M) ≃ₘ⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod J⟯ (ℝ × N),
      (∀ p, (Ψ p).2 = e p.2) ∧ mpullback Ψ Ψ.contMDiff β.symplectization =
        α.symplectization := by
  refine ⟨e.symplectizationLift f hf (fun x ↦ (hf₀ x).ne'),
    ⟨fun p ↦ by simp, mpullback_symplectizationLift_symplectization e hf hf₀ hα⟩, ?_⟩
  intro Ψ hΨ
  have h := eq_symplectizationLift_of_mpullback_eq e.contMDiff hf₀ hα₀ hα
    Ψ.contMDiff hΨ.1 hΨ.2
  apply Diffeomorph.ext
  intro p
  simpa only [symplectizationLift_apply, TauCeti.symplectizationLift_apply] using congrFun h p

end Diffeomorph
