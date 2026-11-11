/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# Reeb fields of energy hypersurfaces

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M`, let `θ` be a one-form
with `dθ = -σ`, and let `ι : S → M` be a hypersurface on which a function `K` is constant, in the
sense that the tangent image of `ι` at `s` is exactly the kernel of `dK`. If the restriction
`ι^* θ` is a contact form, then its Reeb vector field is a rescaling of the Hamiltonian vector
field `X_K` of `K`:

`dι (R_(ι^* θ)) = θ(X_K)⁻¹ • X_K`

(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback`); the contact
condition forces `θ(X_K)` not to vanish
(`TauCeti.SmoothTwoForm.IsNondegenerate.apply_hamiltonianVectorField_ne_zero`). Indeed `X_K` is
tangent to the level, since `dK(X_K) = σ(X_K, X_K) = 0`, and for every vector `w` tangent to the
level, `dθ(X_K, w) = -σ(X_K, w) = -dK(w) = 0`. So the lift of `X_K / θ(X_K)` satisfies the two
Reeb equations, which determine the Reeb vector field.

This is how Reeb flows on hypersurfaces of contact type are reparametrized Hamiltonian flows: on
the unit cosphere bundle of a Riemannian manifold, with `θ` the Liouville form and `K` the kinetic
energy, the factor `θ(X_K)` is identically `1`, and the Reeb flow is the cogeodesic flow.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their characteristic line fields).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.4 (Reeb vector fields).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J 2 S]
  {σ : SmoothTwoForm I M}

/-- Exterior-derivative identity: if `dθ = -σ` at `x`, then
`dθ(a • X_K, u) = -σ(a • X_K, u) = -a dK(u)`. -/
private theorem mextDeriv_smul_hamiltonianVectorField (hσ : σ.IsNondegenerate)
    {θ : SmoothForm I M ℝ 1} {K : M → ℝ} {x : M} (hdθ : mextDeriv θ.1 x = -σ.1 x) (a : ℝ)
    (u : TangentSpace I x) :
    mextDeriv θ.1 x ![a • σ.hamiltonianVectorField K x, u] = -(a * mvfderiv I K x u) := by
  rw [hdθ, ContinuousAlternatingMap.neg_apply, ← SmoothBundleForm.eval₂_apply,
    SmoothBundleForm.eval₂_smul_left, hσ.eval₂_hamiltonianVectorField, smul_eq_mul]

omit [IsManifold J 2 S] in
/-- The Hamiltonian vector field is tangent to the level, since `dK(X_K) = σ(X_K, X_K) = 0`. -/
private theorem smul_hamiltonianVectorField_mem_range (hσ : σ.IsNondegenerate) {ι : S → M}
    {K : M → ℝ} {s : S} (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) (a : ℝ) :
    a • σ.hamiltonianVectorField K (ι s) ∈ (mfderiv J I ι s).range := by
  rw [hK, LinearMap.mem_ker, map_smul, ContinuousLinearMap.coe_coe,
    (hσ.isHamiltonianVectorField_hamiltonianVectorField K).mvfderiv_apply_self (ι s), smul_zero]

/-- **On a hypersurface of contact type, `θ(X_K)` does not vanish.** Let `σ` be a nondegenerate
two-form and `θ` a one-form with `dθ = -σ` at `ι s`, and suppose that the tangent image of
`ι : S → M` at `s` is the kernel of `dK`. If the restriction `ι^* θ` is a contact form, then
`θ(X_K) ≠ 0` at `ι s`. -/
theorem IsNondegenerate.apply_hamiltonianVectorField_ne_zero (hσ : σ.IsNondegenerate)
    {θ : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm) {K : M → ℝ} {s : S}
    (hdθ : mextDeriv θ.1 (ι s) = -σ.1 (ι s))
    (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    θ.1 (ι s) ![σ.hamiltonianVectorField K (ι s)] ≠ 0 := by
  have := SmoothForm.finiteDimensional_of_isContactForm_mpullback hι hα s
  have hdK (w : TangentSpace J s) : mvfderiv I K (ι s) (mfderiv J I ι s w) = 0 :=
    (LinearMap.exact_iff.2 hK.symm).apply_apply_eq_zero w
  -- Suppose `θ(X_K) = 0`. A lift `v` of `X_K` lies in `ker α` and is `dα`-orthogonal to
  -- everything, so `v = 0`.
  intro hc
  obtain ⟨v, hv⟩ := smul_hamiltonianVectorField_mem_range hσ hK 1
  rw [one_smul, ContinuousLinearMap.coe_coe] at hv
  have hv0 : v = 0 := by
    refine (SmoothForm.isContactForm_iff.1 hα s).2 v ?_ fun w _ ↦ ?_
    · rw [SmoothForm.mpullback_apply_one, hv, hc]
    · rw [SmoothForm.mextDeriv_mpullback_apply_two, hv,
        ← one_smul ℝ (σ.hamiltonianVectorField K (ι s)),
        mextDeriv_smul_hamiltonianVectorField hσ hdθ, hdK, mul_zero, neg_zero]
  -- Hence `X_K = 0` and `dK = 0`, so `dι` is surjective.
  have hX0 : σ.hamiltonianVectorField K (ι s) = 0 := by rw [← hv, hv0, map_zero]
  have hdK0 : mvfderiv I K (ι s) = 0 := (hσ.hamiltonianVectorField_eq_zero_iff).1 hX0
  have hsurj (u : TangentSpace I (ι s)) : ∃ w, mfderiv J I ι s w = u := by
    have : u ∈ (mfderiv J I ι s).range := by
      rw [hK, hdK0]
      simp
    exact this
  -- Then `dι (R)` is `σ`-orthogonal to everything, so vanishes, contradicting `α(R) = 1`.
  set R := (SmoothForm.mpullback ι hι θ).reebVectorField s
  have hR : mfderiv J I ι s R = 0 := by
    refine (hσ.isInvertible_flat (ι s)).injective ?_
    ext u
    obtain ⟨w, rfl⟩ := hsurj u
    have h2 := hα.mextDeriv_reebVectorField_left s w
    rw [SmoothForm.mextDeriv_mpullback_apply_two, hdθ, ContinuousAlternatingMap.neg_apply,
      ← SmoothBundleForm.eval₂_apply, neg_eq_zero] at h2
    rw [SmoothTwoForm.flat_apply]
    simpa using h2
  have h1 := hα.apply_reebVectorField s
  rw [SmoothForm.mpullback_apply_one, hR, ← SmoothForm.degreeOneEquiv_coe_apply, map_zero] at h1
  exact zero_ne_one h1

/-- **The Reeb field of an energy hypersurface is a rescaled Hamiltonian field.** Let `σ` be a
nondegenerate two-form and `θ` a one-form with `dθ = -σ` at `ι s`, and suppose that the tangent
image of `ι : S → M` at `s` is the kernel of `dK`. If the restriction `ι^* θ` is a contact form,
then `θ(X_K)` does not vanish at `ι s` (`IsNondegenerate.apply_hamiltonianVectorField_ne_zero`),
and the differential of `ι` sends the Reeb vector field of `ι^* θ` to `X_K / θ(X_K)`. -/
theorem IsNondegenerate.mfderiv_reebVectorField_mpullback (hσ : σ.IsNondegenerate)
    {θ : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm) {K : M → ℝ} {s : S}
    (hdθ : mextDeriv θ.1 (ι s) = -σ.1 (ι s))
    (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    mfderiv J I ι s ((SmoothForm.mpullback ι hι θ).reebVectorField s) =
      (θ.1 (ι s) ![σ.hamiltonianVectorField K (ι s)])⁻¹ •
        σ.hamiltonianVectorField K (ι s) := by
  have := SmoothForm.finiteDimensional_of_isContactForm_mpullback hι hα s
  have hθK := hσ.apply_hamiltonianVectorField_ne_zero hι hα hdθ hK
  have hdK (w : TangentSpace J s) : mvfderiv I K (ι s) (mfderiv J I ι s w) = 0 :=
    (LinearMap.exact_iff.2 hK.symm).apply_apply_eq_zero w
  -- Express `X_K / θ(X_K)` through a lift `v`.
  obtain ⟨v, hv⟩ := smul_hamiltonianVectorField_mem_range hσ hK
    (θ.1 (ι s) ![σ.hamiltonianVectorField K (ι s)])⁻¹
  rw [ContinuousLinearMap.coe_coe] at hv
  set X := σ.hamiltonianVectorField K (ι s)
  set c := θ.1 (ι s) ![X]
  -- Scalar normalization: `θ(X_K / θ(X_K)) = 1`.
  have hθv : θ.1 (ι s) ![c⁻¹ • X] = 1 := by
    rw [← SmoothForm.degreeOneEquiv_coe_apply, map_smul, SmoothForm.degreeOneEquiv_coe_apply,
      smul_eq_mul, inv_mul_cancel₀ hθK]
  -- The lift `v` of `X_K / θ(X_K)` satisfies the two Reeb equations.
  have hR : (SmoothForm.mpullback ι hι θ).reebVectorField s = v :=
    ((hα.eq_reebVectorField_iff).2 ⟨by rw [SmoothForm.mpullback_apply_one, hv, hθv], fun w ↦ by
      rw [SmoothForm.mextDeriv_mpullback_apply_two, hv,
        mextDeriv_smul_hamiltonianVectorField hσ hdθ, hdK, mul_zero, neg_zero]⟩).symm
  rw [hR, hv]

end SmoothTwoForm

end TauCeti
