/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Reeb
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
condition forces `θ(X_K)` not to vanish. Indeed `X_K` is tangent to the level, since
`dK(X_K) = σ(X_K, X_K) = 0`, and for every vector `w` tangent to the level,
`dθ(X_K, w) = -σ(X_K, w) = -dK(w) = 0`. So the lift of `X_K / θ(X_K)` satisfies the two Reeb
equations, which determine the Reeb vector field.

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

/-- **The Reeb field of an energy hypersurface is a rescaled Hamiltonian field.** Let `σ` be a
nondegenerate two-form and `θ` a one-form with `dθ = -σ` at `ι s`, and suppose that the tangent
image of `ι : S → M` at `s` is the kernel of `dK`. If the restriction `ι^* θ` is a contact form,
then `θ(X_K)` does not vanish at `ι s`, and the differential of `ι` sends the Reeb vector field of
`ι^* θ` to `X_K / θ(X_K)`. -/
theorem IsNondegenerate.mfderiv_reebVectorField_mpullback (hσ : σ.IsNondegenerate)
    {θ : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm) {K : M → ℝ} {s : S}
    (hdθ : mextDeriv θ.1 (ι s) = -σ.1 (ι s))
    (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    mfderiv J I ι s ((SmoothForm.mpullback ι hι θ).reebVectorField s) =
      (θ.1 (ι s) ![σ.hamiltonianVectorField K (ι s)])⁻¹ •
        σ.hamiltonianVectorField K (ι s) := by
  set X := σ.hamiltonianVectorField K (ι s)
  -- Evaluating the pullbacks of `θ` and of `dθ` on tangent vectors of `S`.
  have hpull₁ (v : TangentSpace J s) :
      (SmoothForm.mpullback ι hι θ).1 s ![v] = θ.1 (ι s) ![mfderiv J I ι s v] := by
    simp [Matrix.vec_single_eq_const]
  have hpull₂ (v w : TangentSpace J s) :
      mextDeriv (SmoothForm.mpullback ι hι θ).1 s ![v, w] =
        mextDeriv θ.1 (ι s) ![mfderiv J I ι s v, mfderiv J I ι s w] := by
    rw [SmoothForm.coe_mpullback, ← mpullback_mextDeriv_at ((hι s).of_le (by simp))
      ((θ.contMDiff (ι s)).of_le (by simp)), mpullback_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  -- Exterior-derivative identity: `dθ(a • X_K, u) = -σ(a • X_K, u) = -a dK(u)`.
  have hdθX (a : ℝ) (u : TangentSpace I (ι s)) :
      mextDeriv θ.1 (ι s) ![a • X, u] = -(a * mvfderiv I K (ι s) u) := by
    rw [hdθ, ContinuousAlternatingMap.neg_apply, ← SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_smul_left, hσ.eval₂_hamiltonianVectorField, smul_eq_mul]
  -- The differential of `ι` is injective, since `ι^* θ` is a contact form: this makes `S`
  -- finite-dimensional.
  have hinj : Function.Injective (mfderiv J I ι s) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    refine (SmoothForm.isContactForm_iff.1 hα s).2 w ?_ fun w' _ ↦ ?_
    · rw [hpull₁, hw, ← SmoothForm.degreeOneEquiv_coe_apply, map_zero]
    · rw [hpull₂, hw, ← zero_smul ℝ X, hdθX, zero_mul, neg_zero]
  have : FiniteDimensional ℝ E' :=
    Module.Finite.of_injective (mfderiv J I ι s : E' →L[ℝ] E).toLinearMap hinj
  -- Every tangent vector of the level is killed by `dK`.
  have hdK (w : TangentSpace J s) : mvfderiv I K (ι s) (mfderiv J I ι s w) = 0 := by
    have hw : mfderiv J I ι s w ∈ (mvfderiv I K (ι s)).ker := hK ▸ LinearMap.mem_range_self _ w
    rwa [LinearMap.mem_ker] at hw
  -- The Hamiltonian vector field is tangent to the level, since `dK(X_K) = σ(X_K, X_K) = 0`.
  have hX : mvfderiv I K (ι s) X = 0 :=
    (hσ.isHamiltonianVectorField_hamiltonianVectorField K).mvfderiv_apply_self (ι s)
  have hXrange (a : ℝ) : a • X ∈ (mfderiv J I ι s).range := by
    rw [hK, LinearMap.mem_ker, map_smul, ContinuousLinearMap.coe_coe, hX, smul_zero]
  -- `θ(X_K)` does not vanish.
  have hθK : θ.1 (ι s) ![X] ≠ 0 := by
    intro hc
    -- Otherwise a lift `v` of `X_K` lies in `ker α` and is `dα`-orthogonal to everything,
    -- so `v = 0`.
    obtain ⟨v, hv⟩ := hXrange 1
    rw [one_smul, ContinuousLinearMap.coe_coe] at hv
    have hv0 : v = 0 := by
      refine (SmoothForm.isContactForm_iff.1 hα s).2 v ?_ fun w _ ↦ ?_
      · rw [hpull₁, hv, hc]
      · rw [hpull₂, hv, ← one_smul ℝ X, hdθX, hdK, mul_zero, neg_zero]
    -- Hence `X_K = 0` and `dK = 0`, so `dι` is surjective.
    have hX0 : X = 0 := by rw [← hv, hv0, map_zero]
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
      rw [hpull₂, hdθ, ContinuousAlternatingMap.neg_apply, ← SmoothBundleForm.eval₂_apply,
        neg_eq_zero] at h2
      rw [SmoothTwoForm.flat_apply]
      simpa using h2
    have h1 := hα.apply_reebVectorField s
    rw [hpull₁, hR, ← SmoothForm.degreeOneEquiv_coe_apply, map_zero] at h1
    exact zero_ne_one h1
  set c := θ.1 (ι s) ![X]
  -- Express `X_K / θ(X_K)` through the lift `v`.
  obtain ⟨v, hv⟩ := hXrange c⁻¹
  rw [ContinuousLinearMap.coe_coe] at hv
  -- Scalar normalization: `θ(X_K / θ(X_K)) = 1`.
  have hθv : θ.1 (ι s) ![c⁻¹ • X] = 1 := by
    rw [← SmoothForm.degreeOneEquiv_coe_apply, map_smul, SmoothForm.degreeOneEquiv_coe_apply,
      smul_eq_mul, inv_mul_cancel₀ hθK]
  -- The lift `v` of `X_K / θ(X_K)` satisfies the two Reeb equations.
  have hR : (SmoothForm.mpullback ι hι θ).reebVectorField s = v :=
    ((hα.eq_reebVectorField_iff).2 ⟨by rw [hpull₁, hv, hθv], fun w ↦ by
      rw [hpull₂, hv, hdθX, hdK, mul_zero, neg_zero]⟩).symm
  rw [hR, hv]

end SmoothTwoForm

end TauCeti
