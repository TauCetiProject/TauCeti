/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Prod.Basic

/-!
# Twisted products of smooth symplectic forms

The form on `M × N` used for Lagrangian correspondences is `pr₁*σ - pr₂*τ`.
It is constructed using the generic smooth pullback calculus. Its value on each tangent
space is the existing linear twisted product, so nondegeneracy is inherited from the two
factors. Closed factors give a closed product. These comparisons let the linear theory
of Lagrangian graphs apply to graphs of maps between manifolds.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Sections 3 and 5.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The twisted product `pr₁*σ - pr₂*τ` on `M × N`. -/
def twistedProd (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    SmoothTwoForm (I.prod J) (M × N) :=
  SmoothForm.mpullback Prod.fst contMDiff_fst σ -
    SmoothForm.mpullback Prod.snd contMDiff_snd τ

/-- The twisted product is the difference of the pullbacks from its factors. -/
theorem twistedProd_def (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    twistedProd σ τ = SmoothForm.mpullback Prod.fst contMDiff_fst σ -
      SmoothForm.mpullback Prod.snd contMDiff_snd τ := (rfl)

/-- Evaluation of the twisted product on a family of two tangent vectors. -/
@[simp]
theorem twistedProd_apply (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N)
    (p : M × N) (v : Fin 2 → TangentSpace (I.prod J) p) :
    (twistedProd σ τ).1 p v =
      σ.1 p.1 (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).1) -
      τ.1 p.2 (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).2) := by
  simp only [Manifold.tangentSpaceProdEquiv_apply]
  simp only [twistedProd_def, sub_eq_add_neg, SmoothForm.add_toRoughForm,
    SmoothForm.neg_toRoughForm, Pi.add_apply, Pi.neg_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
    SmoothForm.mpullback_apply, mfderiv_fst, mfderiv_snd]
  rfl

/-- Evaluation of the twisted product on two product tangent vectors. -/
theorem eval₂_twistedProd (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N)
    (p : M × N) (v w : TangentSpace (I.prod J) p) :
    (twistedProd σ τ).eval₂ p v w =
      σ.eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
        (Manifold.tangentSpaceProdEquiv p w).1 -
      τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
        (Manifold.tangentSpaceProdEquiv p w).2 := by
  rw [SmoothForm.eval₂_apply σ, SmoothForm.eval₂_apply τ,
    SmoothForm.eval₂_apply, twistedProd_apply]
  congr 1
  · apply congrArg (σ.1 p.1)
    ext i
    fin_cases i <;> rfl
  · apply congrArg (τ.1 p.2)
    ext i
    fin_cases i <;> rfl

/-- Nondegenerate factors give a nondegenerate twisted product. -/
theorem IsNondegenerate.twistedProd {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) : (twistedProd σ τ).IsNondegenerate := by
  rw [isNondegenerate_iff_separatingLeft]
  intro p v hv
  let e := Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
  apply e.injective
  rw [map_zero]
  apply Prod.ext
  · apply (isNondegenerate_iff_separatingLeft.mp hσ) p.1 (e v).1
    intro w
    have h := hv (e.symm (w, 0))
    rw [eval₂_twistedProd] at h
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply, Prod.fst, Prod.snd,
      ← SmoothForm.bilinFormAt_apply, map_zero, sub_zero] using h
  · apply (isNondegenerate_iff_separatingLeft.mp hτ) p.2 (e v).2
    intro w
    have h := hv (e.symm (0, w))
    rw [eval₂_twistedProd] at h
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply, Prod.fst, Prod.snd,
      ← SmoothForm.bilinFormAt_apply, map_zero, zero_sub, neg_eq_zero] using h

/-- The tangent-fibre form of a twisted product is the linear twisted product. -/
@[simp]
theorem IsNondegenerate.symplecticFormAt_twistedProd
    {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) (p : M × N) :
    ((hσ.twistedProd hτ).symplecticFormAt p).transport
        (Manifold.tangentSpaceProdEquiv p).toLinearEquiv =
      SymplecticForm.twistedProd (hσ.symplecticFormAt p.1) (hτ.symplecticFormAt p.2) := by
  apply SymplecticForm.toBilinForm_injective
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  have h := eval₂_twistedProd σ τ p
    ((Manifold.tangentSpaceProdEquiv p).symm v)
    ((Manifold.tangentSpaceProdEquiv p).symm w)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  exact (SymplecticForm.transport_apply _ _ v w).trans
    ((IsNondegenerate.symplecticFormAt_apply _ p _ _).trans
      (h.trans (by
        have h' := SymplecticForm.twistedProd_apply
          (hσ.symplecticFormAt p.1) (hτ.symplecticFormAt p.2) v w
        rw [IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply] at h'
        exact h'.symm)))

/-- Closed factors give a closed twisted product. -/
theorem isClosed_twistedProd {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (hσ : σ.IsClosed) (hτ : τ.IsClosed) : (twistedProd σ τ).IsClosed := by
  rw [SmoothForm.isClosed_def, ← mextDerivₗ_apply, ZeroMemClass.coe_eq_zero,
    twistedProd_def, map_sub, SmoothForm.mextDerivₗ_mpullback, SmoothForm.mextDerivₗ_mpullback]
  have hσ' : mextDerivₗ I 2 σ = 0 := by
    apply Subtype.ext
    simpa only [mextDerivₗ_apply, Submodule.coe_zero] using
      (SmoothForm.isClosed_def σ).mp hσ
  have hτ' : mextDerivₗ J 2 τ = 0 := by
    apply Subtype.ext
    simpa only [mextDerivₗ_apply, Submodule.coe_zero] using
      (SmoothForm.isClosed_def τ).mp hτ
  simp [hσ', hτ']

/-- The twisted product of symplectic forms is symplectic. -/
theorem IsSymplectic.twistedProd {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (hσ : σ.IsSymplectic) (hτ : τ.IsSymplectic) : (twistedProd σ τ).IsSymplectic :=
  ⟨isClosed_twistedProd hσ.isClosed hτ.isClosed,
    hσ.isNondegenerate.twistedProd hτ.isNondegenerate⟩

end TauCeti.SmoothTwoForm
