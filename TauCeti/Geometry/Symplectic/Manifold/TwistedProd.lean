/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# Twisted products of smooth symplectic forms

The form on `M × N` used for Lagrangian correspondences is `pr₁*σ - pr₂*τ`.
It is the product form `TauCeti.SmoothTwoForm.prod` of `σ` and `-τ`
(`TauCeti.SmoothTwoForm.twistedProd_eq_prod_neg`), so nondegeneracy and closedness are
inherited from the two factors through the product form. Its value on each tangent
space is the existing linear twisted product. These comparisons let the linear theory
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

/-- The twisted product `pr₁*σ - pr₂*τ` is the product form of `σ` and `-τ`. -/
theorem twistedProd_eq_prod_neg (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    twistedProd σ τ = prod σ (-τ) := by
  rw [twistedProd_def, prod_def, map_neg, sub_eq_add_neg]

/-- Evaluation of the twisted product on two product tangent vectors. -/
theorem eval₂_twistedProd (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N)
    (p : M × N) (v w : TangentSpace (I.prod J) p) :
    (twistedProd σ τ).eval₂ p v w =
      σ.eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
        (Manifold.tangentSpaceProdEquiv p w).1 -
      τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
        (Manifold.tangentSpaceProdEquiv p w).2 := by
  rw [twistedProd_eq_prod_neg, eval₂_prod, SmoothForm.eval₂_neg, sub_eq_add_neg]

/-- Nondegenerate factors give a nondegenerate twisted product. -/
theorem IsNondegenerate.twistedProd {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) : (twistedProd σ τ).IsNondegenerate :=
  twistedProd_eq_prod_neg σ τ ▸ hσ.prod hτ.neg

/-- The tangent-fibre form of a twisted product is the linear twisted product. -/
@[simp]
theorem IsNondegenerate.symplecticFormAt_twistedProd
    {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) (p : M × N) :
    ((hσ.twistedProd hτ).symplecticFormAt p).transport
        (Manifold.tangentSpaceProdEquiv p).toLinearEquiv =
      SymplecticForm.twistedProd (hσ.symplecticFormAt p.1) (hτ.symplecticFormAt p.2) := by
  rw [← SymplecticForm.isSymplectomorphism_iff_transport_eq, SymplecticForm.isSymplectomorphism_iff]
  intro v w
  rw [SymplecticForm.twistedProd_apply, IsNondegenerate.symplecticFormAt_apply,
    IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply,
    eval₂_twistedProd]
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv]

/-- Closed factors give a closed twisted product. -/
theorem isClosed_twistedProd {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (hσ : σ.IsClosed) (hτ : τ.IsClosed) : (twistedProd σ τ).IsClosed :=
  twistedProd_eq_prod_neg σ τ ▸ isClosed_prod hσ hτ.neg

/-- The twisted product of symplectic forms is symplectic. -/
theorem IsSymplectic.twistedProd {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (hσ : σ.IsSymplectic) (hτ : τ.IsSymplectic) : (twistedProd σ τ).IsSymplectic :=
  ⟨isClosed_twistedProd hσ.isClosed hτ.isClosed,
    hσ.isNondegenerate.twistedProd hτ.isNondegenerate⟩

end TauCeti.SmoothTwoForm
