/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# Twisted products of smooth symplectic forms

The form on `M × N` used for Lagrangian correspondences is `pr₁*σ - pr₂*τ`.
It is the product form `TauCeti.SmoothTwoForm.prod` of `σ` and `-τ`
(`TauCeti.SmoothTwoForm.twistedProd_eq_prod_neg`), so nondegeneracy and closedness are
inherited from the two factors through the product form. Its value on each tangent
space is the existing linear twisted product. These comparisons let the linear theory
of Lagrangian graphs apply to graphs of maps between manifolds.

Two sign laws govern the operations on correspondences. Exchanging the factors pulls
`pr₁*τ - pr₂*σ` on `N × M` back to `-(pr₁*σ - pr₂*τ)` on `M × N`
(`TauCeti.SmoothTwoForm.mpullback_prodComm_twistedProd`), so transposing a relation negates
its form. Regrouping `(M × N) × (M' × N')` as `(M × M') × (N × N')` pulls the twisted product
of the product forms back to the product of the twisted products
(`TauCeti.SmoothTwoForm.mpullback_prodProdProdComm_twistedProd_prod`).

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
    SmoothBundleForm.eval₂ (twistedProd σ τ) p v w =
      SmoothBundleForm.eval₂ σ p.1
        (Manifold.tangentSpaceProdEquiv p v).1
        (Manifold.tangentSpaceProdEquiv p w).1 -
      SmoothBundleForm.eval₂ τ p.2
        (Manifold.tangentSpaceProdEquiv p v).2
        (Manifold.tangentSpaceProdEquiv p w).2 := by
  rw [twistedProd_eq_prod_neg, eval₂_prod]
  simp [sub_eq_add_neg]

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

/-- Exchanging the factors turns the twisted product `pr₁*τ - pr₂*σ` on `N × M` into the
negative of the twisted product `pr₁*σ - pr₂*τ` on `M × N`. -/
theorem mpullback_prodComm_twistedProd (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    SmoothForm.mpullback (Diffeomorph.prodComm I J M N ∞)
        (Diffeomorph.prodComm I J M N ∞).contMDiff (twistedProd τ σ) =
      -twistedProd σ τ := by
  simp only [twistedProd_def, map_sub, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp,
    Diffeomorph.coe_prodComm, Function.comp_def, Prod.fst_swap, Prod.snd_swap, neg_sub]

section Regroup

variable {E' H'' M' F' H''' N' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'']
  {I' : ModelWithCorners ℝ E' H''} [TopologicalSpace M'] [ChartedSpace H'' M']
  [IsManifold I' ∞ M']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [TopologicalSpace H''']
  {J' : ModelWithCorners ℝ F' H'''} [TopologicalSpace N'] [ChartedSpace H''' N']
  [IsManifold J' ∞ N']

/-- Regrouping `(M × N) × (M' × N')` as `(M × M') × (N × N')` pulls the twisted product of the
product forms back to the product of the twisted products. -/
theorem mpullback_prodProdProdComm_twistedProd_prod (σ : SmoothTwoForm I M)
    (τ : SmoothTwoForm J N) (σ' : SmoothTwoForm I' M') (τ' : SmoothTwoForm J' N') :
    SmoothForm.mpullback (Diffeomorph.prodProdProdComm I J I' J' M N M' N' ∞)
        (Diffeomorph.prodProdProdComm I J I' J' M N M' N' ∞).contMDiff
        (twistedProd (prod σ σ') (prod τ τ')) =
      prod (twistedProd σ τ) (twistedProd σ' τ') := by
  simp only [twistedProd_def, prod_def, map_sub, map_add, ← LinearMap.comp_apply,
    ← SmoothForm.mpullback_comp, Diffeomorph.coe_prodProdProdComm, Function.comp_def,
    Equiv.prodProdProdComm_apply]
  abel

end Regroup

end TauCeti.SmoothTwoForm
