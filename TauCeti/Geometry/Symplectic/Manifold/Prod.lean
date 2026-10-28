/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwistedProd

/-!
# Products of smooth symplectic forms

The product of two manifolds `(M, σ)` and `(N, τ)` carrying two-forms carries the product form
`pr₁*σ + pr₂*τ` (`TauCeti.SmoothTwoForm.prod σ τ`). On the tangent space at `p = (x, y)`, which
is `T_x M × T_y N`, it pairs `(v, w)` with `(v', w')` to `σ(v, v') + τ(w, w')`, so its value on
each tangent space is the linear direct-sum form `TauCeti.SymplecticForm.prod`. Nondegeneracy and
closedness are inherited from the factors, so the product of two symplectic manifolds is a
symplectic manifold. This is the symplectic structure in which products of isotropic,
coisotropic and Lagrangian submanifolds of the factors are again of the same kind
(`TauCeti.Geometry.Symplectic.Lagrangian.Prod`).

The twisted product `pr₁*σ - pr₂*τ` (`TauCeti.SmoothTwoForm.twistedProd`) of Lagrangian
correspondences is the product form of `σ` and `-τ`
(`TauCeti.SmoothTwoForm.twistedProd_eq_prod_neg`).

## Main declarations

* `TauCeti.SmoothTwoForm.prod`: the product form `pr₁*σ + pr₂*τ` on `M × N`.
* `TauCeti.SmoothTwoForm.prod_apply`, `TauCeti.SmoothTwoForm.eval₂_prod`: its evaluation on the
  components of tangent vectors.
* `TauCeti.SmoothTwoForm.IsNondegenerate.prod`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_prod`: nondegenerate factors give a
  nondegenerate product, whose tangent-space forms are the linear direct sums.
* `TauCeti.SmoothTwoForm.isClosed_prod`, `TauCeti.SmoothTwoForm.IsSymplectic.prod`: closed,
  respectively symplectic, factors give a closed, respectively symplectic, product.
* `TauCeti.SmoothTwoForm.twistedProd_eq_prod_neg`: the twisted product is the product form with
  the second factor negated.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The product form `pr₁*σ + pr₂*τ` on `M × N` of two-forms `σ` on `M` and `τ` on `N`. -/
def prod (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) : SmoothTwoForm (I.prod J) (M × N) :=
  SmoothForm.mpullback Prod.fst contMDiff_fst σ + SmoothForm.mpullback Prod.snd contMDiff_snd τ

/-- The product form is the sum of the pullbacks from its factors. -/
theorem prod_def (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    prod σ τ =
      SmoothForm.mpullback Prod.fst contMDiff_fst σ +
        SmoothForm.mpullback Prod.snd contMDiff_snd τ := (rfl)

/-- Evaluation of the product form on a family of two tangent vectors. -/
@[simp]
theorem prod_apply (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) (p : M × N)
    (v : Fin 2 → TangentSpace (I.prod J) p) :
    (prod σ τ).1 p v =
      σ.1 p.1 (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).1) +
        τ.1 p.2 (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).2) := by
  simp only [Manifold.tangentSpaceProdEquiv_apply, prod_def, SmoothForm.add_toRoughForm,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, SmoothForm.mpullback_apply, mfderiv_fst,
    mfderiv_snd]
  -- The projections act on product tangent vectors through the identity identification.
  rfl

/-- The product form evaluates on two tangent vectors of `M × N` as the sum of the factor forms
on their components. -/
theorem eval₂_prod (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    (prod σ τ).eval₂ p v w =
      σ.eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1 (Manifold.tangentSpaceProdEquiv p w).1 +
        τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
          (Manifold.tangentSpaceProdEquiv p w).2 := by
  rw [prod_def, SmoothForm.eval₂_add, SmoothForm.eval₂_mpullback_fst,
    SmoothForm.eval₂_mpullback_snd]

variable {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}

/-- Nondegenerate factors give a nondegenerate product form. -/
theorem IsNondegenerate.prod (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate) :
    (prod σ τ).IsNondegenerate := by
  rw [isNondegenerate_iff_separatingLeft]
  intro p v hv
  let e := Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
  -- `e v` pairs to zero with everything under the linear direct sum of the fibre forms.
  have h : e v = 0 :=
    ((hσ.symplecticFormAt p.1).prod (hτ.symplecticFormAt p.2)).separatingLeft (e v) fun w ↦ by
      have hw := hv (e.symm w)
      rw [eval₂_prod, ContinuousLinearEquiv.apply_symm_apply] at hw
      refine (SymplecticForm.prod_apply _ _ (e v) w).trans ?_
      rwa [IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply]
  simpa using congrArg e.symm h

/-- The tangent-space form of a product of nondegenerate forms is, under the identification
`T_(x, y) (M × N) = T_x M × T_y N`, the linear direct sum of the tangent-space forms of the
factors. -/
@[simp]
theorem IsNondegenerate.symplecticFormAt_prod (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate)
    (p : M × N) :
    ((hσ.prod hτ).symplecticFormAt p).transport (Manifold.tangentSpaceProdEquiv p).toLinearEquiv =
      (hσ.symplecticFormAt p.1).prod (hτ.symplecticFormAt p.2) := by
  rw [← SymplecticForm.isSymplectomorphism_iff_transport_eq, SymplecticForm.isSymplectomorphism_iff]
  intro v w
  rw [SymplecticForm.prod_apply, IsNondegenerate.symplecticFormAt_apply,
    IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply, eval₂_prod]
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv]

/-- Closed factors give a closed product form. -/
theorem isClosed_prod (hσ : σ.IsClosed) (hτ : τ.IsClosed) : (prod σ τ).IsClosed :=
  (hσ.mpullback Prod.fst contMDiff_fst).add (hτ.mpullback Prod.snd contMDiff_snd)

/-- **The product of symplectic manifolds is symplectic.** -/
theorem IsSymplectic.prod (hσ : σ.IsSymplectic) (hτ : τ.IsSymplectic) :
    (prod σ τ).IsSymplectic :=
  ⟨isClosed_prod hσ.isClosed hτ.isClosed, hσ.isNondegenerate.prod hτ.isNondegenerate⟩

/-- The twisted product `pr₁*σ - pr₂*τ` is the product form of `σ` and `-τ`. -/
theorem twistedProd_eq_prod_neg (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    twistedProd σ τ = prod σ (-τ) := by
  rw [twistedProd_def, prod_def, map_neg, sub_eq_add_neg]

end TauCeti.SmoothTwoForm
