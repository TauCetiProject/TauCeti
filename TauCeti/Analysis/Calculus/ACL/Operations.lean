/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Algebra
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Operations on `ACL^p` maps that commute with the formal derivative

The formal derivative `u'` of `u : ℝⁿ → F` (`TauCeti.formalDeriv`) is built from the partial
derivatives `∂ᵢu(x) = lineDeriv ℝ u x eᵢ`, taken to be `0` where they do not exist. Some
operations on `u` act on these partial derivatives at every point, whether they exist or not,
because they do not change which line functions are differentiable:

* multiplication by a real constant: `(c • u)' = c • u'` (`TauCeti.formalDeriv_const_smul`; for
  `c ≠ 0` the line functions of `c • u` and `u` are differentiable together, and for `c = 0` both
  sides vanish);
* negation: `(-u)' = -u'` (`TauCeti.formalDeriv_neg`);
* composition with a continuous linear equivalence `L : F ≃L[ℝ] F'`: `(L ∘ u)' = L ∘ u'`
  (`ContinuousLinearEquiv.comp_formalDeriv`);
* constant maps have formal derivative `0` (`TauCeti.formalDeriv_const`).

Hence these operations preserve the class `ACL^p` (`TauCeti.isACLpOn_const`,
`TauCeti.IsACLpOn.const_smul`, `TauCeti.IsACLpOn.neg`,
`ContinuousLinearEquiv.comp_isACLpOn`), the `ACL` part being `TauCeti.IsACLOn.const_smul`,
`TauCeti.IsACLOn.neg` and `ContinuousLinearMap.comp_isACLOn`.

The partial derivatives of `c • u`, `-u` and `L ∘ u` are computed by `TauCeti.lineDeriv_const_smul`,
`TauCeti.lineDeriv_neg_left` and `ContinuousLinearEquiv.comp_lineDeriv`.

Sums and compositions with continuous linear maps that are not equivalences do not commute with
the formal derivative pointwise: a sum may have a partial derivative where neither summand has one.
For them the closure of `ACL^p` needs the almost-everywhere existence of the partial derivatives of
an `ACL` map into a finite-dimensional space.
-/

public section

open MeasureTheory

noncomputable section

namespace TauCeti

variable {n : ℕ} {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {u : EuclideanSpace ℝ (Fin n) → F} {Ω : Set (EuclideanSpace ℝ (Fin n))} {p : ENNReal}

/-! ### Formal derivatives -/

/-- The formal derivative of a constant map is `0`. -/
@[simp]
theorem formalDeriv_const (c : F) (x : EuclideanSpace ℝ (Fin n)) :
    formalDeriv (fun _ : EuclideanSpace ℝ (Fin n) ↦ c) x = 0 :=
  EuclideanSpace.ext_continuousLinearMap_single fun i ↦ by simp [lineDeriv]

/-- The formal derivative of `c • u` is `c • u'`, for every real `c`. -/
@[to_fun (attr := simp) formalDeriv_fun_const_smul]
theorem formalDeriv_const_smul (c : ℝ) (u : EuclideanSpace ℝ (Fin n) → F)
    (x : EuclideanSpace ℝ (Fin n)) : formalDeriv (c • u) x = c • formalDeriv u x :=
  EuclideanSpace.ext_continuousLinearMap_single fun i ↦ by
    simp

/-- The formal derivative of `-u` is `-u'`. -/
@[to_fun (attr := simp) formalDeriv_fun_neg]
theorem formalDeriv_neg (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n)) :
    formalDeriv (-u) x = -formalDeriv u x :=
  EuclideanSpace.ext_continuousLinearMap_single fun i ↦ by
    simp

/-- The formal derivative of `L ∘ u`, for a continuous linear equivalence `L`, is `L ∘ u'`. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_formalDeriv (L : F ≃L[ℝ] F')
    (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n)) :
    formalDeriv (L ∘ u) x = (L : F →L[ℝ] F').comp (formalDeriv u x) :=
  EuclideanSpace.ext_continuousLinearMap_single fun i ↦ by
    simp

/-! ### `ACL^p` maps -/

/-- Constant maps are `ACL^p` on every set, for every exponent. -/
theorem isACLpOn_const (c : F) : IsACLpOn (fun _ : EuclideanSpace ℝ (Fin n) ↦ c) p Ω where
  isACLOn := isACLOn_const c
  memLp_formalDeriv _ _ _ := by
    rw [show formalDeriv (fun _ : EuclideanSpace ℝ (Fin n) ↦ c) = 0 from
      funext (formalDeriv_const c)]
    exact MemLp.zero (ε := EuclideanSpace ℝ (Fin n) →L[ℝ] F)

/-- A real multiple of an `ACL^p` map is `ACL^p`. -/
theorem IsACLpOn.const_smul (hu : IsACLpOn u p Ω) (c : ℝ) : IsACLpOn (c • u) p Ω where
  isACLOn := hu.isACLOn.const_smul c
  memLp_formalDeriv K hKΩ hK := by
    rw [show formalDeriv (c • u) = c • formalDeriv u from funext (formalDeriv_const_smul c u)]
    exact (hu.memLp_formalDeriv K hKΩ hK).const_smul c

/-- The negative of an `ACL^p` map is `ACL^p`. -/
theorem IsACLpOn.neg (hu : IsACLpOn u p Ω) : IsACLpOn (-u) p Ω where
  isACLOn := hu.isACLOn.neg
  memLp_formalDeriv K hKΩ hK := by
    rw [show formalDeriv (-u) = -formalDeriv u from funext (formalDeriv_neg u)]
    exact (hu.memLp_formalDeriv K hKΩ hK).neg

/-- The composition of an `ACL^p` map with a continuous linear equivalence is `ACL^p`. -/
theorem _root_.ContinuousLinearEquiv.comp_isACLpOn (L : F ≃L[ℝ] F') (hu : IsACLpOn u p Ω) :
    IsACLpOn (L ∘ u) p Ω where
  isACLOn := (L : F →L[ℝ] F').comp_isACLOn hu.isACLOn
  memLp_formalDeriv K hKΩ hK := by
    have h := (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin n)) F F'
      (L : F →L[ℝ] F')).comp_memLp' (hu.memLp_formalDeriv K hKΩ hK)
    convert h using 1
    funext x
    rw [Function.comp_apply, ContinuousLinearMap.compL_apply, L.comp_formalDeriv]

end TauCeti
