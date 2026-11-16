/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.Geometry.Symplectic.AlmostComplex

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Adjoining a parameter to the target of the Floer equation

In local coordinates `z ∈ ℂ` on the domain and `x ∈ V` on the target, the Floer equation reads
`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`. Let the data `J_p` and `X_p` depend on a parameter
`p` in a real normed space `P`. Adjoin the parameter to the target as a constant coordinate: a
solution `u` for the parameter `p` is the second component of the map `z ↦ ((p, 0), u z)` into the
Euclidean product `(P × P) × V`, and this map solves the Floer equation for the structure
`(a, b) ↦ (-b, a)` on the parameter block (`TauCeti.Floer.parameterStructure`), the structure
`J_p` on `V`, and the one-form `X_p` with values in `V` (`TauCeti.Floer.parameterJ` and
`TauCeti.Floer.parameterX`). The parameter block has zero derivative, so it solves its equation
trivially, and in the Euclidean product it does not change the energy density. It is doubled only
so that it carries a linear complex structure.

The data adjoining the parameter are as smooth as the data themselves
(`TauCeti.Floer.contDiffOn_parameterJ`, `TauCeti.Floer.contDiffOn_parameterX`), so theorems for a
single datum `J`, `X` apply to them and give the corresponding statements for families of data.
-/

public section

open ContinuousLinearMap Function Set

namespace TauCeti.Floer

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- The standard complex structure `(a, b) ↦ (-b, a)` on `P × P`
(`TauCeti.AlmostComplexStructure.product`), as a continuous linear map of the Euclidean product. -/
noncomputable def parameterStructure : WithLp 2 (P × P) →L[ℝ] WithLp 2 (P × P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ P P).symm.toContinuousLinearMap ∘L
    ⟨(AlmostComplexStructure.product P).toLinearMap, continuous_snd.neg.prodMk continuous_fst⟩ ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ P P).toContinuousLinearMap

theorem parameterStructure_apply (ζ : WithLp 2 (P × P)) :
    parameterStructure ζ = WithLp.toLp 2 (AlmostComplexStructure.product P ζ.ofLp) :=
  (rfl)

@[simp]
theorem parameterStructure_parameterStructure (ζ : WithLp 2 (P × P)) :
    parameterStructure (parameterStructure ζ) = -ζ := by
  rw [parameterStructure_apply, parameterStructure_apply, WithLp.ofLp_toLp,
    AlmostComplexStructure.apply_apply, WithLp.toLp_neg, WithLp.toLp_ofLp]

/-- The point of `P × (ℂ × V)` read off from a point of `ℂ × ((P × P) × V)`: the first parameter
coordinate, the domain point and the target point. -/
noncomputable def parameterPoint :
    ℂ × WithLp 2 (WithLp 2 (P × P) × V) →L[ℝ] P × (ℂ × V) :=
  (WithLp.fstL 2 ℝ P P ∘L WithLp.fstL 2 ℝ (WithLp 2 (P × P)) V ∘L snd ℝ ℂ _).prod
    ((fst ℝ ℂ _).prod (WithLp.sndL 2 ℝ (WithLp 2 (P × P)) V ∘L snd ℝ ℂ _))

@[simp]
theorem parameterPoint_apply (z : ℂ) (p q : P) (x : V) :
    parameterPoint (z, WithLp.toLp 2 (WithLp.toLp 2 (p, q), x)) = (p, (z, x)) := by
  simp [parameterPoint]

/-- The almost complex structure on `(P × P) × V` adjoining the parameter: the structure
`(a, b) ↦ (-b, a)` on the parameter block and `J_a(z, x)` on `V` at the point `(z, ((a, b), x))`.
-/
noncomputable def parameterJ (J : P → ℂ × V → V →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) :
    WithLp 2 (WithLp 2 (P × P) × V) →L[ℝ] WithLp 2 (WithLp 2 (P × P) × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (P × P)) V).symm.toContinuousLinearMap ∘L
    (inl ℝ (WithLp 2 (P × P)) V ∘L parameterStructure ∘L fst ℝ _ V +
      inr ℝ (WithLp 2 (P × P)) V ∘L uncurry J (parameterPoint q) ∘L snd ℝ _ V) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (P × P)) V).toContinuousLinearMap

@[simp]
theorem parameterJ_apply (J : P → ℂ × V → V →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) (ζ : WithLp 2 (WithLp 2 (P × P) × V)) :
    parameterJ J q ζ = WithLp.toLp 2 (parameterStructure ζ.fst,
      uncurry J (parameterPoint q) ζ.snd) := by
  simp [parameterJ, WithLp.ext_iff]

/-- The Hamiltonian one-form on `(P × P) × V` adjoining the parameter: the one-form `X_a(z, x)`
with values in `V` at the point `(z, ((a, b), x))`. -/
noncomputable def parameterX (X : P → ℂ × V → ℂ →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) : ℂ →L[ℝ] WithLp 2 (WithLp 2 (P × P) × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (P × P)) V).symm.toContinuousLinearMap ∘L
    inr ℝ (WithLp 2 (P × P)) V ∘L uncurry X (parameterPoint q)

@[simp]
theorem parameterX_apply (X : P → ℂ × V → ℂ →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) (ξ : ℂ) :
    parameterX X q ξ = WithLp.toLp 2 (0, uncurry X (parameterPoint q) ξ) := by
  simp [parameterX]

theorem contDiffOn_parameterJ {n : WithTop ℕ∞} {J : P → ℂ × V → V →L[ℝ] V}
    {W : Set (P × (ℂ × V))} (hJ : ContDiffOn ℝ n (uncurry J) W) :
    ContDiffOn ℝ n (parameterJ J) (parameterPoint ⁻¹' W) := by
  have hJ' : ContDiffOn ℝ n (fun q ↦ uncurry J (parameterPoint q)) (parameterPoint ⁻¹' W) :=
    hJ.comp (parameterPoint (P := P) (V := V)).contDiff.contDiffOn (mapsTo_preimage _ _)
  unfold parameterJ
  exact contDiffOn_const.clm_comp ((contDiffOn_const.add (contDiffOn_const.clm_comp
    (hJ'.clm_comp contDiffOn_const))).clm_comp contDiffOn_const)

theorem contDiffOn_parameterX {n : WithTop ℕ∞} {X : P → ℂ × V → ℂ →L[ℝ] V}
    {W : Set (P × (ℂ × V))} (hX : ContDiffOn ℝ n (uncurry X) W) :
    ContDiffOn ℝ n (parameterX X) (parameterPoint ⁻¹' W) := by
  have hX' : ContDiffOn ℝ n (fun q ↦ uncurry X (parameterPoint q)) (parameterPoint ⁻¹' W) :=
    hX.comp (parameterPoint (P := P) (V := V)).contDiff.contDiffOn (mapsTo_preimage _ _)
  unfold parameterX
  exact contDiffOn_const.clm_comp (contDiffOn_const.clm_comp hX')

end TauCeti.Floer
