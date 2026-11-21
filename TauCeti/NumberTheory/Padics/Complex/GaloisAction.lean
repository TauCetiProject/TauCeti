/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.FieldTheory.KrullTopology
import TauCeti.NumberTheory.Padics.AlgebraicClosure
import TauCeti.Topology.Algebra.UniformRing

/-!
# The Galois action on `ℂ_p`

An automorphism of the algebraic closure of `ℚ_p` over `ℚ_p` preserves the spectral
norm, by `AlgEquiv.norm_apply`. It extends uniquely to an isometric algebra automorphism of
`ℂ_p` via `UniformSpace.Completion.mapAlgEquiv`. The resulting action is jointly continuous:
orbit maps on the dense algebraic closure are locally constant for the Krull topology, and the
isometry property controls the error of approximation. This action is the input for studying fixed
fields and continuous Galois cohomology with coefficients in `ℂ_p`.

`PadicComplex.galoisAction` is the homomorphism to `ℚ_p`-algebra automorphisms.
The `MulSemiringAction`, `IsIsometricSMul` and `ContinuousSMul` instances also give the action
of the Galois group over any intermediate field, using the native completion scalar action.

See Brinon–Conrad, *CMI summer school notes on p-adic Hodge theory*, §2.1, p. 12, and
Fontaine–Ouyang, *Theory of p-adic Galois representations*, §4.1.2, p. 91.
-/

public section

open UniformSpace

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime]

private theorem isometry_algEquiv (σ : Gal(PadicAlgCl p/ℚ_[p])) : Isometry σ :=
  (AddMonoidHomClass.isometry_iff_norm σ).2 σ.norm_apply

/-- The action of `Gal(PadicAlgCl p/ℚ_[p])` on `ℂ_p` by `ℚ_p`-algebra automorphisms. -/
noncomputable def galoisAction (p : ℕ) [Fact p.Prime] :
    Gal(PadicAlgCl p/ℚ_[p]) →* (ℂ_[p] ≃ₐ[ℚ_[p]] ℂ_[p]) where
  toFun σ := Completion.mapAlgEquiv σ (isometry_algEquiv σ).continuous
    (isometry_algEquiv σ.symm).continuous
  map_one' := Completion.mapAlgEquiv_refl
  map_mul' σ τ := Completion.mapAlgEquiv_trans τ σ _ _ _ _

/-- The completed action is the completion map of the algebraic automorphism. -/
theorem galoisAction_apply_eq_map (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : ℂ_[p]) :
    galoisAction p σ x = Completion.map σ x := by
  exact Completion.mapAlgEquiv_apply σ _ _ x

/-- On the dense algebraic closure, the completed action agrees with the original action. -/
@[simp]
theorem galoisAction_apply_coe (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : PadicAlgCl p) :
    galoisAction p σ (x : ℂ_[p]) = (σ x : ℂ_[p]) := by
  rw [galoisAction_apply_eq_map, Completion.map_coe (isometry_algEquiv σ).uniformContinuous]

/-- Each Galois automorphism acts on `ℂ_p` by an isometry. -/
theorem isometry_galoisAction (σ : Gal(PadicAlgCl p/ℚ_[p])) : Isometry (galoisAction p σ) := by
  rw [funext (galoisAction_apply_eq_map σ)]
  exact (isometry_algEquiv σ).completion_map

/-- The action on `ℂ_p` is the unique continuous extension of the algebraic action. -/
theorem eq_galoisAction_of_continuous (σ : Gal(PadicAlgCl p/ℚ_[p])) {f : ℂ_[p] → ℂ_[p]}
    (hf : Continuous f) (h : ∀ x : PadicAlgCl p, f (x : ℂ_[p]) = (σ x : ℂ_[p])) :
    f = galoisAction p σ :=
  Completion.ext hf (isometry_galoisAction σ).continuous fun x ↦
    (h x).trans (galoisAction_apply_coe σ x).symm

/-- The action on `ℂ_p` is faithful. -/
theorem galoisAction_injective : Function.Injective (galoisAction p) := by
  intro σ τ h
  ext x
  apply Completion.coe_injective
  simpa only [galoisAction_apply_coe] using DFunLike.congr_fun h (x : ℂ_[p])

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
  [IsScalarTower ℚ_[p] K (PadicAlgCl p)]

/-- Over any intermediate field `K`, the action on `ℂ_p` is jointly continuous for the Krull
and norm topologies. No finiteness hypothesis on `K/ℚ_p` is required. -/
theorem continuous_galoisAction :
    Continuous (fun z : Gal(PadicAlgCl p/K) × ℂ_[p] ↦
      galoisAction p (z.1.restrictScalars ℚ_[p]) z.2) := by
  let F : Gal(PadicAlgCl p/K) → ℂ_[p] → ℂ_[p] := fun σ ↦
    galoisAction p (σ.restrictScalars ℚ_[p])
  have hF (σ) : LipschitzWith 1 (F σ) :=
    (isometry_galoisAction (σ.restrictScalars ℚ_[p])).lipschitzWith
  have hequi := (LipschitzWith.uniformEquicontinuous F 1 hF).equicontinuous
  refine continuous_prod_of_continuous_lipschitzWith' _ 1 hF fun x ↦ ?_
  -- Equicontinuity lets us test orbit continuity only on the dense algebraic points.
  refine continuous_iff_continuousAt.2 fun σ ↦
    (hequi x).tendsto_of_mem_closure (hF σ).continuous.continuousWithinAt ?_
      (Completion.denseRange_coe x)
  rintro _ ⟨a, rfl⟩
  have ha : IsIntegral K a := (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) a).tower_top
  have hc := (Completion.continuous_coe (PadicAlgCl p)).comp ha.isLocallyConstant_apply.continuous
  simpa only [F, galoisAction_apply_coe, AlgEquiv.restrictScalars_apply, Function.comp_def,
    ContinuousAt] using hc.continuousAt (x := σ)

/-- Each Galois automorphism acts uniformly continuously on the algebraic closure. -/
instance : UniformContinuousConstSMul Gal(PadicAlgCl p/K) (PadicAlgCl p) where
  uniformContinuous_const_smul σ := by
    simpa only [AlgEquiv.smul_def, AlgEquiv.coe_restrictScalars] using
      (isometry_algEquiv (σ.restrictScalars ℚ_[p])).uniformContinuous

/-- Scalar notation for the action on `ℂ_p` agrees with the algebra automorphism. -/
theorem galois_smul_def (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    σ • x = galoisAction p (σ.restrictScalars ℚ_[p]) x := by
  rw [Completion.smul_def, galoisAction_apply_eq_map]
  simp only [AlgEquiv.smul_def, AlgEquiv.coe_restrictScalars]

/-- The completed action preserves multiplication and the unit. -/
noncomputable instance instGaloisMulSemiringAction :
    MulSemiringAction Gal(PadicAlgCl p/K) ℂ_[p] where
  smul_one σ := by rw [galois_smul_def, map_one]
  smul_mul σ x y := by simp only [galois_smul_def, map_mul]

/-- The completed action preserves distances. -/
instance : IsIsometricSMul Gal(PadicAlgCl p/K) ℂ_[p] where
  isometry_smul σ := by
    simpa only [galois_smul_def] using isometry_galoisAction (σ.restrictScalars ℚ_[p])

/-- The completed action is a continuous scalar action. -/
instance : ContinuousSMul Gal(PadicAlgCl p/K) ℂ_[p] := by
  constructor
  simpa only [galois_smul_def] using continuous_galoisAction (p := p) (K := K)

end PadicComplex
