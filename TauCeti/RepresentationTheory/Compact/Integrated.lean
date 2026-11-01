/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Averaging
public import TauCeti.RepresentationTheory.Continuous.Character
public import TauCeti.RepresentationTheory.Continuous.Schur
import TauCeti.RepresentationTheory.Irreducible

/-!
# A class function acts on an irreducible representation by a scalar

A continuous function `f` on a compact group `G` acts on a continuous representation `π` on `V`
by the **integrated operator**

`integratedOperator π hπ f = ∫ g, f g • π g ∂(haarProb G)`,

the Haar average of the action operators weighted by `f`. Its trace is the Haar integral of
`f · χ_π`, with no hypothesis on `f`.

When `f` is a **class function** — constant on conjugacy classes — the integrated operator commutes
with the action, because conjugating the integrand by `π h` translates its group variable by
`g ↦ h⁻¹ g h`, which normalized Haar measure does not see and which `f` does not see either. So for
an irreducible `π` over an algebraically closed field Schur's lemma makes it a scalar, and the trace
computation fixes that scalar:

`integratedOperator π hπ f = (dim V)⁻¹ · (∫ g, f g · χ_π g) • id`.

Specializing `f` to `conj χ_π` turns the character orthogonality relations into the character
projections; the irreducible block identities are in
`TauCeti/RepresentationTheory/Compact/Character/Projection.lean`, and their assembly into the
isotypic projector is in
`TauCeti/RepresentationTheory/Compact/Character/IsotypicProjection.lean`.

## Main definitions

* `ContRepresentation.integratedOperator`: the operator `∫ g, f g • π g` by which a
  continuous scalar function acts on a continuous representation.
* `ContRepresentation.integratedOperatorₗ`: the same, linear in the acting function.
* `ContRepresentation.integratedIntertwiner`: the integrated operator of a class function,
  packaged as a continuous self-intertwiner.

## Main results

* `ContRepresentation.trace_integratedOperator`: the trace of the integrated operator is
  `∫ g, f g · χ_π g`.
* `ContRepresentation.comp_integratedOperator`: integrated operators are natural with
  respect to continuous intertwiners.
* `ContRepresentation.integratedOperator_comp`: a class function acts by an intertwiner.
* `ContRepresentation.integratedOperator_eq_smul_id`: **a class function acts on a
  finite-dimensional irreducible representation by the scalar `(dim V)⁻¹ · ∫ g, f g · χ_π g`.**
* `ContRepresentation.integratedOperator_eq_zero`: it acts as zero when that integral
  vanishes.

## Implementation notes

Being a class function is carried as the bare hypothesis `∀ g h : G, f (h * g * h⁻¹) = f g`, the
same shape as in `TauCeti/RepresentationTheory/Compact/ClassFunctionLp.lean`, rather than as a new
predicate: it is passed directly through this API, and the `L²`-level notion that deserves a
bundling is the almost-everywhere one, `TauCeti.classFunctionLp`, which is already defined.

The definition asks only that `V` be a normed space: it is `TauCeti.haarAverage` of a continuous
family valued in the operator space `V →L[𝕜] V`, so it inherits that average's convention. What
the Bochner integral reads is completeness of that codomain, and `[CompleteSpace V]` is what
supplies it. When that codomain is incomplete, the average is the integral's junk value `0`
rather than the classical integrated form `π(f)`. Evaluation at a vector and commutation with
the action of a class function remain valid without completeness, with the same Bochner
convention on both sides. Naturality between different representation spaces asks for their
completeness. Finite-dimensionality enters with the trace, and algebraic closedness of the
scalars with Schur's lemma. The integrated operator of the trivial group action and other
structural identities are not developed here: what the character projections need is linearity
in `f`, the trace, and the scalar theorem.

The scalar in `integratedOperator_eq_smul_id` is `(dim V)⁻¹ · ∫ f · χ_π`, not `∫ f · conj χ_π`: the
integrand pairs `f` with the character itself, and the conjugation appears only when the acting
function is specialized to `conj χ_π`.

## References

The integrated operators support averaging against `dim V_π · conj χ_π` to project onto
isotypic components. The mathematical development follows Daniel Bump, *Lie
Groups*, second edition, Chapter 2, and T. Bröcker and T. tom Dieck, *Representations of Compact Lie
Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open MeasureTheory TauCeti

namespace ContRepresentation

section Integrated

section

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] (π : ContRepresentation 𝕜 G V)

variable [TopologicalSpace G] (hπ : Continuous π)

/-- The integrand `g ↦ f g • π g` of the integrated operator, as a continuous map on the group.
Continuity is where the continuity hypothesis on the representation is used. -/
private noncomputable def weightFamily (f : C(G, 𝕜)) : C(G, V →L[𝕜] V) where
  toFun g := f g • π g
  continuous_toFun := f.continuous.smul hπ

/-- The integrand of the integrated operator, evaluated at a group element. This is the unfolding
lemma that keeps the proofs below from reaching through `weightFamily`'s definition. -/
@[simp]
private theorem weightFamily_apply (f : C(G, 𝕜)) (g : G) :
    weightFamily π hπ f g = f g • π g :=
  (rfl)

end

section

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] [SMulCommClass 𝕜 ℝ V]
  (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The operator by which a continuous scalar function acts on a continuous representation**,
`∫ g, f g • π g ∂(haarProb G)`.

On a complete `V` this is the classical integrated form `π(f)` of the representation, and it is
always defined there: the integrand is continuous and normalized Haar measure is finite. `V` is not
assumed complete. The average is taken in the operator space `V →L[𝕜] V`, so it is
`TauCeti.haarAverage`'s junk value `0` unless that space is complete, which `[CompleteSpace V]`
supplies. Evaluation and the class-function intertwining identity respect this convention without
assuming completeness. -/
noncomputable def integratedOperator (f : C(G, 𝕜)) : V →L[𝕜] V :=
  haarAverage G (𝕜 := 𝕜) (weightFamily π hπ f)

/-! ### Linearity in the acting function -/

@[simp]
theorem integratedOperator_zero : integratedOperator π hπ (0 : C(G, 𝕜)) = 0 := by
  have hzero : weightFamily π hπ (0 : C(G, 𝕜)) = 0 := by
    ext g v
    simp
  rw [integratedOperator, hzero, map_zero]

@[simp]
theorem integratedOperator_add (f₁ f₂ : C(G, 𝕜)) :
    integratedOperator π hπ (f₁ + f₂)
      = integratedOperator π hπ f₁ + integratedOperator π hπ f₂ := by
  have hadd : weightFamily π hπ (f₁ + f₂) = weightFamily π hπ f₁ + weightFamily π hπ f₂ := by
    ext g v
    simp [add_smul]
  rw [integratedOperator, integratedOperator, integratedOperator, hadd, map_add]

@[simp]
theorem integratedOperator_smul (c : 𝕜) (f : C(G, 𝕜)) :
    integratedOperator π hπ (c • f) = c • integratedOperator π hπ f := by
  have hsmul : weightFamily π hπ (c • f) = c • weightFamily π hπ f := by
    ext g v
    simp [mul_smul]
  rw [integratedOperator, integratedOperator, hsmul, map_smul]

/-- The integrated operator, bundled as a linear map in the acting function. Bundling supplies the
remaining additive identities (`map_neg`, `map_sub`, `map_sum`) through the `LinearMap` API. -/
noncomputable def integratedOperatorₗ : C(G, 𝕜) →ₗ[𝕜] V →L[𝕜] V where
  toFun := integratedOperator π hπ
  map_add' := integratedOperator_add π hπ
  map_smul' := integratedOperator_smul π hπ

@[simp]
theorem integratedOperatorₗ_apply (f : C(G, 𝕜)) :
    integratedOperatorₗ π hπ f = integratedOperator π hπ f :=
  (rfl)

end

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The integrated operator, evaluated at a vector. This identity also holds without completeness,
with Mathlib's Bochner integral convention on both sides. -/
theorem integratedOperator_apply (f : C(G, 𝕜)) (v : V) :
    integratedOperator π hπ f v = ∫ g, f g • π g v ∂haarProb G := by
  rw [integratedOperator, haarAverage_apply,
    ContinuousLinearMap.integral_apply (integrable_continuousMap G (weightFamily π hπ f))]
  simp only [weightFamily_apply, smul_apply]

/-! ### A class function acts by an intertwiner -/

variable {f : C(G, 𝕜)}

/-- **A class function acts by an intertwiner.** The integrated operator of a function constant on
conjugacy classes commutes with every action operator. -/
theorem integratedOperator_comp (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) (h : G) :
    (integratedOperator π hπ f).comp (π h) = (π h).comp (integratedOperator π hπ f) := by
  have hint := integrable_continuousMap G (weightFamily π hπ f)
  -- Left and right translation reduce the two composites to the same weighted integral.
  have hclass (g : G) : f (g * h⁻¹) = f (h⁻¹ * g) := by
    simpa [mul_assoc] using (hf (g * h⁻¹) h⁻¹).symm
  simp only [← ContinuousLinearMap.mul_def, integratedOperator, haarAverage_apply]
  rw [← integral_mul_const_of_integrable hint, ← integral_const_mul_of_integrable hint]
  calc (∫ g, weightFamily π hπ f g * π h ∂haarProb G)
      = ∫ g, f (g * h⁻¹) • π g ∂haarProb G := by
        rw [← integral_mul_right_eq_self (fun g ↦ weightFamily π hπ f g * π h) h⁻¹]
        apply integral_congr_ae
        filter_upwards [] with g
        simp only [weightFamily_apply, smul_mul_assoc, ← map_mul, inv_mul_cancel_right]
    _ = ∫ g, f (h⁻¹ * g) • π g ∂haarProb G := by simp only [hclass]
    _ = ∫ g, π h * weightFamily π hπ f g ∂haarProb G := by
        rw [← integral_mul_left_eq_self (fun g ↦ π h * weightFamily π hπ f g) h⁻¹]
        apply integral_congr_ae
        filter_upwards [] with g
        simp only [weightFamily_apply, mul_smul_comm, ← map_mul, mul_inv_cancel_left]

/-- The action of a class function, packaged as a term of Mathlib's `ContIntertwiningMap`. -/
noncomputable def integratedIntertwiner (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    ContIntertwiningMap π π where
  __ := integratedOperator π hπ f
  isIntertwining' h := integratedOperator_comp π hπ hf h

@[simp]
theorem toContinuousLinearMap_integratedIntertwiner (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    (integratedIntertwiner π hπ hf).toContinuousLinearMap = integratedOperator π hπ f :=
  (rfl)

variable [CompleteSpace V]

section Naturality

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W]
  [SMulCommClass ℝ 𝕜 W] [CompleteSpace W]
  (rho : ContRepresentation 𝕜 G W) (hrho : Continuous rho)

/-- **Integrated operators are natural in the representation.** A continuous intertwiner commutes
with the operators obtained by integrating the same scalar function on its source and target. -/
theorem comp_integratedOperator
    (T : ContIntertwiningMap π rho) (f : C(G, 𝕜)) :
    T.toContinuousLinearMap.comp (integratedOperator π hπ f) =
      (integratedOperator rho hrho f).comp T.toContinuousLinearMap := by
  ext v
  have hint : Integrable (fun g ↦ f g • π g v) (haarProb G) := by
    exact integrable_continuousMap G
      ⟨fun g ↦ f g • π g v, f.continuous.smul (hπ.clm_apply continuous_const)⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    integratedOperator_apply, integratedOperator_apply,
    ← T.toContinuousLinearMap.integral_comp_comm hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  beta_reduce
  rw [map_smul]
  congr 1
  exact T.isIntertwining g v

end Naturality

end Integrated

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- Completeness of `V` is not an extra hypothesis on the results below: a finite-dimensional
normed space over an `RCLike` field is already complete. Mathlib keeps `FiniteDimensional.complete`
out of the global instance set, so it is installed here as a local instance instead. -/
local instance instCompleteSpaceIntegrated : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The trace of the integrated operator is the Haar integral of `f · χ_π`.** No hypothesis on
`f` is needed. This is what fixes the normalizing factor in
`ContRepresentation.integratedOperator_eq_smul_id`. -/
theorem trace_integratedOperator (f : C(G, 𝕜)) :
    LinearMap.trace 𝕜 V (integratedOperator π hπ f : V →ₗ[𝕜] V)
      = ∫ g, f g * character π hπ g ∂haarProb G := by
  have h := (traceCLM 𝕜 V).haarAverage_comp_comm (G := G) (weightFamily π hπ f)
  rw [← traceCLM_apply, integratedOperator, ← h, haarAverage_apply]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, weightFamily_apply, map_smul,
    traceCLM_apply, smul_eq_mul, character_apply]

variable [IsAlgClosed 𝕜] {f : C(G, 𝕜)}

/-- **A class function acts on a finite-dimensional irreducible representation by the scalar
`(dim V)⁻¹ · ∫ g, f g · χ_π g`.**

This is the operator form of the statement that the centre of the group algebra acts on an
irreducible by central characters; specialized to `f = conj χ_π` it gives the blockwise identities
of the character projection in
`TauCeti/RepresentationTheory/Compact/Character/Projection.lean`. -/
theorem integratedOperator_eq_smul_id (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    integratedOperator π hπ f
      = ((Module.finrank 𝕜 V : 𝕜)⁻¹ * ∫ g, f g * character π hπ g ∂haarProb G) •
        ContinuousLinearMap.id 𝕜 V := by
  have hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0 :=
    Representation.IsIrreducible.natCast_finrank_ne_zero hirr
  have h := π.eq_finrank_inv_mul_trace_smul_id_of_isIrreducible hdim hirr
    (integratedIntertwiner π hπ hf)
  rwa [toContinuousLinearMap_integratedIntertwiner, trace_integratedOperator] at h

/-- A class function whose Haar integral against the character vanishes acts as zero on an
irreducible representation. -/
theorem integratedOperator_eq_zero (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hirr : Representation.IsIrreducible π.toRepresentation)
    (hzero : ∫ g, f g * character π hπ g ∂haarProb G = 0) :
    integratedOperator π hπ f = 0 := by
  rw [integratedOperator_eq_smul_id π hπ hf hirr, hzero, mul_zero, zero_smul]

end Trace

end ContRepresentation
