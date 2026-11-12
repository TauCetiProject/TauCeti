/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.Basic
public import TauCeti.RepresentationTheory.Compact.Integrated
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Compact.UnitaryModel

/-!
# The character projections

The conjugate `conj χ_π` of the character of a continuous representation `π` of a compact group is
a class function, so it acts on a finite-dimensional irreducible representation by a scalar
(`ContRepresentation.integratedOperator_eq_smul_id`, from
`TauCeti/RepresentationTheory/Compact/Integrated.lean`). Its Haar integral against another character
`χ_ρ` is the `L²` inner product of the two characters, so the character orthogonality relations of
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean` evaluate that scalar. This file records
the two resulting **character projections**, for `π` finite-dimensional:

* for `π` irreducible, the kernel `dim V_π · conj χ_π` acts as the identity on `V_π` itself;
* `conj χ_π` acts as zero on a representation `ρ` admitting no nonzero continuous intertwiner
  `ρ → π`, where `ρ` need not be finite-dimensional.

Neither identity asks `π` to be unitary or its carrier to be an inner product space.

These are the two blockwise identities from which the isotypic projectors are built. Their assembly
on a reducible representation is carried out in
`TauCeti/RepresentationTheory/Compact/Character/IsotypicProjection.lean`.

## Main results

* `ContRepresentation.integral_star_character_mul_character`: pairing a character with the
  conjugate of another one is the `L²` inner product of the two characters.
* `ContRepresentation.integratedOperator_star_character_self`: `conj χ_π` acts on `V_π` by
  the scalar `(dim V_π)⁻¹`, so that, by
  `ContRepresentation.finrank_smul_integratedOperator_star_character_self`, the kernel
  `dim V_π · conj χ_π` acts as the identity on `V_π`.
* `ContRepresentation.integratedOperator_star_character_eq_zero`: `conj χ_π` acts as zero on a
  representation admitting no nonzero continuous intertwiner into `π`.

## Implementation notes

The scalar in `ContRepresentation.integratedOperator_eq_smul_id` is
`(dim V)⁻¹ · ∫ f · χ_π`, not `∫ f · conj χ_π`: the integrand pairs the acting function with the
character itself, and the conjugation appears only here, where the acting function is specialized
to `conj χ_π` and `ContRepresentation.integral_star_character_mul_character` identifies the
integral with Mathlib's sesquilinear `L²` inner product of the two characters.

The self-action identity reads the scalar off the first character orthogonality relation, which
holds for any finite-dimensional irreducible `π`. The vanishing identity passes from intertwiners
to integrals of matrix coefficients, which needs a unitary representation on an inner product
space; it is brought to bear on a general `π` by replacing it with a unitary conjugate on the
standard model `EuclideanSpace 𝕜 (Fin (dim V))`
(`ContRepresentation.exists_isUnitary_congr_euclideanSpace`), which has the same character
(`ContinuousLinearEquiv.character_congr`) and, up to that conjugation, the same intertwiners from
`ρ`. The vanishing on `ρ` is detected by continuous linear functionals on its carrier, which need
not be an inner product space.

## References

These character-weighted averages give the operators used for isotypic projection and
class-function completeness. The mathematical development follows Daniel Bump, *Lie Groups*, second
edition, Chapter 2, and T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*,
Springer GTM 98 (1985), Chapter II.
-/

public section

open _root_.ContRepresentation

open MeasureTheory
open scoped InnerProductSpace

open TauCeti

namespace ContRepresentation

section Projection

variable {𝕜 G V W : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]

local instance instCompleteSpaceProjectionSource : CompleteSpace V :=
  FiniteDimensional.completeSpace 𝕜 V

local instance instCompleteSpaceProjectionTarget : CompleteSpace W :=
  FiniteDimensional.completeSpace 𝕜 W

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
  (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)

include hπ

omit [IsAlgClosed 𝕜] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] in
/-- The conjugate of a character is a class function: the hypothesis in the shape that
`ContRepresentation.integratedOperator_eq_smul_id` takes. -/
private theorem star_character_conj (g h : G) :
    (star (character π hπ)) (h * g * h⁻¹) = (star (character π hπ)) g := by
  rw [ContinuousMap.star_apply, ContinuousMap.star_apply, character_conj π hπ g h]

include hρ in
omit [IsAlgClosed 𝕜] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [NormedSpace ℝ W]
  [SMulCommClass ℝ 𝕜 W] in
/-- Pairing a representation's character with the conjugate of another one's is the `L²` inner
product of the two characters, in Mathlib's convention `⟪F, H⟫ = ∫ H · conj F`. This is what turns
the character orthogonality relations into statements about
`ContRepresentation.integratedOperator`. -/
theorem integral_star_character_mul_character :
    ∫ g, (star (character π hπ)) g * character ρ hρ g ∂haarProb G
      = ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 := by
  rw [characterLp_def, characterLp_def, ContinuousMap.inner_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  -- `integral_congr_ae` leaves the two integrands applied but unreduced.
  beta_reduce
  rw [ContinuousMap.star_apply, RCLike.star_def, mul_comm]

include hρ in
omit [IsAlgClosed 𝕜] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- **The character projection kills an inequivalent representation.** If there is no nonzero
continuous intertwiner `ρ → π`, the conjugate character of `π` acts as zero on `ρ`. Neither
unitarity of `π`, irreducibility or finite-dimensionality of `ρ`, nor algebraic closedness of `𝕜`
is assumed.

Schur's lemma is not invoked for the intertwiner hypothesis; it is what supplies it for a pair of
inequivalent irreducibles. -/
theorem integratedOperator_star_character_eq_zero
    (hdistinct : ∀ φ : ContIntertwiningMap ρ π, φ.toContinuousLinearMap = 0) :
    integratedOperator ρ hρ (star (character π hπ)) = 0 := by
  -- `π` is replaced by a unitary conjugate `π'` on a standard model, which has the same character
  -- and still admits no nonzero intertwiner from `ρ`. The operator is not evaluated as a scalar --
  -- which would need Schur's scalar lemma, hence an algebraically closed `𝕜` -- but paired against
  -- a continuous functional `ℓ` on `W`: the diagonal matrix coefficients that make up `conj χ_π'`
  -- (`ContRepresentation.star_character`) pair with `g ↦ ℓ (ρ g v)` to matrix entries of the
  -- averages of the rank-one operators `w ↦ ℓ w • bᵢ`, which are intertwiners `ρ → π'`.
  obtain ⟨f, hunitary⟩ := exists_isUnitary_congr_euclideanSpace π hπ
  have hπ' := f.continuous_congr hπ
  rw [← f.character_congr hπ']
  set π' := ContinuousLinearEquiv.congr f π
  let b := EuclideanSpace.basisFun (Fin (Module.finrank 𝕜 V)) 𝕜
  refine ContinuousLinearMap.ext fun v ↦ ?_
  by_cases hW : CompleteSpace W
  swap
  · rw [integratedOperator_apply, integral_of_not_completeSpace hW]
    rfl
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun ℓ ↦ ?_
  have hterm (i : Fin (Module.finrank 𝕜 V)) :
      ∫ g, matrixCoeff π' hπ' (b i) (b i) g * ℓ (ρ g v) ∂haarProb G = 0 := by
    have hzero : averageOperator ρ hρ π' hπ' (ℓ.smulRight (b i)) v = 0 := by
      have h := congr($(hdistinct (((π.congrEquiv f).symm.toContIntertwiningMap).comp
        (averageIntertwiner ρ hρ π' hπ' (ℓ.smulRight (b i))))) v)
      simpa using h
    have hint : Integrable (fun g ↦ π' g⁻¹ (ℓ.smulRight (b i) (ρ g v))) (haarProb G) :=
      integrable_continuousMap G ⟨fun g ↦ π' g⁻¹ (ℓ.smulRight (b i) (ρ g v)),
        (hπ'.comp continuous_inv).clm_apply
          ((ℓ.smulRight (b i)).continuous.comp (hρ.clm_apply continuous_const))⟩
    have h := congrArg (fun x ↦ ⟪b i, x⟫_𝕜) hzero
    simp only [averageOperator_apply, inner_zero_right] at h
    rw [← integral_inner hint] at h
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)) h
    -- `integral_congr_ae` leaves the two integrands applied but unreduced.
    beta_reduce
    rw [ContinuousLinearMap.smulRight_apply, map_smul, inner_smul_right, matrixCoeff_apply,
      hunitary.inner_map_left, mul_comm]
  have hint : Integrable (fun g ↦ (star (character π' hπ')) g • ρ g v) (haarProb G) :=
    integrable_continuousMap G ⟨fun g ↦ (star (character π' hπ')) g • ρ g v,
      (star (character π' hπ')).continuous.smul (hρ.clm_apply continuous_const)⟩
  rw [integratedOperator_apply, ← ℓ.integral_comp_comm hint]
  simp only [map_smul, smul_eq_mul, star_character π' hπ' b, ContinuousMap.coe_sum,
    Finset.sum_apply, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · exact Finset.sum_eq_zero fun i _ ↦ hterm i
  · exact integrable_continuousMap G ⟨fun g ↦ matrixCoeff π' hπ' (b i) (b i) g * ℓ (ρ g v),
      (matrixCoeff π' hπ' (b i) (b i)).continuous.mul
        (ℓ.continuous.comp (hρ.clm_apply continuous_const))⟩

/-- **The conjugate character acts on its own representation by the inverse dimension.** For a
finite-dimensional irreducible representation of dimension `d`, the integrated operator of
`conj χ_π` on `V_π` is `d⁻¹ • id`. Neither unitarity of `π` nor an inner product on its carrier is
assumed, since none is in the first character orthogonality relation
`ContRepresentation.character_orthonormal_self`.

The scalar is `d⁻¹` rather than `1` exactly because the character has `L²` norm one: the projection
kernel that acts as the identity is `d · conj χ_π`, which is
`ContRepresentation.finrank_smul_integratedOperator_star_character_self`. -/
theorem integratedOperator_star_character_self
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    integratedOperator π hπ (star (character π hπ))
      = (Module.finrank 𝕜 V : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 V := by
  rw [integratedOperator_eq_smul_id π hπ (star_character_conj π hπ) hirr,
    integral_star_character_mul_character π hπ π hπ, character_orthonormal_self π hπ hirr, mul_one]

/-- **The block projection, normalized.** For a finite-dimensional irreducible `π`, the
kernel `dim V_π · conj χ_π` acts as the identity on `V_π`; together with
`ContRepresentation.integratedOperator_star_character_eq_zero`, which makes it act as zero
on a representation with no nonzero intertwiner into `π`, these are the two blockwise
identities that characterize the isotypic projector attached to `π`. Assembling them into a
projector on a reducible representation is done in
`TauCeti/RepresentationTheory/Compact/Character/IsotypicProjection.lean`. -/
theorem finrank_smul_integratedOperator_star_character_self
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    (Module.finrank 𝕜 V : 𝕜) • integratedOperator π hπ (star (character π hπ))
      = ContinuousLinearMap.id 𝕜 V := by
  let : Representation.IsIrreducible π.toRepresentation := hirr
  have hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0 :=
    Representation.IsIrreducible.natCast_finrank_ne_zero hirr
  rw [integratedOperator_star_character_self π hπ hirr, smul_smul,
    mul_inv_cancel₀ hdim, one_smul]

end Projection

end ContRepresentation
