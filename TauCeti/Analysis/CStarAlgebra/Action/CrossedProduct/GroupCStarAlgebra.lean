/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Multiplier
public import TauCeti.Analysis.CStarAlgebra.GroupCStarAlgebra.Full

/-!
# Isomorphism between `ℂ ⋊_id G` and the full group C⋆-algebra `C⋆(G)`

Let `G : Type u` be a locally compact group and `μ` a left Haar measure on `G`. Under the trivial
action `CStarAction.trivial (G := G) (A := ℂ)` of `G` on `ℂ`, the twisted convolution algebra
`CStarAction.ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ` has the untwisted
convolution product and modular-weighted involution of `GroupConvolutionAlgebra G μ`.

We prove that the resulting `L¹`-isometric ⋆-algebra isomorphism
`CStarAction.ConvolutionAlgebra.trivialComplexEquiv G μ` also preserves the universal C⋆-seminorms:

`GroupConvolutionAlgebra.fullSeminorm G μ (trivialComplexEquiv G μ f) =
  ConvolutionAlgebra.fullSeminorm (CStarAction.trivial (G := G) (A := ℂ)) μ f`.

The subtlety is that covariant representations `(π, U)` of `(ℂ, G, id)` in
`CStarAction.CovariantRepresentation` are allowed to have degenerate coefficient representations
`π : ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H)`. For any such `(π, U)` on `H : Type u`, the operator `p := π(1)` is a
self-adjoint idempotent commuting with every `U_g`, so the fixed-point subspace
`K := ker(id - p) : Submodule ℂ H` is a closed `U`-invariant Hilbert subspace in `Type u` on which
`π(z)` acts by scalar multiplication `z • id` and outside which `π ⋊ U` vanishes. Restricting `U` to
`K` via `ContRepresentation.subrepresentation` bounds `‖(π ⋊ U)(f)‖` by
`GroupConvolutionAlgebra.fullSeminorm G μ`, while `ContRepresentation.IsUnitary.toTrivialCovariant`
supplies the reverse inequality.

Completing yields the canonical isometric ⋆-isomorphism

`CStarAction.FullCrossedProduct.trivialComplexEquiv G μ :
  FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ ≃⋆ₐ[ℂ] FullGroupCStarAlgebra G μ`,

intertwining:

* the dense inclusions `FullCrossedProduct.of` and `FullGroupCStarAlgebra.of`,
* the canonical unitary group multiplier homomorphisms `FullCrossedProduct.groupMultiplier` and
  `FullGroupCStarAlgebra.groupMultiplier` via `DoubleCentralizer.congr`,
* the canonical coefficient multiplier `FullCrossedProduct.coefficientMultiplier _ μ z` with the
  scalar multiplier `algebraMap ℂ 𝓜(ℂ, FullGroupCStarAlgebra G μ) z`, and
* extended integrated covariant representations of `(ℂ, G, id)` with extended integrated unitary
  representations of `G`.

No Hausdorff, separability, second-countability, regularity or σ-finiteness assumption is imposed.

## Main definitions

* `TauCeti.CStarAction.ConvolutionAlgebra.trivialComplexEquiv`: the ⋆-algebra isomorphism
  `ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ ≃⋆ₐ[ℂ] GroupConvolutionAlgebra G μ`.
* `TauCeti.CStarAction.FullCrossedProduct.trivialComplexEquiv`: the canonical isometric
  ⋆-isomorphism `ℂ ⋊_id G ≃⋆ₐ[ℂ] C⋆(G)`.

## Main statements

* `TauCeti.CStarAction.ConvolutionAlgebra.fullSeminorm_trivialComplexEquiv`: `trivialComplexEquiv`
  preserves the universal C⋆-seminorm.
* `TauCeti.CStarAction.FullCrossedProduct.congr_trivialComplexEquiv_groupMultiplier` and
  `TauCeti.CStarAction.FullCrossedProduct.congr_trivialComplexEquiv_coefficientMultiplier`:
  `trivialComplexEquiv` intertwines the canonical group and coefficient multipliers.
* `ContRepresentation.IsUnitary.integratedFull_toTrivialCovariant`: extended integrated forms of
  unitary representations correspond under `trivialComplexEquiv`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Example 2.31 (`ℂ ⋊_id G ≃ C*(G)`).
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra MultiplierAlgebra

namespace TauCeti.CStarAction

universe u

section ConvolutionAlgebra

namespace ConvolutionAlgebra

section Basic

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

variable (G μ) in
/-- For the trivial action of `G` on `ℂ`, the twisted convolution algebra
`ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ` is canonically ⋆-isomorphic to
`GroupConvolutionAlgebra G μ`. -/
def trivialComplexEquiv :
    ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ ≃⋆ₐ[ℂ]
      GroupConvolutionAlgebra G μ where
  toFun f := GroupConvolutionAlgebra.toConv f.ofConv
  invFun f := toConv f.ofConv
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := by apply GroupConvolutionAlgebra.ext; simp
  map_smul' _ _ := by apply GroupConvolutionAlgebra.ext; simp
  map_mul' f g := by
    apply GroupConvolutionAlgebra.ext; ext s
    simp [GroupConvolutionAlgebra.ofConv_mul_apply]
  map_star' f := by
    apply GroupConvolutionAlgebra.ext; ext s
    simp [twistedInvolution_apply]

@[simp]
theorem ofConv_trivialComplexEquiv
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    (trivialComplexEquiv G μ f).ofConv = f.ofConv :=
  (rfl)

@[simp]
theorem ofConv_trivialComplexEquiv_symm (f : GroupConvolutionAlgebra G μ) :
    ((trivialComplexEquiv G μ).symm f).ofConv = f.ofConv :=
  (rfl)

@[simp]
theorem trivialComplexEquiv_toConv (f : CompactlySupportedContinuousMap G ℂ) :
    trivialComplexEquiv G μ (toConv f) = GroupConvolutionAlgebra.toConv f :=
  (rfl)

@[simp]
theorem trivialComplexEquiv_symm_toConv (f : CompactlySupportedContinuousMap G ℂ) :
    (trivialComplexEquiv G μ).symm (GroupConvolutionAlgebra.toConv f) = toConv f :=
  (rfl)

/-- `trivialComplexEquiv G μ` preserves the `L¹(μ)` norm. -/
@[simp]
theorem norm_trivialComplexEquiv
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    ‖trivialComplexEquiv G μ f‖ = ‖f‖ := by
  rw [GroupConvolutionAlgebra.norm_eq_integral_norm, norm_eq_integral_norm,
    ofConv_trivialComplexEquiv]

/-- `trivialComplexEquiv G μ` intertwines twisted left translation with left translation on
`GroupConvolutionAlgebra G μ`. -/
@[simp]
theorem trivialComplexEquiv_translateLIE [μ.IsMulLeftInvariant] (r : G)
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    trivialComplexEquiv G μ (translateLIE r f) =
      GroupConvolutionAlgebra.translateLIE r (trivialComplexEquiv G μ f) := by
  apply GroupConvolutionAlgebra.ext; ext s
  simp

/-- `trivialComplexEquiv G μ` turns left coefficient multiplication by `z : ℂ` into scalar
multiplication by `z`. -/
@[simp]
theorem trivialComplexEquiv_coefficientMul (z : ℂ)
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    trivialComplexEquiv G μ (coefficientMul z f) = z • trivialComplexEquiv G μ f := by
  apply GroupConvolutionAlgebra.ext; ext s
  simp

end Basic

end ConvolutionAlgebra

end ConvolutionAlgebra

end TauCeti.CStarAction

namespace ContRepresentation.IsUnitary

open TauCeti TauCeti.CStarAction

section TrivialCovariant

variable {G H : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- View a strongly continuous unitary representation `U` of `G` on `H` as a covariant
representation of the trivial action `CStarAction.trivial (G := G) (A := ℂ)` with unital scalar
coefficient representation `StarAlgHom.ofId ℂ (H →L[ℂ] H)`. -/
def toTrivialCovariant {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) :
    CovariantRepresentation (CStarAction.trivial (G := G) (A := ℂ)) H where
  coefficient := (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom
  group := U
  isUnitary := hU
  continuous_orbit := hcont
  covariance _ _ _ := by simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem toTrivialCovariant_coefficient {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (z : ℂ) :
    (hU.toTrivialCovariant hcont).coefficient z = z • ContinuousLinearMap.id ℂ H :=
  Algebra.algebraMap_eq_smul_one z

@[simp]
theorem toTrivialCovariant_group {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) :
    (hU.toTrivialCovariant hcont).group = U :=
  (rfl)

/-- The covariant integrated operator of `hU.toTrivialCovariant hcont` agrees with
`hU.integratedOperator hcont μ`. -/
@[simp]
theorem integratedOperator_toTrivialCovariant [MeasurableSpace G] [OpensMeasurableSpace G]
    {U : ContRepresentation ℂ G H} (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap G ℂ) :
    (hU.toTrivialCovariant hcont).integratedOperator μ f = hU.integratedOperator hcont μ f := by
  ext v
  simp [CovariantRepresentation.integratedOperator_apply, integratedOperator_apply]

/-- Under `ConvolutionAlgebra.trivialComplexEquiv G μ`, the covariant integrated ⋆-homomorphism of
`hU.toTrivialCovariant hcont` agrees with `hU.integratedStarAlgHom hcont μ`. -/
theorem integratedStarAlgHom_toTrivialCovariant [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    (hU.toTrivialCovariant hcont).integratedStarAlgHom μ f =
      hU.integratedStarAlgHom hcont μ (ConvolutionAlgebra.trivialComplexEquiv G μ f) := by
  rw [CovariantRepresentation.integratedStarAlgHom_apply, integratedStarAlgHom_apply,
    ConvolutionAlgebra.ofConv_trivialComplexEquiv, integratedOperator_toTrivialCovariant]

end TrivialCovariant

end ContRepresentation.IsUnitary

namespace TauCeti.CStarAction

universe u

namespace ConvolutionAlgebra

section FullSeminorm

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

/-- Every possibly degenerate covariant representation `(π, U)` of `(ℂ, G, id)` on a Hilbert space
`H : Type u` has integrated norm bounded by the universal group C⋆-seminorm of
`trivialComplexEquiv G μ f`, obtained by restricting `U` to the closed `U`-invariant subspace
`ker(id - π(1))`. -/
private theorem norm_integratedStarAlgHom_le_groupFullSeminorm {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : CovariantRepresentation (CStarAction.trivial (G := G) (A := ℂ)) H)
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    ‖P.integratedStarAlgHom μ f‖ ≤
      GroupConvolutionAlgebra.fullSeminorm G μ (trivialComplexEquiv G μ f) := by
  let p : H →L[ℂ] H := P.coefficient 1
  have hp_idem (v : H) : p (p v) = p v := by
    have hmul : p * p = p := by
      simp only [p, ← map_mul, one_mul]
    exact congr($hmul v)
  have hp_coeff (z : ℂ) : P.coefficient z = z • p := by
    have hz : z = z • (1 : ℂ) := by simp
    conv_lhs => rw [hz]
    exact map_smul P.coefficient z 1
  have hp_comm (g : G) (v : H) : P.group g (p v) = p (P.group g v) := by
    simpa [p] using P.covariance g 1 v
  have hp_norm (v : H) : ‖p v‖ ≤ ‖v‖ := by
    calc ‖p v‖ ≤ ‖p‖ * ‖v‖ := p.le_opNorm v
      _ ≤ ‖(1 : ℂ)‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le P.coefficient 1)
            (norm_nonneg v)
      _ = ‖v‖ := by simp
  let K : Submodule ℂ H := (ContinuousLinearMap.id ℂ H - p).ker
  have mem_K_iff (v : H) : v ∈ K ↔ p v = v := by
    simpa [K, LinearMap.mem_ker] using (sub_eq_zero (a := v) (b := p v)).trans eq_comm
  have hpv_mem (v : H) : p v ∈ K := (mem_K_iff (p v)).2 (hp_idem v)
  have hK_inv (g : G) (v : H) (hv : v ∈ K) : P.group g v ∈ K := by
    rw [mem_K_iff] at hv ⊢
    rw [← hp_comm, hv]
  have : CompleteSpace K := (ContinuousLinearMap.id ℂ H - p).isClosed_ker.completeSpace_coe
  let U_K : ContRepresentation ℂ G K := P.group.subrepresentation K hK_inv
  have hU_K : U_K.IsUnitary := P.isUnitary.subrepresentation hK_inv
  have hcont_K (w : K) : Continuous fun g => U_K g w := by
    rw [Topology.IsInducing.subtypeVal.continuous_iff]
    simp only [Function.comp_def, U_K, ContRepresentation.coe_subrepresentation_apply]
    exact P.continuous_orbit (w : H)
  have hint_eq (v : H) :
      P.integratedStarAlgHom μ f v =
        K.subtypeL
          (hU_K.integratedStarAlgHom hcont_K μ (trivialComplexEquiv G μ f)
            ⟨p v, hpv_mem v⟩) := by
    rw [CovariantRepresentation.integratedStarAlgHom_apply,
      CovariantRepresentation.integratedOperator_apply,
      ContRepresentation.IsUnitary.integratedStarAlgHom_apply,
      ContRepresentation.IsUnitary.integratedOperator_apply,
      ← K.subtypeL.integral_comp_comm
        (ContRepresentation.IsUnitary.integrable_integrand hcont_K μ _ ⟨p v, hpv_mem v⟩)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    dsimp only
    rw [ofConv_trivialComplexEquiv, map_smul, Submodule.subtypeL_apply,
      ContRepresentation.coe_subrepresentation_apply, hp_comm, hp_coeff, smul_apply]
  refine ContinuousLinearMap.opNorm_le_bound _
    (apply_nonneg (GroupConvolutionAlgebra.fullSeminorm G μ) _) fun v => ?_
  rw [hint_eq v, Submodule.subtypeL_apply, Submodule.norm_coe]
  calc ‖hU_K.integratedStarAlgHom hcont_K μ (trivialComplexEquiv G μ f) ⟨p v, hpv_mem v⟩‖
      ≤ ‖hU_K.integratedStarAlgHom hcont_K μ (trivialComplexEquiv G μ f)‖ *
          ‖(⟨p v, hpv_mem v⟩ : K)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ GroupConvolutionAlgebra.fullSeminorm G μ (trivialComplexEquiv G μ f) * ‖p v‖ :=
        mul_le_mul_of_nonneg_right
          (GroupConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm hU_K hcont_K _)
          (norm_nonneg _)
    _ ≤ GroupConvolutionAlgebra.fullSeminorm G μ (trivialComplexEquiv G μ f) * ‖v‖ :=
        mul_le_mul_of_nonneg_left (hp_norm v) (apply_nonneg _ _)

/-- `trivialComplexEquiv G μ` preserves the universal C⋆-seminorm. -/
@[simp]
theorem fullSeminorm_trivialComplexEquiv
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    GroupConvolutionAlgebra.fullSeminorm G μ (trivialComplexEquiv G μ f) =
      fullSeminorm (CStarAction.trivial (G := G) (A := ℂ)) μ f := by
  refine le_antisymm ?_ ?_
  · refine (GroupConvolutionAlgebra.fullSeminorm_le_iff (apply_nonneg _ f)).2
      fun H _ _ _ U hU hcont => ?_
    rw [← hU.integratedStarAlgHom_toTrivialCovariant hcont μ f]
    exact norm_integratedStarAlgHom_le_fullSeminorm (hU.toTrivialCovariant hcont) f
  · exact (fullSeminorm_le_iff (apply_nonneg _ _)).2 fun H _ _ _ P =>
      norm_integratedStarAlgHom_le_groupFullSeminorm P f

@[simp]
theorem fullSeminorm_trivialComplexEquiv_symm (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm (CStarAction.trivial (G := G) (A := ℂ)) μ ((trivialComplexEquiv G μ).symm f) =
      GroupConvolutionAlgebra.fullSeminorm G μ f := by
  simpa using (fullSeminorm_trivialComplexEquiv ((trivialComplexEquiv G μ).symm f)).symm

end FullSeminorm

end ConvolutionAlgebra

/-! ### The isomorphism `ℂ ⋊_id G ≃⋆ₐ[ℂ] C⋆(G)` -/

namespace FullCrossedProduct

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

private def trivialComplexToGroup (μ : Measure G) [μ.IsHaarMeasure] :
    FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ →⋆ₙₐ[ℂ]
      FullGroupCStarAlgebra G μ :=
  lift ((FullGroupCStarAlgebra.of G μ).comp
    (ConvolutionAlgebra.trivialComplexEquiv G μ).toNonUnitalStarAlgHom)
    fun f => by simp

private def groupToTrivialComplex (μ : Measure G) [μ.IsHaarMeasure] :
    FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ]
      FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ :=
  FullGroupCStarAlgebra.lift
    ((of (CStarAction.trivial (G := G) (A := ℂ)) μ).comp
      (ConvolutionAlgebra.trivialComplexEquiv G μ).symm.toNonUnitalStarAlgHom)
    fun f => by simp

private theorem groupToTrivialComplex_comp_trivialComplexToGroup (μ : Measure G)
    [μ.IsHaarMeasure] :
    (groupToTrivialComplex μ).comp (trivialComplexToGroup μ) =
      NonUnitalStarAlgHom.id ℂ
        (FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ) := by
  apply starAlgHom_ext
  ext f
  simp [trivialComplexToGroup, groupToTrivialComplex]

private theorem trivialComplexToGroup_comp_groupToTrivialComplex (μ : Measure G)
    [μ.IsHaarMeasure] :
    (trivialComplexToGroup μ).comp (groupToTrivialComplex μ) =
      NonUnitalStarAlgHom.id ℂ (FullGroupCStarAlgebra G μ) := by
  apply FullGroupCStarAlgebra.starAlgHom_ext
  ext f
  simp [trivialComplexToGroup, groupToTrivialComplex]

variable (G) in
/-- **Canonical isomorphism `ℂ ⋊_id G ≃⋆ₐ[ℂ] C⋆(G)`**: the full crossed product of `ℂ` by the
trivial action of a locally compact group `G` is canonically ⋆-isomorphic (hence isometric) to
`FullGroupCStarAlgebra G μ`. -/
def trivialComplexEquiv (μ : Measure G) [μ.IsHaarMeasure] :
    FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ ≃⋆ₐ[ℂ]
      FullGroupCStarAlgebra G μ :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (trivialComplexToGroup μ) (groupToTrivialComplex μ)
    (groupToTrivialComplex_comp_trivialComplexToGroup μ)
    (trivialComplexToGroup_comp_groupToTrivialComplex μ)

@[simp]
theorem trivialComplexEquiv_of (μ : Measure G) [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    trivialComplexEquiv G μ (of (CStarAction.trivial (G := G) (A := ℂ)) μ f) =
      FullGroupCStarAlgebra.of G μ (ConvolutionAlgebra.trivialComplexEquiv G μ f) :=
  lift_of _ _ f

@[simp]
theorem trivialComplexEquiv_symm_of (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    (trivialComplexEquiv G μ).symm (FullGroupCStarAlgebra.of G μ f) =
      of (CStarAction.trivial (G := G) (A := ℂ)) μ
        ((ConvolutionAlgebra.trivialComplexEquiv G μ).symm f) :=
  FullGroupCStarAlgebra.lift_of _ _ f

/-- `trivialComplexEquiv G μ` intertwines the canonical unitary group multiplier
`FullCrossedProduct.groupMultiplier` on `ℂ ⋊_id G` with `FullGroupCStarAlgebra.groupMultiplier` on
`C⋆(G)`. -/
@[simp]
theorem congr_trivialComplexEquiv_groupMultiplier (μ : Measure G) [μ.IsHaarMeasure] (r : G) :
    DoubleCentralizer.congr (trivialComplexEquiv G μ)
        (groupMultiplier (CStarAction.trivial (G := G) (A := ℂ)) μ r :
          𝓜(ℂ, FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ)) =
      (FullGroupCStarAlgebra.groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) := by
  refine DoubleCentralizer.ext_fst fun x => ?_
  induction x using FullGroupCStarAlgebra.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    rw [DoubleCentralizer.congr_apply_fst, trivialComplexEquiv_symm_of, groupMultiplier_fst_of,
      trivialComplexEquiv_of, ConvolutionAlgebra.trivialComplexEquiv_translateLIE,
      StarAlgEquiv.apply_symm_apply, FullGroupCStarAlgebra.groupMultiplier_fst_of]

/-- `trivialComplexEquiv G μ` sends the canonical coefficient multiplier
`FullCrossedProduct.coefficientMultiplier _ μ z` on `ℂ ⋊_id G` to the scalar multiplier
`algebraMap ℂ 𝓜(ℂ, FullGroupCStarAlgebra G μ) z` on `C⋆(G)`. -/
@[simp]
theorem congr_trivialComplexEquiv_coefficientMultiplier (μ : Measure G) [μ.IsHaarMeasure]
    (z : ℂ) :
    DoubleCentralizer.congr (trivialComplexEquiv G μ)
        (coefficientMultiplier (CStarAction.trivial (G := G) (A := ℂ)) μ z) =
      algebraMap ℂ 𝓜(ℂ, FullGroupCStarAlgebra G μ) z := by
  refine DoubleCentralizer.ext_fst fun x => ?_
  induction x using FullGroupCStarAlgebra.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    rw [DoubleCentralizer.congr_apply_fst, trivialComplexEquiv_symm_of,
      coefficientMultiplier_fst_of, trivialComplexEquiv_of,
      ConvolutionAlgebra.trivialComplexEquiv_coefficientMul,
      StarAlgEquiv.apply_symm_apply, map_smul, Algebra.algebraMap_eq_smul_one,
      DoubleCentralizer.smul_fst, DoubleCentralizer.one_fst, smul_apply,
      one_apply_eq_self]

end FullCrossedProduct

end TauCeti.CStarAction

namespace ContRepresentation.IsUnitary

universe u

open TauCeti TauCeti.CStarAction

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Under `FullCrossedProduct.trivialComplexEquiv G μ`, the extended integrated covariant
representation of `hU.toTrivialCovariant hcont` on `ℂ ⋊_id G` coincides with
`hU.integratedGroupCStar hcont μ` on `C⋆(G)`. -/
@[simp]
theorem integratedFull_toTrivialCovariant {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (x : FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    (hU.toTrivialCovariant hcont).integratedFull μ x =
      hU.integratedGroupCStar hcont μ (FullCrossedProduct.trivialComplexEquiv G μ x) := by
  induction x using FullCrossedProduct.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    rw [CovariantRepresentation.integratedFull_of, FullCrossedProduct.trivialComplexEquiv_of,
      hU.integratedGroupCStar_of, hU.integratedStarAlgHom_toTrivialCovariant]

end ContRepresentation.IsUnitary

end
