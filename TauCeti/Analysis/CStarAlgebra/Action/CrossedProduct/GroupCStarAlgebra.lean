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

Under the trivial action `CStarAction.trivial (G := G) (A := ℂ)`, the `L¹`-isometric ⋆-isomorphism
`ConvolutionAlgebra.trivialComplexEquiv G μ` preserves universal C⋆-seminorms (by restricting any
covariant representation `(π, U)` to `ker(id - π(1))`), yielding `ℂ ⋊_id G ≃⋆ₐ[ℂ] C⋆(G)`.

## Main definitions and statements

* `TauCeti.CStarAction.ConvolutionAlgebra.trivialComplexEquiv` and
  `fullSeminorm_trivialComplexEquiv`: `L¹` and universal-seminorm ⋆-isomorphism on `C_c(G, ℂ)`.
* `ContRepresentation.IsUnitary.toTrivialCovariant`: scalar-coefficient covariant representation.
* `TauCeti.CStarAction.FullCrossedProduct.trivialComplexEquiv`: `ℂ ⋊_id G ≃⋆ₐ[ℂ] C⋆(G)`, with
  compatibility for `of`, `groupMultiplier`, `coefficientMultiplier` and `integratedFull`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Example 2.31 (`ℂ ⋊_id G ≃ C*(G)`).
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra MultiplierAlgebra

namespace TauCeti.CStarAction

universe u

namespace ConvolutionAlgebra

section Basic

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

variable (G μ) in
/-- For the trivial action of `G` on `ℂ`, `ConvolutionAlgebra (CStarAction.trivial) μ` is
canonically ⋆-isomorphic to `GroupConvolutionAlgebra G μ`. -/
def trivialComplexEquiv :
    ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ ≃⋆ₐ[ℂ]
      GroupConvolutionAlgebra G μ where
  toFun f := GroupConvolutionAlgebra.toConv f.ofConv
  invFun f := toConv f.ofConv
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := GroupConvolutionAlgebra.ext <| by simp
  map_smul' _ _ := GroupConvolutionAlgebra.ext <| by simp
  map_mul' _ _ := GroupConvolutionAlgebra.ext <| CompactlySupportedContinuousMap.ext fun _ => by
    simp [GroupConvolutionAlgebra.ofConv_mul_apply]
  map_star' _ := GroupConvolutionAlgebra.ext <| CompactlySupportedContinuousMap.ext fun _ => by
    simp [twistedInvolution_apply]

@[simp] theorem ofConv_trivialComplexEquiv
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    (trivialComplexEquiv G μ f).ofConv = f.ofConv := (rfl)

@[simp] theorem ofConv_trivialComplexEquiv_symm (f : GroupConvolutionAlgebra G μ) :
    ((trivialComplexEquiv G μ).symm f).ofConv = f.ofConv := (rfl)

@[simp] theorem trivialComplexEquiv_toConv (f : CompactlySupportedContinuousMap G ℂ) :
    trivialComplexEquiv G μ (toConv f) = GroupConvolutionAlgebra.toConv f := (rfl)

@[simp] theorem trivialComplexEquiv_symm_toConv (f : CompactlySupportedContinuousMap G ℂ) :
    (trivialComplexEquiv G μ).symm (GroupConvolutionAlgebra.toConv f) = toConv f := (rfl)

/-- `trivialComplexEquiv` is an isometry for the `L¹(μ)` norms. -/
@[simp] theorem norm_trivialComplexEquiv
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    ‖trivialComplexEquiv G μ f‖ = ‖f‖ := by
  rw [GroupConvolutionAlgebra.norm_eq_integral_norm, norm_eq_integral_norm,
    ofConv_trivialComplexEquiv]

@[simp] theorem trivialComplexEquiv_translateLIE [μ.IsMulLeftInvariant] (r : G)
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    trivialComplexEquiv G μ (translateLIE r f) =
      GroupConvolutionAlgebra.translateLIE r (trivialComplexEquiv G μ f) :=
  GroupConvolutionAlgebra.ext <| CompactlySupportedContinuousMap.ext fun _ => by simp

@[simp] theorem trivialComplexEquiv_coefficientMul (z : ℂ)
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    trivialComplexEquiv G μ (coefficientMul z f) = z • trivialComplexEquiv G μ f :=
  GroupConvolutionAlgebra.ext <| CompactlySupportedContinuousMap.ext fun _ => by simp

end Basic

end ConvolutionAlgebra

end TauCeti.CStarAction

namespace ContRepresentation.IsUnitary

open TauCeti TauCeti.CStarAction

section TrivialCovariant

variable {G H : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- View a strongly continuous unitary representation `U` of `G` on `H` as a covariant
representation of `CStarAction.trivial (G := G) (A := ℂ)` with scalar coefficients. -/
def toTrivialCovariant {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) :
    CovariantRepresentation (CStarAction.trivial (G := G) (A := ℂ)) H where
  coefficient := (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom
  group := U
  isUnitary := hU
  continuous_orbit := hcont
  covariance _ _ _ := by simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem toTrivialCovariant_coefficient {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (z : ℂ) :
    (hU.toTrivialCovariant hcont).coefficient z = z • ContinuousLinearMap.id ℂ H :=
  Algebra.algebraMap_eq_smul_one z

@[simp] theorem toTrivialCovariant_group {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) : (hU.toTrivialCovariant hcont).group = U := (rfl)

@[simp] theorem integratedOperator_toTrivialCovariant [MeasurableSpace G] [OpensMeasurableSpace G]
    {U : ContRepresentation ℂ G H} (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap G ℂ) :
    (hU.toTrivialCovariant hcont).integratedOperator μ f = hU.integratedOperator hcont μ f := by
  ext v; simp [CovariantRepresentation.integratedOperator_apply, integratedOperator_apply]

theorem integratedStarAlgHom_toTrivialCovariant [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    (hU.toTrivialCovariant hcont).integratedStarAlgHom μ f =
      hU.integratedStarAlgHom hcont μ (ConvolutionAlgebra.trivialComplexEquiv G μ f) := by
  simp [CovariantRepresentation.integratedStarAlgHom_apply]

end TrivialCovariant

end ContRepresentation.IsUnitary

namespace TauCeti.CStarAction

universe u

namespace ConvolutionAlgebra

section FullSeminorm

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

private theorem norm_integratedStarAlgHom_le_groupFullSeminorm {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : CovariantRepresentation (CStarAction.trivial (G := G) (A := ℂ)) H)
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    ‖P.integratedStarAlgHom μ f‖ ≤
      GroupConvolutionAlgebra.fullSeminorm G μ (trivialComplexEquiv G μ f) := by
  let p : H →L[ℂ] H := P.coefficient 1
  have hp_idem (v : H) : p (p v) = p v := congr($(show p * p = p by simp [p, ← map_mul]) v)
  have hp_coeff (z : ℂ) : P.coefficient z = z • p := by
    simpa [p] using map_smul P.coefficient z (1 : ℂ)
  have hp_comm (g : G) (v : H) : P.group g (p v) = p (P.group g v) := by
    simpa [p] using P.covariance g 1 v
  have hp_norm (v : H) : ‖p v‖ ≤ ‖v‖ :=
    (p.le_opNorm v).trans <| (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le P.coefficient 1) (norm_nonneg v)).trans_eq (by simp)
  let K : Submodule ℂ H := (ContinuousLinearMap.id ℂ H - p).ker
  have mem_K_iff {v : H} : v ∈ K ↔ p v = v := by
    simpa [K, LinearMap.mem_ker, sub_eq_zero] using eq_comm
  have hK_inv (g : G) (v : H) (hv : v ∈ K) : P.group g v ∈ K :=
    mem_K_iff.2 (by rw [← hp_comm, mem_K_iff.1 hv])
  have : CompleteSpace K := (ContinuousLinearMap.id ℂ H - p).isClosed_ker.completeSpace_coe
  let U_K : ContRepresentation ℂ G K := P.group.subrepresentation K hK_inv
  have hU_K : U_K.IsUnitary := P.isUnitary.subrepresentation hK_inv
  have hcont_K (w : K) : Continuous fun g => U_K g w :=
    Topology.IsInducing.subtypeVal.continuous_iff.2
      (by simpa [U_K, Function.comp_def] using P.continuous_orbit (w : H))
  refine ContinuousLinearMap.opNorm_le_bound _
    (apply_nonneg (GroupConvolutionAlgebra.fullSeminorm G μ) _) fun v => ?_
  have hint_eq : P.integratedStarAlgHom μ f v = K.subtypeL
      (hU_K.integratedStarAlgHom hcont_K μ (trivialComplexEquiv G μ f)
        ⟨p v, mem_K_iff.2 (hp_idem v)⟩) := by
    rw [CovariantRepresentation.integratedStarAlgHom_apply,
      CovariantRepresentation.integratedOperator_apply,
      ContRepresentation.IsUnitary.integratedStarAlgHom_apply,
      ContRepresentation.IsUnitary.integratedOperator_apply,
      ← K.subtypeL.integral_comp_comm (U_K.integrable_integrand hcont_K μ _ _)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    dsimp only
    rw [ofConv_trivialComplexEquiv, map_smul, Submodule.subtypeL_apply,
      ContRepresentation.coe_subrepresentation_apply, hp_comm, hp_coeff, smul_apply]
  rw [hint_eq, Submodule.subtypeL_apply, Submodule.norm_coe]
  exact (ContinuousLinearMap.le_opNorm _ _).trans <|
    (mul_le_mul_of_nonneg_right
      (GroupConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm hU_K hcont_K _)
      (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left (hp_norm v) (apply_nonneg _ _))

/-- Under `trivialComplexEquiv`, the full crossed-product seminorm of `(ℂ, G, id)` equals the
universal group C⋆-seminorm on `GroupConvolutionAlgebra G μ`. -/
@[simp] theorem fullSeminorm_trivialComplexEquiv
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    GroupConvolutionAlgebra.fullSeminorm G μ (trivialComplexEquiv G μ f) =
      fullSeminorm (CStarAction.trivial (G := G) (A := ℂ)) μ f :=
  le_antisymm
    ((GroupConvolutionAlgebra.fullSeminorm_le_iff (apply_nonneg _ f)).2 fun _ _ _ _ _ hU hcont => by
      rw [← hU.integratedStarAlgHom_toTrivialCovariant hcont μ f]
      exact norm_integratedStarAlgHom_le_fullSeminorm (hU.toTrivialCovariant hcont) f)
    ((fullSeminorm_le_iff (apply_nonneg _ _)).2 fun _ _ _ _ P =>
      norm_integratedStarAlgHom_le_groupFullSeminorm P f)

@[simp] theorem fullSeminorm_trivialComplexEquiv_symm (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm (CStarAction.trivial (G := G) (A := ℂ)) μ ((trivialComplexEquiv G μ).symm f) =
      GroupConvolutionAlgebra.fullSeminorm G μ f := by
  simpa using (fullSeminorm_trivialComplexEquiv ((trivialComplexEquiv G μ).symm f)).symm

end FullSeminorm

end ConvolutionAlgebra

namespace FullCrossedProduct

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

private def trivialComplexToGroup (μ : Measure G) [μ.IsHaarMeasure] :
    FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ →⋆ₙₐ[ℂ]
      FullGroupCStarAlgebra G μ :=
  lift ((FullGroupCStarAlgebra.of G μ).comp
    (ConvolutionAlgebra.trivialComplexEquiv G μ).toNonUnitalStarAlgHom) fun _ => by simp

private def groupToTrivialComplex (μ : Measure G) [μ.IsHaarMeasure] :
    FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ]
      FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ :=
  FullGroupCStarAlgebra.lift
    ((of (CStarAction.trivial (G := G) (A := ℂ)) μ).comp
      (ConvolutionAlgebra.trivialComplexEquiv G μ).symm.toNonUnitalStarAlgHom) fun _ => by simp

variable (G) in
/-- **Canonical isomorphism `ℂ ⋊_id G ≃⋆ₐ[ℂ] C⋆(G)`**: the full crossed product of `ℂ` by the
trivial action of `G` is canonically ⋆-isomorphic to `FullGroupCStarAlgebra G μ`. -/
def trivialComplexEquiv (μ : Measure G) [μ.IsHaarMeasure] :
    FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ ≃⋆ₐ[ℂ]
      FullGroupCStarAlgebra G μ :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (trivialComplexToGroup μ) (groupToTrivialComplex μ)
    (starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by
      simp [trivialComplexToGroup, groupToTrivialComplex])
    (FullGroupCStarAlgebra.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by
      simp [trivialComplexToGroup, groupToTrivialComplex])

@[simp] theorem trivialComplexEquiv_of (μ : Measure G) [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    trivialComplexEquiv G μ (of (CStarAction.trivial (G := G) (A := ℂ)) μ f) =
      FullGroupCStarAlgebra.of G μ (ConvolutionAlgebra.trivialComplexEquiv G μ f) := lift_of _ _ f

@[simp] theorem trivialComplexEquiv_symm_of (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    (trivialComplexEquiv G μ).symm (FullGroupCStarAlgebra.of G μ f) =
      of (CStarAction.trivial (G := G) (A := ℂ)) μ
        ((ConvolutionAlgebra.trivialComplexEquiv G μ).symm f) := FullGroupCStarAlgebra.lift_of _ _ f

/-- `trivialComplexEquiv` intertwines the crossed-product and group-C⋆ unitary generator maps
`groupMultiplier`. -/
@[simp] theorem congr_trivialComplexEquiv_groupMultiplier (μ : Measure G) [μ.IsHaarMeasure]
    (r : G) :
    DoubleCentralizer.congr (trivialComplexEquiv G μ)
        (groupMultiplier (CStarAction.trivial (G := G) (A := ℂ)) μ r :
          𝓜(ℂ, FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ)) =
      (FullGroupCStarAlgebra.groupMultiplier G μ r : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) := by
  refine DoubleCentralizer.ext_fst fun x => ?_
  induction x using FullGroupCStarAlgebra.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

/-- `trivialComplexEquiv` maps the scalar `coefficientMultiplier` of `ℂ ⋊_id G` to scalar multiples
of the identity multiplier in `𝓜(ℂ, C⋆(G))`. -/
@[simp] theorem congr_trivialComplexEquiv_coefficientMultiplier (μ : Measure G) [μ.IsHaarMeasure]
    (z : ℂ) :
    DoubleCentralizer.congr (trivialComplexEquiv G μ)
        (coefficientMultiplier (CStarAction.trivial (G := G) (A := ℂ)) μ z) =
      algebraMap ℂ 𝓜(ℂ, FullGroupCStarAlgebra G μ) z := by
  refine DoubleCentralizer.ext_fst fun x => ?_
  induction x using FullGroupCStarAlgebra.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp [Algebra.algebraMap_eq_smul_one]

/-- `trivialComplexEquiv` intertwines the extended integrated representation on `ℂ ⋊_id G` with
`integratedGroupCStar` on `C⋆(G)`. -/
@[simp] theorem _root_.ContRepresentation.IsUnitary.integratedFull_toTrivialCovariant {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U : ContRepresentation ℂ G H} (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [μ.IsHaarMeasure]
    (x : FullCrossedProduct (CStarAction.trivial (G := G) (A := ℂ)) μ) :
    (hU.toTrivialCovariant hcont).integratedFull μ x =
      hU.integratedGroupCStar hcont μ (trivialComplexEquiv G μ x) := by
  induction x using FullCrossedProduct.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp [hU.integratedStarAlgHom_toTrivialCovariant]

end FullCrossedProduct

end TauCeti.CStarAction

end
