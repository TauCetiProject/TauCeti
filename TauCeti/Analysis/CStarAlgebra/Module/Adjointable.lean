/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Basic

/-!
# Adjointable operators on Hilbert C⋆-modules: norm, C⋆-algebra, order, and projections

Building on the algebraic foundations in `TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Basic`,
this file develops the normed, C⋆-algebraic, order, and spectral theory of
`TauCeti.AdjointableMap A E F`:

* The operator norm is induced by the isometric embedding into `E →L[ℂ] F`
  (`AdjointableMap.toContinuousLinearMapₗᵢ`), taking adjoints is a conjugate-linear isometric
  equivalence `AdjointableMap.adjointₗᵢ`, and `‖T.adjoint.comp T‖ = ‖T‖ ^ 2`.
* On complete modules, `AdjointableMap A E F` is complete, plain adjoint pairs upgrade to bundled
  adjointable maps (`AdjointableMap.ofAdjointPair`, `AdjointableMap.exists_coe_eq_iff`), and
  `AdjointableMap A E E` is a unital C⋆-algebra (paralleling `DoubleCentralizer` in
  `Mathlib.Analysis.CStarAlgebra.Multiplier`) equipped with its spectral `PartialOrder` and
  `StarOrderedRing` instances (paralleling `CStarMatrix` in
  `Mathlib.Analysis.CStarAlgebra.CStarMatrix`).
* Positivity is characterized by `0 ≤ T ↔ ∀ x, 0 ≤ ⟪x, T x⟫_A` (`AdjointableMap.nonneg_iff`), and
  every rectangular operator `T` has a positive modulus `T.abs = CFC.sqrt (T.adjoint.comp T)`.
* Adjointable orthogonal projections (`IsStarProjection P`) are characterized by
  `⟪P x, y⟫_A = ⟪P x, P y⟫_A`, uniquely determined by their range, and ordered by range inclusion.
* Adjointable isometries (`T.adjoint.comp T = .id`) are characterized by preserving module inner
  products (`⟪T x, T y⟫_A = ⟪x, y⟫_A`), equivalently diagonal inner products
  `⟪T x, T x⟫_A = ⟪x, x⟫_A`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1, 3, 4.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2 (Definitions 2.16–2.17, Lemma 2.18, Proposition 2.21).
* Bruce Blackadar, *Operator Algebras*, Section II.7.1.
* The proof of `AdjointableMap.nonneg_iff` adapts `CStarMatrix.nonneg_iff_forall_sum_nonneg` from
  `TauCeti.Analysis.CStarAlgebra.CStarMatrix`.
-/

public section

open CStarModule MulOpposite

namespace TauCeti

namespace AdjointableMap

/-! ### Operator norm, isometric forgetful map, and C⋆-identity -/

section NormInduced

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

/-- The operator norm on `AdjointableMap A E F` is induced by the forgetful embedding into
`E →L[ℂ] F`. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (AdjointableMap A E F) :=
  fast_instance% NormedAddCommGroup.induced (AdjointableMap A E F) (E →L[ℂ] F)
    toContinuousLinearMapAddMonoidHom fun _ _ h =>
      toContinuousLinearMap_injective <| by
        simpa only [toContinuousLinearMapAddMonoidHom_apply] using h

@[simp]
theorem norm_toContinuousLinearMap (T : AdjointableMap A E F) :
    ‖T.toContinuousLinearMap‖ = ‖T‖ := by
  rw [← toContinuousLinearMapAddMonoidHom_apply]; rfl

@[simp]
theorem nnNorm_toContinuousLinearMap (T : AdjointableMap A E F) :
    ‖T.toContinuousLinearMap‖₊ = ‖T‖₊ :=
  Subtype.ext (norm_toContinuousLinearMap T)

theorem isometry_toContinuousLinearMap :
    Isometry (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) :=
  Isometry.of_dist_eq fun T S => by
    rw [dist_eq_norm, dist_eq_norm, ← toContinuousLinearMap_sub, norm_toContinuousLinearMap]

theorem le_opNorm (T : AdjointableMap A E F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ := by
  rw [← norm_toContinuousLinearMap]
  exact T.toContinuousLinearMap.le_opNorm x

theorem opNorm_le_bound (T : AdjointableMap A E F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖T x‖ ≤ M * ‖x‖) : ‖T‖ ≤ M := by
  rw [← norm_toContinuousLinearMap]
  exact T.toContinuousLinearMap.opNorm_le_bound hMp hM

theorem opNorm_comp_le (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := by
  simpa only [← norm_toContinuousLinearMap, toContinuousLinearMap_comp] using
    S.toContinuousLinearMap.opNorm_comp_le T.toContinuousLinearMap

noncomputable instance instNormedRing : NormedRing (AdjointableMap A E E) where
  dist_eq := NormedAddCommGroup.dist_eq
  norm_mul_le := opNorm_comp_le

instance applyIsBoundedSMul : IsBoundedSMul (AdjointableMap A E E) E :=
  IsBoundedSMul.of_norm_smul_le fun T x => by rw [AdjointableMap.smul_def]; exact T.le_opNorm x

/-- The pair embedding `(T, T*)` into `(E →L[ℂ] F) × (F →L[ℂ] E)`. -/
private def toProdContinuousLinearMap (T : AdjointableMap A E F) : (E →L[ℂ] F) × (F →L[ℂ] E) :=
  (T.toContinuousLinearMap, T.adjointContinuousLinearMap)

private theorem range_toProdContinuousLinearMap :
    Set.range (toProdContinuousLinearMap : AdjointableMap A E F → (E →L[ℂ] F) × (F →L[ℂ] E)) =
      { p | ∀ x y, inner A (p.1 x) y = inner A x (p.2 y) } := by
  ext p
  exact ⟨by rintro ⟨T, rfl⟩; exact T.inner_map_eq', fun hp => ⟨⟨p.1, p.2, hp⟩, rfl⟩⟩

end NormInduced

section NormedSpace

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

noncomputable instance instNormedSpaceComplex : NormedSpace ℂ (AdjointableMap A E F) where
  norm_smul_le c T := by
    simpa only [← norm_toContinuousLinearMap, toContinuousLinearMap_smul] using
      norm_smul_le c T.toContinuousLinearMap

/-- The forgetful linear isometry `AdjointableMap A E F →ₗᵢ[ℂ] (E →L[ℂ] F)`. -/
noncomputable def toContinuousLinearMapₗᵢ : AdjointableMap A E F →ₗᵢ[ℂ] (E →L[ℂ] F) where
  toLinearMap := toContinuousLinearMapLinearMap
  norm_map' T := by rw [toContinuousLinearMapLinearMap_apply, norm_toContinuousLinearMap]

@[simp]
theorem toContinuousLinearMapₗᵢ_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapₗᵢ T = T.toContinuousLinearMap :=
  toContinuousLinearMapLinearMap_apply T

/-- Composition of adjointable operators as a bounded bilinear map. -/
noncomputable def compL :
    AdjointableMap A F G →L[ℂ] AdjointableMap A E F →L[ℂ] AdjointableMap A E G :=
  LinearMap.mkContinuous₂
    { toFun S :=
        { toFun := S.comp
          map_add' := S.comp_add
          map_smul' := S.comp_smul }
      map_add' := fun S₁ S₂ => LinearMap.ext (add_comp S₁ S₂)
      map_smul' := fun c S => LinearMap.ext (smul_comp c S) }
    1 fun S T => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using opNorm_comp_le S T

@[simp]
theorem compL_apply (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    compL S T = S.comp T := (rfl)

noncomputable instance instNormedAlgebraComplex : NormedAlgebra ℂ (AdjointableMap A E E) where
  norm_smul_le c T := by
    simpa only [← norm_toContinuousLinearMap, toContinuousLinearMap_smul] using
      norm_smul_le c T.toContinuousLinearMap

end NormedSpace

section CStarNorm

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable operator and its adjoint have equal operator norms: `‖T*‖ = ‖T‖`. -/
@[simp]
theorem norm_adjoint (T : AdjointableMap A E F) : ‖T.adjoint‖ = ‖T‖ := by
  simpa only [norm_toContinuousLinearMap] using
    T.isAdjointPair_toContinuousLinearMap.norm_eq_cstarModule

@[simp]
theorem nnNorm_adjoint (T : AdjointableMap A E F) : ‖T.adjoint‖₊ = ‖T‖₊ :=
  Subtype.ext (norm_adjoint T)

/-- Taking the adjoint is a conjugate-linear isometric equivalence
`AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E`. -/
noncomputable def adjointₗᵢ : AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E :=
  { adjointLinearEquiv with
    norm_map' := fun T => by simpa only [adjointLinearEquiv_apply] using norm_adjoint T }

@[simp]
theorem adjointₗᵢ_apply (T : AdjointableMap A E F) : adjointₗᵢ T = T.adjoint :=
  adjointLinearEquiv_apply T

@[simp]
theorem adjointₗᵢ_symm_apply (S : AdjointableMap A F E) :
    adjointₗᵢ.symm S = S.adjoint :=
  adjointLinearEquiv_symm_apply S

/-- The C⋆-identity for rectangular adjointable operators: `‖T* ∘ T‖ = ‖T‖ ^ 2`. -/
@[simp]
theorem norm_adjoint_comp_self (T : AdjointableMap A E F) :
    ‖T.adjoint.comp T‖ = ‖T‖ ^ 2 := by
  simpa only [← norm_toContinuousLinearMap, toContinuousLinearMap_comp] using
    T.isAdjointPair_toContinuousLinearMap.norm_adjoint_comp_self_cstarModule

/-- The dual C⋆-identity for rectangular adjointable operators: `‖T ∘ T*‖ = ‖T‖ ^ 2`. -/
@[simp]
theorem norm_self_comp_adjoint (T : AdjointableMap A E F) :
    ‖T.comp T.adjoint‖ = ‖T‖ ^ 2 := by
  simpa only [adjoint_adjoint, norm_adjoint] using norm_adjoint_comp_self T.adjoint

private theorem isometry_toProdContinuousLinearMap :
    Isometry (toProdContinuousLinearMap : AdjointableMap A E F → (E →L[ℂ] F) × (F →L[ℂ] E)) := by
  refine Isometry.of_dist_eq fun T S => ?_
  rw [dist_eq_norm, dist_eq_norm, Prod.norm_def]
  simp only [toProdContinuousLinearMap, Prod.fst_sub, Prod.snd_sub,
    adjointContinuousLinearMap_eq_toContinuousLinearMap_adjoint, ← toContinuousLinearMap_sub,
    ← adjoint_sub, norm_toContinuousLinearMap, norm_adjoint, max_self]

instance instCompleteSpace [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (AdjointableMap A E F) := by
  rw [completeSpace_iff_isComplete_range
    isometry_toProdContinuousLinearMap.isUniformInducing]
  apply IsClosed.isComplete
  rw [range_toProdContinuousLinearMap]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ ?_
  · exact CStarModule.continuous_inner.comp
      (((ContinuousLinearMap.apply ℂ F x).continuous.comp continuous_fst).prodMk continuous_const)
  · exact CStarModule.continuous_inner.comp
      (continuous_const.prodMk ((ContinuousLinearMap.apply ℂ E y).continuous.comp continuous_snd))

/-- Construct an adjointable operator from a pair of plain functions `T : E → F` and `S : F → E`
between complete Hilbert C⋆-modules satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A`. Neither linearity nor
continuity is assumed of `T` or `S`. -/
noncomputable def ofAdjointPair [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    AdjointableMap A E F where
  toContinuousLinearMap :=
    (CStarModule.isAdjointPair_inner_iff.mpr h).toContinuousLinearMapCStarModule
  adjointContinuousLinearMap :=
    (CStarModule.isAdjointPair_inner_iff.mpr h).symm_cstarModule.toContinuousLinearMapCStarModule
  inner_map_eq' x y := by simp [h x y]

@[simp]
theorem ofAdjointPair_apply [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    ofAdjointPair T S h x = T x :=
  (CStarModule.isAdjointPair_inner_iff.mpr h).toContinuousLinearMapCStarModule_apply x

theorem adjoint_ofAdjointPair_apply [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) (y : F) :
    (ofAdjointPair T S h).adjoint y = S y := by
  rw [← adjointContinuousLinearMap_apply]
  have hS := (CStarModule.isAdjointPair_inner_iff.mpr h).symm_cstarModule
  exact hS.toContinuousLinearMapCStarModule_apply y

@[simp]
theorem adjoint_ofAdjointPair [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    (ofAdjointPair T S h).adjoint =
      ofAdjointPair S T (fun y x => by
        rw [← CStarModule.star_inner, ← h x y, CStarModule.star_inner]) :=
  ext fun y => (adjoint_ofAdjointPair_apply T S h y).trans (ofAdjointPair_apply S T _ y).symm

/-- Construct an adjointable operator from a witness of `CStarModule.IsAdjointable` between
complete Hilbert C⋆-modules. -/
noncomputable def ofIsAdjointable [CompleteSpace E] [CompleteSpace F]
    {T : E → F} (h : CStarModule.IsAdjointable A T) : AdjointableMap A E F :=
  ofAdjointPair T (CStarModule.isAdjointable_def.mp h).choose
    (CStarModule.isAdjointable_def.mp h).choose_spec

@[simp]
theorem ofIsAdjointable_apply [CompleteSpace E] [CompleteSpace F]
    {T : E → F} (h : CStarModule.IsAdjointable A T) (x : E) :
    ofIsAdjointable h x = T x :=
  ofAdjointPair_apply T _ _ x

@[simp]
theorem coe_ofIsAdjointable [CompleteSpace E] [CompleteSpace F]
    {T : E → F} (h : CStarModule.IsAdjointable A T) :
    ⇑(ofIsAdjointable h) = T :=
  funext (ofIsAdjointable_apply h)

/-- Between complete Hilbert C⋆-modules, a function (in particular, a bounded module map) comes
from an element of `AdjointableMap A E F` if and only if it admits a plain adjoint function. -/
theorem exists_coe_eq_iff [CompleteSpace E] [CompleteSpace F] {T : E → F} :
    (∃ T' : AdjointableMap A E F, ⇑T' = T) ↔ CStarModule.IsAdjointable A T :=
  ⟨by rintro ⟨T', rfl⟩; exact T'.isAdjointable, fun h => ⟨ofIsAdjointable h, coe_ofIsAdjointable h⟩⟩

end CStarNorm

/-! ### The unital C⋆-algebra `L_A(E)`, positivity, and modulus -/

section CStarAlgebra

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

instance instCStarRing : CStarRing (AdjointableMap A E E) where
  norm_mul_self_le T := by rw [star_def, mul_def, norm_adjoint_comp_self, sq]

/-- For a complete Hilbert C⋆-module `E`, `AdjointableMap A E E` is a unital C⋆-algebra (with the
zero algebra when `E` is the zero module). -/
noncomputable instance instCStarAlgebra [CompleteSpace E] :
    CStarAlgebra (AdjointableMap A E E) where

noncomputable instance instPartialOrder [CompleteSpace E] :
    PartialOrder (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrder _

instance instStarOrderedRing [CompleteSpace E] :
    StarOrderedRing (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrderedRing _

/-- Positivity in the C⋆-algebra `AdjointableMap A E E` is characterized by positivity of the
module inner products `⟪x, T x⟫_A` in `A` (Lance, Lemma 4.1; Raeburn–Williams, Proposition 2.21).
Self-adjointness is not assumed on the right-hand side: over `ℂ` it follows automatically from
`0 ≤ ⟪x, T x⟫_A`. The proof adapts `CStarMatrix.nonneg_iff_forall_sum_nonneg` from
`TauCeti.Analysis.CStarAlgebra.CStarMatrix`. -/
theorem nonneg_iff [CompleteSpace E] {T : AdjointableMap A E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ inner A x (T x) := by
  refine ⟨fun hT x => ?_, fun h => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
    rw [mul_apply, star_apply, ← R.inner_map_left]
    exact CStarModule.inner_self_nonneg
  · have hsa : IsSelfAdjoint T :=
      (isSelfAdjoint_iff T).mpr fun x => IsSelfAdjoint.of_nonneg (h x)
    refine CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero.mpr ⟨hsa, ?_⟩
    set N := T⁻
    have hN : 0 ≤ N := CFC.negPart_nonneg T
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN
    have hTN : T * N = -(star R * R * N) := by
      conv_lhs => rw [← CFC.posPart_sub_negPart T hsa]
      rw [sub_mul, CFC.posPart_mul_negPart, zero_sub, ← hR]
    have hRN : R * N = 0 := by
      ext x
      have hx := h (N x)
      rw [← mul_apply, hTN] at hx
      have hx : inner A (R (N x)) (R (N x)) ≤ 0 := by
        simpa [← R.inner_map_left] using hx
      rw [mul_apply, zero_apply]
      exact (CStarModule.inner_self (A := A)).mp (le_antisymm hx CStarModule.inner_self_nonneg)
    rw [← star_mul_self_eq_zero, hN.isSelfAdjoint.star_eq]
    calc N * N = star R * (R * N) := by rw [← mul_assoc, ← hR]
      _ = 0 := by rw [hRN, mul_zero]

/-- For a complete Hilbert C⋆-module `E` and any `S : AdjointableMap A E F`, `S* ∘ S` is positive
in `AdjointableMap A E E`, even when `F` is not assumed complete. -/
@[simp]
theorem adjoint_comp_self_nonneg [CompleteSpace E] (S : AdjointableMap A E F) :
    0 ≤ S.adjoint.comp S :=
  nonneg_iff.mpr fun x => by
    rw [comp_apply, ← S.inner_map_left]
    exact CStarModule.inner_self_nonneg

/-- For a complete Hilbert C⋆-module `F` and any `S : AdjointableMap A E F`, `S ∘ S*` is positive
in `AdjointableMap A F F`. -/
@[simp]
theorem self_comp_adjoint_nonneg [CompleteSpace F] (S : AdjointableMap A E F) :
    0 ≤ S.comp S.adjoint := by
  simpa only [adjoint_adjoint] using adjoint_comp_self_nonneg S.adjoint

/-- Rectangular congruence preserves positivity: if `0 ≤ T` in `AdjointableMap A F F` and
`S : AdjointableMap A E F`, then `0 ≤ S* ∘ T ∘ S` in `AdjointableMap A E E`. -/
theorem adjoint_comp_comp_nonneg [CompleteSpace E] [CompleteSpace F]
    {T : AdjointableMap A F F} (hT : 0 ≤ T) (S : AdjointableMap A E F) :
    0 ≤ (S.adjoint.comp T).comp S :=
  nonneg_iff.mpr fun x => by
    rw [comp_apply, comp_apply, ← S.inner_map_left]
    exact nonneg_iff.mp hT (S x)

/-- For a self-adjoint adjointable operator `T`, `⟪x, T x⟫_A ≤ ‖T‖ • ⟪x, x⟫_A`. -/
theorem inner_map_self_le_norm [CompleteSpace E] {T : AdjointableMap A E E}
    (hT : IsSelfAdjoint T) (x : E) :
    inner A x (T x) ≤ ‖T‖ • inner A x x := by
  have hsub : 0 ≤ inner A x ((algebraMap ℝ (AdjointableMap A E E) ‖T‖ - T) x) :=
    nonneg_iff.mp (sub_nonneg.mpr hT.le_algebraMap_norm_self) x
  have halg : algebraMap ℝ (AdjointableMap A E E) ‖T‖ x = (‖T‖ : ℂ) • x := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, smul_apply, one_apply]
  rwa [sub_apply, halg, CStarModule.inner_sub_right, CStarModule.inner_smul_right_complex,
    Complex.coe_smul, sub_nonneg] at hsub

/-- The positive modulus `|T| = √(T* ∘ T) ∈ AdjointableMap A E E` of a rectangular adjointable
operator `T : AdjointableMap A E F` on a complete Hilbert C⋆-module `E`. -/
noncomputable def abs [CompleteSpace E] (T : AdjointableMap A E F) : AdjointableMap A E E :=
  CFC.sqrt (T.adjoint.comp T)

theorem abs_def [CompleteSpace E] (T : AdjointableMap A E F) :
    T.abs = CFC.sqrt (T.adjoint.comp T) := (rfl)

@[simp]
theorem abs_nonneg [CompleteSpace E] (T : AdjointableMap A E F) : 0 ≤ T.abs :=
  CFC.sqrt_nonneg (T.adjoint.comp T)

@[simp]
theorem isSelfAdjoint_abs [CompleteSpace E] (T : AdjointableMap A E F) : IsSelfAdjoint T.abs :=
  T.abs_nonneg.isSelfAdjoint

@[simp]
theorem abs_mul_abs [CompleteSpace E] (T : AdjointableMap A E F) :
    T.abs * T.abs = T.adjoint.comp T :=
  CFC.sqrt_mul_sqrt_self _ (adjoint_comp_self_nonneg T)

/-- The modulus induces the same module inner products as `T`: `⟪|T| x, |T| y⟫_A = ⟪T x, T y⟫_A`.
-/
@[simp]
theorem inner_abs_abs [CompleteSpace E] (T : AdjointableMap A E F) (x y : E) :
    inner A (T.abs x) (T.abs y) = inner A (T x) (T y) := by
  rw [T.abs.inner_map_left, ← star_def, T.isSelfAdjoint_abs.star_eq, ← mul_apply, abs_mul_abs,
    comp_apply, ← T.inner_map_left]

@[simp]
theorem norm_abs_apply [CompleteSpace E] (T : AdjointableMap A E F) (x : E) :
    ‖T.abs x‖ = ‖T x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (T.abs x),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (T x), inner_abs_abs]

@[simp]
theorem norm_abs [CompleteSpace E] (T : AdjointableMap A E F) : ‖T.abs‖ = ‖T‖ := by
  rw [abs_def, CFC.norm_sqrt _ (adjoint_comp_self_nonneg T), norm_adjoint_comp_self,
    Real.sqrt_sq (norm_nonneg T)]

end CStarAlgebra

section RightPositivity

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Right-module form of `AdjointableMap.nonneg_iff`: `0 ≤ T` in `L_B(E)` iff `0 ≤ ⟨x, T x⟩_B` for
all `x : E`. -/
theorem nonneg_iff_unop {T : AdjointableMap Bᵐᵒᵖ E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ unop (inner Bᵐᵒᵖ x (T x)) := by
  simp_rw [nonneg_iff, MulOpposite.unop_nonneg]

end RightPositivity

/-! ### Orthogonal projections and adjointable isometries -/

section Projections

variable {A E : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- An adjointable endomorphism `P` is an orthogonal projection (`IsStarProjection P`, i.e.
`P * P = P` and `P* = P`) if and only if `⟪P x, y⟫_A = ⟪P x, P y⟫_A` for all `x, y : E`. -/
theorem isStarProjection_iff_forall_inner {P : AdjointableMap A E E} :
    IsStarProjection P ↔ ∀ x y : E, inner A (P x) y = inner A (P x) (P y) := by
  refine ⟨fun hP x y => ?_, fun h => ?_⟩
  · calc inner A (P x) y = inner A ((P * P) x) y := by rw [hP.isIdempotentElem.eq]
      _ = inner A (P x) (P.adjoint y) := by rw [mul_apply, P.inner_map_left]
      _ = inner A (P x) (P y) := by rw [← star_def, hP.isSelfAdjoint.star_eq]
  · have hsa : IsSelfAdjoint P := by
      rw [IsSelfAdjoint, star_def]
      exact ext_inner_left fun x y => by
        rw [← P.inner_map_left, h x y, ← CStarModule.star_inner, ← h y x, CStarModule.star_inner]
    refine ⟨?_, hsa⟩
    rw [IsIdempotentElem]
    exact ext_inner_right fun x y => by
      rw [mul_apply, P.inner_map_left, ← star_def, hsa.star_eq, ← h x y]

theorem inner_map_map_eq_inner_map_right_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x y : E) :
    inner A (P x) (P y) = inner A x (P y) := by
  rw [P.inner_map_left, ← star_def, hP.isSelfAdjoint.star_eq, ← mul_apply, hP.isIdempotentElem.eq]

theorem inner_map_one_sub_eq_zero_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x y : E) :
    inner A (P x) ((1 - P) y) = 0 := by
  calc inner A (P x) ((1 - P) y)
      = inner A x ((P.adjoint * (1 - P)) y) := by rw [P.inner_map_left, mul_apply]
    _ = inner A x ((P * (1 - P)) y) := by rw [← star_def, hP.isSelfAdjoint.star_eq]
    _ = inner A x ((0 : AdjointableMap A E E) y) := by rw [hP.mul_one_sub_self]
    _ = 0 := by rw [zero_apply, CStarModule.inner_zero_right']

/-- Orthogonal decomposition of the module inner product under an adjointable projection `P`:
`⟪P x, P y⟫_A + ⟪(1 - P) x, (1 - P) y⟫_A = ⟪x, y⟫_A`. -/
theorem inner_map_add_inner_one_sub_eq_inner_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x y : E) :
    inner A (P x) (P y) + inner A ((1 - P) x) ((1 - P) y) = inner A x y := by
  rw [inner_map_map_eq_inner_map_right_of_isStarProjection hP x y,
    inner_map_map_eq_inner_map_right_of_isStarProjection hP.one_sub x y,
    ← CStarModule.inner_add_right, ← add_apply, add_sub_cancel, one_apply]

theorem comp_eq_right_iff_range_subset_of_isIdempotentElem
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    {P : AdjointableMap A F E} {Q : AdjointableMap A E E} (hQ : IsIdempotentElem Q) :
    Q.comp P = P ↔ Set.range P ⊆ Set.range Q := by
  refine ⟨fun h => ?_, fun h => ext fun x => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨P x, by rw [← comp_apply, h]⟩
  · obtain ⟨z, hz⟩ := h ⟨x, rfl⟩
    rw [comp_apply, ← hz, ← mul_apply, hQ.eq]

theorem mul_eq_right_iff_range_subset_of_isIdempotentElem {P Q : AdjointableMap A E E}
    (hQ : IsIdempotentElem Q) :
    Q * P = P ↔ Set.range P ⊆ Set.range Q := by
  rw [mul_def]
  exact comp_eq_right_iff_range_subset_of_isIdempotentElem hQ

/-- Two adjointable orthogonal projections with the same range are equal. -/
theorem eq_of_isStarProjection_of_range_eq {P Q : AdjointableMap A E E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : Set.range P = Set.range Q) :
    P = Q := by
  have hQP : Q * P = P :=
    (mul_eq_right_iff_range_subset_of_isIdempotentElem hQ.isIdempotentElem).mpr h.le
  have hPQ : P * Q = Q :=
    (mul_eq_right_iff_range_subset_of_isIdempotentElem hP.isIdempotentElem).mpr h.ge
  calc P = star P := hP.isSelfAdjoint.star_eq.symm
    _ = star (Q * P) := by rw [hQP]
    _ = star P * star Q := star_mul Q P
    _ = P * Q := by rw [hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
    _ = Q := hPQ

theorem eq_iff_range_eq_of_isStarProjection {P Q : AdjointableMap A E E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    P = Q ↔ Set.range P = Set.range Q :=
  ⟨fun h => h ▸ rfl, eq_of_isStarProjection_of_range_eq hP hQ⟩

end Projections

section ProjectionOrder

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]

/-- On a complete Hilbert C⋆-module, the spectral order on adjointable orthogonal projections agrees
with range inclusion. -/
theorem le_iff_range_subset_of_isStarProjection {P Q : AdjointableMap A E E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    P ≤ Q ↔ Set.range P ⊆ Set.range Q :=
  (hP.le_iff_mul_eq_right hQ).trans
    (mul_eq_right_iff_range_subset_of_isIdempotentElem hQ.isIdempotentElem)

end ProjectionOrder

section Isometries

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable operator `T` satisfies `T* ∘ T = id` if and only if it preserves the module inner
product: `⟪T x, T y⟫_A = ⟪x, y⟫_A` for all `x, y : E`. -/
theorem adjoint_comp_self_eq_id_iff {T : AdjointableMap A E F} :
    T.adjoint.comp T = .id ↔ ∀ x y : E, inner A (T x) (T y) = inner A x y := by
  refine ⟨fun h x y => ?_, fun h => ext_inner_left fun x y => ?_⟩
  · rw [T.inner_map_left, ← comp_apply, h, id_apply]
  · rw [comp_apply, ← T.inner_map_left, h, id_apply]

theorem norm_map_of_adjoint_comp_self_eq_id {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) (x : E) : ‖T x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (T x),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x,
    adjoint_comp_self_eq_id_iff.mp hT x x]

/-- Convert an adjointable isometry `T` (`T* ∘ T = id`) to a `ℂ`-linear isometry `E →ₗᵢ[ℂ] F`. -/
def toLinearIsometryOfAdjointCompSelfEqId {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) : E →ₗᵢ[ℂ] F where
  toLinearMap := T.toContinuousLinearMap.toLinearMap
  norm_map' := norm_map_of_adjoint_comp_self_eq_id hT

@[simp]
theorem toLinearIsometryOfAdjointCompSelfEqId_apply {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) (x : E) :
    toLinearIsometryOfAdjointCompSelfEqId hT x = T x := (rfl)

theorem isometry_of_adjoint_comp_self_eq_id {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) : Isometry T :=
  (toLinearIsometryOfAdjointCompSelfEqId hT).isometry

/-- For an adjointable isometry `T` (`T* ∘ T = id`), the range projection `T ∘ T*` is an orthogonal
projection in `AdjointableMap A F F`. -/
theorem isStarProjection_self_comp_adjoint_of_adjoint_comp_self_eq_id {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) : IsStarProjection (T.comp T.adjoint) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, mul_def, comp_assoc, ← comp_assoc T.adjoint T T.adjoint, hT, id_comp]
  · rw [IsSelfAdjoint, star_def, adjoint_comp, adjoint_adjoint]

end Isometries

section IsometriesPolarization

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Over `ℂ`, an adjointable operator `T` satisfies `T* ∘ T = id` if and only if it preserves
diagonal module inner products `⟪T x, T x⟫_A = ⟪x, x⟫_A` for all `x : E`. -/
theorem adjoint_comp_self_eq_id_iff_forall_inner_self {T : AdjointableMap A E F} :
    T.adjoint.comp T = .id ↔ ∀ x : E, inner A (T x) (T x) = inner A x x := by
  rw [eq_iff_forall_inner_self]
  exact forall_congr' fun x => by rw [comp_apply, ← T.inner_map_left, id_apply]

end IsometriesPolarization

end AdjointableMap

end TauCeti
