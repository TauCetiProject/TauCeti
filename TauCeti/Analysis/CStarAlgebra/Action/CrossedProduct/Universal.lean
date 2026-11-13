/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Disintegration
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Functoriality
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Nondegenerate

/-!
# The multiplier universal property of full crossed products

For an action `α` of a locally compact group `G : Type u` on a C⋆-algebra `A : Type v` with left
Haar measure `μ`, `coefficientMultiplier` and `groupMultiplier` form
`FullCrossedProduct.covariantMultiplierHom α μ`, whose strict Bochner integrated form on `C_c(G, A)`
is the inclusion into `A ⋊_α G ⊆ 𝓜(ℂ, A ⋊_α G)`
(`FullCrossedProduct.integratedMultiplier_covariantMultiplierHom`,
`FullCrossedProduct.integral_coefficientMultiplier_mul_groupMultiplier_snd`). Every
`CovariantMultiplierHom` into `𝓜(ℂ, B)` (`B : Type w` in any universe) integrates to
`CovariantMultiplierHom.integratedFull : A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`, inverse to
`NonUnitalStarAlgHom.toCovariantMultiplierHom` on nondegenerate homomorphisms
(`NonUnitalStarAlgHom.integratedFull_toCovariantMultiplierHom`,
`CovariantMultiplierHom.toCovariantMultiplierHom_integratedFull`,
`CovariantMultiplierHom.eq_integratedFull_iff`,
`CovariantMultiplierHom.existsUnique_isMultiplierNondegenerate_extendToMultiplier_eq`,
`NonUnitalStarAlgHom.IsMultiplierNondegenerate.existsUnique_covariantMultiplierHom_integratedFull`).

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 2.39 and Theorem 2.61.
* Iain Raeburn, *On crossed products and Takai duality*, Proc. Edinburgh Math. Soc. 31 (1988),
  321–330.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped CompactlySupported MultiplierAlgebra CStarAlgebra

universe u v w

variable {G : Type u} {A : Type v} {B : Type w} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] {α : TauCeti.CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

namespace TauCeti.CStarAction

namespace FullCrossedProduct

variable (α μ) in
/-- The canonical maps `i_A` and `i_G` into `𝓜(ℂ, A ⋊_α G)` as a `CovariantMultiplierHom`. -/
def covariantMultiplierHom : CovariantMultiplierHom α (FullCrossedProduct α μ) where
  coefficient := coefficientMultiplier α μ
  group := groupMultiplier α μ
  continuous_group_fst := continuous_groupMultiplier_fst_apply
  covariance := groupMultiplier_mul_coefficientMultiplier

@[simp]
theorem covariantMultiplierHom_coefficient :
    (covariantMultiplierHom α μ).coefficient = coefficientMultiplier α μ := (rfl)

@[simp]
theorem covariantMultiplierHom_group :
    (covariantMultiplierHom α μ).group = groupMultiplier α μ := (rfl)

/-- Composing `(i_A, i_G)` with `L.multiplierExtension hL` yields `L.toCovariantRepresentation`. -/
@[simp]
theorem toCovariantRepresentation_covariantMultiplierHom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hL : L.IsNondegenerate) :
    (covariantMultiplierHom α μ).toCovariantRepresentation hL = L.toCovariantRepresentation hL :=
  CovariantRepresentation.ext (by ext; simp) (DFunLike.ext _ _ fun _ => by simp)

/-- The strict integrated form of `(i_A, i_G)` on `C_c(G, A)` is the inclusion into `𝓜(ℂ, A ⋊_α G)`.
-/
@[simp]
theorem integratedMultiplier_covariantMultiplierHom (f : C_c(G, A)) :
    (covariantMultiplierHom α μ).integratedMultiplier μ f =
      (of α μ (ConvolutionAlgebra.toConv f) : 𝓜(ℂ, FullCrossedProduct α μ)) :=
  DoubleCentralizer.ext_fst fun x => by
    simpa using integral_coefficientMultiplier_mul_groupMultiplier_fst
      (ConvolutionAlgebra.toConv f) x

/-- The integrated ⋆-homomorphism of `(i_A, i_G)` is `of α μ` into `𝓜(ℂ, A ⋊_α G)`. -/
theorem integratedStarAlgHom_covariantMultiplierHom (f : ConvolutionAlgebra α μ) :
    (covariantMultiplierHom α μ).integratedStarAlgHom μ f =
      (of α μ f : 𝓜(ℂ, FullCrossedProduct α μ)) := by simp

/-- Right multiplication by `of α μ f` equals `∫ s, (i_A(f s) i_G(s)).snd y ∂μ`. -/
theorem integral_coefficientMultiplier_mul_groupMultiplier_snd (f : ConvolutionAlgebra α μ)
    (y : FullCrossedProduct α μ) :
    ∫ s, (coefficientMultiplier α μ (f.ofConv s) *
      (groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ))).snd y ∂μ = y * of α μ f := by
  have hsnd : y * of α μ f = (of α μ f : 𝓜(ℂ, FullCrossedProduct α μ)).snd y := by simp
  rw [hsnd, ← integratedStarAlgHom_covariantMultiplierHom]
  simp only [CovariantMultiplierHom.integratedStarAlgHom_apply,
    CovariantMultiplierHom.integratedMultiplier_snd_apply, covariantMultiplierHom_coefficient,
    covariantMultiplierHom_group]

/-- Left centralizers of integrated canonical multipliers have dense span in `A ⋊_α G`. -/
theorem dense_span_integratedMultiplier_covariantMultiplierHom :
    Dense (Submodule.span ℂ
      (⋃ f : C_c(G, A), Set.range ((covariantMultiplierHom α μ).integratedMultiplier μ f).fst) :
      Set (FullCrossedProduct α μ)) :=
  ((covariantMultiplierHom α μ).dense_span_integratedMultiplier_iff μ).2
    isMultiplierNondegenerate_coefficientMultiplier

end FullCrossedProduct

/-! ### Extended integrated form on the full crossed product -/

namespace CovariantMultiplierHom

open FullCrossedProduct

variable (M : CovariantMultiplierHom α B)

/-- `M.integratedStarAlgHom μ` is bounded by `ConvolutionAlgebra.fullSeminorm`. -/
theorem norm_integratedStarAlgHom_le_fullSeminorm (f : ConvolutionAlgebra α μ) :
    ‖M.integratedStarAlgHom μ f‖ ≤ ConvolutionAlgebra.fullSeminorm α μ f :=
  DoubleCentralizer.norm_le_iff_forall_isNondegenerate.2 fun _ _ _ _ _ hρ =>
    (congrArg norm (M.multiplierExtension_integratedStarAlgHom μ hρ f)).trans_le <|
      ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm
        (M.toCovariantRepresentation hρ) f

variable (μ) in
/-- Continuous extension of `M.integratedStarAlgHom μ` to `FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`.
-/
def integratedFull : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B) :=
  FullCrossedProduct.lift (M.integratedStarAlgHom μ) M.norm_integratedStarAlgHom_le_fullSeminorm

@[simp]
theorem integratedFull_of (f : ConvolutionAlgebra α μ) :
    M.integratedFull μ (of α μ f) = M.integratedStarAlgHom μ f :=
  FullCrossedProduct.lift_of _ _ f

@[simp]
theorem integratedFull_comp_of :
    (M.integratedFull μ).comp (of α μ) = M.integratedStarAlgHom μ :=
  NonUnitalStarAlgHom.ext M.integratedFull_of

variable (μ) in
/-- Composing `M.integratedFull μ` with `ρ.multiplierExtension hρ` gives `integratedFull` of
`M.toCovariantRepresentation hρ`. -/
@[simp]
theorem multiplierExtension_comp_integratedFull {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) :
    (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp (M.integratedFull μ) =
      (M.toCovariantRepresentation hρ).integratedFull μ :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp

@[simp]
theorem multiplierExtension_integratedFull_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (x : FullCrossedProduct α μ) :
    ρ.multiplierExtension hρ (M.integratedFull μ x) =
      (M.toCovariantRepresentation hρ).integratedFull μ x :=
  DFunLike.congr_fun (M.multiplierExtension_comp_integratedFull μ hρ) x

variable (μ) in
/-- `ψ.extendToMultiplier hψ ∘ M.integratedFull μ` equals `(M.map hψ).integratedFull μ`. -/
@[simp]
theorem extendToMultiplier_comp_integratedFull {C : Type*} [NonUnitalCStarAlgebra C]
    {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate) :
    (ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp (M.integratedFull μ) =
      (M.map hψ).integratedFull μ :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp

/-- Pointwise form of `extendToMultiplier_comp_integratedFull`. -/
@[simp]
theorem extendToMultiplier_integratedFull_apply {C : Type*} [NonUnitalCStarAlgebra C]
    {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate) (x : FullCrossedProduct α μ) :
    ψ.extendToMultiplier hψ (M.integratedFull μ x) = (M.map hψ).integratedFull μ x :=
  DFunLike.congr_fun (M.extendToMultiplier_comp_integratedFull μ hψ) x

variable (μ) in
/-- Naturality of `CovariantMultiplierHom.integratedFull` under equivariant coefficient maps. -/
@[simp]
theorem integratedFull_comp_fullCrossedProductMap {A' : Type v} [NonUnitalCStarAlgebra A']
    {α' : CStarAction G A'} (φ : Hom α' α) :
    (M.integratedFull μ).comp (φ.fullCrossedProductMap μ) = (M.comap φ).integratedFull μ :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp

@[simp]
theorem integratedFull_fullCrossedProductMap_apply {A' : Type v} [NonUnitalCStarAlgebra A']
    {α' : CStarAction G A'} (φ : Hom α' α) (x : FullCrossedProduct α' μ) :
    M.integratedFull μ (φ.fullCrossedProductMap μ x) = (M.comap φ).integratedFull μ x :=
  DFunLike.congr_fun (M.integratedFull_comp_fullCrossedProductMap μ φ) x

/-- `M.integratedFull μ` vanishes if and only if `M.coefficient = 0`. -/
@[simp]
theorem integratedFull_eq_zero_iff : M.integratedFull μ = 0 ↔ M.coefficient = 0 :=
  ⟨fun h => NonUnitalStarAlgHom.ext fun a =>
    DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun _ _ _ _ ρ hρ => by
      have hP : (M.toCovariantRepresentation hρ).integratedFull μ = 0 :=
        (M.multiplierExtension_comp_integratedFull μ hρ).symm.trans <|
          h ▸ NonUnitalStarAlgHom.ext fun _ => by simp
      simpa using DFunLike.congr_fun
        ((M.toCovariantRepresentation hρ).integratedFull_eq_zero_iff.1 hP) a,
    fun h => FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ =>
      DoubleCentralizer.ext_fst fun _ => by simp [h]⟩

/-- `M.integratedFull μ` sends `(i_A(a)).fst x` to `M.coefficient a * M.integratedFull μ x`. -/
@[simp]
theorem integratedFull_coefficientMultiplier_fst (a : A) (x : FullCrossedProduct α μ) :
    M.integratedFull μ ((coefficientMultiplier α μ a).fst x) =
      M.coefficient a * M.integratedFull μ x :=
  FullCrossedProduct.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun _ => by simp

/-- `M.integratedFull μ` sends `(i_G(r)).fst x` to `M.group r * M.integratedFull μ x`. -/
@[simp]
theorem integratedFull_groupMultiplier_fst (r : G) (x : FullCrossedProduct α μ) :
    M.integratedFull μ ((groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).fst x) =
      M.group r * M.integratedFull μ x :=
  FullCrossedProduct.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun _ => by simp

/-- `M.integratedFull μ` sends `(i_A(a)).snd x` to `M.integratedFull μ x * M.coefficient a`. -/
@[simp]
theorem integratedFull_coefficientMultiplier_snd (a : A) (x : FullCrossedProduct α μ) :
    M.integratedFull μ ((coefficientMultiplier α μ a).snd x) =
      M.integratedFull μ x * M.coefficient a :=
  FullCrossedProduct.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun _ => by
    simp [map_star, star_mul]

/-- `M.integratedFull μ` sends `(i_G(r)).snd x` to `M.integratedFull μ x * M.group r`. -/
@[simp]
theorem integratedFull_groupMultiplier_snd (r : G) (x : FullCrossedProduct α μ) :
    M.integratedFull μ ((groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).snd x) =
      M.integratedFull μ x * M.group r :=
  FullCrossedProduct.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun _ => by
    simp [map_star, star_mul, ← Unitary.star_eq_inv]

variable (μ) in
/-- `M.integratedFull μ` spans the same closed essential subspace of `B` as `M.coefficient`. -/
theorem topologicalClosure_span_integratedFull :
    (Submodule.span ℂ (⋃ x, Set.range (M.integratedFull μ x).fst)).topologicalClosure =
      (Submodule.span ℂ (⋃ a, Set.range (M.coefficient a).fst)).topologicalClosure := by
  rw [← NonUnitalStarAlgHom.topologicalClosure_span_fst_comp_eq denseRange_of_comp_toConv
    (M.integratedFull μ)]
  simpa only [Function.comp_apply, M.integratedFull_of, integratedStarAlgHom_apply,
    ConvolutionAlgebra.ofConv_toConv] using M.topologicalClosure_span_integratedMultiplier μ

variable (μ) in
/-- `M.integratedFull μ` is multiplier-nondegenerate if and only if `M.coefficient` is. -/
@[simp]
theorem isMultiplierNondegenerate_integratedFull_iff :
    (M.integratedFull μ).IsMultiplierNondegenerate ↔ M.coefficient.IsMultiplierNondegenerate := by
  simp_rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense,
    Submodule.dense_iff_topologicalClosure_eq_top, M.topologicalClosure_span_integratedFull μ]

end CovariantMultiplierHom

namespace FullCrossedProduct

/-- Integrating `(i_A, i_G)` yields the canonical embedding `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)`. -/
@[simp]
theorem integratedFull_covariantMultiplierHom :
    (covariantMultiplierHom α μ).integratedFull μ =
      DoubleCentralizer.coeHom (𝕜 := ℂ) (A := FullCrossedProduct α μ) :=
  starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp

end FullCrossedProduct

end TauCeti.CStarAction

/-! ### Disintegration of nondegenerate multiplier homomorphisms -/

namespace NonUnitalStarAlgHom

open TauCeti TauCeti.CStarAction TauCeti.CStarAction.FullCrossedProduct

/-- Disintegrate a nondegenerate `Φ : A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` into a `CovariantMultiplierHom`. -/
def toCovariantMultiplierHom (Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B))
    (hΦ : Φ.IsMultiplierNondegenerate) : CovariantMultiplierHom α B :=
  (covariantMultiplierHom α μ).map hΦ

/-- Disintegrating the canonical inclusion `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)` recovers `(i_A, i_G)`. -/
@[simp]
theorem toCovariantMultiplierHom_coeHom
    (h : (DoubleCentralizer.coeHom (𝕜 := ℂ) :
      FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, FullCrossedProduct α μ)).IsMultiplierNondegenerate) :
    (DoubleCentralizer.coeHom (𝕜 := ℂ)).toCovariantMultiplierHom h =
      covariantMultiplierHom α μ := by simp [toCovariantMultiplierHom]

variable {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate)

@[simp]
theorem toCovariantMultiplierHom_coefficient :
    (Φ.toCovariantMultiplierHom hΦ).coefficient =
      (Φ.extendToMultiplier hΦ).toNonUnitalStarAlgHom.comp (coefficientMultiplier α μ) := by
  simp [toCovariantMultiplierHom]

@[simp]
theorem coe_toCovariantMultiplierHom_group (r : G) :
    ((Φ.toCovariantMultiplierHom hΦ).group r : 𝓜(ℂ, B)) =
      Φ.extendToMultiplier hΦ (groupMultiplier α μ r) := by simp [toCovariantMultiplierHom]

/-- `Φ.toCovariantMultiplierHom hΦ` has a multiplier-nondegenerate coefficient map. -/
theorem isMultiplierNondegenerate_toCovariantMultiplierHom_coefficient :
    (Φ.toCovariantMultiplierHom hΦ).coefficient.IsMultiplierNondegenerate :=
  toCovariantMultiplierHom_coefficient hΦ ▸
    hΦ.extendToMultiplier_comp isMultiplierNondegenerate_coefficientMultiplier

/-- Disintegrating `(ψ.extendToMultiplier hψ) ∘ Φ` equals `(Φ.toCovariantMultiplierHom hΦ).map hψ`.
-/
@[simp]
theorem toCovariantMultiplierHom_extendToMultiplier_comp {C : Type*} [NonUnitalCStarAlgebra C]
    {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate)
    (h : ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp Φ).IsMultiplierNondegenerate) :
    ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp Φ).toCovariantMultiplierHom h =
      (Φ.toCovariantMultiplierHom hΦ).map hψ := by simp [toCovariantMultiplierHom]

/-- `(Φ.toCovariantMultiplierHom hΦ).toCovariantRepresentation hρ` disintegrates `ρ' ∘ Φ`. -/
@[simp]
theorem toCovariantRepresentation_toCovariantMultiplierHom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) :
    (Φ.toCovariantMultiplierHom hΦ).toCovariantRepresentation hρ =
      ((ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp Φ).toCovariantRepresentation
        (hρ.multiplierExtension_comp hΦ) := by
  rw [toCovariantMultiplierHom, CovariantMultiplierHom.toCovariantRepresentation_map,
    toCovariantRepresentation_covariantMultiplierHom]

@[simp]
theorem integratedMultiplier_toCovariantMultiplierHom (f : C_c(G, A)) :
    (Φ.toCovariantMultiplierHom hΦ).integratedMultiplier μ f =
      Φ (of α μ (ConvolutionAlgebra.toConv f)) := by
  rw [toCovariantMultiplierHom,
    ← (covariantMultiplierHom α μ).extendToMultiplier_integratedMultiplier μ hΦ,
    integratedMultiplier_covariantMultiplierHom, Φ.extendToMultiplier_coe hΦ]

@[simp]
theorem integratedStarAlgHom_toCovariantMultiplierHom :
    (Φ.toCovariantMultiplierHom hΦ).integratedStarAlgHom μ = Φ.comp (of α μ) :=
  NonUnitalStarAlgHom.ext fun _ => by simp [CovariantMultiplierHom.integratedStarAlgHom_apply]

/-- Uniqueness of multiplier disintegration: any `M` with `M.integratedStarAlgHom μ = Φ ∘ of α μ`
has nondegenerate `M.coefficient` and equals `Φ.toCovariantMultiplierHom hΦ`. -/
theorem eq_toCovariantMultiplierHom_of_integratedStarAlgHom_eq {M : CovariantMultiplierHom α B}
    (hM : M.integratedStarAlgHom μ = Φ.comp (of α μ)) : M = Φ.toCovariantMultiplierHom hΦ := by
  have hint (f : C_c(G, A)) :
      M.integratedMultiplier μ f = Φ (of α μ (ConvolutionAlgebra.toConv f)) := by
    simpa [CovariantMultiplierHom.integratedStarAlgHom_apply] using
      congr($hM (ConvolutionAlgebra.toConv f))
  have hMnd : M.coefficient.IsMultiplierNondegenerate :=
    (M.dense_span_integratedMultiplier_iff μ).1 <| by
      simpa only [Function.comp_apply, hint] using
        (isMultiplierNondegenerate_iff_dense_span_comp denseRange_of_comp_toConv).1 hΦ
  exact M.eq_of_integratedStarAlgHom_eq μ hMnd
    (hM.trans (integratedStarAlgHom_toCovariantMultiplierHom hΦ).symm)

/-- Integrating `Φ.toCovariantMultiplierHom hΦ` recovers `Φ`. -/
@[simp]
theorem integratedFull_toCovariantMultiplierHom :
    (Φ.toCovariantMultiplierHom hΦ).integratedFull μ = Φ :=
  FullCrossedProduct.starAlgHom_ext <|
    (Φ.toCovariantMultiplierHom hΦ).integratedFull_comp_of.trans
      (integratedStarAlgHom_toCovariantMultiplierHom hΦ)

/-- For nondegenerate `Φ`, `M = Φ.toCovariantMultiplierHom hΦ` iff `M.integratedFull μ = Φ`. -/
theorem eq_toCovariantMultiplierHom_iff {M : CovariantMultiplierHom α B} :
    M = Φ.toCovariantMultiplierHom hΦ ↔ M.integratedFull μ = Φ :=
  ⟨fun h => h ▸ integratedFull_toCovariantMultiplierHom hΦ, fun h =>
    eq_toCovariantMultiplierHom_of_integratedStarAlgHom_eq hΦ
      (M.integratedFull_comp_of.symm.trans (congrArg (·.comp (of α μ)) h))⟩

include hΦ in
/-- Every nondegenerate `Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is `M.integratedFull μ` for a
unique `M : CovariantMultiplierHom α B`, which has nondegenerate `M.coefficient`. -/
theorem IsMultiplierNondegenerate.existsUnique_covariantMultiplierHom_integratedFull :
    ∃! M : CovariantMultiplierHom α B, M.integratedFull μ = Φ :=
  ⟨Φ.toCovariantMultiplierHom hΦ, integratedFull_toCovariantMultiplierHom hΦ,
    fun _ => (eq_toCovariantMultiplierHom_iff hΦ).2⟩

end NonUnitalStarAlgHom

/-! ### Universal property and round-trip identities for multiplier algebras -/

namespace TauCeti.CStarAction.CovariantMultiplierHom

open FullCrossedProduct

/-- Disintegrating `M.integratedFull μ` recovers `M`. -/
@[simp]
theorem toCovariantMultiplierHom_integratedFull (M : CovariantMultiplierHom α B)
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) :
    (M.integratedFull μ).toCovariantMultiplierHom h = M :=
  (NonUnitalStarAlgHom.eq_toCovariantMultiplierHom_of_integratedStarAlgHom_eq h
    M.integratedFull_comp_of.symm).symm

/-- Applying the extension of `M.integratedFull μ` to `i_A(a)` recovers `M.coefficient a`. -/
@[simp]
theorem extendToMultiplier_integratedFull_coefficientMultiplier (M : CovariantMultiplierHom α B)
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) (a : A) :
    (M.integratedFull μ).extendToMultiplier h (coefficientMultiplier α μ a) = M.coefficient a := by
  simpa only [NonUnitalStarAlgHom.toCovariantMultiplierHom_coefficient,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom] using
      DFunLike.congr_fun (congrArg (·.coefficient) (M.toCovariantMultiplierHom_integratedFull h)) a

/-- Applying the extension of `M.integratedFull μ` to `i_G(r)` recovers `M.group r`. -/
@[simp]
theorem extendToMultiplier_integratedFull_groupMultiplier (M : CovariantMultiplierHom α B)
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) (r : G) :
    (M.integratedFull μ).extendToMultiplier h (groupMultiplier α μ r) = M.group r := by
  simpa only [NonUnitalStarAlgHom.coe_toCovariantMultiplierHom_group] using
    congrArg (fun N => (N.group r : 𝓜(ℂ, B))) (M.toCovariantMultiplierHom_integratedFull h)

/-- Universal property of `(A ⋊_α G, i_A, i_G)`: a nondegenerate
`Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` equals `M.integratedFull μ` iff `Φ.extendToMultiplier`
sends `i_A` to `M.coefficient` and `i_G` to `M.group`. -/
theorem eq_integratedFull_iff {M : CovariantMultiplierHom α B}
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate) :
    Φ = M.integratedFull μ ↔
      (∀ a, Φ.extendToMultiplier hΦ (coefficientMultiplier α μ a) = M.coefficient a) ∧
        ∀ r, Φ.extendToMultiplier hΦ (groupMultiplier α μ r) = M.group r :=
  ⟨fun h => by
      subst h
      exact ⟨M.extendToMultiplier_integratedFull_coefficientMultiplier hΦ,
        M.extendToMultiplier_integratedFull_groupMultiplier hΦ⟩,
    fun ⟨hA, hG⟩ => (Φ.integratedFull_toCovariantMultiplierHom hΦ).symm.trans <|
      congrArg (CovariantMultiplierHom.integratedFull μ) <| CovariantMultiplierHom.ext
        (NonUnitalStarAlgHom.ext fun a => by
          simp [NonUnitalStarAlgHom.toCovariantMultiplierHom_coefficient, hA])
        (MonoidHom.ext fun r => Subtype.ext <| by
          rw [NonUnitalStarAlgHom.coe_toCovariantMultiplierHom_group, hG])⟩

variable (μ) in
/-- Universal property of `(A ⋊_α G, i_A, i_G)` (Williams, Theorem 2.61): for `M` with
nondegenerate `M.coefficient`, `M.integratedFull μ` is the unique nondegenerate `Φ` whose extension
sends `i_A` to `M.coefficient` and `i_G` to `M.group`. -/
theorem existsUnique_isMultiplierNondegenerate_extendToMultiplier_eq
    (M : CovariantMultiplierHom α B) (hM : M.coefficient.IsMultiplierNondegenerate) :
    ∃! Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B), ∃ hΦ : Φ.IsMultiplierNondegenerate,
      (∀ a, Φ.extendToMultiplier hΦ (coefficientMultiplier α μ a) = M.coefficient a) ∧
        ∀ r, Φ.extendToMultiplier hΦ (groupMultiplier α μ r) = M.group r := by
  have hnd := (M.isMultiplierNondegenerate_integratedFull_iff μ).2 hM
  exact ⟨M.integratedFull μ, ⟨hnd, (eq_integratedFull_iff hnd).1 rfl⟩,
    fun _ ⟨hΦ, h⟩ => (eq_integratedFull_iff hΦ).2 h⟩

end TauCeti.CStarAction.CovariantMultiplierHom
