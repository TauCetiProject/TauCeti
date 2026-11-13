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

Let `α` be a point-norm continuous action of a locally compact group `G : Type u` on a possibly
nonunital C⋆-algebra `A : Type v` with left Haar measure `μ`. The canonical maps
`FullCrossedProduct.coefficientMultiplier` and `FullCrossedProduct.groupMultiplier` form a covariant
multiplier homomorphism `FullCrossedProduct.covariantMultiplierHom α μ`.

* **Strict Bochner multiplier-integral identification**
  (`FullCrossedProduct.integratedMultiplier_covariantMultiplierHom`,
  `FullCrossedProduct.integral_coefficientMultiplier_mul_groupMultiplier_snd`): the strict Bochner
  integrated form of `(i_A, i_G)` on `C_c(G, A)` is the canonical inclusion into
  `A ⋊_α G ⊆ 𝓜(ℂ, A ⋊_α G)`, and right multiplication by `of α μ f` agrees with the strict
  Bochner integral `∫ s, (i_A(f(s)) i_G(s)).snd y ∂μ`.
* **Multiplier-algebra universal property and disintegration**
  (`CovariantMultiplierHom.integratedFull`, `NonUnitalStarAlgHom.toCovariantMultiplierHom`,
  `NonUnitalStarAlgHom.integratedFull_toCovariantMultiplierHom`,
  `CovariantMultiplierHom.toCovariantMultiplierHom_integratedFull`,
  `CovariantMultiplierHom.eq_integratedFull_iff`,
  `CovariantMultiplierHom.existsUnique_isMultiplierNondegenerate_extendToMultiplier_eq`, and
  `NonUnitalStarAlgHom.IsMultiplierNondegenerate.existsUnique_covariantMultiplierHom_integratedFull`
  ): every covariant multiplier homomorphism into `𝓜(ℂ, B)` (`B : Type w` in any universe)
  integrates to `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`, giving a bijection between nondegenerate homomorphisms
  `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` and nondegenerate covariant multiplier homomorphisms of `(A, G, α)`
  into `𝓜(ℂ, B)`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 2.39 and Theorem 2.61.
* Iain Raeburn, *On crossed products and Takai duality*, Proc. Edinburgh Math. Soc. 31 (1988),
  321–330.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped CompactlySupported MultiplierAlgebra CStarAlgebra

namespace TauCeti.CStarAction

universe u v w

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

namespace FullCrossedProduct

variable (α μ) in
/-- The canonical maps `i_A` and `i_G` into `𝓜(ℂ, A ⋊_α G)` bundled as a covariant multiplier
homomorphism. -/
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

/-- Composing `(i_A, i_G)` with `L.multiplierExtension hL` yields the disintegrated covariant
representation `L.toCovariantRepresentation hL`. -/
@[simp]
theorem toCovariantRepresentation_covariantMultiplierHom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hL : L.IsNondegenerate) :
    (covariantMultiplierHom α μ).toCovariantRepresentation hL =
      L.toCovariantRepresentation hL :=
  CovariantRepresentation.ext (by ext; simp) (DFunLike.ext _ _ fun _ => by simp)

/-- The strict Bochner integrated form of the canonical covariant multiplier homomorphism on
`C_c(G, A)` is the canonical inclusion into `A ⋊_α G ⊆ 𝓜(ℂ, A ⋊_α G)`. -/
@[simp]
theorem integratedMultiplier_covariantMultiplierHom (f : C_c(G, A)) :
    (covariantMultiplierHom α μ).integratedMultiplier μ f =
      (of α μ (ConvolutionAlgebra.toConv f) : 𝓜(ℂ, FullCrossedProduct α μ)) :=
  DoubleCentralizer.ext_fst fun x => by
    simpa using integral_coefficientMultiplier_mul_groupMultiplier_fst
      (ConvolutionAlgebra.toConv f) x

/-- The integrated ⋆-homomorphism of `(i_A, i_G)` on the twisted convolution algebra is `of α μ`
followed by the canonical inclusion into `𝓜(ℂ, A ⋊_α G)`. -/
theorem integratedStarAlgHom_covariantMultiplierHom (f : ConvolutionAlgebra α μ) :
    (covariantMultiplierHom α μ).integratedStarAlgHom μ f =
      (of α μ f : 𝓜(ℂ, FullCrossedProduct α μ)) := by simp

/-- Right multiplication by `of α μ f` in the full crossed product is given in the strict topology
by the Bochner integral `∫ s, (i_A(f(s)) i_G(s)).snd y ∂μ = y * of α μ f`. -/
theorem integral_coefficientMultiplier_mul_groupMultiplier_snd (f : ConvolutionAlgebra α μ)
    (y : FullCrossedProduct α μ) :
    ∫ s, (coefficientMultiplier α μ (f.ofConv s) *
      (groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ))).snd y ∂μ = y * of α μ f := by
  have hsnd : y * of α μ f = (of α μ f : 𝓜(ℂ, FullCrossedProduct α μ)).snd y := by simp
  rw [hsnd, ← integratedStarAlgHom_covariantMultiplierHom]
  simp only [CovariantMultiplierHom.integratedStarAlgHom_apply,
    CovariantMultiplierHom.integratedMultiplier_snd_apply, covariantMultiplierHom_coefficient,
    covariantMultiplierHom_group]

/-- The left centralizers of the integrated canonical multipliers on `C_c(G, A)` have dense linear
span in `FullCrossedProduct α μ`. -/
theorem dense_span_integratedMultiplier_covariantMultiplierHom :
    Dense (Submodule.span ℂ
      (⋃ f : C_c(G, A),
        Set.range ((covariantMultiplierHom α μ).integratedMultiplier μ f).fst) :
      Set (FullCrossedProduct α μ)) :=
  ((covariantMultiplierHom α μ).dense_span_integratedMultiplier_iff μ).2
    isMultiplierNondegenerate_coefficientMultiplier

end FullCrossedProduct

/-! ### Extended integrated form on the full crossed product -/

namespace CovariantMultiplierHom

open FullCrossedProduct

variable {B : Type w} [NonUnitalCStarAlgebra B] (M : CovariantMultiplierHom α B)

/-- The integrated ⋆-homomorphism of any covariant multiplier homomorphism into `𝓜(ℂ, B)` is
bounded by the full C⋆-seminorm. -/
theorem norm_integratedStarAlgHom_le_fullSeminorm (f : ConvolutionAlgebra α μ) :
    ‖M.integratedStarAlgHom μ f‖ ≤ ConvolutionAlgebra.fullSeminorm α μ f :=
  DoubleCentralizer.norm_le_iff_forall_isNondegenerate.2 fun _ _ _ _ _ hρ =>
    (congrArg norm (M.multiplierExtension_integratedStarAlgHom μ hρ f)).trans_le <|
      ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm
        (M.toCovariantRepresentation hρ) f

variable (μ) in
/-- The integrated form of a covariant multiplier homomorphism into `𝓜(ℂ, B)`, extended by
continuity to a ⋆-homomorphism `FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`. -/
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
/-- Composing `M.integratedFull μ` with the multiplier extension of a nondegenerate Hilbert-space
representation `ρ` of `B` yields the extended integrated form of
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
/-- Composing `M.integratedFull μ` with the multiplier extension of a nondegenerate
`ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)` yields the extended integrated form of `M.map hψ`. -/
@[simp]
theorem extendToMultiplier_comp_integratedFull {C : Type*} [NonUnitalCStarAlgebra C]
    {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate) :
    (ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp (M.integratedFull μ) =
      (M.map hψ).integratedFull μ :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp

/-- Applying `ψ.extendToMultiplier hψ` to `M.integratedFull μ x` yields
`(M.map hψ).integratedFull μ x`. -/
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

/-- The extended integrated form of a covariant multiplier homomorphism vanishes if and only if its
coefficient map is zero. -/
@[simp]
theorem integratedFull_eq_zero_iff : M.integratedFull μ = 0 ↔ M.coefficient = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine NonUnitalStarAlgHom.ext fun a =>
      DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ ρ hρ => ?_
    have hP : (M.toCovariantRepresentation hρ).integratedFull μ = 0 := by
      rw [← M.multiplierExtension_comp_integratedFull μ hρ, h]
      ext
      simp
    simpa using DFunLike.congr_fun
      (((M.toCovariantRepresentation hρ).integratedFull_eq_zero_iff).1 hP) a
  · refine FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun f =>
      DoubleCentralizer.ext_fst fun b => by simp [h]

/-- `M.integratedFull μ` turns the left action of `i_A(a)` into left multiplication by
`M.coefficient a`. -/
@[simp]
theorem integratedFull_coefficientMultiplier_fst (a : A) (x : FullCrossedProduct α μ) :
    M.integratedFull μ ((coefficientMultiplier α μ a).fst x) =
      M.coefficient a * M.integratedFull μ x := by
  induction x using FullCrossedProduct.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

/-- `M.integratedFull μ` turns the left action of `i_G(r)` into left multiplication by
`M.group r`. -/
@[simp]
theorem integratedFull_groupMultiplier_fst (r : G) (x : FullCrossedProduct α μ) :
    M.integratedFull μ ((groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).fst x) =
      M.group r * M.integratedFull μ x := by
  induction x using FullCrossedProduct.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp

/-- `M.integratedFull μ` turns the right action of `i_A(a)` into right multiplication by
`M.coefficient a`. -/
@[simp]
theorem integratedFull_coefficientMultiplier_snd (a : A) (x : FullCrossedProduct α μ) :
    M.integratedFull μ ((coefficientMultiplier α μ a).snd x) =
      M.integratedFull μ x * M.coefficient a := by
  induction x using FullCrossedProduct.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp [map_star, star_mul]

/-- `M.integratedFull μ` turns the right action of `i_G(r)` into right multiplication by
`M.group r`. -/
@[simp]
theorem integratedFull_groupMultiplier_snd (r : G) (x : FullCrossedProduct α μ) :
    M.integratedFull μ ((groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).snd x) =
      M.integratedFull μ x * M.group r := by
  induction x using FullCrossedProduct.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp [map_star, star_mul, ← Unitary.star_eq_inv]

variable (μ) in
/-- `M.integratedFull μ` generates the exact same closed essential subspace of `B` as
`M.coefficient`. -/
theorem topologicalClosure_span_integratedFull :
    (Submodule.span ℂ (⋃ x, Set.range (M.integratedFull μ x).fst)).topologicalClosure =
      (Submodule.span ℂ (⋃ a, Set.range (M.coefficient a).fst)).topologicalClosure := by
  rw [← NonUnitalStarAlgHom.topologicalClosure_span_fst_comp_eq denseRange_of_comp_toConv
    (M.integratedFull μ)]
  simpa only [Function.comp_apply, M.integratedFull_of, integratedStarAlgHom_apply,
    ConvolutionAlgebra.ofConv_toConv] using M.topologicalClosure_span_integratedMultiplier μ

variable (μ) in
/-- The extended integrated homomorphism `M.integratedFull μ` is multiplier-nondegenerate if and
only if `M.coefficient` is multiplier-nondegenerate. -/
@[simp]
theorem isMultiplierNondegenerate_integratedFull_iff :
    (M.integratedFull μ).IsMultiplierNondegenerate ↔ M.coefficient.IsMultiplierNondegenerate := by
  rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense,
    NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense,
    Submodule.dense_iff_topologicalClosure_eq_top, Submodule.dense_iff_topologicalClosure_eq_top,
    M.topologicalClosure_span_integratedFull μ]

end CovariantMultiplierHom

namespace FullCrossedProduct

/-- Integrating the canonical covariant multiplier homomorphism `(i_A, i_G)` of `A ⋊_α G` yields
the canonical embedding `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)`. -/
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

universe u v w

variable {G : Type u} {A : Type v} {B : Type w} [Group G] [TopologicalSpace G]
  [MeasurableSpace G] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

/-- Disintegrate a nondegenerate multiplier homomorphism `Φ : A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` into a
covariant multiplier homomorphism of `(A, G, α)` into `𝓜(ℂ, B)`. -/
def toCovariantMultiplierHom (Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B))
    (hΦ : Φ.IsMultiplierNondegenerate) : CovariantMultiplierHom α B :=
  (covariantMultiplierHom α μ).map hΦ

@[simp]
theorem toCovariantMultiplierHom_coefficient {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) :
    (Φ.toCovariantMultiplierHom hΦ).coefficient =
      (Φ.extendToMultiplier hΦ).toNonUnitalStarAlgHom.comp (coefficientMultiplier α μ) := by
  simp [toCovariantMultiplierHom]

@[simp]
theorem coe_toCovariantMultiplierHom_group {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) (r : G) :
    ((Φ.toCovariantMultiplierHom hΦ).group r : 𝓜(ℂ, B)) =
      Φ.extendToMultiplier hΦ (groupMultiplier α μ r) := by
  simp [toCovariantMultiplierHom]

/-- The disintegrated covariant multiplier homomorphism has a multiplier-nondegenerate coefficient
map. -/
theorem isMultiplierNondegenerate_toCovariantMultiplierHom_coefficient
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate) :
    (Φ.toCovariantMultiplierHom hΦ).coefficient.IsMultiplierNondegenerate :=
  toCovariantMultiplierHom_coefficient hΦ ▸
    hΦ.extendToMultiplier_comp isMultiplierNondegenerate_coefficientMultiplier

/-- Disintegrating the canonical inclusion `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)` recovers `(i_A, i_G)`. -/
@[simp]
theorem toCovariantMultiplierHom_coeHom
    (h : (DoubleCentralizer.coeHom (𝕜 := ℂ) :
      FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, FullCrossedProduct α μ)).IsMultiplierNondegenerate) :
    (DoubleCentralizer.coeHom (𝕜 := ℂ)).toCovariantMultiplierHom h =
      covariantMultiplierHom α μ := by
  simp [toCovariantMultiplierHom]

/-- Disintegrating `(ψ.extendToMultiplier hψ) ∘ Φ` pushes `Φ.toCovariantMultiplierHom hΦ` forward
along `ψ`. -/
@[simp]
theorem toCovariantMultiplierHom_extendToMultiplier_comp {C : Type*} [NonUnitalCStarAlgebra C]
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate)
    {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate)
    (h : ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp Φ).IsMultiplierNondegenerate) :
    ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp Φ).toCovariantMultiplierHom h =
      (Φ.toCovariantMultiplierHom hΦ).map hψ := by
  simp [toCovariantMultiplierHom]

/-- Composing `Φ.toCovariantMultiplierHom hΦ` with a nondegenerate Hilbert-space representation `ρ`
of `B` agrees with disintegrating the composite representation `(ρ.multiplierExtension hρ) ∘ Φ`. -/
@[simp]
theorem toCovariantRepresentation_toCovariantMultiplierHom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate)
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) :
    (Φ.toCovariantMultiplierHom hΦ).toCovariantRepresentation hρ =
      ((ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp Φ).toCovariantRepresentation
        (hρ.multiplierExtension_comp hΦ) := by
  rw [toCovariantMultiplierHom, CovariantMultiplierHom.toCovariantRepresentation_map,
    toCovariantRepresentation_covariantMultiplierHom]

@[simp]
theorem integratedMultiplier_toCovariantMultiplierHom
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate)
    (f : C_c(G, A)) :
    (Φ.toCovariantMultiplierHom hΦ).integratedMultiplier μ f =
      Φ (of α μ (ConvolutionAlgebra.toConv f)) := by
  rw [toCovariantMultiplierHom,
    ← (covariantMultiplierHom α μ).extendToMultiplier_integratedMultiplier μ hΦ,
    integratedMultiplier_covariantMultiplierHom, Φ.extendToMultiplier_coe hΦ]

@[simp]
theorem integratedStarAlgHom_toCovariantMultiplierHom
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate) :
    (Φ.toCovariantMultiplierHom hΦ).integratedStarAlgHom μ = Φ.comp (of α μ) :=
  NonUnitalStarAlgHom.ext fun _ => by simp [CovariantMultiplierHom.integratedStarAlgHom_apply]

/-- Uniqueness of multiplier disintegration on the twisted convolution algebra: any covariant
multiplier homomorphism `M` into `𝓜(ℂ, B)` whose integrated ⋆-homomorphism agrees with
`Φ ∘ of α μ` automatically has multiplier-nondegenerate `M.coefficient` and equals
`Φ.toCovariantMultiplierHom hΦ`. -/
theorem eq_toCovariantMultiplierHom_of_integratedStarAlgHom_eq
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate)
    {M : CovariantMultiplierHom α B} (hM : M.integratedStarAlgHom μ = Φ.comp (of α μ)) :
    M = Φ.toCovariantMultiplierHom hΦ := by
  have hint (f : C_c(G, A)) :
      M.integratedMultiplier μ f = Φ (of α μ (ConvolutionAlgebra.toConv f)) := by
    simpa [CovariantMultiplierHom.integratedStarAlgHom_apply] using
      congr($hM (ConvolutionAlgebra.toConv f))
  have hMnd : M.coefficient.IsMultiplierNondegenerate :=
    (M.dense_span_integratedMultiplier_iff μ).1 <| by
      simpa only [Function.comp_apply, hint] using
        (NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense_span_comp
          denseRange_of_comp_toConv).1 hΦ
  exact M.eq_of_integratedStarAlgHom_eq μ hMnd
    (hM.trans (integratedStarAlgHom_toCovariantMultiplierHom hΦ).symm)

/-- Integrating the disintegrated covariant multiplier homomorphism of a nondegenerate
`Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` recovers `Φ`. -/
@[simp]
theorem integratedFull_toCovariantMultiplierHom {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) :
    (Φ.toCovariantMultiplierHom hΦ).integratedFull μ = Φ :=
  FullCrossedProduct.starAlgHom_ext <|
    (Φ.toCovariantMultiplierHom hΦ).integratedFull_comp_of.trans
      (integratedStarAlgHom_toCovariantMultiplierHom hΦ)

/-- For a multiplier-nondegenerate `Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`, a covariant
multiplier homomorphism `M` equals `Φ.toCovariantMultiplierHom hΦ` if and only if
`M.integratedFull μ = Φ`. -/
theorem eq_toCovariantMultiplierHom_iff {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) {M : CovariantMultiplierHom α B} :
    M = Φ.toCovariantMultiplierHom hΦ ↔ M.integratedFull μ = Φ :=
  ⟨fun h => h ▸ integratedFull_toCovariantMultiplierHom hΦ, fun h =>
    eq_toCovariantMultiplierHom_of_integratedStarAlgHom_eq hΦ
      (M.integratedFull_comp_of.symm.trans (congrArg (·.comp (of α μ)) h))⟩

/-- Every nondegenerate multiplier homomorphism `Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is
the extended integrated form of a unique covariant multiplier homomorphism `M`, whose coefficient
map is automatically nondegenerate
(`isMultiplierNondegenerate_toCovariantMultiplierHom_coefficient`). -/
theorem IsMultiplierNondegenerate.existsUnique_covariantMultiplierHom_integratedFull
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate) :
    ∃! M : CovariantMultiplierHom α B, M.integratedFull μ = Φ :=
  ⟨Φ.toCovariantMultiplierHom hΦ, integratedFull_toCovariantMultiplierHom hΦ,
    fun _ => (eq_toCovariantMultiplierHom_iff hΦ).2⟩

end NonUnitalStarAlgHom

/-! ### Universal property and round-trip identities for multiplier algebras -/

namespace TauCeti.CStarAction.CovariantMultiplierHom

open FullCrossedProduct

universe u v w

variable {G : Type u} {A : Type v} {B : Type w} [Group G] [TopologicalSpace G]
  [MeasurableSpace G] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

/-- Disintegrating `M.integratedFull μ` recovers `M`. -/
@[simp]
theorem toCovariantMultiplierHom_integratedFull (M : CovariantMultiplierHom α B)
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) :
    (M.integratedFull μ).toCovariantMultiplierHom h = M :=
  (NonUnitalStarAlgHom.eq_toCovariantMultiplierHom_of_integratedStarAlgHom_eq h
    M.integratedFull_comp_of.symm).symm

/-- Applying the multiplier extension of `M.integratedFull μ` to `i_A(a)` recovers
`M.coefficient a`. -/
@[simp]
theorem extendToMultiplier_integratedFull_coefficientMultiplier (M : CovariantMultiplierHom α B)
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) (a : A) :
    (M.integratedFull μ).extendToMultiplier h (coefficientMultiplier α μ a) = M.coefficient a := by
  simpa only [NonUnitalStarAlgHom.toCovariantMultiplierHom_coefficient,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom] using
    congrArg (fun N => N.coefficient a) (M.toCovariantMultiplierHom_integratedFull h)

/-- Applying the multiplier extension of `M.integratedFull μ` to `i_G(r)` recovers `M.group r`. -/
@[simp]
theorem extendToMultiplier_integratedFull_groupMultiplier (M : CovariantMultiplierHom α B)
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) (r : G) :
    (M.integratedFull μ).extendToMultiplier h (groupMultiplier α μ r) = M.group r := by
  simpa only [NonUnitalStarAlgHom.coe_toCovariantMultiplierHom_group] using
    congrArg (fun N => (N.group r : 𝓜(ℂ, B))) (M.toCovariantMultiplierHom_integratedFull h)

/-- Universal property of `(A ⋊_α G, i_A, i_G)` for nondegenerate multiplier homomorphisms:
a multiplier-nondegenerate ⋆-homomorphism `Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` equals
`M.integratedFull μ` if and only if its multiplier extension sends `i_A` to `M.coefficient` and
`i_G` to `M.group`. When `M.coefficient` is multiplier-nondegenerate, `M.integratedFull μ` is
therefore the unique multiplier-nondegenerate ⋆-homomorphism with this property. -/
theorem eq_integratedFull_iff {M : CovariantMultiplierHom α B}
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate) :
    Φ = M.integratedFull μ ↔
      (∀ a, Φ.extendToMultiplier hΦ (coefficientMultiplier α μ a) = M.coefficient a) ∧
        ∀ r, Φ.extendToMultiplier hΦ (groupMultiplier α μ r) = M.group r := by
  refine ⟨?_, fun ⟨hA, hG⟩ => ?_⟩
  · rintro rfl
    exact ⟨M.extendToMultiplier_integratedFull_coefficientMultiplier hΦ,
      M.extendToMultiplier_integratedFull_groupMultiplier hΦ⟩
  · have hdis : Φ.toCovariantMultiplierHom hΦ = M :=
      CovariantMultiplierHom.ext (NonUnitalStarAlgHom.ext fun a => by simp [hA])
        (MonoidHom.ext fun r => Subtype.ext <| by simp [hG])
    rw [← Φ.integratedFull_toCovariantMultiplierHom hΦ, hdis]

variable (μ) in
/-- Universal property of `(A ⋊_α G, i_A, i_G)` (Williams, Theorem 2.61): for every covariant
multiplier homomorphism `M` with multiplier-nondegenerate coefficient map, `M.integratedFull μ` is
the unique multiplier-nondegenerate ⋆-homomorphism `Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`
whose multiplier extension sends `i_A` to `M.coefficient` and `i_G` to `M.group`. -/
theorem existsUnique_isMultiplierNondegenerate_extendToMultiplier_eq
    (M : CovariantMultiplierHom α B) (hM : M.coefficient.IsMultiplierNondegenerate) :
    ∃! Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B),
      ∃ hΦ : Φ.IsMultiplierNondegenerate,
        (∀ a, Φ.extendToMultiplier hΦ (coefficientMultiplier α μ a) = M.coefficient a) ∧
          ∀ r, Φ.extendToMultiplier hΦ (groupMultiplier α μ r) = M.group r := by
  have hnd : (M.integratedFull μ).IsMultiplierNondegenerate :=
    (M.isMultiplierNondegenerate_integratedFull_iff μ).2 hM
  exact ⟨M.integratedFull μ, ⟨hnd, (eq_integratedFull_iff hnd).1 rfl⟩,
    fun _ ⟨hΦ, h⟩ => (eq_integratedFull_iff hΦ).2 h⟩

end TauCeti.CStarAction.CovariantMultiplierHom
