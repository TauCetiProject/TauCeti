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
  (`FullCrossedProduct.covariantMultiplierHom_integratedMultiplier`,
  `FullCrossedProduct.integral_coefficientMultiplier_mul_groupMultiplier_snd`): the strict Bochner
  integrated form of `(i_A, i_G)` on `C_c(G, A)` is the canonical inclusion into
  `A ⋊_α G ⊆ 𝓜(ℂ, A ⋊_α G)`, and right multiplication by `of α μ f` agrees with the strict
  Bochner integral `∫ s, (i_A(f(s)) i_G(s)).snd y ∂μ`.
* **Multiplier-algebra universal property and disintegration**
  (`CovariantMultiplierHom.integratedFull`, `FullCrossedProduct.disintegrateMultiplier`,
  `CovariantMultiplierHom.integratedFull_disintegrateMultiplier`,
  `FullCrossedProduct.disintegrateMultiplier_integratedFull`,
  `CovariantMultiplierHom.eq_integratedFull_iff`): every covariant multiplier homomorphism into
  `𝓜(ℂ, B)` (`B : Type w` in any universe) integrates to `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`, giving a
  bijection between nondegenerate homomorphisms `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` and nondegenerate
  covariant multiplier homomorphisms of `(A, G, α)` into `𝓜(ℂ, B)`.

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

/-- Compactly supported continuous functions `C_c(G, A)` map densely into
`FullCrossedProduct α μ`. -/
theorem denseRange_of_toConv :
    DenseRange ((of α μ) ∘ ConvolutionAlgebra.toConv) := by
  rw [DenseRange, (Function.RightInverse.surjective ConvolutionAlgebra.toConv_ofConv).range_comp]
  exact denseRange_of

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
theorem covariantMultiplierHom_toCovariantRepresentation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hL : L.IsNondegenerate) :
    (covariantMultiplierHom α μ).toCovariantRepresentation hL =
      L.toCovariantRepresentation hL :=
  CovariantRepresentation.ext (by ext; simp) (DFunLike.ext _ _ fun _ => by simp)

/-- The strict Bochner integrated form of the canonical covariant multiplier homomorphism on
`C_c(G, A)` is the canonical inclusion into `A ⋊_α G ⊆ 𝓜(ℂ, A ⋊_α G)`. -/
@[simp]
theorem covariantMultiplierHom_integratedMultiplier (f : C_c(G, A)) :
    (covariantMultiplierHom α μ).integratedMultiplier μ f =
      (of α μ (ConvolutionAlgebra.toConv f) : 𝓜(ℂ, FullCrossedProduct α μ)) :=
  DoubleCentralizer.ext_fst fun x => by
    simpa using integral_coefficientMultiplier_mul_groupMultiplier_fst
      (ConvolutionAlgebra.toConv f) x

/-- The integrated ⋆-homomorphism of `(i_A, i_G)` on the twisted convolution algebra is `of α μ`
followed by the canonical inclusion into `𝓜(ℂ, A ⋊_α G)`. -/
theorem covariantMultiplierHom_integratedStarAlgHom (f : ConvolutionAlgebra α μ) :
    (covariantMultiplierHom α μ).integratedStarAlgHom μ f =
      (of α μ f : 𝓜(ℂ, FullCrossedProduct α μ)) := by simp

/-- Right multiplication by `of α μ f` in the full crossed product is given in the strict topology
by the Bochner integral `∫ s, (i_A(f(s)) i_G(s)).snd y ∂μ = y * of α μ f`. -/
theorem integral_coefficientMultiplier_mul_groupMultiplier_snd (f : ConvolutionAlgebra α μ)
    (y : FullCrossedProduct α μ) :
    ∫ s, (coefficientMultiplier α μ (f.ofConv s) *
      (groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ))).snd y ∂μ = y * of α μ f := by
  have hsnd : y * of α μ f = (of α μ f : 𝓜(ℂ, FullCrossedProduct α μ)).snd y := by simp
  rw [hsnd, ← covariantMultiplierHom_integratedStarAlgHom]
  simp only [CovariantMultiplierHom.integratedStarAlgHom_apply,
    CovariantMultiplierHom.integratedMultiplier_snd_apply, covariantMultiplierHom_coefficient,
    covariantMultiplierHom_group]

/-- The canonical coefficient map `i_A : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)` is multiplier-nondegenerate:
the elements `i_A(a) x` span a norm-dense subspace of `A ⋊_α G`. -/
theorem isMultiplierNondegenerate_coefficientMultiplier :
    (coefficientMultiplier α μ).IsMultiplierNondegenerate :=
  NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense.2
    dense_span_range_coefficientMultiplier_fst

/-- The left centralizers of the integrated canonical multipliers on `C_c(G, A)` have dense linear
span in `FullCrossedProduct α μ`. -/
theorem dense_span_covariantMultiplierHom_integratedMultiplier :
    Dense (Submodule.span ℂ
      (⋃ f : C_c(G, A),
        Set.range ((covariantMultiplierHom α μ).integratedMultiplier μ f).fst) :
      Set (FullCrossedProduct α μ)) :=
  ((covariantMultiplierHom α μ).dense_span_integratedMultiplier_iff μ).2
    isMultiplierNondegenerate_coefficientMultiplier

/-! ### Disintegration of nondegenerate multiplier homomorphisms -/

section DisintegrateMultiplier

variable {B : Type w} [NonUnitalCStarAlgebra B]

/-- Disintegrate a nondegenerate multiplier homomorphism `Φ : A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` into a
covariant multiplier homomorphism of `(A, G, α)` into `𝓜(ℂ, B)`. -/
def disintegrateMultiplier (Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B))
    (hΦ : Φ.IsMultiplierNondegenerate) : CovariantMultiplierHom α B :=
  (covariantMultiplierHom α μ).map hΦ

@[simp]
theorem disintegrateMultiplier_coefficient {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) :
    (disintegrateMultiplier Φ hΦ).coefficient =
      (Φ.extendToMultiplier hΦ).toNonUnitalStarAlgHom.comp (coefficientMultiplier α μ) := by
  simp [disintegrateMultiplier]

@[simp]
theorem coe_disintegrateMultiplier_group {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) (r : G) :
    ((disintegrateMultiplier Φ hΦ).group r : 𝓜(ℂ, B)) =
      Φ.extendToMultiplier hΦ (groupMultiplier α μ r) := by
  simp [disintegrateMultiplier]

/-- The disintegrated covariant multiplier homomorphism has a multiplier-nondegenerate coefficient
map. -/
theorem isMultiplierNondegenerate_disintegrateMultiplier_coefficient
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate) :
    (disintegrateMultiplier Φ hΦ).coefficient.IsMultiplierNondegenerate :=
  disintegrateMultiplier_coefficient hΦ ▸
    hΦ.extendToMultiplier_comp isMultiplierNondegenerate_coefficientMultiplier

@[simp]
theorem disintegrateMultiplier_integratedMultiplier {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) (f : C_c(G, A)) :
    (disintegrateMultiplier Φ hΦ).integratedMultiplier μ f =
      Φ (of α μ (ConvolutionAlgebra.toConv f)) := by
  rw [disintegrateMultiplier,
    ← (covariantMultiplierHom α μ).extendToMultiplier_integratedMultiplier μ hΦ,
    covariantMultiplierHom_integratedMultiplier, Φ.extendToMultiplier_coe hΦ]

@[simp]
theorem disintegrateMultiplier_integratedStarAlgHom {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) :
    (disintegrateMultiplier Φ hΦ).integratedStarAlgHom μ = Φ.comp (of α μ) :=
  NonUnitalStarAlgHom.ext fun _ => by simp [CovariantMultiplierHom.integratedStarAlgHom_apply]

/-- Uniqueness of multiplier disintegration: any covariant multiplier homomorphism `M` into
`𝓜(ℂ, B)` whose integrated ⋆-homomorphism agrees with `Φ ∘ of α μ` automatically has
multiplier-nondegenerate `M.coefficient` and equals `disintegrateMultiplier Φ hΦ`. -/
theorem eq_disintegrateMultiplier_of_integratedStarAlgHom_eq
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate)
    {M : CovariantMultiplierHom α B} (hM : M.integratedStarAlgHom μ = Φ.comp (of α μ)) :
    M = disintegrateMultiplier Φ hΦ := by
  have hint (f : C_c(G, A)) :
      M.integratedMultiplier μ f = Φ (of α μ (ConvolutionAlgebra.toConv f)) := by
    simpa [CovariantMultiplierHom.integratedStarAlgHom_apply] using
      congr($hM (ConvolutionAlgebra.toConv f))
  have hMnd : M.coefficient.IsMultiplierNondegenerate :=
    (M.dense_span_integratedMultiplier_iff μ).1 <| by
      simpa only [Function.comp_apply, hint] using
        (NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense_span_comp
          denseRange_of_toConv).1 hΦ
  exact M.eq_of_integratedStarAlgHom_eq μ hMnd
    (hM.trans (disintegrateMultiplier_integratedStarAlgHom hΦ).symm)

end DisintegrateMultiplier

end FullCrossedProduct

/-! ### Universal property and round-trip identities for multiplier algebras -/

namespace CovariantMultiplierHom

open FullCrossedProduct

variable {B : Type w} [NonUnitalCStarAlgebra B] (M : CovariantMultiplierHom α B)

/-- The integrated ⋆-homomorphism of any covariant multiplier homomorphism into `𝓜(ℂ, B)` is
bounded by the full C⋆-seminorm. -/
theorem norm_integratedStarAlgHom_le_fullSeminorm (μ : Measure G) [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra α μ) :
    ‖M.integratedStarAlgHom μ f‖ ≤ ConvolutionAlgebra.fullSeminorm α μ f :=
  (DoubleCentralizer.norm_le_iff_forall_isNondegenerate
    (apply_nonneg (ConvolutionAlgebra.fullSeminorm α μ) f)).2 fun _ _ _ _ _ hρ =>
    (congrArg norm (M.multiplierExtension_integratedStarAlgHom μ hρ f)).trans_le <|
      ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm
        (M.toCovariantRepresentation hρ) f

/-- The integrated form of a covariant multiplier homomorphism into `𝓜(ℂ, B)`, extended by
continuity to a ⋆-homomorphism `FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`. -/
def integratedFull (μ : Measure G) [μ.IsHaarMeasure] :
    FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B) :=
  FullCrossedProduct.lift (M.integratedStarAlgHom μ) (M.norm_integratedStarAlgHom_le_fullSeminorm μ)

@[simp]
theorem integratedFull_of (μ : Measure G) [μ.IsHaarMeasure] (f : ConvolutionAlgebra α μ) :
    M.integratedFull μ (of α μ f) = M.integratedStarAlgHom μ f :=
  FullCrossedProduct.lift_of _ _ f

@[simp]
theorem integratedFull_comp_of (μ : Measure G) [μ.IsHaarMeasure] :
    (M.integratedFull μ).comp (of α μ) = M.integratedStarAlgHom μ :=
  NonUnitalStarAlgHom.ext (M.integratedFull_of μ)

/-- Composing `M.integratedFull μ` with the multiplier extension of a nondegenerate Hilbert-space
representation `ρ` of `B` yields the extended integrated form of
`M.toCovariantRepresentation hρ`. -/
@[simp]
theorem multiplierExtension_comp_integratedFull {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (μ : Measure G) [μ.IsHaarMeasure] :
    (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp (M.integratedFull μ) =
      (M.toCovariantRepresentation hρ).integratedFull μ :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp

@[simp]
theorem multiplierExtension_integratedFull_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (μ : Measure G) [μ.IsHaarMeasure] (x : FullCrossedProduct α μ) :
    ρ.multiplierExtension hρ (M.integratedFull μ x) =
      (M.toCovariantRepresentation hρ).integratedFull μ x :=
  DFunLike.congr_fun (M.multiplierExtension_comp_integratedFull hρ μ) x

/-- Naturality of `CovariantMultiplierHom.integratedFull` under equivariant coefficient maps. -/
@[simp]
theorem integratedFull_comp_fullCrossedProductMap {A' : Type v} [NonUnitalCStarAlgebra A']
    {α' : CStarAction G A'} (φ : Hom α' α) (μ : Measure G) [μ.IsHaarMeasure] :
    (M.integratedFull μ).comp (φ.fullCrossedProductMap μ) = (M.comap φ).integratedFull μ :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun f => by
    simpa using (M.integratedStarAlgHom_comap μ φ f).symm

@[simp]
theorem integratedFull_fullCrossedProductMap_apply {A' : Type v} [NonUnitalCStarAlgebra A']
    {α' : CStarAction G A'} (φ : Hom α' α) (μ : Measure G) [μ.IsHaarMeasure]
    (x : FullCrossedProduct α' μ) :
    M.integratedFull μ (φ.fullCrossedProductMap μ x) = (M.comap φ).integratedFull μ x :=
  DFunLike.congr_fun (M.integratedFull_comp_fullCrossedProductMap φ μ) x

/-- Integrating the disintegrated covariant multiplier homomorphism of a nondegenerate
`Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` recovers `Φ`. -/
@[simp]
theorem integratedFull_disintegrateMultiplier {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hΦ : Φ.IsMultiplierNondegenerate) :
    (disintegrateMultiplier Φ hΦ).integratedFull μ = Φ :=
  FullCrossedProduct.starAlgHom_ext <|
    ((disintegrateMultiplier Φ hΦ).integratedFull_comp_of μ).trans
      (disintegrateMultiplier_integratedStarAlgHom hΦ)

/-- `M.integratedFull μ` generates the exact same closed essential subspace of `B` as
`M.coefficient`. -/
theorem topologicalClosure_span_integratedFull (μ : Measure G) [μ.IsHaarMeasure] :
    (Submodule.span ℂ (⋃ x, Set.range (M.integratedFull μ x).fst)).topologicalClosure =
      (Submodule.span ℂ (⋃ a, Set.range (M.coefficient a).fst)).topologicalClosure := by
  rw [← NonUnitalStarAlgHom.topologicalClosure_span_fst_comp_eq denseRange_of_toConv
    (M.integratedFull μ)]
  simpa only [Function.comp_apply, M.integratedFull_of, integratedStarAlgHom_apply,
    ConvolutionAlgebra.ofConv_toConv] using M.topologicalClosure_span_integratedMultiplier μ

/-- The extended integrated homomorphism `M.integratedFull μ` is multiplier-nondegenerate if and
only if `M.coefficient` is multiplier-nondegenerate. -/
theorem isMultiplierNondegenerate_integratedFull_iff (μ : Measure G) [μ.IsHaarMeasure] :
    (M.integratedFull μ).IsMultiplierNondegenerate ↔ M.coefficient.IsMultiplierNondegenerate := by
  rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense,
    NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense,
    Submodule.dense_iff_topologicalClosure_eq_top, Submodule.dense_iff_topologicalClosure_eq_top,
    M.topologicalClosure_span_integratedFull μ]

/-- Disintegrating `M.integratedFull μ` recovers any nondegenerate covariant multiplier
homomorphism `M`. -/
@[simp]
theorem _root_.TauCeti.CStarAction.FullCrossedProduct.disintegrateMultiplier_integratedFull
    (μ : Measure G) [μ.IsHaarMeasure] (hM : M.coefficient.IsMultiplierNondegenerate) :
    disintegrateMultiplier (M.integratedFull μ)
      ((M.isMultiplierNondegenerate_integratedFull_iff μ).2 hM) = M :=
  (eq_disintegrateMultiplier_of_integratedStarAlgHom_eq
    ((M.isMultiplierNondegenerate_integratedFull_iff μ).2 hM)
    (M.integratedFull_comp_of μ).symm).symm

/-- Applying the multiplier extension of `M.integratedFull μ` to `i_A(a)` recovers
`M.coefficient a`. -/
@[simp]
theorem extendToMultiplier_integratedFull_coefficientMultiplier (μ : Measure G) [μ.IsHaarMeasure]
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) (a : A) :
    (M.integratedFull μ).extendToMultiplier h (coefficientMultiplier α μ a) = M.coefficient a := by
  simpa only [disintegrateMultiplier_coefficient, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.coe_toNonUnitalStarAlgHom] using
    congrArg (fun N => N.coefficient a) (disintegrateMultiplier_integratedFull M μ
      ((M.isMultiplierNondegenerate_integratedFull_iff μ).1 h))

/-- Applying the multiplier extension of `M.integratedFull μ` to `i_G(r)` recovers `M.group r`. -/
@[simp]
theorem extendToMultiplier_integratedFull_groupMultiplier (μ : Measure G) [μ.IsHaarMeasure]
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) (r : G) :
    (M.integratedFull μ).extendToMultiplier h (groupMultiplier α μ r) = M.group r := by
  simpa only [coe_disintegrateMultiplier_group] using
    congrArg (fun N => (N.group r : 𝓜(ℂ, B))) (disintegrateMultiplier_integratedFull M μ
      ((M.isMultiplierNondegenerate_integratedFull_iff μ).1 h))

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
    exact ⟨M.extendToMultiplier_integratedFull_coefficientMultiplier μ hΦ,
      M.extendToMultiplier_integratedFull_groupMultiplier μ hΦ⟩
  · have hdis : disintegrateMultiplier Φ hΦ = M :=
      CovariantMultiplierHom.ext (NonUnitalStarAlgHom.ext fun a => by simp [hA])
        (MonoidHom.ext fun r => Subtype.ext <| by simp [hG])
    rw [← integratedFull_disintegrateMultiplier hΦ, hdis]

/-- Integrating the canonical covariant multiplier homomorphism `(i_A, i_G)` of `A ⋊_α G` yields
the canonical embedding `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)`. -/
@[simp]
theorem _root_.TauCeti.CStarAction.FullCrossedProduct.covariantMultiplierHom_integratedFull :
    (covariantMultiplierHom α μ).integratedFull μ =
      DoubleCentralizer.coeHom (𝕜 := ℂ) (A := FullCrossedProduct α μ) :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp

end CovariantMultiplierHom

end TauCeti.CStarAction
