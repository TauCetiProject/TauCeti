/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Functoriality
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Multiplier

/-!
# Disintegration and the multiplier universal property of full crossed products

Let `α` be a point-norm continuous action of a locally compact group `G : Type u` on a possibly
nonunital C⋆-algebra `A : Type v` with left Haar measure `μ`. The canonical maps
`FullCrossedProduct.coefficientMultiplier : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)` and
`FullCrossedProduct.groupMultiplier : G →* unitary 𝓜(ℂ, A ⋊_α G)` form a covariant multiplier
homomorphism `FullCrossedProduct.covariantMultiplierHom α μ`.

In this file we prove:

* **Strict Bochner multiplier-integral formula** (`FullCrossedProduct.of_mul_eq_integral`,
  `FullCrossedProduct.mul_of_eq_integral`,
  `FullCrossedProduct.covariantMultiplierHom_integratedMultiplier`): left and right multiplication
  by `of α μ f` on `A ⋊_α G` agree with the strict Bochner integral of `r ↦ i_A(f(r)) i_G(r)`, so
  the integrated multipliers of `(i_A, i_G)` lie in `A ⋊_α G ⊆ 𝓜(ℂ, A ⋊_α G)` and have dense range.
* **Nondegeneracy of `i_A`** (`FullCrossedProduct.isMultiplierNondegenerate_coefficientMultiplier`):
  the left-centralizer span `span { i_A(a) x | a ∈ A, x ∈ A ⋊_α G }` is norm-dense in `A ⋊_α G`.
* **Hilbert-space disintegration** (`FullCrossedProduct.disintegrate`,
  `CovariantRepresentation.integratedFull_disintegrate`,
  `FullCrossedProduct.disintegrate_integratedFull`,
  `CovariantRepresentation.eq_integratedFull_iff`): nondegenerate representations of `A ⋊_α G` on
  Hilbert spaces correspond bijectively to nondegenerate covariant representations of `(A, G, α)`.
* **Multiplier-algebra universal property and disintegration**
  (`CovariantMultiplierHom.integratedFull`, `FullCrossedProduct.disintegrateMultiplier`,
  `CovariantMultiplierHom.integratedFull_disintegrateMultiplier`,
  `FullCrossedProduct.disintegrateMultiplier_integratedFull`,
  `CovariantMultiplierHom.eq_integratedFull_iff`): every covariant multiplier homomorphism into
  `𝓜(ℂ, B)` (`B : Type (max u v)`) integrates to `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`, and nondegenerate
  homomorphisms `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` correspond bijectively to nondegenerate covariant
  multiplier homomorphisms of `(A, G, α)` into `𝓜(ℂ, B)`.

No unit, separability, or global σ-finiteness is assumed. Disintegration works for target Hilbert
spaces and C⋆-algebras in an arbitrary universe.

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
    (covariantMultiplierHom α μ).coefficient = coefficientMultiplier α μ :=
  (rfl)

@[simp]
theorem covariantMultiplierHom_group :
    (covariantMultiplierHom α μ).group = groupMultiplier α μ :=
  (rfl)

/-- Left multiplication by `of α μ f` in the full crossed product is given in the strict topology
by the Bochner integral `∫ r, (i_A(f(r)) i_G(r)).fst x ∂μ`. -/
theorem of_mul_eq_integral (f : ConvolutionAlgebra α μ) (x : FullCrossedProduct α μ) :
    of α μ f * x =
      ∫ r, (coefficientMultiplier α μ (f.ofConv r) * groupMultiplier α μ r).fst x ∂μ := by
  have hint := (covariantMultiplierHom α μ).integrable_integrand_fst μ f.ofConv x
  rw [covariantMultiplierHom_coefficient, covariantMultiplierHom_group] at hint
  refine eq_of_sub_eq_zero <| norm_le_zero_iff.1 <| (norm_le_iff le_rfl).2 fun H _ _ _ P => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun v => ?_
  rw [zero_mul, norm_le_zero_iff, map_sub, sub_apply, sub_eq_zero]
  let L : FullCrossedProduct α μ →L[ℂ] H :=
    LinearMap.mkContinuous
      { toFun z := P.integratedFull μ z v
        map_add' y z := by simp
        map_smul' c z := by simp }
      ‖v‖ fun z => ((P.integratedFull μ z).le_opNorm v).trans <|
        (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ z)
          (norm_nonneg v)).trans_eq (mul_comm _ _)
  have hcomm := L.integral_comp_comm hint
  simp only [L, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] at hcomm
  rw [← hcomm, map_mul, P.integratedFull_of, CovariantRepresentation.integratedStarAlgHom_apply,
    mul_apply_eq_comp, P.integratedOperator_apply]
  congr 1 with r
  simp [DoubleCentralizer.mul_fst, mul_apply_eq_comp]

/-- The strict Bochner integrated form of the canonical covariant multiplier homomorphism on
`C_c(G, A)` is the canonical inclusion into `A ⋊_α G ⊆ 𝓜(ℂ, A ⋊_α G)`. -/
@[simp]
theorem covariantMultiplierHom_integratedMultiplier (f : C_c(G, A)) :
    (covariantMultiplierHom α μ).integratedMultiplier μ f =
      (of α μ (ConvolutionAlgebra.toConv f) : 𝓜(ℂ, FullCrossedProduct α μ)) :=
  DoubleCentralizer.ext_fst fun x => by
    simpa using (of_mul_eq_integral (ConvolutionAlgebra.toConv f) x).symm

/-- The integrated ⋆-homomorphism of `(i_A, i_G)` on the twisted convolution algebra is `of α μ`
followed by the canonical inclusion into `𝓜(ℂ, A ⋊_α G)`. -/
@[simp]
theorem covariantMultiplierHom_integratedStarAlgHom (f : ConvolutionAlgebra α μ) :
    (covariantMultiplierHom α μ).integratedStarAlgHom μ f =
      (of α μ f : 𝓜(ℂ, FullCrossedProduct α μ)) := by
  simp [CovariantMultiplierHom.integratedStarAlgHom_apply]

/-- Right multiplication by `of α μ f` in the full crossed product is given in the strict topology
by the Bochner integral `∫ r, (i_A(f(r)) i_G(r)).snd x ∂μ`. -/
theorem mul_of_eq_integral (f : ConvolutionAlgebra α μ) (x : FullCrossedProduct α μ) :
    x * of α μ f =
      ∫ r, (coefficientMultiplier α μ (f.ofConv r) * groupMultiplier α μ r).snd x ∂μ := by
  calc x * of α μ f
      = ((of α μ f : 𝓜(ℂ, FullCrossedProduct α μ))).snd x := by simp
    _ = ((covariantMultiplierHom α μ).integratedStarAlgHom μ f).snd x := by
        rw [covariantMultiplierHom_integratedStarAlgHom]
    _ = ∫ r, (coefficientMultiplier α μ (f.ofConv r) * groupMultiplier α μ r).snd x ∂μ := by
        rw [CovariantMultiplierHom.integratedStarAlgHom_apply,
          CovariantMultiplierHom.integratedMultiplier_snd_apply,
          covariantMultiplierHom_coefficient, covariantMultiplierHom_group]

/-- The canonical coefficient map `i_A : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)` is multiplier-nondegenerate:
the elements `i_A(a) x` span a norm-dense subspace of `A ⋊_α G`. -/
theorem isMultiplierNondegenerate_coefficientMultiplier :
    (coefficientMultiplier α μ).IsMultiplierNondegenerate := by
  rw [← covariantMultiplierHom_coefficient,
    ← (covariantMultiplierHom α μ).dense_span_integratedMultiplier_iff μ]
  have hcoe := (NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense_span_comp
    (φ := DoubleCentralizer.coeHom (𝕜 := ℂ) (A := FullCrossedProduct α μ))
    denseRange_of_toConv).1 NonUnitalStarAlgHom.isMultiplierNondegenerate_coeHom
  simpa only [Function.comp_apply, covariantMultiplierHom_integratedMultiplier,
    DoubleCentralizer.coeHom_apply] using hcoe

/-- The left centralizers of the integrated canonical multipliers on `C_c(G, A)` have dense linear
span in `FullCrossedProduct α μ`. -/
theorem dense_span_covariantMultiplierHom_integratedMultiplier :
    Dense (Submodule.span ℂ
      (⋃ f : C_c(G, A),
        Set.range ((covariantMultiplierHom α μ).integratedMultiplier μ f).fst) :
      Set (FullCrossedProduct α μ)) :=
  ((covariantMultiplierHom α μ).dense_span_integratedMultiplier_iff μ).2
    isMultiplierNondegenerate_coefficientMultiplier

/-! ### Disintegration of nondegenerate Hilbert-space representations -/

section DisintegrateHilbert

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Disintegrate a nondegenerate Hilbert-space representation `L` of `A ⋊_α G` into a covariant
representation of `(A, G, α)` by applying `L.multiplierExtension hL` to `(i_A, i_G)`. -/
def disintegrate (L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hL : L.IsNondegenerate) : CovariantRepresentation α H :=
  (covariantMultiplierHom α μ).toCovariantRepresentation hL

@[simp]
theorem disintegrate_coefficient {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hL : L.IsNondegenerate) :
    (disintegrate L hL).coefficient =
      (L.multiplierExtension hL).toNonUnitalStarAlgHom.comp (coefficientMultiplier α μ) := by
  simp [disintegrate]

@[simp]
theorem disintegrate_group_apply {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hL : L.IsNondegenerate) (r : G) :
    (disintegrate L hL).group r = L.multiplierExtension hL (groupMultiplier α μ r) := by
  simp [disintegrate]

/-- The disintegrated covariant representation has a nondegenerate coefficient representation. -/
theorem isNondegenerate_disintegrate_coefficient {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hL : L.IsNondegenerate) : (disintegrate L hL).coefficient.IsNondegenerate := by
  rw [disintegrate_coefficient]
  exact hL.multiplierExtension_comp isMultiplierNondegenerate_coefficientMultiplier

@[simp]
theorem disintegrate_integratedOperator {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hL : L.IsNondegenerate) (f : C_c(G, A)) :
    (disintegrate L hL).integratedOperator μ f =
      L (of α μ (ConvolutionAlgebra.toConv f)) := by
  rw [disintegrate, ← (covariantMultiplierHom α μ).multiplierExtension_integratedMultiplier μ hL,
    covariantMultiplierHom_integratedMultiplier, L.multiplierExtension_coe hL]

@[simp]
theorem disintegrate_integratedStarAlgHom {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hL : L.IsNondegenerate) :
    (disintegrate L hL).integratedStarAlgHom μ = L.comp (of α μ) := by
  ext f : 1
  simp [CovariantRepresentation.integratedStarAlgHom_apply]

/-- Uniqueness of Hilbert-space disintegration: any covariant representation `P` on `H` whose
integrated ⋆-homomorphism agrees with `L ∘ of α μ` automatically has nondegenerate `P.coefficient`
and equals `disintegrate L hL`. -/
theorem eq_disintegrate_of_integratedStarAlgHom_eq {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hL : L.IsNondegenerate) {P : CovariantRepresentation α H}
    (hP : P.integratedStarAlgHom μ = L.comp (of α μ)) : P = disintegrate L hL := by
  have hop (f : C_c(G, A)) :
      P.integratedOperator μ f = L (of α μ (ConvolutionAlgebra.toConv f)) := by
    simpa [CovariantRepresentation.integratedStarAlgHom_apply] using
      congr($hP (ConvolutionAlgebra.toConv f))
  have hPnd : P.coefficient.IsNondegenerate := by
    rw [← P.dense_span_integratedOperator_iff μ]
    simpa only [Function.comp_apply, hop] using
      (NonUnitalStarAlgHom.isNondegenerate_iff_dense_span_comp denseRange_of_toConv).1 hL
  exact P.eq_of_integratedOperator_eq μ hPnd fun f =>
    (hop f).trans (disintegrate_integratedOperator hL f).symm

end DisintegrateHilbert

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
    (disintegrateMultiplier Φ hΦ).coefficient.IsMultiplierNondegenerate := by
  rw [disintegrateMultiplier_coefficient]
  exact hΦ.extendToMultiplier_comp isMultiplierNondegenerate_coefficientMultiplier

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
    (disintegrateMultiplier Φ hΦ).integratedStarAlgHom μ = Φ.comp (of α μ) := by
  ext f : 1
  simp [CovariantMultiplierHom.integratedStarAlgHom_apply]

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
  have hMnd : M.coefficient.IsMultiplierNondegenerate := by
    rw [← M.dense_span_integratedMultiplier_iff μ]
    simpa only [Function.comp_apply, hint] using
      (NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense_span_comp denseRange_of_toConv).1 hΦ
  exact M.eq_of_integratedStarAlgHom_eq μ hMnd
    (hM.trans (disintegrateMultiplier_integratedStarAlgHom hΦ).symm)

end DisintegrateMultiplier

end FullCrossedProduct

/-! ### Round-trip identities and universal property on Hilbert spaces in `Type (max u v)` -/

namespace CovariantRepresentation

open FullCrossedProduct

variable {H : Type (max u v)} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Integrating the disintegrated covariant representation of a nondegenerate representation `L`
recovers `L`. -/
@[simp]
theorem integratedFull_disintegrate {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hL : L.IsNondegenerate) : (disintegrate L hL).integratedFull μ = L := by
  apply FullCrossedProduct.starAlgHom_ext
  rw [integratedFull_comp_of, disintegrate_integratedStarAlgHom]

/-- `P.integratedFull μ` generates the exact same closed essential subspace of `H` as
`P.coefficient`. -/
theorem topologicalClosure_span_integratedFull (P : CovariantRepresentation α H) (μ : Measure G)
    [μ.IsHaarMeasure] :
    (Submodule.span ℂ (⋃ x, Set.range (P.integratedFull μ x))).topologicalClosure =
      (Submodule.span ℂ (⋃ a, Set.range (P.coefficient a))).topologicalClosure := by
  rw [← NonUnitalStarAlgHom.topologicalClosure_span_range_comp_eq denseRange_of_toConv
    (P.integratedFull μ)]
  simpa only [Function.comp_apply, P.integratedFull_of, integratedStarAlgHom_apply,
    ConvolutionAlgebra.ofConv_toConv] using P.topologicalClosure_span_integratedOperator μ

/-- The extended integrated form `P.integratedFull μ` is nondegenerate if and only if
`P.coefficient` is nondegenerate. -/
theorem isNondegenerate_integratedFull_iff (P : CovariantRepresentation α H) (μ : Measure G)
    [μ.IsHaarMeasure] :
    (P.integratedFull μ).IsNondegenerate ↔ P.coefficient.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense, NonUnitalStarAlgHom.isNondegenerate_iff_dense,
    Submodule.dense_iff_topologicalClosure_eq_top, Submodule.dense_iff_topologicalClosure_eq_top,
    P.topologicalClosure_span_integratedFull μ]

/-- Disintegrating `P.integratedFull μ` recovers any nondegenerate covariant representation `P`. -/
@[simp]
theorem _root_.TauCeti.CStarAction.FullCrossedProduct.disintegrate_integratedFull
    (P : CovariantRepresentation α H) (μ : Measure G) [μ.IsHaarMeasure]
    (hP : P.coefficient.IsNondegenerate) :
    disintegrate (P.integratedFull μ) ((P.isNondegenerate_integratedFull_iff μ).2 hP) = P :=
  (eq_disintegrate_of_integratedStarAlgHom_eq
    ((P.isNondegenerate_integratedFull_iff μ).2 hP) P.integratedFull_comp_of.symm).symm

/-- Applying the multiplier extension of `P.integratedFull μ` to `i_A(a)` recovers
`P.coefficient a`. -/
@[simp]
theorem multiplierExtension_integratedFull_coefficientMultiplier (P : CovariantRepresentation α H)
    (μ : Measure G) [μ.IsHaarMeasure] (h : (P.integratedFull μ).IsNondegenerate) (a : A) :
    (P.integratedFull μ).multiplierExtension h (coefficientMultiplier α μ a) = P.coefficient a := by
  have hP := (P.isNondegenerate_integratedFull_iff μ).1 h
  simpa only [disintegrate_coefficient, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.coe_toNonUnitalStarAlgHom] using
    congrArg (fun Q => Q.coefficient a) (disintegrate_integratedFull P μ hP)

/-- Applying the multiplier extension of `P.integratedFull μ` to `i_G(r)` recovers `P.group r`. -/
@[simp]
theorem multiplierExtension_integratedFull_groupMultiplier (P : CovariantRepresentation α H)
    (μ : Measure G) [μ.IsHaarMeasure] (h : (P.integratedFull μ).IsNondegenerate) (r : G) :
    (P.integratedFull μ).multiplierExtension h (groupMultiplier α μ r) = P.group r := by
  have hP := (P.isNondegenerate_integratedFull_iff μ).1 h
  simpa only [disintegrate_group_apply] using
    congrArg (fun Q => Q.group r) (disintegrate_integratedFull P μ hP)

/-- Universal property of `(A ⋊_α G, i_A, i_G)` for nondegenerate Hilbert-space representations:
`P.integratedFull μ` is the unique nondegenerate representation of `A ⋊_α G` whose multiplier
extension sends `i_A` to `P.coefficient` and `i_G` to `P.group`. -/
theorem eq_integratedFull_iff {P : CovariantRepresentation α H}
    {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hL : L.IsNondegenerate) :
    L = P.integratedFull μ ↔
      (∀ a, L.multiplierExtension hL (coefficientMultiplier α μ a) = P.coefficient a) ∧
        ∀ r, L.multiplierExtension hL (groupMultiplier α μ r) = P.group r := by
  refine ⟨?_, fun ⟨hA, hG⟩ => ?_⟩
  · rintro rfl
    exact ⟨P.multiplierExtension_integratedFull_coefficientMultiplier μ hL,
      P.multiplierExtension_integratedFull_groupMultiplier μ hL⟩
  · have hdis : disintegrate L hL = P := by
      apply CovariantRepresentation.ext
      · ext a v
        simpa only [disintegrate_coefficient, NonUnitalStarAlgHom.comp_apply,
          StarAlgHom.coe_toNonUnitalStarAlgHom] using congr($(hA a) v)
      · refine DFunLike.ext _ _ fun r => ?_
        simpa only [disintegrate_group_apply] using hG r
    rw [← integratedFull_disintegrate hL, hdis]

end CovariantRepresentation

/-! ### Universal property and round-trip identities for multiplier algebras -/

namespace CovariantMultiplierHom

open FullCrossedProduct

variable {B : Type (max u v)} [NonUnitalCStarAlgebra B] (M : CovariantMultiplierHom α B)

/-- The integrated ⋆-homomorphism of any covariant multiplier homomorphism into `𝓜(ℂ, B)`
(`B : Type (max u v)`) is bounded by the full C⋆-seminorm. -/
theorem norm_integratedStarAlgHom_le_fullSeminorm (μ : Measure G) [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra α μ) :
    ‖M.integratedStarAlgHom μ f‖ ≤ ConvolutionAlgebra.fullSeminorm α μ f := by
  refine (DoubleCentralizer.norm_le_iff_forall_isNondegenerate
    (apply_nonneg (ConvolutionAlgebra.fullSeminorm α μ) f)).2 fun H _ _ _ ρ hρ => ?_
  rw [M.multiplierExtension_integratedStarAlgHom μ hρ]
  exact ConvolutionAlgebra.norm_integratedStarAlgHom_le_fullSeminorm
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
theorem multiplierExtension_comp_integratedFull {H : Type (max u v)} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (μ : Measure G) [μ.IsHaarMeasure] :
    (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp (M.integratedFull μ) =
      (M.toCovariantRepresentation hρ).integratedFull μ := by
  apply FullCrossedProduct.starAlgHom_ext
  ext f : 1
  simp

@[simp]
theorem multiplierExtension_integratedFull_apply {H : Type (max u v)} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (μ : Measure G) [μ.IsHaarMeasure] (x : FullCrossedProduct α μ) :
    ρ.multiplierExtension hρ (M.integratedFull μ x) =
      (M.toCovariantRepresentation hρ).integratedFull μ x :=
  DFunLike.congr_fun (M.multiplierExtension_comp_integratedFull hρ μ) x

/-- Naturality of `CovariantMultiplierHom.integratedFull` under equivariant coefficient maps. -/
@[simp]
theorem integratedFull_comp_fullCrossedProductMap {A' : Type v} [NonUnitalCStarAlgebra A']
    {α' : CStarAction G A'} (φ : Hom α' α) (μ : Measure G) [μ.IsHaarMeasure] :
    (M.integratedFull μ).comp (φ.fullCrossedProductMap μ) = (M.comap φ).integratedFull μ := by
  apply FullCrossedProduct.starAlgHom_ext
  ext f : 1
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
    (disintegrateMultiplier Φ hΦ).integratedFull μ = Φ := by
  apply FullCrossedProduct.starAlgHom_ext
  rw [integratedFull_comp_of, disintegrateMultiplier_integratedStarAlgHom]

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
  have hM := (M.isMultiplierNondegenerate_integratedFull_iff μ).1 h
  simpa only [disintegrateMultiplier_coefficient, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.coe_toNonUnitalStarAlgHom] using
    congrArg (fun N => N.coefficient a) (disintegrateMultiplier_integratedFull M μ hM)

/-- Applying the multiplier extension of `M.integratedFull μ` to `i_G(r)` recovers `M.group r`. -/
@[simp]
theorem extendToMultiplier_integratedFull_groupMultiplier (μ : Measure G) [μ.IsHaarMeasure]
    (h : (M.integratedFull μ).IsMultiplierNondegenerate) (r : G) :
    (M.integratedFull μ).extendToMultiplier h (groupMultiplier α μ r) = M.group r := by
  have hM := (M.isMultiplierNondegenerate_integratedFull_iff μ).1 h
  simpa only [coe_disintegrateMultiplier_group] using
    congrArg (fun N => (N.group r : 𝓜(ℂ, B))) (disintegrateMultiplier_integratedFull M μ hM)

/-- Universal property of `(A ⋊_α G, i_A, i_G)` for nondegenerate multiplier homomorphisms:
`M.integratedFull μ` is the unique multiplier-nondegenerate ⋆-homomorphism
`FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` whose multiplier extension sends `i_A` to `M.coefficient`
and `i_G` to `M.group`. -/
theorem eq_integratedFull_iff {M : CovariantMultiplierHom α B}
    {Φ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hΦ : Φ.IsMultiplierNondegenerate) :
    Φ = M.integratedFull μ ↔
      (∀ a, Φ.extendToMultiplier hΦ (coefficientMultiplier α μ a) = M.coefficient a) ∧
        ∀ r, Φ.extendToMultiplier hΦ (groupMultiplier α μ r) = M.group r := by
  refine ⟨?_, fun ⟨hA, hG⟩ => ?_⟩
  · rintro rfl
    exact ⟨M.extendToMultiplier_integratedFull_coefficientMultiplier μ hΦ,
      M.extendToMultiplier_integratedFull_groupMultiplier μ hΦ⟩
  · have hdis : disintegrateMultiplier Φ hΦ = M := by
      refine CovariantMultiplierHom.ext ?_ ?_
      · ext a : 1
        simpa only [disintegrateMultiplier_coefficient, NonUnitalStarAlgHom.comp_apply,
          StarAlgHom.coe_toNonUnitalStarAlgHom] using hA a
      · ext r : 1
        refine Subtype.ext ?_
        simpa only [coe_disintegrateMultiplier_group] using hG r
    rw [← integratedFull_disintegrateMultiplier hΦ, hdis]

/-- Integrating the canonical covariant multiplier homomorphism `(i_A, i_G)` of `A ⋊_α G` yields
the canonical embedding `A ⋊_α G →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)`. -/
@[simp]
theorem _root_.TauCeti.CStarAction.FullCrossedProduct.covariantMultiplierHom_integratedFull :
    (covariantMultiplierHom α μ).integratedFull μ =
      DoubleCentralizer.coeHom (𝕜 := ℂ) (A := FullCrossedProduct α μ) := by
  apply FullCrossedProduct.starAlgHom_ext
  ext f : 1
  simp

end CovariantMultiplierHom

end TauCeti.CStarAction
