/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.MeasureTheory.Function.Lp.Operator.Multiplication
public import TauCeti.RepresentationTheory.Continuous.LeftRegular
import TauCeti.Analysis.CStarAlgebra.ApproximateUnit
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Group.ConvolutionSupport
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Regular covariant representations

Let `α` be a point-norm continuous action of a topological group `G` on a possibly nonunital
C⋆-algebra `A`, let `ρ` be a representation of `A` on a Hilbert space `H`, and let `μ` be a
left-invariant measure on `G`, typically a left Haar measure. The *regular covariant
representation* induced by `ρ` acts on `L²(G, H)` by

`π(a) ξ (r) = ρ (α_{r⁻¹}(a)) (ξ r)` and `λ_s ξ (r) = ξ (s⁻¹ r)`.

The coefficient representation `π` is multiplication by the bounded continuous operator-valued
function `r ↦ ρ (α_{r⁻¹}(a))`, so it is a ⋆-homomorphism; the group representation `λ` is the left
regular representation, which is unitary and strongly continuous. The pair is covariant:
`λ_s π(a) λ_s⁻¹ = π(α_s(a))`. Integrating it gives the regular representations of the convolution
algebra, whose norms define the reduced crossed product.

The representation `ρ` need not be nondegenerate or faithful, and no separability, second
countability, or σ-finiteness is assumed: the measure need only be left invariant, locally finite,
and inner regular with respect to compact sets on sets of finite measure, as the Haar measure
`MeasureTheory.Measure.haar` of a locally compact group is.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.

## Main definitions

* `TauCeti.CStarAction.CovariantRepresentation.regular`: the regular covariant representation
  `(π, λ)` on `L²(G, H)` induced by `ρ`.

If `ρ` is nondegenerate, so is the regular coefficient representation `π`, and conversely when `μ`
is positive on nonempty open sets. Thus a nondegenerate representation of `A` induces a
nondegenerate regular covariant pair, which is the kind of pair whose integrated form is a
nondegenerate representation of the crossed product and extends to its multiplier algebra.

The integrated regular representation `π ⋊ λ` of `C_c(G, A)` has the matrix coefficients
`⟪η, (π ⋊ λ)(f) ξ⟫ = ∫ s, ∫ r, ⟪η r, ρ (α_{r⁻¹}(f s)) (ξ (s⁻¹ r))⟫ dr ds`. If `ρ` is faithful and
`μ` is positive on nonempty open sets, then `π ⋊ λ` is injective on `C_c(G, A)`: testing against
scalar multiples of fixed vectors by continuous compactly supported functions recovers every
matrix coefficient `⟪w, ρ (f s) v⟫`. Hence integrated norms of regular representations are norms,
not merely seminorms, on the convolution algebra.

## Main statements

* `TauCeti.CStarAction.CovariantRepresentation.coeFn_regular_coefficient`: the coefficient
  representation is `π(a) ξ (r) = ρ (α_{r⁻¹}(a)) (ξ r)` almost everywhere.
* `TauCeti.CStarAction.CovariantRepresentation.regular_group`: the group representation is the
  left regular representation `MeasureTheory.Measure.leftRegular`.
* `TauCeti.CStarAction.CovariantRepresentation.isNondegenerate_regular_coefficient`: the regular
  coefficient representation induced by a nondegenerate `ρ` is nondegenerate, and
  `isNondegenerate_regular_coefficient_iff` gives the converse when `μ` is positive on nonempty
  open sets.
* `TauCeti.CStarAction.CovariantRepresentation.inner_integratedOperator_regular_apply`: the
  matrix coefficients of the integrated regular representation.
* `TauCeti.CStarAction.CovariantRepresentation.injective_integratedOperator_regular`: the
  integrated regular representation induced by a faithful `ρ` is injective on `C_c(G, A)`.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CStarAlgebra CompactlySupported ENNReal InnerProductSpace

namespace TauCeti.CStarAction

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded continuous operator-valued function `r ↦ ρ (α_{r⁻¹}(a))` by which `a` acts in the
regular covariant representation, as a ⋆-homomorphism in `a`. -/
private def regularSymbol (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₙₐ[ℂ] (G →ᵇ (H →L[ℂ] H)) where
  toFun a := .ofNormedAddCommGroup (fun r => ρ (α r⁻¹ a))
    ((map_continuous ρ).comp (α.continuous_inv_apply a)) ‖a‖
    fun r => (NonUnitalStarAlgHom.norm_apply_le ρ _).trans (StarAlgEquiv.norm_map _ _).le
  map_smul' c a := by ext1 r; simp
  map_zero' := by ext1 r; simp
  map_add' a b := by ext1 r; simp
  map_mul' a b := by ext1 r; simp
  map_star' a := by ext1 r; simp [map_star]

private theorem regularSymbol_apply (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A)
    (r : G) : regularSymbol α ρ a r = ρ (α r⁻¹ a) :=
  (rfl)

namespace CovariantRepresentation

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]

omit [IsLocallyFiniteMeasure μ] in
/-- Left translation intertwines multiplication by `r ↦ ρ (α_{r⁻¹}(a))` with multiplication by
`r ↦ ρ (α_{r⁻¹}(α_g(a)))`; this is the covariance of the regular covariant representation. -/
private theorem leftRegular_mulLp_regularSymbol (g : G) (a : A) (ξ : Lp H 2 μ) :
    μ.leftRegular ℂ H 2 g ((regularSymbol α ρ a).mulLp μ 2 ENNReal.ofNat_ne_top ξ) =
      (regularSymbol α ρ (α g a)).mulLp μ 2 ENNReal.ofNat_ne_top (μ.leftRegular ℂ H 2 g ξ) := by
  refine (BoundedContinuousFunction.mulLp_eq_iff.2 ?_).symm
  -- Both sides are `r ↦ ρ (α_{r⁻¹ g}(a)) (ξ (g⁻¹ r))` almost everywhere.
  have hcomp := (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
    ((regularSymbol α ρ a).coeFn_mulLp (μ := μ) ENNReal.ofNat_ne_top ξ)
  filter_upwards [μ.coeFn_leftRegular (𝕜 := ℂ) 2 g ξ, hcomp,
    μ.coeFn_leftRegular (𝕜 := ℂ) 2 g ((regularSymbol α ρ a).mulLp μ 2 ENNReal.ofNat_ne_top ξ)]
    with r hξ hcomp hL
  simp only [Function.comp_apply] at hcomp
  simp [hξ, hL, hcomp, regularSymbol_apply, mul_apply]

/-- The regular covariant representation on `L²(G, H)` induced by a representation `ρ` of `A` on
`H`: `a` acts by `ξ ↦ (r ↦ ρ (α_{r⁻¹}(a)) (ξ r))` and `s` by left translation
`ξ ↦ (r ↦ ξ (s⁻¹ r))`. -/
def regular : CovariantRepresentation α (Lp H 2 μ) where
  coefficient :=
    (BoundedContinuousFunction.mulL2StarAlgHom μ).toNonUnitalStarAlgHom.comp (regularSymbol α ρ)
  group := μ.leftRegular ℂ H 2
  isUnitary := μ.isUnitary_leftRegular
  continuous_orbit := μ.continuous_leftRegular_apply 2 ENNReal.ofNat_ne_top
  covariance g a ξ := by
    simp only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
      BoundedContinuousFunction.mulL2StarAlgHom_apply]
    exact leftRegular_mulLp_regularSymbol α ρ μ g a ξ

private theorem regular_coefficient_apply (a : A) :
    (regular α ρ μ).coefficient a = (regularSymbol α ρ a).mulLp μ 2 ENNReal.ofNat_ne_top := by
  simp only [regular, NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
    BoundedContinuousFunction.mulL2StarAlgHom_apply]

/-- The group representation of the regular covariant representation is the left regular
representation. -/
@[simp]
theorem regular_group : (regular α ρ μ).group = μ.leftRegular ℂ H 2 :=
  (rfl)

/-- The coefficient representation of the regular covariant representation acts by
`π(a) ξ (r) = ρ (α_{r⁻¹}(a)) (ξ r)` almost everywhere. -/
theorem coeFn_regular_coefficient (a : A) (ξ : Lp H 2 μ) :
    (regular α ρ μ).coefficient a ξ =ᵐ[μ] fun r => ρ (α r⁻¹ a) (ξ r) := by
  rw [regular_coefficient_apply]
  exact (regularSymbol α ρ a).coeFn_mulLp ENNReal.ofNat_ne_top ξ

variable {α ρ μ} in
/-- The coefficient representation of the regular covariant representation is determined by its
pointwise formula: an `L²` class equal almost everywhere to `r ↦ ρ (α_{r⁻¹}(a)) (ξ r)` is
`π(a) ξ`. -/
theorem regular_coefficient_eq_iff {a : A} {ξ η : Lp H 2 μ} :
    (regular α ρ μ).coefficient a ξ = η ↔ (fun r => ρ (α r⁻¹ a) (ξ r)) =ᵐ[μ] η := by
  rw [regular_coefficient_apply]
  exact BoundedContinuousFunction.mulLp_eq_iff

section Nondegenerate

variable {α ρ μ}

/-- Along an increasing approximate unit `e`, the regular coefficient operators `π(e)` converge
on the vector `r ↦ 𝟙_t(r) ρ(b) w` when `t` is compact: there `π(e)` acts by
`r ↦ 𝟙_t(r) ρ(α_{r⁻¹}(e α_r(b))) w`, and `e α_r(b) → α_r(b)` uniformly for `r ∈ t`. -/
private theorem tendsto_regular_coefficient_indicatorConstLp [PartialOrder A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) {t : Set G} (ht : MeasurableSet t) (htc : IsCompact t)
    (hμt : μ t ≠ ∞) (b : A) (w : H) :
    Tendsto (fun e => (regular α ρ μ).coefficient e (indicatorConstLp 2 ht hμt (ρ b w))) l
      (𝓝 (indicatorConstLp 2 ht hμt (ρ b w))) := by
  set ξ := indicatorConstLp 2 ht hμt (ρ b w)
  set C := μ.real t ^ (1 / (2 : ℝ≥0∞).toReal) * ‖w‖
  have hC : 0 ≤ C := by positivity
  have hunif := Metric.tendstoUniformlyOn_iff.1 <|
    hl.tendstoUniformlyOn_mul_right (htc.image (α.continuous_orbit b))
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [hunif (ε / (C + 1)) (by positivity)] with e he
  rw [dist_eq_norm]
  calc ‖(regular α ρ μ).coefficient e ξ - ξ‖
      ≤ ‖indicatorConstLp 2 ht hμt (ε / (C + 1) * ‖w‖)‖ := by
        refine Lp.norm_le_norm_of_ae_le ?_
        filter_upwards [Lp.coeFn_sub ((regular α ρ μ).coefficient e ξ) ξ,
          coeFn_regular_coefficient α ρ μ e ξ,
          indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hμt) (c := ρ b w),
          indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hμt) (c := ε / (C + 1) * ‖w‖)]
          with r h₁ h₂ h₃ h₄
        rw [h₁, Pi.sub_apply, h₂, h₃, h₄]
        by_cases hr : r ∈ t
        · -- `ρ(α_{r⁻¹}(e)) ρ(b) w - ρ(b) w = ρ(α_{r⁻¹}(e α_r(b) - α_r(b))) w`.
          have hsub : ρ (α r⁻¹ e) (ρ b w) - ρ b w = ρ (α r⁻¹ (e * α r b - α r b)) w := by
            simp [map_sub, map_mul, inv_apply_apply]
          have hdist := he (α r b) ⟨r, hr, rfl⟩
          rw [id, dist_comm, dist_eq_norm] at hdist
          simp only [Set.indicator_of_mem hr, hsub, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : 0 ≤ ε / (C + 1) * ‖w‖)]
          calc ‖ρ (α r⁻¹ (e * α r b - α r b)) w‖ ≤ ‖e * α r b - α r b‖ * ‖w‖ :=
                (ContinuousLinearMap.le_opNorm _ _).trans <| mul_le_mul_of_nonneg_right
                  ((NonUnitalStarAlgHom.norm_apply_le ρ _).trans (StarAlgEquiv.norm_map _ _).le)
                  (norm_nonneg w)
            _ ≤ ε / (C + 1) * ‖w‖ := by gcongr
        · simp [Set.indicator_of_notMem hr]
    _ = ε / (C + 1) * C := by
        rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        ring
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- The regular coefficient representation induced by a nondegenerate representation `ρ` is
nondegenerate. -/
theorem isNondegenerate_regular_coefficient (hρ : ρ.IsNondegenerate) :
    (regular α ρ μ).coefficient.IsNondegenerate := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  set M := (Submodule.span ℂ (⋃ a, Set.range ((regular α ρ μ).coefficient a))).topologicalClosure
  have hM : IsClosed (M : Set (Lp H 2 μ)) := Submodule.isClosed_topologicalClosure _
  -- Vectors `r ↦ 𝟙_t(r) v` with `t` compact lie in `M`: first for `v = ρ(b) w`, then for all `v`
  -- by density of the span of the vectors `ρ(b) w`.
  have hcompact {t : Set G} (ht : MeasurableSet t) (htc : IsCompact t) (hμt : μ t ≠ ∞) (v : H) :
      indicatorConstLp 2 ht hμt v ∈ M := by
    let L : H →L[ℂ] Lp H 2 μ := LinearMap.mkContinuous
      { toFun := indicatorConstLp 2 ht hμt
        map_add' _ _ := indicatorConstLp_add.symm
        map_smul' := indicatorConstLp_smul ht hμt }
      (μ.real t ^ (1 / (2 : ℝ≥0∞).toReal))
      fun v => by simp [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, mul_comm]
    have hspan : Submodule.span ℂ (⋃ a, Set.range (ρ a)) ≤ M.comap (L : H →ₗ[ℂ] Lp H 2 μ) := by
      refine Submodule.span_le.2 fun _ hv => ?_
      obtain ⟨b, w, rfl⟩ := Set.mem_iUnion.1 hv
      have := (CStarAlgebra.increasingApproximateUnit A).neBot
      have hmem (e : A) :
          (regular α ρ μ).coefficient e (indicatorConstLp 2 ht hμt (ρ b w)) ∈ M :=
        Submodule.le_topologicalClosure _ <| Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, _, rfl⟩
      exact hM.mem_of_tendsto (tendsto_regular_coefficient_indicatorConstLp
        (CStarAlgebra.increasingApproximateUnit A) ht htc hμt b w) (.of_forall hmem)
    exact (hM.preimage L.continuous).closure_subset_iff.2 hspan
      (NonUnitalStarAlgHom.isNondegenerate_iff_dense.1 hρ v)
  -- Approximating a measurable set of finite measure from inside by compact sets, every
  -- `r ↦ 𝟙_s(r) v` lies in `M`, and these span a dense subspace of `L²(G, H)`.
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    eq_top_iff]
  refine fun f _ => Lp.induction ENNReal.ofNat_ne_top (· ∈ M) (fun v s hs hμs => ?_)
    (fun _ _ _ _ _ hf hg => M.add_mem hf hg) hM f
  choose K hKs hKc hKcl hK using fun n : ℕ =>
    hs.exists_isCompact_isClosed_sdiff_lt hμs.ne (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  have hμK (n : ℕ) : μ (K n) ≠ ∞ := ne_top_of_le_ne_top hμs.ne (measure_mono (hKs n))
  rw [Lp.simpleFunc.coe_indicatorConst]
  refine hM.mem_of_tendsto (tendsto_indicatorConstLp_set (l := atTop)
    (ht := fun n => (hKcl n).measurableSet) (hμt := hμK) ENNReal.ofNat_ne_top ?_)
    (.of_forall fun n => hcompact _ (hKc n) (hμK n) v)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) fun n => ?_
  rw [symmDiff_of_le (hKs n)]
  exact (hK n).le

/-- For a measure positive on nonempty open sets, such as a Haar measure, the regular coefficient
representation induced by `ρ` is nondegenerate exactly when `ρ` is. -/
@[simp]
theorem isNondegenerate_regular_coefficient_iff [μ.IsOpenPosMeasure] :
    (regular α ρ μ).coefficient.IsNondegenerate ↔ ρ.IsNondegenerate := by
  refine ⟨fun hπ => ?_, isNondegenerate_regular_coefficient⟩
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_forall_apply_eq_zero] at hπ ⊢
  -- If `ρ` kills `v`, then `π` kills `r ↦ 𝟙_U(r) v` for an open `U` of finite positive measure.
  intro v hv
  obtain ⟨U, hU, hUo, hμU⟩ := μ.exists_isOpen_measure_lt_top (1 : G)
  have hzero := hπ (indicatorConstLp 2 hUo.measurableSet hμU.ne v) fun a =>
    regular_coefficient_eq_iff.2 <| by
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hUo.measurableSet) (hμs := hμU.ne)
        (c := v), Lp.coeFn_zero H 2 μ] with r h₁ h₂
      rw [h₁, h₂]
      by_cases hr : r ∈ U <;> simp [hr, hv]
  have hpos : 0 < μ.real U :=
    ENNReal.toReal_pos (hUo.measure_pos μ ⟨1, hU⟩).ne' hμU.ne
  have := congrArg norm hzero
  rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_zero,
    mul_eq_zero] at this
  exact norm_eq_zero.1 <| this.resolve_right (by positivity)

end Nondegenerate

section Integrated

variable {α ρ μ}

/-- Matrix coefficients of the integrated regular representation: for `f ∈ C_c(G, A)` and
`ξ, η ∈ L²(G, H)`,
`⟪η, (π ⋊ λ)(f) ξ⟫ = ∫ s, ∫ r, ⟪η r, ρ (α_{r⁻¹}(f s)) (ξ (s⁻¹ r))⟫ dr ds`. -/
theorem inner_integratedOperator_regular_apply (f : C_c(G, A)) (η ξ : Lp H 2 μ) :
    ⟪η, (regular α ρ μ).integratedOperator μ f ξ⟫_ℂ =
      ∫ s, ∫ r, ⟪η r, ρ (α r⁻¹ (f s)) (ξ (s⁻¹ * r))⟫_ℂ ∂μ ∂μ := by
  rw [inner_integratedOperator_apply]
  congr 1 with s
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_regular_coefficient α ρ μ (f s) ((regular α ρ μ).group s ξ),
    μ.coeFn_leftRegular (𝕜 := ℂ) 2 s ξ] with r h₁ h₂
  rw [h₁, regular_group, h₂]

/-- On scalar test vectors `ξ r = φ r • v` and `η r = ψ r • w`, with `φ` continuous and `ψ`
continuous and compactly supported, the matrix coefficient of the integrated regular
representation is `∫ r, conj (ψ r) * ∫ s, φ (s⁻¹ r) * ⟪w, ρ (α_{r⁻¹}(f s)) v⟫ ds dr`. -/
private theorem inner_integratedOperator_regular_toLp_smul (f : C_c(G, A)) {φ ψ : G → ℂ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) {v w : H}
    (hξ : MemLp (fun r => φ r • v) 2 μ) (hη : MemLp (fun r => ψ r • w) 2 μ) :
    ⟪hη.toLp, (regular α ρ μ).integratedOperator μ f hξ.toLp⟫_ℂ =
      ∫ r, starRingEnd ℂ (ψ r) * ∫ s, φ (s⁻¹ * r) * ⟪w, ρ (α r⁻¹ (f s)) v⟫_ℂ ∂μ ∂μ := by
  -- The integrand on `G × G`, which vanishes unless `s ∈ tsupport f` and `r ∈ tsupport ψ`.
  set F : G → G → ℂ := fun s r =>
    starRingEnd ℂ (ψ r) * (φ (s⁻¹ * r) * ⟪w, ρ (α r⁻¹ (f s)) v⟫_ℂ)
  have hFc : Continuous (Function.uncurry F) := by
    simp only [F, Function.uncurry_def]
    fun_prop
  have hFs : HasCompactSupport (Function.uncurry F) :=
    (f.hasCompactSupport.prod hψs).closure_of_subset fun p hp =>
      ⟨subset_tsupport _ fun hf => hp (by simp [F, Function.uncurry_def, hf]),
        subset_tsupport _ fun hψ => hp (by simp [F, Function.uncurry_def, hψ])⟩
  calc ⟪hη.toLp, (regular α ρ μ).integratedOperator μ f hξ.toLp⟫_ℂ
      = ∫ s, ∫ r, F s r ∂μ ∂μ := by
        rw [inner_integratedOperator_regular_apply]
        congr 1 with s
        refine integral_congr_ae ?_
        filter_upwards [hη.coeFn_toLp, (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving
          |>.ae_eq_comp hξ.coeFn_toLp] with r h₁ h₂
        simp only [Function.comp_apply] at h₂
        simp only [F, h₁, h₂, inner_smul_left, inner_smul_right, map_smul]
        ring
    _ = ∫ r, ∫ s, F s r ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hFc hFs
    _ = _ := by simp only [F, integral_const_mul]

variable [μ.IsOpenPosMeasure]

/-- The integrated regular representation induced by a faithful representation `ρ` of `A` is
injective on `C_c(G, A)`, for a measure positive on nonempty open sets such as a Haar measure. -/
theorem injective_integratedOperator_regular (hρ : Function.Injective ρ) :
    Function.Injective ((regular α ρ μ).integratedOperator μ) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  -- A continuous compactly supported `h` with `∫ conj (h x) * h x = 0` vanishes.
  have eq_zero {h : G → ℂ} (hc : Continuous h) (hs : HasCompactSupport h)
      (h0 : ∫ x, starRingEnd ℂ (h x) * h x ∂μ = 0) (x : G) : h x = 0 := by
    by_contra hx
    have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ)
      (f := fun x => ‖h x‖ ^ 2) (by fun_prop)
      (hs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)) (fun _ => by positivity)
      (by simpa using hx)
    simp_rw [Complex.conj_mul'] at h0
    norm_cast at h0
    exact hpos.ne' h0
  -- It suffices that every matrix coefficient `k s = ⟪w, ρ (f s) v⟫` vanishes.
  suffices hk : ∀ v w : H, ∀ s, ⟪w, ρ (f s) v⟫_ℂ = 0 by
    ext s
    refine hρ ?_
    rw [CompactlySupportedContinuousMap.zero_apply, map_zero]
    exact ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => by simpa using hk v w s
  intro v w
  set k : G → ℂ := fun s => ⟪w, ρ (f s) v⟫_ℂ
  have hkc : Continuous k := by fun_prop
  have hks : HasCompactSupport k :=
    f.hasCompactSupport.mono fun s hs hzero => hs (by simp [k, hzero])
  -- Test the vector `ξ r = φ r • v`, with `φ x = conj (k x⁻¹)`, against `η r = g r • w`, where
  -- `g r = ∫ s, φ (s⁻¹ r) * ⟪w, ρ (α_{r⁻¹}(f s)) v⟫` is continuous and compactly supported.
  set φ : G → ℂ := fun x => starRingEnd ℂ (k x⁻¹)
  have hφc : Continuous φ := by fun_prop
  have hφs : HasCompactSupport φ :=
    (hks.comp_homeomorph (Homeomorph.inv G)).comp_left (g := starRingEnd ℂ) (map_zero _)
  set K : G → G → ℂ := fun r s => φ (s⁻¹ * r) * ⟪w, ρ (α r⁻¹ (f s)) v⟫_ℂ
  have hKs (r s : G) (h : K r s ≠ 0) : s ∈ tsupport f ∧ s⁻¹ * r ∈ tsupport φ :=
    ⟨subset_tsupport _ fun hf => h (by simp [K, hf]),
      subset_tsupport _ fun hφ => h (by simp [K, hφ])⟩
  set g : G → ℂ := fun r => ∫ s, K r s ∂μ
  have hgc : Continuous g :=
    continuous_integral_of_compact_support μ f.hasCompactSupport
      (by simp only [K, Function.uncurry_def]; fun_prop) fun r s h => (hKs r s h).1
  have hgs : HasCompactSupport g :=
    hasCompactSupport_integral_of_inv_mul_mem μ f.hasCompactSupport hφs hKs
  have hξ : MemLp (fun r => φ r • v) 2 μ :=
    (hφc.smul continuous_const).memLp_of_hasCompactSupport hφs.smul_right
  have hη : MemLp (fun r => g r • w) 2 μ :=
    (hgc.smul continuous_const).memLp_of_hasCompactSupport hgs.smul_right
  -- Since `(π ⋊ λ)(f) = 0`, this matrix coefficient `∫ conj (g r) * g r` vanishes, so `g = 0`.
  have hg0 := inner_integratedOperator_regular_toLp_smul (α := α) (ρ := ρ) f hφc hgc hgs hξ hη
  rw [hf, zero_apply, inner_zero_right] at hg0
  have hg1 := eq_zero hgc hgs hg0.symm 1
  -- At the identity, `g 1 = ∫ conj (k s) * k s`, so `k = 0`.
  refine eq_zero hkc hks ?_
  simpa [g, K, φ, k] using hg1

end Integrated

end CovariantRepresentation

end TauCeti.CStarAction
