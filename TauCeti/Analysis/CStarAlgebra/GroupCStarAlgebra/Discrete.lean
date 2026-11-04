/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.AlexandrovDiscrete
public import TauCeti.Analysis.CStarAlgebra.GroupCStarAlgebra.Full
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Full group C⋆-algebras of discrete groups

When a topological group `G : Type u` carries the discrete topology, `G` is automatically a locally
compact Hausdorff topological group, every compact subset of `G` is finite, and every left Haar
measure `μ` on `G` is a positive scalar multiple `μ.real {1}` of counting measure with trivial
modular character.

Normalizing point masses by `(μ.real {1})⁻¹` produces canonical generators
`GroupConvolutionAlgebra.single G μ g` in `GroupConvolutionAlgebra G μ` (with no `DecidableEq G`
assumption) satisfying

* `single G μ g * single G μ h = single G μ (g * h)`,
* `star (single G μ g) = single G μ g⁻¹`,
* `‖single G μ g‖ = 1` and `fullSeminorm G μ (single G μ g) = 1`,
* `hU.integratedStarAlgHom hcont μ (single G μ g) = U g` for every unitary representation `U`.

In particular `single G μ 1` is a multiplicative identity for `GroupConvolutionAlgebra G μ`, making
`GroupConvolutionAlgebra G μ` and `FullGroupConvolutionAlgebra G μ` unital normed `ℂ`-algebras and
upgrading the completion `FullGroupCStarAlgebra G μ` to a unital `CStarAlgebra` (and a
`CommCStarAlgebra` when `G` is abelian) whose underlying `NonUnitalCStarAlgebra` structure is
definitionally equal to the locally compact one from
`TauCeti.Analysis.CStarAlgebra.GroupCStarAlgebra.Full`.

Inside `FullGroupCStarAlgebra G μ`, the elements `of G μ (single G μ g)` assemble into the internal
unitary generator homomorphism

`FullGroupCStarAlgebra.unitaryOf G μ : G →* unitary (FullGroupCStarAlgebra G μ)`,

whose image in the multiplier algebra `𝓜(ℂ, FullGroupCStarAlgebra G μ)` coincides with
`FullGroupCStarAlgebra.groupMultiplier G μ`, whose `ℂ`-linear span is dense in
`FullGroupCStarAlgebra G μ`, and which induces an equivalence
`FullGroupCStarAlgebra.unitaryEquivStarAlgHom` between unitary group homomorphisms
`G →* unitary (H →L[ℂ] H)` and unital ⋆-representations
`FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)` for every Hilbert space `H : Type u`.

## Main definitions

* `TauCeti.GroupConvolutionAlgebra.single`: the normalized point mass `(μ.real {1})⁻¹ • 1_{g}` in
  `GroupConvolutionAlgebra G μ`.
* Unital `Ring`, `Algebra ℂ`, `NormedRing`, `NormOneClass` and `NormedAlgebra ℂ` instances on
  `GroupConvolutionAlgebra G μ` and `FullGroupConvolutionAlgebra G μ`, and `CStarAlgebra` (plus
  `CommCStarAlgebra` for abelian `G`) on `FullGroupCStarAlgebra G μ`.
* `TauCeti.FullGroupCStarAlgebra.ofStarAlgHom`: `FullGroupCStarAlgebra.of G μ` upgraded to a unital
  ⋆-algebra homomorphism.
* `TauCeti.FullGroupCStarAlgebra.unitaryOf`: the canonical unitary generator homomorphism
  `G →* unitary (FullGroupCStarAlgebra G μ)`.
* `TauCeti.FullGroupCStarAlgebra.liftUnitary` and
  `TauCeti.FullGroupCStarAlgebra.unitaryEquivStarAlgHom`: the unital universal property of
  `FullGroupCStarAlgebra G μ` for unitary representations on Hilbert spaces in `Type u`.

## Main statements

* `TauCeti.GroupConvolutionAlgebra.single_mul_single`,
  `TauCeti.GroupConvolutionAlgebra.star_single` and
  `TauCeti.GroupConvolutionAlgebra.fullSeminorm_single`: algebraic and C⋆-norm properties of the
  normalized point masses.
* `TauCeti.GroupConvolutionAlgebra.eq_sum_single`: every element of `GroupConvolutionAlgebra G μ` is
  a finite linear combination of point masses over its support.
* `TauCeti.FullGroupCStarAlgebra.coe_unitaryOf_toMultiplier`: the internal unitary generator
  `unitaryOf G μ g` maps to `groupMultiplier G μ g` in `𝓜(ℂ, FullGroupCStarAlgebra G μ)`.
* `TauCeti.FullGroupCStarAlgebra.dense_span_range_unitaryOf` and
  `TauCeti.FullGroupCStarAlgebra.starAlgHom_ext_unitaryOf`: the unitary generators span a dense
  ⋆-subalgebra and determine ⋆-homomorphisms out of `FullGroupCStarAlgebra G μ`.

## References

* Kenneth R. Davidson, *C*-Algebras by Example*, Chapter VII (full group C*-algebras of discrete
  groups).
* Jacques Dixmier, *C*-Algebras*, Section 13.9.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory UniformSpace Filter Topology Function
open scoped CompactlySupported CStarAlgebra MultiplierAlgebra NNReal ENNReal

namespace TauCeti

universe u

section DiscreteHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]

private theorem measure_singleton_eq_one (μ : Measure G) [μ.IsMulLeftInvariant] (g : G) :
    μ {g} = μ {1} := by
  have hpre : (fun x : G => g * x) ⁻¹' ({g} : Set G) = {1} := by
    ext x
    simp
  rw [← hpre, measure_preimage_mul]

private theorem measureReal_singleton_eq_one (μ : Measure G) [μ.IsMulLeftInvariant] (g : G) :
    μ.real {g} = μ.real {1} := by
  simp [Measure.real, measure_singleton_eq_one μ g]

omit [BorelSpace G] in
private theorem measureReal_singleton_pos (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    0 < μ.real {g} :=
  ENNReal.toReal_pos
    (IsOpen.measure_pos μ (isOpen_discrete ({g} : Set G)) (Set.singleton_nonempty g)).ne'
    isCompact_singleton.measure_lt_top.ne

private theorem integral_eq_measureReal_singleton_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure G) [μ.IsMulLeftInvariant]
    (g : G) {F : G → E} (hF : ∀ x ≠ g, F x = 0) :
    ∫ x, F x ∂μ = μ.real {1} • F g := by
  have hF_ind (x : G) : F x = Set.indicator ({g} : Set G) (fun _ => F g) x := by
    by_cases hx : x = g
    · subst hx
      simp
    · simp [hx, hF x hx]
  rw [integral_congr_ae (.of_forall hF_ind), integral_indicator_const _ (MeasurableSet.singleton g),
    measureReal_singleton_eq_one μ g]

private theorem modularCharacter_apply_eq_one (g : G) :
    (Measure.modularCharacter g : ℝ) = 1 := by
  let μ : Measure G := Measure.haar
  let f : G → ℝ := Set.indicator ({1} : Set G) (fun _ => 1)
  have hf : Continuous f := continuous_of_discreteTopology
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro isCompact_singleton fun _ hx => Set.indicator_of_notMem hx _
  have hint1 : ∫ x, f x ∂μ = μ.real {1} := by
    rw [integral_eq_measureReal_singleton_smul μ (1 : G) fun _ hx => Set.indicator_of_notMem hx _]
    simp
  have hintg : ∫ x, f (x * g) ∂μ = μ.real {1} := by
    rw [integral_eq_measureReal_singleton_smul μ g⁻¹ (F := fun x => f (x * g)) fun x hx => by
      have hxg : x * g ≠ 1 := fun h => hx (mul_eq_one_iff_eq_inv.1 h)
      exact Set.indicator_of_notMem hxg _]
    simp [f]
  have hpos : ∫ x, f x ∂μ ≠ 0 := by
    rw [hint1]
    exact (measureReal_singleton_pos μ 1).ne'
  rw [modularCharacter_eq_integral_div hf hfc hpos g, hintg, hint1, div_self]
  exact (measureReal_singleton_pos μ 1).ne'

end DiscreteHelpers

namespace GroupConvolutionAlgebra

section Single

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

variable (G μ) in
/-- The normalized point mass `(μ.real {1})⁻¹ • 1_{g}` at `g : G` in
`GroupConvolutionAlgebra G μ`. No `DecidableEq G` instance is needed. -/
def single (g : G) : GroupConvolutionAlgebra G μ :=
  toConv
    { toFun := Set.indicator ({g} : Set G) fun _ => ((μ.real {1})⁻¹ : ℂ)
      continuous_toFun := continuous_of_discreteTopology
      hasCompactSupport' :=
        HasCompactSupport.intro isCompact_singleton fun _ hx => Set.indicator_of_notMem hx _ }

omit [BorelSpace G] [μ.IsHaarMeasure] in
theorem ofConv_single_eq_indicator (g : G) :
    ⇑(single G μ g).ofConv = Set.indicator ({g} : Set G) fun _ => ((μ.real {1})⁻¹ : ℂ) :=
  (rfl)

omit [BorelSpace G] [μ.IsHaarMeasure] in
@[simp]
theorem ofConv_single_self (g : G) :
    (single G μ g).ofConv g = ((μ.real {1})⁻¹ : ℂ) := by
  simp [ofConv_single_eq_indicator]

omit [BorelSpace G] [μ.IsHaarMeasure] in
theorem ofConv_single_of_ne {g s : G} (h : s ≠ g) :
    (single G μ g).ofConv s = 0 := by
  simp [ofConv_single_eq_indicator, h]

/-- Left convolution by `single G μ g` is left translation by `g`. -/
@[simp]
theorem single_mul (g : G) (f : GroupConvolutionAlgebra G μ) :
    single G μ g * f = translateLIE g f := by
  apply ext; ext s
  rw [ofConv_mul_apply, ofConv_translateLIE_apply,
    integral_eq_measureReal_singleton_smul μ g fun r hr => by simp [ofConv_single_of_ne hr]]
  have hpos : (μ.real {1} : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (measureReal_singleton_pos μ 1).ne'
  rw [ofConv_single_self, Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hpos, one_mul]

/-- Right convolution by `single G μ g` translates the argument on the right by `g⁻¹`. -/
theorem ofConv_mul_single_apply (f : GroupConvolutionAlgebra G μ) (g s : G) :
    (f * single G μ g).ofConv s = f.ofConv (s * g⁻¹) := by
  rw [ofConv_mul_apply,
    integral_eq_measureReal_singleton_smul μ (s * g⁻¹) fun r hr => by
      have hrg : r⁻¹ * s ≠ g := fun h => hr (by rw [← h]; group)
      simp [ofConv_single_of_ne hrg]]
  have hpos : (μ.real {1} : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (measureReal_singleton_pos μ 1).ne'
  have hsg : (s * g⁻¹)⁻¹ * s = g := by simp
  rw [hsg, ofConv_single_self, Complex.real_smul]
  calc (μ.real {1} : ℂ) * (f.ofConv (s * g⁻¹) * (μ.real {1} : ℂ)⁻¹)
      = ((μ.real {1} : ℂ) * (μ.real {1} : ℂ)⁻¹) * f.ofConv (s * g⁻¹) := by ring
    _ = f.ofConv (s * g⁻¹) := by rw [mul_inv_cancel₀ hpos, one_mul]

@[simp]
theorem mul_single_one (f : GroupConvolutionAlgebra G μ) :
    f * single G μ 1 = f := by
  apply ext; ext s
  rw [ofConv_mul_single_apply, inv_one, mul_one]

/-- Normalized point masses multiply according to the group law. -/
theorem single_mul_single (g h : G) :
    single G μ g * single G μ h = single G μ (g * h) := by
  rw [single_mul]
  apply ext; ext s
  rw [ofConv_translateLIE_apply]
  by_cases hs : s = g * h
  · subst hs
    simp
  · have hgh : g⁻¹ * s ≠ h := fun heq => hs (by rw [← heq, mul_inv_cancel_left])
    rw [ofConv_single_of_ne hgh, ofConv_single_of_ne hs]

omit [μ.IsHaarMeasure] in
/-- The involution sends `single G μ g` to `single G μ g⁻¹`. -/
@[simp]
theorem star_single (g : G) :
    star (single G μ g) = single G μ g⁻¹ := by
  apply ext; ext s
  rw [ofConv_star_apply, modularCharacter_apply_eq_one, one_smul]
  by_cases hs : s = g⁻¹
  · subst hs
    simp [Complex.conj_ofReal]
  · have hsinv : s⁻¹ ≠ g := fun heq => hs (inv_eq_iff_eq_inv.1 heq)
    rw [ofConv_single_of_ne hsinv, star_zero, ofConv_single_of_ne hs]

@[simp]
theorem translateLIE_single (r g : G) :
    translateLIE r (single G μ g) = single G μ (r * g) := by
  rw [← single_mul, single_mul_single]

/-- Every normalized point mass has `L¹(μ)` norm equal to `1`. -/
@[simp]
theorem norm_single (g : G) : ‖single G μ g‖ = 1 := by
  rw [norm_eq_integral_norm,
    integral_eq_measureReal_singleton_smul μ g fun s hs => by simp [ofConv_single_of_ne hs]]
  have hpos : 0 < μ.real {1} := measureReal_singleton_pos μ 1
  simp [ofConv_single_self, abs_of_pos hpos, mul_inv_cancel₀ hpos.ne']

omit [BorelSpace G] [μ.IsHaarMeasure] in
/-- Every element of `GroupConvolutionAlgebra G μ` on a discrete group has finite support. -/
theorem finite_support_ofConv (f : GroupConvolutionAlgebra G μ) :
    (support f.ofConv).Finite :=
  (f.ofConv.hasCompactSupport.finite
    (isDiscrete_iff_discreteTopology.2 inferInstance)).subset (subset_tsupport _)

private theorem ofConv_sum {ι : Type*} (s : Finset ι) (F : ι → GroupConvolutionAlgebra G μ)
    (x : G) :
    (∑ i ∈ s, F i).ofConv x = ∑ i ∈ s, (F i).ofConv x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/-- Every element of `GroupConvolutionAlgebra G μ` is a finite linear combination of normalized
point masses over its support. -/
theorem eq_sum_single (f : GroupConvolutionAlgebra G μ) :
    f = ∑ g ∈ (finite_support_ofConv f).toFinset,
      ((μ.real {1} : ℂ) * f.ofConv g) • single G μ g := by
  apply ext; ext s
  rw [ofConv_sum]
  by_cases hs : s ∈ (finite_support_ofConv f).toFinset
  · rw [Finset.sum_eq_single s]
    · have hpos : (μ.real {1} : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (measureReal_singleton_pos μ 1).ne'
      simp only [ofConv_smul, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
        ofConv_single_self, smul_eq_mul]
      rw [mul_right_comm, mul_inv_cancel₀ hpos, one_mul]
    · intro g _ hgs
      simp [ofConv_single_of_ne hgs.symm]
    · intro hs'
      exact absurd hs hs'
  · rw [Finset.sum_eq_zero]
    · have hnot : s ∉ support f.ofConv := fun h => hs ((Set.Finite.mem_toFinset _).2 h)
      exact Function.notMem_support.1 hnot
    · intro g hg
      have hsg : s ≠ g := fun h => hs (h ▸ hg)
      simp [ofConv_single_of_ne hsg]

/-- The normalized point masses span `GroupConvolutionAlgebra G μ` over `ℂ`. -/
theorem mem_span_range_single (f : GroupConvolutionAlgebra G μ) :
    f ∈ Submodule.span ℂ (Set.range (single G μ)) := by
  rw [eq_sum_single f]
  exact Submodule.sum_mem _ fun g _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end Single

end GroupConvolutionAlgebra

end TauCeti

/-! ### Integrated representations on point masses -/

namespace ContRepresentation.IsUnitary

open TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Integrating a unitary representation against the normalized point mass `single G μ g` returns
the group operator `U g`. -/
theorem integratedStarAlgHom_single {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun x => U x v) (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    hU.integratedStarAlgHom hcont μ (GroupConvolutionAlgebra.single G μ g) = U g := by
  ext v
  rw [integratedStarAlgHom_apply, integratedOperator_apply,
    TauCeti.integral_eq_measureReal_singleton_smul μ g fun s hs => by
      simp [GroupConvolutionAlgebra.ofConv_single_of_ne hs]]
  have hpos : (μ.real {1} : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (TauCeti.measureReal_singleton_pos μ 1).ne'
  rw [GroupConvolutionAlgebra.ofConv_single_self, ← Complex.coe_smul, smul_smul,
    mul_inv_cancel₀ hpos, one_smul]

end ContRepresentation.IsUnitary

namespace TauCeti

universe u

section UnitalInstances

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

namespace GroupConvolutionAlgebra

/-- Every normalized point mass has universal C⋆-norm equal to `1`. -/
@[simp]
theorem fullSeminorm_single (g : G) : fullSeminorm G μ (single G μ g) = 1 := by
  refine le_antisymm ((fullSeminorm_le_norm _).trans_eq (norm_single g)) ?_
  have hU := μ.isUnitary_leftRegular (𝕜 := ℂ) (E := ℂ)
  have hcont : ∀ v : Lp ℂ 2 μ, Continuous fun x => μ.leftRegular ℂ ℂ 2 x v :=
    fun _ => continuous_of_discreteTopology
  let ξ : Lp ℂ 2 μ :=
    indicatorConstLp 2 (MeasurableSet.singleton (1 : G))
      isCompact_singleton.measure_lt_top.ne (1 : ℂ)
  have hξ : ξ ≠ 0 := by
    rw [← norm_pos_iff, norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    exact Real.rpow_pos_of_pos (measureReal_singleton_pos μ 1) _
  have : Nontrivial (Lp ℂ 2 μ) := ⟨⟨ξ, 0, hξ⟩⟩
  have hnorm : ‖μ.leftRegular ℂ ℂ 2 g‖ = 1 :=
    CStarRing.norm_coe_unitary ⟨μ.leftRegular ℂ ℂ 2 g, hU.mem_unitary g⟩
  calc (1 : ℝ) = ‖μ.leftRegular ℂ ℂ 2 g‖ := hnorm.symm
    _ = ‖hU.integratedStarAlgHom hcont μ (single G μ g)‖ := by rw [hU.integratedStarAlgHom_single]
    _ ≤ fullSeminorm G μ (single G μ g) :=
        norm_integratedStarAlgHom_le_fullSeminorm hU hcont (single G μ g)

/-- Haar-measure rescaling sends `single G μ g` to `single G ν g`. -/
@[simp]
theorem haarMeasureEquiv_single (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] (g : G) :
    haarMeasureEquiv G μ ν (single G μ g) = single G ν g :=
  FullGroupCStarAlgebra.of_injective <|
    FullGroupCStarAlgebra.of_eq_of_iff.2 fun _ _ _ _ _ hU hcont => by
      rw [hU.integratedStarAlgHom_haarMeasureEquiv, hU.integratedStarAlgHom_single,
        hU.integratedStarAlgHom_single]

instance : One (GroupConvolutionAlgebra G μ) :=
  ⟨single G μ 1⟩

omit [BorelSpace G] [μ.IsHaarMeasure] in
theorem one_def : (1 : GroupConvolutionAlgebra G μ) = single G μ 1 :=
  (rfl)

omit [BorelSpace G] [μ.IsHaarMeasure] in
@[simp]
theorem ofConv_one_self : (1 : GroupConvolutionAlgebra G μ).ofConv 1 = ((μ.real {1})⁻¹ : ℂ) :=
  ofConv_single_self 1

omit [BorelSpace G] [μ.IsHaarMeasure] in
theorem ofConv_one_of_ne {s : G} (hs : s ≠ 1) : (1 : GroupConvolutionAlgebra G μ).ofConv s = 0 :=
  ofConv_single_of_ne hs

instance : Ring (GroupConvolutionAlgebra G μ) where
  __ : NonUnitalRing (GroupConvolutionAlgebra G μ) := inferInstance
  __ : One (GroupConvolutionAlgebra G μ) := inferInstance
  one_mul f := by
    rw [one_def, single_mul, translateLIE_one]
    rfl
  mul_one := mul_single_one

instance : NormOneClass (GroupConvolutionAlgebra G μ) where
  norm_one := norm_single 1

instance : NormedRing (GroupConvolutionAlgebra G μ) where
  __ : NonUnitalNormedRing (GroupConvolutionAlgebra G μ) := inferInstance
  __ : Ring (GroupConvolutionAlgebra G μ) := inferInstance

instance : Algebra ℂ (GroupConvolutionAlgebra G μ) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

@[simp]
theorem algebraMap_apply (z : ℂ) :
    algebraMap ℂ (GroupConvolutionAlgebra G μ) z = z • single G μ 1 :=
  Algebra.algebraMap_eq_smul_one z

instance : NormedAlgebra ℂ (GroupConvolutionAlgebra G μ) where
  norm_smul_le := norm_smul_le

end GroupConvolutionAlgebra

namespace FullGroupConvolutionAlgebra

instance : One (FullGroupConvolutionAlgebra G μ) :=
  ⟨toFull 1⟩

omit [BorelSpace G] [μ.IsHaarMeasure] in
@[simp]
theorem toFull_one : toFull (1 : GroupConvolutionAlgebra G μ) = 1 :=
  (rfl)

omit [BorelSpace G] [μ.IsHaarMeasure] in
@[simp]
theorem ofFull_one : ofFull (1 : FullGroupConvolutionAlgebra G μ) = 1 :=
  ofFull_toFull 1

instance : Ring (FullGroupConvolutionAlgebra G μ) where
  __ : NonUnitalRing (FullGroupConvolutionAlgebra G μ) := inferInstance
  __ : One (FullGroupConvolutionAlgebra G μ) := inferInstance
  one_mul f := by rw [← toFull_ofFull f, ← toFull_one, ← toFull_mul, one_mul]
  mul_one f := by rw [← toFull_ofFull f, ← toFull_one, ← toFull_mul, mul_one]

instance : Algebra ℂ (FullGroupConvolutionAlgebra G μ) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance : NormedRing (FullGroupConvolutionAlgebra G μ) where
  __ : NonUnitalNormedRing (FullGroupConvolutionAlgebra G μ) := inferInstance
  __ : Ring (FullGroupConvolutionAlgebra G μ) := inferInstance

instance : NormOneClass (FullGroupConvolutionAlgebra G μ) where
  norm_one := by
    rw [norm_def, ofFull_one, GroupConvolutionAlgebra.one_def]
    exact GroupConvolutionAlgebra.fullSeminorm_single 1

instance : NormedAlgebra ℂ (FullGroupConvolutionAlgebra G μ) where
  norm_smul_le := norm_smul_le

end FullGroupConvolutionAlgebra

namespace FullGroupCStarAlgebra

open GroupConvolutionAlgebra FullGroupConvolutionAlgebra

instance : NormedAlgebra ℂ (Completion (FullGroupConvolutionAlgebra G μ)) where
  norm_smul_le := norm_smul_le

instance : CStarAlgebra (Completion (FullGroupConvolutionAlgebra G μ)) where
  __ : NonUnitalCStarAlgebra (Completion (FullGroupConvolutionAlgebra G μ)) := inferInstance
  __ : NormedRing (Completion (FullGroupConvolutionAlgebra G μ)) := inferInstance
  __ : NormedAlgebra ℂ (Completion (FullGroupConvolutionAlgebra G μ)) := inferInstance

/-- For a discrete group `G`, the full group C⋆-algebra `FullGroupCStarAlgebra G μ` is a unital
C⋆-algebra whose underlying `NonUnitalCStarAlgebra` structure is definitionally equal to the
general locally compact one. -/
instance : CStarAlgebra (FullGroupCStarAlgebra G μ) :=
  inferInstanceAs (CStarAlgebra (Completion (FullGroupConvolutionAlgebra G μ)))

instance : NormOneClass (FullGroupCStarAlgebra G μ) :=
  inferInstanceAs (NormOneClass (Completion (FullGroupConvolutionAlgebra G μ)))

-- Compile-time check that the unital `CStarAlgebra` instance creates no diamond with the
-- `NonUnitalCStarAlgebra` instance from `Full.lean`.
example :
    CStarAlgebra.toNonUnitalCStarAlgebra (FullGroupCStarAlgebra G μ) =
      (inferInstance : NonUnitalCStarAlgebra (FullGroupCStarAlgebra G μ)) :=
  rfl

@[simp]
theorem of_one : of G μ 1 = 1 := by
  rw [← coe_toFull_eq_of, toFull_one]
  exact Completion.coe_one _

@[simp]
theorem of_single_one : of G μ (single G μ 1) = 1 :=
  of_one

variable (G μ) in
/-- `FullGroupCStarAlgebra.of G μ` upgraded to a unital ⋆-algebra homomorphism on a discrete
group. -/
def ofStarAlgHom : GroupConvolutionAlgebra G μ →⋆ₐ[ℂ] FullGroupCStarAlgebra G μ where
  toFun := of G μ
  map_one' := of_one
  map_mul' := map_mul (of G μ)
  map_zero' := map_zero (of G μ)
  map_add' := map_add (of G μ)
  map_star' := map_star (of G μ)
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, of_one]

@[simp]
theorem coe_ofStarAlgHom : ⇑(ofStarAlgHom G μ) = of G μ :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_ofStarAlgHom :
    (ofStarAlgHom G μ).toNonUnitalStarAlgHom = of G μ :=
  (rfl)

private theorem of_single_mem_unitary (g : G) :
    of G μ (single G μ g) ∈ unitary (FullGroupCStarAlgebra G μ) := by
  rw [Unitary.mem_iff]
  constructor
  · rw [← map_star, ← map_mul, star_single, single_mul_single, inv_mul_cancel, of_single_one]
  · rw [← map_star, ← map_mul, star_single, single_mul_single, mul_inv_cancel, of_single_one]

variable (G μ) in
/-- The canonical unitary generator homomorphism `g ↦ of G μ (single G μ g)` from a discrete group
`G` into `unitary (FullGroupCStarAlgebra G μ)`. -/
def unitaryOf : G →* unitary (FullGroupCStarAlgebra G μ) where
  toFun g := ⟨of G μ (single G μ g), of_single_mem_unitary g⟩
  map_one' := Subtype.ext of_single_one
  map_mul' g h := Subtype.ext <| by rw [Submonoid.coe_mul, ← map_mul, single_mul_single]

theorem coe_unitaryOf (g : G) :
    (unitaryOf G μ g : FullGroupCStarAlgebra G μ) = of G μ (single G μ g) :=
  (rfl)

@[simp]
theorem norm_unitaryOf (g : G) :
    ‖(unitaryOf G μ g : FullGroupCStarAlgebra G μ)‖ = 1 := by
  rw [coe_unitaryOf, norm_of, fullSeminorm_single]

@[simp]
theorem star_coe_unitaryOf (g : G) :
    star (unitaryOf G μ g : FullGroupCStarAlgebra G μ) =
      (unitaryOf G μ g⁻¹ : FullGroupCStarAlgebra G μ) := by
  rw [coe_unitaryOf, ← map_star, star_single, coe_unitaryOf]

/-- Under the canonical inclusion `FullGroupCStarAlgebra G μ → 𝓜(ℂ, FullGroupCStarAlgebra G μ)`,
the internal unitary generator `unitaryOf G μ g` coincides with `groupMultiplier G μ g`. -/
@[simp]
theorem coe_unitaryOf_toMultiplier (g : G) :
    ((unitaryOf G μ g : FullGroupCStarAlgebra G μ) : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) =
      (groupMultiplier G μ g : 𝓜(ℂ, FullGroupCStarAlgebra G μ)) := by
  refine DoubleCentralizer.ext_fst fun x => ?_
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    rw [DoubleCentralizer.coe_fst, ContinuousLinearMap.mul_apply', coe_unitaryOf, ← map_mul,
      single_mul, groupMultiplier_fst_of]

/-- Haar-measure rescaling intertwines `unitaryOf G μ` and `unitaryOf G ν`. -/
@[simp]
theorem haarMeasureEquiv_unitaryOf (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] (g : G) :
    haarMeasureEquiv G μ ν (unitaryOf G μ g : FullGroupCStarAlgebra G μ) =
      (unitaryOf G ν g : FullGroupCStarAlgebra G ν) := by
  rw [coe_unitaryOf, haarMeasureEquiv_of, haarMeasureEquiv_single, coe_unitaryOf]

@[simp]
theorem haarMeasureEquiv_one (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    haarMeasureEquiv G μ ν 1 = 1 := by
  simp

/-- The `ℂ`-linear span of the unitary generators `unitaryOf G μ g` is dense in
`FullGroupCStarAlgebra G μ`. -/
theorem dense_span_range_unitaryOf :
    Dense (Submodule.span ℂ
      (Set.range fun g : G => (unitaryOf G μ g : FullGroupCStarAlgebra G μ)) :
        Set (FullGroupCStarAlgebra G μ)) := by
  refine denseRange_of.mono ?_
  rintro _ ⟨f, rfl⟩
  rw [eq_sum_single f, map_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/-- Nonunital ⋆-homomorphisms out of `FullGroupCStarAlgebra G μ` into a C⋆-algebra are determined
by their values on the unitary generators `unitaryOf G μ g`. -/
theorem nonUnitalStarAlgHom_ext_unitaryOf {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : FullGroupCStarAlgebra G μ →⋆ₙₐ[ℂ] B}
    (h : ∀ g, φ (unitaryOf G μ g) = ψ (unitaryOf G μ g)) : φ = ψ := by
  apply starAlgHom_ext
  ext f
  rw [eq_sum_single f]
  simp only [NonUnitalStarAlgHom.comp_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun g _ => congrArg (_ • ·) (h g)

/-- Unital ⋆-homomorphisms out of `FullGroupCStarAlgebra G μ` into a unital C⋆-algebra are
determined by their values on the unitary generators `unitaryOf G μ g`. -/
theorem starAlgHom_ext_unitaryOf {B : Type*} [CStarAlgebra B]
    {φ ψ : FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] B}
    (h : ∀ g, φ (unitaryOf G μ g) = ψ (unitaryOf G μ g)) : φ = ψ := by
  have hnu : φ.toNonUnitalStarAlgHom = ψ.toNonUnitalStarAlgHom :=
    nonUnitalStarAlgHom_ext_unitaryOf h
  ext x
  exact congr($hnu x)

end FullGroupCStarAlgebra

end UnitalInstances

end TauCeti

/-! ### Unital universal property for Hilbert-space unitary representations -/

namespace ContRepresentation.IsUnitary

universe u

open TauCeti TauCeti.FullGroupCStarAlgebra

variable {G H : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On a discrete group, the extended integrated representation evaluates at `unitaryOf G μ g` to
`U g`. -/
@[simp]
theorem integratedGroupCStar_unitaryOf {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun x => U x v) (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    hU.integratedGroupCStar hcont μ (unitaryOf G μ g) = U g := by
  rw [coe_unitaryOf, hU.integratedGroupCStar_of, hU.integratedStarAlgHom_single]

@[simp]
theorem integratedGroupCStar_one {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun x => U x v) (μ : Measure G) [μ.IsHaarMeasure] :
    hU.integratedGroupCStar hcont μ 1 = 1 := by
  rw [← Submonoid.coe_one (unitary (FullGroupCStarAlgebra G μ)), ← map_one (unitaryOf G μ),
    hU.integratedGroupCStar_unitaryOf, map_one]

end ContRepresentation.IsUnitary

namespace TauCeti

universe u

namespace FullGroupCStarAlgebra

section UnitaryUniversal

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def contRepOfUnitaryHom (u : G →* unitary (H →L[ℂ] H)) : ContRepresentation ℂ G H where
  toMonoidHom :=
    { toFun g := (u g : H →L[ℂ] H)
      map_one' := by simp
      map_mul' g h := by simp }

omit [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem isUnitary_contRepOfUnitaryHom (u : G →* unitary (H →L[ℂ] H)) :
    (contRepOfUnitaryHom u).IsUnitary :=
  (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun g => (u g).2

variable (G μ) in
/-- Extend a homomorphism `u : G →* unitary (H →L[ℂ] H)` on a discrete group `G` (`H : Type u`) to
a unital ⋆-homomorphism `FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)`. -/
def liftUnitary (u : G →* unitary (H →L[ℂ] H)) :
    FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  let φ := (isUnitary_contRepOfUnitaryHom u).integratedGroupCStar
    (fun _ => continuous_of_discreteTopology) μ
  { toFun := φ
    map_one' := (isUnitary_contRepOfUnitaryHom u).integratedGroupCStar_one _ μ
    map_mul' := map_mul φ
    map_zero' := map_zero φ
    map_add' := map_add φ
    map_star' := map_star φ
    commutes' z := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul,
        (isUnitary_contRepOfUnitaryHom u).integratedGroupCStar_one _ μ] }

@[simp]
theorem liftUnitary_unitaryOf (u : G →* unitary (H →L[ℂ] H)) (g : G) :
    liftUnitary G μ u (unitaryOf G μ g) = (u g : H →L[ℂ] H) :=
  (isUnitary_contRepOfUnitaryHom u).integratedGroupCStar_unitaryOf _ μ g

variable (G μ) in
/-- Restrict a unital ⋆-representation `π : FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)` along
`unitaryOf G μ` to a unitary group homomorphism `G →* unitary (H →L[ℂ] H)`. -/
def restrictUnitary (π : FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    G →* unitary (H →L[ℂ] H) where
  toFun g :=
    ⟨π (unitaryOf G μ g), by
      rw [Unitary.mem_iff]
      have hg := Unitary.mem_iff.1 (unitaryOf G μ g).2
      exact ⟨by rw [← map_star, ← map_mul, hg.1, map_one],
        by rw [← map_star, ← map_mul, hg.2, map_one]⟩⟩
  map_one' := Subtype.ext <| by simp
  map_mul' g h := Subtype.ext <| by simp [map_mul]

@[simp]
theorem coe_restrictUnitary_apply (π : FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)) (g : G) :
    (restrictUnitary G μ π g : H →L[ℂ] H) = π (unitaryOf G μ g) :=
  (rfl)

@[simp]
theorem restrictUnitary_liftUnitary (u : G →* unitary (H →L[ℂ] H)) :
    restrictUnitary G μ (liftUnitary G μ u) = u := by
  ext g : 1
  exact Subtype.ext (liftUnitary_unitaryOf u g)

@[simp]
theorem liftUnitary_restrictUnitary (π : FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    liftUnitary G μ (restrictUnitary G μ π) = π :=
  starAlgHom_ext_unitaryOf fun g => liftUnitary_unitaryOf (restrictUnitary G μ π) g

variable (G μ H) in
/-- For a discrete group `G : Type u` and a Hilbert space `H : Type u`, unitary group homomorphisms
`G →* unitary (H →L[ℂ] H)` correspond bijectively to unital ⋆-representations
`FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)` via `unitaryOf G μ`. -/
def unitaryEquivStarAlgHom :
    (G →* unitary (H →L[ℂ] H)) ≃ (FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)) where
  toFun := liftUnitary G μ
  invFun := restrictUnitary G μ
  left_inv := restrictUnitary_liftUnitary
  right_inv := liftUnitary_restrictUnitary

@[simp]
theorem unitaryEquivStarAlgHom_apply (u : G →* unitary (H →L[ℂ] H)) :
    unitaryEquivStarAlgHom G μ H u = liftUnitary G μ u :=
  (rfl)

@[simp]
theorem unitaryEquivStarAlgHom_symm_apply (π : FullGroupCStarAlgebra G μ →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (unitaryEquivStarAlgHom G μ H).symm π = restrictUnitary G μ π :=
  (rfl)

end UnitaryUniversal

end FullGroupCStarAlgebra

section CommGroup

namespace FullGroupCStarAlgebra

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

/-- For a discrete abelian group `G`, the full group C⋆-algebra `FullGroupCStarAlgebra G μ` is a
unital commutative C⋆-algebra. -/
instance : CommCStarAlgebra (FullGroupCStarAlgebra G μ) where
  mul_comm := mul_comm

end FullGroupCStarAlgebra

end CommGroup

end TauCeti

end
