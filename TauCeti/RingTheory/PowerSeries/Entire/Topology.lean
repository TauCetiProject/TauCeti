/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Eval
public import TauCeti.RingTheory.PowerSeries.GaussFamily
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# The Gauss topology on entire series

For an ultrametric normed ring `R`, the algebra of entire power series carries the topology of
the Gauss norms at all positive radii. Convergence is convergence in each of these norms, rather
than convergence of individual coefficients. The resulting uniform ring is Hausdorff, has a
countably generated uniformity (hence is metrizable), and is complete when `R` is complete.
Polynomial truncations converge in this topology, and each coefficient is a uniformly continuous
function of the series.

Restriction embeds the algebra into the product of the closed-disc algebras of all positive
radii. Its image consists of the families with the same formal coefficients at every radius.
Along any monotone family indexed by a nonempty directed preorder (in particular, any monotone
sequence) of positive radii tending to infinity, the entire-series algebra is isomorphic as a ring
and as a uniform space to the closed subring of compatible restricted series, and both the induced
Gauss uniformity (along any cofinal family or sequence tending to infinity) and this
compatible-series description are independent of the chosen family. Over a nontrivial
ultrametric normed ring with a unit of norm `< 1` (in particular, over any nontrivially normed
ultrametric field), no zero-neighborhood is bounded and no single ring seminorm, scalar-bounded
additive group seminorm, or normable space structure represents this topology. These are
specializations of the Gauss topology of a family of radii in
`TauCeti.RingTheory.PowerSeries.GaussFamily`.

Evaluation of entire series at a point `b` of a complete normed algebra, which needs no
ultrametric hypothesis on the algebra, is continuous for this topology: its value is bounded by a
constant multiple of the Gauss norm at the radius `2 ‖b‖ + 1`
(`PowerSeries.norm_evalAt_le_mul_gaussNorm`).

Because `PowerSeries.IsEntire.subring R` is a complete nonarchimedean ring whose restrictions to
each closed disc are ultrametric normed rings, convergent infinite products are preserved by
restriction, evaluation, constant coefficients, and strict Gauss-norm perturbation bounds near `1`,
and any family tending to `1` along the cofinite filter is unconditionally multipliable in
`PowerSeries.IsEntire.subring R` even when its factors are not units.

## Main definitions

* `TauCeti.PowerSeries.IsEntire.restrict`, `TauCeti.PowerSeries.IsEntire.restrictFamily`, and
  `TauCeti.PowerSeries.IsEntire.restrictSubfamily`: closed-disc restriction to a single positive
  radius, to all positive radii at once, and along a subfamily.
* `TauCeti.PowerSeries.IsEntire.uniformSpace`: the Gauss uniformity on
  `PowerSeries.IsEntire.subring R`.
* `TauCeti.PowerSeries.IsEntire.natRadiusSeq`: the canonical strictly increasing sequence of
  radii `n + 1` tending to infinity.
* `TauCeti.PowerSeries.IsEntire.compatibleRingEquiv` and
  `TauCeti.PowerSeries.IsEntire.compatibleUniformEquiv`: ring and uniform equivalences with the
  subring of compatible restricted series along any monotone family (indexed by a nonempty directed
  preorder) of positive radii tending to infinity.

## Main results

* `TauCeti.PowerSeries.IsEntire.tendsto_iff`,
  `TauCeti.PowerSeries.IsEntire.tendsto_iff_of_cofinal_radius`, and
  `TauCeti.PowerSeries.IsEntire.tendsto_iff_of_tendsto_atTop`: convergence of entire series, tested
  at all positive radii, along any unbounded family, or along any family tending to infinity.
* `TauCeti.PowerSeries.IsEntire.tendsto_polynomialHom_trunc`,
  `TauCeti.PowerSeries.IsEntire.denseRange_polynomialHom`, and
  `TauCeti.PowerSeries.IsEntire.uniformContinuous_coeff`: polynomial truncation convergence,
  density of polynomials, and uniform continuity of coefficients.
* `TauCeti.PowerSeries.IsEntire.range_restrictFamily`,
  `TauCeti.PowerSeries.IsEntire.range_restrictSubfamily_of_cofinal_radius`,
  `TauCeti.PowerSeries.IsEntire.comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius`, and
  `TauCeti.PowerSeries.IsEntire.comap_restrictSubfamily_eq_of_cofinal_radius`: the restriction
  image and sequence-independent induction of the entire Gauss uniformity.
* `TauCeti.PowerSeries.IsEntire.compatibleRingEquiv_symm_eq_iff`: independence of the monotone
  family (indexed by a nonempty directed preorder) in the compatible-series description.
* `TauCeti.PowerSeries.IsEntire.not_isBounded_of_mem_nhds_zero`,
  `TauCeti.PowerSeries.IsEntire.not_exists_ringSeminorm_toTopologicalSpace_eq`,
  `IsEntire.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_polynomialHom_C_mul_le`,
  `IsEntire.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le`, and
  `TauCeti.PowerSeries.IsEntire.not_isNormableSpace`: no zero-neighborhood is bounded and no
  compatible ring seminorm, scalar-bounded additive group seminorm, or normable space structure
  represents the entire Gauss topology over a nontrivial ultrametric normed ring with a unit of
  norm `< 1` (in particular, over a nontrivially normed ultrametric field).
* `TauCeti.PowerSeries.IsEntire.continuous_evalAtHom`: evaluation is continuous.
* `TauCeti.PowerSeries.IsEntire.hasProd_iff`,
  `TauCeti.PowerSeries.IsEntire.multipliable_iff`,
  `TauCeti.PowerSeries.IsEntire.restrict_tprod` and
  `TauCeti.PowerSeries.IsEntire.constantCoeff_tprod`: unconditional infinite products of entire
  series.
* `TauCeti.PowerSeries.IsEntire.evalAt_hasProd` and
  `TauCeti.PowerSeries.IsEntire.gaussNorm_sub_one_lt_of_hasProd`: preservation of convergent
  infinite products of entire series under evaluation and strict Gauss-norm bounds near `1`.
* `TauCeti.PowerSeries.IsEntire.summable_prod_of_tendsto_cofinite_zero`,
  `TauCeti.PowerSeries.IsEntire.multipliable_one_add_of_tendsto_cofinite_zero` and
  `TauCeti.PowerSeries.IsEntire.multipliable_of_tendsto_cofinite_one`: unconditional convergence
  of infinite products in `PowerSeries.IsEntire.subring R` over complete coefficients.
* Instances: `IsUniformAddGroup`, `IsTopologicalRing`, `NonarchimedeanRing`, `ContinuousSMul`,
  `T2Space`, `Filter.IsCountablyGenerated` on `𝓤 (IsEntire.subring R)` (hence `MetrizableSpace`),
  and over complete coefficients `CompleteSpace` on `PowerSeries.IsEntire.subring R`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A.
-/

public section

open Filter PowerSeries
open scoped Topology Uniformity

namespace TauCeti.PowerSeries.IsEntire

-- Supply the positivity witness used by the Gauss-norm instances on each closed disc.
local instance radius_pos (r : Set.Ioi (0 : ℝ)) : Fact (0 < (r : ℝ)) := ⟨r.property⟩

section Radii

/-- Any family of positive radii tending to infinity along a nontrivial filter dominates every
positive radius. -/
theorem cofinal_of_tendsto_atTop {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioi (0 : ℝ)} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l atTop) :
    ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ i :=
  fun r ↦ (hρ.eventually_ge_atTop (r : ℝ)).exists

/-- Canonical strictly increasing sequence of positive radii `n + 1` tending to infinity. -/
def natRadiusSeq (n : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨(n : ℝ) + 1, Set.mem_Ioi.mpr (by positivity)⟩

/-- Underlying real radius of `natRadiusSeq n`. -/
@[simp]
theorem coe_natRadiusSeq (n : ℕ) : (natRadiusSeq n : ℝ) = (n : ℝ) + 1 :=
  (rfl)

/-- The canonical radius sequence `natRadiusSeq` is strictly increasing. -/
theorem strictMono_natRadiusSeq : StrictMono fun n ↦ (natRadiusSeq n : ℝ) :=
  fun _ _ h ↦ by simp [h]

/-- The canonical radius sequence `natRadiusSeq` tends to infinity. -/
theorem tendsto_natRadiusSeq : Tendsto (fun n ↦ (natRadiusSeq n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

end Radii

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]

omit [IsUltrametricDist R] in
/-- A series is entire exactly when it is restricted at every positive radius. -/
theorem mem_subring_iff_forall_isRestricted {f : R⟦X⟧} :
    f ∈ IsEntire.subring R ↔ ∀ r : Set.Ioi (0 : ℝ), f.IsRestricted r :=
  IsEntire.mem_subring.trans <| isEntire_iff_forall_pos.trans
    ⟨fun h r ↦ h r r.property, fun h r hr ↦ h ⟨r, hr⟩⟩

/-- Restriction of an entire series to the closed disc of a positive radius. -/
noncomputable def restrict (r : Set.Ioi (0 : ℝ)) :
    IsEntire.subring R →+* IsRestricted.subring (R := R) (r : ℝ) :=
  GaussFamily.restrict (fun _ ↦ mem_subring_iff_forall_isRestricted) r

/-- Restriction leaves the underlying formal series unchanged. -/
@[simp]
theorem coe_restrict (r : Set.Ioi (0 : ℝ)) (f : IsEntire.subring R) :
    (restrict r f : R⟦X⟧) = f :=
  GaussFamily.coe_restrict _ r f

/-- Restriction of an entire series to the closed discs of all positive radii at once. -/
noncomputable def restrictFamily :
    IsEntire.subring R →+* ∀ r : Set.Ioi (0 : ℝ), IsRestricted.subring (R := R) (r : ℝ) :=
  GaussFamily.restrictFamily fun _ ↦ mem_subring_iff_forall_isRestricted

/-- Each component of the family of restrictions is the restriction to that radius. -/
@[simp]
theorem restrictFamily_apply (f : IsEntire.subring R) (r : Set.Ioi (0 : ℝ)) :
    restrictFamily f r = restrict r f :=
  GaussFamily.restrictFamily_apply _ f r

/-- Restriction of an entire series along a family `ρ : ι → Set.Ioi (0 : ℝ)` of positive radii. -/
noncomputable def restrictSubfamily {ι : Type*} (ρ : ι → Set.Ioi (0 : ℝ)) :
    IsEntire.subring R →+* ∀ i, IsRestricted.subring (R := R) (ρ i : ℝ) :=
  GaussFamily.restrictSubfamily (fun _ ↦ mem_subring_iff_forall_isRestricted) ρ

/-- Each component of `restrictSubfamily` is closed-disc restriction at that radius. -/
@[simp]
theorem restrictSubfamily_apply {ι : Type*} (ρ : ι → Set.Ioi (0 : ℝ))
    (f : IsEntire.subring R) (i : ι) :
    restrictSubfamily ρ f i = restrict (ρ i) f :=
  GaussFamily.restrictSubfamily_apply _ ρ f i

/-- Any nonempty family of closed-disc restrictions determines an entire series. -/
theorem restrictSubfamily_injective {ι : Type*} [Nonempty ι] (ρ : ι → Set.Ioi (0 : ℝ)) :
    Function.Injective (restrictSubfamily (R := R) ρ) :=
  GaussFamily.restrictSubfamily_injective _ ρ

/-- Along any cofinal family of positive radii, the image of `restrictSubfamily` consists of
families with index-independent formal coefficients. -/
theorem range_restrictSubfamily_of_cofinal_radius {ι : Type*} {ρ : ι → Set.Ioi (0 : ℝ)}
    (hρ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ i) :
    Set.range (restrictSubfamily (R := R) ρ) =
      {g | ∀ i j : ι, ∀ n : ℕ, coeff n (g i : R⟦X⟧) = coeff n (g j : R⟦X⟧)} :=
  GaussFamily.range_restrictSubfamily _ (fun r ↦ r.property.le) hρ

/-- Along any cofinal family of positive radii, the image of `restrictSubfamily` is closed in the
product of closed-disc algebras. -/
theorem isClosed_range_restrictSubfamily_of_cofinal_radius {ι : Type*} {ρ : ι → Set.Ioi (0 : ℝ)}
    (hρ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ i) :
    IsClosed (Set.range (restrictSubfamily (R := R) ρ)) :=
  GaussFamily.isClosed_range_restrictSubfamily _ (fun r ↦ r.property.le) hρ

/-- The uniformity generated by the Gauss norms at all positive radii. -/
noncomputable instance uniformSpace : UniformSpace (IsEntire.subring R) :=
  GaussFamily.uniformSpace fun _ ↦ mem_subring_iff_forall_isRestricted

/-- The Gauss uniformity is induced by the family of closed-disc restrictions. -/
theorem isUniformInducing_restrictFamily :
    IsUniformInducing (restrictFamily (R := R)) :=
  GaussFamily.isUniformInducing_restrictFamily_uniformSpace _

/-- Restriction along any cofinal family of positive radii is uniformly inducing. -/
theorem isUniformInducing_restrictSubfamily_of_cofinal_radius {ι : Type*} {ρ : ι → Set.Ioi (0 : ℝ)}
    (hρ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ i) :
    IsUniformInducing (restrictSubfamily (R := R) ρ) :=
  GaussFamily.isUniformInducing_restrictSubfamily isUniformInducing_restrictFamily hρ

/-- Restriction along any cofinal family of positive radii is a uniform embedding. -/
theorem isUniformEmbedding_restrictSubfamily_of_cofinal_radius {ι : Type*} {ρ : ι → Set.Ioi (0 : ℝ)}
    (hρ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ i) :
    IsUniformEmbedding (restrictSubfamily (R := R) ρ) :=
  have : Nonempty ι := let ⟨i, _⟩ := hρ ⟨1, one_pos⟩; ⟨i⟩
  GaussFamily.isUniformEmbedding_restrictSubfamily isUniformInducing_restrictFamily hρ

/-- Any cofinal family of positive radii induces the entire Gauss uniformity. -/
theorem comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius {ι : Type*}
    {ρ : ι → Set.Ioi (0 : ℝ)} (hρ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ i) :
    UniformSpace.comap (restrictSubfamily (R := R) ρ)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ i : ℝ)))) =
      uniformSpace :=
  GaussFamily.comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius _ hρ

/-- **Cofinal-family independence of the entire Gauss uniformity.** Any two cofinal families of
positive radii induce the exact same uniformity on `IsEntire.subring R`. -/
theorem comap_restrictSubfamily_eq_of_cofinal_radius {ι₁ ι₂ : Type*}
    {ρ₁ : ι₁ → Set.Ioi (0 : ℝ)} {ρ₂ : ι₂ → Set.Ioi (0 : ℝ)}
    (hρ₁ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ₁ i)
    (hρ₂ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ₂ i) :
    UniformSpace.comap (restrictSubfamily (R := R) ρ₁)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ₁ i : ℝ)))) =
    UniformSpace.comap (restrictSubfamily (R := R) ρ₂)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ₂ i : ℝ)))) :=
  GaussFamily.comap_restrictSubfamily_eq _ hρ₁ hρ₂

/-- The Gauss uniformity on `IsEntire.subring R` is countably generated (and therefore
metrizable). -/
instance : (𝓤 (IsEntire.subring R)).IsCountablyGenerated :=
  GaussFamily.isCountablyGenerated_uniformity isUniformInducing_restrictFamily
    (cofinal_of_tendsto_atTop tendsto_natRadiusSeq)

/-- **Projective-limit ring isomorphism for entire series.** Along any monotone family indexed by a
nonempty directed preorder (in particular, any monotone sequence) of positive radii tending to
infinity, the entire-series algebra is isomorphic as a ring to the subring of compatible restricted
series. -/
noncomputable def compatibleRingEquiv {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioi (0 : ℝ)} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop atTop) :
    IsEntire.subring R ≃+* GaussFamily.compatibleSubring (R := R) hmono :=
  GaussFamily.compatibleRingEquiv (fun _ ↦ mem_subring_iff_forall_isRestricted)
    (fun r ↦ r.property.le) hmono (cofinal_of_tendsto_atTop hρ)

/-- Each component of `compatibleRingEquiv` is closed-disc restriction at that stage. -/
@[simp]
theorem coe_compatibleRingEquiv_apply {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioi (0 : ℝ)} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop atTop) (f : IsEntire.subring R) (i : ι) :
    (compatibleRingEquiv hmono hρ f : ∀ i, IsRestricted.subring (R := R) (ρ i : ℝ)) i =
      restrict (ρ i) f :=
  GaussFamily.coe_compatibleRingEquiv_apply _ (fun r ↦ r.property.le) hmono
    (cofinal_of_tendsto_atTop hρ) f i

/-- Restricting the entire series reconstructed from a compatible family `g` at stage `i`
recovers `g i`. -/
@[simp]
theorem restrict_compatibleRingEquiv_symm {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {ρ : ι → Set.Ioi (0 : ℝ)} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop atTop)
    (g : GaussFamily.compatibleSubring (R := R) hmono) (i : ι) :
    restrict (ρ i) ((compatibleRingEquiv hmono hρ).symm g) = g.val i :=
  GaussFamily.restrict_compatibleRingEquiv_symm _ (fun r ↦ r.property.le) hmono
    (cofinal_of_tendsto_atTop hρ) g i

/-- The underlying formal power series of the entire series reconstructed from a compatible
family `g` agrees with `g i` at every stage `i`. -/
theorem coe_compatibleRingEquiv_symm {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioi (0 : ℝ)} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop atTop)
    (g : GaussFamily.compatibleSubring (R := R) hmono) (i : ι) :
    (((compatibleRingEquiv hmono hρ).symm g : IsEntire.subring R) : R⟦X⟧) =
      (g.val i : R⟦X⟧) :=
  GaussFamily.coe_compatibleRingEquiv_symm _ (fun r ↦ r.property.le) hmono
    (cofinal_of_tendsto_atTop hρ) g i

/-- **Family independence of the compatible-series description.** Compatible restricted-series
families along any two monotone families (indexed by nonempty directed preorders) of positive radii
tending to infinity define the same entire series if and only if they have the same underlying
formal power series. -/
theorem compatibleRingEquiv_symm_eq_iff {ι₁ ι₂ : Type*} [Preorder ι₁] [IsDirectedOrder ι₁]
    [Nonempty ι₁] [Preorder ι₂] [IsDirectedOrder ι₂] [Nonempty ι₂]
    {ρ₁ : ι₁ → Set.Ioi (0 : ℝ)} {ρ₂ : ι₂ → Set.Ioi (0 : ℝ)}
    (hmono₁ : Monotone fun i ↦ (ρ₁ i : ℝ)) (hρ₁ : Tendsto (fun i ↦ (ρ₁ i : ℝ)) atTop atTop)
    (hmono₂ : Monotone fun i ↦ (ρ₂ i : ℝ)) (hρ₂ : Tendsto (fun i ↦ (ρ₂ i : ℝ)) atTop atTop)
    (g₁ : GaussFamily.compatibleSubring (R := R) hmono₁)
    (g₂ : GaussFamily.compatibleSubring (R := R) hmono₂) (i₁ : ι₁) (i₂ : ι₂) :
    (compatibleRingEquiv hmono₁ hρ₁).symm g₁ = (compatibleRingEquiv hmono₂ hρ₂).symm g₂ ↔
      (g₁.val i₁ : R⟦X⟧) = (g₂.val i₂ : R⟦X⟧) :=
  GaussFamily.compatibleRingEquiv_symm_eq_iff _ (fun r ↦ r.property.le) hmono₁
    (cofinal_of_tendsto_atTop hρ₁) hmono₂ (cofinal_of_tendsto_atTop hρ₂) g₁ g₂ i₁ i₂

/-- **Projective-limit uniform equivalence for entire series.** Along any monotone family indexed by
a nonempty directed preorder (in particular, any monotone sequence) of positive radii tending to
infinity, the entire-series algebra with its Gauss uniformity is uniformly equivalent to the closed
subring of compatible restricted series. -/
noncomputable def compatibleUniformEquiv {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioi (0 : ℝ)} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop atTop) :
    IsEntire.subring R ≃ᵤ GaussFamily.compatibleSubring (R := R) hmono :=
  GaussFamily.compatibleUniformEquiv isUniformInducing_restrictFamily hmono
    (cofinal_of_tendsto_atTop hρ)

/-- `compatibleUniformEquiv` applies on elements as `compatibleRingEquiv`. -/
@[simp]
theorem compatibleUniformEquiv_apply {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioi (0 : ℝ)} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop atTop) (f : IsEntire.subring R) :
    compatibleUniformEquiv hmono hρ f = compatibleRingEquiv hmono hρ f :=
  GaussFamily.compatibleUniformEquiv_apply isUniformInducing_restrictFamily hmono
    (cofinal_of_tendsto_atTop hρ) f

/-- The inverse of `compatibleUniformEquiv` applies on elements as the inverse of
`compatibleRingEquiv`. -/
@[simp]
theorem compatibleUniformEquiv_symm_apply {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {ρ : ι → Set.Ioi (0 : ℝ)} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop atTop)
    (g : GaussFamily.compatibleSubring (R := R) hmono) :
    (compatibleUniformEquiv hmono hρ).symm g = (compatibleRingEquiv hmono hρ).symm g :=
  GaussFamily.compatibleUniformEquiv_symm_apply isUniformInducing_restrictFamily hmono
    (cofinal_of_tendsto_atTop hρ) g

/-- Restriction to any closed disc is uniformly continuous for the Gauss uniformities. -/
theorem uniformContinuous_restrict (r : Set.Ioi (0 : ℝ)) :
    UniformContinuous (restrict (R := R) r) :=
  GaussFamily.uniformContinuous_restrict isUniformInducing_restrictFamily r

/-- Convergence of entire series is convergence in the Gauss norm at every positive radius. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι}
    {f : ι → IsEntire.subring R} {g : IsEntire.subring R} :
    Tendsto f l (𝓝 g) ↔ ∀ r : Set.Ioi (0 : ℝ),
      Tendsto (fun i ↦ restrict r (f i)) l (𝓝 (restrict r g)) :=
  GaussFamily.tendsto_iff isUniformInducing_restrictFamily

/-- Convergence can be tested at any family of positive radii that is unbounded above. -/
theorem tendsto_iff_of_cofinal_radius {ι κ : Type*}
    {ρ : ι → Set.Ioi (0 : ℝ)} (hρ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ i)
    {F : Filter κ} {f : κ → IsEntire.subring R} {g : IsEntire.subring R} :
    Tendsto f F (𝓝 g) ↔ ∀ i, Tendsto (fun j ↦ restrict (ρ i) (f j)) F (𝓝 (restrict (ρ i) g)) :=
  GaussFamily.tendsto_iff_of_cofinal_radius isUniformInducing_restrictFamily hρ

/-- Convergence can be tested along positive radii tending to infinity, for instance along a
sequence of radii tending to infinity. -/
theorem tendsto_iff_of_tendsto_atTop {ι κ : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioi (0 : ℝ)} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l atTop)
    {F : Filter κ} {f : κ → IsEntire.subring R} {g : IsEntire.subring R} :
    Tendsto f F (𝓝 g) ↔ ∀ i, Tendsto (fun j ↦ restrict (ρ i) (f j)) F (𝓝 (restrict (ρ i) g)) :=
  tendsto_iff_of_cofinal_radius (cofinal_of_tendsto_atTop hρ)

/-- A map into the entire series is continuous exactly when each restriction is continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → IsEntire.subring R} :
    Continuous f ↔ ∀ r : Set.Ioi (0 : ℝ), Continuous fun x ↦ restrict r (f x) :=
  GaussFamily.continuous_iff isUniformInducing_restrictFamily

/-- A map into the entire series is uniformly continuous exactly when each restriction is. -/
theorem uniformContinuous_iff {X : Type*} [UniformSpace X] {f : X → IsEntire.subring R} :
    UniformContinuous f ↔ ∀ r : Set.Ioi (0 : ℝ), UniformContinuous fun x ↦ restrict r (f x) :=
  GaussFamily.uniformContinuous_iff isUniformInducing_restrictFamily

instance : IsUniformAddGroup (IsEntire.subring R) :=
  GaussFamily.isUniformAddGroup isUniformInducing_restrictFamily

instance : IsTopologicalRing (IsEntire.subring R) :=
  GaussFamily.isTopologicalRing isUniformInducing_restrictFamily

instance : NonarchimedeanRing (IsEntire.subring R) :=
  GaussFamily.nonarchimedeanRing isUniformInducing_restrictFamily

instance {S : Type*} [CommSemiring S] [TopologicalSpace S] [Algebra S R] [ContinuousSMul S R] :
    ContinuousSMul S (IsEntire.subring R) :=
  GaussFamily.continuousSMul isUniformInducing_restrictFamily.isInducing
    IsEntire.coe_smul_subring

/-- Polynomial truncations converge in the Gauss norms at all positive radii simultaneously. -/
theorem tendsto_polynomialHom_trunc (f : IsEntire.subring R) :
    Tendsto (fun n ↦ IsEntire.polynomialHom ((f : R⟦X⟧).trunc n)) atTop (𝓝 f) :=
  GaussFamily.tendsto_polynomialHom_trunc isUniformInducing_restrictFamily _
    IsEntire.coe_polynomialHom f

/-- Polynomials are dense for the topology of the Gauss norms at all positive radii. -/
theorem denseRange_polynomialHom : DenseRange (IsEntire.polynomialHom (R := R)) :=
  GaussFamily.denseRange_polynomialHom isUniformInducing_restrictFamily _
    IsEntire.coe_polynomialHom

instance : T2Space (IsEntire.subring R) :=
  GaussFamily.t2Space isUniformInducing_restrictFamily

/-- Each coefficient is uniformly continuous for the Gauss uniformity on entire series. -/
theorem uniformContinuous_coeff (n : ℕ) :
    UniformContinuous fun f : IsEntire.subring R ↦ coeff n (f : R⟦X⟧) :=
  GaussFamily.uniformContinuous_coeff isUniformInducing_restrictFamily n

/-- The restriction image consists exactly of families with radius-independent coefficients. -/
theorem range_restrictFamily :
    Set.range (restrictFamily (R := R)) =
      {g | ∀ r s : Set.Ioi (0 : ℝ), ∀ n : ℕ, coeff n (g r : R⟦X⟧) = coeff n (g s : R⟦X⟧)} :=
  GaussFamily.range_restrictFamily _

/-- The entire series with the Gauss norms at all positive radii form a complete ring over
complete coefficients. -/
instance [CompleteSpace R] : CompleteSpace (IsEntire.subring R) :=
  GaussFamily.completeSpace isUniformInducing_restrictFamily

/-- No zero-neighborhood in `IsEntire.subring R` is bounded in the sense of
`TauCeti.Huber.IsBounded` over a nontrivial ultrametric normed coefficient ring `R` containing a
unit of norm `< 1`. -/
theorem not_isBounded_of_mem_nhds_zero [Nontrivial R] (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1)
    {U : Set (IsEntire.subring R)} (hU : U ∈ 𝓝 (0 : IsEntire.subring R)) :
    ¬ TauCeti.Huber.IsBounded U :=
  GaussFamily.not_isBounded_of_mem_nhds_zero isUniformInducing_restrictFamily.isInducing
    exists_gt hu hU

/-- **No single ring seminorm represents the entire Gauss topology.** Over a nontrivial ultrametric
normed coefficient ring `R` containing a unit of norm `< 1`, no ring seminorm on
`IsEntire.subring R` induces its Gauss topology. -/
theorem not_exists_ringSeminorm_toTopologicalSpace_eq [Nontrivial R]
    (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ p : RingSeminorm (IsEntire.subring R),
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace :=
  GaussFamily.not_exists_ringSeminorm_toTopologicalSpace_eq
    isUniformInducing_restrictFamily.isInducing exists_gt hu

/-- **No scalar-bounded group seminorm represents the entire Gauss topology.** Over a nontrivial
ultrametric normed coefficient ring `R` containing a unit of norm `< 1`, no additive group
seminorm `p` on `IsEntire.subring R` in which left multiplication by constant series is bounded by
`C * ‖c‖` induces the Gauss topology. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_polynomialHom_C_mul_le [Nontrivial R]
    (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ (p : AddGroupSeminorm (IsEntire.subring R)) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : R) (f : IsEntire.subring R),
        p (IsEntire.polynomialHom (Polynomial.C c) * f) ≤ C * ‖c‖ * p f :=
  GaussFamily.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_mul_le
    isUniformInducing_restrictFamily.isInducing exists_gt hu (fun _ ↦ by simp)

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- **No scalar-bounded group seminorm represents the entire Gauss topology.** Over a nontrivial
ultrametric normed commutative ring `R` containing a unit of norm `< 1`, no additive group seminorm
`p` on `IsEntire.subring R` in which scalar multiplication is bounded by `C * ‖c‖` induces the
Gauss topology. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le [Nontrivial R]
    (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ (p : AddGroupSeminorm (IsEntire.subring R)) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : R) (f : IsEntire.subring R), p (c • f) ≤ C * ‖c‖ * p f :=
  GaussFamily.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le
    isUniformInducing_restrictFamily.isInducing exists_gt hu IsEntire.coe_smul_subring

end NormedCommRing

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Over a nontrivially normed ultrametric field, no zero-neighborhood in `IsEntire.subring K` is
bounded in the sense of `TauCeti.Huber.IsBounded`. -/
theorem not_isBounded_of_mem_nhds_zero_of_nontriviallyNormedField
    {U : Set (IsEntire.subring K)} (hU : U ∈ 𝓝 (0 : IsEntire.subring K)) :
    ¬ TauCeti.Huber.IsBounded U :=
  GaussFamily.not_isBounded_of_mem_nhds_zero_of_nontriviallyNormedField
    (isUniformInducing_restrictFamily (R := K)).isInducing exists_gt hU

/-- Over a nontrivially normed ultrametric field, no single ring seminorm (and in particular no
single Banach-algebra norm) induces the Gauss topology on entire series. -/
theorem not_exists_ringSeminorm_toTopologicalSpace_eq_of_nontriviallyNormedField :
    ¬ ∃ p : RingSeminorm (IsEntire.subring K),
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace :=
  GaussFamily.not_exists_ringSeminorm_toTopologicalSpace_eq_of_nontriviallyNormedField
    (isUniformInducing_restrictFamily (R := K)).isInducing exists_gt

/-- Over a nontrivially normed ultrametric field, no additive group seminorm in which scalar
multiplication (equivalently, left multiplication by constant series) is bounded by `C * ‖c‖`
induces the Gauss topology on entire series. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le_of_nontriviallyNormedField :
    ¬ ∃ (p : AddGroupSeminorm (IsEntire.subring K)) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : K) (f : IsEntire.subring K), p (c • f) ≤ C * ‖c‖ * p f :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le
    ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩

/-- Over a nontrivially normed ultrametric field `K`, `IsEntire.subring K` with its Gauss topology
is not normable as a `K`-vector space. -/
theorem not_isNormableSpace : ¬ IsNormableSpace K (IsEntire.subring K) :=
  GaussFamily.not_isNormableSpace (isUniformInducing_restrictFamily (R := K)).isInducing exists_gt
    IsEntire.coe_smul_subring

end NontriviallyNormedField

section Eval

variable {R A : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormedRing A] [Algebra R A]
  [IsBoundedSMul R A]

/-- The radius `2 ‖b‖ + 1`, at least twice the norm of `b`, whose Gauss norm controls
evaluation at `b`. -/
private noncomputable def evalRadius (b : A) : Set.Ioi (0 : ℝ) :=
  ⟨2 * ‖b‖ + 1, Set.mem_Ioi.mpr (by positivity)⟩

variable [CompleteSpace A]

/-- Evaluation of entire series at a point of a complete normed algebra is continuous for the
topology of the Gauss norms at all positive radii. -/
theorem continuous_evalAtHom (b : A) : Continuous (IsEntire.evalAtHom R b) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  have h : Tendsto (restrict (R := R) (evalRadius b)) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using
      (uniformContinuous_restrict (R := R) (evalRadius b)).continuous.tendsto 0
  have hb : ‖b‖ ≤ 2⁻¹ * (evalRadius b : ℝ) := by
    simp only [evalRadius]
    linarith
  refine squeeze_zero_norm
    (a := fun f ↦ (‖(1 : A)‖ + 1) * ‖restrict (evalRadius b) f‖ * (1 - 2⁻¹)⁻¹) (fun f ↦ ?_) ?_
  · have hf := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (restrict (evalRadius b) f).property
    rw [coe_restrict] at hf
    rw [IsEntire.evalAtHom_apply, TauCeti.PowerSeries.norm_eq_gaussNorm, coe_restrict]
    exact norm_evalAt_le_mul_gaussNorm hf (by norm_num) (by norm_num) hb
  · simpa using (h.norm.const_mul (‖(1 : A)‖ + 1)).mul_const (1 - 2⁻¹ : ℝ)⁻¹

end Eval

section InfiniteProd

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- An unconditional product of entire series converges in the Gauss topology exactly when its
restriction to every positive-radius closed disc converges. -/
theorem hasProd_iff {ι : Type*} {f : ι → IsEntire.subring R} {g : IsEntire.subring R} :
    HasProd f g ↔
      ∀ r : Set.Ioi (0 : ℝ), HasProd (fun i ↦ restrict r (f i)) (restrict r g) :=
  GaussFamily.hasProd_iff isUniformInducing_restrictFamily

/-- A family of entire series is unconditionally multipliable in the Gauss topology exactly when
its restriction to every positive-radius closed disc is multipliable. -/
theorem multipliable_iff {ι : Type*} {f : ι → IsEntire.subring R} :
    Multipliable f ↔ ∀ r : Set.Ioi (0 : ℝ), Multipliable fun i ↦ restrict r (f i) :=
  GaussFamily.multipliable_iff isUniformInducing_restrictFamily

/-- Restriction to a positive-radius closed disc commutes with convergent infinite products of
entire series. -/
theorem restrict_tprod {ι : Type*} {f : ι → IsEntire.subring R} (hf : Multipliable f)
    (r : Set.Ioi (0 : ℝ)) :
    restrict r (∏' i, f i) = ∏' i, restrict r (f i) :=
  GaussFamily.restrict_tprod isUniformInducing_restrictFamily hf r

/-- The constant coefficient of a convergent infinite product of entire series is the infinite
product of the constant coefficients. -/
theorem constantCoeff_tprod {ι : Type*} {f : ι → IsEntire.subring R} (hf : Multipliable f) :
    constantCoeff ((∏' i, f i : IsEntire.subring R) : R⟦X⟧) =
      ∏' i, constantCoeff (f i : R⟦X⟧) :=
  have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, one_pos⟩⟩
  GaussFamily.constantCoeff_tprod isUniformInducing_restrictFamily hf

/-- Evaluation at a point of a complete normed commutative algebra preserves convergent infinite
products of entire series. -/
theorem evalAt_hasProd {ι A : Type*} [NormedCommRing A] [Algebra R A] [IsBoundedSMul R A]
    [CompleteSpace A] {f : ι → IsEntire.subring R} {g : IsEntire.subring R}
    (hf : HasProd f g) (b : A) :
    HasProd (fun i ↦ (f i : R⟦X⟧).evalAt b) ((g : R⟦X⟧).evalAt b) := by
  simpa only [Function.comp_def, IsEntire.evalAtHom_apply] using
    hf.map (IsEntire.evalAtHom R b) (continuous_evalAtHom b)

/-- If every factor of a convergent infinite product of entire series lies strictly within `ε ≤ 1`
of `1` in the Gauss norm at `r > 0`, then so does the infinite product. -/
theorem gaussNorm_sub_one_lt_of_hasProd {ι : Type*} {f : ι → IsEntire.subring R}
    {g : IsEntire.subring R} (hf : HasProd f g) {r ε : ℝ} (hr : 0 < r) (hε0 : 0 < ε)
    (hε : ε ≤ 1) (h : ∀ i, ((f i : R⟦X⟧) - 1).gaussNorm norm r < ε) :
    ((g : R⟦X⟧) - 1).gaussNorm norm r < ε := by
  have : Fact (0 < r) := ⟨hr⟩
  have hlt := (hasProd_iff.mp hf ⟨r, hr⟩).norm_sub_one_lt hε0 hε fun i ↦ by
    rw [TauCeti.PowerSeries.norm_eq_gaussNorm, AddSubgroupClass.coe_sub, coe_restrict,
      OneMemClass.coe_one]
    exact h i
  rwa [TauCeti.PowerSeries.norm_eq_gaussNorm, AddSubgroupClass.coe_sub, coe_restrict,
    OneMemClass.coe_one] at hlt

variable [CompleteSpace R]

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, if `f`
tends to `0` along the cofinite filter, then the family of finite products `s ↦ ∏ i ∈ s, f i` is
unconditionally summable. -/
theorem summable_prod_of_tendsto_cofinite_zero {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    Summable fun s : Finset ι ↦ ∏ i ∈ s, f i := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_iff.mpr fun r ↦ ?_)
  have hr : Tendsto (fun i ↦ restrict r (f i)) cofinite (𝓝 0) := by
    simpa only [map_zero] using tendsto_iff.mp hf r
  simpa only [map_zero, map_prod] using TauCeti.tendsto_finsetProd_cofinite_zero hr

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, if `f`
tends to `0` along the cofinite filter, then `i ↦ 1 + f i` is unconditionally multipliable. -/
theorem multipliable_one_add_of_tendsto_cofinite_zero {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    Multipliable fun i ↦ 1 + f i :=
  multipliable_one_add_of_summable_prod (summable_prod_of_tendsto_cofinite_zero hf)

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, any
family tending to `1` along the cofinite filter is unconditionally multipliable, even when its
factors are not units of `PowerSeries.IsEntire.subring R`. -/
theorem multipliable_of_tendsto_cofinite_one {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 1)) :
    Multipliable f := by
  have h0 : Tendsto (fun i ↦ f i - 1) cofinite (𝓝 0) := by
    simpa only [sub_self] using hf.sub_const 1
  simpa only [add_sub_cancel] using multipliable_one_add_of_tendsto_cofinite_zero h0

end InfiniteProd

end TauCeti.PowerSeries.IsEntire
