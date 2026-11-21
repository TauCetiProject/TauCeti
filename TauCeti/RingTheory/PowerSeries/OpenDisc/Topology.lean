/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.Basic
public import TauCeti.RingTheory.PowerSeries.Entire.Topology
public import TauCeti.RingTheory.PowerSeries.GaussFamily

/-!
# The Gauss topology on series on an open disc

For an ultrametric normed ring `R` and a positive radius `R₀`, the algebra of series on the
open disc carries the topology of the Gauss norms at all radii `0 < r < R₀`. Convergence is
convergence in each of these norms, rather than convergence of individual coefficients.
The resulting uniform ring has a countably generated uniformity, is Hausdorff when `0 < R₀` (hence
is metrizable), has continuous scalar multiplication, and is complete when `R` is complete.
Polynomial truncations converge in this topology, and coefficient maps, radius restrictions
(`radiusHom`), and inclusions from the boundary closed-disc algebra (`ofIsRestricted`) are
uniformly continuous; the latter two have dense range. The inclusion of entire series is likewise
uniformly continuous with dense range, and additive maps bounded between smaller-radius Gauss norms
are uniformly continuous.

Restriction embeds the algebra into the product of the smaller closed-disc algebras. Its
image consists of the families with the same formal coefficients at every radius. Along any
monotone family indexed by a nonempty directed preorder (in particular, any monotone sequence) of
radii in `(0, R₀)` tending to `R₀`, the open-disc algebra is isomorphic as a ring and as a uniform
space to the closed subring of compatible restricted series, and both the induced Gauss uniformity
(along any cofinal family or sequence tending to `R₀`) and this compatible-series description are
independent of the chosen family. Over a nontrivial ultrametric normed ring
with a unit of norm `< 1` (in particular, over any nontrivially normed ultrametric field), no
zero-neighborhood is bounded and no single ring seminorm, scalar-bounded additive group seminorm,
or normable space structure represents this topology when `0 < R₀`. These are specializations of
the Gauss topology of a family of radii in `TauCeti.RingTheory.PowerSeries.GaussFamily`.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.restrict`, `TauCeti.PowerSeries.OnOpenDisc.restrictFamily`, and
  `TauCeti.PowerSeries.OnOpenDisc.restrictSubfamily`: closed-disc restriction to a single smaller
  positive radius, to all radii in `(0, R₀)` at once, and along a subfamily.
* `TauCeti.PowerSeries.OnOpenDisc.uniformSpace`: the Gauss uniformity on
  `PowerSeries.OnOpenDisc.subring R R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.radiusSeq`: the canonical strictly increasing sequence of radii
  `(1 - (n + 2)⁻¹) * R₀` exhausting `(0, R₀)` when `0 < R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.compatibleRingEquiv` and
  `TauCeti.PowerSeries.OnOpenDisc.compatibleUniformEquiv`: ring and uniform equivalences with the
  subring of compatible restricted series along any monotone family (indexed by a nonempty directed
  preorder) of radii in `(0, R₀)` tending to `R₀`.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.tendsto_iff`,
  `TauCeti.PowerSeries.OnOpenDisc.tendsto_iff_of_cofinal_radius`, and
  `TauCeti.PowerSeries.OnOpenDisc.tendsto_iff_of_tendsto`: convergence on the open disc, tested at
  all radii in `(0, R₀)`, along any cofinal family, or along any family tending to `R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.tendsto_polynomialHom_trunc`,
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_polynomialHom`,
  `TauCeti.PowerSeries.OnOpenDisc.ringHom_ext`, and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_coeff`: polynomial truncation convergence,
  density of polynomials, determination of continuous ring homomorphisms, and uniform continuity
  of coefficients (when `0 < R₀`).
* `TauCeti.PowerSeries.OnOpenDisc.range_restrictFamily`,
  `TauCeti.PowerSeries.OnOpenDisc.range_restrictSubfamily_of_cofinal_radius`,
  `TauCeti.PowerSeries.OnOpenDisc.comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius`, and
  `TauCeti.PowerSeries.OnOpenDisc.comap_restrictSubfamily_eq_of_cofinal_radius`: the restriction
  image and sequence-independent induction of the open-disc Gauss uniformity.
* `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_radiusHom`,
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_radiusHom`,
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_ofIsRestricted`,
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_ofIsRestricted`,
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_inclusion_entire`, and
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_inclusion_entire`: uniform continuity and dense range
  of radius restriction and of the inclusions of boundary closed-disc and entire series.
* `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_of_norm_restrict_le`: uniform continuity of
  additive maps between open-disc subrings bounded between smaller-radius Gauss norms.
* `TauCeti.PowerSeries.OnOpenDisc.compatibleRingEquiv_symm_eq_iff`: independence of the monotone
  family (indexed by a nonempty directed preorder) in the compatible-series description.
* `TauCeti.PowerSeries.OnOpenDisc.not_isBounded_of_mem_nhds_zero`,
  `TauCeti.PowerSeries.OnOpenDisc.not_exists_ringSeminorm_toTopologicalSpace_eq`,
  `OnOpenDisc.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_polynomialHom_C_mul_le`,
  `OnOpenDisc.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le`, and
  `TauCeti.PowerSeries.OnOpenDisc.not_isNormableSpace`: when `0 < R₀`, no zero-neighborhood is
  bounded and no compatible ring seminorm, scalar-bounded additive group seminorm, or normable
  space structure represents the open-disc Gauss topology over a nontrivial ultrametric normed ring
  with a unit of norm `< 1` (in particular, over a nontrivially normed ultrametric field).
* Instances: `IsUniformAddGroup`, `IsTopologicalRing`, `ContinuousSMul`,
  `Filter.IsCountablyGenerated` on the uniformity `𝓤 (OnOpenDisc.subring R R₀)`, `T2Space` when
  `0 < R₀` (hence `MetrizableSpace`), and over complete coefficients (`[CompleteSpace R]`)
  `CompleteSpace` on `PowerSeries.OnOpenDisc.subring R R₀`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter PowerSeries
open scoped Topology Uniformity

namespace TauCeti.PowerSeries.OnOpenDisc

-- Supply the positivity witness used by the Gauss-norm instances on each closed disc.
local instance radius_pos {R₀ : ℝ} (r : Set.Ioo (0 : ℝ) R₀) : Fact (0 < (r : ℝ)) := ⟨r.property.1⟩

-- The radii below a positive boundary form a nonempty family.
local instance {R₀ : ℝ} [Fact (0 < R₀)] : Nonempty (Set.Ioo (0 : ℝ) R₀) :=
  Set.nonempty_Ioo_subtype Fact.out

section Radii

variable {R₀ : ℝ}

/-- Any family of radii in `(0, R₀)` tending to `R₀` along a nontrivial filter dominates every
radius in `(0, R₀)`. -/
theorem cofinal_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l (𝓝 R₀)) :
    ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i :=
  fun r ↦ (hρ.eventually (Ici_mem_nhds r.property.2)).exists

/-- Canonical strictly increasing sequence of radii `(1 - (n + 2)⁻¹) * R₀` exhausting `(0, R₀)`
when `0 < R₀`. -/
noncomputable def radiusSeq (R₀ : ℝ) [Fact (0 < R₀)] (n : ℕ) : Set.Ioo (0 : ℝ) R₀ :=
  ⟨(1 - ((n + 2 : ℕ) : ℝ)⁻¹) * R₀, by
    have hR₀ : 0 < R₀ := Fact.out
    have hn2 : (2 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast Nat.le_add_left 2 n
    have hinv_pos : 0 < ((n + 2 : ℕ) : ℝ)⁻¹ := inv_pos.mpr (two_pos.trans_le hn2)
    have hinv_lt : ((n + 2 : ℕ) : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_two.trans_le hn2)
    exact ⟨mul_pos (sub_pos.mpr hinv_lt) hR₀, mul_lt_of_lt_one_left hR₀ (sub_lt_self 1 hinv_pos)⟩⟩

/-- Underlying real radius of `radiusSeq R₀ n`. -/
@[simp]
theorem coe_radiusSeq (R₀ : ℝ) [Fact (0 < R₀)] (n : ℕ) :
    (radiusSeq R₀ n : ℝ) = (1 - ((n + 2 : ℕ) : ℝ)⁻¹) * R₀ :=
  (rfl)

/-- The canonical radius sequence `radiusSeq R₀` is strictly increasing. -/
theorem strictMono_radiusSeq (R₀ : ℝ) [Fact (0 < R₀)] :
    StrictMono fun n ↦ (radiusSeq R₀ n : ℝ) := by
  intro m n hmn
  have hR₀ : 0 < R₀ := Fact.out
  have hm_pos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
  have hlt : ((m + 2 : ℕ) : ℝ) < (n + 2 : ℕ) := by exact_mod_cast Nat.add_lt_add_right hmn 2
  exact mul_lt_mul_of_pos_right (sub_lt_sub_left (inv_strictAnti₀ hm_pos hlt) 1) hR₀

/-- The canonical radius sequence `radiusSeq R₀` tends to `R₀`. -/
theorem tendsto_radiusSeq (R₀ : ℝ) [Fact (0 < R₀)] :
    Tendsto (fun n ↦ (radiusSeq R₀ n : ℝ)) atTop (𝓝 R₀) := by
  have h0 : Tendsto (fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  simpa only [coe_radiusSeq, Function.comp_def, sub_zero, one_mul] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).mul_const R₀

end Radii

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ : ℝ}

omit [IsUltrametricDist R] in
/-- A series lies on the open disc of radius `R₀` exactly when it is restricted at every smaller
positive radius. -/
theorem mem_subring_iff_forall_isRestricted {f : R⟦X⟧} :
    f ∈ OnOpenDisc.subring R R₀ ↔ ∀ r : Set.Ioo (0 : ℝ) R₀, f.IsRestricted r :=
  OnOpenDisc.mem_subring.trans <| onOpenDisc_iff.trans
    ⟨fun h r ↦ h r r.property.1 r.property.2, fun h r hr hrR ↦ h ⟨r, hr, hrR⟩⟩

/-- Restriction of an open-disc series to a smaller positive closed disc. -/
noncomputable def restrict (r : Set.Ioo (0 : ℝ) R₀) :
    OnOpenDisc.subring R R₀ →+* IsRestricted.subring (R := R) (r : ℝ) :=
  GaussFamily.restrict (fun _ ↦ mem_subring_iff_forall_isRestricted) r

/-- Restriction leaves the underlying formal series unchanged. -/
@[simp]
theorem coe_restrict (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    (restrict r f : R⟦X⟧) = f :=
  GaussFamily.coe_restrict _ r f

/-- The variable has Gauss norm equal to the radius of the smaller closed disc. -/
@[simp]
theorem norm_restrict_X [NormOneClass R] (r : Set.Ioo (0 : ℝ) R₀) :
    ‖restrict r (OnOpenDisc.polynomialHom Polynomial.X : OnOpenDisc.subring R R₀)‖ = r := by
  have h : restrict r (OnOpenDisc.polynomialHom Polynomial.X : OnOpenDisc.subring R R₀) =
      (⟨X, by
        rw [PowerSeries.X_eq]
        exact PowerSeries.isRestricted_monomial (r : ℝ) 1 (1 : R)⟩ :
        IsRestricted.subring (R := R) (r : ℝ)) :=
    Subtype.ext (by simp)
  rw [h, norm_X]

/-- Restriction to a smaller closed disc is injective, since it preserves every coefficient. -/
theorem restrict_injective (r : Set.Ioo (0 : ℝ) R₀) :
    Function.Injective (restrict (R := R) r) := fun f g h ↦
  Subtype.ext (by simpa only [coe_restrict] using congrArg Subtype.val h)

/-- Restriction sends a constant to the same scalar in the closed-disc algebra. -/
@[simp]
theorem restrict_polynomialHom_C {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    (r : Set.Ioo (0 : ℝ) R₀) (a : S) :
    restrict r (OnOpenDisc.polynomialHom (Polynomial.C a)) =
      algebraMap S (IsRestricted.subring (R := S) (r : ℝ)) a := by
  apply Subtype.ext
  simp

/-- Restriction to a smaller closed disc commutes with `algebraMap` from any base algebra. -/
@[simp]
theorem restrict_algebraMap {A : Type*} [CommSemiring A] [Algebra A R]
    (r : Set.Ioo (0 : ℝ) R₀) (a : A) :
    restrict r (algebraMap A (OnOpenDisc.subring R R₀) a) =
      algebraMap A (IsRestricted.subring (R := R) (r : ℝ)) a :=
  Subtype.ext (by simp)

/-- Restriction to a smaller closed disc commutes with scalar multiplication from any base
algebra. -/
@[simp]
theorem restrict_smul {A : Type*} [CommSemiring A] [Algebra A R] (r : Set.Ioo (0 : ℝ) R₀)
    (a : A) (f : OnOpenDisc.subring R R₀) :
    restrict r (a • f) = a • restrict r f :=
  Subtype.ext (by simp)

/-- Restriction of an open-disc series to all smaller positive closed discs at once. -/
noncomputable def restrictFamily :
    OnOpenDisc.subring R R₀ →+* ∀ r : Set.Ioo (0 : ℝ) R₀, IsRestricted.subring (R := R) (r : ℝ) :=
  GaussFamily.restrictFamily fun _ ↦ mem_subring_iff_forall_isRestricted

/-- Each component of the family of restrictions is the restriction to that radius. -/
@[simp]
theorem restrictFamily_apply (f : OnOpenDisc.subring R R₀) (r : Set.Ioo (0 : ℝ) R₀) :
    restrictFamily f r = restrict r f :=
  GaussFamily.restrictFamily_apply _ f r

/-- Restriction of an open-disc series along a family `ρ : ι → Set.Ioo (0 : ℝ) R₀` of smaller
positive radii. -/
noncomputable def restrictSubfamily {ι : Type*} (ρ : ι → Set.Ioo (0 : ℝ) R₀) :
    OnOpenDisc.subring R R₀ →+* ∀ i, IsRestricted.subring (R := R) (ρ i : ℝ) :=
  GaussFamily.restrictSubfamily (fun _ ↦ mem_subring_iff_forall_isRestricted) ρ

/-- Each component of `restrictSubfamily` is closed-disc restriction at that radius. -/
@[simp]
theorem restrictSubfamily_apply {ι : Type*} (ρ : ι → Set.Ioo (0 : ℝ) R₀)
    (f : OnOpenDisc.subring R R₀) (i : ι) :
    restrictSubfamily ρ f i = restrict (ρ i) f :=
  GaussFamily.restrictSubfamily_apply _ ρ f i

/-- Any nonempty family of closed-disc restrictions determines an open-disc series. -/
theorem restrictSubfamily_injective {ι : Type*} [Nonempty ι] (ρ : ι → Set.Ioo (0 : ℝ) R₀) :
    Function.Injective (restrictSubfamily (R := R) ρ) :=
  GaussFamily.restrictSubfamily_injective _ ρ

/-- Along any cofinal family of radii in `(0, R₀)`, the image of `restrictSubfamily` consists of
families with index-independent formal coefficients. -/
theorem range_restrictSubfamily_of_cofinal_radius {ι : Type*} {ρ : ι → Set.Ioo (0 : ℝ) R₀}
    (hρ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i) :
    Set.range (restrictSubfamily (R := R) ρ) =
      {g | ∀ i j : ι, ∀ n : ℕ, coeff n (g i : R⟦X⟧) = coeff n (g j : R⟦X⟧)} :=
  GaussFamily.range_restrictSubfamily _ (fun r ↦ r.property.1.le) hρ

/-- Along any cofinal family of radii in `(0, R₀)`, the image of `restrictSubfamily` is closed in
the product of closed-disc algebras. -/
theorem isClosed_range_restrictSubfamily_of_cofinal_radius {ι : Type*}
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i) :
    IsClosed (Set.range (restrictSubfamily (R := R) ρ)) :=
  GaussFamily.isClosed_range_restrictSubfamily _ (fun r ↦ r.property.1.le) hρ

/-- The uniformity generated by all smaller positive-radius Gauss norms. -/
noncomputable instance uniformSpace : UniformSpace (OnOpenDisc.subring R R₀) :=
  GaussFamily.uniformSpace fun _ ↦ mem_subring_iff_forall_isRestricted

/-- The Gauss uniformity is induced by the family of closed-disc restrictions. -/
theorem isUniformInducing_restrictFamily :
    IsUniformInducing (restrictFamily (R := R) (R₀ := R₀)) :=
  GaussFamily.isUniformInducing_restrictFamily_uniformSpace _

/-- Restriction along any cofinal family of radii in `(0, R₀)` is uniformly inducing. -/
theorem isUniformInducing_restrictSubfamily_of_cofinal_radius {ι : Type*}
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i) :
    IsUniformInducing (restrictSubfamily (R := R) ρ) :=
  GaussFamily.isUniformInducing_restrictSubfamily isUniformInducing_restrictFamily hρ

/-- Restriction along any nonempty cofinal family of radii in `(0, R₀)` is a uniform embedding. -/
theorem isUniformEmbedding_restrictSubfamily_of_cofinal_radius {ι : Type*} [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i) :
    IsUniformEmbedding (restrictSubfamily (R := R) ρ) :=
  GaussFamily.isUniformEmbedding_restrictSubfamily isUniformInducing_restrictFamily hρ

/-- Any cofinal family of smaller positive radii induces the open-disc Gauss uniformity. -/
theorem comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius {ι : Type*}
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i) :
    UniformSpace.comap (restrictSubfamily (R := R) ρ)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ i : ℝ)))) =
      uniformSpace :=
  GaussFamily.comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius _ hρ

/-- **Cofinal-family independence of the open-disc Gauss uniformity.** Any two cofinal families of
radii in `(0, R₀)` induce the exact same uniformity on `OnOpenDisc.subring R R₀`. -/
theorem comap_restrictSubfamily_eq_of_cofinal_radius {ι₁ ι₂ : Type*}
    {ρ₁ : ι₁ → Set.Ioo (0 : ℝ) R₀} {ρ₂ : ι₂ → Set.Ioo (0 : ℝ) R₀}
    (hρ₁ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ₁ i)
    (hρ₂ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ₂ i) :
    UniformSpace.comap (restrictSubfamily (R := R) ρ₁)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ₁ i : ℝ)))) =
    UniformSpace.comap (restrictSubfamily (R := R) ρ₂)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ₂ i : ℝ)))) :=
  GaussFamily.comap_restrictSubfamily_eq _ hρ₁ hρ₂

/-- The Gauss uniformity on `OnOpenDisc.subring R R₀` is countably generated (and therefore
metrizable when `0 < R₀`). -/
instance : (𝓤 (OnOpenDisc.subring R R₀)).IsCountablyGenerated := by
  rcases lt_or_ge 0 R₀ with hR₀ | hR₀
  · have : Fact (0 < R₀) := ⟨hR₀⟩
    exact GaussFamily.isCountablyGenerated_uniformity isUniformInducing_restrictFamily
      (cofinal_of_tendsto (tendsto_radiusSeq R₀))
  · have : IsEmpty (Set.Ioo (0 : ℝ) R₀) := ⟨fun r ↦ (r.property.1.trans r.property.2).not_ge hR₀⟩
    exact GaussFamily.isCountablyGenerated_uniformity isUniformInducing_restrictFamily
      (σ := id) fun r ↦ ⟨r, le_rfl⟩

/-- **Projective-limit ring isomorphism for the open disc.** Along any monotone family indexed by a
nonempty directed preorder (in particular, any monotone sequence) of radii in `(0, R₀)` tending to
`R₀`, the open-disc algebra is isomorphic as a ring to the subring of compatible restricted
series. -/
noncomputable def compatibleRingEquiv {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀)) :
    OnOpenDisc.subring R R₀ ≃+* GaussFamily.compatibleSubring (R := R) hmono :=
  GaussFamily.compatibleRingEquiv (fun _ ↦ mem_subring_iff_forall_isRestricted)
    (fun r ↦ r.property.1.le) hmono (cofinal_of_tendsto hρ)

/-- Each component of `compatibleRingEquiv` is closed-disc restriction at that stage. -/
@[simp]
theorem coe_compatibleRingEquiv_apply {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀)) (f : OnOpenDisc.subring R R₀) (i : ι) :
    (compatibleRingEquiv hmono hρ f : ∀ i, IsRestricted.subring (R := R) (ρ i : ℝ)) i =
      restrict (ρ i) f :=
  GaussFamily.coe_compatibleRingEquiv_apply _ (fun r ↦ r.property.1.le) hmono
    (cofinal_of_tendsto hρ) f i

/-- Restricting the open-disc series reconstructed from a compatible family `g` at stage `i`
recovers `g i`. -/
@[simp]
theorem restrict_compatibleRingEquiv_symm {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀))
    (g : GaussFamily.compatibleSubring (R := R) hmono) (i : ι) :
    restrict (ρ i) ((compatibleRingEquiv hmono hρ).symm g) = g.val i :=
  GaussFamily.restrict_compatibleRingEquiv_symm _ (fun r ↦ r.property.1.le) hmono
    (cofinal_of_tendsto hρ) g i

/-- The underlying formal power series of the open-disc element reconstructed from a compatible
family `g` agrees with `g i` at every stage `i`. -/
theorem coe_compatibleRingEquiv_symm {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀))
    (g : GaussFamily.compatibleSubring (R := R) hmono) (i : ι) :
    (((compatibleRingEquiv hmono hρ).symm g : OnOpenDisc.subring R R₀) : R⟦X⟧) =
      (g.val i : R⟦X⟧) :=
  GaussFamily.coe_compatibleRingEquiv_symm _ (fun r ↦ r.property.1.le) hmono
    (cofinal_of_tendsto hρ) g i

/-- **Family independence of the compatible-series description.** Compatible restricted-series
families along any two monotone families (indexed by nonempty directed preorders) of radii in
`(0, R₀)` tending to `R₀` define the same open-disc series if and only if they have the same
underlying formal power series. -/
theorem compatibleRingEquiv_symm_eq_iff {ι₁ ι₂ : Type*} [Preorder ι₁] [IsDirectedOrder ι₁]
    [Nonempty ι₁] [Preorder ι₂] [IsDirectedOrder ι₂] [Nonempty ι₂]
    {ρ₁ : ι₁ → Set.Ioo (0 : ℝ) R₀} {ρ₂ : ι₂ → Set.Ioo (0 : ℝ) R₀}
    (hmono₁ : Monotone fun i ↦ (ρ₁ i : ℝ)) (hρ₁ : Tendsto (fun i ↦ (ρ₁ i : ℝ)) atTop (𝓝 R₀))
    (hmono₂ : Monotone fun i ↦ (ρ₂ i : ℝ)) (hρ₂ : Tendsto (fun i ↦ (ρ₂ i : ℝ)) atTop (𝓝 R₀))
    (g₁ : GaussFamily.compatibleSubring (R := R) hmono₁)
    (g₂ : GaussFamily.compatibleSubring (R := R) hmono₂) (i₁ : ι₁) (i₂ : ι₂) :
    (compatibleRingEquiv hmono₁ hρ₁).symm g₁ = (compatibleRingEquiv hmono₂ hρ₂).symm g₂ ↔
      (g₁.val i₁ : R⟦X⟧) = (g₂.val i₂ : R⟦X⟧) :=
  GaussFamily.compatibleRingEquiv_symm_eq_iff _ (fun r ↦ r.property.1.le) hmono₁
    (cofinal_of_tendsto hρ₁) hmono₂ (cofinal_of_tendsto hρ₂) g₁ g₂ i₁ i₂

/-- **Projective-limit uniform equivalence for the open disc.** Along any monotone family indexed
by a nonempty directed preorder (in particular, any monotone sequence) of radii in `(0, R₀)` tending
to `R₀`, the open-disc algebra with its Gauss uniformity is uniformly equivalent to the closed
subring of compatible restricted series. -/
noncomputable def compatibleUniformEquiv {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀)) :
    OnOpenDisc.subring R R₀ ≃ᵤ GaussFamily.compatibleSubring (R := R) hmono :=
  GaussFamily.compatibleUniformEquiv isUniformInducing_restrictFamily hmono
    (cofinal_of_tendsto hρ)

/-- `compatibleUniformEquiv` applies on elements as `compatibleRingEquiv`. -/
@[simp]
theorem compatibleUniformEquiv_apply {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀)) (f : OnOpenDisc.subring R R₀) :
    compatibleUniformEquiv hmono hρ f = compatibleRingEquiv hmono hρ f :=
  GaussFamily.compatibleUniformEquiv_apply isUniformInducing_restrictFamily hmono
    (cofinal_of_tendsto hρ) f

/-- The inverse of `compatibleUniformEquiv` applies on elements as the inverse of
`compatibleRingEquiv`. -/
@[simp]
theorem compatibleUniformEquiv_symm_apply {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀))
    (g : GaussFamily.compatibleSubring (R := R) hmono) :
    (compatibleUniformEquiv hmono hρ).symm g = (compatibleRingEquiv hmono hρ).symm g :=
  GaussFamily.compatibleUniformEquiv_symm_apply isUniformInducing_restrictFamily hmono
    (cofinal_of_tendsto hρ) g

/-- Restriction to any smaller closed disc is uniformly continuous for the Gauss uniformities. -/
theorem uniformContinuous_restrict (r : Set.Ioo (0 : ℝ) R₀) :
    UniformContinuous (restrict (R := R) r) :=
  GaussFamily.uniformContinuous_restrict isUniformInducing_restrictFamily r

/-- Convergence on the open disc is convergence in every smaller positive-radius Gauss norm. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι}
    {f : ι → OnOpenDisc.subring R R₀} {g : OnOpenDisc.subring R R₀} :
    Tendsto f l (𝓝 g) ↔ ∀ r : Set.Ioo (0 : ℝ) R₀,
      Tendsto (fun i ↦ restrict r (f i)) l (𝓝 (restrict r g)) :=
  GaussFamily.tendsto_iff isUniformInducing_restrictFamily

/-- Convergence can be tested at any cofinal family of smaller positive radii. -/
theorem tendsto_iff_of_cofinal_radius {ι κ : Type*}
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i)
    {F : Filter κ} {f : κ → OnOpenDisc.subring R R₀} {g : OnOpenDisc.subring R R₀} :
    Tendsto f F (𝓝 g) ↔ ∀ i, Tendsto (fun j ↦ restrict (ρ i) (f j)) F (𝓝 (restrict (ρ i) g)) :=
  GaussFamily.tendsto_iff_of_cofinal_radius isUniformInducing_restrictFamily hρ

/-- Convergence on the open disc can be tested along any family of smaller positive radii tending
to `R₀`, for instance along a sequence increasing to `R₀`. -/
theorem tendsto_iff_of_tendsto {ι κ : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l (𝓝 R₀))
    {F : Filter κ} {f : κ → OnOpenDisc.subring R R₀} {g : OnOpenDisc.subring R R₀} :
    Tendsto f F (𝓝 g) ↔ ∀ i, Tendsto (fun j ↦ restrict (ρ i) (f j)) F (𝓝 (restrict (ρ i) g)) :=
  tendsto_iff_of_cofinal_radius (cofinal_of_tendsto hρ)

/-- A map into the open-disc algebra is continuous exactly when each restriction is continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → OnOpenDisc.subring R R₀} :
    Continuous f ↔ ∀ r : Set.Ioo (0 : ℝ) R₀, Continuous fun x ↦ restrict r (f x) :=
  GaussFamily.continuous_iff isUniformInducing_restrictFamily

/-- A map into the open-disc algebra is uniformly continuous exactly when each restriction is. -/
theorem uniformContinuous_iff {X : Type*} [UniformSpace X]
    {f : X → OnOpenDisc.subring R R₀} :
    UniformContinuous f ↔ ∀ r : Set.Ioo (0 : ℝ) R₀,
      UniformContinuous fun x ↦ restrict r (f x) :=
  GaussFamily.uniformContinuous_iff isUniformInducing_restrictFamily

instance : IsUniformAddGroup (OnOpenDisc.subring R R₀) :=
  GaussFamily.isUniformAddGroup isUniformInducing_restrictFamily

/-- An additive homomorphism between open-disc subrings is uniformly continuous when each target
smaller-radius Gauss norm is bounded by a multiple of some source smaller-radius Gauss norm. -/
theorem uniformContinuous_of_norm_restrict_le {S F : Type*} [NormedRing S] [IsUltrametricDist S]
    {S₀ : ℝ} [FunLike F (OnOpenDisc.subring R R₀) (OnOpenDisc.subring S S₀)]
    [AddMonoidHomClass F (OnOpenDisc.subring R R₀) (OnOpenDisc.subring S S₀)] (φ : F)
    (hφ : ∀ s : Set.Ioo (0 : ℝ) S₀, ∃ (r : Set.Ioo (0 : ℝ) R₀) (C : ℝ),
      ∀ f, ‖restrict s (φ f)‖ ≤ C * ‖restrict r f‖) :
    UniformContinuous φ :=
  GaussFamily.uniformContinuous_of_norm_restrict_le isUniformInducing_restrictFamily
    isUniformInducing_restrictFamily φ hφ

instance : IsTopologicalRing (OnOpenDisc.subring R R₀) :=
  GaussFamily.isTopologicalRing isUniformInducing_restrictFamily

/-- Coefficient scalar multiplication on open-disc series is continuous for the Gauss topology. -/
instance : ContinuousSMul R (OnOpenDisc.subring R R₀) :=
  GaussFamily.continuousSMul isUniformInducing_restrictFamily.isInducing coe_smul

/-- Any continuous algebra scalar action on `R` acts continuously on open-disc series. -/
instance {S : Type*} [CommSemiring S] [TopologicalSpace S] [Algebra S R] [ContinuousSMul S R] :
    ContinuousSMul S (OnOpenDisc.subring R R₀) :=
  IsScalarTower.continuousSMul R

/-- Polynomial truncations converge in every smaller-radius Gauss norm simultaneously. -/
theorem tendsto_polynomialHom_trunc (f : OnOpenDisc.subring R R₀) :
    Tendsto (fun n ↦ OnOpenDisc.polynomialHom (R₀ := R₀) ((f : R⟦X⟧).trunc n)) atTop (𝓝 f) :=
  GaussFamily.tendsto_polynomialHom_trunc isUniformInducing_restrictFamily _
    OnOpenDisc.coe_polynomialHom f

/-- Polynomials are dense for the topology of all smaller-radius Gauss norms. -/
theorem denseRange_polynomialHom : DenseRange (OnOpenDisc.polynomialHom (R := R) (R₀ := R₀)) :=
  GaussFamily.denseRange_polynomialHom isUniformInducing_restrictFamily _
    OnOpenDisc.coe_polynomialHom

/-- Continuous ring homomorphisms out of the open-disc algebra are determined by coefficients
and the variable. -/
theorem ringHom_ext {A : Type*} [Semiring A] [TopologicalSpace A] [T2Space A]
    {φ ψ : OnOpenDisc.subring R R₀ →+* A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hC : ∀ a, φ (OnOpenDisc.polynomialHom (Polynomial.C a)) =
      ψ (OnOpenDisc.polynomialHom (Polynomial.C a)))
    (hX : φ (OnOpenDisc.polynomialHom Polynomial.X) = ψ (OnOpenDisc.polynomialHom Polynomial.X)) :
    φ = ψ := by
  have hpol : φ.comp OnOpenDisc.polynomialHom = ψ.comp OnOpenDisc.polynomialHom :=
    Polynomial.ringHom_ext hC hX
  exact RingHom.ext (congrFun (hφ.ext_on denseRange_polynomialHom hψ
    (fun _ ⟨p, hp⟩ ↦ by
      subst hp
      exact RingHom.congr_fun hpol p)))

section PosRadius

variable [Fact (0 < R₀)]

instance : T2Space (OnOpenDisc.subring R R₀) :=
  GaussFamily.t2Space isUniformInducing_restrictFamily

/-- Each coefficient is uniformly continuous for the open-disc Gauss uniformity. -/
theorem uniformContinuous_coeff (n : ℕ) :
    UniformContinuous fun f : OnOpenDisc.subring R R₀ ↦ coeff n (f : R⟦X⟧) :=
  GaussFamily.uniformContinuous_coeff isUniformInducing_restrictFamily n

omit [Fact (0 < R₀)] in
/-- The restriction image consists exactly of families with radius-independent coefficients. -/
theorem range_restrictFamily :
    Set.range (restrictFamily (R := R) (R₀ := R₀)) =
      {g | ∀ r s : Set.Ioo (0 : ℝ) R₀, ∀ n : ℕ,
        coeff n (g r : R⟦X⟧) = coeff n (g s : R⟦X⟧)} :=
  GaussFamily.range_restrictFamily _

/-- The open-disc algebra with all smaller-radius Gauss norms is complete over complete
coefficients. -/
instance [CompleteSpace R] : CompleteSpace (OnOpenDisc.subring R R₀) :=
  GaussFamily.completeSpace isUniformInducing_restrictFamily

/-- When `0 < R₀`, no zero-neighborhood in `OnOpenDisc.subring R R₀` is bounded in the sense of
`TauCeti.Huber.IsBounded` over a nontrivial ultrametric normed coefficient ring `R` containing a
unit of norm `< 1`. -/
theorem not_isBounded_of_mem_nhds_zero [Nontrivial R] (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1)
    {U : Set (OnOpenDisc.subring R R₀)} (hU : U ∈ 𝓝 (0 : OnOpenDisc.subring R R₀)) :
    ¬ TauCeti.Huber.IsBounded U :=
  GaussFamily.not_isBounded_of_mem_nhds_zero isUniformInducing_restrictFamily.isInducing
    exists_gt hu hU

/-- **No single ring seminorm represents the open-disc Gauss topology.** When `0 < R₀` and the
nontrivial ultrametric normed coefficient ring `R` contains a unit of norm `< 1`, no ring seminorm
on `OnOpenDisc.subring R R₀` induces its Gauss topology. -/
theorem not_exists_ringSeminorm_toTopologicalSpace_eq [Nontrivial R]
    (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ p : RingSeminorm (OnOpenDisc.subring R R₀),
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace :=
  GaussFamily.not_exists_ringSeminorm_toTopologicalSpace_eq
    isUniformInducing_restrictFamily.isInducing exists_gt hu

/-- **No scalar-bounded group seminorm represents the open-disc Gauss topology.** When `0 < R₀`
and the nontrivial ultrametric normed coefficient ring `R` contains a unit of norm `< 1`, no
additive group seminorm `p` on `OnOpenDisc.subring R R₀` in which left multiplication by constant
series is bounded by `C * ‖c‖` induces the Gauss topology. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_polynomialHom_C_mul_le [Nontrivial R]
    (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ (p : AddGroupSeminorm (OnOpenDisc.subring R R₀)) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : R) (f : OnOpenDisc.subring R R₀),
        p (OnOpenDisc.polynomialHom (Polynomial.C c) * f) ≤ C * ‖c‖ * p f :=
  GaussFamily.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_mul_le
    isUniformInducing_restrictFamily.isInducing exists_gt hu (fun _ ↦ by simp)

end PosRadius

section Radius

variable {R₁ : ℝ}

/-- Restricting to a closed disc inside `R₁` after `radiusHom h` is restricting directly from
`R₀`. -/
@[simp]
theorem restrict_radiusHom (h : R₁ ≤ R₀) (r : Set.Ioo (0 : ℝ) R₁)
    (f : OnOpenDisc.subring R R₀) :
    restrict r (radiusHom h f) = restrict ⟨r, r.property.1, r.property.2.trans_le h⟩ f :=
  Subtype.ext (by simp)

/-- Radius restriction between open discs is uniformly continuous for the Gauss uniformities. -/
theorem uniformContinuous_radiusHom (h : R₁ ≤ R₀) :
    UniformContinuous (radiusHom (R := R) h) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  simp_rw [restrict_radiusHom]
  exact uniformContinuous_restrict ⟨r, r.property.1, r.property.2.trans_le h⟩

/-- Radius restriction between open discs is continuous for the Gauss topologies. -/
@[continuity]
theorem continuous_radiusHom (h : R₁ ≤ R₀) : Continuous (radiusHom (R := R) h) :=
  (uniformContinuous_radiusHom h).continuous

/-- Larger-disc series are dense in smaller-disc series for the Gauss topology. -/
theorem denseRange_radiusHom (h : R₁ ≤ R₀) : DenseRange (radiusHom (R := R) h) := by
  have hcomp : radiusHom h ∘ OnOpenDisc.polynomialHom (R := R) (R₀ := R₀) =
      OnOpenDisc.polynomialHom (R := R) (R₀ := R₁) :=
    funext (radiusHom_polynomialHom h)
  exact Dense.mono (hcomp ▸ Set.range_comp_subset_range _ _)
    (denseRange_polynomialHom (R := R) (R₀ := R₁))

/-- Restricting `ofIsRestricted f` to a smaller positive closed disc applies the closed-disc
radius restriction `restrictedRadiusHom` from `R₀` to `r`. -/
@[simp]
theorem restrict_ofIsRestricted (r : Set.Ioo (0 : ℝ) R₀)
    (f : IsRestricted.subring (R := R) R₀) :
    restrict r (ofIsRestricted f) =
      TauCeti.PowerSeries.restrictedRadiusHom r.property.1.le r.property.2.le f :=
  Subtype.ext (by simp)

/-- Including a smaller closed-disc restriction `restrict r f` back into the open disc of radius
`r` restricts `f` along `r ≤ R₀`. -/
@[simp]
theorem ofIsRestricted_restrict (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    ofIsRestricted (restrict r f) = radiusHom r.property.2.le f :=
  Subtype.ext (by simp)

/-- Open-disc radius restriction commutes with `ofIsRestricted` via `restrictedRadiusHom`. -/
theorem radiusHom_ofIsRestricted (h0 : 0 ≤ R₁) (h : R₁ ≤ R₀)
    (f : IsRestricted.subring (R := R) R₀) :
    radiusHom h (ofIsRestricted f) =
      ofIsRestricted (TauCeti.PowerSeries.restrictedRadiusHom h0 h f) :=
  Subtype.ext (by simp)

/-- Every smaller-radius Gauss norm of `ofIsRestricted f` is bounded by the Gauss norm of `f` at
`R₀`. -/
theorem norm_restrict_ofIsRestricted_le [Fact (0 < R₀)] (r : Set.Ioo (0 : ℝ) R₀)
    (f : IsRestricted.subring (R := R) R₀) :
    ‖restrict r (ofIsRestricted f)‖ ≤ ‖f‖ := by
  rw [restrict_ofIsRestricted]
  exact TauCeti.PowerSeries.norm_restrictedRadiusHom_le r.property.1.le r.property.2.le f

/-- The inclusion from the boundary closed-disc algebra into the open-disc algebra is uniformly
continuous. -/
theorem uniformContinuous_ofIsRestricted [Fact (0 < R₀)] :
    UniformContinuous (ofIsRestricted (R := R) (R₀ := R₀)) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  simp_rw [restrict_ofIsRestricted]
  exact (TauCeti.PowerSeries.lipschitzWith_restrictedRadiusHom
    r.property.1.le r.property.2.le).uniformContinuous

/-- The inclusion from the boundary closed-disc algebra into the open-disc algebra is
continuous. -/
@[continuity]
theorem continuous_ofIsRestricted [Fact (0 < R₀)] :
    Continuous (ofIsRestricted (R := R) (R₀ := R₀)) :=
  uniformContinuous_ofIsRestricted.continuous

/-- Series restricted at `R₀` are dense in series on the open disc of radius `R₀`. -/
theorem denseRange_ofIsRestricted : DenseRange (ofIsRestricted (R := R) (R₀ := R₀)) := by
  let pHom : Polynomial R → IsRestricted.subring (R := R) R₀ :=
    fun p ↦ ⟨p, isRestricted_polynomial p⟩
  have hcomp : ofIsRestricted ∘ pHom = OnOpenDisc.polynomialHom (R := R) (R₀ := R₀) :=
    funext fun p ↦ Subtype.ext (by simp [pHom])
  exact Dense.mono (hcomp ▸ Set.range_comp_subset_range _ _)
    (denseRange_polynomialHom (R := R) (R₀ := R₀))

end Radius

section Entire

/-- Restricting an entire series through an open disc to a smaller closed disc agrees with its
direct restriction from entire series. -/
@[simp]
theorem restrict_inclusion_entire (r : Set.Ioo (0 : ℝ) R₀) (f : IsEntire.subring R) :
    restrict r (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring R₀) f) =
      TauCeti.PowerSeries.IsEntire.restrict ⟨r, r.property.1⟩ f :=
  Subtype.ext (by simp)

/-- The inclusion of entire series into series on any open disc is uniformly continuous. -/
theorem uniformContinuous_inclusion_entire :
    UniformContinuous (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring (R := R) R₀)) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  simp_rw [restrict_inclusion_entire]
  exact TauCeti.PowerSeries.IsEntire.uniformContinuous_restrict ⟨r, r.property.1⟩

/-- The inclusion of entire series into series on any open disc is continuous. -/
@[continuity]
theorem continuous_inclusion_entire :
    Continuous (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring (R := R) R₀)) :=
  uniformContinuous_inclusion_entire.continuous

/-- Entire series are dense in series on any open disc. -/
theorem denseRange_inclusion_entire :
    DenseRange (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring (R := R) R₀)) := by
  refine (denseRange_polynomialHom (R := R) (R₀ := R₀)).mono ?_
  rintro _ ⟨p, rfl⟩
  exact ⟨IsEntire.polynomialHom p, Subtype.ext (by simp)⟩

end Entire

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ : ℝ} [Fact (0 < R₀)]

/-- **No scalar-bounded group seminorm represents the open-disc Gauss topology.** When `0 < R₀`
and the nontrivial ultrametric normed commutative ring `R` contains a unit of norm `< 1`, no
additive group seminorm `p` on `OnOpenDisc.subring R R₀` in which scalar multiplication is bounded
by `C * ‖c‖` induces the Gauss topology. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le [Nontrivial R]
    (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ (p : AddGroupSeminorm (OnOpenDisc.subring R R₀)) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : R) (f : OnOpenDisc.subring R R₀), p (c • f) ≤ C * ‖c‖ * p f :=
  GaussFamily.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le
    isUniformInducing_restrictFamily.isInducing exists_gt hu TauCeti.PowerSeries.OnOpenDisc.coe_smul

end NormedCommRing

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {R₀ : ℝ} [Fact (0 < R₀)]

/-- Over a nontrivially normed ultrametric field, when `0 < R₀`, no zero-neighborhood in
`OnOpenDisc.subring K R₀` is bounded in the sense of `TauCeti.Huber.IsBounded`. -/
theorem not_isBounded_of_mem_nhds_zero_of_nontriviallyNormedField
    {U : Set (OnOpenDisc.subring K R₀)} (hU : U ∈ 𝓝 (0 : OnOpenDisc.subring K R₀)) :
    ¬ TauCeti.Huber.IsBounded U :=
  GaussFamily.not_isBounded_of_mem_nhds_zero_of_nontriviallyNormedField
    (isUniformInducing_restrictFamily (R := K)).isInducing exists_gt hU

/-- Over a nontrivially normed ultrametric field, no single ring seminorm induces the open-disc
Gauss topology when `0 < R₀`. -/
theorem not_exists_ringSeminorm_toTopologicalSpace_eq_of_nontriviallyNormedField :
    ¬ ∃ p : RingSeminorm (OnOpenDisc.subring K R₀),
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace :=
  GaussFamily.not_exists_ringSeminorm_toTopologicalSpace_eq_of_nontriviallyNormedField
    (isUniformInducing_restrictFamily (R := K)).isInducing exists_gt

/-- Over a nontrivially normed ultrametric field, when `0 < R₀`, no additive group seminorm in
which scalar multiplication (equivalently, left multiplication by constant series) is bounded by
`C * ‖c‖` induces the open-disc Gauss topology. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le_of_nontriviallyNormedField :
    ¬ ∃ (p : AddGroupSeminorm (OnOpenDisc.subring K R₀)) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : K) (f : OnOpenDisc.subring K R₀), p (c • f) ≤ C * ‖c‖ * p f :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le
    ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩

/-- Over a nontrivially normed ultrametric field `K`, when `0 < R₀`, `OnOpenDisc.subring K R₀` with
its Gauss topology is not normable as a `K`-vector space. -/
theorem not_isNormableSpace : ¬ IsNormableSpace K (OnOpenDisc.subring K R₀) :=
  GaussFamily.not_isNormableSpace (isUniformInducing_restrictFamily (R := K)).isInducing exists_gt
    TauCeti.PowerSeries.OnOpenDisc.coe_smul

end NontriviallyNormedField

end TauCeti.PowerSeries.OnOpenDisc
