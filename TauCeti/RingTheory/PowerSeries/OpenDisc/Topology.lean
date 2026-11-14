/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.Basic
public import TauCeti.RingTheory.PowerSeries.GaussFamily

/-!
# The Gauss topology on series on an open disc

For an ultrametric normed ring `R` and a positive radius `R₀`, the algebra of series on the
open disc carries the topology of the Gauss norms at all radii `0 < r < R₀`. Convergence is
convergence in each of these norms, rather than convergence of individual coefficients.
The resulting uniform ring is Hausdorff, has a countably generated uniformity (hence is
metrizable), and is complete when `R` is complete.

Restriction embeds the algebra into the product of the smaller closed-disc algebras. Its
image consists of the families with the same formal coefficients at every radius. Along any
monotone family (in particular, any countable sequence) of radii in `(0, R₀)` tending to `R₀`,
the open-disc algebra is isomorphic as a ring and as a uniform space to the closed subring of
compatible restricted series, and both the induced Gauss uniformity and this compatible-series
description are independent of the chosen sequence. Over a nontrivial ultrametric normed ring
with a unit of norm `< 1` (in particular, over any nontrivially normed ultrametric field), no
single ring seminorm or scalar-bounded additive group seminorm represents this topology when
`0 < R₀`. These are specializations of the Gauss topology of a family of radii in
`TauCeti.RingTheory.PowerSeries.GaussFamily`.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.uniformSpace`: the Gauss uniformity on
  `PowerSeries.OnOpenDisc.subring R R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.restrictSubfamily`: closed-disc restriction along an arbitrary
  subfamily of radii in `(0, R₀)`.
* `TauCeti.PowerSeries.OnOpenDisc.radiusSeq`: the canonical strictly increasing sequence of radii
  `(1 - (n + 2)⁻¹) * R₀` exhausting `(0, R₀)` when `0 < R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.compatibleRingEquiv` and
  `TauCeti.PowerSeries.OnOpenDisc.compatibleUniformEquiv`: ring and uniform equivalences with the
  subring of compatible restricted series along any monotone family of radii tending to `R₀`.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.tendsto_iff` and
  `TauCeti.PowerSeries.OnOpenDisc.tendsto_iff_of_tendsto`: convergence on the open disc, tested at
  all radii in `(0, R₀)` or along any family tending to `R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.uniformSpace_eq_comap_of_tendsto` and
  `TauCeti.PowerSeries.OnOpenDisc.comap_restrictSubfamily_eq_of_tendsto`: any family of radii in
  `(0, R₀)` tending to `R₀` induces the open-disc Gauss uniformity, independently of the chosen
  sequence or family.
* `TauCeti.PowerSeries.OnOpenDisc.compatibleRingEquiv_symm_eq_iff`: independence of the monotone
  sequence in the compatible-series description.
* `TauCeti.PowerSeries.OnOpenDisc.not_exists_ringSeminorm` and
  `TauCeti.PowerSeries.OnOpenDisc.not_exists_addGroupSeminorm_polynomialHom_C_mul_le`: when
  `0 < R₀`, no single ring seminorm or scalar-bounded additive group seminorm represents the
  open-disc Gauss topology over a nontrivial ultrametric normed ring with a unit of norm `< 1`
  (with field specializations `not_exists_ringSeminorm_of_nontriviallyNormedField` and
  `not_exists_addGroupSeminorm_polynomialHom_C_mul_le_of_nontriviallyNormedField`).
* Instances: `IsUniformAddGroup`, `IsTopologicalRing`, `Filter.IsCountablyGenerated` on the
  uniformity `𝓤 (OnOpenDisc.subring R R₀)`, and (when `0 < R₀`) `T2Space` and `CompleteSpace`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter PowerSeries
open scoped Topology Uniformity

namespace TauCeti.PowerSeries.OnOpenDisc

-- Supply the positivity witness used by the Gauss-norm instances on each closed disc.
local instance radius_pos {R₀ : ℝ} (r : Set.Ioo (0 : ℝ) R₀) : Fact (0 < (r : ℝ)) := ⟨r.2.1⟩

section Radii

variable {R₀ : ℝ}

/-- Any family of radii in `(0, R₀)` tending to `R₀` along a nontrivial filter dominates every
radius in `(0, R₀)`. -/
theorem cofinal_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l (𝓝 R₀)) :
    ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i :=
  fun r ↦ (hρ.eventually (Ici_mem_nhds r.2.2)).exists

private theorem exists_gt_radius (r : Set.Ioo (0 : ℝ) R₀) :
    ∃ s : Set.Ioo (0 : ℝ) R₀, (r : ℝ) < s :=
  ⟨⟨((r : ℝ) + R₀) / 2, by linarith [r.2.1, r.2.2], by linarith [r.2.2]⟩, by linarith [r.2.2]⟩

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
    ⟨fun h r ↦ h r r.2.1 r.2.2, fun h r hr hrR ↦ h ⟨r, hr, hrR⟩⟩

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

/-- Along any family of radii in `(0, R₀)` tending to `R₀`, the image of `restrictSubfamily`
consists of families with index-independent formal coefficients. -/
theorem range_restrictSubfamily_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l (𝓝 R₀)) :
    Set.range (restrictSubfamily (R := R) ρ) =
      {g | ∀ i j : ι, ∀ n : ℕ, coeff n (g i : R⟦X⟧) = coeff n (g j : R⟦X⟧)} :=
  GaussFamily.range_restrictSubfamily _ (fun r ↦ r.2.1.le) (cofinal_of_tendsto hρ)

/-- Along any family of radii in `(0, R₀)` tending to `R₀`, the image of `restrictSubfamily` is
closed in the product of closed-disc algebras. -/
theorem isClosed_range_restrictSubfamily_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l (𝓝 R₀)) :
    IsClosed (Set.range (restrictSubfamily (R := R) ρ)) :=
  GaussFamily.isClosed_range_restrictSubfamily _ (fun r ↦ r.2.1.le) (cofinal_of_tendsto hρ)

/-- The uniformity generated by all smaller positive-radius Gauss norms. -/
noncomputable instance uniformSpace : UniformSpace (OnOpenDisc.subring R R₀) :=
  GaussFamily.uniformSpace fun _ ↦ mem_subring_iff_forall_isRestricted

/-- The Gauss uniformity is induced by the family of closed-disc restrictions. -/
theorem isUniformInducing_restrictFamily :
    IsUniformInducing (restrictFamily (R := R) (R₀ := R₀)) :=
  GaussFamily.isUniformInducing_restrictFamily_uniformSpace _

/-- Restriction along any family of radii in `(0, R₀)` tending to `R₀` is uniformly inducing. -/
theorem isUniformInducing_restrictSubfamily_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l (𝓝 R₀)) :
    IsUniformInducing (restrictSubfamily (R := R) ρ) :=
  GaussFamily.isUniformInducing_restrictSubfamily isUniformInducing_restrictFamily
    (cofinal_of_tendsto hρ)

/-- Restriction along any family of radii in `(0, R₀)` tending to `R₀` along a nontrivial filter
is a uniform embedding. -/
theorem isUniformEmbedding_restrictSubfamily_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l (𝓝 R₀)) :
    IsUniformEmbedding (restrictSubfamily (R := R) ρ) :=
  have := Filter.nonempty_of_neBot l
  GaussFamily.isUniformEmbedding_restrictSubfamily isUniformInducing_restrictFamily
    (cofinal_of_tendsto hρ)

/-- Any cofinal family of smaller positive radii induces the open-disc Gauss uniformity. -/
theorem uniformSpace_eq_comap_of_cofinal_radius {ι : Type*} {ρ : ι → Set.Ioo (0 : ℝ) R₀}
    (hρ : ∀ r : Set.Ioo (0 : ℝ) R₀, ∃ i, (r : ℝ) ≤ ρ i) :
    UniformSpace.comap (restrictSubfamily (R := R) ρ)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ i : ℝ)))) =
      uniformSpace :=
  GaussFamily.uniformSpace_eq_comap_of_cofinal_radius _ hρ

/-- Any family of radii in `(0, R₀)` tending to `R₀` induces the open-disc Gauss uniformity. -/
theorem uniformSpace_eq_comap_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l (𝓝 R₀)) :
    UniformSpace.comap (restrictSubfamily (R := R) ρ)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ i : ℝ)))) =
      uniformSpace :=
  uniformSpace_eq_comap_of_cofinal_radius (cofinal_of_tendsto hρ)

/-- **Sequence independence of the open-disc Gauss uniformity.** Any two families of radii in
`(0, R₀)` tending to `R₀` induce the exact same uniformity on `OnOpenDisc.subring R R₀`. -/
theorem comap_restrictSubfamily_eq_of_tendsto {ι₁ ι₂ : Type*} {l₁ : Filter ι₁} {l₂ : Filter ι₂}
    [l₁.NeBot] [l₂.NeBot] {ρ₁ : ι₁ → Set.Ioo (0 : ℝ) R₀} {ρ₂ : ι₂ → Set.Ioo (0 : ℝ) R₀}
    (hρ₁ : Tendsto (fun i ↦ (ρ₁ i : ℝ)) l₁ (𝓝 R₀))
    (hρ₂ : Tendsto (fun i ↦ (ρ₂ i : ℝ)) l₂ (𝓝 R₀)) :
    UniformSpace.comap (restrictSubfamily (R := R) ρ₁)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ₁ i : ℝ)))) =
    UniformSpace.comap (restrictSubfamily (R := R) ρ₂)
      (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ₂ i : ℝ)))) :=
  GaussFamily.comap_restrictSubfamily_eq _ (cofinal_of_tendsto hρ₁) (cofinal_of_tendsto hρ₂)

/-- The Gauss uniformity on `OnOpenDisc.subring R R₀` is countably generated (and therefore
metrizable when `0 < R₀`). -/
instance : (𝓤 (OnOpenDisc.subring R R₀)).IsCountablyGenerated := by
  rcases lt_or_ge 0 R₀ with hR₀ | hR₀
  · have : Fact (0 < R₀) := ⟨hR₀⟩
    exact GaussFamily.isCountablyGenerated_uniformity isUniformInducing_restrictFamily
      (cofinal_of_tendsto (tendsto_radiusSeq R₀))
  · have : IsEmpty (Set.Ioo (0 : ℝ) R₀) := ⟨fun r ↦ (r.2.1.trans r.2.2).not_ge hR₀⟩
    exact GaussFamily.isCountablyGenerated_uniformity isUniformInducing_restrictFamily
      (σ := id) fun r ↦ ⟨r, le_rfl⟩

/-- **Projective-limit ring isomorphism for the open disc.** Along any monotone family (in
particular, any increasing sequence) of radii in `(0, R₀)` tending to `R₀`, the open-disc algebra
is isomorphic as a ring to the subring of compatible restricted series. -/
noncomputable def compatibleRingEquiv {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀)) :
    OnOpenDisc.subring R R₀ ≃+* GaussFamily.compatibleSubring (R := R) hmono :=
  GaussFamily.compatibleRingEquiv (fun _ ↦ mem_subring_iff_forall_isRestricted) hmono
    (cofinal_of_tendsto hρ)

/-- Each component of `compatibleRingEquiv` is closed-disc restriction at that stage. -/
@[simp]
theorem coe_compatibleRingEquiv_apply {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀)) (f : OnOpenDisc.subring R R₀) (i : ι) :
    (compatibleRingEquiv hmono hρ f : ∀ i, IsRestricted.subring (R := R) (ρ i : ℝ)) i =
      restrict (ρ i) f :=
  GaussFamily.coe_compatibleRingEquiv_apply _ hmono (cofinal_of_tendsto hρ) f i

/-- Restricting the open-disc series reconstructed from a compatible family `g` at stage `i`
recovers `g i`. -/
@[simp]
theorem restrict_symm_compatibleRingEquiv {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀))
    (g : GaussFamily.compatibleSubring (R := R) hmono) (i : ι) :
    restrict (ρ i) ((compatibleRingEquiv hmono hρ).symm g) = g.1 i :=
  GaussFamily.restrict_symm_compatibleRingEquiv _ hmono (cofinal_of_tendsto hρ) g i

/-- The underlying formal power series of the open-disc element reconstructed from a compatible
family `g` agrees with `g i` at every stage `i`. -/
theorem coe_symm_compatibleRingEquiv {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {ρ : ι → Set.Ioo (0 : ℝ) R₀} (hmono : Monotone fun i ↦ (ρ i : ℝ))
    (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) atTop (𝓝 R₀))
    (g : GaussFamily.compatibleSubring (R := R) hmono) (i : ι) :
    (((compatibleRingEquiv hmono hρ).symm g : OnOpenDisc.subring R R₀) : R⟦X⟧) =
      (g.1 i : R⟦X⟧) :=
  GaussFamily.coe_symm_compatibleRingEquiv _ hmono (cofinal_of_tendsto hρ) g i

/-- **Sequence independence of the compatible-series description.** Compatible restricted-series
families along any two monotone families of radii in `(0, R₀)` tending to `R₀` define the same
open-disc series if and only if they have the same underlying formal power series. -/
theorem compatibleRingEquiv_symm_eq_iff {ι₁ ι₂ : Type*} [Preorder ι₁] [IsDirectedOrder ι₁]
    [Nonempty ι₁] [Preorder ι₂] [IsDirectedOrder ι₂] [Nonempty ι₂]
    {ρ₁ : ι₁ → Set.Ioo (0 : ℝ) R₀} {ρ₂ : ι₂ → Set.Ioo (0 : ℝ) R₀}
    (hmono₁ : Monotone fun i ↦ (ρ₁ i : ℝ)) (hρ₁ : Tendsto (fun i ↦ (ρ₁ i : ℝ)) atTop (𝓝 R₀))
    (hmono₂ : Monotone fun i ↦ (ρ₂ i : ℝ)) (hρ₂ : Tendsto (fun i ↦ (ρ₂ i : ℝ)) atTop (𝓝 R₀))
    (g₁ : GaussFamily.compatibleSubring (R := R) hmono₁)
    (g₂ : GaussFamily.compatibleSubring (R := R) hmono₂) (i₁ : ι₁) (i₂ : ι₂) :
    (compatibleRingEquiv hmono₁ hρ₁).symm g₁ = (compatibleRingEquiv hmono₂ hρ₂).symm g₂ ↔
      (g₁.1 i₁ : R⟦X⟧) = (g₂.1 i₂ : R⟦X⟧) :=
  GaussFamily.compatibleRingEquiv_symm_eq_iff _ hmono₁ (cofinal_of_tendsto hρ₁)
    hmono₂ (cofinal_of_tendsto hρ₂) g₁ g₂ i₁ i₂

/-- **Projective-limit uniform equivalence for the open disc.** Along any monotone family (in
particular, any increasing sequence) of radii in `(0, R₀)` tending to `R₀`, the open-disc algebra
with its Gauss uniformity is uniformly equivalent to the closed subring of compatible restricted
series. -/
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

instance : IsTopologicalRing (OnOpenDisc.subring R R₀) :=
  GaussFamily.isTopologicalRing isUniformInducing_restrictFamily

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

variable [Fact (0 < R₀)]

-- The radii below a positive boundary form a nonempty family.
local instance : Nonempty (Set.Ioo (0 : ℝ) R₀) :=
  Set.nonempty_Ioo_subtype Fact.out

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

/-- **No single ring seminorm represents the open-disc Gauss topology.** When `0 < R₀` and the
nontrivial ultrametric normed coefficient ring `R` contains a unit of norm `< 1`, no ring seminorm
on `OnOpenDisc.subring R R₀` induces its Gauss topology. -/
theorem not_exists_ringSeminorm [Nontrivial R] (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ p : RingSeminorm (OnOpenDisc.subring R R₀),
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace :=
  GaussFamily.not_exists_ringSeminorm isUniformInducing_restrictFamily exists_gt_radius hu

/-- **No scalar-bounded group seminorm represents the open-disc Gauss topology.** When `0 < R₀`
and the nontrivial ultrametric normed coefficient ring `R` contains a unit of norm `< 1`, no
additive group seminorm `p` on `OnOpenDisc.subring R R₀` in which left multiplication by constant
series is bounded by `C * ‖c‖` induces the Gauss topology. -/
theorem not_exists_addGroupSeminorm_polynomialHom_C_mul_le [Nontrivial R]
    (hu : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ (p : AddGroupSeminorm (OnOpenDisc.subring R R₀)) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : R) (f : OnOpenDisc.subring R R₀),
        p (OnOpenDisc.polynomialHom (Polynomial.C c) * f) ≤ C * ‖c‖ * p f := by
  rintro ⟨p, C, htop, hsmul⟩
  refine GaussFamily.not_exists_addGroupSeminorm_constHom_mul_le
    isUniformInducing_restrictFamily exists_gt_radius hu ⟨p, C, htop, fun c f ↦ ?_⟩
  have hC : GaussFamily.constHom (fun _ ↦ mem_subring_iff_forall_isRestricted) c =
      OnOpenDisc.polynomialHom (R₀ := R₀) (Polynomial.C c) := Subtype.ext (by simp)
  rw [hC]
  exact hsmul c f

end NormedRing

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {R₀ : ℝ} [Fact (0 < R₀)]

/-- Over a nontrivially normed ultrametric field, no single ring seminorm induces the open-disc
Gauss topology when `0 < R₀`. -/
theorem not_exists_ringSeminorm_of_nontriviallyNormedField :
    ¬ ∃ p : RingSeminorm (OnOpenDisc.subring K R₀),
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_ringSeminorm ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩

/-- Over a nontrivially normed ultrametric field, no additive group seminorm in which left
multiplication by constants is bounded by `C * ‖c‖` (in particular, no Banach-space norm) induces
the open-disc Gauss topology when `0 < R₀`. -/
theorem not_exists_addGroupSeminorm_polynomialHom_C_mul_le_of_nontriviallyNormedField :
    ¬ ∃ (p : AddGroupSeminorm (OnOpenDisc.subring K R₀)) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : K) (f : OnOpenDisc.subring K R₀),
        p (OnOpenDisc.polynomialHom (Polynomial.C c) * f) ≤ C * ‖c‖ * p f :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_addGroupSeminorm_polynomialHom_C_mul_le ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩

end NontriviallyNormedField

end TauCeti.PowerSeries.OnOpenDisc
