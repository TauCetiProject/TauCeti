/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Riemannian volume under finite quotient coverings

Let a finite group `G` act on a Riemannian manifold `M`, and let `q : M → N` be a quotient
covering map for this action (`IsQuotientCoveringMap q G`): the fibres of `q` are the `G`-orbits
and every point has a neighbourhood disjoint from its nontrivial translates. This is the situation
of the orbit projection `M → M / G` of a free action of a finite group, for instance by
isometries of a closed manifold. If `q` is a local isometry onto a Riemannian metric on `N`, then
it pushes the Riemannian volume of `M` forward to `|G|` times the Riemannian volume of `N`:

`q_* vol_M = |G| • vol_N`.

So `vol_M (q⁻¹ B) = |G| vol_N B` for measurable `B`, and pulling back along `q` multiplies
integrals by the covering degree `|G|`: `∫ f ∘ q = |G| ∫ f`, and `Lᵖ` norms by `|G| ^ (1/p)`. In
particular `|G| ^ (-1/2) q^*` is an isometry from `L²(N)` to `L²(M)`. These are the
normalizations used to transplant eigenfunctions of the Laplacian between the quotients of one
manifold by almost-conjugate subgroups.

The proof is local on `N`. Near any point, `q⁻¹ D` of a small set `D` is the disjoint union of
the `|G|` translates of one sheet, and on each sheet `q` is an injective local isometry, hence
preserves volume (`TauCeti.riemannianVolume_image_of_inner_mfderiv`). Only the tangent maps of
`q` are required to preserve the inner products; no separate hypothesis that `G` acts by
isometries is needed.

## Main results

* `IsQuotientCoveringMap.map_riemannianVolume`: `q_* vol_M = |G| • vol_N`.
* `IsQuotientCoveringMap.riemannianVolume_preimage`: `vol_M (q⁻¹ B) = |G| vol_N B`.
* `IsQuotientCoveringMap.lintegral_comp_riemannianVolume`,
  `IsQuotientCoveringMap.integral_comp_riemannianVolume`: `∫ f ∘ q = |G| ∫ f`.
* `IsQuotientCoveringMap.eLpNorm_comp_riemannianVolume`: `‖f ∘ q‖_p = |G| ^ (1/p) ‖f‖_p`.

## References

* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Lemma 16, p. 159.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (Riemannian coverings and the Riemannian density).
-/

public section

open Bundle Function MeasureTheory Set TauCeti
open scoped ENNReal InnerProductSpace Manifold Pointwise

noncomputable section

namespace IsQuotientCoveringMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [HereditarilyLindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [MeasurableSpace N] [BorelSpace N] [LindelofSpace N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]
  {G : Type*} [Group G] [MulAction G M] [Finite G] {q : M → N}

/-- If `q` is injective on a measurable set `V` and `D ⊆ q '' V` is measurable, then `q⁻¹ D` is
the disjoint union of the `|G|` translates of `V ∩ q⁻¹ D`, each of which `q` maps isometrically
onto `D`. -/
private theorem riemannianVolume_preimage_of_subset_image (hq : IsQuotientCoveringMap q G)
    (hd : MDifferentiable I I' q)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' q x v, mfderiv I I' q x w⟫_ℝ = ⟪v, w⟫_ℝ)
    {V : Set M} (hVm : MeasurableSet V) (hV : InjOn q V) {D : Set N} (hD : MeasurableSet D)
    (hDV : D ⊆ q '' V) :
    riemannianVolume I M (q ⁻¹' D) = Nat.card G * riemannianVolume I' N D := by
  have := hq.isCancelSMul
  set A := V ∩ q ⁻¹' D
  have hA : MeasurableSet A := hVm.inter (hq.continuous.measurable hD)
  have hsmul (g : G) : MeasurableSet (g • A) := by
    rw [← preimage_smul_inv]
    exact hA.preimage (hq.continuous_const_smul g⁻¹).measurable
  have hunion : q ⁻¹' D = ⋃ g : G, g • A := by
    ext y
    simp only [mem_preimage, mem_iUnion, mem_smul_set]
    refine ⟨fun hy ↦ ?_, ?_⟩
    · obtain ⟨a, ha, hay⟩ := hDV hy
      obtain ⟨g, rfl⟩ := hq.apply_eq_iff_mem_orbit.1 hay.symm
      exact ⟨g, a, ⟨ha, by rwa [mem_preimage, hay]⟩, rfl⟩
    · rintro ⟨g, a, ⟨-, ha⟩, rfl⟩
      rwa [hq.map_smul]
  have hdisj : Pairwise (Disjoint on fun g : G ↦ g • A) := by
    intro g h hgh
    refine disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    replace hab : h • b = g • a := hab
    obtain rfl : b = a := hV hb.1 ha.1 (by rw [← hq.map_smul h, hab, hq.map_smul])
    exact hgh (IsCancelSMul.right_cancel _ _ _ hab).symm
  have hpiece (g : G) : riemannianVolume I M (g • A) = riemannianVolume I' N D := by
    have himage : q '' (g • A) = D := by
      rw [← image_smul, image_image]
      simp only [hq.map_smul]
      rw [image_inter_preimage, inter_eq_right.2 hDV]
    conv_rhs => rw [← himage]
    refine (riemannianVolume_image_of_inner_mfderiv (hsmul g) ?_
      (fun t _ ht ↦ hq.isLocalHomeomorph.measurableSet_image ht) (fun x _ ↦ hd x)
      fun x _ ↦ hinner x).symm
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    simp only [hq.map_smul] at hab
    rw [hV ha.1 hb.1 hab]
  rw [hunion, measure_iUnion hdisj hsmul, tsum_congr hpiece, ENNReal.tsum_const,
    ENat.card_eq_coe_natCard, ENat.toENNReal_coe]

/-- **Riemannian volume under a finite quotient covering.** If `q : M → N` is a quotient covering
map for an action of a finite group `G` and a local isometry, then it pushes the Riemannian volume
of `M` forward to `|G|` times the Riemannian volume of `N`. -/
theorem map_riemannianVolume (hq : IsQuotientCoveringMap q G) (hd : MDifferentiable I I' q)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' q x v, mfderiv I I' q x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    (riemannianVolume I M).map q = (Nat.card G : ℝ≥0∞) • riemannianVolume I' N := by
  -- `q` is injective on a neighbourhood `U x` of each point disjoint from its translates, and the
  -- open sets `q '' interior (U x)` cover `N`; compare the two measures on each of them.
  choose U hU hUdisj using hq.disjoint
  have hinj (x : M) : InjOn q (U x) := by
    intro a ha b hb hab
    obtain ⟨g, rfl⟩ := hq.apply_eq_iff_mem_orbit.1 hab.symm
    obtain rfl := hUdisj x g ⟨_, ⟨a, ha, rfl⟩, hb⟩
    simp
  obtain ⟨T, hTc, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x ↦ interior (U x))
    fun x ↦ interior_mem_nhds.2 (hU x)
  have hopen := hq.isOpenQuotientMap.isOpenMap
  refine Measure.ext_of_biUnion_eq_univ (s := fun x ↦ q '' interior (U x)) hTc
    (by rw [← image_iUnion₂, hcover, image_univ, hq.surjective.range_eq]) fun x _ ↦ ?_
  ext D hD
  have hDU : MeasurableSet (D ∩ q '' interior (U x)) :=
    hD.inter (hopen _ isOpen_interior).measurableSet
  rw [Measure.restrict_apply hD, Measure.restrict_apply hD,
    Measure.map_apply hq.continuous.measurable hDU, smul_apply, smul_eq_mul]
  exact riemannianVolume_preimage_of_subset_image hq hd hinner isOpen_interior.measurableSet
    ((hinj x).mono interior_subset) hDU inter_subset_right

/-- The preimage of a measurable set under a finite quotient covering map which is a local
isometry has `|G|` times its Riemannian volume. -/
theorem riemannianVolume_preimage (hq : IsQuotientCoveringMap q G) (hd : MDifferentiable I I' q)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' q x v, mfderiv I I' q x w⟫_ℝ = ⟪v, w⟫_ℝ)
    {B : Set N} (hB : MeasurableSet B) :
    riemannianVolume I M (q ⁻¹' B) = Nat.card G * riemannianVolume I' N B := by
  rw [← Measure.map_apply hq.continuous.measurable hB, hq.map_riemannianVolume hd hinner,
    smul_apply, smul_eq_mul]

/-- Pulling a nonnegative function back along a finite quotient covering map which is a local
isometry multiplies its integral by `|G|`. -/
theorem lintegral_comp_riemannianVolume (hq : IsQuotientCoveringMap q G)
    (hd : MDifferentiable I I' q)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' q x v, mfderiv I I' q x w⟫_ℝ = ⟪v, w⟫_ℝ)
    {f : N → ℝ≥0∞} (hf : AEMeasurable f (riemannianVolume I' N)) :
    ∫⁻ x, f (q x) ∂riemannianVolume I M = Nat.card G * ∫⁻ y, f y ∂riemannianVolume I' N := by
  have h := hq.map_riemannianVolume hd hinner
  rw [← lintegral_map' (by rw [h]; exact hf.smul_measure _) hq.continuous.aemeasurable, h,
    lintegral_smul_measure, smul_eq_mul]

/-- Pulling a function back along a finite quotient covering map which is a local isometry
multiplies its Bochner integral by `|G|`. -/
theorem integral_comp_riemannianVolume (hq : IsQuotientCoveringMap q G)
    (hd : MDifferentiable I I' q)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' q x v, mfderiv I I' q x w⟫_ℝ = ⟪v, w⟫_ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : N → F}
    (hf : AEStronglyMeasurable f (riemannianVolume I' N)) :
    ∫ x, f (q x) ∂riemannianVolume I M = Nat.card G • ∫ y, f y ∂riemannianVolume I' N := by
  have h := hq.map_riemannianVolume hd hinner
  rw [← integral_map hq.continuous.aemeasurable (by rw [h]; exact hf.smul_measure _), h,
    integral_smul_measure, ENNReal.toReal_natCast, Nat.cast_smul_eq_nsmul]

/-- Pulling a function back along a finite quotient covering map which is a local isometry
multiplies its `Lᵖ` seminorm by `|G| ^ (1/p)`. For `p = 2` this says that `|G| ^ (-1/2) q^*` is
an isometry from `L²(N)` to `L²(M)`. -/
theorem eLpNorm_comp_riemannianVolume (hq : IsQuotientCoveringMap q G)
    (hd : MDifferentiable I I' q)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' q x v, mfderiv I I' q x w⟫_ℝ = ⟪v, w⟫_ℝ)
    {F : Type*} [NormedAddCommGroup F] {f : N → F}
    (hf : AEStronglyMeasurable f (riemannianVolume I' N)) (p : ℝ≥0∞) :
    eLpNorm (f ∘ q) p (riemannianVolume I M) =
      (Nat.card G : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm f p (riemannianVolume I' N) := by
  have h := hq.map_riemannianVolume hd hinner
  rw [← eLpNorm_map_measure (by rw [h]; exact hf.smul_measure _) hq.continuous.aemeasurable, h,
    eLpNorm_smul_measure_of_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne'), smul_eq_mul]

end IsQuotientCoveringMap
