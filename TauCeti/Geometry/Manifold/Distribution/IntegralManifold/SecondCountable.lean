/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.WeakEmbeddedness

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import TauCeti.Topology.Bases

/-!
# Second countability of connected integral manifolds

In a second-countable finite-dimensional real boundaryless manifold, every preconnected
boundaryless integral manifold of an involutive constant-rank distribution with an injective
parametrization is second countable. Consequently, every `C^m` map into the image of such an
integral manifold factors as a `C^m` map through its intrinsic carrier without assuming second
countability of the carrier in advance.

The proof covers the ambient manifold by countably many Frobenius coordinate domains. In each
coordinate domain, the preimages of the affine slices are pairwise disjoint open plaques of the
integral carrier, and each plaque embeds openly into the finite-dimensional direction subspace.
A chain argument (`TauCeti.secondCountableTopology_of_isOpen_cover`) then shows that only
countably many plaques are reachable in the preconnected carrier.

## Main results

* `TauCeti.IsIntegralManifold.secondCountableTopology`: an injectively parametrized preconnected
  boundaryless integral manifold over a second-countable boundaryless manifold is second countable.
* `TauCeti.IsIntegralManifold.continuous_of_comp_eq_of_preconnectedSpace`: continuity of lifts
  into an injectively parametrized preconnected integral manifold over a second-countable ambient
  manifold.
* `TauCeti.IsIntegralManifold.exists_contMDiff_factor_of_preconnectedSpace`: weak embeddedness
  for injectively parametrized preconnected integral manifolds over a second-countable ambient
  manifold.
* `TauCeti.IntegralManifold.secondCountableTopology` and
  `TauCeti.IntegralManifold.exists_contMDiff_factor_of_preconnectedSpace`: corresponding results
  for packaged integral manifolds.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Lemma 19.23,
  pp. 504–505 (every connected integral manifold of an involutive distribution is second
  countable), and Theorem 19.17, p. 501 (weak embeddedness).
-/

public section

noncomputable section

open Set Function Topology TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

section Plaques

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {m : ℕ∞} [IsManifold J m N]
  {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {f : N → M}

/-- The plaque of an integral carrier cut out by one value of the transverse quotient coordinate
in a Frobenius chart. -/
private def plaqueSet (f : N → M) (Φ : PartialEquiv M E) (W : Submodule ℝ E) (q : E ⧸ W) :
    Set N :=
  {y : N | f y ∈ Φ.source ∧ (Submodule.Quotient.mk (Φ (f y)) : E ⧸ W) = q}

private theorem isOpen_plaqueSet (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m)
    (Φ : PartialEquiv M E) (hΦopen : IsOpen Φ.source)
    (hΦsmooth : ContMDiffOn I 𝓘(ℝ, E) m Φ Φ.source) (W : Submodule ℝ E)
    (hflat : ∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap = W)
    (q : E ⧸ W) : IsOpen (plaqueSet f Φ W q) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyΦ, hyq⟩
  have hstay := hf.eventually_sub_mem_of_flatChart (by exact_mod_cast hm) Φ hΦopen hΦsmooth W
    hflat hyΦ
  filter_upwards [(hΦopen.preimage hf.contMDiff.continuous).mem_nhds hyΦ, hstay] with z hzΦ hzW
  exact ⟨hzΦ, ((Submodule.Quotient.eq W).mpr hzW).trans hyq⟩

omit [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace H'] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J m N] in
private theorem pairwiseDisjoint_plaqueSet (f : N → M) (Φ : PartialEquiv M E) (W : Submodule ℝ E) :
    (univ : Set (E ⧸ W)).PairwiseDisjoint (plaqueSet f Φ W) :=
  fun _ _ _ _ hne ↦ disjoint_left.mpr fun _ h₁ h₂ ↦ hne (h₁.2.symm.trans h₂.2)

/-- On a boundaryless source manifold, an injective integral immersion maps each plaque of a
Frobenius coordinate domain openly and injectively into the direction subspace, so the plaque is
second countable. -/
private theorem secondCountableTopology_plaqueSet [IsManifold I (m : ℕ∞ω) M]
    [BoundarylessManifold J N] (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m) (hinj : Injective f)
    (Φ : PartialEquiv M E) (hΦopen : IsOpen Φ.source)
    (hΦsmooth : ContMDiffOn I 𝓘(ℝ, E) m Φ Φ.source) (W : Submodule ℝ E)
    (hflat : ∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap = W)
    (hΦinj : ∀ z ∈ Φ.source, Injective (mfderiv I 𝓘(ℝ, E) Φ z)) (q : E ⧸ W) :
    SecondCountableTopology (plaqueSet f Φ W q) := by
  rcases isEmpty_or_nonempty (plaqueSet f Φ W q) with hE | ⟨⟨y₀, hy₀⟩⟩
  · exact secondCountableTopology_of_countable_cover (U := fun _ : Empty ↦ (∅ : Set _))
      (fun _ ↦ isOpen_empty) (eq_univ_of_forall fun y ↦ hE.elim y)
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional W
  let g : plaqueSet f Φ W q → W := fun y ↦ p (Φ (f y.1) - Φ (f y₀))
  have hgval (y : plaqueSet f Φ W q) : (g y : E) = Φ (f y.1) - Φ (f y₀) := by
    have hmem : Φ (f y.1) - Φ (f y₀) ∈ W :=
      (Submodule.Quotient.eq W).mp (y.2.2.trans hy₀.2.symm)
    exact congrArg Subtype.val (hp ⟨Φ (f y.1) - Φ (f y₀), hmem⟩)
  have hgcont : Continuous g := p.continuous.comp <|
    (hΦsmooth.continuousOn.comp_continuous (hf.contMDiff.continuous.comp continuous_subtype_val)
      fun y ↦ y.2.1).sub continuous_const
  have hginj : Injective g := fun y₁ y₂ h ↦ Subtype.ext <| hinj <| Φ.injOn y₁.2.1 y₂.2.1 <|
    sub_left_injective ((hgval y₁).symm.trans ((congrArg Subtype.val h).trans (hgval y₂)))
  have hgopen : IsOpenMap g := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨y, hyU, rfl⟩
    obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.mp hU
    obtain ⟨c, hyc, hc0, _, hfc⟩ :=
      hf.exists_plaque_chart_of_flatChart Φ hΦopen hΦsmooth (by exact_mod_cast hm) W hflat
        (BoundarylessManifold.isInteriorPoint (I := J)) y.2.1 (hΦinj _ y.2.1)
    let O : Set N := c.source ∩ (plaqueSet f Φ W q ∩ U')
    have hO : IsOpen O :=
      c.open_source.inter ((isOpen_plaqueSet hf hm Φ hΦopen hΦsmooth W hflat q).inter hU')
    have hyO : y.1 ∈ O := ⟨hyc, y.2, hyU⟩
    have hcO : IsOpen ((Homeomorph.addLeft (g y)) '' (c '' O)) :=
      (Homeomorph.addLeft (g y)).isOpenMap _
        (c.toOpenPartialHomeomorph.isOpen_image_of_subset_source hO inter_subset_left)
    have hmem : g y ∈ (Homeomorph.addLeft (g y)) '' (c '' O) :=
      ⟨0, ⟨y.1, hyO, hc0⟩, add_zero (g y)⟩
    refine Filter.mem_of_superset (hcO.mem_nhds hmem) ?_
    rintro _ ⟨w, ⟨z, ⟨hzc, hzp, hzU'⟩, rfl⟩, rfl⟩
    refine ⟨⟨z, hzp⟩, hzU', Subtype.ext ?_⟩
    rw [hgval, Homeomorph.coe_addLeft, Submodule.coe_add, hgval, hfc z hzc]
    abel
  exact (IsOpenEmbedding.of_continuous_injective_isOpenMap hgcont hginj
    hgopen).isEmbedding.secondCountableTopology

end Plaques

section Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SecondCountableTopology M]
  [BoundarylessManifold I M]
  {m : ℕ∞} {r : ℕ∞ω} [IsManifold I r M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J m N]
  [BoundarylessManifold J N] [PreconnectedSpace N]
  {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {f : N → M}

/-- Every preconnected boundaryless integral manifold with injective parametrization of an
involutive `C^m` constant-rank distribution on a second-countable boundaryless `C^r` manifold
(`1 ≤ m`, `m + 1 ≤ r`) is second countable. -/
theorem IsIntegralManifold.secondCountableTopology
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    (hinj : Injective f) : SecondCountableTopology N := by
  let _ : IsManifold I 1 M :=
    .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
  let _ : IsManifold I (m : ℕ∞ω) M := .of_le (le_self_add.trans hmr)
  choose Φ W hΦopen hxΦ _ hΦsmooth hflat hΦinj using fun x : M ↦
    hinv.exists_flatChart_extend hm hmr hD (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  obtain ⟨T, hTc, hTcover⟩ := isOpen_iUnion_countable (fun x ↦ (Φ x).source) hΦopen
  have := hTc.to_subtype
  let V : (Σ x : T, E ⧸ W x.1) → Set N := fun a ↦ plaqueSet f (Φ a.1.1) (W a.1.1) a.2
  have hVo (a) : IsOpen (V a) :=
    isOpen_plaqueSet hf hm (Φ a.1.1) (hΦopen a.1.1) (hΦsmooth a.1.1) (W a.1.1) (hflat a.1.1) a.2
  have hVsc (a) : SecondCountableTopology (V a) :=
    secondCountableTopology_plaqueSet hf hm hinj (Φ a.1.1) (hΦopen a.1.1) (hΦsmooth a.1.1)
      (W a.1.1) (hflat a.1.1) (hΦinj a.1.1) a.2
  refine secondCountableTopology_of_isOpen_cover V hVo ?_ hVsc fun a ↦ ?_
  · refine eq_univ_of_forall fun y ↦ ?_
    have hy : f y ∈ ⋃ x ∈ T, (Φ x).source := hTcover ▸ mem_iUnion.mpr ⟨f y, hxΦ (f y)⟩
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion.mpr ⟨⟨⟨x, hxT⟩, Submodule.Quotient.mk (Φ x (f y))⟩, hyx, rfl⟩
  · have hsub : {b | (V a ∩ V b).Nonempty} ⊆
        ⋃ x : T, Sigma.mk x '' {q | (V a ∩ plaqueSet f (Φ x.1) (W x.1) q).Nonempty} := by
      rintro ⟨x, q⟩ hb
      exact mem_iUnion.mpr ⟨x, q, hb, rfl⟩
    refine Countable.mono hsub (countable_iUnion fun x ↦ Countable.image ?_ _)
    have := (hVsc a).to_separableSpace
    exact Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun q ↦ ((↑) : V a → N) ⁻¹' plaqueSet f (Φ x.1) (W x.1) q)
      (a := {q | (V a ∩ plaqueSet f (Φ x.1) (W x.1) q).Nonempty})
      (fun q₁ _ q₂ _ hne ↦
        (pairwiseDisjoint_plaqueSet f (Φ x.1) (W x.1) (mem_univ q₁) (mem_univ q₂) hne).preimage _)
      (fun q _ ↦ (isOpen_plaqueSet hf hm (Φ x.1) (hΦopen x.1) (hΦsmooth x.1) (W x.1)
        (hflat x.1) q).preimage continuous_subtype_val)
      (fun q ⟨y, hy, hy'⟩ ↦ ⟨⟨y, hy⟩, hy'⟩)

/-- A lift of a continuous map from a locally connected space into an injectively parametrized
preconnected boundaryless integral manifold over a second-countable boundaryless manifold is
continuous. -/
theorem IsIntegralManifold.continuous_of_comp_eq_of_preconnectedSpace
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m) (hinj : Injective f)
    (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    {P : Type*} [TopologicalSpace P] [LocallyConnectedSpace P]
    {g : P → M} {h : P → N} (hg : Continuous g) (hcomp : f ∘ h = g) : Continuous h := by
  have := hf.secondCountableTopology hm hmr hinv hD hinj
  exact hf.continuous_of_comp_eq hm hinj hmr hinv hD hg hcomp

/-- Every `C^m` map into the image of an injectively parametrized preconnected boundaryless
integral manifold over a second-countable boundaryless manifold factors as a `C^m` map through its
intrinsic carrier. -/
theorem IsIntegralManifold.exists_contMDiff_factor_of_preconnectedSpace
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m) (hinj : Injective f)
    (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Type*} [TopologicalSpace A] {K : ModelWithCorners ℝ V A}
    {P : Type*} [TopologicalSpace P] [ChartedSpace A P]
    {g : P → M} (hg : ContMDiff K I m g) (hr : range g ⊆ range f) :
    ∃ h : P → N, ContMDiff K J m h ∧ f ∘ h = g := by
  have := hf.secondCountableTopology hm hmr hinv hD hinj
  exact hf.exists_contMDiff_factor hm hinj hmr hinv hD hg hr

/-- A preconnected packaged integral manifold with injective parametrization over a
second-countable boundaryless manifold has a second-countable carrier. -/
theorem IntegralManifold.secondCountableTopology {k : ℕ}
    (L : IntegralManifold (I := I) m D k) [PreconnectedSpace L.carrier]
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D)
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    (hinj : Injective L.map) : SecondCountableTopology L.carrier :=
  L.isIntegralManifold.secondCountableTopology hm hmr hinv hD hinj

/-- Every `C^m` map into the image of an injectively parametrized preconnected packaged integral
manifold over a second-countable boundaryless manifold factors as a `C^m` map through its
carrier. -/
theorem IntegralManifold.exists_contMDiff_factor_of_preconnectedSpace {k : ℕ}
    (L : IntegralManifold (I := I) m D k) [PreconnectedSpace L.carrier]
    (hm : 1 ≤ m) (hinj : Injective L.map) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D)
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Type*} [TopologicalSpace A] {K : ModelWithCorners ℝ V A}
    {P : Type*} [TopologicalSpace P] [ChartedSpace A P]
    {g : P → M} (hg : ContMDiff K I m g) (hr : range g ⊆ range L.map) :
    ∃ h : P → L.carrier, ContMDiff K (𝓡 k) m h ∧ L.map ∘ h = g :=
  L.isIntegralManifold.exists_contMDiff_factor_of_preconnectedSpace hm hinj hmr hinv hD hg hr

end Global

end TauCeti
