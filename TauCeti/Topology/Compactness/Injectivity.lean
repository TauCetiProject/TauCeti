/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.SeparatedMap

/-!
# Compactness and local injectivity

For a continuous locally injective map to a Hausdorff space, the distinct equal-image pairs
form a closed set. Restriction to a compact set therefore gives a compact set of such pairs;
local injectivity is needed only in the relative topology.

Injectivity on a compact set persists along an arbitrary parameter filter when the family
converges jointly along that filter and the compact set, and is eventually locally injective
on relative neighbourhoods. A specialization handles locally injective total maps retaining
the parameter, with joint continuity relative to the parameter and domain sets.

## Main results

* `IsLocallyInjective.isClosed_setOf_apply_eq_and_ne`: closedness of distinct equal-image pairs.
* `IsCompact.isCompact_setOf_apply_eq_and_ne`: compactness after restriction to a compact set.
* `IsCompact.eventually_injOn`: persistence of injectivity along a parameter filter.
* `IsCompact.eventually_injOn_of_injOn_prodMk`: persistence for a locally injective total map.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter
open scoped Topology

/-- For a continuous locally injective map into a Hausdorff space, the set of distinct
pairs with the same image is closed. No separation assumption on the domain is needed. -/
theorem IsLocallyInjective.isClosed_setOf_apply_eq_and_ne
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {f : E → X} (hinj : IsLocallyInjective f) (hf : Continuous f) :
    IsClosed {z : E × E | f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  have heq : IsClosed {z : E × E | f z.1 = f z.2} :=
    isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)
  have hdiag := isLocallyInjective_iff_isOpen_diagonal.mp hinj
  -- The pullback diagonal is the equality locus inside the equal-image subtype.
  have hclosed : IsClosed {z : {z : E × E // f z.1 = f z.2} | z.1.1 ≠ z.1.2} :=
    hdiag.isClosed_compl
  convert heq.isClosedMap_subtype_val _ hclosed using 1
  ext z
  simp [and_comm]

namespace IsCompact

/-- For a map continuous on a compact set and locally injective in its relative topology,
the distinct equal-image pairs in that set form a compact set. The target is Hausdorff. -/
theorem isCompact_setOf_apply_eq_and_ne
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {f : E → X} (hf : ContinuousOn f K)
    (hinj : ∀ x ∈ K, ∃ U ∈ 𝓝[K] x, InjOn f U) :
    IsCompact {z : E × E | z.1 ∈ K ∧ z.2 ∈ K ∧ f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  have hc : Continuous (K.domRestrict f) := continuousOn_iff_continuous_domRestrict.mp hf
  have hi : IsLocallyInjective (K.domRestrict f) := by
    rw [isLocallyInjective_iff_nhds]
    intro x
    obtain ⟨U, hU, hUi⟩ := hinj x x.property
    exact ⟨Subtype.val ⁻¹' U, preimage_coe_mem_nhds_subtype.mpr hU,
      fun _ hv _ hw he ↦ Subtype.ext (hUi hv hw he)⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcompact := (hi.isClosed_setOf_apply_eq_and_ne hc).isCompact.image
    (continuous_subtype_val.prodMap continuous_subtype_val)
  convert hcompact using 1
  ext z
  constructor
  · rintro ⟨hv, hw, he, hne⟩
    exact ⟨(⟨z.1, hv⟩, ⟨z.2, hw⟩),
      ⟨he, fun h ↦ hne (congrArg Subtype.val h)⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.1.property, w.2.property, hw.1,
      fun h ↦ hw.2 (Subtype.ext h)⟩

/-- Injectivity on a compact set persists along a parameter filter if the family converges
jointly to an injective map into a Hausdorff space and is eventually injective on a relative
neighbourhood of each point. The parameter type needs no topology. -/
theorem eventually_injOn
    {P E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {l : Filter P} {f : P → E → X} {g : E → X} {K : Set E}
    (hK : IsCompact K) (hinj : InjOn g K)
    (hcont : ∀ v ∈ K, Tendsto (fun z : P × E ↦ f z.1 z.2) (l ×ˢ 𝓝[K] v) (𝓝 (g v)))
    (hlocal : ∀ v ∈ K, ∃ V ∈ 𝓝[K] v, ∀ᶠ q in l, InjOn (f q) V) :
    ∀ᶠ q in l, InjOn (f q) K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc (v : K) : Tendsto (fun z : P × K ↦ f z.1 z.2)
      (l ×ˢ 𝓝 v) (𝓝 (g v)) := by
    have hv : Tendsto ((↑) : K → E) (𝓝 v) (𝓝[K] (v : E)) := by
      rw [← map_nhds_subtype_val v]
      exact tendsto_map
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using
      (hcont v v.property).comp ((tendsto_id : Tendsto (id : P → P) l l).prodMap hv)
  have hpair (v w : K) : ∀ᶠ t : P × (K × K) in l ×ˢ 𝓝 (v, w),
      f t.1 t.2.1 = f t.1 t.2.2 → t.2.1 = t.2.2 := by
    by_cases h : v = w
    · subst w
      obtain ⟨V, hV, hVi⟩ := hlocal v v.property
      have hV' : Subtype.val ⁻¹' V ∈ 𝓝 v := preimage_coe_mem_nhds_subtype.mpr hV
      have hprod : (Subtype.val ⁻¹' V) ×ˢ (Subtype.val ⁻¹' V) ∈ 𝓝 (v, v) :=
        prod_mem_nhds hV' hV'
      filter_upwards [prod_mem_prod hVi hprod] with t ht
      exact fun he ↦ Subtype.ext (ht.1 ht.2.1 ht.2.2 he)
    · have hne : g v ≠ g w := fun he ↦ h (Subtype.ext (hinj v.property w.property he))
      have hl : Tendsto (fun t : P × (K × K) ↦ f t.1 t.2.1)
          (l ×ˢ 𝓝 (v, w)) (𝓝 (g v)) := by
        simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using
          (hc v).comp ((tendsto_id : Tendsto (id : P → P) l l).prodMap
            (continuous_fst.continuousAt : Tendsto Prod.fst (𝓝 (v, w)) (𝓝 v)))
      have hr : Tendsto (fun t : P × (K × K) ↦ f t.1 t.2.2)
          (l ×ˢ 𝓝 (v, w)) (𝓝 (g w)) := by
        simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using
          (hc w).comp ((tendsto_id : Tendsto (id : P → P) l l).prodMap
            (continuous_snd.continuousAt : Tendsto Prod.snd (𝓝 (v, w)) (𝓝 w)))
      have hnear := (hl.prodMk_nhds hr).eventually
        ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hne)
      filter_upwards [hnear] with t ht
      exact fun he ↦ False.elim (ht he)
  have hnear : ∀ᶠ t : P × (K × K) in l ×ˢ 𝓝ˢ (univ : Set (K × K)),
      f t.1 t.2.1 = f t.1 t.2.2 → t.2.1 = t.2.2 :=
    (isCompact_univ : IsCompact (univ : Set (K × K))).mem_prod_nhdsSet_of_forall
      (fun z _ ↦ hpair z.1 z.2)
  filter_upwards [hnear.curry] with q hq
  intro v hv w hw he
  exact congrArg Subtype.val (hq.self_of_nhdsSet (⟨v, hv⟩, ⟨w, hw⟩) (mem_univ _) he)

/-- For a Hausdorff target, injectivity on a compact set persists near a parameter within
`S` when the family is jointly continuous relative to `S ×ˢ K` along that parameter fibre,
and the total map retaining the parameter is locally injective there. -/
theorem eventually_injOn_of_injOn_prodMk
    {P E X : Type*} [TopologicalSpace P] [TopologicalSpace E]
    [TopologicalSpace X] [T2Space X] {f : P → E → X} {p : P} {S : Set P} {K : Set E}
    (hK : IsCompact K) (hinj : InjOn (f p) K)
    (hcont : ∀ v ∈ K, ContinuousWithinAt (fun z : P × E ↦ f z.1 z.2) (S ×ˢ K) (p, v))
    (hlocal : ∀ v ∈ K, ∃ U ∈ 𝓝[S ×ˢ K] (p, v),
      InjOn (fun z : P × E ↦ (z.1, f z.1 z.2)) U) :
    ∀ᶠ q in 𝓝[S] p, InjOn (f q) K := by
  apply hK.eventually_injOn hinj
  · intro v hv
    simpa only [ContinuousWithinAt, nhdsWithin_prod_eq] using hcont v hv
  · intro v hv
    obtain ⟨U, hU, hUi⟩ := hlocal v hv
    obtain ⟨W, hW, V, hV, hWV⟩ := mem_nhdsWithin_prod_iff.mp hU
    refine ⟨V, hV, ?_⟩
    filter_upwards [hW] with q hq
    intro x hx y hy he
    exact congrArg Prod.snd (hUi (hWV (show (q, x) ∈ W ×ˢ V from ⟨hq, hx⟩))
      (hWV (show (q, y) ∈ W ×ˢ V from ⟨hq, hy⟩)) (Prod.ext rfl he))

end IsCompact
