/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact

/-!
# Compactness and local injectivity

Distinct points in a compact set with the same image under a locally injective continuous
map form a compact set of pairs. Thus a noninjective restriction to a compact metric set
has a first collision: a pair minimizing the maximum distance from any chosen center.
The domain need not be a vector space or have compact closed balls.

For a parameterized family, injectivity on a compact fiber persists near that parameter
when the total map retaining the parameter is locally injective along the fiber. These
are the compactness steps used in injectivity-radius estimates before the geometric
return-direction argument; they do not construct an exponential map or a geodesic.

## Main results

* `TauCeti.isCompact_colliding_pairs`: compactness of the set of distinct equal-image pairs.
* `TauCeti.exists_minimal_collision`: attainment of a positive first collision radius.
* `TauCeti.eventually_injOn_of_locally_injective_total_map`: stability on a compact fiber.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

/-- For a continuous map locally injective along a compact set, the distinct pairs in that
set with the same image form a compact set. Only the target must be Hausdorff. -/
theorem isCompact_colliding_pairs
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {f : E → X} (hf : ContinuousOn f K)
    (hinj : ∀ x ∈ K, ∃ U ∈ 𝓝 x, InjOn f U) :
    IsCompact {z : E × E | z.1 ∈ K ∧ z.2 ∈ K ∧ f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  let S : Set (K × K) := {z | f z.1 = f z.2 ∧ z.1 ≠ z.2}
  have hc : Continuous (fun x : K ↦ f x) := continuousOn_iff_continuous_domRestrict.mp hf
  have heq : IsClosed {z : K × K | f z.1 = f z.2} :=
    isClosed_eq (hc.comp continuous_fst) (hc.comp continuous_snd)
  have hclosed : IsClosed S := by
    apply isClosed_of_closure_subset
    intro z hz
    have hzEq := closure_minimal (show S ⊆ {z : K × K | f z.1 = f z.2} from
      fun _ h ↦ h.1) heq hz
    refine ⟨hzEq, ?_⟩
    intro hdiag
    obtain ⟨U, hU, hUi⟩ := hinj z.1 z.1.property
    have hU' : U ∈ 𝓝 (z.2 : E) := congrArg Subtype.val hdiag ▸ hU
    have hprod : (Subtype.val ⁻¹' U) ×ˢ (Subtype.val ⁻¹' U) ∈ 𝓝 z := by
      rw [nhds_prod_eq]
      exact prod_mem_prod
        (continuous_subtype_val.continuousAt.preimage_mem_nhds hU)
        (continuous_subtype_val.continuousAt.preimage_mem_nhds hU')
    obtain ⟨w, hwU, hwS⟩ := mem_closure_iff_nhds.mp hz _ hprod
    exact hwS.2 (Subtype.ext (hUi hwU.1 hwU.2 hwS.1))
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcompact := hclosed.isCompact.image
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

/-- On any compact metric set, a locally injective continuous map that is not injective has
a pair of distinct equal-image points minimizing their maximum distance from a chosen center.
This minimum is positive. No properness or linear structure is required. -/
theorem exists_minimal_collision
    {E X : Type*} [MetricSpace E] [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {f : E → X} (hf : ContinuousOn f K)
    (hinj : ∀ x ∈ K, ∃ U ∈ 𝓝 x, InjOn f U) (hnot : ¬ InjOn f K) (c : E) :
    ∃ v ∈ K, ∃ w ∈ K, f v = f w ∧ v ≠ w ∧ 0 < max (dist v c) (dist w c) ∧
      ∀ x ∈ K, ∀ y ∈ K, f x = f y → x ≠ y →
        max (dist v c) (dist w c) ≤ max (dist x c) (dist y c) := by
  let S : Set (E × E) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ f z.1 = f z.2 ∧ z.1 ≠ z.2}
  have hS : IsCompact S := isCompact_colliding_pairs hK hf hinj
  have hSne : S.Nonempty := by
    simp only [InjOn, not_forall] at hnot
    obtain ⟨v, hv, w, hw, heq, hne⟩ := hnot
    exact ⟨(v, w), hv, hw, heq, hne⟩
  have hc : Continuous (fun z : E × E ↦ max (dist z.1 c) (dist z.2 c)) := by fun_prop
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
  refine ⟨z.1, hz.1, z.2, hz.2.1, hz.2.2.1, hz.2.2.2, ?_, ?_⟩
  · by_contra h
    have hzero := le_of_not_gt h
    have hv : z.1 = c := dist_eq_zero.mp
      (le_antisymm ((le_max_left _ _).trans hzero) dist_nonneg)
    have hw : z.2 = c := dist_eq_zero.mp
      (le_antisymm ((le_max_right _ _).trans hzero) dist_nonneg)
    exact hz.2.2.2 (hv.trans hw.symm)
  · intro x hx y hy he hne
    exact hmin (show (x, y) ∈ S from ⟨hx, hy, he, hne⟩)

/-- Fiberwise injectivity on a compact set persists near the parameter if the
total map, retaining the parameter, is locally injective along that fiber. -/
theorem eventually_injOn_of_locally_injective_total_map
    {P E X : Type*} [TopologicalSpace P] [TopologicalSpace E]
    [TopologicalSpace X] [T2Space X] {f : P → E → X} {p : P} {K : Set E}
    (hK : IsCompact K) (hinj : InjOn (f p) K)
    (hcont : ∀ v ∈ K, ContinuousAt (fun z : P × E ↦ f z.1 z.2) (p, v))
    (hlocal : ∀ v ∈ K, ∃ U ∈ 𝓝 (p, v),
      InjOn (fun z : P × E ↦ (z.1, f z.1 z.2)) U) :
    ∀ᶠ q in 𝓝 p, InjOn (f q) K := by
  have hpair : ∀ z ∈ K ×ˢ K,
      ∀ᶠ t : P × (E × E) in 𝓝 (p, z),
        f t.1 t.2.1 = f t.1 t.2.2 → t.2.1 = t.2.2 := by
    rintro ⟨v, w⟩ ⟨hv, hw⟩
    have hleft : ContinuousAt (fun t : P × (E × E) ↦ (t.1, t.2.1)) (p, v, w) :=
      continuous_fst.continuousAt.prodMk continuous_snd.fst.continuousAt
    have hright : ContinuousAt (fun t : P × (E × E) ↦ (t.1, t.2.2)) (p, v, w) :=
      continuous_fst.continuousAt.prodMk continuous_snd.snd.continuousAt
    by_cases h : v = w
    · subst w
      obtain ⟨U, hU, hUi⟩ := hlocal v hv
      filter_upwards [hleft.preimage_mem_nhds hU, hright.preimage_mem_nhds hU]
        with t ht₁ ht₂
      intro heq
      exact congrArg Prod.snd (hUi ht₁ ht₂ (Prod.ext rfl heq))
    · have hne : f p v ≠ f p w := fun heq ↦ h (hinj hv hw heq)
      have hcont₁ : ContinuousAt (fun t : P × (E × E) ↦ f t.1 t.2.1) (p, v, w) :=
        (hcont v hv).comp_of_eq hleft rfl
      have hcont₂ : ContinuousAt (fun t : P × (E × E) ↦ f t.1 t.2.2) (p, v, w) :=
        (hcont w hw).comp_of_eq hright rfl
      have hnear := (hcont₁.ne_iff_eventually_ne hcont₂).mp hne
      filter_upwards [hnear] with t ht
      exact fun heq ↦ False.elim (ht heq)
  filter_upwards [(hK.prod hK).eventually_forall_of_forall_eventually
    (P := fun q z ↦ f q z.1 = f q z.2 → z.1 = z.2) hpair] with q hq
  exact fun v hv w hw heq ↦ hq (v, w) ⟨hv, hw⟩ heq


end TauCeti
