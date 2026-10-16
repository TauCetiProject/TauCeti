/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Prod
public import TauCeti.Topology.Homotopy.HurewiczFibration

/-!
# Restriction fibrations of mapping spaces

For a closed cofibration `A ⊆ K`, restriction `C(K, X) → C(A, X)` is a Hurewicz fibration
when `K` is locally compact. Its closed subspace `A` is then locally compact as well.
In particular this applies to closed cofibrations of compact Hausdorff spaces. The mapping
spaces have the compact-open topology.

A homotopy of restricted maps is extended over `K` while retaining an arbitrary parameter
space. Local compactness is needed only to evaluate the original families continuously;
there is no compactness or separation assumption on the parameter space or the target `X`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I, cofibrations and mapping spaces.
-/

public section

open Set unitInterval

universe w u v

namespace TauCeti

variable {K : Type u} {X : Type v} [TopologicalSpace K] [TopologicalSpace X]
  {A : Set K} [LocallyCompactSpace K]

/-- Restriction along a closed cofibration is a Hurewicz fibration of compact-open mapping
spaces. The test spaces can lie in any universe. -/
theorem HasHomotopyExtensionProperty.isHurewiczFibration_restrict
    (h : HasHomotopyExtensionProperty A) (hA : IsClosed A) :
    IsHurewiczFibration.{w} (fun f : C(K, X) ↦ f.restrict A) := by
  let _ : LocallyCompactSpace A := hA.locallyCompactSpace
  refine isHurewiczFibration_iff.mpr ⟨ContinuousMap.continuous_restrict A,
    fun T _ f H hH ↦ ?_⟩
  let F : C(T × K, X) := f.uncurry
  let H' : C(I × ((univ : Set T) ×ˢ A), X) :=
    ⟨fun q ↦ H (q.1, q.2.val.1) ⟨q.2.val.2, q.2.property.2⟩,
      (H.continuous.comp (by fun_prop)).eval (by fun_prop)⟩
  have hH' : ∀ z : (univ : Set T) ×ˢ A, H' (0, z) = F z := fun z ↦
    ContinuousMap.congr_fun (hH z.val.1) ⟨z.val.2, z.property.2⟩
  obtain ⟨G, hG₀, hG₁⟩ := (h.univ_prod hA).exists_extension_of_isClosed
    (isClosed_univ.prod hA) F H' hH'
  let G' : C(I × T, C(K, X)) :=
    (G.comp ⟨fun q : (I × T) × K ↦ (q.1.1, (q.1.2, q.2)), by fun_prop⟩).curry
  refine ⟨G', funext fun q ↦ ContinuousMap.ext fun a ↦ ?_, fun t ↦ ?_⟩
  · simpa only [G', H', Function.comp_apply, ContinuousMap.restrict_apply,
      ContinuousMap.curry_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using
      hG₁ q.1 ⟨(q.2, a.val), ⟨mem_univ _, a.property⟩⟩
  · apply ContinuousMap.ext
    intro k
    simpa only [G', F, ContinuousMap.curry_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair] using
      hG₀ (t, k)

end TauCeti
