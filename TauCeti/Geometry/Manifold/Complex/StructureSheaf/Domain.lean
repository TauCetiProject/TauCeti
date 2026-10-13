/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
import TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Holomorphic stalks are integral domains

On a complex curve, holomorphic sections over a connected open set have no zero divisors,
by the identity theorem. Every point has a basis of connected open neighborhoods, so the
same holds for the stalk of the holomorphic structure sheaf. Thus a holomorphic germ embeds
in its fraction field, providing the local algebra for meromorphic functions and divisor sheaves.

Neither the curve nor an arbitrary domain of sections is required to be connected: only the
sectionwise statement needs connectedness of its domain. Compactness is not needed.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§1, 6 and 16.
* The section argument uses `TauCeti.RiemannSurface.apply_eq_of_eventuallyConst`;
  the passage to stalks uses Mathlib's `TopCat.Presheaf.germ_eq` and
  `TopCat.Presheaf.exists_germ_eq`.
-/

public noncomputable section

open CategoryTheory Filter Opposite Set TopologicalSpace Topology
open scoped Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Holomorphic sections on a preconnected open set have no zero divisors. -/
instance sectionsNoZeroDivisors (U : Opens X) [PreconnectedSpace U] :
    NoZeroDivisors ((holomorphicStructureSheaf 𝓘(ℂ) X).obj.obj (op U)) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    by_cases hf : f = 0
    · exact Or.inl hf
    right
    have hfg : ∀ y : U, f y * g y = 0 := fun y ↦ by
      simpa only [mul_apply, zero_apply] using congrArg (fun s ↦ s y) h
    obtain ⟨y, hy⟩ : ∃ y : U, f y ≠ 0 := by
      by_contra hn
      exact hf (ext fun y ↦ by simpa using not_exists.mp hn y)
    have hg : g =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [(contMDiff f).continuous.continuousAt.eventually_ne hy] with z hz
      exact (mul_eq_zero.mp (hfg z)).resolve_left hz
    apply ext
    intro z
    simpa only [zero_apply] using (RiemannSurface.apply_eq_of_eventuallyConst (mdifferentiable g)
      (eventuallyConst_iff_exists_eventuallyEq.mpr ⟨0, hg⟩) z).trans hg.eq_of_nhds

/-- The stalk of holomorphic functions at any point of a complex curve is an integral domain. -/
instance stalkIsDomain (x : X) :
    IsDomain ((holomorphicStructureSheaf 𝓘(ℂ) X).presheaf.stalk x) := by
  let F := (holomorphicStructureSheaf 𝓘(ℂ) X).presheaf
  have : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have : NoZeroDivisors (F.stalk x) := ⟨by
    intro a b hab
    obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq a
    obtain ⟨V, hxV, t, rfl⟩ := F.exists_germ_eq b
    let P : Opens X := U ⊓ V
    have hxP : x ∈ P := ⟨hxU, hxV⟩
    let s' := F.map (homOfLE (inf_le_left : P ≤ U)).op s
    let t' := F.map (homOfLE (inf_le_right : P ≤ V)).op t
    have hprod : F.germ P x hxP (s' * t') = F.germ P x hxP 0 := by
      rw [map_mul, map_zero, F.germ_res_apply, F.germ_res_apply]
      exact hab
    obtain ⟨W, hxW, iP, jP, hW⟩ := F.germ_eq x hxP hxP (s' * t') 0 hprod
    obtain ⟨C, hC, hCW⟩ := (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp
      (W.isOpen.mem_nhds hxW)
    let Q : Opens X := ⟨C, hC.1⟩
    have hxQ : x ∈ Q := hC.2.1
    have : PreconnectedSpace Q := isPreconnected_iff_preconnectedSpace.mp
      hC.2.2.isPreconnected
    let j : Q ⟶ W := homOfLE hCW
    let k : Q ⟶ P := j ≫ iP
    have hQ : F.map k.op s' * F.map k.op t' = 0 := by
      rw [← map_mul]
      simp only [k, op_comp, F.map_comp, ConcreteCategory.comp_apply, hW, map_zero]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hQ with hs | ht
    · left
      rw [← F.germ_res_apply (homOfLE inf_le_left) x hxP s,
        ← F.germ_res_apply k x hxQ s', hs, map_zero]
    · right
      rw [← F.germ_res_apply (homOfLE inf_le_right) x hxP t,
        ← F.germ_res_apply k x hxQ t', ht, map_zero]⟩
  exact (isDomain_iff_noZeroDivisors_and_nontrivial (α := F.stalk x)).mpr
    ⟨inferInstance, inferInstance⟩

end TauCeti.holomorphicStructureSheaf
