/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Extending local smooth data to global smooth maps

Vector-valued data on a closed subset of a smooth manifold extend globally if they
extend smoothly near every point of that subset. The extension can have topological
support inside any prescribed open neighbourhood. This is the partition-of-unity
step in extending velocities from an embedded submanifold to its ambient manifold.

The construction reduces to Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local`, applied
to singleton constraints on the closed set and zero constraints off an open neighbourhood whose
closure lies in the prescribed one.

The pointwise form needs only one bump function: a function that is smooth on a
neighbourhood of a point has the germ there of a globally smooth map
(`ContMDiffOn.exists_contMDiffMap_eventuallyEq`), with no paracompactness assumption.
A smooth map on an open subset, extended arbitrarily outside it, stays smooth on that subset
(`ContMDiffMap.contMDiffOn_extend`).
Reference: M. Hirsch, *Differential Topology*, Chapter 2, §2, and Chapter 8, §1.
-/

public section

open Set Function Topology
open scoped Manifold ContDiff

namespace ContMDiffMap

variable {𝕜 E E' H H' M M' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M'] {n : ℕ∞ω}

/-- Extending a smooth map on an open subset arbitrarily outside that subset gives a map that is
smooth on the subset. -/
theorem contMDiffOn_extend (U : TopologicalSpace.Opens M) (f : C^n⟮I, U; I', M'⟯) (g : M → M') :
    ContMDiffOn I I' n (Function.extend Subtype.val f g) U := fun x hx ↦ by
  refine (contMDiffAt_subtype_iff (x := ⟨x, hx⟩)).mp ?_ |>.contMDiffWithinAt
  rw [show (fun z : U ↦ extend Subtype.val f g z) = f from extend_comp Subtype.val_injective _ _]
  exact f.contMDiff _

end ContMDiffMap

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {n : ℕ∞}

/-- **A smooth germ is the germ of a global smooth map.** A vector-valued function that is `C^n`
on a neighbourhood of a point agrees near that point with a globally `C^n` map, namely its
product with a smooth bump function supported in that neighbourhood. -/
theorem ContMDiffOn.exists_contMDiffMap_eventuallyEq {U : Set M} {g : M → F} {x : M}
    (hg : ContMDiffOn I 𝓘(ℝ, F) n g U) (hU : U ∈ 𝓝 x) :
    ∃ G : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (G : M → F) =ᶠ[𝓝 x] g := by
  have hU' : interior U ∈ 𝓝 x := interior_mem_nhds.mpr hU
  obtain ⟨β, hβ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hU').mem_iff.mp hU'
  refine ⟨⟨fun y ↦ β y • g y, contMDiff_of_tsupport fun y hy ↦ ?_⟩, ?_⟩
  · exact β.contMDiffAt.of_le (mod_cast le_top) |>.smul <| hg.contMDiffAt <|
      mem_interior_iff_mem_nhds.mp <| hβ <| tsupport_smul_subset_left _ _ hy
  · filter_upwards [β.eventuallyEq_one] with y hy
    simp [hy]

/-- Locally smoothly extendible vector-valued data on a closed set have a global
`C^n` extension supported inside any prescribed open neighbourhood of that set.
No regularity is required of the original function away from the closed set. -/
theorem IsClosed.exists_contMDiffMap_eqOn [SigmaCompactSpace M] {s U : Set M} (hs : IsClosed s)
    {g : M → F} (hU : IsOpen U) (hsU : s ⊆ U)
    (hloc : ∀ x ∈ s, ∃ V ∈ 𝓝 x, ∃ g' : M → F, ContMDiffOn I 𝓘(ℝ, F) n g' V ∧ EqOn g' g (s ∩ V)) :
    ∃ G : C^n⟮I, M; 𝓘(ℝ, F), F⟯, EqOn G g s ∧ tsupport G ⊆ U := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Ask for the value of `g` on `s`, anything on `W`, and zero off `W`, where `closure W ⊆ U`.
  obtain ⟨W, hWo, hsW, hWU⟩ := normal_exists_closure_subset hs hU hsU
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := n) I
    (t := fun y ↦ if y ∈ s then {g y} else if y ∈ W then univ else {0})
    (fun y ↦ by split_ifs <;> first | exact convex_singleton _ | exact convex_univ) fun x ↦ by
      by_cases hx : x ∈ s
      · obtain ⟨V, hV, g', hg', heq⟩ := hloc x hx
        refine ⟨V ∩ W, Filter.inter_mem hV (hWo.mem_nhds (hsW hx)), g',
          hg'.mono inter_subset_left, ?_⟩
        rintro y ⟨hyV, hyW⟩
        split_ifs with hys
        exacts [heq ⟨hys, hyV⟩, mem_univ _]
      · refine ⟨sᶜ, hs.isOpen_compl.mem_nhds hx, 0, contMDiffOn_const, fun y hy ↦ ?_⟩
        split_ifs <;> simp_all
  refine ⟨G, fun x hx ↦ by simpa [hx] using hG x, (closure_mono fun x hx ↦ ?_).trans hWU⟩
  by_contra hxW
  have hxs : x ∉ s := fun h ↦ hxW (hsW h)
  exact mem_support.mp hx (by simpa [hxs, hxW] using hG x)
