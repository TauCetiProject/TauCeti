/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Topology.Separation.Hausdorff

/-!
# Locally constant functions near a compact set

A locally constant function on a compact subset `K` of a Hausdorff space takes finitely many
values, on pairwise disjoint compact fibres. Separating these fibres by disjoint open sets extends
the function to a locally constant function on an open neighbourhood of `K`
(`LocallyConstant.exists_isOpen_comap_eq`), and, in a locally compact Hausdorff space, on a
compact neighbourhood of `K` (`LocallyConstant.exists_isCompact_comap_eq`). Conversely, two
locally constant functions on a neighbourhood of `K` which agree on `K` agree on a smaller
compact neighbourhood (`LocallyConstant.exists_isCompact_comap_eq_comap`): the set where they
agree is open.

Together, these say that the locally constant functions on `K` are the germs along `K` of the
locally constant functions on its compact neighbourhoods. This is the continuity axiom of a
K-sheaf for the locally constant functions, see
`TauCeti.Topology.Sheaves.KSheaf.LocallyConstant`. The agreement statement
(`LocallyConstant.exists_isCompact_comap_eq_comap`) fails for continuous real functions: on a
metric space, `x ↦ dist x K` and `0` agree on a compact set `K` but on no neighbourhood of `K`
unless `K` is open.

## Main results

* `LocallyConstant.exists_isOpen_comap_eq`: extension from a compact set to an open
  neighbourhood, in a Hausdorff space.
* `LocallyConstant.exists_isCompact_comap_eq`: extension from a compact set to a compact
  neighbourhood, in a locally compact Hausdorff space.
* `LocallyConstant.exists_isCompact_comap_eq_comap`: locally constant functions agreeing on a
  compact set agree on a compact neighbourhood of it, in a locally compact space.
-/

public section

open Set Topology

namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X]

/-- A locally constant function on a compact subset `K` of a Hausdorff space extends to a locally
constant function on an open neighbourhood of `K`. -/
theorem exists_isOpen_comap_eq [T2Space X] {K : Set X} (hK : IsCompact K)
    (f : LocallyConstant K Y) :
    ∃ (U : Set X) (_ : IsOpen U) (hKU : K ⊆ U) (g : LocallyConstant U Y),
      g.comap ⟨inclusion hKU, continuous_inclusion hKU⟩ = f := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- The fibres `F m` of `f` over its finitely many values are pairwise disjoint compact sets, so
  -- they have pairwise disjoint open neighbourhoods `V m`.
  set F : Y → Set X := fun m => Subtype.val '' {x | f x = m}
  have hF : ∀ m, IsCompact (F m) := fun m =>
    (f.isLocallyConstant.isClosed_fiber m).isCompact.image continuous_subtype_val
  set S := range f
  have hd : S.PairwiseDisjoint fun m => 𝓝ˢ (F m) := fun m _ m' _ hne =>
    separatedNhds_iff_disjoint.1 <| SeparatedNhds.of_isCompact_isCompact (hF m) (hF m') <|
      disjoint_left.2 fun _ ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩ =>
        hne (hx.symm.trans ((congrArg f (Subtype.ext (hxz.trans hyz.symm))).trans hy))
  obtain ⟨V, hV, hVd⟩ := hd.exists_mem_filter_basis f.range_finite fun m => hasBasis_nhdsSet (F m)
  -- On `U = ⋃ m ∈ S, V m` the extension takes the value `m` on `V m`.
  set U := ⋃ m ∈ S, V m
  have hKU : K ⊆ U := fun x hx =>
    mem_biUnion (mem_range_self (⟨x, hx⟩ : K)) ((hV _).2 ⟨⟨x, hx⟩, rfl, rfl⟩)
  have hmem : ∀ z : U, ∃ m, m ∈ S ∧ (z : X) ∈ V m := fun z => by
    obtain ⟨m, hm, hz⟩ := mem_iUnion₂.1 z.2
    exact ⟨m, hm, hz⟩
  choose g hgS hgV using hmem
  have hg : ∀ (z : U) m, m ∈ S → (z : X) ∈ V m → g z = m := fun z m hm hz =>
    hVd.elim (hgS z) hm (not_disjoint_iff.2 ⟨z, hgV z, hz⟩)
  refine ⟨U, isOpen_biUnion fun m _ => (hV m).1, hKU, ⟨g, ?_⟩, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    exact fun z => ⟨Subtype.val ⁻¹' V (g z), (hV _).1.preimage continuous_subtype_val, hgV z,
      fun z' hz' => hg z' _ (hgS z) hz'⟩
  · ext x
    exact hg _ _ (mem_range_self x) ((hV _).2 ⟨x, rfl, rfl⟩)

/-- A locally constant function on a compact subset `K` of a locally compact Hausdorff space
extends to a locally constant function on a compact neighbourhood of `K`. -/
theorem exists_isCompact_comap_eq [T2Space X] [LocallyCompactSpace X] {K : Set X}
    (hK : IsCompact K) (f : LocallyConstant K Y) :
    ∃ (L : Set X) (_ : IsCompact L) (hKL : K ⊆ interior L) (g : LocallyConstant L Y),
      g.comap ⟨inclusion (hKL.trans interior_subset),
        continuous_inclusion (hKL.trans interior_subset)⟩ = f := by
  obtain ⟨U, hU, hKU, g, rfl⟩ := exists_isOpen_comap_eq hK f
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  exact ⟨L, hL, hKL, g.comap ⟨inclusion hLU, continuous_inclusion hLU⟩, rfl⟩

/-- Two locally constant functions on a set `L` which agree on a compact set `K ⊆ interior L` of a
locally compact space agree on a compact neighbourhood `L' ⊆ L` of `K`. -/
theorem exists_isCompact_comap_eq_comap [LocallyCompactSpace X] {K L : Set X}
    (hK : IsCompact K) (hKL : K ⊆ interior L) (f g : LocallyConstant L Y)
    (h : f.comap ⟨inclusion (hKL.trans interior_subset),
        continuous_inclusion (hKL.trans interior_subset)⟩ =
      g.comap ⟨inclusion (hKL.trans interior_subset),
        continuous_inclusion (hKL.trans interior_subset)⟩) :
    ∃ (L' : Set X) (_ : IsCompact L') (_ : K ⊆ interior L') (hL' : L' ⊆ L),
      f.comap ⟨inclusion hL', continuous_inclusion hL'⟩ =
        g.comap ⟨inclusion hL', continuous_inclusion hL'⟩ := by
  -- The set where `f` and `g` agree is open in `L`, so it is cut out by an open `t ⊆ X`.
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1
    ((f.isLocallyConstant.prodMk g.isLocallyConstant) {p : Y × Y | p.1 = p.2})
  have hKt : K ⊆ t ∩ interior L := fun x hx => by
    refine ⟨?_, hKL hx⟩
    have : (⟨x, interior_subset (hKL hx)⟩ : L) ∈ Subtype.val ⁻¹' t := by
      rw [hte]
      exact congr($h ⟨x, hx⟩)
    exact this
  obtain ⟨L', hL', hKL', hL't⟩ := exists_compact_between hK (ht.inter isOpen_interior) hKt
  have hL'L : L' ⊆ L := fun x hx => interior_subset (hL't hx).2
  refine ⟨L', hL', hKL', hL'L, LocallyConstant.ext fun x => ?_⟩
  have : (inclusion hL'L x : L) ∈ Subtype.val ⁻¹' t := (hL't x.2).1
  rw [hte] at this
  exact this

end LocallyConstant
