/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Order.PiLex

/-!
# Lexicographic upper semicontinuity under local finiteness

When `f : X → ∀ i, β i` takes only finitely many values on a set `s` (or locally on a
neighborhood of each point), each lexicographic upper cut decomposes as a finite union of
pointwise upper cuts (`Pi.inter_preimage_Ici_toLex_eq_biUnion`). Consequently:

* closedness of pointwise upper cuts transfers to closedness of lexicographic upper cuts
  (`Pi.isClosed_inter_preimage_Ici_toLex`, `Pi.isClosed_preimage_Ici_toLex`);
* coordinatewise upper semicontinuity transfers to upper semicontinuity of `toLex ∘ f`
  (`Pi.upperSemicontinuousOn_toLex_comp`, `Pi.upperSemicontinuous_toLex_comp`).

## Main results

* `Pi.isClosed_inter_preimage_Ici_toLex`: closedness on a set `s` with finite image `f '' s`.
* `Pi.isClosed_preimage_Ici_toLex`: closedness of `(toLex ∘ f) ⁻¹' Set.Ici c` when `f` has
  locally finite range and closed pointwise upper cuts.
* `Pi.upperSemicontinuousOn_toLex_comp`, `Pi.upperSemicontinuous_toLex_comp`: coordinatewise
  upper semicontinuity implies upper semicontinuity of `toLex ∘ f` under local finiteness.
-/

public section

open scoped Topology

namespace Pi

section PartialOrder

variable {X ι : Type*} {β : ι → Type*} [TopologicalSpace X]
  [LinearOrder ι] [WellFoundedLT ι] [∀ i, PartialOrder (β i)]

/-- On a set `s` where `f` takes finitely many values, if every pointwise upper cut
`s ∩ f ⁻¹' Set.Ici v` at an attained value `v ∈ f '' s` with `c ≤ toLex v` is closed, then the
lexicographic upper cut `s ∩ (toLex ∘ f) ⁻¹' Set.Ici c` is closed. -/
theorem isClosed_inter_preimage_Ici_toLex {f : X → ∀ i, β i} {s : Set X}
    (hf : (f '' s).Finite) (c : Lex (∀ i, β i))
    (hclosed : ∀ v ∈ f '' s ∩ toLex ⁻¹' Set.Ici c, IsClosed (s ∩ f ⁻¹' Set.Ici v)) :
    IsClosed (s ∩ (toLex ∘ f) ⁻¹' Set.Ici c) := by
  rw [inter_preimage_Ici_toLex_eq_biUnion]
  exact (hf.inter_of_left _).isClosed_biUnion hclosed

/-- If `f : X → ∀ i, β i` locally takes finitely many values and every pointwise upper cut
`f ⁻¹' Set.Ici v` at an attained value `v ∈ Set.range f` with `c ≤ toLex v` is closed, then the
lexicographic upper cut `(toLex ∘ f) ⁻¹' Set.Ici c` is closed. -/
theorem isClosed_preimage_Ici_toLex {f : X → ∀ i, β i}
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) (c : Lex (∀ i, β i))
    (hclosed : ∀ v ∈ Set.range f ∩ toLex ⁻¹' Set.Ici c, IsClosed (f ⁻¹' Set.Ici v)) :
    IsClosed ((toLex ∘ f) ⁻¹' Set.Ici c) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨u, hu, hfu⟩ := hfin x
  let F : Set X := ⋃ v ∈ f '' u ∩ toLex ⁻¹' Set.Ici c, f ⁻¹' Set.Ici v
  have hF_closed : IsClosed F := (hfu.inter_of_left _).isClosed_biUnion fun v hv ↦
    hclosed v ⟨Set.image_subset_range f u hv.1, hv.2⟩
  have hu_eq : u ∩ (toLex ∘ f) ⁻¹' Set.Ici c = u ∩ F := by
    rw [inter_preimage_Ici_toLex_eq_biUnion, Set.inter_iUnion₂]
  have hxF : x ∉ F := fun hmem ↦ by
    have hx_mem : x ∈ u ∩ (toLex ∘ f) ⁻¹' Set.Ici c := hu_eq ▸ ⟨mem_of_mem_nhds hu, hmem⟩
    exact hx hx_mem.2
  filter_upwards [hu, hF_closed.isOpen_compl.mem_nhds hxF] with y hyu hyF hyc
  have hy_mem : y ∈ u ∩ F := hu_eq ▸ ⟨hyu, hyc⟩
  exact hyF hy_mem.2

end PartialOrder

section LinearOrder

variable {X ι : Type*} {β : ι → Type*} [TopologicalSpace X]
  [LinearOrder ι] [WellFoundedLT ι] [∀ i, LinearOrder (β i)]

/-- If each coordinate `x ↦ f x i` is upper semicontinuous on `s` and `f` locally takes finitely
many values within `s`, then `toLex ∘ f` is upper semicontinuous on `s`. -/
theorem upperSemicontinuousOn_toLex_comp {f : X → ∀ i, β i} {s : Set X}
    (hf : ∀ i, UpperSemicontinuousOn (fun x ↦ f x i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousOn (toLex ∘ f) s := by
  intro x hx c hxc
  obtain ⟨u, hu, hfu⟩ := hfin x hx
  have hus : u ∩ s ∈ 𝓝[s] x := Filter.inter_mem hu self_mem_nhdsWithin
  have hfin' : (f '' (u ∩ s) ∩ toLex ⁻¹' Set.Ici c).Finite :=
    (hfu.subset (Set.image_mono Set.inter_subset_left)).inter_of_left _
  have hev : ∀ v ∈ f '' (u ∩ s) ∩ toLex ⁻¹' Set.Ici c,
      ∀ᶠ y in 𝓝[s] x, y ∉ f ⁻¹' Set.Ici v := by
    intro v hv
    have hnotle : ¬ v ≤ f x := fun hle ↦ (toLex_monotone hle).not_gt (lt_of_lt_of_le hxc hv.2)
    simp only [Pi.le_def, not_forall, not_le] at hnotle
    obtain ⟨i, hi⟩ := hnotle
    filter_upwards [hf i x hx (v i) hi] with y hy hle
    exact hy.not_ge (hle i)
  filter_upwards [hus, hfin'.eventually_all.2 hev] with y hyus hyavoid
  by_contra! hyc
  have hy_mem : y ∈ (u ∩ s) ∩ (toLex ∘ f) ⁻¹' Set.Ici c := ⟨hyus, hyc⟩
  rw [inter_preimage_Ici_toLex_eq_biUnion] at hy_mem
  obtain ⟨v, hv, -, hyfv⟩ := Set.mem_iUnion₂.mp hy_mem
  exact hyavoid v hv hyfv

/-- If each coordinate `x ↦ f x i` is upper semicontinuous and `f` locally takes finitely many
values, then `toLex ∘ f` is upper semicontinuous. -/
theorem upperSemicontinuous_toLex_comp {f : X → ∀ i, β i}
    (hf : ∀ i, UpperSemicontinuous (fun x ↦ f x i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuous (toLex ∘ f) :=
  upperSemicontinuous_iff_isClosed_preimage.2 fun c ↦
    isClosed_preimage_Ici_toLex hfin c fun v _ ↦ by
      have hpre : f ⁻¹' Set.Ici v = ⋂ i, (fun x ↦ f x i) ⁻¹' Set.Ici (v i) := by
        ext x
        simp [Pi.le_def]
      rw [hpre]
      exact isClosed_iInter fun i ↦ (hf i).isClosed_preimage (v i)

end LinearOrder

end Pi
