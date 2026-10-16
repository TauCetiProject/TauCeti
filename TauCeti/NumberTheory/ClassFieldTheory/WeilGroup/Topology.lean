/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Basic

/-!
# The Weil topology on the local Weil group

Let `K` be a nonarchimedean local field, `G_K` its absolute Galois group, `I_K ≤ G_K` the inertia
subgroup and `W_K = TauCeti.ClassFieldTheory.WeilGroup K` the local Weil group, with its degree
`weilDegree K : W_K →* ℤ` and kernel `I_K`. The **Weil topology** on `W_K` is the unique group
topology in which `I_K`, with the profinite topology it carries as a closed subgroup of `G_K`, is an
open subgroup. It is not the topology induced from `G_K`, in which inertia is not open
(`TauCeti.not_isOpen_inertiaSubgroup`).

We define it without choosing a Frobenius lift, as the topology induced by the injective
homomorphism

`W_K → G_K × ℤ, w ↦ (w, deg w)`,

with `ℤ` discrete (`isEmbedding_weilToAbsolute_prod_weilDegree`). A neighbourhood basis of `1` is
then `{w | deg w = 0, w ∈ U} = I_K ∩ U` for `U` open in `G_K`, so inertia is open with its own
profinite topology. Weil's description of the same topology goes through a choice of arithmetic
Frobenius lift, writing `W_K` as `I_K ⋊ ℤ` with the product of the profinite and the discrete
topologies; the description used here needs no choice.

## Main definitions

* `TauCeti.ClassFieldTheory.instTopologicalSpaceWeilGroup`: the Weil topology on `WeilGroup K`.

## Main results

* `TauCeti.ClassFieldTheory.isOpenEmbedding_inertiaToWeil`: `I_K`, with its profinite topology,
  is an open topological subgroup of `W_K` via the inclusion `inertiaToWeil K : I_K →* W_K`.
* `TauCeti.ClassFieldTheory.weilTopology_unique`: the Weil topology is the only group topology on
  `W_K` with this property.
* `TauCeti.ClassFieldTheory.continuous_weilToAbsolute`,
  `TauCeti.ClassFieldTheory.denseRange_weilToAbsolute`: the inclusion `W_K → G_K` is a continuous
  injection with dense image.
* `TauCeti.ClassFieldTheory.continuous_weilDegree`: the degree `W_K → ℤ` is continuous, so the exact
  sequence `1 → I_K → W_K → ℤ → 1` is one of topological groups.
* `W_K` is a locally compact, totally disconnected Hausdorff group
  (`TauCeti.ClassFieldTheory.instLocallyCompactSpaceWeilGroup`,
  `TauCeti.ClassFieldTheory.instTotallyDisconnectedSpaceWeilGroup`), and it is not compact
  (`TauCeti.ClassFieldTheory.not_compactSpace_weilGroup`).

## References

* A. Weil, *Sur la théorie du corps de classes*, J. Math. Soc. Japan 3 (1951).
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
-/

public section

noncomputable section

open Topology

namespace TauCeti.ClassFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### The topology -/

/-- **The Weil topology** on the local Weil group: the topology induced by
`w ↦ (w, deg w) : W_K → G_K × ℤ`, with `ℤ` discrete. It is the unique group topology in which
inertia, with its profinite topology, is an open subgroup (`isOpenEmbedding_inertiaToWeil`,
`weilTopology_unique`), and it is finer than the topology induced from `G_K`
(`continuous_weilToAbsolute`). -/
instance instTopologicalSpaceWeilGroup : TopologicalSpace (WeilGroup K) :=
  .induced ((weilToAbsolute K).prod (weilDegree K)) inferInstance

/-- **The characterization of the Weil topology**: `w ↦ (w, deg w)` is a topological embedding of
`W_K` into `G_K × ℤ`, with `ℤ` discrete. -/
theorem isEmbedding_weilToAbsolute_prod_weilDegree :
    IsEmbedding ((weilToAbsolute K).prod (weilDegree K)) :=
  Function.Injective.isEmbedding_induced fun _ _ h ↦
    injective_weilToAbsolute K (congrArg Prod.fst h)

/-- The Weil topology makes `W_K` a topological group. -/
instance instIsTopologicalGroupWeilGroup : IsTopologicalGroup (WeilGroup K) :=
  isTopologicalGroup_induced ((weilToAbsolute K).prod (weilDegree K))

/-- **The inclusion `W_K → G_K` is continuous**: the Weil topology is finer than the topology
induced from `G_K`. -/
@[fun_prop]
theorem continuous_weilToAbsolute : Continuous (weilToAbsolute K) :=
  continuous_fst.comp (isEmbedding_weilToAbsolute_prod_weilDegree K).continuous

/-- **The degree `W_K → ℤ` is continuous** for the discrete topology on `ℤ`. -/
@[fun_prop]
theorem continuous_weilDegree : Continuous (weilDegree K) :=
  continuous_snd.comp (isEmbedding_weilToAbsolute_prod_weilDegree K).continuous

/-- **The inclusion `W_K → G_K` has dense image**, since `W_K` is dense in `G_K`. -/
theorem denseRange_weilToAbsolute : DenseRange (weilToAbsolute K) := by
  rw [DenseRange, ← MonoidHom.coe_range, range_weilToAbsolute]
  exact dense_localWeilGroup K

/-- The Weil topology is Hausdorff. -/
instance instT2SpaceWeilGroup : T2Space (WeilGroup K) :=
  (isEmbedding_weilToAbsolute_prod_weilDegree K).t2Space

/-! ### Inertia is open, with its own topology -/

/-- **Inertia is open in the Weil group**, being the kernel of the continuous degree map to the
discrete group `ℤ`. -/
theorem isOpen_inertia_weil :
    IsOpen ((inertiaSubgroup K).comap (weilToAbsolute K) : Set (WeilGroup K)) := by
  rw [← ker_weilDegree, MonoidHom.coe_ker]
  exact (continuous_weilDegree K).isOpen_preimage _ (isOpen_discrete _)

/-- **The characterization of the Weil topology, first half.** The inclusion of `I_K`, with its
profinite topology as a closed subgroup of `G_K`, into `W_K` is an open topological embedding. -/
theorem isOpenEmbedding_inertiaToWeil : IsOpenEmbedding (inertiaToWeil K) := by
  have hcomp : Continuous ((weilToAbsolute K).prod (weilDegree K) ∘ inertiaToWeil K) := by
    have : (weilToAbsolute K).prod (weilDegree K) ∘ inertiaToWeil K = fun σ : inertiaSubgroup K ↦
        ((σ : Field.absoluteGaloisGroup K), (1 : Multiplicative ℤ)) := by
      ext σ <;> simp
    rw [this]
    fun_prop
  have hcont := (isEmbedding_weilToAbsolute_prod_weilDegree K).continuous_iff.2 hcomp
  refine ⟨.of_comp hcont (continuous_weilToAbsolute K) ?_, ?_⟩
  · have : weilToAbsolute K ∘ inertiaToWeil K = Subtype.val := funext weilToAbsolute_inertiaToWeil
    rw [this]
    exact .subtypeVal
  · rw [← MonoidHom.coe_range, range_inertiaToWeil]
    exact isOpen_inertia_weil K

/-- **The characterization of the Weil topology, second half: uniqueness.** Any group topology on
`W_K` in which `I_K`, with its profinite topology, includes as an open embedding is the Weil
topology. -/
theorem weilTopology_unique (t : TopologicalSpace (WeilGroup K))
    (ht : @IsTopologicalGroup (WeilGroup K) t _)
    (hopen : @IsOpenEmbedding _ _ _ t (inertiaToWeil K)) :
    t = instTopologicalSpaceWeilGroup K := by
  refine ht.ext (instIsTopologicalGroupWeilGroup K) ?_
  -- In both topologies, the neighbourhoods of `1` are the images of those of `1` in `I_K`. The
  -- instance arguments are explicit because `t` is a local instance here.
  have h := @IsOpenEmbedding.map_nhds_eq _ _ _ _ t hopen 1
  have h' := @IsOpenEmbedding.map_nhds_eq _ _ _ _ (instTopologicalSpaceWeilGroup K)
    (isOpenEmbedding_inertiaToWeil K) 1
  rw [map_one] at h h'
  exact h.symm.trans h'

/-! ### Local compactness and noncompactness -/

/-- **The Weil group is locally compact**: inertia is a compact open neighbourhood of `1`. -/
instance instLocallyCompactSpaceWeilGroup : LocallyCompactSpace (WeilGroup K) := by
  have : CompactSpace (inertiaSubgroup K) :=
    isCompact_iff_compactSpace.1 (isClosed_inertiaSubgroup K).isCompact
  have hopen := isOpenEmbedding_inertiaToWeil K
  exact (isCompact_range hopen.continuous).locallyCompactSpace_of_mem_nhds_of_group
    (x := 1) (hopen.isOpen_range.mem_nhds ⟨1, map_one _⟩)

/-- **The Weil group is totally disconnected**, as it embeds into the totally disconnected group
`G_K × ℤ`. -/
instance instTotallyDisconnectedSpaceWeilGroup : TotallyDisconnectedSpace (WeilGroup K) :=
  (isEmbedding_weilToAbsolute_prod_weilDegree K).isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- **The Weil group is not compact**, although `G_K` is compact and `W_K` is dense in it: the
degree is a continuous surjection onto the infinite discrete group `ℤ`. -/
theorem not_compactSpace_weilGroup : ¬ CompactSpace (WeilGroup K) := fun _ ↦ by
  have hfin := (isCompact_range (continuous_weilDegree K)).finite_of_discrete
  rw [(surjective_weilDegree K).range_eq] at hfin
  have : Finite (Multiplicative ℤ) := Set.finite_univ_iff.1 hfin
  exact not_finite (Multiplicative ℤ)

end TauCeti.ClassFieldTheory
