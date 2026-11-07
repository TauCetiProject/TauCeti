/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import TauCeti.Topology.Homotopy.HurewiczFibration.Numerable

/-!
# Numerable and paracompact locally trivial bundles are Hurewicz fibrations

Every local trivialization `e : Bundle.Trivialization F p` makes the restriction
`p ⁻¹' e.baseSet → e.baseSet` a Hurewicz fibration
(`Bundle.Trivialization.isHurewiczFibration_restrict`). Combining this with Dold's local-to-global
theorem over numerable covers (`TauCeti.isHurewiczFibration_of_partitionOfUnity`) shows that:

* a map `p : E → B` equipped with an explicit numerable trivializing cover — a family of
  trivializations `(e i : Bundle.Trivialization F p)` and a partition of unity
  `ρ : PartitionOfUnity ι B` with `support (ρ i) ⊆ (e i).baseSet` — is a Hurewicz fibration
  (`TauCeti.isHurewiczFibration_of_partitionOfUnity_trivialization`);
* over a normal paracompact base `B` (which includes every paracompact Hausdorff base via Mathlib's
  `NormalSpace` instance), any locally trivial map
  (`∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet`) is a Hurewicz fibration
  (`TauCeti.isHurewiczFibration_of_exists_trivialization`), and in particular the projection of
  every `FiberBundle F E` over `B` is a Hurewicz fibration
  (`FiberBundle.isHurewiczFibration_proj`).

Test spaces may lie in any universe `w`, with no separation, countability or paracompactness
assumption on them, and the fibre `F`, total space `E`, and base `B` may lie in distinct universes.

## Main results

* `Bundle.Trivialization.hasHomotopyLiftingProperty_restrict` and
  `Bundle.Trivialization.isHurewiczFibration_restrict`: the restriction of `p` over the base set of
  a local trivialization is a Hurewicz fibration.
* `TauCeti.hasHomotopyLiftingProperty_of_partitionOfUnity_trivialization` and
  `TauCeti.isHurewiczFibration_of_partitionOfUnity_trivialization`: a map with an explicit
  numerable trivializing cover is a Hurewicz fibration.
* `TauCeti.isHurewiczFibration_of_isSubordinate_trivialization`: convenience form for closed-support
  subordination `ρ.IsSubordinate fun i ↦ (e i).baseSet`.
* `TauCeti.hasHomotopyLiftingProperty_of_exists_trivialization` and
  `TauCeti.isHurewiczFibration_of_exists_trivialization`: over a normal paracompact base, a locally
  trivial map is a Hurewicz fibration.
* `FiberBundle.hasHomotopyLiftingProperty_proj` and `FiberBundle.isHurewiczFibration_proj`: over a
  normal paracompact base, the projection of a fibre bundle is a Hurewicz fibration.

## References

* A. Dold, *Partitions of unity in the theory of fibrations*, Ann. of Math. (2) 78 (1963),
  223–255, Theorem 4.8.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Theorem 4.42.
-/

public section

open Bundle Function Set Topology unitInterval

universe w u v uF

namespace Bundle.Trivialization

variable {E : Type u} {B : Type v} {F : Type uF}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F] {p : E → B}

/-- Over the base set of a local trivialization `e`, the restricted projection
`p ⁻¹' e.baseSet → e.baseSet` is a Hurewicz fibration. -/
theorem isHurewiczFibration_restrict (e : Trivialization F p) :
    TauCeti.IsHurewiczFibration.{w}
      (Set.MapsTo.restrict p (p ⁻¹' e.baseSet) e.baseSet (mapsTo_preimage p e.baseSet)) := by
  have heq : (Prod.fst : e.baseSet × F → e.baseSet) ∘ e.preimageHomeomorph subset_rfl =
      Set.MapsTo.restrict p (p ⁻¹' e.baseSet) e.baseSet (mapsTo_preimage p e.baseSet) := by
    ext x
    simp [Set.MapsTo.restrict, Subtype.map]
  exact heq ▸ (TauCeti.isHurewiczFibration_fst F).comp_homeomorph (e.preimageHomeomorph subset_rfl)

/-- Over the base set of a local trivialization `e`, the restricted projection
`p ⁻¹' e.baseSet → e.baseSet` has the homotopy lifting property with respect to every space `A`. -/
theorem hasHomotopyLiftingProperty_restrict (e : Trivialization F p) (A : Type w)
    [TopologicalSpace A] :
    TauCeti.HasHomotopyLiftingProperty
      (Set.MapsTo.restrict p (p ⁻¹' e.baseSet) e.baseSet (mapsTo_preimage p e.baseSet)) A :=
  e.isHurewiczFibration_restrict.hasHomotopyLiftingProperty A

end Bundle.Trivialization

namespace TauCeti

section Trivializations

variable {ι : Type*} {E : Type u} {B : Type v} {F : Type uF}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F] {p : E → B}

/-- A map equipped with a numerable trivializing cover — a family of trivializations `e i` and a
partition of unity `ρ` on `B` with `support (ρ i) ⊆ (e i).baseSet` — has the homotopy lifting
property with respect to every space `A`. -/
theorem hasHomotopyLiftingProperty_of_partitionOfUnity_trivialization
    (e : ι → Trivialization F p) (ρ : PartitionOfUnity ι B)
    (hρ : ∀ i, support (ρ i) ⊆ (e i).baseSet) (A : Type w) [TopologicalSpace A] :
    HasHomotopyLiftingProperty p A :=
  HasHomotopyLiftingProperty.of_partitionOfUnity ρ hρ
    fun i W _ ↦ (e i).hasHomotopyLiftingProperty_restrict W

/-- A map equipped with an explicit numerable trivializing cover — a family of trivializations
`e i` and a partition of unity `ρ` on `B` with `support (ρ i) ⊆ (e i).baseSet` — is a Hurewicz
fibration. Global continuity of `p` follows automatically from the trivializations covering `B`. -/
theorem isHurewiczFibration_of_partitionOfUnity_trivialization
    (e : ι → Trivialization F p) (ρ : PartitionOfUnity ι B)
    (hρ : ∀ i, support (ρ i) ⊆ (e i).baseSet) :
    IsHurewiczFibration.{w} p := by
  have hp : Continuous p := continuous_iff_continuousAt.2 fun x ↦
    let ⟨i, hi⟩ := ρ.exists_pos (mem_univ (p x))
    (e i).continuousAt_proj ((e i).mem_source.2 (hρ i hi.ne'))
  exact isHurewiczFibration_of_partitionOfUnity hp ρ hρ
    fun i ↦ (e i).isHurewiczFibration_restrict

/-- Convenience form of `TauCeti.isHurewiczFibration_of_partitionOfUnity_trivialization` when `ρ`
is subordinate to `(e i).baseSet` in the closed-support sense
(`PartitionOfUnity.IsSubordinate`). -/
theorem isHurewiczFibration_of_isSubordinate_trivialization
    (e : ι → Trivialization F p) {ρ : PartitionOfUnity ι B}
    (hρ : ρ.IsSubordinate fun i ↦ (e i).baseSet) :
    IsHurewiczFibration.{w} p :=
  isHurewiczFibration_of_partitionOfUnity_trivialization e ρ
    fun i ↦ (subset_tsupport _).trans (hρ i)

/-- Over a normal paracompact base (including every paracompact Hausdorff base), a locally trivial
map has the homotopy lifting property with respect to every space `A`. -/
theorem hasHomotopyLiftingProperty_of_exists_trivialization
    [NormalSpace B] [ParacompactSpace B]
    (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) (A : Type w) [TopologicalSpace A] :
    HasHomotopyLiftingProperty p A := by
  choose e he using h
  exact HasHomotopyLiftingProperty.of_isOpenCover
    (fun b ↦ (e b).open_baseSet) (fun b ↦ ⟨b, he b⟩)
    fun b W _ ↦ (e b).hasHomotopyLiftingProperty_restrict W

/-- Over a normal paracompact base (including every paracompact Hausdorff base), a locally trivial
map is a Hurewicz fibration. -/
theorem isHurewiczFibration_of_exists_trivialization
    [NormalSpace B] [ParacompactSpace B]
    (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) :
    IsHurewiczFibration.{w} p := by
  choose e he using h
  have hp : Continuous p := continuous_iff_continuousAt.2 fun x ↦
    (e (p x)).continuousAt_proj ((e (p x)).mem_source.2 (he (p x)))
  exact isHurewiczFibration_of_isOpenCover hp
    (fun b ↦ (e b).open_baseSet) (fun b ↦ ⟨b, he b⟩)
    fun b ↦ (e b).isHurewiczFibration_restrict

end Trivializations

end TauCeti

namespace FiberBundle

variable {B : Type v} {F : Type uF} {E : B → Type u}
  [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (F E) in
/-- Over a normal paracompact base (including every paracompact Hausdorff base), the projection of
a fibre bundle has the homotopy lifting property with respect to every space `A`. -/
theorem hasHomotopyLiftingProperty_proj [NormalSpace B] [ParacompactSpace B]
    (A : Type w) [TopologicalSpace A] :
    TauCeti.HasHomotopyLiftingProperty (TotalSpace.proj : TotalSpace F E → B) A :=
  TauCeti.hasHomotopyLiftingProperty_of_exists_trivialization
    (fun b ↦ ⟨trivializationAt F E b, mem_baseSet_trivializationAt F E b⟩) A

variable (F E) in
/-- Over a normal paracompact base (including every paracompact Hausdorff base), the projection of
a fibre bundle is a Hurewicz fibration. -/
theorem isHurewiczFibration_proj [NormalSpace B] [ParacompactSpace B] :
    TauCeti.IsHurewiczFibration.{w} (TotalSpace.proj : TotalSpace F E → B) :=
  TauCeti.isHurewiczFibration_of_exists_trivialization
    fun b ↦ ⟨trivializationAt F E b, mem_baseSet_trivializationAt F E b⟩

end FiberBundle
