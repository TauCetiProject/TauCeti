/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Projective
import TauCeti.Topology.Algebra.IsUniformGroup.Quotient
import TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# The module topology on a finite module

Let `M` be a finite module over a topological ring `A`. Choosing a finite spanning family of `M`
presents it as an open quotient of `Aⁿ`, by Mathlib's
`IsModuleTopology.isOpenQuotientMap_of_surjective`, and so three properties of `A` descend to
`moduleTopology A M`: first countability, nonarchimedeanness, and — for the canonical right
uniformity, by `IsOpenQuotientMap.completeSpace` — completeness.

Each theorem asks of `A` exactly what its proof consumes, and none of them needs `A` to be a
Huber or a Tate ring. Separatedness is different: it is equivalent to closedness of the kernel of
the presentation, which is a genuinely arithmetic condition, and it is proved for a complete
noetherian Tate ring in `TauCeti.RingTheory.Huber.FiniteModuleTopology`. For a finite
*projective* module no arithmetic is needed: `M` is a direct summand of some `Aⁿ`, the section
`M → Aⁿ` is a continuous injection, and so `M` is Hausdorff as soon as `A` is (compare
Kedlaya–Liu, Lemma 2.2.12(a), where the module topology of a finite projective module is
identified with the subspace topology from such a summand embedding).

The topology is kept as the explicit expression `moduleTopology A M` in the statements: these are
theorem constructors for local instances, rather than global instances whose heads would hide the
topology on `M` from typeclass search.

## Main results

* `TauCeti.firstCountableTopology_moduleTopology`: the module topology on a finite module over a
  first-countable topological ring is first countable.
* `TauCeti.nonarchimedeanAddGroup_moduleTopology`: over a nonarchimedean topological ring it makes
  the additive group of the module nonarchimedean.
* `TauCeti.completeSpace_moduleTopology`: over a complete first-countable ring its canonical right
  uniformity is complete.
* `TauCeti.t2Space_moduleTopology_of_projective`: over a Hausdorff topological ring the module
  topology on a finite projective module is Hausdorff.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.2, Lemma 2.2.12.
-/

public section

open Filter Topology

namespace TauCeti

variable {A : Type*} [Ring A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The module topology on a finite module over a first-countable topological ring is first
countable.** -/
theorem firstCountableTopology_moduleTopology [TopologicalSpace A]
    [IsTopologicalRing A] [FirstCountableTopology A] :
    @FirstCountableTopology M (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  have hquot : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  rw [← hquot.map_nhds_eq x]
  infer_instance

/-- **The additive group of a finite module over a nonarchimedean topological ring, with its
module topology, is nonarchimedean.** -/
theorem nonarchimedeanAddGroup_moduleTopology [TopologicalSpace A]
    [IsTopologicalRing A] [NonarchimedeanAddGroup A] :
    @NonarchimedeanAddGroup M _ (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  exact NonarchimedeanAddGroup.nonarchimedean_of_isOpenMap f.toAddMonoidHom
    (IsModuleTopology.continuous_of_linearMap f).continuousAt
    (IsModuleTopology.isOpenQuotientMap_of_surjective hf).isOpenMap

/-- **The canonical right uniformity of the module topology on a finite module over a complete
first-countable ring is complete.** -/
theorem completeSpace_moduleTopology [UniformSpace A] [IsTopologicalRing A]
    [IsUniformAddGroup A] [CompleteSpace A] [FirstCountableTopology A] :
    letI : TopologicalSpace M := moduleTopology A M
    letI : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
    letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    CompleteSpace M := by
  let _ : TopologicalSpace M := moduleTopology A M
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  let _ : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  have _ : IsModuleTopology A M := inferInstance
  have _ : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  exact (IsModuleTopology.isOpenQuotientMap_of_surjective hf).completeSpace

/-- **The module topology on a finite projective module over a Hausdorff topological ring is
Hausdorff.** -/
theorem t2Space_moduleTopology_of_projective [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [Module.Projective A M] : @T2Space M (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  obtain ⟨n, -, g, -, hg, -⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  exact .of_injective_continuous hg (IsModuleTopology.continuous_of_linearMap g)

end TauCeti

end
