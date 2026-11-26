/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Admissible

/-!
# Locally admissible representations

A smooth representation `V` of a topological group `G` over a commutative ring `A` is *locally
admissible* if every vector `v` generates an admissible subrepresentation `A[G] · v`, the
subrepresentation `Representation.cyclicSubrepresentation ρ v` (defined in
`TauCeti.RepresentationTheory.Subrepresentation`) corresponding to the cyclic
`A[G]`-submodule of `ρ.asModule` spanned by `v`. Over a noetherian ring every subrepresentation of
an admissible representation is admissible, so admissible representations are locally admissible
(`Representation.IsAdmissible.isLocallyAdmissible`). The converse needs finite generation and
invertible pro-orders, and is not proved here.

## Main definitions

* `Representation.IsLocallyAdmissible ρ`: the `Prop`-valued class asserting that every
  `A[G] · v` is admissible.

## Main results

The first three results are instances.

* `Representation.IsLocallyAdmissible.isSmooth`: locally admissible representations are smooth.
* `Representation.IsAdmissible.isLocallyAdmissible`: over a noetherian ring, admissible
  representations are locally admissible.
* `Representation.isLocallyAdmissible_of_isTrivial`: trivial representations are locally
  admissible, over any commutative ring.
* `Representation.isLocallyAdmissible_trivial_self`: the trivial rank-one representation is locally
  admissible.

## References

* F. Calegari and D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*,
  arXiv:1207.4224v2, §9.2.1, Definition 9.11, p. 91.
-/

public section

namespace Representation

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V}

variable [TopologicalSpace G]

variable (ρ) in
/-- A representation is *locally admissible* if every vector generates an admissible
subrepresentation. -/
class IsLocallyAdmissible : Prop where
  isAdmissible_cyclicSubrepresentation (v : V) :
    IsAdmissible (cyclicSubrepresentation ρ v).toRepresentation

theorem isLocallyAdmissible_iff :
    IsLocallyAdmissible ρ ↔ ∀ v : V, IsAdmissible (cyclicSubrepresentation ρ v).toRepresentation :=
  ⟨fun h ↦ h.isAdmissible_cyclicSubrepresentation, fun h ↦ ⟨h⟩⟩

/-- A locally admissible representation is smooth: each `v` lies in the admissible, hence smooth,
subrepresentation `A[G] · v`, whose stabilizers are those of `ρ`. -/
instance IsLocallyAdmissible.isSmooth [h : IsLocallyAdmissible ρ] : IsSmooth ρ :=
  ⟨fun v ↦ (cyclicSubrepresentation ρ v).stabilizer_toRepresentation
    ⟨v, mem_cyclicSubrepresentation_self v⟩ ▸
      (h.isAdmissible_cyclicSubrepresentation v).isOpen_stabilizer _⟩

/-- **Admissible representations are locally admissible** over a noetherian ring. -/
instance IsAdmissible.isLocallyAdmissible [IsNoetherianRing A] [IsAdmissible ρ] :
    IsLocallyAdmissible ρ :=
  ⟨fun _ ↦ inferInstance⟩

/-- A trivial representation is locally admissible: each `A[G] · v` is the `A`-span of `v`, a
finitely generated module with trivial action. -/
instance isLocallyAdmissible_of_isTrivial [ρ.IsTrivial] : IsLocallyAdmissible ρ := ⟨fun v ↦
  have : Module.Finite A (cyclicSubrepresentation ρ v).toSubmodule := by
    have h : (fun g ↦ ρ g v) = fun _ ↦ v := funext (ρ.isTrivial_apply · v)
    rw [toSubmodule_cyclicSubrepresentation, h, Set.range_const]
    infer_instance
  inferInstance⟩

variable (A G) in
/-- The trivial rank-one representation `A` is locally admissible. -/
theorem isLocallyAdmissible_trivial_self : IsLocallyAdmissible (trivial A G A) :=
  inferInstance

end Representation
