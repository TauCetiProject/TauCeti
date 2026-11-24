/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Hom
public import TauCeti.SetTheory.Descriptive.BorelReducibility

/-!
# Equivariant Borel injections

A *Borel `S∞`-space* is a standard Borel space `X` with an action of `Equiv.Perm ℕ` that is
jointly measurable, `[MeasurableSMul₂ (Equiv.Perm ℕ) X]` (Becker and Kechris); its orbit
equivalence relation is `MulAction.orbitRel`. The facts below hold for the action of any group `G`.

* The restriction of a jointly measurable action to an invariant subset (a `SubMulAction`) is
  jointly measurable (`SubMulAction.instMeasurableSMul₂`, in
  `TauCeti.MeasureTheory.Group.Arithmetic`). An invariant Borel subset of a standard Borel space is
  standard Borel (`MeasurableSet.standardBorel`), so an invariant Borel subset of a Borel
  `S∞`-space is again one.
* The range of an equivariant map is invariant (`MulActionHom.range`). For a measurable
  injection from a standard Borel space into a countably separated space it is Borel, by the
  Lusin–Souslin theorem (`Measurable.measurableEmbedding`,
  `MeasurableEmbedding.measurableSet_range`).
* An injective equivariant map preserves and reflects the orbit relation
  (`TauCeti.MulAction.orbitRel_apply_iff_of_injective`), so an equivariant measurable injection is
  a Borel reduction of the orbit relations (`TauCeti.borelReducible_orbitRel`).

## References

* H. Becker and A. S. Kechris, *Borel actions of Polish groups*, arXiv:math/9304208; Bull. Amer.
  Math. Soc. 28 (1993).
-/

public section

namespace TauCeti

variable {G X Y F : Type*} [Group G] [MulAction G X] [MulAction G Y] [FunLike F X Y]
  [MulActionHomClass F G X Y]

/-- An equivariant measurable injection is a Borel reduction of the orbit relations. -/
theorem borelReducible_orbitRel [MeasurableSpace X] [MeasurableSpace Y] {f : F}
    (hmeas : Measurable f) (hinj : Function.Injective f) :
    (MulAction.orbitRel G X).BorelReducible (MulAction.orbitRel G Y) :=
  Setoid.borelReducible_iff.2
    ⟨f, hmeas, fun _ _ => (MulAction.orbitRel_apply_iff_of_injective hinj).symm⟩

end TauCeti
