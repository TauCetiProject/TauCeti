/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import TauCeti.SetTheory.Descriptive.BorelReducibility

/-!
# Invariant Borel sets and equivariant Borel injections

A *Borel `S∞`-space* is a standard Borel space `X` with an action of `Equiv.Perm ℕ` that is
jointly measurable, `[MeasurableSMul₂ (Equiv.Perm ℕ) X]` (Becker and Kechris); its orbit
equivalence relation is `MulAction.orbitRel`. The facts below hold for the action of any group `G`.

* The restriction of a jointly measurable action to an invariant subset (a `SubMulAction`) is
  jointly measurable (`SubMulAction.instMeasurableSMul₂`). An invariant Borel subset of a standard
  Borel space is standard Borel (`MeasurableSet.standardBorel`), so an invariant Borel subset of a
  Borel `S∞`-space is again one.
* The range of an equivariant map is invariant (`TauCeti.rangeSubMulAction`). For a measurable
  injection from a standard Borel space into a countably separated space it is Borel, by the
  Lusin–Souslin theorem (`TauCeti.measurableSet_rangeSubMulAction`).
* An equivariant injection preserves and reflects the orbit relation
  (`TauCeti.orbitRel_apply_iff_of_smul_eq`), so an equivariant measurable injection is a Borel
  reduction of the orbit relations (`TauCeti.borelReducible_orbitRel_of_smul_eq`).

## References

* H. Becker and A. S. Kechris, *Borel actions of Polish groups*, arXiv:math/9304208; Bull. Amer.
  Math. Soc. 28 (1993).
-/

public section

open Set Function

/-- The restriction of a jointly measurable action to an invariant subset is jointly
measurable. -/
instance SubMulAction.instMeasurableSMul₂ {G X : Type*} [SMul G X] [MeasurableSpace G]
    [MeasurableSpace X] [MeasurableSMul₂ G X] (p : SubMulAction G X) : MeasurableSMul₂ G p :=
  ⟨(measurable_smul.comp (measurable_fst.prodMk (measurable_subtypeVal.comp
    measurable_snd))).subtype_mk⟩

namespace TauCeti

variable {G X Y : Type*}

section SMul

variable [SMul G X] [SMul G Y] {f : X → Y}

/-- The range of an equivariant map, as an invariant subset of the target. -/
def rangeSubMulAction (f : X → Y) (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    SubMulAction G Y where
  carrier := range f
  smul_mem' g := by
    rintro _ ⟨x, rfl⟩
    exact ⟨g • x, hf g x⟩

@[simp]
theorem coe_rangeSubMulAction (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    (rangeSubMulAction f hf : Set Y) = range f :=
  Set.ext fun _ => Iff.rfl

/-- **Lusin–Souslin for equivariant maps.** The range of an equivariant measurable injection from
a standard Borel space into a countably separated space is an invariant Borel set. -/
theorem measurableSet_rangeSubMulAction [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (hf : ∀ (g : G) x, f (g • x) = g • f x) (hmeas : Measurable f) (hinj : Injective f) :
    MeasurableSet (rangeSubMulAction f hf : Set Y) :=
  (hmeas.measurableEmbedding hinj).measurableSet_range

end SMul

section Group

variable [Group G] [MulAction G X] [MulAction G Y] {f : X → Y}

/-- An equivariant injection preserves and reflects the orbit relation. -/
theorem orbitRel_apply_iff_of_smul_eq (hf : ∀ (g : G) x, f (g • x) = g • f x)
    (hinj : Injective f) {x x' : X} :
    MulAction.orbitRel G Y (f x) (f x') ↔ MulAction.orbitRel G X x x' := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, ← hf, hinj.eq_iff]

/-- An equivariant measurable injection is a Borel reduction of the orbit relations. -/
theorem borelReducible_orbitRel_of_smul_eq [MeasurableSpace X] [MeasurableSpace Y]
    (hf : ∀ (g : G) x, f (g • x) = g • f x) (hmeas : Measurable f) (hinj : Injective f) :
    (MulAction.orbitRel G X).BorelReducible (MulAction.orbitRel G Y) :=
  Setoid.borelReducible_iff.2 ⟨f, hmeas, fun _ _ => (orbitRel_apply_iff_of_smul_eq hf hinj).symm⟩

end Group

end TauCeti
