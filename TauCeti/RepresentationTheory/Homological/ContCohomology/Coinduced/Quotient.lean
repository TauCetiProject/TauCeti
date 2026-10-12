/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# The cokernel of the unit of coinduction

For a subgroup `U` of a topological group `G` and a discrete `G`-module `M`, the unit of
coinduction `TauCeti.DiscreteCoind.unit G U M` embeds `M` into `Coind_U^G M` by its orbit maps,

```text
M ↪ Coind_U^G M,   m ↦ (x ↦ x • m).
```

This file builds its cokernel `Coind_U^G M ⧸ M` as a discrete `G`-module and the resulting short
exact sequence `0 → M → Coind_U^G M → Coind_U^G M ⧸ M → 0` of discrete `G`-modules. For `U = ⊥` it
is the sequence on which dimension shifting runs
(`TauCeti/RepresentationTheory/Homological/ContCohomology/DimensionShifting/Basic.lean`); for an
open subgroup `U` it feeds the reduction of finiteness of cohomology to an open subgroup.

## Main definitions

* `TauCeti.ContCohomology.CoindQuotient`: the discrete `G`-module `Coind_U^G M ⧸ M`, the
  cokernel of the unit of coinduction for a subgroup `U`.
* `TauCeti.ContCohomology.coindShortExact`: the short exact sequence
  `0 → M → Coind_U^G M → Coind_U^G M ⧸ M → 0` of discrete `G`-modules.

## Main results

* `TauCeti.ContCohomology.CoindQuotient.smul_eq_self_of_forall_smul_eq_self`: a normal subgroup
  `U` acting trivially on `M` acts trivially on `Coind_U^G M ⧸ M`.
* `TauCeti.ContCohomology.precomp_coindShortExact_inclDistribMulActionHom_surjective`: every
  homomorphism out of `M` extends along the unit, so `coindShortExact` has a dual sequence.

## Implementation notes

As for `TauCeti.DiscreteCoind`, the quotient is a type synonym carrying the discrete topology; the
quotient topology inherited from `QuotientAddGroup` is not the one used for coefficients. Its
`G`-action is induced by the right-translation action on `Coind_U^G M`, which preserves the image
of `M` because the embedding is `G`-equivariant, and it is continuous because the stabilizer of a
class contains the open stabilizer of any representative.

Compactness of `G` makes the right-translation action on `Coind_U^G M` continuous. The underlying
quotient and its algebraic action do not require compactness, but its `ContinuousSMul` instance
does.
-/

public section

namespace TauCeti.ContCohomology

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] (U : Subgroup G)
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

section ContinuousMul

variable [ContinuousMul G]

/-- **The cokernel `Coind_U^G M ⧸ M` of the unit of coinduction**, the quotient of `Coind_U^G M`
by the image of the embedding `TauCeti.DiscreteCoind.unit G U M`, carrying the discrete topology.
For `U = ⊥` this is the dimension-shifting module `Coind_1^G M ⧸ M`. -/
@[expose] def CoindQuotient : Type _ :=
  DiscreteCoind G U M ⧸ (DiscreteCoind.unit G U M).toAddMonoidHom.range

namespace CoindQuotient

/-- `Coind_U^G M ⧸ M` is an additive group, as a quotient of `Coind_U^G M`. -/
instance : AddCommGroup (CoindQuotient G U M) :=
  inferInstanceAs
    (AddCommGroup (DiscreteCoind G U M ⧸ (DiscreteCoind.unit G U M).toAddMonoidHom.range))

/-- `Coind_U^G M ⧸ M` carries the discrete topology. -/
instance : TopologicalSpace (CoindQuotient G U M) := ⊥

/-- The topology on `Coind_U^G M ⧸ M` is discrete. -/
instance : DiscreteTopology (CoindQuotient G U M) := ⟨rfl⟩

/-- The projection `Coind_U^G M → Coind_U^G M ⧸ M`. -/
@[expose] def mk : DiscreteCoind G U M →+ CoindQuotient G U M := QuotientAddGroup.mk' _

variable {G U M}

/-- The projection `Coind_U^G M → Coind_U^G M ⧸ M` is surjective. -/
theorem mk_surjective : Function.Surjective (mk G U M) := QuotientAddGroup.mk'_surjective _

/-- A coinduced element dies in the quotient exactly when it is in the image of the unit. -/
@[simp]
theorem mk_eq_zero_iff {f : DiscreteCoind G U M} :
    mk G U M f = 0 ↔ f ∈ (DiscreteCoind.unit G U M).toAddMonoidHom.range :=
  QuotientAddGroup.eq_zero_iff f

/-- Induction on `Coind_U^G M ⧸ M`: a property of the classes of all coinduced elements holds for
every element of the quotient. -/
@[elab_as_elim]
theorem induction_on {motive : CoindQuotient G U M → Prop}
    (q : CoindQuotient G U M) (h : ∀ f : DiscreteCoind G U M, motive (mk G U M f)) :
    motive q :=
  QuotientAddGroup.induction_on q h

/-- `Coind_U^G M ⧸ M` is finite when `Coind_U^G M` is. -/
instance [Finite (DiscreteCoind G U M)] : Finite (CoindQuotient G U M) :=
  Finite.of_surjective _ mk_surjective

/-- Right translation on `Coind_U^G M`, descended to the quotient; the image of `M` is preserved
because the embedding is equivariant. -/
instance : DistribMulAction G (CoindQuotient G U M) where
  smul g := QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom (DiscreteCoind G U M) g) <| by
    rintro _ ⟨m, rfl⟩
    exact ⟨g • m, _root_.map_smul (DiscreteCoind.unit G U M) g m⟩
  one_smul q := induction_on q fun f => congrArg (mk G U M) (one_smul G f)
  mul_smul g h q := induction_on q fun f => congrArg (mk G U M) (mul_smul g h f)
  smul_zero g := map_zero (QuotientAddGroup.map _ _ _ _)
  smul_add g := map_add (QuotientAddGroup.map _ _ _ _)

/-- The projection is `G`-equivariant. -/
@[simp]
theorem mk_smul (g : G) (f : DiscreteCoind G U M) : mk G U M (g • f) = g • mk G U M f := (rfl)

/-- **A normal subgroup acting trivially on `M` acts trivially on `Coind_U^G M ⧸ M`**, as it does on
`Coind_U^G M` (`TauCeti.DiscreteCoind.smul_eq_self_of_forall_smul_eq_self`). -/
theorem smul_eq_self_of_forall_smul_eq_self [U.Normal] (htriv : ∀ (u : U) (m : M), u • m = m)
    {g : G} (hg : g ∈ U) (q : CoindQuotient G U M) : g • q = q := by
  induction q using induction_on with
  | h f => rw [← mk_smul, DiscreteCoind.smul_eq_self_of_forall_smul_eq_self htriv hg f]

end CoindQuotient

/-- **The short exact sequence `0 → M → Coind_U^G M → Coind_U^G M ⧸ M → 0`** of discrete
`G`-modules given by the unit of coinduction. For `U = ⊥` it is the sequence on which dimension
shifting runs. -/
def coindShortExact :
    DiscreteShortExact G M (DiscreteCoind G U M) (CoindQuotient G U M) where
  incl := (DiscreteCoind.unit G U M).toAddMonoidHom
  proj := CoindQuotient.mk G U M
  incl_equivariant g m := _root_.map_smul (DiscreteCoind.unit G U M) g m
  proj_equivariant := CoindQuotient.mk_smul
  incl_injective := DiscreteCoind.unit_injective
  proj_surjective := CoindQuotient.mk_surjective
  exact _ := CoindQuotient.mk_eq_zero_iff

/-- The first map of the short exact sequence of the unit is the unit `M → Coind_U^G M`. -/
@[simp]
theorem coindShortExact_incl :
    (coindShortExact G U M).incl = (DiscreteCoind.unit G U M).toAddMonoidHom := (rfl)

/-- The second map of the short exact sequence of the unit is the projection `Coind_U^G M →
Coind_U^G M ⧸ M`. -/
@[simp]
theorem coindShortExact_proj :
    (coindShortExact G U M).proj = CoindQuotient.mk G U M := (rfl)

/-- **Homomorphisms out of `M` extend along the unit of coinduction**: precomposition with the
inclusion of `coindShortExact` is surjective on internal homs into any `N`, since `φ : M →+ N`
extends to `Coind_U^G M` as `f ↦ φ (f 1)`. So the dual sequence of `coindShortExact`
(`TauCeti.ContCohomology.DiscreteShortExact.dual`) exists for all coefficients. -/
theorem precomp_coindShortExact_inclDistribMulActionHom_surjective {N : Type*} [AddCommGroup N]
    [DistribMulAction G N] :
    Function.Surjective
      (InternalHom.precomp G (coindShortExact G U M).inclDistribMulActionHom (N := N)) :=
  InternalHom.precomp_surjective_of_forall_exists_comp_eq fun φ =>
    ⟨φ.comp (DiscreteCoind.eval G U M), AddMonoidHom.ext fun m => by simp⟩

end ContinuousMul

variable {G U M} in
/-- The action on the quotient is continuous: the stabilizer of a class contains the stabilizer of
any representative, which is open. -/
instance CoindQuotient.instContinuousSMul [IsTopologicalGroup G] [CompactSpace G] :
    ContinuousSMul G (CoindQuotient G U M) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun q => ?_
  obtain ⟨f, rfl⟩ := CoindQuotient.mk_surjective q
  refine Subgroup.isOpen_mono (fun g hg => ?_) (stabilizer_isOpen G f)
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← CoindQuotient.mk_smul, hg]

end TauCeti.ContCohomology
