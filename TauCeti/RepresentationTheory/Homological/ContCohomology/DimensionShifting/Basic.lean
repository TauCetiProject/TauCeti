/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Separation.Connected
public import TauCeti.Algebra.Category.ModuleCat.Topology.Iso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Acyclic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Basic

/-!
# Acyclicity of `Coind_1^G` and dimension shifting

For a profinite group `G`, the coinduced module `Coind_1^G A` of the trivial subgroup, which is the
group of all locally constant maps `G → A` (`TauCeti.mem_coind_bot_iff`), has vanishing
explicit continuous cohomology in degrees one and two. This is Shapiro's lemma at `U = ⊥`: the
trivial subgroup of a totally disconnected group is closed, and a trivial group has no cohomology
in positive degrees. In every positive degree, and for any compact `G`, the canonical continuous
cohomology of `Coind_1^G A` vanishes by
`TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot`.

Every discrete `G`-module `M` embeds into this acyclic module by its orbit maps, the unit of
coinduction `TauCeti.DiscreteCoind.unit G ⊥ M`,

```text
M ↪ Coind_1^G M,   m ↦ (x ↦ x • m),
```

and the long exact sequence of `0 → M → Coind_1^G M → Coind_1^G M ⧸ M → 0` then shifts degrees:

```text
H²(G, M) ≅ H¹(G, Coind_1^G M ⧸ M),
H¹(G, M) ≅ H⁰(G, Coind_1^G M ⧸ M) ⧸ image of H⁰(G, Coind_1^G M).
```

These are the two instances of `Hⁱ⁺¹(G, M) ≅ Hⁱ(G, Coind_1^G M ⧸ M)` in which both sides live in
the explicit low-degree complex; in degree zero the source `H⁰(G, Coind_1^G M)` need not vanish,
and the statement is the cokernel form. The shift itself is proved for an arbitrary short exact
sequence of discrete modules whose middle term has vanishing `H¹` and `H²`
(`TauCeti.ContCohomology.DiscreteShortExact.explicitDelta1_bijective_of_subsingleton`, in
`TauCeti/RepresentationTheory/Homological/ContCohomology/LongExact.lean`).

In every positive degree the same short exact sequence, fed to the long exact sequence of Mathlib's
canonical continuous cohomology and to the all-degree acyclicity of `Coind_1^G M`, gives

```text
Hⁱ⁺¹(G, M) ≅ Hⁱ(G, Coind_1^G M ⧸ M)   (i ≥ 1)
```

for every compact group `G` (`TauCeti.ContCohomology.dimensionShiftIso`), inverse to the
connecting map, which is an isomorphism (`TauCeti.ContCohomology.isIso_coindShortExact_bot_delta`).

## Main definitions

* `TauCeti.ContCohomology.DimensionShiftQuotient`: the discrete `G`-module `Coind_U^G M ⧸ M`, the
  cokernel of the unit of coinduction for a subgroup `U`; `Coind_1^G M ⧸ M` for `U = ⊥`.
* `TauCeti.ContCohomology.coindShortExact`: the short exact sequence
  `0 → M → Coind_U^G M → Coind_U^G M ⧸ M → 0` of discrete `G`-modules.
* `TauCeti.ContCohomology.explicitDimensionShift1`: `H¹(G, Coind_1^G M ⧸ M) ≃+ H²(G, M)`, the
  connecting map `δ¹`.
* `TauCeti.ContCohomology.explicitDimensionShift0`: the cokernel of
  `H⁰(G, Coind_1^G M) → H⁰(G, Coind_1^G M ⧸ M)` is `H¹(G, M)`, through `δ⁰`.
* `TauCeti.ContCohomology.dimensionShiftIso`: **dimension shifting in every positive degree**,
  `Hⁱ⁺¹(G, M) ≅ Hⁱ(G, Coind_1^G M ⧸ M)` for `i ≥ 1` and the canonical continuous cohomology,
  inverse to the connecting map.

## Main statements

* `TauCeti.ContCohomology.subsingleton_H1_discreteCoind_bot` and
  `subsingleton_H2_discreteCoind_bot`: **acyclicity of `Coind_1^G A`** in degrees one and two,
  for profinite `G`.
* `TauCeti.ContCohomology.isIso_coindShortExact_bot_delta`: the connecting map
  `Hⁱ(G, Coind_1^G M ⧸ M) ⟶ Hⁱ⁺¹(G, M)` is an isomorphism for `i ≥ 1`, for compact `G`.

## Implementation notes

As for `TauCeti.DiscreteCoind`, the quotient is a type synonym carrying the discrete topology; the
quotient topology inherited from `QuotientAddGroup` is not the one used for coefficients. Its
`G`-action is induced by the right-translation action on `Coind_U^G M`, which preserves the image
of `M` because the embedding is `G`-equivariant, and it is continuous because the stabilizer of a
class contains the open stabilizer of any representative.

Compactness of `G` makes the right-translation action on `Coind_1^G M` continuous. The underlying
quotient and its algebraic action do not require compactness, but its `ContinuousSMul` instance
does. Total disconnectedness supplies the `T1` property making the trivial subgroup closed, as
required by the available Shapiro isomorphisms; the acyclicity and the two shifts use both
profinite hypotheses.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.7) and the
  dimension-shifting argument following it; (1.6.4) for Shapiro's lemma, with the footnote on p. 61
  recording that NSW writes `Ind` for the coinduced module used here.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5 and Cor. 6.10.6.
-/

public section

namespace TauCeti.ContCohomology

universe u v

/-! ### Acyclicity of `Coind_1^G A` -/

section Acyclic

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  (A : Type v) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction (⊥ : Subgroup G) A] [ContinuousSMul (⊥ : Subgroup G) A]

/-- **`Coind_1^G A` has vanishing `H¹`**, for a profinite group `G`: Shapiro's lemma identifies
`H¹(G, Coind_1^G A)` with `H¹(1, A)`. -/
instance subsingleton_H1_discreteCoind_bot : Subsingleton (H1 G (DiscreteCoind G ⊥ A)) :=
  (explicitShapiro1 G ⊥ A (Subgroup.coe_bot (G := G) ▸ isClosed_singleton)).injective.subsingleton

/-- **`Coind_1^G A` has vanishing `H²`**, for a profinite group `G`: Shapiro's lemma identifies
`H²(G, Coind_1^G A)` with `H²(1, A)`. -/
instance subsingleton_H2_discreteCoind_bot : Subsingleton (H2 G (DiscreteCoind G ⊥ A)) :=
  (explicitShapiro2 G ⊥ A (Subgroup.coe_bot (G := G) ▸ isClosed_singleton)).injective.subsingleton

end Acyclic

/-! ### The embedding into `Coind_U^G M` and its cokernel -/

section Embedding

variable (G : Type u) [Group G] [TopologicalSpace G] (U : Subgroup G)
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

section ContinuousMul

variable [ContinuousMul G]

/-- **The cokernel `Coind_U^G M ⧸ M` of the unit of coinduction**, the quotient of `Coind_U^G M`
by the image of the embedding `TauCeti.DiscreteCoind.unit G U M`, carrying the discrete topology.
For `U = ⊥` this is the dimension-shifting module `Coind_1^G M ⧸ M`. -/
@[expose] def DimensionShiftQuotient : Type _ :=
  DiscreteCoind G U M ⧸ (DiscreteCoind.unit G U M).toAddMonoidHom.range

namespace DimensionShiftQuotient

/-- `Coind_U^G M ⧸ M` is an additive group, as a quotient of `Coind_U^G M`. -/
instance : AddCommGroup (DimensionShiftQuotient G U M) :=
  inferInstanceAs
    (AddCommGroup (DiscreteCoind G U M ⧸ (DiscreteCoind.unit G U M).toAddMonoidHom.range))

/-- `Coind_U^G M ⧸ M` carries the discrete topology. -/
instance : TopologicalSpace (DimensionShiftQuotient G U M) := ⊥

/-- The topology on `Coind_U^G M ⧸ M` is discrete. -/
instance : DiscreteTopology (DimensionShiftQuotient G U M) := ⟨rfl⟩

/-- The projection `Coind_U^G M → Coind_U^G M ⧸ M`. -/
@[expose] def mk : DiscreteCoind G U M →+ DimensionShiftQuotient G U M := QuotientAddGroup.mk' _

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
theorem induction_on {motive : DimensionShiftQuotient G U M → Prop}
    (q : DimensionShiftQuotient G U M) (h : ∀ f : DiscreteCoind G U M, motive (mk G U M f)) :
    motive q :=
  QuotientAddGroup.induction_on q h

/-- `Coind_U^G M ⧸ M` is finite when `Coind_U^G M` is. -/
instance [Finite (DiscreteCoind G U M)] : Finite (DimensionShiftQuotient G U M) :=
  Finite.of_surjective _ mk_surjective

/-- Right translation on `Coind_U^G M`, descended to the quotient; the image of `M` is preserved
because the embedding is equivariant. -/
instance : DistribMulAction G (DimensionShiftQuotient G U M) where
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

end DimensionShiftQuotient

/-- **The short exact sequence `0 → M → Coind_U^G M → Coind_U^G M ⧸ M → 0`** of discrete
`G`-modules given by the unit of coinduction. For `U = ⊥` it is the sequence on which dimension
shifting runs. -/
def coindShortExact :
    DiscreteShortExact G M (DiscreteCoind G U M) (DimensionShiftQuotient G U M) where
  incl := (DiscreteCoind.unit G U M).toAddMonoidHom
  proj := DimensionShiftQuotient.mk G U M
  incl_equivariant g m := _root_.map_smul (DiscreteCoind.unit G U M) g m
  proj_equivariant := DimensionShiftQuotient.mk_smul
  incl_injective := DiscreteCoind.unit_injective
  proj_surjective := DimensionShiftQuotient.mk_surjective
  exact _ := DimensionShiftQuotient.mk_eq_zero_iff

/-- The first map of the short exact sequence of the unit is the unit `M → Coind_U^G M`. -/
@[simp]
theorem coindShortExact_incl :
    (coindShortExact G U M).incl = (DiscreteCoind.unit G U M).toAddMonoidHom := (rfl)

/-- The second map of the short exact sequence of the unit is the projection `Coind_U^G M →
Coind_U^G M ⧸ M`. -/
@[simp]
theorem coindShortExact_proj :
    (coindShortExact G U M).proj = DimensionShiftQuotient.mk G U M := (rfl)

end ContinuousMul

variable {G U M} in
/-- The action on the quotient is continuous: the stabilizer of a class contains the stabilizer of
any representative, which is open. -/
instance DimensionShiftQuotient.instContinuousSMul [IsTopologicalGroup G] [CompactSpace G] :
    ContinuousSMul G (DimensionShiftQuotient G U M) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun q => ?_
  obtain ⟨f, rfl⟩ := DimensionShiftQuotient.mk_surjective q
  refine Subgroup.isOpen_mono (fun g hg => ?_) (stabilizer_isOpen G f)
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← DimensionShiftQuotient.mk_smul, hg]

end Embedding

/-! ### Dimension shifting -/

section DimensionShift

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **Dimension shifting from degree two to degree one**, `H¹(G, Coind_1^G M ⧸ M) ≅ H²(G, M)`,
for a profinite group `G`: the connecting map `δ¹` of
`TauCeti.ContCohomology.coindShortExact G ⊥ M` is bijective because `Coind_1^G M` is acyclic. -/
noncomputable def explicitDimensionShift1 : H1 G (DimensionShiftQuotient G ⊥ M) ≃+ H2 G M :=
  AddEquiv.ofBijective (coindShortExact G ⊥ M).explicitDelta1
    (coindShortExact G ⊥ M).explicitDelta1_bijective_of_subsingleton

/-- The dimension-shifting isomorphism `H¹(G, Coind_1^G M ⧸ M) ≃ H²(G, M)` is the connecting map
`δ¹`. -/
@[simp]
theorem explicitDimensionShift1_apply (x : H1 G (DimensionShiftQuotient G ⊥ M)) :
    explicitDimensionShift1 G M x = (coindShortExact G ⊥ M).explicitDelta1 x := (rfl)

/-- **Dimension shifting from degree one to degree zero**, for a profinite group `G`: `H¹(G, M)` is
the cokernel of `H⁰(G, Coind_1^G M) → H⁰(G, Coind_1^G M ⧸ M)`, through the connecting map `δ⁰`,
which is surjective because `Coind_1^G M` has vanishing `H¹`. -/
noncomputable def explicitDimensionShift0 :
    H0 G (DimensionShiftQuotient G ⊥ M) ⧸
        (explicitCoeff0 G (DiscreteCoind G ⊥ M)
          (coindShortExact G ⊥ M).projDistribMulActionHom).range ≃+ H1 G M :=
  (QuotientAddGroup.quotientAddEquivOfEq (coindShortExact G ⊥ M).explicitLongExact_H0C).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (coindShortExact G ⊥ M).explicitDelta0_surjective_of_subsingleton)

/-- The dimension-shifting isomorphism onto `H¹(G, M)` sends the class of `x ∈ H⁰(G, Coind_1^G M ⧸
M)` to `δ⁰ x`. -/
@[simp]
theorem explicitDimensionShift0_mk (x : H0 G (DimensionShiftQuotient G ⊥ M)) :
    explicitDimensionShift0 G M x = (coindShortExact G ⊥ M).explicitDelta0 x := by
  rw [explicitDimensionShift0, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk,
    QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse_apply,
    QuotientAddGroup.kerLift_mk]

end DimensionShift

/-! ### Dimension shifting in every degree -/

section DimensionShiftAll

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

open CategoryTheory Limits

/-- **The connecting map of the dimension-shifting sequence is an isomorphism in every positive
degree**: `δ : Hⁱ(G, Coind_1^G M ⧸ M) ⟶ Hⁱ⁺¹(G, M)` for `i ≥ 1` and a compact group `G`, because
`Coind_1^G M` is acyclic in degrees `i` and `i + 1`. -/
theorem isIso_coindShortExact_bot_delta (i : ℕ) (hi : 0 < i) :
    IsIso ((coindShortExact G ⊥ M).delta i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi.ne'
  exact (coindShortExact G ⊥ M).isIso_delta (n + 1)

/-- **Dimension shifting in every positive degree**, `Hⁱ⁺¹(G, M) ≅ Hⁱ(G, Coind_1^G M ⧸ M)` for
`i ≥ 1` and a compact group `G`, as an isomorphism of Mathlib's canonical continuous cohomology. Its
inverse is the connecting map of `TauCeti.ContCohomology.coindShortExact G ⊥ M`
(`dimensionShiftIso_inv`), an isomorphism by `isIso_coindShortExact_bot_delta`. The analogous
statement on the explicit low-degree model, for a profinite `G` and in the direction of the
connecting map, is `TauCeti.ContCohomology.explicitDimensionShift1 :
H¹(G, Coind_1^G M ⧸ M) ≃+ H²(G, M)`. -/
noncomputable def dimensionShiftIso (i : ℕ) (hi : 0 < i) :
    continuousCohomology (i + 1) (ofDiscreteModule ℤ G M) ≅
      continuousCohomology i (ofDiscreteModule ℤ G (DimensionShiftQuotient G ⊥ M)) :=
  (@asIso _ _ _ _ ((coindShortExact G ⊥ M).delta i)
    (isIso_coindShortExact_bot_delta G M i hi)).symm

/-- The inverse of the dimension-shifting isomorphism is the connecting map. -/
@[simp]
theorem dimensionShiftIso_inv (i : ℕ) (hi : 0 < i) :
    (dimensionShiftIso G M i hi).inv = (coindShortExact G ⊥ M).delta i := by
  rw [dimensionShiftIso, Iso.symm_inv, asIso_hom]

end DimensionShiftAll

end TauCeti.ContCohomology
