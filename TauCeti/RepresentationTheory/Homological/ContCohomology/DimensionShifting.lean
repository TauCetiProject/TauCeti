/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Separation.Connected
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro

/-!
# Acyclicity of `Coind_1^G` and dimension shifting in low degrees

For a profinite group `G`, the coinduced module `Coind_1^G A` of the trivial subgroup, which is the
group of all locally constant maps `G → A` (`TauCeti.mem_coind_bot_iff`), has vanishing
continuous cohomology in degrees one and two. This is Shapiro's lemma at `U = ⊥`: the trivial
subgroup of a totally disconnected group is closed, and a trivial group has no cohomology in
positive degrees.

Every discrete `G`-module `M` embeds into this acyclic module by its orbit maps,

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

## Main definitions

* `TauCeti.ContCohomology.coindBotEmbedding`: the orbit-map embedding `M → Coind_1^G M`.
* `TauCeti.ContCohomology.DimensionShiftQuotient`: the discrete `G`-module `Coind_1^G M ⧸ M`.
* `TauCeti.ContCohomology.coindBotShortExact`: the short exact sequence
  `0 → M → Coind_1^G M → Coind_1^G M ⧸ M → 0` of discrete `G`-modules.
* `TauCeti.ContCohomology.explicitDimensionShift1`: `H¹(G, Coind_1^G M ⧸ M) ≃+ H²(G, M)`, the
  connecting map `δ¹`.
* `TauCeti.ContCohomology.explicitDimensionShift0`: the cokernel of
  `H⁰(G, Coind_1^G M) → H⁰(G, Coind_1^G M ⧸ M)` is `H¹(G, M)`, through `δ⁰`.

## Main statements

* `TauCeti.ContCohomology.subsingleton_H1_of_subsingleton` and
  `subsingleton_H2_of_subsingleton`: a trivial group has vanishing `H¹` and `H²`.
* `TauCeti.ContCohomology.subsingleton_H1_discreteCoind_bot` and
  `subsingleton_H2_discreteCoind_bot`: **acyclicity of `Coind_1^G A`** in degrees one and two,
  for profinite `G`.

## Implementation notes

As for `TauCeti.DiscreteCoind`, the quotient is a type synonym carrying the discrete topology; the
quotient topology inherited from `QuotientAddGroup` is not the one used for coefficients. Its
`G`-action is induced by the right-translation action on `Coind_1^G M`, which preserves the image
of `M` because the embedding is equivariant (`TauCeti.ContCohomology.coindBotEmbedding_smul`), and
it is continuous because the stabilizer of a class contains the open stabilizer of any
representative.

Compactness of `G` makes the right-translation action on `Coind_1^G M` continuous, and total
disconnectedness makes `G` a `T1` space, so that the trivial subgroup is closed, which is what
Shapiro's lemma asks of it. The embedding and the quotient need neither; only the acyclicity and
the two shifts use them.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.7) and the
  dimension-shifting argument following it; (1.6.4) for Shapiro's lemma, with the footnote on p. 61
  recording that NSW writes `Ind` for the coinduced module used here.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5 and Cor. 6.10.6.
-/

public section

namespace TauCeti.ContCohomology

universe u v

/-! ### The cohomology of a trivial group -/

section TrivialGroup

variable (H : Type u) [Monoid H] [TopologicalSpace H] [Subsingleton H]
  (A : Type v) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction H A] [ContinuousSMul H A]

/-- **A trivial group has vanishing `H¹`**: a `1`-cocycle satisfies `f 1 = 1 • f 1 + f 1`, so it
vanishes at the only element. -/
instance subsingleton_H1_of_subsingleton : Subsingleton (H1 H A) := by
  have hzero : ∀ f : Z1 H A, (f : H → A) = 0 := fun f => funext fun g => by
    have h := (mem_Z1_iff.1 f.2).2 1 1
    rw [Subsingleton.elim g 1]
    rw [mul_one, one_smul] at h
    simpa using h
  refine ⟨fun x y => ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    induction y using QuotientAddGroup.induction_on with
    | _ f' =>
      refine H1pi_eq_iff.2 ?_
      rw [hzero f, hzero f', sub_zero]
      exact zero_mem _

/-- **A trivial group has vanishing `H²`**: a `2`-cochain `f` is the coboundary of the constant
`1`-cochain at `f (1, 1)`. -/
instance subsingleton_H2_of_subsingleton [ContinuousMul H] : Subsingleton (H2 H A) := by
  have hB : ∀ f : H × H → A, f ∈ B2 H A := fun f => mem_B2_iff'.2
    ⟨fun _ => f (1, 1), continuous_const, fun g h => by
      rw [Subsingleton.elim g 1, Subsingleton.elim h 1, one_smul, sub_add_cancel]⟩
  refine ⟨fun x y => ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    induction y using QuotientAddGroup.induction_on with
    | _ f' => exact H2pi_eq_iff.2 (hB _)

end TrivialGroup

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

/-! ### The embedding into `Coind_1^G M` and its cokernel -/

section Embedding

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **The embedding `M ↪ Coind_1^G M`**, sending `m` to its orbit map `x ↦ x • m`, which is
locally constant because the action is continuous and `M` is discrete. -/
def coindBotEmbedding : M →+ DiscreteCoind G ⊥ M where
  toFun m := DiscreteCoind.mk G ⊥ M (fun x => x • m)
    ((IsLocallyConstant.iff_continuous _).2 (continuous_id.smul continuous_const))
    (fun u g => by rw [Subsingleton.elim u 1, one_smul, OneMemClass.coe_one, one_mul])
  map_zero' := DiscreteCoind.ext fun x => smul_zero x
  map_add' m m' := DiscreteCoind.ext fun x => smul_add x m m'

@[simp]
theorem coindBotEmbedding_apply (m : M) (x : G) : coindBotEmbedding G M m x = x • m := (rfl)

/-- The embedding is injective: evaluation at `1` recovers `m`. -/
theorem coindBotEmbedding_injective : Function.Injective (coindBotEmbedding G M) := fun m m' h => by
  simpa using DFunLike.congr_fun h 1

/-- The embedding is `G`-equivariant for the right-translation action on `Coind_1^G M`. -/
theorem coindBotEmbedding_smul [ContinuousMul G] (g : G) (m : M) :
    coindBotEmbedding G M (g • m) = g • coindBotEmbedding G M m :=
  DiscreteCoind.ext fun x => by simp [mul_smul]

/-- **The dimension-shifting module `Coind_1^G M ⧸ M`**, the cokernel of
`TauCeti.ContCohomology.coindBotEmbedding`, carrying the discrete topology. -/
@[expose] def DimensionShiftQuotient : Type _ :=
  DiscreteCoind G ⊥ M ⧸ (coindBotEmbedding G M).range

namespace DimensionShiftQuotient

instance : AddCommGroup (DimensionShiftQuotient G M) :=
  inferInstanceAs (AddCommGroup (DiscreteCoind G ⊥ M ⧸ (coindBotEmbedding G M).range))

instance : TopologicalSpace (DimensionShiftQuotient G M) := ⊥

instance : DiscreteTopology (DimensionShiftQuotient G M) := ⟨rfl⟩

/-- The projection `Coind_1^G M → Coind_1^G M ⧸ M`. -/
@[expose] def mk : DiscreteCoind G ⊥ M →+ DimensionShiftQuotient G M := QuotientAddGroup.mk' _

variable {G M}

theorem mk_surjective : Function.Surjective (mk G M) := QuotientAddGroup.mk'_surjective _

/-- A coinduced element dies in the quotient exactly when it is an orbit map. -/
theorem mk_eq_zero_iff {f : DiscreteCoind G ⊥ M} :
    mk G M f = 0 ↔ f ∈ (coindBotEmbedding G M).range :=
  QuotientAddGroup.eq_zero_iff f

@[elab_as_elim]
theorem induction_on {motive : DimensionShiftQuotient G M → Prop} (q : DimensionShiftQuotient G M)
    (h : ∀ f : DiscreteCoind G ⊥ M, motive (mk G M f)) : motive q :=
  QuotientAddGroup.induction_on q h

section Action

variable [ContinuousMul G]

/-- Right translation on `Coind_1^G M`, descended to the quotient; the image of `M` is preserved
because the embedding is equivariant. -/
instance : DistribMulAction G (DimensionShiftQuotient G M) where
  smul g := QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom (DiscreteCoind G ⊥ M) g) <| by
    rintro _ ⟨m, rfl⟩
    exact ⟨g • m, coindBotEmbedding_smul G M g m⟩
  one_smul q := induction_on q fun f => congrArg (mk G M) (one_smul G f)
  mul_smul g h q := induction_on q fun f => congrArg (mk G M) (mul_smul g h f)
  smul_zero g := map_zero (QuotientAddGroup.map _ _ _ _)
  smul_add g := map_add (QuotientAddGroup.map _ _ _ _)

/-- The projection is `G`-equivariant. -/
@[simp]
theorem mk_smul (g : G) (f : DiscreteCoind G ⊥ M) : mk G M (g • f) = g • mk G M f := (rfl)

end Action

/-- The action on the quotient is continuous: the stabilizer of a class contains the stabilizer of
any representative, which is open. -/
instance [IsTopologicalGroup G] [CompactSpace G] :
    ContinuousSMul G (DimensionShiftQuotient G M) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun q => ?_
  obtain ⟨f, rfl⟩ := mk_surjective q
  refine Subgroup.isOpen_mono (fun g hg => ?_) (stabilizer_isOpen G f)
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← mk_smul, hg]

end DimensionShiftQuotient

variable [ContinuousMul G]

/-- **The short exact sequence `0 → M → Coind_1^G M → Coind_1^G M ⧸ M → 0`** of discrete
`G`-modules on which dimension shifting runs. -/
def coindBotShortExact :
    DiscreteShortExact G M (DiscreteCoind G ⊥ M) (DimensionShiftQuotient G M) where
  incl := coindBotEmbedding G M
  proj := DimensionShiftQuotient.mk G M
  incl_equivariant := coindBotEmbedding_smul G M
  proj_equivariant := DimensionShiftQuotient.mk_smul
  incl_injective := coindBotEmbedding_injective G M
  proj_surjective := DimensionShiftQuotient.mk_surjective
  exact _ := DimensionShiftQuotient.mk_eq_zero_iff

@[simp]
theorem coindBotShortExact_incl : (coindBotShortExact G M).incl = coindBotEmbedding G M := (rfl)

@[simp]
theorem coindBotShortExact_proj :
    (coindBotShortExact G M).proj = DimensionShiftQuotient.mk G M := (rfl)

end Embedding

/-! ### Dimension shifting -/

section DimensionShift

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **Dimension shifting from degree two to degree one**, `H¹(G, Coind_1^G M ⧸ M) ≅ H²(G, M)`,
for a profinite group `G`: the connecting map `δ¹` of `TauCeti.ContCohomology.coindBotShortExact`
is bijective because `Coind_1^G M` is acyclic. -/
noncomputable def explicitDimensionShift1 : H1 G (DimensionShiftQuotient G M) ≃+ H2 G M :=
  AddEquiv.ofBijective (coindBotShortExact G M).explicitDelta1
    (coindBotShortExact G M).explicitDelta1_bijective_of_subsingleton

@[simp]
theorem explicitDimensionShift1_apply (x : H1 G (DimensionShiftQuotient G M)) :
    explicitDimensionShift1 G M x = (coindBotShortExact G M).explicitDelta1 x := (rfl)

/-- **Dimension shifting from degree one to degree zero**, for a profinite group `G`: `H¹(G, M)` is
the cokernel of `H⁰(G, Coind_1^G M) → H⁰(G, Coind_1^G M ⧸ M)`, through the connecting map `δ⁰`,
which is surjective because `Coind_1^G M` has vanishing `H¹`. -/
noncomputable def explicitDimensionShift0 :
    H0 G (DimensionShiftQuotient G M) ⧸
        (explicitCoeff0 G (DiscreteCoind G ⊥ M)
          (coindBotShortExact G M).projDistribMulActionHom).range ≃+ H1 G M :=
  (QuotientAddGroup.quotientAddEquivOfEq (coindBotShortExact G M).explicitLongExact_H0C).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (coindBotShortExact G M).explicitDelta0_surjective_of_subsingleton)

@[simp]
theorem explicitDimensionShift0_mk (x : H0 G (DimensionShiftQuotient G M)) :
    explicitDimensionShift0 G M x = (coindBotShortExact G M).explicitDelta0 x := (rfl)

end DimensionShift

end TauCeti.ContCohomology
