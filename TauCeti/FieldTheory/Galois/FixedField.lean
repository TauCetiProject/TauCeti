/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import TauCeti.Algebra.Group.Subgroup.ZPowers
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Fixed fields and fixing subgroups

Complements to Mathlib's Galois correspondence: its interaction with the complete-lattice
operations, when a fixed field and an intermediate field generate the whole extension, when the
correspondence survives dropping finiteness of `M / K` for a finite subgroup, and what the
correspondence gives for a cyclic subgroup.

Taking fixed fields always sends joins of automorphism subgroups to intersections of intermediate
fields. For a finite Galois extension it also sends subgroup intersections to composita of fixed
fields. Both the binary and indexed forms are recorded so that finite generating families and
arbitrary families can use these lattice laws without manually passing through the order dual in
the Galois correspondence.

For a finite Galois extension `M / K`, a subgroup `H ≤ Gal(M/K)` and an intermediate field `E`,
the fixed field of `H` and `E` generate `M` exactly when `H` meets the fixers of `E` trivially.
With no hypothesis on `M / K`, the fixers of an arbitrary join of intermediate fields are the
automorphisms fixing each of them.

The correspondence is equivariant for conjugation: the fixed field of a conjugate subgroup is the
image of the fixed field under the conjugating automorphism.

The correspondence between subgroups and their fixed fields also holds with no hypothesis on
`M / K` at all, provided the subgroup is finite: Artin's theorem makes `M` finite Galois over the
fixed field of a finite `H`, and the fixers of that field are then exactly `H`. This is how a
subgroup of the automorphism group of an infinite extension is recovered from the field it cuts
out; the fixing subgroup of a subfield of finite degree is finite for the same reason.

The last results specialise the correspondence to a *cyclic* subgroup: the field fixed by a finite
cyclic group of automorphisms has `M` cyclic over it, and for `⟨σ⟩` there is a named automorphism
over the fixed field — `AlgEquiv.toFixedFieldAlgEquiv σ` acts on `M` as `σ` does, and generates
once `⟨σ⟩` is finite.

Neither `M / K` Galois nor `M / K` finite is needed, and neither is faithfulness of the action:
`FixedPoints.toAlgAut_surjective` asks only that the group be finite, and cyclicity passes along
its surjection. The fixed-point subfield it produces is the one underlying
`IntermediateField.fixedField`.

A simple extension `K⟮x⟯` is fixed pointwise by exactly those automorphisms that fix `x`, so
its fixing subgroup is the stabilizer of `x`; this too needs no hypothesis on `M / K` at all.

Two facts hold for every intermediate field `E` algebraic over `K`, with no separability anywhere
and nothing asked of `M / K`: its fixing subgroup is closed in the Krull topology, being the
intersection over the finite simple subextensions of their open fixing subgroups; and it is
unchanged by cutting `E` down to its part inside `separableClosure K M`, because every element of
`E` has a `q`-th power iterate there. The second is why a Galois correspondence over an
inseparable extension can only be indexed by the intermediate fields of the separable closure.

## Main results

* `Subgroup.fixedField_inf` and `Subgroup.fixedField_sup`
* `Subgroup.fixedField_iInf` and `Subgroup.fixedField_iSup`
* `Subgroup.fixedField_sInf` and `Subgroup.fixedField_sSup`
* `Subgroup.fixedField_sup_eq_top_iff`
* `Subgroup.fixedField_map_conj`
* `IntermediateField.fixingSubgroup_inf`
* `IntermediateField.fixingSubgroup_iSup`
* `IntermediateField.fixingSubgroup_isClosed_of_isAlgebraic`
* `IntermediateField.fixingSubgroup_inf_separableClosure`
* `IntermediateField.fixingSubgroup_fixedField_of_finite`
* `IntermediateField.finite_of_finiteDimensional_fixedField`
* `IntermediateField.card_fixingSubgroup_le`
* `IntermediateField.fixingSubgroup_adjoin_simple`, with
  `IntermediateField.mem_fixedField_stabilizer`,
  `IntermediateField.fixedField_stabilizer_eq_adjoin_simple`,
  `IntermediateField.fixedField_iInf_stabilizer_eq_adjoin_range` and
  `IntermediateField.adjoin_eq_top_of_fixedField_stabilizer`: the stabilizer of `x` fixes
  exactly `K⟮x⟯`, in which `x` is a primitive element
* `FixedPoints.isCyclic_algEquiv`
* `AlgEquiv.toFixedFieldAlgEquiv`, with `AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top` and
  `AlgEquiv.card_algEquiv_fixedField_zpowers`
-/

public section

open IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **The fixed field of an intersection is the compositum of the fixed fields.** For a finite
Galois extension, the Galois correspondence reverses binary meets and joins. -/
@[simp]
theorem fixedField_inf [FiniteDimensional K M] [IsGalois K M]
    (H H' : Subgroup (M ≃ₐ[K] M)) :
    fixedField (H ⊓ H') = fixedField H ⊔ fixedField H' := by
  have h := (IsGalois.intermediateFieldEquivSubgroup (F := K) (E := M)).symm.map_sup
    (OrderDual.toDual H) (OrderDual.toDual H')
  simpa only [IsGalois.intermediateFieldEquivSubgroup_symm_apply, ofDual_sup,
    OrderDual.ofDual_toDual] using h

/-- **The fixed field of generated subgroups is the intersection of their fixed fields.** This
direction needs no finiteness or Galois hypothesis: fixing every generator is exactly fixing the
subgroup they generate. At the level of carriers, this is `fixedPoints_subgroup_sup`. -/
@[simp]
theorem fixedField_sup (H H' : Subgroup (M ≃ₐ[K] M)) :
    fixedField (H ⊔ H') = fixedField H ⊓ fixedField H' := by
  apply SetLike.coe_injective
  rw [IntermediateField.coe_inf]
  change MulAction.fixedPoints (↑(H ⊔ H')) M =
    MulAction.fixedPoints (↑H) M ∩ MulAction.fixedPoints (↑H') M
  exact fixedPoints_subgroup_sup (M := M ≃ₐ[K] M) (α := M)

/-- **The fixed field of a common intersection is the compositum of the fixed fields.** This is
the indexed Galois-lattice law: an element fixed by every automorphism common to all `H i` lies in
the field generated by the individual fixed fields. -/
@[simp]
theorem fixedField_iInf [FiniteDimensional K M] [IsGalois K M]
    {I : Sort*} (H : I → Subgroup (M ≃ₐ[K] M)) :
    fixedField (⨅ i, H i) = ⨆ i, fixedField (H i) := by
  have h := (IsGalois.intermediateFieldEquivSubgroup (F := K) (E := M)).symm.map_iSup
    (fun i ↦ OrderDual.toDual (H i))
  simpa only [IsGalois.intermediateFieldEquivSubgroup_symm_apply,
    ofDual_iSup, OrderDual.ofDual_toDual] using h

/-- **The fixed field of the subgroups generated by a family is their common fixed field.** This
direction, like `Subgroup.fixedField_sup`, needs no finiteness or Galois hypothesis. At the level
of carriers, this is `fixedPoints_subgroup_iSup`. -/
@[simp]
theorem fixedField_iSup {I : Sort*} (H : I → Subgroup (M ≃ₐ[K] M)) :
    fixedField (⨆ i, H i) = ⨅ i, fixedField (H i) := by
  apply SetLike.coe_injective
  rw [IntermediateField.coe_iInf]
  change MulAction.fixedPoints (↑(⨆ i, H i)) M = ⋂ i, MulAction.fixedPoints (↑(H i)) M
  exact fixedPoints_subgroup_iSup (M := M ≃ₐ[K] M) (α := M)

/-- **The fixed field of the infimum of a set of subgroups is the compositum of their fixed
fields.** This is the set-indexed form of `Subgroup.fixedField_iInf`. -/
@[simp]
theorem fixedField_sInf [FiniteDimensional K M] [IsGalois K M]
    (S : Set (Subgroup (M ≃ₐ[K] M))) :
    fixedField (sInf S) = ⨆ H ∈ S, fixedField H := by
  rw [sInf_eq_iInf, fixedField_iInf]
  simp only [fixedField_iInf]

/-- **The fixed field of the supremum of a set of subgroups is the intersection of their fixed
fields.** This is the set-indexed form of `Subgroup.fixedField_iSup`. -/
@[simp]
theorem fixedField_sSup (S : Set (Subgroup (M ≃ₐ[K] M))) :
    fixedField (sSup S) = ⨅ H ∈ S, fixedField H := by
  rw [sSup_eq_iSup, fixedField_iSup]
  simp only [fixedField_iSup]

/-- **A trivial meet of subgroups is a full join of fields.** `M ^ H` and `E` generate `M` exactly
when `H ⊓ Gal(M/E)` is trivial.

This is the Galois correspondence read in both directions: `fixingSubgroup` turns a join of fields
into a meet of subgroups, and `fixedField` turns the trivial subgroup back into `⊤`.

Stated in the `Subgroup` namespace rather than `IntermediateField`, so that `H` — the first
explicit argument, and the one `fixedField` is applied to — carries the dot notation: a consumer
writes `H.fixedField_sup_eq_top_iff E`. -/
theorem fixedField_sup_eq_top_iff [FiniteDimensional K M] [IsGalois K M]
    (H : Subgroup (M ≃ₐ[K] M)) (E : IntermediateField K M) :
    fixedField H ⊔ E = ⊤ ↔ H ⊓ E.fixingSubgroup = ⊥ := by
  constructor
  · intro h
    have := congrArg IntermediateField.fixingSubgroup h
    rwa [fixingSubgroup_sup, fixingSubgroup_fixedField, fixingSubgroup_top] at this
  · intro h
    have hbot : (fixedField H ⊔ E).fixingSubgroup = ⊥ := by
      rw [fixingSubgroup_sup, fixingSubgroup_fixedField, h]
    have := congrArg fixedField hbot
    rwa [IsGalois.fixedField_fixingSubgroup, fixedField_bot] at this

end Subgroup

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **The Galois correspondence turns a meet of fields into a join of subgroups.** In a finite
Galois extension, the automorphisms fixing `E ⊓ E'` pointwise form the subgroup generated by those
fixing `E` and those fixing `E'`. The dual `IntermediateField.fixingSubgroup_sup` holds with no
hypothesis on `M / K`; this direction needs the full correspondence. -/
theorem fixingSubgroup_inf [FiniteDimensional K M] [IsGalois K M] (E E' : IntermediateField K M) :
    (E ⊓ E').fixingSubgroup = E.fixingSubgroup ⊔ E'.fixingSubgroup :=
  congrArg OrderDual.ofDual
    ((IsGalois.intermediateFieldEquivSubgroup (F := K) (E := M)).map_inf E E')

/-- **The fixing subgroup of a join of fields is the meet of the fixing subgroups.** An
automorphism fixes `⨆ i, E i` pointwise exactly when it fixes every `E i` pointwise. This is the
indexed form of Mathlib's `IntermediateField.fixingSubgroup_sup`, and like it needs no hypothesis
on `M / K`. -/
theorem fixingSubgroup_iSup {ι : Sort*} (E : ι → IntermediateField K M) :
    (⨆ i, E i).fixingSubgroup = ⨅ i, (E i).fixingSubgroup := by
  ext σ
  rw [Subgroup.mem_iInf]
  exact ⟨fun h i ↦ fixingSubgroup_antitone (le_iSup E i) h,
    by simp [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]⟩

/-- **The fixing subgroup of an algebraic intermediate field is closed** for the Krull topology:
`E` is the join of the simple extensions it contains, each of them finite over `K`, so
`E.fixingSubgroup` is the intersection of the open subgroups `K⟮x⟯.fixingSubgroup`.

Mathlib's `IntermediateField.fixingSubgroup_isClosed` is the case of a finite `E / K`, where the
subgroup is even open, and `InfiniteGalois.fixingSubgroup_isClosed` is the case of a Galois
`M / K`. Algebraicity of `E / K` alone suffices — nothing is asked of `M / K`, so `E` may be an
algebraic subfield of a transcendental extension, and over an algebraic `M / K` the hypothesis is
supplied by `IntermediateField.isAlgebraic_tower_bot`. The suffix names that hypothesis, as
`MulAction.stabilizer_isOpen_of_isIntegral` does. -/
theorem fixingSubgroup_isClosed_of_isAlgebraic (E : IntermediateField K M)
    [Algebra.IsAlgebraic K E] : IsClosed (E.fixingSubgroup : Set (M ≃ₐ[K] M)) := by
  have hE : E = ⨆ x : E, K⟮(x : M)⟯ := by
    refine le_antisymm (fun x hx ↦ ?_) (iSup_le fun x ↦ adjoin_simple_le_iff.mpr x.2)
    exact le_iSup (fun y : E ↦ K⟮(y : M)⟯) ⟨x, hx⟩ (mem_adjoin_simple_self K x)
  rw [hE, fixingSubgroup_iSup, Subgroup.coe_iInf]
  refine isClosed_iInter fun x ↦ ?_
  have : FiniteDimensional K K⟮(x : M)⟯ :=
    adjoin.finiteDimensional
      (isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic (R := K) x)).isIntegral
  exact fixingSubgroup_isClosed _

/-- **A fixing subgroup sees only the separable closure.** For an intermediate field `E` algebraic
over `K` a `K`-automorphism of `M` fixing `E ⊓ separableClosure K M` pointwise already fixes `E`
pointwise, because every `x ∈ E` has a power `x ^ q ^ n` in that intersection, `q` the exponential
characteristic of `K`.

So an intermediate field outside the separable closure is invisible to the correspondence between
fixing subgroups and fields: it has the same fixing subgroup as its separable part. Like
`IntermediateField.fixingSubgroup_isClosed_of_isAlgebraic` this asks nothing of `M / K`; the power
is produced inside `E`, where `separableClosure K E` is what the elements of `E` are purely
inseparable over. -/
theorem fixingSubgroup_inf_separableClosure (E : IntermediateField K M)
    [Algebra.IsAlgebraic K E] :
    (E ⊓ separableClosure K M).fixingSubgroup = E.fixingSubgroup := by
  have hM : ExpChar M (ringExpChar K) :=
    expChar_of_injective_algebraMap (algebraMap K M).injective _
  have hS : ExpChar (separableClosure K E) (ringExpChar K) :=
    expChar_of_injective_algebraMap (algebraMap K (separableClosure K E)).injective _
  refine le_antisymm (fun σ hσ ↦ ?_) (fixingSubgroup_antitone inf_le_left)
  rw [mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  obtain ⟨n, y, hy⟩ :=
    IsPurelyInseparable.pow_mem (separableClosure K E) (ringExpChar K) (⟨x, hx⟩ : E)
  have hyM : ((y : E) : M) = x ^ ringExpChar K ^ n := by
    simpa using congrArg (algebraMap E M) hy
  have hyS : x ^ ringExpChar K ^ n ∈ separableClosure K M := by
    rw [← hyM]
    exact (map_mem_separableClosure_iff (IsScalarTower.toAlgHom K E M)).mpr y.2
  have hpow : σ x ^ ringExpChar K ^ n = x ^ ringExpChar K ^ n := by
    rw [← map_pow]
    exact hσ _ (mem_inf.mpr ⟨_root_.pow_mem hx _, hyS⟩)
  exact iterateFrobenius_inj M (ringExpChar K) n hpow

/-- **A finite group of automorphisms is the whole fixing subgroup of its fixed field.** Every
`K`-automorphism of `M` that fixes `M ^ H` pointwise already lies in `H`.

Mathlib's `IntermediateField.fixingSubgroup_fixedField` is the same conclusion under
`[FiniteDimensional K M]`, which is the stronger hypothesis: a finite-dimensional `M / K` has a
finite automorphism group, so every subgroup of it is finite. Finiteness of `H` is what an
infinite extension `M / K` can still supply. -/
theorem fixingSubgroup_fixedField_of_finite (H : Subgroup (M ≃ₐ[K] M)) [Finite H] :
    fixingSubgroup (fixedField H) = H := by
  refine le_antisymm (fun σ hσ ↦ ?_) ((le_iff_le _ _).mp le_rfl)
  rw [mem_fixingSubgroup_iff] at hσ
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective H M
    (AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x ↦ hσ x x.2)
  have hgσ : (g : M ≃ₐ[K] M) = σ := AlgEquiv.ext fun z ↦ congrArg (fun τ ↦ τ z) hg
  exact hgσ ▸ g.2

/-- **An intermediate field of finite degree has a finite fixing subgroup**, being a copy of the
automorphism group of a finite extension. -/
instance finite_fixingSubgroup (E : IntermediateField K M) [FiniteDimensional E M] :
    Finite (fixingSubgroup E) :=
  .of_equiv _ (fixingSubgroupEquiv E).symm.toEquiv

/-- **A group of automorphisms whose fixed field has finite degree is finite.** Thus a subgroup of
`K`-automorphisms cannot be infinite when its fixed field has finite degree in `M`. -/
theorem finite_of_finiteDimensional_fixedField (H : Subgroup (M ≃ₐ[K] M))
    [FiniteDimensional (fixedField H) M] : Finite H :=
  letI := finite_fixingSubgroup (fixedField H)
  have hH : H ≤ fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  .of_injective (Set.inclusion hH) (Set.inclusion_injective hH)

/-- **The fixing subgroup of an intermediate field of finite degree is no larger than that
degree**, the bound on the automorphisms of a finite extension. -/
theorem card_fixingSubgroup_le (E : IntermediateField K M) [FiniteDimensional E M] :
    Nat.card (fixingSubgroup E) ≤ Module.finrank E M := by
  rw [Nat.card_congr (fixingSubgroupEquiv E).toEquiv, Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

-- The subgroup extensionality argument below, reducing membership of `K⟮x⟯.fixingSubgroup` to
-- `IntermediateField.forall_mem_adjoin_smul_eq_self_iff` at the singleton `{x}`, is adapted from
-- the proof of `stabilizer_isOpen_of_isIntegral` in `Mathlib/FieldTheory/KrullTopology.lean`,
-- which uses it there to identify a point stabilizer with the fixing subgroup of a finite
-- intermediate field. Here it is recorded as a statement in its own right, with no integrality
-- hypothesis.
/-- **The fixing subgroup of a simple extension is the stabilizer of its generator.** A
`K`-automorphism of `M` is determined on `K⟮x⟯` by its value at `x`, so fixing `K⟮x⟯` pointwise is
fixing `x`; no hypothesis on `M / K` is needed, and `x` need not be algebraic.

This is what turns a statement about the action of `Gal(M/K)` on a set of elements of `M` into a
statement about the Galois correspondence. -/
@[simp]
theorem fixingSubgroup_adjoin_simple (x : M) :
    K⟮x⟯.fixingSubgroup = MulAction.stabilizer (M ≃ₐ[K] M) x := by
  ext σ
  rw [mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff]
  simpa using forall_mem_adjoin_smul_eq_self_iff K (S := {x}) σ

/-- An element lies in the fixed field of its own stabilizer. -/
theorem mem_fixedField_stabilizer (x : M) :
    x ∈ fixedField (MulAction.stabilizer (M ≃ₐ[K] M) x) :=
  (mem_fixedField_iff _ x).mpr fun _ hσ => hσ

/-- For a Galois extension, the fixed field of the stabilizer of `x` is `K⟮x⟯`. -/
@[simp]
theorem fixedField_stabilizer_eq_adjoin_simple [IsGalois K M] (x : M) :
    fixedField (MulAction.stabilizer (M ≃ₐ[K] M) x) = K⟮x⟯ := by
  rw [← fixingSubgroup_adjoin_simple, InfiniteGalois.fixedField_fixingSubgroup]

/-- **The common stabilizer of a family fixes exactly the field generated by that family.** For a
Galois extension, intersecting the point stabilizers of `x i` cuts out `K(Set.range x)`. This is
the family form of `fixedField_stabilizer_eq_adjoin_simple`. -/
theorem fixedField_iInf_stabilizer_eq_adjoin_range [IsGalois K M]
    {I : Sort*} (x : I → M) :
    fixedField (⨅ i, MulAction.stabilizer (M ≃ₐ[K] M) (x i)) =
      adjoin K (Set.range x) := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (adjoin K (Set.range x)),
    Set.range_eq_iUnion, adjoin_iUnion, fixingSubgroup_iSup]
  simp_rw [fixingSubgroup_adjoin_simple]

/-- For a Galois extension, `x` generates the fixed field of its stabilizer as a `K`-algebra. -/
@[simp]
theorem adjoin_eq_top_of_fixedField_stabilizer [IsGalois K M] (x : M) :
    Algebra.adjoin K {(⟨x, mem_fixedField_stabilizer x⟩ :
      fixedField (MulAction.stabilizer (M ≃ₐ[K] M) x))} = ⊤ := by
  set E := fixedField (MulAction.stabilizer (M ≃ₐ[K] M) x) with hE
  set x' : E := ⟨x, mem_fixedField_stabilizer x⟩
  have hx' : IsAlgebraic K x' :=
    (isAlgebraic_algebraMap_iff (algebraMap E M).injective).mp (Algebra.IsAlgebraic.isAlgebraic x)
  have htop : K⟮x'⟯ = ⊤ := by
    apply IntermediateField.map_injective E.val
    rw [adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val]
    exact (fixedField_stabilizer_eq_adjoin_simple x).symm
  have h := adjoin_simple_toSubalgebra_of_isAlgebraic hx'
  rw [htop, IntermediateField.top_toSubalgebra] at h
  exact h.symm

end IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **The Galois correspondence is conjugation-equivariant.** The fixed field of the conjugate
subgroup `σ H σ⁻¹` is the image under `σ` of the fixed field of `H`.

Stated in the `Subgroup` namespace, so that `H` — the first explicit argument, and the one
`fixedField` is applied to — carries the dot notation. -/
@[simp]
theorem fixedField_map_conj (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    fixedField (H.map (MulAut.conj σ)) = (fixedField H).map σ.toAlgHom := by
  ext x
  simp only [mem_fixedField_iff, IntermediateField.mem_map]
  constructor
  · intro h
    refine ⟨σ.symm x, fun g hg ↦ ?_, by simp⟩
    have hx := h (MulAut.conj σ g) (Subgroup.mem_map_of_mem _ hg)
    simpa [MulAut.conj_apply] using congrArg σ.symm hx
  · rintro ⟨y, hy, rfl⟩ g ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply] using congrArg σ (hy h hh)

end Subgroup

namespace FixedPoints

/-- **The fixed subfield of a finite cyclic group action has cyclic Galois group.** For a finite
cyclic group `G` acting on a field `F` by ring automorphisms, `F` is cyclic over its subfield of
`G`-fixed points.

No faithfulness is asked of the action: `FixedPoints.toAlgAut_surjective` needs only finiteness,
and cyclicity passes along any surjection. A non-faithful action simply presents the Galois group
as a proper quotient of `G`, which is cyclic all the same. -/
theorem isCyclic_algEquiv (G F : Type*) [Group G] [Field F] [MulSemiringAction G F] [Finite G]
    [IsCyclic G] : IsCyclic (F ≃ₐ[FixedPoints.subfield G F] F) :=
  isCyclic_of_surjective _ (FixedPoints.toAlgAut_surjective G F)

end FixedPoints

namespace AlgEquiv

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

-- Source. The fixed field of `⟨σ⟩` and its named generator are the constructions pinned at
-- `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 283-291, as `cyclicFixedField` and
-- `fixedFieldGenerator`. Neither name is kept: the field is spelled
-- `IntermediateField.fixedField (Subgroup.zpowers σ)` throughout rather than abbreviated, and the
-- automorphism is `toFixedFieldAlgEquiv`, because it is defined without finiteness and only
-- generates once `⟨σ⟩` is finite.

/-- **The automorphism of `M` over `M ^ ⟨σ⟩` given by `σ`.** Acting through `⟨σ⟩` fixes
`M ^ ⟨σ⟩` pointwise, so `σ` is an automorphism over that field; this is that automorphism, and
nothing more. It is `σ` rebundled over a smaller base, so the name says only that.

Named rather than inlined so that consumers have a term to talk about: a fibre count needs the
relative Frobenius exhibited as a specific power of a specific generator, and `IsCyclic` supplies
only an anonymous one. Use `toFixedFieldAlgEquiv_apply` to compute with it. That it *generates* is
`zpowers_toFixedFieldAlgEquiv_eq_top`, a separate statement, and it is the only one that needs
`⟨σ⟩` to be finite. -/
def toFixedFieldAlgEquiv (σ : M ≃ₐ[K] M) :
    M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] M :=
  MulSemiringAction.toAlgAut (Subgroup.zpowers σ)
    (FixedPoints.subfield (Subgroup.zpowers σ) M) M ⟨σ, Subgroup.mem_zpowers σ⟩

/-- **The rebundled automorphism acts as `σ`.** This is what makes `toFixedFieldAlgEquiv σ`
usable: it is a different bundling of the same underlying map, over the fixed field rather than
over `K`. It says nothing about generation, which needs `⟨σ⟩` finite and is
`zpowers_toFixedFieldAlgEquiv_eq_top`. -/
@[simp]
theorem toFixedFieldAlgEquiv_apply (σ : M ≃ₐ[K] M) (x : M) :
    toFixedFieldAlgEquiv σ x = σ x :=
  (rfl)

/-- **Restricting scalars undoes the rebundling.** Read back over `K`, `σ.toFixedFieldAlgEquiv`
is `σ` itself — the elimination rule matching `toFixedFieldAlgEquiv_apply`, in bundled form, which
is what a tower argument needs when it must produce an equation between automorphisms rather than
between their values. -/
@[simp]
theorem restrictScalars_toFixedFieldAlgEquiv (σ : M ≃ₐ[K] M) :
    AlgEquiv.restrictScalars K σ.toFixedFieldAlgEquiv = σ :=
  AlgEquiv.ext fun x ↦ toFixedFieldAlgEquiv_apply σ x

/-- **And, for finite `⟨σ⟩`, it generates.** The automorphisms of `M` fixing `M ^ ⟨σ⟩` are exactly
the powers of `σ.toFixedFieldAlgEquiv`.

Together with `FixedPoints.isCyclic_algEquiv`, applied to the action of `⟨σ⟩` on `M`, this is the
cyclic picture of `M / M ^ ⟨σ⟩` with a named generator; neither statement asks `M / K` to be
finite or Galois. -/
@[simp]
theorem zpowers_toFixedFieldAlgEquiv_eq_top (σ : M ≃ₐ[K] M) [Finite (Subgroup.zpowers σ)] :
    Subgroup.zpowers (toFixedFieldAlgEquiv σ) = ⊤ := by
  -- Generation is a statement about the `MulEquiv`, so it is proved for `toAlgAutMulEquiv` and
  -- then transported to `toFixedFieldAlgEquiv` by `exact`, which works up to definitional equality:
  -- `toAlgAutMulEquiv` is `MulEquiv.ofBijective` of the very `toAlgAut` the definition uses. It
  -- cannot be done by rewriting with `toFixedFieldAlgEquiv` instead, because that term lives over
  -- `FixedPoints.subfield`, defeq to `IntermediateField.fixedField` but not syntactically equal,
  -- so `rw` produces a type-incorrect goal.
  --
  -- Within the `have`, `MonoidHom.map_zpowers` is about a `MonoidHom`, so the `MulEquiv`
  -- application is restated through `MulEquiv.coe_toMonoidHom` rather than by unfolding the
  -- coercion. The image of `⊤` is then `Subgroup.map_equiv_top`, which `simp` reaches through
  -- `MulEquiv.toMonoidHom_eq_coe`.
  have h : Subgroup.zpowers (FixedPoints.toAlgAutMulEquiv (Subgroup.zpowers σ) M
      ⟨σ, Subgroup.mem_zpowers σ⟩) = ⊤ := by
    rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_zpowers, Subgroup.zpowers_mk_self_eq_top]
    simp
  exact h

/-- **The automorphism group of `M` over `M ^ ⟨σ⟩` has order `orderOf σ`.** The automorphisms of
`M` fixing the field cut out by `⟨σ⟩` number exactly the order of `σ`.

Only the generated subgroup `⟨σ⟩` need be finite: `M / K` is asked to be neither finite nor
Galois, so this applies to an automorphism of finite order of an arbitrary extension. -/
-- Not a `simp` lemma: `simpNF` rejects it. Normalising the left-hand side sends `simp` after
-- `Fintype Gal(M/M ^ ⟨σ⟩)`, and with only `Finite (Subgroup.zpowers σ)` in scope that instance
-- search exhausts its heartbeat budget instead of failing, so the lemma could never fire.
theorem card_algEquiv_fixedField_zpowers (σ : M ≃ₐ[K] M) [Finite (Subgroup.zpowers σ)] :
    Nat.card (M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] M) = orderOf σ := by
  have horder : orderOf (toFixedFieldAlgEquiv σ) = orderOf σ := by
    rw [← orderOf_injective (AlgEquiv.restrictScalarsHom K)
      (AlgEquiv.restrictScalarsHom_injective K) (toFixedFieldAlgEquiv σ),
      AlgEquiv.restrictScalarsHom_apply, restrictScalars_toFixedFieldAlgEquiv]
  rw [← Subgroup.card_top (G := M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] M),
    ← zpowers_toFixedFieldAlgEquiv_eq_top σ, Nat.card_zpowers, horder]

end AlgEquiv
