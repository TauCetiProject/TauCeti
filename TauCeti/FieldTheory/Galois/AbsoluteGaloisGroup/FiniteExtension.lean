/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension
public import TauCeti.FieldTheory.Galois.Quotient
public import TauCeti.FieldTheory.Galois.Restriction

/-!
# The absolute Galois group of a finite separable extension as an open subgroup

Let `L/K` be a finite separable extension and `σ : L →ₐ[K] Kˢ` a `K`-embedding of `L` into a
separable closure `Kˢ` of `K`. The automorphisms of `Kˢ` that fix `σ(L)` pointwise form an open
subgroup

```text
galoisSubgroup K L σ ≤ G_K = AbsoluteGaloisGroup K
```

of index `[L : K]`, and it is the absolute Galois group of `L`: the isomorphism of topological
groups `absoluteGaloisGroupEquivFixingSubgroup K L σ : G_L ≃ₜ* σ.fieldRange.fixingSubgroup` of
`TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension`, read at the open subgroup, is an
isomorphism `G_L ≃ₜ* galoisSubgroup K L σ` for the Krull topologies, which is what continuous
cohomology depends on.

The embedding is genuine data. Without one there is no homomorphism `G_L → G_K` induced by the
extension `L/K`, hence no realization of `G_L` as a subgroup of `G_K`, and two embeddings cut out
conjugate subgroups. Restriction, corestriction and the other subgroup-indexed operations of
Galois cohomology along `L/K` are the operations at `galoisSubgroup K L σ`, read through
`galoisSubgroupEquiv K L σ`, and their independence of `σ` is a statement about those operations
rather than about the subgroup. The index formula is what discharges the finite-index and
index-two hypotheses those operations carry.

Finiteness of `L/K` enters in three places: it makes the fixing subgroup open, so that it can be
packaged as the `OpenSubgroup` `galoisSubgroup K L σ`; it is the hypothesis of the finite-degree
index formula `galoisSubgroup_index`; and, through the packaging, it is carried by
`galoisSubgroupEquiv K L σ` and its application lemmas. The identification of separable closures
and the isomorphism of Galois groups themselves need no finiteness and live in the imported
module. Separability of `L/K` is a consequence of the existence of `σ` and is not assumed.

When `L/K` is normal, every automorphism of `Kˢ` preserves `σ(L)`, so restriction
`σ.restrictNormalHom : G_K →* Gal(L/K)` along `σ` is defined; it is surjective with kernel the
subgroup fixing `σ(L)`, and `quotientFixingSubgroupFieldRangeEquiv K L σ` is the induced
isomorphism `G_K ⧸ Gal(Kˢ/σ(L)) ≃* Gal(L/K)`. This part uses normality but not finiteness. When
`L/K` is both finite and normal, the subgroup fixing `σ(L)` is packaged as the open normal subgroup
`galoisOpenNormalSubgroup K L σ`, the level of `L` among the finite quotients of `G_K`. When
`L/K` is finite Galois, all embeddings have the same image, the normal closure of `L` in `Kˢ`, and
`fixingOpenNormalSubgroup K L` is this subgroup with no embedding chosen.

## Main definitions

* `TauCeti.galoisSubgroup K L σ`: the open subgroup of `G_K` fixing `σ(L)` pointwise, for a
  finite `L/K`.
* `TauCeti.galoisSubgroupEquiv K L σ`: the isomorphism of topological groups
  `G_L ≃ₜ* galoisSubgroup K L σ`.
* `TauCeti.quotientFixingSubgroupFieldRangeEquiv K L σ`: for a normal `L/K`, the isomorphism
  `G_K ⧸ Gal(Kˢ/σ(L)) ≃* Gal(L/K)` induced by restriction `σ.restrictNormalHom`.
* `TauCeti.galoisOpenNormalSubgroup K L σ`: for a finite normal `L/K`, the subgroup fixing
  `σ(L)` as an open normal subgroup of `G_K`.
* `TauCeti.fixingOpenNormalSubgroup K L`: for a finite `L/K`, the open normal subgroup of `G_K`
  fixing the normal closure of `L` in `Kˢ`, with no embedding chosen.
* `TauCeti.absoluteGaloisGroupExtend K L σ`: the injective continuous homomorphism
  `Field.absoluteGaloisGroup L →* Field.absoluteGaloisGroup K` between Mathlib's absolute Galois
  groups, `galoisSubgroupEquiv K L σ` followed by the inclusion of `galoisSubgroup K L σ`.

## Main results

* `TauCeti.galoisSubgroup_index`: the index of `galoisSubgroup K L σ` in `G_K` is `[L : K]`, so
  the subgroup fixing `σ(L)` has finite index
  (`TauCeti.finiteIndex_fixingSubgroup_fieldRange`, `TauCeti.finiteIndex_galoisSubgroup`).
* `TauCeti.galoisSubgroupEquiv_apply_separableClosureRingEquiv`: the isomorphism intertwines the
  actions of `G_L` on `Lˢ` and of `G_K` on `Kˢ` through `separableClosureRingEquiv K L σ`.
* `TauCeti.absoluteGaloisGroupExtend_apply_separableClosureRingEquiv`: the embedding of Mathlib's
  absolute Galois groups intertwines the actions on the identified separable closures.
* `TauCeti.mem_range_absoluteGaloisGroupExtend_iff`,
  `TauCeti.isOpen_range_absoluteGaloisGroupExtend`,
  `TauCeti.index_range_absoluteGaloisGroupExtend`: the image of `G_L` in Mathlib's `G_K` is the
  open subgroup `galoisSubgroup K L σ`, of index `[L : K]`.
* `TauCeti.quotientFixingSubgroupFieldRangeEquiv_mk`: the isomorphism sends the class of `g`
  to `σ.restrictNormalHom g`.
* `TauCeti.exists_galoisOpenNormalSubgroup_eq`: every open normal subgroup of `G_K` is
  `galoisOpenNormalSubgroup K E E.val` for a finite Galois intermediate field `E` of `Kˢ/K`.
* `TauCeti.fixingOpenNormalSubgroup_eq_galoisOpenNormalSubgroup`: for a finite Galois `L/K`,
  `fixingOpenNormalSubgroup K L` is `galoisOpenNormalSubgroup K L σ` for every embedding `σ`.
* `TauCeti.restrictNormalHom_of_compatible`: a compatible pair between normal subextensions of
  `Kˢ` carries restriction to the larger field to restriction to the smaller field.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §5 for
  restriction and corestriction along a finite extension, and Ch. VI §1 for the absolute Galois
  group at the separable closure.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-! ### The open subgroup -/

/-- **The open subgroup of `G_K` cut out by a `K`-embedding of `L` into `Kˢ`**: the automorphisms
of `Kˢ` fixing `σ(L)` pointwise. It is open because `L/K` is finite, and `galoisSubgroupEquiv`
identifies it with the absolute Galois group of `L`. -/
def galoisSubgroup : OpenSubgroup (AbsoluteGaloisGroup K) where
  toSubgroup := σ.fieldRange.fixingSubgroup
  isOpen' :=
    haveI : FiniteDimensional K σ.fieldRange := σ.toLinearMap.finiteDimensional_range
    σ.fieldRange.fixingSubgroup_isOpen

/-- The subgroup underlying `galoisSubgroup K L σ` is the fixing subgroup of the image of `σ`. -/
@[simp]
theorem galoisSubgroup_toSubgroup :
    (galoisSubgroup K L σ).toSubgroup = σ.fieldRange.fixingSubgroup :=
  (rfl)

/-- An automorphism of `Kˢ` lies in `galoisSubgroup K L σ` exactly when it fixes `σ x` for every
`x : L`. -/
@[simp]
theorem mem_galoisSubgroup_iff {g : AbsoluteGaloisGroup K} :
    g ∈ galoisSubgroup K L σ ↔ ∀ x : L, g (σ x) = σ x := by
  rw [← OpenSubgroup.mem_toSubgroup, galoisSubgroup_toSubgroup,
    IntermediateField.mem_fixingSubgroup_iff]
  simp

/-- **The index of `galoisSubgroup K L σ` is the degree `[L : K]`.** -/
theorem galoisSubgroup_index : (galoisSubgroup K L σ).toSubgroup.index = Module.finrank K L := by
  rw [galoisSubgroup_toSubgroup, ← finrank_eq_fixingSubgroup_index]
  exact (AlgEquiv.ofInjectiveField σ).toLinearEquiv.finrank_eq.symm

/-- **The subgroup of `G_K` fixing `σ(L)` has finite index**, namely `[L : K]`. This is what
discharges the finite-index hypothesis of corestriction and of the other operations of Galois
cohomology indexed by a subgroup of `G_K`. -/
instance finiteIndex_fixingSubgroup_fieldRange :
    (σ.fieldRange.fixingSubgroup : Subgroup (AbsoluteGaloisGroup K)).FiniteIndex :=
  ⟨by rw [← galoisSubgroup_toSubgroup, galoisSubgroup_index]; exact Module.finrank_pos.ne'⟩

/-- **`galoisSubgroup K L σ` has finite index**, namely `[L : K]`: the instance
`finiteIndex_fixingSubgroup_fieldRange` read through `galoisSubgroup_toSubgroup`. -/
instance finiteIndex_galoisSubgroup : (galoisSubgroup K L σ).toSubgroup.FiniteIndex :=
  inferInstanceAs (σ.fieldRange.fixingSubgroup : Subgroup (AbsoluteGaloisGroup K)).FiniteIndex

/-- **The subgroup of `G_K` fixing `σ(L)` is open**, `galoisSubgroup K L σ` read as a plain
subgroup. -/
theorem isOpen_fixingSubgroup_fieldRange :
    IsOpen (σ.fieldRange.fixingSubgroup : Set (AbsoluteGaloisGroup K)) :=
  galoisSubgroup_toSubgroup K L σ ▸ (galoisSubgroup K L σ).isOpen

/-- `galoisSubgroup K L σ` is all of `G_K` exactly when `L/K` is trivial, that is `[L : K] = 1`. -/
theorem galoisSubgroup_eq_top_iff : galoisSubgroup K L σ = ⊤ ↔ Module.finrank K L = 1 := by
  rw [← galoisSubgroup_index, Subgroup.index_eq_one, ← OpenSubgroup.toSubgroup_top,
    OpenSubgroup.toSubgroup_injective.eq_iff]

/-! ### The isomorphism with the absolute Galois group of `L` -/

/-- **The absolute Galois group of `L` is the open subgroup of `G_K` cut out by `σ`**, as
topological groups: conjugation by the identification `separableClosureRingEquiv K L σ` of separable
closures is an isomorphism `G_L ≃ₜ* galoisSubgroup K L σ` for the Krull topologies. It is
`absoluteGaloisGroupEquivFixingSubgroup K L σ` read at the open subgroup. -/
def galoisSubgroupEquiv : AbsoluteGaloisGroup L ≃ₜ* ↥(galoisSubgroup K L σ).toSubgroup :=
  absoluteGaloisGroupEquivFixingSubgroup K L σ

/-- `galoisSubgroupEquiv K L σ` conjugates by the identification of separable closures. -/
@[simp]
theorem galoisSubgroupEquiv_apply (g : AbsoluteGaloisGroup L) (y : SeparableClosure K) :
    (galoisSubgroupEquiv K L σ g : AbsoluteGaloisGroup K) y =
      separableClosureRingEquiv K L σ (g ((separableClosureRingEquiv K L σ).symm y)) :=
  absoluteGaloisGroupEquivFixingSubgroup_apply K L σ g y

/-- **The isomorphism intertwines the Galois actions**: the image of `g : G_L` acts on
`e x ∈ Kˢ` as `g` acts on `x ∈ Lˢ`, where `e = separableClosureRingEquiv K L σ`. -/
theorem galoisSubgroupEquiv_apply_separableClosureRingEquiv (g : AbsoluteGaloisGroup L)
    (x : SeparableClosure L) :
    (galoisSubgroupEquiv K L σ g : AbsoluteGaloisGroup K) (separableClosureRingEquiv K L σ x) =
      separableClosureRingEquiv K L σ (g x) := by
  rw [galoisSubgroupEquiv_apply, RingEquiv.symm_apply_apply]

/-- The inverse of `galoisSubgroupEquiv K L σ` conjugates back by the identification of separable
closures. -/
@[simp]
theorem galoisSubgroupEquiv_symm_apply (h : ↥(galoisSubgroup K L σ).toSubgroup)
    (x : SeparableClosure L) :
    (galoisSubgroupEquiv K L σ).symm h x =
      (separableClosureRingEquiv K L σ).symm
        ((h : AbsoluteGaloisGroup K) (separableClosureRingEquiv K L σ x)) :=
  absoluteGaloisGroupEquivFixingSubgroup_symm_apply K L σ h x

/-! ### The embedding of Mathlib's absolute Galois groups -/

/-- **The absolute Galois group of a finite extension inside that of `K`**, along a `K`-embedding
`σ : L →ₐ[K] Kˢ`: identify `G_L` with the open subgroup of `G_K` fixing `σ(L)`, and include that
subgroup in `G_K`. The two absolute Galois groups use Mathlib's algebraic closures, while the
subgroup identification uses Tau Ceti's separable closures; `absoluteGaloisGroupRestrictEquiv`
transports between the two models. -/
def absoluteGaloisGroupExtend : Field.absoluteGaloisGroup L →* Field.absoluteGaloisGroup K :=
  (absoluteGaloisGroupRestrictEquiv K).symm.toMulEquiv.toMonoidHom.comp
    ((galoisSubgroup K L σ).toSubgroup.subtype.comp
      ((galoisSubgroupEquiv K L σ).toMulEquiv.toMonoidHom.comp
        (absoluteGaloisGroupRestrictEquiv L).toMulEquiv.toMonoidHom))

/-- Reading `absoluteGaloisGroupExtend` on separable closures gives the inclusion of the open
subgroup identified with `G_L`. -/
@[simp]
theorem absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend
    (τ : Field.absoluteGaloisGroup L) :
    absoluteGaloisGroupRestrictEquiv K (absoluteGaloisGroupExtend K L σ τ) =
      (galoisSubgroupEquiv K L σ (absoluteGaloisGroupRestrictEquiv L τ) :
        AbsoluteGaloisGroup K) :=
  (absoluteGaloisGroupRestrictEquiv K).apply_symm_apply _

/-- The embedding of absolute Galois groups intertwines the actions on the identified separable
closures. -/
theorem absoluteGaloisGroupExtend_apply_separableClosureRingEquiv
    (τ : Field.absoluteGaloisGroup L) (x : SeparableClosure L) :
    absoluteGaloisGroupRestrictEquiv K (absoluteGaloisGroupExtend K L σ τ)
        (separableClosureRingEquiv K L σ x) =
      separableClosureRingEquiv K L σ (absoluteGaloisGroupRestrictEquiv L τ x) := by
  rw [absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend]
  exact galoisSubgroupEquiv_apply_separableClosureRingEquiv K L σ _ x

/-- The embedding `G_L → G_K` induced by an embedding of a finite extension is continuous. -/
theorem continuous_absoluteGaloisGroupExtend : Continuous (absoluteGaloisGroupExtend K L σ) :=
  (absoluteGaloisGroupRestrictEquiv K).symm.continuous_toFun.comp <|
    continuous_subtype_val.comp <|
      (galoisSubgroupEquiv K L σ).continuous_toFun.comp
        (absoluteGaloisGroupRestrictEquiv L).continuous_toFun

/-- The map `G_L → G_K` induced by an embedding of a finite extension is injective. -/
theorem injective_absoluteGaloisGroupExtend :
    Function.Injective (absoluteGaloisGroupExtend K L σ) :=
  (absoluteGaloisGroupRestrictEquiv K).symm.injective.comp <|
    Subtype.val_injective.comp <|
      (galoisSubgroupEquiv K L σ).injective.comp
        (absoluteGaloisGroupRestrictEquiv L).injective

/-- **The image of `G_L` in `G_K`** is the open subgroup `galoisSubgroup K L σ` fixing `σ(L)`,
read in Mathlib's absolute Galois group through `absoluteGaloisGroupRestrictEquiv K`. -/
theorem mem_range_absoluteGaloisGroupExtend_iff {g : Field.absoluteGaloisGroup K} :
    g ∈ (absoluteGaloisGroupExtend K L σ).range ↔
      absoluteGaloisGroupRestrictEquiv K g ∈ galoisSubgroup K L σ := by
  refine ⟨?_, fun hg ↦ ?_⟩
  · rintro ⟨τ, rfl⟩
    rw [absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend]
    exact (galoisSubgroupEquiv K L σ _).2
  · refine ⟨(absoluteGaloisGroupRestrictEquiv L).symm
      ((galoisSubgroupEquiv K L σ).symm ⟨absoluteGaloisGroupRestrictEquiv K g, hg⟩),
      (absoluteGaloisGroupRestrictEquiv K).injective ?_⟩
    rw [absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend,
      ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The image of `G_L` in `G_K` is open. -/
theorem isOpen_range_absoluteGaloisGroupExtend :
    IsOpen ((absoluteGaloisGroupExtend K L σ).range : Set (Field.absoluteGaloisGroup K)) := by
  have h : ((absoluteGaloisGroupExtend K L σ).range : Set (Field.absoluteGaloisGroup K)) =
      absoluteGaloisGroupRestrictEquiv K ⁻¹' (galoisSubgroup K L σ : Set (AbsoluteGaloisGroup K)) :=
    Set.ext fun _ ↦ mem_range_absoluteGaloisGroupExtend_iff K L σ
  rw [h]
  exact (galoisSubgroup K L σ).isOpen.preimage (absoluteGaloisGroupRestrictEquiv K).continuous

/-- **The image of `G_L` in `G_K` has index `[L : K]`.** -/
theorem index_range_absoluteGaloisGroupExtend :
    (absoluteGaloisGroupExtend K L σ).range.index = Module.finrank K L := by
  have h : (absoluteGaloisGroupExtend K L σ).range =
      (galoisSubgroup K L σ).toSubgroup.comap
        (absoluteGaloisGroupRestrictEquiv K).toMulEquiv.toMonoidHom :=
    Subgroup.ext fun _ ↦ mem_range_absoluteGaloisGroupExtend_iff K L σ
  rw [h, Subgroup.index_comap_of_surjective _ (absoluteGaloisGroupRestrictEquiv K).surjective,
    galoisSubgroup_index]

/-! ### Normal extensions: the quotient by the open subgroup -/

section Normal

omit [FiniteDimensional K L]

variable [Normal K L]

/-- **The Galois group of a normal extension `L` embedded by `σ` is the quotient of `G_K` by the
subgroup fixing `σ(L)`**: `TauCeti.quotientFixingSubgroupEquiv` for the intermediate field `σ(L)`,
read on `L` through `σ`. It sends the class of `g` to its restriction `σ.restrictNormalHom g`
along `σ` (`quotientFixingSubgroupFieldRangeEquiv_mk`). -/
def quotientFixingSubgroupFieldRangeEquiv :
    AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup ≃* Gal(L/K) :=
  (quotientFixingSubgroupEquiv K (SeparableClosure K) σ.fieldRange).toMulEquiv.trans
    (AlgEquiv.autCongr σ.equivFieldRange).symm

/-- The isomorphism `quotientFixingSubgroupFieldRangeEquiv` sends the class of `g` to its
restriction `σ.restrictNormalHom g`. -/
@[simp]
theorem quotientFixingSubgroupFieldRangeEquiv_mk (g : AbsoluteGaloisGroup K) :
    quotientFixingSubgroupFieldRangeEquiv K L σ g = σ.restrictNormalHom g := by
  rw [quotientFixingSubgroupFieldRangeEquiv, MulEquiv.trans_apply]
  refine (congrArg (AlgEquiv.autCongr σ.equivFieldRange).symm
    (quotientFixingSubgroupEquiv_mk g)).trans (σ.restrictNormalHom_eq_iff.2 fun x ↦ ?_).symm
  simp only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_symm]
  symm
  rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply,
    AlgEquiv.restrictNormalHom_apply, ← AlgHom.equivFieldRange_apply_coe]

end Normal

/-! ### Restriction along compatible normal subextensions -/

section CompatibleRestriction

variable {K : Type*} [Field K]
  {E M : IntermediateField K (SeparableClosure K)} [Normal K E] [Normal K M]
  (pi : (M ≃ₐ[K] M) →* (E ≃ₐ[K] E)) (iota : E →ₐ[K] M)
  (hpiiota : ∀ g x, iota (pi g x) = g (iota x))
  (hiota : ∀ x, M.val (iota x) = E.val x)
include hpiiota hiota

/-- Along a compatible pair `(pi, iota)` between normal subextensions of `Kˢ`, with `iota`
compatible with their inclusions into `Kˢ`, `pi` carries restriction to `M` to restriction to
`E`. -/
theorem restrictNormalHom_of_compatible (g : AbsoluteGaloisGroup K) :
    pi (AlgEquiv.restrictNormalHom M g) = AlgEquiv.restrictNormalHom E g :=
  AlgEquiv.ext fun x ↦ E.val.injective <| (hiota _).symm.trans <|
    (congrArg M.val (hpiiota _ x)).trans <| (AlgEquiv.restrictNormal_commutes g M (iota x)).trans <|
      (congrArg g (hiota x)).trans (AlgEquiv.restrictNormal_commutes g E x).symm

end CompatibleRestriction

/-! ### Finite normal extensions: the open normal subgroup -/

section OpenNormal

variable [Normal K L]

/-- **The level of a finite normal extension**: the subgroup `Gal(Kˢ/σ(L))` of automorphisms of
`Kˢ` fixing `σ(L)`, an open normal subgroup of `Gal(Kˢ/K)` because `L/K` is finite and normal.
Its underlying subgroup is the fixing subgroup of `σ(L)` by definition, so the quotient by it is
the domain of `quotientFixingSubgroupFieldRangeEquiv K L σ`. -/
@[expose] def galoisOpenNormalSubgroup : OpenNormalSubgroup (AbsoluteGaloisGroup K) where
  toSubgroup := σ.fieldRange.fixingSubgroup
  isOpen' := isOpen_fixingSubgroup_fieldRange K L σ
  isNormal' := inferInstance

/-- The subgroup underlying `galoisOpenNormalSubgroup K L σ` is the fixing subgroup of `σ(L)`. -/
@[simp]
theorem galoisOpenNormalSubgroup_toSubgroup :
    (galoisOpenNormalSubgroup K L σ).toSubgroup = σ.fieldRange.fixingSubgroup :=
  (rfl)

end OpenNormal

variable {K} in
/-- **Every open normal subgroup of `G_K` is the level of a finite Galois subextension**: it is
`galoisOpenNormalSubgroup K E E.val` for its fixed field `E`, an intermediate field of `Kˢ/K`
finite and Galois over `K`. -/
theorem exists_galoisOpenNormalSubgroup_eq (U : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    ∃ (E : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K E)
      (_ : IsGalois K E), galoisOpenNormalSubgroup K E E.val = U := by
  obtain ⟨E, hE⟩ : ∃ E : IntermediateField K (SeparableClosure K),
      E.fixingSubgroup = U.toSubgroup :=
    ⟨_, InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩⟩
  have : FiniteDimensional K E := by
    rw [← InfiniteGalois.isOpen_iff_finite, hE]
    exact U.isOpen
  have : IsGalois K E := by
    rw [← InfiniteGalois.normal_iff_isGalois, hE]
    infer_instance
  refine ⟨E, inferInstance, inferInstance, OpenNormalSubgroup.toSubgroup_injective ?_⟩
  dsimp only
  rw [galoisOpenNormalSubgroup_toSubgroup, IntermediateField.fieldRange_val, hE]

/-! ### The fixing subgroup of the normal closure -/

section FixingNormalClosure

/-- **The open normal subgroup cut out by a finite extension** `L/K`: the subgroup of
`G_K = Gal(Kˢ/K)` fixing the normal closure of `L` in `Kˢ`, that is, fixing the image of every
`K`-embedding of `L` into `Kˢ`. When `L/K` is Galois all these images coincide, so this is
`TauCeti.galoisOpenNormalSubgroup K L ι` for every embedding `ι`
(`fixingOpenNormalSubgroup_eq_galoisOpenNormalSubgroup`), with no embedding chosen. -/
def fixingOpenNormalSubgroup : OpenNormalSubgroup (AbsoluteGaloisGroup K) where
  toSubgroup := (normalClosure K L (SeparableClosure K)).fixingSubgroup
  isOpen' := (normalClosure K L (SeparableClosure K)).fixingSubgroup_isOpen
  isNormal' := (InfiniteGalois.normal_iff_isGalois _).2 inferInstance

variable {K L} [IsGalois K L]

/-- The subgroup underlying `fixingOpenNormalSubgroup K L` is the fixing subgroup of the image of
any `K`-embedding `ι` of the Galois extension `L` into `Kˢ`. -/
theorem fixingOpenNormalSubgroup_toSubgroup (ι : L →ₐ[K] SeparableClosure K) :
    (fixingOpenNormalSubgroup K L).toSubgroup = ι.fieldRange.fixingSubgroup := by
  rw [← IntermediateField.normalClosure_eq_fieldRange ι]
  rfl

/-- **The fixing subgroup of a Galois extension does not depend on the embedding**: it is the
subgroup `TauCeti.galoisOpenNormalSubgroup K L ι` fixing the image of any `K`-embedding `ι`. -/
theorem fixingOpenNormalSubgroup_eq_galoisOpenNormalSubgroup (ι : L →ₐ[K] SeparableClosure K) :
    fixingOpenNormalSubgroup K L = galoisOpenNormalSubgroup K L ι :=
  OpenNormalSubgroup.toSubgroup_injective <|
    (fixingOpenNormalSubgroup_toSubgroup ι).trans (galoisOpenNormalSubgroup_toSubgroup K L ι).symm

/-- An element of `G_K` lies in `fixingOpenNormalSubgroup K L` exactly when it fixes the image
of a (any) `K`-embedding `ι` of the Galois extension `L` into `Kˢ`. -/
theorem mem_fixingOpenNormalSubgroup_iff (ι : L →ₐ[K] SeparableClosure K)
    {σ : AbsoluteGaloisGroup K} :
    σ ∈ fixingOpenNormalSubgroup K L ↔ ∀ x : L, σ (ι x) = ι x := by
  -- Membership in an open normal subgroup is by definition membership in its underlying subgroup;
  -- Mathlib states no lemma for this.
  change σ ∈ (fixingOpenNormalSubgroup K L).toSubgroup ↔ _
  rw [fixingOpenNormalSubgroup_toSubgroup ι, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x => h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

end FixingNormalClosure

end TauCeti
