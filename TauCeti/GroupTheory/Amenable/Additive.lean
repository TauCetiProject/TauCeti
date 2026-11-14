/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.DirectedUnion
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.GroupTheory.Amenable.Extension
public import TauCeti.GroupTheory.Amenable.Prod
import Mathlib.Algebra.Group.TypeTags.Finite
import TauCeti.Topology.Algebra.ContinuousMonoidHom.TypeTags
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Amenable additive topological groups

`TauCeti.Amenable G` is defined by the existence of a left-invariant mean on the real algebra
`TauCeti.UCB G` of left uniformly continuous bounded functions, so `@[to_additive]` cannot translate
`UCB` or `Mean` directly without duplicating the function-algebra hierarchy. Instead, we define
`TauCeti.AddAmenable A` for an additive topological group `A` by amenability of the topological
group `Multiplicative A`, register `insert_to_additive_translation TauCeti.Amenable
TauCeti.AddAmenable`, and provide native additive formulations of the invariant-mean, permanence,
directed-union, and Følner theorems directly on `A`.

To avoid typeclass synthesis cycles between `A`, `Multiplicative A`, and `Additive G`, only the
forward transport instances `AddAmenable A → Amenable (Multiplicative A)` and
`Amenable G → AddAmenable (Additive G)` are registered as instances; the two-way equivalences
`TauCeti.amenable_multiplicative_iff` and `TauCeti.addAmenable_additive_iff` are plain `@[simp]`
theorems.

## Main definitions

* `TauCeti.AddAmenable A`: `A` is an amenable additive topological group, defined via
  `TauCeti.Amenable (Multiplicative A)` and paired with `TauCeti.Amenable` via `@[to_additive]`.

## Main results

* `TauCeti.amenable_multiplicative_iff` and `TauCeti.addAmenable_additive_iff`: compatibility of
  `Amenable` and `AddAmenable` with `Multiplicative` and `Additive`.
* `TauCeti.addAmenable_iff_exists_boundedContinuousFunction_mean`: a discrete additive group `A` is
  amenable if and only if `A →ᵇ ℝ` admits a normalized positive translation-invariant linear
  functional.
* `TauCeti.AddAmenable.of_denseRange`, `TauCeti.AddAmenable.of_surjective`,
  `TauCeti.AddAmenable.of_le`, `TauCeti.AddAmenable.of_discrete`, and
  `ContinuousAddEquiv.addAmenable_iff`: functoriality and topology change.
* `TauCeti.AddAmenable.of_finite`, `TauCeti.AddAmenable.prod`, `TauCeti.addAmenable_prod_iff`,
  `TauCeti.AddAmenable.pi`, and `TauCeti.addAmenable_pi_iff`: finite groups and finite products.
* `TauCeti.AddAmenable.of_injective`, `TauCeti.AddAmenable.addSubgroup`,
  `TauCeti.AddAmenable.of_ker_le_range`, and `TauCeti.addAmenable_iff_addSubgroup_quotient`:
  subgroups and extensions of discrete additive groups.
* `TauCeti.AddAmenable.of_forall_finset_subset_range`, `TauCeti.addAmenable_iSup_of_directed`,
  `TauCeti.AddAmenable.of_directed_of_iSup_eq_top`, and `TauCeti.AddAmenable.of_forall_fg`:
  directed unions and reduction to finitely generated additive subgroups.
* `TauCeti.addAmenable_iff_hasAddFoelnerSets`, `TauCeti.addAmenable_iff_maxAddFoelner_neBot`,
  `TauCeti.addAmenable_iff_exists_finset`, and `TauCeti.addAmenable_iff_exists_seq`: Følner
  characterizations of discrete additive amenability.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.
* A. Garrido, *An introduction to amenable groups*, §§1–3.
-/

public section

noncomputable section

open Filter Finset Topology
open scoped BoundedContinuousFunction Pointwise symmDiff

namespace TauCeti

section Basic

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

variable (A) in
/-- An additive topological group `A` is amenable when the topological group `Multiplicative A` is
amenable. -/
class AddAmenable : Prop where
  /-- `Multiplicative A` is amenable when `A` is additively amenable. -/
  amenable_multiplicative : Amenable (Multiplicative A)

insert_to_additive_translation TauCeti.Amenable TauCeti.AddAmenable

instance [AddAmenable A] : Amenable (Multiplicative A) :=
  AddAmenable.amenable_multiplicative

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Amenable G] :
    AddAmenable (Additive G) :=
  ⟨(ContinuousMulEquiv.multiplicativeAdditive G).amenable_iff.2 ‹_›⟩

/-- `Multiplicative A` is amenable if and only if `A` is additively amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative A) ↔ AddAmenable A :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

variable (A) in
/-- An additive topological group `A` is amenable exactly when `Multiplicative A` is amenable. -/
theorem addAmenable_iff_amenable_multiplicative : AddAmenable A ↔ Amenable (Multiplicative A) :=
  amenable_multiplicative_iff.symm

/-- `Additive G` is additively amenable if and only if `G` is amenable. -/
@[simp]
theorem addAmenable_additive_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : AddAmenable (Additive G) ↔ Amenable G :=
  ⟨fun _ => (ContinuousMulEquiv.multiplicativeAdditive G).amenable_iff.1 inferInstance,
    fun _ => inferInstance⟩

/-- The target of a continuous additive homomorphism with dense range from an amenable additive
topological group is amenable; in particular, so is the image under a surjective continuous
additive homomorphism. -/
theorem AddAmenable.of_denseRange [AddAmenable A] (φ : A →ₜ+ B) (hφ : DenseRange φ) :
    AddAmenable B :=
  ⟨.of_denseRange φ.toMultiplicative (φ.denseRange_toMultiplicative_iff.2 hφ)⟩

attribute [to_additive existing] Amenable.of_denseRange

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Additive amenability passes from a finer additive-group topology to a coarser one. -/
theorem AddAmenable.of_le {t₁ t₂ : TopologicalSpace A}
    [@IsTopologicalAddGroup A t₁ _] [@IsTopologicalAddGroup A t₂ _] (h : t₁ ≤ t₂)
    (ha : @AddAmenable A _ t₁ _) : @AddAmenable A _ t₂ _ := by
  let φ : @ContinuousAddMonoidHom A A _ _ t₁ t₂ :=
    @ContinuousAddMonoidHom.mk A A _ _ t₁ t₂ (AddMonoidHom.id A) (continuous_id_of_le h)
  exact @AddAmenable.of_denseRange A A _ t₁ _ _ t₂ _ ha φ
    (@Function.Surjective.denseRange A t₂ A _ fun x => ⟨x, AddMonoidHom.id_apply A x⟩)

attribute [to_additive existing] Amenable.of_le

end Basic

end TauCeti

namespace ContinuousAddEquiv

open TauCeti

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Additive amenability is invariant under topological additive-group isomorphisms. -/
theorem addAmenable_iff (e : A ≃ₜ+ B) : AddAmenable A ↔ AddAmenable B := by
  rw [← amenable_multiplicative_iff, ← amenable_multiplicative_iff, e.toMultiplicative.amenable_iff]

attribute [to_additive existing ContinuousAddEquiv.addAmenable_iff] ContinuousMulEquiv.amenable_iff

end ContinuousAddEquiv

namespace TauCeti

section FiniteAndProd

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- A finite additive topological group is amenable, for any additive-group topology. -/
instance (priority := 100) AddAmenable.of_finite [Finite A] : AddAmenable A :=
  ⟨inferInstance⟩

attribute [to_additive existing] Amenable.of_finite

/-- The product of two amenable additive topological groups is amenable. -/
instance AddAmenable.prod [AddAmenable A] [AddAmenable B] : AddAmenable (A × B) :=
  ⟨(ContinuousMulEquiv.prodMultiplicative A B).amenable_iff.2 inferInstance⟩

attribute [to_additive existing AddAmenable.prod] Amenable.prod

variable (A B) in
/-- A product of two additive topological groups is amenable exactly when both factors are. -/
theorem addAmenable_prod_iff : AddAmenable (A × B) ↔ AddAmenable A ∧ AddAmenable B := by
  rw [← amenable_multiplicative_iff, (ContinuousMulEquiv.prodMultiplicative A B).amenable_iff,
    amenable_prod_iff, amenable_multiplicative_iff, amenable_multiplicative_iff]

attribute [to_additive existing addAmenable_prod_iff] amenable_prod_iff

/-- The product of a finite family of amenable additive topological groups is amenable. -/
instance AddAmenable.pi {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, AddGroup (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalAddGroup (A i)] [∀ i, AddAmenable (A i)] :
    AddAmenable (∀ i, A i) :=
  ⟨(ContinuousMulEquiv.piMultiplicative A).amenable_iff.2 inferInstance⟩

attribute [to_additive existing] Amenable.pi

/-- A product of a finite family of additive topological groups is amenable exactly when every
factor is. -/
theorem addAmenable_pi_iff {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, AddGroup (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalAddGroup (A i)] :
    AddAmenable (∀ i, A i) ↔ ∀ i, AddAmenable (A i) := by
  simp_rw [← amenable_multiplicative_iff, (ContinuousMulEquiv.piMultiplicative A).amenable_iff,
    amenable_pi_iff]

attribute [to_additive existing addAmenable_pi_iff] amenable_pi_iff

end FiniteAndProd

section Discrete

variable {A : Type*} [AddGroup A] [TopologicalSpace A]

section DiscreteTopology

variable [DiscreteTopology A]

variable (A) in
/-- A discrete additive group is amenable exactly when all bounded functions admit a normalized
positive translation-invariant real linear functional. -/
theorem addAmenable_iff_exists_boundedContinuousFunction_mean :
    AddAmenable A ↔ ∃ m : (A →ᵇ ℝ) →ₚ[ℝ] ℝ, m 1 = 1 ∧
      ∀ (a : A) (f : A →ᵇ ℝ),
        m (f.compContinuous (ContinuousMap.addLeft (-a))) = m f := by
  rw [← amenable_multiplicative_iff,
    amenable_iff_exists_boundedContinuousFunction_mean (Multiplicative A)]
  let toAddMap : C(Multiplicative A, A) := ⟨Multiplicative.toAdd, continuous_toAdd⟩
  let ofAddMap : C(A, Multiplicative A) := ⟨Multiplicative.ofAdd, continuous_ofAdd⟩
  constructor
  · rintro ⟨m, hm1, hm⟩
    refine ⟨{ toFun f := m (f.compContinuous toAddMap)
              map_add' f g := map_add m _ _
              map_smul' c f := map_smul m c _
              monotone' _ _ h := OrderHomClass.mono m fun x => h x.toAdd }, hm1, fun a f => ?_⟩
    exact hm (Multiplicative.ofAdd a) (f.compContinuous toAddMap)
  · rintro ⟨m, hm1, hm⟩
    refine ⟨{ toFun f := m (f.compContinuous ofAddMap)
              map_add' f g := map_add m _ _
              map_smul' c f := map_smul m c _
              monotone' _ _ h := OrderHomClass.mono m fun x => h (Multiplicative.ofAdd x) },
      hm1, fun g f => ?_⟩
    have htrans : (f.compContinuous (ContinuousMap.mulLeft g⁻¹)).compContinuous ofAddMap =
        (f.compContinuous ofAddMap).compContinuous (ContinuousMap.addLeft (-g.toAdd)) := by
      ext x
      simp [ofAddMap, ofAdd_add]
    exact (congrArg m htrans).trans (hm g.toAdd (f.compContinuous ofAddMap))

/-- An additive topological group which is a homomorphic image of an amenable discrete additive
group is amenable, for every additive-group topology on the target. -/
theorem AddAmenable.of_surjective [AddAmenable A] {B : Type*} [AddGroup B]
    [TopologicalSpace B] [IsTopologicalAddGroup B] (φ : A →+ B) (hφ : Function.Surjective φ) :
    AddAmenable B :=
  .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hφ.denseRange

attribute [to_additive existing] Amenable.of_surjective

end DiscreteTopology

/-- An abstract additive group which is amenable with the discrete topology is amenable with any
additive-group topology. -/
theorem AddAmenable.of_discrete [IsTopologicalAddGroup A]
    (h : letI : TopologicalSpace A := ⊥;
      letI := discreteTopology_bot A; AddAmenable A) :
    AddAmenable A := by
  let : @DiscreteTopology A ⊥ := discreteTopology_bot A
  exact AddAmenable.of_le (t₁ := ⊥) bot_le h

attribute [to_additive existing] Amenable.of_discrete

end Discrete

section SubgroupAndExtension

variable {A B K Q : Type*} [AddGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddGroup K] [TopologicalSpace K] [DiscreteTopology K]
  [AddGroup Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- An additive group `B` which embeds by an injective homomorphism in an amenable discrete
additive group is amenable, for every additive-group topology on `B`. -/
theorem AddAmenable.of_injective [AddAmenable A] (φ : B →+ A) (hφ : Function.Injective φ) :
    AddAmenable B :=
  ⟨.of_injective φ.toMultiplicative fun _ _ hxy =>
    Multiplicative.toAdd.injective (hφ (Multiplicative.ofAdd.injective hxy))⟩

attribute [to_additive existing] Amenable.of_injective

/-- Every additive subgroup of an amenable discrete additive group is amenable. -/
instance AddAmenable.addSubgroup [AddAmenable A] (H : AddSubgroup A) : AddAmenable H :=
  .of_injective H.subtype H.subtype_injective

attribute [to_additive existing] Amenable.subgroup

/-- If `ψ : K →+ A` and `φ : A →+ Q` are homomorphisms of discrete additive groups with
`φ.ker ≤ ψ.range`, and `K` and `Q` are amenable, then `A` is amenable. -/
theorem AddAmenable.of_ker_le_range [AddAmenable K] [AddAmenable Q] (ψ : K →+ A) (φ : A →+ Q)
    (h : φ.ker ≤ ψ.range) : AddAmenable A :=
  ⟨.of_ker_le_range ψ.toMultiplicative φ.toMultiplicative (AddSubgroup.toSubgroup.monotone h)⟩

attribute [to_additive existing] Amenable.of_ker_le_range

/-- A discrete additive group with a normal additive subgroup `N` is amenable exactly when `N` and
`A ⧸ N` are amenable. -/
theorem addAmenable_iff_addSubgroup_quotient (N : AddSubgroup A) [N.Normal] :
    AddAmenable A ↔ AddAmenable N ∧ AddAmenable (A ⧸ N) := by
  have := QuotientAddGroup.discreteTopology (isOpen_discrete (N : Set A))
  exact ⟨fun _ => ⟨inferInstance,
      .of_surjective (QuotientAddGroup.mk' N) (QuotientAddGroup.mk'_surjective N)⟩,
    fun ⟨_, _⟩ => .of_ker_le_range N.subtype (QuotientAddGroup.mk' N) (by simp)⟩

attribute [to_additive existing addAmenable_iff_addSubgroup_quotient] amenable_iff_subgroup_quotient

/-- A discrete additive group is amenable when it has an amenable normal additive subgroup with
amenable quotient. -/
theorem AddAmenable.of_addSubgroup_quotient (N : AddSubgroup A) [N.Normal] [AddAmenable N]
    [AddAmenable (A ⧸ N)] : AddAmenable A :=
  (addAmenable_iff_addSubgroup_quotient N).2 ⟨‹_›, ‹_›⟩

attribute [to_additive existing] Amenable.of_subgroup_quotient

end SubgroupAndExtension

section DirectedUnion

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- An additive topological group `A` is amenable if, for a family of continuous additive
homomorphisms `φ i : K i →ₜ+ A` from amenable additive topological groups, every finite subset of
`A` lies in the range of some `φ i`. -/
theorem AddAmenable.of_forall_finset_subset_range {ι : Type*} {K : ι → Type*}
    [∀ i, AddGroup (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)]
    [∀ i, AddAmenable (K i)] (φ : ∀ i, K i →ₜ+ A)
    (h : ∀ s : Finset A, ∃ i, (s : Set A) ⊆ Set.range (φ i)) : AddAmenable A := by
  classical
  refine ⟨.of_forall_finset_subset_range (fun i => (φ i).toMultiplicative) fun s => ?_⟩
  obtain ⟨i, hi⟩ := h (s.image Multiplicative.toAdd)
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hi (Finset.mem_coe.2 (Finset.mem_image_of_mem Multiplicative.toAdd hx))
  exact ⟨Multiplicative.ofAdd k, by simp [hk]⟩

attribute [to_additive existing] Amenable.of_forall_finset_subset_range

/-- The supremum `⨆ i, H i` of a directed family of amenable additive subgroups `H i` of an
additive topological group is an amenable additive subgroup. -/
theorem addAmenable_iSup_of_directed {ι : Type*} {H : ι → AddSubgroup A}
    (hH : Directed (· ≤ ·) H) [∀ i, AddAmenable (H i)] : AddAmenable ↥(⨆ i, H i) := by
  have : ∀ i, Amenable ((H i).toSubgroup) :=
    fun i => (H i).toSubgroupContinuousMulEquiv.amenable_iff.1 inferInstance
  have hdir : Directed (· ≤ ·) fun i => (H i).toSubgroup := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hH i j
    exact ⟨k, AddSubgroup.toSubgroup.monotone hik, AddSubgroup.toSubgroup.monotone hjk⟩
  have hsup : Amenable ↥((⨆ i, H i).toSubgroup) := by
    rw [OrderIso.map_iSup AddSubgroup.toSubgroup]
    exact amenable_iSup_of_directed hdir
  exact ⟨(⨆ i, H i).toSubgroupContinuousMulEquiv.amenable_iff.2 hsup⟩

attribute [to_additive existing addAmenable_iSup_of_directed] amenable_iSup_of_directed

/-- An additive topological group which is the supremum of a directed family of amenable additive
subgroups is amenable. -/
theorem AddAmenable.of_directed_of_iSup_eq_top {ι : Type*} {H : ι → AddSubgroup A}
    (hH : Directed (· ≤ ·) H) (htop : ⨆ i, H i = ⊤) [∀ i, AddAmenable (H i)] : AddAmenable A := by
  have : ∀ i, Amenable ((H i).toSubgroup) :=
    fun i => (H i).toSubgroupContinuousMulEquiv.amenable_iff.1 inferInstance
  have hdir : Directed (· ≤ ·) fun i => (H i).toSubgroup := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hH i j
    exact ⟨k, AddSubgroup.toSubgroup.monotone hik, AddSubgroup.toSubgroup.monotone hjk⟩
  refine ⟨.of_directed_of_iSup_eq_top hdir ?_⟩
  rw [← OrderIso.map_iSup AddSubgroup.toSubgroup, htop, OrderIso.map_top]

attribute [to_additive existing] Amenable.of_directed_of_iSup_eq_top

/-- An additive topological group all of whose finitely generated additive subgroups are amenable
is amenable. -/
theorem AddAmenable.of_forall_fg (h : ∀ K : AddSubgroup A, K.FG → AddAmenable K) :
    AddAmenable A := by
  refine ⟨.of_forall_fg fun K hK => ?_⟩
  let K' : AddSubgroup A := AddSubgroup.toSubgroup.symm K
  have hK' : AddAmenable K' := h K' ((AddSubgroup.fg_iff_mul_fg K').2 (by simpa [K'] using hK))
  have heq : K'.toSubgroup = K := AddSubgroup.toSubgroup.apply_symm_apply K
  exact heq ▸ K'.toSubgroupContinuousMulEquiv.amenable_iff.1 inferInstance

attribute [to_additive existing] Amenable.of_forall_fg

end DirectedUnion

section Foelner

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- An additive group with additive Følner sets is amenable, for every additive-group topology. -/
theorem AddAmenable.of_hasAddFoelnerSets (h : HasAddFoelnerSets A) : AddAmenable A :=
  ⟨.of_hasFoelnerSets (hasFoelnerSets_multiplicative_iff.2 h)⟩

attribute [to_additive existing AddAmenable.of_hasAddFoelnerSets] Amenable.of_hasFoelnerSets

/-- An additive topological group is amenable when it has an additive Følner family for counting
measure, along a nontrivial filter. -/
theorem AddAmenable.of_isAddFoelner [MeasurableSpace A] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Set A}
    (hF : IsAddFoelner A MeasureTheory.Measure.count l F) : AddAmenable A :=
  .of_hasAddFoelnerSets hF.hasAddFoelnerSets

attribute [to_additive existing AddAmenable.of_isAddFoelner] Amenable.of_isFoelner

/-- An additive topological group is amenable when it has finite nonempty sets `F i` with
`|(a +ᵥ F i) △ F i| / |F i| → 0` for every `a`, along a nontrivial filter. -/
theorem AddAmenable.of_tendsto_card_vadd_symmDiff_div_card [DecidableEq A] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset A} (hne : ∀ i, (F i).Nonempty)
    (h : ∀ a : A, Tendsto (fun i => (#((a +ᵥ F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    AddAmenable A :=
  .of_hasAddFoelnerSets (.of_tendsto_card_vadd_symmDiff_div_card (Eventually.of_forall hne) h)

attribute [to_additive existing AddAmenable.of_tendsto_card_vadd_symmDiff_div_card]
  Amenable.of_tendsto_card_smul_symmDiff_div_card

/-- An amenable discrete additive group has additive Følner sets. -/
theorem AddAmenable.hasAddFoelnerSets [DiscreteTopology A] [AddAmenable A] :
    HasAddFoelnerSets A :=
  hasFoelnerSets_multiplicative_iff.1 Amenable.hasFoelnerSets

attribute [to_additive existing AddAmenable.hasAddFoelnerSets] Amenable.hasFoelnerSets

/-- A discrete additive group is amenable exactly when it has additive Følner sets. -/
theorem addAmenable_iff_hasAddFoelnerSets [DiscreteTopology A] :
    AddAmenable A ↔ HasAddFoelnerSets A :=
  ⟨fun _ => AddAmenable.hasAddFoelnerSets, .of_hasAddFoelnerSets⟩

attribute [to_additive existing addAmenable_iff_hasAddFoelnerSets] amenable_iff_hasFoelnerSets

/-- For any measurable space on `A` with measurable singletons, a discrete additive group `A` is
amenable exactly when Mathlib's maximal counting-measure additive Følner filter
`maxAddFoelner A Measure.count` is nontrivial. -/
theorem addAmenable_iff_maxAddFoelner_neBot [DiscreteTopology A] [MeasurableSpace A]
    [MeasurableSingletonClass A] :
    AddAmenable A ↔
      NeBot (maxAddFoelner A (MeasureTheory.Measure.count : MeasureTheory.Measure A)) :=
  addAmenable_iff_hasAddFoelnerSets.trans hasAddFoelnerSets_iff_maxAddFoelner_neBot

attribute [to_additive existing addAmenable_iff_maxAddFoelner_neBot] amenable_iff_maxFoelner_neBot

/-- A discrete additive group is amenable exactly when for every finite `K ⊆ A` and every `ε > 0`
there is a finite nonempty `F ⊆ A` with `|(a +ᵥ F) △ F| < ε · |F|` for all `a ∈ K`. -/
theorem addAmenable_iff_exists_finset [DiscreteTopology A] [DecidableEq A] :
    AddAmenable A ↔ ∀ K : Finset A, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, F.Nonempty ∧ ∀ a ∈ K, (#((a +ᵥ F) ∆ F) : ℝ) < ε * #F :=
  addAmenable_iff_hasAddFoelnerSets.trans hasAddFoelnerSets_iff

attribute [to_additive existing addAmenable_iff_exists_finset] amenable_iff_exists_finset

/-- A countable discrete additive group is amenable exactly when there is a sequence of finite
nonempty sets whose relative translation boundaries tend to zero for every element. -/
theorem addAmenable_iff_exists_seq [DiscreteTopology A] [Countable A] [DecidableEq A] :
    AddAmenable A ↔ ∃ F : ℕ → Finset A, (∀ n, (F n).Nonempty) ∧
      ∀ a : A, Tendsto (fun n => (#((a +ᵥ F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) :=
  addAmenable_iff_hasAddFoelnerSets.trans hasAddFoelnerSets_iff_exists_seq

attribute [to_additive existing addAmenable_iff_exists_seq] amenable_iff_exists_seq

end Foelner

end TauCeti
