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
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Additive amenability: products, subgroups, extensions, directed unions, and Følner sets

This module complements the additive amenability API in
`TauCeti.GroupTheory.Amenable.Basic`, `TauCeti.GroupTheory.Amenable.Finite`,
`TauCeti.GroupTheory.Amenable.Discrete`, and `TauCeti.GroupTheory.Amenable.DiscreteFoelner`
with additive versions of finite products, subgroups and extensions of discrete groups, directed
unions, and Følner characterizations.

## Main results

* `TauCeti.AddAmenable.prod`, `TauCeti.addAmenable_prod_iff`, `TauCeti.AddAmenable.pi`, and
  `TauCeti.addAmenable_pi_iff`: finite products.
* `TauCeti.AddAmenable.of_injective`, `TauCeti.AddAmenable.addSubgroup`,
  `TauCeti.AddAmenable.of_ker_le_range`, `TauCeti.addAmenable_iff_addSubgroup_quotient`, and
  `TauCeti.AddAmenable.of_addSubgroup_quotient`: subgroups and extensions of discrete additive
  groups.
* `TauCeti.AddAmenable.of_forall_finset_subset_range`, `TauCeti.addAmenable_iSup_of_directed`,
  `TauCeti.AddAmenable.of_directed_of_iSup_eq_top`, and `TauCeti.AddAmenable.of_forall_fg`:
  directed unions and reduction to finitely generated additive subgroups.
* `TauCeti.AddAmenable.of_hasAddFoelnerSets`, `TauCeti.addAmenable_iff_hasAddFoelnerSets`,
  `TauCeti.addAmenable_iff_maxAddFoelner_neBot`, `TauCeti.addAmenable_iff_exists_finset`,
  `TauCeti.addAmenable_iff_exists_seq`,
  `TauCeti.addAmenable_iff_exists_finset_of_closure_eq_top`, and
  `TauCeti.addAmenable_iff_exists_finset_of_closure_finset_eq_top`: Følner characterizations of
  additive amenability.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.
* A. Garrido, *An introduction to amenable groups*, §§1–3.
-/

public section

noncomputable section

open Filter Finset Topology
open scoped Pointwise symmDiff

namespace TauCeti

section Prod

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

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

end Prod

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

/-- If `ψ : K →+ B` and `φ : B →+ Q` are homomorphisms with `φ.ker ≤ ψ.range` and `K`, `Q` are
amenable discrete additive groups, then `B` is amenable for every additive-group topology on `B`. -/
theorem AddAmenable.of_ker_le_range [AddAmenable K] [AddAmenable Q] (ψ : K →+ B) (φ : B →+ Q)
    (h : φ.ker ≤ ψ.range) : AddAmenable B :=
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

/-- An additive topological group is amenable when it has eventually nonempty finite sets `F i`
with `|(a +ᵥ F i) △ F i| / |F i| → 0` for every `a`, along a nontrivial filter. -/
theorem AddAmenable.of_tendsto_card_vadd_symmDiff_div_card [DecidableEq A] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset A} (hne : ∀ᶠ i in l, (F i).Nonempty)
    (h : ∀ a : A, Tendsto (fun i => (#((a +ᵥ F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    AddAmenable A :=
  .of_hasAddFoelnerSets (.of_tendsto_card_vadd_symmDiff_div_card hne h)

attribute [to_additive existing AddAmenable.of_tendsto_card_vadd_symmDiff_div_card]
  Amenable.of_tendsto_card_smul_symmDiff_div_card

end Foelner

section DiscreteFoelner

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- An amenable discrete additive group has additive Følner sets. -/
theorem AddAmenable.hasAddFoelnerSets [AddAmenable A] :
    HasAddFoelnerSets A :=
  hasFoelnerSets_multiplicative_iff.1 Amenable.hasFoelnerSets

attribute [to_additive existing AddAmenable.hasAddFoelnerSets] Amenable.hasFoelnerSets

/-- A discrete additive group is amenable exactly when it has additive Følner sets. -/
theorem addAmenable_iff_hasAddFoelnerSets :
    AddAmenable A ↔ HasAddFoelnerSets A :=
  ⟨fun _ => AddAmenable.hasAddFoelnerSets, .of_hasAddFoelnerSets⟩

attribute [to_additive existing addAmenable_iff_hasAddFoelnerSets] amenable_iff_hasFoelnerSets

/-- For any measurable space on `A` with measurable singletons, a discrete additive group `A` is
amenable exactly when Mathlib's maximal counting-measure additive Følner filter
`maxAddFoelner A Measure.count` is nontrivial. -/
theorem addAmenable_iff_maxAddFoelner_neBot [MeasurableSpace A] [MeasurableSingletonClass A] :
    AddAmenable A ↔
      NeBot (maxAddFoelner A (MeasureTheory.Measure.count : MeasureTheory.Measure A)) :=
  addAmenable_iff_hasAddFoelnerSets.trans hasAddFoelnerSets_iff_maxAddFoelner_neBot

attribute [to_additive existing addAmenable_iff_maxAddFoelner_neBot] amenable_iff_maxFoelner_neBot

/-- A discrete additive group is amenable exactly when for every finite `K ⊆ A` and every `ε > 0`
there is a finite nonempty `F ⊆ A` with `|(a +ᵥ F) △ F| < ε · |F|` for all `a ∈ K`. -/
theorem addAmenable_iff_exists_finset [DecidableEq A] :
    AddAmenable A ↔ ∀ K : Finset A, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, F.Nonempty ∧ ∀ a ∈ K, (#((a +ᵥ F) ∆ F) : ℝ) < ε * #F :=
  addAmenable_iff_hasAddFoelnerSets.trans hasAddFoelnerSets_iff

attribute [to_additive existing addAmenable_iff_exists_finset] amenable_iff_exists_finset

/-- A discrete additive group generated by `S` is amenable exactly when for every finite `K ⊆ S`
and every `ε > 0` there is a finite nonempty `F ⊆ A` with `|(a +ᵥ F) △ F| < ε · |F|` for all
`a ∈ K`. -/
theorem addAmenable_iff_exists_finset_of_closure_eq_top [DecidableEq A] {S : Set A}
    (hS : AddSubgroup.closure S = ⊤) :
    AddAmenable A ↔ ∀ K : Finset A, (K : Set A) ⊆ S → ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, F.Nonempty ∧ ∀ a ∈ K, (#((a +ᵥ F) ∆ F) : ℝ) < ε * #F :=
  addAmenable_iff_hasAddFoelnerSets.trans (hasAddFoelnerSets_iff_of_closure_eq_top hS)

attribute [to_additive existing addAmenable_iff_exists_finset_of_closure_eq_top]
  amenable_iff_exists_finset_of_closure_eq_top

/-- A discrete additive group generated by a finite set `S` is amenable exactly when for every
`ε > 0` there is a finite nonempty `F ⊆ A` with `|(s +ᵥ F) △ F| < ε · |F|` for all `s ∈ S`. -/
theorem addAmenable_iff_exists_finset_of_closure_finset_eq_top [DecidableEq A] {S : Finset A}
    (hS : AddSubgroup.closure (S : Set A) = ⊤) :
    AddAmenable A ↔ ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, F.Nonempty ∧ ∀ s ∈ S, (#((s +ᵥ F) ∆ F) : ℝ) < ε * #F :=
  addAmenable_iff_hasAddFoelnerSets.trans (hasAddFoelnerSets_iff_of_closure_finset_eq_top hS)

attribute [to_additive existing addAmenable_iff_exists_finset_of_closure_finset_eq_top]
  amenable_iff_exists_finset_of_closure_finset_eq_top

/-- A countable discrete additive group is amenable exactly when there is a sequence of finite
nonempty sets whose relative translation boundaries tend to zero for every element. -/
theorem addAmenable_iff_exists_seq [Countable A] [DecidableEq A] :
    AddAmenable A ↔ ∃ F : ℕ → Finset A, (∀ n, (F n).Nonempty) ∧
      ∀ a : A, Tendsto (fun n => (#((a +ᵥ F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) :=
  addAmenable_iff_hasAddFoelnerSets.trans hasAddFoelnerSets_iff_exists_seq

attribute [to_additive existing addAmenable_iff_exists_seq] amenable_iff_exists_seq

end DiscreteFoelner

end TauCeti
