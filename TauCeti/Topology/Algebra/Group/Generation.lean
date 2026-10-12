/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
public import TauCeti.Topology.Algebra.Group.Subgroup
import Mathlib.GroupTheory.Schreier

/-!
# Topological generation of a topological group

A subset of a topological group *generates it topologically* when the subgroup it generates is
dense, that is when `(Subgroup.closure s).topologicalClosure = ⊤`. This file introduces the
predicate `IsTopologicallyFinitelyGenerated`, asking for a *finite* topological generating set,
and its basic API.

The predicate is covariant: a topological generating set is carried to a topological generating
set by any continuous homomorphism with dense range, hence in particular by a continuous
surjection and so to every quotient. It is invariant under a topological group isomorphism, and
it has the uniqueness half one expects of a notion of generation — a continuous homomorphism into
a Hausdorff monoid is determined by its values on a topological generating set, as is a
homomorphism with open kernel into an arbitrary group. Counting the latter over a finite target
is what bounds the supply of open subgroups of a compact group.

For a profinite group topological finite generation is detected by the finite quotients; that
criterion is in `TauCeti/Topology/Algebra/Group/Profinite/Generation.lean`.

## Main results

* `TauCeti.IsTopologicallyFinitelyGenerated`: some finite subset generates a dense subgroup.
* `TauCeti.topologicalClosure_closure_image_eq_top`: the image of a topological generating set
  under a continuous homomorphism with dense range is a topological generating set.
* `TauCeti.IsTopologicallyFinitelyGenerated.of_denseRange`,
  `TauCeti.IsTopologicallyFinitelyGenerated.of_surjective`,
  `TauCeti.IsTopologicallyFinitelyGenerated.quotient`: topological finite generation passes along
  continuous homomorphisms with dense range, along continuous surjections, and to quotients.
* `TauCeti.topologicalClosure_closure_sup_eq_top_iff`: a subset together with a normal subgroup
  `K` topologically generates `G` exactly when its image topologically generates `G ⧸ K`.
* `MonoidHom.ker_eq_topologicalClosure_normalClosure_insert_pow_of_orderOf_eq`: if a character
  kills all but one topological generator, whose image has finite order `m > 0`, its kernel is the
  closed normal closure of the killed generators and the `m`-th power of the remaining one.
* `TauCeti.IsTopologicallyFinitelyGenerated.of_openSubgroup_of_finiteIndex`,
  `TauCeti.IsTopologicallyFinitelyGenerated.of_openSubgroup`: topological finite generation
  passes to open finite-index subgroups, in particular to open subgroups of compact groups.
* `MonoidHom.eqOn_topologicalClosure_closure` and
  `MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top`: continuous homomorphisms into a
  Hausdorff monoid agreeing on a set agree on the closed subgroup it generates, so such a
  homomorphism is determined by its values on a topological generating set.
* `MonoidHom.eq_of_eqOn_of_isOpen_ker`: the same uniqueness statement for a homomorphism with
  open kernel, for which the target carries no topology.
* `TauCeti.IsTopologicallyFinitelyGenerated.finite_monoidHom_isOpen_ker`: only finitely many
  homomorphisms with open kernel go from a topologically finitely generated group to a fixed
  finite group.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Corollary 3.6.3.
* Mathlib's `Subgroup.fg_of_index_ne_zero` and
  `DenseRange.subset_closure_image_preimage_of_isOpen`.
-/

public section

namespace TauCeti

/-- **Topological finite generation**: some finite subset of `G` generates a dense subgroup.
For a profinite group this is the notion of finite generation that all of the pro-`p` theory
uses; abstract finite generation is strictly stronger and is never meant. -/
def IsTopologicallyFinitelyGenerated (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop :=
  ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The defining property of `IsTopologicallyFinitelyGenerated`, available to modules that only
see the declaration and not its body. -/
@[simp]
theorem isTopologicallyFinitelyGenerated_iff :
    IsTopologicallyFinitelyGenerated G ↔
      ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤ :=
  Iff.rfl

/-- A finite topological generating set, presented as a set rather than as a `Finset`, witnesses
topological finite generation. -/
theorem _root_.Set.Finite.isTopologicallyFinitelyGenerated {s : Set G} (hs : s.Finite)
    (hgen : (Subgroup.closure s).topologicalClosure = ⊤) :
    IsTopologicallyFinitelyGenerated G :=
  ⟨hs.toFinset, by rwa [hs.coe_toFinset]⟩

/-- A finitely generated group, in any group topology, is topologically finitely generated: an
algebraic generating set is a topological one. Via `Group.fg_of_finite` this covers the finite
groups, and so all the finite quotients of a profinite group. -/
theorem isTopologicallyFinitelyGenerated_of_fg [Group.FG G] :
    IsTopologicallyFinitelyGenerated G := by
  obtain ⟨s, hs, hsfin⟩ := Group.fg_iff.mp ‹Group.FG G›
  exact hsfin.isTopologicallyFinitelyGenerated <| by
    rw [hs]
    exact eq_top_iff.mpr (⊤ : Subgroup G).le_topologicalClosure

/-- The image of a topological generating set under a continuous homomorphism with dense range
is again a topological generating set. -/
theorem topologicalClosure_closure_image_eq_top {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f : G →* H} (hf : Continuous f)
    (hf' : DenseRange f) : (Subgroup.closure (f '' s)).topologicalClosure = ⊤ := by
  rw [← MonoidHom.map_closure]
  exact hf'.topologicalClosure_map_subgroup hf hs

/-- **The kernel of a character whose marked value has finite order.** If the topological group
`G` is topologically generated by `insert a S`, `χ` has closed kernel, kills `S`, and `χ a` has
order `m > 0`, then `ker χ` is the closed normal closure of `S` together with `a ^ m`. -/
theorem _root_.MonoidHom.ker_eq_topologicalClosure_normalClosure_insert_pow_of_orderOf_eq
    {A : Type*} [Group A] (χ : G →* A) (hker : IsClosed (χ.ker : Set G))
    {S : Set G} {a : G} {m : ℕ} (hgen : (Subgroup.closure (insert a S)).topologicalClosure = ⊤)
    (hS : ∀ s ∈ S, χ s = 1) (hm : 0 < m) (ha : orderOf (χ a) = m) :
    χ.ker = (Subgroup.normalClosure (insert (a ^ m) S)).topologicalClosure := by
  set N := (Subgroup.normalClosure (insert (a ^ m) S)).topologicalClosure
  have hNker : N ≤ χ.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hker
    rintro x (rfl | hx)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_pow, ← ha, pow_orderOf_eq_one]
    · exact MonoidHom.mem_ker.2 (hS x hx)
  have haN : a ^ m ∈ N :=
    Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (Set.mem_insert _ _))
  have hSN : S ⊆ N := fun s hs ↦
    Subgroup.le_topologicalClosure _
      (Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ hs))
  have hgenQ :
      (Subgroup.closure ({(a : G ⧸ N)} : Set (G ⧸ N))).topologicalClosure = ⊤ := by
    refine top_le_iff.1 ((topologicalClosure_closure_image_eq_top hgen
      (f := QuotientGroup.mk' N) QuotientGroup.continuous_mk
      QuotientGroup.mk_surjective.denseRange).ge.trans
      (Subgroup.topologicalClosure_mono ((Subgroup.closure_le _).2 ?_)))
    rintro _ ⟨x, (rfl | hx), rfl⟩
    · exact Subgroup.subset_closure rfl
    · rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 (hSN hx)]
      exact one_mem _
  have hpow : (a : G ⧸ N) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact haN
  have hfin : IsOfFinOrder (a : G ⧸ N) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, hpow⟩
  have hfinite : Finite (Subgroup.zpowers (a : G ⧸ N)) := hfin.finite_zpowers
  have hzpowers : Subgroup.zpowers (a : G ⧸ N) = ⊤ := by
    rw [← (Set.finite_coe_iff.1 hfinite).isClosed.subgroup_topologicalClosure_eq,
      Subgroup.zpowers_eq_closure, hgenQ]
  refine le_antisymm (fun x hx ↦ ?_) hNker
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp
    (hzpowers ▸ Subgroup.mem_top (x : G ⧸ N))
  have hχz : (χ a) ^ z = 1 := by
    rw [← QuotientGroup.lift_mk N hNker a, ← map_zpow, hz, QuotientGroup.lift_mk]
    exact MonoidHom.mem_ker.mp hx
  obtain ⟨k, rfl⟩ : (m : ℤ) ∣ z := by
    rw [← ha, orderOf_dvd_iff_zpow_eq_one]
    exact hχz
  rw [← QuotientGroup.eq_one_iff]
  rw [← hz, zpow_mul, zpow_natCast, hpow, one_zpow]

/-- Two continuous homomorphisms into a Hausdorff monoid that agree on a set agree on the closed
subgroup it generates. -/
theorem _root_.MonoidHom.eqOn_topologicalClosure_closure {M : Type*} [Monoid M]
    [TopologicalSpace M] [T2Space M] {s : Set G} {f g : G →* M} (hf : Continuous f)
    (hg : Continuous g) (hfg : Set.EqOn f g s) :
    Set.EqOn f g ((Subgroup.closure s).topologicalClosure : Set G) := by
  rw [Subgroup.topologicalClosure_coe]
  exact (MonoidHom.eqOn_closure hfg).closure hf hg

/-- A continuous homomorphism out of a topological group is determined by its values on a
topological generating set, provided the target is a Hausdorff monoid. This is the uniqueness
half of every construction that defines a map on generators. -/
theorem _root_.MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top {M : Type*} [Monoid M]
    [TopologicalSpace M] [T2Space M] {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f g : G →* M} (hf : Continuous f)
    (hg : Continuous g) (hfg : Set.EqOn f g s) : f = g :=
  MonoidHom.ext fun x ↦
    MonoidHom.eqOn_topologicalClosure_closure hf hg hfg (by rw [hs]; exact Subgroup.mem_top x)

/-- The range of a continuous homomorphism lies in a closed subgroup exactly when a topological
generating set of the source maps into it. -/
theorem _root_.MonoidHom.range_le_iff_of_topologicalClosure_closure_eq_top {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f : G →* H} (hf : Continuous f)
    {T : Subgroup H} (hT : IsClosed (T : Set H)) : f.range ≤ T ↔ ∀ x ∈ s, f x ∈ T := by
  refine ⟨fun h x _ ↦ h ⟨x, rfl⟩, fun h ↦ ?_⟩
  rw [MonoidHom.range_eq_map, ← hs]
  refine (f.map_topologicalClosure_le hf _).trans (Subgroup.topologicalClosure_minimal _ ?_ hT)
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

/-- The closed range of a continuous homomorphism is the closure of a subgroup `T` as soon as a
topological generating set of the source maps into that closure and `T` lies in the range. Out
of a compact group into a Hausdorff group the range is closed by
`MonoidHom.isClosed_range_of_continuous`. -/
theorem _root_.MonoidHom.range_eq_topologicalClosure_of_topologicalClosure_closure_eq_top
    {s : Set G} (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f : G →* H}
    (hf : Continuous f) (hf' : IsClosed (f.range : Set H)) {T : Subgroup H}
    (h₁ : ∀ x ∈ s, f x ∈ T.topologicalClosure) (h₂ : T ≤ f.range) :
    f.range = T.topologicalClosure :=
  le_antisymm ((MonoidHom.range_le_iff_of_topologicalClosure_closure_eq_top hs hf
    (Subgroup.isClosed_topologicalClosure _)).mpr h₁)
    (Subgroup.topologicalClosure_minimal _ h₂ hf')

/-- Topological finite generation passes along a continuous homomorphism with dense range. -/
theorem IsTopologicallyFinitelyGenerated.of_denseRange
    (hG : IsTopologicallyFinitelyGenerated G) {f : G →* H} (hf : Continuous f)
    (hf' : DenseRange f) : IsTopologicallyFinitelyGenerated H := by
  obtain ⟨s, hs⟩ := hG
  exact (s.finite_toSet.image f).isTopologicallyFinitelyGenerated
    (topologicalClosure_closure_image_eq_top hs hf hf')

/-- Topological finite generation passes to continuous surjective images. -/
theorem IsTopologicallyFinitelyGenerated.of_surjective
    (hG : IsTopologicallyFinitelyGenerated G) {f : G →* H} (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsTopologicallyFinitelyGenerated H :=
  hG.of_denseRange hf hsurj.denseRange

/-- Topological finite generation passes to quotients by normal subgroups, closed or not. -/
theorem IsTopologicallyFinitelyGenerated.quotient (hG : IsTopologicallyFinitelyGenerated G)
    (N : Subgroup G) [N.Normal] : IsTopologicallyFinitelyGenerated (G ⧸ N) :=
  hG.of_surjective QuotientGroup.continuous_mk (QuotientGroup.mk'_surjective N)

/-- **Generation modulo a normal subgroup.** A subset `s` together with a normal subgroup `K`
topologically generates `G` exactly when the image of `s` topologically generates the quotient
`G ⧸ K`. Neither compactness of `G` nor closedness of `K` is needed: the quotient map is open, so
it exchanges preimages and closures. -/
theorem topologicalClosure_closure_sup_eq_top_iff {s : Set G} {K : Subgroup G} [K.Normal] :
    (Subgroup.closure s ⊔ K).topologicalClosure = ⊤ ↔
      (Subgroup.closure (QuotientGroup.mk' K '' s)).topologicalClosure = ⊤ := by
  -- `closure s ⊔ K` is the preimage of the image of `closure s`, and the quotient map is open, so
  -- the closure of that preimage is the preimage of the closure; the map is onto, so a preimage
  -- is everything exactly when the set is.
  have hcomap : (Subgroup.closure (QuotientGroup.mk' K '' s)).comap (QuotientGroup.mk' K) =
      Subgroup.closure s ⊔ K := by
    rw [← MonoidHom.map_closure, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  simp only [← Subgroup.coe_eq_univ, Subgroup.topologicalClosure_coe]
  rw [← hcomap, Subgroup.coe_comap, QuotientGroup.coe_mk',
    ← QuotientGroup.isOpenMap_coe.preimage_closure_eq_closure_preimage QuotientGroup.continuous_mk,
    Set.preimage_eq_univ_iff, QuotientGroup.mk_surjective.range_eq, Set.univ_subset_iff]

/-- An open finite-index subgroup of a topologically finitely generated group is topologically
finitely generated. -/
theorem IsTopologicallyFinitelyGenerated.of_openSubgroup_of_finiteIndex
    (hG : IsTopologicallyFinitelyGenerated G) (U : OpenSubgroup G)
    [U.toSubgroup.FiniteIndex] : IsTopologicallyFinitelyGenerated (↥U.toSubgroup) := by
  -- A finite topological generating set `s` of `G` generates a dense subgroup `D`; the subgroup
  -- `U ⊓ D` has finite index in `D`, so it is finitely generated by Schreier's lemma, and it is
  -- dense in `U`.
  obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.mp hG
  have hD : Dense ((Subgroup.closure (s : Set G) : Subgroup G) : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs, Subgroup.coe_top]
  exact isTopologicallyFinitelyGenerated_of_fg.of_denseRange
    (Subgroup.continuous_subgroupOf_codRestrict _ _)
    (hD.denseRange_subgroupOf_codRestrict U.isOpen)

/-- An open subgroup of a topologically finitely generated compact topological group is
topologically finitely generated. -/
theorem IsTopologicallyFinitelyGenerated.of_openSubgroup [CompactSpace G]
    (hG : IsTopologicallyFinitelyGenerated G) (U : OpenSubgroup G) :
    IsTopologicallyFinitelyGenerated (↥U.toSubgroup) :=
  hG.of_openSubgroup_of_finiteIndex U

/-- Topological finite generation is invariant under topological group isomorphism. -/
theorem isTopologicallyFinitelyGenerated_congr (e : G ≃ₜ* H) :
    IsTopologicallyFinitelyGenerated G ↔ IsTopologicallyFinitelyGenerated H :=
  ⟨fun hG ↦ hG.of_surjective (f := (e : G →* H)) e.continuous e.surjective,
    fun hH ↦ hH.of_surjective (f := (e.symm : H →* G)) e.symm.continuous e.symm.surjective⟩

section OpenKernel

/-- A homomorphism from a topological group into a monoid carrying the discrete topology is
continuous exactly when its kernel is open. -/
theorem _root_.MonoidHom.continuous_iff_isOpen_ker {F : Type*} [MulOneClass F] [TopologicalSpace F]
    [DiscreteTopology F] (f : G →* F) : Continuous f ↔ IsOpen (f.ker : Set G) := by
  -- The kernel is the preimage of the open point `1`.
  refine ⟨fun hf ↦ ?_, f.continuous_of_isOpen_ker⟩
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete _).preimage hf

/-- A homomorphism whose kernel is open is determined by its values on a topological generating
set: the equalizer of two such homomorphisms contains the (open) intersection of their kernels,
hence is open, hence closed, hence contains the whole group. The target carries no topology at
all, which is what makes the statement usable for a target such as a permutation group that has
no topology to hand; compare `MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top`, which
asks instead for continuity into a Hausdorff target. -/
theorem _root_.MonoidHom.eq_of_eqOn_of_isOpen_ker {F : Type*} [Group F] {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) {f g : G →* F}
    (hf : IsOpen (f.ker : Set G)) (hg : IsOpen (g.ker : Set G)) (hfg : Set.EqOn f g s) :
    f = g := by
  -- Membership in `MonoidHom.eqLocus` is the equation `f x = g x`, as in `MonoidHom.eqOn_closure`.
  have hsub : f.ker ⊓ g.ker ≤ f.eqLocus g := fun x hx ↦ by
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hx
    exact hx.1.trans hx.2.symm
  have hopen : IsOpen ((f.eqLocus g : Subgroup G) : Set G) :=
    Subgroup.isOpen_mono hsub (by simpa only [Subgroup.coe_inf] using hf.inter hg)
  have htop : f.eqLocus g = ⊤ :=
    top_le_iff.mp <| hs ▸ Subgroup.topologicalClosure_minimal _
      ((Subgroup.closure_le _).mpr hfg) (Subgroup.isClosed_of_isOpen _ hopen)
  exact MonoidHom.eq_of_eqOn_top fun x _ ↦ htop.ge (Subgroup.mem_top x)

/-- **A topologically finitely generated group has few homomorphisms to a finite group.** There
are only finitely many homomorphisms with open kernel from a topologically finitely generated
topological group to a fixed finite group, because such a homomorphism is determined by its
values on a finite topological generating set. -/
theorem IsTopologicallyFinitelyGenerated.finite_monoidHom_isOpen_ker
    (hG : IsTopologicallyFinitelyGenerated G) (F : Type*) [Group F] [Finite F] :
    Finite {f : G →* F // IsOpen (f.ker : Set G)} := by
  obtain ⟨s, hs⟩ := hG
  have : Finite (s : Set G) := s.finite_toSet.to_subtype
  refine Finite.of_injective (fun f (x : (s : Set G)) ↦ f.1 x) fun f g hfg ↦ Subtype.ext ?_
  exact MonoidHom.eq_of_eqOn_of_isOpen_ker hs f.2 g.2 fun x hx ↦ congrFun hfg ⟨x, hx⟩

end OpenKernel

end TauCeti
