/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Characteristic
public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import TauCeti.Topology.Algebra.Group.ClosedSubgroup
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Extension

/-!
# The maximal pro-`p` quotient of a profinite group

The **pro-`p` kernel** `proPKernel p G` of a topological group `G` is the intersection of the
open normal subgroups whose quotient is a `p`-group, and the **maximal pro-`p` quotient** is
`maximalProPQuotient p G = G ⧸ proPKernel p G`. For a profinite `G` this quotient is the
universal pro-`p` group receiving a continuous homomorphism from `G`.

The one substantial step is that `G(p)` really is pro-`p`. This is a compactness argument
rather than a formal one: an open normal subgroup `M` of `G` containing `proPKernel p G`
already contains one member `U` of the defining family, because the sets `U \ M` form a
downward directed family of closed subsets of the compact space `G` with empty intersection,
so one of them is empty. Directedness of the family is where `IsPGroup.quotient_inf` enters.
Once that is known, `G ⧸ M` is a quotient of `G ⧸ U` and hence a `p`-group, and the open
normal subgroups of `G(p)` are exactly the images of such `M`.

The universal property goes the other way and needs no compactness: if `P` is profinite and
pro-`p` and `f : G →* P` is continuous, then for each open normal `V ≤ P` the preimage
`V.comap f` is an open normal subgroup of `G` with `p`-group quotient, so `f` maps
`proPKernel p G` into every `V`, and the open normal subgroups of a profinite group intersect
in `1`.

The pro-`p` kernel `N` of a profinite group `G` has trivial maximal pro-`p` quotient itself. This
is not the definition, since the open normal subgroups of `N` need not come from those of `G`.
The pro-`p` kernel `K` of `N` is topologically characteristic in `N`, hence normal and closed in
`G`; then `G ⧸ K` is an extension of the pro-`p` group `G ⧸ N` by a quotient of the pro-`p` group
`N ⧸ K`, so it is pro-`p`, and the universal property gives `N ≤ K`.

Everything before the compactness lemma is stated for an arbitrary topological group: the
kernel, its normality, its closedness and its behaviour under continuous homomorphisms all
hold there. Compactness of `G` is assumed exactly where it is used.

## Main definitions

* `TauCeti.proPKernel`: the intersection of the open normal subgroups with `p`-group quotient.
* `TauCeti.maximalProPQuotient`: the quotient `G ⧸ proPKernel p G`, written `G(p)` in prose.
* `TauCeti.maximalProPQuotient.mk`: the canonical quotient homomorphism.
* `TauCeti.maximalProPQuotient.map`: the functorial action on continuous homomorphisms.
* `TauCeti.maximalProPQuotient.lift`: the canonical factorisation of a continuous homomorphism
  to a profinite pro-`p` group.

## Main results

* `TauCeti.isClosed_proPKernel`: the pro-`p` kernel is closed, so `G(p)` is profinite again.
* `TauCeti.proPKernel_eq_top_iff`: the pro-`p` kernel is the whole group exactly when every
  relevant `p`-group quotient is trivial.
* `TauCeti.exists_openNormalSubgroup_isPGroup_subset`: a set with compact complement containing
  the pro-`p` kernel contains a member of the defining family.
* `TauCeti.isProP_maximalProPQuotient`: `G(p)` is pro-`p`.
* `TauCeti.existsUnique_continuousMonoidHom_maximalProPQuotient`: a continuous homomorphism
  from `G` to a profinite pro-`p` group factors uniquely and continuously through `G(p)`.
* `TauCeti.maximalProPQuotient.lift_comp_map` and `TauCeti.maximalProPQuotient.comp_lift`: that
  factorisation is natural in the source and in the target.
* `TauCeti.proPKernel_eq_bot_iff`: `G` is pro-`p` if and only if its pro-`p` kernel is trivial;
  with `TauCeti.proPKernel_maximalProPQuotient_eq_bot` this is idempotence of `G ↦ G(p)`.
* `TauCeti.maximalProPQuotient.range_map`: the image of the induced map `G(p) → H(p)` is the
  image of the image of `f`; so its index divides that of `f` and it is open when `f` has open
  image (`TauCeti.maximalProPQuotient.index_range_map_dvd`,
  `TauCeti.maximalProPQuotient.isOpen_range_map`).
* `TauCeti.map_proPKernel_eq`: continuous multiplicative equivalences preserve the pro-`p`
  kernel.
* `TauCeti.maximalProPQuotient.congr`: hence they induce isomorphisms of maximal pro-`p`
  quotients.
* `TauCeti.isTopCharacteristic_proPKernel`: the pro-`p` kernel is topologically characteristic.
* `TauCeti.proPKernel_proPKernel_eq_top`: the pro-`p` kernel of a profinite group has no
  nontrivial continuous finite `p`-group quotient, so every continuous homomorphism from it to a
  profinite pro-`p` group is trivial (`TauCeti.eq_one_of_proPKernel_eq_top`).

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*.
-/

public section

namespace TauCeti

universe u v w

section Defs

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]

/-- The **pro-`p` kernel** of a topological group `G`: the intersection of the open normal
subgroups of `G` whose quotient is a `p`-group. For profinite `G` it is the kernel of the
universal continuous homomorphism from `G` to a pro-`p` group. -/
def proPKernel : Subgroup G :=
  ⨅ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}, U.1.toSubgroup

/-- The pro-`p` kernel is a normal subgroup. -/
instance proPKernel_normal : (proPKernel p G).Normal :=
  Subgroup.normal_iInf_normal fun U ↦ U.1.isNormal'

/-- The **maximal pro-`p` quotient** `G(p) = G ⧸ proPKernel p G`. -/
abbrev maximalProPQuotient : Type u := G ⧸ proPKernel p G

/-- The canonical homomorphism from `G` to its maximal pro-`p` quotient. -/
abbrev maximalProPQuotient.mk : G →* maximalProPQuotient p G :=
  QuotientGroup.mk' (proPKernel p G)

/-- The canonical quotient homomorphism sends an element to its quotient class. -/
@[simp]
theorem maximalProPQuotient.mk_apply (x : G) :
    maximalProPQuotient.mk p G x = QuotientGroup.mk x :=
  rfl

/-- The canonical homomorphism to the maximal pro-`p` quotient is surjective. -/
theorem maximalProPQuotient.mk_surjective :
    Function.Surjective (maximalProPQuotient.mk p G) :=
  QuotientGroup.mk'_surjective (proPKernel p G)

/-- The canonical homomorphism to the maximal pro-`p` quotient is continuous. -/
theorem maximalProPQuotient.continuous_mk : Continuous (maximalProPQuotient.mk p G) :=
  QuotientGroup.continuous_mk

end Defs

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- Membership in the pro-`p` kernel, unfolded over the defining family. -/
theorem mem_proPKernel_iff {x : G} :
    x ∈ proPKernel p G ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) → x ∈ U.toSubgroup := by
  rw [proPKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The pro-`p` kernel is contained in every open normal subgroup with `p`-group quotient. -/
theorem proPKernel_le {U : OpenNormalSubgroup G} (hU : IsPGroup p (G ⧸ U.toSubgroup)) :
    proPKernel p G ≤ U.toSubgroup :=
  fun _ hx ↦ mem_proPKernel_iff.mp hx U hU

/-- The pro-`p` kernel is closed, so its quotient is profinite when `G` is profinite. -/
instance isClosed_proPKernel [SeparatelyContinuousMul G] :
    IsClosed ((proPKernel p G : Subgroup G) : Set G) := by
  rw [proPKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun U ↦ U.1.toOpenSubgroup.isClosed

/-! ### Trivial maximal quotients -/

/-- The pro-`p` kernel is the whole group exactly when every open normal subgroup with
`p`-group quotient is the whole group. Equivalently, every quotient in the defining family
is trivial. -/
theorem proPKernel_eq_top_iff : proPKernel p G = ⊤ ↔
    ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) → U.toSubgroup = ⊤ := by
  rw [proPKernel, iInf_eq_top]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The maximal pro-`p` quotient is trivial exactly when the pro-`p` kernel is the whole
group. -/
theorem maximalProPQuotient.subsingleton_iff :
    Subsingleton (maximalProPQuotient p G) ↔ proPKernel p G = ⊤ :=
  QuotientGroup.subsingleton_iff

/-- If `p` does not divide the cardinality of `G`, then its pro-`p` kernel is the whole group.
For prime `p` this hypothesis forces `G` to be finite. -/
theorem proPKernel_eq_top_of_not_dvd_card [Fact p.Prime]
    (hcard : ¬ p ∣ Nat.card G) : proPKernel p G = ⊤ := by
  rw [proPKernel_eq_top_iff]
  intro U hU
  rw [← QuotientGroup.subsingleton_iff]
  apply (Nat.card_eq_one_iff_unique.mp ?_).1
  exact hU.card_eq_or_dvd.resolve_right fun hp ↦
    hcard (hp.trans (Subgroup.card_quotient_dvd_card U.toSubgroup))

/-- If `p` does not divide the cardinality of `G`, then its maximal pro-`p` quotient is
trivial. For prime `p` this hypothesis forces `G` to be finite. -/
theorem maximalProPQuotient.subsingleton_of_not_dvd_card [Fact p.Prime]
    (hcard : ¬ p ∣ Nat.card G) : Subsingleton (maximalProPQuotient p G) :=
  maximalProPQuotient.subsingleton_iff.mpr (proPKernel_eq_top_of_not_dvd_card hcard)

/-! ### Functoriality -/

/-- A continuous homomorphism carries the pro-`p` kernel into the pro-`p` kernel. -/
theorem proPKernel_le_comap (f : G →* H) (hf : Continuous f) :
    proPKernel p G ≤ (proPKernel p H).comap f := by
  intro x hx
  rw [Subgroup.mem_comap, mem_proPKernel_iff]
  intro V hV
  exact OpenNormalSubgroup.mem_comap.mp <| mem_proPKernel_iff.mp hx (V.comap f hf)
    (hV.quotient_comap f)

/-- The image of the pro-`p` kernel under a continuous homomorphism lies in the pro-`p`
kernel of the target. -/
theorem map_proPKernel_le (f : G →* H) (hf : Continuous f) :
    (proPKernel p G).map f ≤ proPKernel p H :=
  Subgroup.map_le_iff_le_comap.mpr (proPKernel_le_comap f hf)

/-- Continuous multiplicative equivalences identify the pro-`p` kernels of their source and
target. In particular, the pro-`p` kernel is characteristic under continuous automorphisms. -/
@[simp]
theorem map_proPKernel_eq (e : G ≃ₜ* H) :
    (proPKernel p G).map ((e : G ≃* H) : G →* H) = proPKernel p H := by
  refine le_antisymm (map_proPKernel_le _ e.continuous) fun x hx ↦ ?_
  have hsymm : e.symm x ∈ proPKernel p G :=
    map_proPKernel_le e.symm.toMulEquiv.toMonoidHom e.symm.continuous
      (Subgroup.mem_map_of_mem _ hx)
  exact ⟨e.symm x, hsymm, e.apply_symm_apply x⟩

/-- The pro-`p` kernel is topologically characteristic for every topological group and every
natural number `p`. -/
theorem isTopCharacteristic_proPKernel (p : ℕ) :
    IsTopCharacteristic G (proPKernel p G) :=
  isTopCharacteristic_iff_map_eq.mpr fun φ ↦ map_proPKernel_eq φ

/-- The map induced on maximal pro-`p` quotients by a continuous homomorphism. -/
def maximalProPQuotient.map (f : G →* H) (hf : Continuous f) :
    maximalProPQuotient p G →* maximalProPQuotient p H :=
  QuotientGroup.map (proPKernel p G) (proPKernel p H) f (proPKernel_le_comap f hf)

/-- The induced map on maximal pro-`p` quotients is computed on classes by `f`. -/
@[simp]
theorem maximalProPQuotient.map_mk (f : G →* H) (hf : Continuous f) (x : G) :
    maximalProPQuotient.map (p := p) f hf (x : maximalProPQuotient p G) =
      maximalProPQuotient.mk p H (f x) := by
  rfl

/-- The induced map on maximal pro-`p` quotients is continuous. -/
theorem maximalProPQuotient.continuous_map (f : G →* H) (hf : Continuous f) :
    Continuous (maximalProPQuotient.map (p := p) f hf) :=
  (QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hf)

/-- Functoriality: the identity induces the identity. -/
@[simp]
theorem maximalProPQuotient.map_id :
    maximalProPQuotient.map (p := p) (MonoidHom.id G) continuous_id = MonoidHom.id _ := by
  ext x
  rfl

/-- Functoriality: the induced maps compose. -/
@[simp]
theorem maximalProPQuotient.map_comp {K : Type w} [Group K] [TopologicalSpace K] (f : G →* H)
    (hf : Continuous f) (g : H →* K) (hg : Continuous g) :
    maximalProPQuotient.map (p := p) (g.comp f) (hg.comp hf) =
      (maximalProPQuotient.map g hg).comp (maximalProPQuotient.map f hf) := by
  ext x
  rfl

/-- The image of the map `G(p) → H(p)` induced by `f : G → H` is the image in `H(p)` of the image
of `f`. -/
theorem maximalProPQuotient.range_map (f : G →* H) (hf : Continuous f) :
    (maximalProPQuotient.map (p := p) f hf).range = f.range.map (maximalProPQuotient.mk p H) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with
    | H x => exact ⟨f x, ⟨x, rfl⟩, (maximalProPQuotient.map_mk f hf x).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨maximalProPQuotient.mk p G x, maximalProPQuotient.map_mk f hf x⟩

/-- The image of the map of maximal pro-`p` quotients induced by `f : G → H` has index dividing the
index of the image of `f`. -/
theorem maximalProPQuotient.index_range_map_dvd (f : G →* H) (hf : Continuous f) :
    (maximalProPQuotient.map (p := p) f hf).range.index ∣ f.range.index := by
  rw [maximalProPQuotient.range_map]
  exact Subgroup.index_map_dvd _ (maximalProPQuotient.mk_surjective p H)

/-- If `f : G → H` has open image, so does the induced map of maximal pro-`p` quotients. -/
theorem maximalProPQuotient.isOpen_range_map [IsTopologicalGroup H] (f : G →* H)
    (hf : Continuous f) (ho : IsOpen (f.range : Set H)) :
    IsOpen ((maximalProPQuotient.map (p := p) f hf).range : Set (maximalProPQuotient p H)) := by
  rw [maximalProPQuotient.range_map, Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe _ ho

/-- The isomorphism of maximal pro-`p` quotients induced by an isomorphism of topological groups,
which carries the pro-`p` kernel onto the pro-`p` kernel (`map_proPKernel_eq`). -/
noncomputable def maximalProPQuotient.congr (e : G ≃ₜ* H) :
    maximalProPQuotient p G ≃ₜ* maximalProPQuotient p H :=
  e.quotientCongr _ _ (map_proPKernel_eq e)

/-- The induced isomorphism of maximal pro-`p` quotients is computed on classes by `e`. -/
@[simp]
theorem maximalProPQuotient.congr_mk (e : G ≃ₜ* H) (x : G) :
    maximalProPQuotient.congr (p := p) e (x : maximalProPQuotient p G) =
      maximalProPQuotient.mk p H (e x) :=
  e.quotientCongr_mk _ _ _ x

/-- The inverse of the induced isomorphism of maximal pro-`p` quotients is computed on classes by
`e.symm`. -/
@[simp]
theorem maximalProPQuotient.congr_symm_mk (e : G ≃ₜ* H) (y : H) :
    (maximalProPQuotient.congr (p := p) e).symm (y : maximalProPQuotient p H) =
      maximalProPQuotient.mk p G (e.symm y) :=
  e.quotientCongr_symm_mk _ _ _ y

/-! ### The compactness step -/

/-- A set with compact complement containing the pro-`p` kernel contains an open normal
subgroup with `p`-group quotient. In a compact space this applies to every open neighbourhood
of the kernel. -/
theorem exists_openNormalSubgroup_isPGroup_subset [SeparatelyContinuousMul G] {s : Set G}
    (hs : IsCompact sᶜ) (hKs : (proPKernel p G : Set G) ⊆ s) :
    ∃ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) ∧ (U : Set G) ⊆ s := by
  let S : Type u := {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}
  -- The family contains the whole group, so it is nonempty.
  have : Subsingleton (G ⧸ (openNormalSubgroupTop G).toSubgroup) :=
    QuotientGroup.subsingleton_iff.mpr (openNormalSubgroupTop_toSubgroup G)
  have htop : IsPGroup p (G ⧸ (openNormalSubgroupTop G).toSubgroup) := .of_subsingleton p _
  have : Nonempty S := ⟨⟨openNormalSubgroupTop G, htop⟩⟩
  have hinf : Disjoint sᶜ (⋂ U : S, (U.1 : Set G)) := by
    rw [Set.disjoint_compl_left_iff_subset]
    exact fun x hx ↦ hKs (mem_proPKernel_iff.mpr fun U hU ↦ Set.mem_iInter.mp hx ⟨U, hU⟩)
  -- Compactness reduces disjointness from the intersection to one member of the family.
  obtain ⟨U, hU⟩ := hs.elim_directed_family_closed (fun U : S ↦ (U.1 : Set G))
    (fun U ↦ U.1.toOpenSubgroup.isClosed) hinf fun U V ↦
      ⟨⟨U.1 ⊓ V.1, U.2.quotient_inf V.2⟩,
        SetLike.coe_subset_coe.mpr inf_le_left, SetLike.coe_subset_coe.mpr inf_le_right⟩
  exact ⟨U.1, U.2, Set.disjoint_compl_left_iff_subset.mp hU⟩

section Compact

variable [SeparatelyContinuousMul G] [CompactSpace G]

/-- An open normal subgroup containing the pro-`p` kernel has `p`-group quotient. -/
theorem isPGroup_quotient_of_proPKernel_le {U : OpenNormalSubgroup G}
    (hU : proPKernel p G ≤ U.toSubgroup) : IsPGroup p (G ⧸ U.toSubgroup) := by
  obtain ⟨V, hV, hVU⟩ :=
    exists_openNormalSubgroup_isPGroup_subset U.toOpenSubgroup.isOpen.isClosed_compl.isCompact hU
  have hle : V.toSubgroup ≤ (U.toSubgroup).comap (MonoidHom.id G) := by
    rw [Subgroup.comap_id]
    exact hVU
  refine hV.of_surjective (QuotientGroup.map V.toSubgroup U.toSubgroup (MonoidHom.id G) hle) ?_
  exact QuotientGroup.map_surjective_of_surjective V.toSubgroup U.toSubgroup (MonoidHom.id G)
    (QuotientGroup.mk'_surjective U.toSubgroup) hle

/-- For an open normal subgroup of a compact group, containing the pro-`p` kernel is the same
as having a `p`-group quotient. -/
theorem proPKernel_le_iff_isPGroup_quotient {U : OpenNormalSubgroup G} :
    proPKernel p G ≤ U.toSubgroup ↔ IsPGroup p (G ⧸ U.toSubgroup) :=
  ⟨isPGroup_quotient_of_proPKernel_le, proPKernel_le⟩

/-- **The maximal pro-`p` quotient is pro-`p`.** -/
theorem isProP_maximalProPQuotient : IsProP p (maximalProPQuotient p G) := by
  refine isProP_iff.mpr fun M ↦ ?_
  let π : G →* maximalProPQuotient p G := maximalProPQuotient.mk p G
  let M' := M.comap π QuotientGroup.continuous_mk
  have hKM' : proPKernel p G ≤ M'.toSubgroup := by
    rw [M.toSubgroup_comap π QuotientGroup.continuous_mk]
    exact (QuotientGroup.ker_mk' (proPKernel p G)).symm.trans_le (π.ker_le_comap M.toSubgroup)
  have hM' : IsPGroup p (G ⧸ M'.toSubgroup) := isPGroup_quotient_of_proPKernel_le hKM'
  have hle : M'.toSubgroup ≤ M.toSubgroup.comap π :=
    (M.toSubgroup_comap π QuotientGroup.continuous_mk).le
  refine hM'.of_surjective (QuotientGroup.map M'.toSubgroup M.toSubgroup π hle) ?_
  exact QuotientGroup.map_surjective_of_surjective M'.toSubgroup M.toSubgroup π
    ((QuotientGroup.mk'_surjective M.toSubgroup).comp
      (maximalProPQuotient.mk_surjective p G)) hle

end Compact

/-! ### The universal property -/

section UniversalProperty

variable {P : Type v} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- A continuous homomorphism to a profinite pro-`p` group kills the pro-`p` kernel. -/
theorem proPKernel_le_ker (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    proPKernel p G ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  refine Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun V ↦ ?_
  exact OpenNormalSubgroup.mem_comap.mp <| mem_proPKernel_iff.mp hx (V.comap f hf)
    ((isProP_iff.mp hP V).quotient_comap f)

/-- The canonical factorisation of a continuous homomorphism to a profinite pro-`p` group
through the maximal pro-`p` quotient. -/
def maximalProPQuotient.lift (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    maximalProPQuotient p G →* P :=
  QuotientGroup.lift (proPKernel p G) f fun _ hx ↦ proPKernel_le_ker hP f hf hx

/-- The factorisation through the maximal pro-`p` quotient computes as `f` on classes. -/
@[simp]
theorem maximalProPQuotient.lift_mk (hP : IsProP p P) (f : G →* P) (hf : Continuous f) (x : G) :
    maximalProPQuotient.lift hP f hf (x : maximalProPQuotient p G) = f x := by
  rfl

/-- The factorisation through the maximal pro-`p` quotient recovers `f`. -/
@[simp]
theorem maximalProPQuotient.lift_comp_mk (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    (maximalProPQuotient.lift hP f hf).comp (maximalProPQuotient.mk p G) = f := by
  ext x
  rfl

/-- The factorisation through the maximal pro-`p` quotient is continuous. -/
theorem maximalProPQuotient.continuous_lift (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    Continuous (maximalProPQuotient.lift hP f hf) :=
  (QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff.mpr hf

/-- The factorisation through the maximal pro-`p` quotient is the only homomorphism restricting
to `f` along the quotient map. -/
theorem maximalProPQuotient.lift_unique (hP : IsProP p P) (f : G →* P) (hf : Continuous f)
    {g : maximalProPQuotient p G →* P} (hg : ∀ x : G, g (maximalProPQuotient.mk p G x) = f x) :
    g = maximalProPQuotient.lift hP f hf := by
  ext x
  exact hg x

/-- Naturality in the source: the factorisation of `f ∘ u` is the factorisation of `f`
precomposed with the map induced by `u`. -/
theorem maximalProPQuotient.lift_comp_map {G' : Type w} [Group G'] [TopologicalSpace G']
    (hP : IsProP p P) (f : G →* P) (hf : Continuous f) (u : G' →* G) (hu : Continuous u) :
    (maximalProPQuotient.lift hP f hf).comp (maximalProPQuotient.map (p := p) u hu) =
      maximalProPQuotient.lift hP (f.comp u) (hf.comp hu) := by
  ext x
  rfl

/-- Naturality in the target: postcomposing the factorisation of `f` with a continuous
homomorphism of profinite pro-`p` groups gives the factorisation of the composite. -/
theorem maximalProPQuotient.comp_lift {Q : Type w} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [CompactSpace Q] [TotallyDisconnectedSpace Q] (hP : IsProP p P)
    (hQ : IsProP p Q) (f : G →* P) (hf : Continuous f) (v : P →* Q) (hv : Continuous v) :
    v.comp (maximalProPQuotient.lift hP f hf) =
      maximalProPQuotient.lift hQ (v.comp f) (hv.comp hf) := by
  ext x
  rfl

/-- **The universal property of the maximal pro-`p` quotient.** A continuous homomorphism to a
profinite pro-`p` group factors uniquely and continuously through the canonical quotient map. -/
theorem existsUnique_continuousMonoidHom_maximalProPQuotient (hP : IsProP p P) (f : G →* P)
    (hf : Continuous f) :
    ∃! g : maximalProPQuotient p G →* P,
      Continuous g ∧ ∀ x : G, g (maximalProPQuotient.mk p G x) = f x :=
  ⟨maximalProPQuotient.lift hP f hf,
    ⟨maximalProPQuotient.continuous_lift hP f hf, maximalProPQuotient.lift_mk hP f hf⟩,
    fun _ hg ↦ maximalProPQuotient.lift_unique hP f hf hg.2⟩

/-- A topological group with no nontrivial `p`-group quotient by an open normal subgroup admits
no nontrivial continuous homomorphism to a profinite pro-`p` group. -/
theorem eq_one_of_proPKernel_eq_top (h : proPKernel p G = ⊤) (hP : IsProP p P) (f : G →* P)
    (hf : Continuous f) : f = 1 :=
  MonoidHom.ker_eq_top_iff.mp (top_le_iff.mp (h ▸ proPKernel_le_ker hP f hf))

end UniversalProperty

/-! ### Pro-`p` groups and idempotence -/

section Idempotence

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A profinite group is pro-`p` exactly when its pro-`p` kernel is trivial. -/
theorem proPKernel_eq_bot_iff : proPKernel p G = ⊥ ↔ IsProP p G := by
  refine ⟨fun h ↦ isProP_iff.mpr fun U ↦
      isPGroup_quotient_of_proPKernel_le (h.trans_le bot_le), fun hG ↦ ?_⟩
  refine le_antisymm ?_ bot_le
  rw [← Subgroup.iInf_openNormalSubgroup_eq_bot (G := G)]
  exact le_iInf fun U ↦ proPKernel_le (isProP_iff.mp hG U)

/-- The pro-`p` kernel of a profinite pro-`p` group is trivial. -/
theorem IsProP.proPKernel_eq_bot (hG : IsProP p G) : proPKernel p G = ⊥ :=
  proPKernel_eq_bot_iff.mpr hG

/-- The canonical continuous multiplicative equivalence from the maximal pro-`p` quotient of a
profinite pro-`p` group to the group itself. -/
def maximalProPQuotient.equivOfIsProP (hG : IsProP p G) :
    maximalProPQuotient p G ≃ₜ* G :=
  ContinuousMulEquiv.mk
    ((QuotientGroup.quotientMulEquivOfEq hG.proPKernel_eq_bot).trans
      QuotientGroup.quotientBot)
    ((QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff.mpr continuous_id)
    (maximalProPQuotient.continuous_mk p G)

/-- The canonical equivalence from a pro-`p` group's maximal pro-`p` quotient sends each class
to its representative. -/
@[simp]
theorem maximalProPQuotient.equivOfIsProP_mk (hG : IsProP p G) (x : G) :
    maximalProPQuotient.equivOfIsProP hG (x : maximalProPQuotient p G) = x :=
  (rfl)

/-- **Idempotence.** The pro-`p` kernel of a maximal pro-`p` quotient is trivial. -/
theorem proPKernel_maximalProPQuotient_eq_bot :
    proPKernel p (maximalProPQuotient p G) = ⊥ :=
  proPKernel_eq_bot_iff.mpr isProP_maximalProPQuotient

/-- **Idempotence.** Applying the maximal pro-`p` quotient construction twice gives a group
canonically continuously equivalent to applying it once. -/
def maximalProPQuotient.idempotentEquiv :
    maximalProPQuotient p (maximalProPQuotient p G) ≃ₜ* maximalProPQuotient p G :=
  maximalProPQuotient.equivOfIsProP isProP_maximalProPQuotient

/-- The idempotence equivalence sends each class to its representative. -/
@[simp]
theorem maximalProPQuotient.idempotentEquiv_mk (x : maximalProPQuotient p G) :
    maximalProPQuotient.idempotentEquiv
      (x : maximalProPQuotient p (maximalProPQuotient p G)) = x :=
  (rfl)

end Idempotence

/-! ### The pro-`p` kernel has no `p`-quotient -/

section Kernel

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The pro-`p` kernel has no `p`-quotient.** The pro-`p` kernel of the pro-`p` kernel `N` of a
profinite group is all of `N`. Equivalently, `N` has no nontrivial continuous finite `p`-group
quotient (`TauCeti.proPKernel_eq_top_iff`), so every continuous homomorphism from `N` to a profinite
pro-`p` group is trivial (`TauCeti.eq_one_of_proPKernel_eq_top`). -/
@[simp]
theorem proPKernel_proPKernel_eq_top : proPKernel p (proPKernel p G) = ⊤ := by
  set N := proPKernel p G
  have : CompactSpace N := isCompact_iff_compactSpace.mp (isClosed_proPKernel (G := G)).isCompact
  set K := proPKernel p N
  -- The image `K'` of `K` in `G` is closed, and normal because `K` is topologically
  -- characteristic in the normal subgroup `N`.
  set K' : Subgroup G := K.map N.subtype
  have hK'N : K' ≤ N := Subgroup.map_subtype_le K
  have : K'.Normal := (isTopCharacteristic_proPKernel p).map_subtype_normal
  have : IsClosed (K' : Set G) := by
    rw [Subgroup.coe_map]
    exact (isClosed_proPKernel (G := G)).isClosedMap_subtype_val _ (isClosed_proPKernel (G := N))
  -- `G ⧸ K'` maps onto the pro-`p` group `G ⧸ N`.
  let f : G ⧸ K' →* G ⧸ N := QuotientGroup.map K' N (MonoidHom.id G) hK'N
  have hf : Continuous f :=
    -- `f ∘ QuotientGroup.mk` is `QuotientGroup.mk` by `QuotientGroup.map_mk`, definitionally.
    (QuotientGroup.isQuotientMap_mk K').continuous_iff.mpr QuotientGroup.continuous_mk
  have hfs : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective K' N (MonoidHom.id G)
      (QuotientGroup.mk'_surjective N) hK'N
  -- The kernel of that map is a continuous image of the pro-`p` group `N ⧸ K`.
  let ψ : N →* f.ker := ((QuotientGroup.mk' K').comp N.subtype).codRestrict f.ker fun n ↦
    (QuotientGroup.eq_one_iff (N := N) _).mpr n.2
  have hψK : K ≤ ψ.ker := fun k hk ↦
    Subtype.ext <| (QuotientGroup.eq_one_iff _).mpr ⟨k, hk, rfl⟩
  let φ : maximalProPQuotient p N →* f.ker := QuotientGroup.lift K ψ hψK
  have hφ : Continuous φ :=
    -- `φ ∘ QuotientGroup.mk` is `ψ` by `QuotientGroup.lift_mk`, definitionally.
    (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr
      ((QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _)
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk ⟨g, (QuotientGroup.eq_one_iff g).mp hx⟩, rfl⟩
  -- So `G ⧸ K'` is pro-`p`, and the universal property puts `N` inside `K'`.
  have hpro : IsProP p (G ⧸ K') := isProP_maximalProPQuotient.of_ker_isProP
    (MonoidHom.isOpenQuotientMap_of_isQuotientMap
      (Topology.IsQuotientMap.of_surjective_continuous hfs hf)).isOpenMap hfs
    (isProP_maximalProPQuotient.of_surjective φ hφ hφs)
  have hle : N ≤ K' := by
    simpa using proPKernel_le_ker hpro (QuotientGroup.mk' K') QuotientGroup.continuous_mk
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨k, hk, hkx⟩ := hle x.2
  rwa [Subtype.ext hkx] at hk

/-- The maximal pro-`p` quotient of the pro-`p` kernel of a profinite group is trivial. -/
theorem maximalProPQuotient.subsingleton_proPKernel :
    Subsingleton (maximalProPQuotient p (proPKernel p G)) :=
  maximalProPQuotient.subsingleton_iff.mpr proPKernel_proPKernel_eq_top

end Kernel

end TauCeti
