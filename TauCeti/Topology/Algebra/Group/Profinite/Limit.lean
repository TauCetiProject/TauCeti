/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti AI contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Profinite groups: the finite-quotient limit description

The unbundled workhorse of profinite group theory, phrased for the type-class stack
`[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]`
(with `TotallyDisconnectedSpace G` only where needed) so that consumers outside the
`ProfiniteGrp` category can use them directly.

* The limit description: a family of cosets of the open normal subgroups of a compact totally
  disconnected group, compatible along the canonical quotient maps, is realized by a unique
  element of `G` (`existsUnique_forall_mk_eq`; Ribes and Zalesskii, *Profinite Groups*,
  Proposition 1.1.4). This is the unbundled counterpart of `ProfiniteGrp.toLimit_surjective`
  and `ProfiniteGrp.toLimit_injective`, which describe the same identification for the
  `ProfiniteGrp` category. The compactness input is
  `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`.
* Two companion forms of the same identification: a point of `G` is determined by its images in
  the finite quotients (`eq_of_forall_mk_eq`), and a map into `G` is continuous as soon as all
  of its finite-quotient shadows are (`continuous_iff_forall_continuous_mk`).
* The same identification for homomorphisms: a family of homomorphisms `H →* G ⧸ U` compatible
  along the quotient maps is induced by a unique homomorphism `H →* G`
  (`existsUnique_monoidHom_mk'_comp_eq`).
* The same for subgroups: a family `H` of subgroups of the quotients `G ⧸ U` cuts out the closed
  subgroup `limitSubgroup H` of `G` (`isClosed_limitSubgroup`), and when `H` is compatible along
  the quotient maps and `G` is compact, its image in every `G ⧸ U` is exactly `H U`
  (`map_mk'_limitSubgroup`). Conversely a closed subgroup is cut out by its own images
  (`limitSubgroup_map_mk'`), so the two constructions are mutually inverse.
* Sequential reconstruction along a sequence `N : ℕ → Subgroup G` of closed subgroups of a
  compact group with trivial intersection: a coset sequence `x k` has a unique common representative
  if every representative of `x (k + 1)` also represents `x k`
  (`existsUnique_forall_mk_eq_of_iInf_eq_bot`). For decreasing `N`, this is the inverse-limit
  description. When the `N k` are normal and decreasing,
  a compatible sequence of homomorphisms into the quotients `G ⧸ N k` comes from a unique
  homomorphism into `G` (`existsUnique_monoidHom_mk'_comp_eq_of_iInf_eq_bot`); when they are
  normal, a map into `G` is continuous as soon as its composites with the quotient maps are
  (`continuous_iff_forall_continuous_mk_of_iInf_eq_bot`); and when they are open and decreasing
  they form a neighbourhood basis of `1` (`hasAntitoneBasis_nhds_one_of_iInf_eq_bot`). The lower
  `p`-series of a pro-`p` group is a decreasing sequence of closed normal subgroups with trivial
  intersection, and its terms are open when the group is topologically finitely generated.
-/

public section

namespace TauCeti

section LimitDescription

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Limit description of a profinite group** (unbundled). A family `x` of cosets of the open
normal subgroups of a compact totally disconnected group `G` that is compatible along the
canonical quotient maps is realized by a unique element of `G`: the natural map from `G` to
the inverse limit of the quotients `G ⧸ U` over the open normal subgroups `U` is bijective.
The bundled counterpart for the `ProfiniteGrp` category is
`ProfiniteGrp.toLimit_surjective` together with `ProfiniteGrp.toLimit_injective`. -/
theorem existsUnique_forall_mk_eq (x : ∀ U : OpenNormalSubgroup G, G ⧸ (U : Subgroup G))
    (hcompat : ∀ (U V : OpenNormalSubgroup G) (_hle : (U : Subgroup G) ≤ V) (g : G),
      QuotientGroup.mk' (U : Subgroup G) g = x U → QuotientGroup.mk' (V : Subgroup G) g = x V) :
    ∃! g : G, ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g = x U := by
  have hneIdx : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⟨⊤, isOpen_univ⟩ }⟩
  have hne : ∀ U : OpenNormalSubgroup G,
      ((QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U}).Nonempty := fun U =>
    QuotientGroup.mk'_surjective (U : Subgroup G) (x U)
  have hcl : ∀ U : OpenNormalSubgroup G,
      IsClosed ((QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U}) := fun U =>
    isClosed_singleton.preimage (QuotientGroup.continuous_mk (N := (U : Subgroup G)))
  have hdir : Directed (· ⊇ ·) fun U : OpenNormalSubgroup G =>
      (QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U} := by
    rintro U V
    refine ⟨U ⊓ V, fun g hgU => ?_, fun g hgV => ?_⟩
    · rw [Set.mem_preimage, Set.mem_singleton_iff] at hgU ⊢
      exact hcompat (U ⊓ V) U inf_le_left g hgU
    · rw [Set.mem_preimage, Set.mem_singleton_iff] at hgV ⊢
      exact hcompat (U ⊓ V) V inf_le_right g hgV
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun U : OpenNormalSubgroup G => (QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U}) hdir hne
    (fun U ↦ (hcl U).isCompact) hcl
  refine ⟨g, fun U => Set.mem_iInter.mp hg U, fun g' hg' => ?_⟩
  have hgg : ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g = x U :=
    fun U => Set.mem_iInter.mp hg U
  have hgg' : ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g' = x U :=
    fun U => hg' U
  refine (inv_mul_eq_one.mp ?_).symm
  refine Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U => ?_
  exact QuotientGroup.eq.mp ((hgg U).trans (hgg' U).symm)

/-- Two elements of a profinite group with the same class modulo every open normal subgroup
are equal. -/
theorem eq_of_forall_mk_eq {x y : G}
    (h : ∀ U : OpenNormalSubgroup G, (x : G ⧸ U.toSubgroup) = (y : G ⧸ U.toSubgroup)) : x = y := by
  refine inv_mul_eq_one.mp (Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U ↦ ?_)
  exact QuotientGroup.eq.mp (h U)

/-- A map into a profinite group is continuous exactly when all of its composites with the
quotient maps onto the finite quotients are.

Only the quotients themselves are visible in the criterion, so continuity of a map built from
the limit description can be checked one finite quotient at a time. -/
theorem continuous_iff_forall_continuous_mk {X : Type*} [TopologicalSpace X] {f : X → G} :
    Continuous f ↔ ∀ U : OpenNormalSubgroup G,
      Continuous fun x ↦ (f x : G ⧸ U.toSubgroup) := by
  refine ⟨fun hf U ↦ QuotientGroup.continuous_mk.comp hf, fun h ↦ ?_⟩
  refine continuous_iff_continuousAt.mpr fun x₀ ↦ Filter.tendsto_def.mpr fun V hV ↦ ?_
  obtain ⟨W, hWV, hWopen, hWx⟩ := mem_nhds_iff.mp hV
  -- An open normal subgroup `U` small enough that the coset `f x₀ * U` stays inside `W`.
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hWopen.preimage (f := fun y ↦ f x₀ * y) (continuous_const.mul continuous_id))
    (by simpa using hWx)
  refine Filter.mem_of_superset
    (((h U).isOpen_preimage _ (isOpen_discrete {(f x₀ : G ⧸ U.toSubgroup)})).mem_nhds rfl)
    fun x hx ↦ ?_
  have hmem : (f x₀)⁻¹ * f x ∈ U.toSubgroup := by
    simpa using U.toSubgroup.inv_mem (QuotientGroup.eq.mp hx)
  exact hWV (by simpa using hU hmem)

/-- **Limit description of a profinite group, for homomorphisms.** A family of homomorphisms
`x N : H →* G ⧸ N` into the quotients of `G` by its open normal subgroups, compatible along the
quotient maps `G ⧸ N → G ⧸ N'` for `N ≤ N'`, is induced by a unique homomorphism `H →* G`. This is
the universal property of `G` as the inverse limit of its finite quotients, for abstract
homomorphisms out of a monoid `H` that carries no topology. -/
theorem existsUnique_monoidHom_mk'_comp_eq {H : Type*} [MulOneClass H]
    (x : ∀ N : OpenNormalSubgroup G, H →* G ⧸ N.toSubgroup)
    (hx : ∀ ⦃N N' : OpenNormalSubgroup G⦄ (hle : N ≤ N'),
      (QuotientGroup.mapOfLE hle).comp (x N) = x N') :
    ∃! φ : H →* G, ∀ N : OpenNormalSubgroup G, (QuotientGroup.mk' N.toSubgroup).comp φ = x N := by
  -- For a fixed `a : H`, the classes `x N a` form a compatible family of cosets, so the limit
  -- description of `G` realizes them by a unique element `φ a`.
  have hcompat : ∀ a : H, ∀ (U V : OpenNormalSubgroup G) (hle : (U : Subgroup G) ≤ V) (g : G),
      QuotientGroup.mk' (U : Subgroup G) g = x U a →
        QuotientGroup.mk' (V : Subgroup G) g = x V a := by
    intro a U V hle g hg
    rw [← hx hle, MonoidHom.comp_apply, ← hg, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mapOfLE_mk]
  choose φ hφ using fun a : H ↦ (existsUnique_forall_mk_eq (fun N ↦ x N a) (hcompat a)).exists
  refine ⟨MonoidHom.mk' φ fun a b ↦ eq_of_forall_mk_eq fun N ↦ ?_, fun N ↦ MonoidHom.ext (hφ · N),
    fun ψ hψ ↦ MonoidHom.ext fun a ↦ eq_of_forall_mk_eq fun N ↦ ?_⟩
  · -- Multiplicativity is checked in every finite quotient, where it is that of `x N`.
    calc (φ (a * b) : G ⧸ N.toSubgroup) = x N (a * b) := hφ (a * b) N
      _ = x N a * x N b := map_mul _ _ _
      _ = ((φ a * φ b : G) : G ⧸ N.toSubgroup) := by
        rw [QuotientGroup.mk_mul, ← hφ a N, ← hφ b N, QuotientGroup.mk'_apply,
          QuotientGroup.mk'_apply]
  · exact (DFunLike.congr_fun (hψ N) a).trans (hφ a N).symm

end LimitDescription

section LimitSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]
  {H : ∀ U : OpenNormalSubgroup G, Subgroup (G ⧸ U.toSubgroup)}

/-- The subgroup of `G` cut out by a family `H` of subgroups of its quotients `G ⧸ U` by open
normal subgroups: the elements whose class modulo every `U` lies in `H U`. It is closed
(`isClosed_limitSubgroup`), and when `H` is compatible along the quotient maps and `G` is
compact, its image in every `G ⧸ U` is `H U` (`map_mk'_limitSubgroup`). -/
def limitSubgroup (H : ∀ U : OpenNormalSubgroup G, Subgroup (G ⧸ U.toSubgroup)) : Subgroup G :=
  ⨅ U, (H U).comap (QuotientGroup.mk' U.toSubgroup)

/-- An element lies in `limitSubgroup H` exactly when its class modulo every `U` lies in
`H U`. -/
@[simp]
theorem mem_limitSubgroup_iff {g : G} :
    g ∈ limitSubgroup H ↔ ∀ U : OpenNormalSubgroup G, (g : G ⧸ U.toSubgroup) ∈ H U :=
  Subgroup.mem_iInf

variable [IsTopologicalGroup G]

/-- The subgroup cut out by a family of subgroups of the quotients by open normal subgroups is
closed. -/
theorem isClosed_limitSubgroup (H : ∀ U : OpenNormalSubgroup G, Subgroup (G ⧸ U.toSubgroup)) :
    IsClosed (limitSubgroup H : Set G) := by
  rw [limitSubgroup, Subgroup.coe_iInf]
  exact isClosed_iInter fun U ↦ (isClosed_discrete _).preimage QuotientGroup.continuous_mk

/-- A closed subgroup of a profinite group is cut out by the family of its images in the finite
quotients. Together with `map_mk'_limitSubgroup` this identifies the closed subgroups of `G` with
the compatible families of subgroups of the quotients `G ⧸ U`. -/
theorem limitSubgroup_map_mk' [CompactSpace G] [TotallyDisconnectedSpace G] (P : Subgroup G)
    (hP : IsClosed (P : Set G)) :
    limitSubgroup (fun U ↦ P.map (QuotientGroup.mk' U.toSubgroup)) = P := by
  rw [limitSubgroup]
  refine (iInf_congr fun U ↦ ?_).trans (P.eq_iInf_sup_openNormalSubgroup hP).symm
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

/-- A family of subgroups of the quotients of a compact group by its open normal subgroups that
is compatible along the quotient maps is the family of images of the subgroup it cuts out. -/
theorem map_mk'_limitSubgroup [CompactSpace G]
    (hH : ∀ ⦃U V : OpenNormalSubgroup G⦄ (hUV : U ≤ V),
      (H U).map (QuotientGroup.mapOfLE hUV) = H V)
    (U : OpenNormalSubgroup G) :
    (limitSubgroup H).map (QuotientGroup.mk' U.toSubgroup) = H U := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact fun g hg ↦ mem_limitSubgroup_iff.mp hg U
  · intro y hy
    -- Find a preimage of `y` that lies in the inverse image of every `H V`, by compactness.
    let t : OpenNormalSubgroup G → Set G := fun V ↦
      (QuotientGroup.mk' U.toSubgroup) ⁻¹' {y} ∩
        (QuotientGroup.mk' V.toSubgroup) ⁻¹' (H V : Set (G ⧸ V.toSubgroup))
    have ht_nonempty (V : OpenNormalSubgroup G) : (t V).Nonempty := by
      have hyW : y ∈ (H (U ⊓ V)).map (QuotientGroup.mapOfLE inf_le_left) := by
        rwa [hH inf_le_left]
      obtain ⟨z, hz, hzy⟩ := hyW
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (U ⊓ V).toSubgroup z
      refine ⟨g, ?_, ?_⟩
      · simpa using hzy
      · have hzV : (QuotientGroup.mk g : G ⧸ V.toSubgroup) ∈
            (H (U ⊓ V)).map (QuotientGroup.mapOfLE inf_le_right) :=
          ⟨QuotientGroup.mk g, hz, QuotientGroup.mapOfLE_mk _ g⟩
        rwa [hH inf_le_right] at hzV
    have ht_closed (V : OpenNormalSubgroup G) : IsClosed (t V) :=
      (isClosed_singleton.preimage QuotientGroup.continuous_mk).inter
        ((isClosed_discrete _).preimage QuotientGroup.continuous_mk)
    have ht_directed : Directed (· ⊇ ·) t := by
      intro V W
      refine ⟨V ⊓ W, ?_, ?_⟩
      · rintro g ⟨hgy, hg⟩
        refine ⟨hgy, ?_⟩
        have : (QuotientGroup.mk g : G ⧸ V.toSubgroup) ∈
            (H (V ⊓ W)).map (QuotientGroup.mapOfLE inf_le_left) :=
          ⟨QuotientGroup.mk g, hg, QuotientGroup.mapOfLE_mk _ g⟩
        rwa [hH inf_le_left] at this
      · rintro g ⟨hgy, hg⟩
        refine ⟨hgy, ?_⟩
        have : (QuotientGroup.mk g : G ⧸ W.toSubgroup) ∈
            (H (V ⊓ W)).map (QuotientGroup.mapOfLE inf_le_right) :=
          ⟨QuotientGroup.mk g, hg, QuotientGroup.mapOfLE_mk _ g⟩
        rwa [hH inf_le_right] at this
    let _ : Nonempty (OpenNormalSubgroup G) :=
      ⟨{ toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }⟩
    obtain ⟨g, hg⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t ht_directed ht_nonempty
        (fun V ↦ (ht_closed V).isCompact) ht_closed
    exact ⟨g, mem_limitSubgroup_iff.mpr fun V ↦ (Set.mem_iInter.mp hg V).2,
      (Set.mem_iInter.mp hg U).1⟩

end LimitSubgroup

/-! ### Sequential limit descriptions

The limit description of a profinite group runs over all of its open normal subgroups. When a
sequence `N : ℕ → Subgroup G` of closed subgroups of a compact group `G` has trivial intersection,
a coset sequence `x k` has a unique common representative if every representative of `x (k + 1)`
also represents `x k`: the coset fibers are nested. For decreasing `N`, this is the inverse-limit
description. When the `N k` are normal and decreasing, a compatible sequence of
homomorphisms into the quotients `G ⧸ N k` is induced by a unique homomorphism into `G`; and when
they are normal, continuity of a map into `G` can be tested one quotient at a time. When the `N k`
are open and decreasing, they are a neighbourhood basis of `1`. The lower `p`-series of a pro-`p`
group is a decreasing sequence of closed normal subgroups with trivial intersection, and its terms
are open when the group is topologically finitely generated. -/

section Sequential

open Filter Topology

variable {G : Type*} [Group G]

/-- Two elements of a group with the same class modulo every member of a family of subgroups with
trivial intersection are equal. -/
theorem eq_of_forall_mk_eq_of_iInf_eq_bot {ι : Type*} {N : ι → Subgroup G} (hN : ⨅ i, N i = ⊥)
    {x y : G} (h : ∀ i, (x : G ⧸ N i) = (y : G ⧸ N i)) : x = y := by
  refine inv_mul_eq_one.mp ?_
  rw [← Subgroup.mem_bot, ← hN, Subgroup.mem_iInf]
  exact fun i ↦ QuotientGroup.eq.mp (h i)

variable [TopologicalSpace G] [SeparatelyContinuousMul G] {N : ℕ → Subgroup G}

/-- **Sequential coset reconstruction in a compact group.** Suppose the closed subgroups `N k`
of a compact group `G` have trivial intersection, and let `x k : G ⧸ N k`. If every representative
of `x (k + 1)` also represents `x k`, the coset fibers are nested and have a unique common
representative in `G`. For decreasing `N`, this is the inverse-limit description of `G` using
the coset spaces `G ⧸ N k`; normality is not required. -/
theorem existsUnique_forall_mk_eq_of_iInf_eq_bot [CompactSpace G]
    (hclosed : ∀ k, IsClosed (N k : Set G)) (hN : ⨅ k, N k = ⊥) (x : ∀ k, G ⧸ N k)
    (hcompat : ∀ (k : ℕ) (g : G), (g : G ⧸ N (k + 1)) = x (k + 1) → (g : G ⧸ N k) = x k) :
    ∃! g : G, ∀ k, (g : G ⧸ N k) = x k := by
  have hcl (k : ℕ) : IsClosed ((QuotientGroup.mk : G → G ⧸ N k) ⁻¹' {x k}) := by
    have : T1Space (G ⧸ N k) := QuotientGroup.t1Space_iff.mpr (hclosed k)
    exact isClosed_singleton.preimage QuotientGroup.continuous_mk
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k ↦ (QuotientGroup.mk : G → G ⧸ N k) ⁻¹' {x k}) (fun k g hg ↦ hcompat k g hg)
    (fun k ↦ QuotientGroup.mk_surjective (x k)) (hcl 0).isCompact hcl
  exact ⟨g, fun k ↦ Set.mem_iInter.mp hg k, fun g' hg' ↦ eq_of_forall_mk_eq_of_iInf_eq_bot hN
    fun k ↦ (hg' k).trans (Set.mem_iInter.mp hg k).symm⟩

/-- **Sequential limit description of a compact group, for homomorphisms.** A sequence of
homomorphisms `x k : H →* G ⧸ N k` into the quotients of a compact group `G` by a decreasing
sequence of closed normal subgroups with trivial intersection, compatible along the quotient maps,
is induced by a unique homomorphism `H →* G`. -/
theorem existsUnique_monoidHom_mk'_comp_eq_of_iInf_eq_bot [CompactSpace G] [∀ k, (N k).Normal]
    {H : Type*} [MulOneClass H] (hle : ∀ k, N (k + 1) ≤ N k)
    (hclosed : ∀ k, IsClosed (N k : Set G)) (hN : ⨅ k, N k = ⊥) (x : ∀ k, H →* G ⧸ N k)
    (hx : ∀ k, (QuotientGroup.mapOfLE (hle k)).comp (x (k + 1)) = x k) :
    ∃! φ : H →* G, ∀ k, (QuotientGroup.mk' (N k)).comp φ = x k := by
  -- For a fixed `a : H`, the classes `x k a` form a compatible sequence of cosets, so the
  -- sequential limit description realizes them by a unique element `φ a`.
  have hcompat (a : H) (k : ℕ) (g : G) (hg : (g : G ⧸ N (k + 1)) = x (k + 1) a) :
      (g : G ⧸ N k) = x k a := by
    rw [← hx k, MonoidHom.comp_apply, ← hg, QuotientGroup.mapOfLE_mk]
  choose φ hφ using fun a : H ↦
    (existsUnique_forall_mk_eq_of_iInf_eq_bot hclosed hN (fun k ↦ x k a) (hcompat a)).exists
  refine ⟨MonoidHom.mk' φ fun a b ↦ eq_of_forall_mk_eq_of_iInf_eq_bot hN fun k ↦ ?_,
    fun k ↦ MonoidHom.ext (hφ · k), fun ψ hψ ↦ MonoidHom.ext fun a ↦
      eq_of_forall_mk_eq_of_iInf_eq_bot hN fun k ↦ ?_⟩
  · -- Multiplicativity is checked in every quotient, where it is that of `x k`.
    calc (φ (a * b) : G ⧸ N k) = x k (a * b) := hφ (a * b) k
      _ = x k a * x k b := map_mul _ _ _
      _ = ((φ a * φ b : G) : G ⧸ N k) := by rw [QuotientGroup.mk_mul, ← hφ a k, ← hφ b k]
  · exact (DFunLike.congr_fun (hψ k) a).trans (hφ a k).symm

/-- **A decreasing sequence of open subgroups with trivial intersection is a neighbourhood basis
of `1`** in a compact group. -/
theorem hasAntitoneBasis_nhds_one_of_iInf_eq_bot [CompactSpace G] (hanti : Antitone N)
    (hopen : ∀ k, IsOpen (N k : Set G)) (hN : ⨅ k, N k = ⊥) :
    (𝓝 (1 : G)).HasAntitoneBasis fun k ↦ (N k : Set G) := by
  have hanti' : Antitone fun k ↦ (N k : Set G) := fun _ _ h ↦ SetLike.coe_subset_coe.mpr (hanti h)
  refine ⟨hasBasis_iff.mpr fun t ↦ ⟨fun ht ↦ ?_, ?_⟩, hanti'⟩
  · -- The `N k` are closed and decreasing with intersection `{1}`, so by compactness one of them
    -- lies inside any neighbourhood of `1`.
    obtain ⟨k, hk⟩ := exists_subset_nhds_of_compactSpace hanti'.directed_ge
      (fun k ↦ (N k).isClosed_of_isOpen (hopen k))
      (by rwa [← Subgroup.coe_iInf, hN, Subgroup.coe_bot, nhdsSet_singleton])
    exact ⟨k, trivial, hk⟩
  · rintro ⟨k, -, hk⟩
    exact mem_of_superset ((hopen k).mem_nhds (N k).one_mem) hk

omit [SeparatelyContinuousMul G] in
/-- A map into a compact group `G` is continuous exactly when all of its composites with the
quotient maps `G → G ⧸ N i` are, for any family of closed normal subgroups `N i` with trivial
intersection: `G` embeds into the product of the Hausdorff quotients `G ⧸ N i`. -/
theorem continuous_iff_forall_continuous_mk_of_iInf_eq_bot [IsTopologicalGroup G] [CompactSpace G]
    {ι : Type*} {N : ι → Subgroup G} [∀ i, (N i).Normal] (hclosed : ∀ i, IsClosed (N i : Set G))
    (hN : ⨅ i, N i = ⊥) {X : Type*} [TopologicalSpace X] {f : X → G} :
    Continuous f ↔ ∀ i, Continuous fun x ↦ (f x : G ⧸ N i) := by
  refine ⟨fun hf i ↦ QuotientGroup.continuous_mk.comp hf, fun h ↦ ?_⟩
  have := hclosed
  have he : IsInducing fun g : G ↦ fun i ↦ (g : G ⧸ N i) :=
    ((continuous_pi fun i ↦ QuotientGroup.continuous_mk).isClosedEmbedding fun a b hab ↦
      eq_of_forall_mk_eq_of_iInf_eq_bot hN fun i ↦ congr_fun hab i).isInducing
  exact he.continuous_iff.mpr (continuous_pi h)

end Sequential

end TauCeti
