/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Topology.Algebra.Group.Metrizable
import Mathlib.Topology.UniformSpace.Separation

/-!
# The Kakutani–Kodaira theorem for σ-compact locally compact groups

Every σ-compact weakly locally compact topological group `G` admits arbitrarily small closed compact
normal subgroups `K` whose quotient `G ⧸ K` is metrizable and second countable. No separation
axiom on `G` itself is needed: because `K` is constructed as a countable intersection of closed
compact symmetric identity neighbourhoods, `K` is closed as well as compact, so `G ⧸ K` is
automatically Hausdorff (`T₁`, hence `T₃`) and therefore metrizable by the Birkhoff–Kakutani
theorem (`IsTopologicalGroup.metrizableSpace`).

From this basic existence result we deduce two consequences:
* any countable family of closed normal subgroups of `G` whose quotients have countably generated
  identity-neighbourhood filters can be simultaneously refined by a single closed compact normal
  subgroup `K` with metrizable second-countable quotient;
* any countable family of continuous maps from `G` into metrizable spaces factors simultaneously
  through `G ⧸ K` for a single closed compact normal subgroup `K` with metrizable second-countable
  quotient.

## Main results

* `IsCompact.exists_nhds_one_conj_subset` / `IsCompact.exists_nhds_zero_conj_subset`:
  equicontinuity of conjugation over a compact set at the identity.
* `IsCompact.exists_nhds_one_mul_mem_uniformity` / `IsCompact.exists_nhds_zero_add_mem_uniformity`:
  uniform right equicontinuity of a continuous map into a uniform space over a compact set.
* `QuotientGroup.instSigmaCompactSpace` / `QuotientAddGroup.instSigmaCompactSpace`:
  quotients of σ-compact topological groups are σ-compact.
* `TauCeti.exists_compact_normal_subgroup_quotient_metrizable` /
  `TauCeti.exists_compact_normal_addSubgroup_quotient_metrizable`: the Kakutani–Kodaira theorem.
* `TauCeti.exists_compact_normal_subgroup_le` /
  `TauCeti.exists_compact_normal_addSubgroup_le`: simultaneous refinement of countably many closed
  normal subgroups with first-countable quotients.
* `TauCeti.exists_compact_normal_subgroup_factor_continuous` /
  `TauCeti.exists_compact_normal_addSubgroup_factor_continuous`: simultaneous factorization of
  countably many continuous maps into metrizable spaces.

## References

* S. Kakutani and K. Kodaira, *Über das Haarsche Maß in der lokal bikompakten Gruppe*,
  Proc. Imp. Acad. Tokyo **20** (1944), 444–450.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979),
  Theorem 8.7.
* D. H. Fremlin, *Measure Theory*, Vol. 4, Torres Fremlin (2003), §443L.
-/

public section

open Filter Set TopologicalSpace
open scoped Pointwise Topology Uniformity

/-- Over a compact subset `C` of a topological group, conjugation sends a sufficiently small
identity neighbourhood into any prescribed identity neighbourhood. -/
@[to_additive /-- Over a compact subset `C` of a topological additive group, conjugation sends a
sufficiently small neighbourhood of zero into any prescribed neighbourhood of zero. -/]
theorem IsCompact.exists_nhds_one_conj_subset {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {C U : Set G} (hC : IsCompact C) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ C, ∀ y ∈ V, x * y * x⁻¹ ∈ U := by
  let φ : G × G → G := fun p ↦ p.1 * p.2 * p.1⁻¹
  have hφ : Continuous φ :=
    (continuous_fst.mul continuous_snd).mul continuous_fst.inv
  have hsub : C ×ˢ ({1} : Set G) ⊆ φ ⁻¹' interior U := by
    rintro ⟨x, y⟩ ⟨_, hy⟩
    simp only [mem_singleton_iff] at hy
    simpa [φ, hy] using mem_interior_iff_mem_nhds.mpr hU
  obtain ⟨A, B, _, hBo, hCA, h1B, hAB⟩ :=
    generalized_tube_lemma hC isCompact_singleton (isOpen_interior.preimage hφ) hsub
  refine ⟨B, hBo.mem_nhds (singleton_subset_iff.mp h1B), fun x hx y hy ↦ ?_⟩
  exact interior_subset (mem_preimage.mp (hAB (mk_mem_prod (hCA hx) hy)))

/-- A continuous map `f` from a topological monoid into a uniform space is uniformly right
equicontinuous over any compact set `C`: for every entourage `s ∈ 𝓤 Y` there is an identity
neighbourhood `V` such that `(f (x * u), f x) ∈ s` for all `x ∈ C` and `u ∈ V`. -/
@[to_additive /-- A continuous map `f` from a topological additive monoid into a uniform space is
uniformly right equicontinuous over any compact set `C`: for every entourage `s ∈ 𝓤 Y` there is a
zero neighbourhood `V` such that `(f (x + u), f x) ∈ s` for all `x ∈ C` and `u ∈ V`. -/]
theorem IsCompact.exists_nhds_one_mul_mem_uniformity {G Y : Type*} [Monoid G] [TopologicalSpace G]
    [ContinuousMul G] [UniformSpace Y] {C : Set G} (hC : IsCompact C) {f : G → Y}
    (hf : Continuous f) {s : Set (Y × Y)} (hs : s ∈ 𝓤 Y) :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ C, ∀ u ∈ V, (f (x * u), f x) ∈ s := by
  obtain ⟨t, ⟨ht_mem, ht_open⟩, hts⟩ := uniformity_hasBasis_open.mem_iff.mp hs
  let ψ : G × G → Y × Y := fun p ↦ (f (p.1 * p.2), f p.1)
  have hψ : Continuous ψ := (hf.comp continuous_mul).prodMk (hf.comp continuous_fst)
  have hsub : C ×ˢ ({1} : Set G) ⊆ ψ ⁻¹' t := by
    rintro ⟨x, y⟩ ⟨_, hy⟩
    simp only [mem_singleton_iff] at hy
    simpa [ψ, hy] using refl_mem_uniformity ht_mem
  obtain ⟨A, B, _, hBo, hCA, h1B, hAB⟩ :=
    generalized_tube_lemma hC isCompact_singleton (ht_open.preimage hψ) hsub
  refine ⟨B, hBo.mem_nhds (singleton_subset_iff.mp h1B), fun x hx u hu ↦ ?_⟩
  exact hts (mem_preimage.mp (hAB (mk_mem_prod (hCA hx) hu)))

/-- Any quotient of a σ-compact group by a subgroup is σ-compact. -/
@[to_additive /-- Any quotient of a σ-compact additive group by an additive subgroup is
σ-compact. -/]
instance QuotientGroup.instSigmaCompactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [SigmaCompactSpace G] (N : Subgroup G) : SigmaCompactSpace (G ⧸ N) := by
  rw [← isSigmaCompact_univ_iff, ← (QuotientGroup.mk_surjective (s := N)).range_eq]
  exact isSigmaCompact_range QuotientGroup.continuous_mk

namespace TauCeti

section KakutaniKodaira

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G]

/-- Every identity neighbourhood in a weakly locally compact topological group contains a closed,
compact, symmetric identity neighbourhood. -/
@[to_additive]
private theorem exists_isClosed_isCompact_symm_mem_nhds_one {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), IsClosed V ∧ IsCompact V ∧ V⁻¹ = V ∧ V ⊆ U := by
  obtain ⟨K₀, hK₀_comp, hK₀_mem⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨F, ⟨hF_mem, hF_closed⟩, hF_sub⟩ :=
    (closed_nhds_basis (1 : G)).mem_iff.mp (inter_mem hU hK₀_mem)
  have hF_comp : IsCompact F :=
    hK₀_comp.of_isClosed_subset hF_closed (hF_sub.trans inter_subset_right)
  refine ⟨F ∩ F⁻¹, inter_mem hF_mem (inv_mem_nhds_one G hF_mem), hF_closed.inter hF_closed.inv,
    hF_comp.inter_right hF_closed.inv, ?_, inter_subset_left.trans (hF_sub.trans inter_subset_left)⟩
  simp [inter_comm]

variable [SigmaCompactSpace G]

/-- One inductive step of the Kakutani–Kodaira construction: inside `U` and `interior V`, find a
closed compact symmetric identity neighbourhood `W` with `W * W ⊆ interior V` and conjugate-stable
into `interior V` under `⋃ k ≤ n, compactCovering G k`. -/
@[to_additive]
private theorem exists_kakutaniKodaira_step_one {V U : Set G} (hV : V ∈ 𝓝 (1 : G))
    (hU : U ∈ 𝓝 (1 : G)) (n : ℕ) :
    ∃ W ∈ 𝓝 (1 : G), IsClosed W ∧ IsCompact W ∧ W⁻¹ = W ∧ W ⊆ U ∧ W * W ⊆ interior V ∧
      ∀ k ≤ n, ∀ x ∈ compactCovering G k, ∀ y ∈ W, x * y * x⁻¹ ∈ interior V := by
  have hintV : interior V ∈ 𝓝 (1 : G) := interior_mem_nhds.mpr hV
  obtain ⟨W₁, hW₁_mem, hW₁_mul⟩ := exists_nhds_one_split hintV
  have hC : IsCompact (⋃ k ≤ n, compactCovering G k) :=
    (finite_le_nat n).isCompact_biUnion fun k _ ↦ isCompact_compactCovering G k
  obtain ⟨W₂, hW₂_mem, hW₂_conj⟩ := hC.exists_nhds_one_conj_subset hintV
  obtain ⟨W, hW_mem, hW_cl, hW_cp, hW_symm, hW_sub⟩ :=
    exists_isClosed_isCompact_symm_mem_nhds_one (inter_mem hU (inter_mem hW₁_mem hW₂_mem))
  have hWU : W ⊆ U := hW_sub.trans inter_subset_left
  have hWW₁ : W ⊆ W₁ := hW_sub.trans (inter_subset_right.trans inter_subset_left)
  have hWW₂ : W ⊆ W₂ := hW_sub.trans (inter_subset_right.trans inter_subset_right)
  refine ⟨W, hW_mem, hW_cl, hW_cp, hW_symm, hWU, ?_, fun k hk x hx y hy ↦ ?_⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hW₁_mul a (hWW₁ ha) b (hWW₁ hb)
  · exact hW₂_conj x (mem_iUnion₂.mpr ⟨k, hk, hx⟩) y (hWW₂ hy)

/-- Given `U : ℕ → Set G` in `𝓝 1`, construct the Kakutani–Kodaira sequence `V : ℕ → Set G` and the
closed compact normal subgroup `K = ⋂ n, V n` together with its antitone basis at `1 : G ⧸ K`. -/
@[to_additive]
private theorem exists_compact_normal_subgroup_nat (U : ℕ → Set G) (hU : ∀ n, U n ∈ 𝓝 (1 : G)) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      (K : Set G) ⊆ ⋂ n, U n ∧ (𝓝 (1 : G ⧸ K)).IsCountablyGenerated := by
  -- Build `V : ℕ → Set G` recursively using `exists_isClosed_isCompact_symm_mem_nhds_one` at `0`
  -- and `exists_kakutaniKodaira_step_one` at `n + 1`.
  let V : ℕ → {S : Set G // S ∈ 𝓝 (1 : G)} := fun n ↦
    Nat.recOn n
      ⟨(exists_isClosed_isCompact_symm_mem_nhds_one (hU 0)).choose,
        (exists_isClosed_isCompact_symm_mem_nhds_one (hU 0)).choose_spec.1⟩
      fun m ih ↦
        ⟨(exists_kakutaniKodaira_step_one ih.2 (hU (m + 1)) m).choose,
          (exists_kakutaniKodaira_step_one ih.2 (hU (m + 1)) m).choose_spec.1⟩
  have hV0 := (exists_isClosed_isCompact_symm_mem_nhds_one (hU 0)).choose_spec.2
  have hVstep (n : ℕ) := (exists_kakutaniKodaira_step_one (V n).2 (hU (n + 1)) n).choose_spec.2
  have hV_cl : ∀ n, IsClosed (V n).1 := Nat.rec hV0.1 fun n _ ↦ (hVstep n).1
  have hV_symm : ∀ n, (V n).1⁻¹ = (V n).1 := Nat.rec hV0.2.2.1 fun n _ ↦ (hVstep n).2.2.1
  have hV_sub : ∀ n, (V n).1 ⊆ U n := Nat.rec hV0.2.2.2 fun n _ ↦ (hVstep n).2.2.2.1
  have hV_mul : ∀ n, (V (n + 1)).1 * (V (n + 1)).1 ⊆ interior (V n).1 :=
    fun n ↦ (hVstep n).2.2.2.2.1
  have hV_conj : ∀ n, ∀ k ≤ n, ∀ x ∈ compactCovering G k, ∀ y ∈ (V (n + 1)).1,
      x * y * x⁻¹ ∈ interior (V n).1 := fun n ↦ (hVstep n).2.2.2.2.2
  have hV_anti : Antitone (fun n ↦ (V n).1) := antitone_nat_of_succ_le fun n x hx ↦
    interior_subset <| hV_mul n ⟨x, hx, 1, mem_of_mem_nhds (V (n + 1)).2, mul_one x⟩
  let K : Subgroup G :=
    { carrier := ⋂ n, (V n).1
      one_mem' := mem_iInter.mpr fun n ↦ mem_of_mem_nhds (V n).2
      mul_mem' {a b} ha hb := mem_iInter.mpr fun n ↦
        interior_subset <| hV_mul n ⟨a, mem_iInter.mp ha (n + 1), b, mem_iInter.mp hb (n + 1), rfl⟩
      inv_mem' {a} ha := mem_iInter.mpr fun n ↦ by
        rw [← hV_symm n]
        exact inv_mem_inv.mpr (mem_iInter.mp ha n) }
  have hK_norm : K.Normal := ⟨fun y hy g ↦ mem_iInter.mpr fun n ↦ by
    obtain ⟨k, hk⟩ := exists_mem_compactCovering g
    exact hV_anti (le_max_left n k) <| interior_subset <|
      hV_conj (max n k) k (le_max_right n k) g hk y (mem_iInter.mp hy (max n k + 1))⟩
  have hK_cl : IsClosed (K : Set G) := isClosed_iInter hV_cl
  have hK_cp : IsCompact (K : Set G) :=
    hV0.2.1.of_isClosed_subset hK_cl (iInter_subset (fun n ↦ (V n).1) 0)
  -- The images of `interior (V n)` form a countable basis of `𝓝 (1 : G ⧸ K)`.
  have hK_cg : (𝓝 (1 : G ⧸ K)).IsCountablyGenerated := by
    let π : G → G ⧸ K := QuotientGroup.mk
    have hbasis : (𝓝 (1 : G ⧸ K)).HasBasis (fun _ : ℕ ↦ True)
        (fun n ↦ π '' interior (V n).1) := by
      refine ⟨fun O ↦ ⟨fun hO ↦ ?_, fun ⟨n, _, hn⟩ ↦ ?_⟩⟩
      · have hO' : IsOpen (π ⁻¹' interior O) :=
          isOpen_interior.preimage QuotientGroup.continuous_mk
        have hdisj : Disjoint ((V 0).1 ∩ (π ⁻¹' interior O)ᶜ) (⋂ n, (V n).1) := by
          refine disjoint_left.mpr fun x ⟨_, hxO⟩ hxK ↦ hxO ?_
          have hπx : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hxK
          simpa [π, hπx] using mem_interior_iff_mem_nhds.mpr hO
        obtain ⟨n, hn⟩ := (hV0.2.1.inter_right hO'.isClosed_compl).elim_directed_family_closed
          (fun n ↦ (V n).1) hV_cl hdisj hV_anti.directed_ge
        refine ⟨n, trivial, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        have hxV : x ∈ (V n).1 := interior_subset hx
        have hxO : x ∈ π ⁻¹' interior O := by
          by_contra hxno
          exact hn.le_bot ⟨⟨hV_anti (Nat.zero_le n) hxV, hxno⟩, hxV⟩
        exact interior_subset hxO
      · refine mem_of_superset ?_ hn
        exact (QuotientGroup.isOpenMap_coe (N := K) _ isOpen_interior).mem_nhds
          ⟨(1 : G), mem_interior_iff_mem_nhds.mpr (V n).2, rfl⟩
    exact hbasis.isCountablyGenerated
  exact ⟨K, hK_norm, hK_cp, hK_cl, iInter_mono hV_sub, hK_cg⟩

/-- **The Kakutani–Kodaira theorem.** In a σ-compact weakly locally compact topological group `G`,
for any countable family `U` of neighbourhoods of `1`, there exists a closed compact normal
subgroup `K` contained in `⋂ i, U i` whose quotient `G ⧸ K` is metrizable and second countable. -/
@[to_additive /-- **The Kakutani–Kodaira theorem** (additive form). In a σ-compact weakly locally
compact topological additive group `G`, for any countable family `U` of neighbourhoods of `0`,
there exists a closed compact normal additive subgroup `K` contained in `⋂ i, U i` whose quotient
`G ⧸ K` is metrizable and second countable. -/]
theorem exists_compact_normal_subgroup_quotient_metrizable {ι : Type*} [Countable ι]
    (U : ι → Set G) (hU : ∀ i, U i ∈ 𝓝 (1 : G)) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      (K : Set G) ⊆ ⋂ i, U i ∧ (𝓝 (1 : G ⧸ K)).IsCountablyGenerated ∧
      MetrizableSpace (G ⧸ K) ∧ SecondCountableTopology (G ⧸ K) := by
  -- Reduce an arbitrary countable index type `ι` to `ℕ`.
  have hseq : ∃ U' : ℕ → Set G, (∀ n, U' n ∈ 𝓝 (1 : G)) ∧ ⋂ n, U' n ⊆ ⋂ i, U i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨fun _ ↦ univ, fun _ ↦ univ_mem, by simp⟩
    · obtain ⟨e, he⟩ := exists_surjective_nat ι
      refine ⟨fun n ↦ U (e n), fun n ↦ hU (e n), fun x hx ↦ mem_iInter.mpr fun i ↦ ?_⟩
      obtain ⟨n, rfl⟩ := he i
      exact mem_iInter.mp hx n
  obtain ⟨U', hU', hU'sub⟩ := hseq
  obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_sub, hK_cg⟩ := exists_compact_normal_subgroup_nat U' hU'
  have : IsClosed (K : Set G) := hK_cl
  have : MetrizableSpace (G ⧸ K) := IsTopologicalGroup.metrizableSpace (G ⧸ K)
  have : SecondCountableTopology (G ⧸ K) := IsTopologicalGroup.secondCountableTopology (G ⧸ K)
  exact ⟨K, hK_norm, hK_cp, hK_cl, hK_sub.trans hU'sub, hK_cg, inferInstance, inferInstance⟩

/-- Any countable family of closed normal subgroups of `G` whose quotients have countably generated
identity-neighbourhood filters can be simultaneously refined by a single closed compact normal
subgroup `K` whose quotient `G ⧸ K` is metrizable and second countable. -/
@[to_additive /-- Any countable family of closed normal additive subgroups of `G` whose quotients
have countably generated zero-neighbourhood filters can be simultaneously refined by a single
closed compact normal additive subgroup `K` whose quotient `G ⧸ K` is metrizable and second
countable. -/]
theorem exists_compact_normal_subgroup_le {ι : Type*} [Countable ι] (L : ι → Subgroup G)
    (hL_norm : ∀ i, (L i).Normal) (hL_cl : ∀ i, IsClosed (L i : Set G))
    (hL_cg : ∀ i, (𝓝 (1 : G ⧸ L i)).IsCountablyGenerated) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      (∀ i, K ≤ L i) ∧ (𝓝 (1 : G ⧸ K)).IsCountablyGenerated ∧
      MetrizableSpace (G ⧸ K) ∧ SecondCountableTopology (G ⧸ K) := by
  have hex (i : ι) : ∃ B : ℕ → Set (G ⧸ L i), (𝓝 (1 : G ⧸ L i)).HasAntitoneBasis B := by
    have := hL_cg i
    exact (𝓝 (1 : G ⧸ L i)).exists_antitone_basis
  choose B hB using hex
  let U : ι × ℕ → Set G := fun p ↦ (QuotientGroup.mk : G → G ⧸ L p.1) ⁻¹' B p.1 p.2
  have hU (p : ι × ℕ) : U p ∈ 𝓝 (1 : G) :=
    QuotientGroup.continuous_mk.continuousAt.preimage_mem_nhds ((hB p.1).mem p.2)
  obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_sub, hK_cg, hK_met, hK_sc⟩ :=
    exists_compact_normal_subgroup_quotient_metrizable U hU
  refine ⟨K, hK_norm, hK_cp, hK_cl, fun i x hx ↦ ?_, hK_cg, hK_met, hK_sc⟩
  have := hL_norm i
  have := hL_cl i
  -- In the `T₁` quotient `G ⧸ L i`, `{x}ᶜ` is an open neighbourhood of `1` whenever `x ≠ 1`.
  rw [← QuotientGroup.eq_one_iff]
  by_contra hne
  have hnhds : ({(QuotientGroup.mk x : G ⧸ L i)} : Set (G ⧸ L i))ᶜ ∈ 𝓝 (1 : G ⧸ L i) :=
    isClosed_singleton.isOpen_compl.mem_nhds (Ne.symm hne)
  obtain ⟨m, _, hm⟩ := (hB i).toHasBasis.mem_iff.mp hnhds
  exact hm (mem_iInter.mp (hK_sub hx) (i, m)) rfl

/-- Any countable family of continuous maps from `G` into metrizable spaces factors simultaneously
through `G ⧸ K` for a single closed compact normal subgroup `K` whose quotient `G ⧸ K` is
metrizable and second countable. -/
@[to_additive /-- Any countable family of continuous maps from `G` into metrizable spaces factors
simultaneously through `G ⧸ K` for a single closed compact normal additive subgroup `K` whose
quotient `G ⧸ K` is metrizable and second countable. -/]
theorem exists_compact_normal_subgroup_factor_continuous {ι : Type*} [Countable ι]
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, MetrizableSpace (Y i)]
    (f : ∀ i, G → Y i) (hf : ∀ i, Continuous (f i)) :
    ∃ (K : Subgroup G) (_ : K.Normal), IsCompact (K : Set G) ∧ IsClosed (K : Set G) ∧
      (𝓝 (1 : G ⧸ K)).IsCountablyGenerated ∧ MetrizableSpace (G ⧸ K) ∧
      SecondCountableTopology (G ⧸ K) ∧
      ∀ i, ∃ g : G ⧸ K → Y i, Continuous g ∧ g ∘ QuotientGroup.mk = f i := by
  let u : ∀ i, UniformSpace (Y i) := fun i ↦ pseudoMetrizableSpaceUniformity (Y i)
  have hex (i : ι) : ∃ E : ℕ → Set (Y i × Y i), 𝓤[u i].HasAntitoneBasis E := by
    let _ : UniformSpace (Y i) := u i
    have : (𝓤 (Y i)).IsCountablyGenerated :=
      pseudoMetrizableSpaceUniformity_countably_generated (Y i)
    exact (𝓤 (Y i)).exists_antitone_basis
  choose E hE using hex
  have hW (p : ι × ℕ × ℕ) : ∃ W ∈ 𝓝 (1 : G), ∀ x ∈ compactCovering G p.2.1, ∀ z ∈ W,
      (f p.1 (x * z), f p.1 x) ∈ E p.1 p.2.2 := by
    let _ : UniformSpace (Y p.1) := u p.1
    exact (isCompact_compactCovering G p.2.1).exists_nhds_one_mul_mem_uniformity (hf p.1)
      ((hE p.1).mem p.2.2)
  choose W hW_mem hW_ent using hW
  obtain ⟨K, hK_norm, hK_cp, hK_cl, hK_sub, hK_cg, hK_met, hK_sc⟩ :=
    exists_compact_normal_subgroup_quotient_metrizable W hW_mem
  refine ⟨K, hK_norm, hK_cp, hK_cl, hK_cg, hK_met, hK_sc, fun i ↦ ?_⟩
  -- For `z ∈ K` and any `x : G`, `(f i (x * z), f i x)` lies in every basis entourage, hence `=`.
  have hconst (x : G) {z : G} (hz : z ∈ K) : f i (x * z) = f i x := by
    let _ : UniformSpace (Y i) := u i
    obtain ⟨k, hk⟩ := exists_mem_compactCovering x
    refine (inseparable_iff_ker_uniformity.mpr ?_).eq
    rw [Filter.mem_ker]
    intro s hs
    obtain ⟨m, _, hm⟩ := (hE i).toHasBasis.mem_iff.mp hs
    exact hm (hW_ent (i, k, m) x hk z (mem_iInter.mp (hK_sub hz) (i, k, m)))
  let g : G ⧸ K → Y i := fun q ↦ Quotient.liftOn' q (f i) fun a b hab ↦ by
    have hmem : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
    rw [← hconst a hmem, mul_inv_cancel_left]
  have hgf : g ∘ QuotientGroup.mk = f i := rfl
  exact ⟨g, (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr (hf i), hgf⟩

end KakutaniKodaira

end TauCeti

end
