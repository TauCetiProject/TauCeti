/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.Hopfian
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries
public import TauCeti.Topology.Compactness.InverseSystem

/-!
# Levelwise comparison along the lower `p`-series

A `PLowerCentralSeriesComparison p G H S` assigns to each datum in `S k` a continuous
surjection `G ⧸ λ_k → H ⧸ λ_k`. Its bonding maps commute with the quotient projections; when the
data are themselves continuous homomorphisms of the finite levels, the descent
`ContinuousMonoidHom.pLowerCentralSeriesDesc` of
`TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries` supplies them.
When every `S k` is finite and nonempty, there is a compatible sequence of data. If `G` is
compact and `H` is a pro-`p` group, the corresponding quotient maps come from a continuous
surjection `G → H`.

Surjectivity of the bonding maps is unnecessary: a tower of nonempty finite sets already
has a compatible sequence. Surjectivity of the realization maps is essential.

## Main results

* `PLowerCentralSeriesComparison.exists_continuous_surjective`: a compatible sequence of
  finite comparison data is realized at every level by a continuous surjection.
* `PLowerCentralSeriesComparison.exists_continuousMulEquiv`: comparison data in both
  directions give a topological isomorphism realizing the forward data.
* `PLowerCentralSeriesComparison.exists_continuousMulEquiv_preserving`: self-comparison
  data preserving marked elements and all finite character quotients give an automorphism
  preserving the marked elements and the character.
* `TauCeti.IsProP.exists_continuousMulEquiv_apply_eq_of_forall_exists_surjective`: in a
  topologically finitely generated pro-`p` group, if for every `k` a continuous surjective
  endomorphism carries `r` to `w` modulo `λ_k` and moves each marked element `a i` by an element
  of a closed subgroup `C i`, then a continuous automorphism carries `r` to `w` and moves each
  `a i` by an element of `C i`. The comparison data are the surjective endomorphisms of the
  finite quotients carrying the class of `r` to the class of `w` and moving the class of each
  `a i` inside the image of `C i`.

The last two results apply to basis changes of a finite-rank free pro-`p` group with a marked
relator. Constructing the finite nonempty sets of admissible basis changes, or the finite
approximations, is a separate hypothesis; the theorems do not construct the corrections used in a
normal-form argument.
-/

public section

namespace TauCeti

variable (p : ℕ) (G H : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (S : ℕ → Type*)

/-- Surjective maps between lower `p`-series quotients, indexed by a tower of comparison data.
Applications put their finite-level constraints in `S`; finiteness and nonemptiness are required
only by the realization theorems. -/
structure PLowerCentralSeriesComparison where
  /-- The map realized by one comparison datum. -/
  map : ∀ k, S k → (G ⧸ pLowerCentralSeries p G k) →ₜ*
    (H ⧸ pLowerCentralSeries p H k)
  /-- Every realization covers the target quotient. -/
  map_surjective : ∀ k s, Function.Surjective (map k s)
  /-- Forgetting the last level of comparison data. -/
  bond : ∀ k, S (k + 1) → S k
  /-- Realization commutes with forgetting a level. -/
  commutes : ∀ k s x,
    QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k) (map (k + 1) s x) =
      map k (bond k s) (QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k) x)

namespace PLowerCentralSeriesComparison

variable {p G H S} [CompactSpace G] [CompactSpace H] [TotallyDisconnectedSpace H]
  [∀ k, Finite (S k)] [∀ k, Nonempty (S k)]

/-- **Levelwise comparison.** Finite nonempty comparison data give a compatible sequence and
a continuous surjection inducing its realization on every quotient. The source need only be
compact and the target any pro-`p` group; neither is assumed finitely generated. -/
theorem exists_continuous_surjective (C : PLowerCentralSeriesComparison p G H S)
    (hH : IsProP p H) (hp : p.Prime) :
    ∃ (s : ∀ k, S k) (φ : G →ₜ* H),
      (∀ k, C.bond k (s (k + 1)) = s k) ∧ Function.Surjective φ ∧
        ∀ k g, (φ g : H ⧸ pLowerCentralSeries p H k) =
          C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k) := by
  obtain ⟨s, hs⟩ := exists_forall_map_succ_eq_of_finite C.bond
  let x (k : ℕ) : G →* H ⧸ pLowerCentralSeries p H k :=
    (C.map k (s k)).toMonoidHom.comp (QuotientGroup.mk' (pLowerCentralSeries p G k))
  have hx : ∀ k, (QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k)).comp
      (x (k + 1)) = x k := by
    intro k
    ext g
    simpa only [x, MonoidHom.comp_apply, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
      QuotientGroup.mk'_apply,
      QuotientGroup.mapOfLE_mk, hs k] using
      C.commutes k (s (k + 1)) (g : G ⧸ pLowerCentralSeries p G (k + 1))
  obtain ⟨φ, hφ, _⟩ := hH.existsUnique_monoidHom_mk'_comp_eq_pLowerCentralSeries hp x hx
  have hφk : ∀ k g, (φ g : H ⧸ pLowerCentralSeries p H k) =
      C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k) :=
    fun k g ↦ DFunLike.congr_fun (hφ k) g
  have hcont : Continuous φ :=
    (hH.continuous_iff_forall_continuous_mk_pLowerCentralSeries hp).mpr fun k ↦
      ((C.map k (s k)).continuous.comp QuotientGroup.continuous_mk).congr
        fun g ↦ (hφk k g).symm
  have hsurj : Function.Surjective φ := by
    apply surjective_of_forall_surjective_mk'_comp hcont
    intro U
    obtain ⟨k, hk⟩ := hH.exists_pLowerCentralSeries_le hp U
    have hcomp : (QuotientGroup.mk' U.toSubgroup).comp φ =
        (QuotientGroup.mapOfLE hk).comp (x k) := by
      ext g
      simp only [x, MonoidHom.comp_apply, ContinuousMonoidHom.coe_toMonoidHom,
        MonoidHom.coe_ofClass, QuotientGroup.mk'_apply]
      rw [← hφk k g, QuotientGroup.mapOfLE_mk]
    rw [hcomp]
    exact (QuotientGroup.mapOfLE_surjective hk).comp
      ((C.map_surjective k (s k)).comp (QuotientGroup.mk'_surjective _))
  exact ⟨s, ⟨φ, hcont⟩, hs, hsurj, hφk⟩

variable [TotallyDisconnectedSpace G]

/-- **Two-sided comparison.** For a topologically finitely generated pro-`p` source and a pro-`p`
target, comparison data in both directions give an isomorphism realizing a compatible sequence of
the forward data. -/
theorem exists_continuousMulEquiv {T : ℕ → Type*} [∀ k, Finite (T k)] [∀ k, Nonempty (T k)]
    (C : PLowerCentralSeriesComparison p G H S) (D : PLowerCentralSeriesComparison p H G T)
    (hG : IsProP p G) (hGfg : IsTopologicallyFinitelyGenerated G) (hH : IsProP p H)
    (hp : p.Prime) :
    ∃ (s : ∀ k, S k) (e : G ≃ₜ* H),
      (∀ k, C.bond k (s (k + 1)) = s k) ∧
        ∀ k g, (e g : H ⧸ pLowerCentralSeries p H k) =
          C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k) := by
  obtain ⟨s, φ, hs, hφs, hφ⟩ := C.exists_continuous_surjective hH hp
  obtain ⟨_, ψ, _, hψs, _⟩ := D.exists_continuous_surjective hG hp
  have hb := hGfg.bijective_of_surjective_of_surjective φ.continuous hφs ψ.continuous hψs
  let e : G ≃ₜ* H := ContinuousMulEquiv.mk (MulEquiv.ofBijective φ.toMonoidHom hb)
    φ.continuous (φ.continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective φ.toMonoidHom hb).toEquiv))
  exact ⟨s, e, hs, hφ⟩

omit [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- **Comparison preserving relators and characters.** Suppose every level map takes the marked
elements `a` to `b`, and each finite quotient of the character is respected at some level.
Then a self-comparison is realized by an automorphism taking `a` to `b` and intertwining the
characters. The character target may be any profinite group.

The character condition is entirely finite-level: equality of the level-`k` image of `x`
with the class of `y` must imply equality of the prescribed character values modulo `U`.
The level `k` may depend on `U`. -/
theorem exists_continuousMulEquiv_preserving {ι K : Type*}
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [TotallyDisconnectedSpace K] (C : PLowerCentralSeriesComparison p G G S)
    (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime)
    (a b : ι → G) (χ ψ : G →ₜ* K)
    (hmark : ∀ k s i, C.map k s (a i : G ⧸ pLowerCentralSeries p G k) =
      (b i : G ⧸ pLowerCentralSeries p G k))
    (hchar : ∀ U : OpenNormalSubgroup K, ∃ k, ∀ (s : S k) (x y : G),
      C.map k s (x : G ⧸ pLowerCentralSeries p G k) =
          (y : G ⧸ pLowerCentralSeries p G k) →
        (ψ y : K ⧸ U.toSubgroup) = (χ x : K ⧸ U.toSubgroup)) :
    ∃ (s : ∀ k, S k) (e : G ≃ₜ* G),
      (∀ k, C.bond k (s (k + 1)) = s k) ∧
        (∀ k g, (e g : G ⧸ pLowerCentralSeries p G k) =
          C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k)) ∧
        (∀ i, e (a i) = b i) ∧ ψ.comp (e : G →ₜ* G) = χ := by
  obtain ⟨s, φ, hs, hφs, hφ⟩ := C.exists_continuous_surjective hG hp
  let e := hfg.continuousMulEquivOfSurjective φ.continuous hφs
  have he (g : G) : e g = φ g :=
    hfg.continuousMulEquivOfSurjective_apply φ.continuous hφs g
  have hlevel : ∀ k g, (e g : G ⧸ pLowerCentralSeries p G k) =
      C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k) := by
    intro k g
    rw [he]
    exact hφ k g
  refine ⟨s, e, hs, hlevel, ?_, ?_⟩
  · intro i
    exact eq_of_forall_mk_eq_of_iInf_eq_bot (hG.iInf_pLowerCentralSeries_eq_bot hp)
      fun k ↦ (hlevel k (a i)).trans (hmark k (s k) i)
  · ext g
    apply eq_of_forall_mk_eq_of_iInf_eq_bot (Subgroup.iInf_openNormalSubgroup_eq_bot (G := K))
    intro U
    obtain ⟨k, hk⟩ := hchar U
    exact hk (s k) g (e g) (hlevel k g).symm

end PLowerCentralSeriesComparison

section Limit

variable {p G} [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **From finite approximations to an automorphism.** Let `G` be a topologically finitely
generated pro-`p` group, let `a : ι → G` be marked elements and let `C : ι → Subgroup G` be closed
subgroups. If for every `k` some continuous surjective endomorphism `φ_k` of `G` moves each `a i`
inside `C i`, that is `(a i)⁻¹ * φ_k (a i) ∈ C i`, and has `φ_k r ≡ w mod λ_k(G)`, then a
continuous automorphism `e` of `G` carries `r` to `w` and moves each `a i` inside `C i`.

The constraints pass to the limit because membership in a closed subgroup is detected on the
quotients `G ⧸ λ_k` (`TauCeti.IsProP.mem_of_forall_mk_mem_map_pLowerCentralSeries`). -/
theorem IsProP.exists_continuousMulEquiv_apply_eq_of_forall_exists_surjective {ι : Type*}
    (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (r w : G)
    (a : ι → G) (C : ι → Subgroup G) (hC : ∀ i, IsClosed (C i : Set G))
    (h : ∀ k, ∃ φ : G →ₜ* G, Function.Surjective φ ∧ (∀ i, (a i)⁻¹ * φ (a i) ∈ C i) ∧
      (φ r)⁻¹ * w ∈ pLowerCentralSeries p G k) :
    ∃ e : G ≃ₜ* G, (∀ i, (a i)⁻¹ * e (a i) ∈ C i) ∧ e r = w := by
  have : ∀ k, DiscreteTopology (G ⧸ pLowerCentralSeries p G k) :=
    fun k ↦ QuotientGroup.discreteTopology (hfg.isOpen_pLowerCentralSeries hp k)
  -- The level-`k` comparison data: surjective endomorphisms of the finite group `G ⧸ λ_k`
  -- carrying `r` to `w` and moving the class of each `a i` inside the image of `C i`; descent
  -- along the series bonds the levels.
  let S (k : ℕ) : Type _ :=
    {ψ : G ⧸ pLowerCentralSeries p G k →ₜ* G ⧸ pLowerCentralSeries p G k //
      Function.Surjective ψ ∧
        (∀ i, (a i : G ⧸ pLowerCentralSeries p G k)⁻¹ * ψ (a i) ∈
          (C i).map (QuotientGroup.mk' (pLowerCentralSeries p G k))) ∧
        ψ r = w}
  have : ∀ k, Finite (S k) := fun k ↦ by
    have := hfg.finite_quotient_pLowerCentralSeries hp k
    exact Finite.of_injective (fun s : S k ↦ ⇑s.1)
      (DFunLike.coe_injective.comp Subtype.val_injective)
  -- Each level is nonempty: a surjective endomorphism of `G` induces a surjection of `G ⧸ λ_k`.
  have : ∀ k, Nonempty (S k) := fun k ↦ by
    obtain ⟨φ, hsurj, hφa, hr⟩ := h k
    have hle : pLowerCentralSeries p G k ≤ (pLowerCentralSeries p G k).comap φ.toMonoidHom :=
      Subgroup.map_le_iff_le_comap.mp (φ.toMonoidHom.map_pLowerCentralSeries_le φ.continuous k)
    refine ⟨⟨⟨QuotientGroup.map _ _ φ.toMonoidHom hle, continuous_of_discreteTopology⟩,
      QuotientGroup.map_surjective_of_surjective _ _ _ (QuotientGroup.mk_surjective.comp hsurj) hle,
      fun i ↦ ?_, ?_⟩⟩
    · rw [ContinuousMonoidHom.coe_mk, QuotientGroup.map_mk, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
      exact ⟨_, hφa i, rfl⟩
    · rw [ContinuousMonoidHom.coe_mk, QuotientGroup.map_mk]
      exact QuotientGroup.eq.mpr hr
  let D : PLowerCentralSeriesComparison p G G S :=
    { map := fun _ s ↦ s.1
      map_surjective := fun _ s ↦ s.2.1
      bond := fun k s ↦ ⟨s.1.pLowerCentralSeriesDesc, s.1.pLowerCentralSeriesDesc_surjective s.2.1,
        fun i ↦ by
          obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp (s.2.2.1 i)
          refine ⟨x, hx, ?_⟩
          have := congrArg (QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k)) hxs
          rw [QuotientGroup.mk'_apply, QuotientGroup.mapOfLE_mk, map_mul, map_inv,
            QuotientGroup.mapOfLE_mk, ← ContinuousMonoidHom.pLowerCentralSeriesDesc_mk] at this
          exact this,
        by rw [ContinuousMonoidHom.pLowerCentralSeriesDesc_mk, s.2.2.2, QuotientGroup.mapOfLE_mk]⟩
      commutes := fun _ s x ↦ (s.1.pLowerCentralSeriesDesc_mapOfLE x).symm }
  obtain ⟨s, e, -, he, hr, -⟩ := D.exists_continuousMulEquiv_preserving hG hfg hp
    (fun _ : Unit ↦ r) (fun _ ↦ w) (1 : G →ₜ* G) 1 (fun _ s _ ↦ s.2.2.2)
    (fun _ ↦ ⟨0, fun _ _ _ _ ↦ by simp⟩)
  -- Each constraint holds on every finite quotient, hence in the limit.
  refine ⟨e, fun i ↦ hG.mem_of_forall_mk_mem_map_pLowerCentralSeries hp (hC i) fun k ↦ ?_, hr ()⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, he k]
  exact (s k).2.2.1 i

end Limit

end TauCeti
