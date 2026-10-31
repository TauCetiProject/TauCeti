/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Closure
public import TauCeti.GroupTheory.FreeGroup.Centralizer
public import TauCeti.GroupTheory.Finiteness
public import TauCeti.Order.Filter.AtTopBot
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The space of marked groups and limit groups

An `n`-marked group is a group `G` together with a generating tuple `S : Fin n → G`; it is
recorded by the kernel of `FreeGroup.lift S`, a normal subgroup of `FreeGroup (Fin n)`. The space
`𝒢ₙ` of `n`-marked groups is therefore the type of normal subgroups of `FreeGroup (Fin n)`,
topologised as a subspace of the Cantor space `FreeGroup (Fin n) → Bool` of indicator functions.
A sequence of marked groups converges exactly when, for every word, membership of that word in the
kernels eventually stabilises at its membership in the limit.

A limit group is a group some finite generating tuple of which marks a limit of markings of free
groups. This does not depend on the tuple: pulling markings back along a homomorphism of free
groups is continuous and sends markings of free groups to markings of free groups, by the
Nielsen–Schreier theorem, so every finite tuple of a limit group marks a limit of free markings.

## Main definitions

* `TauCeti.LimitGroup.MarkedGroup n`: the space `𝒢ₙ` of `n`-marked groups.
* `TauCeti.LimitGroup.MarkedGroup.ofMarking S`: the point of `𝒢ₙ` given by `S : Fin n → G`.
* `TauCeti.LimitGroup.MarkedGroup.freeMarkings n`: the markings of free groups.
* `TauCeti.LimitGroup.IsLimitGroup G`: `G` is a limit group.

## Main results

* `𝒢ₙ` embeds in the Cantor space, so it is Hausdorff and totally disconnected (instances); its
  image is closed, so it is compact (instance):
  `TauCeti.LimitGroup.MarkedGroup.isClosedEmbedding_kerIndicator`.
* `TauCeti.LimitGroup.MarkedGroup.tendsto_nhds_iff`: convergence in `𝒢ₙ` is eventual agreement
  of the kernels on each word.
* `TauCeti.LimitGroup.IsLimitGroup.ofMarking_mem_closure_freeMarkings`: every finite tuple of a
  limit group marks a limit of markings of free groups; `TauCeti.LimitGroup.isLimitGroup_iff`
  restates this as a characterization by all markings.
* `TauCeti.LimitGroup.IsLimitGroup.of_mulEquiv`, `MulEquiv.isLimitGroup_iff`: being a limit group
  is invariant under isomorphism.
* `TauCeti.LimitGroup.IsLimitGroup.of_isFreeGroup`: finitely generated free groups are limit
  groups.
* `TauCeti.LimitGroup.IsLimitGroup.isMulTorsionFree`: limit groups are torsion-free, so a
  nontrivial finite group is not a limit group.
* `TauCeti.LimitGroup.isLimitGroup_multiplicative_fin_two_int`: `ℤ²` is a limit group, the limit
  of the markings `(1, k)` of `ℤ`.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), §2.1, Definition 2.1, and §2.3, Definition 2.4.
-/

public section

open Filter Topology

namespace TauCeti.LimitGroup

/-- An `n`-marked group, recorded by the kernel of its marking `FreeGroup (Fin n) →* G`. The type
`MarkedGroup n` is the space `𝒢ₙ` of normal subgroups of `FreeGroup (Fin n)`. -/
@[ext]
structure MarkedGroup (n : ℕ) where
  /-- The kernel of the marking, a normal subgroup of `FreeGroup (Fin n)`. -/
  ker : Subgroup (FreeGroup (Fin n))
  [normal : ker.Normal]

namespace MarkedGroup

attribute [instance] normal

variable {l m n : ℕ}

/-- The indicator function of the kernel of a marked group, a point of the Cantor space
`FreeGroup (Fin n) → Bool`. -/
noncomputable def kerIndicator (N : MarkedGroup n) : FreeGroup (Fin n) → Bool := by
  classical exact fun w => decide (w ∈ N.ker)

@[simp]
theorem kerIndicator_eq_true {N : MarkedGroup n} {w : FreeGroup (Fin n)} :
    N.kerIndicator w = true ↔ w ∈ N.ker := by
  simp [kerIndicator]

theorem kerIndicator_eq_kerIndicator_iff {N : MarkedGroup m} {N' : MarkedGroup n}
    {w : FreeGroup (Fin m)} {w' : FreeGroup (Fin n)} :
    N.kerIndicator w = N'.kerIndicator w' ↔ (w ∈ N.ker ↔ w' ∈ N'.ker) := by
  simp only [kerIndicator, decide_eq_decide]

theorem kerIndicator_injective : Function.Injective (kerIndicator (n := n)) := by
  intro N N' h
  ext w
  rw [← kerIndicator_eq_true, h, kerIndicator_eq_true]

/-- The Cantor topology on `𝒢ₙ`, induced from the product topology on
`FreeGroup (Fin n) → Bool`. -/
noncomputable instance : TopologicalSpace (MarkedGroup n) :=
  .induced kerIndicator inferInstance

theorem isEmbedding_kerIndicator : IsEmbedding (kerIndicator (n := n)) :=
  ⟨⟨rfl⟩, kerIndicator_injective⟩

theorem continuous_kerIndicator_apply (w : FreeGroup (Fin n)) :
    Continuous fun N : MarkedGroup n => N.kerIndicator w :=
  (continuous_apply w).comp isEmbedding_kerIndicator.continuous

/-- The indicator functions of normal subgroups form a closed subset of the Cantor space: each of
the subgroup and normality axioms involves only finitely many coordinates. -/
theorem isClosed_range_kerIndicator : IsClosed (Set.range (kerIndicator (n := n))) := by
  have hclosed (a b c : FreeGroup (Fin n)) (P : Bool → Bool → Bool → Prop) :
      IsClosed {f : FreeGroup (Fin n) → Bool | P (f a) (f b) (f c)} :=
    (isClosed_discrete {t : Bool × Bool × Bool | P t.1 t.2.1 t.2.2}).preimage
      (f := fun f : FreeGroup (Fin n) → Bool => (f a, f b, f c)) (by fun_prop)
  have hrange : Set.range (kerIndicator (n := n)) =
      {f | f 1 = true} ∩ (⋂ a, ⋂ b, {f | f a = true → f b = true → f (a * b⁻¹) = true}) ∩
        ⋂ a, ⋂ b, {f | f a = true → f (b * a * b⁻¹) = true} := by
    ext f
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N, rfl⟩
      simp only [kerIndicator_eq_true]
      exact ⟨⟨N.ker.one_mem, fun a b ha hb => N.ker.mul_mem ha (N.ker.inv_mem hb)⟩,
        fun a b ha => N.normal.conj_mem a ha b⟩
    · rintro ⟨⟨h1, hmul⟩, hconj⟩
      let K : Subgroup (FreeGroup (Fin n)) := Subgroup.ofDiv {w | f w = true} ⟨1, h1⟩
        fun a ha b hb => by simpa [div_eq_mul_inv] using hmul a b ha hb
      -- `Subgroup.ofDiv s` has carrier `s`, and Mathlib states no membership lemma for it.
      have hmemK (w : FreeGroup (Fin n)) : w ∈ K ↔ f w = true := Iff.rfl
      have hK : K.Normal := ⟨fun a ha b => (hmemK _).2 (hconj a b ((hmemK a).1 ha))⟩
      refine ⟨⟨K⟩, funext fun w => ?_⟩
      rw [Bool.eq_iff_iff, kerIndicator_eq_true]
      exact hmemK w
  rw [hrange]
  exact ((hclosed 1 1 1 fun _ _ z => z = true).inter
    (isClosed_iInter fun a => isClosed_iInter fun b =>
      hclosed a b (a * b⁻¹) fun x y z => x = true → y = true → z = true)).inter
    (isClosed_iInter fun a => isClosed_iInter fun b =>
      hclosed a a (b * a * b⁻¹) fun x _ z => x = true → z = true)

theorem isClosedEmbedding_kerIndicator : IsClosedEmbedding (kerIndicator (n := n)) :=
  ⟨isEmbedding_kerIndicator, isClosed_range_kerIndicator⟩

/-- The space of `n`-marked groups is compact. -/
instance : CompactSpace (MarkedGroup n) :=
  isClosedEmbedding_kerIndicator.compactSpace

instance : T2Space (MarkedGroup n) :=
  isEmbedding_kerIndicator.t2Space

instance : TotallyDisconnectedSpace (MarkedGroup n) :=
  isEmbedding_kerIndicator.isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- The marked groups whose kernel contains a given word form a clopen set. -/
theorem isClopen_setOf_mem_ker (w : FreeGroup (Fin n)) :
    IsClopen {N : MarkedGroup n | w ∈ N.ker} := by
  convert (isClopen_discrete {true}).preimage (continuous_kerIndicator_apply w) using 1
  ext N
  simp

/-- Convergence in the space of marked groups is pointwise convergence of the indicator functions
of the kernels: for every word, its membership in the kernels eventually agrees with its
membership in the kernel of the limit. -/
theorem tendsto_nhds_iff {α : Type*} {f : α → MarkedGroup n} {l : Filter α} {N : MarkedGroup n} :
    Tendsto f l (𝓝 N) ↔ ∀ w, ∀ᶠ a in l, (w ∈ (f a).ker ↔ w ∈ N.ker) := by
  rw [isEmbedding_kerIndicator.tendsto_nhds_iff, tendsto_pi_nhds]
  refine forall_congr' fun w => ?_
  rw [nhds_discrete, tendsto_pure]
  simp only [Function.comp_apply, kerIndicator_eq_kerIndicator_iff]

section ofMarking

variable {G : Type*} [Group G]

/-- The `n`-marked group given by a tuple `S : Fin n → G`, recorded by the kernel of
`FreeGroup.lift S`. When `S` generates `G` this is the point of `𝒢ₙ` representing `(G, S)`. -/
def ofMarking (S : Fin n → G) : MarkedGroup n :=
  ⟨(FreeGroup.lift S).ker⟩

theorem ker_ofMarking (S : Fin n → G) : (ofMarking S).ker = (FreeGroup.lift S).ker :=
  (rfl)

@[simp]
theorem mem_ofMarking_ker {S : Fin n → G} {w : FreeGroup (Fin n)} :
    w ∈ (ofMarking S).ker ↔ FreeGroup.lift S w = 1 :=
  MonoidHom.mem_ker

/-- Every marked group is the marking of its own quotient by the images of the generators. -/
@[simp]
theorem ofMarking_mk_of (N : MarkedGroup n) :
    ofMarking (fun i => (FreeGroup.of i : FreeGroup (Fin n) ⧸ N.ker)) = N := by
  ext w
  rw [mem_ofMarking_ker, ← QuotientGroup.eq_one_iff (N := N.ker)]
  have : FreeGroup.lift (fun i => (FreeGroup.of i : FreeGroup (Fin n) ⧸ N.ker)) =
      QuotientGroup.mk' N.ker :=
    FreeGroup.ext_hom _ _ fun i => by simp
  rw [this, QuotientGroup.mk'_apply]

/-- Composing a tuple with an injective homomorphism does not change its marking. -/
@[simp]
theorem ofMarking_comp {H : Type*} [Group H] {f : G →* H} (hf : Function.Injective f)
    (S : Fin n → G) : ofMarking (f ∘ S) = ofMarking S := by
  have : FreeGroup.lift (f ∘ S) = f.comp (FreeGroup.lift S) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  ext w
  rw [ker_ofMarking, ker_ofMarking, this, MonoidHom.ker_comp_of_injective _ _ hf]

end ofMarking

/-- Pull a marked group back along a homomorphism `σ` of free groups: the kernel of the result is
the preimage of the kernel under `σ`. -/
def comap (σ : FreeGroup (Fin m) →* FreeGroup (Fin n)) (N : MarkedGroup n) : MarkedGroup m :=
  ⟨N.ker.comap σ⟩

theorem ker_comap (σ : FreeGroup (Fin m) →* FreeGroup (Fin n)) (N : MarkedGroup n) :
    (N.comap σ).ker = N.ker.comap σ :=
  (rfl)

@[simp]
theorem mem_comap_ker {σ : FreeGroup (Fin m) →* FreeGroup (Fin n)} {N : MarkedGroup n}
    {w : FreeGroup (Fin m)} : w ∈ (N.comap σ).ker ↔ σ w ∈ N.ker :=
  Subgroup.mem_comap

@[simp]
theorem comap_id (N : MarkedGroup n) : N.comap (MonoidHom.id _) = N := by
  ext
  simp

theorem comap_comp (σ : FreeGroup (Fin m) →* FreeGroup (Fin n))
    (τ : FreeGroup (Fin l) →* FreeGroup (Fin m)) (N : MarkedGroup n) :
    (N.comap σ).comap τ = N.comap (σ.comp τ) := by
  ext
  simp

theorem continuous_comap (σ : FreeGroup (Fin m) →* FreeGroup (Fin n)) :
    Continuous (comap σ) := by
  refine continuous_induced_rng.2 (continuous_pi fun w => ?_)
  convert continuous_kerIndicator_apply (σ w) using 2 with N
  exact kerIndicator_eq_kerIndicator_iff.2 mem_comap_ker

theorem comap_ofMarking {G : Type*} [Group G] (σ : FreeGroup (Fin m) →* FreeGroup (Fin n))
    (S : Fin n → G) :
    (ofMarking S).comap σ = ofMarking fun i => FreeGroup.lift S (σ (FreeGroup.of i)) := by
  have : (FreeGroup.lift S).comp σ =
      FreeGroup.lift fun i => FreeGroup.lift S (σ (FreeGroup.of i)) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  ext w
  simp [← this]

/-- The markings of free groups: the points of `𝒢ₙ` whose quotient group is free. -/
def freeMarkings (n : ℕ) : Set (MarkedGroup n) :=
  {N | IsFreeGroup (FreeGroup (Fin n) ⧸ N.ker)}

theorem mem_freeMarkings {N : MarkedGroup n} :
    N ∈ freeMarkings n ↔ IsFreeGroup (FreeGroup (Fin n) ⧸ N.ker) :=
  Iff.rfl

/-- Any tuple in a free group marks a free group: the subgroup it generates, which is free by the
Nielsen–Schreier theorem. -/
theorem ofMarking_mem_freeMarkings {F : Type*} [Group F] [IsFreeGroup F] (S : Fin n → F) :
    ofMarking S ∈ freeMarkings n :=
  mem_freeMarkings.2 <|
    IsFreeGroup.ofMulEquiv (QuotientGroup.quotientKerEquivRange (FreeGroup.lift S)).symm

/-- Pulling back along a homomorphism of free groups preserves markings of free groups. -/
theorem comap_mem_freeMarkings (σ : FreeGroup (Fin m) →* FreeGroup (Fin n)) {N : MarkedGroup n}
    (hN : N ∈ freeMarkings n) : N.comap σ ∈ freeMarkings m := by
  have := mem_freeMarkings.1 hN
  rw [← ofMarking_mk_of N, comap_ofMarking]
  exact ofMarking_mem_freeMarkings _

/-- Pulling back along a homomorphism of free groups preserves limits of markings of free
groups. -/
theorem comap_mem_closure_freeMarkings (σ : FreeGroup (Fin m) →* FreeGroup (Fin n))
    {N : MarkedGroup n} (hN : N ∈ closure (freeMarkings n)) :
    N.comap σ ∈ closure (freeMarkings m) :=
  map_mem_closure (continuous_comap σ) hN fun _ => comap_mem_freeMarkings σ

end MarkedGroup

open MarkedGroup

/-- A limit group: a group with a finite generating tuple whose marking is a limit of markings
of free groups. By `IsLimitGroup.ofMarking_mem_closure_freeMarkings`, every finite tuple of a
limit group then marks a limit of markings of free groups. -/
def IsLimitGroup (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (S : Fin n → G), Subgroup.closure (Set.range S) = ⊤ ∧
    ofMarking S ∈ closure (freeMarkings n)

variable {G : Type*} [Group G]

theorem isLimitGroup_def :
    IsLimitGroup G ↔ ∃ (n : ℕ) (S : Fin n → G), Subgroup.closure (Set.range S) = ⊤ ∧
      ofMarking S ∈ closure (freeMarkings n) :=
  Iff.rfl

namespace IsLimitGroup

/-- Limit groups are finitely generated. -/
theorem fg (h : IsLimitGroup G) : Group.FG G :=
  let ⟨n, S, hS, _⟩ := h
  Group.fg_iff_exists_fin_generating_family.2 ⟨n, S, hS⟩

/-- Independence of the marking: every finite tuple of a limit group, generating or not, marks a
limit of markings of free groups. Writing the tuple in terms of a generating tuple whose marking
is such a limit expresses its marking as a pullback along a homomorphism of free groups. -/
theorem ofMarking_mem_closure_freeMarkings (h : IsLimitGroup G) {m : ℕ} (T : Fin m → G) :
    ofMarking T ∈ closure (freeMarkings m) := by
  obtain ⟨n, S, hS, hmem⟩ := h
  choose u hu using fun j => FreeGroup.lift_surjective_iff_closure_range_eq_top.2 hS (T j)
  have : (ofMarking S).comap (FreeGroup.lift u) = ofMarking T := by
    rw [comap_ofMarking]
    simp [hu]
  exact this ▸ comap_mem_closure_freeMarkings _ hmem

/-- Being a limit group is invariant under isomorphism: an isomorphism carries a generating tuple
to a generating tuple with the same marking. -/
theorem of_mulEquiv {H : Type*} [Group H] (h : IsLimitGroup G) (e : G ≃* H) : IsLimitGroup H := by
  obtain ⟨n, S, hS, hmem⟩ := h
  refine ⟨n, e ∘ S, ?_, ?_⟩
  · rw [Set.range_comp]
    exact MonoidHom.closure_image_eq_top_of_surjective (e : G →* H) e.surjective hS
  · rwa [← MonoidHom.coe_ofClass e, ofMarking_comp e.injective]

/-- Finitely generated free groups are limit groups: their markings are markings of free
groups. -/
theorem of_isFreeGroup [IsFreeGroup G] [Group.FG G] : IsLimitGroup G := by
  obtain ⟨n, S, hS⟩ := Group.fg_iff_exists_fin_generating_family.1 ‹Group.FG G›
  exact ⟨n, S, hS, subset_closure (ofMarking_mem_freeMarkings S)⟩

/-- Limit groups are torsion-free. A torsion relation `w ^ k = 1`, `w ≠ 1`, defines an open
neighbourhood of the marking that contains no marking of a free group, because free groups are
torsion-free. -/
theorem isMulTorsionFree (h : IsLimitGroup G) : IsMulTorsionFree G := by
  obtain ⟨n, S, hS, hmem⟩ := h
  refine isMulTorsionFree_iff_not_isOfFinOrder.2 fun g hg hfin => ?_
  obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  obtain ⟨w, rfl⟩ := FreeGroup.lift_surjective_iff_closure_range_eq_top.2 hS g
  have hopen : IsOpen {N : MarkedGroup n | w ^ k ∈ N.ker ∧ w ∉ N.ker} :=
    (isClopen_setOf_mem_ker _).isOpen.inter (isClopen_setOf_mem_ker w).compl.isOpen
  obtain ⟨N, ⟨hwk, hw⟩, hN⟩ :=
    mem_closure_iff.1 hmem _ hopen ⟨by simpa using hgk, by simpa using hg⟩
  have := mem_freeMarkings.1 hN
  apply hw
  rw [← QuotientGroup.eq_one_iff] at hwk ⊢
  rw [QuotientGroup.mk_pow] at hwk
  exact (pow_eq_one_iff_left hk.ne').1 hwk

end IsLimitGroup

/-- Isomorphic groups are limit groups together. -/
theorem _root_.MulEquiv.isLimitGroup_iff {H : Type*} [Group H] (e : G ≃* H) :
    IsLimitGroup G ↔ IsLimitGroup H :=
  ⟨fun h => h.of_mulEquiv e, fun h => h.of_mulEquiv e.symm⟩

/-- Independence of the marking: a group is a limit group exactly when it is finitely generated
and every finite tuple in it marks a limit of markings of free groups. -/
theorem isLimitGroup_iff :
    IsLimitGroup G ↔
      Group.FG G ∧ ∀ (n : ℕ) (S : Fin n → G), ofMarking S ∈ closure (freeMarkings n) := by
  refine ⟨fun h => ⟨h.fg, fun _ => h.ofMarking_mem_closure_freeMarkings⟩, fun ⟨hG, h⟩ => ?_⟩
  obtain ⟨n, S, hS⟩ := Group.fg_iff_exists_fin_generating_family.1 hG
  exact ⟨n, S, hS, h n S⟩

/-- A nontrivial finite group is not a limit group, since it has torsion. -/
theorem not_isLimitGroup_of_finite [Finite G] [Nontrivial G] : ¬IsLimitGroup G := fun h =>
  let ⟨g, hg⟩ := exists_ne (1 : G)
  not_isMulTorsionFree_iff_isOfFinOrder.2 ⟨g, hg, isOfFinOrder_of_finite g⟩ h.isMulTorsionFree

/-- `ℤ²` is a limit group although it is not free: its standard marking is the limit, as
`k → ∞`, of the markings `(1, k)` of `ℤ`, because a word dies under `(1, k)` for all large `k`
exactly when both of its exponent sums vanish. -/
theorem isLimitGroup_multiplicative_fin_two_int : IsLimitGroup (Multiplicative (Fin 2 → ℤ)) := by
  let S : Fin 2 → Multiplicative (Fin 2 → ℤ) := fun i => .ofAdd (Pi.single i 1)
  let ψ (k : ℕ) : Multiplicative (Fin 2 → ℤ) →* Multiplicative ℤ :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.mk' (fun v => v 0 + k * v 1) fun v w => by
      simp only [Pi.add_apply]
      ring)
  have hψ (k : ℕ) (x : Multiplicative (Fin 2 → ℤ)) :
      ψ k x = 1 ↔ x.toAdd 0 + k * x.toAdd 1 = 0 := by
    simp [ψ, ← toAdd_eq_zero]
  have hS : Subgroup.closure (Set.range S) = ⊤ := by
    refine FreeGroup.lift_surjective_iff_closure_range_eq_top.1 fun x => ?_
    refine ⟨FreeGroup.of 0 ^ x.toAdd 0 * FreeGroup.of 1 ^ x.toAdd 1, ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [S]
  have : IsFreeGroup (Multiplicative ℤ) :=
    IsFreeGroup.ofMulEquiv (FreeGroup.mulEquivIntOfUnique (α := Unit))
  refine ⟨2, S, hS, mem_closure_of_tendsto (f := fun k => ofMarking (ψ k ∘ S)) (b := atTop) ?_
    (Eventually.of_forall fun k => ofMarking_mem_freeMarkings _)⟩
  rw [tendsto_nhds_iff]
  intro w
  have hlift (k : ℕ) : FreeGroup.lift (ψ k ∘ S) = (ψ k).comp (FreeGroup.lift S) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  simp only [mem_ofMarking_ker, hlift, MonoidHom.comp_apply, hψ]
  generalize FreeGroup.lift S w = x
  simp only [← toAdd_eq_zero, funext_iff, Fin.forall_fin_two, Pi.zero_apply]
  exact TauCeti.eventually_add_mul_eq_zero_iff _ _

end TauCeti.LimitGroup
