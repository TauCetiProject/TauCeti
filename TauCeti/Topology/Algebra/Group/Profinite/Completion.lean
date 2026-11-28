/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import TauCeti.Topology.Algebra.Group.Profinite.FiniteQuotients

/-!
# The universal property of profinite completion

This file restates the categorical universal property of Mathlib's profinite completion for
unbundled groups and continuous monoid homomorphisms. It also proves that the canonical map from
a finite group to its profinite completion is bijective, and exposes the projections of the
profinite completion onto the finite quotients it is the limit of.

The correspondence `continuousMonoidHomEquiv` allows the group and the profinite target to live
in independent universes, unlike Mathlib's single-universe adjunction
`ProfiniteGrp.ProfiniteCompletion.homEquiv`; this is what lets a fixed universe-polymorphic
completion, such as the profinite integers, map to profinite groups in any universe.

A continuous homomorphism out of the completion is surjective onto a Hausdorff target when it has
dense range on `G` (`surjective_continuousMonoidHom_of_denseRange`), and injective when every
finite-index normal subgroup of `G` contains the elements sent near `1`
(`injective_continuousMonoidHom_of_forall_exists_nhds_one_comap_le`).

The continuous finite quotients of the completion are exactly the finite quotients of `G`
(`isFiniteContinuousQuotient_iff_exists_surjective`), and the completion of a finitely generated
group is topologically finitely generated (`isTopologicallyFinitelyGenerated`). Through the
finite-quotient determinacy of topologically finitely generated profinite groups this gives the
theorem of Dixon, Formanek, Poland and Ribes: two finitely generated groups with the same finite
quotients have topologically isomorphic profinite completions
(`nonempty_continuousMulEquiv_of_forall_exists_surjective_iff`); in fact finite generation of one
of the two groups suffices.

A family `𝒩` of finite-index normal subgroups of `G` defines a coarser completion
`lim_{N ∈ 𝒩} G ⧸ N`, such as the congruence completion of an arithmetic group, and the profinite
completion maps to it through its coordinates at the members of `𝒩`. The kernel of this
comparison is `familyKernel G 𝒩`, a closed normal subgroup which is the intersection of the
closures of the members of `𝒩` (`familyKernel_eq_iInf_topologicalClosure`). For a nonempty
downward directed family it is trivial exactly when every finite-index subgroup of `G` contains a
member of `𝒩` (`familyKernel_eq_bot_iff_forall_finiteIndex`).

## References

* J. D. Dixon, E. W. Formanek, J. C. Poland and L. Ribes, *Profinite completions and isomorphic
  finite quotients*, J. Pure Appl. Algebra 23 (1982), 227–231.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 3.2.
* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for
  `SLₙ (n ≥ 3)` and `Sp₂ₙ (n ≥ 2)`*, Publ. Math. IHÉS 33 (1967), §14, for the kernel of the
  comparison with a coarser completion.
-/

public section

namespace TauCeti

open CategoryTheory

namespace ProfiniteCompletion

universe u v

variable (G : Type u) [Group G]
variable (P : Type v) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [TotallyDisconnectedSpace P]

/-- Two continuous homomorphisms from a profinite completion to a Hausdorff topological monoid
agree if they agree on the canonical dense image of the original group. -/
@[ext]
theorem continuousMonoidHom_ext
    {Q : Type v} [Monoid Q] [TopologicalSpace Q] [T2Space Q]
    {f g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* Q}
    (h : ∀ x : G,
      f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) x) =
        g (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) x)) : f = g := by
  apply DFunLike.coe_injective
  exact (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
    f.continuous_toFun g.continuous_toFun (funext h)

/-- The canonical map from a finite group to its profinite completion is bijective. -/
theorem etaFn_bijective_of_finite [Finite G] :
    Function.Bijective (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G)) := by
  refine ⟨(ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
    (G := GrpCat.of G)).2 inferInstance, ?_⟩
  intro x
  have hx : x ∈ closure (Set.range
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G))) := by
    rw [(ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).closure_range]
    exact Set.mem_univ x
  rw [(Set.finite_range _).isClosed.closure_eq] at hx
  exact hx

/-- The projection from the profinite completion of `G` onto its finite quotient indexed by the
finite-index normal subgroup `H`. -/
def coordinateHom (H : FiniteIndexNormalSubgroup G) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →* G ⧸ H.toSubgroup := by
  let f := ((ProfiniteGrp.limitCone
    (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of G))).π.app H).hom
    |>.toMonoidHom
  -- The finite-quotient object hides its underlying quotient group.
  change ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →* G ⧸ H.toSubgroup at f
  exact f

/-- The projection onto the finite quotient by `H` evaluates the underlying compatible family of
cosets at `H`. -/
@[simp]
theorem coordinateHom_apply (H : FiniteIndexNormalSubgroup G)
    (x : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) :
    coordinateHom G H x = x.val H :=
  -- The limit-cone projection computes on coordinates by definition; isolate that reduction in
  -- this opaque theorem so that `coordinateHom` itself stays unexposed.
  (rfl)

/-- The `H`-coordinate of the canonical image of `g` is its coset modulo `H`. -/
-- The priority keeps this specialization ahead of `coordinateHom_apply`, which would otherwise
-- rewrite its left-hand side to the raw coordinate of the canonical image.
@[simp high]
theorem coordinateHom_etaFn (H : FiniteIndexNormalSubgroup G) (g : G) :
    coordinateHom G H (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
      QuotientGroup.mk g := by
  rw [coordinateHom_apply]
  -- `etaFn g` is the constant family of cosets of `g`.
  rfl

/-- The projection onto a finite quotient is continuous, that quotient carrying the discrete
topology. -/
theorem continuous_coordinateHom (H : FiniteIndexNormalSubgroup G) :
    @Continuous (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))
      (G ⧸ H.toSubgroup) inferInstance ⊥ (coordinateHom G H) :=
  -- The finite-quotient object hides its discrete underlying quotient group.
  ((ProfiniteGrp.limitCone
    (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of G))).π.app H).hom.continuous_toFun

variable {G P} in
/-- The continuous homomorphism from the profinite completion of `G` to the limit of the finite
quotients of `P` induced by `f : G →* P`: its coordinate at an open normal subgroup `U` is the
coordinate of the completion at the preimage of `U`, pushed forward along `f`. -/
private def liftToLimit (f : G →* P) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
      ProfiniteGrp.limit (ProfiniteGrp.diagram (ProfiniteGrp.of P)) where
  toFun x := ⟨fun U ↦ QuotientGroup.map
      (U.toFiniteIndexNormalSubgroup.comap f).toSubgroup U.toSubgroup f (fun _ h ↦ h)
      (x.val (U.toFiniteIndexNormalSubgroup.comap f)), by
    intro U V hUV
    have hx := x.property (FiniteIndexNormalSubgroup.comap_mono f
      (OpenNormalSubgroup.toFiniteIndexNormalSubgroup_mono hUV.le)).hom
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (x.val (U.toFiniteIndexNormalSubgroup.comap f))
    dsimp only
    rw [← hx, ← hg]
    -- Both sides are the coset of `f g` modulo `V`.
    rfl⟩
  map_one' := ProfiniteGrp.limit_ext _ _ _ fun _ ↦ map_one (QuotientGroup.map _ _ f _)
  map_mul' _ _ := ProfiniteGrp.limit_ext _ _ _ fun _ ↦ map_mul (QuotientGroup.map _ _ f _) _ _
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun U ↦ ?_) _
    let H := U.toFiniteIndexNormalSubgroup.comap f
    let _ : TopologicalSpace (G ⧸ H.toSubgroup) := ⊥
    have _ : DiscreteTopology (G ⧸ H.toSubgroup) := ⟨rfl⟩
    have hc : Continuous fun x : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) ↦
        x.val H :=
      (continuous_coordinateHom G H).congr (coordinateHom_apply G H)
    exact (continuous_of_discreteTopology (α := G ⧸ H.toSubgroup)
      (β := (ProfiniteGrp.diagram (ProfiniteGrp.of P)).obj U)
      (f := QuotientGroup.map H.toSubgroup U.toSubgroup f fun _ h ↦ h)).comp hc

variable {G P} in
/-- The continuous extension of `f : G →* P` to the profinite completion of `G`, read back into
`P` through its presentation as the limit of its finite quotients. -/
private noncomputable def liftAux (f : G →* P) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* P :=
  ContinuousMonoidHom.comp
    (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor (ProfiniteGrp.of P)).symm
    (liftToLimit f)

variable {G P} in
/-- The continuous extension of `f` agrees with `f` on the original group. -/
private theorem liftAux_etaFn (f : G →* P) (g : G) :
    liftAux f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = f g := by
  -- Unfold `liftAux` to the inverse of the limit presentation applied to `liftToLimit f`.
  change (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor (ProfiniteGrp.of P)).symm
    (liftToLimit f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)) = f g
  rw [ContinuousMulEquiv.symm_apply_eq]
  -- Both sides are the family of cosets of `f g`.
  rfl

/-- Continuous homomorphisms from the profinite completion of `G` to a profinite group `P`
correspond to abstract homomorphisms from `G` to `P`, by restriction along the canonical map.
The target `P` may live in a different universe from `G`. -/
-- Mathlib's adjunction `ProfiniteGrp.ProfiniteCompletion.homEquiv` is stated within one universe,
-- so the inverse is built from the presentation of `P` as the limit of its finite quotients,
-- Mathlib's `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`.
noncomputable def continuousMonoidHomEquiv :
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* P) ≃ (G →* P) where
  toFun f := (f : _ →* P).comp (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom
  invFun := liftAux
  left_inv _ := continuousMonoidHom_ext G fun g ↦ liftAux_etaFn _ g
  right_inv f := MonoidHom.ext (liftAux_etaFn f)

/-- The unbundled profinite-completion correspondence restricts a continuous homomorphism along
the canonical map. -/
@[simp]
theorem continuousMonoidHomEquiv_apply
    (f : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* P) (g : G) :
    continuousMonoidHomEquiv G P f g =
      f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) :=
  -- The canonical morphism `eta` is `etaFn` as a homomorphism, by definition.
  (rfl)

/-- The continuous lift of an abstract homomorphism agrees with it on the original group. -/
@[simp]
theorem continuousMonoidHomEquiv_symm_apply_etaFn (f : G →* P) (g : G) :
    (continuousMonoidHomEquiv G P).symm f
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = f g :=
  liftAux_etaFn f g

/-- A continuous homomorphism from the profinite completion of `G` to a Hausdorff topological
monoid is surjective as soon as its restriction to the canonical image of `G` has dense range: its
image is compact, hence closed. -/
theorem surjective_continuousMonoidHom_of_denseRange
    {Q : Type v} [Monoid Q] [TopologicalSpace Q] [T2Space Q]
    (F : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* Q)
    (hF : DenseRange fun g : G ↦ F (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g)) :
    Function.Surjective F := by
  have hc : IsClosed (Set.range F) := (map_continuous F).isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← hc.closure_eq]
  refine Dense.closure_eq (hF.mono ?_)
  rintro _ ⟨g, rfl⟩
  exact ⟨_, rfl⟩

/-- **Injectivity criterion for maps out of a profinite completion.** A continuous homomorphism
`F` from the profinite completion of `G` to a topological monoid is injective if every
finite-index normal subgroup `H` of `G` contains every `g` that `F` maps into some fixed
neighbourhood of `1`. -/
theorem injective_continuousMonoidHom_of_forall_exists_nhds_one_comap_le
    {Q : Type v} [Monoid Q] [TopologicalSpace Q]
    (F : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* Q)
    (h : ∀ H : FiniteIndexNormalSubgroup G, ∃ U ∈ nhds (1 : Q), ∀ g : G,
      F (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) ∈ U → g ∈ H) :
    Function.Injective F := by
  rw [injective_iff_map_eq_one]
  intro c hc
  refine ProfiniteGrp.limit_ext _ _ _ fun H ↦ ?_
  rw [← coordinateHom_apply G H c, ← coordinateHom_apply G H 1, map_one]
  obtain ⟨U, hU, hUH⟩ := h H
  -- the elements of `G` near `c` lie in `H` and share the `H`-coordinate of `c`; the fibre of
  -- `coordinateHom G H` is open since every set is open in the discrete topology `⊥`
  have hN : F ⁻¹' U ∩ coordinateHom G H ⁻¹' {coordinateHom G H c} ∈ nhds c :=
    Filter.inter_mem ((map_continuous F).continuousAt (hc ▸ hU))
      ((@Continuous.isOpen_preimage _ _ _ ⊥ _ (continuous_coordinateHom G H) _ trivial).mem_nhds
        rfl)
  obtain ⟨_, ⟨g, rfl⟩, hgU, hgc⟩ :=
    (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).inter_nhds_nonempty hN
  rw [← hgc, coordinateHom_etaFn]
  exact (QuotientGroup.eq_one_iff g).2 (hUH g hgU)

section FiniteQuotients

variable {G}

/-- **The continuous finite quotients of the profinite completion are the finite quotients of the
group.** A finite group `Q` occurs as a continuous finite quotient of the profinite completion of
`G` exactly when there is a surjective homomorphism `G →* Q`. -/
theorem isFiniteContinuousQuotient_iff_exists_surjective {Q : Type u} [Group Q] [Finite Q] :
    IsFiniteContinuousQuotient (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) Q ↔
      ∃ f : G →* Q, Function.Surjective f := by
  -- A continuous surjection out of the completion restricts along the dense canonical image to a
  -- surjection out of `G`; a surjection out of `G` extends continuously to the completion by the
  -- universal property.
  let : TopologicalSpace Q := ⊥
  have : DiscreteTopology Q := ⟨rfl⟩
  rw [isFiniteContinuousQuotient_iff_exists_continuous]
  constructor
  · rintro ⟨F, hF, hFc⟩
    refine ⟨continuousMonoidHomEquiv G Q ⟨F, hFc⟩, fun q ↦ ?_⟩
    -- The image of the dense canonical image of `G` is dense in the discrete group `Q`, hence
    -- is all of `Q`.
    have hq : q ∈ closure (Set.range (⇑F ∘ ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G))) :=
      hF.denseRange.comp (ProfiniteGrp.ProfiniteCompletion.denseRange _) hFc q
    rw [(isClosed_discrete _).closure_eq] at hq
    obtain ⟨g, hg⟩ := hq
    refine ⟨g, ?_⟩
    rw [continuousMonoidHomEquiv_apply]
    -- The continuous homomorphism `⟨F, hFc⟩` is `F` as a function, by definition.
    exact hg
  · rintro ⟨f, hf⟩
    refine ⟨((continuousMonoidHomEquiv G Q).symm f : _ →* Q), fun q ↦ ?_,
      ((continuousMonoidHomEquiv G Q).symm f).continuous⟩
    obtain ⟨g, rfl⟩ := hf q
    exact ⟨_, continuousMonoidHomEquiv_symm_apply_etaFn G Q f g⟩

/-- The profinite completion of a finitely generated group is topologically finitely generated:
the canonical image of `G` is dense. -/
theorem isTopologicallyFinitelyGenerated [Group.FG G] :
    IsTopologicallyFinitelyGenerated
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) := by
  let : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  -- The canonical map, as a homomorphism: the restriction of the identity of the completion.
  let η : G →* ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) :=
    continuousMonoidHomEquiv G _ (ContinuousMonoidHom.id _)
  have hη : ⇑η = ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) := funext fun g ↦ by
    simp [η]
  refine (TauCeti.isTopologicallyFinitelyGenerated_of_fg (G := G)).of_denseRange (f := η)
    continuous_of_discreteTopology ?_
  rw [hη]
  exact ProfiniteGrp.ProfiniteCompletion.denseRange _

/-- **Finitely generated groups with the same finite quotients have isomorphic profinite
completions** (Dixon, Formanek, Poland and Ribes). If `G` is finitely generated and every finite
group is a quotient of `G` exactly when it is a quotient of `H`, then the profinite completions of
`G` and `H` are topologically isomorphic. No finiteness hypothesis is placed on `H`. -/
theorem nonempty_continuousMulEquiv_of_forall_exists_surjective_iff {H : Type u} [Group H]
    [Group.FG G]
    (h : ∀ (Q : Type u) [Group Q] [Finite Q],
      (∃ f : G →* Q, Function.Surjective f) ↔ ∃ f : H →* Q, Function.Surjective f) :
    Nonempty (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) ≃ₜ*
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of H)) :=
  nonempty_continuousMulEquiv_of_forall_isFiniteContinuousQuotient_iff
    isTopologicallyFinitelyGenerated fun Q _ _ ↦ by
      rw [isFiniteContinuousQuotient_iff_exists_surjective,
        isFiniteContinuousQuotient_iff_exists_surjective]
      exact h Q

end FiniteQuotients


section FamilyKernel

/-! ### Completion relative to a family of finite-index normal subgroups

A family `𝒩` of finite-index normal subgroups of `G` defines the coarser completion
`lim_{N ∈ 𝒩} G ⧸ N`; the profinite completion maps onto it through its coordinates at the
members of `𝒩`. The kernel of that comparison is `familyKernel G 𝒩`. -/

variable {G} in
/-- The coordinates of an element of the profinite completion are compatible: for `H ≤ K`, the
`K`-coordinate is the image of the `H`-coordinate under `G ⧸ H → G ⧸ K`. -/
theorem coordinateHom_eq_map {H K : FiniteIndexNormalSubgroup G} (h : H ≤ K)
    (x : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) :
    coordinateHom G K x = QuotientGroup.map _ _ (MonoidHom.id G) h (coordinateHom G H x) := by
  rw [coordinateHom_apply, coordinateHom_apply]
  exact (x.property (homOfLE h)).symm

/-- A smaller finite-index normal subgroup has a smaller coordinate kernel. -/
theorem ker_coordinateHom_mono {H K : FiniteIndexNormalSubgroup G} (h : H ≤ K) :
    (coordinateHom G H).ker ≤ (coordinateHom G K).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [coordinateHom_eq_map h, hx, map_one]

/-- The kernel of a coordinate projection is open in the profinite completion. -/
theorem isOpen_ker_coordinateHom (H : FiniteIndexNormalSubgroup G) :
    IsOpen (SetLike.coe (coordinateHom G H).ker) :=
  -- every set is open in the discrete topology `⊥` of the finite quotient
  @Continuous.isOpen_preimage _ _ _ ⊥ _ (continuous_coordinateHom G H) {1} trivial

/-- The kernel of a coordinate projection is closed in the profinite completion. -/
theorem isClosed_ker_coordinateHom (H : FiniteIndexNormalSubgroup G) :
    IsClosed (SetLike.coe (coordinateHom G H).ker) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_ker_coordinateHom G H)

/-- The canonical image of `g` lies in the kernel of the `H`-coordinate exactly when `g ∈ H`. -/
theorem etaFn_mem_ker_coordinateHom_iff (H : FiniteIndexNormalSubgroup G) {g : G} :
    ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g ∈ (coordinateHom G H).ker ↔ g ∈ H := by
  rw [MonoidHom.mem_ker, coordinateHom_etaFn, QuotientGroup.eq_one_iff,
    FiniteIndexNormalSubgroup.mem_toSubgroup_iff]

/-- The kernel of the `H`-coordinate is the closure of the canonical image of `H`. -/
theorem topologicalClosure_map_eta (H : FiniteIndexNormalSubgroup G) :
    (H.toSubgroup.map
      (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom).topologicalClosure =
      (coordinateHom G H).ker := by
  refine le_antisymm (Subgroup.topologicalClosure_minimal _ ?_
    (isClosed_ker_coordinateHom G H)) fun x hx ↦ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact (etaFn_mem_ker_coordinateHom_iff G H).2 hg
  · -- the open kernel lies in the closure of its intersection with the dense image of `G`
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    refine closure_mono ?_
      ((ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).open_subset_closure_inter
        (isOpen_ker_coordinateHom G H) hx)
    rintro _ ⟨hgH, g, rfl⟩
    exact ⟨g, (etaFn_mem_ker_coordinateHom_iff G H).1 hgH, rfl⟩

/-- The kernel of the comparison from the profinite completion of `G` to its completion
`lim_{N ∈ 𝒩} G ⧸ N` relative to a family `𝒩` of finite-index normal subgroups: the elements
whose coordinates at all members of `𝒩` are trivial. For the principal congruence subgroups of an
arithmetic group this is the congruence kernel. -/
def familyKernel (𝒩 : Set (FiniteIndexNormalSubgroup G)) :
    Subgroup (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) :=
  ⨅ H ∈ 𝒩, (coordinateHom G H).ker

variable {G}

theorem mem_familyKernel_iff {𝒩 : Set (FiniteIndexNormalSubgroup G)}
    {x : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)} :
    x ∈ familyKernel G 𝒩 ↔ ∀ H ∈ 𝒩, coordinateHom G H x = 1 := by
  simp [familyKernel]

instance familyKernel_normal (𝒩 : Set (FiniteIndexNormalSubgroup G)) :
    (familyKernel G 𝒩).Normal :=
  Subgroup.normal_iInf_normal fun _ ↦ Subgroup.normal_iInf_normal fun _ ↦ inferInstance

theorem isClosed_familyKernel (𝒩 : Set (FiniteIndexNormalSubgroup G)) :
    IsClosed (SetLike.coe (familyKernel G 𝒩)) := by
  simp only [familyKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun H ↦ isClosed_iInter fun _ ↦ isClosed_ker_coordinateHom G H

/-- The canonical image of `g` lies in the family kernel exactly when `g` lies in every member of
the family. -/
@[simp]
theorem etaFn_mem_familyKernel_iff {𝒩 : Set (FiniteIndexNormalSubgroup G)} {g : G} :
    ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g ∈ familyKernel G 𝒩 ↔ ∀ H ∈ 𝒩, g ∈ H := by
  simp only [familyKernel, Subgroup.mem_iInf, etaFn_mem_ker_coordinateHom_iff]

/-- The family kernel is the intersection of the closures in the profinite completion of the
canonical images of the members of the family. -/
theorem familyKernel_eq_iInf_topologicalClosure (𝒩 : Set (FiniteIndexNormalSubgroup G)) :
    familyKernel G 𝒩 = ⨅ H ∈ 𝒩, (H.toSubgroup.map
      (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom).topologicalClosure := by
  unfold familyKernel
  exact iInf_congr fun H ↦ iInf_congr fun _ ↦ (topologicalClosure_map_eta G H).symm

/-- Passing to a cofinal family can only shrink the family kernel: if every member of `𝒩`
contains a member of `𝒩'`, the kernel of `𝒩'` lies in that of `𝒩`. In particular mutually
cofinal families have the same kernel. -/
theorem familyKernel_le_of_forall_exists_le {𝒩 𝒩' : Set (FiniteIndexNormalSubgroup G)}
    (h : ∀ H ∈ 𝒩, ∃ K ∈ 𝒩', K ≤ H) : familyKernel G 𝒩' ≤ familyKernel G 𝒩 := by
  intro x hx
  rw [mem_familyKernel_iff] at hx ⊢
  intro H hH
  obtain ⟨K, hK, hKH⟩ := h H hH
  exact ker_coordinateHom_mono G hKH (hx K hK)

/-- **The family kernel is trivial exactly when the family is cofinal.** For a nonempty
downward directed family `𝒩` of finite-index normal subgroups, the comparison from the profinite
completion to the completion relative to `𝒩` is injective exactly when every finite-index normal
subgroup contains a member of `𝒩`. -/
theorem familyKernel_eq_bot_iff {𝒩 : Set (FiniteIndexNormalSubgroup G)} (hne : 𝒩.Nonempty)
    (hdir : DirectedOn (· ≥ ·) 𝒩) :
    familyKernel G 𝒩 = ⊥ ↔ ∀ M : FiniteIndexNormalSubgroup G, ∃ H ∈ 𝒩, H ≤ M := by
  refine ⟨fun h M ↦ ?_, fun h ↦ (Subgroup.eq_bot_iff_forall _).2 fun x hx ↦ ?_⟩
  · have : Nonempty 𝒩 := hne.to_subtype
    -- The complement of the open subgroup `ker (coordinateHom G M)` is compact and misses the
    -- intersection of the directed family of closed kernels at the members of `𝒩`, so it
    -- misses one of them.
    have hdisj : Disjoint (SetLike.coe (coordinateHom G M).ker)ᶜ
        (⋂ H : 𝒩, (SetLike.coe (coordinateHom G H).ker)) := by
      refine Set.disjoint_left.2 fun x hxM hx ↦ hxM ?_
      have hx' : x ∈ familyKernel G 𝒩 := mem_familyKernel_iff.2 fun H hH ↦
        Set.mem_iInter.1 hx ⟨H, hH⟩
      rw [h, Subgroup.mem_bot] at hx'
      exact hx' ▸ one_mem _
    have hdir' : Directed (· ⊇ ·) fun H : 𝒩 ↦ (SetLike.coe (coordinateHom G H).ker) := by
      rintro ⟨H₁, h₁⟩ ⟨H₂, h₂⟩
      obtain ⟨H, hH, hH₁, hH₂⟩ := hdir H₁ h₁ H₂ h₂
      exact ⟨⟨H, hH⟩, ker_coordinateHom_mono G hH₁, ker_coordinateHom_mono G hH₂⟩
    obtain ⟨⟨H, hH⟩, hHM⟩ := (isOpen_ker_coordinateHom G M).isClosed_compl.isCompact
      |>.elim_directed_family_closed _ (fun H : 𝒩 ↦ isClosed_ker_coordinateHom G H) hdisj hdir'
    refine ⟨H, hH, fun g hg ↦ (etaFn_mem_ker_coordinateHom_iff G M).1 ?_⟩
    by_contra hgM
    exact Set.disjoint_left.1 hHM hgM ((etaFn_mem_ker_coordinateHom_iff G H).2 hg)
  · -- an element with trivial coordinates at a cofinal family has all coordinates trivial
    refine ProfiniteGrp.limit_ext _ _ _ fun M ↦ ?_
    obtain ⟨H, hH, hHM⟩ := h M
    rw [← coordinateHom_apply G M x, ← coordinateHom_apply G M 1, map_one]
    exact ker_coordinateHom_mono G hHM (mem_familyKernel_iff.1 hx H hH)

/-- The family kernel is trivial exactly when every finite-index subgroup, normal or not,
contains a member of the nonempty downward directed family `𝒩`. -/
theorem familyKernel_eq_bot_iff_forall_finiteIndex {𝒩 : Set (FiniteIndexNormalSubgroup G)}
    (hne : 𝒩.Nonempty) (hdir : DirectedOn (· ≥ ·) 𝒩) :
    familyKernel G 𝒩 = ⊥ ↔ ∀ H : Subgroup G, H.FiniteIndex → ∃ N ∈ 𝒩, N.toSubgroup ≤ H := by
  rw [familyKernel_eq_bot_iff hne hdir]
  refine ⟨fun h H _ ↦ ?_, fun h M ↦ h M.toSubgroup inferInstance⟩
  obtain ⟨N, hN, hNH⟩ := h (.ofSubgroup H.normalCore)
  exact ⟨N, hN, le_trans hNH H.normalCore_le⟩

end FamilyKernel

end ProfiniteCompletion

end TauCeti
