/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.ChangeOfGroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Transfer.StrictDimension
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# Inflation of the pro-p class module along `V ≤ W`

Let `G` be a profinite group and `V ≤ W` open subgroups. The transfer
`W → V^ab(p)` of the canonical map `V → V^ab(p)` factors through `W^ab(p)`, giving
`Ver_{W→V} = TauCeti.abelianizationProPTransferLe : W^ab(p) →* V^ab(p)`. It is continuous, and
when `V` and `W` are normal in `G` it is equivariant along the quotient map `G ⧸ V → G ⧸ W`, so
it forms a compatible pair with that map. The induced maps on explicit `H¹` and `H²` are NSW's
map `i : Hⁱ(G ⧸ W, W^ab(p)) → Hⁱ(G ⧸ V, V^ab(p))` of (3.6.1)(ii), here
`TauCeti.abelianizationProPInfl1` and `TauCeti.abelianizationProPInfl2`.

On the class of an element of `V`, the transfer is the norm of `W.map (mk' V)`, the image of `W` in
`G ⧸ V`. The inflation of the class `u_{G/W}(p)` to `G ⧸ V` and the push-forward of `u_{G/V}(p)`
along `V^ab(p) → W^ab(p)` differ by an explicit coboundary, and the norm of the finite normal
subgroup `W.map (mk' V)` acts on `H²(G ⧸ V, V^ab(p))` as multiplication by its order
(`TauCeti.ContCohomology.explicitCoeff2_eq_card_nsmul`). Together these give NSW (3.6.1)(ii),
`i (u_{G/W}(p)) = (W : V) • u_{G/V}(p)`, with no hypothesis on the cohomological dimension.

When `scd_p G ≤ 2`, the induced map `Ver_{W→V} : W^ab(p) →* V^ab(p)` is injective with image the
invariants of `W.map (mk' V)`. This is NSW (3.6.4)(ii) for the group `W`. Its strict dimension is
at most that of `G`, and the pair `V ◁ W` computed in `W` is identified with the restriction of the
pair `V ◁ G` by `TauCeti.abelianizationProPSubgroupOfEquiv`. So `i` is inflation from
`(G ⧸ V) ⧸ W.map (mk' V) ≅ G ⧸ W` with coefficients the invariants. The inflation-restriction
sequence `TauCeti.ContCohomology.explicitInfRes_exact` then makes `i` in degree one injective with
image the kernel of restriction to `W.map (mk' V)`, NSW (1.6.7) for this pair. In degree two the
same holds when `H¹(W.map (mk' V), V^ab(p))` vanishes, by
`TauCeti.ContCohomology.explicitInfl2_injective` and `TauCeti.ContCohomology.explicitInfRes2_exact`.

## Main definitions

* `TauCeti.abelianizationProPTransferLe`: the transfer `W^ab(p) →* V^ab(p)` for `V ≤ W`.
* `TauCeti.abelianizationProPInfl1` and `TauCeti.abelianizationProPInfl2`: the compatible-pair
  pullbacks along `G ⧸ V → G ⧸ W` and `Ver_{W→V}` on explicit `H¹` and `H²`.

## Main results

* `TauCeti.abelianizationProPTransferLe_mk`: on the class of `w : W`, the map is Mathlib's
  transfer of `V.subgroupOf W → V^ab(p)` at `w`.
* `TauCeti.abelianizationProPTransferLe_smul`: equivariance along `G ⧸ V → G ⧸ W`.
* `TauCeti.abelianizationProPTransferLe_mk_inclusion`: on the class of `v : V`, the map is the norm
  of `W.map (mk' V)`.
* `TauCeti.abelianizationProPTransferLe_injective` and `TauCeti.abelianizationProPTransferLe_range`:
  under `scd_p G ≤ 2`, the map is injective with image the `W.map (mk' V)`-invariants.
* `TauCeti.abelianizationProPInfl1_injective` and `TauCeti.abelianizationProPInfl1_exact`: under
  `scd_p G ≤ 2`, the map `i` in degree one is injective with image the kernel of restriction to
  `W.map (mk' V)`.
* `TauCeti.abelianizationProPInfl2_injective` and `TauCeti.abelianizationProPInfl2_exact`: the same
  in degree two, when moreover `H¹(W.map (mk' V), V^ab(p))` vanishes.
* `TauCeti.abelianizationProPInfl2_class`: NSW (3.6.1)(ii), `i (u_{G/W}(p)) = (W : V) • u_{G/V}(p)`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (1.6.7), (3.6.1)(ii) and (3.6.4)(ii).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {V W : Subgroup G} [V.FiniteIndex] (hVW : V ≤ W)
  (hV : IsOpen (V : Set G))

/-- The transfer `Ver_{W→V} : W^ab(p) →* V^ab(p)` for open `V ≤ W`: Mathlib's transfer
`W → V^ab(p)` of the canonical map `V.subgroupOf W ≃ V → V^ab(p)`, which is continuous and so
factors through the maximal pro-`p` abelian quotient `W^ab(p)`. -/
noncomputable def abelianizationProPTransferLe :
    abelianizationProP p G W →* abelianizationProP p G V :=
  haveI : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  let T : W →ₜ* abelianizationProP p G V :=
    ⟨MonoidHom.transfer ((abelianizationProPMk p G V).comp
        (Subgroup.subgroupOfEquivOfLe hVW).toMonoidHom),
      continuous_transfer (W.subgroupOf_isOpen V hV)
        ((continuous_abelianizationProPMk p G V).comp
          (Subgroup.subgroupOfContinuousMulEquivOfLe hVW).continuous)⟩
  let Tab := TopologicalAbelianization.lift T
  maximalProPQuotient.lift (isProP_maximalProPQuotient (p := p) (G := TopologicalAbelianization V))
    Tab.toMonoidHom Tab.continuous

/-- On the class of `w : W`, `abelianizationProPTransferLe` is the transfer of the canonical map
`V.subgroupOf W → V^ab(p)` at `w`. -/
@[simp]
theorem abelianizationProPTransferLe_mk (w : W) :
    abelianizationProPTransferLe p hVW hV (abelianizationProPMk p G W w) =
      MonoidHom.transfer ((abelianizationProPMk p G V).comp
        (Subgroup.subgroupOfEquivOfLe hVW).toMonoidHom) w := by
  simp [abelianizationProPTransferLe, abelianizationProPMk_apply]

/-- The transfer `W^ab(p) →* V^ab(p)` is continuous. -/
theorem continuous_abelianizationProPTransferLe :
    Continuous (abelianizationProPTransferLe p hVW hV) := by
  have : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  exact maximalProPQuotient.continuous_lift _ _ _

/-- On the class of `w : W`, `abelianizationProPTransferLe` is the transfer of the group `W` to
its own class module `(V.subgroupOf W)^ab(p)`, read in `V^ab(p)` through the change of group
`abelianizationProPSubgroupOfEquiv`. This is how the statements about
`abelianizationProPTransfer` for the group `W` apply to it. -/
theorem abelianizationProPTransferLe_mk_eq_subgroupOfEquiv (w : W) :
    abelianizationProPTransferLe p hVW hV (abelianizationProPMk p G W w) =
      abelianizationProPSubgroupOfEquiv p hVW
        (abelianizationProPTransfer p W (V.subgroupOf W) w) := by
  rw [abelianizationProPTransferLe_mk, abelianizationProPTransfer_def,
    ← ContinuousMulEquiv.coe_toMulEquiv, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.comp_apply,
    ← MonoidHom.transfer_comp]
  congr 2
  ext ⟨w, hw⟩
  exact (abelianizationProPSubgroupOfEquiv_mk p hVW w hw).symm

/-- For `V` and `W` normal in `G`, the transfer `W^ab(p) →* V^ab(p)` is equivariant along the
quotient map `G ⧸ V → G ⧸ W`: transfer is natural under the conjugation by `g`, which preserves
both `W` and `V`. -/
@[simp]
theorem abelianizationProPTransferLe_smul [V.Normal] [W.Normal] (q : G ⧸ V)
    (x : abelianizationProP p G W) :
    abelianizationProPTransferLe p hVW hV (QuotientGroup.mapOfLE hVW q • x) =
      q • abelianizationProPTransferLe p hVW hV x := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨w, rfl⟩ := abelianizationProPMk_surjective p G W x
    rw [QuotientGroup.mapOfLE_mk, abelianizationProPMk_conj,
      abelianizationProPTransferLe_mk, abelianizationProPTransferLe_mk]
    set φ := (abelianizationProPMk p G V).comp (Subgroup.subgroupOfEquivOfLe hVW).toMonoidHom
    let ψ := (MulDistribMulAction.toMonoidHom (abelianizationProP p G V) (g : G ⧸ V)).comp φ
    have he : (V.subgroupOf W).map (MulAut.conjNormal g : W ≃* W).toMonoidHom = V.subgroupOf W := by
      ext x
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [MulAut.conjNormal_symm_apply]
      exact ⟨fun h ↦ by simpa [mul_assoc] using ‹V.Normal›.conj_mem _ h g,
        fun h ↦ by simpa using ‹V.Normal›.conj_mem _ h g⁻¹⟩
    have hφ : ∀ v : V.subgroupOf W, φ ⟨(MulAut.conjNormal g : W ≃* W) v,
        he.le (Subgroup.mem_map_of_mem _ v.2)⟩ = ψ v := by
      intro v
      simp only [φ, ψ, MonoidHom.comp_apply, MulDistribMulAction.toMonoidHom_apply,
        abelianizationProPMk_conj]
      congr 1
    -- Naturality of transfer under the conjugation, then `transfer_comp` for the action of `g`.
    rw [MonoidHom.transfer_apply_of_mulEquiv ψ (MulAut.conjNormal g) he φ hφ w,
      MonoidHom.transfer_comp]
    rfl

/-- **The transfer `W^ab(p) → V^ab(p)` is injective** under `scd_p G ≤ 2`: this is
`abelianizationProPTransfer_eq_one_iff` for the group `W`, whose strict dimension is at most
that of `G`. -/
theorem abelianizationProPTransferLe_injective (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) :
    Function.Injective (abelianizationProPTransferLe p hVW hV) := by
  have hW : IsOpen (W : Set G) := Subgroup.isOpen_mono hVW hV
  have : CompactSpace W := isCompact_iff_compactSpace.mp (W.isClosed_of_isOpen hW).isCompact
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨w, rfl⟩ := abelianizationProPMk_surjective p G W x
  rw [abelianizationProPTransferLe_mk_eq_subgroupOfEquiv,
    map_eq_one_iff _ (abelianizationProPSubgroupOfEquiv p hVW).injective] at hx
  rw [abelianizationProPMk_apply]
  exact (abelianizationProPTransfer_eq_one_iff hp
    ((strictCohomologicalDimensionAt_le_of_isClosed (W.isClosed_of_isOpen hW)).trans h)
    (W.subgroupOf_isOpen V hV) w).1 hx

/-- **The image of the transfer `W^ab(p) → V^ab(p)`** under `scd_p G ≤ 2` and for `V` normal in
`G` is the subgroup of invariants of the image `W.map (mk' V)` of `W` in `G ⧸ V`. This is
`abelianizationProPTransfer_range` for the group `W`, carried to `G ⧸ V` by the change of
group. -/
theorem abelianizationProPTransferLe_range [V.Normal] (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) :
    (abelianizationProPTransferLe p hVW hV).range =
      FixedPoints.subgroup (W.map (QuotientGroup.mk' V)) (abelianizationProP p G V) := by
  have hW : IsOpen (W : Set G) := Subgroup.isOpen_mono hVW hV
  have : CompactSpace W := isCompact_iff_compactSpace.mp (W.isClosed_of_isOpen hW).isCompact
  have hrange := abelianizationProPTransfer_range hp
    ((strictCohomologicalDimensionAt_le_of_isClosed (W.isClosed_of_isOpen hW)).trans h)
    (W.subgroupOf_isOpen V hV)
  set E := abelianizationProPSubgroupOfEquiv p hVW
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ := abelianizationProPMk_surjective p G W x
    have hw : abelianizationProPTransfer p W (V.subgroupOf W) w ∈
        FixedPoints.subgroup (W ⧸ V.subgroupOf W) _ := hrange ▸ ⟨w, rfl⟩
    rw [FixedPoints.mem_subgroup] at hw ⊢
    intro s
    obtain ⟨q, rfl⟩ := (quotientSubgroupOfEquivMap V W hV).surjective s
    rw [abelianizationProPTransferLe_mk_eq_subgroupOfEquiv, Subgroup.smul_def,
      ← abelianizationProPSubgroupOfEquiv_smul, hw q]
  · intro hy
    obtain ⟨x, rfl⟩ := E.surjective y
    have hx : x ∈ FixedPoints.subgroup (W ⧸ V.subgroupOf W) _ := by
      rw [FixedPoints.mem_subgroup]
      intro q
      apply E.injective
      rw [abelianizationProPSubgroupOfEquiv_smul p hVW hV]
      exact (FixedPoints.mem_subgroup _ _ _).1 hy _
    rw [← hrange] at hx
    obtain ⟨w, rfl⟩ := hx
    exact ⟨abelianizationProPMk p G W w,
      abelianizationProPTransferLe_mk_eq_subgroupOfEquiv p hVW hV w⟩

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
/-- On the class in `W^ab(p)` of an element `v` of `V`, the transfer `W^ab(p) → V^ab(p)` is the
norm of the image `W.map (mk' V)` of `W` in `G ⧸ V`: `Ver_{W→V} [v] = ∏ s, s • [v]`. So the
transfer after the map `V^ab(p) → W^ab(p)` induced by the inclusion is the norm of `W ⧸ V`. -/
theorem abelianizationProPTransferLe_mk_inclusion [V.Normal] (v : V) :
    letI := Fintype.ofFinite (W.map (QuotientGroup.mk' V))
    abelianizationProPTransferLe p hVW hV (abelianizationProPMk p G W (Subgroup.inclusion hVW v)) =
      ∏ s : W.map (QuotientGroup.mk' V), (s : G ⧸ V) • abelianizationProPMk p G V v := by
  let := Fintype.ofFinite (W.map (QuotientGroup.mk' V))
  have hv : Subgroup.inclusion hVW v ∈ V.subgroupOf W := v.2
  -- The inclusion and the corresponding element of `V.subgroupOf W` have definitionally equal
  -- carriers; there is no separate inclusion map between these two presentations to rewrite.
  have hinclusion : Subgroup.inclusion hVW v =
      ((⟨Subgroup.inclusion hVW v, hv⟩ : V.subgroupOf W) : W) := rfl
  rw [abelianizationProPTransferLe_mk_eq_subgroupOfEquiv]
  rw [hinclusion, abelianizationProPTransfer_apply_of_mem, map_prod]
  refine Fintype.prod_equiv (quotientSubgroupOfEquivMap V W hV).toEquiv _ _ fun q ↦ ?_
  rw [abelianizationProPSubgroupOfEquiv_smul p hVW hV, abelianizationProPSubgroupOfEquiv_mk]
  -- The element `⟨inclusion v, hv⟩` of `V` is `v` by structure eta.
  rfl

section Inflation

variable [V.Normal] [W.Normal]

/-- The equivariance of `abelianizationProPTransferLe` on the additive coefficient modules: the
compatibility under which it pairs with `G ⧸ V → G ⧸ W` on explicit cohomology. -/
theorem abelianizationProPTransferLe_toAdditive_smul (q : G ⧸ V)
    (x : Additive (abelianizationProP p G W)) :
    (abelianizationProPTransferLe p hVW hV).toAdditive (QuotientGroup.mapOfLE hVW q • x) =
      q • (abelianizationProPTransferLe p hVW hV).toAdditive x :=
  congrArg Additive.ofMul (abelianizationProPTransferLe_smul p hVW hV q x.toMul)

/-- NSW's map `i : H¹(G ⧸ W, W^ab(p)) → H¹(G ⧸ V, V^ab(p))` of (3.6.1)(ii): the compatible-pair
pullback along the quotient map `G ⧸ V → G ⧸ W` and the transfer `W^ab(p) → V^ab(p)`. -/
noncomputable def abelianizationProPInfl1 :
    H1 (G ⧸ W) (Additive (abelianizationProP p G W)) →+
      H1 (G ⧸ V) (Additive (abelianizationProP p G V)) :=
  explicitMap1 (G ⧸ W) (Additive (abelianizationProP p G W)) (G ⧸ V)
    (Additive (abelianizationProP p G V))
    ⟨QuotientGroup.mapOfLE hVW, QuotientGroup.continuous_mapOfLE hVW⟩
    (abelianizationProPTransferLe p hVW hV).toAdditive
    -- `Additive` preserves the topology, but the named continuity theorem uses the multiplicative
    -- presentation, so make the expected additive presentation explicit.
    (by
      change Continuous (abelianizationProPTransferLe p hVW hV).toAdditive
      exact continuous_abelianizationProPTransferLe p hVW hV)
    (abelianizationProPTransferLe_toAdditive_smul p hVW hV)

/-- `abelianizationProPInfl1` is `explicitMap1` along its compatible pair. -/
theorem abelianizationProPInfl1_def :
    abelianizationProPInfl1 p hVW hV =
      explicitMap1 (G ⧸ W) (Additive (abelianizationProP p G W)) (G ⧸ V)
        (Additive (abelianizationProP p G V))
        ⟨QuotientGroup.mapOfLE hVW, QuotientGroup.continuous_mapOfLE hVW⟩
        (abelianizationProPTransferLe p hVW hV).toAdditive
        -- Match the additive presentation used by `abelianizationProPInfl1`.
        (by
          change Continuous (abelianizationProPTransferLe p hVW hV).toAdditive
          exact continuous_abelianizationProPTransferLe p hVW hV)
        (abelianizationProPTransferLe_toAdditive_smul p hVW hV) :=
  (rfl)

/-- NSW's map `i : H²(G ⧸ W, W^ab(p)) → H²(G ⧸ V, V^ab(p))` of (3.6.1)(ii): the compatible-pair
pullback along the quotient map `G ⧸ V → G ⧸ W` and the transfer `W^ab(p) → V^ab(p)`. -/
noncomputable def abelianizationProPInfl2 :
    H2 (G ⧸ W) (Additive (abelianizationProP p G W)) →+
      H2 (G ⧸ V) (Additive (abelianizationProP p G V)) :=
  explicitMap2 (G ⧸ W) (Additive (abelianizationProP p G W)) (G ⧸ V)
    (Additive (abelianizationProP p G V))
    ⟨QuotientGroup.mapOfLE hVW, QuotientGroup.continuous_mapOfLE hVW⟩
    (abelianizationProPTransferLe p hVW hV).toAdditive
    -- `Additive` preserves the topology, but the named continuity theorem uses the multiplicative
    -- presentation, so make the expected additive presentation explicit.
    (by
      change Continuous (abelianizationProPTransferLe p hVW hV).toAdditive
      exact continuous_abelianizationProPTransferLe p hVW hV)
    (abelianizationProPTransferLe_toAdditive_smul p hVW hV)

/-- `abelianizationProPInfl2` is `explicitMap2` along its compatible pair. -/
theorem abelianizationProPInfl2_def :
    abelianizationProPInfl2 p hVW hV =
      explicitMap2 (G ⧸ W) (Additive (abelianizationProP p G W)) (G ⧸ V)
        (Additive (abelianizationProP p G V))
        ⟨QuotientGroup.mapOfLE hVW, QuotientGroup.continuous_mapOfLE hVW⟩
        (abelianizationProPTransferLe p hVW hV).toAdditive
        -- Match the additive presentation used by `abelianizationProPInfl2`.
        (by
          change Continuous (abelianizationProPTransferLe p hVW hV).toAdditive
          exact continuous_abelianizationProPTransferLe p hVW hV)
        (abelianizationProPTransferLe_toAdditive_smul p hVW hV) :=
  (rfl)

/-- Under `scd_p G ≤ 2`, the transfer `W^ab(p) → V^ab(p)` as an additive equivalence onto the
invariants of `W.map (mk' V)`. -/
private noncomputable def transferLeFixedPointsEquiv (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) :
    Additive (abelianizationProP p G W) ≃+
      FixedPoints.addSubgroup (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V)) :=
  AddEquiv.ofBijective ((abelianizationProPTransferLe p hVW hV).toAdditive.codRestrict _
    fun x ↦ (FixedPoints.mem_addSubgroup _ _ _).2 fun n ↦ congrArg Additive.ofMul
      ((FixedPoints.mem_subgroup _ _ _).1
        ((abelianizationProPTransferLe_range p hVW hV hp h).le ⟨x.toMul, rfl⟩) n))
    ⟨fun x y hxy ↦ Additive.toMul.injective (abelianizationProPTransferLe_injective p hVW hV hp h
        (Additive.ofMul.injective (congrArg Subtype.val hxy))),
      fun y ↦ by
        obtain ⟨x, hx⟩ := (abelianizationProPTransferLe_range p hVW hV hp h).ge
          ((FixedPoints.mem_subgroup _ _ _).2 fun n ↦
            congrArg Additive.toMul ((FixedPoints.mem_addSubgroup _ _ _).1 y.2 n))
        exact ⟨Additive.ofMul x, Subtype.ext (congrArg Additive.ofMul hx)⟩⟩

omit [W.Normal] in
private theorem coe_transferLeFixedPointsEquiv (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) (x : Additive (abelianizationProP p G W)) :
    (transferLeFixedPointsEquiv p hVW hV hp h x : Additive (abelianizationProP p G V)) =
      (abelianizationProPTransferLe p hVW hV).toAdditive x :=
  (rfl)

/-- The equivalence onto the invariants intertwines the action of `G ⧸ W` with that of
`(G ⧸ V) ⧸ W.map (mk' V)`, the two quotients being identified by the third isomorphism
theorem. -/
private theorem transferLeFixedPointsEquiv_smul (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2)
    (q : (G ⧸ V) ⧸ W.map (QuotientGroup.mk' V)) (x : Additive (abelianizationProP p G W)) :
    transferLeFixedPointsEquiv p hVW hV hp h (quotientQuotientContinuousMulEquiv V W hVW hV q • x) =
      q • transferLeFixedPointsEquiv p hVW hV hp h x := by
  induction q using QuotientGroup.induction_on with
  | H γ =>
    induction γ using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      rw [coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup,
        coe_transferLeFixedPointsEquiv, coe_transferLeFixedPointsEquiv,
        quotientQuotientContinuousMulEquiv_mk, ← QuotientGroup.mapOfLE_mk hVW,
        abelianizationProPTransferLe_toAdditive_smul]

omit [W.Normal] in
/-- The equivalence onto the invariants is continuous in both directions: it is a continuous
bijection from the compact space `W^ab(p)` to the Hausdorff space of invariants. -/
private theorem continuous_transferLeFixedPointsEquiv (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) :
    Continuous (transferLeFixedPointsEquiv p hVW hV hp h) ∧
      Continuous (transferLeFixedPointsEquiv p hVW hV hp h).symm := by
  have : CompactSpace W := isCompact_iff_compactSpace.mp
    (W.isClosed_of_isOpen (Subgroup.isOpen_mono hVW hV)).isCompact
  have : T2Space (Additive (abelianizationProP p G V)) :=
    inferInstanceAs (T2Space (abelianizationProP p G V))
  have he : Continuous (transferLeFixedPointsEquiv p hVW hV hp h) :=
    (continuous_abelianizationProPTransferLe p hVW hV).subtype_mk _
  exact ⟨he, he.continuous_symm_of_equiv_compact_to_t2
    (f := (transferLeFixedPointsEquiv p hVW hV hp h).toEquiv)⟩

include hV in
omit [CompactSpace G] [TotallyDisconnectedSpace G] [V.FiniteIndex] in
/-- The discrete group `(G ⧸ V) ⧸ W.map (mk' V)` acts continuously on the invariants of
`W.map (mk' V)` in `V^ab(p)`, which is what inflation from it needs. -/
private theorem continuousSMul_quotient_fixedPoints :
    ContinuousSMul ((G ⧸ V) ⧸ W.map (QuotientGroup.mk' V))
      (FixedPoints.addSubgroup (W.map (QuotientGroup.mk' V))
        (Additive (abelianizationProP p G V))) := by
  have : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  refine ⟨continuous_prod_of_discrete_left.2 fun q ↦ ?_⟩
  induction q using QuotientGroup.induction_on with
  | H γ =>
    refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
    simp_rw [Function.comp_def, coe_quotient_smul_fixedPoints_addSubgroup]
    exact (continuous_const_smul γ).comp continuous_subtype_val

/-- Under `scd_p G ≤ 2`, `abelianizationProPInfl1` is inflation from
`(G ⧸ V) ⧸ W.map (mk' V) ≅ G ⧸ W` with the invariants as coefficients, after the isomorphism
induced by the transfer onto the invariants; so it is injective with image the kernel of
restriction to `W.map (mk' V)`. -/
private theorem abelianizationProPInfl1_injective_and_range (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) :
    Function.Injective (abelianizationProPInfl1 p hVW hV) ∧
      (abelianizationProPInfl1 p hVW hV).range =
        (explicitRes1 (G ⧸ V) (Additive (abelianizationProP p G V))
          (W.map (QuotientGroup.mk' V))).ker := by
  have := continuousSMul_quotient_fixedPoints p (W := W) hV
  set N := W.map (QuotientGroup.mk' V)
  set M := Additive (abelianizationProP p G V)
  -- The isomorphism `j : H¹(G ⧸ W, W^ab(p)) ≃ H¹((G ⧸ V) ⧸ N, M ^ N)` along the third isomorphism
  -- theorem and the transfer onto the invariants.
  let e := transferLeFixedPointsEquiv p hVW hV hp h
  have he := continuous_transferLeFixedPointsEquiv p hVW hV hp h
  let j := explicitMap1Equiv (G ⧸ W) (Additive (abelianizationProP p G W)) ((G ⧸ V) ⧸ N)
    (FixedPoints.addSubgroup N M) (quotientQuotientContinuousMulEquiv V W hVW hV) e he.1 he.2
    (transferLeFixedPointsEquiv_smul p hVW hV hp h)
  -- `i` is inflation after `j`: the two pulled-back cocycles agree at every `g : G`.
  have key (x) : abelianizationProPInfl1 p hVW hV x = explicitInfl1 (G ⧸ V) M N (j x) := by
    induction x using QuotientAddGroup.induction_on with
    | _ c =>
      -- `explicitMap1_mk` is applied as a term: the continuity argument of `j`'s pullback is
      -- stated at the `AddEquiv` coercion, so the rewrite would produce an ill-typed motive.
      rw [explicitMap1Equiv_apply]
      refine (explicitMap1_mk _ _ _ _ _ _ _ _ c).trans (Eq.trans ?_
        (congrArg (explicitInfl1 (G ⧸ V) M N) (explicitMap1_mk _ _ _ _ _ _ _ _ c).symm))
      rw [explicitInfl1_mk]
      congr 1
      apply Subtype.ext
      funext γ
      induction γ using QuotientGroup.induction_on with
      | H g =>
        rw [cocyclesMap1_apply, cocyclesMap1_apply]
        refine Eq.trans ?_ (congrArg (FixedPoints.addSubgroup N M).subtype
          (cocyclesMap1_apply (G ⧸ W) (Additive (abelianizationProP p G W)) ((G ⧸ V) ⧸ N)
            (FixedPoints.addSubgroup N M) _ e.toAddMonoidHom he.1
              (transferLeFixedPointsEquiv_smul p hVW hV hp h) c _)).symm
        rw [AddSubgroup.coe_subtype, AddEquiv.coe_toAddMonoidHom, coe_transferLeFixedPointsEquiv]
        exact congrArg _ (congrArg _ ((quotientQuotientContinuousMulEquiv_mk V W hVW hV g).trans
          (QuotientGroup.mapOfLE_mk hVW g).symm).symm)
  -- Inflation is injective with image the kernel of restriction, and `j` is bijective.
  refine ⟨fun x y hxy ↦ j.injective (explicitInfl1_injective _ _ _ (by rw [← key, ← key, hxy])),
    ?_⟩
  rw [← explicitInfRes_exact]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨j x, (key x).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨j.symm z, by rw [key, j.apply_symm_apply]⟩

/-- **The map `i` is injective in degree one** under `scd_p G ≤ 2`, NSW (1.6.7) for the pair
`V ≤ W`: it is inflation, after the isomorphism of coefficients given by the transfer onto the
invariants. -/
theorem abelianizationProPInfl1_injective (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) :
    Function.Injective (abelianizationProPInfl1 p hVW hV) :=
  (abelianizationProPInfl1_injective_and_range p hVW hV hp h).1

/-- **The image of `i` in degree one** under `scd_p G ≤ 2` is the kernel of restriction to the
image `W.map (mk' V)` of `W` in `G ⧸ V`, NSW (1.6.7) for the pair `V ≤ W`. -/
theorem abelianizationProPInfl1_exact (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) :
    (abelianizationProPInfl1 p hVW hV).range =
      (explicitRes1 (G ⧸ V) (Additive (abelianizationProP p G V))
        (W.map (QuotientGroup.mk' V))).ker :=
  (abelianizationProPInfl1_injective_and_range p hVW hV hp h).2

/-- Under `scd_p G ≤ 2` and the vanishing of `H¹(W.map (mk' V), V^ab(p))`,
`abelianizationProPInfl2` is inflation from `(G ⧸ V) ⧸ W.map (mk' V) ≅ G ⧸ W` with the invariants
as coefficients, after the isomorphism induced by the transfer onto the invariants; so it is
injective with image the kernel of restriction to `W.map (mk' V)`. -/
private theorem abelianizationProPInfl2_injective_and_range (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2)
    [Subsingleton (H1 (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V)))] :
    Function.Injective (abelianizationProPInfl2 p hVW hV) ∧
      (abelianizationProPInfl2 p hVW hV).range =
        (explicitRes2 (G ⧸ V) (Additive (abelianizationProP p G V))
          (W.map (QuotientGroup.mk' V))).ker := by
  have : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  have := continuousSMul_quotient_fixedPoints p (W := W) hV
  set N := W.map (QuotientGroup.mk' V)
  set M := Additive (abelianizationProP p G V)
  -- The isomorphism `j : H²(G ⧸ W, W^ab(p)) ≃ H²((G ⧸ V) ⧸ N, M ^ N)` along the third isomorphism
  -- theorem and the transfer onto the invariants.
  let e := transferLeFixedPointsEquiv p hVW hV hp h
  have he := continuous_transferLeFixedPointsEquiv p hVW hV hp h
  let j := explicitMap2Equiv (G ⧸ W) (Additive (abelianizationProP p G W)) ((G ⧸ V) ⧸ N)
    (FixedPoints.addSubgroup N M) (quotientQuotientContinuousMulEquiv V W hVW hV) e he.1 he.2
    (transferLeFixedPointsEquiv_smul p hVW hV hp h)
  -- `i` is inflation after `j`: the two pulled-back cocycles agree at every pair from `G`.
  have key (x) : abelianizationProPInfl2 p hVW hV x = explicitInfl2 (G ⧸ V) M N (j x) := by
    induction x using QuotientAddGroup.induction_on with
    | _ c =>
      -- `explicitMap2_mk` is applied as a term: the continuity argument of `j`'s pullback is
      -- stated at the `AddEquiv` coercion, so the rewrite would produce an ill-typed motive.
      rw [explicitMap2Equiv_apply]
      refine (explicitMap2_mk _ _ _ _ _ _ _ _ c).trans (Eq.trans ?_
        (congrArg (explicitInfl2 (G ⧸ V) M N) (explicitMap2_mk _ _ _ _ _ _ _ _ c).symm))
      rw [explicitInfl2_mk]
      congr 1
      apply Subtype.ext
      funext ⟨γ, δ⟩
      induction γ using QuotientGroup.induction_on with
      | H g =>
        induction δ using QuotientGroup.induction_on with
        | H g' =>
          rw [cocyclesMap2_apply, cocyclesMap2_apply]
          refine Eq.trans ?_ (congrArg (FixedPoints.addSubgroup N M).subtype
            (cocyclesMap2_apply (G ⧸ W) (Additive (abelianizationProP p G W)) ((G ⧸ V) ⧸ N)
              (FixedPoints.addSubgroup N M) _ e.toAddMonoidHom he.1
                (transferLeFixedPointsEquiv_smul p hVW hV hp h) c _ _)).symm
          rw [AddSubgroup.coe_subtype, AddEquiv.coe_toAddMonoidHom]
          rw [coe_transferLeFixedPointsEquiv]
          exact congrArg _ (congrArg _ (Prod.ext
            ((quotientQuotientContinuousMulEquiv_mk V W hVW hV g).trans
              (QuotientGroup.mapOfLE_mk hVW g).symm).symm
            ((quotientQuotientContinuousMulEquiv_mk V W hVW hV g').trans
              (QuotientGroup.mapOfLE_mk hVW g').symm).symm))
  -- Inflation is injective with image the kernel of restriction when `H¹(N, M)` vanishes, and
  -- `j` is bijective.
  refine ⟨fun x y hxy ↦ j.injective (explicitInfl2_injective _ _ _ (by rw [← key, ← key, hxy])),
    ?_⟩
  rw [← explicitInfRes2_exact _ _ _ (isOpen_discrete _)]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨j x, (key x).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨j.symm z, by rw [key, j.apply_symm_apply]⟩

/-- **The map `i` is injective in degree two** under `scd_p G ≤ 2`, when
`H¹(W.map (mk' V), V^ab(p))` vanishes, NSW (1.6.7) for the pair `V ≤ W`: it is inflation, after
the isomorphism of coefficients given by the transfer onto the invariants. -/
theorem abelianizationProPInfl2_injective (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2)
    [Subsingleton (H1 (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V)))] :
    Function.Injective (abelianizationProPInfl2 p hVW hV) :=
  (abelianizationProPInfl2_injective_and_range p hVW hV hp h).1

/-- **The image of `i` in degree two** under `scd_p G ≤ 2`, when `H¹(W.map (mk' V), V^ab(p))`
vanishes, is the kernel of restriction to the image `W.map (mk' V)` of `W` in `G ⧸ V`, NSW (1.6.7)
for the pair `V ≤ W`. -/
theorem abelianizationProPInfl2_exact (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2)
    [Subsingleton (H1 (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V)))] :
    (abelianizationProPInfl2 p hVW hV).range =
      (explicitRes2 (G ⧸ V) (Additive (abelianizationProP p G V))
        (W.map (QuotientGroup.mk' V))).ker :=
  (abelianizationProPInfl2_injective_and_range p hVW hV hp h).2

/-- The quotient `a.out / (mapOfLE a).out` of the representative of `a : G ⧸ V` by that of its
image in `G ⧸ W`, an element of `W`. -/
private noncomputable def outDivOut (a : G ⧸ V) : W :=
  ⟨a.out / (QuotientGroup.mapOfLE hVW a).out, by
    rw [← QuotientGroup.eq_iff_div_mem, QuotientGroup.out_eq', ← QuotientGroup.mapOfLE_mk hVW,
      QuotientGroup.out_eq']⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] [V.FiniteIndex] in
/-- The defect `a.out * b.out * (a * b).out⁻¹` of the representatives of `G ⧸ V`, read in
`W^ab(p)`, is the factor set of `G ⧸ W` at the images of `a` and `b` corrected by the coboundary of
`outDivOut`. -/
private theorem abelianizationProPMk_inclusion_out_mul_out_mul_inv (a b : G ⧸ V) :
    abelianizationProPMk p G W (Subgroup.inclusion hVW
      ⟨a.out * b.out * (a * b).out⁻¹, QuotientGroup.out_mul_out_mul_inv_mem V a b⟩) =
      abelianizationProPMk p G W (outDivOut hVW a) *
        (QuotientGroup.mapOfLE hVW a • abelianizationProPMk p G W (outDivOut hVW b)) *
        abelianizationProPMk p G W
          ⟨_, QuotientGroup.out_mul_out_mul_inv_mem W (QuotientGroup.mapOfLE hVW a)
            (QuotientGroup.mapOfLE hVW b)⟩ *
        (abelianizationProPMk p G W (outDivOut hVW (a * b)))⁻¹ := by
  rw [← QuotientGroup.out_eq' (QuotientGroup.mapOfLE hVW a), abelianizationProPMk_conj,
    QuotientGroup.out_eq', ← map_mul, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  ext
  simp only [outDivOut, div_eq_mul_inv, map_mul, Subgroup.coe_inclusion, Subgroup.coe_mul,
    MulAut.conjNormal_apply, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
  group

/-- **NSW (3.6.1)(ii).** The map `i` carries the class `u_{G/W}(p)` to `(W : V) • u_{G/V}(p)`.
The inflation of `u_{G/W}(p)` to `G ⧸ V` and the push-forward of `u_{G/V}(p)` along
`V^ab(p) → W^ab(p)` differ by a coboundary, and the transfer after `V^ab(p) → W^ab(p)` is the norm
of `W.map (mk' V)`, which acts on `H²(G ⧸ V, V^ab(p))` as multiplication by its order `(W : V)`.
No hypothesis on the cohomological dimension of `G` is needed. -/
theorem abelianizationProPInfl2_class :
    abelianizationProPInfl2 p hVW hV
        (abelianizationProPClass p G W (Subgroup.isOpen_mono hVW hV)) =
      V.relIndex W • abelianizationProPClass p G V hV := by
  have : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  set Δ := W.map (QuotientGroup.mk' V)
  set M := Additive (abelianizationProP p G V)
  let : Fintype Δ := Fintype.ofFinite Δ
  -- The norm of `Δ`, an equivariant endomorphism of `V^ab(p)` because `Δ` is normal, multiplies
  -- `u_{G/V}(p)` by `#Δ = (W : V)`.
  have hcard : Nat.card Δ = V.relIndex W :=
    (Nat.card_congr (quotientSubgroupOfEquivMap V W hV).toEquiv).symm
  rw [← hcard, ← explicitCoeff2_eq_card_nsmul (G ⧸ V) M Δ,
    abelianizationProPInfl2_def, abelianizationProPClass_def, abelianizationProPClass_def,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, explicitCoeff2_mk]
  refine (explicitMap2_mk _ _ _ _ _ _ _ _ _).trans ?_
  -- The two factor sets differ, in `W^ab(p)`, by the coboundary of `outDivOut`, so their
  -- transfers differ by the coboundary of `X`.
  rw [H2pi_eq_iff, mem_B2_iff']
  let X : G ⧸ V → M := fun a ↦ Additive.ofMul
    (abelianizationProPTransferLe p hVW hV (abelianizationProPMk p G W (outDivOut hVW a)))
  refine ⟨fun a ↦ -X a, continuous_of_discreteTopology, fun a b ↦ ?_⟩
  have h := congrArg (abelianizationProPTransferLe p hVW hV)
    (abelianizationProPMk_inclusion_out_mul_out_mul_inv p hVW a b)
  rw [abelianizationProPTransferLe_mk_inclusion, map_mul, map_mul, map_mul, map_inv,
    abelianizationProPTransferLe_smul] at h
  -- The norm of the factor set of `t` is the transfer of its defect.
  have hN : groupNormHom Δ M (abelianizationProPFactorSet p G V (a, b)) = Additive.ofMul
      (∏ s : Δ, (s : G ⧸ V) • abelianizationProPMk p G V
        ⟨a.out * b.out * (a * b).out⁻¹, QuotientGroup.out_mul_out_mul_inv_mem V a b⟩) := by
    rw [groupNormHom_apply, groupNorm_apply]
    simp only [abelianizationProPFactorSet_apply, ofMul_prod, Additive.ofMul_smul,
      Subgroup.smul_def]
  rw [Pi.sub_apply]
  refine Eq.trans ?_ (congrArg₂ (· - ·) (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ a b).symm
    (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ a b).symm)
  simp only [ContinuousMonoidHom.coe_id, id, AddMonoidHom.coe_ofClass]
  rw [hN, h]
  simp only [ContinuousMonoidHom.coe_mk, MonoidHom.toAdditive_apply_apply,
    abelianizationProPFactorSet_apply, toMul_ofMul, ofMul_mul, ofMul_inv, Additive.ofMul_smul,
    smul_neg, X]
  abel

end Inflation

end TauCeti
