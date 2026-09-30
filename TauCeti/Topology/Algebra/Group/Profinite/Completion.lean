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

The continuous finite quotients of the completion are exactly the finite quotients of `G`
(`isFiniteContinuousQuotient_iff_exists_surjective`), and the completion of a finitely generated
group is topologically finitely generated (`isTopologicallyFinitelyGenerated`). Through the
finite-quotient determinacy of topologically finitely generated profinite groups this gives the
theorem of Dixon, Formanek, Poland and Ribes: two finitely generated groups with the same finite
quotients have topologically isomorphic profinite completions
(`nonempty_continuousMulEquiv_of_forall_exists_surjective_iff`); in fact finite generation of one
of the two groups suffices.

## References

* J. D. Dixon, E. W. Formanek, J. C. Poland and L. Ribes, *Profinite completions and isomorphic
  finite quotients*, J. Pure Appl. Algebra 23 (1982), 227–231.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 3.2.
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

end ProfiniteCompletion

end TauCeti
