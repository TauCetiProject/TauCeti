/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Map
public import TauCeti.Topology.Algebra.GroupExtension.Cohomology

/-!
# Naturality of pro-`p` class-module extension classes

A continuous homomorphism `f : G → H` carrying a closed normal subgroup `V` into `W`
induces a map `Vᵃᵇ(p) → Wᵃᵇ(p)`. If its map on quotients is a continuous isomorphism
`e : G/V ≃ H/W`, this is a coefficient map over `H/W`, with the source conjugation action
transported along `e`.

The induced coefficient map carries the class of the source extension, with its quotient
relabelled by `e`, to the class of the target extension. Thus it is onto on second
cohomology whenever the target extension class generates. Neither the ambient map nor
the coefficient map needs to be surjective. This is useful for detecting the cohomological
image of relation-group maps arising from free profinite presentations.

The comparison uses `abelianizationProPExtensionMap` and
`ProfiniteGroupExtension.contCohomologyClass_map_eq_of_continuous_monoidHom`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (3.6.2) and the proofs of (7.4.1) and (7.4.2)(i).
-/

public noncomputable section

namespace TauCeti

open ContCohomology

universe u

variable (p : ℕ) {G H : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {V : Subgroup G} {W : Subgroup H} [V.Normal] [W.Normal]
  (f : G →* H) (hf : Continuous f) (hVW : V ≤ W.comap f)
  (e : G ⧸ V ≃ₜ* H ⧸ W) (he : ∀ g : G, e (QuotientGroup.mk g) = QuotientGroup.mk (f g))

/-- The induced map on pro-`p` class modules, equivariant over the target quotient.
The source action is conjugation transported along the inverse quotient isomorphism. -/
def abelianizationProPMapEquivariant :
    letI := MulDistribMulAction.compHom (abelianizationProP p G V) e.symm.toMulEquiv.toMonoidHom
    abelianizationProP p G V →*[H ⧸ W] abelianizationProP p H W := by
  letI := MulDistribMulAction.compHom (abelianizationProP p G V) e.symm.toMulEquiv.toMonoidHom
  refine { abelianizationProPMap p f hf hVW with map_smul' := ?_ }
  intro q a
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm q)
  have hq : (f g : H ⧸ W) = q := (he g).symm.trans (by rw [hg]; exact e.apply_symm_apply q)
  -- The transported action is defined by precomposition with e⁻¹; expose this
  -- action once, then use the canonical conjugation-equivariance theorem.
  change abelianizationProPMap p f hf hVW (e.symm q • a) = q • _
  rw [← hg, abelianizationProPMap_smul, hq]
  rfl

/-- The equivariant class-module map has the canonical induced map as its underlying function. -/
@[simp]
theorem abelianizationProPMapEquivariant_apply (a : abelianizationProP p G V) :
    abelianizationProPMapEquivariant p f hf hVW e he a = abelianizationProPMap p f hf hVW a :=
  (rfl)

/-- The induced equivariant map of pro-`p` class modules is continuous. -/
theorem continuous_abelianizationProPMapEquivariant :
    Continuous (abelianizationProPMapEquivariant p f hf hVW e he) :=
  (continuous_abelianizationProPMap p f hf hVW).congr
    (fun a ↦ (abelianizationProPMapEquivariant_apply p f hf hVW e he a).symm)

variable [CompactSpace G] [TotallyDisconnectedSpace G] [IsClosed (V : Set G)]
  [CompactSpace H] [TotallyDisconnectedSpace H] [IsClosed (W : Set H)]

/-- The canonical coefficient map carries the source extension class to the target
extension class, after identifying their quotients by the induced isomorphism. -/
theorem contCohomologyClass_map_abelianizationProPMapEquivariant :
    letI := MulDistribMulAction.compHom (abelianizationProP p G V) e.symm.toMulEquiv.toMonoidHom
    letI := MulAction.continuousSMul_compHom (X := abelianizationProP p G V)
      (f := e.symm.toMulEquiv.toMonoidHom) e.symm.continuous
    let X := (abelianizationProPProfiniteExtension p G V).relabelQuotient e
      (fun q a ↦ congrArg (fun r : G ⧸ V ↦ r • a) (e.symm_apply_apply q))
    (X.map (abelianizationProPMapEquivariant p f hf hVW e he)
      (continuous_abelianizationProPMapEquivariant p f hf hVW e he)).contCohomologyClass =
        (abelianizationProPProfiniteExtension p H W).contCohomologyClass := by
  let := MulDistribMulAction.compHom (abelianizationProP p G V) e.symm.toMulEquiv.toMonoidHom
  let := MulAction.continuousSMul_compHom (X := abelianizationProP p G V)
    (f := e.symm.toMulEquiv.toMonoidHom) e.symm.continuous
  let X := (abelianizationProPProfiniteExtension p G V).relabelQuotient e
    (fun q a ↦ congrArg (fun r : G ⧸ V ↦ r • a) (e.symm_apply_apply q))
  let Y := abelianizationProPProfiniteExtension p H W
  let κ := abelianizationProPMapEquivariant p f hf hVW e he
  let ψ := abelianizationProPExtensionMap p f hf hVW
  apply X.contCohomologyClass_map_eq_of_continuous_monoidHom κ
    (continuous_abelianizationProPMapEquivariant p f hf hVW e he) Y ψ.toMonoidHom ψ.continuous
  · apply MonoidHom.ext
    intro a
    -- Read the equivariant homomorphism as a function so its apply lemma, rather
    -- than the hidden monoid-hom projection, specifies the coefficient map.
    change ψ (X.toGroupExtension.inl a) = Y.toGroupExtension.inl (κ a)
    obtain ⟨v, rfl⟩ := abelianizationProPMk_surjective p G V a
    simp [X, Y, κ, ψ]
  · apply MonoidHom.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    -- Evaluate the bundled map at a quotient representative; otherwise the
    -- monoid-hom projection hides its characteristic evaluation lemma.
    change (abelianizationProPExtension p H W).rightHom
      (ψ (QuotientGroup.mk g)) = X.toGroupExtension.rightHom (QuotientGroup.mk g)
    rw [abelianizationProPExtensionMap_mk,
      ProfiniteGroupExtension.relabelQuotient_rightHom_apply]
    simpa only [abelianizationProPExtension_rightHom, QuotientGroup.mapOfLE_mk] using (he g).symm

/-- If the target class-module extension class generates second cohomology, the
canonical induced class-module map is surjective on second cohomology. This does not
require surjectivity on the ambient groups or on their class modules. -/
theorem explicitCoeff2_abelianizationProPMapEquivariant_surjective
    (hgen : AddSubgroup.zmultiples
      (abelianizationProPProfiniteExtension p H W).contCohomologyClass = ⊤) :
    letI := MulDistribMulAction.compHom (abelianizationProP p G V) e.symm.toMulEquiv.toMonoidHom
    letI := MulAction.continuousSMul_compHom (X := abelianizationProP p G V)
      (f := e.symm.toMulEquiv.toMonoidHom) e.symm.continuous
    Function.Surjective (explicitCoeff2 (H ⧸ W) (Additive (abelianizationProP p G V))
      (abelianizationProPMapEquivariant p f hf hVW e he).toAdditive
      ((abelianizationProPMapEquivariant p f hf hVW e he).continuous_toAdditive
        (continuous_abelianizationProPMapEquivariant p f hf hVW e he))) := by
  let := MulDistribMulAction.compHom (abelianizationProP p G V) e.symm.toMulEquiv.toMonoidHom
  let := MulAction.continuousSMul_compHom (X := abelianizationProP p G V)
    (f := e.symm.toMulEquiv.toMonoidHom) e.symm.continuous
  let X := (abelianizationProPProfiniteExtension p G V).relabelQuotient e
    (fun q a ↦ congrArg (fun r : G ⧸ V ↦ r • a) (e.symm_apply_apply q))
  let κ := abelianizationProPMapEquivariant p f hf hVW e he
  let hc := continuous_abelianizationProPMapEquivariant p f hf hVW e he
  have hclass : (X.map κ hc).contCohomologyClass =
      (abelianizationProPProfiniteExtension p H W).contCohomologyClass :=
    contCohomologyClass_map_abelianizationProPMapEquivariant p f hf hVW e he
  rw [ProfiniteGroupExtension.contCohomologyClass_map] at hclass
  intro y
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen.ge (AddSubgroup.mem_top y))
  refine ⟨n • X.contCohomologyClass, ?_⟩
  simpa only [map_zsmul] using (congrArg (fun z ↦ n • z) hclass).trans hn

end TauCeti
