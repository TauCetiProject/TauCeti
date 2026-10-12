/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Connected
public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection
public import TauCeti.Topology.Algebra.Group.Profinite.Section
public import TauCeti.Topology.Algebra.GroupExtension.FactorSet

/-!
# Profinite extensions by a compact kernel are twisted products

A group extension `1 → M → E → G → 1` is an extension *of topological groups* when its inclusion
and its projection are continuous. This file proves that, when `E` is profinite and the kernel `M`
is compact — in the application of the extension dictionary, finite and discrete — such an
extension is the twisted product of `G` by `M` built from a continuous factor set:

* the projection has a continuous normalized set-theoretic section
  (`TauCeti.GroupExtension.exists_continuous_section`);
* the factor set that section measures is continuous
  (`TauCeti.GroupExtension.continuous_factorSet`);
* the comparison map from the twisted product back to `E` is a multiplicative equivalence and a
  homeomorphism (`TauCeti.GroupExtension.factorSetContinuousMulEquiv`), assembled into
  `TauCeti.GroupExtension.exists_continuous_factorSet`.

In the other direction `TauCeti.GroupExtension.factorSet_canonicalSection` reads a factor set back
off the twisted product it builds, through the canonical section, which is continuous by
`TauCeti.FactorSet.continuous_canonicalSection`. So the two constructions are mutually inverse up
to equivalence of extensions.

The continuous section is the only step that uses the topology of `E` in an essential way. It comes
from the continuous section of a profinite group over the quotient by a closed subgroup, applied to
the kernel, which is closed because it is compact and `E`, being profinite, is Hausdorff. Nothing
asks the kernel to be *open*: an open kernel would force `G` to be discrete, whereas the extensions
this dictionary is used on have infinite `G`.

Bundling the data, `TauCeti.ProfiniteGroupExtension G M` is an extension of `G` by `M` with
profinite total group, continuous inclusion and projection, inducing the given action of `G` on
`M`. When `G` and `M` are both profinite the twisted product of a continuous factor set is one
(`TauCeti.ProfiniteGroupExtension.ofFactorSet`); compactness of `M` alone would not do, the
twisted product being `M × G` as a space. The continuous cohomology classifying these bundled
extensions is the subject of `TauCeti/Topology/Algebra/GroupExtension/Cohomology.lean`.

## Main definitions

* `TauCeti.ProfiniteGroupExtension`: an extension of `G` by `M` with profinite total group,
  continuous inclusion and projection, inducing the given action, bundled with its total group, and
  `TauCeti.ProfiniteGroupExtension.ofFactorSet`, the twisted product of a continuous factor set
  when `G` and `M` are profinite.
* `TauCeti.GroupExtension.continuousMulEquivOfEquiv`: an equivalence of extensions with compact
  total group is a homeomorphism as soon as it is continuous, hence a `ContinuousMulEquiv`, and
  `TauCeti.GroupExtension.continuousMulEquivOfMonoidHom` is its form for a bare morphism. Neither
  assumes the group operations continuous, so neither is stated as an isomorphism of topological
  groups.
* `TauCeti.GroupExtension.factorSetContinuousMulEquiv`: the extension is the twisted product built
  from the factor set of a continuous normalized section, by a multiplicative equivalence that is a
  homeomorphism.

## Main results

* `TauCeti.GroupExtension.isClosed_ker_rightHom`: a compact kernel is a closed subgroup of a
  Hausdorff extension.
* `TauCeti.GroupExtension.exists_continuous_section`: the projection of a profinite extension with
  compact kernel has a continuous normalized section.
* `TauCeti.GroupExtension.continuous_factorSet`: the factor set of a continuous normalized section
  is continuous whenever the inclusion of the kernel is an embedding, as a compact kernel of a
  Hausdorff extension is.
* `TauCeti.GroupExtension.exists_continuous_factorSet`: **a profinite extension with compact kernel
  is the twisted product of a continuous factor set.**

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2.
* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., Prop. 2.2.2 for the continuous section over
  an arbitrary closed subgroup, of which the compact-kernel case used here is a special case.
-/

public section

namespace TauCeti.GroupExtension

universe u v w

variable {G : Type u} {M : Type v} {E : Type w}
  [Group G] [TopologicalSpace G] [Group E] [TopologicalSpace E]

/-! ### Continuous morphisms of extensions -/

section Morphism

variable [Group M] {E' : Type*} [Group E'] [TopologicalSpace E'] [CompactSpace E] [T2Space E']
  {S : GroupExtension M E G} {S' : GroupExtension M E' G}

/-- **A continuous equivalence of extensions with compact total group is a homeomorphism**, so it
is a multiplicative equivalence that is a homeomorphism. Only continuity in one direction has to be
checked: a continuous bijection from a compact space onto a Hausdorff space is a homeomorphism. No
compatibility between the group operations and the topologies is assumed, so the conclusion is a
`ContinuousMulEquiv` and not, on its own, an isomorphism of topological groups. -/
noncomputable def continuousMulEquivOfEquiv (e : S.Equiv S') (he : Continuous e) : E ≃ₜ* E' :=
  let h : E ≃ₜ E' := Continuous.homeoOfEquivCompactToT2 (f := e.toMulEquiv.toEquiv) he
  { toMulEquiv := e.toMulEquiv
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

omit [TopologicalSpace G] in
@[simp]
theorem continuousMulEquivOfEquiv_apply (e : S.Equiv S') (he : Continuous e) (x : E) :
    continuousMulEquivOfEquiv e he x = e x :=
  (rfl)

/-- **Every continuous morphism between extensions with compact total group is a multiplicative
equivalence and a homeomorphism.** Algebraically this is the five lemma,
`GroupExtension.Equiv.ofMonoidHom`; as in
`TauCeti.GroupExtension.continuousMulEquivOfEquiv`, nothing ties the group operations to the
topologies, so the conclusion is a `ContinuousMulEquiv`. -/
noncomputable def continuousMulEquivOfMonoidHom (f : E →* E') (hf : Continuous f)
    (comp_inl : f.comp S.inl = S'.inl) (rightHom_comp : S'.rightHom.comp f = S.rightHom) :
    E ≃ₜ* E' :=
  continuousMulEquivOfEquiv (GroupExtension.Equiv.ofMonoidHom f comp_inl rightHom_comp) hf

omit [TopologicalSpace G] in
@[simp]
theorem continuousMulEquivOfMonoidHom_apply (f : E →* E') (hf : Continuous f)
    (comp_inl : f.comp S.inl = S'.inl) (rightHom_comp : S'.rightHom.comp f = S.rightHom) (x : E) :
    continuousMulEquivOfMonoidHom f hf comp_inl rightHom_comp x = f x :=
  (rfl)

end Morphism

/-! ### The continuous section and its factor set -/

section ClosedKernel

variable [Group M] [TopologicalSpace M] [CompactSpace M] [T2Space E] {S : GroupExtension M E G}

omit [TopologicalSpace G] in
/-- **A compact kernel is a closed subgroup of a Hausdorff extension.** It is the continuous image
of a compact space in a Hausdorff space, so the finite kernels of the extension dictionary are
covered without a separate argument. -/
theorem isClosed_ker_rightHom (hinl : Continuous S.inl) :
    IsClosed (S.rightHom.ker : Set E) := by
  have hker : (S.rightHom.ker : Set E) = Set.range S.inl := by
    rw [← S.range_inl_eq_ker_rightHom, MonoidHom.coe_range]
  rw [hker]
  exact (hinl.isClosedEmbedding S.inl_injective).isClosed_range

end ClosedKernel

section Profinite

variable [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E]
  [Group M] [TopologicalSpace M] [CompactSpace M] {S : GroupExtension M E G}

/-- **The projection of a profinite extension with compact kernel has a continuous normalized
set-theoretic section.** The kernel is compact, hence closed, so the continuous section of a
profinite group over the quotient by a closed subgroup applies; the base is identified with that
quotient because the projection is a continuous bijection out of a compact space. -/
theorem exists_continuous_section [T2Space G] (hinl : Continuous S.inl)
    (hrh : Continuous S.rightHom) : ∃ σ : S.Section, Continuous ⇑σ ∧ σ 1 = 1 := by
  -- identify `G` with the quotient of `E` by the kernel of the projection
  set N := S.rightHom.ker
  let q : E ⧸ N ≃ G :=
    (QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective).toEquiv
  -- `quotientKerEquivOfSurjective` is `QuotientGroup.kerLift` up to the identification of the
  -- range with `G`, so on a class it is the projection by definition
  have hq : ∀ x : E, q (QuotientGroup.mk x) = S.rightHom x := fun _ => rfl
  have hqc : Continuous q :=
    (QuotientGroup.isQuotientMap_mk N).continuous_iff.2 <| by
      simpa only [Function.comp_def, hq] using hrh
  let e : (E ⧸ N) ≃ₜ G := Continuous.homeoOfEquivCompactToT2 (f := q) hqc
  have he : ∀ x : E, e (QuotientGroup.mk x) = S.rightHom x := hq
  -- pull the continuous section of `E → E ⧸ N` back along that identification
  obtain ⟨s, hs, hsec, hs₁⟩ := TauCeti.exists_continuous_section N (isClosed_ker_rightHom hinl)
  have hone : e.symm 1 = QuotientGroup.mk 1 := e.symm_apply_eq.2 (by rw [he, map_one])
  have hsec' : ∀ g : G, S.rightHom (s (e.symm g)) = g := fun g => by
    rw [← he, hsec, Homeomorph.apply_symm_apply]
  have hone' : s (e.symm 1) = 1 := by rw [hone]; exact hs₁
  -- the coercion of a `GroupExtension.Section` is its underlying function, so `hone'` is the
  -- normalization of the section just built
  exact ⟨⟨fun g => s (e.symm g), hsec'⟩, hs.comp e.symm.continuous, hone'⟩

end Profinite

section FactorSet

variable [CommGroup M] [TopologicalSpace M] [MulDistribMulAction G M]
  {S : GroupExtension M E G}

/-- **The factor set of a continuous normalized section is continuous** as soon as the kernel
carries the subspace topology of its image: the factor set is continuous exactly because its image
under the inclusion, the failure `σ g * σ h * (σ (g * h))⁻¹` of the section to be a homomorphism, is
continuous. In the profinite dictionary the hypothesis comes for free, the kernel being compact and
the extension Hausdorff: a continuous inclusion is then a closed embedding by
`Continuous.isClosedEmbedding`. Of `E` only the multiplication and the inversion are asked to be
continuous. -/
theorem continuous_factorSet [ContinuousMul E] [ContinuousInv E] [ContinuousMul G]
    (hinl : Topology.IsEmbedding ⇑S.inl)
    {σ : S.Section} (hσc : Continuous ⇑σ) (hσ : σ 1 = 1) (hact : InducesAction S) :
    Continuous ⇑(factorSet σ hσ hact) := by
  refine hinl.continuous_iff.2 ?_
  have hfs : ⇑S.inl ∘ ⇑(factorSet σ hσ hact)
      = fun p : G × G => σ p.1 * σ p.2 * (σ (p.1 * p.2))⁻¹ :=
    funext fun p => inl_factorSet σ hσ hact p.1 p.2
  rw [hfs]
  exact ((hσc.comp continuous_fst).mul (hσc.comp continuous_snd)).mul
    (hσc.comp (continuous_fst.mul continuous_snd)).inv

/-- The comparison map `⟨a, g⟩ ↦ inl a * σ g` out of the twisted product is continuous when the
section is. Only the multiplication of `E` has to be continuous: the map is a product of two
continuous maps, so nothing is asked of inversion. -/
theorem continuous_factorSetToGroupExtensionEquiv [ContinuousMul E] (hinl : Continuous S.inl)
    {σ : S.Section}
    (hσc : Continuous ⇑σ) (hσ : σ 1 = 1) (hact : InducesAction S) :
    Continuous ⇑(factorSetToGroupExtensionEquiv σ hσ hact) := by
  have he : ⇑(factorSetToGroupExtensionEquiv σ hσ hact)
      = fun x : (factorSet σ hσ hact).Extension => S.inl x.left * σ x.right :=
    funext (factorSetToGroupExtensionEquiv_apply σ hσ hact)
  rw [he]
  exact (hinl.comp FactorSet.Extension.continuous_left).mul
    (hσc.comp FactorSet.Extension.continuous_right)

/-- **The inverse of the comparison map is continuous** when the projection and the section are
continuous and the kernel is embedded: it sends `y` to
`⟨inl⁻¹ (y * (σ (rightHom y))⁻¹), rightHom y⟩`, and the first coordinate is continuous because its
image under the embedding `inl` is. Together with
`TauCeti.GroupExtension.continuous_factorSetToGroupExtensionEquiv` this makes the comparison a
homeomorphism with no compactness assumption. -/
theorem continuous_factorSetToGroupExtensionEquiv_symm [ContinuousMul E] [ContinuousInv E]
    (hinl : Topology.IsEmbedding ⇑S.inl) (hrh : Continuous S.rightHom) {σ : S.Section}
    (hσc : Continuous ⇑σ) (hσ : σ 1 = 1) (hact : InducesAction S) :
    Continuous ⇑(factorSetToGroupExtensionEquiv σ hσ hact).symm := by
  have hright : ∀ y : E, ((factorSetToGroupExtensionEquiv σ hσ hact).symm y).right =
      S.rightHom y := fun y => by
    have h := GroupExtension.Equiv.rightHom_map (factorSetToGroupExtensionEquiv σ hσ hact).symm y
    rwa [FactorSet.groupExtension_rightHom, FactorSet.rightHom_apply] at h
  have hleft : ∀ y : E, S.inl ((factorSetToGroupExtensionEquiv σ hσ hact).symm y).left =
      y * (σ (S.rightHom y))⁻¹ := fun y => by
    have hy : factorSetToGroupExtensionEquiv σ hσ hact
        ((factorSetToGroupExtensionEquiv σ hσ hact).symm y) = y := by
      simpa using (factorSetToGroupExtensionEquiv σ hσ hact).toMulEquiv.apply_symm_apply y
    rw [factorSetToGroupExtensionEquiv_apply, hright] at hy
    exact eq_mul_inv_of_mul_eq hy
  refine FactorSet.Extension.isInducing_leftRight.continuous_iff.2 ?_
  refine Continuous.prodMk ?_ (hrh.congr fun y => (hright y).symm)
  refine hinl.continuous_iff.2 ?_
  exact (continuous_id.mul (hσc.comp hrh).inv).congr fun y => (hleft y).symm

omit [MulDistribMulAction G M] in
/-- **The difference of two continuous sections is continuous** when the kernel carries the
subspace topology of its image: the image of the difference under the inclusion is
`σ g * (σ' g)⁻¹`. -/
theorem continuous_sectionDiff [ContinuousMul E] [ContinuousInv E]
    (hinl : Topology.IsEmbedding ⇑S.inl) {σ σ' : S.Section} (hσc : Continuous ⇑σ)
    (hσ'c : Continuous ⇑σ') : Continuous (sectionDiff σ σ') := by
  refine hinl.continuous_iff.2 ?_
  have h : ⇑S.inl ∘ sectionDiff σ σ' = fun g => σ g * (σ' g)⁻¹ := funext (inl_sectionDiff σ σ')
  rw [h]
  exact hσc.mul hσ'c.inv

/-- **A Hausdorff extension with compact kernel over a compact base is the twisted product built
from the factor set of a continuous normalized section**: the comparison map of
`TauCeti.GroupExtension.factorSetToGroupExtensionEquiv` is a multiplicative equivalence and a
homeomorphism. Compactness is asked of the base rather than of the extension because it is the
twisted product, the source of the comparison map, that has to be compact; a compact extension with
continuous projection has compact base by `Function.Surjective.compactSpace`. As for the comparison
map itself, only the multiplication of `E` is asked to be continuous. -/
noncomputable def factorSetContinuousMulEquiv [ContinuousMul E] [T2Space E] [CompactSpace M]
    [CompactSpace G] (hinl : Continuous S.inl)
    {σ : S.Section} (hσc : Continuous ⇑σ) (hσ : σ 1 = 1)
    (hact : InducesAction S) : (factorSet σ hσ hact).Extension ≃ₜ* E :=
  continuousMulEquivOfEquiv (factorSetToGroupExtensionEquiv σ hσ hact)
    (continuous_factorSetToGroupExtensionEquiv hinl hσc hσ hact)

@[simp]
theorem factorSetContinuousMulEquiv_apply [ContinuousMul E] [T2Space E] [CompactSpace M]
    [CompactSpace G] (hinl : Continuous S.inl)
    {σ : S.Section} (hσc : Continuous ⇑σ) (hσ : σ 1 = 1)
    (hact : InducesAction S) (x : (factorSet σ hσ hact).Extension) :
    factorSetContinuousMulEquiv hinl hσc hσ hact x = S.inl x.left * σ x.right :=
  factorSetToGroupExtensionEquiv_apply σ hσ hact x

/-- **A profinite extension with compact kernel is the twisted product of a continuous factor
set**, by an equivalence of extensions that is continuous, hence a homeomorphism through
`TauCeti.GroupExtension.continuousMulEquivOfEquiv`. This is the direction of the extension
dictionary that reads a cocycle off an extension;
`TauCeti.GroupExtension.factorSet_canonicalSection` is the other one. -/
theorem exists_continuous_factorSet [IsTopologicalGroup E] [CompactSpace E]
    [TotallyDisconnectedSpace E] [CompactSpace M] [T2Space G]
    [ContinuousMul G] (hinl : Continuous S.inl)
    (hrh : Continuous S.rightHom) (hact : InducesAction S) :
    ∃ α : FactorSet G M, Continuous ⇑α ∧ ∃ e : α.groupExtension.Equiv S, Continuous ⇑e := by
  obtain ⟨σ, hσc, hσ⟩ := exists_continuous_section hinl hrh
  exact ⟨factorSet σ hσ hact,
    continuous_factorSet (hinl.isClosedEmbedding S.inl_injective).isEmbedding hσc hσ hact,
    factorSetToGroupExtensionEquiv σ hσ hact,
    continuous_factorSetToGroupExtensionEquiv hinl hσc hσ hact⟩

end FactorSet

end TauCeti.GroupExtension

namespace TauCeti

/-! ### Bundled profinite extensions -/

universe u v

variable {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [CommGroup M]
  [TopologicalSpace M] [MulDistribMulAction G M]

variable (G M) in
/-- **An extension of `G` by `M` with profinite total group inducing the given action**: a
profinite group `E` together with an extension `1 → M → E → G → 1` of abstract groups whose
inclusion and projection are continuous and whose conjugation action on `M` is the given one.
Only the total group is required to be profinite; `G` and `M` carry just their topologies and the
action. The classification in `TauCeti/Topology/Algebra/GroupExtension/Cohomology.lean` adds what
it needs: for the class and the equivalence criterion, `G` Hausdorff with continuous multiplication
acting continuously on a compact `M`; for realizing every class, `G` and `M` both profinite. The
total group is taken in the universe of `M × G`, where the twisted products of the factor sets
live; under those hypotheses every such extension is, up to continuous equivalence, one of those
(`TauCeti.ProfiniteGroupExtension.ofFactorSet`), and the classification
`TauCeti.ProfiniteGroupExtension.contCohomologyClassEquiv` is stated at this universe for that
reason. -/
structure ProfiniteGroupExtension where
  /-- The total group of the extension. -/
  E : Type (max u v)
  [instGroup : Group E]
  [instTopologicalSpace : TopologicalSpace E]
  [instIsTopologicalGroup : IsTopologicalGroup E]
  [instCompactSpace : CompactSpace E]
  [instTotallyDisconnectedSpace : TotallyDisconnectedSpace E]
  /-- The extension `1 → M → E → G → 1` of abstract groups. -/
  toGroupExtension : GroupExtension M E G
  continuous_inl : Continuous toGroupExtension.inl
  continuous_rightHom : Continuous toGroupExtension.rightHom
  inducesAction : GroupExtension.InducesAction toGroupExtension

namespace ProfiniteGroupExtension

attribute [instance] instGroup instTopologicalSpace instIsTopologicalGroup instCompactSpace
  instTotallyDisconnectedSpace

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [IsTopologicalGroup M] [ContinuousSMul G M] [CompactSpace M] [TotallyDisconnectedSpace M]
  (α : FactorSet G M) (hα : Continuous ⇑α)

/-- **The twisted product of a continuous factor set is a profinite extension** when `G` and `M`
are profinite: it is `M × G` as a space, `TauCeti.FactorSet.Extension.isTopologicalGroup` makes
it a topological group, and its inclusion and projection are the coordinate maps. Compactness of
`M` alone would not do: the twisted product of the trivial factor set over the trivial group is `M`
itself. The realization is an abbreviation so that its total group and group structure remain
definitionally those of `α.Extension`; the underlying extension is given by
`TauCeti.ProfiniteGroupExtension.ofFactorSet_toGroupExtension`. -/
abbrev ofFactorSet : ProfiniteGroupExtension G M where
  E := α.Extension
  instIsTopologicalGroup := FactorSet.Extension.isTopologicalGroup hα
  toGroupExtension := α.groupExtension
  continuous_inl := by
    rw [FactorSet.groupExtension_inl]
    exact FactorSet.continuous_inl α
  continuous_rightHom := by
    rw [FactorSet.groupExtension_rightHom]
    exact FactorSet.continuous_rightHom α
  inducesAction := GroupExtension.inducesAction_groupExtension α

@[simp]
theorem ofFactorSet_toGroupExtension : (ofFactorSet α hα).toGroupExtension = α.groupExtension :=
  rfl

end ProfiniteGroupExtension

end TauCeti
