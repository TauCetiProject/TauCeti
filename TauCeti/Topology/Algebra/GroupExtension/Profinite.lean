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
* the comparison map from the twisted product back to `E` is an isomorphism of topological groups
  (`TauCeti.GroupExtension.factorSetContinuousMulEquiv`), assembled into
  `TauCeti.GroupExtension.exists_continuous_factorSet`.

In the other direction `TauCeti.GroupExtension.factorSet_canonicalSection` reads a factor set back
off the twisted product it builds, through the canonical section, which is continuous by
`TauCeti.FactorSet.continuous_canonicalSection`. So the two constructions are mutually inverse up
to equivalence of extensions.

The continuous section is the only step that uses the topology of `E` in an essential way. It comes
from the continuous section of a profinite group over the quotient by a closed subgroup, applied to
the kernel, which is closed because it is compact. Nothing asks the kernel to be *open*: an open
kernel would force `G` to be discrete, whereas the extensions this dictionary is used on have
infinite `G`.

## Main definitions

* `TauCeti.GroupExtension.continuousMulEquivOfEquiv`: an equivalence of extensions with compact
  total group is an isomorphism of topological groups as soon as it is continuous, and
  `TauCeti.GroupExtension.continuousMulEquivOfMonoidHom` is its form for a bare morphism.
* `TauCeti.GroupExtension.factorSetContinuousMulEquiv`: the extension, as a topological group, is
  the twisted product built from the factor set of a continuous normalized section.

## Main results

* `TauCeti.GroupExtension.isClosed_ker_rightHom`: a compact kernel is a closed subgroup.
* `TauCeti.GroupExtension.exists_continuous_section`: the projection of a profinite extension with
  compact kernel has a continuous normalized section.
* `TauCeti.GroupExtension.continuous_factorSet`: the factor set of a continuous normalized section
  is continuous.
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

/-- **A continuous equivalence of extensions with compact total group is an isomorphism of
topological groups.** Only continuity in one direction has to be checked: a continuous bijection
from a compact space onto a Hausdorff space is a homeomorphism. -/
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

/-- **Every continuous morphism between extensions with compact total group is an isomorphism of
topological groups.** Algebraically this is the five lemma, `GroupExtension.Equiv.ofMonoidHom`. -/
noncomputable def continuousMulEquivOfMonoidHom (f : E →* E') (hf : Continuous f)
    (comp_inl : f.comp S.inl = S'.inl) (rightHom_comp : S'.rightHom.comp f = S.rightHom) :
    E ≃ₜ* E' :=
  continuousMulEquivOfEquiv (GroupExtension.Equiv.ofMonoidHom f comp_inl rightHom_comp) hf

end Morphism

/-! ### The continuous section and its factor set -/

section ClosedKernel

variable [Group M] [TopologicalSpace M] [CompactSpace M] [T2Space E] {S : GroupExtension M E G}

omit [TopologicalSpace G] in
/-- **A compact kernel is a closed subgroup of the extension.** It is the continuous image of a
compact space, so the finite kernels of the extension dictionary are covered without a separate
argument. -/
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

variable [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E]
  [CommGroup M] [TopologicalSpace M] [CompactSpace M] [MulDistribMulAction G M]
  {S : GroupExtension M E G}

/-- **The factor set of a continuous normalized section is continuous.** The kernel is compact, so
its inclusion is a closed embedding, and the factor set is continuous exactly because its image
under that inclusion, the failure `σ g * σ h * (σ (g * h))⁻¹` of the section to be a homomorphism,
is continuous. -/
theorem continuous_factorSet [ContinuousMul G] (hinl : Continuous S.inl) {σ : S.Section}
    (hσc : Continuous ⇑σ) (hσ : σ 1 = 1) (hact : InducesAction S) :
    Continuous ⇑(factorSet σ hσ hact) := by
  refine (hinl.isClosedEmbedding S.inl_injective).isEmbedding.continuous_iff.2 ?_
  have hfs : ⇑S.inl ∘ ⇑(factorSet σ hσ hact)
      = fun p : G × G => σ p.1 * σ p.2 * (σ (p.1 * p.2))⁻¹ :=
    funext fun p => inl_factorSet σ hσ hact p.1 p.2
  rw [hfs]
  exact ((hσc.comp continuous_fst).mul (hσc.comp continuous_snd)).mul
    (hσc.comp (continuous_fst.mul continuous_snd)).inv

omit [CompactSpace E] [TotallyDisconnectedSpace E] [CompactSpace M] in
/-- The comparison map `⟨a, g⟩ ↦ inl a * σ g` out of the twisted product is continuous when the
section is. -/
theorem continuous_factorSetToGroupExtensionEquiv (hinl : Continuous S.inl) {σ : S.Section}
    (hσc : Continuous ⇑σ) (hσ : σ 1 = 1) (hact : InducesAction S) :
    Continuous ⇑(factorSetToGroupExtensionEquiv σ hσ hact) := by
  have he : ⇑(factorSetToGroupExtensionEquiv σ hσ hact)
      = fun x : (factorSet σ hσ hact).Extension => S.inl x.left * σ x.right :=
    funext (factorSetToGroupExtensionEquiv_apply σ hσ hact)
  rw [he]
  exact (hinl.comp FactorSet.Extension.continuous_left).mul
    (hσc.comp FactorSet.Extension.continuous_right)

/-- **A profinite extension with compact kernel is the twisted product built from the factor set of
a continuous normalized section**, as a topological group: the comparison map of
`TauCeti.GroupExtension.factorSetToGroupExtensionEquiv` is a homeomorphism. -/
noncomputable def factorSetContinuousMulEquiv (hinl : Continuous S.inl)
    (hrh : Continuous S.rightHom) {σ : S.Section} (hσc : Continuous ⇑σ) (hσ : σ 1 = 1)
    (hact : InducesAction S) : (factorSet σ hσ hact).Extension ≃ₜ* E :=
  haveI : CompactSpace G := S.rightHom_surjective.compactSpace hrh
  continuousMulEquivOfEquiv (factorSetToGroupExtensionEquiv σ hσ hact)
    (continuous_factorSetToGroupExtensionEquiv hinl hσc hσ hact)

/-- **A profinite extension with compact kernel is the twisted product of a continuous factor
set**, by an equivalence of extensions that is continuous, hence an isomorphism of topological
groups through `TauCeti.GroupExtension.continuousMulEquivOfEquiv`. This is the direction of the
extension dictionary that reads a cocycle off an extension;
`TauCeti.GroupExtension.factorSet_canonicalSection` is the other one. -/
theorem exists_continuous_factorSet [T2Space G] [ContinuousMul G] (hinl : Continuous S.inl)
    (hrh : Continuous S.rightHom) (hact : InducesAction S) :
    ∃ α : FactorSet G M, Continuous ⇑α ∧ ∃ e : α.groupExtension.Equiv S, Continuous ⇑e := by
  obtain ⟨σ, hσc, hσ⟩ := exists_continuous_section hinl hrh
  exact ⟨factorSet σ hσ hact, continuous_factorSet hinl hσc hσ hact,
    factorSetToGroupExtensionEquiv σ hσ hact,
    continuous_factorSetToGroupExtensionEquiv hinl hσc hσ hact⟩

end FactorSet

end TauCeti.GroupExtension
