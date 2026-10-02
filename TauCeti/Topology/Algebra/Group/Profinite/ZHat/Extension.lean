/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupExtension.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic

/-!
# Extensions of the profinite integers split, and `H²(ℤ̂, M)` vanishes

Let `1 → M → E → ℤ̂ → 1` be an extension of groups whose total group `E` is profinite and whose
projection is continuous. Choose a preimage `e ∈ E` of the generator `zHat.gen`. The universal
property of `ℤ̂` (`TauCeti.zHat.lift`) extends it to a continuous homomorphism `ℤ̂ → E`, and this
is a section of the projection because both composites agree on the generator. So every such
extension splits by a continuous homomorphic section, which may be prescribed at the generator
(`GroupExtension.exists_splitting_continuous_zHat_apply_gen_eq`). Nothing is assumed of the
kernel: in contrast with the free pro-`p` groups, `ℤ̂` is free on one generator as a profinite
group, not only as a pro-`p` group.

Read through the classification of profinite extensions by continuous `H²`
(`TauCeti.ProfiniteGroupExtension.exists_contCohomologyClass_eq` and
`GroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero`), this is the
vanishing of the explicit second continuous cohomology `H²(ℤ̂, M)` for **every** profinite abelian
group `M` with a continuous action of `ℤ̂`, with no primary or torsion hypothesis on `M`
(`TauCeti.zHat.subsingleton_H2`). The finite discrete modules are among these coefficients; the
consequences for Mathlib's continuous cohomology and for the cohomological dimension of `ℤ̂` are
drawn in `TauCeti.Topology.Algebra.Group.Profinite.ZHat.CohomologicalDimension`.

## Main results

* `GroupExtension.exists_splitting_continuous_zHat_apply_gen_eq`: an extension of `ℤ̂` with
  profinite total group and continuous projection has a continuous homomorphic section taking any
  prescribed preimage of the generator as its value at the generator.
* `TauCeti.zHat.subsingleton_H2_additive`, `TauCeti.zHat.subsingleton_H2`: **`H²(ℤ̂, M) = 0`** for
  every profinite abelian group `M` with a continuous action of `ℤ̂`, written multiplicatively and
  additively.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §1, Proposition 2.
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 7.6.
-/

public section

namespace TauCeti

universe u v

/-! ### Extensions of `ℤ̂` split -/

section Splitting

variable {M : Type*} [Group M] {E : Type v} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
  [CompactSpace E] [TotallyDisconnectedSpace E] (S : GroupExtension M E zHat.{u})

/-- **Extensions of `ℤ̂` split, with a prescribed value at the generator.** Given an extension
`1 → M → E → ℤ̂ → 1` of groups with profinite total group and continuous projection, and a preimage
`e` of the generator `zHat.gen`, there is a continuous homomorphic section sending `zHat.gen` to
`e`: the universal property of `ℤ̂` extends `e` to a continuous homomorphism, which is a section
because both composites agree on the generator. -/
theorem _root_.GroupExtension.exists_splitting_continuous_zHat_apply_gen_eq
    (hrh : Continuous S.rightHom) (e : E) (he : S.rightHom e = zHat.gen) :
    ∃ s : S.Splitting, Continuous ⇑s ∧ s zHat.gen = e := by
  -- The projection, bundled with its continuity; it evaluates as `S.rightHom` by construction.
  let π : E →ₜ* zHat.{u} := ⟨S.rightHom, hrh⟩
  have hπ : ∀ z, π z = S.rightHom z := fun _ ↦ rfl
  have hs : π.comp (zHat.lift e) = ContinuousMonoidHom.id zHat.{u} :=
    zHat.hom_ext (by simp [hπ, he])
  exact ⟨GroupExtension.Splitting.mk (zHat.lift e).toMonoidHom fun y ↦ by
    simpa [hπ] using DFunLike.congr_fun hs y, (zHat.lift e).continuous, zHat.lift_gen e⟩

end Splitting

/-! ### The vanishing of `H²(ℤ̂, M)` -/

namespace zHat

open ContCohomology

section Multiplicative

variable {M : Type v} [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [CompactSpace M]
  [TotallyDisconnectedSpace M] [MulDistribMulAction zHat.{u} M] [ContinuousSMul zHat.{u} M]

/-- **`H²(ℤ̂, M)` vanishes**, for `M` a profinite abelian group, written multiplicatively, with a
continuous action of `ℤ̂`: every class of the explicit second continuous cohomology group is the
class of a profinite extension of `ℤ̂` by `M`, and every such extension splits. -/
theorem subsingleton_H2_additive : Subsingleton (H2 zHat.{u} (Additive M)) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨Y, rfl⟩ := ProfiniteGroupExtension.exists_contCohomologyClass_eq c
  rw [ProfiniteGroupExtension.contCohomologyClass_def,
    ← Y.toGroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero]
  obtain ⟨e, he⟩ := Y.toGroupExtension.rightHom_surjective gen
  obtain ⟨s, hs, -⟩ :=
    Y.toGroupExtension.exists_splitting_continuous_zHat_apply_gen_eq Y.continuous_rightHom e he
  exact ⟨s, hs⟩

end Multiplicative

/-- **`H²(ℤ̂, M)` vanishes, additive form**, for `M` a profinite abelian group, written additively,
with a continuous action of `ℤ̂`. No torsion hypothesis on `M` is needed. -/
theorem subsingleton_H2 {M : Type v} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [CompactSpace M] [TotallyDisconnectedSpace M]
    [DistribMulAction zHat.{u} M] [ContinuousSMul zHat.{u} M] : Subsingleton (H2 zHat.{u} M) :=
  -- `Additive (Multiplicative M)` is `M` with the same instances, so the multiplicative statement
  -- applies as it stands.
  subsingleton_H2_additive (M := Multiplicative M)

end zHat

end TauCeti
