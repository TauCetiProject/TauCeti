/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Simple
public import TauCeti.GroupTheory.Torsion

/-!
# Simplicity from normal generation by elements of prime order

A group is simple when it is nontrivial and each of its nontrivial elements generates it as a
normal subgroup. In a torsion group, and in particular in a finite group, it suffices to check
this for elements of **prime order**: a nontrivial normal subgroup contains a nontrivial element,
some power of which has prime order, and the normal closure of that power lies in the normal
subgroup. For a finite group this is the usual argument through Cauchy's theorem.

Since a normal subgroup containing an element contains its whole conjugacy class, it is enough to
know one normal generator in each conjugacy class of elements of prime order. This turns the
simplicity of a concrete finite group into finitely many checkable facts: a list of
representatives covering the classes of elements of prime order, and, for each representative,
that its normal closure is the whole group. This is the shape of the simplicity certificates for
groups given by presentations or by permutation and matrix generators.

## Main results

* `IsSimpleGroup.normalClosure_singleton_eq_top`: in a simple group, every nontrivial element
  generates the whole group as a normal subgroup.
* `IsMulTorsion.isSimpleGroup_iff_normalClosure_singleton_eq_top`: a torsion group is simple if
  and only if it is nontrivial and each of its elements of prime order generates it as a normal
  subgroup.
* `IsMulTorsion.isSimpleGroup_of_isConj_of_normalClosure_eq_top`: the certificate form, where the
  elements of prime order are covered up to conjugacy by a set of normal generators.

A finite group is torsion by `isMulTorsion_of_finite`. The prime-order element of a nontrivial
normal subgroup comes from `IsMulTorsion.exists_prime_orderOf_mem` in
`TauCeti.GroupTheory.Torsion`.
-/

public section

open Subgroup

variable {G : Type*} [Group G]

/-- In a simple group, every nontrivial element generates the whole group as a normal
subgroup. -/
theorem IsSimpleGroup.normalClosure_singleton_eq_top [IsSimpleGroup G] {g : G} (hg : g ≠ 1) :
    normalClosure {g} = ⊤ :=
  (Normal.eq_bot_or_eq_top (normalClosure {g})).resolve_left fun h ↦
    hg (by simpa using normalClosure_eq_bot_iff.mp h)

/-- **Simplicity of a torsion group from its elements of prime order.** A torsion group, for
instance a finite group, is simple if and only if it is nontrivial and each of its elements of
prime order generates it as a normal subgroup. -/
theorem IsMulTorsion.isSimpleGroup_iff_normalClosure_singleton_eq_top (hG : IsMulTorsion G) :
    IsSimpleGroup G ↔
      Nontrivial G ∧ ∀ g : G, (orderOf g).Prime → normalClosure {g} = ⊤ := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun g hg ↦
    IsSimpleGroup.normalClosure_singleton_eq_top fun h ↦ ?_⟩, fun ⟨_, h⟩ ↦ ⟨fun N _ ↦ ?_⟩⟩
  · exact hg.ne_one (by rw [h, orderOf_one])
  · -- A nontrivial normal subgroup contains an element of prime order, which normally generates.
    refine or_iff_not_imp_left.mpr fun hN ↦ ?_
    obtain ⟨g, hgN, hg⟩ := hG.exists_prime_orderOf_mem hN
    exact top_le_iff.mp (h g hg ▸ normalClosure_le_normal (Set.singleton_subset_iff.mpr hgN))

/-- **A simplicity certificate from conjugacy-class representatives.** Let `G` be a nontrivial
torsion group, for instance a nontrivial finite group, and let `s` be a set of elements each of
which generates `G` as a normal subgroup. If every element of prime order is conjugate to some
element of `s`, then `G` is simple.

For a concrete finite group, `s` is a list of representatives of the conjugacy classes of
elements of prime order, together with a proof that each representative normally generates the
group. -/
theorem IsMulTorsion.isSimpleGroup_of_isConj_of_normalClosure_eq_top (hG : IsMulTorsion G)
    [Nontrivial G] {s : Set G} (hs : ∀ x ∈ s, normalClosure {x} = ⊤)
    (hcover : ∀ g : G, (orderOf g).Prime → ∃ x ∈ s, IsConj x g) : IsSimpleGroup G := by
  refine hG.isSimpleGroup_iff_normalClosure_singleton_eq_top.mpr ⟨inferInstance, fun g hg ↦ ?_⟩
  obtain ⟨x, hxs, hxg⟩ := hcover g hg
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxg
  -- The normal closure of a conjugate `c * x * c⁻¹` contains `x` itself.
  refine top_le_iff.mp (hs x hxs ▸ normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_))
  simpa [mul_assoc] using
    (normalClosure_normal (s := {c * x * c⁻¹})).conj_mem _ (subset_normalClosure rfl) c⁻¹
