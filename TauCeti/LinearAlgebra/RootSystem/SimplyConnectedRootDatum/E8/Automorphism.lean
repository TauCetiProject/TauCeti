/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Datum
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.Index
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# The order of the automorphism group of the `E₈` root system

The automorphism group of the pinned root datum of type `E₈` has order
`240 · 126 · 23040 = 696729600`.

The count runs along the chain of pointwise stabilizers of the Bourbaki simple roots
`α₁, …, α₈`. Write `H k` for the subgroup fixing `α₁, …, α_k`, so that `H 0` is the whole group
and `H 8` is trivial, an automorphism fixing a base being the identity. By orbit and stabilizer,
`|H k| = |H k · α_{k+1}| · |H (k + 1)|`, and the orbit `H k · α_{k+1}` is the set of roots having
the same pairings with `α₁, …, α_k` as `α_{k+1}`. The orbit sizes are
`240, 126, 32, 6, 5, 4, 3, 2`. In particular the group is transitive on the 240 roots, the
stabilizer of `α₁` is transitive on the 126 roots orthogonal to it, and the pointwise stabilizer of
the orthogonal pair `α₁, α₂` has order `32 · 6 · 5 · 4 · 3 · 2 = 2⁵ · 6! = 23040`. These are the
orders of the Weyl groups of types `E₇` and `D₆`, the classical identifications of the two
stabilizers, which the count does not need.

That every root `β` with the right pairings lies in the orbit is the content of the count. If two
such roots `β` and `γ` pair to `1`, then `β - γ` is a root orthogonal to `α₁, …, α_k`, and the
reflection in it fixes `α₁, …, α_k` and exchanges `β` and `γ`. A finite computation checks that
every such `β` other than `α_{k+1}` pairs to `1` with such a root `γ` whose pairing with `α_{k+1}`
is strictly larger, so induction on that pairing reaches `α_{k+1}`.

## Main results

* `TauCeti.DynkinType.card_aut_e8SimplyConnectedRootDatum`: **the automorphism group of the pinned
  `E₈` datum has order `696729600`.**
* `TauCeti.DynkinType.card_weylGroup_e8SimplyConnectedRootDatum`: so does its Weyl group.
* `TauCeti.DynkinType.isPretransitive_aut_e8SimplyConnectedRootDatum`: it acts transitively on the
  240 roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.10 and Plate VII.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.1.
-/

public section

namespace TauCeti

open _root_.Matrix MulAction

namespace DynkinType

/-! ## Orbits through reflections -/

/-- Pairing a root with a simple root reads off a coordinate of the root in the fundamental-weight
basis. -/
private theorem e8Root_dotProduct_e8Coroot_e8SimpleIndex (j : Fin 240) (i : Fin 8) :
    e8Root j ⬝ᵥ e8Coroot (e8SimpleIndex i) = e8Root j i := by
  rw [coroot_e8SimpleIndex, dotProduct_single, mul_one]

/-- If two roots pair to `1`, the reflection in their difference, itself a root, carries the second
to the first and fixes every root pairing equally with both. -/
private theorem exists_smul_eq_of_dotProduct_eq_one {i j : Fin 240}
    (h : e8Root i ⬝ᵥ e8Coroot j = 1) :
    ∃ g : e8SimplyConnectedRootDatum.Aut, g • j = i ∧
      ∀ m, e8Root m ⬝ᵥ e8Coroot i = e8Root m ⬝ᵥ e8Coroot j → g • m = m := by
  have h' : e8Root j ⬝ᵥ e8Coroot i = 1 := by rw [e8Root_dotProduct_e8Coroot_comm, h]
  obtain ⟨r, hr⟩ := exists_e8Coroot_eq (v := e8Coroot i - e8Coroot j) (by
    rw [sub_vecMul, ← e8Root_apply, ← e8Root_apply, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, e8Root_dotProduct_coroot, e8Root_dotProduct_coroot, h, h']
    norm_num)
  have hroot : e8Root r = e8Root i - e8Root j := by
    rw [e8Root_apply, hr, sub_vecMul, ← e8Root_apply, ← e8Root_apply]
  have hpair (m : Fin 240) : e8SimplyConnectedRootDatum.pairing m r =
      e8Root m ⬝ᵥ e8Coroot i - e8Root m ⬝ᵥ e8Coroot j := by
    rw [e8SimplyConnectedRootDatum_pairing, hr, dotProduct_sub]
  have hsmul (m : Fin 240) : RootPairing.Equiv.reflection e8SimplyConnectedRootDatum r • m =
      e8SimplyConnectedRootDatum.reflectionPerm r m := by
    -- The action of `Aut` on root indices is `indexEquiv` by definition; Mathlib states no lemma
    -- unfolding it.
    change (RootPairing.Equiv.reflection e8SimplyConnectedRootDatum r).indexEquiv m = _
    rw [RootPairing.Equiv.reflection_indexEquiv]
  refine ⟨RootPairing.Equiv.reflection e8SimplyConnectedRootDatum r, ?_, fun m hm ↦ ?_⟩
  · rw [hsmul]
    apply e8Root.injective
    rw [← e8SimplyConnectedRootDatum_root, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_root, hpair, h', e8Root_dotProduct_coroot,
      e8SimplyConnectedRootDatum_root, hroot]
    abel
  · rw [hsmul]
    exact e8SimplyConnectedRootDatum.reflectionPerm_eq_of_pairing_eq_zero
      (by rw [hpair, hm, sub_self])

/-- **The certificate of transitivity.** For each `k`, every root `β` having the same pairings with
`α₁, …, α_k` as `α_{k+1}`, other than `α_{k+1}` itself, pairs to `1` with another such root whose
pairing with `α_{k+1}` is strictly larger. Pairing with the simple root `α_{i+1}` is the `i`-th
coordinate in the fundamental-weight basis. -/
private theorem eq_e8SimpleIndex_or_exists_dotProduct_eq_one (k : Fin 8) (j : Fin 240)
    (hj : ∀ i : Fin 8, i < k → e8Root j i = CartanMatrix.E 8 k i) :
    j = e8SimpleIndex k ∨ ∃ l : Fin 240, (∀ i : Fin 8, i < k → e8Root l i = CartanMatrix.E 8 k i) ∧
      (2 - e8Root l k).toNat < (2 - e8Root j k).toNat ∧ e8Root j ⬝ᵥ e8Coroot l = 1 := by
  -- A closed check over the eight levels and the 240 roots, run in the kernel.
  revert k j
  decide +kernel

/-- The number of roots having the same pairings with `α₁, …, α_k` as `α_{k+1}`. -/
private theorem card_filter_e8Root_eq_cartan (k : Fin 8) :
    (Finset.univ.filter fun j : Fin 240 ↦
      ∀ i : Fin 8, i < k → e8Root j i = CartanMatrix.E 8 k i).card =
      ![240, 126, 32, 6, 5, 4, 3, 2] k := by
  -- A closed check over the eight levels, run in the kernel.
  revert k
  decide +kernel

/-! ## The chain of stabilizers -/

/-- The automorphisms fixing the first `k` simple roots `α₁, …, α_k`, which are the root indices
below `k`. -/
private noncomputable abbrev e8FixingSubgroup (k : ℕ) : Subgroup e8SimplyConnectedRootDatum.Aut :=
  fixingSubgroup e8SimplyConnectedRootDatum.Aut {j : Fin 240 | (j : ℕ) < k}

/-- **The orbit of `α_{k+1}` under the automorphisms fixing `α₁, …, α_k`** is the set of roots
having the same pairings with `α₁, …, α_k` as `α_{k+1}`. -/
private theorem orbit_e8FixingSubgroup (k : Fin 8) :
    orbit (e8FixingSubgroup k) (e8SimpleIndex k) =
      {j | ∀ i : Fin 8, i < k → e8Root j i = CartanMatrix.E 8 k i} := by
  have hfix {g : e8SimplyConnectedRootDatum.Aut} (hg : g ∈ e8FixingSubgroup k) {i : Fin 8}
      (hi : i < k) : g • e8SimpleIndex i = e8SimpleIndex i :=
    (mem_fixingSubgroup_iff _).mp hg _ (by simpa using hi)
  refine subset_antisymm ?_ fun j hj ↦ ?_
  · rintro _ ⟨⟨g, hg⟩, rfl⟩ i hi
    -- The action of `Aut` on root indices is `indexEquiv` by definition, and automorphisms
    -- preserve the pairing.
    have h : e8SimplyConnectedRootDatum.pairing (g • e8SimpleIndex k) (g • e8SimpleIndex i) =
        e8SimplyConnectedRootDatum.pairing (e8SimpleIndex k) (e8SimpleIndex i) :=
      RootPairing.Hom.pairing g.toHom
    rw [hfix hg hi, e8SimplyConnectedRootDatum_pairing, e8SimplyConnectedRootDatum_pairing,
      e8Root_dotProduct_e8Coroot_e8SimpleIndex, e8Root_dotProduct_e8Coroot_e8SimpleIndex,
      root_e8SimpleIndex] at h
    exact h
  -- Induction on the distance `2 - ⟪β, α_{k+1}⟫` of the pairing from its value at `α_{k+1}`.
  induction hφ : (2 - e8Root j k).toNat using Nat.strong_induction_on generalizing j with
  | _ n ih =>
    obtain rfl | ⟨l, hl, hlt, hjl⟩ := eq_e8SimpleIndex_or_exists_dotProduct_eq_one k j hj
    · exact mem_orbit_self _
    obtain ⟨g, hgl, hg⟩ := exists_smul_eq_of_dotProduct_eq_one hjl
    have hgk : g ∈ e8FixingSubgroup k := (mem_fixingSubgroup_iff _).mpr fun m hm ↦ hg m (by
      -- The root indices below `k` are the simple roots `α₁, …, α_k`.
      have hm' : m = e8SimpleIndex ⟨m, hm.trans k.isLt⟩ :=
        Fin.ext (e8SimpleIndex_val ⟨m, hm.trans k.isLt⟩).symm
      rw [hm', e8Root_dotProduct_e8Coroot_comm, e8Root_dotProduct_e8Coroot_e8SimpleIndex,
        e8Root_dotProduct_e8Coroot_comm, e8Root_dotProduct_e8Coroot_e8SimpleIndex, hj _ hm,
        hl _ hm])
    have h := mem_orbit_of_mem_orbit (⟨g, hgk⟩ : e8FixingSubgroup k) (ih _ (hφ ▸ hlt) l hl rfl)
    rwa [Subgroup.mk_smul, hgl] at h

/-- One step of the chain: the automorphisms fixing `α₁, …, α_k` are `|orbit|` times as many as
those also fixing `α_{k+1}`. -/
private theorem card_e8FixingSubgroup (k : ℕ) (hk : k < 8) :
    Nat.card (e8FixingSubgroup k) =
      ![240, 126, 32, 6, 5, 4, 3, 2] ⟨k, hk⟩ * Nat.card (e8FixingSubgroup (k + 1)) := by
  have h := Subgroup.relIndex_mul_card (stabilizer e8SimplyConnectedRootDatum.Aut
    (e8SimpleIndex ⟨k, hk⟩)) (e8FixingSubgroup k)
  have hinf : stabilizer e8SimplyConnectedRootDatum.Aut (e8SimpleIndex ⟨k, hk⟩) ⊓
      e8FixingSubgroup k = e8FixingSubgroup (k + 1) := by
    ext g
    simp only [Subgroup.mem_inf, mem_stabilizer_iff, mem_fixingSubgroup_iff, Set.mem_ofPred_eq]
    refine ⟨fun ⟨h₁, h₂⟩ j hj ↦ ?_, fun h ↦ ⟨h _ (by simp), fun j hj ↦ h j (by omega)⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact h₂ j hj
    · rwa [show j = e8SimpleIndex ⟨k, hk⟩ from Fin.ext (hj.trans (e8SimpleIndex_val ⟨k, hk⟩).symm)]
  rw [Subgroup.relIndex, stabilizer_subgroupOf, index_stabilizer, hinf] at h
  rw [← h, orbit_e8FixingSubgroup ⟨k, hk⟩, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
    card_filter_e8Root_eq_cartan]

/-- An automorphism fixing all eight simple roots is the identity. -/
private theorem e8FixingSubgroup_eight : e8FixingSubgroup 8 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦
    e8SimplyConnectedBase.eq_one_of_forall_indexEquiv_eq fun i hi ↦ ?_
  exact (mem_fixingSubgroup_iff _).mp hg i (mem_support_e8SimplyConnectedBase.mp hi)

/-! ## The order -/

/-- **The automorphism group of the pinned `E₈` root datum has order
`240 · 126 · 23040 = 696729600`.** -/
theorem card_aut_e8SimplyConnectedRootDatum :
    Nat.card e8SimplyConnectedRootDatum.Aut = 696729600 := by
  have h0 : e8FixingSubgroup 0 = ⊤ := by simp [e8FixingSubgroup]
  rw [← Subgroup.card_top, ← h0]
  simp [card_e8FixingSubgroup, e8FixingSubgroup_eight]

/-- **The Weyl group of the pinned `E₈` root datum has order `696729600`**: it is the whole
automorphism group, the `E₈` diagram having no nontrivial symmetry. -/
theorem card_weylGroup_e8SimplyConnectedRootDatum :
    Nat.card e8SimplyConnectedRootDatum.weylGroup = 696729600 := by
  rw [weylGroup_eq_top_of_hasCartanType_E8 hasCartanType_e8SimplyConnectedRootDatum,
    Subgroup.card_top, card_aut_e8SimplyConnectedRootDatum]

/-- **The automorphism group of the pinned `E₈` root datum acts transitively on the 240 roots.** -/
instance isPretransitive_aut_e8SimplyConnectedRootDatum :
    IsPretransitive e8SimplyConnectedRootDatum.Aut (Fin 240) := by
  refine (isPretransitive_iff_base (e8SimpleIndex 0)).mpr fun j ↦ ?_
  have hj : j ∈ orbit (e8FixingSubgroup (0 : Fin 8)) (e8SimpleIndex 0) := by
    rw [orbit_e8FixingSubgroup 0]
    exact fun i hi ↦ absurd hi (Fin.not_lt_zero i)
  obtain ⟨g, rfl⟩ := hj
  exact ⟨g, rfl⟩

end DynkinType

end TauCeti
