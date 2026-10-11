/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.GroupTheory.Perm.Imprimitivity
public import TauCeti.GroupTheory.Perm.Semiconj
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Tactic.Linarith
import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Quotient triples by blocks

Let `t` be a permutation triple and `B` a set of sheets. The monodromy group of `t` permutes the
translates `g • B` of `B`, so after numbering those translates by `Fin m` the three components of
`t` induce a triple of degree `m`: this is `TauCeti.PermutationTriple.blockQuotient`. It is always
connected, since a group acts transitively on each of its orbits, and changing the numbering only
relabels it.

When `t` is connected and `B` is a nonempty block of the monodromy action, the translates of `B`
partition the sheets (`MulAction.IsBlock.isBlockSystem`), and sending a sheet to the number of the
translate containing it is a surjection `TauCeti.PermutationTriple.blockIndex` from the sheets of
`t` to those of the quotient which intertwines the three components. Geometrically, the cover
described by `t` factors through the cover described by the quotient triple, and the fibres of
the intermediate map are the blocks. The degree of the quotient times the size of `B` is the
degree of `t`.

The cycle data of `t` refines that of the quotient. A cycle of an element `g` of the monodromy
group goes round the cycle of `g` on the blocks below it a whole number of times, namely the
number of its sheets lying in one block. Counting cycles, `g` has at most `|B|` times as many
cycles on the sheets as on the blocks; summed over the three components this bounds the Euler
characteristic of `t` by `|B|` times that of the quotient, which is the combinatorial form of the
Riemann–Hurwitz inequality for the intermediate cover, and shows that passing to a quotient does
not increase the genus.

Every block system of a transitive action that is stable under the group consists of the
translates of any one of its blocks, so describing quotients through a single block `B` loses
nothing.

Quotients are transitive. The blocks of the quotient by `B` containing the translate `B` itself
correspond, by pulling back along the quotient map, to the blocks of `t` containing `B`, so the
block systems of the quotient are exactly the block systems of `t` coarser than the translates of
`B`. Taking the quotient of the quotient by a set `C` of its sheets is taking the quotient of `t`
by the preimage of `C`, and the quotient maps compose accordingly: geometrically, a tower of
intermediate covers is read off from a chain of block systems.

## Main definitions

* `TauCeti.PermutationTriple.blockActionHom`: the action of the monodromy group on the translates
  of `B`, numbered by `Fin m`.
* `TauCeti.PermutationTriple.blockQuotient`: the quotient triple.
* `TauCeti.PermutationTriple.blockIndex`: the quotient map on sheets.
* `TauCeti.PermutationTriple.preimageBlockIndexOrderIso`: the blocks of the quotient containing
  `B` are the blocks of `t` containing `B`.
* `TauCeti.PermutationTriple.blockIndexOrbitEquiv`: the translates of a set of sheets of the
  quotient are the translates of its preimage.

## Main results

* `TauCeti.PermutationTriple.blockQuotient_eq_smul`: two numberings of the translates give
  quotient triples related by an explicit relabeling.
* `TauCeti.PermutationTriple.isConnected_blockQuotient`: quotient triples are connected.
* `TauCeti.PermutationTriple.blockIndex_σ0`, `blockIndex_σ1`, `blockIndex_σinf`: the quotient map
  intertwines the components of `t` with those of the quotient.
* `TauCeti.PermutationTriple.ncard_mul_eq_of_isBlock`: the size of the block times the degree of
  the quotient is the degree of `t`.
* `TauCeti.PermutationTriple.isBlock_preimage_blockIndex_iff`: a set of sheets of the quotient is a
  block exactly when its preimage is one.
* `TauCeti.PermutationTriple.blockQuotient_blockQuotient`: the quotient of the quotient by `C` is
  the quotient by the preimage of `C`.
* `TauCeti.PermutationTriple.equivalent_blockQuotient_image_blockIndex`: the quotient by a block
  containing `B` is, up to isomorphism, a quotient of the quotient by `B`.
* `TauCeti.PermutationTriple.blockIndex_blockIndex`: the quotient maps compose.
* `TauCeti.PermutationTriple.ncard_sameCycle_and_mem_mul_minimalPeriod_blockActionHom`: the length
  of the cycle of a sheet is the length of the cycle of its block times the number of sheets of
  that cycle in the block.
* `TauCeti.PermutationTriple.eulerChar_le_ncard_mul_eulerChar_blockQuotient`: the Euler
  characteristic of `t` is at most `|B|` times that of the quotient.
* `TauCeti.PermutationTriple.genus_blockQuotient_le`: the quotient of a connected triple has genus
  at most that of the triple.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, Graduate Texts in Mathematics 163,
  Springer 1996, §1.5.
-/

public section

namespace TauCeti

open Equiv Function MulAction
open scoped Pointwise

namespace PermutationTriple

variable {n m : ℕ} (t : PermutationTriple n) (B : Set (Fin n))

/-! ### The quotient triple -/

/-- The action of the monodromy group of `t` on the translates of `B`, with the translates
numbered by `e`. -/
def blockActionHom (e : orbit t.monodromyGroup B ≃ Fin m) :
    t.monodromyGroup →* Perm (Fin m) :=
  e.permCongrHom.toMonoidHom.comp (toPermHom t.monodromyGroup (orbit t.monodromyGroup B))

/-- Numbering the translates of `B` by `e`, the permutation of the numbers induced by `g` is
the action of `g` on the translates. -/
@[simp] theorem symm_blockActionHom_apply (e : orbit t.monodromyGroup B ≃ Fin m)
    (g : t.monodromyGroup) (i : Fin m) :
    e.symm (t.blockActionHom B e g i) = g • e.symm i := by
  simp [blockActionHom]

/-- The quotient of a triple by the translates of `B`: the triple of permutations induced on
the translates, numbered by `e`, by the three components. -/
def blockQuotient (e : orbit t.monodromyGroup B ≃ Fin m) : PermutationTriple m :=
  t.mapMonodromy (t.blockActionHom B e)

variable (e : orbit t.monodromyGroup B ≃ Fin m)

@[simp] theorem blockQuotient_σ0 :
    (t.blockQuotient B e).σ0 = t.blockActionHom B e ⟨t.σ0, t.σ0_mem_monodromyGroup⟩ :=
  t.mapMonodromy_σ0 _

@[simp] theorem blockQuotient_σ1 :
    (t.blockQuotient B e).σ1 = t.blockActionHom B e ⟨t.σ1, t.σ1_mem_monodromyGroup⟩ :=
  t.mapMonodromy_σ1 _

@[simp] theorem blockQuotient_σinf :
    (t.blockQuotient B e).σinf = t.blockActionHom B e ⟨t.σinf, t.σinf_mem_monodromyGroup⟩ :=
  t.mapMonodromy_σinf _

/-- The first component of the quotient moves the translate numbered `i` by `t.σ0`. -/
theorem coe_symm_blockQuotient_σ0 (i : Fin m) :
    (e.symm ((t.blockQuotient B e).σ0 i) : Set (Fin n)) = t.σ0 '' (e.symm i : Set (Fin n)) := by
  simp [orbit.coe_smul, ← Set.image_smul, Subgroup.smul_def, Perm.smul_def]

/-- The second component of the quotient moves the translate numbered `i` by `t.σ1`. -/
theorem coe_symm_blockQuotient_σ1 (i : Fin m) :
    (e.symm ((t.blockQuotient B e).σ1 i) : Set (Fin n)) = t.σ1 '' (e.symm i : Set (Fin n)) := by
  simp [orbit.coe_smul, ← Set.image_smul, Subgroup.smul_def, Perm.smul_def]

/-- The third component of the quotient moves the translate numbered `i` by `t.σinf`. -/
theorem coe_symm_blockQuotient_σinf (i : Fin m) :
    (e.symm ((t.blockQuotient B e).σinf i) : Set (Fin n)) =
      t.σinf '' (e.symm i : Set (Fin n)) := by
  simp [orbit.coe_smul, ← Set.image_smul, Subgroup.smul_def, Perm.smul_def]

/-- The monodromy group of the quotient is the image of the monodromy group of `t` acting on
the translates of `B`. -/
theorem monodromyGroup_blockQuotient :
    (t.blockQuotient B e).monodromyGroup = (t.blockActionHom B e).range :=
  t.monodromyGroup_mapMonodromy _

/-- Changing the numbering of the translates from `e` to `e'` relabels the quotient triple by
the permutation `e.symm.trans e'` of `Fin m` comparing the two numberings. -/
theorem blockQuotient_eq_smul (e' : orbit t.monodromyGroup B ≃ Fin m) :
    t.blockQuotient B e' = (e.symm.trans e') • t.blockQuotient B e := by
  rw [blockQuotient, blockQuotient, ← mapMonodromy_conj_comp]
  congr 1
  ext g i
  simp [blockActionHom]

/-- The quotient triple does not depend on the numbering of the translates, up to
isomorphism. -/
theorem equivalent_blockQuotient (e' : orbit t.monodromyGroup B ≃ Fin m) :
    Equivalent (t.blockQuotient B e) (t.blockQuotient B e') :=
  equivalent_iff_exists_smul_eq.2 ⟨e.symm.trans e', (t.blockQuotient_eq_smul B e e').symm⟩

/-- A quotient triple is connected: it has a sheet, the translate `B` itself, and the monodromy
group of `t` acts transitively on the translates of `B`. -/
theorem isConnected_blockQuotient : (t.blockQuotient B e).IsConnected := by
  rw [blockQuotient, isConnected_mapMonodromy_iff]
  refine ⟨fun hm ↦ (hm ▸ e ⟨B, mem_orbit_self B⟩).elim0, ?_⟩
  rw [blockActionHom, MonoidHom.range_comp, Equiv.isPretransitive_map_permCongrHom_iff,
    MulAction.isPretransitive_range_toPermHom_iff]
  infer_instance

/-! ### The quotient map on sheets -/

variable {t B}

/-- For a triple with transitive monodromy and a nonempty block `B`, the number of the unique
translate of `B` containing the sheet `x`. -/
noncomputable def blockIndex (_ : IsPretransitive t.monodromyGroup (Fin n))
    (hB : IsBlock t.monodromyGroup B) (hBne : B.Nonempty) (e : orbit t.monodromyGroup B ≃ Fin m)
    (x : Fin n) : Fin m :=
  e (hB.imprimitivityEquiv hBne x).1

variable (ht : IsPretransitive t.monodromyGroup (Fin n)) (hB : IsBlock t.monodromyGroup B)
  (hBne : B.Nonempty)

/-- The sheet `x` is sent to `i` exactly when it lies in the translate numbered `i`. -/
@[simp] theorem blockIndex_eq_iff {x : Fin n} {i : Fin m} :
    blockIndex ht hB hBne e x = i ↔ x ∈ (e.symm i : Set (Fin n)) := by
  rw [blockIndex, ← Equiv.eq_symm_apply, IsBlock.imprimitivityEquiv_fst_eq_iff]

/-- Every sheet lies in the translate of `B` whose number it is sent to. -/
theorem mem_symm_blockIndex (x : Fin n) :
    x ∈ (e.symm (blockIndex ht hB hBne e x) : Set (Fin n)) :=
  (blockIndex_eq_iff e ht hB hBne).1 rfl

/-- Every sheet of the quotient is hit: translates of a nonempty set are nonempty. -/
theorem blockIndex_surjective : Function.Surjective (blockIndex ht hB hBne e) := by
  intro i
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 (e.symm i).2
  have ⟨x, hx⟩ := hBne
  exact ⟨g • x, (blockIndex_eq_iff e ht hB hBne).2 (hg ▸ Set.smul_mem_smul_set hx)⟩

/-- The quotient map is equivariant for the monodromy group, acting on the quotient through
`TauCeti.PermutationTriple.blockActionHom`. -/
@[simp] theorem blockIndex_smul (g : t.monodromyGroup) (x : Fin n) :
    blockIndex ht hB hBne e (g • x) = t.blockActionHom B e g (blockIndex ht hB hBne e x) := by
  rw [blockIndex, blockIndex, hB.imprimitivityEquiv_smul_fst hBne g x]
  apply e.symm.injective
  simp

/-- The quotient map intertwines the first components. -/
@[simp] theorem blockIndex_σ0 (x : Fin n) :
    blockIndex ht hB hBne e (t.σ0 x) = (t.blockQuotient B e).σ0 (blockIndex ht hB hBne e x) := by
  rw [blockQuotient_σ0]
  exact blockIndex_smul e ht hB hBne ⟨t.σ0, t.σ0_mem_monodromyGroup⟩ x

/-- The quotient map intertwines the second components. -/
@[simp] theorem blockIndex_σ1 (x : Fin n) :
    blockIndex ht hB hBne e (t.σ1 x) = (t.blockQuotient B e).σ1 (blockIndex ht hB hBne e x) := by
  rw [blockQuotient_σ1]
  exact blockIndex_smul e ht hB hBne ⟨t.σ1, t.σ1_mem_monodromyGroup⟩ x

/-- The quotient map intertwines the third components. -/
@[simp] theorem blockIndex_σinf (x : Fin n) :
    blockIndex ht hB hBne e (t.σinf x) =
      (t.blockQuotient B e).σinf (blockIndex ht hB hBne e x) := by
  rw [blockQuotient_σinf]
  exact blockIndex_smul e ht hB hBne ⟨t.σinf, t.σinf_mem_monodromyGroup⟩ x

omit e in
include ht hB hBne in
/-- The degree of a triple with transitive monodromy is the size of a nonempty block times the
degree of the quotient by it. -/
theorem ncard_mul_eq_of_isBlock (e : orbit t.monodromyGroup B ≃ Fin m) : B.ncard * m = n := by
  have h := @IsBlock.ncard_block_mul_ncard_orbit_eq _ _ _ _ ht _ hB hBne
  rwa [← Nat.card_coe_set_eq (orbit _ B), Nat.card_congr e, Nat.card_fin, Nat.card_fin] at h

/-! ### Composing quotients -/

/-- The action of an element of the monodromy group of `t` on the translates of `B` lies in the
monodromy group of the quotient. -/
theorem blockActionHom_mem_monodromyGroup (g : t.monodromyGroup) :
    t.blockActionHom B e g ∈ (t.blockQuotient B e).monodromyGroup := by
  rw [monodromyGroup_blockQuotient]
  exact ⟨g, rfl⟩

/-- Every element of the monodromy group of the quotient is the action on the translates of `B`
of an element of the monodromy group of `t`. -/
private theorem exists_blockActionHom_eq (h : (t.blockQuotient B e).monodromyGroup) :
    ∃ g, t.blockActionHom B e g = h := by
  have hh : (h : Perm (Fin m)) ∈ (t.blockActionHom B e).range :=
    monodromyGroup_blockQuotient t B e ▸ h.2
  exact MonoidHom.mem_range.1 hh

/-- Pulling back along the quotient map turns the translate of a set of sheets of the quotient
by `h` into the translate of its preimage by any `g` acting on the translates of `B` as `h`. -/
theorem preimage_blockIndex_smul {g : t.monodromyGroup} {h : (t.blockQuotient B e).monodromyGroup}
    (hgh : t.blockActionHom B e g = h) (C : Set (Fin m)) :
    blockIndex ht hB hBne e ⁻¹' (h • C) = g • blockIndex ht hB hBne e ⁻¹' C := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage, Set.mem_preimage,
    Set.mem_smul_set_iff_inv_smul_mem, blockIndex_smul, map_inv, Subgroup.smul_def,
    Subgroup.coe_inv, hgh, Perm.smul_def]

/-- **Blocks of a quotient.** A set of sheets of the quotient is a block of its monodromy action
exactly when its preimage under the quotient map is a block of the monodromy action of `t`. -/
theorem isBlock_preimage_blockIndex_iff {C : Set (Fin m)} :
    IsBlock t.monodromyGroup (blockIndex ht hB hBne e ⁻¹' C) ↔
      IsBlock (t.blockQuotient B e).monodromyGroup C := by
  have hsurj := blockIndex_surjective e ht hB hBne
  simp only [isBlock_iff_smul_eq_or_disjoint]
  refine ⟨fun H h ↦ ?_, fun H g ↦ ?_⟩
  · obtain ⟨g, hg⟩ := exists_blockActionHom_eq e h
    have := H g
    rwa [← preimage_blockIndex_smul e ht hB hBne hg, (Set.preimage_injective.2 hsurj).eq_iff,
      Set.disjoint_preimage_iff hsurj] at this
  · rw [← preimage_blockIndex_smul e ht hB hBne
        (h := ⟨_, blockActionHom_mem_monodromyGroup e g⟩) rfl,
      (Set.preimage_injective.2 hsurj).eq_iff, Set.disjoint_preimage_iff hsurj]
    exact H _

include ht hB hBne in
/-- **Blocks containing `B` come from the quotient.** A block of the monodromy action of `t`
containing `B` is the preimage of its image under the quotient map: it is a union of translates
of `B`. -/
theorem preimage_image_blockIndex {D : Set (Fin n)} (hD : IsBlock t.monodromyGroup D)
    (hBD : B ⊆ D) : blockIndex ht hB hBne e ⁻¹' (blockIndex ht hB hBne e '' D) = D := by
  refine (Set.subset_preimage_image _ _).antisymm' ?_
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 (e.symm (blockIndex ht hB hBne e y)).2
  have hx := mem_symm_blockIndex e ht hB hBne x
  have hy' := mem_symm_blockIndex e ht hB hBne y
  rw [← hxy, ← hg] at hx
  rw [← hg] at hy'
  have hgD : g • D = D := hD.smul_eq_of_nonempty ⟨y, Set.smul_set_mono hBD hy', hy⟩
  exact hgD ▸ Set.smul_set_mono hBD hx

include ht hB hBne in
/-- **Block systems refine.** Pulling back along the quotient map is an order isomorphism from
the blocks of the monodromy action of the quotient containing the sheet that numbers the
translate `B` itself to the blocks of the monodromy action of `t` containing `B`. -/
noncomputable def preimageBlockIndexOrderIso :
    {C : Set (Fin m) //
        IsBlock (t.blockQuotient B e).monodromyGroup C ∧ e ⟨B, mem_orbit_self B⟩ ∈ C} ≃o
      {D : Set (Fin n) // IsBlock t.monodromyGroup D ∧ B ⊆ D} where
  toFun C := ⟨blockIndex ht hB hBne e ⁻¹' C, (isBlock_preimage_blockIndex_iff e ht hB hBne).2 C.2.1,
    fun x hx ↦ by
      rw [Set.mem_preimage, (blockIndex_eq_iff e ht hB hBne (i := e ⟨B, mem_orbit_self B⟩)).2
        (by simpa using hx)]
      exact C.2.2⟩
  invFun D := ⟨blockIndex ht hB hBne e '' D, by
    rw [← isBlock_preimage_blockIndex_iff e ht hB hBne,
      preimage_image_blockIndex e ht hB hBne D.2.1 D.2.2]
    exact D.2.1, by
    have ⟨x, hx⟩ := hBne
    exact ⟨x, D.2.2 hx,
      (blockIndex_eq_iff e ht hB hBne (i := e ⟨B, mem_orbit_self B⟩)).2 (by simpa using hx)⟩⟩
  left_inv C := Subtype.ext (Set.image_preimage_eq _ (blockIndex_surjective e ht hB hBne))
  right_inv D := Subtype.ext (preimage_image_blockIndex e ht hB hBne D.2.1 D.2.2)
  map_rel_iff' := (blockIndex_surjective e ht hB hBne).preimage_subset_preimage_iff

/-- The block of `t` corresponding to a block of the quotient is its preimage. -/
@[simp] theorem coe_preimageBlockIndexOrderIso_apply
    (C : {C : Set (Fin m) //
      IsBlock (t.blockQuotient B e).monodromyGroup C ∧ e ⟨B, mem_orbit_self B⟩ ∈ C}) :
    (preimageBlockIndexOrderIso e ht hB hBne C : Set (Fin n)) =
      blockIndex ht hB hBne e ⁻¹' C :=
  (rfl)

/-- The block of the quotient corresponding to a block of `t` containing `B` is its image. -/
@[simp] theorem coe_preimageBlockIndexOrderIso_symm_apply
    (D : {D : Set (Fin n) // IsBlock t.monodromyGroup D ∧ B ⊆ D}) :
    ((preimageBlockIndexOrderIso e ht hB hBne).symm D : Set (Fin m)) =
      blockIndex ht hB hBne e '' D :=
  (rfl)

/-- Pulling back along the quotient map identifies the translates of a set `C` of sheets of the
quotient with the translates of its preimage. -/
noncomputable def blockIndexOrbitEquiv (C : Set (Fin m)) :
    orbit (t.blockQuotient B e).monodromyGroup C ≃
      orbit t.monodromyGroup (blockIndex ht hB hBne e ⁻¹' C) where
  toFun S := ⟨blockIndex ht hB hBne e ⁻¹' S, by
    obtain ⟨h, hS⟩ := mem_orbit_iff.1 S.2
    obtain ⟨g, hg⟩ := exists_blockActionHom_eq e h
    exact mem_orbit_iff.2 ⟨g, by rw [← hS, preimage_blockIndex_smul e ht hB hBne hg]⟩⟩
  invFun T := ⟨blockIndex ht hB hBne e '' T, by
    obtain ⟨g, hT⟩ := mem_orbit_iff.1 T.2
    refine mem_orbit_iff.2 ⟨⟨_, blockActionHom_mem_monodromyGroup e g⟩, ?_⟩
    rw [← hT, ← preimage_blockIndex_smul e ht hB hBne
        (h := ⟨_, blockActionHom_mem_monodromyGroup e g⟩) rfl,
      Set.image_preimage_eq _ (blockIndex_surjective e ht hB hBne)]⟩
  left_inv S := Subtype.ext (Set.image_preimage_eq _ (blockIndex_surjective e ht hB hBne))
  right_inv T := by
    obtain ⟨g, hT⟩ := mem_orbit_iff.1 T.2
    refine Subtype.ext ?_
    dsimp only
    rw [← hT, ← preimage_blockIndex_smul e ht hB hBne
      (h := ⟨_, blockActionHom_mem_monodromyGroup e g⟩) rfl, Set.preimage_image_preimage]

/-- The translate of the preimage of `C` corresponding to a translate of `C` is its preimage. -/
@[simp] theorem coe_blockIndexOrbitEquiv_apply (C : Set (Fin m))
    (S : orbit (t.blockQuotient B e).monodromyGroup C) :
    (blockIndexOrbitEquiv e ht hB hBne C S : Set (Fin n)) = blockIndex ht hB hBne e ⁻¹' S :=
  (rfl)

/-- The translate of `C` corresponding to a translate of its preimage is its image. -/
@[simp] theorem coe_blockIndexOrbitEquiv_symm_apply (C : Set (Fin m))
    (T : orbit t.monodromyGroup (blockIndex ht hB hBne e ⁻¹' C)) :
    ((blockIndexOrbitEquiv e ht hB hBne C).symm T : Set (Fin m)) =
      blockIndex ht hB hBne e '' T :=
  (rfl)

/-- The identification of translates is equivariant for the monodromy group of `t`, acting on
the translates of `C` through its action on the sheets of the quotient. -/
theorem blockIndexOrbitEquiv_smul (C : Set (Fin m)) (g : t.monodromyGroup)
    (S : orbit (t.blockQuotient B e).monodromyGroup C) :
    blockIndexOrbitEquiv e ht hB hBne C
        ((⟨_, blockActionHom_mem_monodromyGroup e g⟩ :
          (t.blockQuotient B e).monodromyGroup) • S) =
      g • blockIndexOrbitEquiv e ht hB hBne C S := by
  refine Subtype.ext ?_
  rw [coe_blockIndexOrbitEquiv_apply, orbit.coe_smul, orbit.coe_smul,
    coe_blockIndexOrbitEquiv_apply, preimage_blockIndex_smul e ht hB hBne rfl]

/-- The action on the translates of `C` of the quotient, through the action on the sheets of the
quotient, is the action on the translates of the preimage of `C`, numbered compatibly. -/
theorem blockActionHom_blockQuotient {k : ℕ} (C : Set (Fin m))
    (e' : orbit (t.blockQuotient B e).monodromyGroup C ≃ Fin k) (g : t.monodromyGroup) :
    (t.blockQuotient B e).blockActionHom C e'
        ⟨t.blockActionHom B e g, blockActionHom_mem_monodromyGroup e g⟩ =
      t.blockActionHom (blockIndex ht hB hBne e ⁻¹' C)
        ((blockIndexOrbitEquiv e ht hB hBne C).symm.trans e') g := by
  ext i : 1
  apply ((blockIndexOrbitEquiv e ht hB hBne C).symm.trans e').symm.injective
  rw [symm_blockActionHom_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_trans_apply,
    Equiv.symm_symm, symm_blockActionHom_apply, blockIndexOrbitEquiv_smul]

/-- **Quotient triples compose.** Taking the quotient of the quotient of `t` by `B` by a set `C`
of its sheets gives the quotient of `t` by the preimage of `C`, for the numbering of the
translates of the preimage induced by that of the translates of `C`. -/
theorem blockQuotient_blockQuotient {k : ℕ} (C : Set (Fin m))
    (e' : orbit (t.blockQuotient B e).monodromyGroup C ≃ Fin k) :
    (t.blockQuotient B e).blockQuotient C e' =
      t.blockQuotient (blockIndex ht hB hBne e ⁻¹' C)
        ((blockIndexOrbitEquiv e ht hB hBne C).symm.trans e') := by
  ext1
  · simp only [blockQuotient_σ0]
    exact blockActionHom_blockQuotient e ht hB hBne C e' _
  · simp only [blockQuotient_σ1]
    exact blockActionHom_blockQuotient e ht hB hBne C e' _

/-- Up to isomorphism, the quotient of the quotient of `t` by `B` by a set `C` of its sheets is
the quotient of `t` by the preimage of `C`, whatever the numberings of the translates. -/
theorem equivalent_blockQuotient_blockQuotient {k : ℕ} (C : Set (Fin m))
    (e' : orbit (t.blockQuotient B e).monodromyGroup C ≃ Fin k)
    (e'' : orbit t.monodromyGroup (blockIndex ht hB hBne e ⁻¹' C) ≃ Fin k) :
    Equivalent ((t.blockQuotient B e).blockQuotient C e')
      (t.blockQuotient (blockIndex ht hB hBne e ⁻¹' C) e'') := by
  rw [blockQuotient_blockQuotient e ht hB hBne]
  exact equivalent_blockQuotient _ _ _ _

/-- **Quotients by coarser blocks factor through finer ones.** For a block `D` of the monodromy
action of `t` containing `B`, the quotient of `t` by `D` is, up to isomorphism, the quotient of
the quotient of `t` by `B` by the image of `D`. -/
theorem equivalent_blockQuotient_image_blockIndex {k : ℕ} {D : Set (Fin n)}
    (hD : IsBlock t.monodromyGroup D) (hBD : B ⊆ D)
    (e' : orbit (t.blockQuotient B e).monodromyGroup (blockIndex ht hB hBne e '' D) ≃ Fin k)
    (e'' : orbit t.monodromyGroup D ≃ Fin k) :
    Equivalent ((t.blockQuotient B e).blockQuotient (blockIndex ht hB hBne e '' D) e')
      (t.blockQuotient D e'') := by
  have h := preimage_image_blockIndex e ht hB hBne hD hBD
  generalize blockIndex ht hB hBne e '' D = C at e' h
  subst h
  exact equivalent_blockQuotient_blockQuotient e ht hB hBne C e' e''

/-- **Quotient maps compose.** For a nonempty block `C` of the monodromy action of the quotient
of `t` by `B`, the quotient map of `t` by the preimage of `C` is the quotient map of `t` by `B`
followed by the quotient map of the quotient by `C`. -/
theorem blockIndex_blockIndex {k : ℕ} {C : Set (Fin m)}
    (hC : IsBlock (t.blockQuotient B e).monodromyGroup C) (hCne : C.Nonempty)
    (e' : orbit (t.blockQuotient B e).monodromyGroup C ≃ Fin k) (x : Fin n) :
    blockIndex (t.isConnected_blockQuotient B e).isPretransitive hC hCne e'
        (blockIndex ht hB hBne e x) =
      blockIndex ht ((isBlock_preimage_blockIndex_iff e ht hB hBne).2 hC)
        (hCne.preimage (blockIndex_surjective e ht hB hBne))
        ((blockIndexOrbitEquiv e ht hB hBne C).symm.trans e') x := by
  rw [eq_comm, blockIndex_eq_iff, Equiv.symm_trans_apply, Equiv.symm_symm,
    coe_blockIndexOrbitEquiv_apply, Set.mem_preimage]
  exact mem_symm_blockIndex _ _ _ _ _

/-! ### Cycle data of the quotient -/

/-- The quotient map is a semiconjugacy from each element of the monodromy group to its action on
the translates. -/
theorem semiconj_blockIndex (g : t.monodromyGroup) :
    Function.Semiconj (blockIndex ht hB hBne e) (g : Perm (Fin n)) (t.blockActionHom B e g) :=
  fun x ↦ by simpa [Subgroup.smul_def, Perm.smul_def] using blockIndex_smul e ht hB hBne g x

/-- Each fibre of the quotient map is a translate of `B`, so it has as many sheets as `B`. -/
@[simp] theorem ncard_preimage_blockIndex (i : Fin m) :
    (blockIndex ht hB hBne e ⁻¹' {i}).ncard = B.ncard := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 (e.symm i).2
  have hfib : blockIndex ht hB hBne e ⁻¹' {i} = g • B := by
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, blockIndex_eq_iff, hg]
  rw [hfib, Set.ncard_smul_set]

/-- **Cycle lengths in a block quotient.** For `g` in the monodromy group and a sheet `x`, the
length of the cycle of `x` under `g` is the length of the cycle of the block of `x` under the
quotient action of `g`, times the number of sheets of the cycle of `x` that lie in the block
of `x`. -/
theorem ncard_sameCycle_and_mem_mul_minimalPeriod_blockActionHom (g : t.monodromyGroup)
    (x : Fin n) :
    {y | (g : Perm (Fin n)).SameCycle x y ∧
        y ∈ (e.symm (blockIndex ht hB hBne e x) : Set (Fin n))}.ncard *
      minimalPeriod (t.blockActionHom B e g) (blockIndex ht hB hBne e x) =
      minimalPeriod (g : Perm (Fin n)) x := by
  simp_rw [← blockIndex_eq_iff e ht hB hBne]
  exact (semiconj_blockIndex e ht hB hBne g).ncard_sameCycle_and_eq_mul_minimalPeriod x

include ht hB hBne in
/-- An element of the monodromy group has at most `|B|` times as many cycles on the sheets as on
the translates of `B`. -/
theorem orbitCount_le_ncard_mul_orbitCount_blockActionHom (g : t.monodromyGroup) :
    orbitCount (g : Perm (Fin n)) ≤ B.ncard * orbitCount (t.blockActionHom B e g) :=
  orbitCount_le_mul_orbitCount_of_semiconj (semiconj_blockIndex e ht hB hBne g)
    fun i ↦ (ncard_preimage_blockIndex e ht hB hBne i).le

include ht hB hBne in
/-- **The Riemann–Hurwitz inequality for a block quotient.** The Euler characteristic of a triple
with transitive monodromy is at most `|B|` times that of its quotient by a nonempty block `B`. -/
theorem eulerChar_le_ncard_mul_eulerChar_blockQuotient :
    t.eulerChar ≤ B.ncard * (t.blockQuotient B e).eulerChar := by
  have h0 := orbitCount_le_ncard_mul_orbitCount_blockActionHom e ht hB hBne
    ⟨t.σ0, t.σ0_mem_monodromyGroup⟩
  have h1 := orbitCount_le_ncard_mul_orbitCount_blockActionHom e ht hB hBne
    ⟨t.σ1, t.σ1_mem_monodromyGroup⟩
  have h2 := orbitCount_le_ncard_mul_orbitCount_blockActionHom e ht hB hBne
    ⟨t.σinf, t.σinf_mem_monodromyGroup⟩
  have hn : (n : ℤ) = B.ncard * m := by exact_mod_cast (ncard_mul_eq_of_isBlock ht hB hBne e).symm
  rw [eulerChar_def, eulerChar_def, blockQuotient_σ0, blockQuotient_σ1, blockQuotient_σinf, hn]
  push_cast at h0 h1 h2 ⊢
  linarith

include hB hBne in
/-- **Passing to a block quotient does not increase the genus.** The quotient of a connected
triple by a nonempty block has genus at most that of the triple. -/
theorem genus_blockQuotient_le (htc : t.IsConnected) :
    (t.blockQuotient B e).genus ≤ t.genus := by
  have hχ := eulerChar_le_ncard_mul_eulerChar_blockQuotient e htc.isPretransitive hB hBne
  rw [← htc.two_sub_two_mul_genus,
    ← (t.isConnected_blockQuotient B e).two_sub_two_mul_genus] at hχ
  have hs : (1 : ℤ) ≤ B.ncard := by exact_mod_cast (Set.ncard_pos B.toFinite).2 hBne
  rcases Nat.eq_zero_or_pos (t.blockQuotient B e).genus with h | h
  · simp [h]
  · have hneg : (2 : ℤ) - 2 * (t.blockQuotient B e).genus ≤ 0 := by omega
    have := mul_le_mul_of_nonpos_right hs hneg
    omega

end PermutationTriple

end TauCeti
