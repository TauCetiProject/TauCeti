/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Basic
public import TauCeti.GroupTheory.Perm.Imprimitivity

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

Every block system of a transitive action that is stable under the group consists of the
translates of any one of its blocks, so describing quotients through a single block `B` loses
nothing.

## Main definitions

* `TauCeti.PermutationTriple.blockActionHom`: the action of the monodromy group on the translates
  of `B`, numbered by `Fin m`.
* `TauCeti.PermutationTriple.blockQuotient`: the quotient triple.
* `TauCeti.PermutationTriple.blockIndex`: the quotient map on sheets.

## Main results

* `TauCeti.PermutationTriple.blockQuotient_eq_smul`: two numberings of the translates give
  quotient triples related by an explicit relabeling.
* `TauCeti.PermutationTriple.isConnected_blockQuotient`: quotient triples are connected.
* `TauCeti.PermutationTriple.blockIndex_σ0`, `blockIndex_σ1`, `blockIndex_σinf`: the quotient map
  intertwines the components of `t` with those of the quotient.
* `TauCeti.PermutationTriple.ncard_mul_eq_of_isBlock`: the size of the block times the degree of
  the quotient is the degree of `t`.
## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, Graduate Texts in Mathematics 163,
  Springer 1996, §1.5.
-/

public section

namespace TauCeti

open Equiv MulAction
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
  refine ⟨fun hm ↦ (hm ▸ e ⟨B, mem_orbit_self B⟩).elim0, ⟨fun i j ↦ ?_⟩⟩
  obtain ⟨g, hg⟩ := exists_smul_eq t.monodromyGroup (e.symm i) (e.symm j)
  refine ⟨⟨t.blockActionHom B e g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩, e.symm.injective ?_⟩
  rw [Submonoid.mk_smul, Perm.smul_def, symm_blockActionHom_apply, hg]

/-! ### The quotient map on sheets -/

variable {t B}

/-- For a triple with transitive monodromy and a nonempty block `B`, the number of the unique
translate of `B` containing the sheet `x`. -/
noncomputable def blockIndex (ht : IsPretransitive t.monodromyGroup (Fin n))
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
theorem blockIndex_smul (g : t.monodromyGroup) (x : Fin n) :
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

end PermutationTriple

end TauCeti
