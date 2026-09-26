/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.GroupAction.Defs
public import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.InformationTheory.Coding.Semilinear.Basic

/-!
# The semilinear monomial group and the semilinear automorphism group of a code

A semilinear monomial transformation of the word space `ι → R` applies a ring automorphism of
the alphabet to every coordinate, rescales by coordinate units, and relabels the coordinates.
When there is at least one coordinate and the alphabet automorphism is not the identity, such a
transformation is not `R`-linear, so the semilinear transformations do not in general form a
subgroup of the `R`-linear automorphisms of the word space, as the monomial and permutation
transformations do. They are all bijections of the word space, so this file collects them as a
subgroup of its permutation group, and defines the semilinear automorphism group of a code as the
stabilizer of the code inside it. Its elements are additive and preserve all Hamming data, and
the group acts on codewords.

## Main definitions

* `TauCeti.semilinearMonomialGroup R ι`: the group of semilinear monomial transformations of
  `ι → R`, as a subgroup of the permutation group `Equiv.Perm (ι → R)` of the word space.
* `TauCeti.semilinearAut C`: the semilinear automorphism group of a code `C`, the subgroup of
  `TauCeti.semilinearMonomialGroup R ι` stabilizing the set of codewords, acting on the codewords.

## Main statements

* `TauCeti.semilinearMonomialEquiv_toEquiv_mem_semilinearAut_iff`: a semilinear monomial
  transformation is a semilinear automorphism of `C` exactly when its semilinear image of `C`
  is `C`, the condition appearing in `TauCeti.IsSemilinearEquivalent`.
* `TauCeti.map_monomialAut_le_semilinearAut`: monomial automorphisms of a code are semilinear
  automorphisms, through the permutation of the word space underlying a linear automorphism.
* `TauCeti.semilinearMonomialEquiv_toEquiv_not_mem_map_of_ne_refl`: when the coordinate set is
  nonempty, a semilinear monomial transformation with a nontrivial alphabet automorphism is not
  induced by any `R`-linear automorphism, so the semilinear groups can be strictly larger than
  the images of the monomial ones.
* `TauCeti.semilinearMonomialGroup_eq_map_monomialGroup`,
  `TauCeti.semilinearAut_eq_map_monomialAut`: when the identity is the only ring automorphism
  of the alphabet, as for `ZMod n`, the semilinear groups are the images of the monomial ones.

Linear automorphisms of the word space are sent to permutations by
`MulAction.toPermHom ((ι → R) ≃ₗ[R] (ι → R)) (ι → R)`; this is the map along which the monomial
groups of `TauCeti.InformationTheory.Coding.Equivalence` are compared with the groups here.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §1.7.
-/

public section

namespace TauCeti

open Function Pointwise

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {R ι : Type*}

/-! ### The semilinear monomial group of a word space -/

section SemilinearMonomialGroup

/-- The group of semilinear monomial transformations of the word space `ι → R`, as a subgroup
of its permutation group. -/
def semilinearMonomialGroup (R ι : Type*) [CommSemiring R] : Subgroup (Equiv.Perm (ι → R)) where
  carrier := {f | ∃ (σ : R ≃+* R) (u : ι → Rˣ) (e : Equiv.Perm ι),
    (semilinearMonomialEquiv u e σ).toEquiv = f}
  one_mem' := ⟨RingEquiv.refl R, 1, Equiv.refl ι, by
    ext x j
    simp only [LinearEquiv.coe_toEquiv, semilinearMonomialEquiv_apply, Equiv.refl_symm,
      Equiv.refl_apply, Pi.one_apply, Units.val_one, one_mul, RingEquiv.refl_apply,
      Equiv.Perm.one_apply]⟩
  mul_mem' := by
    rintro f g ⟨σ, u, e, rfl⟩ ⟨τ, v, d, rfl⟩
    refine ⟨τ.trans σ, fun i ↦ u (d i) * Units.map σ.toMonoidHom (v i), d.trans e, ?_⟩
    ext x : 1
    simp only [LinearEquiv.coe_toEquiv, Equiv.Perm.mul_apply, semilinearMonomialEquiv_trans_apply]
  inv_mem' := by
    rintro f ⟨σ, u, e, rfl⟩
    refine ⟨σ.symm, fun j ↦ Units.map σ.symm.toMonoidHom (u (e.symm j))⁻¹, e.symm, ?_⟩
    ext x : 1
    exact (semilinearMonomialEquiv_symm_apply_eq_apply u e σ x).symm

variable [CommSemiring R]

/-- The semilinear monomial group consists exactly of the semilinear monomial transformations of
`ι → R`. -/
@[simp]
theorem mem_semilinearMonomialGroup {f : Equiv.Perm (ι → R)} :
    f ∈ semilinearMonomialGroup R ι ↔ ∃ (σ : R ≃+* R) (u : ι → Rˣ) (e : Equiv.Perm ι),
      (semilinearMonomialEquiv u e σ).toEquiv = f :=
  Iff.rfl

/-- Every semilinear monomial transformation lies in the semilinear monomial group. -/
theorem semilinearMonomialEquiv_toEquiv_mem_semilinearMonomialGroup (u : ι → Rˣ) (e : Equiv.Perm ι)
    (σ : R ≃+* R) : (semilinearMonomialEquiv u e σ).toEquiv ∈ semilinearMonomialGroup R ι :=
  ⟨σ, u, e, rfl⟩

/-- An element of the semilinear monomial group is additive. -/
@[simp]
theorem map_add_of_mem_semilinearMonomialGroup {f : Equiv.Perm (ι → R)}
    (hf : f ∈ semilinearMonomialGroup R ι) (x y : ι → R) : f (x + y) = f x + f y := by
  obtain ⟨σ, u, e, rfl⟩ := hf
  simp only [LinearEquiv.coe_toEquiv, map_add]

/-- An element of the semilinear monomial group fixes the zero word. -/
@[simp]
theorem map_zero_of_mem_semilinearMonomialGroup {f : Equiv.Perm (ι → R)}
    (hf : f ∈ semilinearMonomialGroup R ι) : f 0 = 0 := by
  obtain ⟨σ, u, e, rfl⟩ := hf
  simp only [LinearEquiv.coe_toEquiv, map_zero]

/-- An element of the semilinear monomial group is semilinear for some automorphism of the
alphabet. -/
theorem exists_map_smul_of_mem_semilinearMonomialGroup {f : Equiv.Perm (ι → R)}
    (hf : f ∈ semilinearMonomialGroup R ι) :
    ∃ σ : R ≃+* R, ∀ (r : R) (x : ι → R), f (r • x) = σ r • f x := by
  obtain ⟨σ, u, e, rfl⟩ := hf
  exact ⟨σ, fun r x ↦ (semilinearMonomialEquiv u e σ).map_smulₛₗ r x⟩

/-- An element of the semilinear monomial group preserves Hamming weight. -/
@[simp]
theorem hammingNorm_apply_of_mem_semilinearMonomialGroup [Fintype ι] [DecidableEq R]
    {f : Equiv.Perm (ι → R)} (hf : f ∈ semilinearMonomialGroup R ι) (x : ι → R) :
    hammingNorm (f x) = hammingNorm x := by
  obtain ⟨σ, u, e, rfl⟩ := hf
  exact hammingNorm_semilinearMonomialEquiv u e σ x

/-- An element of the semilinear monomial group preserves Hamming distance. -/
@[simp]
theorem hammingDist_apply_of_mem_semilinearMonomialGroup [Fintype ι] [DecidableEq R]
    {f : Equiv.Perm (ι → R)} (hf : f ∈ semilinearMonomialGroup R ι) (x y : ι → R) :
    hammingDist (f x) (f y) = hammingDist x y := by
  obtain ⟨σ, u, e, rfl⟩ := hf
  exact hammingDist_semilinearMonomialEquiv u e σ x y

end SemilinearMonomialGroup

/-! ### The semilinear automorphism group of a code -/

section SemilinearAut

variable [CommSemiring R] (C : Submodule R (ι → R))

/-- The semilinear automorphism group of a linear code: the semilinear monomial transformations
of its word space that map the set of codewords onto itself. -/
def semilinearAut : Subgroup (Equiv.Perm (ι → R)) :=
  semilinearMonomialGroup R ι ⊓ MulAction.stabilizer (Equiv.Perm (ι → R)) (C : Set (ι → R))

variable {C}

/-- The semilinear automorphism group of `C` consists exactly of the semilinear monomial
transformations mapping the set of codewords onto itself. -/
@[simp]
theorem mem_semilinearAut {f : Equiv.Perm (ι → R)} :
    f ∈ semilinearAut C ↔ f ∈ semilinearMonomialGroup R ι ∧ f • (C : Set (ι → R)) = C :=
  Iff.rfl

/-- Every semilinear automorphism of a code is a semilinear monomial transformation. -/
theorem semilinearAut_le_semilinearMonomialGroup : semilinearAut C ≤ semilinearMonomialGroup R ι :=
  inf_le_left

/-- A semilinear automorphism of a code sends codewords to codewords. -/
theorem apply_mem_of_mem_semilinearAut {f : Equiv.Perm (ι → R)} (hf : f ∈ semilinearAut C)
    {x : ι → R} (hx : x ∈ C) : f x ∈ C := by
  have hx' := Set.smul_mem_smul_set (a := f) (s := (C : Set (ι → R))) hx
  rwa [(mem_semilinearAut.mp hf).2] at hx'

/-- The permutation of the word space underlying a semilinear monomial transformation moves the
set of codewords to the semilinear image of the code. -/
@[simp]
theorem semilinearMonomialEquiv_toEquiv_smul_coe (u : ι → Rˣ) (e : Equiv.Perm ι) (σ : R ≃+* R) :
    (semilinearMonomialEquiv u e σ).toEquiv • (C : Set (ι → R)) =
      (C.map (semilinearMonomialEquiv u e σ).toLinearMap : Set (ι → R)) := by
  ext x
  simp only [Set.mem_smul_set, SetLike.mem_coe, Submodule.mem_map, Equiv.Perm.smul_def,
    LinearEquiv.coe_toEquiv, LinearEquiv.coe_coe]

/-- A semilinear monomial transformation is a semilinear automorphism of `C` exactly when its
semilinear image of `C` is `C`. -/
theorem semilinearMonomialEquiv_toEquiv_mem_semilinearAut_iff (u : ι → Rˣ) (e : Equiv.Perm ι)
    (σ : R ≃+* R) :
    (semilinearMonomialEquiv u e σ).toEquiv ∈ semilinearAut C ↔
      C.map (semilinearMonomialEquiv u e σ).toLinearMap = C := by
  rw [mem_semilinearAut, semilinearMonomialEquiv_toEquiv_smul_coe, SetLike.coe_set_eq]
  exact and_iff_right (semilinearMonomialEquiv_toEquiv_mem_semilinearMonomialGroup u e σ)

/-- A semilinear automorphism of a code permutes its codewords. -/
instance instSMulSemilinearAut : SMul (semilinearAut C) C where
  smul f c := ⟨(f : Equiv.Perm (ι → R)) c, apply_mem_of_mem_semilinearAut f.2 c.2⟩

/-- Coercing the action of a semilinear automorphism on a codeword back to a word gives the
underlying permutation of the word space applied to that codeword. -/
@[simp]
theorem coe_smul_semilinearAut (f : semilinearAut C) (c : C) :
    ((f • c : C) : ι → R) = (f : Equiv.Perm (ι → R)) c :=
  (rfl)

/-- The action of the semilinear automorphism group on the codewords is additive, since every
semilinear monomial transformation is additive. -/
instance instDistribMulActionSemilinearAut : DistribMulAction (semilinearAut C) C where
  one_smul _ := Subtype.ext (by simp)
  mul_smul _ _ _ := Subtype.ext (by simp)
  smul_zero f :=
    Subtype.ext
      (map_zero_of_mem_semilinearMonomialGroup (semilinearAut_le_semilinearMonomialGroup f.2))
  smul_add f c d :=
    Subtype.ext
      (map_add_of_mem_semilinearMonomialGroup (semilinearAut_le_semilinearMonomialGroup f.2) c d)

/-- A semilinear automorphism of a code acts on its codewords semilinearly for some automorphism
of the alphabet. -/
theorem exists_smul_smul_semilinearAut (f : semilinearAut C) :
    ∃ σ : R ≃+* R, ∀ (r : R) (c : C), f • (r • c) = σ r • (f • c) := by
  obtain ⟨σ, hσ⟩ :=
    exists_map_smul_of_mem_semilinearMonomialGroup (semilinearAut_le_semilinearMonomialGroup f.2)
  exact ⟨σ, fun r c ↦ Subtype.ext (hσ r c)⟩

/-- A semilinear automorphism of a code preserves Hamming weight. -/
@[simp]
theorem hammingNorm_semilinearAut_apply [Fintype ι] [DecidableEq R] (f : semilinearAut C)
    (x : ι → R) : hammingNorm ((f : Equiv.Perm (ι → R)) x) = hammingNorm x :=
  hammingNorm_apply_of_mem_semilinearMonomialGroup (semilinearAut_le_semilinearMonomialGroup f.2) x

/-- A semilinear automorphism of a code preserves Hamming distance. -/
@[simp]
theorem hammingDist_semilinearAut_apply [Fintype ι] [DecidableEq R] (f : semilinearAut C)
    (x y : ι → R) :
    hammingDist ((f : Equiv.Perm (ι → R)) x) ((f : Equiv.Perm (ι → R)) y) = hammingDist x y :=
  hammingDist_apply_of_mem_semilinearMonomialGroup (semilinearAut_le_semilinearMonomialGroup f.2)
    x y

end SemilinearAut

/-! ### Comparison with the monomial groups -/

section Monomial

variable [CommSemiring R] {C : Submodule R (ι → R)}

/-- The permutation of the word space underlying a monomial transformation is the semilinear
monomial transformation with the identity alphabet automorphism. -/
theorem toPermHom_monomialEquiv (u : ι → Rˣ) (e : Equiv.Perm ι) :
    MulAction.toPermHom ((ι → R) ≃ₗ[R] (ι → R)) (ι → R) (monomialEquiv u e) =
      (semilinearMonomialEquiv u e (RingEquiv.refl R)).toEquiv := by
  ext x j
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, LinearEquiv.smul_def,
    monomialEquiv_apply, LinearEquiv.coe_toEquiv, semilinearMonomialEquiv_apply,
    RingEquiv.refl_apply]

/-- A monomial transformation is a semilinear monomial transformation. -/
theorem map_monomialGroup_le_semilinearMonomialGroup :
    (monomialGroup R ι).map (MulAction.toPermHom ((ι → R) ≃ₗ[R] (ι → R)) (ι → R)) ≤
      semilinearMonomialGroup R ι := by
  rintro f ⟨g, hg, rfl⟩
  obtain ⟨u, e, rfl⟩ := mem_monomialGroup.mp hg
  rw [toPermHom_monomialEquiv]
  exact semilinearMonomialEquiv_toEquiv_mem_semilinearMonomialGroup u e _

/-- A monomial automorphism of a code is a semilinear automorphism of it. -/
theorem map_monomialAut_le_semilinearAut :
    (monomialAut C).map (MulAction.toPermHom ((ι → R) ≃ₗ[R] (ι → R)) (ι → R)) ≤
      semilinearAut C := by
  rintro f ⟨g, hg, rfl⟩
  obtain ⟨hg, hgC⟩ := mem_monomialAut.mp hg
  exact mem_semilinearAut.mpr
    ⟨map_monomialGroup_le_semilinearMonomialGroup (Subgroup.mem_map_of_mem _ hg),
      by rw [LinearEquiv.toPermHom_smul_coe, hgC]⟩

/-- A semilinear monomial transformation whose alphabet automorphism is not the identity is not
the permutation underlying any `R`-linear automorphism of the word space. -/
theorem semilinearMonomialEquiv_toEquiv_not_mem_map_of_ne_refl [Nonempty ι] (u : ι → Rˣ)
    (e : Equiv.Perm ι) {σ : R ≃+* R} (hσ : σ ≠ RingEquiv.refl R)
    (H : Subgroup ((ι → R) ≃ₗ[R] (ι → R))) :
    (semilinearMonomialEquiv u e σ).toEquiv ∉
      H.map (MulAction.toPermHom ((ι → R) ≃ₗ[R] (ι → R)) (ι → R)) := by
  rintro ⟨g, -, hg⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  classical
  refine hσ (RingEquiv.ext fun r ↦ ?_)
  have hg' : ∀ x, g x = semilinearMonomialEquiv u e σ x := fun x ↦ by
    simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply, LinearEquiv.smul_def,
      LinearEquiv.coe_toEquiv] using DFunLike.congr_fun hg x
  -- Compare the linear and the semilinear scalar rules on the word `Pi.single i 1` at the
  -- coordinate `e i`, where that word is sent to the unit `u i`.
  have h := congr_fun (hg' (r • Pi.single i 1)) (e i)
  rw [LinearEquiv.map_smul, Pi.smul_apply, hg', LinearEquiv.map_smulₛₗ, Pi.smul_apply] at h
  simp only [RingHom.coe_coe, smul_eq_mul, semilinearMonomialEquiv_apply, Equiv.symm_apply_apply,
    Pi.single_eq_same, map_one, mul_one] at h
  exact ((Units.mul_left_inj (u i)).mp h).symm

section TrivialAutomorphisms

variable [Subsingleton (R ≃+* R)]

/-- When the identity is the only ring automorphism of the alphabet, as for `ZMod n`, the
semilinear monomial group is the image of the monomial group. -/
@[simp]
theorem semilinearMonomialGroup_eq_map_monomialGroup :
    semilinearMonomialGroup R ι =
      (monomialGroup R ι).map (MulAction.toPermHom ((ι → R) ≃ₗ[R] (ι → R)) (ι → R)) := by
  refine le_antisymm ?_ map_monomialGroup_le_semilinearMonomialGroup
  intro f hf
  obtain ⟨σ, u, e, rfl⟩ := mem_semilinearMonomialGroup.mp hf
  obtain rfl := Subsingleton.elim σ (RingEquiv.refl R)
  exact Subgroup.mem_map.mpr
    ⟨monomialEquiv u e, monomialEquiv_mem_monomialGroup u e, toPermHom_monomialEquiv u e⟩

/-- When the identity is the only ring automorphism of the alphabet, the semilinear automorphism
group of a code is the image of its monomial automorphism group. -/
@[simp]
theorem semilinearAut_eq_map_monomialAut :
    semilinearAut C =
      (monomialAut C).map (MulAction.toPermHom ((ι → R) ≃ₗ[R] (ι → R)) (ι → R)) := by
  refine le_antisymm ?_ map_monomialAut_le_semilinearAut
  intro f hf
  obtain ⟨hf', hfC⟩ := mem_semilinearAut.mp hf
  obtain ⟨σ, u, e, rfl⟩ := mem_semilinearMonomialGroup.mp hf'
  obtain rfl := Subsingleton.elim σ (RingEquiv.refl R)
  refine Subgroup.mem_map.mpr ⟨monomialEquiv u e,
    mem_monomialAut.mpr ⟨monomialEquiv_mem_monomialGroup u e, SetLike.coe_injective ?_⟩,
    toPermHom_monomialEquiv u e⟩
  rw [← LinearEquiv.toPermHom_smul_coe, toPermHom_monomialEquiv]
  exact hfC

end TrivialAutomorphisms

end Monomial

end TauCeti
