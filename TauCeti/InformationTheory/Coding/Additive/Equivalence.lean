/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import TauCeti.InformationTheory.Coding.Reindex
public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic

/-!
# Permutation equivalence of additive codes

Coordinate relabelling transports additive codes over an arbitrary group alphabet. It requires
no scalar closure, and restricts to an additive equivalence of codewords. Permutation equivalence
preserves cardinality and minimum distance, including the zero-code convention. The permutation
automorphism group acts additively on codewords by the same coordinate relabelling.

These constructions permit coordinate changes for codes over discriminant alphabets. For linear
codes, forgetting scalar closure commutes with reindexing and preserves permutation equivalence.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.7.
-/

public section

namespace TauCeti.AdditiveCode

variable {A ι κ μ : Type*} [AddGroup A]

/-- Relabel an additive code along an equivalence from the new coordinates to the old ones.
The transported word has value `x (e j)` at coordinate `j`. -/
def reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) : AddSubgroup (κ → A) :=
  C.map (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).toAddMonoidHom

/-- Membership after relabelling is tested by pulling the word back to the old coordinates. -/
@[simp]
theorem mem_reindex {C : AddSubgroup (ι → A)} {e : κ ≃ ι} {y : κ → A} :
    y ∈ reindex C e ↔ y ∘ e.symm ∈ C :=
  AddSubgroup.mem_map_equiv

/-- Relabelling by the identity leaves an additive code unchanged. -/
@[simp]
theorem reindex_refl (C : AddSubgroup (ι → A)) : reindex C (Equiv.refl ι) = C := by
  ext x
  simp

/-- Successive relabellings compose in their contravariant order. -/
@[simp]
theorem reindex_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) (f : μ ≃ κ) :
    reindex (reindex C e) f = reindex C (f.trans e) := by
  ext x
  simp [Function.comp_assoc]

/-- Coordinate relabelling reflects and preserves inclusion of additive codes. -/
@[simp]
theorem reindex_le_reindex_iff {C D : AddSubgroup (ι → A)} (e : κ ≃ ι) :
    reindex C e ≤ reindex D e ↔ C ≤ D := by
  constructor
  · intro h x hx
    have := h (x := x ∘ e) (by simpa [Function.comp_def] using hx)
    simpa [Function.comp_def] using this
  · intro h x hx
    exact mem_reindex.mpr (h (mem_reindex.mp hx))

/-- Relabelling preserves the zero code. -/
@[simp]
theorem reindex_bot (e : κ ≃ ι) : reindex (⊥ : AddSubgroup (ι → A)) e = ⊥ := by
  simp [reindex]

/-- Relabelling preserves the whole word space. -/
@[simp]
theorem reindex_top (e : κ ≃ ι) : reindex (⊤ : AddSubgroup (ι → A)) e = ⊤ := by
  ext x
  simp

/-- Relabelling commutes with sums of additive codes. -/
@[simp]
theorem reindex_sup (C D : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    reindex (C ⊔ D) e = reindex C e ⊔ reindex D e :=
  AddSubgroup.map_sup _ _ _

/-- Relabelling commutes with intersections of additive codes. -/
@[simp]
theorem reindex_inf (C D : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    reindex (C ⊓ D) e = reindex C e ⊓ reindex D e := by
  ext x
  simp

/-- Coordinate relabelling restricts to an additive equivalence between a code and its image. -/
def reindexEquiv (C : AddSubgroup (ι → A)) (e : κ ≃ ι) : C ≃+ reindex C e :=
  (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).addSubgroupMap C

/-- The equivalence on codewords applies the coordinate relabelling. -/
@[simp]
theorem coe_reindexEquiv_apply (C : AddSubgroup (ι → A)) (e : κ ≃ ι) (x : C) :
    (reindexEquiv C e x : κ → A) = (x : ι → A) ∘ e := by
  exact (AddEquiv.coe_addSubgroupMap_apply
    (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)) C x).trans
      (funext fun j ↦ by simp)

/-- The inverse equivalence on codewords applies the inverse coordinate relabelling. -/
@[simp]
theorem coe_reindexEquiv_symm_apply (C : AddSubgroup (ι → A)) (e : κ ≃ ι)
    (y : reindex C e) :
    ((reindexEquiv C e).symm y : ι → A) = (y : κ → A) ∘ e.symm := by
  exact congrArg (fun z : C ↦ (z : ι → A))
    (AddEquiv.addSubgroupMap_symm_apply
      (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)) C y)

/-- Relabelling preserves cardinality, without requiring a finite alphabet. -/
@[simp↓]
theorem natCard_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    Nat.card (reindex C e) = Nat.card C :=
  Nat.card_congr (reindexEquiv C e).symm.toEquiv

/-- Two additive codes are permutation equivalent when coordinate relabelling carries one
onto the other. No change of the alphabet is allowed. -/
def IsPermutationEquivalent (C : AddSubgroup (ι → A)) (D : AddSubgroup (κ → A)) : Prop :=
  ∃ e : κ ≃ ι, reindex C e = D

/-- Permutation equivalence is witnessed by exactly a coordinate relabelling. -/
theorem isPermutationEquivalent_iff {C : AddSubgroup (ι → A)} {D : AddSubgroup (κ → A)} :
    IsPermutationEquivalent C D ↔ ∃ e : κ ≃ ι, reindex C e = D := Iff.rfl

@[refl]
theorem IsPermutationEquivalent.refl (C : AddSubgroup (ι → A)) :
    IsPermutationEquivalent C C := ⟨Equiv.refl ι, reindex_refl C⟩

@[symm]
theorem IsPermutationEquivalent.symm {C : AddSubgroup (ι → A)} {D : AddSubgroup (κ → A)}
    (h : IsPermutationEquivalent C D) : IsPermutationEquivalent D C := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.symm, by simp⟩

@[trans]
theorem IsPermutationEquivalent.trans {C : AddSubgroup (ι → A)} {D : AddSubgroup (κ → A)}
    {E : AddSubgroup (μ → A)} (h : IsPermutationEquivalent C D)
    (h' : IsPermutationEquivalent D E) : IsPermutationEquivalent C E := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨f, rfl⟩ := h'
  exact ⟨f.trans e, (reindex_reindex C e f).symm⟩

/-- Permutation-equivalent additive codes have the same cardinality. -/
theorem IsPermutationEquivalent.natCard_eq {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) : Nat.card C = Nat.card D := by
  obtain ⟨e, rfl⟩ := h
  exact (natCard_reindex C e).symm

/-- Coordinate relabelling preserves minimum distance, even for the zero code. -/
@[simp]
theorem hammingMinDist_reindex [Fintype ι] [Fintype κ] [DecidableEq A]
    (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    Set.hammingMinDist (reindex C e : Set (κ → A)) =
      Set.hammingMinDist (C : Set (ι → A)) := by
  rw [reindex, AddSubgroup.coe_map]
  exact Set.hammingMinDist_image _ fun x _ y _ _ ↦ Equiv.hammingDist_comp e x y

/-- Permutation-equivalent additive codes have the same minimum distance. -/
theorem IsPermutationEquivalent.hammingMinDist_eq [Fintype ι] [Fintype κ] [DecidableEq A]
    {C : AddSubgroup (ι → A)} {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) :
    Set.hammingMinDist (C : Set (ι → A)) = Set.hammingMinDist (D : Set (κ → A)) := by
  obtain ⟨e, rfl⟩ := h
  exact (hammingMinDist_reindex C e).symm

/-- The coordinate permutations preserving an additive code. Their action on words is
`x ↦ x ∘ e.symm`. -/
def permutationAut (C : AddSubgroup (ι → A)) : Subgroup (Equiv.Perm ι) where
  carrier := {e | reindex C e.symm = C}
  one_mem' := by simp [Equiv.Perm.one_def]
  mul_mem' := by
    intro e f he hf
    simpa [Equiv.Perm.mul_def] using
      (reindex_reindex C f.symm e.symm).symm.trans (by rw [hf, he])
  inv_mem' := by
    intro e he
    simpa [Equiv.Perm.inv_def] using (congrArg (fun D ↦ reindex D e) he).symm

/-- Membership in the permutation automorphism group is preservation under relabelling. -/
@[simp]
theorem mem_permutationAut {C : AddSubgroup (ι → A)} {e : Equiv.Perm ι} :
    e ∈ permutationAut C ↔ reindex C e.symm = C := Iff.rfl

/-- Permutation automorphisms act additively on the codewords. -/
instance (C : AddSubgroup (ι → A)) : SMul (permutationAut C) C where
  smul e x := ⟨(x : ι → A) ∘ (e : Equiv.Perm ι).symm, by
    have hx : (x : ι → A) ∘ (e : Equiv.Perm ι).symm ∈
        reindex C (e : Equiv.Perm ι).symm := by
      simp [Function.comp_def]
    simpa only [mem_permutationAut.mp e.2] using hx⟩

/-- The action on codewords is the underlying coordinate permutation. -/
@[simp]
theorem coe_smul_permutationAut (C : AddSubgroup (ι → A)) (e : permutationAut C) (x : C) :
    ((e • x : C) : ι → A) = (x : ι → A) ∘ (e : Equiv.Perm ι).symm := by rfl

/-- The coordinate permutation action respects addition and the group multiplication. -/
instance (C : AddSubgroup (ι → A)) : DistribMulAction (permutationAut C) C where
  one_smul x := Subtype.ext (by simp [Equiv.Perm.one_def])
  mul_smul e f x := Subtype.ext (by
    ext j
    simp [Equiv.Perm.mul_def])
  smul_zero e := Subtype.ext (by ext; simp)
  smul_add e x y := Subtype.ext (by ext; simp)

/-- Permutation automorphisms preserve Hamming weight. -/
@[simp↓]
theorem hammingNorm_smul_permutationAut [Fintype ι] [DecidableEq A]
    (C : AddSubgroup (ι → A)) (e : permutationAut C) (x : C) :
    hammingNorm ((e • x : C) : ι → A) = hammingNorm (x : ι → A) :=
  Equiv.hammingNorm_comp (e : Equiv.Perm ι).symm (x : ι → A)

/-- Permutation automorphisms preserve Hamming distance. -/
@[simp↓]
theorem hammingDist_smul_permutationAut [Fintype ι] [DecidableEq A]
    (C : AddSubgroup (ι → A)) (e : permutationAut C) (x y : C) :
    hammingDist ((e • x : C) : ι → A) ((e • y : C) : ι → A) =
      hammingDist (x : ι → A) (y : ι → A) :=
  Equiv.hammingDist_comp (e : Equiv.Perm ι).symm (x : ι → A) (y : ι → A)

section Linear

variable {F : Type*} [Field F]

/-- Forgetting scalar closure commutes with coordinate relabelling. -/
@[simp]
theorem reindex_toAddSubgroup (C : LinearCode F ι) (e : κ ≃ ι) :
    reindex C.toAddSubgroup e = (TauCeti.reindex C e).toAddSubgroup := by
  ext x
  simp only [mem_reindex, Submodule.mem_toAddSubgroup, TauCeti.mem_reindex]
  constructor
  · intro hx
    exact ⟨x ∘ e.symm, hx, by simp⟩
  · rintro ⟨y, hy, h⟩
    have heq : x ∘ e.symm = y := funext fun i ↦ by
      simpa using (h (e.symm i)).symm
    simpa [heq] using hy

/-- The additive and linear notions of permutation equivalence agree on linear codes. -/
theorem isPermutationEquivalent_toAddSubgroup_iff (C : LinearCode F ι) (D : LinearCode F κ) :
    IsPermutationEquivalent C.toAddSubgroup D.toAddSubgroup ↔
      TauCeti.IsPermutationEquivalent C D := by
  simp only [IsPermutationEquivalent, reindex_toAddSubgroup,
    TauCeti.isPermutationEquivalent_iff, TauCeti.reindex_def]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.symm, Submodule.toAddSubgroup_injective he⟩
  · rintro ⟨e, he⟩
    exact ⟨e.symm, congrArg Submodule.toAddSubgroup he⟩

end Linear

end TauCeti.AdditiveCode
