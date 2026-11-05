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
automorphism group acts additively on codewords by the same coordinate relabelling, and coordinate
relabelling induces a conjugation isomorphism between permutation automorphism groups
(`reindexPermutationAutEquiv`).

These constructions permit coordinate changes for codes over discriminant alphabets. For linear
codes, forgetting scalar closure commutes with reindexing, preserves permutation equivalence, and
identifies the additive and linear permutation automorphism groups over any nontrivial ring
(`permutationAutToAddSubgroupMulEquiv`).

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.6.
-/

public section

namespace TauCeti.AdditiveCode

variable {A ι κ μ : Type*} [AddGroup A]

/-- Relabel an additive code along an equivalence from the new coordinates to the old ones.
The transported word has value `x (e j)` at coordinate `j`. -/
def reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) : AddSubgroup (κ → A) :=
  C.map (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).toAddMonoidHom

/-- Reindexing is the additive subgroup image under coordinate transport. -/
theorem reindex_def (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    reindex C e = C.map (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).toAddMonoidHom := by rfl

/-- The underlying set of a reindexed code is the image under coordinate composition. -/
@[simp]
theorem coe_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    (reindex C e : Set (κ → A)) = (· ∘ e) '' (C : Set (ι → A)) := by
  have hcomp :
      ⇑(AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).toAddMonoidHom = (· ∘ e) := by
    ext x j
    simp
  rw [reindex_def, AddSubgroup.coe_map, hcomp]

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

/-- Relabelling and then applying the inverse relabelling recovers the code. -/
theorem reindex_reindex_symm (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    reindex (reindex C e) e.symm = C := by simp

/-- Coordinate relabelling reflects and preserves inclusion of additive codes. -/
@[simp]
theorem reindex_le_reindex_iff {C D : AddSubgroup (ι → A)} (e : κ ≃ ι) :
    reindex C e ≤ reindex D e ↔ C ≤ D :=
  AddSubgroup.map_le_map_iff_of_injective
    (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).injective

/-- Relabelling preserves the zero code. -/
@[simp]
theorem reindex_bot (e : κ ≃ ι) : reindex (⊥ : AddSubgroup (ι → A)) e = ⊥ := by
  simp [reindex_def]

/-- Relabelling preserves the whole word space. -/
@[simp]
theorem reindex_top (e : κ ≃ ι) : reindex (⊤ : AddSubgroup (ι → A)) e = ⊤ :=
  AddSubgroup.map_equiv_top (AddEquiv.arrowCongr e.symm (AddEquiv.refl A))

/-- Relabelling commutes with sums of additive codes. -/
@[simp]
theorem reindex_sup (C D : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    reindex (C ⊔ D) e = reindex C e ⊔ reindex D e :=
  AddSubgroup.map_sup _ _ _

/-- Relabelling commutes with intersections of additive codes. -/
@[simp]
theorem reindex_inf (C D : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    reindex (C ⊓ D) e = reindex C e ⊓ reindex D e :=
  AddSubgroup.map_inf C D _ (AddEquiv.arrowCongr e.symm (AddEquiv.refl A)).injective

/-- Coordinate relabelling restricts to an additive equivalence between a code and its image. -/
def reindexEquiv (C : AddSubgroup (ι → A)) (e : κ ≃ ι) : C ≃+ reindex C e :=
  -- By `reindex_def`, the codomain is the subgroup image used by `addSubgroupMap`.
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
  have h := coe_reindexEquiv_apply C e ((reindexEquiv C e).symm y)
  rw [AddEquiv.apply_symm_apply] at h
  ext i
  simpa using (congrFun h (e.symm i)).symm

/-- Relabelling preserves cardinality, without requiring a finite alphabet. -/
@[simp↓]
theorem natCard_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    Nat.card (reindex C e) = Nat.card C :=
  Nat.card_congr (reindexEquiv C e).symm.toEquiv

/-- Two additive codes are permutation equivalent when coordinate relabelling carries one
onto the other. The witness `e : κ ≃ ι` points from `D`'s coordinates to `C`'s,
opposite to the witness of `TauCeti.IsPermutationEquivalent`.
No change of the alphabet is allowed. -/
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
  exact ⟨e.symm, reindex_reindex_symm C e⟩

@[trans]
theorem IsPermutationEquivalent.trans {C : AddSubgroup (ι → A)} {D : AddSubgroup (κ → A)}
    {E : AddSubgroup (μ → A)} (h : IsPermutationEquivalent C D)
    (h' : IsPermutationEquivalent D E) : IsPermutationEquivalent C E := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨f, rfl⟩ := h'
  exact ⟨f.trans e, (reindex_reindex C e f).symm⟩

/-- Permutation-equivalent additive codes have the same cardinality. -/
theorem IsPermutationEquivalent.card_eq {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} (h : IsPermutationEquivalent C D) : Nat.card C = Nat.card D := by
  obtain ⟨e, rfl⟩ := h
  exact (natCard_reindex C e).symm

/-- Coordinate relabelling preserves minimum distance, even for the zero code. -/
@[simp↓]
theorem hammingMinDist_reindex [Fintype ι] [Fintype κ] [DecidableEq A]
    (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    Set.hammingMinDist (reindex C e : Set (κ → A)) =
      Set.hammingMinDist (C : Set (ι → A)) := by
  rw [coe_reindex]
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
    have h : reindex (reindex C f.symm) e.symm = C := by rw [hf, he]
    rw [reindex_reindex] at h
    simpa [Equiv.Perm.mul_def] using h
  inv_mem' := by
    intro e he
    have h : reindex C e = C := by
      calc
        reindex C e = reindex (reindex C e.symm) e := by rw [he]
        _ = C := reindex_reindex_symm C e.symm
    simpa [Equiv.Perm.inv_def] using h

/-- Membership in the permutation automorphism group is preservation under relabelling. -/
@[simp]
theorem mem_permutationAut {C : AddSubgroup (ι → A)} {e : Equiv.Perm ι} :
    e ∈ permutationAut C ↔ reindex C e.symm = C := Iff.rfl

/-- A permutation automorphism carries every codeword to a codeword. -/
theorem comp_symm_mem_of_mem_permutationAut {C : AddSubgroup (ι → A)} {e : Equiv.Perm ι}
    (he : e ∈ permutationAut C) {x : ι → A} (hx : x ∈ C) : x ∘ e.symm ∈ C := by
  rw [← mem_permutationAut.mp he]
  simpa [Function.comp_def] using hx

/-- Permutation automorphisms act additively on the codewords. -/
instance instSMulPermutationAut (C : AddSubgroup (ι → A)) : SMul (permutationAut C) C where
  smul e x := ⟨(x : ι → A) ∘ (e : Equiv.Perm ι).symm,
    comp_symm_mem_of_mem_permutationAut e.2 x.2⟩

/-- The action on codewords is the underlying coordinate permutation. -/
@[simp]
theorem coe_smul_permutationAut (C : AddSubgroup (ι → A)) (e : permutationAut C) (x : C) :
    ((e • x : C) : ι → A) = (x : ι → A) ∘ (e : Equiv.Perm ι).symm := by rfl

/-- The coordinate permutation action respects addition and the group multiplication. -/
instance instDistribMulActionPermutationAut (C : AddSubgroup (ι → A)) :
    DistribMulAction (permutationAut C) C where
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
    hammingNorm ((e • x : C) : ι → A) = hammingNorm (x : ι → A) := by
  rw [coe_smul_permutationAut]
  exact Equiv.hammingNorm_comp (e : Equiv.Perm ι).symm (x : ι → A)

/-- Permutation automorphisms preserve Hamming distance. -/
@[simp↓]
theorem hammingDist_smul_permutationAut [Fintype ι] [DecidableEq A]
    (C : AddSubgroup (ι → A)) (e : permutationAut C) (x y : C) :
    hammingDist ((e • x : C) : ι → A) ((e • y : C) : ι → A) =
      hammingDist (x : ι → A) (y : ι → A) := by
  rw [coe_smul_permutationAut, coe_smul_permutationAut]
  exact Equiv.hammingDist_comp (e : Equiv.Perm ι).symm (x : ι → A) (y : ι → A)

/-- Coordinate relabelling is injective on additive codes. -/
@[simp]
theorem reindex_eq_reindex_iff {C D : AddSubgroup (ι → A)} (e : κ ≃ ι) :
    reindex C e = reindex D e ↔ C = D := by
  rw [le_antisymm_iff, le_antisymm_iff, reindex_le_reindex_iff, reindex_le_reindex_iff]

/-- Permutation automorphisms of a reindexed additive code correspond to those of the original code
by conjugation along `e`. -/
theorem mem_permutationAut_reindex {C : AddSubgroup (ι → A)} {e : κ ≃ ι} {σ : Equiv.Perm κ} :
    σ ∈ permutationAut (reindex C e) ↔ e.permCongr σ ∈ permutationAut C := by
  have hcomp : e.trans (e.permCongr σ).symm = σ.symm.trans e := by
    ext j
    simp [Equiv.permCongr_def]
  rw [mem_permutationAut, reindex_reindex, ← hcomp, ← reindex_reindex, reindex_eq_reindex_iff,
    mem_permutationAut]

/-- Coordinate relabelling maps the permutation automorphism group along `e.symm.permCongrHom`. -/
theorem permutationAut_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    permutationAut (reindex C e) = (permutationAut C).map e.symm.permCongrHom.toMonoidHom := by
  ext σ
  rw [mem_permutationAut_reindex, Subgroup.mem_map]
  refine ⟨fun h ↦ ⟨e.permCongr σ, h, ?_⟩, ?_⟩
  · ext j
    simp [Equiv.permCongr_def]
  · rintro ⟨τ, hτ, rfl⟩
    have hτ' : e.permCongr (e.symm.permCongr τ) = τ := by
      ext i
      simp [Equiv.permCongr_def]
    simpa [hτ'] using hτ

/-- Coordinate relabelling induces a group isomorphism between permutation automorphism groups. -/
def reindexPermutationAutEquiv (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    permutationAut C ≃* permutationAut (reindex C e) :=
  (e.symm.permCongrHom.subgroupMap (permutationAut C)).trans
    (MulEquiv.subgroupCongr (permutationAut_reindex C e).symm)

/-- The forward isomorphism conjugates underlying permutations along `e.symm`. -/
@[simp]
theorem coe_reindexPermutationAutEquiv_apply (C : AddSubgroup (ι → A)) (e : κ ≃ ι)
    (g : permutationAut C) :
    (reindexPermutationAutEquiv C e g : Equiv.Perm κ) = e.symm.permCongr (g : Equiv.Perm ι) :=
  (rfl)

/-- The inverse isomorphism conjugates underlying permutations along `e`. -/
@[simp]
theorem coe_reindexPermutationAutEquiv_symm_apply (C : AddSubgroup (ι → A)) (e : κ ≃ ι)
    (g : permutationAut (reindex C e)) :
    ((reindexPermutationAutEquiv C e).symm g : Equiv.Perm ι) =
      e.permCongr (g : Equiv.Perm κ) := by
  apply e.symm.permCongr.injective
  rw [← coe_reindexPermutationAutEquiv_apply, MulEquiv.apply_symm_apply, ← Equiv.permCongr_symm,
    Equiv.symm_apply_apply]

/-- Relabelling preserves the order of the permutation automorphism group. -/
@[simp↓]
theorem natCard_permutationAut_reindex (C : AddSubgroup (ι → A)) (e : κ ≃ ι) :
    Nat.card (permutationAut (reindex C e)) = Nat.card (permutationAut C) :=
  Nat.card_congr (reindexPermutationAutEquiv C e).symm.toEquiv

section Ring

variable {R : Type*} [Ring R]

/-- Over a ring, additive-code reindexing can be expressed using the underlying additive
equivalence of the corresponding linear coordinate relabelling. -/
theorem reindex_eq_map_funCongrLeft (C : AddSubgroup (ι → R)) (e : κ ≃ ι) :
    reindex C e =
      C.map (LinearEquiv.funCongrLeft R R e).toAddEquiv.toAddMonoidHom := by
  rw [reindex_def]
  congr 1

/-- Additive coordinate transport agrees with the underlying subgroup of a linear image. -/
theorem reindex_toAddSubgroup_eq_map (C : Submodule R (ι → R)) (e : κ ≃ ι) :
    reindex C.toAddSubgroup e =
      (C.map (LinearEquiv.funCongrLeft R R e).toLinearMap).toAddSubgroup := by
  have hmap : (AddEquiv.arrowCongr e.symm (AddEquiv.refl R)).toAddMonoidHom =
      ((LinearEquiv.funCongrLeft R R e).toLinearMap : (ι → R) →+ (κ → R)) := by
    ext x j
    simp
  rw [reindex_def, Submodule.map_toAddSubgroup, hmap]

/-- The additive and linear notions of permutation equivalence agree on linear codes. -/
theorem isPermutationEquivalent_toAddSubgroup_iff
    (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    IsPermutationEquivalent C.toAddSubgroup D.toAddSubgroup ↔
      TauCeti.IsPermutationEquivalent C D := by
  simp only [isPermutationEquivalent_iff, reindex_toAddSubgroup_eq_map,
    TauCeti.isPermutationEquivalent_iff]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.symm, Submodule.toAddSubgroup_injective he⟩
  · rintro ⟨e, he⟩
    exact ⟨e.symm, congrArg Submodule.toAddSubgroup he⟩

/-- The additive permutation stabilizer agrees with the linear stabilizer on coordinate maps. -/
theorem mem_permutationAut_toAddSubgroup_iff (C : Submodule R (ι → R)) (e : Equiv.Perm ι) :
    e ∈ permutationAut C.toAddSubgroup ↔
      LinearEquiv.funCongrLeft R R e.symm ∈ TauCeti.permutationAut C := by
  rw [mem_permutationAut, reindex_toAddSubgroup_eq_map, TauCeti.mem_permutationAut]
  simp only [TauCeti.funCongrLeft_mem_permutationGroup, true_and,
    Submodule.toAddSubgroup_injective.eq_iff]

/-- Over a nontrivial ring, the additive permutation automorphism group of `C.toAddSubgroup` is
canonically isomorphic to the linear permutation automorphism group `TauCeti.permutationAut C`. -/
noncomputable def permutationAutToAddSubgroupMulEquiv (C : Submodule R (ι → R)) [Nontrivial R] :
    permutationAut C.toAddSubgroup ≃* TauCeti.permutationAut C :=
  MulEquiv.ofBijective
    ({ toFun := fun e ↦ ⟨LinearEquiv.funCongrLeft R R (e : Equiv.Perm ι).symm,
         (mem_permutationAut_toAddSubgroup_iff C e).mp e.2⟩
       map_one' := Subtype.ext <| by
         dsimp only
         rw [Subgroup.coe_one, Equiv.Perm.one_def, Equiv.refl_symm,
           LinearEquiv.funCongrLeft_id, Subgroup.coe_one, LinearEquiv.one_eq_refl]
       map_mul' := fun e₁ e₂ ↦ Subtype.ext <| by
         dsimp only
         rw [Subgroup.coe_mul, Equiv.Perm.mul_def, Equiv.symm_trans,
           LinearEquiv.funCongrLeft_comp, Subgroup.coe_mul, LinearEquiv.mul_eq_trans] } :
      permutationAut C.toAddSubgroup →* TauCeti.permutationAut C)
    ⟨fun e₁ e₂ h ↦ by
        classical
        refine Subtype.ext <| Equiv.symm_bijective.injective <| Equiv.ext fun j ↦ ?_
        have hj := congrArg
          (fun f : (ι → R) ≃ₗ[R] (ι → R) ↦ f (Pi.single ((e₁ : Equiv.Perm ι).symm j) 1) j)
          (congrArg Subtype.val h)
        dsimp only [MonoidHom.coe_mk, OneHom.coe_mk] at hj
        simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
          Pi.single_eq_same] at hj
        by_contra hne
        rw [Pi.single_eq_of_ne (Ne.symm hne)] at hj
        exact one_ne_zero hj,
      fun f ↦ by
        obtain ⟨e, he⟩ := TauCeti.mem_permutationGroup.mp (TauCeti.mem_permutationAut.mp f.2).1
        exact ⟨⟨e, (mem_permutationAut_toAddSubgroup_iff C e).mpr (he.symm ▸ f.2)⟩,
          Subtype.ext he⟩⟩

/-- `permutationAutToAddSubgroupMulEquiv` sends a coordinate permutation `e` to the linear
equivalence `LinearEquiv.funCongrLeft R R e.symm`. -/
@[simp]
theorem coe_permutationAutToAddSubgroupMulEquiv_apply (C : Submodule R (ι → R)) [Nontrivial R]
    (e : permutationAut C.toAddSubgroup) :
    (permutationAutToAddSubgroupMulEquiv C e : (ι → R) ≃ₗ[R] (ι → R)) =
      LinearEquiv.funCongrLeft R R (e : Equiv.Perm ι).symm :=
  (rfl)

/-- Reconstructing the linear equivalence from the inverse of `permutationAutToAddSubgroupMulEquiv`
recovers the original automorphism. -/
@[simp]
theorem funCongrLeft_symm_permutationAutToAddSubgroupMulEquiv_symm
    (C : Submodule R (ι → R)) [Nontrivial R] (f : TauCeti.permutationAut C) :
    LinearEquiv.funCongrLeft R R
      ((permutationAutToAddSubgroupMulEquiv C).symm f : Equiv.Perm ι).symm =
      (f : (ι → R) ≃ₗ[R] (ι → R)) := by
  rw [← coe_permutationAutToAddSubgroupMulEquiv_apply, MulEquiv.apply_symm_apply]

/-- The action of `permutationAutToAddSubgroupMulEquiv C e` on codewords agrees with coordinate
composition by `e.symm`. -/
theorem coe_smul_permutationAutToAddSubgroupMulEquiv (C : Submodule R (ι → R)) [Nontrivial R]
    (e : permutationAut C.toAddSubgroup) (x : C) :
    ((permutationAutToAddSubgroupMulEquiv C e • x : C) : ι → R) =
      (x : ι → R) ∘ (e : Equiv.Perm ι).symm := by
  ext j
  simp

/-- Over a nontrivial ring, the additive and linear permutation automorphism groups of a linear code
have the same cardinality. -/
theorem natCard_permutationAut_toAddSubgroup (C : Submodule R (ι → R)) [Nontrivial R] :
    Nat.card (permutationAut C.toAddSubgroup) = Nat.card (TauCeti.permutationAut C) :=
  Nat.card_congr (permutationAutToAddSubgroupMulEquiv C).toEquiv

end Ring

section Linear

variable {F : Type*} [Field F]

/-- Forgetting scalar closure commutes with coordinate relabelling. -/
@[simp]
theorem reindex_toAddSubgroup (C : LinearCode F ι) (e : κ ≃ ι) :
    reindex C.toAddSubgroup e = (TauCeti.reindex C e).toAddSubgroup := by
  rw [TauCeti.reindex_def]
  exact reindex_toAddSubgroup_eq_map C e

/-- Coordinate permutation automorphisms of a reindexed linear code conjugate along `e`. -/
theorem mem_permutationAut_reindex_toAddSubgroup {C : LinearCode F ι} {e : κ ≃ ι}
    {σ : Equiv.Perm κ} :
    σ ∈ permutationAut (TauCeti.reindex C e).toAddSubgroup ↔
      e.permCongr σ ∈ permutationAut C.toAddSubgroup := by
  rw [← reindex_toAddSubgroup, mem_permutationAut_reindex]

end Linear

end TauCeti.AdditiveCode
