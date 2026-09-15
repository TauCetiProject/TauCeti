/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Pi
public import TauCeti.InformationTheory.Hamming

/-!
# Monomial and permutation equivalences of linear codes

A *monomial* transformation of the coordinate space `ι → R` rescales each coordinate by a unit
of `R` and then relabels the coordinates along an equivalence of index types; a *permutation*
transformation only relabels. Two linear codes — unbundled submodules of coordinate spaces — are
monomially, respectively permutation, equivalent when such a transformation carries one onto the
other. These are the transformations preserving all Hamming data of a code, so weights, weight
distributions and pairwise Hamming distances are invariants of the resulting equivalence classes.

## Main definitions

* `TauCeti.monomialEquiv u e`: the monomial linear equivalence `(ι → R) ≃ₗ[R] (κ → R)` that
  rescales the `i`-th coordinate by the unit `u i` and moves it to the coordinate `e i`.
* `TauCeti.IsMonomialEquivalent`, `TauCeti.IsPermutationEquivalent`: the two resulting
  equivalence relations on linear codes.
* `TauCeti.monomialGroup R ι`: the group of monomial transformations of `ι → R`.
* `TauCeti.monomialAut C`: the monomial automorphism group of a code, acting on its codewords.
* `TauCeti.permutationGroup R ι`, `TauCeti.permutationAut C`: the corresponding permutation
  group and code automorphism group.

## Main statements

* `TauCeti.hammingNorm_monomialEquiv`, `TauCeti.hammingDist_monomialEquiv`: a monomial
  equivalence preserves Hamming weight and Hamming distance.
* `TauCeti.IsMonomialEquivalent.finrank_eq`, `TauCeti.IsMonomialEquivalent.card_eq`,
  `TauCeti.IsMonomialEquivalent.card_weight_eq`: monomially equivalent codes have the same
  dimension, the same number of codewords, and the same weight distribution.
* `TauCeti.IsPermutationEquivalent.finrank_eq`, `TauCeti.IsPermutationEquivalent.card_eq`,
  `TauCeti.IsPermutationEquivalent.card_weight_eq`: the corresponding invariants for
  permutation-equivalent codes.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §1.6.
-/

public section

open Function

namespace TauCeti

variable {ι κ μ R : Type*}

/-! ### Monomial transformations of a coordinate space -/

section Monomial

variable [CommSemiring R]

/-- The monomial equivalence of coordinate spaces attached to a family of units `u : ι → Rˣ`
and a relabelling `e : ι ≃ κ` of coordinates: it rescales the `i`-th coordinate by `u i` and
places the result in the coordinate `e i`. -/
def monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) : (ι → R) ≃ₗ[R] (κ → R) :=
  (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.smulOfUnit (M := R) (u i)).trans
    (LinearEquiv.funCongrLeft R R e.symm)

@[simp]
theorem monomialEquiv_apply (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) (j : κ) :
    monomialEquiv u e x j = u (e.symm j) * x (e.symm j) :=
  (rfl)

@[simp]
theorem monomialEquiv_symm_apply (u : ι → Rˣ) (e : ι ≃ κ) (y : κ → R) (i : ι) :
    (monomialEquiv u e).symm y i = ↑(u i)⁻¹ * y (e i) :=
  (rfl)

/-- With trivial scalars a monomial equivalence is a bare relabelling of coordinates. -/
theorem monomialEquiv_one (e : ι ≃ κ) :
    monomialEquiv (1 : ι → Rˣ) e = LinearEquiv.funCongrLeft R R e.symm :=
  LinearEquiv.ext fun x ↦ funext fun j ↦ by simp

theorem monomialEquiv_trans (u : ι → Rˣ) (e : ι ≃ κ) (v : κ → Rˣ) (f : κ ≃ μ) :
    (monomialEquiv u e).trans (monomialEquiv v f) =
      monomialEquiv (fun i ↦ u i * v (e i)) (e.trans f) := by
  refine LinearEquiv.ext fun x ↦ funext fun m ↦ ?_
  simp only [LinearEquiv.trans_apply, monomialEquiv_apply, Equiv.symm_trans_apply,
    Equiv.apply_symm_apply, Units.val_mul]
  ring

theorem monomialEquiv_symm (u : ι → Rˣ) (e : ι ≃ κ) :
    (monomialEquiv u e).symm = monomialEquiv (fun j ↦ (u (e.symm j))⁻¹) e.symm :=
  LinearEquiv.ext fun y ↦ funext fun i ↦ by simp

/-- A monomial equivalence transports support along its coordinate equivalence. -/
@[simp]
theorem support_monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) :
    support (monomialEquiv u e x) = e '' support x := by
  rw [Equiv.image_eq_preimage_symm]
  ext j
  simp [Units.mul_right_eq_zero]

private theorem monomialEquiv_eq_comp (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) :
    (monomialEquiv u e x : κ → R) = (fun i ↦ (u i : R) * x i) ∘ e.symm :=
  funext fun j ↦ by simp

section Fintype

variable [Fintype ι] [Fintype κ] [DecidableEq R]

/-- A monomial equivalence of finite coordinate spaces preserves Hamming weight. -/
@[simp]
theorem hammingNorm_monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) :
    hammingNorm (monomialEquiv u e x) = hammingNorm x := by
  rw [monomialEquiv_eq_comp, Equiv.hammingNorm_comp]
  exact hammingNorm_comp (fun i (c : R) ↦ (u i : R) * c)
    (fun i ↦ (u i).isUnit.mul_right_injective) fun _ ↦ mul_zero _

/-- A monomial equivalence of finite coordinate spaces preserves Hamming distance. -/
@[simp]
theorem hammingDist_monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) (x y : ι → R) :
    hammingDist (monomialEquiv u e x) (monomialEquiv u e y) = hammingDist x y := by
  rw [monomialEquiv_eq_comp, monomialEquiv_eq_comp, Equiv.hammingDist_comp]
  exact hammingDist_comp (fun i (c : R) ↦ (u i : R) * c)
    fun i ↦ (u i).isUnit.mul_right_injective

end Fintype

end Monomial

/-! ### Permutation equivalence of linear codes -/

section PermutationEquivalence

variable [Semiring R] {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}
  {E : Submodule R (μ → R)}

/-- Two linear codes are *permutation equivalent* when a relabelling of the coordinates carries
one onto the other. -/
def IsPermutationEquivalent (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) : Prop :=
  ∃ e : ι ≃ κ, C.map (LinearEquiv.funCongrLeft R R e.symm : (ι → R) →ₗ[R] (κ → R)) = D

/-- A coordinate relabelling that maps one code onto another restricts to a linear equivalence
between their codewords. -/
def permutationCodeEquiv (e : ι ≃ κ)
    (h : C.map (LinearEquiv.funCongrLeft R R e.symm : (ι → R) →ₗ[R] (κ → R)) = D) :
    C ≃ₗ[R] D :=
  (LinearEquiv.funCongrLeft R R e.symm).ofSubmodules C D h

@[refl]
theorem IsPermutationEquivalent.refl (C : Submodule R (ι → R)) : IsPermutationEquivalent C C :=
  ⟨Equiv.refl ι, by simp⟩

@[symm]
theorem IsPermutationEquivalent.symm (h : IsPermutationEquivalent C D) :
    IsPermutationEquivalent D C := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  have h' := (Submodule.map_symm_eq_iff (LinearEquiv.funCongrLeft R R e.symm)).2 he
  rwa [LinearEquiv.funCongrLeft_symm] at h'

@[trans]
theorem IsPermutationEquivalent.trans (h : IsPermutationEquivalent C D)
    (h' : IsPermutationEquivalent D E) : IsPermutationEquivalent C E := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨f, rfl⟩ := h'
  exact ⟨e.trans f, by
    rw [Equiv.symm_trans, LinearEquiv.funCongrLeft_comp, LinearEquiv.coe_trans,
      Submodule.map_comp]⟩

/-- Permutation-equivalent codes have the same dimension. -/
theorem IsPermutationEquivalent.finrank_eq (h : IsPermutationEquivalent C D) :
    Module.finrank R C = Module.finrank R D := by
  obtain ⟨e, rfl⟩ := h
  exact (LinearEquiv.finrank_map_eq _ _).symm

/-- Permutation-equivalent codes have the same number of codewords. -/
theorem IsPermutationEquivalent.card_eq (h : IsPermutationEquivalent C D) :
    Nat.card C = Nat.card D := by
  obtain ⟨e, rfl⟩ := h
  exact Nat.card_congr
    ((LinearEquiv.funCongrLeft R R e.symm).submoduleMap C).toEquiv

/-- Permutation-equivalent codes have the same weight distribution. -/
theorem IsPermutationEquivalent.card_weight_eq [Fintype ι] [Fintype κ] [DecidableEq R]
    (h : IsPermutationEquivalent C D) (w : ℕ) :
    Nat.card {x : ι → R // x ∈ C ∧ hammingNorm x = w} =
      Nat.card {y : κ → R // y ∈ D ∧ hammingNorm y = w} := by
  obtain ⟨e, rfl⟩ := h
  exact Nat.card_congr
    (Equiv.subtypeEquiv (LinearEquiv.funCongrLeft R R e.symm).toEquiv fun x ↦ by
      simp only [LinearEquiv.coe_toEquiv, LinearEquiv.funCongrLeft_apply,
        Submodule.mem_map_equiv, LinearEquiv.funCongrLeft_symm, Equiv.symm_symm]
      have hinv :
          LinearMap.funLeft R R e (LinearMap.funLeft R R e.symm x) = x := by
        funext i
        simp [LinearMap.funLeft_apply]
      have hnorm : hammingNorm (LinearMap.funLeft R R e.symm x) = hammingNorm x := by
        exact Equiv.hammingNorm_comp e.symm x
      rw [hinv, hnorm])

end PermutationEquivalence

/-! ### Monomial equivalence of linear codes -/

section MonomialEquivalence

variable [CommSemiring R] {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}
  {E : Submodule R (μ → R)}

/-- Two linear codes are *monomially equivalent* when some monomial transformation of the
coordinate spaces carries one onto the other. -/
def IsMonomialEquivalent (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) : Prop :=
  ∃ (u : ι → Rˣ) (e : ι ≃ κ), C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R)) = D

/-- A monomial transformation that maps one code onto another restricts to a linear equivalence
between their codewords. -/
def monomialCodeEquiv (u : ι → Rˣ) (e : ι ≃ κ)
    (h : C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R)) = D) : C ≃ₗ[R] D :=
  (monomialEquiv u e).ofSubmodules C D h

theorem IsPermutationEquivalent.isMonomialEquivalent (h : IsPermutationEquivalent C D) :
    IsMonomialEquivalent C D := by
  obtain ⟨e, he⟩ := h
  exact ⟨1, e, by rw [monomialEquiv_one]; exact he⟩

@[refl]
theorem IsMonomialEquivalent.refl (C : Submodule R (ι → R)) : IsMonomialEquivalent C C :=
  (IsPermutationEquivalent.refl C).isMonomialEquivalent

@[symm]
theorem IsMonomialEquivalent.symm (h : IsMonomialEquivalent C D) : IsMonomialEquivalent D C := by
  obtain ⟨u, e, he⟩ := h
  refine ⟨fun j ↦ (u (e.symm j))⁻¹, e.symm, ?_⟩
  rw [← monomialEquiv_symm]
  exact (Submodule.map_symm_eq_iff _).2 he

@[trans]
theorem IsMonomialEquivalent.trans (h : IsMonomialEquivalent C D)
    (h' : IsMonomialEquivalent D E) : IsMonomialEquivalent C E := by
  obtain ⟨u, e, rfl⟩ := h
  obtain ⟨v, f, rfl⟩ := h'
  exact ⟨fun i ↦ u i * v (e i), e.trans f, by
    rw [← monomialEquiv_trans, LinearEquiv.coe_trans, Submodule.map_comp]⟩

/-- Monomially equivalent codes have the same dimension. -/
theorem IsMonomialEquivalent.finrank_eq (h : IsMonomialEquivalent C D) :
    Module.finrank R C = Module.finrank R D := by
  obtain ⟨u, e, rfl⟩ := h
  exact (LinearEquiv.finrank_map_eq _ _).symm

/-- Monomially equivalent codes have the same number of codewords. -/
theorem IsMonomialEquivalent.card_eq (h : IsMonomialEquivalent C D) :
    Nat.card C = Nat.card D := by
  obtain ⟨u, e, rfl⟩ := h
  exact Nat.card_congr ((monomialEquiv u e).submoduleMap C).toEquiv

/-- Monomially equivalent codes have the same weight distribution. -/
theorem IsMonomialEquivalent.card_weight_eq [Fintype ι] [Fintype κ] [DecidableEq R]
    (h : IsMonomialEquivalent C D) (w : ℕ) :
    Nat.card {x : ι → R // x ∈ C ∧ hammingNorm x = w} =
      Nat.card {y : κ → R // y ∈ D ∧ hammingNorm y = w} := by
  obtain ⟨u, e, rfl⟩ := h
  exact Nat.card_congr (Equiv.subtypeEquiv (monomialEquiv u e).toEquiv fun x ↦ by simp)

end MonomialEquivalence

/-! ### The monomial group and the automorphism group of a code -/

section Group

/-- The group of monomial transformations of the coordinate space `ι → R`, as a subgroup of its
group of linear automorphisms. -/
def monomialGroup (R ι : Type*) [CommSemiring R] : Subgroup ((ι → R) ≃ₗ[R] (ι → R)) where
  carrier := {f | ∃ (u : ι → Rˣ) (e : Equiv.Perm ι), monomialEquiv u e = f}
  one_mem' := ⟨1, Equiv.refl ι, by
    rw [monomialEquiv_one, Equiv.refl_symm, LinearEquiv.funCongrLeft_id,
      LinearEquiv.one_eq_refl]⟩
  mul_mem' := by
    rintro f g ⟨u, e, rfl⟩ ⟨v, d, rfl⟩
    exact ⟨fun i ↦ v i * u (d i), d.trans e, by
      rw [← monomialEquiv_trans, LinearEquiv.mul_eq_trans]⟩
  inv_mem' := by
    rintro f ⟨u, e, rfl⟩
    exact ⟨fun j ↦ (u (e.symm j))⁻¹, e.symm, (monomialEquiv_symm u e).symm⟩

variable [CommSemiring R]

/-- The monomial group consists exactly of the monomial transformations of `ι → R`. -/
@[simp]
theorem mem_monomialGroup {f : (ι → R) ≃ₗ[R] (ι → R)} :
    f ∈ monomialGroup R ι ↔ ∃ (u : ι → Rˣ) (e : Equiv.Perm ι), monomialEquiv u e = f :=
  Iff.rfl

theorem monomialEquiv_mem_monomialGroup (u : ι → Rˣ) (e : Equiv.Perm ι) :
    monomialEquiv u e ∈ monomialGroup R ι :=
  ⟨u, e, rfl⟩

/-- A monomial-group element preserves Hamming weight. -/
theorem hammingNorm_apply_of_mem_monomialGroup [Fintype ι] [DecidableEq R]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ monomialGroup R ι) (x : ι → R) :
    hammingNorm (f x) = hammingNorm x := by
  obtain ⟨u, e, rfl⟩ := hf
  exact hammingNorm_monomialEquiv u e x

/-- A monomial-group element preserves Hamming distance. -/
theorem hammingDist_apply_of_mem_monomialGroup [Fintype ι] [DecidableEq R]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ monomialGroup R ι) (x y : ι → R) :
    hammingDist (f x) (f y) = hammingDist x y := by
  obtain ⟨u, e, rfl⟩ := hf
  exact hammingDist_monomialEquiv u e x y

variable (C : Submodule R (ι → R))

/-- The monomial automorphism group of a linear code: the monomial transformations of its
coordinate space that map the code onto itself. -/
def monomialAut : Subgroup ((ι → R) ≃ₗ[R] (ι → R)) where
  carrier := {f | f ∈ monomialGroup R ι ∧ C.map (f : (ι → R) →ₗ[R] (ι → R)) = C}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨mul_mem hf hg, ?_⟩
    rw [LinearEquiv.mul_eq_trans, LinearEquiv.coe_trans, Submodule.map_comp, hg', hf']
  inv_mem' := by
    rintro f ⟨hf, hf'⟩
    -- The inverse in `LinearEquiv.automorphismGroup` is the inverse equivalence.
    have hinv : (f : (ι → R) ≃ₗ[R] (ι → R))⁻¹ = f.symm := rfl
    exact ⟨inv_mem hf, by rw [hinv]; exact (Submodule.map_symm_eq_iff _).2 hf'⟩

variable {C}

/-- The monomial automorphism group of `C` consists exactly of the monomial transformations
mapping `C` onto itself. -/
@[simp]
theorem mem_monomialAut {f : (ι → R) ≃ₗ[R] (ι → R)} :
    f ∈ monomialAut C ↔ f ∈ monomialGroup R ι ∧ C.map (f : (ι → R) →ₗ[R] (ι → R)) = C :=
  Iff.rfl

theorem monomialAut_le_monomialGroup : monomialAut C ≤ monomialGroup R ι :=
  fun _ hf ↦ hf.1

theorem apply_mem_of_mem_monomialAut {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ monomialAut C)
    {x : ι → R} (hx : x ∈ C) : f x ∈ C :=
  hf.2 ▸ Submodule.mem_map_of_mem hx

/-- A monomial automorphism of a code permutes its codewords. -/
instance instSMulMonomialAut : SMul (monomialAut C) C where
  smul f c := ⟨(f : (ι → R) ≃ₗ[R] (ι → R)) c, apply_mem_of_mem_monomialAut f.2 c.2⟩

@[simp]
theorem coe_smul_monomialAut (f : monomialAut C) (c : C) :
    ((f • c : C) : ι → R) = (f : (ι → R) ≃ₗ[R] (ι → R)) c :=
  (rfl)

instance instDistribMulActionMonomialAut : DistribMulAction (monomialAut C) C where
  one_smul _ := Subtype.ext (by simp)
  mul_smul _ _ _ := Subtype.ext (by simp)
  smul_zero _ := Subtype.ext (by simp)
  smul_add _ _ _ := Subtype.ext (by simp)

/-- A monomial automorphism of a code preserves Hamming weight. -/
@[simp]
theorem hammingNorm_monomialAut_apply [Fintype ι] [DecidableEq R]
    (f : monomialAut C) (x : ι → R) :
    hammingNorm ((f : (ι → R) ≃ₗ[R] (ι → R)) x) = hammingNorm x :=
  hammingNorm_apply_of_mem_monomialGroup (monomialAut_le_monomialGroup f.2) x

/-- A monomial automorphism of a code preserves Hamming distance. -/
@[simp]
theorem hammingDist_monomialAut_apply [Fintype ι] [DecidableEq R]
    (f : monomialAut C) (x y : ι → R) :
    hammingDist ((f : (ι → R) ≃ₗ[R] (ι → R)) x) ((f : (ι → R) ≃ₗ[R] (ι → R)) y) =
      hammingDist x y :=
  hammingDist_apply_of_mem_monomialGroup (monomialAut_le_monomialGroup f.2) x y

end Group

/-! ### The permutation group and the permutation automorphism group of a code -/

section PermutationGroup

/-- The group of coordinate permutations of `ι → R`, as a subgroup of its group of linear
automorphisms. -/
def permutationGroup (R ι : Type*) [Semiring R] : Subgroup ((ι → R) ≃ₗ[R] (ι → R)) where
  carrier := {f | ∃ e : Equiv.Perm ι, LinearEquiv.funCongrLeft R R e.symm = f}
  one_mem' := ⟨Equiv.refl ι, by
    rw [Equiv.refl_symm, LinearEquiv.funCongrLeft_id, LinearEquiv.one_eq_refl]⟩
  mul_mem' := by
    rintro f g ⟨e, rfl⟩ ⟨d, rfl⟩
    exact ⟨d.trans e, by
      rw [Equiv.symm_trans, LinearEquiv.funCongrLeft_comp, LinearEquiv.mul_eq_trans]⟩
  inv_mem' := by
    rintro f ⟨e, rfl⟩
    exact ⟨e.symm, by rw [Equiv.symm_symm, ← LinearEquiv.funCongrLeft_symm]; rfl⟩

variable [Semiring R]

/-- The permutation group consists exactly of the coordinate relabellings of `ι → R`. -/
@[simp]
theorem mem_permutationGroup {f : (ι → R) ≃ₗ[R] (ι → R)} :
    f ∈ permutationGroup R ι ↔ ∃ e : Equiv.Perm ι, LinearEquiv.funCongrLeft R R e.symm = f :=
  Iff.rfl

/-- A coordinate relabelling belongs to the permutation group. -/
theorem funCongrLeft_mem_permutationGroup (e : Equiv.Perm ι) :
    LinearEquiv.funCongrLeft R R e.symm ∈ permutationGroup R ι :=
  ⟨e, rfl⟩

/-- A permutation-group element preserves Hamming weight. -/
theorem hammingNorm_apply_of_mem_permutationGroup [Fintype ι] [DecidableEq R]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ permutationGroup R ι) (x : ι → R) :
    hammingNorm (f x) = hammingNorm x := by
  obtain ⟨e, rfl⟩ := hf
  exact Equiv.hammingNorm_comp e.symm x

/-- A permutation-group element preserves Hamming distance. -/
theorem hammingDist_apply_of_mem_permutationGroup [Fintype ι] [DecidableEq R]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ permutationGroup R ι) (x y : ι → R) :
    hammingDist (f x) (f y) = hammingDist x y := by
  obtain ⟨e, rfl⟩ := hf
  exact Equiv.hammingDist_comp e.symm x y

variable (C : Submodule R (ι → R))

/-- The permutation automorphism group of a linear code: the coordinate permutations that map
the code onto itself. -/
def permutationAut : Subgroup ((ι → R) ≃ₗ[R] (ι → R)) where
  carrier := {f | f ∈ permutationGroup R ι ∧ C.map (f : (ι → R) →ₗ[R] (ι → R)) = C}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨mul_mem hf hg, ?_⟩
    rw [LinearEquiv.mul_eq_trans, LinearEquiv.coe_trans, Submodule.map_comp, hg', hf']
  inv_mem' := by
    rintro f ⟨hf, hf'⟩
    have hinv : (f : (ι → R) ≃ₗ[R] (ι → R))⁻¹ = f.symm := rfl
    exact ⟨inv_mem hf, by rw [hinv]; exact (Submodule.map_symm_eq_iff _).2 hf'⟩

variable {C}

/-- The permutation automorphism group of `C` consists exactly of the coordinate permutations
mapping `C` onto itself. -/
@[simp]
theorem mem_permutationAut {f : (ι → R) ≃ₗ[R] (ι → R)} :
    f ∈ permutationAut C ↔ f ∈ permutationGroup R ι ∧ C.map (f : (ι → R) →ₗ[R] (ι → R)) = C :=
  Iff.rfl

theorem permutationAut_le_permutationGroup : permutationAut C ≤ permutationGroup R ι :=
  fun _ hf ↦ hf.1

theorem apply_mem_of_mem_permutationAut {f : (ι → R) ≃ₗ[R] (ι → R)}
    (hf : f ∈ permutationAut C) {x : ι → R} (hx : x ∈ C) : f x ∈ C :=
  hf.2 ▸ Submodule.mem_map_of_mem hx

/-- A permutation automorphism of a code permutes its codewords. -/
instance instSMulPermutationAut : SMul (permutationAut C) C where
  smul f c := ⟨(f : (ι → R) ≃ₗ[R] (ι → R)) c, apply_mem_of_mem_permutationAut f.2 c.2⟩

@[simp]
theorem coe_smul_permutationAut (f : permutationAut C) (c : C) :
    ((f • c : C) : ι → R) = (f : (ι → R) ≃ₗ[R] (ι → R)) c :=
  (rfl)

instance instDistribMulActionPermutationAut : DistribMulAction (permutationAut C) C where
  one_smul _ := Subtype.ext (by simp)
  mul_smul _ _ _ := Subtype.ext (by simp)
  smul_zero _ := Subtype.ext (by simp)
  smul_add _ _ _ := Subtype.ext (by simp)

/-- A permutation automorphism of a code preserves Hamming weight. -/
@[simp]
theorem hammingNorm_permutationAut_apply [Fintype ι] [DecidableEq R]
    (f : permutationAut C) (x : ι → R) :
    hammingNorm ((f : (ι → R) ≃ₗ[R] (ι → R)) x) = hammingNorm x :=
  hammingNorm_apply_of_mem_permutationGroup (permutationAut_le_permutationGroup f.2) x

/-- A permutation automorphism of a code preserves Hamming distance. -/
@[simp]
theorem hammingDist_permutationAut_apply [Fintype ι] [DecidableEq R]
    (f : permutationAut C) (x y : ι → R) :
    hammingDist ((f : (ι → R) ≃ₗ[R] (ι → R)) x) ((f : (ι → R) ≃ₗ[R] (ι → R)) y) =
      hammingDist x y :=
  hammingDist_apply_of_mem_permutationGroup (permutationAut_le_permutationGroup f.2) x y

end PermutationGroup

/-! ### Permutation transformations as monomial transformations -/

section PermutationLeMonomial

variable [CommSemiring R] {C : Submodule R (ι → R)}

/-- A coordinate permutation is the monomial transformation with all scalars equal to one. -/
theorem permutationGroup_le_monomialGroup : permutationGroup R ι ≤ monomialGroup R ι := by
  intro f hf
  obtain ⟨e, rfl⟩ := mem_permutationGroup.1 hf
  exact mem_monomialGroup.2 ⟨1, e, monomialEquiv_one e⟩

/-- A permutation automorphism of a code is a monomial automorphism of it. -/
theorem permutationAut_le_monomialAut : permutationAut C ≤ monomialAut C := fun _ hf ↦
  mem_monomialAut.2 ⟨permutationGroup_le_monomialGroup (mem_permutationAut.1 hf).1,
    (mem_permutationAut.1 hf).2⟩

end PermutationLeMonomial

end TauCeti
