/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Monomial
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.Int.Order.Units
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.InformationTheory.Hamming
public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic

/-!
# Monomial and permutation equivalences of linear codes

A *monomial* transformation of the coordinate space `ι → R` rescales each coordinate by a unit
of `R` and then relabels the coordinates along an equivalence of index types; a *permutation*
transformation only relabels. Two linear codes — unbundled submodules of coordinate spaces — are
monomially, respectively permutation, equivalent when such a transformation carries one onto the
other. These are the transformations preserving all Hamming data of a code, so weights, weight
distributions, pairwise Hamming distances and minimum distance are invariants of the resulting
equivalence classes.

The coordinate transformations and their ambient monomial and permutation groups are defined
in `TauCeti.LinearAlgebra.Monomial`. This file develops their Hamming invariants and their
actions on codes.

## Main definitions

* `TauCeti.signedEquiv u e`: the monomial equivalence induced by integer signs and a coordinate
  relabelling, available over every commutative ring.
* `TauCeti.IsMonomialEquivalent`, `TauCeti.IsPermutationEquivalent`: the two resulting
  equivalence relations on linear codes.
* `TauCeti.monomialAut C`: the monomial automorphism group of a code, acting on its codewords.
* `TauCeti.permutationAut C`: the coordinate-permutation automorphism group of a code.

## Main statements

* `TauCeti.hammingNorm_monomialEquiv`, `TauCeti.hammingDist_monomialEquiv`: a monomial
  equivalence preserves Hamming weight and Hamming distance.
* `TauCeti.IsMonomialEquivalent.finrank_eq`, `TauCeti.IsMonomialEquivalent.card_eq`:
  monomially equivalent codes have the same dimension and the same number of codewords.
* `TauCeti.IsPermutationEquivalent.finrank_eq`, `TauCeti.IsPermutationEquivalent.card_eq`: the
  corresponding invariants for permutation-equivalent codes.
* `TauCeti.IsMonomialEquivalent.hammingMinDist_eq`,
  `TauCeti.IsPermutationEquivalent.hammingMinDist_eq`: equivalent codes have the same minimum
  distance, including under the zero-code convention.
* `TauCeti.monomialGroup_eq_permutationGroup`,
  `TauCeti.isMonomialEquivalent_iff_isPermutationEquivalent`,
  `TauCeti.monomialAut_eq_permutationAut`: over a ring whose only unit is one — the binary field
  in particular — monomial transformations are exactly coordinate permutations, so the two
  notions of equivalence and the two automorphism groups agree.

Invariance of the weight distribution and weight enumerator is in
`TauCeti.InformationTheory.Coding.Weight.Enumerator`.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §1.6.
-/

public section

open Function Matrix

namespace TauCeti

variable {ι κ μ R : Type*}

/-! ### Monomial transformations of a coordinate space -/

section Monomial

variable [CommSemiring R]

section Fintype

variable [Fintype ι] [Fintype κ] [DecidableEq R]

/-- A monomial equivalence of finite coordinate spaces preserves Hamming weight. -/
@[simp]
theorem hammingNorm_monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) :
    hammingNorm (monomialEquiv u e x) = hammingNorm x := by
  rw [monomialEquiv_apply_eq_comp, Equiv.hammingNorm_comp]
  exact hammingNorm_comp (fun i (c : R) ↦ (u i : R) * c)
    (fun i ↦ (u i).isUnit.mul_right_injective) fun _ ↦ mul_zero _

/-- A monomial equivalence of finite coordinate spaces preserves Hamming distance. -/
@[simp]
theorem hammingDist_monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) (x y : ι → R) :
    hammingDist (monomialEquiv u e x) (monomialEquiv u e y) = hammingDist x y := by
  rw [monomialEquiv_apply_eq_comp, monomialEquiv_apply_eq_comp, Equiv.hammingDist_comp]
  exact hammingDist_comp (fun i (c : R) ↦ (u i : R) * c)
    fun i ↦ (u i).isUnit.mul_right_injective

end Fintype

end Monomial

/-! ### Signed coordinate transformations -/

section Signed

variable [CommRing R]

/-- The monomial equivalence which multiplies coordinates by integer signs before relabelling
them.  It specializes coherently to every commutative ring. -/
def signedEquiv (u : ι → ℤˣ) (e : ι ≃ κ) : (ι → R) ≃ₗ[R] (κ → R) :=
  monomialEquiv (fun i ↦ Units.map (Int.castRingHom R) (u i)) e

/-- With trivial signs a signed coordinate change is a bare relabelling of coordinates. -/
theorem signedEquiv_one (e : ι ≃ κ) :
    signedEquiv (R := R) (1 : ι → ℤˣ) e = LinearEquiv.funCongrLeft R R e.symm := by
  rw [signedEquiv]
  convert monomialEquiv_one (R := R) e using 1
  ext i
  simp

/-- Evaluation of a signed coordinate change. -/
@[simp]
theorem signedEquiv_apply (u : ι → ℤˣ) (e : ι ≃ κ) (x : ι → R) (j : κ) :
    signedEquiv (R := R) u e x j = (u (e.symm j) : R) * x (e.symm j) := by
  simp [signedEquiv]

/-- The additive homomorphism underlying a signed coordinate change has the same action as the
ambient linear equivalence. -/
@[simp]
theorem signedEquiv_toAddMonoidHom_apply (u : ι → ℤˣ) (e : ι ≃ κ) (x : ι → R) :
    (signedEquiv (R := R) u e).toAddEquiv.toAddMonoidHom x = signedEquiv u e x := rfl

/-- Signed coordinate changes commute with taking integer coordinates in any commutative ring. -/
@[simp]
theorem signedEquiv_intCast (u : ι → ℤˣ) (e : ι ≃ κ) (z : ι → ℤ) :
    signedEquiv (R := R) u e (fun i ↦ (z i : R)) =
      fun j ↦ ((signedEquiv (R := ℤ) u e z j : ℤ) : R) := by
  funext j
  simp [signedEquiv_apply]

/-- Restricting a rational signed coordinate change to integer scalars does not change its
underlying function. -/
@[simp]
theorem signedEquiv_restrictScalars_apply (u : ι → ℤˣ) (e : ι ≃ κ) (x : ι → ℚ) :
    (signedEquiv (R := ℚ) u e).restrictScalars ℤ x = signedEquiv u e x := rfl

/-- A monomial coordinate change agrees with a signed coordinate change when its
coordinate units are images of integer units. -/
theorem monomialEquiv_eq_signedEquiv_of_intUnits (u : ι → Rˣ) (e : ι ≃ κ)
    (v : ι → ℤˣ) (hv : ∀ i, (v i : R) = u i) :
    monomialEquiv u e = signedEquiv v e := by
  ext x j
  rw [monomialEquiv_apply, signedEquiv_apply, hv]

/-- A monomial map over a commutative ring is a signed coordinate change exactly when
each multiplier is `1` or `-1`. -/
theorem exists_signed_monomialEquiv_iff (u : ι → Rˣ) (e : ι ≃ κ) :
    (∃ v : ι → ℤˣ, monomialEquiv u e = signedEquiv v e) ↔
      ∀ i, u i = 1 ∨ u i = -1 := by
  classical
  constructor
  · rintro ⟨v, hv⟩ i
    have hi : (u i : R) = (v i : R) := by
      have h := congrArg
        (fun f : (ι → R) ≃ₗ[R] (κ → R) ↦
          f (Pi.single i 1) (e i)) hv
      simpa [monomialEquiv_apply, signedEquiv_apply] using h
    obtain h | h := Int.units_eq_one_or (v i)
    · left
      apply Units.ext
      simpa [h] using hi
    · right
      apply Units.ext
      simpa [h] using hi
  · intro hu
    let v : ι → ℤˣ := fun i ↦ if u i = 1 then 1 else -1
    have hv (i : ι) : (v i : R) = u i := by
      obtain h | h := hu i
      · simp [v, h]
      · by_cases h1 : u i = 1
        · simp [v, h1]
        · simp only [v, h1, ↓reduceIte]
          simpa using congrArg (fun a : Rˣ ↦ (a : R)) h.symm
    exact ⟨v, monomialEquiv_eq_signedEquiv_of_intUnits u e v hv⟩

section Fintype

variable [Fintype ι] [Fintype κ]

/-- A signed coordinate change preserves the standard dot product. -/
@[simp]
theorem dotProduct_signedEquiv (u : ι → ℤˣ) (e : ι ≃ κ) (x y : ι → R) :
    signedEquiv u e x ⬝ᵥ signedEquiv u e y = x ⬝ᵥ y := by
  apply (dotProduct_monomialEquiv_iff
    (fun i ↦ Units.map (Int.castRingHom R) (u i)) e).mpr
    (by
      intro i
      have hu : (u i : R) ^ 2 = 1 := by
        calc
          (u i : R) ^ 2 = (((u i : ℤ) ^ 2 : ℤ) : R) := by norm_cast
          _ = 1 := by simp only [← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one,
            Int.cast_one]
      simpa using hu) x y

end Fintype

end Signed

end TauCeti

namespace TauCeti

/-! ### Permutation equivalence of linear codes -/

section PermutationEquivalence

variable [Semiring R] {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}
  {E : Submodule R (μ → R)}

/-- Two linear codes are *permutation equivalent* when a relabelling of the coordinates carries
one onto the other. -/
def IsPermutationEquivalent (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) : Prop :=
  ∃ e : ι ≃ κ, C.map (LinearEquiv.funCongrLeft R R e.symm : (ι → R) →ₗ[R] (κ → R)) = D

/-- Unfolds permutation equivalence to the existence of a relabelling carrying one code onto the
other. -/
theorem isPermutationEquivalent_iff :
    IsPermutationEquivalent C D ↔
      ∃ e : ι ≃ κ, C.map (LinearEquiv.funCongrLeft R R e.symm : (ι → R) →ₗ[R] (κ → R)) = D :=
  Iff.rfl

/-- A coordinate relabelling that maps one code onto another restricts to a linear equivalence
between their codewords. -/
def permutationCodeEquiv (e : ι ≃ κ)
    (h : C.map (LinearEquiv.funCongrLeft R R e.symm : (ι → R) →ₗ[R] (κ → R)) = D) :
    C ≃ₗ[R] D :=
  (LinearEquiv.funCongrLeft R R e.symm).ofSubmodules C D h

/-- `permutationCodeEquiv` acts on codewords by the ambient relabelling
`LinearEquiv.funCongrLeft R R e.symm`, in its simp normal form `LinearMap.funLeft R R e.symm`. -/
@[simp]
theorem coe_permutationCodeEquiv_apply (e : ι ≃ κ)
    (h : C.map (LinearEquiv.funCongrLeft R R e.symm : (ι → R) →ₗ[R] (κ → R)) = D) (x : C) :
    (permutationCodeEquiv e h x : κ → R) = LinearMap.funLeft R R e.symm x :=
  (rfl)

/-- The inverse of `permutationCodeEquiv` acts on codewords by the inverse relabelling. -/
@[simp]
theorem coe_permutationCodeEquiv_symm_apply (e : ι ≃ κ)
    (h : C.map (LinearEquiv.funCongrLeft R R e.symm : (ι → R) →ₗ[R] (κ → R)) = D) (y : D) :
    ((permutationCodeEquiv e h).symm y : ι → R) = LinearMap.funLeft R R e y :=
  (rfl)

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

/-- Permutation-equivalent codes have the same minimum distance. -/
theorem IsPermutationEquivalent.hammingMinDist_eq [Fintype ι] [Fintype κ] [DecidableEq R]
    (h : IsPermutationEquivalent C D) :
    (C : Set (ι → R)).hammingMinDist = (D : Set (κ → R)).hammingMinDist := by
  obtain ⟨e, rfl⟩ := h
  rw [Submodule.map_coe]
  exact (Set.hammingMinDist_image _ fun x _ y _ _ ↦ Equiv.hammingDist_funLeft e.symm x y).symm

end PermutationEquivalence

/-! ### Monomial equivalence of linear codes -/

section MonomialEquivalence

variable [CommSemiring R] {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}
  {E : Submodule R (μ → R)}

/-- Two linear codes are *monomially equivalent* when some monomial transformation of the
coordinate spaces carries one onto the other. -/
def IsMonomialEquivalent (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) : Prop :=
  ∃ (u : ι → Rˣ) (e : ι ≃ κ), C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R)) = D

/-- Unfolds monomial equivalence to the existence of a monomial transformation carrying one code
onto the other. -/
theorem isMonomialEquivalent_iff :
    IsMonomialEquivalent C D ↔
      ∃ (u : ι → Rˣ) (e : ι ≃ κ), C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R)) = D :=
  Iff.rfl

/-- A monomial transformation that maps one code onto another restricts to a linear equivalence
between their codewords. -/
def monomialCodeEquiv (u : ι → Rˣ) (e : ι ≃ κ)
    (h : C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R)) = D) : C ≃ₗ[R] D :=
  (monomialEquiv u e).ofSubmodules C D h

/-- `monomialCodeEquiv` acts on codewords by the ambient monomial transformation. -/
@[simp]
theorem coe_monomialCodeEquiv_apply (u : ι → Rˣ) (e : ι ≃ κ)
    (h : C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R)) = D) (x : C) :
    (monomialCodeEquiv u e h x : κ → R) = monomialEquiv u e x :=
  (rfl)

/-- The inverse of `monomialCodeEquiv` acts on codewords by the inverse monomial
transformation. -/
@[simp]
theorem coe_monomialCodeEquiv_symm_apply (u : ι → Rˣ) (e : ι ≃ κ)
    (h : C.map (monomialEquiv u e : (ι → R) →ₗ[R] (κ → R)) = D) (y : D) :
    ((monomialCodeEquiv u e h).symm y : ι → R) = (monomialEquiv u e).symm y :=
  (rfl)

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

/-- A monomial equivalence matches every word of the target code with a word of the source code
of the same Hamming weight. -/
theorem IsMonomialEquivalent.exists_mem_hammingNorm_eq [Fintype ι] [Fintype κ] [DecidableEq R]
    (h : IsMonomialEquivalent C D) {y : κ → R} (hy : y ∈ D) :
    ∃ x ∈ C, hammingNorm x = hammingNorm y := by
  obtain ⟨u, e, rfl⟩ := h
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, (hammingNorm_monomialEquiv u e x).symm⟩

/-- Monomial equivalence preserves divisibility of all codeword weights. -/
theorem IsMonomialEquivalent.forall_dvd_hammingNorm_iff [Fintype ι] [Fintype κ]
    [DecidableEq R] (h : IsMonomialEquivalent C D) (k : ℕ) :
    (∀ x ∈ C, k ∣ hammingNorm x) ↔ ∀ y ∈ D, k ∣ hammingNorm y := by
  constructor
  · intro hC y hy
    obtain ⟨x, hx, hxy⟩ := h.exists_mem_hammingNorm_eq hy
    rw [← hxy]
    exact hC x hx
  · intro hD x hx
    obtain ⟨y, hy, hyx⟩ := h.symm.exists_mem_hammingNorm_eq hx
    rw [← hyx]
    exact hD y hy

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

/-- Monomially equivalent codes have the same minimum distance. -/
theorem IsMonomialEquivalent.hammingMinDist_eq [Fintype ι] [Fintype κ] [DecidableEq R]
    (h : IsMonomialEquivalent C D) :
    (C : Set (ι → R)).hammingMinDist = (D : Set (κ → R)).hammingMinDist := by
  obtain ⟨u, e, rfl⟩ := h
  rw [Submodule.map_coe]
  exact (Set.hammingMinDist_image _ fun x _ y _ _ ↦ hammingDist_monomialEquiv u e x y).symm

end MonomialEquivalence

/-! ### The monomial group and the automorphism group of a code -/

section Group

variable [CommSemiring R]

/-- A monomial-group element preserves Hamming weight. -/
theorem hammingNorm_apply_of_mem_monomialGroup [Fintype ι] [DecidableEq R]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ monomialGroup R ι) (x : ι → R) :
    hammingNorm (f x) = hammingNorm x := by
  obtain ⟨u, e, rfl⟩ := mem_monomialGroup.mp hf
  exact hammingNorm_monomialEquiv u e x

/-- A monomial-group element preserves Hamming distance. -/
theorem hammingDist_apply_of_mem_monomialGroup [Fintype ι] [DecidableEq R]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ monomialGroup R ι) (x y : ι → R) :
    hammingDist (f x) (f y) = hammingDist x y := by
  obtain ⟨u, e, rfl⟩ := mem_monomialGroup.mp hf
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

/-- Monomial automorphisms act by `R`-linear maps, so their action on codewords commutes with
the scalar action. -/
instance instSMulCommClassMonomialAut : SMulCommClass R (monomialAut C) C where
  smul_comm _ _ _ := Subtype.ext (by simp)

/-- The converse orientation of `TauCeti.instSMulCommClassMonomialAut`: the monomial
automorphism action on codewords commutes with the scalar action of `R`. -/
instance instSMulCommClassMonomialAut' : SMulCommClass (monomialAut C) R C :=
  SMulCommClass.symm _ _ _

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

variable [Semiring R]

/-- A permutation-group element preserves Hamming weight. -/
theorem hammingNorm_apply_of_mem_permutationGroup [Fintype ι] [DecidableEq R]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ permutationGroup R ι) (x : ι → R) :
    hammingNorm (f x) = hammingNorm x := by
  obtain ⟨e, rfl⟩ := mem_permutationGroup.mp hf
  exact Equiv.hammingNorm_funLeft e.symm x

/-- A permutation-group element preserves Hamming distance. -/
theorem hammingDist_apply_of_mem_permutationGroup [Fintype ι] [DecidableEq R]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ permutationGroup R ι) (x y : ι → R) :
    hammingDist (f x) (f y) = hammingDist x y := by
  obtain ⟨e, rfl⟩ := mem_permutationGroup.mp hf
  exact Equiv.hammingDist_funLeft e.symm x y

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

/-- Permutation automorphisms act by `R`-linear maps, so their action on codewords commutes with
the scalar action. -/
instance instSMulCommClassPermutationAut : SMulCommClass R (permutationAut C) C where
  smul_comm _ _ _ := Subtype.ext (by simp)

/-- The converse orientation of `TauCeti.instSMulCommClassPermutationAut`: the permutation
automorphism action on codewords commutes with the scalar action of `R`. -/
instance instSMulCommClassPermutationAut' : SMulCommClass (permutationAut C) R C :=
  SMulCommClass.symm _ _ _

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

/-- A permutation automorphism of a code is a monomial automorphism of it. -/
theorem permutationAut_le_monomialAut : permutationAut C ≤ monomialAut C := fun _ hf ↦
  mem_monomialAut.2 ⟨permutationGroup_le_monomialGroup (mem_permutationAut.1 hf).1,
    (mem_permutationAut.1 hf).2⟩

end PermutationLeMonomial

/-! ### Monomial transformations when one is the only unit -/

section TrivialUnits

variable [CommSemiring R] [Subsingleton Rˣ]

/-- When one is the only unit, monomial equivalence is permutation equivalence. -/
@[simp]
theorem isMonomialEquivalent_iff_isPermutationEquivalent {C : Submodule R (ι → R)}
    {D : Submodule R (κ → R)} : IsMonomialEquivalent C D ↔ IsPermutationEquivalent C D := by
  refine ⟨?_, IsPermutationEquivalent.isMonomialEquivalent⟩
  rintro ⟨u, e, h⟩
  exact ⟨e, (monomialEquiv_eq_funCongrLeft u e) ▸ h⟩

/-- When one is the only unit, the monomial and permutation automorphism groups of a code
coincide. -/
@[simp]
theorem monomialAut_eq_permutationAut (C : Submodule R (ι → R)) :
    monomialAut C = permutationAut C := by
  ext f
  rw [mem_monomialAut, mem_permutationAut, monomialGroup_eq_permutationGroup]

end TrivialUnits

end TauCeti
