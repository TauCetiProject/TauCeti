/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Tactic.Abel
import TauCeti.Algebra.DirectSum.Component

/-!
# Signed Leibniz endomorphisms and lower-triangular matrix derivations

Let `A` be an internally `ι`-graded `R`-algebra with grading `𝒜 : ι → Submodule R A`. A linear
endomorphism `d : A →ₗ[R] A` satisfies an `s`-signed Leibniz rule (for a sign function `s : ι → ℤˣ`)
when

`d (a * b) = d a * b + s i • (a * d b)` for `a ∈ 𝒜 i`.

This generalizes the integer-graded Leibniz consequences in
`TauCeti.Algebra.Homology.DG.Algebra.Defs` to arbitrary grading index types `ι` (in particular both
`ℤ` and `ZMod 2`) and arbitrary sign maps `s : ι → ℤˣ`:

* `d` annihilates `1` and `algebraMap R A r`, and its kernel is a subalgebra of `A`, so two
  `s`-signed Leibniz maps that agree on an algebra-generating set are equal;
* if `d` shifts the degrees of homogeneous generators by `q`, then `d` is homogeneous of degree `q`
  on all of `A`;
* if `d` is homogeneous of degree `q` and `s (i + q) = -s i`, then `d ∘ₗ d` is an unsigned
  derivation, hence vanishes on `A` as soon as it vanishes on an algebra-generating set.

To *construct* signed derivations out of algebras presented by generators and Koszul commutation
relations (such as `TauCeti.SignedSym` and `TauCeti.ParitySignedSym`), we also package the `2 × 2`
lower-triangular matrix representation `x ↦ !![g x, 0; δ x, σ (g x)]`, whose `(1, 0)` entry after
lifting to an algebra map `Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A` is a `(1, σ)`-derivation.

## Main definitions

* `TauCeti.lowerTriangularLinearMap`: the linear map `x ↦ !![g x, 0; δ x, h x]`.
* `TauCeti.lowerTriangularDerivation`: the `(1, 0)` entry of an algebra map
  `A →ₐ[R] Matrix (Fin 2) (Fin 2) A` as an `R`-linear endomorphism of `A`.

## Main results

* `TauCeti.eq_zero_of_signedLeibniz_of_adjoin_eq_top` and
  `TauCeti.eq_of_signedLeibniz_of_adjoin_eq_top`: an `s`-signed Leibniz map is determined on any
  algebra-generating set.
* `TauCeti.isHomogeneous_of_signedLeibniz_of_adjoin_range_eq_top`: degree shift on generators
  propagates to the whole graded algebra.
* `TauCeti.comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_range_eq_top`: an odd-sign Leibniz map
  squares to zero if and only if its square vanishes on generators.
* `TauCeti.lowerTriangularLinearMap_mul_eq_smul` and
  `TauCeti.lowerTriangularDerivation_mul_of_adjoin_range_eq_top`: Koszul supercommutativity of the
  generator matrices and the resulting twisted Leibniz rule.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the left-factor
  graded Leibniz convention.
* N. Bourbaki, *Algebra I*, Chapter III, §10.2, for derivations via `2 × 2` triangular matrices.
-/

public section

namespace TauCeti

section SignedLeibniz

variable {R A ι : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  [DecidableEq ι] {𝒜 : ι → Submodule R A} [DirectSum.Decomposition 𝒜]
  {s : ι → ℤˣ} {d : A →ₗ[R] A}

/-- An `s`-signed Leibniz rule against a cycle in the right factor holds for an arbitrary left
factor, without a homogeneity assumption. -/
theorem map_mul_of_signedLeibniz_of_map_eq_zero
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    (a : A) {b : A} (hb : d b = 0) : d (a * b) = d a * b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a => simp [hl a.property b, hb]
  | add a a' ha ha' => simp [add_mul, ha, ha']

end SignedLeibniz

section UnitalSignedLeibniz

variable {A ι σ : Type*} [NonAssocRing A] [SetLike σ A] [Zero ι] {𝒜 : ι → σ}
  [SetLike.GradedOne 𝒜] {s : ι → ℤˣ} {d : A → A}

/-- A function satisfying an `s`-signed Leibniz rule on homogeneous left factors annihilates the
unit: the rule for `1 * 1` gives `s 0 • d 1 = 0`, and `s 0` is a unit of `ℤ`. -/
theorem map_one_eq_zero_of_signedLeibniz
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b)) :
    d 1 = 0 := by
  have key := hl (SetLike.one_mem_graded 𝒜) 1
  simp only [mul_one, one_mul, left_eq_add] at key
  exact (smul_eq_zero_iff_eq (s 0)).mp key

end UnitalSignedLeibniz

section AlgebraSignedLeibniz

variable {R A ι : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Zero ι]
  {𝒜 : ι → Submodule R A} [SetLike.GradedOne 𝒜] {s : ι → ℤˣ} {d : A →ₗ[R] A}

/-- A linear map satisfying an `s`-signed Leibniz rule annihilates the image of the ground
semiring. -/
theorem map_algebraMap_of_signedLeibniz
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    (r : R) : d (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one_eq_zero_of_signedLeibniz (𝒜 := 𝒜) hl,
    smul_zero]

end AlgebraSignedLeibniz

section Uniqueness

variable {R A V ι : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [DecidableEq ι] [Zero ι] {𝒜 : ι → Submodule R A} [SetLike.GradedOne 𝒜]
  [DirectSum.Decomposition 𝒜] {s : ι → ℤˣ}

/-- The kernel of a linear endomorphism satisfying an `s`-signed Leibniz rule is a subalgebra, so
such an endomorphism vanishes if it vanishes on an algebra-generating set. -/
theorem eq_zero_of_signedLeibniz_of_adjoin_eq_top {D : A →ₗ[R] A}
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, D (a * b) = D a * b + s i • (a * D b))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤) (hS : ∀ x ∈ S, D x = 0) : D = 0 := by
  let K : Subalgebra R A :=
    (LinearMap.ker D).toSubalgebra (map_one_eq_zero_of_signedLeibniz (𝒜 := 𝒜) hl) fun a b ha hb ↦ by
      rw [LinearMap.mem_ker] at ha hb ⊢
      rw [map_mul_of_signedLeibniz_of_map_eq_zero (𝒜 := 𝒜) hl a hb, ha, zero_mul]
  have htop : (⊤ : Subalgebra R A) ≤ K := hadj ▸ Algebra.adjoin_le fun x hx ↦ hS x hx
  ext a
  exact htop Algebra.mem_top

/-- Two linear endomorphisms satisfying the same `s`-signed Leibniz rule and agreeing on an
algebra-generating set are equal. -/
theorem eq_of_signedLeibniz_of_adjoin_eq_top {d₁ d₂ : A →ₗ[R] A}
    (hl₁ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₁ (a * b) = d₁ a * b + s i • (a * d₁ b))
    (hl₂ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₂ (a * b) = d₂ a * b + s i • (a * d₂ b))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤) (hS : ∀ x ∈ S, d₁ x = d₂ x) : d₁ = d₂ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) (s := s) (fun {i a} ha b ↦ ?_)
    hadj fun x hx ↦ sub_eq_zero.2 (hS x hx)
  simp only [LinearMap.sub_apply, hl₁ ha, hl₂ ha, sub_mul, mul_sub, Units.smul_def, zsmul_sub]
  abel

/-- An `s`-signed Leibniz endomorphism vanishing on the range of an algebra-generating map is
zero. -/
theorem eq_zero_of_signedLeibniz_of_adjoin_range_eq_top {D : A →ₗ[R] A}
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, D (a * b) = D a * b + s i • (a * D b))
    {g : V → A} (hadj : Algebra.adjoin R (Set.range g) = ⊤) (hg : ∀ x, D (g x) = 0) : D = 0 :=
  eq_zero_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) hl hadj <| Set.forall_mem_range.2 hg

/-- Two `s`-signed Leibniz endomorphisms agreeing on the range of an algebra-generating map are
equal. -/
theorem eq_of_signedLeibniz_of_adjoin_range_eq_top {d₁ d₂ : A →ₗ[R] A}
    (hl₁ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₁ (a * b) = d₁ a * b + s i • (a * d₁ b))
    (hl₂ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₂ (a * b) = d₂ a * b + s i • (a * d₂ b))
    {g : V → A} (hadj : Algebra.adjoin R (Set.range g) = ⊤)
    (hg : ∀ x, d₁ (g x) = d₂ (g x)) : d₁ = d₂ :=
  eq_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) hl₁ hl₂ hadj <| Set.forall_mem_range.2 hg

end Uniqueness

section Homogeneity

variable {R A V ι : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [AddCommMonoid V] [Module R V] [DecidableEq ι] [AddCommMonoid ι]
  {𝒱 : ι → Submodule R V} {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
  {s : ι → ℤˣ} {q : ι} {d : A →ₗ[R] A}

/-- An `s`-signed Leibniz endomorphism is homogeneous of degree `q` if an algebra-generating set
lies in the sum of the subspaces `𝒜 i ⊓ d⁻¹(𝒜 (i + q))`. -/
theorem isHomogeneous_of_signedLeibniz_of_adjoin_eq_top
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤)
    (hS : S ⊆ (⨆ i : ι, 𝒜 i ⊓ (𝒜 (i + q)).comap d : Submodule R A)) :
    LinearMap.IsHomogeneous d 𝒜 𝒜 q := by
  let F : ι → Submodule R A := fun i ↦ 𝒜 i ⊓ (𝒜 (i + q)).comap d
  let P : Submodule R A := ⨆ i, F i
  have h1 : (1 : A) ∈ P :=
    le_iSup F 0 ⟨SetLike.GradedOne.one_mem, Submodule.mem_comap.2 <| by
      rw [map_one_eq_zero_of_signedLeibniz (𝒜 := 𝒜) hl]
      exact zero_mem _⟩
  have hmul : ∀ a b, a ∈ P → b ∈ P → a * b ∈ P := fun a b ha hb ↦ by
    refine Submodule.iSup_induction F (motive := fun a ↦ a * b ∈ P) ha
      (fun i a ha ↦ ?_) (by simp) fun a₁ a₂ h₁ h₂ ↦ by rw [add_mul]; exact add_mem h₁ h₂
    refine Submodule.iSup_induction F (motive := fun b ↦ a * b ∈ P) hb
      (fun j b hb ↦ ?_) (by simp) fun b₁ b₂ h₁ h₂ ↦ by rw [mul_add]; exact add_mem h₁ h₂
    refine le_iSup F (i + j) ⟨SetLike.GradedMul.mul_mem ha.1 hb.1, Submodule.mem_comap.2 ?_⟩
    rw [hl ha.1 b]
    have hda_b : d a * b ∈ 𝒜 ((i + j) + q) :=
      add_right_comm i q j ▸ SetLike.GradedMul.mul_mem ha.2 hb.1
    have ha_db : a * d b ∈ 𝒜 ((i + j) + q) :=
      add_assoc i j q ▸ SetLike.GradedMul.mul_mem ha.1 hb.2
    -- Direct summands of an `AddCommGroup` are closed under `±1` even over a `CommSemiring`.
    have hneg : -(a * d b) ∈ 𝒜 ((i + j) + q) := by
      have h : -(a * d b) = homogeneousComponent 𝒜 ((i + j) + q) (-(a * d b)) := by
        rw [map_neg, homogeneousComponent_apply_of_mem 𝒜 ha_db]
      exact h ▸ homogeneousComponent_mem 𝒜 ((i + j) + q) (-(a * d b))
    refine add_mem hda_b ?_
    rcases Int.units_eq_one_or (s i) with hs | hs <;> simp [hs, ha_db, hneg]
  have htop : (⊤ : Subalgebra R A) ≤ P.toSubalgebra h1 hmul :=
    hadj ▸ Algebra.adjoin_le hS
  refine LinearMap.isHomogeneous_def.2 fun k a ha ↦ ?_
  let π : A →ₗ[R] A := d ∘ₗ homogeneousComponent 𝒜 k
  have hπ : P ≤ (𝒜 (k + q)).comap π := iSup_le fun i x hx ↦ by
    by_cases hik : i = k
    · subst hik
      simpa [π, homogeneousComponent_apply_of_mem 𝒜 hx.1] using hx.2
    · simp [π, homogeneousComponent_apply_of_mem_ne 𝒜 hx.1 hik]
  have haP : a ∈ P := htop Algebra.mem_top
  simpa [π, homogeneousComponent_apply_of_mem 𝒜 ha] using hπ haP

/-- If `g : V →ₗ[R] A` is homogeneous of degree `0`, its image generates `A`, `𝒱` spans `V`, and
`d ∘ₗ g` is homogeneous of degree `q`, then any `s`-signed Leibniz endomorphism `d` is homogeneous
of degree `q`. -/
theorem isHomogeneous_of_signedLeibniz_of_adjoin_range_eq_top
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    {g : V →ₗ[R] A} (hadj : Algebra.adjoin R (Set.range g) = ⊤) (h𝒱 : ⨆ i, 𝒱 i = ⊤)
    (hg : LinearMap.IsHomogeneous g 𝒱 𝒜 0) (hdg : LinearMap.IsHomogeneous (d ∘ₗ g) 𝒱 𝒜 q) :
    LinearMap.IsHomogeneous d 𝒜 𝒜 q := by
  refine isHomogeneous_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) hl hadj ?_
  rintro _ ⟨v, rfl⟩
  have hle : (⊤ : Submodule R V) ≤
      (⨆ i : ι, 𝒜 i ⊓ (𝒜 (i + q)).comap d).comap g := by
    rw [← h𝒱]
    refine iSup_le fun i x hx ↦
      le_iSup (fun k ↦ 𝒜 k ⊓ (𝒜 (k + q)).comap d) i ⟨by simpa using hg.map_mem hx, hdg.map_mem hx⟩
  exact hle Submodule.mem_top

end Homogeneity

section SquareZero

variable {R A V ι : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [DecidableEq ι] [AddMonoid ι] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
  {s : ι → ℤˣ} {q : ι} {d : A →ₗ[R] A}

/-- When `d` has degree `q` and `s (i + q) = -s i`, the square `d ∘ₗ d` is an unsigned derivation:
the two cross terms of `d (d (a * b))` cancel. -/
theorem comp_self_mul_of_signedLeibniz (hdeg : LinearMap.IsHomogeneous d 𝒜 𝒜 q)
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    (hs : ∀ i, s (i + q) = -s i) (a b : A) :
    d (d (a * b)) = d (d a) * b + a * d (d b) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a₁ a₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, h₁, h₂, map_add, map_add, add_mul, add_mul]
    abel
  | @homogeneous i a =>
    obtain ⟨a, ha⟩ := a
    have hda : d a ∈ 𝒜 (i + q) := hdeg.map_mem ha
    rw [hl ha, map_add, Units.smul_def, map_zsmul, hl hda, hl ha, hs i]
    simp only [Units.smul_def, Units.val_neg, neg_zsmul, zsmul_add, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_zsmul]
    abel

/-- A degree-`q` endomorphism satisfying an `s`-signed Leibniz rule with `s (i + q) = -s i` squares
to zero if and only if its square vanishes on an algebra-generating set. -/
theorem comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_eq_top
    (hdeg : LinearMap.IsHomogeneous d 𝒜 𝒜 q)
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    (hs : ∀ i, s (i + q) = -s i) {S : Set A} (hadj : Algebra.adjoin R S = ⊤) :
    d ∘ₗ d = 0 ↔ ∀ x ∈ S, d (d x) = 0 := by
  refine ⟨fun h x _ ↦ LinearMap.congr_fun h x, fun hS ↦ ?_⟩
  exact eq_zero_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) (s := fun _ ↦ 1)
    (fun {_ a} _ b ↦ by simp [comp_self_mul_of_signedLeibniz hdeg hl hs a b]) hadj hS

/-- A degree-`q` endomorphism satisfying an `s`-signed Leibniz rule with `s (i + q) = -s i` squares
to zero if and only if its square vanishes on the range of an algebra-generating map. -/
theorem comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_range_eq_top
    (hdeg : LinearMap.IsHomogeneous d 𝒜 𝒜 q)
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    (hs : ∀ i, s (i + q) = -s i) {g : V → A} (hadj : Algebra.adjoin R (Set.range g) = ⊤) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (g x)) = 0 := by
  rw [comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_eq_top hdeg hl hs hadj,
    Set.forall_mem_range]

end SquareZero

section LowerTriangular

/-- The `R`-linear map `x ↦ !![g x, 0; δ x, h x]` into lower-triangular `2 × 2` matrices. -/
def lowerTriangularLinearMap {R V A : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid A] [Module R A] (g δ h : V →ₗ[R] A) : V →ₗ[R] Matrix (Fin 2) (Fin 2) A where
  toFun x := !![g x, 0; δ x, h x]
  map_add' x y := by
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Evaluation of `lowerTriangularLinearMap` as an explicit `2 × 2` matrix. -/
@[simp]
theorem lowerTriangularLinearMap_apply {R V A : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid A] [Module R A] (g δ h : V →ₗ[R] A) (x : V) :
    lowerTriangularLinearMap g δ h x = !![g x, 0; δ x, h x] := (rfl)

private theorem mul_add_smul_mul_eq_smul {R A ι : Type*} [Semiring R] [Ring A] [Module R A]
    [Semiring ι] {𝒜 : ι → Submodule R A} {c : ι → ℤˣ} (hc : ∀ i j, c (i + j) = c i * c j)
    (hcomm : ∀ {i j : ι} {a b : A}, a ∈ 𝒜 i → b ∈ 𝒜 j → a * b = c (i * j) • (b * a))
    {i j : ι} {a b a' b' : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (ha' : a' ∈ 𝒜 (i + 1)) (hb' : b' ∈ 𝒜 (j + 1)) :
    a' * b + (c i • a) * b' = c (i * j) • (b' * a + (c j • b) * a') := by
  have h₁ : c ((i + 1) * j) = c (i * j) * c j := by
    rw [add_mul, one_mul, hc]
  have h₂ : c i * c (i * (j + 1)) = c (i * j) := by
    rw [mul_add, mul_one, hc, mul_left_comm, Int.units_mul_self, mul_one]
  have hleft : a' * b = c (i * j) • ((c j • b) * a') := by
    rw [hcomm ha' hb, h₁, mul_smul]
    simp only [Units.smul_def, smul_mul_assoc]
  have hright : (c i • a) * b' = c (i * j) • (b' * a) := by
    have hab' : a * b' = c (i * (j + 1)) • (b' * a) := hcomm ha hb'
    calc
      (c i • a) * b' = c i • (a * b') := by simp only [Units.smul_def, smul_mul_assoc]
      _ = (c i * c (i * (j + 1))) • (b' * a) := by rw [hab', mul_smul]
      _ = c (i * j) • (b' * a) := by rw [h₂]
  rw [hleft, hright, ← smul_add, add_comm]

/-- For homogeneous generators `x ∈ 𝒱 i` and `y ∈ 𝒱 j`, a degree-`0` generator map `g`, a
degree-`1` derivation assignment `δ`, and an algebra endomorphism `σ` scaling `𝒜 k` by `c k`, the
lower-triangular matrices `!![g x, 0; δ x, σ (g x)]` obey the Koszul commutation relation with sign
`c (i * j)`. -/
theorem lowerTriangularLinearMap_mul_eq_smul {R V A ι : Type*} [CommSemiring R] [Ring A]
    [Algebra R A] [AddCommMonoid V] [Module R V] [Semiring ι]
    {𝒱 : ι → Submodule R V} {𝒜 : ι → Submodule R A} {c : ι → ℤˣ}
    (hc : ∀ i j, c (i + j) = c i * c j)
    (hcomm : ∀ {i j : ι} {a b : A}, a ∈ 𝒜 i → b ∈ 𝒜 j → a * b = c (i * j) • (b * a))
    {σ : A →ₐ[R] A} (hσ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → σ a = c i • a)
    {g δ : V →ₗ[R] A} (hg : LinearMap.IsHomogeneous g 𝒱 𝒜 0)
    (hδ : LinearMap.IsHomogeneous δ 𝒱 𝒜 1) {i j : ι} {x y : V}
    (hx : x ∈ 𝒱 i) (hy : y ∈ 𝒱 j) :
    lowerTriangularLinearMap g δ (σ.toLinearMap ∘ₗ g) x *
        lowerTriangularLinearMap g δ (σ.toLinearMap ∘ₗ g) y =
      c (i * j) •
        (lowerTriangularLinearMap g δ (σ.toLinearMap ∘ₗ g) y *
          lowerTriangularLinearMap g δ (σ.toLinearMap ∘ₗ g) x) := by
  have hgx : g x ∈ 𝒜 i := by simpa only [add_zero] using hg.map_mem hx
  have hgy : g y ∈ 𝒜 j := by simpa only [add_zero] using hg.map_mem hy
  have hdx : δ x ∈ 𝒜 (i + 1) := hδ.map_mem hx
  have hdy : δ y ∈ 𝒜 (j + 1) := hδ.map_mem hy
  ext r col
  fin_cases r <;> fin_cases col
  · simpa [Matrix.mul_apply] using hcomm hgx hgy
  · simp [Matrix.mul_apply]
  · have hcross := mul_add_smul_mul_eq_smul hc hcomm hgx hgy hdx hdy
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hσ hgx, hσ hgy, Units.smul_def, smul_mul_assoc]
      using hcross
  · have key : σ (g x) * σ (g y) = c (i * j) • (σ (g y) * σ (g x)) := by
      rw [← map_mul σ, ← map_mul σ, hcomm hgx hgy, Units.smul_def, map_zsmul, Units.smul_def]
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using key

/-- Extract the lower-left `(1, 0)` entry of an algebra homomorphism into `2 × 2` matrices as an
`R`-linear endomorphism of `A`. -/
def lowerTriangularDerivation {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) : A →ₗ[R] A :=
  Matrix.entryLinearMap R A 1 0 ∘ₗ Φ.toLinearMap

/-- `lowerTriangularDerivation Φ` evaluates to the `(1, 0)` entry of `Φ`. -/
theorem lowerTriangularDerivation_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) (a : A) :
    lowerTriangularDerivation Φ a = Φ a 1 0 := (rfl)

/-- The `(1, 0)` entry of an algebra map into `2 × 2` matrices vanishes on scalar matrices. -/
@[simp]
theorem lowerTriangularDerivation_algebraMap {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) (r : R) :
    lowerTriangularDerivation Φ (algebraMap R A r) = 0 := by
  simp [lowerTriangularDerivation_apply, Matrix.algebraMap_matrix_apply]

/-- The `(1, 0)` entry of an algebra map into `2 × 2` matrices annihilates `1`. -/
@[simp]
theorem lowerTriangularDerivation_one {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) :
    lowerTriangularDerivation Φ 1 = 0 := by
  simpa only [map_one] using lowerTriangularDerivation_algebraMap Φ 1

/-- If `Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A` has diagonal `(id, σ)` and zero `(0, 1)` entry on an
algebra-generating set, it has that form on all of `A`. -/
theorem algHom_lowerTriangular_entries_of_adjoin_eq_top {R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) (σ : A →ₐ[R] A)
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤)
    (hS : ∀ x ∈ S, Φ x 0 0 = x ∧ Φ x 0 1 = 0 ∧ Φ x 1 1 = σ x) (a : A) :
    Φ a 0 0 = a ∧ Φ a 0 1 = 0 ∧ Φ a 1 1 = σ a := by
  let L : Subalgebra R A :=
    { carrier := {a | Φ a 0 0 = a ∧ Φ a 0 1 = 0 ∧ Φ a 1 1 = σ a}
      mul_mem' := fun {a b} ha hb ↦ by
        simp [Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
      add_mem' := fun {a b} ha hb ↦ by
        simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
      algebraMap_mem' := fun r ↦ by
        simp [Matrix.algebraMap_matrix_apply] }
  have htop : (⊤ : Subalgebra R A) ≤ L := hadj ▸ Algebra.adjoin_le hS
  exact htop Algebra.mem_top

/-- Under the hypotheses of `algHom_lowerTriangular_entries_of_adjoin_eq_top`, the `(1, 0)` entry of
`Φ` satisfies the `(1, σ)`-twisted Leibniz rule `d (a * b) = d a * b + σ a * d b`. -/
theorem lowerTriangularDerivation_mul_of_adjoin_eq_top {R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) (σ : A →ₐ[R] A)
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤)
    (hS : ∀ x ∈ S, Φ x 0 0 = x ∧ Φ x 0 1 = 0 ∧ Φ x 1 1 = σ x) (a b : A) :
    lowerTriangularDerivation Φ (a * b) =
      lowerTriangularDerivation Φ a * b + σ a * lowerTriangularDerivation Φ b := by
  have ha := algHom_lowerTriangular_entries_of_adjoin_eq_top Φ σ hadj hS a
  have hb := algHom_lowerTriangular_entries_of_adjoin_eq_top Φ σ hadj hS b
  simp [lowerTriangularDerivation_apply, Matrix.mul_apply, Fin.sum_univ_two, ha.2.2, hb.1]

/-- When `Φ (g x) = !![g x, 0; δ x, σ (g x)]` for an algebra-generating map `g : V →ₗ[R] A`, the
`(1, 0)` entry of `Φ` satisfies `d (a * b) = d a * b + σ a * d b` for all `a, b : A`. -/
theorem lowerTriangularDerivation_mul_of_adjoin_range_eq_top {R V A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [AddCommMonoid V] [Module R V]
    (Φ : A →ₐ[R] Matrix (Fin 2) (Fin 2) A) (σ : A →ₐ[R] A) {g δ : V →ₗ[R] A}
    (hadj : Algebra.adjoin R (Set.range g) = ⊤)
    (hΦ : ∀ x, Φ (g x) = lowerTriangularLinearMap g δ (σ.toLinearMap ∘ₗ g) x) (a b : A) :
    lowerTriangularDerivation Φ (a * b) =
      lowerTriangularDerivation Φ a * b + σ a * lowerTriangularDerivation Φ b := by
  refine lowerTriangularDerivation_mul_of_adjoin_eq_top Φ σ hadj ?_ a b
  rintro _ ⟨x, rfl⟩
  simp [hΦ x]

end LowerTriangular

end TauCeti
