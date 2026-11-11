/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Matrices homogeneous with respect to a grading by a `G`-set

Let `A` be an algebra graded by a family of submodules `Ag : G → Submodule R A` over a group `G`,
and let the rows and columns of a matrix over `A` be graded by maps `gr : X → T` and
`gr' : X' → T` into a left `G`-set `T`. A matrix `F` is homogeneous of degree `c` when each entry
`F x x'` is a sum of elements of the degrees `g` with `g • gr' x' = c • gr x`. Read as a map
`x ↦ ∑ x', F x x' ⊗ x'`, such a matrix sends a generator of degree `t` to a sum of terms of
degree `c • t`. This is the grading of the morphisms of type `D` structures over the bordered
algebras of Lipshitz, Ozsváth and Thurston, which are graded by a nonabelian group.

The results assume only the compatibilities they use: `Ag g * Ag h ⊆ Ag (g * h)` for products,
and that a linear map `d` maps `Ag g` into `Ag (l * g)` for the entrywise image. That the parts
span `A` independently is never needed.

## Main definitions

* `TauCeti.homogeneousMatrices Ag gr gr' c`: the matrices homogeneous of degree `c` from the
  grading `gr` to the grading `gr'`.

## Main results

* `TauCeti.mul_mem_homogeneousMatrices`: degrees multiply under products, for a central second
  degree.
* `TauCeti.map_mem_homogeneousMatrices`: a linear map shifting degrees by `l` shifts the degree of
  a homogeneous matrix by `l` entrywise.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §2.5.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommSemiring R] [Semiring A] [Module R A] {G : Type*} [Group G]
  (Ag : G → Submodule R A) {T : Type*} [MulAction G T] {X X' X'' : Type*}

/-- The matrices of coefficients **homogeneous of degree `c`** from the grading `gr : X → T` to
the grading `gr' : X' → T`: each entry `F x x'` is a sum of elements of the degrees `g` with
`g • gr' x' = c • gr x`. Read as a map `x ↦ ∑ x', F x x' ⊗ x'`, such a matrix sends a generator
of degree `t` to a sum of terms of degree `c • t`. -/
def homogeneousMatrices (gr : X → T) (gr' : X' → T) (c : G) : Submodule R (Matrix X X' A) where
  carrier := {F | ∀ x x', F x x' ∈ ⨆ g : {g : G // g • gr' x' = c • gr x}, Ag g}
  add_mem' hF hG x x' := add_mem (hF x x') (hG x x')
  zero_mem' _ _ := zero_mem _
  smul_mem' r _ hF x x' := Submodule.smul_mem _ r (hF x x')

variable {Ag}

@[simp]
theorem mem_homogeneousMatrices_iff {gr : X → T} {gr' : X' → T} {c : G} {F : Matrix X X' A} :
    F ∈ homogeneousMatrices Ag gr gr' c ↔
      ∀ x x', F x x' ∈ ⨆ g : {g : G // g • gr' x' = c • gr x}, Ag g :=
  Iff.rfl

/-- **Degrees add under products**: when `A` is graded, the product of matrices homogeneous of
degrees `c` and `c'`, with `c'` central, is homogeneous of degree `c * c'`. -/
theorem mul_mem_homogeneousMatrices [Fintype X']
    (hA : ∀ {g h : G} {a b : A}, a ∈ Ag g → b ∈ Ag h → a * b ∈ Ag (g * h))
    {gr : X → T} {gr' : X' → T} {gr'' : X'' → T} {c c' : G} (hc' : c' ∈ Subgroup.center G)
    {F : Matrix X X' A} {F' : Matrix X' X'' A} (hF : F ∈ homogeneousMatrices Ag gr gr' c)
    (hF' : F' ∈ homogeneousMatrices Ag gr' gr'' c') :
    F * F' ∈ homogeneousMatrices Ag gr gr'' (c * c') := by
  intro x x''
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun x' _ ↦ ?_
  refine Submodule.iSup_induction _ (motive := fun a ↦ a * F' x' x'' ∈ _) (hF x x') ?_
    (by rw [zero_mul]; exact zero_mem _) fun a a' ha ha' ↦ by rw [add_mul]; exact add_mem ha ha'
  rintro ⟨g, hg⟩ a ha
  refine Submodule.iSup_induction _ (motive := fun b ↦ a * b ∈ _) (hF' x' x'') ?_
    (by rw [mul_zero]; exact zero_mem _) fun b b' hb hb' ↦ by rw [mul_add]; exact add_mem hb hb'
  rintro ⟨h, hh⟩ b hb
  refine Submodule.mem_iSup_of_mem ⟨g * h, ?_⟩ (hA ha hb)
  rw [mul_smul, hh, smul_smul, Subgroup.mem_center_iff.mp hc' g, mul_smul, hg, smul_smul,
    Subgroup.mem_center_iff.mp hc' c]

/-- If `d` maps degree `g` to degree `l * g`, the entrywise differential of a matrix homogeneous of
degree `c` is homogeneous of degree `l * c`. -/
theorem map_mem_homogeneousMatrices {d : A →ₗ[R] A} {l : G}
    (hd : ∀ {g : G} {a : A}, a ∈ Ag g → d a ∈ Ag (l * g)) {gr : X → T} {gr' : X' → T} {c : G}
    {F : Matrix X X' A} (hF : F ∈ homogeneousMatrices Ag gr gr' c) :
    F.map d ∈ homogeneousMatrices Ag gr gr' (l * c) := by
  intro x x'
  rw [Matrix.map_apply]
  refine Submodule.iSup_induction _ (motive := fun a ↦ d a ∈ _) (hF x x') ?_
    (by rw [map_zero]; exact zero_mem _) fun a a' ha ha' ↦ by rw [map_add]; exact add_mem ha ha'
  rintro ⟨g, hg⟩ a ha
  exact Submodule.mem_iSup_of_mem ⟨l * g, by rw [mul_smul, hg, smul_smul]⟩ (hd ha)


end TauCeti
