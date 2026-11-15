/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.RingTheory.GradedAlgebra.BraidedTensorProduct.Basic

import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.LinearAlgebra.TensorAlgebra.Grading
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Gradings and monoidal structure on bicharacter-twisted tensor products

Given `R`-algebras `A` and `B` internally graded by `𝒜 : G₁ → Submodule R A` and
`ℬ : G₂ → Submodule R B` and a multiplicative bicharacter `χ : AddChar G₂ (AddChar G₁ R)`, this
file equips `BraidedTensorProduct R 𝒜 ℬ χ` with:

1. Its canonical `G₁ × G₂`-bigrading `BraidedTensorProduct.bigrading 𝒜 ℬ χ`, turning it into an
   internally `G₁ × G₂`-graded `R`-algebra for arbitrary grading monoids `G₁` and `G₂`.
2. When `G₁ = G₂ = G` is an `AddCommMonoid` (such as the positive root cone `Q⁺ = ι →₀ ℕ` or the
   root lattice `Q = ι →₀ ℤ` of a quantized enveloping algebra), its total-degree `G`-grading
   `BraidedTensorProduct.grading 𝒜 ℬ χ`, obtained by collecting the bigrading along addition
   `G × G → G` via `DirectSum.IsInternal.iSup_fiber` without requiring subtraction in `G` (in
   contrast to `TauCeti.gradedTensorGrading`, which grades Mathlib's `ℤ`-indexed Koszul
   `GradedTensorProduct` via `ℤ`-subtraction).
3. Graded factor inclusions, the graded universal property, graded functoriality, graded factor
   swap for paired bicharacters, and the graded associator equivalence
   `((A ⊗_χ B) ⊗_χ C) ≃ₐ[R] (A ⊗_χ (B ⊗_χ C))` needed to express braided coassociativity of
   Lusztig's coproduct `r : U⁺ → U⁺ ⊗_χ U⁺`.

## Main definitions

* `TauCeti.BraidedTensorProduct.bigrading`: the `G₁ × G₂`-bigrading of
  `BraidedTensorProduct R 𝒜 ℬ χ`.
* `TauCeti.BraidedTensorProduct.grading`: the total-degree `G`-grading when `𝒜` and `ℬ` share a
  commutative grading monoid `G`.
* `TauCeti.BraidedTensorProduct.includeLeftGraded` and
  `TauCeti.BraidedTensorProduct.includeRightGraded`: the factor inclusions as `GradedAlgHom`s.
* `TauCeti.BraidedTensorProduct.liftGraded`: the graded universal property out of
  `grading 𝒜 ℬ χ`.
* `TauCeti.BraidedTensorProduct.mapGraded`: functoriality of `grading` for `GradedAlgHom`s.
* `TauCeti.BraidedTensorProduct.commGraded`: the braided factor-swap `GradedAlgHom` for paired
  bicharacters.
* `TauCeti.BraidedTensorProduct.assocGraded`, `TauCeti.BraidedTensorProduct.assocSymmGraded`, and
  `TauCeti.BraidedTensorProduct.assocAlgEquiv`: the monoidal associator of bicharacter-twisted
  tensor products over a common commutative grading monoid.

## Main results

* `TauCeti.BraidedTensorProduct.instGradedAlgebraBigrading` and
  `TauCeti.BraidedTensorProduct.instGradedAlgebraGrading`: internal `GradedAlgebra` instances for
  the bigrading and total-degree grading.
* `TauCeti.BraidedTensorProduct.eq_top_of_tmul_mem` and
  `TauCeti.BraidedTensorProduct.linearMap_ext_of_mem`: reduction principles to pure tensors of
  homogeneous elements.
* `TauCeti.BraidedTensorProduct.gradedAlgHom_ext`: two `GradedAlgHom`s out of `grading 𝒜 ℬ χ`
  agree if they agree on both factor inclusions.
* `TauCeti.BraidedTensorProduct.assocSymmGraded_comp_assocGraded` and
  `TauCeti.BraidedTensorProduct.assocGraded_comp_assocSymmGraded`: `assocGraded` and
  `assocSymmGraded` are mutually inverse `GradedAlgHom`s.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.2.2–1.2.4.
* S. Majid, *Foundations of Quantum Group Theory*, Cambridge University Press, 1995, §9.2.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

namespace BraidedTensorProduct

universe uR uG uG₁ uG₂ uA uB uC

section Bigrading

section Module

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
  [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B)
  (χ : AddChar G₂ (AddChar G₁ R))

/-- The `(i, j)`-homogeneous piece of `BraidedTensorProduct R 𝒜 ℬ χ`, spanned over `R` by pure
tensors `tmul 𝒜 ℬ χ a b` with `a ∈ 𝒜 i` and `b ∈ ℬ j`. -/
def bigrading (p : G₁ × G₂) : Submodule R (BraidedTensorProduct R 𝒜 ℬ χ) :=
  Submodule.map₂ (tmulBilinear 𝒜 ℬ χ) (𝒜 p.1) (ℬ p.2)

/-- A pure tensor of homogeneous elements lies in the corresponding bidegree piece. -/
theorem tmul_mem_bigrading {i : G₁} {j : G₂} {a : A} (ha : a ∈ 𝒜 i) {b : B} (hb : b ∈ ℬ j) :
    tmul 𝒜 ℬ χ a b ∈ bigrading 𝒜 ℬ χ (i, j) := by
  simpa only [bigrading, tmulBilinear_apply] using
    Submodule.apply_mem_map₂ (tmulBilinear 𝒜 ℬ χ) ha hb

/-- A submodule containing every pure tensor from `𝒜 p.1 × ℬ p.2` contains `bigrading 𝒜 ℬ χ p`. -/
theorem bigrading_le {p : G₁ × G₂} {M : Submodule R (BraidedTensorProduct R 𝒜 ℬ χ)}
    (h : ∀ a ∈ 𝒜 p.1, ∀ b ∈ ℬ p.2, tmul 𝒜 ℬ χ a b ∈ M) :
    bigrading 𝒜 ℬ χ p ≤ M :=
  Submodule.map₂_le.2 fun a ha b hb ↦ by simpa only [tmulBilinear_apply] using h a ha b hb

section Decomposition

variable [DecidableEq G₁] [DecidableEq G₂]
  [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]

/-- The bidegree pieces `bigrading 𝒜 ℬ χ` form an internal direct sum decomposition of
`BraidedTensorProduct R 𝒜 ℬ χ`. -/
theorem isInternal_bigrading : DirectSum.IsInternal (bigrading 𝒜 ℬ χ) := by
  have hmap : (fun p : G₁ × G₂ ↦
      (Submodule.map₂ (TensorProduct.mk R A B) (𝒜 p.1) (ℬ p.2)).map
        (ofLinearEquiv 𝒜 ℬ χ).toLinearMap) = bigrading 𝒜 ℬ χ := by
    funext p
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.map₂_le.2 fun a ha b hb ↦ ?_
      rw [Submodule.mem_comap, LinearEquiv.coe_coe, ofLinearEquiv_apply,
        TensorProduct.mk_apply, of_tmul]
      exact tmul_mem_bigrading 𝒜 ℬ χ ha hb
    · exact bigrading_le 𝒜 ℬ χ fun a ha b hb ↦
        ⟨a ⊗ₜ[R] b, Submodule.apply_mem_map₂ (TensorProduct.mk R A B) ha hb, by simp⟩
  rw [← hmap]
  exact ((DirectSum.Decomposition.isInternal 𝒜).tensorProduct 𝒜 ℬ
    (DirectSum.Decomposition.isInternal ℬ)).map_linearEquiv (ofLinearEquiv 𝒜 ℬ χ)

/-- A submodule containing all pure tensors of homogeneous elements is the whole braided tensor
product. -/
theorem eq_top_of_tmul_mem {M : Submodule R (BraidedTensorProduct R 𝒜 ℬ χ)}
    (h : ∀ i j, ∀ a ∈ 𝒜 i, ∀ b ∈ ℬ j, tmul 𝒜 ℬ χ a b ∈ M) : M = ⊤ := by
  refine top_le_iff.1 ?_
  rw [← (isInternal_bigrading 𝒜 ℬ χ).submodule_iSup_eq_top]
  exact iSup_le fun p ↦ bigrading_le 𝒜 ℬ χ (h p.1 p.2)

/-- Two `R`-linear maps out of `BraidedTensorProduct R 𝒜 ℬ χ` agree as soon as they agree on pure
tensors of homogeneous elements. -/
theorem linearMap_ext_of_mem {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : BraidedTensorProduct R 𝒜 ℬ χ →ₗ[R] N}
    (h : ∀ i j, ∀ a ∈ 𝒜 i, ∀ b ∈ ℬ j, f (tmul 𝒜 ℬ χ a b) = g (tmul 𝒜 ℬ χ a b)) :
    f = g :=
  LinearMap.eqLocus_eq_top.1 (eq_top_of_tmul_mem 𝒜 ℬ χ h)

end Decomposition

end Module

section Algebra

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂] [DecidableEq G₁] [DecidableEq G₂]
  [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B)
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (χ : AddChar G₂ (AddChar G₁ R))

private theorem tmul_mul_mem_bigrading {i₁ i₂ : G₁} {j₁ j₂ : G₂}
    {a₁ : A} (ha₁ : a₁ ∈ 𝒜 i₁) {b₁ : B} (hb₁ : b₁ ∈ ℬ j₁)
    {y : BraidedTensorProduct R 𝒜 ℬ χ} (hy : y ∈ bigrading 𝒜 ℬ χ (i₂, j₂)) :
    tmul 𝒜 ℬ χ a₁ b₁ * y ∈ bigrading 𝒜 ℬ χ ((i₁, j₁) + (i₂, j₂)) := by
  refine bigrading_le 𝒜 ℬ χ
    (M := (bigrading 𝒜 ℬ χ ((i₁, j₁) + (i₂, j₂))).comap (mulHom 𝒜 ℬ χ (tmul 𝒜 ℬ χ a₁ b₁)))
    (fun a₂ ha₂ b₂ hb₂ ↦ ?_) hy
  rw [Submodule.mem_comap, ← mul_def, tmul_mul_tmul_of_mem 𝒜 ℬ χ a₁ hb₁ ha₂ b₂]
  exact Submodule.smul_mem _ _
    (tmul_mem_bigrading 𝒜 ℬ χ (SetLike.mul_mem_graded ha₁ ha₂) (SetLike.mul_mem_graded hb₁ hb₂))

/-- The `χ`-twisted multiplication adds bidegrees in `G₁ × G₂`. -/
instance instGradedMonoidBigrading : SetLike.GradedMonoid (bigrading 𝒜 ℬ χ) where
  one_mem := by
    rw [one_def]
    exact tmul_mem_bigrading 𝒜 ℬ χ (SetLike.one_mem_graded 𝒜) (SetLike.one_mem_graded ℬ)
  mul_mem p q x y hx hy := by
    refine bigrading_le 𝒜 ℬ χ
      (M := (bigrading 𝒜 ℬ χ (p + q)).comap ((mulHom 𝒜 ℬ χ).flip y))
      (fun a₁ ha₁ b₁ hb₁ ↦ ?_) hx
    rw [Submodule.mem_comap, LinearMap.flip_apply, ← mul_def]
    exact tmul_mul_mem_bigrading 𝒜 ℬ χ ha₁ hb₁ hy

/-- `BraidedTensorProduct R 𝒜 ℬ χ` is an internally `G₁ × G₂`-graded `R`-algebra. -/
noncomputable instance instGradedAlgebraBigrading : GradedAlgebra (bigrading 𝒜 ℬ χ) :=
  (isInternal_bigrading 𝒜 ℬ χ).gradedAlgebra

end Algebra

end Bigrading

section TotalGrading

section Module

variable {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G]
  [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  (𝒜 : G → Submodule R A) (ℬ : G → Submodule R B)
  (χ : AddChar G (AddChar G R))

/-- The total-degree `G`-grading of `BraidedTensorProduct R 𝒜 ℬ χ`: degree `k` is the supremum of
`bigrading 𝒜 ℬ χ (i, j)` over all pairs `(i, j)` with `i + j = k`. -/
def grading (k : G) : Submodule R (BraidedTensorProduct R 𝒜 ℬ χ) :=
  ⨆ p : G × G, ⨆ _ : p.1 + p.2 = k, bigrading 𝒜 ℬ χ p

/-- Each `(i, j)`-bidegree piece is contained in the `(i + j)`-total-degree piece. -/
theorem bigrading_le_grading (i j : G) :
    bigrading 𝒜 ℬ χ (i, j) ≤ grading 𝒜 ℬ χ (i + j) :=
  le_iSup₂_of_le (i, j) rfl le_rfl

/-- A pure tensor of homogeneous elements of degrees `i` and `j` has total degree `i + j`. -/
theorem tmul_mem_grading {i j : G} {a : A} (ha : a ∈ 𝒜 i) {b : B} (hb : b ∈ ℬ j) :
    tmul 𝒜 ℬ χ a b ∈ grading 𝒜 ℬ χ (i + j) :=
  bigrading_le_grading 𝒜 ℬ χ i j (tmul_mem_bigrading 𝒜 ℬ χ ha hb)

/-- A submodule containing every pure tensor `tmul 𝒜 ℬ χ a b` with `a ∈ 𝒜 i`, `b ∈ ℬ j`, and
`i + j = k` contains `grading 𝒜 ℬ χ k`. -/
theorem grading_le {k : G} {M : Submodule R (BraidedTensorProduct R 𝒜 ℬ χ)}
    (h : ∀ i j, i + j = k → ∀ a ∈ 𝒜 i, ∀ b ∈ ℬ j, tmul 𝒜 ℬ χ a b ∈ M) :
    grading 𝒜 ℬ χ k ≤ M :=
  iSup₂_le fun p hp ↦ bigrading_le 𝒜 ℬ χ (h p.1 p.2 hp)

/-- The total-degree pieces `grading 𝒜 ℬ χ` form an internal direct sum decomposition of
`BraidedTensorProduct R 𝒜 ℬ χ`. -/
theorem isInternal_grading [DecidableEq G]
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] :
    DirectSum.IsInternal (grading 𝒜 ℬ χ) :=
  (isInternal_bigrading 𝒜 ℬ χ).iSup_fiber fun p ↦ p.1 + p.2

end Module

section Algebra

variable {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddCommMonoid G] [DecidableEq G]
  [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (𝒜 : G → Submodule R A) (ℬ : G → Submodule R B)
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (χ : AddChar G (AddChar G R))

private theorem tmul_mul_mem_grading {i₁ j₁ n : G}
    {a₁ : A} (ha₁ : a₁ ∈ 𝒜 i₁) {b₁ : B} (hb₁ : b₁ ∈ ℬ j₁)
    {y : BraidedTensorProduct R 𝒜 ℬ χ} (hy : y ∈ grading 𝒜 ℬ χ n) :
    tmul 𝒜 ℬ χ a₁ b₁ * y ∈ grading 𝒜 ℬ χ (i₁ + j₁ + n) := by
  refine grading_le 𝒜 ℬ χ
    (M := (grading 𝒜 ℬ χ (i₁ + j₁ + n)).comap (mulHom 𝒜 ℬ χ (tmul 𝒜 ℬ χ a₁ b₁)))
    (fun i₂ j₂ hn a₂ ha₂ b₂ hb₂ ↦ ?_) hy
  rw [Submodule.mem_comap, ← mul_def, tmul_mul_tmul_of_mem 𝒜 ℬ χ a₁ hb₁ ha₂ b₂]
  have hdeg : (i₁ + i₂) + (j₁ + j₂) = i₁ + j₁ + n := by
    rw [add_add_add_comm, hn]
  exact hdeg ▸ Submodule.smul_mem _ _
    (tmul_mem_grading 𝒜 ℬ χ (SetLike.mul_mem_graded ha₁ ha₂) (SetLike.mul_mem_graded hb₁ hb₂))

/-- When `G` is commutative, the `χ`-twisted multiplication adds total degrees in `G`. -/
instance instGradedMonoidGrading : SetLike.GradedMonoid (grading 𝒜 ℬ χ) where
  one_mem := by
    rw [one_def, ← add_zero (0 : G)]
    exact tmul_mem_grading 𝒜 ℬ χ (SetLike.one_mem_graded 𝒜) (SetLike.one_mem_graded ℬ)
  mul_mem m n x y hx hy := by
    refine grading_le 𝒜 ℬ χ
      (M := (grading 𝒜 ℬ χ (m + n)).comap ((mulHom 𝒜 ℬ χ).flip y))
      (fun i₁ j₁ hm a₁ ha₁ b₁ hb₁ ↦ ?_) hx
    rw [Submodule.mem_comap, LinearMap.flip_apply, ← mul_def, ← hm]
    exact tmul_mul_mem_grading 𝒜 ℬ χ ha₁ hb₁ hy

/-- When `𝒜` and `ℬ` are graded by a common `AddCommMonoid G`, `BraidedTensorProduct R 𝒜 ℬ χ` is
an internally `G`-graded `R`-algebra for `grading 𝒜 ℬ χ`. -/
noncomputable instance instGradedAlgebraGrading : GradedAlgebra (grading 𝒜 ℬ χ) :=
  (isInternal_grading 𝒜 ℬ χ).gradedAlgebra

/-- The left factor inclusion `a ↦ a ⊗ₜ 1` as a `GradedAlgHom`. -/
noncomputable def includeLeftGraded : 𝒜 →ₐᵍ[R] grading 𝒜 ℬ χ where
  toAlgHom := includeLeft 𝒜 ℬ χ
  map_mem {i a} ha := by
    change includeLeft 𝒜 ℬ χ a ∈ grading 𝒜 ℬ χ i
    simpa only [includeLeft_apply, add_zero] using
      tmul_mem_grading 𝒜 ℬ χ ha (SetLike.one_mem_graded ℬ)

@[simp]
theorem includeLeftGraded_apply (a : A) :
    includeLeftGraded 𝒜 ℬ χ a = tmul 𝒜 ℬ χ a 1 :=
  includeLeft_apply 𝒜 ℬ χ a

@[simp]
theorem includeLeftGraded_toAlgHom :
    (includeLeftGraded 𝒜 ℬ χ).toAlgHom = includeLeft 𝒜 ℬ χ := by
  rfl

/-- The right factor inclusion `b ↦ 1 ⊗ₜ b` as a `GradedAlgHom`. -/
noncomputable def includeRightGraded : ℬ →ₐᵍ[R] grading 𝒜 ℬ χ where
  toAlgHom := includeRight 𝒜 ℬ χ
  map_mem {j b} hb := by
    change includeRight 𝒜 ℬ χ b ∈ grading 𝒜 ℬ χ j
    simpa only [includeRight_apply, zero_add] using
      tmul_mem_grading 𝒜 ℬ χ (SetLike.one_mem_graded 𝒜) hb

@[simp]
theorem includeRightGraded_apply (b : B) :
    includeRightGraded 𝒜 ℬ χ b = tmul 𝒜 ℬ χ 1 b :=
  includeRight_apply 𝒜 ℬ χ b

@[simp]
theorem includeRightGraded_toAlgHom :
    (includeRightGraded 𝒜 ℬ χ).toAlgHom = includeRight 𝒜 ℬ χ := by
  rfl

/-- Homogeneous elements in the images of `includeRightGraded` and `includeLeftGraded` braid
according to `χ`. -/
theorem includeRightGraded_mul_includeLeftGraded_of_mem {i j : G}
    {a : A} (ha : a ∈ 𝒜 i) {b : B} (hb : b ∈ ℬ j) :
    includeRightGraded 𝒜 ℬ χ b * includeLeftGraded 𝒜 ℬ χ a =
      χ j i • (includeLeftGraded 𝒜 ℬ χ a * includeRightGraded 𝒜 ℬ χ b) := by
  rw [includeRightGraded_apply, includeLeftGraded_apply, ← includeRight_apply, ← includeLeft_apply]
  exact includeRight_mul_includeLeft_of_mem 𝒜 ℬ χ ha hb

section LiftGraded

variable {C : Type uC} [Semiring C] [Algebra R C]
  {𝒞 : G → Submodule R C} [GradedAlgebra 𝒞]

/-- Graded universal property of `BraidedTensorProduct R 𝒜 ℬ χ`: a pair of `GradedAlgHom`s
`f : 𝒜 →ₐᵍ[R] 𝒞` and `g : ℬ →ₐᵍ[R] 𝒞` satisfying `g b * f a = χ j i • (f a * g b)` for `a ∈ 𝒜 i`
and `b ∈ ℬ j` induces a `GradedAlgHom` out of `grading 𝒜 ℬ χ`. -/
noncomputable def liftGraded (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j : G⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b)) :
    grading 𝒜 ℬ χ →ₐᵍ[R] 𝒞 where
  toAlgHom := lift 𝒜 ℬ χ f.toAlgHom g.toAlgHom h
  map_mem {k x} hx := by
    refine grading_le 𝒜 ℬ χ
      (M := (𝒞 k).comap (lift 𝒜 ℬ χ f.toAlgHom g.toAlgHom h).toLinearMap)
      (fun i j hij a ha b hb ↦ ?_) hx
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, lift_tmul, GradedAlgHom.coe_toAlgHom,
      GradedAlgHom.coe_toAlgHom, ← hij]
    exact SetLike.mul_mem_graded (Graded.map_mem f ha) (Graded.map_mem g hb)

@[simp]
theorem liftGraded_toAlgHom (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j : G⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b)) :
    (liftGraded 𝒜 ℬ χ f g h).toAlgHom = lift 𝒜 ℬ χ f.toAlgHom g.toAlgHom h := by
  rfl

@[simp]
theorem liftGraded_tmul (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j : G⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b))
    (a : A) (b : B) :
    liftGraded 𝒜 ℬ χ f g h (tmul 𝒜 ℬ χ a b) = f a * g b :=
  lift_tmul 𝒜 ℬ χ f.toAlgHom g.toAlgHom h a b

@[simp]
theorem liftGraded_comp_includeLeftGraded (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j : G⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b)) :
    (liftGraded 𝒜 ℬ χ f g h).comp (includeLeftGraded 𝒜 ℬ χ) = f := by
  ext a
  simp

@[simp]
theorem liftGraded_comp_includeRightGraded (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j : G⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b)) :
    (liftGraded 𝒜 ℬ χ f g h).comp (includeRightGraded 𝒜 ℬ χ) = g := by
  ext b
  simp

variable {𝒜 ℬ χ} in
/-- Two `GradedAlgHom`s out of `grading 𝒜 ℬ χ` agree if their compositions with
`includeLeftGraded` and `includeRightGraded` agree. -/
@[ext]
theorem gradedAlgHom_ext ⦃F₁ F₂ : grading 𝒜 ℬ χ →ₐᵍ[R] 𝒞⦄
    (hL : F₁.comp (includeLeftGraded 𝒜 ℬ χ) = F₂.comp (includeLeftGraded 𝒜 ℬ χ))
    (hR : F₁.comp (includeRightGraded 𝒜 ℬ χ) = F₂.comp (includeRightGraded 𝒜 ℬ χ)) :
    F₁ = F₂ := by
  apply GradedAlgHom.coe_toAlgHom_injective
  exact algHom_ext (congrArg GradedAlgHom.toAlgHom hL) (congrArg GradedAlgHom.toAlgHom hR)

end LiftGraded

section MapGraded

variable {𝒜 ℬ}
  {A' B' A'' B'' : Type*}
  [Semiring A'] [Semiring B'] [Algebra R A'] [Algebra R B']
  [Semiring A''] [Semiring B''] [Algebra R A''] [Algebra R B'']
  {𝒜' : G → Submodule R A'} {ℬ' : G → Submodule R B'}
  [GradedAlgebra 𝒜'] [GradedAlgebra ℬ']
  {𝒜'' : G → Submodule R A''} {ℬ'' : G → Submodule R B''}
  [GradedAlgebra 𝒜''] [GradedAlgebra ℬ'']

/-- Functoriality of `grading` for `GradedAlgHom`s. -/
noncomputable def mapGraded (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    grading 𝒜 ℬ χ →ₐᵍ[R] grading 𝒜' ℬ' χ where
  toAlgHom := map χ f g
  map_mem {k x} hx := by
    refine grading_le 𝒜 ℬ χ
      (M := (grading 𝒜' ℬ' χ k).comap (map χ f g).toLinearMap)
      (fun i j hij a ha b hb ↦ ?_) hx
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_tmul, ← hij]
    exact tmul_mem_grading 𝒜' ℬ' χ (Graded.map_mem f ha) (Graded.map_mem g hb)

@[simp]
theorem mapGraded_toAlgHom (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    (mapGraded χ f g).toAlgHom = map χ f g := by
  rfl

@[simp]
theorem mapGraded_tmul (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') (a : A) (b : B) :
    mapGraded χ f g (tmul 𝒜 ℬ χ a b) = tmul 𝒜' ℬ' χ (f a) (g b) :=
  map_tmul χ f g a b

@[simp]
theorem mapGraded_comp_includeLeftGraded (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    (mapGraded χ f g).comp (includeLeftGraded 𝒜 ℬ χ) =
      (includeLeftGraded 𝒜' ℬ' χ).comp f := by
  apply GradedAlgHom.coe_toAlgHom_injective
  exact map_comp_includeLeft χ f g

@[simp]
theorem mapGraded_comp_includeRightGraded (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    (mapGraded χ f g).comp (includeRightGraded 𝒜 ℬ χ) =
      (includeRightGraded 𝒜' ℬ' χ).comp g := by
  apply GradedAlgHom.coe_toAlgHom_injective
  exact map_comp_includeRight χ f g

@[simp]
theorem mapGraded_id :
    mapGraded χ (.id R 𝒜) (.id R ℬ) = .id R (grading 𝒜 ℬ χ) := by
  apply GradedAlgHom.coe_toAlgHom_injective
  exact map_id χ

theorem mapGraded_comp (f' : 𝒜' →ₐᵍ[R] 𝒜'') (g' : ℬ' →ₐᵍ[R] ℬ'')
    (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    (mapGraded χ f' g').comp (mapGraded χ f g) =
      mapGraded χ (f'.comp f) (g'.comp g) := by
  apply GradedAlgHom.coe_toAlgHom_injective
  exact map_comp χ f' g' f g

/-- If `f` and `g` are surjective `GradedAlgHom`s, then so is `mapGraded χ f g`. -/
theorem mapGraded_surjective {f : 𝒜 →ₐᵍ[R] 𝒜'} {g : ℬ →ₐᵍ[R] ℬ'}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (mapGraded χ f g) :=
  map_surjective χ hf hg

end MapGraded

section CommGraded

variable {χ : AddChar G (AddChar G R)} {ψ : AddChar G (AddChar G R)}

/-- Paired bicharacters `χ` and `ψ` satisfying `∀ i j, χ j i * ψ i j = 1` induce a total-degree
preserving factor-swap `GradedAlgHom` from `grading 𝒜 ℬ χ` to `grading ℬ 𝒜 ψ`. -/
noncomputable def commGraded (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    grading 𝒜 ℬ χ →ₐᵍ[R] grading ℬ 𝒜 ψ where
  toAlgHom := comm 𝒜 ℬ hχψ
  map_mem {k x} hx := by
    refine grading_le 𝒜 ℬ χ
      (M := (grading ℬ 𝒜 ψ k).comap (comm 𝒜 ℬ hχψ).toLinearMap)
      (fun i j hij a ha b hb ↦ ?_) hx
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, comm_tmul_of_mem 𝒜 ℬ hχψ ha hb,
      ← hij, add_comm i j]
    exact Submodule.smul_mem _ _ (tmul_mem_grading ℬ 𝒜 ψ hb ha)

@[simp]
theorem commGraded_toAlgHom (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    (commGraded 𝒜 ℬ hχψ).toAlgHom = comm 𝒜 ℬ hχψ := by
  rfl

@[simp]
theorem commGraded_tmul_one (hχψ : ∀ i j, χ j i * ψ i j = 1) (a : A) :
    commGraded 𝒜 ℬ hχψ (tmul 𝒜 ℬ χ a 1) = tmul ℬ 𝒜 ψ 1 a :=
  comm_tmul_one 𝒜 ℬ hχψ a

@[simp]
theorem commGraded_one_tmul (hχψ : ∀ i j, χ j i * ψ i j = 1) (b : B) :
    commGraded 𝒜 ℬ hχψ (tmul 𝒜 ℬ χ 1 b) = tmul ℬ 𝒜 ψ b 1 :=
  comm_one_tmul 𝒜 ℬ hχψ b

theorem commGraded_tmul_of_mem (hχψ : ∀ i j, χ j i * ψ i j = 1) {i j : G}
    {a : A} (ha : a ∈ 𝒜 i) {b : B} (hb : b ∈ ℬ j) :
    commGraded 𝒜 ℬ hχψ (tmul 𝒜 ℬ χ a b) = ψ i j • tmul ℬ 𝒜 ψ b a :=
  comm_tmul_of_mem 𝒜 ℬ hχψ ha hb

@[simp]
theorem commGraded_comp_includeLeftGraded (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    (commGraded 𝒜 ℬ hχψ).comp (includeLeftGraded 𝒜 ℬ χ) = includeRightGraded ℬ 𝒜 ψ := by
  apply GradedAlgHom.coe_toAlgHom_injective
  exact comm_comp_includeLeft 𝒜 ℬ hχψ

@[simp]
theorem commGraded_comp_includeRightGraded (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    (commGraded 𝒜 ℬ hχψ).comp (includeRightGraded 𝒜 ℬ χ) = includeLeftGraded ℬ 𝒜 ψ := by
  apply GradedAlgHom.coe_toAlgHom_injective
  exact comm_comp_includeRight 𝒜 ℬ hχψ

@[simp]
theorem commGraded_comp_commGraded (hχψ : ∀ i j, χ j i * ψ i j = 1)
    (hψχ : ∀ j i, ψ i j * χ j i = 1 := fun j i ↦ mul_comm (ψ i j) (χ j i) ▸ hχψ i j) :
    (commGraded ℬ 𝒜 hψχ).comp (commGraded 𝒜 ℬ hχψ) = .id R (grading 𝒜 ℬ χ) := by
  apply GradedAlgHom.coe_toAlgHom_injective
  exact comm_comp_comm 𝒜 ℬ hχψ hψχ

end CommGraded

end Algebra

section Assoc

variable {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommSemiring R] [AddCommMonoid G] [DecidableEq G]
  [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  (𝒜 : G → Submodule R A) (ℬ : G → Submodule R B) (𝒞 : G → Submodule R C)
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  (χ : AddChar G (AddChar G R))

private noncomputable def assocLeftGraded :
    grading 𝒜 ℬ χ →ₐᵍ[R] grading 𝒜 (grading ℬ 𝒞 χ) χ :=
  liftGraded 𝒜 ℬ χ
    (includeLeftGraded 𝒜 (grading ℬ 𝒞 χ) χ)
    ((includeRightGraded 𝒜 (grading ℬ 𝒞 χ) χ).comp (includeLeftGraded ℬ 𝒞 χ))
    (by
      intro i j _ ha _ hb
      rw [GradedAlgHom.comp_apply]
      exact includeRightGraded_mul_includeLeftGraded_of_mem 𝒜 (grading ℬ 𝒞 χ) χ ha
        (Graded.map_mem (includeLeftGraded ℬ 𝒞 χ) hb))

private theorem assocLeftGraded_comm {m k : G}
    {u : BraidedTensorProduct R 𝒜 ℬ χ} (hu : u ∈ grading 𝒜 ℬ χ m)
    {c : C} (hc : c ∈ 𝒞 k) :
    ((includeRightGraded 𝒜 (grading ℬ 𝒞 χ) χ).comp (includeRightGraded ℬ 𝒞 χ)) c *
        assocLeftGraded 𝒜 ℬ 𝒞 χ u =
      χ k m • (assocLeftGraded 𝒜 ℬ 𝒞 χ u *
        ((includeRightGraded 𝒜 (grading ℬ 𝒞 χ) χ).comp (includeRightGraded ℬ 𝒞 χ)) c) := by
  let ιA := includeLeftGraded 𝒜 (grading ℬ 𝒞 χ) χ
  let ιB := (includeRightGraded 𝒜 (grading ℬ 𝒞 χ) χ).comp (includeLeftGraded ℬ 𝒞 χ)
  let ιC := (includeRightGraded 𝒜 (grading ℬ 𝒞 χ) χ).comp (includeRightGraded ℬ 𝒞 χ)
  let F := assocLeftGraded 𝒜 ℬ 𝒞 χ
  let L : BraidedTensorProduct R 𝒜 ℬ χ →ₗ[R] BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ :=
    LinearMap.mul R (BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ) (ιC c) ∘ₗ
      F.toAlgHom.toLinearMap
  let M : BraidedTensorProduct R 𝒜 ℬ χ →ₗ[R] BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ :=
    χ k m •
      ((LinearMap.mul R (BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ)).flip (ιC c) ∘ₗ
        F.toAlgHom.toLinearMap)
  change L u = M u
  refine grading_le 𝒜 ℬ χ (M := LinearMap.eqLocus L M) (fun i j hij a ha b hb ↦ ?_) hu
  rw [LinearMap.mem_eqLocus]
  change ιC c * F (tmul 𝒜 ℬ χ a b) = χ k m • (F (tmul 𝒜 ℬ χ a b) * ιC c)
  have hF : F (tmul 𝒜 ℬ χ a b) = ιA a * ιB b :=
    liftGraded_tmul 𝒜 ℬ χ ιA ιB _ a b
  have hCA : ιC c * ιA a = χ k i • (ιA a * ιC c) :=
    includeRightGraded_mul_includeLeftGraded_of_mem 𝒜 (grading ℬ 𝒞 χ) χ ha
      (Graded.map_mem (includeRightGraded ℬ 𝒞 χ) hc)
  have hCB : ιC c * ιB b = χ k j • (ιB b * ιC c) := by
    simp only [ιB, ιC, GradedAlgHom.comp_apply, ← map_mul,
      includeRightGraded_mul_includeLeftGraded_of_mem ℬ 𝒞 χ hb hc, map_smul]
  rw [hF, ← mul_assoc, hCA, smul_mul_assoc, mul_assoc (ιA a), hCB, mul_smul_comm, smul_smul,
    ← AddChar.map_add_eq_mul, hij, mul_assoc]

/-- The graded associator `((A ⊗_χ B) ⊗_χ C) →ₐᵍ[R] (A ⊗_χ (B ⊗_χ C))` sending
`((a ⊗ₜ b) ⊗ₜ c)` to `(a ⊗ₜ (b ⊗ₜ c))`. -/
noncomputable def assocGraded :
    grading (grading 𝒜 ℬ χ) 𝒞 χ →ₐᵍ[R] grading 𝒜 (grading ℬ 𝒞 χ) χ :=
  liftGraded (grading 𝒜 ℬ χ) 𝒞 χ
    (assocLeftGraded 𝒜 ℬ 𝒞 χ)
    ((includeRightGraded 𝒜 (grading ℬ 𝒞 χ) χ).comp (includeRightGraded ℬ 𝒞 χ))
    (by
      intro _ _ _ hu _ hc
      exact assocLeftGraded_comm 𝒜 ℬ 𝒞 χ hu hc)

@[simp]
theorem assocGraded_tmul_tmul (a : A) (b : B) (c : C) :
    assocGraded 𝒜 ℬ 𝒞 χ (tmul (grading 𝒜 ℬ χ) 𝒞 χ (tmul 𝒜 ℬ χ a b) c) =
      tmul 𝒜 (grading ℬ 𝒞 χ) χ a (tmul ℬ 𝒞 χ b c) := by
  rw [assocGraded, liftGraded_tmul, assocLeftGraded, liftGraded_tmul]
  simp [one_def]

private noncomputable def assocRightGraded :
    grading ℬ 𝒞 χ →ₐᵍ[R] grading (grading 𝒜 ℬ χ) 𝒞 χ :=
  liftGraded ℬ 𝒞 χ
    ((includeLeftGraded (grading 𝒜 ℬ χ) 𝒞 χ).comp (includeRightGraded 𝒜 ℬ χ))
    (includeRightGraded (grading 𝒜 ℬ χ) 𝒞 χ)
    (by
      intro j k _ hb _ hc
      rw [GradedAlgHom.comp_apply]
      exact includeRightGraded_mul_includeLeftGraded_of_mem (grading 𝒜 ℬ χ) 𝒞 χ
        (Graded.map_mem (includeRightGraded 𝒜 ℬ χ) hb) hc)

private theorem assocRightGraded_comm {i n : G}
    {a : A} (ha : a ∈ 𝒜 i)
    {v : BraidedTensorProduct R ℬ 𝒞 χ} (hv : v ∈ grading ℬ 𝒞 χ n) :
    assocRightGraded 𝒜 ℬ 𝒞 χ v *
        ((includeLeftGraded (grading 𝒜 ℬ χ) 𝒞 χ).comp (includeLeftGraded 𝒜 ℬ χ)) a =
      χ n i • (((includeLeftGraded (grading 𝒜 ℬ χ) 𝒞 χ).comp (includeLeftGraded 𝒜 ℬ χ)) a *
        assocRightGraded 𝒜 ℬ 𝒞 χ v) := by
  let κA := (includeLeftGraded (grading 𝒜 ℬ χ) 𝒞 χ).comp (includeLeftGraded 𝒜 ℬ χ)
  let κB := (includeLeftGraded (grading 𝒜 ℬ χ) 𝒞 χ).comp (includeRightGraded 𝒜 ℬ χ)
  let κC := includeRightGraded (grading 𝒜 ℬ χ) 𝒞 χ
  let GMap := assocRightGraded 𝒜 ℬ 𝒞 χ
  let L : BraidedTensorProduct R ℬ 𝒞 χ →ₗ[R] BraidedTensorProduct R (grading 𝒜 ℬ χ) 𝒞 χ :=
    (LinearMap.mul R (BraidedTensorProduct R (grading 𝒜 ℬ χ) 𝒞 χ)).flip (κA a) ∘ₗ
      GMap.toAlgHom.toLinearMap
  let M : BraidedTensorProduct R ℬ 𝒞 χ →ₗ[R] BraidedTensorProduct R (grading 𝒜 ℬ χ) 𝒞 χ :=
    χ n i •
      (LinearMap.mul R (BraidedTensorProduct R (grading 𝒜 ℬ χ) 𝒞 χ) (κA a) ∘ₗ
        GMap.toAlgHom.toLinearMap)
  change L v = M v
  refine grading_le ℬ 𝒞 χ (M := LinearMap.eqLocus L M) (fun j k hjk b hb c hc ↦ ?_) hv
  rw [LinearMap.mem_eqLocus]
  change GMap (tmul ℬ 𝒞 χ b c) * κA a = χ n i • (κA a * GMap (tmul ℬ 𝒞 χ b c))
  have hG : GMap (tmul ℬ 𝒞 χ b c) = κB b * κC c :=
    liftGraded_tmul ℬ 𝒞 χ κB κC _ b c
  have hCA : κC c * κA a = χ k i • (κA a * κC c) :=
    includeRightGraded_mul_includeLeftGraded_of_mem (grading 𝒜 ℬ χ) 𝒞 χ
      (Graded.map_mem (includeLeftGraded 𝒜 ℬ χ) ha) hc
  have hBA : κB b * κA a = χ j i • (κA a * κB b) := by
    simp only [κA, κB, GradedAlgHom.comp_apply, ← map_mul,
      includeRightGraded_mul_includeLeftGraded_of_mem 𝒜 ℬ χ ha hb, map_smul]
  rw [hG, mul_assoc, hCA, mul_smul_comm, ← mul_assoc (κB b), hBA, smul_mul_assoc, smul_smul,
    mul_comm (χ k i) (χ j i), ← mul_apply, ← AddChar.map_add_eq_mul, hjk, mul_assoc]

/-- The inverse graded associator `(A ⊗_χ (B ⊗_χ C)) →ₐᵍ[R] ((A ⊗_χ B) ⊗_χ C)` sending
`(a ⊗ₜ (b ⊗ₜ c))` to `((a ⊗ₜ b) ⊗ₜ c)`. -/
noncomputable def assocSymmGraded :
    grading 𝒜 (grading ℬ 𝒞 χ) χ →ₐᵍ[R] grading (grading 𝒜 ℬ χ) 𝒞 χ :=
  liftGraded 𝒜 (grading ℬ 𝒞 χ) χ
    ((includeLeftGraded (grading 𝒜 ℬ χ) 𝒞 χ).comp (includeLeftGraded 𝒜 ℬ χ))
    (assocRightGraded 𝒜 ℬ 𝒞 χ)
    (by
      intro _ _ _ ha _ hv
      exact assocRightGraded_comm 𝒜 ℬ 𝒞 χ ha hv)

@[simp]
theorem assocSymmGraded_tmul_tmul (a : A) (b : B) (c : C) :
    assocSymmGraded 𝒜 ℬ 𝒞 χ (tmul 𝒜 (grading ℬ 𝒞 χ) χ a (tmul ℬ 𝒞 χ b c)) =
      tmul (grading 𝒜 ℬ χ) 𝒞 χ (tmul 𝒜 ℬ χ a b) c := by
  rw [assocSymmGraded, liftGraded_tmul, assocRightGraded, liftGraded_tmul]
  simp [one_def]

@[simp]
theorem assocSymmGraded_comp_assocGraded :
    (assocSymmGraded 𝒜 ℬ 𝒞 χ).comp (assocGraded 𝒜 ℬ 𝒞 χ) =
      .id R (grading (grading 𝒜 ℬ χ) 𝒞 χ) := by
  apply gradedAlgHom_ext
  · apply gradedAlgHom_ext
    · ext a; simp
    · ext b; simp
  · ext c; simp [one_def]

@[simp]
theorem assocGraded_comp_assocSymmGraded :
    (assocGraded 𝒜 ℬ 𝒞 χ).comp (assocSymmGraded 𝒜 ℬ 𝒞 χ) =
      .id R (grading 𝒜 (grading ℬ 𝒞 χ) χ) := by
  apply gradedAlgHom_ext
  · ext a; simp [one_def]
  · apply gradedAlgHom_ext
    · ext b; simp
    · ext c; simp

/-- The `R`-algebra associator equivalence
`((A ⊗_χ B) ⊗_χ C) ≃ₐ[R] (A ⊗_χ (B ⊗_χ C))` for bicharacter-twisted tensor products over a common
commutative grading monoid. -/
noncomputable def assocAlgEquiv :
    BraidedTensorProduct R (grading 𝒜 ℬ χ) 𝒞 χ ≃ₐ[R]
      BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ :=
  AlgEquiv.ofAlgHom
    (assocGraded 𝒜 ℬ 𝒞 χ).toAlgHom
    (assocSymmGraded 𝒜 ℬ 𝒞 χ).toAlgHom
    (congrArg GradedAlgHom.toAlgHom (assocGraded_comp_assocSymmGraded 𝒜 ℬ 𝒞 χ))
    (congrArg GradedAlgHom.toAlgHom (assocSymmGraded_comp_assocGraded 𝒜 ℬ 𝒞 χ))

@[simp]
theorem assocAlgEquiv_apply (z : BraidedTensorProduct R (grading 𝒜 ℬ χ) 𝒞 χ) :
    assocAlgEquiv 𝒜 ℬ 𝒞 χ z = assocGraded 𝒜 ℬ 𝒞 χ z := by
  rfl

@[simp]
theorem assocAlgEquiv_symm_apply (z : BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ) :
    (assocAlgEquiv 𝒜 ℬ 𝒞 χ).symm z = assocSymmGraded 𝒜 ℬ 𝒞 χ z := by
  rfl

theorem assocAlgEquiv_tmul_tmul (a : A) (b : B) (c : C) :
    assocAlgEquiv 𝒜 ℬ 𝒞 χ (tmul (grading 𝒜 ℬ χ) 𝒞 χ (tmul 𝒜 ℬ χ a b) c) =
      tmul 𝒜 (grading ℬ 𝒞 χ) χ a (tmul ℬ 𝒞 χ b c) :=
  assocGraded_tmul_tmul 𝒜 ℬ 𝒞 χ a b c

theorem assocAlgEquiv_symm_tmul_tmul (a : A) (b : B) (c : C) :
    (assocAlgEquiv 𝒜 ℬ 𝒞 χ).symm (tmul 𝒜 (grading ℬ 𝒞 χ) χ a (tmul ℬ 𝒞 χ b c)) =
      tmul (grading 𝒜 ℬ χ) 𝒞 χ (tmul 𝒜 ℬ χ a b) c :=
  assocSymmGraded_tmul_tmul 𝒜 ℬ 𝒞 χ a b c

end Assoc

end TotalGrading

section Examples

-- Cross-module instance-diamond checks: `Ring`, `Semiring`, `AddCommGroup`, and `Algebra` agree
-- definitionally with `instAddCommMonoid` and `instModule`, and synthesize `SMulCommClass` and
-- `IsScalarTower`.
example {R G₁ G₂ A B : Type*} [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
    [DecidableEq G₁] [DecidableEq G₂] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (χ : AddChar G₂ (AddChar G₁ R)) :
    (inferInstance : Ring (BraidedTensorProduct R 𝒜 ℬ χ)).toAddCommGroup.toAddCommMonoid =
      instAddCommMonoid 𝒜 ℬ χ := rfl

example {R G₁ G₂ A B : Type*} [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
    [DecidableEq G₁] [DecidableEq G₂] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (χ : AddChar G₂ (AddChar G₁ R)) :
    (inferInstance : Ring (BraidedTensorProduct R 𝒜 ℬ χ)).toSemiring =
      instSemiring 𝒜 ℬ χ := rfl

example {R G₁ G₂ A B : Type*} [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
    [DecidableEq G₁] [DecidableEq G₂] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (χ : AddChar G₂ (AddChar G₁ R)) :
    (inferInstance : Algebra R (BraidedTensorProduct R 𝒜 ℬ χ)).toModule =
      instModule 𝒜 ℬ χ := rfl

noncomputable example {R G A B C : Type*} [CommSemiring R] [AddCommMonoid G] [DecidableEq G]
    [Semiring A] [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (𝒜 : G → Submodule R A) (ℬ : G → Submodule R B) (𝒞 : G → Submodule R C)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
    (χ : AddChar G (AddChar G R)) :
    BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ →ₗ[R]
      BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ →ₗ[R]
        BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ :=
  LinearMap.mul R (BraidedTensorProduct R 𝒜 (grading ℬ 𝒞 χ) χ)

private abbrev tensorGrading : ℕ → Submodule ℤ (TensorAlgebra ℤ ℤ) :=
  (LinearMap.range (TensorAlgebra.ι ℤ : ℤ →ₗ[ℤ] TensorAlgebra ℤ ℤ) ^ ·)

private def exampleChar (r : ℤ) : AddChar ℕ ℤ :=
  ⟨fun i ↦ r ^ i, pow_zero r, pow_add r⟩

private def exampleBichar : AddChar ℕ (AddChar ℕ ℤ) :=
  ⟨fun j ↦ exampleChar (2 ^ j),
    by ext i; simp [exampleChar],
    by intro j₁ j₂; ext i; simp [exampleChar, pow_add, mul_pow]⟩

private def exampleX : TensorAlgebra ℤ ℤ := TensorAlgebra.ι ℤ 1

-- Concrete noncommutative example: Manin's quantum plane at `q = 2` over `ℤ`, realized as the
-- braided tensor product of two copies of `TensorAlgebra ℤ ℤ` with `χ j i = 2 ^ (j * i)`.
example :
    tmul tensorGrading tensorGrading exampleBichar 1 exampleX *
        tmul tensorGrading tensorGrading exampleBichar exampleX 1 =
      (2 : ℤ) • (tmul tensorGrading tensorGrading exampleBichar exampleX 1 *
        tmul tensorGrading tensorGrading exampleBichar 1 exampleX) ∧
      tmul tensorGrading tensorGrading exampleBichar 1 exampleX *
          tmul tensorGrading tensorGrading exampleBichar exampleX 1 ≠
        tmul tensorGrading tensorGrading exampleBichar exampleX 1 *
          tmul tensorGrading tensorGrading exampleBichar 1 exampleX ∧
      tmul tensorGrading tensorGrading exampleBichar exampleX exampleX ∈
        grading tensorGrading tensorGrading exampleBichar 2 := by
  have hX : exampleX ∈ tensorGrading 1 := by
    simpa only [exampleX, tensorGrading, pow_one] using
      LinearMap.mem_range_self (TensorAlgebra.ι ℤ : ℤ →ₗ[ℤ] TensorAlgebra ℤ ℤ) (1 : ℤ)
  refine ⟨?_, ?_,
    tmul_mem_grading tensorGrading tensorGrading exampleBichar (i := 1) (j := 1) hX hX⟩
  · rw [one_tmul_mul_tmul_one_of_mem tensorGrading tensorGrading exampleBichar (i := 1) (j := 1)
      hX hX, tmul_one_mul_one_tmul]
    rfl
  · rw [one_tmul_mul_tmul_one_of_mem tensorGrading tensorGrading exampleBichar (i := 1) (j := 1)
      hX hX, tmul_one_mul_one_tmul]
    intro hEq
    let ε : TensorAlgebra ℤ ℤ →ₗ[ℤ] ℤ := (TensorAlgebra.lift ℤ LinearMap.id).toLinearMap
    have hT := congrArg (fun z ↦
      TensorProduct.lift ((LinearMap.mul ℤ ℤ ∘ₗ ε).compl₂ ε) z.toTensorProduct) hEq
    simp only [toTensorProduct_smul, map_smul, toTensorProduct_tmul, TensorProduct.lift.tmul,
      LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.mul_apply', ε, exampleX,
      AlgHom.toLinearMap_apply, TensorAlgebra.lift_ι_apply, LinearMap.id_apply, mul_one,
      smul_eq_mul] at hT
    exact absurd hT (by decide)

end Examples

end BraidedTensorProduct

end TauCeti
