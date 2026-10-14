/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Completed.Map

/-!
# Tensoring bounded maps on completed tensor words

The completed tensor square is a product indexed by pairs of tensor lengths. Two
bounded-length maps act on it by finite sums of their length components. On the
algebraic tensor product this agrees with the ordinary tensor product of the maps.
Each output bidegree depends only on a finite rectangle of input bidegrees. This
permits transporting coalgebra identities from finite words to completed words.

The length-completion convention follows Loday--Vallette, *Algebraic Operads*,
Chapters 9--10; tensor products and finite sums use Mathlib's linear-map API.
-/

public section

open scoped TensorProduct

namespace TauCeti.CompletedTensorWords

universe uR uM uN uP uQ

variable {R : Type uR} [CommSemiring R]
  {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- The product of tensor-power bidegrees, rather than the algebraic tensor product
of the two completed modules. -/
abbrev TensorProduct (R : Type uR) (M : Type uM) (N : Type uN)
    [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] :=
  ∀ p q : ℕ, TensorPower R p M ⊗[R] TensorPower R q N

/-- Include an algebraic tensor of finite words into the product of its bidegrees. -/
noncomputable def tensorInclusion :
    TensorWords R M ⊗[R] TensorWords R N →ₗ[R] TensorProduct R M N :=
  LinearMap.pi fun p ↦ LinearMap.pi fun q ↦
    TensorProduct.map (TensorWords.component R M p) (TensorWords.component R N q)

/-- Each bidegree of the inclusion is the tensor product of the two projections. -/
@[simp]
theorem tensorInclusion_apply (z : TensorWords R M ⊗[R] TensorWords R N) (p q : ℕ) :
    tensorInclusion z p q =
      TensorProduct.map (TensorWords.component R M p) (TensorWords.component R N q) z :=
  (rfl)

/-- Act on the completed tensor product by two finite-word maps, using their
length bounds as finite cutoffs. -/
noncomputable def tensorMap (c d : ℕ)
    (f : TensorWords R M →ₗ[R] TensorWords R P)
    (g : TensorWords R N →ₗ[R] TensorWords R Q) :
    TensorProduct R M N →ₗ[R] TensorProduct R P Q :=
  LinearMap.pi fun p ↦ LinearMap.pi fun q ↦
    ∑ i ∈ Finset.range (p + 1 + c), ∑ j ∈ Finset.range (q + 1 + d),
      TensorProduct.map
          (TensorWords.component R P p ∘ₗ f ∘ₗ TensorWords.of R M i)
          (TensorWords.component R Q q ∘ₗ g ∘ₗ TensorWords.of R N j) ∘ₗ
        (LinearMap.proj j ∘ₗ LinearMap.proj i)

/-- A coordinate of the completed tensor map is a finite sum over input bidegrees. -/
@[simp]
theorem tensorMap_apply (c d : ℕ)
    (f : TensorWords R M →ₗ[R] TensorWords R P)
    (g : TensorWords R N →ₗ[R] TensorWords R Q) (z : TensorProduct R M N) (p q : ℕ) :
    tensorMap c d f g z p q =
      ∑ i ∈ Finset.range (p + 1 + c), ∑ j ∈ Finset.range (q + 1 + d),
        TensorProduct.map
          (TensorWords.component R P p ∘ₗ f ∘ₗ TensorWords.of R M i)
          (TensorWords.component R Q q ∘ₗ g ∘ₗ TensorWords.of R N j) (z i j) := by
  simp [tensorMap]

/-- Each output coordinate depends only on the indicated finite input rectangle. -/
theorem tensorMap_apply_eq_of_eq (c d : ℕ)
    (f : TensorWords R M →ₗ[R] TensorWords R P)
    (g : TensorWords R N →ₗ[R] TensorWords R Q)
    {z w : TensorProduct R M N} (p q : ℕ)
    (h : ∀ i < p + 1 + c, ∀ j < q + 1 + d, z i j = w i j) :
    tensorMap c d f g z p q = tensorMap c d f g w p q := by
  simp only [tensorMap_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [h i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]

/-- On an algebraic tensor of finite words the completed map agrees with the
ordinary tensor product of the maps. -/
@[simp]
theorem tensorMap_tensorInclusion (c d : ℕ)
    (f : TensorWords R M →ₗ[R] TensorWords R P)
    (g : TensorWords R N →ₗ[R] TensorWords R Q)
    (hf : HasLengthBound c f) (hg : HasLengthBound d g)
    (z : TensorWords R M ⊗[R] TensorWords R N) :
    tensorMap c d f g (tensorInclusion z) = tensorInclusion (TensorProduct.map f g z) := by
  classical
  rw [hasLengthBound_iff] at hf hg
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    funext p q
    simp only [tensorMap_apply, tensorInclusion_apply, TensorProduct.map_tmul,
      LinearMap.comp_apply]
    simp only [← TensorProduct.tmul_sum]
    rw [← TensorProduct.sum_tmul]
    simp only [← map_sum]
    simp only [TensorWords.component_apply]
    rw [← truncate_eq_sum, ← truncate_eq_sum, hf p x, hg q y]
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Deconcatenation of finite words is the included algebraic coproduct. -/
@[simp]
theorem tensorInclusion_deconcatenation (x : TensorWords R M) :
    tensorInclusion (TensorWords.deconcatenation R M x) =
      deconcatenation R M (x : CompletedTensorWords R M) := by
  funext p q
  simpa only [tensorInclusion_apply, DFinsupp.coeFnLinearMap_apply] using
    (deconcatenation_coe R M x p q).symm

/-- Computing a bidegree after deconcatenation and a bounded tensor map only
requires a finite prefix of the original word. -/
theorem tensorMap_deconcatenation_truncate (c d : ℕ)
    (f : TensorWords R M →ₗ[R] TensorWords R P)
    (g : TensorWords R M →ₗ[R] TensorWords R Q)
    (x : CompletedTensorWords R M) (p q n : ℕ) (hn : p + q + 1 + c + d ≤ n) :
    tensorMap c d f g (deconcatenation R M (truncate R M n x)) p q =
      tensorMap c d f g (deconcatenation R M x) p q := by
  apply tensorMap_apply_eq_of_eq
  intro i hi j hj
  have hij : i + j < n := by omega
  simp [deconcatenation_apply, truncate_apply, hij]

end TauCeti.CompletedTensorWords
