/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.RingTheory.GradedAlgebra.Rescale

import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Bicharacter-twisted tensor products of graded algebras

Given an `R`-algebra `A` graded by `𝒜 : G₁ → Submodule R A`, an `R`-algebra `B` graded by
`ℬ : G₂ → Submodule R B`, and a multiplicative bicharacter `χ : AddChar G₂ (AddChar G₁ R)` on the
grading monoids `G₂` and `G₁`, the *braided* (or *bicharacter-twisted*) tensor product
`BraidedTensorProduct R 𝒜 ℬ χ` has the underlying `R`-module `A ⊗[R] B` equipped with the
multiplication characterized on pure tensors with homogeneous inner factors `b₁ ∈ ℬ j₁` and
`a₂ ∈ 𝒜 i₂` by

`(a₁ ⊗ₜ b₁) * (a₂ ⊗ₜ b₂) = χ j₁ i₂ • ((a₁ * a₂) ⊗ₜ (b₁ * b₂))`.

Mathlib's `GradedTensorProduct` covers the Koszul sign `(-1) ^ (j₁ * i₂)` when both algebras share
a commutative semiring of degrees equipped with a `Module` action on `Additive ℤˣ`.  Quantum
enveloping algebras require the general bicharacter twist: Lusztig's braided coproduct
`r : U⁺ → U⁺ ⊗_χ U⁺` on the positive half of a quantized enveloping algebra is an algebra
homomorphism only when `U⁺ ⊗ U⁺` carries the multiplication twisted by the root-lattice bicharacter
`χ(μ, ν) = q^{(μ, ν)}` on `Q⁺ = ι →₀ ℕ` (or on the root lattice `Q`).

Rather than decomposing all four tensor factors and checking associativity on quadruple sums, we
use the degreewise rescaling endomorphism `TauCeti.GradedAlgebra.rescale 𝒜 φ` of `A` acting by
`φ i` on `𝒜 i` for each character `φ : AddChar G₁ R`.  Decomposing only the first right factor
`b₁ ∈ ℬ j₁` and rescaling `a₂` by `χ j₁` defines the product directly as an `R`-bilinear map and
reduces associativity and unitality to those of `A`, `B`, and `χ`.

## Main definitions

* `TauCeti.BraidedTensorProduct R 𝒜 ℬ χ`: the `R`-module copy of `A ⊗[R] B` carrying the
  `χ`-twisted algebra structure.
* `TauCeti.BraidedTensorProduct.ofLinearEquiv`: the canonical `R`-linear equivalence
  `A ⊗[R] B ≃ₗ[R] BraidedTensorProduct R 𝒜 ℬ χ`.
* `TauCeti.BraidedTensorProduct.tmul`: the pure tensor `a ⊗ₜ b` in
  `BraidedTensorProduct R 𝒜 ℬ χ`, bundled bilinearly as `tmulBilinear`.
* `TauCeti.BraidedTensorProduct.includeLeft` and `TauCeti.BraidedTensorProduct.includeRight`:
  the canonical `R`-algebra inclusions `a ↦ a ⊗ₜ 1` and `b ↦ 1 ⊗ₜ b`.
* `TauCeti.BraidedTensorProduct.lift` and `TauCeti.BraidedTensorProduct.liftEquiv`: the universal
  property characterizing `R`-algebra maps out of `BraidedTensorProduct R 𝒜 ℬ χ` as pairs `(f, g)`
  satisfying `g b * f a = χ j i • (f a * g b)` for `a ∈ 𝒜 i` and `b ∈ ℬ j`.
* `TauCeti.BraidedTensorProduct.map`: functoriality for `GradedAlgHom`s.
* `TauCeti.BraidedTensorProduct.trivialAlgEquiv`: the `R`-algebra equivalence with the ordinary
  tensor product `A ⊗[R] B` when `χ = 1`.
* `TauCeti.BraidedTensorProduct.comm` and `TauCeti.BraidedTensorProduct.commAlgEquiv`: the braided
  factor-swap `R`-algebra homomorphism and equivalence for paired bicharacters `χ, ψ` satisfying
  `∀ i j, χ j i * ψ i j = 1`.

## Main results

* `TauCeti.BraidedTensorProduct.tmul_mul_tmul_of_mem` and
  `TauCeti.BraidedTensorProduct.tmul_coe_mul_coe_tmul`: the twisted product formula on pure tensors
  with homogeneous inner factors.
* `TauCeti.BraidedTensorProduct.one_tmul_mul_tmul_one_of_mem`: the defining braiding relation
  `(1 ⊗ₜ b) * (a ⊗ₜ 1) = χ j i • (a ⊗ₜ b)` for `a ∈ 𝒜 i` and `b ∈ ℬ j`.
* `TauCeti.BraidedTensorProduct.algHom_ext`: two `R`-algebra homomorphisms out of
  `BraidedTensorProduct R 𝒜 ℬ χ` agree if they agree on both factor inclusions.
* `TauCeti.BraidedTensorProduct.restrictScalars_ker_map`: for surjective `GradedAlgHom`s `f` and
  `g` over a commutative ring, the kernel of `map χ f g` is `ker f ⊗ B + A ⊗ ker g`.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §4.7.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.2.1.
* S. Majid, *Foundations of Quantum Group Theory*, Cambridge University Press, 1995, §9.2.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe uR uG₁ uG₂ uA uB uC

/-- The bicharacter-twisted (braided) tensor product of an `R`-module `A` carrying a submodule
family `𝒜 : G₁ → Submodule R A` and an `R`-module `B` carrying `ℬ : G₂ → Submodule R B`, twisted
by a multiplicative bicharacter `χ : AddChar G₂ (AddChar G₁ R)`.

When `𝒜` and `ℬ` are `GradedAlgebra`s, `BraidedTensorProduct R 𝒜 ℬ χ` is an `R`-algebra with
`(a₁ ⊗ₜ b₁) * (a₂ ⊗ₜ b₂) = χ j₁ i₂ • ((a₁ * a₂) ⊗ₜ (b₁ * b₂))` for `b₁ ∈ ℬ j₁` and `a₂ ∈ 𝒜 i₂`. -/
inductive BraidedTensorProduct (R : Type uR) {G₁ : Type uG₁} {G₂ : Type uG₂}
    {A : Type uA} {B : Type uB} [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B] :
    (G₁ → Submodule R A) → (G₂ → Submodule R B) → AddChar G₂ (AddChar G₁ R) →
      Type (max uA uB) where
  /-- Regard an element of `A ⊗[R] B` as an element of `BraidedTensorProduct R 𝒜 ℬ χ`. -/
  | of (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B)
      (χ : AddChar G₂ (AddChar G₁ R)) (x : A ⊗[R] B) :
      BraidedTensorProduct R 𝒜 ℬ χ

namespace BraidedTensorProduct

section Linear

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
  [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]

/-- Extract the underlying element of `A ⊗[R] B` from `BraidedTensorProduct R 𝒜 ℬ χ`. -/
def toTensorProduct :
    {_𝒜 : G₁ → Submodule R A} → {_ℬ : G₂ → Submodule R B} →
      {_χ : AddChar G₂ (AddChar G₁ R)} → BraidedTensorProduct R _𝒜 _ℬ _χ → A ⊗[R] B
  | _, _, _, of _ _ _ x => x

@[simp] theorem toTensorProduct_of (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B)
    (χ : AddChar G₂ (AddChar G₁ R)) (x : A ⊗[R] B) :
    (of 𝒜 ℬ χ x).toTensorProduct = x := by rfl

@[simp] theorem of_toTensorProduct {𝒜 : G₁ → Submodule R A} {ℬ : G₂ → Submodule R B}
    {χ : AddChar G₂ (AddChar G₁ R)} (x : BraidedTensorProduct R 𝒜 ℬ χ) :
    of 𝒜 ℬ χ x.toTensorProduct = x := by cases x; rfl

/-- Two elements of `BraidedTensorProduct R 𝒜 ℬ χ` are equal if their underlying tensors in
`A ⊗[R] B` are equal. -/
@[ext] theorem ext {𝒜 : G₁ → Submodule R A} {ℬ : G₂ → Submodule R B}
    {χ : AddChar G₂ (AddChar G₁ R)} {x y : BraidedTensorProduct R 𝒜 ℬ χ}
    (h : x.toTensorProduct = y.toTensorProduct) : x = y := by
  rw [← of_toTensorProduct x, ← of_toTensorProduct y, h]

variable (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) (χ : AddChar G₂ (AddChar G₁ R))

instance instAddCommMonoid : AddCommMonoid (BraidedTensorProduct R 𝒜 ℬ χ) :=
  fast_instance%
    (⟨toTensorProduct, of 𝒜 ℬ χ, of_toTensorProduct, toTensorProduct_of 𝒜 ℬ χ⟩ :
      BraidedTensorProduct R 𝒜 ℬ χ ≃ A ⊗[R] B).addCommMonoid

instance instModule : Module R (BraidedTensorProduct R 𝒜 ℬ χ) :=
  fast_instance%
    AddEquiv.module R
      (⟨toTensorProduct, of 𝒜 ℬ χ, of_toTensorProduct, toTensorProduct_of 𝒜 ℬ χ⟩ :
        BraidedTensorProduct R 𝒜 ℬ χ ≃ A ⊗[R] B).addEquiv

/-- The canonical `R`-linear equivalence between `A ⊗[R] B` and `BraidedTensorProduct R 𝒜 ℬ χ`. -/
def ofLinearEquiv : A ⊗[R] B ≃ₗ[R] BraidedTensorProduct R 𝒜 ℬ χ where
  toFun := of 𝒜 ℬ χ
  invFun := toTensorProduct
  left_inv := toTensorProduct_of 𝒜 ℬ χ
  right_inv := of_toTensorProduct
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ofLinearEquiv_apply (x : A ⊗[R] B) : ofLinearEquiv 𝒜 ℬ χ x = of 𝒜 ℬ χ x := by rfl

@[simp] theorem ofLinearEquiv_symm_apply (x : BraidedTensorProduct R 𝒜 ℬ χ) :
    (ofLinearEquiv 𝒜 ℬ χ).symm x = x.toTensorProduct := by rfl

@[simp] theorem of_zero : of 𝒜 ℬ χ (0 : A ⊗[R] B) = 0 := by rfl

@[simp] theorem of_add (x y : A ⊗[R] B) : of 𝒜 ℬ χ (x + y) = of 𝒜 ℬ χ x + of 𝒜 ℬ χ y := by rfl

@[simp] theorem of_smul (r : R) (x : A ⊗[R] B) : of 𝒜 ℬ χ (r • x) = r • of 𝒜 ℬ χ x := by rfl

@[simp] theorem toTensorProduct_zero : (0 : BraidedTensorProduct R 𝒜 ℬ χ).toTensorProduct = 0 := by
  rfl

@[simp] theorem toTensorProduct_add (x y : BraidedTensorProduct R 𝒜 ℬ χ) :
    (x + y).toTensorProduct = x.toTensorProduct + y.toTensorProduct :=
  toTensorProduct_of 𝒜 ℬ χ _

@[simp] theorem toTensorProduct_smul (r : R) (x : BraidedTensorProduct R 𝒜 ℬ χ) :
    (r • x).toTensorProduct = r • x.toTensorProduct :=
  toTensorProduct_of 𝒜 ℬ χ _

/-- Form the pure tensor `a ⊗ₜ b` inside `BraidedTensorProduct R 𝒜 ℬ χ`. -/
def tmul (a : A) (b : B) : BraidedTensorProduct R 𝒜 ℬ χ := of 𝒜 ℬ χ (a ⊗ₜ[R] b)

/-- Pure tensor formation bundled as an `R`-bilinear map into `BraidedTensorProduct R 𝒜 ℬ χ`. -/
def tmulBilinear : A →ₗ[R] B →ₗ[R] BraidedTensorProduct R 𝒜 ℬ χ :=
  (TensorProduct.mk R A B).compr₂ (ofLinearEquiv 𝒜 ℬ χ).toLinearMap

theorem tmulBilinear_def :
    tmulBilinear 𝒜 ℬ χ = (TensorProduct.mk R A B).compr₂ (ofLinearEquiv 𝒜 ℬ χ).toLinearMap := by rfl

@[simp] theorem tmulBilinear_apply (a : A) (b : B) :
    tmulBilinear 𝒜 ℬ χ a b = tmul 𝒜 ℬ χ a b := by simp [tmulBilinear, tmul]

@[simp] theorem of_tmul (a : A) (b : B) : of 𝒜 ℬ χ (a ⊗ₜ[R] b) = tmul 𝒜 ℬ χ a b := by rfl

@[simp] theorem toTensorProduct_tmul (a : A) (b : B) :
    (tmul 𝒜 ℬ χ a b).toTensorProduct = a ⊗ₜ[R] b := by rfl

@[simp] theorem tmul_add (a : A) (b₁ b₂ : B) :
    tmul 𝒜 ℬ χ a (b₁ + b₂) = tmul 𝒜 ℬ χ a b₁ + tmul 𝒜 ℬ χ a b₂ := by
  simpa only [tmulBilinear_apply] using (tmulBilinear 𝒜 ℬ χ a).map_add b₁ b₂

@[simp] theorem add_tmul (a₁ a₂ : A) (b : B) :
    tmul 𝒜 ℬ χ (a₁ + a₂) b = tmul 𝒜 ℬ χ a₁ b + tmul 𝒜 ℬ χ a₂ b := by
  simpa only [tmulBilinear_apply] using LinearMap.map_add₂ (tmulBilinear 𝒜 ℬ χ) a₁ a₂ b

@[simp] theorem smul_tmul (r : R) (a : A) (b : B) :
    tmul 𝒜 ℬ χ (r • a) b = r • tmul 𝒜 ℬ χ a b := by
  simpa only [tmulBilinear_apply] using LinearMap.map_smul₂ (tmulBilinear 𝒜 ℬ χ) r a b

@[simp] theorem tmul_smul (r : R) (a : A) (b : B) :
    tmul 𝒜 ℬ χ a (r • b) = r • tmul 𝒜 ℬ χ a b := by
  simpa only [tmulBilinear_apply] using (tmulBilinear 𝒜 ℬ χ a).map_smul r b

@[simp] theorem tmul_zero (a : A) : tmul 𝒜 ℬ χ a 0 = 0 := by
  simpa only [tmulBilinear_apply] using (tmulBilinear 𝒜 ℬ χ a).map_zero

@[simp] theorem zero_tmul (b : B) : tmul 𝒜 ℬ χ 0 b = 0 := by
  simpa only [tmulBilinear_apply] using LinearMap.map_zero₂ (tmulBilinear 𝒜 ℬ χ) b

/-- Induction principle for `BraidedTensorProduct R 𝒜 ℬ χ` reducing to pure tensors
`tmul 𝒜 ℬ χ a b` and sums, mirroring `TensorProduct.inductionOn`. -/
@[elab_as_elim] theorem inductionOn {𝒜 : G₁ → Submodule R A} {ℬ : G₂ → Submodule R B}
    {χ : AddChar G₂ (AddChar G₁ R)} {motive : BraidedTensorProduct R 𝒜 ℬ χ → Prop}
    (x : BraidedTensorProduct R 𝒜 ℬ χ) (tmul : ∀ a b, motive (tmul 𝒜 ℬ χ a b))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  rw [← of_toTensorProduct x]
  induction x.toTensorProduct using TensorProduct.inductionOn with
  | tmul a b => exact tmul a b
  | add x y hx hy => rw [of_add]; exact add _ _ hx hy

/-- Two semilinear maps out of `BraidedTensorProduct R 𝒜 ℬ χ` agree if they agree on all pure
tensors `tmul 𝒜 ℬ χ a b`. -/
theorem linearMap_ext {𝒜 : G₁ → Submodule R A} {ℬ : G₂ → Submodule R B}
    {χ : AddChar G₂ (AddChar G₁ R)} {R₂ M : Type*} [Semiring R₂] [AddCommMonoid M] [Module R₂ M]
    {σ : R →+* R₂} {f g : BraidedTensorProduct R 𝒜 ℬ χ →ₛₗ[σ] M}
    (h : ∀ a b, f (tmul 𝒜 ℬ χ a b) = g (tmul 𝒜 ℬ χ a b)) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using inductionOn with
  | tmul a b => exact h a b
  | add x y hx hy => simp [hx, hy]

end Linear

section AddCommGroup

section Left

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
  [AddCommGroup A] [AddCommMonoid B] [Module R A] [Module R B]
  (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) (χ : AddChar G₂ (AddChar G₁ R))

instance instAddCommGroup : AddCommGroup (BraidedTensorProduct R 𝒜 ℬ χ) :=
  fast_instance%
    (⟨toTensorProduct, of 𝒜 ℬ χ, of_toTensorProduct, toTensorProduct_of 𝒜 ℬ χ⟩ :
      BraidedTensorProduct R 𝒜 ℬ χ ≃ A ⊗[R] B).addCommGroup

@[simp] theorem of_neg (x : A ⊗[R] B) : of 𝒜 ℬ χ (-x) = -of 𝒜 ℬ χ x :=
  map_neg (ofLinearEquiv 𝒜 ℬ χ) x

@[simp] theorem of_sub (x y : A ⊗[R] B) : of 𝒜 ℬ χ (x - y) = of 𝒜 ℬ χ x - of 𝒜 ℬ χ y :=
  map_sub (ofLinearEquiv 𝒜 ℬ χ) x y

@[simp] theorem toTensorProduct_neg (x : BraidedTensorProduct R 𝒜 ℬ χ) :
    (-x).toTensorProduct = -x.toTensorProduct := map_neg (ofLinearEquiv 𝒜 ℬ χ).symm x

@[simp] theorem toTensorProduct_sub (x y : BraidedTensorProduct R 𝒜 ℬ χ) :
    (x - y).toTensorProduct = x.toTensorProduct - y.toTensorProduct :=
  map_sub (ofLinearEquiv 𝒜 ℬ χ).symm x y

@[simp] theorem neg_tmul (a : A) (b : B) : tmul 𝒜 ℬ χ (-a) b = -tmul 𝒜 ℬ χ a b := by
  simpa only [tmulBilinear_apply] using LinearMap.map_neg₂ (tmulBilinear 𝒜 ℬ χ) a b

@[simp] theorem sub_tmul (a₁ a₂ : A) (b : B) :
    tmul 𝒜 ℬ χ (a₁ - a₂) b = tmul 𝒜 ℬ χ a₁ b - tmul 𝒜 ℬ χ a₂ b := by
  simpa only [tmulBilinear_apply] using LinearMap.map_sub₂ (tmulBilinear 𝒜 ℬ χ) a₁ a₂ b

end Left

section Right

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
  [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
  (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) (χ : AddChar G₂ (AddChar G₁ R))

@[simp] theorem tmul_neg (a : A) (b : B) : tmul 𝒜 ℬ χ a (-b) = -tmul 𝒜 ℬ χ a b := by
  simpa only [tmulBilinear_apply] using (tmulBilinear 𝒜 ℬ χ a).map_neg b

@[simp] theorem tmul_sub (a : A) (b₁ b₂ : B) :
    tmul 𝒜 ℬ χ a (b₁ - b₂) = tmul 𝒜 ℬ χ a b₁ - tmul 𝒜 ℬ χ a b₂ := by
  simpa only [tmulBilinear_apply] using (tmulBilinear 𝒜 ℬ χ a).map_sub b₁ b₂

end Right

end AddCommGroup

section One

section Monoid

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
  [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B] [One A] [One B]
  (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) (χ : AddChar G₂ (AddChar G₁ R))

/-- The multiplicative identity `1 ⊗ₜ 1` of `BraidedTensorProduct R 𝒜 ℬ χ`. -/
instance instOne : One (BraidedTensorProduct R 𝒜 ℬ χ) where one := tmul 𝒜 ℬ χ 1 1

theorem one_def : (1 : BraidedTensorProduct R 𝒜 ℬ χ) = tmul 𝒜 ℬ χ 1 1 := by rfl

theorem toTensorProduct_one_eq_tmul :
    (1 : BraidedTensorProduct R 𝒜 ℬ χ).toTensorProduct = (1 : A) ⊗ₜ[R] (1 : B) := by rfl

end Monoid

section AddCommMonoidWithOne

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂]
  [AddCommMonoidWithOne A] [AddCommMonoidWithOne B] [Module R A] [Module R B]
  (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) (χ : AddChar G₂ (AddChar G₁ R))

@[simp] theorem of_one : of 𝒜 ℬ χ 1 = 1 := by rfl

@[simp] theorem toTensorProduct_one : (1 : BraidedTensorProduct R 𝒜 ℬ χ).toTensorProduct = 1 := by
  rfl

end AddCommMonoidWithOne

end One

section Algebra

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂] [DecidableEq G₁] [DecidableEq G₂]
  [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (χ : AddChar G₂ (AddChar G₁ R))

/-- Left multiplication on `A ⊗[R] B` twisted by degree `j₁ : G₂`, sending `(a₁, b₁)` to the
endomorphism `(a₂ ⊗ₜ b₂) ↦ (a₁ * GradedAlgebra.rescale 𝒜 (χ j₁) a₂) ⊗ₜ (b₁ * b₂)`. -/
private noncomputable def rawMulPiece (j₁ : G₂) :
    A →ₗ[R] ℬ j₁ →ₗ[R] (A ⊗[R] B →ₗ[R] A ⊗[R] B) :=
  (TensorProduct.mapBilinear (RingHom.id R) A B A B).compl₁₂
    (((LinearMap.mul R A).flip ∘ₗ (GradedAlgebra.rescale 𝒜 (χ j₁)).toAlgHom.toLinearMap).flip)
    (LinearMap.mul R B ∘ₗ (ℬ j₁).subtype)

/-- The `χ`-twisted multiplication on the underlying tensor product `A ⊗[R] B`. -/
private noncomputable def rawMul : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) :=
  TensorProduct.lift <|
    (DirectSum.toModule R G₂ (A →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B)
      (fun j₁ ↦ (rawMulPiece 𝒜 ℬ χ j₁).flip) ∘ₗ
        (DirectSum.decomposeLinearEquiv ℬ).toLinearMap).flip

private theorem rawMul_tmul_of_mem_tmul {j₁ : G₂} (a₁ : A) {b₁ : B} (hb₁ : b₁ ∈ ℬ j₁)
    (a₂ : A) (b₂ : B) :
    rawMul 𝒜 ℬ χ (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) =
      (a₁ * GradedAlgebra.rescale 𝒜 (χ j₁) a₂) ⊗ₜ[R] (b₁ * b₂) := by
  rw [rawMul, TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem ℬ hb₁,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  simp [rawMulPiece]

/-- The `χ`-twisted multiplication of `BraidedTensorProduct R 𝒜 ℬ χ` bundled as an `R`-bilinear
map. -/
noncomputable def mulHom :
    BraidedTensorProduct R 𝒜 ℬ χ →ₗ[R]
      BraidedTensorProduct R 𝒜 ℬ χ →ₗ[R] BraidedTensorProduct R 𝒜 ℬ χ :=
  ((rawMul 𝒜 ℬ χ).compl₁₂ (ofLinearEquiv 𝒜 ℬ χ).symm.toLinearMap
    (ofLinearEquiv 𝒜 ℬ χ).symm.toLinearMap).compr₂ (ofLinearEquiv 𝒜 ℬ χ).toLinearMap

/-- The `χ`-twisted multiplication on `BraidedTensorProduct R 𝒜 ℬ χ`. -/
noncomputable instance instMul : Mul (BraidedTensorProduct R 𝒜 ℬ χ) where
  mul x y := mulHom 𝒜 ℬ χ x y

theorem mul_def (x y : BraidedTensorProduct R 𝒜 ℬ χ) : x * y = mulHom 𝒜 ℬ χ x y := by rfl

@[simp] theorem mulHom_apply (x y : BraidedTensorProduct R 𝒜 ℬ χ) : mulHom 𝒜 ℬ χ x y = x * y := by
  rfl

private theorem mul_tmul_of_mem_tmul {j₁ : G₂} (a₁ : A) {b₁ : B} (hb₁ : b₁ ∈ ℬ j₁)
    (a₂ : A) (b₂ : B) :
    tmul 𝒜 ℬ χ a₁ b₁ * tmul 𝒜 ℬ χ a₂ b₂ =
      tmul 𝒜 ℬ χ (a₁ * GradedAlgebra.rescale 𝒜 (χ j₁) a₂) (b₁ * b₂) := by
  ext; simpa [mul_def, mulHom] using rawMul_tmul_of_mem_tmul 𝒜 ℬ χ a₁ hb₁ a₂ b₂

noncomputable instance instNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (BraidedTensorProduct R 𝒜 ℬ χ) where
  left_distrib x y z := (mulHom 𝒜 ℬ χ x).map_add y z
  right_distrib x y z := LinearMap.map_add₂ (mulHom 𝒜 ℬ χ) x y z
  zero_mul x := LinearMap.map_zero₂ (mulHom 𝒜 ℬ χ) x
  mul_zero x := (mulHom 𝒜 ℬ χ x).map_zero

instance instSMulCommClass :
    SMulCommClass R (BraidedTensorProduct R 𝒜 ℬ χ) (BraidedTensorProduct R 𝒜 ℬ χ) where
  smul_comm r x y := ((mulHom 𝒜 ℬ χ x).map_smul r y).symm

instance instIsScalarTower :
    IsScalarTower R (BraidedTensorProduct R 𝒜 ℬ χ) (BraidedTensorProduct R 𝒜 ℬ χ) where
  smul_assoc r x y := LinearMap.map_smul₂ (mulHom 𝒜 ℬ χ) r x y

/-- Product of two pure tensors in `BraidedTensorProduct R 𝒜 ℬ χ` when the inner factors `b₁ ∈ ℬ j₁`
and `a₂ ∈ 𝒜 i₂` are homogeneous. -/
theorem tmul_mul_tmul_of_mem {j₁ : G₂} {i₂ : G₁} (a₁ : A) {b₁ : B} (hb₁ : b₁ ∈ ℬ j₁)
    {a₂ : A} (ha₂ : a₂ ∈ 𝒜 i₂) (b₂ : B) :
    tmul 𝒜 ℬ χ a₁ b₁ * tmul 𝒜 ℬ χ a₂ b₂ =
      χ j₁ i₂ • tmul 𝒜 ℬ χ (a₁ * a₂) (b₁ * b₂) := by
  rw [mul_tmul_of_mem_tmul 𝒜 ℬ χ a₁ hb₁ a₂ b₂, GradedAlgebra.rescale_of_mem 𝒜 (χ j₁) ha₂,
    mul_smul_comm, smul_tmul]

/-- Subtype-coercion form of `tmul_mul_tmul_of_mem`, matching
`GradedTensorProduct.tmul_coe_mul_coe_tmul`. -/
theorem tmul_coe_mul_coe_tmul {j₁ : G₂} {i₂ : G₁} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B) :
    tmul 𝒜 ℬ χ a₁ b₁ * tmul 𝒜 ℬ χ a₂ b₂ =
      χ j₁ i₂ • tmul 𝒜 ℬ χ (a₁ * a₂) (b₁ * b₂) :=
  tmul_mul_tmul_of_mem 𝒜 ℬ χ a₁ b₁.2 a₂.2 b₂

/-- When the first right factor lies in degree `0`, pure tensors multiply componentwise with no
homogeneity assumption on the remaining factors. -/
theorem tmul_mul_tmul_of_mem_zero_left (a₁ : A) {b₁ : B} (hb₁ : b₁ ∈ ℬ 0) (a₂ : A) (b₂ : B) :
    tmul 𝒜 ℬ χ a₁ b₁ * tmul 𝒜 ℬ χ a₂ b₂ = tmul 𝒜 ℬ χ (a₁ * a₂) (b₁ * b₂) := by
  simp [mul_tmul_of_mem_tmul 𝒜 ℬ χ a₁ hb₁ a₂ b₂]

/-- When the second left factor lies in degree `0`, pure tensors multiply componentwise with no
homogeneity assumption on the remaining factors. -/
theorem tmul_mul_tmul_of_mem_zero_right (a₁ : A) (b₁ : B) {a₂ : A} (ha₂ : a₂ ∈ 𝒜 0) (b₂ : B) :
    tmul 𝒜 ℬ χ a₁ b₁ * tmul 𝒜 ℬ χ a₂ b₂ = tmul 𝒜 ℬ χ (a₁ * a₂) (b₁ * b₂) := by
  induction b₁ using DirectSum.Decomposition.inductionOn ℬ with
  | zero => simp
  | add x y hx hy => simp [tmul_add, add_mul, hx, hy]
  | homogeneous x =>
    rw [tmul_mul_tmul_of_mem 𝒜 ℬ χ a₁ x.2 ha₂ b₂, AddChar.map_zero_eq_one, one_smul]

@[simp] theorem tmul_one_mul_tmul (a₁ a₂ : A) (b₂ : B) :
    tmul 𝒜 ℬ χ a₁ 1 * tmul 𝒜 ℬ χ a₂ b₂ = tmul 𝒜 ℬ χ (a₁ * a₂) b₂ := by
  rw [tmul_mul_tmul_of_mem_zero_left 𝒜 ℬ χ a₁ (SetLike.one_mem_graded ℬ) a₂ b₂, one_mul]

@[simp] theorem tmul_mul_one_tmul (a₁ : A) (b₁ b₂ : B) :
    tmul 𝒜 ℬ χ a₁ b₁ * tmul 𝒜 ℬ χ 1 b₂ = tmul 𝒜 ℬ χ a₁ (b₁ * b₂) := by
  rw [tmul_mul_tmul_of_mem_zero_right 𝒜 ℬ χ a₁ b₁ (SetLike.one_mem_graded 𝒜) b₂, mul_one]

theorem tmul_one_mul_one_tmul (a : A) (b : B) :
    tmul 𝒜 ℬ χ a 1 * tmul 𝒜 ℬ χ 1 b = tmul 𝒜 ℬ χ a b := by simp

/-- The defining braiding relation `(1 ⊗ₜ b) * (a ⊗ₜ 1) = χ j i • (a ⊗ₜ b)` for `a ∈ 𝒜 i` and
`b ∈ ℬ j`. -/
theorem one_tmul_mul_tmul_one_of_mem {i : G₁} {j : G₂} {a : A} (ha : a ∈ 𝒜 i)
    {b : B} (hb : b ∈ ℬ j) :
    tmul 𝒜 ℬ χ 1 b * tmul 𝒜 ℬ χ a 1 = χ j i • tmul 𝒜 ℬ χ a b := by
  rw [tmul_mul_tmul_of_mem 𝒜 ℬ χ 1 hb ha 1, one_mul, mul_one]

private theorem mul_assoc_aux (x y z : BraidedTensorProduct R 𝒜 ℬ χ) :
    x * y * z = x * (y * z) := by
  induction x using inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
  | tmul a₁ b₁ =>
    induction b₁ using DirectSum.Decomposition.inductionOn ℬ with
    | zero => simp
    | add u v hu hv => simp [tmul_add, add_mul, hu, hv]
    | @homogeneous j₁ b₁ =>
      induction y using inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simp [mul_add, add_mul, hy₁, hy₂]
      | tmul a₂ b₂ =>
        induction b₂ using DirectSum.Decomposition.inductionOn ℬ with
        | zero => simp
        | add u v hu hv => simp [tmul_add, mul_add, add_mul, hu, hv]
        | homogeneous b₂ =>
          induction z using inductionOn with
          | add z₁ z₂ hz₁ hz₂ => simp [mul_add, hz₁, hz₂]
          | tmul a₃ b₃ =>
            rw [mul_tmul_of_mem_tmul 𝒜 ℬ χ a₁ b₁.2 a₂ b₂,
              mul_tmul_of_mem_tmul 𝒜 ℬ χ _ (SetLike.mul_mem_graded b₁.2 b₂.2) a₃ b₃,
              mul_tmul_of_mem_tmul 𝒜 ℬ χ a₂ b₂.2 a₃ b₃,
              mul_tmul_of_mem_tmul 𝒜 ℬ χ a₁ b₁.2 _ _,
              map_mul (GradedAlgebra.rescale 𝒜 (χ j₁)), ← GradedAlgebra.rescale_mul_apply,
              ← AddChar.map_add_eq_mul, mul_assoc, mul_assoc]

noncomputable instance instSemiring : Semiring (BraidedTensorProduct R 𝒜 ℬ χ) where
  __ := instNonUnitalNonAssocSemiring 𝒜 ℬ χ
  mul_assoc := by exact mul_assoc_aux 𝒜 ℬ χ
  one_mul x := by
    induction x using inductionOn with
    | tmul a b => rw [one_def, tmul_one_mul_tmul, one_mul]
    | add x y hx hy => simp [mul_add, hx, hy]
  mul_one x := by
    induction x using inductionOn with
    | tmul a b => rw [one_def, tmul_mul_one_tmul, mul_one]
    | add x y hx hy => simp [add_mul, hx, hy]

/-- `mulHom 𝒜 ℬ χ` agrees with `LinearMap.mul` for the `Semiring` structure on
`BraidedTensorProduct R 𝒜 ℬ χ`. -/
theorem mulHom_eq_mul :
    mulHom 𝒜 ℬ χ = LinearMap.mul R (BraidedTensorProduct R 𝒜 ℬ χ) := by rfl

noncomputable instance instAlgebra : Algebra R (BraidedTensorProduct R 𝒜 ℬ χ) where
  algebraMap :=
    { toFun r := tmul 𝒜 ℬ χ (algebraMap R A r) 1
      map_one' := by rw [map_one]; rfl
      map_mul' r s := by rw [map_mul, ← tmul_one_mul_tmul]
      map_zero' := by rw [map_zero, zero_tmul]
      map_add' r s := by rw [map_add, add_tmul] }
  commutes' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Algebra.algebraMap_eq_smul_one,
      smul_tmul, ← one_def, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  smul_def' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Algebra.algebraMap_eq_smul_one,
      smul_tmul, ← one_def, smul_mul_assoc, one_mul]

theorem algebraMap_def (r : R) :
    algebraMap R (BraidedTensorProduct R 𝒜 ℬ χ) r = tmul 𝒜 ℬ χ (algebraMap R A r) 1 := by rfl

/-- The canonical `R`-algebra inclusion `A →ₐ[R] BraidedTensorProduct R 𝒜 ℬ χ` sending `a` to
`a ⊗ₜ 1`. -/
noncomputable def includeLeft : A →ₐ[R] BraidedTensorProduct R 𝒜 ℬ χ :=
  AlgHom.ofLinearMap ((tmulBilinear 𝒜 ℬ χ).flip 1) (by simp [one_def]) fun a₁ a₂ ↦ by simp

@[simp] theorem includeLeft_apply (a : A) : includeLeft 𝒜 ℬ χ a = tmul 𝒜 ℬ χ a 1 := by
  simp [includeLeft]

/-- The canonical `R`-algebra inclusion `B →ₐ[R] BraidedTensorProduct R 𝒜 ℬ χ` sending `b` to
`1 ⊗ₜ b`. -/
noncomputable def includeRight : B →ₐ[R] BraidedTensorProduct R 𝒜 ℬ χ :=
  AlgHom.ofLinearMap (tmulBilinear 𝒜 ℬ χ 1) (tmulBilinear_apply 𝒜 ℬ χ 1 1) fun b₁ b₂ ↦ by
    rw [tmulBilinear_apply, tmulBilinear_apply, tmulBilinear_apply, tmul_mul_one_tmul]

@[simp] theorem includeRight_apply (b : B) : includeRight 𝒜 ℬ χ b = tmul 𝒜 ℬ χ 1 b := by
  rw [includeRight, AlgHom.ofLinearMap_apply, tmulBilinear_apply]

theorem algebraMap_def' (r : R) :
    algebraMap R (BraidedTensorProduct R 𝒜 ℬ χ) r = tmul 𝒜 ℬ χ 1 (algebraMap R B r) := by
  rw [← (includeRight 𝒜 ℬ χ).commutes r, includeRight_apply]

/-- Homogeneous elements in the images of `includeRight` and `includeLeft` braid according to
`χ`. -/
theorem includeRight_mul_includeLeft_of_mem {i : G₁} {j : G₂} {a : A} (ha : a ∈ 𝒜 i)
    {b : B} (hb : b ∈ ℬ j) :
    includeRight 𝒜 ℬ χ b * includeLeft 𝒜 ℬ χ a =
      χ j i • (includeLeft 𝒜 ℬ χ a * includeRight 𝒜 ℬ χ b) := by
  rw [includeRight_apply, includeLeft_apply, one_tmul_mul_tmul_one_of_mem 𝒜 ℬ χ ha hb,
    tmul_one_mul_one_tmul]

section Lift

variable {C : Type uC} [Semiring C] [Algebra R C]

private theorem lift_map_mul_aux (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : ∀ ⦃i : G₁⦄ ⦃j : G₂⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b))
    (x y : BraidedTensorProduct R 𝒜 ℬ χ) :
    let F : BraidedTensorProduct R 𝒜 ℬ χ →ₗ[R] C :=
      LinearMap.mul' R C ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ
        (ofLinearEquiv 𝒜 ℬ χ).symm.toLinearMap
    F (x * y) = F x * F y := by
  intro F
  have hF (a : A) (b : B) : F (tmul 𝒜 ℬ χ a b) = f a * g b := by simp [F]
  induction x using inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
  | tmul a₁ b₁ =>
    induction b₁ using DirectSum.Decomposition.inductionOn ℬ with
    | zero => simp
    | add u v hu hv => simp [tmul_add, add_mul, hu, hv]
    | @homogeneous j₁ b₁ =>
      induction y using inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simp [mul_add, hy₁, hy₂]
      | tmul a₂ b₂ =>
        induction a₂ using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp
        | add u v hu hv => simp [add_tmul, mul_add, hu, hv]
        | @homogeneous i₂ a₂ =>
          rw [tmul_mul_tmul_of_mem 𝒜 ℬ χ a₁ b₁.2 a₂.2 b₂, map_smul, hF, hF, hF,
            map_mul, map_mul]
          calc
            χ j₁ i₂ • (f a₁ * f a₂ * (g b₁ * g b₂)) =
                f a₁ * (χ j₁ i₂ • (f a₂ * g b₁)) * g b₂ := by
              simp only [mul_assoc, smul_mul_assoc, mul_smul_comm]
            _ = f a₁ * (g b₁ * f a₂) * g b₂ := by rw [← h a₂.2 b₁.2]
            _ = f a₁ * g b₁ * (f a₂ * g b₂) := by simp only [mul_assoc]

/-- Universal property of `BraidedTensorProduct R 𝒜 ℬ χ`: a pair of `R`-algebra homomorphisms
`f : A →ₐ[R] C` and `g : B →ₐ[R] C` satisfying `g b * f a = χ j i • (f a * g b)` for `a ∈ 𝒜 i` and
`b ∈ ℬ j` induces an `R`-algebra homomorphism `(a ⊗ₜ b) ↦ f a * g b`. -/
noncomputable def lift (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : ∀ ⦃i : G₁⦄ ⦃j : G₂⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b)) :
    BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] C :=
  AlgHom.ofLinearMap
    (LinearMap.mul' R C ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ
      (ofLinearEquiv 𝒜 ℬ χ).symm.toLinearMap)
    (by simp [Algebra.TensorProduct.one_def])
    (lift_map_mul_aux 𝒜 ℬ χ f g h)

@[simp] theorem lift_tmul (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : ∀ ⦃i : G₁⦄ ⦃j : G₂⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b))
    (a : A) (b : B) :
    lift 𝒜 ℬ χ f g h (tmul 𝒜 ℬ χ a b) = f a * g b := by
  rw [lift, AlgHom.ofLinearMap_apply]; simp

@[simp] theorem lift_comp_includeLeft (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : ∀ ⦃i : G₁⦄ ⦃j : G₂⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b)) :
    (lift 𝒜 ℬ χ f g h).comp (includeLeft 𝒜 ℬ χ) = f := by ext a; simp

@[simp] theorem lift_comp_includeRight (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : ∀ ⦃i : G₁⦄ ⦃j : G₂⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
      g b * f a = χ j i • (f a * g b)) :
    (lift 𝒜 ℬ χ f g h).comp (includeRight 𝒜 ℬ χ) = g := by ext b; simp

variable {𝒜 ℬ χ} in
/-- Two `R`-algebra homomorphisms out of `BraidedTensorProduct R 𝒜 ℬ χ` agree if their
compositions with `includeLeft` and `includeRight` agree. -/
@[ext] theorem algHom_ext ⦃F₁ F₂ : BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] C⦄
    (hL : F₁.comp (includeLeft 𝒜 ℬ χ) = F₂.comp (includeLeft 𝒜 ℬ χ))
    (hR : F₁.comp (includeRight 𝒜 ℬ χ) = F₂.comp (includeRight 𝒜 ℬ χ)) :
    F₁ = F₂ := by
  apply AlgHom.toLinearMap_injective
  refine linearMap_ext fun a b ↦ ?_
  simp only [AlgHom.toLinearMap_apply]
  rw [← tmul_one_mul_one_tmul 𝒜 ℬ χ a b, map_mul, map_mul]
  exact congrArg₂ (· * ·) (by simpa using AlgHom.congr_fun hL a)
    (by simpa using AlgHom.congr_fun hR b)

/-- Equivalence form of the universal property of `BraidedTensorProduct R 𝒜 ℬ χ`. -/
noncomputable def liftEquiv :
    { fg : (A →ₐ[R] C) × (B →ₐ[R] C) //
        ∀ ⦃i : G₁⦄ ⦃j : G₂⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
          fg.2 b * fg.1 a = χ j i • (fg.1 a * fg.2 b) } ≃
      (BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] C) where
  toFun fg := lift 𝒜 ℬ χ fg.1.1 fg.1.2 fg.2
  invFun F :=
    ⟨(F.comp (includeLeft 𝒜 ℬ χ), F.comp (includeRight 𝒜 ℬ χ)),
      fun _ _ _ ha _ hb ↦ by
        simp only [AlgHom.comp_apply, ← map_mul,
          includeRight_mul_includeLeft_of_mem 𝒜 ℬ χ ha hb, map_smul]⟩
  left_inv fg := by ext <;> simp
  right_inv F := by ext <;> simp

@[simp] theorem liftEquiv_apply
    (fg : { fg : (A →ₐ[R] C) × (B →ₐ[R] C) //
        ∀ ⦃i : G₁⦄ ⦃j : G₂⦄ {a : A}, a ∈ 𝒜 i → ∀ {b : B}, b ∈ ℬ j →
          fg.2 b * fg.1 a = χ j i • (fg.1 a * fg.2 b) }) :
    liftEquiv 𝒜 ℬ χ fg = lift 𝒜 ℬ χ fg.1.1 fg.1.2 fg.2 := by rfl

@[simp] theorem liftEquiv_symm_apply_fst (F : BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] C) :
    ((liftEquiv 𝒜 ℬ χ).symm F).1.1 = F.comp (includeLeft 𝒜 ℬ χ) := by rfl

@[simp] theorem liftEquiv_symm_apply_snd (F : BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] C) :
    ((liftEquiv 𝒜 ℬ χ).symm F).1.2 = F.comp (includeRight 𝒜 ℬ χ) := by rfl

end Lift

section Map

variable {𝒜 ℬ} {A' B' A'' B'' : Type*}
  [Semiring A'] [Semiring B'] [Algebra R A'] [Algebra R B']
  [Semiring A''] [Semiring B''] [Algebra R A''] [Algebra R B'']
  {𝒜' : G₁ → Submodule R A'} {ℬ' : G₂ → Submodule R B'} [GradedAlgebra 𝒜'] [GradedAlgebra ℬ']
  {𝒜'' : G₁ → Submodule R A''} {ℬ'' : G₂ → Submodule R B''} [GradedAlgebra 𝒜''] [GradedAlgebra ℬ'']

/-- Functoriality of `BraidedTensorProduct` for `GradedAlgHom`s. -/
noncomputable def map (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] BraidedTensorProduct R 𝒜' ℬ' χ :=
  lift 𝒜 ℬ χ ((includeLeft 𝒜' ℬ' χ).comp f.toAlgHom) ((includeRight 𝒜' ℬ' χ).comp g.toAlgHom)
    fun _ _ _ ha _ hb ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, GradedAlgHom.coe_toAlgHom,
        GradedAlgHom.coe_toAlgHom]
      exact includeRight_mul_includeLeft_of_mem 𝒜' ℬ' χ (Graded.map_mem f ha) (Graded.map_mem g hb)

@[simp] theorem map_tmul (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') (a : A) (b : B) :
    map χ f g (tmul 𝒜 ℬ χ a b) = tmul 𝒜' ℬ' χ (f a) (g b) := by simp [map]

@[simp] theorem map_comp_includeLeft (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    (map χ f g).comp (includeLeft 𝒜 ℬ χ) = (includeLeft 𝒜' ℬ' χ).comp f.toAlgHom :=
  lift_comp_includeLeft _ _ _ _ _ _

@[simp] theorem map_comp_includeRight (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    (map χ f g).comp (includeRight 𝒜 ℬ χ) = (includeRight 𝒜' ℬ' χ).comp g.toAlgHom :=
  lift_comp_includeRight _ _ _ _ _ _

/-- On underlying tensors, `BraidedTensorProduct.map` acts as `TensorProduct.map`. -/
@[simp] theorem toTensorProduct_map (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ')
    (x : BraidedTensorProduct R 𝒜 ℬ χ) :
    (map χ f g x).toTensorProduct =
      TensorProduct.map f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap x.toTensorProduct := by
  induction x using inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

@[simp] theorem map_id :
    map χ (.id R 𝒜) (.id R ℬ) = AlgHom.id R (BraidedTensorProduct R 𝒜 ℬ χ) := by ext <;> simp

theorem map_comp (f' : 𝒜' →ₐᵍ[R] 𝒜'') (g' : ℬ' →ₐᵍ[R] ℬ'')
    (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    map χ (f'.comp f) (g'.comp g) = (map χ f' g').comp (map χ f g) := by ext <;> simp

/-- If `f` and `g` are surjective `GradedAlgHom`s, then so is `BraidedTensorProduct.map χ f g`. -/
theorem map_surjective {f : 𝒜 →ₐᵍ[R] 𝒜'} {g : ℬ →ₐᵍ[R] ℬ'}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (map χ f g) := by
  intro y
  obtain ⟨z, hz⟩ := TensorProduct.map_surjective (g := f.toAlgHom.toLinearMap)
    (g' := g.toAlgHom.toLinearMap) hf hg y.toTensorProduct
  exact ⟨of 𝒜 ℬ χ z, ext (by rw [toTensorProduct_map, toTensorProduct_of, hz])⟩

end Map

/-- When the twisting bicharacter is trivial (`χ = 1`), `BraidedTensorProduct R 𝒜 ℬ 1` is
canonically isomorphic as an `R`-algebra to the ordinary tensor product `A ⊗[R] B`. -/
noncomputable def trivialAlgEquiv :
    BraidedTensorProduct R 𝒜 ℬ 1 ≃ₐ[R] A ⊗[R] B :=
  AlgEquiv.ofAlgHom
    (lift 𝒜 ℬ 1 Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
      fun _ _ a _ b _ ↦ by
        simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply])
    (Algebra.TensorProduct.lift (includeLeft 𝒜 ℬ 1) (includeRight 𝒜 ℬ 1) fun a b ↦ by
      rw [Commute, SemiconjBy, includeLeft_apply, includeRight_apply, tmul_one_mul_one_tmul]
      induction a using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add x y hx hy => simp [add_tmul, mul_add, hx, hy]
      | homogeneous x =>
        induction b using DirectSum.Decomposition.inductionOn ℬ with
        | zero => simp
        | add u v hu hv => simp [tmul_add, add_mul, hu, hv]
        | homogeneous y =>
          rw [one_tmul_mul_tmul_one_of_mem 𝒜 ℬ 1 x.2 y.2, one_apply, one_apply, one_smul])
    (by apply Algebra.TensorProduct.ext <;> (ext; simp))
    (by ext <;> simp)

@[simp] theorem trivialAlgEquiv_apply (x : BraidedTensorProduct R 𝒜 ℬ 1) :
    trivialAlgEquiv 𝒜 ℬ x = x.toTensorProduct := by
  induction x using inductionOn with
  | tmul a b => simp [trivialAlgEquiv]
  | add x y hx hy => simp [hx, hy]

@[simp] theorem trivialAlgEquiv_symm_apply (z : A ⊗[R] B) :
    (trivialAlgEquiv 𝒜 ℬ).symm z = of 𝒜 ℬ 1 z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [trivialAlgEquiv]
  | add x y hx hy => simp [hx, hy]

theorem trivialAlgEquiv_tmul (a : A) (b : B) :
    trivialAlgEquiv 𝒜 ℬ (tmul 𝒜 ℬ 1 a b) = a ⊗ₜ[R] b := by simp

theorem trivialAlgEquiv_symm_tmul (a : A) (b : B) :
    (trivialAlgEquiv 𝒜 ℬ).symm (a ⊗ₜ[R] b) = tmul 𝒜 ℬ 1 a b := by simp

@[simp] theorem trivialAlgEquiv_toLinearEquiv :
    (trivialAlgEquiv 𝒜 ℬ).toLinearEquiv = (ofLinearEquiv 𝒜 ℬ 1).symm := by ext x; simp

theorem trivialAlgEquiv_symm_toLinearEquiv :
    (trivialAlgEquiv 𝒜 ℬ).symm.toLinearEquiv = ofLinearEquiv 𝒜 ℬ 1 := by simp

@[simp] theorem trivialAlgEquiv_comp_includeLeft :
    (trivialAlgEquiv 𝒜 ℬ : BraidedTensorProduct R 𝒜 ℬ 1 →ₐ[R] A ⊗[R] B).comp
        (includeLeft 𝒜 ℬ 1) = Algebra.TensorProduct.includeLeft := by ext a; simp

@[simp] theorem trivialAlgEquiv_comp_includeRight :
    (trivialAlgEquiv 𝒜 ℬ : BraidedTensorProduct R 𝒜 ℬ 1 →ₐ[R] A ⊗[R] B).comp
        (includeRight 𝒜 ℬ 1) = Algebra.TensorProduct.includeRight := by ext b; simp

@[simp] theorem trivialAlgEquiv_symm_comp_includeLeft :
    ((trivialAlgEquiv 𝒜 ℬ).symm : A ⊗[R] B →ₐ[R] BraidedTensorProduct R 𝒜 ℬ 1).comp
        Algebra.TensorProduct.includeLeft = includeLeft 𝒜 ℬ 1 := by ext a; simp

@[simp] theorem trivialAlgEquiv_symm_comp_includeRight :
    ((trivialAlgEquiv 𝒜 ℬ).symm : A ⊗[R] B →ₐ[R] BraidedTensorProduct R 𝒜 ℬ 1).comp
        Algebra.TensorProduct.includeRight = includeRight 𝒜 ℬ 1 := by ext b; simp

section Comm

variable {χ : AddChar G₂ (AddChar G₁ R)} {ψ : AddChar G₁ (AddChar G₂ R)}

/-- For bicharacters `χ : AddChar G₂ (AddChar G₁ R)` and `ψ : AddChar G₁ (AddChar G₂ R)`
satisfying `∀ i j, χ j i * ψ i j = 1`, swapping factors with the `ψ`-braiding defines an
`R`-algebra homomorphism `BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] BraidedTensorProduct R ℬ 𝒜 ψ`. -/
noncomputable def comm (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] BraidedTensorProduct R ℬ 𝒜 ψ :=
  lift 𝒜 ℬ χ (includeRight ℬ 𝒜 ψ) (includeLeft ℬ 𝒜 ψ) fun i j a ha b hb ↦ by
    rw [includeLeft_apply, includeRight_apply, tmul_one_mul_one_tmul,
      one_tmul_mul_tmul_one_of_mem ℬ 𝒜 ψ hb ha, smul_smul, hχψ i j, one_smul]

@[simp] theorem comm_tmul_one (hχψ : ∀ i j, χ j i * ψ i j = 1) (a : A) :
    comm 𝒜 ℬ hχψ (tmul 𝒜 ℬ χ a 1) = tmul ℬ 𝒜 ψ 1 a := by simp [comm]

@[simp] theorem comm_one_tmul (hχψ : ∀ i j, χ j i * ψ i j = 1) (b : B) :
    comm 𝒜 ℬ hχψ (tmul 𝒜 ℬ χ 1 b) = tmul ℬ 𝒜 ψ b 1 := by simp [comm]

@[simp] theorem comm_comp_includeLeft (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    (comm 𝒜 ℬ hχψ).comp (includeLeft 𝒜 ℬ χ) = includeRight ℬ 𝒜 ψ :=
  lift_comp_includeLeft _ _ _ _ _ _

@[simp] theorem comm_comp_includeRight (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    (comm 𝒜 ℬ hχψ).comp (includeRight 𝒜 ℬ χ) = includeLeft ℬ 𝒜 ψ :=
  lift_comp_includeRight _ _ _ _ _ _

theorem comm_tmul_of_mem (hχψ : ∀ i j, χ j i * ψ i j = 1) {i : G₁} {j : G₂}
    {a : A} (ha : a ∈ 𝒜 i) {b : B} (hb : b ∈ ℬ j) :
    comm 𝒜 ℬ hχψ (tmul 𝒜 ℬ χ a b) = ψ i j • tmul ℬ 𝒜 ψ b a := by
  rw [comm, lift_tmul, includeRight_apply, includeLeft_apply,
    one_tmul_mul_tmul_one_of_mem ℬ 𝒜 ψ hb ha]

@[simp] theorem comm_comp_comm (hχψ : ∀ i j, χ j i * ψ i j = 1)
    (hψχ : ∀ j i, ψ i j * χ j i = 1 := fun j i ↦ mul_comm (ψ i j) (χ j i) ▸ hχψ i j) :
    (comm ℬ 𝒜 hψχ).comp (comm 𝒜 ℬ hχψ) = AlgHom.id R (BraidedTensorProduct R 𝒜 ℬ χ) := by
  ext <;> simp

/-- Paired bicharacters `χ` and `ψ` satisfying `∀ i j, χ j i * ψ i j = 1` induce a braided
factor-swap `R`-algebra equivalence
`BraidedTensorProduct R 𝒜 ℬ χ ≃ₐ[R] BraidedTensorProduct R ℬ 𝒜 ψ`. -/
noncomputable def commAlgEquiv (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    BraidedTensorProduct R 𝒜 ℬ χ ≃ₐ[R] BraidedTensorProduct R ℬ 𝒜 ψ :=
  have hψχ : ∀ j i, ψ i j * χ j i = 1 := fun j i ↦ mul_comm (ψ i j) (χ j i) ▸ hχψ i j
  AlgEquiv.ofAlgHom (comm 𝒜 ℬ hχψ) (comm ℬ 𝒜 hψχ)
    (comm_comp_comm ℬ 𝒜 hψχ hχψ) (comm_comp_comm 𝒜 ℬ hχψ hψχ)

@[simp] theorem commAlgEquiv_toAlgHom (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    (commAlgEquiv 𝒜 ℬ hχψ :
        BraidedTensorProduct R 𝒜 ℬ χ →ₐ[R] BraidedTensorProduct R ℬ 𝒜 ψ) = comm 𝒜 ℬ hχψ := by rfl

@[simp] theorem commAlgEquiv_symm_toAlgHom (hχψ : ∀ i j, χ j i * ψ i j = 1) :
    ((commAlgEquiv 𝒜 ℬ hχψ).symm :
        BraidedTensorProduct R ℬ 𝒜 ψ →ₐ[R] BraidedTensorProduct R 𝒜 ℬ χ) =
      comm ℬ 𝒜 (fun j i ↦ mul_comm (ψ i j) (χ j i) ▸ hχψ i j) := by rfl

@[simp] theorem commAlgEquiv_apply (hχψ : ∀ i j, χ j i * ψ i j = 1)
    (x : BraidedTensorProduct R 𝒜 ℬ χ) :
    commAlgEquiv 𝒜 ℬ hχψ x = comm 𝒜 ℬ hχψ x := by rfl

@[simp] theorem commAlgEquiv_symm_apply (hχψ : ∀ i j, χ j i * ψ i j = 1)
    (y : BraidedTensorProduct R ℬ 𝒜 ψ) :
    (commAlgEquiv 𝒜 ℬ hχψ).symm y =
      comm ℬ 𝒜 (fun j i ↦ mul_comm (ψ i j) (χ j i) ▸ hχψ i j) y := by rfl

end Comm

end Algebra

section Ring

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂} {A : Type uA} {B : Type uB}
  [CommSemiring R] [AddMonoid G₁] [AddMonoid G₂] [DecidableEq G₁] [DecidableEq G₂]
  [Ring A] [Semiring B] [Algebra R A] [Algebra R B]
  (𝒜 : G₁ → Submodule R A) (ℬ : G₂ → Submodule R B)
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (χ : AddChar G₂ (AddChar G₁ R))

noncomputable instance instRing : Ring (BraidedTensorProduct R 𝒜 ℬ χ) :=
  { instSemiring 𝒜 ℬ χ, instAddCommGroup 𝒜 ℬ χ with }

end Ring

section KerMap

variable {R : Type uR} {G₁ : Type uG₁} {G₂ : Type uG₂}
  {A : Type uA} {B : Type uB} {A' B' : Type*}
  [CommRing R] [AddMonoid G₁] [AddMonoid G₂] [DecidableEq G₁] [DecidableEq G₂]
  [Ring A] [Ring B] [Ring A'] [Ring B']
  [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
  {𝒜 : G₁ → Submodule R A} {ℬ : G₂ → Submodule R B}
  {𝒜' : G₁ → Submodule R A'} {ℬ' : G₂ → Submodule R B'}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒜'] [GradedAlgebra ℬ']
  (χ : AddChar G₂ (AddChar G₁ R))

/-- Over a commutative ring, the kernel of `BraidedTensorProduct.map χ f g` for surjective
`GradedAlgHom`s `f` and `g` is `ker f ⊗ B + A ⊗ ker g`. -/
theorem restrictScalars_ker_map {f : 𝒜 →ₐᵍ[R] 𝒜'} {g : ℬ →ₐᵍ[R] ℬ'}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (RingHom.ker (map χ f g)).restrictScalars R =
      Submodule.map₂ (tmulBilinear 𝒜 ℬ χ) (LinearMap.ker f.toAlgHom.toLinearMap) ⊤ ⊔
        Submodule.map₂ (tmulBilinear 𝒜 ℬ χ) ⊤ (LinearMap.ker g.toAlgHom.toLinearMap) := by
  have hker : (RingHom.ker (map χ f g)).restrictScalars R =
      (LinearMap.ker (TensorProduct.map f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap)).map
        (ofLinearEquiv 𝒜 ℬ χ).toLinearMap := by
    ext x
    simp only [RingHom.mem_ker, Submodule.restrictScalars_mem, Submodule.mem_map,
      LinearMap.mem_ker, LinearEquiv.coe_coe, ofLinearEquiv_apply]
    refine ⟨fun hx ↦ ⟨x.toTensorProduct, ?_, of_toTensorProduct x⟩, ?_⟩
    · simpa using congrArg toTensorProduct hx
    · rintro ⟨z, hz, rfl⟩
      exact ext (by simpa using hz)
  rw [hker, TensorProduct.map_ker f.toAlgHom.toLinearMap.exact_subtype_ker_map hf
    g.toAlgHom.toLinearMap.exact_subtype_ker_map hg, Submodule.map_sup, sup_comm]
  simp only [LinearMap.rTensor_def, LinearMap.lTensor_def, TensorProduct.range_map,
    LinearMap.range_id, Submodule.range_subtype, Submodule.map_map₂, ← tmulBilinear_def]

end KerMap

end BraidedTensorProduct

end TauCeti
