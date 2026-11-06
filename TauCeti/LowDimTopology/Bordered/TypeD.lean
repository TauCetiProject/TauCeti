/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import TauCeti.Algebra.CharP.Two
public import TauCeti.Algebra.Homology.DG.Ungraded
import Mathlib.Tactic.Abel

/-!
# Type `D` structures and the box tensor product

Bordered Heegaard Floer homology attaches to a three-manifold with parametrized boundary a type `D`
structure over a differential algebra `A`, and recovers the Floer complex of a closed manifold as a
box tensor product `M ⊠ N` of a module `M` with a type `D` structure `N`. This file sets up type
`D` structures, their morphisms, and the box tensor product with differential right modules, over
an ungraded differential algebra (`TauCeti.IsUngradedDGAlgebra`) over a ring of characteristic
two.

The ground ring of the algebra is a ring of idempotents: `A` comes with a family `ι : S → A`,
for the strands algebras the idempotents `I(s)` of the occupied sets `s`. A type `D` structure is
a module `N` over this ring of idempotents with a map `δ¹ : N → A ⊗ N`. We describe it in a
basis of generators `x : X`, each lying in the summand of one idempotent `ι (idem x)`:
`δ¹ x = ∑ y, coeff x y ⊗ y` with `coeff x y ∈ ι (idem x) * A * ι (idem y)`. The structure equation
`(μ₂ ⊗ 1) ∘ (1 ⊗ δ¹) ∘ δ¹ + (μ₁ ⊗ 1) ∘ δ¹ = 0` then says that the coefficient matrix `δ` is a
Maurer–Cartan element, `d δ + δ * δ = 0` (`TauCeti.TypeDStructure`), the differential `d` acting
on matrices entrywise.

* **Morphisms.** A morphism from `N` to `N'` is a matrix `F` of coefficients compatible with the
  idempotents (`TauCeti.TypeDStructure.morphisms`), with differential
  `∂F = d F + F * δ' + δ * F` (`TauCeti.TypeDStructure.morphismDifferential`). It squares to zero,
  is a derivation for the matrix product, which composes morphisms, and the diagonal matrix of
  idempotents `TauCeti.TypeDStructure.idMorphism` is a two-sided unit and a cycle. The cycles are
  the homomorphisms of type `D` structures and the boundaries their null-homotopic maps.
* **The box tensor product.** For a differential right `A`-module `(M, dM)`, the box tensor
  product `M ⊠ N = M ⊗ N` over the idempotents has the differential
  `∂ (m ⊗ x) = dM m ⊗ x + ∑ y, m * coeff x y ⊗ y`. In the basis, `M ⊗ N` is the submodule of
  row vectors `φ : X → M` with `φ x * ι (idem x) = φ x` (`TauCeti.TypeDStructure.boxTensor`) and the
  differential is `∂ φ = dM φ + φ ⬝ δ` (`TauCeti.TypeDStructure.boxDifferential`), where
  `φ ⬝ F = TauCeti.continuationMap R M F φ` is the action of a matrix on row vectors. It squares to
  zero, and preserves `M ⊗ N` when the idempotents are cycles. Taking `M = A` gives the
  differential left module `A ⊠ N` induced by `N`.
* **Functoriality.** A morphism `F` acts on box tensor products by `φ ↦ φ ⬝ F`, and
  `∂ (φ ⬝ F) + (∂ φ) ⬝ F = φ ⬝ ∂F` (`TauCeti.TypeDStructure.boxDifferential_continuationMap`). So
  homomorphisms induce chain maps, a morphism `H` with `∂H = F + G` induces a chain homotopy
  between the maps of `F` and `G`, composition is preserved
  (`TauCeti.continuationMap_matMul`), and the identity morphism acts as the identity on `M ⊗ N`.

Over a ring of characteristic two the type `D` structure equation, the box tensor product and the
morphism complex need no signs; this is the setting of bordered Heegaard Floer homology over `𝔽₂`.
The `ℤ`-graded analogue of the box tensor product with a differential module is the twisted complex
`TauCeti.twistedDifferential`, which needs a `ℤ`-grading compatible with a differential of degree
one and so does not apply to an ungraded differential algebra.

## Main definitions

* `TauCeti.TypeDStructure`: a type `D` structure, given by its generators, their idempotents and
  its coefficient matrix.
* `TauCeti.TypeDStructure.morphisms`, `TauCeti.TypeDStructure.morphismDifferential`,
  `TauCeti.TypeDStructure.idMorphism`: morphisms of type `D` structures, their differential and the
  identity morphism.
* `TauCeti.TypeDStructure.boxTensor`, `TauCeti.TypeDStructure.boxDifferential`: the box tensor
  product with a right module and its differential, and
  `TauCeti.TypeDStructure.boxTensorDifferential`: the differential restricted to `M ⊗ N`.

## Main results

* `TauCeti.TypeDStructure.boxDifferential_boxDifferential`: `∂ ∘ ∂ = 0` on `M ⊠ N`.
* `TauCeti.TypeDStructure.boxDifferential_mem_boxTensor`: `∂` preserves `M ⊗ N`.
* `TauCeti.TypeDStructure.boxDifferential_smul`: `A ⊠ N` is a differential left module.
* `TauCeti.TypeDStructure.morphismDifferential_morphismDifferential`,
  `TauCeti.TypeDStructure.morphismDifferential_mul`: the morphisms form a differential category.
* `TauCeti.TypeDStructure.boxDifferential_continuationMap`: morphisms act on box tensor products
  compatibly with the differentials.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (type `D` structures, their morphisms, and the box tensor product, equation (2.29)).
-/

public section

open MulOpposite

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (d : A →ₗ[R] A) {S : Type*}
  (ι : S → A) (X : Type*) [Fintype X]

/-- A **type `D` structure** over the differential algebra `(A, d)` with idempotents `ι`, in a
basis of generators `X`. Each generator `x` lies in the summand of the idempotent `ι (idem x)`, and
`δ¹ x = ∑ y, coeff x y ⊗ y`, so `coeff x y` lies in `ι (idem x) * A * ι (idem y)`. The structure
equation `(μ₂ ⊗ 1) ∘ (1 ⊗ δ¹) ∘ δ¹ + (μ₁ ⊗ 1) ∘ δ¹ = 0` says that the coefficient matrix satisfies
`d coeff + coeff * coeff = 0`, the differential acting entrywise. -/
@[ext]
structure TypeDStructure where
  /-- The idempotent of each generator. -/
  idem : X → S
  /-- The coefficient matrix: `δ¹ x = ∑ y, coeff x y ⊗ y`. -/
  coeff : Matrix X X A
  /-- The coefficients from `x` lie in the summand of the idempotent of `x` on the left. -/
  idem_mul_coeff (x y : X) : ι (idem x) * coeff x y = coeff x y
  /-- The coefficients to `y` lie in the summand of the idempotent of `y` on the right. -/
  coeff_mul_idem (x y : X) : coeff x y * ι (idem y) = coeff x y
  /-- The structure equation `d δ + δ * δ = 0`. -/
  map_coeff_add_coeff_mul_coeff : coeff.map d + coeff * coeff = 0

namespace TypeDStructure

variable {d ι X} {X' X'' : Type*} [Fintype X'] [Fintype X'']

/-! ### Morphisms -/

/-- The **morphisms** from `N` to `N'`: matrices `F` of coefficients with `F x x'` in
`ι (idem x) * A * ι (idem x')`, describing maps `N → A ⊗ N'` over the idempotents by
`x ↦ ∑ x', F x x' ⊗ x'`. -/
def morphisms (N : TypeDStructure d ι X) (N' : TypeDStructure d ι X') :
    Submodule R (Matrix X X' A) where
  carrier := {F | ∀ x x', ι (N.idem x) * F x x' = F x x' ∧ F x x' * ι (N'.idem x') = F x x'}
  add_mem' {F G} hF hG x x' := by
    simp [mul_add, add_mul, (hF x x').1, (hF x x').2, (hG x x').1, (hG x x').2]
  zero_mem' := by simp
  smul_mem' r F hF x x' := by
    simp [(hF x x').1, (hF x x').2]

variable {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'}
  {N'' : TypeDStructure d ι X''}

@[simp]
theorem mem_morphisms_iff {F : Matrix X X' A} :
    F ∈ morphisms N N' ↔
      ∀ x x', ι (N.idem x) * F x x' = F x x' ∧ F x x' * ι (N'.idem x') = F x x' :=
  Iff.rfl

variable (N) in
/-- The coefficient matrix of a type `D` structure is a morphism from it to itself. -/
theorem coeff_mem_morphisms : N.coeff ∈ morphisms N N :=
  fun x y => ⟨N.idem_mul_coeff x y, N.coeff_mul_idem x y⟩

variable (N) in
/-- The **identity morphism**: the diagonal matrix of the idempotents of the generators. -/
def idMorphism [DecidableEq X] : Matrix X X A :=
  Matrix.diagonal fun x => ι (N.idem x)

@[simp]
theorem idMorphism_apply [DecidableEq X] (x y : X) :
    N.idMorphism x y = if x = y then ι (N.idem x) else 0 := by
  simp only [idMorphism, Matrix.diagonal_apply]

/-- A matrix is a morphism exactly when the identity morphisms of its source and target are
units for it on the left and on the right. -/
theorem mem_morphisms_iff_mul [DecidableEq X] [DecidableEq X'] {F : Matrix X X' A} :
    F ∈ morphisms N N' ↔ N.idMorphism * F = F ∧ F * N'.idMorphism = F := by
  constructor
  · intro hF
    constructor <;> ext x x' <;>
      simp [idMorphism, Matrix.diagonal_mul, Matrix.mul_diagonal, (hF x x').1, (hF x x').2]
  · rintro ⟨h₁, h₂⟩ x x'
    exact ⟨by simpa [idMorphism, Matrix.diagonal_mul] using congrFun (congrFun h₁ x) x',
      by simpa [idMorphism, Matrix.mul_diagonal] using congrFun (congrFun h₂ x) x'⟩

/-- The identity morphism is a left unit for morphisms. -/
theorem idMorphism_mul [DecidableEq X] {F : Matrix X X' A} (hF : F ∈ morphisms N N') :
    N.idMorphism * F = F := by
  classical
  exact (mem_morphisms_iff_mul.mp hF).1

/-- The identity morphism is a right unit for morphisms. -/
theorem mul_idMorphism [DecidableEq X'] {F : Matrix X X' A} (hF : F ∈ morphisms N N') :
    F * N'.idMorphism = F := by
  classical
  exact (mem_morphisms_iff_mul.mp hF).2

variable (N) in
/-- When the `ι s` are idempotents, the identity morphism is a morphism. -/
theorem idMorphism_mem_morphisms [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s)) :
    N.idMorphism ∈ morphisms N N := by
  have h : N.idMorphism * N.idMorphism = N.idMorphism := by
    simp [idMorphism, Matrix.diagonal_mul_diagonal, (hι _).eq]
  exact mem_morphisms_iff_mul.mpr ⟨h, h⟩

/-- Morphisms compose by matrix multiplication. -/
theorem mul_mem_morphisms {F : Matrix X X' A} {G : Matrix X' X'' A} (hF : F ∈ morphisms N N')
    (hG : G ∈ morphisms N' N'') : F * G ∈ morphisms N N'' := by
  classical
  refine mem_morphisms_iff_mul.mpr ⟨?_, ?_⟩
  · rw [← Matrix.mul_assoc, idMorphism_mul hF]
  · rw [Matrix.mul_assoc, mul_idMorphism hG]

variable (N N') in
/-- The **differential of morphisms** `∂F = d F + F * δ' + δ * F`, where `δ` and `δ'` are the
coefficient matrices of the source and the target. Its cycles are the homomorphisms of type `D`
structures. -/
def morphismDifferential : Matrix X X' A →ₗ[R] Matrix X X' A where
  toFun F := F.map d + F * N'.coeff + N.coeff * F
  map_add' F G := by
    ext x y
    simp only [Matrix.add_apply, Matrix.map_apply, map_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' r F := by
    ext x y
    simp [Matrix.smul_mul, Matrix.mul_smul]

theorem morphismDifferential_apply (F : Matrix X X' A) :
    morphismDifferential N N' F = F.map d + F * N'.coeff + N.coeff * F :=
  (rfl)

variable (N) in
/-- In characteristic two the structure equation reads `d δ = δ * δ`. -/
theorem map_coeff_eq_coeff_mul_coeff [CharP R 2] :
    N.coeff.map d = N.coeff * N.coeff :=
  (add_eq_zero_iff_eq_of_charTwo R).mp N.map_coeff_add_coeff_mul_coeff

/-- **The morphism differential squares to zero.** -/
@[simp]
theorem morphismDifferential_morphismDifferential [CharP R 2] (hd : IsUngradedDGAlgebra d)
    (F : Matrix X X' A) : morphismDifferential N N' (morphismDifferential N N' F) = 0 := by
  have h2 := add_self_eq_zero_of_charTwo (M := Matrix X X' A) R
  simp only [morphismDifferential_apply, Matrix.map_add _ (map_add d), hd.map_mul_matrix,
    hd.map_map_matrix, map_coeff_eq_coeff_mul_coeff, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  calc _ = (F.map d * N'.coeff + F.map d * N'.coeff) + (N.coeff * F.map d + N.coeff * F.map d) +
        (N.coeff * (F * N'.coeff) + N.coeff * (F * N'.coeff)) +
        (F * (N'.coeff * N'.coeff) + F * (N'.coeff * N'.coeff)) +
        (N.coeff * (N.coeff * F) + N.coeff * (N.coeff * F)) := by abel
    _ = 0 := by simp only [h2]

/-- **The Leibniz rule for composition of morphisms**: `∂(F * G) = ∂F * G + F * ∂G`. -/
theorem morphismDifferential_mul [CharP R 2] (hd : IsUngradedDGAlgebra d) (F : Matrix X X' A)
    (G : Matrix X' X'' A) :
    morphismDifferential N N'' (F * G) =
      morphismDifferential N N' F * G + F * morphismDifferential N' N'' G := by
  have h2 := add_self_eq_zero_of_charTwo (M := Matrix X X'' A) R
  simp only [morphismDifferential_apply, hd.map_mul_matrix, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  calc _ = F.map d * G + F * G.map d + F * (G * N''.coeff) + N.coeff * (F * G) +
        (F * (N'.coeff * G) + F * (N'.coeff * G)) := by rw [h2, add_zero]
    _ = _ := by abel

variable (N) in
/-- When the `ι s` are cycles, the entrywise differential of the identity morphism vanishes. -/
@[simp]
theorem map_idMorphism [DecidableEq X] (hι : ∀ s, d (ι s) = 0) : N.idMorphism.map d = 0 := by
  simp [idMorphism, Matrix.diagonal_map, hι]

variable (N) in
/-- When the `ι s` are cycles, the identity morphism is a cycle: it is a homomorphism. -/
@[simp]
theorem morphismDifferential_idMorphism [CharP R 2] [DecidableEq X] (hι : ∀ s, d (ι s) = 0) :
    morphismDifferential N N N.idMorphism = 0 := by
  simp [morphismDifferential_apply, map_idMorphism N hι, idMorphism_mul (coeff_mem_morphisms N),
    mul_idMorphism (coeff_mem_morphisms N), add_self_eq_zero_of_charTwo R]

/-- When the `ι s` are cycles, the entrywise differential of a morphism is a morphism. -/
theorem map_mem_morphisms (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    {F : Matrix X X' A} (hF : F ∈ morphisms N N') : F.map d ∈ morphisms N N' := by
  classical
  refine mem_morphisms_iff_mul.mpr ⟨?_, ?_⟩
  · have h := hd.map_mul_matrix N.idMorphism F
    rwa [idMorphism_mul hF, map_idMorphism N hι, Matrix.zero_mul, zero_add, eq_comm] at h
  · have h := hd.map_mul_matrix F N'.idMorphism
    rwa [mul_idMorphism hF, map_idMorphism N' hι, Matrix.mul_zero, add_zero, eq_comm] at h

/-- When the `ι s` are cycles, the differential of a morphism is a morphism. -/
theorem morphismDifferential_mem_morphisms (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    {F : Matrix X X' A} (hF : F ∈ morphisms N N') :
    morphismDifferential N N' F ∈ morphisms N N' :=
  add_mem (add_mem (map_mem_morphisms hd hι hF) (mul_mem_morphisms hF (coeff_mem_morphisms N')))
    (mul_mem_morphisms (coeff_mem_morphisms N) hF)

/-! ### The box tensor product -/

section BoxTensor

variable {M : Type*} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

variable (N M) in
/-- The **box tensor product** `M ⊗ N` over the idempotents of a right `A`-module `M` with a type
`D` structure `N`, as the submodule of row vectors `φ : X → M`, standing for `∑ x, φ x ⊗ x`, with
`φ x * ι (idem x) = φ x`. -/
def boxTensor : Submodule R (X → M) where
  carrier := {φ | ∀ x, op (ι (N.idem x)) • φ x = φ x}
  add_mem' {φ ψ} hφ hψ x := by simp [hφ x, hψ x]
  zero_mem' := by simp
  smul_mem' r φ hφ x := by
    simp only [Pi.smul_apply]
    rw [← smul_comm r, hφ x]

@[simp]
theorem mem_boxTensor_iff {φ : X → M} :
    φ ∈ N.boxTensor M ↔ ∀ x, op (ι (N.idem x)) • φ x = φ x :=
  Iff.rfl

/-- `M ⊗ N` is the submodule of row vectors fixed by the identity morphism. -/
theorem mem_boxTensor_iff_continuationMap_idMorphism [DecidableEq X] {φ : X → M} :
    φ ∈ N.boxTensor M ↔ continuationMap R M N.idMorphism φ = φ := by
  simp only [mem_boxTensor_iff, funext_iff, continuationMap_apply (R := R) (M := M) N.idMorphism,
    idMorphism_apply, apply_ite op, op_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The identity morphism acts as the identity on `M ⊗ N`. -/
@[simp]
theorem continuationMap_idMorphism [DecidableEq X] {φ : X → M} (hφ : φ ∈ N.boxTensor M) :
    continuationMap R M N.idMorphism φ = φ :=
  mem_boxTensor_iff_continuationMap_idMorphism.mp hφ

/-- A morphism `F` from `N` to `N'` sends row vectors into `M ⊗ N'`. -/
theorem continuationMap_mem_boxTensor {F : Matrix X X' A} (hF : F ∈ morphisms N N')
    (φ : X → M) : continuationMap R M F φ ∈ N'.boxTensor M := by
  intro z
  simp only [continuationMap_apply (R := R) (M := M) F, Finset.smul_sum, ← mul_smul, ← op_mul,
    ((hF _ z).2)]

variable (N) in
/-- The **differential of the box tensor product** `M ⊠ N`, on row vectors `φ : X → M`:
`∂ φ = dM φ + φ ⬝ δ`, that is `∂ (m ⊗ x) = dM m ⊗ x + ∑ y, m * coeff x y ⊗ y`. -/
noncomputable def boxDifferential (dM : M →ₗ[R] M) : (X → M) →ₗ[R] (X → M) :=
  dM.compLeft X + continuationMap R M N.coeff

theorem boxDifferential_apply (dM : M →ₗ[R] M) (φ : X → M) :
    N.boxDifferential dM φ = (fun x => dM (φ x)) + continuationMap R M N.coeff φ :=
  (rfl)

/-- **The box tensor differential squares to zero.** This uses only the structure equation of `N`
and the axioms of the differential module `M`. -/
@[simp]
theorem boxDifferential_boxDifferential [CharP R 2] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (φ : X → M) :
    N.boxDifferential dM (N.boxDifferential dM φ) = 0 := by
  have h := congrArg (fun F => continuationMap R M F φ) N.map_coeff_add_coeff_mul_coeff
  simp only [continuationMap_add, continuationMap_matMul, continuationMap_zero,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h
  ext z
  have hz := congrFun h z
  simp only [Pi.add_apply, Pi.zero_apply] at hz
  simp only [boxDifferential_apply, map_add, Pi.add_apply, hM.map_map, hM.map_continuationMap,
    Pi.zero_apply]
  calc _ = (continuationMap R M N.coeff (fun x => dM (φ x)) z +
        continuationMap R M N.coeff (fun x => dM (φ x)) z) +
        (continuationMap R M (N.coeff.map d) φ z +
          continuationMap R M N.coeff (continuationMap R M N.coeff φ) z) := by
        abel
    _ = 0 := by rw [add_self_eq_zero_of_charTwo R, hz, add_zero]

/-- When the `ι s` are cycles, the box tensor differential preserves `M ⊗ N`. -/
theorem boxDifferential_mem_boxTensor (hι : ∀ s, d (ι s) = 0) {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) {φ : X → M} (hφ : φ ∈ N.boxTensor M) :
    N.boxDifferential dM φ ∈ N.boxTensor M := by
  rw [boxDifferential_apply]
  refine add_mem (fun x => ?_) (continuationMap_mem_boxTensor (coeff_mem_morphisms N) φ)
  have h := hM.map_smul (ι (N.idem x)) (φ x)
  rwa [hφ x, hι, op_zero, zero_smul, add_zero, eq_comm] at h

variable (N) in
/-- The box tensor differential restricted to `M ⊗ N`, when the `ι s` are cycles. -/
noncomputable def boxTensorDifferential (hι : ∀ s, d (ι s) = 0) {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) : N.boxTensor M →ₗ[R] N.boxTensor M :=
  (N.boxDifferential dM).restrict fun _ hφ => N.boxDifferential_mem_boxTensor hι hM hφ

@[simp]
theorem coe_boxTensorDifferential_apply (hι : ∀ s, d (ι s) = 0) {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (φ : N.boxTensor M) :
    (N.boxTensorDifferential hι hM φ : X → M) = N.boxDifferential dM φ :=
  (rfl)

/-- The differential of `M ⊠ N` squares to zero on `M ⊗ N`. -/
@[simp]
theorem boxTensorDifferential_boxTensorDifferential [CharP R 2] (hι : ∀ s, d (ι s) = 0)
    {dM : M →ₗ[R] M} (hM : IsUngradedDGRightModule d dM) (φ : N.boxTensor M) :
    N.boxTensorDifferential hι hM (N.boxTensorDifferential hι hM φ) = 0 := by
  ext1
  simp [hM]

/-- **Morphisms act on box tensor products compatibly with the differentials:**
`∂ (φ ⬝ F) + (∂ φ) ⬝ F = φ ⬝ ∂F`. So a homomorphism `F` (`∂F = 0`) induces a chain map
`φ ↦ φ ⬝ F` from `M ⊠ N` to `M ⊠ N'`, and a morphism `H` with `∂H = F + G` induces a chain
homotopy between the maps of `F` and `G`. -/
theorem boxDifferential_continuationMap [CharP R 2] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (F : Matrix X X' A) (φ : X → M) :
    N'.boxDifferential dM (continuationMap R M F φ) +
        continuationMap R M F (N.boxDifferential dM φ) =
      continuationMap R M (morphismDifferential N N' F) φ := by
  ext z
  simp only [boxDifferential_apply, morphismDifferential_apply, continuationMap_add,
    continuationMap_matMul, map_add, LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply,
    hM.map_continuationMap]
  calc _ = (continuationMap R M F (fun x => dM (φ x)) z +
        continuationMap R M F (fun x => dM (φ x)) z) +
        (continuationMap R M (F.map d) φ z +
          continuationMap R M N'.coeff (continuationMap R M F φ) z +
          continuationMap R M F (continuationMap R M N.coeff φ) z) := by abel
    _ = _ := by rw [add_self_eq_zero_of_charTwo R, zero_add]

/-- A homomorphism of type `D` structures induces a chain map of box tensor products. -/
theorem boxDifferential_continuationMap_of_morphismDifferential_eq_zero [CharP R 2]
    {dM : M →ₗ[R] M} (hM : IsUngradedDGRightModule d dM) {F : Matrix X X' A}
    (hF : morphismDifferential N N' F = 0) (φ : X → M) :
    N'.boxDifferential dM (continuationMap R M F φ) =
      continuationMap R M F (N.boxDifferential dM φ) := by
  have h := boxDifferential_continuationMap (N := N) (N' := N') hM F φ
  rw [hF, continuationMap_zero, LinearMap.zero_apply] at h
  exact (add_eq_zero_iff_eq_of_charTwo R).mp h

end BoxTensor

/-- **The induced differential module.** On the box tensor product `A ⊠ N` of the algebra with
`N`, the differential satisfies the Leibniz rule for the left action of `A`,
`∂ (b • φ) = d b • φ + b • ∂ φ`; with `boxDifferential_boxDifferential` for the regular module,
this makes `A ⊠ N` a differential left `A`-module. -/
theorem boxDifferential_smul (hd : IsUngradedDGAlgebra d) (N : TypeDStructure d ι X) (b : A)
    (φ : X → A) : N.boxDifferential d (b • φ) = d b • φ + b • N.boxDifferential d φ := by
  ext z
  simp only [boxDifferential_apply, continuationMap_apply (R := R) (M := A) N.coeff,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul, hd.map_mul, mul_add,
    Finset.mul_sum, mul_assoc]
  abel

end TypeDStructure

end TauCeti
