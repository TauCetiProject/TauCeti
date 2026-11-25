/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HochschildCohomology.Bimodule
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# Infinitesimal deformations of an algebra and `HH²(A, A)`

Let `A` be an associative algebra over a commutative ring `R`, and write `A[ε] = A ⊕ εA` for its
extension of scalars to the dual numbers `R[ε] = R[X]/(X²)`, modelled on `A × A` with
`ε • (a, b) = (0, a)`. An `R[ε]`-bilinear multiplication on `A[ε]` that reduces to the
multiplication of `A` modulo `ε` is determined by its values `ac + ε φ(a, c)` on `A`, so it is

`(a + εb)(c + εd) = ac + ε(ad + bc + φ(a, c))`              (`infinitesimalDeformationMul`)

for an `R`-bilinear map `φ`, a Hochschild `2`-cochain of `A` with coefficients in `A`. Following
Gerstenhaber, `φ` is an **infinitesimal deformation** of `A` (`IsInfinitesimalDeformation`) when
this multiplication is associative. Expanding both sides, associativity says exactly that

`a φ(b, c) - φ(ab, c) + φ(a, bc) - φ(a, b) c = 0`,

that is, that `φ` is a Hochschild `2`-cocycle
(`isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles`). The deformed algebra is then
unital with unit `1 - ε φ(1, 1)` (`infinitesimalDeformationMul_one_sub_left`,
`infinitesimalDeformationMul_one_sub_right`).

Two deformations `φ` and `ψ` are equivalent when some `R[ε]`-linear map `F : A[ε] → A[ε]`
reducing to the identity modulo `ε` carries the first multiplication to the second
(`IsInfinitesimalEquivalence`). Such a map is `a + εb ↦ a + ε(b + g a)` for an `R`-linear
`g : A → A`, and it is multiplicative exactly when `φ - ψ` is the Hochschild coboundary of `g`
(`isInfinitesimalEquivalence_iff`). Hence two deformations are equivalent exactly when they
differ by a coboundary (`infinitesimallyEquivalent_iff_sub_mem_hochschildBimoduleCoboundaries`),
and the equivalence classes of infinitesimal deformations are the elements of the Hochschild
cohomology `HH²(A, A)` (`InfinitesimalDeformation.equivHochschildBimoduleCohomology`).

## Main definitions

* `TauCeti.infinitesimalDeformationMul`: the multiplication on `A[ε] = A × A` deformed by a
  Hochschild `2`-cochain.
* `TauCeti.IsInfinitesimalDeformation`: the deformed multiplication is associative.
* `TauCeti.IsInfinitesimalEquivalence`: an `R[ε]`-linear map reducing to the identity which carries
  one deformed multiplication to another.
* `TauCeti.InfinitesimallyEquivalent`: two deformations related by such a map.
* `TauCeti.InfinitesimalDeformation`: the infinitesimal deformations of `A`, with the setoid
  `TauCeti.InfinitesimalDeformation.setoid` of infinitesimal equivalence, and
  `TauCeti.InfinitesimalDeformation.cocycleEquiv` identifying them with Hochschild `2`-cocycles.

## Main results

* `TauCeti.isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles`: infinitesimal
  deformations are the Hochschild `2`-cocycles.
* `TauCeti.zero_infinitesimalDeformationMul`, `TauCeti.add_infinitesimalDeformationMul`,
  `TauCeti.smul_infinitesimalDeformationMul` and their right-hand versions: the deformed
  multiplication is `R`-bilinear.
* `TauCeti.IsInfinitesimalEquivalence.apply_eq`: infinitesimal equivalences are shears
  `a + εb ↦ a + ε(b + g a)`, and `TauCeti.IsInfinitesimalEquivalence.exists_inverse`: they are
  invertible, over any additive group `A` with a multiplication.
* `TauCeti.InfinitesimallyEquivalent.refl`, `.symm` and `.trans`: infinitesimal equivalence is an
  equivalence relation.
* `TauCeti.isInfinitesimalEquivalence_iff`: the equivalences are the maps `id + ε g` for which
  `φ - ψ = δ g`.
* `TauCeti.infinitesimallyEquivalent_iff_sub_mem_hochschildBimoduleCoboundaries`: deformations are
  equivalent exactly when they differ by a Hochschild coboundary.
* `TauCeti.InfinitesimalDeformation.equivHochschildBimoduleCohomology`: equivalence classes of
  infinitesimal deformations correspond to the elements of `HH²(A, A)`.

## References

* M. Gerstenhaber, *On the deformation of rings and algebras*, Annals of Mathematics 79 (1964),
  59--103.
-/

public section

noncomputable section

open MulOpposite

namespace TauCeti

section Deformation

variable {R A : Type*} [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]

/-- The multiplication `(a + εb)(c + εd) = ac + ε(ad + bc + φ(a, c))` on `A[ε]`, modelled on
`A × A`, deformed by the Hochschild `2`-cochain `φ`. Every `R[ε]`-bilinear multiplication on
`A[ε]` reducing to the multiplication of `A` modulo `ε` has this form. -/
def infinitesimalDeformationMul (φ : (Fin 2 → A) →ₘₗ[R] A) (x y : A × A) : A × A :=
  (x.1 * y.1, x.1 * y.2 + x.2 * y.1 + φ ![x.1, y.1])

/-- Modulo `ε`, the deformed multiplication is the multiplication of `A`. -/
@[simp]
theorem infinitesimalDeformationMul_fst (φ : (Fin 2 → A) →ₘₗ[R] A) (x y : A × A) :
    (infinitesimalDeformationMul φ x y).1 = x.1 * y.1 := by
  rw [infinitesimalDeformationMul]

/-- The `ε`-component of the deformed multiplication. -/
@[simp]
theorem infinitesimalDeformationMul_snd (φ : (Fin 2 → A) →ₘₗ[R] A) (x y : A × A) :
    (infinitesimalDeformationMul φ x y).2 = x.1 * y.2 + x.2 * y.1 + φ ![x.1, y.1] := by
  rw [infinitesimalDeformationMul]

/-- A Hochschild `2`-cochain `φ` is an **infinitesimal deformation** of `A` when the
multiplication `μ + εφ` on `A[ε]` is associative. -/
def IsInfinitesimalDeformation (φ : (Fin 2 → A) →ₘₗ[R] A) : Prop :=
  ∀ x y z : A × A, infinitesimalDeformationMul φ (infinitesimalDeformationMul φ x y) z =
    infinitesimalDeformationMul φ x (infinitesimalDeformationMul φ y z)

/-- Unfolding `TauCeti.IsInfinitesimalDeformation`: the deformed multiplication is
associative. -/
theorem isInfinitesimalDeformation_iff {φ : (Fin 2 → A) →ₘₗ[R] A} :
    IsInfinitesimalDeformation φ ↔
      ∀ x y z : A × A, infinitesimalDeformationMul φ (infinitesimalDeformationMul φ x y) z =
        infinitesimalDeformationMul φ x (infinitesimalDeformationMul φ y z) :=
  Iff.rfl

variable (R A) in
/-- The **infinitesimal deformations** of `A`: the Hochschild `2`-cochains `φ` for which the
multiplication `μ + εφ` on `A[ε]` is associative. -/
abbrev InfinitesimalDeformation : Type _ :=
  {φ : (Fin 2 → A) →ₘₗ[R] A // IsInfinitesimalDeformation φ}

/-- An **infinitesimal equivalence** from the deformation `μ + εφ` to `μ + εψ`: an `R`-linear map
`F : A[ε] → A[ε]` which reduces to the identity modulo `ε`, commutes with multiplication by `ε`,
`ε • (a, b) = (0, a)`, and carries the first deformed multiplication to the second. -/
structure IsInfinitesimalEquivalence (φ ψ : (Fin 2 → A) →ₘₗ[R] A) (F : A × A →ₗ[R] A × A) :
    Prop where
  /-- `F` reduces to the identity modulo `ε`. -/
  fst_apply (x : A × A) : (F x).1 = x.1
  /-- `F` commutes with multiplication by `ε`, given that it reduces to the identity. -/
  apply_zero_prod (a : A) : F (0, a) = (0, a)
  /-- `F` carries `μ + εφ` to `μ + εψ`. -/
  map_mul (x y : A × A) :
    F (infinitesimalDeformationMul φ x y) = infinitesimalDeformationMul ψ (F x) (F y)

/-- Two Hochschild `2`-cochains are **infinitesimally equivalent** when some infinitesimal
equivalence carries the first deformed multiplication to the second. -/
def InfinitesimallyEquivalent (φ ψ : (Fin 2 → A) →ₘₗ[R] A) : Prop :=
  ∃ F : A × A →ₗ[R] A × A, IsInfinitesimalEquivalence φ ψ F

/-- Unfolding `TauCeti.InfinitesimallyEquivalent`: some infinitesimal equivalence exists. -/
theorem infinitesimallyEquivalent_iff {φ ψ : (Fin 2 → A) →ₘₗ[R] A} :
    InfinitesimallyEquivalent φ ψ ↔ ∃ F : A × A →ₗ[R] A × A, IsInfinitesimalEquivalence φ ψ F :=
  Iff.rfl

/-- The identity is an infinitesimal equivalence from a deformation to itself. -/
theorem IsInfinitesimalEquivalence.refl (φ : (Fin 2 → A) →ₘₗ[R] A) :
    IsInfinitesimalEquivalence φ φ LinearMap.id where
  fst_apply _ := by simp
  apply_zero_prod _ := by simp
  map_mul _ _ := by simp

/-- Infinitesimal equivalences compose. -/
theorem IsInfinitesimalEquivalence.comp {φ ψ χ : (Fin 2 → A) →ₘₗ[R] A}
    {F G : A × A →ₗ[R] A × A} (hF : IsInfinitesimalEquivalence φ ψ F)
    (hG : IsInfinitesimalEquivalence ψ χ G) : IsInfinitesimalEquivalence φ χ (G ∘ₗ F) where
  fst_apply x := by rw [LinearMap.comp_apply, hG.fst_apply, hF.fst_apply]
  apply_zero_prod a := by rw [LinearMap.comp_apply, hF.apply_zero_prod, hG.apply_zero_prod]
  map_mul x y := by simp only [LinearMap.comp_apply, hF.map_mul, hG.map_mul]

/-- Every Hochschild `2`-cochain is infinitesimally equivalent to itself. -/
@[refl]
theorem InfinitesimallyEquivalent.refl (φ : (Fin 2 → A) →ₘₗ[R] A) :
    InfinitesimallyEquivalent φ φ :=
  ⟨_, .refl φ⟩

/-- Infinitesimal equivalence is transitive. -/
theorem InfinitesimallyEquivalent.trans {φ ψ χ : (Fin 2 → A) →ₘₗ[R] A}
    (h₁ : InfinitesimallyEquivalent φ ψ) (h₂ : InfinitesimallyEquivalent ψ χ) :
    InfinitesimallyEquivalent φ χ :=
  let ⟨_, hF⟩ := h₁
  let ⟨_, hG⟩ := h₂
  ⟨_, hF.comp hG⟩

/-- **Infinitesimal equivalences are shears**: an infinitesimal equivalence `F` is
`a + εb ↦ a + ε(b + g a)` for `g = snd ∘ F ∘ inl`. -/
theorem IsInfinitesimalEquivalence.apply_eq {φ ψ : (Fin 2 → A) →ₘₗ[R] A}
    {F : A × A →ₗ[R] A × A} (hF : IsInfinitesimalEquivalence φ ψ F) (x : A × A) :
    F x = (x.1, x.2 + (LinearMap.snd R A A ∘ₗ F ∘ₗ LinearMap.inl R A A) x.1) := by
  have hx : F x = F (x.1, 0) + F (0, x.2) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  refine Prod.ext (hF.fst_apply x) ?_
  rw [hx, Prod.snd_add, hF.apply_zero_prod, add_comm]
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply]

end Deformation

section Inverse

variable {R A : Type*} [Semiring R] [AddCommGroup A] [Mul A] [Module R A]

/-- **Inverse of an infinitesimal equivalence.** An infinitesimal equivalence `F` from `μ + εφ`
to `μ + εψ` has a two-sided inverse which is an infinitesimal equivalence from `μ + εψ` to
`μ + εφ`: if `F` is the shear `a + εb ↦ a + ε(b + g a)`, its inverse is the shear for `-g`. -/
theorem IsInfinitesimalEquivalence.exists_inverse {φ ψ : (Fin 2 → A) →ₘₗ[R] A}
    {F : A × A →ₗ[R] A × A} (hF : IsInfinitesimalEquivalence φ ψ F) :
    ∃ G : A × A →ₗ[R] A × A, IsInfinitesimalEquivalence ψ φ G ∧ G ∘ₗ F = LinearMap.id ∧
      F ∘ₗ G = LinearMap.id := by
  set g := LinearMap.snd R A A ∘ₗ F ∘ₗ LinearMap.inl R A A
  set G := LinearMap.id - LinearMap.inr R A A ∘ₗ g ∘ₗ LinearMap.fst R A A
  have hG (x : A × A) : G x = (x.1, x.2 - g x.1) := by
    simp [G, Prod.ext_iff]
  have hGF (x : A × A) : G (F x) = x := by
    rw [hG, hF.apply_eq x, add_sub_cancel_right]
  have hFG (x : A × A) : F (G x) = x := by
    rw [hF.apply_eq, hG, sub_add_cancel]
  refine ⟨G, ⟨fun x ↦ by rw [hG], fun a ↦ by rw [hG, map_zero, sub_zero], fun x y ↦ ?_⟩,
    LinearMap.ext hGF, LinearMap.ext hFG⟩
  rw [← hFG x, ← hFG y, ← hF.map_mul, hGF, hGF, hGF]

/-- Infinitesimal equivalence is symmetric. -/
@[symm]
theorem InfinitesimallyEquivalent.symm {φ ψ : (Fin 2 → A) →ₘₗ[R] A}
    (h : InfinitesimallyEquivalent φ ψ) : InfinitesimallyEquivalent ψ φ :=
  let ⟨_, hF⟩ := h
  let ⟨G, hG, _⟩ := hF.exists_inverse
  ⟨G, hG⟩

namespace InfinitesimalDeformation

variable (R A) in
/-- Infinitesimal equivalence, as an equivalence relation on infinitesimal deformations. -/
def setoid : Setoid (InfinitesimalDeformation R A) where
  r φ ψ := InfinitesimallyEquivalent φ.val ψ.val
  iseqv := ⟨fun φ ↦ .refl φ.val, .symm, .trans⟩

/-- Two infinitesimal deformations are related by `TauCeti.InfinitesimalDeformation.setoid`
exactly when they are infinitesimally equivalent. -/
theorem setoid_r_iff {φ ψ : InfinitesimalDeformation R A} :
    (setoid R A) φ ψ ↔ InfinitesimallyEquivalent φ.val ψ.val :=
  Iff.rfl

end InfinitesimalDeformation

end Inverse

section Bilinear

variable {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]

/-- `0` is absorbing on the left for the deformed multiplication. -/
@[simp]
theorem zero_infinitesimalDeformationMul {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
    (φ : (Fin 2 → A) →ₘₗ[R] A) (y : A × A) :
    infinitesimalDeformationMul φ 0 y = 0 :=
  Prod.ext (by simp) (by simp [φ.map_coord_zero (m := ![0, y.1]) 0 rfl])

/-- `0` is absorbing on the right for the deformed multiplication. -/
@[simp]
theorem infinitesimalDeformationMul_zero {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
    (φ : (Fin 2 → A) →ₘₗ[R] A) (x : A × A) :
    infinitesimalDeformationMul φ x 0 = 0 :=
  Prod.ext (by simp) (by simp [φ.map_coord_zero (m := ![x.1, 0]) 1 rfl])

/-- The deformed multiplication is additive in its first argument. -/
theorem add_infinitesimalDeformationMul [Mul A] [RightDistribClass A] (φ : (Fin 2 → A) →ₘₗ[R] A)
    (x x' y : A × A) :
    infinitesimalDeformationMul φ (x + x') y =
      infinitesimalDeformationMul φ x y + infinitesimalDeformationMul φ x' y := by
  refine Prod.ext (by simp [add_mul]) ?_
  simp only [infinitesimalDeformationMul_snd, Prod.fst_add, Prod.snd_add, Prod.snd_add, add_mul,
    φ.map_vecCons_add_left]
  abel

/-- The deformed multiplication is additive in its second argument. -/
theorem infinitesimalDeformationMul_add [Mul A] [LeftDistribClass A] (φ : (Fin 2 → A) →ₘₗ[R] A)
    (x y y' : A × A) :
    infinitesimalDeformationMul φ x (y + y') =
      infinitesimalDeformationMul φ x y + infinitesimalDeformationMul φ x y' := by
  refine Prod.ext (by simp [mul_add]) ?_
  simp only [infinitesimalDeformationMul_snd, Prod.fst_add, Prod.snd_add, mul_add,
    φ.map_vecCons_add_right]
  abel

/-- The deformed multiplication is `R`-linear in its first argument. -/
theorem smul_infinitesimalDeformationMul [Mul A] [IsScalarTower R A A] (φ : (Fin 2 → A) →ₘₗ[R] A)
    (c : R) (x y : A × A) :
    infinitesimalDeformationMul φ (c • x) y = c • infinitesimalDeformationMul φ x y :=
  Prod.ext (by simp [smul_mul_assoc])
    (by simp [smul_mul_assoc, φ.map_vecCons_smul_left, smul_add])

/-- The deformed multiplication is `R`-linear in its second argument. -/
theorem infinitesimalDeformationMul_smul [Mul A] [SMulCommClass R A A] (φ : (Fin 2 → A) →ₘₗ[R] A)
    (c : R) (x y : A × A) :
    infinitesimalDeformationMul φ x (c • y) = c • infinitesimalDeformationMul φ x y :=
  Prod.ext (by simp [mul_smul_comm])
    (by simp [mul_smul_comm, φ.map_vecCons_smul_right, smul_add])

end Bilinear

section Unit

variable {R A : Type*} [Semiring R] [NonAssocRing A] [Module R A]

/-- For an infinitesimal deformation `φ`, `φ(1, a) = φ(1, 1) a`: compare the `ε`-components of
`((1, 0)(1, 0))(a, 0)` and `(1, 0)((1, 0)(a, 0))`. -/
private theorem apply_one_left {φ : (Fin 2 → A) →ₘₗ[R] A} (hφ : IsInfinitesimalDeformation φ)
    (a : A) : φ ![1, a] = φ ![1, 1] * a := by
  have h := congrArg Prod.snd (hφ (1, 0) (1, 0) (a, 0))
  simp only [infinitesimalDeformationMul_snd, infinitesimalDeformationMul_fst, mul_zero,
    zero_mul, add_zero, zero_add, one_mul] at h
  simpa using h.symm

/-- For an infinitesimal deformation `φ`, `φ(a, 1) = a φ(1, 1)`: compare the `ε`-components of
`((a, 0)(1, 0))(1, 0)` and `(a, 0)((1, 0)(1, 0))`. -/
private theorem apply_one_right {φ : (Fin 2 → A) →ₘₗ[R] A} (hφ : IsInfinitesimalDeformation φ)
    (a : A) : φ ![a, 1] = a * φ ![1, 1] := by
  have h := congrArg Prod.snd (hφ (a, 0) (1, 0) (1, 0))
  simp only [infinitesimalDeformationMul_snd, infinitesimalDeformationMul_fst, mul_zero,
    add_zero, zero_add, mul_one] at h
  simpa using h

/-- For an infinitesimal deformation `φ`, the element `1 - ε φ(1, 1)` is a left unit for the
deformed multiplication. -/
@[simp]
theorem infinitesimalDeformationMul_one_sub_left {φ : (Fin 2 → A) →ₘₗ[R] A}
    (hφ : IsInfinitesimalDeformation φ) (x : A × A) :
    infinitesimalDeformationMul φ (1, -φ ![1, 1]) x = x := by
  refine Prod.ext (one_mul _) ?_
  rw [infinitesimalDeformationMul_snd, apply_one_left hφ x.1, neg_mul, one_mul,
    neg_add_cancel_right]

/-- For an infinitesimal deformation `φ`, the element `1 - ε φ(1, 1)` is a right unit for the
deformed multiplication. -/
@[simp]
theorem infinitesimalDeformationMul_one_sub_right {φ : (Fin 2 → A) →ₘₗ[R] A}
    (hφ : IsInfinitesimalDeformation φ) (x : A × A) :
    infinitesimalDeformationMul φ x (1, -φ ![1, 1]) = x := by
  refine Prod.ext (mul_one _) ?_
  rw [infinitesimalDeformationMul_snd, apply_one_right hφ x.1, mul_neg, mul_one]
  abel

end Unit

section Cocycle

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- With coefficients in `A`, the degree-two cocycle condition reads
`a φ(b, c) - φ(ab, c) + φ(a, bc) - φ(a, b) c = 0`. -/
private theorem mem_cocycles_two_iff (φ : (Fin 2 → A) →ₘₗ[R] A) :
    φ ∈ hochschildBimoduleCocycles R A A 2 ↔
      ∀ a b c : A, a * φ ![b, c] - φ ![a * b, c] + φ ![a, b * c] - φ ![a, b] * c = 0 := by
  simp only [mem_hochschildBimoduleCocycles_two_iff, smul_eq_mul, op_smul_eq_mul]

/-- **Infinitesimal deformations are Hochschild `2`-cocycles**: the multiplication `μ + εφ` on
`A[ε]` is associative exactly when `φ` is a Hochschild `2`-cocycle of `A` with coefficients
in `A`. -/
theorem isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles
    {φ : (Fin 2 → A) →ₘₗ[R] A} :
    IsInfinitesimalDeformation φ ↔ φ ∈ hochschildBimoduleCocycles R A A 2 := by
  rw [mem_cocycles_two_iff]
  refine ⟨fun h a b c ↦ ?_, fun h x y z ↦ ?_⟩
  · have h₂ := congrArg Prod.snd (h (a, 0) (b, 0) (c, 0))
    simp only [infinitesimalDeformationMul_snd, infinitesimalDeformationMul_fst, mul_zero,
      zero_mul, add_zero, zero_add] at h₂
    rw [← sub_eq_zero] at h₂
    rw [← neg_eq_zero, ← h₂]
    noncomm_ring
  · have h₃ := h x.1 y.1 z.1
    refine Prod.ext (mul_assoc _ _ _) ?_
    simp only [infinitesimalDeformationMul_snd, infinitesimalDeformationMul_fst]
    rw [← sub_eq_zero, ← neg_eq_zero, ← h₃]
    noncomm_ring

end Cocycle

section Equivalence

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- The coboundary of the `1`-cochain `g`, written with tuples `![a, b]`. -/
private theorem hochschildBimoduleCoboundary_ofSubsingleton_vecCons (g : A →ₗ[R] A) (a b : A) :
    hochschildBimoduleCoboundary R A A 1
        (MultilinearMap.ofSubsingleton (RingHom.id R) A A 0 g) ![a, b] =
      a * g b - g (a * b) + g a * b := by
  rw [hochschildBimoduleCoboundary_ofSubsingleton]
  simp

/-- The map `a + εb ↦ a + ε(b + g a)` multiplies like an infinitesimal equivalence from `φ` to
`ψ` exactly when `φ - ψ` is the coboundary of `g`. -/
private theorem map_mul_iff (φ ψ : (Fin 2 → A) →ₘₗ[R] A) (g : A →ₗ[R] A) :
    (∀ x y : A × A,
      ((infinitesimalDeformationMul φ x y).1,
          (infinitesimalDeformationMul φ x y).2 + g (infinitesimalDeformationMul φ x y).1) =
        infinitesimalDeformationMul ψ (x.1, x.2 + g x.1) (y.1, y.2 + g y.1)) ↔
      φ - ψ = hochschildBimoduleCoboundary R A A 1
        (MultilinearMap.ofSubsingleton (RingHom.id R) A A 0 g) := by
  refine ⟨fun h ↦ ?_, fun h x y ↦ ?_⟩
  · ext v
    have hv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hv, hochschildBimoduleCoboundary_ofSubsingleton_vecCons, sub_apply]
    have h₂ := congrArg Prod.snd (h (v 0, 0) (v 1, 0))
    simp only [infinitesimalDeformationMul_snd, infinitesimalDeformationMul_fst, mul_zero,
      zero_mul, add_zero, zero_add] at h₂
    rw [sub_eq_iff_eq_add, ← sub_eq_zero]
    rw [← sub_eq_zero] at h₂
    rw [← h₂]
    abel
  · have h₂ := congrArg (· ![x.1, y.1]) h
    simp only [sub_apply,
      hochschildBimoduleCoboundary_ofSubsingleton_vecCons] at h₂
    refine Prod.ext rfl ?_
    simp only [infinitesimalDeformationMul_snd, infinitesimalDeformationMul_fst, mul_add, add_mul]
    rw [sub_eq_iff_eq_add] at h₂
    rw [h₂]
    abel

/-- The infinitesimal equivalences from `μ + εφ` to `μ + εψ` are the maps
`a + εb ↦ a + ε(b + g a)` for the `R`-linear maps `g : A → A` whose Hochschild coboundary is
`φ - ψ`. -/
theorem isInfinitesimalEquivalence_iff {φ ψ : (Fin 2 → A) →ₘₗ[R] A}
    {F : A × A →ₗ[R] A × A} :
    IsInfinitesimalEquivalence φ ψ F ↔
      ∃ g : A →ₗ[R] A, (∀ x : A × A, F x = (x.1, x.2 + g x.1)) ∧
        φ - ψ = hochschildBimoduleCoboundary R A A 1
          (MultilinearMap.ofSubsingleton (RingHom.id R) A A 0 g) := by
  refine ⟨fun hF ↦ ?_, fun ⟨g, hFg, hg⟩ ↦ ?_⟩
  · obtain ⟨g, hg⟩ : ∃ g : A →ₗ[R] A, ∀ x : A × A, F x = (x.1, x.2 + g x.1) :=
      ⟨_, hF.apply_eq⟩
    refine ⟨g, hg, (map_mul_iff φ ψ g).1 fun x y ↦ ?_⟩
    have h := hF.map_mul x y
    rwa [hg x, hg y, hg] at h
  · refine ⟨fun x ↦ by rw [hFg], fun a ↦ by rw [hFg, map_zero, add_zero], fun x y ↦ ?_⟩
    simp only [hFg]
    exact (map_mul_iff φ ψ g).2 hg x y

/-- **Equivalent infinitesimal deformations differ by a coboundary**: two Hochschild
`2`-cochains are infinitesimally equivalent exactly when their difference is a Hochschild
coboundary. -/
theorem infinitesimallyEquivalent_iff_sub_mem_hochschildBimoduleCoboundaries
    {φ ψ : (Fin 2 → A) →ₘₗ[R] A} :
    InfinitesimallyEquivalent φ ψ ↔ φ - ψ ∈ hochschildBimoduleCoboundaries R A A 2 := by
  rw [mem_hochschildBimoduleCoboundaries_succ_iff]
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨g, -, hg⟩ := isInfinitesimalEquivalence_iff.1 hF
    exact ⟨_, hg.symm⟩
  · rintro ⟨χ, hχ⟩
    obtain ⟨g, rfl⟩ := (MultilinearMap.ofSubsingleton (RingHom.id R) A A (0 : Fin 1)).surjective χ
    exact ⟨LinearMap.id + LinearMap.inr R A A ∘ₗ g ∘ₗ LinearMap.fst R A A,
      isInfinitesimalEquivalence_iff.2 ⟨g, fun x ↦ by simp [Prod.ext_iff], hχ.symm⟩⟩

namespace InfinitesimalDeformation

variable (R A) in
/-- **Infinitesimal deformations are Hochschild `2`-cocycles**, as subtypes of the
`2`-cochains. -/
def cocycleEquiv : InfinitesimalDeformation R A ≃ hochschildBimoduleCocycles R A A 2 :=
  Equiv.subtypeEquivRight fun _ ↦ isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles

/-- The cocycle of an infinitesimal deformation is its underlying cochain. -/
@[simp]
theorem coe_cocycleEquiv (φ : InfinitesimalDeformation R A) :
    (cocycleEquiv R A φ : _) = φ.val := by
  simp [cocycleEquiv]

/-- The underlying cochain of the deformation of a cocycle is the cocycle. -/
@[simp]
theorem val_cocycleEquiv_symm (ψ : hochschildBimoduleCocycles R A A 2) :
    ((cocycleEquiv R A).symm ψ).val = ψ := by
  simp [cocycleEquiv]

end InfinitesimalDeformation

end Equivalence

section Cohomology

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

namespace InfinitesimalDeformation

/-- Two infinitesimal deformations are equivalent exactly when their cocycles have the same
class in `HH²(A, A)`. -/
theorem infinitesimallyEquivalent_iff_mk_eq_mk {φ ψ : InfinitesimalDeformation R A} :
    InfinitesimallyEquivalent φ.val ψ.val ↔
      hochschildBimoduleCohomology.mk R A A 2 (cocycleEquiv R A φ) =
        hochschildBimoduleCohomology.mk R A A 2 (cocycleEquiv R A ψ) := by
  rw [hochschildBimoduleCohomology.mk_eq_mk_iff,
    infinitesimallyEquivalent_iff_sub_mem_hochschildBimoduleCoboundaries, coe_cocycleEquiv,
    coe_cocycleEquiv]

variable (R A) in
/-- **`HH²` classifies infinitesimal deformations**: the equivalence classes of infinitesimal
deformations of `A` correspond to the elements of the Hochschild cohomology `HH²(A, A)`, by
sending a deformation `μ + εφ` to the class of the cocycle `φ`. -/
def equivHochschildBimoduleCohomology :
    Quotient (setoid R A) ≃ hochschildBimoduleCohomology R A A 2 :=
  Equiv.ofBijective
    (Quotient.lift (fun φ ↦ hochschildBimoduleCohomology.mk R A A 2 (cocycleEquiv R A φ))
      fun _ _ h ↦ infinitesimallyEquivalent_iff_mk_eq_mk.1 (setoid_r_iff.1 h))
    ⟨fun φ ψ ↦ Quotient.inductionOn₂ φ ψ fun _ _ h ↦
        Quotient.sound (setoid_r_iff.2 (infinitesimallyEquivalent_iff_mk_eq_mk.2 h)),
      fun c ↦ by
        obtain ⟨ψ, rfl⟩ := hochschildBimoduleCohomology.mk_surjective R A A 2 c
        exact ⟨⟦(cocycleEquiv R A).symm ψ⟧, congrArg _ (Equiv.apply_symm_apply _ ψ)⟩⟩

/-- The class in `HH²(A, A)` of the equivalence class of a deformation `φ` is the cohomology
class of the cocycle `φ`. -/
@[simp]
theorem equivHochschildBimoduleCohomology_mk (φ : InfinitesimalDeformation R A) :
    equivHochschildBimoduleCohomology R A ⟦φ⟧ =
      hochschildBimoduleCohomology.mk R A A 2 (cocycleEquiv R A φ) := by
  rw [equivHochschildBimoduleCohomology]
  exact (Equiv.ofBijective_apply _ _ _).trans (Quotient.lift_mk _ _ φ)

/-- The equivalence class of deformations corresponding to the class of a cocycle `ψ` is that
of the deformation `μ + εψ`. -/
@[simp]
theorem equivHochschildBimoduleCohomology_symm_mk (ψ : hochschildBimoduleCocycles R A A 2) :
    (equivHochschildBimoduleCohomology R A).symm (hochschildBimoduleCohomology.mk R A A 2 ψ) =
      ⟦(cocycleEquiv R A).symm ψ⟧ := by
  rw [Equiv.symm_apply_eq, equivHochschildBimoduleCohomology_mk, Equiv.apply_symm_apply]

end InfinitesimalDeformation

end Cohomology

end TauCeti
