/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HochschildCohomology.Bimodule
import Mathlib.Tactic.NoncommRing

/-!
# Infinitesimal deformations of an algebra and `HH²(A, A)`

Let `A` be an associative algebra over a commutative ring `R`, and write `A[ε] = A ⊕ εA` for its
extension of scalars to the dual numbers `R[ε] = R[ε]/(ε²)`, modelled on `A × A` with
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
  `TauCeti.InfinitesimalDeformation.setoid` of infinitesimal equivalence.

## Main results

* `TauCeti.isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles`: infinitesimal
  deformations are the Hochschild `2`-cocycles.
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

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

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

/-- A `2`-cochain is determined by its values on the tuples `![a, b]`. -/
private theorem apply_eq_apply_vecCons (φ : (Fin 2 → A) →ₘₗ[R] A) (a : Fin 2 → A) :
    φ a = φ ![a 0, a 1] := by
  congr 1
  ext i
  fin_cases i <;> rfl

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

/-- For an infinitesimal deformation `φ`, the element `1 - ε φ(1, 1)` is a left unit for the
deformed multiplication. -/
theorem infinitesimalDeformationMul_one_sub_left {φ : (Fin 2 → A) →ₘₗ[R] A}
    (hφ : IsInfinitesimalDeformation φ) (x : A × A) :
    infinitesimalDeformationMul φ (1, -φ ![1, 1]) x = x := by
  have h := (mem_cocycles_two_iff φ).1
    (isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles.1 hφ) 1 1 x.1
  simp only [one_mul, mul_one, sub_self, zero_add] at h
  refine Prod.ext (one_mul _) ?_
  simp only [infinitesimalDeformationMul_snd, one_mul, neg_mul]
  rw [sub_eq_zero] at h
  rw [h]
  abel

/-- For an infinitesimal deformation `φ`, the element `1 - ε φ(1, 1)` is a right unit for the
deformed multiplication. -/
theorem infinitesimalDeformationMul_one_sub_right {φ : (Fin 2 → A) →ₘₗ[R] A}
    (hφ : IsInfinitesimalDeformation φ) (x : A × A) :
    infinitesimalDeformationMul φ x (1, -φ ![1, 1]) = x := by
  have h := (mem_cocycles_two_iff φ).1
    (isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles.1 hφ) x.1 1 1
  simp only [mul_one, sub_add_cancel] at h
  refine Prod.ext (mul_one _) ?_
  simp only [infinitesimalDeformationMul_snd, mul_one, mul_neg]
  rw [sub_eq_zero] at h
  rw [h]
  abel

end Deformation

section Equivalence

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

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
    rw [apply_eq_apply_vecCons, apply_eq_apply_vecCons (hochschildBimoduleCoboundary R A A 1
      (MultilinearMap.ofSubsingleton (RingHom.id R) A A 0 g)),
      hochschildBimoduleCoboundary_ofSubsingleton_vecCons, sub_apply]
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
  · obtain ⟨g, hg⟩ : ∃ g : A →ₗ[R] A, ∀ x : A × A, F x = (x.1, x.2 + g x.1) := by
      refine ⟨LinearMap.snd R A A ∘ₗ F ∘ₗ LinearMap.inl R A A, fun x ↦ ?_⟩
      have hx : F x = F (x.1, 0) + F (0, x.2) := by
        rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      refine Prod.ext (hF.fst_apply x) ?_
      rw [hx, Prod.snd_add, hF.apply_zero_prod, add_comm]
      rfl
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

end Equivalence

section Cohomology

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A]

/-- The **infinitesimal deformations** of `A`: the Hochschild `2`-cochains `φ` for which the
multiplication `μ + εφ` on `A[ε]` is associative. -/
abbrev InfinitesimalDeformation : Type _ :=
  {φ : (Fin 2 → A) →ₘₗ[R] A // IsInfinitesimalDeformation φ}

namespace InfinitesimalDeformation

variable {R A}

/-- The Hochschild cocycle of an infinitesimal deformation. -/
def toCocycle (φ : InfinitesimalDeformation R A) : hochschildBimoduleCocycles R A A 2 :=
  ⟨φ.val, isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles.1 φ.property⟩

/-- The cocycle of an infinitesimal deformation is its underlying cochain. -/
@[simp]
theorem coe_toCocycle (φ : InfinitesimalDeformation R A) : (toCocycle φ : _) = φ.val := by
  rw [toCocycle]

/-- Two infinitesimal deformations are equivalent exactly when their cocycles have the same
class in `HH²(A, A)`. -/
theorem infinitesimallyEquivalent_iff_mk_eq_mk {φ ψ : InfinitesimalDeformation R A} :
    InfinitesimallyEquivalent φ.val ψ.val ↔
      hochschildBimoduleCohomology.mk R A A 2 (toCocycle φ) =
        hochschildBimoduleCohomology.mk R A A 2 (toCocycle ψ) := by
  rw [hochschildBimoduleCohomology.mk_eq_mk_iff,
    infinitesimallyEquivalent_iff_sub_mem_hochschildBimoduleCoboundaries, coe_toCocycle,
    coe_toCocycle]

variable (R A) in
/-- Infinitesimal equivalence, as an equivalence relation on infinitesimal deformations. -/
def setoid : Setoid (InfinitesimalDeformation R A) where
  r φ ψ := InfinitesimallyEquivalent φ.val ψ.val
  iseqv := by
    simp only [infinitesimallyEquivalent_iff_mk_eq_mk]
    exact ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Two infinitesimal deformations are related by `TauCeti.InfinitesimalDeformation.setoid`
exactly when they are infinitesimally equivalent. -/
theorem setoid_r_iff {φ ψ : InfinitesimalDeformation R A} :
    (setoid R A) φ ψ ↔ InfinitesimallyEquivalent φ.val ψ.val :=
  Iff.rfl

variable (R A) in
/-- **`HH²` classifies infinitesimal deformations**: the equivalence classes of infinitesimal
deformations of `A` correspond to the elements of the Hochschild cohomology `HH²(A, A)`, by
sending a deformation `μ + εφ` to the class of the cocycle `φ`. -/
def equivHochschildBimoduleCohomology :
    Quotient (setoid R A) ≃ hochschildBimoduleCohomology R A A 2 :=
  Equiv.ofBijective
    (Quotient.lift (fun φ ↦ hochschildBimoduleCohomology.mk R A A 2 (toCocycle φ))
      fun _ _ ↦ infinitesimallyEquivalent_iff_mk_eq_mk.1)
    ⟨fun φ ψ ↦ Quotient.inductionOn₂ φ ψ fun _ _ h ↦
        Quotient.sound (infinitesimallyEquivalent_iff_mk_eq_mk.2 h),
      fun c ↦ by
        obtain ⟨φ, rfl⟩ := hochschildBimoduleCohomology.mk_surjective R A A 2 c
        exact ⟨⟦⟨φ.val,
          isInfinitesimalDeformation_iff_mem_hochschildBimoduleCocycles.2 φ.property⟩⟧, rfl⟩⟩

/-- The class in `HH²(A, A)` of the equivalence class of a deformation `φ` is the cohomology
class of the cocycle `φ`. -/
@[simp]
theorem equivHochschildBimoduleCohomology_mk (φ : InfinitesimalDeformation R A) :
    equivHochschildBimoduleCohomology R A ⟦φ⟧ =
      hochschildBimoduleCohomology.mk R A A 2 (toCocycle φ) := by
  rw [equivHochschildBimoduleCohomology]
  rfl

end InfinitesimalDeformation

end Cohomology

end TauCeti
