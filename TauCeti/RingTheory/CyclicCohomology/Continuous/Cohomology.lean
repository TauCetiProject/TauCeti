/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import TauCeti.RingTheory.CyclicCohomology.OperatorTopology

/-!
# Continuous cyclic cohomology

For a topological algebra `A` with jointly continuous multiplication, the jointly continuous
cyclic cochains form a subcomplex of Connes' cyclic cochain complex. Its cohomology
`HCⁿ_cont(A; M)` is the continuous cyclic cohomology, the version of cyclic cohomology used
for Fréchet and other locally convex algebras.

This file defines it as the algebraic quotient of the continuous cyclic cocycles by the
continuous cyclic coboundaries, where a continuous coboundary is the Hochschild coboundary of a
*continuous* cyclic cochain. Over a normed field the continuous cochains carry the topology of
uniform convergence on bounded sets, and continuous cyclic cohomology carries the induced
quotient topology. The coboundaries are not replaced by their closure, so this quotient need
not be Hausdorff: `TauCeti.continuousCyclicCohomology.t2Space_iff` shows it is Hausdorff exactly
when the continuous coboundaries are closed.

Forgetting continuity sends continuous cocycles to cocycles and continuous coboundaries to
coboundaries, so for unital `A` it induces a comparison map to the algebraic cyclic cohomology
`HCⁿ(A; M)`.
This map need not be injective or surjective. Continuous homomorphisms of nonunital algebras
pull continuous cyclic cohomology back, compatibly with the comparison map and continuously for
the quotient topologies.

## Main definitions

* `TauCeti.continuousCyclicCocycles`, `TauCeti.continuousCyclicCoboundaries`: continuous cyclic
  cocycles and coboundaries.
* `TauCeti.continuousCyclicCohomology`: the continuous cyclic cohomology `HCⁿ_cont(A; M)`.
* `TauCeti.continuousCyclicCohomology.mk`: the class of a continuous cyclic cocycle.
* `TauCeti.continuousCyclicCohomology.desc`: the linear map out of continuous cyclic cohomology
  induced by a linear map on continuous cocycles vanishing on continuous coboundaries.
* `TauCeti.continuousCyclicCohomology.toCyclicCohomology`: the comparison map to `HCⁿ(A; M)`.
* `TauCeti.continuousCyclicCochainsMap`, `TauCeti.continuousCyclicCohomology.map`: pullback along
  continuous linear maps and continuous homomorphisms of nonunital algebras.

## Main results

* `TauCeti.continuousCyclicCohomology.mk_eq_zero_iff`: a continuous cocycle has zero class
  exactly when it is the coboundary of a continuous cyclic cochain.
* `TauCeti.continuousCyclicCohomology.zeroEquiv`: `HC⁰_cont(A; M)` is the module of continuous
  `M`-valued traces on `A`.
* `TauCeti.continuousCyclicCohomology.map_id`, `TauCeti.continuousCyclicCohomology.map_comp`,
  `TauCeti.continuousCyclicCohomology.toCyclicCohomology_map`: functoriality and naturality of
  the comparison map.
* `TauCeti.continuousCyclicCohomology.isOpenQuotientMap_mk`: the class map is an open quotient
  map onto `HCⁿ_cont(A; M)`.
* `TauCeti.isClosed_continuousCyclicCocycles`, `TauCeti.continuousCyclicCohomology.t2Space_iff`:
  for Hausdorff `M`, continuous cyclic cocycles are closed, and `HCⁿ_cont(A; M)` is Hausdorff
  exactly when the continuous cyclic coboundaries are closed.

## References

* A. Connes, *Noncommutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II,
  §§1–2 (continuous cyclic cohomology of locally convex algebras).
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
-/

public section

noncomputable section

open Topology

namespace TauCeti

universe u

section Cocycles

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

/-- The continuous cyclic `n`-cocycles: the continuous cyclic cochains annihilated by the
Hochschild coboundary. -/
def continuousCyclicCocycles (n : ℕ) : Submodule R (continuousCyclicCochains R A M n) :=
  LinearMap.ker (continuousCyclicHochschildCoboundary R A M n)

/-- A continuous cyclic cochain is a cocycle exactly when its Hochschild coboundary vanishes. -/
@[simp]
theorem mem_continuousCyclicCocycles_iff {n : ℕ} {φ : continuousCyclicCochains R A M n} :
    φ ∈ continuousCyclicCocycles R A M n ↔
      continuousHochschildCoboundary R A M n (φ : ContinuousMultilinearMap R
        (fun _ : Fin (n + 1) ↦ A) M) = 0 := by
  rw [continuousCyclicCocycles, LinearMap.mem_ker, ← Subtype.coe_inj,
    coe_continuousCyclicHochschildCoboundary, ZeroMemClass.coe_zero]

/-- A continuous cyclic cochain is a continuous cocycle exactly when its underlying algebraic
cyclic cochain is a cocycle. -/
theorem mem_continuousCyclicCocycles_iff_hochschildCoboundary {n : ℕ}
    {φ : continuousCyclicCochains R A M n} :
    φ ∈ continuousCyclicCocycles R A M n ↔
      hochschildCoboundary R A M n (φ : ContinuousMultilinearMap R
        (fun _ : Fin (n + 1) ↦ A) M).toMultilinearMap = 0 := by
  rw [mem_continuousCyclicCocycles_iff, ← toMultilinearMap_continuousHochschildCoboundary,
    ← ContinuousMultilinearMap.toMultilinearMap_zero,
    ContinuousMultilinearMap.toMultilinearMap_injective.eq_iff]

/-- The continuous cyclic `n`-coboundaries: zero in degree zero, and in degree `n + 1` the
Hochschild coboundaries of continuous cyclic `n`-cochains. -/
def continuousCyclicCoboundaries : (n : ℕ) → Submodule R (continuousCyclicCochains R A M n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (continuousCyclicHochschildCoboundary R A M n)

/-- There are no nonzero continuous cyclic coboundaries in degree zero. -/
@[simp]
theorem continuousCyclicCoboundaries_zero : continuousCyclicCoboundaries R A M 0 = ⊥ := (rfl)

/-- In positive degree the continuous cyclic coboundaries are the image of the Hochschild
coboundary on continuous cyclic cochains. -/
theorem continuousCyclicCoboundaries_succ (n : ℕ) :
    continuousCyclicCoboundaries R A M (n + 1) =
      LinearMap.range (continuousCyclicHochschildCoboundary R A M n) :=
  (rfl)

/-- A continuous cyclic `(n + 1)`-cochain is a continuous coboundary exactly when it is the
Hochschild coboundary of a continuous cyclic `n`-cochain. -/
@[simp]
theorem mem_continuousCyclicCoboundaries_succ_iff {n : ℕ}
    {φ : continuousCyclicCochains R A M (n + 1)} :
    φ ∈ continuousCyclicCoboundaries R A M (n + 1) ↔
      ∃ ψ : continuousCyclicCochains R A M n,
        continuousCyclicHochschildCoboundary R A M n ψ = φ := by
  rw [continuousCyclicCoboundaries_succ, LinearMap.mem_range]

/-- A continuous cyclic `0`-cochain is a cocycle exactly when it is a trace. -/
theorem mem_continuousCyclicCocycles_zero_iff {φ : continuousCyclicCochains R A M 0} :
    φ ∈ continuousCyclicCocycles R A M 0 ↔
      ∀ x y : A, (φ : ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A) M) (fun _ ↦ x * y) =
        (φ : ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A) M) (fun _ ↦ y * x) := by
  rw [mem_continuousCyclicCocycles_iff_hochschildCoboundary, hochschildCoboundary_zero_eq_zero_iff]
  simp only [ContinuousMultilinearMap.coe_coe]

end Cocycles

section AssociativeCocycles

variable (R A M : Type*) [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

/-- Every continuous cyclic coboundary is a continuous cyclic cocycle. -/
theorem continuousCyclicCoboundaries_le_continuousCyclicCocycles (n : ℕ) :
    continuousCyclicCoboundaries R A M n ≤ continuousCyclicCocycles R A M n := by
  cases n with
  | zero => simp
  | succ n =>
    rintro _ ⟨ψ, rfl⟩
    exact continuousCyclicHochschildCoboundary_continuousCyclicHochschildCoboundary R A M ψ

end AssociativeCocycles

section Forget

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [Module R A] [TopologicalSpace A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul R M]

/-- Forgetting continuity, as a linear map from continuous cyclic cochains to cyclic cochains. -/
def continuousCyclicCochains.toCyclicCochains (n : ℕ) :
    continuousCyclicCochains R A M n →ₗ[R] cyclicCochains R A M n :=
  ContinuousMultilinearMap.toMultilinearMapLinear.restrict fun _ hφ ↦
    (mem_continuousCyclicCochains_iff R A M).1 hφ

/-- Forgetting continuity keeps the underlying multilinear map. -/
@[simp]
theorem continuousCyclicCochains.coe_toCyclicCochains {n : ℕ}
    (φ : continuousCyclicCochains R A M n) :
    (toCyclicCochains R A M n φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) =
      (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M).toMultilinearMap :=
  (rfl)

/-- Forgetting continuity is injective. -/
theorem continuousCyclicCochains.toCyclicCochains_injective (n : ℕ) :
    Function.Injective (toCyclicCochains R A M n) := fun _ _ h ↦
  Subtype.ext (ContinuousMultilinearMap.toMultilinearMap_injective (congrArg Subtype.val h))

end Forget

section ForgetAlgebra

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

open continuousCyclicCochains

/-- Forgetting continuity commutes with the Hochschild coboundary. -/
theorem continuousCyclicCochains.toCyclicCochains_continuousCyclicHochschildCoboundary {n : ℕ}
    (φ : continuousCyclicCochains R A M n) :
    toCyclicCochains R A M (n + 1) (continuousCyclicHochschildCoboundary R A M n φ) =
      cyclicHochschildCoboundary R A M n (toCyclicCochains R A M n φ) := by
  ext : 1
  simp

/-- A continuous cyclic cocycle is a cyclic cocycle. -/
theorem continuousCyclicCochains.toCyclicCochains_mem_cyclicCocycles {n : ℕ}
    {φ : continuousCyclicCochains R A M n} (hφ : φ ∈ continuousCyclicCocycles R A M n) :
    toCyclicCochains R A M n φ ∈ cyclicCocycles R A M n := by
  rw [mem_continuousCyclicCocycles_iff_hochschildCoboundary] at hφ
  simpa using hφ

/-- A continuous cyclic coboundary is a cyclic coboundary. -/
theorem continuousCyclicCochains.toCyclicCochains_mem_cyclicCoboundaries {n : ℕ}
    {φ : continuousCyclicCochains R A M n} (hφ : φ ∈ continuousCyclicCoboundaries R A M n) :
    toCyclicCochains R A M n φ ∈ cyclicCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [continuousCyclicCoboundaries_zero, Submodule.mem_bot] at hφ
    simp [hφ]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_continuousCyclicCoboundaries_succ_iff R A M).1 hφ
    exact (mem_cyclicCoboundaries_succ_iff R A M).2 ⟨toCyclicCochains R A M n ψ,
      (toCyclicCochains_continuousCyclicHochschildCoboundary ψ).symm⟩

end ForgetAlgebra

section Pullback

variable {R A B C : Type*} (M : Type*) [Semiring R] [AddCommMonoid A] [Module R A]
  [TopologicalSpace A] [AddCommMonoid B] [Module R B] [TopologicalSpace B] [AddCommMonoid C]
  [Module R C] [TopologicalSpace C] [AddCommGroup M] [Module R M] [SMulCommClass R R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]

/-- The pullback `φ ↦ φ ∘ (f × ⋯ × f)` of continuous cyclic cochains along a continuous linear
map. -/
def continuousCyclicCochainsMap (f : A →L[R] B) (n : ℕ) :
    continuousCyclicCochains R B M n →ₗ[R] continuousCyclicCochains R A M n where
  toFun φ := ⟨(φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ B) M).compContinuousLinearMap
      fun _ ↦ f, (mem_continuousCyclicCochains_iff R A M).2 <|
        compLinearMap_mem_cyclicCochains (f : A →ₗ[R] B)
          ((mem_continuousCyclicCochains_iff R B M).1 φ.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {M}

/-- The pullback of a continuous cyclic cochain evaluates it on the images of the arguments. -/
@[simp]
theorem coe_continuousCyclicCochainsMap_apply (f : A →L[R] B) {n : ℕ}
    (φ : continuousCyclicCochains R B M n) :
    (continuousCyclicCochainsMap M f n φ : ContinuousMultilinearMap R
        (fun _ : Fin (n + 1) ↦ A) M) =
      (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ B) M).compContinuousLinearMap
        fun _ ↦ f :=
  (rfl)

/-- Forgetting continuity commutes with pullback. -/
theorem continuousCyclicCochains.toCyclicCochains_continuousCyclicCochainsMap (f : A →L[R] B)
    {n : ℕ} (φ : continuousCyclicCochains R B M n) :
    continuousCyclicCochains.toCyclicCochains R A M n (continuousCyclicCochainsMap M f n φ) =
      cyclicCochainsMap M (f : A →ₗ[R] B) n
        (continuousCyclicCochains.toCyclicCochains R B M n φ) := by
  ext a
  simp

variable (M) in
/-- Pulling back along the identity is the identity. -/
@[simp]
theorem continuousCyclicCochainsMap_id (n : ℕ) :
    continuousCyclicCochainsMap M (ContinuousLinearMap.id R A) n = LinearMap.id := by
  ext φ a
  simp

variable (M) in
/-- Pulling back along a composite is the composite of the pullbacks, in the opposite order. -/
theorem continuousCyclicCochainsMap_comp (f : A →L[R] B) (g : B →L[R] C) (n : ℕ) :
    continuousCyclicCochainsMap M (g.comp f) n =
      continuousCyclicCochainsMap M f n ∘ₗ continuousCyclicCochainsMap M g n := by
  ext φ a
  simp

end Pullback

section PullbackAlgebra

variable {R A B M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A]
  [NonUnitalNonAssocSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [TopologicalSpace B] [ContinuousMul B] [AddCommGroup M] [Module R M] [SMulCommClass R R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- Pulling continuous cyclic cochains back along a continuous homomorphism of nonunital
algebras commutes with the Hochschild coboundary. -/
theorem continuousCyclicHochschildCoboundary_continuousCyclicCochainsMap (f : A →ₙₐ[R] B)
    (hf : Continuous f) {n : ℕ} (φ : continuousCyclicCochains R B M n) :
    continuousCyclicHochschildCoboundary R A M n
        (continuousCyclicCochainsMap M ⟨(f : A →ₗ[R] B), hf⟩ n φ) =
      continuousCyclicCochainsMap M ⟨(f : A →ₗ[R] B), hf⟩ (n + 1)
        (continuousCyclicHochschildCoboundary R B M n φ) :=
  continuousCyclicCochains.toCyclicCochains_injective R A M (n + 1) <| by
    rw [continuousCyclicCochains.toCyclicCochains_continuousCyclicHochschildCoboundary,
      continuousCyclicCochains.toCyclicCochains_continuousCyclicCochainsMap,
      continuousCyclicCochains.toCyclicCochains_continuousCyclicCochainsMap,
      continuousCyclicCochains.toCyclicCochains_continuousCyclicHochschildCoboundary]
    exact cyclicHochschildCoboundary_cyclicCochainsMap f _

/-- Pulling back a continuous cyclic cocycle along a continuous homomorphism of nonunital
algebras gives a continuous cyclic cocycle. -/
theorem continuousCyclicCochainsMap_mem_continuousCyclicCocycles (f : A →ₙₐ[R] B)
    (hf : Continuous f) {n : ℕ} {φ : continuousCyclicCochains R B M n}
    (hφ : φ ∈ continuousCyclicCocycles R B M n) :
    continuousCyclicCochainsMap M ⟨(f : A →ₗ[R] B), hf⟩ n φ ∈ continuousCyclicCocycles R A M n := by
  rw [continuousCyclicCocycles, LinearMap.mem_ker,
    continuousCyclicHochschildCoboundary_continuousCyclicCochainsMap f hf,
    LinearMap.mem_ker.1 hφ, map_zero]

/-- Pulling back a continuous cyclic coboundary along a continuous homomorphism of nonunital
algebras gives a continuous cyclic coboundary. -/
theorem continuousCyclicCochainsMap_mem_continuousCyclicCoboundaries (f : A →ₙₐ[R] B)
    (hf : Continuous f) {n : ℕ} {φ : continuousCyclicCochains R B M n}
    (hφ : φ ∈ continuousCyclicCoboundaries R B M n) :
    continuousCyclicCochainsMap M ⟨(f : A →ₗ[R] B), hf⟩ n φ ∈
      continuousCyclicCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [continuousCyclicCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_continuousCyclicCoboundaries_succ_iff R B M).1 hφ
    exact (mem_continuousCyclicCoboundaries_succ_iff R A M).2
      ⟨_, continuousCyclicHochschildCoboundary_continuousCyclicCochainsMap f hf ψ⟩

end PullbackAlgebra

section Cohomology

variable (R A M : Type*) [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The continuous cyclic cohomology `HCⁿ_cont(A; M)` of a topological algebra `A` with jointly
continuous multiplication: the quotient of the continuous cyclic cocycles by the continuous
cyclic coboundaries. Over a normed field it carries the quotient topology of the topology of
bounded convergence on cochains.

This is the continuous cyclic cohomology of a unital algebra `A`. For a nonunital algebra, cyclic
cohomology is instead defined through the forced unitization, and this quotient is only the
cohomology of the naive continuous cyclic complex. -/
abbrev continuousCyclicCohomology (n : ℕ) :=
  -- Instance search does not find this quotient instance by itself. The cocycles are a
  -- submodule of a submodule elaborated with only its additive monoid structure, and Mathlib's
  -- `AddCommGroup` on continuous multilinear maps needs an additive group domain.
  @HasQuotient.Quotient _ _ (@Submodule.hasQuotient R (continuousCyclicCocycles R A M n) _ _ _)
    ((continuousCyclicCoboundaries R A M n).comap (continuousCyclicCocycles R A M n).subtype)

namespace continuousCyclicCohomology

/-- The continuous cyclic cohomology class of a continuous cyclic cocycle. -/
def mk (n : ℕ) : continuousCyclicCocycles R A M n →ₗ[R] continuousCyclicCohomology R A M n :=
  Submodule.mkQ _

/-- Every continuous cyclic cohomology class is the class of a continuous cyclic cocycle. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) :=
  Submodule.mkQ_surjective _

variable {R A M}

/-- A continuous cyclic cocycle has zero class exactly when it is a continuous cyclic
coboundary. -/
@[simp]
theorem mk_eq_zero_iff {n : ℕ} (φ : continuousCyclicCocycles R A M n) :
    mk R A M n φ = 0 ↔
      (φ : continuousCyclicCochains R A M n) ∈ continuousCyclicCoboundaries R A M n :=
  Submodule.Quotient.mk_eq_zero _

/-- Two continuous cyclic cocycles have the same class exactly when they differ by a continuous
cyclic coboundary. -/
theorem mk_eq_mk_iff {n : ℕ} (φ ψ : continuousCyclicCocycles R A M n) :
    mk R A M n φ = mk R A M n ψ ↔
      (φ : continuousCyclicCochains R A M n) - ψ ∈ continuousCyclicCoboundaries R A M n :=
  Submodule.Quotient.eq _

/-- Two linear maps out of continuous cyclic cohomology agree once they agree on classes of
continuous cocycles. -/
@[ext]
theorem linearMap_ext {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    {f g : continuousCyclicCohomology R A M n →ₗ[R] N} (h : f ∘ₗ mk R A M n = g ∘ₗ mk R A M n) :
    f = g :=
  Submodule.linearMap_qext _ h

section Desc

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- A linear map on continuous cyclic cocycles that vanishes on continuous cyclic coboundaries
descends to continuous cyclic cohomology. -/
def desc (n : ℕ) (f : continuousCyclicCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : continuousCyclicCocycles R A M n,
      (φ : continuousCyclicCochains R A M n) ∈ continuousCyclicCoboundaries R A M n → f φ = 0) :
    continuousCyclicCohomology R A M n →ₗ[R] N :=
  Submodule.liftQ _ f fun φ hφ ↦ hf φ hφ

/-- The descended map sends the class of a continuous cocycle to the value of the original
map. -/
@[simp]
theorem desc_mk (n : ℕ) (f : continuousCyclicCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : continuousCyclicCocycles R A M n,
      (φ : continuousCyclicCochains R A M n) ∈ continuousCyclicCoboundaries R A M n → f φ = 0)
    (φ : continuousCyclicCocycles R A M n) :
    desc n f hf (mk R A M n φ) = f φ :=
  Submodule.liftQ_apply _ _ _

/-- The descended map composed with the class map is the original map. -/
@[simp]
theorem desc_comp_mk (n : ℕ) (f : continuousCyclicCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ : continuousCyclicCocycles R A M n,
      (φ : continuousCyclicCochains R A M n) ∈ continuousCyclicCoboundaries R A M n → f φ = 0) :
    desc n f hf ∘ₗ mk R A M n = f :=
  LinearMap.ext (desc_mk n f hf)

end Desc

variable (R A M) in
/-- `HC⁰_cont(A; M)` is the module of continuous cyclic `0`-cocycles, that is, of continuous
`M`-valued traces on `A` (`mem_continuousCyclicCocycles_zero_iff`): in degree zero there are no
continuous coboundaries. -/
def zeroEquiv : continuousCyclicCocycles R A M 0 ≃ₗ[R] continuousCyclicCohomology R A M 0 :=
  LinearEquiv.ofBijective (mk R A M 0)
    ⟨(injective_iff_map_eq_zero _).2 fun φ hφ ↦ by
      rw [mk_eq_zero_iff, continuousCyclicCoboundaries_zero, Submodule.mem_bot] at hφ
      exact Subtype.ext hφ, mk_surjective R A M 0⟩

/-- The equivalence `zeroEquiv` sends a continuous cyclic `0`-cocycle to its class. -/
@[simp]
theorem zeroEquiv_apply (φ : continuousCyclicCocycles R A M 0) :
    zeroEquiv R A M φ = mk R A M 0 φ :=
  (rfl)

section Map

variable {B C : Type*} [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [TopologicalSpace B] [ContinuousMul B] [NonUnitalRing C] [Module R C] [IsScalarTower R C C]
  [SMulCommClass R C C] [TopologicalSpace C] [ContinuousMul C]

variable (M) in
/-- The map on continuous cyclic cohomology induced by a continuous homomorphism of nonunital
algebras. For unital algebras the homomorphism need not preserve the unit. -/
def map (f : A →ₙₐ[R] B) (hf : Continuous f) (n : ℕ) :
    continuousCyclicCohomology R B M n →ₗ[R] continuousCyclicCohomology R A M n :=
  desc n (mk R A M n ∘ₗ ((continuousCyclicCochainsMap M ⟨(f : A →ₗ[R] B), hf⟩ n).restrict
      fun _ hφ ↦ continuousCyclicCochainsMap_mem_continuousCyclicCocycles f hf hφ))
    fun _ hφ ↦ (mk_eq_zero_iff _).2
      (continuousCyclicCochainsMap_mem_continuousCyclicCoboundaries f hf hφ)

/-- The induced map sends the class of a continuous cocycle to the class of its pullback. -/
@[simp]
theorem map_mk (f : A →ₙₐ[R] B) (hf : Continuous f) {n : ℕ}
    (φ : continuousCyclicCocycles R B M n) :
    map M f hf n (mk R B M n φ) =
      mk R A M n ⟨continuousCyclicCochainsMap M ⟨(f : A →ₗ[R] B), hf⟩ n φ,
        continuousCyclicCochainsMap_mem_continuousCyclicCocycles f hf φ.2⟩ :=
  desc_mk _ _ _ _

/-- The identity homomorphism induces the identity on continuous cyclic cohomology. The
continuity proof is a hypothesis so that the lemma applies to whichever proof appears. -/
@[simp]
theorem map_id (h : Continuous (NonUnitalAlgHom.id R A)) (n : ℕ) :
    map M (NonUnitalAlgHom.id R A) h n = LinearMap.id :=
  linearMap_ext <| LinearMap.ext fun φ ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, map_mk, LinearMap.id_apply]
    exact congrArg _ (Subtype.ext (LinearMap.congr_fun (continuousCyclicCochainsMap_id M n) φ.1))

/-- Continuous cyclic cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (hf : Continuous f) (g : B →ₙₐ[R] C) (hg : Continuous g)
    (hgf : Continuous (g.comp f)) (n : ℕ) :
    map M (g.comp f) hgf n = map M f hf n ∘ₗ map M g hg n :=
  linearMap_ext <| LinearMap.ext fun φ ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_mk, map_mk, map_mk]
    exact congrArg _ (Subtype.ext (LinearMap.congr_fun (continuousCyclicCochainsMap_comp M
      ⟨(f : A →ₗ[R] B), hf⟩ ⟨(g : B →ₗ[R] C), hg⟩ n) φ.1))

end Map

end continuousCyclicCohomology

end Cohomology

section Comparison

variable {R : Type*} {A : Type u} {M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [TopologicalSpace A] [ContinuousMul A] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

namespace continuousCyclicCohomology

variable (R A M) in
/-- The comparison map `HCⁿ_cont(A; M) → HCⁿ(A; M)` from continuous to algebraic cyclic
cohomology, induced by forgetting continuity of cocycles. -/
def toCyclicCohomology (n : ℕ) :
    continuousCyclicCohomology R A M n →ₗ[R] cyclicCohomology R A M n :=
  desc n (cyclicCohomology.mk R A M n ∘ₗ
      ((continuousCyclicCochains.toCyclicCochains R A M n).restrict fun _ hφ ↦
        continuousCyclicCochains.toCyclicCochains_mem_cyclicCocycles hφ))
    fun _ hφ ↦ (cyclicCohomology.mk_eq_zero_iff R A M n _).2
      (continuousCyclicCochains.toCyclicCochains_mem_cyclicCoboundaries hφ)

/-- The comparison map sends the class of a continuous cocycle to the class of its underlying
algebraic cocycle. -/
@[simp]
theorem toCyclicCohomology_mk {n : ℕ} (φ : continuousCyclicCocycles R A M n) :
    toCyclicCohomology R A M n (mk R A M n φ) =
      cyclicCohomology.mk R A M n
        ⟨continuousCyclicCochains.toCyclicCochains R A M n φ,
          continuousCyclicCochains.toCyclicCochains_mem_cyclicCocycles φ.2⟩ :=
  desc_mk _ _ _ _

/-- The comparison with algebraic cyclic cohomology is natural for continuous homomorphisms. -/
theorem toCyclicCohomology_map {B : Type u} [Ring B] [Algebra R B] [TopologicalSpace B]
    [ContinuousMul B] (f : A →ₙₐ[R] B) (hf : Continuous f) (n : ℕ)
    (z : continuousCyclicCohomology R B M n) :
    toCyclicCohomology R A M n (map M f hf n z) =
      cyclicCohomology.map M f n (toCyclicCohomology R B M n z) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R B M n z
  rw [map_mk, toCyclicCohomology_mk, toCyclicCohomology_mk, cyclicCohomology.map_mk]
  exact congrArg _ (Subtype.ext
    (continuousCyclicCochains.toCyclicCochains_continuousCyclicCochainsMap _ φ.1))

end continuousCyclicCohomology

end Comparison

section Topology

variable (𝕜 A M : Type*) [NormedField 𝕜] [NonUnitalRing A] [Module 𝕜 A] [IsScalarTower 𝕜 A A]
  [SMulCommClass 𝕜 A A] [TopologicalSpace A] [ContinuousMul A] [AddCommGroup M] [Module 𝕜 M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

namespace continuousCyclicCohomology

/-- The class map is an open quotient map onto continuous cyclic cohomology with its quotient
topology. -/
theorem isOpenQuotientMap_mk (n : ℕ) : IsOpenQuotientMap (mk 𝕜 A M n) :=
  Submodule.isOpenQuotientMap_mkQ _

/-- The class map is continuous for the quotient topology. -/
@[fun_prop]
theorem continuous_mk (n : ℕ) : Continuous (mk 𝕜 A M n) :=
  (isOpenQuotientMap_mk 𝕜 A M n).continuous

variable {𝕜 A M}

/-- Pullback along a continuous homomorphism is continuous for the quotient topologies. -/
theorem continuous_map {B : Type*} [NonUnitalRing B] [Module 𝕜 B] [IsScalarTower 𝕜 B B]
    [SMulCommClass 𝕜 B B] [TopologicalSpace B] [ContinuousMul B] (f : A →ₙₐ[𝕜] B)
    (hf : Continuous f) (n : ℕ) :
    Continuous (map M f hf n) := by
  refine (isOpenQuotientMap_mk 𝕜 B M n).isQuotientMap.continuous_iff.2 ?_
  refine (continuous_mk 𝕜 A M n).comp (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _)
  exact (ContinuousMultilinearMap.continuous_precomp fun _ ↦ ⟨(f : A →ₗ[𝕜] B), hf⟩).comp
    (continuous_subtype_val.comp continuous_subtype_val)

end continuousCyclicCohomology

variable [ContinuousSMul 𝕜 A] [T2Space M]

/-- For Hausdorff `M`, the continuous cyclic cocycles are closed in the continuous cyclic
cochains. -/
theorem isClosed_continuousCyclicCocycles (n : ℕ) :
    IsClosed (continuousCyclicCocycles 𝕜 A M n : Set (continuousCyclicCochains 𝕜 A M n)) :=
  isClosed_singleton.preimage (continuous_continuousCyclicHochschildCoboundary 𝕜 A M n)

namespace continuousCyclicCohomology

/-- For Hausdorff `M`, continuous cyclic cohomology is Hausdorff exactly when the continuous
cyclic coboundaries are closed in the continuous cyclic cochains. -/
theorem t2Space_iff (n : ℕ) :
    T2Space (continuousCyclicCohomology 𝕜 A M n) ↔
      IsClosed (continuousCyclicCoboundaries 𝕜 A M n :
        Set (continuousCyclicCochains 𝕜 A M n)) := by
  let S := (continuousCyclicCoboundaries 𝕜 A M n).comap (continuousCyclicCocycles 𝕜 A M n).subtype
  have hclosed : IsClosed (S : Set (continuousCyclicCocycles 𝕜 A M n)) ↔
      IsClosed (continuousCyclicCoboundaries 𝕜 A M n : Set (continuousCyclicCochains 𝕜 A M n)) := by
    rw [(isClosed_continuousCyclicCocycles 𝕜 A M n).isClosedEmbedding_subtypeVal
      |>.isClosed_iff_image_isClosed]
    -- `S` is the preimage of the coboundaries, which lie in the cocycles.
    exact iff_of_eq (congrArg IsClosed (Set.image_preimage_eq_of_subset fun x hx ↦
      ⟨⟨x, continuousCyclicCoboundaries_le_continuousCyclicCocycles 𝕜 A M n hx⟩, rfl⟩))
  rw [← hclosed]
  -- The quotient by a submodule is the quotient by its additive subgroup.
  refine ⟨fun _ ↦ (QuotientAddGroup.t1Space_iff (G := continuousCyclicCocycles 𝕜 A M n)
    (N := S.toAddSubgroup)).1 ?_, fun hS ↦ ?_⟩
  · exact inferInstanceAs (T1Space (continuousCyclicCohomology 𝕜 A M n))
  · have := (QuotientAddGroup.t1Space_iff (G := continuousCyclicCocycles 𝕜 A M n)
      (N := S.toAddSubgroup)).2 hS
    -- Naming the group instance keeps instance search for separation axioms fast.
    have : IsTopologicalAddGroup (continuousCyclicCocycles 𝕜 A M n ⧸ S.toAddSubgroup) :=
      QuotientAddGroup.instIsTopologicalAddGroup _
    have : T2Space (continuousCyclicCocycles 𝕜 A M n ⧸ S.toAddSubgroup) := inferInstance
    exact this

end continuousCyclicCohomology

end Topology

end TauCeti
