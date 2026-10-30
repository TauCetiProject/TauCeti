/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import TauCeti.RingTheory.CyclicCohomology.OperatorTopology
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Continuous cyclic cohomology with its quotient topology

For a unital topological algebra, continuous cyclic cohomology is the quotient of
continuous cyclic cocycles by continuous cyclic coboundaries. Cochains carry uniform
convergence on products of bounded sets, cocycles have the subspace topology, and
cohomology has the quotient topology. Cocycles form a closed subspace when the
coefficient space is Hausdorff and scalar multiplication on the algebra is continuous.
We do not close the space of coboundaries or assume that cohomology is Hausdorff.

The class map is an open quotient map. Its continuous linear universal property is
`continuousCyclicCohomology.desc`, and `continuousCyclicCohomology.homologyEquiv`
identifies this explicit quotient with the cohomology of the native cyclic cochain
complex. In degree zero, the class map identifies cohomology with the continuous
traces. No local convexity or completeness assumption is needed for these constructions.
For Hausdorff coefficients, `continuousCyclicCohomology.t2Space_iff` shows that cohomology is
Hausdorff exactly when the continuous coboundaries are closed.

Forgetting continuity sends continuous cocycles to cocycles and continuous coboundaries to
coboundaries, so it induces the comparison map
`continuousCyclicCohomology.toCyclicCohomology` to algebraic cyclic cohomology. This map need
not be injective or surjective. Continuous homomorphisms of nonunital algebras pull continuous
cyclic cohomology back by continuous linear maps (`continuousCyclicCohomology.map`),
functorially and compatibly with the comparison map.

The underlying complex is also defined for nonunital algebras; its cohomology is not
called continuous cyclic cohomology here. For nonunital algebras the relative
forced-unitization construction is needed instead.

## References

* A. Connes, *Noncommutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II,
  §§1–2.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.

The topology and quotient maps use Mathlib's `ContinuousMultilinearMap` and
`Submodule.mkQL`. The comparison with categorical cohomology uses
`HomologicalComplex.moduleCatCohomologyClassOfIso`.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

section Nonunital

variable (𝕜 A M : Type*) [NormedField 𝕜] [NonUnitalRing A] [Module 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [TopologicalSpace A] [ContinuousMul A]
  [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul 𝕜 M]

/-- Continuous cyclic cocycles are the kernel of the continuous cyclic differential. -/
def continuousCyclicCocycles (n : ℕ) : Submodule 𝕜 (continuousCyclicCochains 𝕜 A M n) :=
  (continuousCyclicHochschildCoboundary 𝕜 A M n).ker

/-- Continuous cyclic cocycles inherit the additive group of continuous cochains. -/
instance continuousCyclicCocyclesAddCommGroup (n : ℕ) :
    AddCommGroup (continuousCyclicCocycles 𝕜 A M n) :=
  (continuousCyclicCocycles 𝕜 A M n).addCommGroup

/-- Cocycles carry the induced topological additive group structure. -/
instance continuousCyclicCocyclesIsTopologicalAddGroup (n : ℕ) :
    IsTopologicalAddGroup (continuousCyclicCocycles 𝕜 A M n) :=
  Submodule.isTopologicalAddGroup _

/-- A continuous cyclic cochain is a cocycle exactly when its coboundary vanishes. -/
@[simp]
theorem mem_continuousCyclicCocycles_iff {n : ℕ} {φ : continuousCyclicCochains 𝕜 A M n} :
    φ ∈ continuousCyclicCocycles 𝕜 A M n ↔
      continuousCyclicHochschildCoboundary 𝕜 A M n φ = 0 :=
  LinearMap.mem_ker

/-- A continuous cyclic cochain is a continuous cocycle exactly when its underlying algebraic
cyclic cochain is a cocycle. -/
theorem mem_continuousCyclicCocycles_iff_hochschildCoboundary {n : ℕ}
    {φ : continuousCyclicCochains 𝕜 A M n} :
    φ ∈ continuousCyclicCocycles 𝕜 A M n ↔
      hochschildCoboundary 𝕜 A M n (φ : ContinuousMultilinearMap 𝕜
        (fun _ : Fin (n + 1) ↦ A) M).toMultilinearMap = 0 := by
  rw [mem_continuousCyclicCocycles_iff, ← Subtype.val_inj]
  simp [← ContinuousMultilinearMap.toMultilinearMap_injective.eq_iff]

/-- Continuous cyclic zero-cocycles are precisely continuous traces. -/
theorem mem_continuousCyclicCocycles_zero_iff {φ : continuousCyclicCochains 𝕜 A M 0} :
    φ ∈ continuousCyclicCocycles 𝕜 A M 0 ↔
      ∀ x y : A, φ.1 (fun _ ↦ x * y) = φ.1 (fun _ ↦ y * x) := by
  rw [mem_continuousCyclicCocycles_iff, ← Subtype.val_inj]
  simp [← ContinuousMultilinearMap.toMultilinearMap_injective.eq_iff,
    hochschildCoboundary_zero_eq_zero_iff]

/-- Continuous cyclic coboundaries: zero in degree zero and the actual differential range
in positive degree, not its closure. -/
def continuousCyclicCoboundaries : (n : ℕ) → Submodule 𝕜 (continuousCyclicCochains 𝕜 A M n)
  | 0 => ⊥
  | n + 1 => (continuousCyclicHochschildCoboundary 𝕜 A M n).range

@[simp]
theorem continuousCyclicCoboundaries_zero : continuousCyclicCoboundaries 𝕜 A M 0 = ⊥ :=
  (rfl)

theorem continuousCyclicCoboundaries_succ (n : ℕ) :
    continuousCyclicCoboundaries 𝕜 A M (n + 1) =
      (continuousCyclicHochschildCoboundary 𝕜 A M n).range := (rfl)

@[simp]
theorem mem_continuousCyclicCoboundaries_succ_iff {n : ℕ}
    {φ : continuousCyclicCochains 𝕜 A M (n + 1)} :
    φ ∈ continuousCyclicCoboundaries 𝕜 A M (n + 1) ↔
      ∃ ψ, continuousCyclicHochschildCoboundary 𝕜 A M n ψ = φ :=
  LinearMap.mem_range

/-- The square-zero identity puts continuous coboundaries inside continuous cocycles. -/
theorem continuousCyclicCoboundaries_le_continuousCyclicCocycles (n : ℕ) :
    continuousCyclicCoboundaries 𝕜 A M n ≤ continuousCyclicCocycles 𝕜 A M n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨φ, rfl⟩
    simp

/-- The native cochain complex of continuous cyclic cochains with Hochschild differential. -/
def continuousCyclicCochainComplex : CochainComplex (ModuleCat 𝕜) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of 𝕜 (continuousCyclicCochains 𝕜 A M n))
    (fun n ↦ ModuleCat.ofHom (continuousCyclicHochschildCoboundary 𝕜 A M n))
    (fun n ↦ by
      apply ModuleCat.hom_ext
      exact LinearMap.ext
        (continuousCyclicHochschildCoboundary_continuousCyclicHochschildCoboundary 𝕜 A M))

/-- Identify the term of the native complex with the continuous cyclic cochain module. -/
def continuousCyclicCochainComplexXIso (n : ℕ) :
    (continuousCyclicCochainComplex 𝕜 A M).X n ≅
      ModuleCat.of 𝕜 (continuousCyclicCochains 𝕜 A M n) := Iso.refl _

/-- Under the carrier identifications, the complex differential is the continuous
cyclic Hochschild coboundary. -/
@[reassoc]
theorem continuousCyclicCochainComplex_d (n : ℕ) :
    (continuousCyclicCochainComplex 𝕜 A M).d n (n + 1) ≫
        (continuousCyclicCochainComplexXIso 𝕜 A M (n + 1)).hom =
      (continuousCyclicCochainComplexXIso 𝕜 A M n).hom ≫
        ModuleCat.ofHom (continuousCyclicHochschildCoboundary 𝕜 A M n) := by
  simp [continuousCyclicCochainComplex, continuousCyclicCochainComplexXIso]

/-- With Hausdorff coefficients, continuous cyclic cocycles form a closed subspace. -/
theorem isClosed_continuousCyclicCocycles [ContinuousSMul 𝕜 A] [T2Space M] (n : ℕ) :
    IsClosed (continuousCyclicCocycles 𝕜 A M n : Set (continuousCyclicCochains 𝕜 A M n)) :=
  isClosed_singleton.preimage (continuous_continuousCyclicHochschildCoboundary 𝕜 A M n)

end Nonunital

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

/-- Forgetting continuity commutes with the Hochschild coboundary. -/
theorem continuousCyclicCochains.toCyclicCochains_continuousCyclicHochschildCoboundary {n : ℕ}
    (φ : continuousCyclicCochains R A M n) :
    toCyclicCochains R A M (n + 1) (continuousCyclicHochschildCoboundary R A M n φ) =
      cyclicHochschildCoboundary R A M n (toCyclicCochains R A M n φ) := by
  ext : 1
  simp

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

section PullbackTopology

variable {𝕜 A B M : Type*} [NormedField 𝕜] [AddCommGroup A] [Module 𝕜 A] [TopologicalSpace A]
  [AddCommGroup B] [Module 𝕜 B] [TopologicalSpace B] [AddCommGroup M] [Module 𝕜 M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

/-- Pullback of continuous cyclic cochains is continuous for bounded convergence. -/
theorem continuous_continuousCyclicCochainsMap (f : A →L[𝕜] B) (n : ℕ) :
    Continuous (continuousCyclicCochainsMap M f n) :=
  ((ContinuousMultilinearMap.continuous_precomp fun _ ↦ f).comp
    continuous_subtype_val).subtype_mk _

end PullbackTopology

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

end PullbackAlgebra

section NonunitalMaps

variable {𝕜 A B M : Type*} [NormedField 𝕜] [NonUnitalRing A] [Module 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [TopologicalSpace A] [ContinuousMul A]
  [NonUnitalRing B] [Module 𝕜 B] [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
  [TopologicalSpace B] [ContinuousMul B] [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

open continuousCyclicCochains

/-- A continuous cyclic cocycle is a cyclic cocycle. -/
theorem continuousCyclicCochains.toCyclicCochains_mem_cyclicCocycles {n : ℕ}
    {φ : continuousCyclicCochains 𝕜 A M n} (hφ : φ ∈ continuousCyclicCocycles 𝕜 A M n) :
    toCyclicCochains 𝕜 A M n φ ∈ cyclicCocycles 𝕜 A M n := by
  rw [mem_continuousCyclicCocycles_iff_hochschildCoboundary] at hφ
  simpa using hφ

/-- A continuous cyclic coboundary is a cyclic coboundary. -/
theorem continuousCyclicCochains.toCyclicCochains_mem_cyclicCoboundaries {n : ℕ}
    {φ : continuousCyclicCochains 𝕜 A M n} (hφ : φ ∈ continuousCyclicCoboundaries 𝕜 A M n) :
    toCyclicCochains 𝕜 A M n φ ∈ cyclicCoboundaries 𝕜 A M n := by
  cases n with
  | zero =>
    rw [continuousCyclicCoboundaries_zero, Submodule.mem_bot] at hφ
    simp [hφ]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_continuousCyclicCoboundaries_succ_iff 𝕜 A M).1 hφ
    exact (mem_cyclicCoboundaries_succ_iff 𝕜 A M).2 ⟨toCyclicCochains 𝕜 A M n ψ,
      (toCyclicCochains_continuousCyclicHochschildCoboundary ψ).symm⟩

/-- Pulling back a continuous cyclic cocycle along a continuous homomorphism of nonunital
algebras gives a continuous cyclic cocycle. -/
theorem continuousCyclicCochainsMap_mem_continuousCyclicCocycles (f : A →ₙₐ[𝕜] B)
    (hf : Continuous f) {n : ℕ} {φ : continuousCyclicCochains 𝕜 B M n}
    (hφ : φ ∈ continuousCyclicCocycles 𝕜 B M n) :
    continuousCyclicCochainsMap M ⟨(f : A →ₗ[𝕜] B), hf⟩ n φ ∈
      continuousCyclicCocycles 𝕜 A M n := by
  rw [continuousCyclicCocycles, LinearMap.mem_ker,
    continuousCyclicHochschildCoboundary_continuousCyclicCochainsMap f hf,
    LinearMap.mem_ker.1 hφ, map_zero]

/-- Pulling back a continuous cyclic coboundary along a continuous homomorphism of nonunital
algebras gives a continuous cyclic coboundary. -/
theorem continuousCyclicCochainsMap_mem_continuousCyclicCoboundaries (f : A →ₙₐ[𝕜] B)
    (hf : Continuous f) {n : ℕ} {φ : continuousCyclicCochains 𝕜 B M n}
    (hφ : φ ∈ continuousCyclicCoboundaries 𝕜 B M n) :
    continuousCyclicCochainsMap M ⟨(f : A →ₗ[𝕜] B), hf⟩ n φ ∈
      continuousCyclicCoboundaries 𝕜 A M n := by
  cases n with
  | zero =>
    rw [continuousCyclicCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_continuousCyclicCoboundaries_succ_iff 𝕜 B M).1 hφ
    exact (mem_continuousCyclicCoboundaries_succ_iff 𝕜 A M).2
      ⟨_, continuousCyclicHochschildCoboundary_continuousCyclicCochainsMap f hf ψ⟩

end NonunitalMaps

section Unital

variable (𝕜 A M : Type*) [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
  [TopologicalSpace A] [ContinuousMul A] [AddCommGroup M] [Module 𝕜 M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

/-- Continuous cyclic cohomology of a unital topological algebra, with the quotient topology
on cocycles modulo actual coboundaries. This is the `M`-valued theory `HCⁿ(A; M)`;
for `𝕜 = M = ℂ` it is Connes' continuous `HCⁿ(A)`. -/
abbrev continuousCyclicCohomology (n : ℕ) :=
  (continuousCyclicCocycles 𝕜 A M n) ⧸
    (continuousCyclicCoboundaries 𝕜 A M n).comap (continuousCyclicCocycles 𝕜 A M n).subtype

namespace continuousCyclicCohomology

/-- The continuous linear class map from continuous cyclic cocycles to their cohomology. -/
def mk (n : ℕ) : continuousCyclicCocycles 𝕜 A M n →L[𝕜] continuousCyclicCohomology 𝕜 A M n :=
  Submodule.mkQL _

/-- Cohomology carries precisely the quotient topology, and its class map is open. -/
theorem isOpenQuotientMap_mk (n : ℕ) : IsOpenQuotientMap (mk 𝕜 A M n) :=
  Submodule.isOpenQuotientMap_mkQL _

/-- Every continuous cyclic cohomology class has a continuous cocycle representative. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk 𝕜 A M n) :=
  (isOpenQuotientMap_mk 𝕜 A M n).surjective

/-- A continuous cocycle represents zero precisely when it is an actual coboundary. -/
@[simp]
theorem mk_eq_zero_iff {n : ℕ} (φ : continuousCyclicCocycles 𝕜 A M n) :
    mk 𝕜 A M n φ = 0 ↔ φ.1 ∈ continuousCyclicCoboundaries 𝕜 A M n :=
  Submodule.Quotient.mk_eq_zero _

/-- Two continuous cocycles represent the same class exactly when their difference is a
continuous cyclic coboundary. -/
theorem mk_eq_mk_iff {n : ℕ} (φ ψ : continuousCyclicCocycles 𝕜 A M n) :
    mk 𝕜 A M n φ = mk 𝕜 A M n ψ ↔
      φ.1 - ψ.1 ∈ continuousCyclicCoboundaries 𝕜 A M n := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  simp

variable {𝕜 A M} {N : Type*} [AddCommGroup N] [Module 𝕜 N] [TopologicalSpace N]

/-- Descend a continuous linear map on cocycles which vanishes on coboundaries.
No separation hypothesis is imposed on the target. -/
def desc {n : ℕ} (f : continuousCyclicCocycles 𝕜 A M n →L[𝕜] N)
    (hf : ∀ φ, φ.1 ∈ continuousCyclicCoboundaries 𝕜 A M n → f φ = 0) :
    continuousCyclicCohomology 𝕜 A M n →L[𝕜] N :=
  Submodule.liftQL _ f hf

@[simp]
theorem desc_mk {n : ℕ} (f : continuousCyclicCocycles 𝕜 A M n →L[𝕜] N)
    (hf : ∀ φ, φ.1 ∈ continuousCyclicCoboundaries 𝕜 A M n → f φ = 0)
    (φ : continuousCyclicCocycles 𝕜 A M n) :
    desc f hf (mk 𝕜 A M n φ) = f φ := (rfl)

/-- Composing the descended map with the class map recovers the given map on cocycles. -/
@[simp]
theorem desc_comp_mk {n : ℕ} (f : continuousCyclicCocycles 𝕜 A M n →L[𝕜] N)
    (hf : ∀ φ, φ.1 ∈ continuousCyclicCoboundaries 𝕜 A M n → f φ = 0) :
    (desc f hf).comp (mk 𝕜 A M n) = f := by
  ext φ
  exact desc_mk f hf φ

/-- Continuous linear maps out of cohomology are determined by their values on cocycles. -/
@[ext]
theorem hom_ext {n : ℕ} {f g : continuousCyclicCohomology 𝕜 A M n →L[𝕜] N}
    (h : ∀ φ, f (mk 𝕜 A M n φ) = g (mk 𝕜 A M n φ)) : f = g :=
  ContinuousLinearMap.ext fun x ↦ by
    obtain ⟨φ, rfl⟩ := mk_surjective 𝕜 A M n x
    exact h φ

variable (𝕜 A M)

private theorem mem_cocycles_complex (n : ℕ) (φ : continuousCyclicCochains 𝕜 A M n) :
    φ ∈ continuousCyclicCocycles 𝕜 A M n ↔
      (continuousCyclicCochainComplex 𝕜 A M).d n (n + 1)
        ((continuousCyclicCochainComplexXIso 𝕜 A M n).inv φ) = 0 := by
  rw [mem_continuousCyclicCocycles_iff]
  exact ((continuousCyclicCochainComplex 𝕜 A M).moduleCat_d_inv_eq_zero_iff
    (continuousCyclicHochschildCoboundary 𝕜 A M)
    (continuousCyclicCochainComplex_d 𝕜 A M) φ).symm

private theorem mem_coboundaries_complex (n : ℕ) (φ : continuousCyclicCochains 𝕜 A M n) :
    φ ∈ continuousCyclicCoboundaries 𝕜 A M n ↔
      ∃ ψ : (continuousCyclicCochainComplex 𝕜 A M).X ((ComplexShape.up ℕ).prev n),
        (continuousCyclicCochainComplex 𝕜 A M).d ((ComplexShape.up ℕ).prev n) n ψ =
          (continuousCyclicCochainComplexXIso 𝕜 A M n).inv φ :=
  (continuousCyclicCochainComplex 𝕜 A M).moduleCat_mem_iff_exists_d_eq_inv
    (continuousCyclicCoboundaries 𝕜 A M) (continuousCyclicHochschildCoboundary 𝕜 A M)
    (continuousCyclicCochainComplex_d 𝕜 A M) (continuousCyclicCoboundaries_zero 𝕜 A M)
    (continuousCyclicCoboundaries_succ 𝕜 A M) n φ

private def classToHomology (n : ℕ) : continuousCyclicCocycles 𝕜 A M n →ₗ[𝕜]
    (continuousCyclicCochainComplex 𝕜 A M).homology n :=
  (continuousCyclicCochainComplex 𝕜 A M).moduleCatCohomologyClassOfIso
    (fun n ↦ continuousCyclicCochains 𝕜 A M n) (continuousCyclicCocycles 𝕜 A M)
    (continuousCyclicCochainComplexXIso 𝕜 A M) (mem_cocycles_complex 𝕜 A M) n

private theorem classToHomology_surjective (n : ℕ) :
    Function.Surjective (classToHomology 𝕜 A M n) := by
  unfold classToHomology
  exact (continuousCyclicCochainComplex 𝕜 A M).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ continuousCyclicCochains 𝕜 A M n) (continuousCyclicCocycles 𝕜 A M)
    (continuousCyclicCochainComplexXIso 𝕜 A M) (mem_cocycles_complex 𝕜 A M) n

private theorem classToHomology_eq_zero_iff (n : ℕ) (φ : continuousCyclicCocycles 𝕜 A M n) :
    classToHomology 𝕜 A M n φ = 0 ↔ φ.1 ∈ continuousCyclicCoboundaries 𝕜 A M n :=
  (continuousCyclicCochainComplex 𝕜 A M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ continuousCyclicCochains 𝕜 A M n) (continuousCyclicCocycles 𝕜 A M)
    (continuousCyclicCoboundaries 𝕜 A M) (continuousCyclicCochainComplexXIso 𝕜 A M)
    (mem_cocycles_complex 𝕜 A M) (mem_coboundaries_complex 𝕜 A M) n φ

/-- The quotient defining continuous cyclic cohomology is linearly equivalent to the native
cohomology of the continuous cyclic cochain complex. -/
def homologyEquiv (n : ℕ) : continuousCyclicCohomology 𝕜 A M n ≃ₗ[𝕜]
    (continuousCyclicCochainComplex 𝕜 A M).homology n :=
  (Submodule.quotEquivOfEq _ _ (by
    ext φ
    exact (classToHomology_eq_zero_iff 𝕜 A M n φ).symm)).trans
      ((classToHomology 𝕜 A M n).quotKerEquivOfSurjective
        (classToHomology_surjective 𝕜 A M n))

/-- The comparison sends a cocycle class to the class of the corresponding native cycle. -/
theorem homologyEquiv_mk_eq_homologyπ {n : ℕ} (φ : continuousCyclicCocycles 𝕜 A M n)
    (z : (continuousCyclicCochainComplex 𝕜 A M).cycles n)
    (hz : (continuousCyclicCochainComplexXIso 𝕜 A M n).hom
      ((continuousCyclicCochainComplex 𝕜 A M).iCycles n z) = φ.1) :
    homologyEquiv 𝕜 A M n (mk 𝕜 A M n φ) =
      (continuousCyclicCochainComplex 𝕜 A M).homologyπ n z := by
  have h : homologyEquiv 𝕜 A M n (mk 𝕜 A M n φ) = classToHomology 𝕜 A M n φ := by
    simp [homologyEquiv, mk, Submodule.quotEquivOfEq_mk]
  rw [h]
  exact (continuousCyclicCochainComplex 𝕜 A M).moduleCatCohomologyClassOfIso_eq_homologyπ
    (fun n ↦ continuousCyclicCochains 𝕜 A M n) (continuousCyclicCocycles 𝕜 A M)
    (continuousCyclicCochainComplexXIso 𝕜 A M) (mem_cocycles_complex 𝕜 A M) φ z hz

/-- There are no coboundaries to identify distinct continuous zero-cocycles. -/
theorem mk_zero_injective : Function.Injective (mk 𝕜 A M 0) := by
  apply (injective_iff_map_eq_zero _).2
  intro φ hφ
  apply Subtype.ext
  simpa using (mk_eq_zero_iff 𝕜 A M φ).1 hφ

/-- Degree-zero continuous cyclic cohomology is the space of continuous traces, with its
bounded-convergence subspace topology. -/
def zeroEquiv : continuousCyclicCocycles 𝕜 A M 0 ≃L[𝕜] continuousCyclicCohomology 𝕜 A M 0 :=
  ContinuousLinearEquiv.ofIsHomeomorph
    (LinearEquiv.ofBijective (mk 𝕜 A M 0).toLinearMap
      ⟨mk_zero_injective 𝕜 A M, mk_surjective 𝕜 A M 0⟩)
    (isHomeomorph_iff_isQuotientMap_injective.2
      ⟨(isOpenQuotientMap_mk 𝕜 A M 0).isQuotientMap, mk_zero_injective 𝕜 A M⟩)

@[simp]
theorem zeroEquiv_apply (φ : continuousCyclicCocycles 𝕜 A M 0) :
    zeroEquiv 𝕜 A M φ = mk 𝕜 A M 0 φ := (rfl)

@[simp]
theorem zeroEquiv_symm_mk (φ : continuousCyclicCocycles 𝕜 A M 0) :
    (zeroEquiv 𝕜 A M).symm (mk 𝕜 A M 0 φ) = φ :=
  (zeroEquiv 𝕜 A M).symm_apply_apply φ

variable [ContinuousSMul 𝕜 A] [T2Space M]

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

end Unital

section Maps

universe u

variable {𝕜 : Type*} {A B C : Type u} {M : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
  [TopologicalSpace A] [ContinuousMul A] [Ring B] [Algebra 𝕜 B] [TopologicalSpace B]
  [ContinuousMul B] [Ring C] [Algebra 𝕜 C] [TopologicalSpace C] [ContinuousMul C]
  [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul 𝕜 M]

namespace continuousCyclicCohomology

variable (M) in
/-- The continuous linear map on continuous cyclic cohomology induced by a continuous
homomorphism of nonunital algebras; the homomorphism need not preserve the unit. -/
def map (f : A →ₙₐ[𝕜] B) (hf : Continuous f) (n : ℕ) :
    continuousCyclicCohomology 𝕜 B M n →L[𝕜] continuousCyclicCohomology 𝕜 A M n :=
  desc ((mk 𝕜 A M n).comp
      ⟨(continuousCyclicCochainsMap M ⟨(f : A →ₗ[𝕜] B), hf⟩ n).restrict
        fun _ hφ ↦ continuousCyclicCochainsMap_mem_continuousCyclicCocycles f hf hφ,
        ((continuous_continuousCyclicCochainsMap _ n).comp
          continuous_subtype_val).subtype_mk _⟩)
    fun _ hφ ↦ (mk_eq_zero_iff 𝕜 A M _).2
      (continuousCyclicCochainsMap_mem_continuousCyclicCoboundaries f hf hφ)

/-- The induced map sends the class of a continuous cocycle to the class of its pullback. -/
@[simp]
theorem map_mk (f : A →ₙₐ[𝕜] B) (hf : Continuous f) {n : ℕ}
    (φ : continuousCyclicCocycles 𝕜 B M n) :
    map M f hf n (mk 𝕜 B M n φ) =
      mk 𝕜 A M n ⟨continuousCyclicCochainsMap M ⟨(f : A →ₗ[𝕜] B), hf⟩ n φ,
        continuousCyclicCochainsMap_mem_continuousCyclicCocycles f hf φ.2⟩ :=
  desc_mk _ _ _

/-- The identity homomorphism induces the identity on continuous cyclic cohomology. The
continuity proof is a hypothesis so that the lemma applies to whichever proof appears. -/
@[simp]
theorem map_id (h : Continuous (NonUnitalAlgHom.id 𝕜 A)) (n : ℕ) :
    map M (NonUnitalAlgHom.id 𝕜 A) h n = ContinuousLinearMap.id 𝕜 _ :=
  hom_ext fun φ ↦ by
    rw [map_mk, ContinuousLinearMap.id_apply]
    exact congrArg _ (Subtype.ext (LinearMap.congr_fun (continuousCyclicCochainsMap_id M n) φ.1))

/-- Continuous cyclic cohomology is contravariantly functorial. -/
theorem map_comp (f : A →ₙₐ[𝕜] B) (hf : Continuous f) (g : B →ₙₐ[𝕜] C) (hg : Continuous g)
    (hgf : Continuous (g.comp f)) (n : ℕ) :
    map M (g.comp f) hgf n = (map M f hf n).comp (map M g hg n) :=
  hom_ext fun φ ↦ by
    rw [ContinuousLinearMap.comp_apply, map_mk, map_mk, map_mk]
    exact congrArg _ (Subtype.ext (LinearMap.congr_fun (continuousCyclicCochainsMap_comp M
      ⟨(f : A →ₗ[𝕜] B), hf⟩ ⟨(g : B →ₗ[𝕜] C), hg⟩ n) φ.1))

variable (𝕜 A M) in
/-- The comparison map `HCⁿ_cont(A; M) → HCⁿ(A; M)` from continuous to algebraic cyclic
cohomology, induced by forgetting continuity of cocycles. -/
def toCyclicCohomology (n : ℕ) :
    continuousCyclicCohomology 𝕜 A M n →ₗ[𝕜] cyclicCohomology 𝕜 A M n :=
  Submodule.liftQ _ (cyclicCohomology.mk 𝕜 A M n ∘ₗ
      ((continuousCyclicCochains.toCyclicCochains 𝕜 A M n).restrict fun _ hφ ↦
        continuousCyclicCochains.toCyclicCochains_mem_cyclicCocycles hφ))
    fun _ hφ ↦ LinearMap.mem_ker.2 ((cyclicCohomology.mk_eq_zero_iff 𝕜 A M n _).2
      (continuousCyclicCochains.toCyclicCochains_mem_cyclicCoboundaries hφ))

/-- The comparison map sends the class of a continuous cocycle to the class of its underlying
algebraic cocycle. -/
@[simp]
theorem toCyclicCohomology_mk {n : ℕ} (φ : continuousCyclicCocycles 𝕜 A M n) :
    toCyclicCohomology 𝕜 A M n (mk 𝕜 A M n φ) =
      cyclicCohomology.mk 𝕜 A M n
        ⟨continuousCyclicCochains.toCyclicCochains 𝕜 A M n φ,
          continuousCyclicCochains.toCyclicCochains_mem_cyclicCocycles φ.2⟩ :=
  (rfl)

/-- The comparison with algebraic cyclic cohomology is natural for continuous homomorphisms. -/
theorem toCyclicCohomology_map (f : A →ₙₐ[𝕜] B) (hf : Continuous f) (n : ℕ)
    (z : continuousCyclicCohomology 𝕜 B M n) :
    toCyclicCohomology 𝕜 A M n (map M f hf n z) =
      cyclicCohomology.map M f n (toCyclicCohomology 𝕜 B M n z) := by
  obtain ⟨φ, rfl⟩ := mk_surjective 𝕜 B M n z
  rw [map_mk, toCyclicCohomology_mk, toCyclicCohomology_mk, cyclicCohomology.map_mk]
  exact congrArg _ (Subtype.ext
    (continuousCyclicCochains.toCyclicCochains_continuousCyclicCochainsMap _ φ.1))

end continuousCyclicCohomology

end Maps

end TauCeti
