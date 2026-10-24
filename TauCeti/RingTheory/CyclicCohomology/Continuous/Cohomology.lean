/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Continuous.Basic
public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Continuous cyclic cohomology

Jointly continuous cyclic cochains form a native cochain complex of modules. For a unital
algebra its cohomology is `continuousCyclicCohomology`. The class map is surjective, and its
kernel consists of actual continuous coboundaries, not their closure. Forgetting continuity
gives a cochain map to the algebraic cyclic complex and a comparison on cohomology.

Over a normed field we use Mathlib's topology of uniform convergence on bounded sets on
continuous multilinear maps and the resulting subspace topology on cocycles. Cohomology
carries the quotient topology under the class map. No closed-range or Hausdorff assertion is
made. In degree zero the cocycles are the continuous traces and the class map is bijective.

The cochain complex is available for nonunital algebras, but its cohomology is named here only
for unital algebras. Nonunital cyclic cohomology instead requires the relative complex of the
forced unitization.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.

The concrete class-map interface follows `TauCeti.RingTheory.CyclicCohomology.Cohomology`,
using `HomologicalComplex.moduleCatCohomologyClassOfIso` for the categorical identification.
The cochain topology is Mathlib's `ContinuousMultilinearMap.instTopologicalSpace`.
-/

public section

noncomputable section

open CategoryTheory Topology

namespace TauCeti

universe u

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [TopologicalSpace A] [ContinuousMul A] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- Continuous cyclic cocycles are continuous cyclic cochains killed by `b`. -/
def continuousCyclicCocycles (n : ℕ) : Submodule R (continuousCyclicCochains R A M n) :=
  LinearMap.ker (continuousCyclicHochschildCoboundary R A M n)

/-- The continuous cocycle condition is the algebraic Hochschild cocycle condition. -/
@[simp]
theorem mem_continuousCyclicCocycles_iff {n : ℕ} {φ : continuousCyclicCochains R A M n} :
    φ ∈ continuousCyclicCocycles R A M n ↔
      hochschildCoboundary R A M n φ.val.toMultilinearMap = 0 := by
  rw [continuousCyclicCocycles, LinearMap.mem_ker, ← Subtype.coe_inj,
    coe_continuousCyclicHochschildCoboundary]
  rw [← (ContinuousMultilinearMap.toMultilinearMap_injective
    (R := R) (M₁ := fun _ : Fin (n + 2) ↦ A) (M₂ := M)).eq_iff]
  simp only [toMultilinearMap_continuousHochschildCoboundary,
    ContinuousMultilinearMap.toMultilinearMap_zero, Submodule.coe_zero]

/-- Continuous cyclic coboundaries: zero in degree zero and the actual image of `b` thereafter. -/
def continuousCyclicCoboundaries : (n : ℕ) → Submodule R (continuousCyclicCochains R A M n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (continuousCyclicHochschildCoboundary R A M n)

/-- There are no nonzero continuous cyclic coboundaries in degree zero. -/
@[simp]
theorem continuousCyclicCoboundaries_zero : continuousCyclicCoboundaries R A M 0 = ⊥ := (rfl)

/-- Positive-degree continuous coboundaries are the image of the preceding differential. -/
theorem continuousCyclicCoboundaries_succ (n : ℕ) :
    continuousCyclicCoboundaries R A M (n + 1) =
      LinearMap.range (continuousCyclicHochschildCoboundary R A M n) := (rfl)

/-- A positive-degree coboundary has a continuous cyclic primitive. -/
@[simp]
theorem mem_continuousCyclicCoboundaries_succ_iff {n : ℕ}
    {φ : continuousCyclicCochains R A M (n + 1)} :
    φ ∈ continuousCyclicCoboundaries R A M (n + 1) ↔
      ∃ ψ, continuousCyclicHochschildCoboundary R A M n ψ = φ := Iff.rfl

/-- Every continuous cyclic coboundary is a continuous cyclic cocycle. -/
theorem continuousCyclicCoboundaries_le_continuousCyclicCocycles (n : ℕ) :
    continuousCyclicCoboundaries R A M n ≤ continuousCyclicCocycles R A M n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨ψ, rfl⟩
    exact continuousCyclicHochschildCoboundary_continuousCyclicHochschildCoboundary R A M ψ

/-- A continuous cyclic degree-zero cochain is a cocycle exactly when it is a trace. -/
theorem mem_continuousCyclicCocycles_zero_iff {φ : continuousCyclicCochains R A M 0} :
    φ ∈ continuousCyclicCocycles R A M 0 ↔
      ∀ x y : A, φ.val (fun _ ↦ x * y) = φ.val (fun _ ↦ y * x) := by
  simp only [mem_continuousCyclicCocycles_iff, hochschildCoboundary_zero_eq_zero_iff,
    ContinuousMultilinearMap.coe_coe]

/-- The cochain complex of jointly continuous cyclic cochains with differential `b`. -/
def continuousCyclicCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (continuousCyclicCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (continuousCyclicHochschildCoboundary R A M n))
    fun _ ↦ ModuleCat.hom_ext (LinearMap.ext
      (continuousCyclicHochschildCoboundary_continuousCyclicHochschildCoboundary R A M))

/-- Identify a term of the complex with its concrete module of continuous cyclic cochains. -/
def continuousCyclicCochainComplexXIso (n : ℕ) :
    (continuousCyclicCochainComplex R A M).X n ≅
      ModuleCat.of R (continuousCyclicCochains R A M n) := Iso.refl _

/-- Under the term identifications, the differential is the continuous cyclic coboundary. -/
@[reassoc, elementwise]
theorem continuousCyclicCochainComplex_d (n : ℕ) :
    (continuousCyclicCochainComplex R A M).d n (n + 1) ≫
        (continuousCyclicCochainComplexXIso R A M (n + 1)).hom =
      (continuousCyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (continuousCyclicHochschildCoboundary R A M n) := by
  simp [continuousCyclicCochainComplex, continuousCyclicCochainComplexXIso]

/-- Concrete continuous cocycles are precisely cycles of the native complex. -/
theorem mem_continuousCyclicCocycles_iff_complex (n : ℕ)
    (φ : continuousCyclicCochains R A M n) :
    φ ∈ continuousCyclicCocycles R A M n ↔
      (continuousCyclicCochainComplex R A M).d n (n + 1)
        ((continuousCyclicCochainComplexXIso R A M n).inv φ) = 0 := by
  exact ((continuousCyclicCochainComplex R A M).moduleCat_d_inv_eq_zero_iff
    (continuousCyclicHochschildCoboundary R A M)
    (continuousCyclicCochainComplex_d R A M) φ).symm

/-- Forgetting continuity gives a map to the algebraic cyclic cochain complex. -/
def continuousCyclicCochainComplexForget :
    continuousCyclicCochainComplex R A M ⟶ cyclicCochainComplex R A M where
  f n := (continuousCyclicCochainComplexXIso R A M n).hom ≫
    ModuleCat.ofHom (continuousCyclicCochainsForget R A M n) ≫
    (cyclicCochainComplexXIso R A M n).inv
  comm' := by
    rintro n _ rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
    apply (ModuleCat.mono_iff_injective (cyclicCochainComplexXIso R A M (n + 1)).hom).1
      inferInstance
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cyclicCochainComplex_d_apply,
      Iso.inv_hom_id_apply, continuousCyclicCochainComplex_d_apply, ModuleCat.hom_ofHom]
    apply Subtype.ext
    simp only [coe_cyclicHochschildCoboundary_apply, coe_continuousCyclicCochainsForget,
      coe_continuousCyclicHochschildCoboundary, toMultilinearMap_continuousHochschildCoboundary]

/-- The forgetful cochain map acts by forgetting continuity in every degree. -/
@[reassoc, elementwise]
theorem continuousCyclicCochainComplexForget_f (n : ℕ) :
    (continuousCyclicCochainComplexForget R A M).f n ≫
        (cyclicCochainComplexXIso R A M n).hom =
      (continuousCyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (continuousCyclicCochainsForget R A M n) := by
  simp [continuousCyclicCochainComplexForget]

end Complex

section Cohomology

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Ring A] [Algebra R A]
  [TopologicalSpace A] [ContinuousMul A] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- Continuous cyclic cohomology of a unital topological algebra, with no closure of boundaries. -/
abbrev continuousCyclicCohomology (n : ℕ) : ModuleCat R :=
  (continuousCyclicCochainComplex R A M).homology n

private theorem mem_continuousCyclicCoboundaries_iff_complex (n : ℕ)
    (φ : continuousCyclicCochains R A M n) :
    φ ∈ continuousCyclicCoboundaries R A M n ↔
      ∃ y : (continuousCyclicCochainComplex R A M).X ((ComplexShape.up ℕ).prev n),
        (continuousCyclicCochainComplex R A M).d ((ComplexShape.up ℕ).prev n) n y =
          (continuousCyclicCochainComplexXIso R A M n).inv φ :=
  (continuousCyclicCochainComplex R A M).moduleCat_mem_iff_exists_d_eq_inv
    (continuousCyclicCoboundaries R A M) (continuousCyclicHochschildCoboundary R A M)
    (continuousCyclicCochainComplex_d R A M) (continuousCyclicCoboundaries_zero R A M)
    (continuousCyclicCoboundaries_succ R A M) n φ

namespace continuousCyclicCohomology

/-- The cohomology class of a continuous cyclic cocycle. -/
def mk (n : ℕ) : continuousCyclicCocycles R A M n →ₗ[R] continuousCyclicCohomology R A M n :=
  (continuousCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso
    (fun n ↦ continuousCyclicCochains R A M n) (continuousCyclicCocycles R A M)
    (continuousCyclicCochainComplexXIso R A M) (mem_continuousCyclicCocycles_iff_complex R A M) n

/-- Every continuous cyclic cohomology class has a continuous cyclic cocycle representative. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) :=
  (continuousCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ continuousCyclicCochains R A M n) (continuousCyclicCocycles R A M)
    (continuousCyclicCochainComplexXIso R A M) (mem_continuousCyclicCocycles_iff_complex R A M) n

/-- A continuous cocycle represents zero exactly when it is a continuous cyclic coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (φ : continuousCyclicCocycles R A M n) :
    mk R A M n φ = 0 ↔ φ.val ∈ continuousCyclicCoboundaries R A M n :=
  (continuousCyclicCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ continuousCyclicCochains R A M n) (continuousCyclicCocycles R A M)
    (continuousCyclicCoboundaries R A M) (continuousCyclicCochainComplexXIso R A M)
    (mem_continuousCyclicCocycles_iff_complex R A M)
    (mem_continuousCyclicCoboundaries_iff_complex R A M) n φ

/-- Two continuous cocycles agree in cohomology exactly when their difference is a continuous
cyclic coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (φ ψ : continuousCyclicCocycles R A M n) :
    mk R A M n φ = mk R A M n ψ ↔
      φ.val - ψ.val ∈ continuousCyclicCoboundaries R A M n := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, Submodule.coe_sub]

/-- Degree-zero continuous cyclic cohomology is the module of continuous traces. -/
def zeroEquiv : continuousCyclicCocycles R A M 0 ≃ₗ[R] continuousCyclicCohomology R A M 0 :=
  LinearEquiv.ofBijective (mk R A M 0) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun φ hφ ↦ ?_
    exact Subtype.ext ((mk_eq_zero_iff R A M 0 φ).1 hφ), mk_surjective R A M 0⟩

/-- The degree-zero identification sends a continuous trace to its class. -/
@[simp]
theorem zeroEquiv_apply (φ : continuousCyclicCocycles R A M 0) :
    zeroEquiv R A M φ = mk R A M 0 φ := (rfl)

variable {R A M} in
/-- Maps out of continuous cyclic cohomology are determined by cocycle representatives. -/
@[ext]
theorem linearMap_ext {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    {f g : continuousCyclicCohomology R A M n →ₗ[R] N}
    (h : f ∘ₗ mk R A M n = g ∘ₗ mk R A M n) : f = g :=
  LinearMap.ext fun x ↦ by
    obtain ⟨φ, rfl⟩ := mk_surjective R A M n x
    exact LinearMap.congr_fun h φ

variable {R A M} in
/-- A linear map on continuous cocycles vanishing on continuous coboundaries descends to
continuous cyclic cohomology. -/
def desc {N : Type*} [AddCommGroup N] [Module R N] (n : ℕ)
    (f : continuousCyclicCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ, φ.val ∈ continuousCyclicCoboundaries R A M n → f φ = 0) :
    continuousCyclicCohomology R A M n →ₗ[R] N :=
  (mk R A M n).liftOfSurjective (mk_surjective R A M n)
    ⟨f, fun φ hφ ↦ hf φ ((mk_eq_zero_iff R A M n φ).1 (LinearMap.mem_ker.1 hφ))⟩

/-- The descended map takes a cocycle class to the prescribed value. -/
@[simp]
theorem desc_mk {N : Type*} [AddCommGroup N] [Module R N] (n : ℕ)
    (f : continuousCyclicCocycles R A M n →ₗ[R] N)
    (hf : ∀ φ, φ.val ∈ continuousCyclicCoboundaries R A M n → f φ = 0)
    (φ : continuousCyclicCocycles R A M n) : desc n f hf (mk R A M n φ) = f φ :=
  LinearMap.equivOfSurjective_apply _ _

/-- Forgetting continuity induces the comparison to algebraic cyclic cohomology. -/
def toAlgebraic (n : ℕ) : continuousCyclicCohomology R A M n ⟶ cyclicCohomology R A M n :=
  HomologicalComplex.homologyMap (continuousCyclicCochainComplexForget R A M) n

/-- The comparison sends a continuous cocycle to the algebraic class of the same cochain. -/
@[simp]
theorem toAlgebraic_mk {n : ℕ} (φ : continuousCyclicCocycles R A M n) :
    toAlgebraic R A M n (mk R A M n φ) =
      cyclicCohomology.mk R A M n
        ⟨continuousCyclicCochainsForget R A M n φ.val,
          (mem_cyclicCocycles_iff R A M).2
            (by simpa only [coe_continuousCyclicCochainsForget] using
              (mem_continuousCyclicCocycles_iff R A M).1 φ.property)⟩ := by
  rw [toAlgebraic, mk,
    HomologicalComplex.moduleCatCohomologyClassOfIso_apply]
  refine (HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk _ _ _ _ _).trans ?_
  exact (cyclicCohomology.mk_eq_homologyπ R A M _ _ (by
    rw [HomologicalComplex.iCycles_moduleCatCyclesMk,
      continuousCyclicCochainComplexForget_f_apply, Iso.inv_hom_id_apply])).symm

end continuousCyclicCohomology

end Cohomology

section Topology

variable (𝕜 : Type*) (A : Type u) (M : Type*) [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
  [TopologicalSpace A] [ContinuousMul A] [AddCommGroup M] [Module 𝕜 M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

namespace continuousCyclicCohomology

/-- The quotient topology of bounded-uniform convergence on continuous cyclic cocycles.
Boundaries are not replaced by their closure. -/
instance instTopologicalSpace (n : ℕ) : TopologicalSpace (continuousCyclicCohomology 𝕜 A M n) :=
  TopologicalSpace.coinduced (mk 𝕜 A M n) inferInstance

/-- The class map is a quotient map for the topology of bounded-uniform convergence. -/
theorem isQuotientMap_mk (n : ℕ) : IsQuotientMap (mk 𝕜 A M n) :=
  ⟨⟨rfl⟩, mk_surjective 𝕜 A M n⟩

/-- The continuous cyclic class map is open as well as quotient. -/
theorem isOpenQuotientMap_mk (n : ℕ) : IsOpenQuotientMap (mk 𝕜 A M n) :=
  AddMonoidHom.isOpenQuotientMap_of_isQuotientMap (isQuotientMap_mk 𝕜 A M n)

/-- Passing from a continuous cyclic cocycle to its class is continuous. -/
@[fun_prop]
theorem continuous_mk (n : ℕ) : Continuous (mk 𝕜 A M n) :=
  (isQuotientMap_mk 𝕜 A M n).continuous

/-- Continuity out of continuous cyclic cohomology can be checked on cocycle representatives. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (n : ℕ)
    (f : continuousCyclicCohomology 𝕜 A M n → X) :
    Continuous f ↔ Continuous (f ∘ mk 𝕜 A M n) :=
  (isQuotientMap_mk 𝕜 A M n).continuous_iff

/-- Addition and negation are continuous for the quotient topology, even when it is not
Hausdorff. -/
instance instIsTopologicalAddGroup (n : ℕ) :
    IsTopologicalAddGroup (continuousCyclicCohomology 𝕜 A M n) where
  continuous_add := by
    rw [← ((isOpenQuotientMap_mk 𝕜 A M n).prodMap
      (isOpenQuotientMap_mk 𝕜 A M n)).continuous_comp_iff]
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, ← map_add, Pi.add_apply] using
      (continuous_mk 𝕜 A M n).comp (continuous_fst.add continuous_snd)
  continuous_neg := by
    rw [continuous_iff]
    simpa only [Function.comp_def, ← map_neg] using
      (continuous_mk 𝕜 A M n).comp continuous_neg

/-- Scalar multiplication is continuous on the quotient whenever it is continuous on values. -/
instance instContinuousSMul [ContinuousSMul 𝕜 M] (n : ℕ) :
    ContinuousSMul 𝕜 (continuousCyclicCohomology 𝕜 A M n) where
  continuous_smul := by
    rw [← ((IsOpenQuotientMap.id : IsOpenQuotientMap (id : 𝕜 → 𝕜)).prodMap
      (isOpenQuotientMap_mk 𝕜 A M n)).continuous_comp_iff]
    have h : Continuous (fun x : 𝕜 × continuousCyclicCocycles 𝕜 A M n ↦
        mk 𝕜 A M n (x.1 • x.2)) :=
      (continuous_mk 𝕜 A M n).comp (continuous_fst.smul continuous_snd)
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, ← map_smul] using h

end continuousCyclicCohomology

end Topology

end TauCeti
