/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

The underlying complex is also defined for nonunital algebras; its cohomology is not
called continuous cyclic cohomology here. For nonunital algebras the relative
forced-unitization construction is needed instead.

## References

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

end continuousCyclicCohomology

end Unital

end TauCeti
