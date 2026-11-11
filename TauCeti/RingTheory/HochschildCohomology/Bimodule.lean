/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HochschildCohomology.Coboundary
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Hochschild cohomology with coefficients in a bimodule

Let `A` be an algebra over a commutative ring `R` and `M` an `A`-bimodule, written as a left
`A`-module and a left `Aᵐᵒᵖ`-module whose actions commute. The Hochschild cochains
`Cⁿ(A, M) = Hom_R(A^{⊗n}, M)` are the `R`-multilinear maps `Aⁿ → M`, including the constant
`0`-cochains, the elements of `M`. Under the Hochschild coboundary
`TauCeti.hochschildBimoduleCoboundary`,

`(δψ)(a₀, …, aₙ) = a₀ ψ(a₁, …, aₙ) + ∑_{j < n} (-1)ʲ⁺¹ ψ(a₀, …, aⱼaⱼ₊₁, …, aₙ)`
`  + (-1)ⁿ⁺¹ ψ(a₀, …, aₙ₋₁) aₙ`,

they form the Hochschild cochain complex `TauCeti.hochschildBimoduleCochainComplex R A M`, whose
cohomology is the Hochschild cohomology `HHⁿ(A, M)`. The degree of a cochain is its number of
arguments. For `M = A`, with the actions by left and right multiplication, this is the Hochschild
cohomology `HHⁿ(A, A)` of an ordinary associative algebra, whose degree-two classes are the
infinitesimal deformations of `A` and whose degree-three classes contain the obstructions.

The class map `TauCeti.hochschildBimoduleCohomology.mk` is surjective, and its kernel consists
exactly of the coboundaries. In degree zero there are no coboundaries and the cocycles are the
central elements of `M`. In degree one the cocycles are the derivations `A → M` and the
coboundaries the inner derivations `a ↦ a m - m a`.

## Main definitions

* `TauCeti.hochschildBimoduleCocycles`, `TauCeti.hochschildBimoduleCoboundaries`: Hochschild
  cocycles and coboundaries with coefficients in `M`.
* `TauCeti.hochschildBimoduleCochainComplex`: the Hochschild cochain complex `C^•(A, M)`.
* `TauCeti.hochschildBimoduleCohomology`: the Hochschild cohomology `HHⁿ(A, M)`.
* `TauCeti.hochschildBimoduleCohomology.mk`: the class of a Hochschild cocycle.
* `TauCeti.hochschildBimoduleCohomology.desc`: the linear map out of Hochschild cohomology induced
  by a linear map on cocycles vanishing on coboundaries.

## Main results

* `TauCeti.hochschildBimoduleCohomology.mk_eq_homologyπ`: the class of a cocycle is the homology
  class of any cycle of the cochain complex representing it.
* `TauCeti.hochschildBimoduleCohomology.mk_surjective`,
  `TauCeti.hochschildBimoduleCohomology.mk_eq_zero_iff`,
  `TauCeti.hochschildBimoduleCohomology.mk_eq_mk_iff`: the classes are the cocycles modulo the
  coboundaries.
* `TauCeti.mem_hochschildBimoduleCocycles_zero_iff`: the degree-zero cocycles are the central
  elements.
* `TauCeti.mem_hochschildBimoduleCoboundaries_one_iff`,
  `TauCeti.hochschildBimoduleCohomology.mk_one_eq_zero_iff`: a degree-one cochain is a coboundary
  exactly when it is an inner derivation.

The construction of the complex and of the class map follows the bounded Hochschild complex in
`TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Complex` and the Hochschild complex with
coefficients in `Hom_R(A, M)` in `TauCeti.RingTheory.HochschildCohomology.Complex`.

## References

* G. Hochschild, *On the cohomology groups of an associative algebra*, Annals of Mathematics 46
  (1945), 58--67.
* M. Gerstenhaber, *On the deformation of rings and algebras*, Annals of Mathematics 79 (1964),
  59--103.
* J.-L. Loday, *Cyclic Homology*, §1.5.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

section Cocycles

variable (R A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The Hochschild `n`-cocycles with coefficients in the bimodule `M`: the kernel of the
Hochschild coboundary on `n`-cochains. -/
def hochschildBimoduleCocycles (n : ℕ) :
    Submodule R (MultilinearMap R (fun _ : Fin n ↦ A) M) :=
  LinearMap.ker (hochschildBimoduleCoboundary R A M n)

variable {R A M} in
/-- A cochain is a cocycle exactly when its coboundary vanishes. -/
@[simp]
theorem mem_hochschildBimoduleCocycles_iff {n : ℕ}
    {ψ : MultilinearMap R (fun _ : Fin n ↦ A) M} :
    ψ ∈ hochschildBimoduleCocycles R A M n ↔ hochschildBimoduleCoboundary R A M n ψ = 0 :=
  LinearMap.mem_ker

/-- The Hochschild `n`-coboundaries with coefficients in the bimodule `M`: zero in degree zero,
and the range of the preceding coboundary in positive degree. -/
def hochschildBimoduleCoboundaries :
    (n : ℕ) → Submodule R (MultilinearMap R (fun _ : Fin n ↦ A) M)
  | 0 => ⊥
  | n + 1 => LinearMap.range (hochschildBimoduleCoboundary R A M n)

/-- There are no nonzero degree-zero coboundaries. -/
@[simp]
theorem hochschildBimoduleCoboundaries_zero : hochschildBimoduleCoboundaries R A M 0 = ⊥ :=
  (rfl)

/-- In positive degree the coboundaries are the range of the preceding coboundary. -/
theorem hochschildBimoduleCoboundaries_succ (n : ℕ) :
    hochschildBimoduleCoboundaries R A M (n + 1) =
      LinearMap.range (hochschildBimoduleCoboundary R A M n) :=
  (rfl)

variable {R A M} in
/-- A positive-degree coboundary is the coboundary of a cochain. -/
@[simp]
theorem mem_hochschildBimoduleCoboundaries_succ_iff {n : ℕ}
    {ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} :
    ψ ∈ hochschildBimoduleCoboundaries R A M (n + 1) ↔
      ∃ φ, hochschildBimoduleCoboundary R A M n φ = ψ :=
  LinearMap.mem_range

/-- Every Hochschild coboundary is a cocycle. -/
theorem hochschildBimoduleCoboundaries_le_hochschildBimoduleCocycles [SMulCommClass A Aᵐᵒᵖ M]
    (n : ℕ) : hochschildBimoduleCoboundaries R A M n ≤ hochschildBimoduleCocycles R A M n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨φ, rfl⟩
    exact hochschildBimoduleCoboundary_hochschildBimoduleCoboundary φ

variable {R A M} in
/-- A degree-zero cochain is a cocycle exactly when its value is central. -/
theorem mem_hochschildBimoduleCocycles_zero_iff (m : M) :
    MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 ↦ A) m ∈ hochschildBimoduleCocycles R A M 0 ↔
      ∀ x : A, x • m = op x • m := by
  rw [mem_hochschildBimoduleCocycles_iff, hochschildBimoduleCoboundary_constOfIsEmpty_eq_zero_iff]

variable {R A M} in
/-- A degree-one cochain is a coboundary exactly when it is an inner derivation
`a ↦ a • m - op a • m`. -/
theorem mem_hochschildBimoduleCoboundaries_one_iff
    (ψ : MultilinearMap R (fun _ : Fin 1 ↦ A) M) :
    ψ ∈ hochschildBimoduleCoboundaries R A M 1 ↔
      ∃ m : M, ∀ a : A, ψ (fun _ ↦ a) = a • m - op a • m := by
  rw [mem_hochschildBimoduleCoboundaries_succ_iff]
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨φ 0, fun a ↦ ?_⟩
    have hφ : φ = MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 ↦ A) (φ 0) := by
      ext v
      rw [MultilinearMap.constOfIsEmpty_apply, Subsingleton.elim v 0]
      rfl
    rw [hφ, hochschildBimoduleCoboundary_constOfIsEmpty, MultilinearMap.constOfIsEmpty_apply]
    rfl
  · rintro ⟨m, hm⟩
    refine ⟨MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 ↦ A) m, ?_⟩
    ext a
    rw [hochschildBimoduleCoboundary_constOfIsEmpty]
    have ha : (fun _ : Fin 1 ↦ a 0) = a := funext fun i ↦ congrArg a (Subsingleton.elim 0 i)
    simpa only [ha] using (hm (a 0)).symm

end Cocycles

variable (R A M : Type*) [CommRing R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M]

section Complex

/-- The Hochschild cochain complex `C⁰(A, M) → C¹(A, M) → ⋯` with coefficients in the bimodule
`M`: in degree `n` the `R`-multilinear maps `Aⁿ → M`, with the Hochschild coboundary as
differential. -/
def hochschildBimoduleCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (MultilinearMap R (fun _ : Fin n ↦ A) M))
    (fun n ↦ ModuleCat.ofHom (hochschildBimoduleCoboundary R A M n))
    fun _ ↦ ModuleCat.hom_ext hochschildBimoduleCoboundary_comp_hochschildBimoduleCoboundary

/-- The degree-`n` term of the Hochschild cochain complex is the module of `n`-cochains. -/
def hochschildBimoduleCochainComplexXIso (n : ℕ) :
    (hochschildBimoduleCochainComplex R A M).X n ≅
      ModuleCat.of R (MultilinearMap R (fun _ : Fin n ↦ A) M) :=
  Iso.refl _

/-- Under the identifications `hochschildBimoduleCochainComplexXIso`, the differential of the
Hochschild cochain complex is the Hochschild coboundary. -/
@[reassoc, elementwise]
theorem hochschildBimoduleCochainComplex_d (n : ℕ) :
    (hochschildBimoduleCochainComplex R A M).d n (n + 1) ≫
        (hochschildBimoduleCochainComplexXIso R A M (n + 1)).hom =
      (hochschildBimoduleCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (hochschildBimoduleCoboundary R A M n) := by
  simp [hochschildBimoduleCochainComplex, hochschildBimoduleCochainComplexXIso]

end Complex

/-- The **Hochschild cohomology** `HHⁿ(A, M)` of `A` with coefficients in the bimodule `M`, the
cohomology of the Hochschild cochain complex. For `M = A` it is `HHⁿ(A, A)`. -/
abbrev hochschildBimoduleCohomology (n : ℕ) : ModuleCat R :=
  (hochschildBimoduleCochainComplex R A M).homology n

private theorem mem_hochschildBimoduleCocycles_iff_complex (n : ℕ)
    (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) :
    ψ ∈ hochschildBimoduleCocycles R A M n ↔
      (hochschildBimoduleCochainComplex R A M).d n (n + 1)
        ((hochschildBimoduleCochainComplexXIso R A M n).inv ψ) = 0 := by
  rw [mem_hochschildBimoduleCocycles_iff,
    (hochschildBimoduleCochainComplex R A M).moduleCat_d_inv_eq_zero_iff
      (hochschildBimoduleCoboundary R A M) (hochschildBimoduleCochainComplex_d R A M)]

private theorem mem_hochschildBimoduleCoboundaries_iff_complex (n : ℕ)
    (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) :
    ψ ∈ hochschildBimoduleCoboundaries R A M n ↔
      ∃ y : (hochschildBimoduleCochainComplex R A M).X ((ComplexShape.up ℕ).prev n),
        (hochschildBimoduleCochainComplex R A M).d ((ComplexShape.up ℕ).prev n) n y =
          (hochschildBimoduleCochainComplexXIso R A M n).inv ψ :=
  (hochschildBimoduleCochainComplex R A M).moduleCat_mem_iff_exists_d_eq_inv
    (hochschildBimoduleCoboundaries R A M) (hochschildBimoduleCoboundary R A M)
    (hochschildBimoduleCochainComplex_d R A M) (hochschildBimoduleCoboundaries_zero R A M)
    (hochschildBimoduleCoboundaries_succ R A M) n ψ

namespace hochschildBimoduleCohomology

/-- The Hochschild cohomology class of a Hochschild cocycle. -/
def mk (n : ℕ) : hochschildBimoduleCocycles R A M n →ₗ[R] hochschildBimoduleCohomology R A M n :=
  (hochschildBimoduleCochainComplex R A M).moduleCatCohomologyClassOfIso
    (fun n ↦ MultilinearMap R (fun _ : Fin n ↦ A) M) (hochschildBimoduleCocycles R A M)
    (hochschildBimoduleCochainComplexXIso R A M)
    (mem_hochschildBimoduleCocycles_iff_complex R A M) n

/-- The class of a Hochschild cocycle `ψ` is the homology class of any cycle of the Hochschild
cochain complex whose underlying cochain is `ψ`. -/
theorem mk_eq_homologyπ {n : ℕ} (ψ : hochschildBimoduleCocycles R A M n)
    (z : (hochschildBimoduleCochainComplex R A M).cycles n)
    (hz : (hochschildBimoduleCochainComplexXIso R A M n).hom
      ((hochschildBimoduleCochainComplex R A M).iCycles n z) = ψ) :
    mk R A M n ψ = (hochschildBimoduleCochainComplex R A M).homologyπ n z :=
  (hochschildBimoduleCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_homologyπ
    (fun n ↦ MultilinearMap R (fun _ : Fin n ↦ A) M) (hochschildBimoduleCocycles R A M)
    (hochschildBimoduleCochainComplexXIso R A M)
    (mem_hochschildBimoduleCocycles_iff_complex R A M) ψ z hz

/-- Every Hochschild cohomology class is the class of a Hochschild cocycle. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk R A M n) :=
  (hochschildBimoduleCochainComplex R A M).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ MultilinearMap R (fun _ : Fin n ↦ A) M) (hochschildBimoduleCocycles R A M)
    (hochschildBimoduleCochainComplexXIso R A M)
    (mem_hochschildBimoduleCocycles_iff_complex R A M) n

/-- A Hochschild cocycle has zero class exactly when it is a Hochschild coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (ψ : hochschildBimoduleCocycles R A M n) :
    mk R A M n ψ = 0 ↔
      (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) ∈ hochschildBimoduleCoboundaries R A M n :=
  (hochschildBimoduleCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ MultilinearMap R (fun _ : Fin n ↦ A) M) (hochschildBimoduleCocycles R A M)
    (hochschildBimoduleCoboundaries R A M) (hochschildBimoduleCochainComplexXIso R A M)
    (mem_hochschildBimoduleCocycles_iff_complex R A M)
    (mem_hochschildBimoduleCoboundaries_iff_complex R A M) n ψ

/-- Two Hochschild cocycles have the same class exactly when they differ by a Hochschild
coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (ψ φ : hochschildBimoduleCocycles R A M n) :
    mk R A M n ψ = mk R A M n φ ↔
      (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) - φ ∈
        hochschildBimoduleCoboundaries R A M n :=
  (hochschildBimoduleCochainComplex R A M).moduleCatCohomologyClassOfIso_eq_iff
    (fun n ↦ MultilinearMap R (fun _ : Fin n ↦ A) M) (hochschildBimoduleCocycles R A M)
    (hochschildBimoduleCoboundaries R A M) (hochschildBimoduleCochainComplexXIso R A M)
    (mem_hochschildBimoduleCocycles_iff_complex R A M)
    (mem_hochschildBimoduleCoboundaries_iff_complex R A M) n ψ φ

variable {R A M} {N : Type*} [AddCommGroup N] [Module R N]

/-- Linear maps out of Hochschild cohomology are determined by their values on classes of
cocycles. -/
@[ext]
theorem linearMap_ext {n : ℕ} {f g : hochschildBimoduleCohomology R A M n →ₗ[R] N}
    (h : f ∘ₗ mk R A M n = g ∘ₗ mk R A M n) : f = g :=
  LinearMap.ext fun z ↦ by
    obtain ⟨ψ, rfl⟩ := mk_surjective R A M n z
    exact LinearMap.congr_fun h ψ

/-- A linear map on Hochschild cocycles vanishing on coboundaries descends to Hochschild
cohomology. -/
def desc (n : ℕ) (f : hochschildBimoduleCocycles R A M n →ₗ[R] N)
    (hf : ∀ ψ : hochschildBimoduleCocycles R A M n,
      (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) ∈ hochschildBimoduleCoboundaries R A M n →
        f ψ = 0) :
    hochschildBimoduleCohomology R A M n →ₗ[R] N :=
  (mk R A M n).liftOfSurjective (mk_surjective R A M n)
    ⟨f, fun ψ hψ ↦ LinearMap.mem_ker.2
      (hf ψ ((mk_eq_zero_iff R A M n ψ).1 (LinearMap.mem_ker.1 hψ)))⟩

/-- The descended map evaluates on a class by evaluating on its representative. -/
@[simp]
theorem desc_mk (n : ℕ) (f : hochschildBimoduleCocycles R A M n →ₗ[R] N)
    (hf : ∀ ψ : hochschildBimoduleCocycles R A M n,
      (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) ∈ hochschildBimoduleCoboundaries R A M n →
        f ψ = 0)
    (ψ : hochschildBimoduleCocycles R A M n) :
    desc n f hf (mk R A M n ψ) = f ψ :=
  LinearMap.equivOfSurjective_apply _ _

variable (R A M) in
/-- A degree-one cocycle has zero class exactly when it is an inner derivation. -/
theorem mk_one_eq_zero_iff (ψ : hochschildBimoduleCocycles R A M 1) :
    mk R A M 1 ψ = 0 ↔ ∃ m : M, ∀ a : A, ψ.val (fun _ ↦ a) = a • m - op a • m := by
  rw [mk_eq_zero_iff, mem_hochschildBimoduleCoboundaries_one_iff]

variable (R A M) in
/-- In degree zero there are no coboundaries, so distinct cocycles have distinct classes. -/
theorem mk_zero_injective : Function.Injective (mk R A M 0) := fun ψ φ h ↦ Subtype.ext <|
  sub_eq_zero.mp (by
    simpa only [hochschildBimoduleCoboundaries_zero, Submodule.mem_bot] using
      (mk_eq_mk_iff R A M 0 ψ φ).1 h)

end hochschildBimoduleCohomology

end TauCeti

end
