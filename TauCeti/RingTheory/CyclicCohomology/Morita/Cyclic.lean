/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Morita.Hochschild
public import TauCeti.RingTheory.CyclicCohomology.PeriodicCohomology
import Mathlib.Algebra.FiveLemma

/-!
# Matrix Morita invariance of cyclic and periodic cyclic cohomology

Building on the matrix Morita invariance of Hochschild cohomology
(`TauCeti.RingTheory.CyclicCohomology.Morita.Hochschild`), this file proves matrix Morita
invariance for:

1. **The total cyclic bicomplex cohomology `Hᵐ(Tot)`.** Since `matrixCochainExtension` commutes
   with all Hochschild cofaces, the cyclic operator, the cyclic norm, and Connes' operator `B`, it
   extends rowwise to `matrixCyclicTotalCochainExtension` on the total cyclic bicomplex and induces
   `cyclicTotalHomologyMatrixExtension` on `Hᵐ(Tot)`, commuting with the maps `I`, `S`, and `B` of
   the SBI long exact sequence. Strong induction in steps of two—using `H⁰(Tot) ≅ HH⁰`, the
   left-exact five lemma on `0 → H¹(Tot) → HH¹ → H⁰(Tot)`, and the five lemma on
   `HHᵐ⁺¹ → Hᵐ(Tot) → Hᵐ⁺²(Tot) → HHᵐ⁺² → Hᵐ⁺¹(Tot)`—proves that
   `cyclicTotalHomologyMatrixExtension` is bijective in every degree over every commutative
   ring `R`.
2. **Periodic cyclic cohomology `HPⁿ(A; M)`.** Passing to the direct limit along `S` via
   `periodicCyclicCohomology.lift` yields matrix Morita invariance of periodic cyclic cohomology
   over every commutative ring `R`.
3. **Connes' cyclic cohomology `HCⁿ(A; M)`.** The inclusion `cyclicCochainComplexToTotal`
   intertwines `cyclicCohomology.matrixExtension` with `cyclicTotalHomologyMatrixExtension`.
   Whenever `q + 1` is a unit in `R` for all `q < n` (in particular whenever `[Algebra ℚ R]`),
   `cyclicCochainComplexToTotal` is a quasi-isomorphism in degree `n`, so
   `cyclicCohomology.matrixExtension` is bijective—with two-sided inverse
   `cyclicCohomology.cornerRestriction r`. Compatibility of `cyclicCohomology.matrixExtension` with
   `I`, `B`, Connes' periodicity operator `S`, and the normalized stage maps `fromCyclicCohomology`
   is also established.

All induced cohomology maps are constructed as `R`-linear maps rather than `ModuleCat R` morphisms,
so the index type `ι` may live in any universe independent of `R`, `A`, and `M`.

## Main definitions

* `TauCeti.matrixCyclicTotalCochainExtension`, `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixEquiv`: matrix extension on the total cyclic bicomplex and its
  cohomology.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixEquiv`: matrix extension and the Morita equivalence on
  periodic cyclic cohomology.
* `TauCeti.cyclicCohomology.cornerRestriction`, `TauCeti.cyclicCohomology.matrixEquiv`: corner
  restriction and the Morita equivalence on cyclic cohomology.

## Main results

* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix Morita invariance of the cohomology
  of the total cyclic bicomplex over every commutative ring.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of periodic
  cyclic cohomology over every commutative ring.
* `TauCeti.cyclicCohomology.injective_matrixExtension`: matrix extension on `HCⁿ` is split injective
  over every commutative ring.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of Connes' cyclic
  cohomology when `1, …, n` are units in `R`, and in particular over any `ℚ`-algebra.
* `TauCeti.cyclicCohomology.toHochschild_comp_matrixExtension`,
  `TauCeti.hochschildCohomology.connesB_comp_matrixExtension`,
  `TauCeti.cyclicCohomology.periodicity_comp_matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtension_fromCyclicCohomology`: compatibility of matrix
  extension with `I`, `B`, Connes' periodicity `S`, and `fromCyclicCohomology`.

## References

* A. Connes, *Non-commutative differential geometry*, Publications Mathématiques de l'IHÉS 62
  (1985), Part II, Corollary 24.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§2.2, 5.1.
-/

public section

open CategoryTheory

namespace TauCeti

/-! ### Compatibility with the cyclic bicomplex and periodicity -/

section BicomplexCompatibility

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- Matrix extension commutes with the bar coboundary `b'`. -/
theorem matrixCochainExtension_barCoboundary (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 1) (barCoboundary R A M n φ) =
      barCoboundary R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  rw [barCoboundary_eq_sum, barCoboundary_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, matrixCochainExtension_hochschildCoface]

/-- Matrix extension commutes with Connes' unaveraged cochain periodicity operator `S₀`. -/
theorem matrixCochainExtension_cochainPeriodicity (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 2) (cochainPeriodicity R A M n φ) =
      cochainPeriodicity R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  rw [cochainPeriodicity_eq_sum, cochainPeriodicity_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_zsmul, matrixCochainExtension_hochschildCoface, matrixCochainExtension_hochschildCoface]

end BicomplexCompatibility

section TotalCochainsBasic

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommGroup M] [Module R M]

/-- Matrix extension commutes with the horizontal differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexHorizontal_of_even hp, cyclicBicomplexHorizontal_of_even hp]
    simp [matrixCochainExtension_cyclicOperator]
  · rw [cyclicBicomplexHorizontal_of_odd hp, cyclicBicomplexHorizontal_of_odd hp,
      matrixCochainExtension_cyclicNorm]

/-- Rowwise matrix extension on total cochains of the cyclic bicomplex. -/
noncomputable def matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  (LinearMap.pi fun q ↦ matrixCochainExtension ι q ∘ₗ LinearMap.proj q).restrict fun x hx ↦ by
    rw [mem_cyclicTotalCochains_iff] at hx ⊢
    intro q hq
    simp [hx q hq]

/-- In each row `q`, `matrixCyclicTotalCochainExtension` applies `matrixCochainExtension ι q`. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixCyclicTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) :=
  (rfl)

/-- Matrix extension on total cochains commutes with the inclusion of cyclic cochains into column
zero. -/
theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal (ι : Type*) [Fintype ι] {m : ℕ}
    (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  apply Subtype.ext
  funext q
  simp only [coe_matrixCyclicTotalCochainExtension_apply, coe_cyclicCochainsToTotal_apply]
  by_cases hq : q = m
  · subst hq
    simp
  · simp [Pi.single_eq_of_ne hq]

/-- Matrix extension on total cochains commutes with the projection onto column zero. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by
  rw [cyclicTotalToHochschild_apply, cyclicTotalToHochschild_apply,
    coe_matrixCyclicTotalCochainExtension_apply]

/-- Matrix extension on total cochains commutes with the bicomplex periodicity map. -/
theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) := by
  apply Subtype.ext
  funext q
  simp only [coe_matrixCyclicTotalCochainExtension_apply, coe_cyclicTotalPeriodicity_apply]

end TotalCochainsBasic

section TotalCochainsDifferential

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension commutes with the vertical differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexVertical_of_even hp, cyclicBicomplexVertical_of_even hp,
      matrixCochainExtension_hochschildCoboundary]
  · rw [cyclicBicomplexVertical_of_odd hp, cyclicBicomplexVertical_of_odd hp]
    simp [matrixCochainExtension_barCoboundary]

/-- Matrix extension on total cochains commutes with the total differential. -/
theorem matrixCyclicTotalCochainExtension_cyclicTotalDifferential (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) := by
  apply Subtype.ext
  funext q
  cases q with
  | zero =>
    simp only [cyclicTotalDifferential_apply_zero, coe_matrixCyclicTotalCochainExtension_apply]
    exact (matrixCochainExtension_cyclicBicomplexHorizontal ι m 0 (x.1 0)).symm
  | succ q =>
    simp only [cyclicTotalDifferential_apply_succ, coe_matrixCyclicTotalCochainExtension_apply,
      map_add]
    rw [matrixCochainExtension_cyclicBicomplexVertical,
      matrixCochainExtension_cyclicBicomplexHorizontal]

end TotalCochainsDifferential

/-! ### Matrix Morita invariance of the total cyclic bicomplex cohomology -/

section TotalCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Descend an `R`-linear map on total `m`-cocycles to `Hᵐ(Tot)` when it vanishes on cocycles with
zero cohomology class. -/
private noncomputable def cyclicTotalHomologyDesc {P : Type*} [AddCommGroup P] [Module R P]
    (m : ℕ) (f : LinearMap.ker (cyclicTotalDifferential R A M m) →ₗ[R] P)
    (hf : ∀ x : LinearMap.ker (cyclicTotalDifferential R A M m),
      cyclicTotalHomologyMk R A M m x = 0 → f x = 0) :
    (cyclicTotalComplex R A M).homology m →ₗ[R] P :=
  (cyclicTotalHomologyMk R A M m).liftOfSurjective (cyclicTotalHomologyMk_surjective m)
    ⟨f, fun x hx ↦ LinearMap.mem_ker.2 (hf x (LinearMap.mem_ker.1 hx))⟩

private theorem cyclicTotalHomologyDesc_mk {P : Type*} [AddCommGroup P] [Module R P]
    (m : ℕ) (f : LinearMap.ker (cyclicTotalDifferential R A M m) →ₗ[R] P)
    (hf : ∀ x : LinearMap.ker (cyclicTotalDifferential R A M m),
      cyclicTotalHomologyMk R A M m x = 0 → f x = 0)
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyDesc m f hf (cyclicTotalHomologyMk R A M m x) = f x :=
  LinearMap.equivOfSurjective_apply _ _

variable (M) in
/-- The map `Hᵐ(Tot(A)) → Hᵐ(Tot(Matrix ι ι A))` on cohomology of the total cyclic bicomplex
induced by rowwise matrix extension. -/
noncomputable def cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    (cyclicTotalComplex R A M).homology m →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  cyclicTotalHomologyDesc m
    (cyclicTotalHomologyMk R (Matrix ι ι A) M m ∘ₗ
      (matrixCyclicTotalCochainExtension (R := R) (A := A) (M := M) ι m).restrict
        (p := LinearMap.ker (cyclicTotalDifferential R A M m))
        (q := LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m))
        fun x hx ↦ by
          rw [LinearMap.mem_ker] at hx ⊢
          rw [matrixCyclicTotalCochainExtension_cyclicTotalDifferential, hx, map_zero])
    fun x hx ↦ by
      cases m with
      | zero =>
        rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hx
        simp [hx]
      | succ m =>
        obtain ⟨w, hw⟩ := (cyclicTotalHomologyMk_succ_eq_zero_iff x).1 hx
        exact (cyclicTotalHomologyMk_succ_eq_zero_iff _).2
          ⟨matrixCyclicTotalCochainExtension ι m w, by
            rw [matrixCyclicTotalCochainExtension_cyclicTotalDifferential, hw]
            rfl⟩

/-- Matrix extension on total cohomology sends the class of a total cocycle to the class of its
rowwise matrix extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_mk {ι : Type*} [Fintype ι] {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyMk R A M m x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M m
        ⟨matrixCyclicTotalCochainExtension ι m x.1, by
          rw [LinearMap.mem_ker, matrixCyclicTotalCochainExtension_cyclicTotalDifferential,
            LinearMap.mem_ker.1 x.2, map_zero]⟩ :=
  cyclicTotalHomologyDesc_mk _ _ _ x

/-- Matrix extension on total cohomology commutes with `I : Hᵐ(Tot) → HHᵐ`. -/
theorem homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (m : ℕ) :
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) m).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι m =
      hochschildCohomology.matrixExtension M ι m ∘ₗ
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m).hom := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [LinearMap.comp_apply, cyclicTotalHomologyMatrixExtension_mk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk]
  rfl

/-- Matrix extension on total cohomology commutes with `S : Hᵐ(Tot) → Hᵐ⁺²(Tot)`. -/
theorem cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (m : ℕ) :
    (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι m =
      cyclicTotalHomologyMatrixExtension M ι (m + 2) ∘ₗ
        (cyclicTotalHomologyPeriodicity R A M m).hom := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [LinearMap.comp_apply, cyclicTotalHomologyMatrixExtension_mk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity ι x.1).symm

/-- Matrix extension on total cohomology commutes with the transition maps `S^(j - i)` of the
periodic direct system. -/
theorem cyclicTotalHomologyPeriodicTransition_comp_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (n : ℕ) {i j : ℕ} (h : i ≤ j) :
    (cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * j) ∘ₗ
        (cyclicTotalHomologyPeriodicTransition R A M n h).hom := by
  induction j, h using Nat.le_induction with
  | base =>
    simp [cyclicTotalHomologyPeriodicTransition_self]
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hij
        (Nat.le_add_right j 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ,
      ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]
    -- `n + 2 * (j + 1)` is definitionally `(n + 2 * j) + 2` (`Nat.mul_succ`).
    exact congrArg (· ∘ₗ _)
      (cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension ι (n + 2 * j))

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- The inclusion of Connes' cyclic cochain complex into the total cyclic bicomplex intertwines
matrix extension on cyclic cohomology with matrix extension on total cohomology. -/
theorem cyclicTotalHomologyMatrixExtension_comp_homologyMap_cyclicCochainComplexToTotal
    (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) :
    cyclicTotalHomologyMatrixExtension M ι m ∘ₗ
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m).hom =
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) m).hom ∘ₗ
        cyclicCohomology.matrixExtension M ι m := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M m c
  simp only [LinearMap.comp_apply,
    homologyMap_cyclicCochainComplexToTotal_mk, cyclicTotalHomologyMatrixExtension_mk,
    cyclicCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι φ.1)

/-- Matrix extension commutes with Connes' operator `B : HHᵐ⁺¹ → HCᵐ`. -/
theorem hochschildCohomology.connesB_comp_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι]
    (m : ℕ) :
    (hochschildCohomology.connesB R (Matrix ι ι A) M m).hom ∘ₗ
        hochschildCohomology.matrixExtension M ι (m + 1) =
      cyclicCohomology.matrixExtension M ι m ∘ₗ
        (hochschildCohomology.connesB R A M m).hom := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (m + 1) c
  simp only [LinearMap.comp_apply, hochschildCohomology.matrixExtension_mk,
    hochschildCohomology.connesB_mk, cyclicCohomology.matrixExtension_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_matrixCyclicCochainExtension_apply]
  exact (matrixCochainExtension_connesB ι m φ.1).symm

/-- Matrix extension commutes with the map `B : HHᵐ⁺¹ → Hᵐ(Tot)` of the bicomplex SBI sequence. -/
theorem cyclicTotalHomologyConnesB_comp_hochschildMatrixExtension (ι : Type*) [Fintype ι]
    [DecidableEq ι] (m : ℕ) :
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m).hom ∘ₗ
        hochschildCohomology.matrixExtension M ι (m + 1) =
      cyclicTotalHomologyMatrixExtension M ι m ∘ₗ
        (cyclicTotalHomologyConnesB R A M m).hom := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.hom_comp,
    ModuleCat.hom_comp, LinearMap.comp_assoc, hochschildCohomology.connesB_comp_matrixExtension,
    ← LinearMap.comp_assoc,
    ← cyclicTotalHomologyMatrixExtension_comp_homologyMap_cyclicCochainComplexToTotal,
    LinearMap.comp_assoc]

/-- **Matrix Morita invariance of the total cyclic bicomplex cohomology.** For a unital associative
algebra `A` over any commutative ring `R` and any finite nonempty index type `ι`, rowwise matrix
extension induces a bijection `Hᵐ(Tot(A)) → Hᵐ(Tot(Matrix ι ι A))` in every degree `m`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] [Nonempty ι]
    (m : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι m) := by
  classical
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m with
    | 0 =>
      have hI₀A : Function.Bijective
          (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0).hom :=
        (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
      have hI₀M : Function.Bijective
          (HomologicalComplex.homologyMap
            (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0).hom :=
        (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
      have hHH₀ := hochschildCohomology.bijective_matrixExtension (R := R) (A := A) (M := M) ι 0
      have hcomm :=
        homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension
          (R := R) (A := A) (M := M) ι 0
      have hcomp : Function.Bijective
          ((HomologicalComplex.homologyMap
              (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0).hom ∘ₗ
            cyclicTotalHomologyMatrixExtension M ι 0) := by
        rw [hcomm]
        exact hHH₀.comp hI₀A
      refine ⟨Function.Injective.of_comp hcomp.1, fun y ↦ ?_⟩
      obtain ⟨x, hx⟩ := hcomp.2
        ((HomologicalComplex.homologyMap
          (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0).hom y)
      exact ⟨x, hI₀M.1 hx⟩
    | 1 =>
      have h0 := ih 0 (by omega)
      have hHH₁ := hochschildCohomology.bijective_matrixExtension (R := R) (A := A) (M := M) ι 1
      exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 1).hom
        (cyclicTotalHomologyConnesB R A M 0).hom
        (HomologicalComplex.homologyMap
          (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 1).hom
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M 0).hom
        (cyclicTotalHomologyMatrixExtension M ι 1)
        (hochschildCohomology.matrixExtension M ι 1)
        (cyclicTotalHomologyMatrixExtension M ι 0)
        (homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension ι 1)
        (cyclicTotalHomologyConnesB_comp_hochschildMatrixExtension ι 0)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
        hHH₁ h0.1
        injective_homologyMap_cyclicTotalComplexToHochschild_one
        injective_homologyMap_cyclicTotalComplexToHochschild_one
    | k + 2 =>
      have hk := ih k (by omega)
      have hk1 := ih (k + 1) (by omega)
      have hHH1 :=
        hochschildCohomology.bijective_matrixExtension (R := R) (A := A) (M := M) ι (k + 1)
      have hHH2 :=
        hochschildCohomology.bijective_matrixExtension (R := R) (A := A) (M := M) ι (k + 2)
      exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
        (cyclicTotalHomologyConnesB R A M k).hom
        (cyclicTotalHomologyPeriodicity R A M k).hom
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (k + 2)).hom
        (cyclicTotalHomologyConnesB R A M (k + 1)).hom
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M k).hom
        (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M k).hom
        (HomologicalComplex.homologyMap
          (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) (k + 2)).hom
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M (k + 1)).hom
        (hochschildCohomology.matrixExtension M ι (k + 1))
        (cyclicTotalHomologyMatrixExtension M ι k)
        (cyclicTotalHomologyMatrixExtension M ι (k + 2))
        (hochschildCohomology.matrixExtension M ι (k + 2))
        (cyclicTotalHomologyMatrixExtension M ι (k + 1))
        (cyclicTotalHomologyConnesB_comp_hochschildMatrixExtension ι k)
        (cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension ι k)
        (homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension ι
          (k + 2))
        (cyclicTotalHomologyConnesB_comp_hochschildMatrixExtension ι (k + 1))
        (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity k)
        (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M k)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (k + 1))
        (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity k)
        (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
          R (Matrix ι ι A) M k)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (k + 1))
        hHH1.2 hk hHH2 hk1.1

variable (M) in
/-- Matrix Morita equivalence on total cyclic bicomplex cohomology as an `R`-linear equivalence. -/
noncomputable def cyclicTotalHomologyMatrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    (cyclicTotalComplex R A M).homology m ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι m)
    (bijective_cyclicTotalHomologyMatrixExtension ι m)

/-- The underlying linear map of `cyclicTotalHomologyMatrixEquiv` is
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem coe_cyclicTotalHomologyMatrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    (cyclicTotalHomologyMatrixEquiv (R := R) (A := A) M ι m :
        (cyclicTotalComplex R A M).homology m →ₗ[R]
          (cyclicTotalComplex R (Matrix ι ι A) M).homology m) =
      cyclicTotalHomologyMatrixExtension M ι m :=
  (rfl)

/-- Applying `cyclicTotalHomologyMatrixEquiv` is applying `cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ)
    (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyMatrixEquiv (R := R) (A := A) M ι m c =
      cyclicTotalHomologyMatrixExtension M ι m c :=
  (rfl)

end Unital

end TotalCohomology

/-! ### Matrix Morita invariance of periodic cyclic cohomology -/

section PeriodicCohomology

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- The map `HPⁿ(A; M) → HPⁿ(Matrix ι ι A; M)` on periodic cyclic cohomology induced by matrix
extension on the stages `H^(n + 2k)(Tot)`. -/
noncomputable def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  lift
    (fun k ↦ (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun k ↦ by
      have hcomm : cyclicTotalHomologyMatrixExtension M ι (n + 2 * (k + 1)) ∘ₗ
            (cyclicTotalHomologyPeriodicity R A M (n + 2 * k)).hom =
          (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M (n + 2 * k)).hom ∘ₗ
            cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) :=
        (cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension ι (n + 2 * k)).symm
      rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc]
      have hι : (periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1)).hom ∘ₗ
          (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M (n + 2 * k)).hom =
          (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom := by
        rw [← ModuleCat.hom_comp, cyclicTotalHomologyPeriodicity_ι]
      rw [hι]

/-- On the `k`-th stage `H^(n + 2k)(Tot)`, `periodicCyclicCohomology.matrixExtension` acts by
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem matrixExtension_ι (ι : Type*) [Fintype ι] (n k : ℕ)
    (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k y) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) y) :=
  lift_ι _ _ k y

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of periodic cyclic cohomology.** For a unital associative algebra `A`
over any commutative ring `R` and any finite nonempty index type `ι`, matrix extension induces a
bijection `HPⁿ(A; M) → HPⁿ(Matrix ι ι A; M)`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨k, y, rfl⟩ := exists_ι_eq x
    rw [matrixExtension_ι, ι_eq_zero_iff] at hx
    obtain ⟨j, hkj, hj⟩ := hx
    rw [← LinearMap.comp_apply (f := (cyclicTotalHomologyPeriodicTransition _ _ _ _ _).hom),
      cyclicTotalHomologyPeriodicTransition_comp_cyclicTotalHomologyMatrixExtension ι n hkj,
      LinearMap.comp_apply] at hj
    have hy0 : (cyclicTotalHomologyPeriodicTransition R A M n hkj).hom y = 0 :=
      (bijective_cyclicTotalHomologyMatrixExtension (R := R) (A := A) (M := M) ι (n + 2 * j)).1
        (hj.trans (map_zero _).symm)
    exact (ι_eq_zero_iff y).2 ⟨j, hkj, hy0⟩
  · obtain ⟨k, w, rfl⟩ := exists_ι_eq z
    obtain ⟨y, rfl⟩ :=
      (bijective_cyclicTotalHomologyMatrixExtension (R := R) (A := A) (M := M) ι (n + 2 * k)).2 w
    exact ⟨periodicCyclicCohomology.ι R A M n k y, matrixExtension_ι ι n k y⟩

variable (M) in
/-- Matrix Morita equivalence on periodic cyclic cohomology as an `R`-linear equivalence. -/
noncomputable def matrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The underlying linear map of `periodicCyclicCohomology.matrixEquiv` is `matrixExtension`. -/
@[simp]
theorem coe_matrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixEquiv (R := R) (A := A) M ι n :
        periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

/-- Applying `periodicCyclicCohomology.matrixEquiv` is applying `matrixExtension`. -/
@[simp]
theorem matrixEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : periodicCyclicCohomology R A M n) :
    matrixEquiv (R := R) (A := A) M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- Over a `ℚ`-algebra, `periodicCyclicCohomology.matrixExtension` commutes with the normalized
cyclic cohomology stage maps `fromCyclicCohomology`. -/
@[simp]
theorem matrixExtension_fromCyclicCohomology [Algebra ℚ R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n k : ℕ) (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix ι ι A) M n k
        (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by
  simp only [fromCyclicCohomology_apply, map_smul, matrixExtension_ι]
  congr 2
  exact LinearMap.congr_fun
    (cyclicTotalHomologyMatrixExtension_comp_homologyMap_cyclicCochainComplexToTotal
      (R := R) (A := A) (M := M) ι (n + 2 * k)) c

end Unital

end periodicCyclicCohomology

end PeriodicCohomology

/-! ### Matrix Morita invariance of Connes' cyclic cohomology -/

section CyclicCohomology

namespace cyclicCohomology

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

variable (M) in
/-- The map `HCⁿ(Matrix ι ι A; M) → HCⁿ(A; M)` induced by restricting cyclic cocycles to the
`(r, r)` corner. -/
noncomputable def cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    cyclicCohomology R (Matrix ι ι A) M n →ₗ[R] cyclicCohomology R A M n :=
  desc n (mk R A M n ∘ₗ (matrixCyclicCochainCornerRestriction r n).restrict fun φ hφ ↦ by
        rw [mem_cyclicCocycles_iff] at hφ ⊢
        rw [coe_matrixCyclicCochainCornerRestriction_apply]
        exact (matrixCochainCornerRestriction_hochschildCoboundary r n φ.1).symm.trans
          (by rw [hφ, map_zero]))
    fun φ hφ ↦ (mk_eq_zero_iff R A M n _).2 <| by
      cases n with
      | zero =>
        rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
        simp [hφ]
      | succ n =>
        obtain ⟨ψ, hψ⟩ := (mem_cyclicCoboundaries_succ_iff R (Matrix ι ι A) M).1 hφ
        refine (mem_cyclicCoboundaries_succ_iff R A M).2
          ⟨matrixCyclicCochainCornerRestriction r n ψ, Subtype.ext ?_⟩
        rw [LinearMap.restrict_apply, coe_cyclicHochschildCoboundary_apply,
          coe_matrixCyclicCochainCornerRestriction_apply,
          coe_matrixCyclicCochainCornerRestriction_apply]
        exact (matrixCochainCornerRestriction_hochschildCoboundary r n ψ.1).symm.trans <| by
          rw [← coe_cyclicHochschildCoboundary_apply, hψ]

/-- Corner restriction on cyclic cohomology sends the class of a cyclic cocycle to the class of
its `(r, r)` corner restriction. -/
@[simp]
theorem cornerRestriction_mk {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}
    (φ : cyclicCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M r n (mk R (Matrix ι ι A) M n φ) =
      mk R A M n ⟨matrixCyclicCochainCornerRestriction r n φ.1, by
        rw [mem_cyclicCocycles_iff, coe_matrixCyclicCochainCornerRestriction_apply]
        exact (matrixCochainCornerRestriction_hochschildCoboundary r n φ.1.1).symm.trans
          (by rw [(mem_cyclicCocycles_iff R (Matrix ι ι A) M).1 φ.2, map_zero])⟩ :=
  desc_mk _ _ _ φ

/-- Corner restriction is a left inverse to matrix extension on cyclic cohomology, over every
commutative ring `R`. -/
@[simp]
theorem cornerRestriction_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) (c : cyclicCohomology R A M n) :
    cornerRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [matrixExtension_mk, cornerRestriction_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_matrixCyclicCochainCornerRestriction_apply, coe_matrixCyclicCochainExtension_apply]
  exact matrixCochainCornerRestriction_matrixCochainExtension r n φ.1.1

/-- Matrix extension on cyclic cohomology is split injective over every commutative ring `R` for
any finite nonempty index type `ι`. -/
theorem injective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (cornerRestriction_matrixExtension r n)

/-- Matrix extension commutes with `I : HCⁿ → HHⁿ`. -/
theorem toHochschild_comp_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    (toHochschild R (Matrix ι ι A) M n).hom ∘ₗ matrixExtension M ι n =
      hochschildCohomology.matrixExtension M ι n ∘ₗ (toHochschild R A M n).hom := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [LinearMap.comp_apply, matrixExtension_mk, toHochschild_mk,
    hochschildCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (coe_matrixCyclicCochainExtension_apply ι n φ.1)

/-- **Matrix Morita invariance of cyclic cohomology (torsion-free degree form).** If `q + 1` is a
unit in `R` for all `q < n`, then `cyclicCohomology.matrixExtension` is bijective in degree `n`. -/
theorem bijective_matrixExtension_of_isUnit (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have hTotA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have hTotM : Function.Bijective
      (HomologicalComplex.homologyMap
        (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  have hTr := bijective_cyclicTotalHomologyMatrixExtension (R := R) (A := A) (M := M) ι n
  have hcomm :=
    cyclicTotalHomologyMatrixExtension_comp_homologyMap_cyclicCochainComplexToTotal
      (R := R) (A := A) (M := M) ι n
  have hcomp : Function.Bijective
      ((HomologicalComplex.homologyMap
          (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n).hom ∘ₗ
        matrixExtension M ι n) := by
    rw [← hcomm]
    exact hTr.comp hTotA
  refine ⟨Function.Injective.of_comp hcomp.1, fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hcomp.2
    ((HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n).hom y)
  exact ⟨x, hTotM.1 hx⟩

/-- When `q + 1` is a unit in `R` for all `q < n`, corner restriction at any corner `r` is also a
right inverse to matrix extension on `HCⁿ`. -/
theorem matrixExtension_cornerRestriction_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1))
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M r n c) = c := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨x, rfl⟩ := (bijective_matrixExtension_of_isUnit (R := R) (A := A) (M := M) ι n hR).2 c
  rw [cornerRestriction_matrixExtension]

end Unital

section Rational

variable {R A M : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- Matrix extension commutes with Connes' periodicity operator `S : HCⁿ → HCⁿ⁺²`. -/
theorem periodicity_comp_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    (periodicity R (Matrix ι ι A) M n).hom ∘ₗ matrixExtension M ι n =
      matrixExtension M ι (n + 2) ∘ₗ (periodicity R A M n).hom := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [LinearMap.comp_apply, matrixExtension_mk, periodicity_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_cyclicCocyclesPeriodicity_apply, coe_matrixCyclicCochainExtension_apply,
    coe_matrixCyclicCochainExtension_apply, coe_cyclicCocyclesPeriodicity_apply]
  exact (matrixCochainExtension_cochainPeriodicity ι n φ.1.1).symm

/-- **Matrix Morita invariance of Connes' cyclic cohomology.** For a unital associative algebra `A`
over a `ℚ`-algebra `R` and any finite nonempty index type `ι`, the generalized matrix trace
induces a bijection `HCⁿ(A; M) → HCⁿ(Matrix ι ι A; M)`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦ by
    simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

/-- Over a `ℚ`-algebra, corner restriction at any corner `r` is a two-sided inverse to matrix
extension on cyclic cohomology. -/
@[simp]
theorem matrixExtension_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M r n c) = c :=
  matrixExtension_cornerRestriction_of_isUnit r n
    (fun q _ ↦ by simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)) c

variable (M) in
/-- Matrix Morita equivalence on Connes' cyclic cohomology as an `R`-linear equivalence. -/
noncomputable def matrixEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The underlying linear map of `cyclicCohomology.matrixEquiv` is `matrixExtension`. -/
@[simp]
theorem coe_matrixEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    (matrixEquiv (R := R) (A := A) M ι n :
        cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

/-- Applying `cyclicCohomology.matrixEquiv` is applying `matrixExtension`. -/
@[simp]
theorem matrixEquiv_apply (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    matrixEquiv (R := R) (A := A) M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- The inverse of `cyclicCohomology.matrixEquiv` is `cornerRestriction` at any corner `r`. -/
theorem matrixEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (r : ι)
    (n : ℕ) (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixEquiv (R := R) (A := A) M ι n).symm c = cornerRestriction M r n c := by
  apply (matrixEquiv (R := R) (A := A) M ι n).injective
  simp

end Rational

end cyclicCohomology

end CyclicCohomology

end TauCeti
