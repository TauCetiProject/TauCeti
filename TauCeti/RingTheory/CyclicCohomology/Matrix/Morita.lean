/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix.Hochschild
public import TauCeti.RingTheory.CyclicCohomology.PeriodicCohomology
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Regular.SMul

/-!
# Matrix Morita invariance of cyclic and periodic cyclic cohomology

For an algebra `A` over a commutative ring `R`, an `R`-module `M`, and a finite index type `ι`, the
generalized matrix trace `TauCeti.matrixCochainExtension` commutes with every Hochschild coface,
with the Hochschild and bar coboundaries, with the cyclic operator and cyclic norm, and (when `A`
is unital) with `TauCeti.barContraction` and Connes' operator `B`.

Applying `matrixCochainExtension` in every row of Connes' cyclic bicomplex therefore produces a
total cochain map `TauCeti.matrixCyclicTotalCochainExtension` and an induced linear map
`TauCeti.cyclicTotalHomologyMatrixExtension` on the cohomology `Hⁿ(Tot)` of the total cyclic
bicomplex, compatible with the SBI sequence maps `I`, `B`, and `S`.

Combined with matrix Morita invariance of Hochschild cohomology
(`TauCeti.hochschildCohomology.bijective_matrixExtension`), the five lemma along the SBI exact
sequence of `TauCeti.RingTheory.CyclicCohomology.ExactSequence` proves by strong induction on `n`
that `cyclicTotalHomologyMatrixExtension` is bijective in every degree for any unital `R`-algebra
`A` over any commutative ring `R` and any nonempty finite index type `ι`. Passing to the direct
limit along `S` yields matrix Morita invariance of periodic cyclic cohomology
(`TauCeti.periodicCyclicCohomology.bijective_matrixExtension`) over any commutative ring `R`.

When `1, 2, …, n` are invertible in `R` — in particular in degrees `0` and `1` over every
commutative ring `R`, and in every degree `n` when `R` is a `ℚ`-algebra — the column-zero inclusion
`TauCeti.cyclicCochainComplexToTotal` is a quasi-isomorphism in degree `n`
(`TauCeti.quasiIsoAt_cyclicCochainComplexToTotal`). Transporting bijectivity across this
quasi-isomorphism proves matrix Morita invariance of Connes' cyclic cohomology
(`TauCeti.cyclicCohomology.bijective_matrixExtension`) and identifies diagonal corner restriction as
its two-sided inverse. Specializing `A = R` computes the Hochschild, periodic cyclic, and cyclic
cohomology of finite matrix algebras `Matrix ι ι R` from those of the ground ring `R`.

## Main definitions

* `TauCeti.matrixCyclicTotalCochainExtension`: row-wise matrix extension on total cochains of the
  cyclic bicomplex.
* `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`: matrix extension on `Hⁿ(Tot)` and the
  resulting linear equivalence.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`: matrix extension on periodic cyclic
  cohomology `HPⁿ` and the resulting linear equivalence.
* `TauCeti.cyclicCohomology.cornerRestriction`: diagonal corner restriction on `HCⁿ`.
* `TauCeti.cyclicCohomology.matrixExtensionEquiv`: matrix Morita equivalence
  `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a `ℚ`-algebra.
* `TauCeti.cyclicCohomology.matrixSelfEquiv`: `M ≃ₗ[R] HCⁿ(Matrix ι ι R; M)` in even degree `n`
  over a `ℚ`-algebra.

## Main results

* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix extension on `Hⁿ(Tot)` is bijective
  for any unital algebra over any commutative ring `R` and nonempty finite `ι`.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix extension on `HPⁿ(A; M)` is
  bijective over any commutative ring `R`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`: matrix extension on `HCⁿ(A; M)` is
  bijective whenever `q + 1` is a unit in `R` for all `q < n` (in particular unconditionally in
  degrees `0` and `1`).
* `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of `HCⁿ(A; M)` over
  a `ℚ`-algebra.
* `TauCeti.isZero_hochschildCohomology_matrix_of_ne_zero`,
  `TauCeti.isZero_periodicCyclicCohomology_matrix_one`,
  `TauCeti.isZero_cyclicCohomology_matrix_of_odd`: cohomology computations for `Matrix ι ι R`.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS **62** (1985), Part II,
  Corollary 24, p. 113.
* A. Connes, *Noncommutative Geometry* (1994), Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, 2nd ed., Springer, 1998, §§1.2, 2.2, 5.1.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

/-! ### Row-wise matrix extension on the cyclic bicomplex -/

section TotalCochains

section NonAssoc

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension commutes with the bar coboundary `b'`. -/
theorem matrixCochainExtension_barCoboundary (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) M) :
    matrixCochainExtension (R := R) ι (n + 1) (barCoboundary R A M n φ) =
      barCoboundary R (Matrix ι ι A) M n (matrixCochainExtension (R := R) ι n φ) := by
  have h1 := eq_sub_of_add_eq (hochschildCoboundary_eq_barCoboundary_add (R := R) φ).symm
  have h2 := eq_sub_of_add_eq (hochschildCoboundary_eq_barCoboundary_add (R := R)
    (matrixCochainExtension (R := R) ι n φ)).symm
  rw [h1, h2, map_sub, map_zsmul, matrixCochainExtension_hochschildCoboundary,
    matrixCochainExtension_hochschildCoface]

omit [NonUnitalNonAssocSemiring A] [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Matrix extension commutes with the horizontal differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal {A : Type*} [AddCommMonoid A] [Module R A]
    (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) => A) M) :
    matrixCochainExtension (R := R) ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension (R := R) ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_cyclicOperator]
  · simp [hp, matrixCochainExtension_cyclicNorm]

/-- Matrix extension commutes with the vertical differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) => A) M) :
    matrixCochainExtension (R := R) ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension (R := R) ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_hochschildCoboundary]
  · simp [hp, matrixCochainExtension_barCoboundary]

/-- Row-wise matrix extension on total cochains of degree `m` of the cyclic bicomplex. -/
def matrixCyclicTotalCochainExtension {A : Type*} [AddCommMonoid A] [Module R A]
    (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  LinearMap.codRestrict (cyclicTotalCochains R (Matrix ι ι A) M m)
    (LinearMap.pi fun q =>
      matrixCochainExtension (R := R) ι q ∘ₗ LinearMap.proj q ∘ₗ
        (cyclicTotalCochains R A M m).subtype)
    fun x => mem_cyclicTotalCochains_iff.2 fun q hq => by
      simp [coe_cyclicTotalCochains_apply_of_lt x hq]

/-- The `q`-th row component of `matrixCyclicTotalCochainExtension ι m x` is the matrix extension
of `x.1 q`. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply {A : Type*} [AddCommMonoid A] [Module R A]
    (ι : Type*) [Fintype ι] {m : ℕ} (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixCyclicTotalCochainExtension ι m x).1 q =
      matrixCochainExtension (R := R) ι q (x.1 q) :=
  (rfl)

/-- Row-wise matrix extension commutes with the total differential of the cyclic bicomplex. -/
@[simp]
theorem cyclicTotalDifferential_matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) := by
  refine Subtype.ext (funext fun q => ?_)
  cases q with
  | zero =>
    simp [matrixCochainExtension_cyclicBicomplexHorizontal]
  | succ q =>
    simp [matrixCochainExtension_cyclicBicomplexVertical,
      matrixCochainExtension_cyclicBicomplexHorizontal]

omit [NonUnitalNonAssocSemiring A] [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Row-wise matrix extension commutes with the column-zero inclusion of cyclic cochains. -/
@[simp]
theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal {A : Type*} [AddCommMonoid A]
    [Module R A] (ι : Type*) [Fintype ι] {m : ℕ} (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  refine Subtype.ext (funext fun q => ?_)
  simp only [coe_matrixCyclicTotalCochainExtension_apply, coe_cyclicCochainsToTotal_apply,
    coe_matrixCyclicCochainExtension_apply]
  by_cases hq : q = m
  · subst hq
    simp
  · simp [Pi.single_eq_of_ne hq]

omit [NonUnitalNonAssocSemiring A] [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Row-wise matrix extension commutes with the projection onto column zero. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension {A : Type*} [AddCommMonoid A]
    [Module R A] (ι : Type*) [Fintype ι] {m : ℕ} (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension (R := R) ι m (cyclicTotalToHochschild R A M m x) := by
  rw [cyclicTotalToHochschild_apply, cyclicTotalToHochschild_apply,
    coe_matrixCyclicTotalCochainExtension_apply]

omit [NonUnitalNonAssocSemiring A] [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Row-wise matrix extension commutes with the periodicity shift on total cochains. -/
@[simp]
theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity {A : Type*} [AddCommMonoid A]
    [Module R A] (ι : Type*) [Fintype ι] {m : ℕ} (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) := by
  refine Subtype.ext (funext fun q => ?_)
  rw [coe_matrixCyclicTotalCochainExtension_apply, coe_cyclicTotalPeriodicity_apply,
    coe_cyclicTotalPeriodicity_apply, coe_matrixCyclicTotalCochainExtension_apply]

end NonAssoc

end TotalCochains

/-! ### Matrix Morita invariance on total cohomology `Hⁿ(Tot)` -/

section TotalHomology

section NonUnital

variable {R A M ι : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] [Fintype ι]

/-- Row-wise matrix extension sends total cocycles to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker {n : ℕ}
    {x : cyclicTotalCochains R A M n} (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M n)) :
    matrixCyclicTotalCochainExtension ι n x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hx, map_zero]

private theorem cyclicTotalHomologyMk_matrixCyclicTotalCochainExtension_eq_zero {n : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M n))
    (hx : cyclicTotalHomologyMk R A M n x = 0) :
    cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixCyclicTotalCochainExtension ι n x.1,
          matrixCyclicTotalCochainExtension_mem_ker x.2⟩ = 0 := by
  cases n with
  | zero =>
    rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hx ⊢
    rw [hx]
    ext q
    simp
  | succ k =>
    rw [cyclicTotalHomologyMk_succ_eq_zero_iff] at hx ⊢
    obtain ⟨w, hw⟩ := hx
    exact ⟨matrixCyclicTotalCochainExtension ι k w, by
      rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hw]⟩

variable (M ι) in
/-- Matrix extension `Hⁿ(Tot(A; M)) →ₗ[R] Hⁿ(Tot(Matrix ι ι A; M))` on the cohomology of the total
cyclic bicomplex. -/
def cyclicTotalHomologyMatrixExtension (n : ℕ) :
    (cyclicTotalComplex R A M).homology n →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  cyclicTotalHomologyDesc n
    (cyclicTotalHomologyMk R (Matrix ι ι A) M n ∘ₗ
      LinearMap.codRestrict (LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n))
        (matrixCyclicTotalCochainExtension ι n ∘ₗ
          (LinearMap.ker (cyclicTotalDifferential R A M n)).subtype)
        fun x => matrixCyclicTotalCochainExtension_mem_ker x.2)
    cyclicTotalHomologyMk_matrixCyclicTotalCochainExtension_eq_zero

/-- `cyclicTotalHomologyMatrixExtension` sends the class of a total cocycle to the class of its
row-wise matrix extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_mk {n : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M n)) :
    cyclicTotalHomologyMatrixExtension M ι n (cyclicTotalHomologyMk R A M n x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixCyclicTotalCochainExtension ι n x.1,
          matrixCyclicTotalCochainExtension_mem_ker x.2⟩ :=
  cyclicTotalHomologyDesc_mk _ _ _ x

/-- Matrix extension on `Hⁿ(Tot)` commutes with the projection `I` onto Hochschild cohomology. -/
@[simp]
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension {n : ℕ}
    (c : (cyclicTotalComplex R A M).homology n) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) n
        (cyclicTotalHomologyMatrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  simp only [cyclicTotalHomologyMatrixExtension_mk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk]
  congr 1

/-- Composite form of compatibility between `cyclicTotalHomologyMatrixExtension` and `I`. -/
theorem homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension (n : ℕ) :
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) n).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι n =
      hochschildCohomology.matrixExtension M ι n ∘ₗ
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n).hom :=
  LinearMap.ext homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension

/-- Matrix extension on `Hⁿ(Tot)` commutes with the bicomplex periodicity map `S`. -/
@[simp]
theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension {n : ℕ}
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M n
        (cyclicTotalHomologyMatrixExtension M ι n c) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2)
        (cyclicTotalHomologyPeriodicity R A M n c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  simp only [cyclicTotalHomologyMatrixExtension_mk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity ι x.1).symm

/-- Composite form of compatibility between `cyclicTotalHomologyMatrixExtension` and `S`. -/
theorem cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension (n : ℕ) :
    (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M n).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι (n + 2) ∘ₗ
        (cyclicTotalHomologyPeriodicity R A M n).hom :=
  LinearMap.ext cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension

/-- Matrix extension on `Hⁿ(Tot)` commutes with every transition map of the periodic system. -/
@[simp]
theorem cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension {n i j : ℕ}
    (h : i ≤ j) (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) c) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h c) := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [cyclicTotalHomologyPeriodicTransition_self, cyclicTotalHomologyPeriodicTransition_self,
      ModuleCat.id_apply, ModuleCat.id_apply]
  | succ k hik ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hik
        (Nat.le_add_right k 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R A M n hik (Nat.le_add_right k 1),
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ,
      ModuleCat.comp_apply, ModuleCat.comp_apply, ih,
      cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension]
    rfl

end NonUnital

section UnitalSquares

variable {R A M ι : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/-- Matrix extension on `Hⁿ(Tot)` commutes with the column-zero inclusion from `HCⁿ`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal {n : ℕ}
    (c : cyclicCohomology R A M n) :
    cyclicTotalHomologyMatrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n c) =
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n
        (cyclicCohomology.matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M n c
  simp only [homologyMap_cyclicCochainComplexToTotal_mk, cyclicCohomology.matrixExtension_mk,
    cyclicTotalHomologyMatrixExtension_mk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι φ.1)

/-- Composite form of compatibility between matrix extension on `HCⁿ` and on `Hⁿ(Tot)`. -/
theorem cyclicTotalHomologyMatrixExtension_comp_homologyMap_cyclicCochainComplexToTotal (n : ℕ) :
    cyclicTotalHomologyMatrixExtension M ι n ∘ₗ
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n).hom =
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n).hom ∘ₗ
        cyclicCohomology.matrixExtension M ι n :=
  LinearMap.ext cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal

/-- Matrix extension commutes with Connes' operator `B : HHⁿ⁺¹ → HCⁿ`. -/
@[simp]
theorem cyclicCohomology.matrixExtension_connesB {n : ℕ}
    (c : hochschildCohomology R A M (n + 1)) :
    cyclicCohomology.matrixExtension M ι n (hochschildCohomology.connesB R A M n c) =
      hochschildCohomology.connesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (n + 1) c
  simp only [hochschildCohomology.connesB_mk, cyclicCohomology.matrixExtension_mk,
    hochschildCohomology.matrixExtension_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_matrixCyclicCochainExtension_apply]
  exact matrixCochainExtension_connesB ι n φ.1

/-- Composite form of compatibility between matrix extension and `hochschildCohomology.connesB`. -/
theorem cyclicCohomology.matrixExtension_comp_connesB (n : ℕ) :
    cyclicCohomology.matrixExtension M ι n ∘ₗ (hochschildCohomology.connesB R A M n).hom =
      (hochschildCohomology.connesB R (Matrix ι ι A) M n).hom ∘ₗ
        hochschildCohomology.matrixExtension M ι (n + 1) :=
  LinearMap.ext cyclicCohomology.matrixExtension_connesB

/-- Matrix extension on `Hⁿ(Tot)` commutes with the connecting map `B : HHⁿ⁺¹ → Hⁿ(Tot)`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB {n : ℕ}
    (c : hochschildCohomology R A M (n + 1)) :
    cyclicTotalHomologyMatrixExtension M ι n (cyclicTotalHomologyConnesB R A M n c) =
      cyclicTotalHomologyConnesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.comp_apply,
    ModuleCat.comp_apply,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    cyclicCohomology.matrixExtension_connesB]

/-- Composite form of compatibility between `cyclicTotalHomologyMatrixExtension` and `B`. -/
theorem cyclicTotalHomologyConnesB_comp_hochschildMatrixExtension (n : ℕ) :
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M n).hom ∘ₗ
        hochschildCohomology.matrixExtension M ι (n + 1) =
      cyclicTotalHomologyMatrixExtension M ι n ∘ₗ (cyclicTotalHomologyConnesB R A M n).hom :=
  LinearMap.ext fun c => (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB c).symm

end UnitalSquares

section TotalBijective

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance on the total cyclic bicomplex.** For a unital `R`-algebra `A` over
any commutative ring `R`, coefficients in `M`, and any nonempty finite index type `ι`, row-wise
matrix extension induces a bijection `Hⁿ(Tot(A; M)) → Hⁿ(Tot(Matrix ι ι A; M))` in every degree
`n`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  classical
  refine Nat.strongRecOn n fun m ih => ?_
  match m with
  | 0 =>
    -- In degree `0`, `I : H⁰(Tot) → HH⁰` is an isomorphism.
    have hIA : Function.Bijective
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0) :=
      (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    have hIM : Function.Bijective
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0) :=
      (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    rw [← hIM.of_comp_iff', ← LinearMap.coe_comp,
      homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension]
    exact (hochschildCohomology.bijective_matrixExtension ι 0).comp hIA
  | 1 =>
    -- In degree `1`, apply the left-exact four lemma to `0 → H¹(Tot) →I HH¹ →B H⁰(Tot)`.
    exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 1).hom
      (cyclicTotalHomologyConnesB R A M 0).hom
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 1).hom
      (cyclicTotalHomologyConnesB R (Matrix ι ι A) M 0).hom
      (cyclicTotalHomologyMatrixExtension M ι 1)
      (hochschildCohomology.matrixExtension M ι 1)
      (cyclicTotalHomologyMatrixExtension M ι 0)
      (homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension 1)
      (cyclicTotalHomologyConnesB_comp_hochschildMatrixExtension 0)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
      (hochschildCohomology.bijective_matrixExtension ι 1)
      (ih 0 one_pos).1
      injective_homologyMap_cyclicTotalComplexToHochschild_one
      injective_homologyMap_cyclicTotalComplexToHochschild_one
  | k + 2 =>
    -- In degree `k + 2`, apply the five lemma to `HH^(k+1) →B H^k(Tot) →S H^(k+2)(Tot) →I
    -- HH^(k+2) →B H^(k+1)(Tot)`.
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (cyclicTotalHomologyConnesB R A M k).hom
      (cyclicTotalHomologyPeriodicity R A M k).hom
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (k + 2)).hom
      (cyclicTotalHomologyConnesB R A M (k + 1)).hom
      (cyclicTotalHomologyConnesB R (Matrix ι ι A) M k).hom
      (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M k).hom
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M)
        (k + 2)).hom
      (cyclicTotalHomologyConnesB R (Matrix ι ι A) M (k + 1)).hom
      (hochschildCohomology.matrixExtension M ι (k + 1))
      (cyclicTotalHomologyMatrixExtension M ι k)
      (cyclicTotalHomologyMatrixExtension M ι (k + 2))
      (hochschildCohomology.matrixExtension M ι (k + 2))
      (cyclicTotalHomologyMatrixExtension M ι (k + 1))
      (cyclicTotalHomologyConnesB_comp_hochschildMatrixExtension k)
      (cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension k)
      (homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension (k + 2))
      (cyclicTotalHomologyConnesB_comp_hochschildMatrixExtension (k + 1))
      (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity k)
      (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M k)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (k + 1))
      (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity k)
      (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
        R (Matrix ι ι A) M k)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (k + 1))
      (hochschildCohomology.bijective_matrixExtension ι (k + 1)).2
      (ih k (by omega))
      (hochschildCohomology.bijective_matrixExtension ι (k + 2))
      (ih (k + 1) (by omega)).1

variable (M) in
/-- Matrix extension on `Hⁿ(Tot)` as a linear equivalence for a unital algebra `A` and nonempty
finite index type `ι`. -/
def cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (cyclicTotalComplex R A M).homology n ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι n)
    (bijective_cyclicTotalHomologyMatrixExtension ι n)

/-- Applying `cyclicTotalHomologyMatrixExtensionEquiv` agrees with
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_apply {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixExtensionEquiv M ι n c =
      cyclicTotalHomologyMatrixExtension M ι n c :=
  (rfl)

/-- Converting `cyclicTotalHomologyMatrixExtensionEquiv` to a linear map recovers
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem toLinearMap_cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) :
    (cyclicTotalHomologyMatrixExtensionEquiv (R := R) (A := A) M ι n :
      (cyclicTotalComplex R A M).homology n →ₗ[R]
        (cyclicTotalComplex R (Matrix ι ι A) M).homology n) =
      cyclicTotalHomologyMatrixExtension M ι n :=
  (rfl)

end TotalBijective

end TotalHomology

/-! ### Matrix Morita invariance of periodic cyclic cohomology `HPⁿ(A; M)` -/

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- Matrix extension `HPⁿ(A; M) →ₗ[R] HPⁿ(Matrix ι ι A; M)` on periodic cyclic cohomology. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  descLinearMap
    (fun k => (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun k y => by
      have h1 := LinearMap.congr_fun
        (congrArg (fun f : _ →ₗ[R] _ =>
            (periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1)).hom ∘ₗ f)
          (cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension
            (R := R) (A := A) (M := M) (ι := ι) (n + 2 * k)).symm) y
      have h2 := congrArg
        (fun f => ModuleCat.Hom.hom f (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) y))
        (cyclicTotalHomologyPeriodicity_ι R (Matrix ι ι A) M n k)
      exact h1.trans h2

/-- Matrix extension on `HPⁿ` commutes with the canonical stage maps `ι`. -/
@[simp]
theorem matrixExtension_ι {ι : Type*} [Fintype ι] (n k : ℕ)
    (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k y) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) y) :=
  descLinearMap_ι _ _ k y

private theorem cyclicTotalHomologyMatrixExtension_eqToHom {ι : Type*} [Fintype ι]
    {m m' : ℕ} (hm : m = m') (y : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyMatrixExtension M ι m'
        (ModuleCat.Hom.hom
          (eqToHom (by rw [hm]) :
            (cyclicTotalComplex R A M).homology m ⟶
              (cyclicTotalComplex R A M).homology m') y) =
      ModuleCat.Hom.hom
        (eqToHom (by rw [hm]) :
          (cyclicTotalComplex R (Matrix ι ι A) M).homology m ⟶
            (cyclicTotalComplex R (Matrix ι ι A) M).homology m')
        (cyclicTotalHomologyMatrixExtension M ι m y) := by
  subst hm
  simp

/-- Matrix extension on `HPⁿ` commutes with the `2`-periodicity isomorphism `shiftIso`. -/
@[simp]
theorem shiftIso_hom_matrixExtension {ι : Type*} [Fintype ι] (n : ℕ)
    (x : periodicCyclicCohomology R A M (n + 2)) :
    (shiftIso R (Matrix ι ι A) M n).hom (matrixExtension M ι (n + 2) x) =
      matrixExtension M ι n ((shiftIso R A M n).hom x) := by
  obtain ⟨k, y, rfl⟩ := exists_ι_eq x
  have hA := congrArg (fun f => ModuleCat.Hom.hom f y) (ι_shiftIso_hom R A M n k)
  have hM := congrArg
    (fun f => ModuleCat.Hom.hom f (cyclicTotalHomologyMatrixExtension M ι (n + 2 + 2 * k) y))
    (ι_shiftIso_hom R (Matrix ι ι A) M n k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hA hM
  rw [matrixExtension_ι]
  exact hM.trans <|
    (congrArg (ModuleCat.Hom.hom (periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1)))
      (cyclicTotalHomologyMatrixExtension_eqToHom (by omega) y).symm).trans <|
    (matrixExtension_ι n (k + 1) _).symm.trans (congrArg (matrixExtension M ι n) hA.symm)

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of periodic cyclic cohomology.** For a unital `R`-algebra `A` over
any commutative ring `R`, coefficients in `M`, and any nonempty finite index type `ι`, matrix
extension induces a bijection `HPⁿ(A; M) → HPⁿ(Matrix ι ι A; M)` in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun z => ?_⟩
  · obtain ⟨k, y, rfl⟩ := exists_ι_eq x
    rw [matrixExtension_ι, ι_eq_zero_iff] at hx
    obtain ⟨j, hkj, hj⟩ := hx
    rw [cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension] at hj
    exact (ι_eq_zero_iff y).2 ⟨j, hkj,
      (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * j)).1 (hj.trans (map_zero _).symm)⟩
  · obtain ⟨k, w, rfl⟩ := exists_ι_eq z
    obtain ⟨y, rfl⟩ := (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * k)).2 w
    exact ⟨periodicCyclicCohomology.ι R A M n k y, matrixExtension_ι n k y⟩

variable (M) in
/-- Matrix extension on `HPⁿ` as a linear equivalence `HPⁿ(A; M) ≃ₗ[R] HPⁿ(Matrix ι ι A; M)` over
any commutative ring `R`. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Applying `periodicCyclicCohomology.matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (x : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n x = matrixExtension M ι n x :=
  (rfl)

/-- Converting `periodicCyclicCohomology.matrixExtensionEquiv` to a linear map recovers
`matrixExtension`. -/
@[simp]
theorem toLinearMap_matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

end Unital

section Rational

variable {R A M ι : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Fintype ι] [DecidableEq ι]

/-- Over a `ℚ`-algebra, matrix extension on `HPⁿ` commutes with the normalized stage maps
`fromCyclicCohomology : HC^(n+2k) → HPⁿ`. -/
@[simp]
theorem matrixExtension_fromCyclicCohomology (n k : ℕ)
    (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix ι ι A) M n k
        (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by
  rw [fromCyclicCohomology_apply, fromCyclicCohomology_apply, map_smul, matrixExtension_ι,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]

end Rational

end periodicCyclicCohomology

/-! ### Matrix Morita invariance of cyclic cohomology `HCⁿ(A; M)` -/

section CyclicCorner

variable {R A M ι : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [DecidableEq ι] {n : ℕ}

omit [NonUnitalSemiring A] [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Diagonal corner restriction preserves cyclic cochains. -/
theorem matrixCornerRestriction_mem_cyclicCochains {A : Type*} [AddCommMonoid A] [Module R A]
    (r : ι) (n : ℕ)
    {Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M}
    (hΦ : Φ ∈ cyclicCochains R (Matrix ι ι A) M n) :
    matrixCornerRestriction r n Φ ∈ cyclicCochains R A M n := by
  rw [← ker_one_sub_cyclicOperator, LinearMap.mem_ker, LinearMap.sub_apply,
    _root_.one_apply_eq_self, sub_eq_zero] at hΦ ⊢
  rw [← matrixCornerRestriction_cyclicOperator, ← hΦ]

omit [NonUnitalSemiring A] [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Restriction of cyclic `n`-cochains on `Matrix ι ι A` to the `(r, r)` diagonal corner. -/
def matrixCyclicCornerRestriction {A : Type*} [AddCommMonoid A] [Module R A] (r : ι) (n : ℕ) :
    cyclicCochains R (Matrix ι ι A) M n →ₗ[R] cyclicCochains R A M n :=
  LinearMap.codRestrict (cyclicCochains R A M n)
    (matrixCornerRestriction r n ∘ₗ (cyclicCochains R (Matrix ι ι A) M n).subtype)
    fun Φ => matrixCornerRestriction_mem_cyclicCochains r n Φ.2

omit [NonUnitalSemiring A] [IsScalarTower R A A] [SMulCommClass R A A] in
/-- The underlying multilinear map of `matrixCyclicCornerRestriction r n Φ` is
`matrixCornerRestriction r n Φ`. -/
@[simp]
theorem coe_matrixCyclicCornerRestriction_apply {A : Type*} [AddCommMonoid A] [Module R A]
    (r : ι) (n : ℕ) (Φ : cyclicCochains R (Matrix ι ι A) M n) :
    (matrixCyclicCornerRestriction r n Φ :
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) M) =
      matrixCornerRestriction r n Φ :=
  (rfl)

/-- Corner restriction of cyclic cochains commutes with the Hochschild coboundary. -/
theorem cyclicHochschildCoboundary_matrixCyclicCornerRestriction [Fintype ι] (r : ι)
    (Φ : cyclicCochains R (Matrix ι ι A) M n) :
    cyclicHochschildCoboundary R A M n (matrixCyclicCornerRestriction r n Φ) =
      matrixCyclicCornerRestriction r (n + 1)
        (cyclicHochschildCoboundary R (Matrix ι ι A) M n Φ) := by
  apply Subtype.ext
  rw [coe_cyclicHochschildCoboundary_apply, coe_matrixCyclicCornerRestriction_apply,
    coe_matrixCyclicCornerRestriction_apply, coe_cyclicHochschildCoboundary_apply,
    matrixCornerRestriction_hochschildCoboundary]

/-- Corner restriction maps cyclic cocycles to cyclic cocycles. -/
theorem matrixCyclicCornerRestriction_mem_cyclicCocycles [Fintype ι] (r : ι)
    {Φ : cyclicCochains R (Matrix ι ι A) M n}
    (hΦ : Φ ∈ cyclicCocycles R (Matrix ι ι A) M n) :
    matrixCyclicCornerRestriction r n Φ ∈ cyclicCocycles R A M n := by
  rw [mem_cyclicCocycles_iff] at hΦ ⊢
  rw [coe_matrixCyclicCornerRestriction_apply, ← matrixCornerRestriction_hochschildCoboundary,
    hΦ, map_zero]

/-- Corner restriction maps cyclic coboundaries to cyclic coboundaries. -/
theorem matrixCyclicCornerRestriction_mem_cyclicCoboundaries [Fintype ι] (r : ι)
    {Φ : cyclicCochains R (Matrix ι ι A) M n}
    (hΦ : Φ ∈ cyclicCoboundaries R (Matrix ι ι A) M n) :
    matrixCyclicCornerRestriction r n Φ ∈ cyclicCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hΦ ⊢
    rw [hΦ, map_zero]
  | succ k =>
    obtain ⟨Ψ, rfl⟩ := (mem_cyclicCoboundaries_succ_iff _ _ _).1 hΦ
    exact (mem_cyclicCoboundaries_succ_iff _ _ _).2
      ⟨matrixCyclicCornerRestriction r k Ψ,
        cyclicHochschildCoboundary_matrixCyclicCornerRestriction r Ψ⟩

end CyclicCorner

namespace cyclicCohomology

section GeneralRing

variable {R A M ι : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] {n : ℕ}

variable (M n) in
/-- Diagonal corner restriction `HCⁿ(Matrix ι ι A; M) →ₗ[R] HCⁿ(A; M)` along the `(r, r)` matrix
corner, induced by `matrixCyclicCornerRestriction`. -/
def cornerRestriction (r : ι) :
    cyclicCohomology R (Matrix ι ι A) M n →ₗ[R] cyclicCohomology R A M n :=
  desc n
    (mk R A M n ∘ₗ
      (matrixCyclicCornerRestriction r n).restrict
        fun _ => matrixCyclicCornerRestriction_mem_cyclicCocycles r)
    fun _ hΦ => (mk_eq_zero_iff R A M n _).2
      (matrixCyclicCornerRestriction_mem_cyclicCoboundaries r hΦ)

/-- `cornerRestriction` sends the class of `Φ` to the class of `Φ ∘ E_{rr}`. -/
@[simp]
theorem cornerRestriction_mk (r : ι) (Φ : cyclicCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M n r (mk R (Matrix ι ι A) M n Φ) =
      mk R A M n ⟨matrixCyclicCornerRestriction r n Φ,
        matrixCyclicCornerRestriction_mem_cyclicCocycles r Φ.2⟩ :=
  desc_mk _ _ _ Φ

/-- When `A` and `ι` live in the same universe, `cornerRestriction M n r` agrees with pullback
along `matrixCornerNonUnitalAlgHom R A r`. -/
@[simp]
theorem map_matrixCornerNonUnitalAlgHom_eq_cornerRestriction.{u} {B κ : Type u}
    [Ring B] [Algebra R B] [Fintype κ] [DecidableEq κ] (r : κ) (n : ℕ) :
    (map M (matrixCornerNonUnitalAlgHom R B r) n).hom = cornerRestriction M n r := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨Φ, rfl⟩ := mk_surjective R (Matrix κ κ B) M n c
  rw [map_mk, cornerRestriction_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  ext x
  simp

/-- Diagonal corner restriction is a left inverse to matrix extension on cyclic cohomology over
every commutative ring `R`. -/
@[simp]
theorem cornerRestriction_matrixExtension (r : ι) (c : cyclicCohomology R A M n) :
    cornerRestriction M n r (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, cornerRestriction_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  simp

/-- `cornerRestriction` composed with `matrixExtension` is the identity on `HCⁿ(A; M)`. -/
@[simp]
theorem cornerRestriction_comp_matrixExtension (r : ι) :
    cornerRestriction (R := R) (A := A) M n r ∘ₗ matrixExtension M ι n = LinearMap.id :=
  LinearMap.ext (cornerRestriction_matrixExtension r)

/-- Matrix extension on cyclic cohomology is injective over every commutative ring `R` for any
nonempty finite index type `ι`. -/
theorem matrixExtension_injective [Nonempty ι] :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (cornerRestriction_matrixExtension r)

/-- Matrix extension on cyclic cohomology commutes with `I : HCⁿ → HHⁿ` over every commutative
ring `R`. -/
@[simp]
theorem toHochschild_matrixExtension (c : cyclicCohomology R A M n) :
    toHochschild R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n (toHochschild R A M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, toHochschild_mk, toHochschild_mk, hochschildCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (coe_matrixCyclicCochainExtension_apply ι n φ.1)

/-- **Matrix Morita invariance of `HCⁿ(A; M)` under low-degree invertibility.** Whenever `q + 1`
is a unit in `R` for every `q < n`, matrix extension on `HCⁿ` is bijective. -/
theorem bijective_matrixExtension_of_isUnit (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have hA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have hM : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  rw [← hM.of_comp_iff', ← LinearMap.coe_comp,
    ← cyclicTotalHomologyMatrixExtension_comp_homologyMap_cyclicCochainComplexToTotal]
  exact (bijective_cyclicTotalHomologyMatrixExtension ι n).comp hA

/-- In degree zero, matrix extension on `HC⁰(A; M)` is bijective over every commutative ring `R`:
every `M`-valued trace on `Matrix ι ι A` is `φ#Tr` for a unique trace `φ` on `A`. -/
theorem bijective_matrixExtension_zero (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 fun q hq => absurd hq (Nat.not_lt_zero q)

/-- In degree one, matrix extension on `HC¹(A; M)` is bijective over every commutative ring `R`. -/
theorem bijective_matrixExtension_one (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 1) :=
  bijective_matrixExtension_of_isUnit ι 1 fun q hq => by
    obtain rfl : q = 0 := by omega
    simp

end GeneralRing

section Rational

variable {R A M : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of cyclic cohomology.** For a unital algebra `A` over a commutative
`ℚ`-algebra `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`, the
matrix extension `φ ↦ φ#Tr` induces a bijection `HCⁿ(A; M) → HCⁿ(Matrix ι ι A; M)` in every
degree `n` (Connes 1985, Part II, Corollary 24). -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ => by
    simpa only [map_add, map_natCast, map_one] using
      (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

/-- Over a `ℚ`-algebra, matrix extension is a left inverse to diagonal corner restriction on
cyclic cohomology. -/
@[simp]
theorem matrixExtension_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M n r c) = c := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨d, rfl⟩ := (bijective_matrixExtension (R := R) (A := A) (M := M) ι n).2 c
  rw [cornerRestriction_matrixExtension]

/-- Over a `ℚ`-algebra, `matrixExtension ∘ₗ cornerRestriction` is the identity on
`HCⁿ(Matrix ι ι A; M)`. -/
@[simp]
theorem matrixExtension_comp_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ cornerRestriction M n r = LinearMap.id :=
  LinearMap.ext (matrixExtension_cornerRestriction r)

/-- Over a `ℚ`-algebra, diagonal corner restriction on `HCⁿ` is independent of the chosen diagonal
corner. -/
theorem cornerRestriction_eq_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r s : ι)
    (n : ℕ) :
    cornerRestriction (R := R) (A := A) M n r = cornerRestriction M n s := by
  refine LinearMap.ext fun c => ?_
  calc
    cornerRestriction M n r c =
        cornerRestriction M n r (matrixExtension M ι n (cornerRestriction M n s c)) := by
      rw [matrixExtension_cornerRestriction]
    _ = cornerRestriction M n s c := cornerRestriction_matrixExtension r _

/-- Over a `ℚ`-algebra, matrix extension on cyclic cohomology commutes with Connes' periodicity
operator `S : HCⁿ → HCⁿ⁺²`. -/
@[simp]
theorem periodicity_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (c : cyclicCohomology R A M n) :
    periodicity R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      matrixExtension M ι (n + 2) (periodicity R A M n c) := by
  apply (bijective_homologyMap_cyclicCochainComplexToTotal R (Matrix ι ι A) M (n + 2)).1
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, periodicity_mk, periodicity_mk,
    ← cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    homologyMap_cyclicCochainComplexToTotal_mk_cyclicCocyclesPeriodicity,
    homologyMap_cyclicCochainComplexToTotal_mk_cyclicCocyclesPeriodicity, map_smul,
    ← cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    matrixExtension_mk]

variable (M) in
/-- Matrix extension as a linear equivalence `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a
`ℚ`-algebra. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Applying `cyclicCohomology.matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {n : ℕ}
    (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- Converting `cyclicCohomology.matrixExtensionEquiv` to a linear map recovers
`matrixExtension`. -/
@[simp]
theorem toLinearMap_matrixExtensionEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` agrees with restriction to any diagonal
corner `r : ι`. -/
theorem matrixExtensionEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (r : ι) {n : ℕ} (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = cornerRestriction M n r c := by
  apply (matrixExtensionEquiv M ι n).injective
  simp

end Rational

end cyclicCohomology

/-! ### Cohomology of finite matrix algebras `Matrix ι ι R` -/

section MatrixGroundRing

section CommRing

variable (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [Nonempty ι]

/-- For any nonempty finite index type `ι` and commutative ring `R`, the Hochschild cohomology
`HHⁿ(Matrix ι ι R, Hom_R(Matrix ι ι R, M))` vanishes in every positive degree `n ≠ 0`. -/
theorem isZero_hochschildCohomology_matrix_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Limits.IsZero (hochschildCohomology R (Matrix ι ι R) M n) := by
  classical
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_hochschildCohomology_self R M hn)
  exact ModuleCat.isZero_iff_subsingleton.2
    (hochschildCohomology.matrixExtensionEquiv (R := R) (A := R) M ι n).symm.injective.subsingleton

/-- For any nonempty finite index type `ι` and commutative ring `R`, the odd periodic cyclic
cohomology `HP¹(Matrix ι ι R; M)` vanishes. -/
theorem isZero_periodicCyclicCohomology_matrix_one :
    Limits.IsZero (periodicCyclicCohomology R (Matrix ι ι R) M 1) := by
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_periodicCyclicCohomology_self_one R M)
  exact ModuleCat.isZero_iff_subsingleton.2
    (periodicCyclicCohomology.matrixExtensionEquiv
      (R := R) (A := R) M ι 1).symm.injective.subsingleton

/-- Over every commutative ring `R`, `M ≃ₗ[R] HC⁰(Matrix ι ι R; M)` via `m ↦ [a₀ ↦ Tr(a₀) • m]`:
every `M`-valued trace on `Matrix ι ι R` is a multiple of the matrix trace. -/
def cyclicCohomology.matrixZeroSelfEquiv [DecidableEq ι] :
    M ≃ₗ[R] cyclicCohomology R (Matrix ι ι R) M 0 :=
  (LinearEquiv.ofBijective (cyclicCohomology.mkPiRing R M 0 Even.zero)
    ⟨cyclicCohomology.mkPiRing_zero_injective R M,
      cyclicCohomology.mkPiRing_surjective R M Even.zero⟩).trans
    (LinearEquiv.ofBijective (cyclicCohomology.matrixExtension M ι 0)
      (cyclicCohomology.bijective_matrixExtension_zero ι))

/-- Evaluating `matrixZeroSelfEquiv` at `m` extends the degree-zero product class `mkPiRing`. -/
@[simp]
theorem cyclicCohomology.matrixZeroSelfEquiv_apply [DecidableEq ι] (m : M) :
    cyclicCohomology.matrixZeroSelfEquiv R M ι m =
      cyclicCohomology.matrixExtension M ι 0 (cyclicCohomology.mkPiRing R M 0 Even.zero m) :=
  (rfl)

end CommRing

section Rational

variable (R M ι : Type*) [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Over a `ℚ`-algebra `R`, the cyclic cohomology `HCⁿ(Matrix ι ι R; M)` vanishes in odd degree. -/
theorem isZero_cyclicCohomology_matrix_of_odd {n : ℕ} (hn : Odd n) :
    Limits.IsZero (cyclicCohomology R (Matrix ι ι R) M n) := by
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_cyclicCohomology_self_of_odd R M hn)
  exact ModuleCat.isZero_iff_subsingleton.2
    (cyclicCohomology.matrixExtensionEquiv (R := R) (A := R) M ι n).symm.injective.subsingleton

/-- Over a `ℚ`-algebra `R`, `M ≃ₗ[R] HCⁿ(Matrix ι ι R; M)` in every even degree `n`, sending
`m : M` to the generalized matrix trace of `(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • m`. -/
def cyclicCohomology.matrixSelfEquiv {n : ℕ} (hn : Even n) :
    M ≃ₗ[R] cyclicCohomology R (Matrix ι ι R) M n :=
  have h2 : IsSMulRegular M (2 : R) := by
    have hu : IsUnit (2 : R) := by
      simpa only [map_ofNat] using (two_ne_zero (α := ℚ)).isUnit.map (algebraMap ℚ R)
    exact hu.isSMulRegular M
  (cyclicCohomology.selfEquiv R M hn h2).trans (cyclicCohomology.matrixExtensionEquiv M ι n)

/-- `matrixSelfEquiv` sends `m : M` to the matrix extension of `mkPiRing R M n hn m`. -/
@[simp]
theorem cyclicCohomology.matrixSelfEquiv_apply {n : ℕ} (hn : Even n) (m : M) :
    cyclicCohomology.matrixSelfEquiv R M ι hn m =
      cyclicCohomology.matrixExtension M ι n (cyclicCohomology.mkPiRing R M n hn m) := by
  simp [cyclicCohomology.matrixSelfEquiv]

end Rational

end MatrixGroundRing

end TauCeti
