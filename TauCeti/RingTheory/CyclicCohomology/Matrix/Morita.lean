/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HochschildCohomology.Matrix
public import TauCeti.RingTheory.CyclicCohomology.PeriodicCohomology
import Mathlib.Algebra.FiveLemma

/-!
# Matrix Morita invariance of cyclic and periodic cyclic cohomology

For a unital `R`-algebra `A`, coefficients in an `R`-module `M` and a nonempty finite index type
`ι`, the generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`) commutes with all
differentials and structural maps of Connes' cyclic bicomplex: the bar coboundary `b'`, the
horizontal and vertical differentials of the bicomplex, the total differential `D = d_h + d_v`,
the column-zero inclusion `C_λ^• → Tot^•`, the projection `I : Tot^• → C^•` onto column zero and
the periodicity shift `S : Tot^m → Tot^(m+2)`.

Passing to cohomology yields natural `R`-linear maps across arbitrary universes for `R`, `A`, `M`
and `ι`:
* `TauCeti.cyclicTotalHomologyMatrixExtension`: `H^n(Tot(A)) →ₗ[R] H^n(Tot(M_ι(A)))`,
* `TauCeti.periodicCyclicCohomology.matrixExtension`: `HP^n(A; M) →ₗ[R] HP^n(M_ι(A); M)`.

Together with `TauCeti.hochschildCohomology.matrixExtension`, `cyclicTotalHomologyMatrixExtension`
gives a morphism of SBI exact sequences (`I`, `B`, `S`) from `A` to `M_ι(A)`. Since matrix
extension is bijective on Hochschild cohomology in every degree
(`TauCeti.hochschildCohomology.bijective_matrixExtension`), strong induction on the degree and the
five lemma (`LinearMap.bijective_of_bijective_of_injective_of_left_exact` at `n = 1` and
`LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective` at `n = m + 2`) prove
that `cyclicTotalHomologyMatrixExtension` is bijective in every degree over any commutative ring
`R` (`TauCeti.bijective_cyclicTotalHomologyMatrixExtension`). Passing to the direct limit along `S`
gives matrix Morita invariance of periodic cyclic cohomology over any commutative ring `R`
(`TauCeti.periodicCyclicCohomology.bijective_matrixExtension`).

On cyclic cohomology `HC^n(A; M)` defined by cyclic cochains, pullback along a diagonal corner
inclusion `a ↦ E_{rr}(a)` (`Matrix.singleNonUnitalAlgHom`) is always a left inverse to
`TauCeti.cyclicCohomology.matrixExtension`, so `matrixExtension` is injective in all degrees over
every commutative ring `R` (`TauCeti.cyclicCohomology.injective_matrixExtension`). Whenever
`1, 2, …, n` are invertible in `R` — unconditionally in degrees `0` and `1`, and in all degrees
when `R` is a `ℚ`-algebra — the column-zero inclusion `C_λ^• → Tot^•` is a quasi-isomorphism in
degree `n` (`TauCeti.quasiIsoAt_cyclicCochainComplexToTotal`), so `cyclicCohomology.matrixExtension`
is bijective (`TauCeti.cyclicCohomology.bijective_matrixExtension`), with inverse given by diagonal
corner pullback.

## Main definitions

* `TauCeti.matrixCyclicTotalCochainExtension`: matrix extension on total cochains of Connes' cyclic
  bicomplex.
* `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`: matrix extension and Morita equivalence on the
  cohomology `H^n(Tot)` of the total cyclic bicomplex.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`: matrix extension and Morita equivalence
  on periodic cyclic cohomology `HP^n(A; M)`.
* `TauCeti.cyclicCohomology.matrixExtensionEquiv`: matrix Morita equivalence
  `HC^n(A; M) ≃ₗ[R] HC^n(Matrix ι ι A; M)` over a `ℚ`-algebra.

## Main results

* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix extension is bijective on
  `H^n(Tot)` in every degree over any commutative ring `R`.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix extension is bijective on
  `HP^n(A; M)` in every degree over any commutative ring `R`.
* `TauCeti.cyclicCohomology.injective_matrixExtension`: matrix extension on `HC^n(A; M)` is
  injective in every degree over any commutative ring `R`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of `HC^n(A; M)`
  when `1, …, n` are invertible in `R`, and in all degrees over a `ℚ`-algebra.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS **62** (1985), Part II,
  Corollary 24, p. 113.
* J.-L. Loday, *Cyclic Homology*, §§1.2, 2.2.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

/-! ### Cochain-level compatibility with the cyclic bicomplex -/

section BicomplexOperators

/-- Matrix extension commutes with the bar coboundary `b'`. -/
theorem matrixCochainExtension_barCoboundary {R A M : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M] [SMulCommClass R R M] (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 1) (barCoboundary R A M n φ) =
      barCoboundary R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  rw [eq_sub_of_add_eq (hochschildCoboundary_eq_barCoboundary_add φ).symm,
    eq_sub_of_add_eq
      (hochschildCoboundary_eq_barCoboundary_add (matrixCochainExtension ι n φ)).symm,
    map_sub, map_zsmul, matrixCochainExtension_hochschildCoboundary,
    matrixCochainExtension_hochschildCoface]

/-- Matrix extension commutes with the horizontal differentials of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal {R A M : Type*} [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι]
    (p q : ℕ) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_cyclicOperator]
  · simp [hp, matrixCochainExtension_cyclicNorm]

/-- Matrix extension commutes with the vertical differentials of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical {R A M : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_hochschildCoboundary]
  · simp [hp, matrixCochainExtension_barCoboundary]

end BicomplexOperators

section TotalCochains

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

/-- Matrix extension of total cochains of degree `m` in Connes' cyclic bicomplex, applying
`matrixCochainExtension ι q` in each row `q`. -/
def matrixCyclicTotalCochainExtension [AddCommMonoid M] [Module R M] (ι : Type*) [Fintype ι]
    (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  LinearMap.codRestrict (cyclicTotalCochains R (Matrix ι ι A) M m)
    (LinearMap.pi fun q ↦
      matrixCochainExtension ι q ∘ₗ LinearMap.proj q ∘ₗ (cyclicTotalCochains R A M m).subtype)
    fun x ↦ mem_cyclicTotalCochains_iff.2 fun q hq ↦ by
      simp [coe_cyclicTotalCochains_apply_of_lt x hq]

/-- In row `q`, the matrix extension of a total cochain `x` is the matrix extension of `x q`. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply [AddCommMonoid M] [Module R M] (ι : Type*)
    [Fintype ι] {m : ℕ} (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixCyclicTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) :=
  (rfl)

/-- Matrix extension of total cochains commutes with the periodicity shift `Tot^m → Tot^(m+2)`. -/
@[simp]
theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity [AddCommMonoid M] [Module R M]
    (ι : Type*) [Fintype ι] {m : ℕ} (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) :=
  Subtype.ext (funext fun q ↦ by simp)

/-- Matrix extension of total cochains commutes with the projection onto column zero. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension [AddCommMonoid M] [Module R M]
    (ι : Type*) [Fintype ι] {m : ℕ} (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by
  simp

/-- Matrix extension of total cochains commutes with the inclusion of cyclic cochains into column
zero. -/
@[simp]
theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] {m : ℕ} (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  rw [coe_matrixCyclicTotalCochainExtension_apply, coe_cyclicCochainsToTotal_apply,
    coe_cyclicCochainsToTotal_apply]
  by_cases hq : q = m
  · subst hq
    simp
  · rw [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne hq, map_zero]

end TotalCochains

section TotalDifferential

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension of total cochains commutes with the total differential `D = d_h + d_v`. -/
@[simp]
theorem cyclicTotalDifferential_matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  cases q with
  | zero =>
    simp [matrixCochainExtension_cyclicBicomplexHorizontal]
  | succ q =>
    simp [matrixCochainExtension_cyclicBicomplexVertical,
      matrixCochainExtension_cyclicBicomplexHorizontal]

/-- Matrix extension carries total cocycles to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker (ι : Type*) [Fintype ι] {m : ℕ}
    {x : cyclicTotalCochains R A M m} (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M m)) :
    matrixCyclicTotalCochainExtension ι m x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hx, map_zero]

end TotalDifferential

/-! ### Induced map on the cohomology of the total cyclic bicomplex -/

section TotalHomology

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Auxiliary lemma: `matrixCyclicTotalCochainExtension` sends total cocycles with zero cohomology
class to total cocycles with zero cohomology class. -/
private theorem cyclicTotalHomologyMk_matrixCyclicTotalCochainExtension_eq_zero (ι : Type*)
    [Fintype ι] {n : ℕ} (x : LinearMap.ker (cyclicTotalDifferential R A M n))
    (hx : cyclicTotalHomologyMk R A M n x = 0) :
    cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixCyclicTotalCochainExtension ι n x.1,
          matrixCyclicTotalCochainExtension_mem_ker ι x.2⟩ = 0 := by
  cases n with
  | zero =>
    rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hx ⊢
    subst hx
    exact Subtype.ext (map_zero _)
  | succ n =>
    rw [cyclicTotalHomologyMk_succ_eq_zero_iff] at hx ⊢
    obtain ⟨w, hw⟩ := hx
    exact ⟨matrixCyclicTotalCochainExtension ι n w, by
      rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hw]⟩

variable (M) in
/-- Matrix extension on the cohomology `H^n(Tot)` of the total cyclic bicomplex, defined across
arbitrary universes for `R`, `A`, `M` and `ι`. -/
def cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    (cyclicTotalComplex R A M).homology n →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  cyclicTotalHomologyDesc n
    (cyclicTotalHomologyMk R (Matrix ι ι A) M n ∘ₗ
      (matrixCyclicTotalCochainExtension ι n).restrict
        fun _ ↦ matrixCyclicTotalCochainExtension_mem_ker ι)
    fun x hx ↦ by
      rw [LinearMap.comp_apply, LinearMap.restrict_apply]
      exact cyclicTotalHomologyMk_matrixCyclicTotalCochainExtension_eq_zero ι x hx

/-- Matrix extension on `H^n(Tot)` sends the class of a total cocycle to the class of its matrix
extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk (ι : Type*) [Fintype ι] {n : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M n)) :
    cyclicTotalHomologyMatrixExtension M ι n (cyclicTotalHomologyMk R A M n x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixCyclicTotalCochainExtension ι n x.1,
          matrixCyclicTotalCochainExtension_mem_ker ι x.2⟩ := by
  rw [cyclicTotalHomologyMatrixExtension, cyclicTotalHomologyDesc_cyclicTotalHomologyMk,
    LinearMap.comp_apply, LinearMap.restrict_apply]

/-- Matrix extension commutes with the column-zero projection `I : H^n(Tot) → HH^n`. -/
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (n : ℕ) (c : (cyclicTotalComplex R A M).homology n) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) n
        (cyclicTotalHomologyMatrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  rw [cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk]
  congr 1

/-- Matrix extension commutes with the periodicity map `S : H^m(Tot) → H^(m+2)(Tot)`. -/
theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι]
    (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      cyclicTotalHomologyMatrixExtension M ι (m + 2)
        (cyclicTotalHomologyPeriodicity R A M m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  rw [cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity ι x.1).symm

/-- Matrix extension commutes with every transition map `S^(j-i)` of the periodic direct system. -/
theorem cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension (ι : Type*)
    [Fintype ι] (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) c) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h c) := by
  induction j, h using Nat.le_induction with
  | base =>
    simp
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hij
        (Nat.le_add_right j 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ModuleCat.comp_apply, ModuleCat.comp_apply, ih,
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ,
      cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension]
    rfl

end TotalHomology

/-! ### Compatibility with cyclic cohomology and the SBI sequence -/

section UnitalSBI

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Matrix extension on cyclic cohomology commutes with the comparison map
`HC^n(A; M) → H^n(Tot)` induced by column-zero inclusion. -/
theorem homologyMap_cyclicCochainComplexToTotal_matrixExtension (ι : Type*) [Fintype ι]
    [DecidableEq ι] (n : ℕ) (c : cyclicCohomology R A M n) :
    HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n
        (cyclicCohomology.matrixExtension M ι n c) =
      cyclicTotalHomologyMatrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M n c
  rw [cyclicCohomology.matrixExtension_mk, homologyMap_cyclicCochainComplexToTotal_mk,
    homologyMap_cyclicCochainComplexToTotal_mk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι φ.1).symm

/-- Matrix extension commutes with Connes' operator `B : HH^(m+1) → H^m(Tot)` of the SBI exact
sequence. -/
theorem cyclicTotalHomologyConnesB_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ)
    (c : hochschildCohomology R A M (m + 1)) :
    cyclicTotalHomologyConnesB R (Matrix ι ι A) M m
        (hochschildCohomology.matrixExtension M ι (m + 1) c) =
      cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyConnesB R A M m c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (m + 1) c
  rw [hochschildCohomology.matrixExtension_mk, cyclicTotalHomologyConnesB_mk,
    cyclicTotalHomologyConnesB_mk, cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1
  apply Subtype.ext
  dsimp only
  rw [matrixCyclicTotalCochainExtension_cyclicCochainsToTotal]
  congr 1
  apply Subtype.ext
  simp [matrixCochainExtension_connesB]

/-- Base case `n = 0` of matrix Morita invariance on `H^n(Tot)`: `I : H^0(Tot) → HH^0` is an
isomorphism for both `A` and `Matrix ι ι A`. -/
private theorem bijective_cyclicTotalHomologyMatrixExtension_zero (ι : Type*) [Fintype ι]
    [Nonempty ι] :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 0) := by
  have hIA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hIMat : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  refine (Function.Bijective.of_comp_iff' hIMat _).1 ?_
  have hcomm :
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0) ∘
        cyclicTotalHomologyMatrixExtension M ι 0 =
      hochschildCohomology.matrixExtension M ι 0 ∘
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0) :=
    funext (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension ι 0)
  rw [hcomm]
  exact (hochschildCohomology.bijective_matrixExtension ι 0).comp hIA

/-- Degree `n = 1` of matrix Morita invariance on `H^n(Tot)`, from the left-exact initial segment
`0 → H^1(Tot) →I HH^1 →B H^0(Tot)` of the SBI sequence. -/
private theorem bijective_cyclicTotalHomologyMatrixExtension_one (ι : Type*) [Fintype ι]
    [Nonempty ι] :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 1) := by
  classical
  refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 1).hom
    (cyclicTotalHomologyConnesB R A M 0).hom
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 1).hom
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M 0).hom
    (cyclicTotalHomologyMatrixExtension M ι 1)
    (hochschildCohomology.matrixExtension M ι 1)
    (cyclicTotalHomologyMatrixExtension M ι 0)
    (LinearMap.ext
      (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension ι 1))
    (LinearMap.ext (cyclicTotalHomologyConnesB_matrixExtension ι 0))
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
    (hochschildCohomology.bijective_matrixExtension ι 1)
    (bijective_cyclicTotalHomologyMatrixExtension_zero ι).1
    injective_homologyMap_cyclicTotalComplexToHochschild_one
    injective_homologyMap_cyclicTotalComplexToHochschild_one

/-- Inductive step `n = m + 2` of matrix Morita invariance on `H^n(Tot)`, applying the five lemma
to `HH^(m+1) →B H^m(Tot) →S H^(m+2)(Tot) →I HH^(m+2) →B H^(m+1)(Tot)`. -/
private theorem bijective_cyclicTotalHomologyMatrixExtension_add_two (ι : Type*) [Fintype ι]
    [Nonempty ι] {m : ℕ}
    (hm : Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι m))
    (hm₁ : Function.Bijective
      (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι (m + 1))) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι (m + 2)) := by
  classical
  refine LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (cyclicTotalHomologyConnesB R A M m).hom
    (cyclicTotalHomologyPeriodicity R A M m).hom
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 2)).hom
    (cyclicTotalHomologyConnesB R A M (m + 1)).hom
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m).hom
    (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m).hom
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) (m + 2)).hom
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M (m + 1)).hom
    (hochschildCohomology.matrixExtension M ι (m + 1))
    (cyclicTotalHomologyMatrixExtension M ι m)
    (cyclicTotalHomologyMatrixExtension M ι (m + 2))
    (hochschildCohomology.matrixExtension M ι (m + 2))
    (cyclicTotalHomologyMatrixExtension M ι (m + 1))
    (LinearMap.ext (cyclicTotalHomologyConnesB_matrixExtension ι m))
    (LinearMap.ext (cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension ι m))
    (LinearMap.ext
      (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension ι (m + 2)))
    (LinearMap.ext (cyclicTotalHomologyConnesB_matrixExtension ι (m + 1)))
    (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m)
    (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M m)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m + 1))
    (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m)
    (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
      R (Matrix ι ι A) M m)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m + 1))
    (hochschildCohomology.bijective_matrixExtension ι (m + 1)).2 hm
    (hochschildCohomology.bijective_matrixExtension ι (m + 2)) hm₁.1

/-- **Matrix Morita invariance of the total cyclic bicomplex.** For a unital algebra `A` over any
commutative ring `R` and a nonempty finite index type `ι`, matrix extension induces a bijection
`H^n(Tot(A)) → H^n(Tot(Matrix ι ι A))` in every degree `n`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => exact bijective_cyclicTotalHomologyMatrixExtension_zero ι
    | 1 => exact bijective_cyclicTotalHomologyMatrixExtension_one ι
    | m + 2 =>
      exact bijective_cyclicTotalHomologyMatrixExtension_add_two ι
        (ih m (by omega)) (ih (m + 1) (by omega))

variable (M) in
/-- **Matrix Morita equivalence for the total cyclic bicomplex.** Matrix extension as an `R`-linear
equivalence `H^n(Tot(A)) ≃ₗ[R] H^n(Tot(Matrix ι ι A))` over any commutative ring `R`. -/
def cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (cyclicTotalComplex R A M).homology n ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι n)
    (bijective_cyclicTotalHomologyMatrixExtension ι n)

/-- The underlying map of `cyclicTotalHomologyMatrixExtensionEquiv` is
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixExtensionEquiv M ι n c =
      cyclicTotalHomologyMatrixExtension M ι n c :=
  (rfl)

end UnitalSBI

/-! ### Matrix Morita invariance of periodic cyclic cohomology -/

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- Matrix extension `HP^n(A; M) →ₗ[R] HP^n(Matrix ι ι A; M)` on periodic cyclic cohomology,
induced on the direct limit of `H^(n+2k)(Tot)` across arbitrary universes for `R`, `A`, `M` and
`ι`. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  lift
    (fun k ↦ (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun k ↦ LinearMap.ext fun c ↦ by
      change periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1)
          (cyclicTotalHomologyMatrixExtension M ι ((n + 2 * k) + 2)
            (cyclicTotalHomologyPeriodicity R A M (n + 2 * k) c)) =
        periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
          (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) c)
      rw [← cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension,
        ← ModuleCat.comp_apply, cyclicTotalHomologyPeriodicity_ι]

/-- Matrix extension on `HP^n` commutes with the canonical stage maps `H^(n+2k)(Tot) → HP^n`. -/
@[simp]
theorem matrixExtension_ι (ι : Type*) [Fintype ι] (n k : ℕ)
    (c : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k c) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) c) :=
  lift_ι _ _ k c

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Over a `ℚ`-algebra, matrix extension on periodic cyclic cohomology commutes with the normalized
stage maps `HC^(n+2k)(A; M) → HP^n(A; M)`. -/
@[simp]
theorem matrixExtension_fromCyclicCohomology [Algebra ℚ R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n k : ℕ) (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix ι ι A) M n k
        (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by
  rw [fromCyclicCohomology_def, fromCyclicCohomology_def]
  simp [homologyMap_cyclicCochainComplexToTotal_matrixExtension]

/-- **Matrix Morita invariance of periodic cyclic cohomology.** For a unital algebra `A` over any
commutative ring `R` and a nonempty finite index type `ι`, matrix extension induces a bijection
`HP^n(A; M) → HP^n(Matrix ι ι A; M)` in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨k, y, rfl⟩ := exists_ι_eq x
    rw [matrixExtension_ι, ι_eq_zero_iff] at hx
    obtain ⟨j, hkj, hj⟩ := hx
    rw [cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension] at hj
    exact (ι_eq_zero_iff y).2 ⟨j, hkj,
      (injective_iff_map_eq_zero _).1
        (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * j)).1 _ hj⟩
  · obtain ⟨k, z, rfl⟩ := exists_ι_eq x
    obtain ⟨y, rfl⟩ := (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * k)).2 z
    exact ⟨periodicCyclicCohomology.ι R A M n k y, matrixExtension_ι ι n k y⟩

variable (M) in
/-- **Matrix Morita equivalence for periodic cyclic cohomology.** Matrix extension as an `R`-linear
equivalence `HP^n(A; M) ≃ₗ[R] HP^n(Matrix ι ι A; M)` over any commutative ring `R`. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The forward map of `periodicCyclicCohomology.matrixExtensionEquiv` is `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

end Unital

end periodicCyclicCohomology

/-! ### Matrix Morita invariance of cyclic cohomology -/

namespace cyclicCohomology

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Pulling back along a diagonal corner inclusion `a ↦ E_{rr}(a)` is a left inverse to matrix
extension on cyclic cohomology, over any commutative ring `R`. -/
@[simp]
theorem pullback_singleNonUnitalAlgHom_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) {n : ℕ} (c : cyclicCohomology R A M n) :
    pullback M (Matrix.singleNonUnitalAlgHom R A r) n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, pullback_mk]
  congr 1
  apply Subtype.ext
  ext x
  simp [MultilinearMap.compLinearMap_apply]

/-- For a nonempty finite matrix index type, matrix extension on cyclic cohomology is injective in
every degree over any commutative ring `R`. -/
theorem injective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (pullback_singleNonUnitalAlgHom_matrixExtension r)

/-- **Matrix Morita invariance of cyclic cohomology at invertible degrees.** If `q + 1` is a unit
in `R` for every `q < n`, then matrix extension induces a bijection
`HC^n(A; M) → HC^n(Matrix ι ι A; M)`. -/
theorem bijective_matrixExtension_of_isUnit (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have htotA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have htotMat : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  refine (Function.Bijective.of_comp_iff' htotMat _).1 ?_
  have hcomm :
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) ∘
        matrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι n ∘
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n) :=
    funext (homologyMap_cyclicCochainComplexToTotal_matrixExtension ι n)
  rw [hcomm]
  exact (bijective_cyclicTotalHomologyMatrixExtension ι n).comp htotA

/-- Matrix extension on `HC^0` is bijective over any commutative ring `R`. -/
theorem bijective_matrixExtension_zero (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 fun q hq ↦ absurd hq (Nat.not_lt_zero q)

/-- Matrix extension on `HC^1` is bijective over any commutative ring `R`. -/
theorem bijective_matrixExtension_one (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 1) :=
  bijective_matrixExtension_of_isUnit ι 1 fun q hq ↦ by
    obtain rfl : q = 0 := by omega
    simp

section Rational

variable [Algebra ℚ R]

/-- **Matrix Morita invariance of cyclic cohomology.** For a unital algebra `A` over a commutative
`ℚ`-algebra `R`, coefficients in an `R`-module `M` and a nonempty finite index type `ι`, the matrix
extension `φ ↦ φ#Tr` induces a bijection `HC^n(A; M) → HC^n(Matrix ι ι A; M)` in every degree
`n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦ by
    simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

/-- Over a `ℚ`-algebra, matrix extension is a right inverse to diagonal corner pullback on cyclic
cohomology. -/
@[simp]
theorem matrixExtension_pullback_singleNonUnitalAlgHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) {n : ℕ} (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (pullback M (Matrix.singleNonUnitalAlgHom R A r) n c) = c := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨x, rfl⟩ := (bijective_matrixExtension ι n).2 c
  rw [pullback_singleNonUnitalAlgHom_matrixExtension]

variable (M) in
/-- **Matrix Morita equivalence for cyclic cohomology.** Matrix extension as an `R`-linear
equivalence `HC^n(A; M) ≃ₗ[R] HC^n(Matrix ι ι A; M)` over a commutative `ℚ`-algebra `R`. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The forward map of `cyclicCohomology.matrixExtensionEquiv` is `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` is pullback along any diagonal corner
inclusion `a ↦ E_{rr}(a)`. -/
theorem matrixExtensionEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (r : ι) {n : ℕ} (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c =
      pullback M (Matrix.singleNonUnitalAlgHom R A r) n c := by
  apply (matrixExtensionEquiv M ι n).injective
  rw [LinearEquiv.apply_symm_apply, matrixExtensionEquiv_apply,
    matrixExtension_pullback_singleNonUnitalAlgHom]

end Rational

end cyclicCohomology

end TauCeti
