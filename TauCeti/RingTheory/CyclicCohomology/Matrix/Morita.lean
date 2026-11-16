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
import TauCeti.Algebra.Algebra.NatCast

/-!
# Matrix Morita invariance of cyclic and periodic cyclic cohomology

Row-wise application of `TauCeti.matrixCochainExtension` on Connes' cyclic bicomplex defines
`TauCeti.matrixCyclicTotalCochainExtension` and `TauCeti.cyclicTotalHomologyMatrixExtension` on
`Hⁿ(Tot)`, compatible with `I`, `B`, and `S`. Using
`TauCeti.hochschildCohomology.bijective_matrixExtension`, strong induction on `n`, and the five
lemma along the SBI sequence, `cyclicTotalHomologyMatrixExtension` is bijective for any unital
algebra over any commutative ring `R` and nonempty finite `ι`; passing to the direct limit proves
Morita invariance of `HPⁿ` (`TauCeti.periodicCyclicCohomology.bijective_matrixExtension`).

When `1, …, n` are units in `R` (so in degrees `0, 1` over any commutative ring and in all degrees
over a `ℚ`-algebra), `TauCeti.quasiIsoAt_cyclicCochainComplexToTotal` gives Morita invariance of
`HCⁿ` (`TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
`TauCeti.cyclicCohomology.bijective_matrixExtension`), with `cornerRestriction` as inverse. For
`Matrix ι ι R`, this yields `HHⁿ = 0` (`n ≠ 0`), `HP¹ = 0`, `HC¹ = 0`, `M ≃ₗ[R] HH⁰`, `M ≃ₗ[R] HP⁰`,
and `M ≃ₗ[R] HC⁰` over any commutative ring `R`, plus `HCⁿ = 0` (odd `n`) and `M ≃ₗ[R] HCⁿ`
(even `n`) whenever `1, …, n` are units in `R`.

## Main definitions and results

* `TauCeti.matrixCyclicTotalCochainExtension`, `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.matrixExtensionEquivOfIsUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`,
  `TauCeti.cyclicCohomology.matrixExtensionEquiv`.
* `TauCeti.hochschildCohomology.matrixZeroSelfEquiv`,
  `TauCeti.periodicCyclicCohomology.matrixZeroSelfEquiv`,
  `TauCeti.cyclicCohomology.matrixZeroSelfEquiv`,
  `TauCeti.cyclicCohomology.matrixSelfEquivOfIsUnit`, `TauCeti.cyclicCohomology.matrixSelfEquiv`.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS **62** (1985), Part II,
  Corollary 24, p. 113; *Noncommutative Geometry* (1994), Chapter III, §1.
* R. McCarthy, *Morita equivalence and cyclic homology*, C. R. Acad. Sci. Paris Sér. I Math.
  **307** (1988), 211–215.
* J.-L. Loday, *Cyclic Homology*, 2nd ed., Springer, 1998, §§1.2, 2.2, 5.1.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

section AddCommMonoid

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M] (ι : Type*) [Fintype ι]

/-- Matrix extension commutes with the horizontal differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) => A) M) :
    matrixCochainExtension (R := R) ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension (R := R) ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp <;>
    simp [hp, matrixCochainExtension_cyclicOperator, matrixCochainExtension_cyclicNorm]

/-- Row-wise matrix extension on total cochains of degree `m` of the cyclic bicomplex. -/
def matrixCyclicTotalCochainExtension (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  LinearMap.codRestrict (cyclicTotalCochains R (Matrix ι ι A) M m)
    (LinearMap.pi fun q => matrixCochainExtension (R := R) ι q ∘ₗ
      LinearMap.proj q ∘ₗ (cyclicTotalCochains R A M m).subtype)
    fun x => mem_cyclicTotalCochains_iff.2 fun q hq => by
      simp [coe_cyclicTotalCochains_apply_of_lt x hq]

/-- The `q`-th row component of `matrixCyclicTotalCochainExtension` is `matrixCochainExtension`. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply {m : ℕ} (x : cyclicTotalCochains R A M m)
    (q : ℕ) : (matrixCyclicTotalCochainExtension ι m x).1 q =
      matrixCochainExtension (R := R) ι q (x.1 q) := (rfl)

/-- Row-wise matrix extension commutes with the column-zero inclusion of cyclic cochains. -/
@[simp] theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal {m : ℕ}
    (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  refine Subtype.ext (funext fun q => ?_)
  simp only [coe_matrixCyclicTotalCochainExtension_apply, coe_cyclicCochainsToTotal_apply,
    coe_matrixCyclicCochainExtension_apply]
  rcases eq_or_ne q m with rfl | hq
  · simp
  · simp [Pi.single_eq_of_ne hq]

/-- Row-wise matrix extension commutes with the projection onto column zero. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension (R := R) ι m (cyclicTotalToHochschild R A M m x) := by
  rw [cyclicTotalToHochschild_apply, cyclicTotalToHochschild_apply,
    coe_matrixCyclicTotalCochainExtension_apply]

/-- Row-wise matrix extension commutes with the periodicity shift on total cochains. -/
@[simp] theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) :=
  Subtype.ext (funext fun q => by
    rw [coe_matrixCyclicTotalCochainExtension_apply, coe_cyclicTotalPeriodicity_apply,
      coe_cyclicTotalPeriodicity_apply, coe_matrixCyclicTotalCochainExtension_apply])

end AddCommMonoid

section NonAssoc

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι]

/-- Matrix extension commutes with the vertical differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) => A) M) :
    matrixCochainExtension (R := R) ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension (R := R) ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp <;>
    simp [hp, matrixCochainExtension_hochschildCoboundary, matrixCochainExtension_barCoboundary]

/-- Row-wise matrix extension commutes with the total differential of the cyclic bicomplex. -/
@[simp] theorem cyclicTotalDifferential_matrixCyclicTotalCochainExtension {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) := by
  refine Subtype.ext (funext fun q => ?_)
  cases q <;> simp [matrixCochainExtension_cyclicBicomplexVertical,
    matrixCochainExtension_cyclicBicomplexHorizontal]

end NonAssoc

section NonUnital

variable {R A M ι : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [Fintype ι] {n : ℕ}

/-- Row-wise matrix extension sends total cocycles to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker {x : cyclicTotalCochains R A M n}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M n)) :
    matrixCyclicTotalCochainExtension ι n x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n) := by
  rw [LinearMap.mem_ker, cyclicTotalDifferential_matrixCyclicTotalCochainExtension,
    LinearMap.mem_ker.1 hx, map_zero]

private theorem cyclicTotalHomologyMk_matrixCyclicTotalCochainExtension_eq_zero
    (x : LinearMap.ker (cyclicTotalDifferential R A M n))
    (hx : cyclicTotalHomologyMk R A M n x = 0) :
    cyclicTotalHomologyMk R (Matrix ι ι A) M n
      ⟨matrixCyclicTotalCochainExtension ι n x.1, matrixCyclicTotalCochainExtension_mem_ker x.2⟩ =
      0 := by
  cases n with
  | zero => rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hx ⊢; rw [hx]; ext q; simp
  | succ k =>
    obtain ⟨w, hw⟩ := (cyclicTotalHomologyMk_succ_eq_zero_iff x).1 hx
    exact (cyclicTotalHomologyMk_succ_eq_zero_iff _).2 ⟨matrixCyclicTotalCochainExtension ι k w,
      by rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hw]⟩

variable (M ι) in
/-- Matrix extension `Hⁿ(Tot(A; M)) →ₗ[R] Hⁿ(Tot(Matrix ι ι A; M))` on total cohomology. -/
def cyclicTotalHomologyMatrixExtension (n : ℕ) :
    (cyclicTotalComplex R A M).homology n →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  cyclicTotalHomologyDesc n (cyclicTotalHomologyMk R (Matrix ι ι A) M n ∘ₗ
      LinearMap.codRestrict (LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n))
        (matrixCyclicTotalCochainExtension ι n ∘ₗ
          (LinearMap.ker (cyclicTotalDifferential R A M n)).subtype)
        fun x => matrixCyclicTotalCochainExtension_mem_ker x.2)
    cyclicTotalHomologyMk_matrixCyclicTotalCochainExtension_eq_zero

/-- `cyclicTotalHomologyMatrixExtension` sends `[x]` to the class of its row-wise extension. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk
    (x : LinearMap.ker (cyclicTotalDifferential R A M n)) :
    cyclicTotalHomologyMatrixExtension M ι n (cyclicTotalHomologyMk R A M n x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M n ⟨matrixCyclicTotalCochainExtension ι n x.1,
        matrixCyclicTotalCochainExtension_mem_ker x.2⟩ :=
  cyclicTotalHomologyDesc_cyclicTotalHomologyMk _ _ _ x

/-- Matrix extension on `Hⁿ(Tot)` commutes with the projection `I` onto Hochschild cohomology. -/
@[simp] theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension
    (c : (cyclicTotalComplex R A M).homology n) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) n
        (cyclicTotalHomologyMatrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  simp only [cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk, coe_matrixCyclicTotalCochainExtension_apply]

/-- Composite form of compatibility between `cyclicTotalHomologyMatrixExtension` and `I`. -/
theorem homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension (n : ℕ) :
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) n).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι n =
      hochschildCohomology.matrixExtension M ι n ∘ₗ
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n).hom :=
  LinearMap.ext homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension

/-- Matrix extension on `Hⁿ(Tot)` commutes with the bicomplex periodicity map `S`. -/
@[simp] theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M n
        (cyclicTotalHomologyMatrixExtension M ι n c) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2)
        (cyclicTotalHomologyPeriodicity R A M n c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  simp only [cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk]
  exact congrArg _ <| Subtype.ext <|
    (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity ι x.1).symm

/-- Composite form of compatibility between `cyclicTotalHomologyMatrixExtension` and `S`. -/
theorem cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension (n : ℕ) :
    (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M n).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι (n + 2) ∘ₗ
        (cyclicTotalHomologyPeriodicity R A M n).hom :=
  LinearMap.ext cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension

/-- Matrix extension on `Hⁿ(Tot)` commutes with every transition map of the periodic system. -/
@[simp] theorem cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension {i j : ℕ}
    (h : i ≤ j) (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) c) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h c) := by
  induction j, h using Nat.le_induction with
  | base => simp [cyclicTotalHomologyPeriodicTransition_self]
  | succ k hik ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hik
        (Nat.le_add_right k 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R A M n hik (Nat.le_add_right k 1),
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ,
      ModuleCat.comp_apply, ModuleCat.comp_apply, ih,
      cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension]; rfl

end NonUnital

section UnitalSquares

variable {R A M ι : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Matrix extension on `Hⁿ(Tot)` commutes with the column-zero inclusion from `HCⁿ`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal
    (c : cyclicCohomology R A M n) :
    cyclicTotalHomologyMatrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n c) =
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n
        (cyclicCohomology.matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M n c
  simp only [homologyMap_cyclicCochainComplexToTotal_mk, cyclicCohomology.matrixExtension_mk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  exact congrArg _ (Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι φ.1))

/-- Composite form of compatibility between matrix extension on `HCⁿ` and on `Hⁿ(Tot)`. -/
theorem cyclicTotalHomologyMatrixExtension_comp_homologyMap_cyclicCochainComplexToTotal (n : ℕ) :
    cyclicTotalHomologyMatrixExtension M ι n ∘ₗ
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n).hom =
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n).hom ∘ₗ
        cyclicCohomology.matrixExtension M ι n :=
  LinearMap.ext cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal

/-- Matrix extension commutes with Connes' operator `B : HHⁿ⁺¹ → HCⁿ`. -/
@[simp]
theorem cyclicCohomology.matrixExtension_connesB (c : hochschildCohomology R A M (n + 1)) :
    cyclicCohomology.matrixExtension M ι n (hochschildCohomology.connesB R A M n c) =
      hochschildCohomology.connesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (n + 1) c
  simp only [hochschildCohomology.connesB_mk, cyclicCohomology.matrixExtension_mk,
    hochschildCohomology.matrixExtension_mk]
  exact congrArg _ (Subtype.ext <| Subtype.ext <|
    (coe_matrixCyclicCochainExtension_apply ι n _).trans (matrixCochainExtension_connesB ι n φ.1))

/-- Composite form of compatibility between matrix extension and `hochschildCohomology.connesB`. -/
theorem cyclicCohomology.matrixExtension_comp_connesB (n : ℕ) :
    cyclicCohomology.matrixExtension M ι n ∘ₗ (hochschildCohomology.connesB R A M n).hom =
      (hochschildCohomology.connesB R (Matrix ι ι A) M n).hom ∘ₗ
        hochschildCohomology.matrixExtension M ι (n + 1) :=
  LinearMap.ext cyclicCohomology.matrixExtension_connesB

/-- Matrix extension on `Hⁿ(Tot)` commutes with the connecting map `B : HHⁿ⁺¹ → Hⁿ(Tot)`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB
    (c : hochschildCohomology R A M (n + 1)) :
    cyclicTotalHomologyMatrixExtension M ι n (cyclicTotalHomologyConnesB R A M n c) =
      cyclicTotalHomologyConnesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.comp_apply,
    ModuleCat.comp_apply,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    cyclicCohomology.matrixExtension_connesB]

/-- Composite form of compatibility between `cyclicTotalHomologyMatrixExtension` and `B`. -/
theorem cyclicTotalHomologyConnesB_comp_hochschildCohomologyMatrixExtension (n : ℕ) :
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M n).hom ∘ₗ
        hochschildCohomology.matrixExtension M ι (n + 1) =
      cyclicTotalHomologyMatrixExtension M ι n ∘ₗ (cyclicTotalHomologyConnesB R A M n).hom :=
  LinearMap.ext fun c => (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB c).symm

end UnitalSquares

section TotalBijective

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance on the total cyclic bicomplex** over any commutative ring `R`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  classical
  let extT := cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι
  let extH := hochschildCohomology.matrixExtension (R := R) (A := A) M ι
  let IA (d : ℕ) := (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) d).hom
  let IM (d : ℕ) :=
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) d).hom
  let BA (d : ℕ) := (cyclicTotalHomologyConnesB R A M d).hom
  let BM (d : ℕ) := (cyclicTotalHomologyConnesB R (Matrix ι ι A) M d).hom
  refine Nat.strongRecOn n fun m ih => ?_
  match m with
  | 0 =>
    rw [← ((ConcreteCategory.isIso_iff_bijective (HomologicalComplex.homologyMap
        (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0)).1 inferInstance).of_comp_iff',
      ← LinearMap.coe_comp,
      homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension]
    exact (hochschildCohomology.bijective_matrixExtension ι 0).comp
      ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance)
  | 1 =>
    exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
      (IA 1) (BA 0) (IM 1) (BM 0) (extT 1) (extH 1) (extT 0)
      (homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension 1)
      (cyclicTotalHomologyConnesB_comp_hochschildCohomologyMatrixExtension 0)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
      (hochschildCohomology.bijective_matrixExtension ι 1) (ih 0 one_pos).1
      injective_homologyMap_cyclicTotalComplexToHochschild_one
      injective_homologyMap_cyclicTotalComplexToHochschild_one
  | k + 2 =>
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (BA k) (cyclicTotalHomologyPeriodicity R A M k).hom (IA (k + 2)) (BA (k + 1))
      (BM k) (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M k).hom (IM (k + 2)) (BM (k + 1))
      (extH (k + 1)) (extT k) (extT (k + 2)) (extH (k + 2)) (extT (k + 1))
      (cyclicTotalHomologyConnesB_comp_hochschildCohomologyMatrixExtension k)
      (cyclicTotalHomologyPeriodicity_comp_cyclicTotalHomologyMatrixExtension k)
      (homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension (k + 2))
      (cyclicTotalHomologyConnesB_comp_hochschildCohomologyMatrixExtension (k + 1))
      (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity k)
      (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M k)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (k + 1))
      (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity k)
      (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
        R (Matrix ι ι A) M k)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (k + 1))
      (hochschildCohomology.bijective_matrixExtension ι (k + 1)).2 (ih k (by omega))
      (hochschildCohomology.bijective_matrixExtension ι (k + 2)) (ih (k + 1) (by omega)).1

variable (M) in
/-- Matrix extension on `Hⁿ(Tot)` as a linear equivalence for unital `A` and nonempty finite `ι`. -/
def cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (cyclicTotalComplex R A M).homology n ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι n)
    (bijective_cyclicTotalHomologyMatrixExtension ι n)

/-- Applying `cyclicTotalHomologyMatrixExtensionEquiv` agrees with the linear map. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_apply {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixExtensionEquiv M ι n c =
      cyclicTotalHomologyMatrixExtension M ι n c := (rfl)

/-- Coercing `cyclicTotalHomologyMatrixExtensionEquiv` recovers the linear map. -/
@[simp]
theorem toLinearMap_cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) : (cyclicTotalHomologyMatrixExtensionEquiv (R := R) (A := A) M ι n :
      (cyclicTotalComplex R A M).homology n →ₗ[R]
        (cyclicTotalComplex R (Matrix ι ι A) M).homology n) =
      cyclicTotalHomologyMatrixExtension M ι n := (rfl)

end TotalBijective

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- Matrix extension `HPⁿ(A; M) →ₗ[R] HPⁿ(Matrix ι ι A; M)` on periodic cyclic cohomology. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  descLinearMap (fun k => (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * k)) fun k y => by
    have h1 := (cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension
      (ι := ι) (Nat.le_add_right k 1) y).symm
    rw [cyclicTotalHomologyPeriodicTransition_succ R A M] at h1
    exact (congrArg (periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1)) h1).trans
      (cyclicTotalHomologyPeriodicTransition_ι_apply (Nat.le_add_right k 1) _)

/-- Matrix extension on `HPⁿ` commutes with the canonical stage maps `ι`. -/
@[simp] theorem matrixExtension_ι {ι : Type*} [Fintype ι] (n k : ℕ)
    (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k y) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) y) := descLinearMap_ι _ _ k y

/-- Composing `matrixExtension` with stage `k` equals `ι ∘ₗ cyclicTotalHomologyMatrixExtension`. -/
@[simp] theorem matrixExtension_comp_ι {ι : Type*} [Fintype ι] (n k : ℕ) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ (periodicCyclicCohomology.ι R A M n k).hom =
      (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) := LinearMap.ext (matrixExtension_ι n k)

private theorem cyclicTotalHomologyMatrixExtension_eqToHom {ι : Type*} [Fintype ι] {m m' : ℕ}
    (hm : m = m') (y : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyMatrixExtension M ι m'
        (eqToHom (congrArg (fun i => (cyclicTotalComplex R A M).homology i) hm) y) =
      eqToHom (congrArg (fun i => (cyclicTotalComplex R (Matrix ι ι A) M).homology i) hm)
        (cyclicTotalHomologyMatrixExtension M ι m y) := by
  subst hm; simp

/-- Matrix extension on `HPⁿ` commutes with the `2`-periodicity isomorphism `shiftIso`. -/
@[simp] theorem shiftIso_hom_matrixExtension {ι : Type*} [Fintype ι] (n : ℕ)
    (x : periodicCyclicCohomology R A M (n + 2)) :
    (shiftIso R (Matrix ι ι A) M n).hom (matrixExtension M ι (n + 2) x) =
      matrixExtension M ι n ((shiftIso R A M n).hom x) := by
  obtain ⟨k, y, rfl⟩ := exists_ι_eq x
  have hA := congrArg (fun f => f y) (ι_shiftIso_hom R A M n k)
  have hM := congrArg
    (fun f => f (cyclicTotalHomologyMatrixExtension M ι (n + 2 + 2 * k) y))
    (ι_shiftIso_hom R (Matrix ι ι A) M n k)
  simp only [ModuleCat.comp_apply] at hA hM; rw [matrixExtension_ι]
  exact hM.trans <|
    (congrArg (periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1))
      (cyclicTotalHomologyMatrixExtension_eqToHom (by omega) y).symm).trans <|
    (matrixExtension_ι n (k + 1) _).symm.trans (congrArg (matrixExtension M ι n) hA.symm)

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of periodic cyclic cohomology** over any commutative ring `R`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun z => ?_⟩
  · obtain ⟨k, y, rfl⟩ := exists_ι_eq x
    rw [matrixExtension_ι, ι_eq_zero_iff] at hx; obtain ⟨j, hkj, hj⟩ := hx
    rw [cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension] at hj
    exact (ι_eq_zero_iff y).2 ⟨j, hkj,
      (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * j)).1 (hj.trans (map_zero _).symm)⟩
  · obtain ⟨k, w, rfl⟩ := exists_ι_eq z
    obtain ⟨y, rfl⟩ := (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * k)).2 w
    exact ⟨periodicCyclicCohomology.ι R A M n k y, matrixExtension_ι n k y⟩

variable (M) in
/-- Matrix extension as a linear equivalence `HPⁿ(A; M) ≃ₗ[R] HPⁿ(Matrix ι ι A; M)`. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Applying `periodicCyclicCohomology.matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp] theorem matrixExtensionEquiv_apply {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (x : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n x = matrixExtension M ι n x := (rfl)

/-- Coercing `periodicCyclicCohomology.matrixExtensionEquiv` recovers `matrixExtension`. -/
@[simp] theorem toLinearMap_matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := (rfl)

end Unital

section Rational

variable {R A M ι : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Fintype ι] [DecidableEq ι]

/-- Over a `ℚ`-algebra, matrix extension on `HPⁿ` commutes with `fromCyclicCohomology`. -/
@[simp]
theorem matrixExtension_fromCyclicCohomology (n k : ℕ) (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) = fromCyclicCohomology
      R (Matrix ι ι A) M n k (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by
  rw [fromCyclicCohomology_apply, fromCyclicCohomology_apply, map_smul, matrixExtension_ι,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]

end Rational

end periodicCyclicCohomology

namespace cyclicCohomology

section GeneralRing

variable {R A M ι : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Matrix extension on cyclic cohomology commutes with `I : HCⁿ → HHⁿ`. -/
@[simp] theorem toHochschild_matrixExtension (c : cyclicCohomology R A M n) :
    toHochschild R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n (toHochschild R A M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, toHochschild_mk, toHochschild_mk, hochschildCohomology.matrixExtension_mk]
  exact congrArg _ (Subtype.ext (coe_matrixCyclicCochainExtension_apply ι n φ.1))

/-- **Matrix Morita invariance of `HCⁿ(A; M)`** when `q + 1` is a unit in `R` for all `q < n`. -/
theorem bijective_matrixExtension_of_isUnit (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have hA := (ConcreteCategory.isIso_iff_bijective _).1
    ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have hM := (ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
    (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  rw [← hM.of_comp_iff', ← LinearMap.coe_comp,
    ← cyclicTotalHomologyMatrixExtension_comp_homologyMap_cyclicCochainComplexToTotal]
  exact (bijective_cyclicTotalHomologyMatrixExtension ι n).comp hA

/-- In degree zero, matrix extension on `HC⁰(A; M)` is bijective over every commutative ring `R`. -/
theorem bijective_matrixExtension_zero (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 fun q hq => absurd hq (Nat.not_lt_zero q)

/-- In degree one, matrix extension on `HC¹(A; M)` is bijective over every commutative ring `R`. -/
theorem bijective_matrixExtension_one (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 1) :=
  bijective_matrixExtension_of_isUnit ι 1 fun _ hq => by simp [Nat.lt_one_iff.1 hq]

/-- When `q + 1` is a unit in `R` for `q < n`, `matrixExtension` is left inverse to
`cornerRestriction`. -/
theorem matrixExtension_cornerRestriction_of_isUnit (r : ι) (hR : ∀ q < n, IsUnit ((q : R) + 1))
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M n r c) = c := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨d, rfl⟩ := (bijective_matrixExtension_of_isUnit (R := R) (A := A) (M := M) ι n hR).2 c
  rw [cornerRestriction_matrixExtension]

/-- Composite form of `matrixExtension_cornerRestriction_of_isUnit`. -/
theorem matrixExtension_comp_cornerRestriction_of_isUnit (r : ι) (n : ℕ)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ cornerRestriction M n r = LinearMap.id :=
  LinearMap.ext (matrixExtension_cornerRestriction_of_isUnit r hR)

/-- In degree zero, `matrixExtension` is left inverse to `cornerRestriction` over any `R`. -/
@[simp]
theorem matrixExtension_cornerRestriction_zero (r : ι) (c : cyclicCohomology R (Matrix ι ι A) M 0) :
    matrixExtension M ι 0 (cornerRestriction M 0 r c) = c :=
  matrixExtension_cornerRestriction_of_isUnit r (fun q hq => absurd hq (Nat.not_lt_zero q)) c

/-- In degree one, `matrixExtension` is left inverse to `cornerRestriction` over any `R`. -/
@[simp]
theorem matrixExtension_cornerRestriction_one (r : ι) (c : cyclicCohomology R (Matrix ι ι A) M 1) :
    matrixExtension M ι 1 (cornerRestriction M 1 r c) = c :=
  matrixExtension_cornerRestriction_of_isUnit r (fun _ hq => by simp [Nat.lt_one_iff.1 hq]) c

/-- Whenever `q + 1` is a unit in `R` for `q < n`, `cornerRestriction` is independent of `r : ι`. -/
theorem cornerRestriction_eq_cornerRestriction_of_isUnit (r s : ι) (n : ℕ)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    cornerRestriction (R := R) (A := A) M n r = cornerRestriction M n s :=
  LinearMap.ext fun c => by
    conv_lhs =>
      rw [← matrixExtension_cornerRestriction_of_isUnit s hR c, cornerRestriction_matrixExtension]

/-- Whenever `q + 1` is a unit in `R` for all `q < n`, `cornerRestriction` on `HCⁿ` is bijective. -/
theorem bijective_cornerRestriction_of_isUnit (r : ι) (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (cornerRestriction (R := R) (A := A) M n r) :=
  ⟨Function.LeftInverse.injective (matrixExtension_cornerRestriction_of_isUnit r hR),
    Function.RightInverse.surjective (cornerRestriction_matrixExtension r)⟩

variable (M) in
/-- Matrix extension equivalence `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` under unit hypotheses. -/
def matrixExtensionEquivOfIsUnit (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension_of_isUnit ι n hR)

/-- Applying `matrixExtensionEquivOfIsUnit` agrees with `matrixExtension`. -/
@[simp] theorem matrixExtensionEquivOfIsUnit_apply [Nonempty ι]
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) (c : cyclicCohomology R A M n) :
    matrixExtensionEquivOfIsUnit M ι n hR c = matrixExtension M ι n c := (rfl)

/-- Coercing `matrixExtensionEquivOfIsUnit` recovers `matrixExtension`. -/
@[simp] theorem toLinearMap_matrixExtensionEquivOfIsUnit [Nonempty ι] (n : ℕ)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    (matrixExtensionEquivOfIsUnit (R := R) (A := A) M ι n hR :
      cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := (rfl)

/-- The inverse of `matrixExtensionEquivOfIsUnit` agrees with `cornerRestriction M n r`. -/
theorem matrixExtensionEquivOfIsUnit_symm_apply [Nonempty ι] (r : ι)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquivOfIsUnit M ι n hR).symm c = cornerRestriction M n r c := by
  apply (matrixExtensionEquivOfIsUnit M ι n hR).injective
  simp [matrixExtension_cornerRestriction_of_isUnit r hR]

end GeneralRing

section Rational

variable {R A M ι : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Fintype ι] [DecidableEq ι]

/-- **Matrix Morita invariance of cyclic cohomology** over a `ℚ`-algebra (Connes 1985, Cor. 24). -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ => isUnit_natCast_add_one q

/-- Over a `ℚ`-algebra, `matrixExtension` is a left inverse to `cornerRestriction` on `HCⁿ`. -/
@[simp] theorem matrixExtension_cornerRestriction (r : ι) {n : ℕ}
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M n r c) = c :=
  matrixExtension_cornerRestriction_of_isUnit r (fun q _ => isUnit_natCast_add_one q) c

/-- Over a `ℚ`-algebra, `matrixExtension ∘ₗ cornerRestriction = id` on `HCⁿ(Matrix ι ι A; M)`. -/
@[simp] theorem matrixExtension_comp_cornerRestriction (r : ι) (n : ℕ) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ cornerRestriction M n r = LinearMap.id :=
  LinearMap.ext (matrixExtension_cornerRestriction r)

/-- Over a `ℚ`-algebra, `cornerRestriction` on `HCⁿ` is independent of `r : ι`. -/
theorem cornerRestriction_eq_cornerRestriction (r s : ι) (n : ℕ) :
    cornerRestriction (R := R) (A := A) M n r = cornerRestriction M n s :=
  cornerRestriction_eq_cornerRestriction_of_isUnit r s n fun q _ => isUnit_natCast_add_one q

/-- Over a `ℚ`-algebra, `cornerRestriction` on `HCⁿ` is bijective. -/
theorem bijective_cornerRestriction (r : ι) (n : ℕ) :
    Function.Bijective (cornerRestriction (R := R) (A := A) M n r) :=
  bijective_cornerRestriction_of_isUnit r n fun q _ => isUnit_natCast_add_one q

/-- Over a `ℚ`-algebra, `matrixExtension` commutes with Connes' periodicity `S : HCⁿ → HCⁿ⁺²`. -/
@[simp] theorem periodicity_matrixExtension {n : ℕ} (c : cyclicCohomology R A M n) :
    periodicity R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      matrixExtension M ι (n + 2) (periodicity R A M n c) := by
  apply (bijective_homologyMap_cyclicCochainComplexToTotal R (Matrix ι ι A) M (n + 2)).1
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, periodicity_mk, periodicity_mk,
    ← cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    homologyMap_cyclicCochainComplexToTotal_mk_cyclicCocyclesPeriodicity,
    homologyMap_cyclicCochainComplexToTotal_mk_cyclicCocyclesPeriodicity, map_smul,
    ← cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal, matrixExtension_mk]

variable (M) in
/-- Matrix extension as `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a `ℚ`-algebra. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  matrixExtensionEquivOfIsUnit M ι n fun q _ => isUnit_natCast_add_one q

/-- Applying `cyclicCohomology.matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp] theorem matrixExtensionEquiv_apply [Nonempty ι] {n : ℕ} (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c := (rfl)

/-- Coercing `cyclicCohomology.matrixExtensionEquiv` recovers `matrixExtension`. -/
@[simp] theorem toLinearMap_matrixExtensionEquiv [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := (rfl)

/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` agrees with `cornerRestriction`. -/
theorem matrixExtensionEquiv_symm_apply [Nonempty ι] (r : ι) {n : ℕ}
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = cornerRestriction M n r c :=
  matrixExtensionEquivOfIsUnit_symm_apply r (fun q _ => isUnit_natCast_add_one q) c

end Rational

end cyclicCohomology

section CommRing

variable (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [Nonempty ι]

omit [AddCommGroup M] [Module R M] [Fintype ι] [Nonempty ι] in
private theorem isZero_of_equiv {X : ModuleCat R} {Y : ModuleCat R} (hX : Limits.IsZero X)
    (e : X ≃ₗ[R] Y) : Limits.IsZero Y := by
  have := ModuleCat.isZero_iff_subsingleton.1 hX
  exact ModuleCat.isZero_iff_subsingleton.2 e.symm.injective.subsingleton

/-- For nonempty finite `ι` and commutative `R`, `HHⁿ(Matrix ι ι R; M)` vanishes for `n ≠ 0`. -/
theorem isZero_hochschildCohomology_matrix_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Limits.IsZero (hochschildCohomology R (Matrix ι ι R) M n) :=
  isZero_of_equiv R (isZero_hochschildCohomology_self R M hn)
    (hochschildCohomology.matrixExtensionEquiv M ι n)

/-- `HPⁿ(Matrix ι ι R; M)` stabilizes at stage `0`: `ι : Hⁿ(Tot) ⟶ HPⁿ` is an isomorphism. -/
instance periodicCyclicCohomology.isIso_ι_matrix (n : ℕ) :
    IsIso (periodicCyclicCohomology.ι R (Matrix ι ι R) M n 0) := by
  classical
  exact periodicCyclicCohomology.isIso_ι_of_isZero_hochschildCohomology fun _ hm =>
    isZero_hochschildCohomology_matrix_of_ne_zero R M ι (Nat.ne_zero_of_lt hm)

/-- Over every commutative ring `R`, `HP¹(Matrix ι ι R; M)` vanishes. -/
theorem isZero_periodicCyclicCohomology_matrix_one :
    Limits.IsZero (periodicCyclicCohomology R (Matrix ι ι R) M 1) :=
  isZero_of_equiv R (isZero_periodicCyclicCohomology_self_one R M)
    (periodicCyclicCohomology.matrixExtensionEquiv M ι 1)

omit [Fintype ι] [Nonempty ι] in
private theorem bijective_mkPiRing_of_isUnit {n : ℕ} (hn : Even n)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (cyclicCohomology.mkPiRing R M n hn) := by
  refine ⟨?_, cyclicCohomology.mkPiRing_surjective R M hn⟩
  rcases eq_or_ne n 0 with rfl | hn0
  · exact cyclicCohomology.mkPiRing_zero_injective R M
  · have h2 : IsUnit (2 : R) := by
      simpa [one_add_one_eq_two] using hR 1 (by obtain ⟨k, rfl⟩ := hn; omega)
    exact cyclicCohomology.mkPiRing_injective R M hn (h2.isSMulRegular M)

omit [Fintype ι] [Nonempty ι] in
private def mkPiRingZeroEquiv : M ≃ₗ[R] cyclicCohomology R R M 0 :=
  LinearEquiv.ofBijective (cyclicCohomology.mkPiRing R M 0 Even.zero)
    ⟨cyclicCohomology.mkPiRing_zero_injective R M,
      cyclicCohomology.mkPiRing_surjective R M Even.zero⟩

omit [AddCommGroup M] [Module R M] [Fintype ι] [Nonempty ι] in
private def linearEquivOfIsIso {X Y : ModuleCat R} (f : X ⟶ Y) [IsIso f] : X ≃ₗ[R] Y :=
  LinearEquiv.ofBijective f.hom ((ConcreteCategory.isIso_iff_bijective f).1 inferInstance)

/-- Over every commutative ring `R`, `M ≃ₗ[R] HH⁰(Matrix ι ι R, Hom_R(Matrix ι ι R, M))`. -/
def hochschildCohomology.matrixZeroSelfEquiv :
    M ≃ₗ[R] hochschildCohomology R (Matrix ι ι R) M 0 :=
  (mkPiRingZeroEquiv R M).trans <|
    (linearEquivOfIsIso R (cyclicCohomology.toHochschild R R M 0)).trans
      (hochschildCohomology.matrixExtensionEquiv M ι 0)

/-- Evaluating `hochschildCohomology.matrixZeroSelfEquiv` extends `toHochschild (mkPiRing … m)`. -/
@[simp] theorem hochschildCohomology.matrixZeroSelfEquiv_apply (m : M) :
    hochschildCohomology.matrixZeroSelfEquiv R M ι m = hochschildCohomology.matrixExtension M ι 0
      (cyclicCohomology.toHochschild R R M 0 (cyclicCohomology.mkPiRing R M 0 Even.zero m)) := by
  simp only [hochschildCohomology.matrixZeroSelfEquiv, mkPiRingZeroEquiv, linearEquivOfIsIso,
    LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    hochschildCohomology.matrixExtensionEquiv_apply]; rfl

/-- Over every commutative ring `R`, `M ≃ₗ[R] HP⁰(Matrix ι ι R; M)` via stage `0`. -/
def periodicCyclicCohomology.matrixZeroSelfEquiv :
    M ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι R) M 0 :=
  (mkPiRingZeroEquiv R M).trans <| (LinearEquiv.ofBijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R R M) 0).hom
      ((ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        (quasiIsoAt_cyclicCochainComplexToTotal R R M 0 fun q hq =>
          absurd hq (Nat.not_lt_zero q))))).trans <|
    (linearEquivOfIsIso R (periodicCyclicCohomology.ι R R M 0 0)).trans
      (periodicCyclicCohomology.matrixExtensionEquiv M ι 0)

/-- Evaluating `periodicCyclicCohomology.matrixZeroSelfEquiv` sends `m` to stage `0`. -/
@[simp] theorem periodicCyclicCohomology.matrixZeroSelfEquiv_apply (m : M) :
    periodicCyclicCohomology.matrixZeroSelfEquiv R M ι m =
      periodicCyclicCohomology.ι R (Matrix ι ι R) M 0 0
        (cyclicTotalHomologyMatrixExtension M ι 0
          (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R R M) 0
            (cyclicCohomology.mkPiRing R M 0 Even.zero m))) := by
  simp only [periodicCyclicCohomology.matrixZeroSelfEquiv, mkPiRingZeroEquiv, linearEquivOfIsIso,
    LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    periodicCyclicCohomology.matrixExtensionEquiv_apply]
  exact periodicCyclicCohomology.matrixExtension_ι 0 0 _

section Decidable

variable [DecidableEq ι]

/-- Whenever `q + 1` is a unit in `R` for all `q < n`, odd `HCⁿ(Matrix ι ι R; M)` vanishes. -/
theorem isZero_cyclicCohomology_matrix_of_odd_of_isUnit {n : ℕ} (hn : Odd n)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Limits.IsZero (cyclicCohomology R (Matrix ι ι R) M n) :=
  isZero_of_equiv R (isZero_cyclicCohomology_self_of_odd R M hn)
    (cyclicCohomology.matrixExtensionEquivOfIsUnit M ι n hR)

/-- Over every commutative ring `R`, `HC¹(Matrix ι ι R; M)` vanishes. -/
theorem isZero_cyclicCohomology_matrix_one :
    Limits.IsZero (cyclicCohomology R (Matrix ι ι R) M 1) :=
  isZero_cyclicCohomology_matrix_of_odd_of_isUnit R M ι ⟨0, rfl⟩ fun _ hq => by
    simp [Nat.lt_one_iff.1 hq]

/-- Even-degree equivalence `M ≃ₗ[R] HCⁿ(Matrix ι ι R; M)` when `q + 1` is a unit for `q < n`. -/
def cyclicCohomology.matrixSelfEquivOfIsUnit {n : ℕ} (hn : Even n)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) : M ≃ₗ[R] cyclicCohomology R (Matrix ι ι R) M n :=
  (LinearEquiv.ofBijective (cyclicCohomology.mkPiRing R M n hn)
    (bijective_mkPiRing_of_isUnit R M hn hR)).trans
    (cyclicCohomology.matrixExtensionEquivOfIsUnit M ι n hR)

/-- `matrixSelfEquivOfIsUnit` sends `m` to `matrixExtension (mkPiRing R M n hn m)`. -/
@[simp] theorem cyclicCohomology.matrixSelfEquivOfIsUnit_apply {n : ℕ} (hn : Even n)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) (m : M) :
    cyclicCohomology.matrixSelfEquivOfIsUnit R M ι hn hR m =
      cyclicCohomology.matrixExtension M ι n (cyclicCohomology.mkPiRing R M n hn m) := (rfl)

/-- `(matrixSelfEquivOfIsUnit …).symm [Φ]` evaluates `Φ` at `fun _ => Matrix.single r r 1`. -/
theorem cyclicCohomology.matrixSelfEquivOfIsUnit_symm_mk (r : ι) {n : ℕ} (hn : Even n)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) (Φ : cyclicCocycles R (Matrix ι ι R) M n) :
    (cyclicCohomology.matrixSelfEquivOfIsUnit R M ι hn hR).symm
        (cyclicCohomology.mk R (Matrix ι ι R) M n Φ) =
      (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι R) M)
        fun _ => Matrix.single r r 1 := by
  rw [LinearEquiv.symm_apply_eq, cyclicCohomology.matrixSelfEquivOfIsUnit_apply]
  apply (cyclicCohomology.bijective_cornerRestriction_of_isUnit r n hR).1
  rw [cyclicCohomology.cornerRestriction_matrixExtension, cyclicCohomology.cornerRestriction_mk,
    cyclicCohomology.mk_eq_mkPiRing R M hn]; congr 1; simp

/-- If `2` is `M`-regular, `(matrixSelfEquivOfIsUnit …).symm` factors via `cornerRestriction`. -/
theorem cyclicCohomology.matrixSelfEquivOfIsUnit_symm_apply (r : ι) {n : ℕ} (hn : Even n)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) (h2 : IsSMulRegular M (2 : R))
    (c : cyclicCohomology R (Matrix ι ι R) M n) :
    (cyclicCohomology.matrixSelfEquivOfIsUnit R M ι hn hR).symm c =
      (cyclicCohomology.selfEquiv R M hn h2).symm (cyclicCohomology.cornerRestriction M n r c) := by
  obtain ⟨Φ, rfl⟩ := cyclicCohomology.mk_surjective R (Matrix ι ι R) M n c
  rw [cyclicCohomology.matrixSelfEquivOfIsUnit_symm_mk R M ι r hn hR Φ,
    cyclicCohomology.cornerRestriction_mk, cyclicCohomology.selfEquiv_symm_mk]; simp

/-- Over every commutative ring `R`, `M ≃ₗ[R] HC⁰(Matrix ι ι R; M)` via `m ↦ [a₀ ↦ Tr(a₀) • m]`. -/
def cyclicCohomology.matrixZeroSelfEquiv : M ≃ₗ[R] cyclicCohomology R (Matrix ι ι R) M 0 :=
  cyclicCohomology.matrixSelfEquivOfIsUnit R M ι Even.zero fun q hq => absurd hq (Nat.not_lt_zero q)

/-- Evaluating `matrixZeroSelfEquiv` extends `mkPiRing R M 0 Even.zero m`. -/
@[simp] theorem cyclicCohomology.matrixZeroSelfEquiv_apply (m : M) :
    cyclicCohomology.matrixZeroSelfEquiv R M ι m =
      cyclicCohomology.matrixExtension M ι 0 (cyclicCohomology.mkPiRing R M 0 Even.zero m) := (rfl)

/-- `(cyclicCohomology.matrixZeroSelfEquiv R M ι).symm [Φ]` evaluates `Φ` at `E_{rr}(1)`. -/
theorem cyclicCohomology.matrixZeroSelfEquiv_symm_mk (r : ι)
    (Φ : cyclicCocycles R (Matrix ι ι R) M 0) :
    (cyclicCohomology.matrixZeroSelfEquiv R M ι).symm
        (cyclicCohomology.mk R (Matrix ι ι R) M 0 Φ) =
      (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 => Matrix ι ι R) M)
        fun _ => Matrix.single r r 1 :=
  cyclicCohomology.matrixSelfEquivOfIsUnit_symm_mk R M ι r Even.zero
    (fun q hq => absurd hq (Nat.not_lt_zero q)) Φ

/-- `(cyclicCohomology.matrixZeroSelfEquiv R M ι).symm` factors via `cornerRestriction`. -/
theorem cyclicCohomology.matrixZeroSelfEquiv_symm_apply (r : ι)
    (c : cyclicCohomology R (Matrix ι ι R) M 0) :
    (cyclicCohomology.matrixZeroSelfEquiv R M ι).symm c =
      (((cyclicCohomology.zeroEquiv R R M).symm
          (cyclicCohomology.cornerRestriction M 0 r c) : cyclicCochains R R M 0) :
        MultilinearMap (RingHom.id R) (fun _ : Fin 1 => R) M) fun _ => 1 := by
  obtain ⟨Φ, rfl⟩ := cyclicCohomology.mk_surjective R (Matrix ι ι R) M 0 c
  rw [cyclicCohomology.matrixZeroSelfEquiv_symm_mk R M ι r Φ, cyclicCohomology.cornerRestriction_mk,
    ← cyclicCohomology.zeroEquiv_apply, LinearEquiv.symm_apply_apply]; simp

/-- `I : HC⁰ → HH⁰` intertwines the degree-zero trace equivalences on `Matrix ι ι R`. -/
theorem cyclicCohomology.toHochschild_matrixZeroSelfEquiv (m : M) :
    cyclicCohomology.toHochschild R (Matrix ι ι R) M 0
        (cyclicCohomology.matrixZeroSelfEquiv R M ι m) =
      hochschildCohomology.matrixZeroSelfEquiv R M ι m := by simp

/-- `(hochschildCohomology.matrixZeroSelfEquiv R M ι).symm [Φ]` evaluates `Φ` at `E_{rr}(1)`. -/
theorem hochschildCohomology.matrixZeroSelfEquiv_symm_mk (r : ι)
    (Φ : hochschildCocycles R (Matrix ι ι R) M 0) :
    (hochschildCohomology.matrixZeroSelfEquiv R M ι).symm
        (hochschildCohomology.mk R (Matrix ι ι R) M 0 Φ) =
      (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 => Matrix ι ι R) M)
        fun _ => Matrix.single r r 1 := by
  let Φc : cyclicCocycles R (Matrix ι ι R) M 0 := ⟨⟨Φ.1, by simp⟩,
    (mem_cyclicCocycles_iff R (Matrix ι ι R) M).2 (mem_hochschildCocycles_iff.1 Φ.2)⟩
  rw [← cyclicCohomology.toHochschild_mk R (Matrix ι ι R) M Φc, LinearEquiv.symm_apply_eq,
    ← cyclicCohomology.toHochschild_matrixZeroSelfEquiv]; congr 1
  rw [← LinearEquiv.symm_apply_eq, cyclicCohomology.matrixZeroSelfEquiv_symm_mk R M ι r Φc]

/-- `(periodicCyclicCohomology.matrixZeroSelfEquiv R M ι).symm` evaluates `[Φ]` at `E_{rr}(1)`. -/
theorem periodicCyclicCohomology.matrixZeroSelfEquiv_symm_ι_homologyMap_mk (r : ι)
    (Φ : cyclicCocycles R (Matrix ι ι R) M 0) :
    (periodicCyclicCohomology.matrixZeroSelfEquiv R M ι).symm
        (periodicCyclicCohomology.ι R (Matrix ι ι R) M 0 0
          (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι R) M) 0
            (cyclicCohomology.mk R (Matrix ι ι R) M 0 Φ))) =
      (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 => Matrix ι ι R) M)
        fun _ => Matrix.single r r 1 := by
  rw [LinearEquiv.symm_apply_eq, periodicCyclicCohomology.matrixZeroSelfEquiv_apply,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]
  exact congrArg (periodicCyclicCohomology.ι R (Matrix ι ι R) M 0 0)
    (congrArg (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι R) M) 0)
      ((LinearEquiv.symm_apply_eq (cyclicCohomology.matrixZeroSelfEquiv R M ι)).1
        (cyclicCohomology.matrixZeroSelfEquiv_symm_mk R M ι r Φ)))

end Decidable

end CommRing

section Rational

variable (R M ι : Type*) [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M] [Fintype ι]
  [DecidableEq ι] [Nonempty ι]

/-- Over a `ℚ`-algebra `R`, `HCⁿ(Matrix ι ι R; M)` vanishes in odd degree. -/
theorem isZero_cyclicCohomology_matrix_of_odd {n : ℕ} (hn : Odd n) :
    Limits.IsZero (cyclicCohomology R (Matrix ι ι R) M n) :=
  isZero_cyclicCohomology_matrix_of_odd_of_isUnit R M ι hn fun q _ => isUnit_natCast_add_one q

/-- Over a `ℚ`-algebra `R`, `M ≃ₗ[R] HCⁿ(Matrix ι ι R; M)` in every even degree `n`. -/
def cyclicCohomology.matrixSelfEquiv {n : ℕ} (hn : Even n) :
    M ≃ₗ[R] cyclicCohomology R (Matrix ι ι R) M n :=
  cyclicCohomology.matrixSelfEquivOfIsUnit R M ι hn fun q _ => isUnit_natCast_add_one q

/-- `matrixSelfEquiv` sends `m` to `matrixExtension (mkPiRing R M n hn m)`. -/
@[simp] theorem cyclicCohomology.matrixSelfEquiv_apply {n : ℕ} (hn : Even n) (m : M) :
    cyclicCohomology.matrixSelfEquiv R M ι hn m =
      cyclicCohomology.matrixExtension M ι n (cyclicCohomology.mkPiRing R M n hn m) := (rfl)

/-- `(matrixSelfEquiv R M ι hn).symm [Φ]` evaluates `Φ` at `fun _ => Matrix.single r r 1`. -/
theorem cyclicCohomology.matrixSelfEquiv_symm_mk (r : ι) {n : ℕ} (hn : Even n)
    (Φ : cyclicCocycles R (Matrix ι ι R) M n) :
    (cyclicCohomology.matrixSelfEquiv R M ι hn).symm (cyclicCohomology.mk R (Matrix ι ι R) M n Φ) =
      (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι R) M)
        fun _ => Matrix.single r r 1 :=
  cyclicCohomology.matrixSelfEquivOfIsUnit_symm_mk R M ι r hn
    (fun q _ => isUnit_natCast_add_one q) Φ

/-- Over a `ℚ`-algebra `R`, `(matrixSelfEquiv R M ι hn).symm` factors via `cornerRestriction`. -/
theorem cyclicCohomology.matrixSelfEquiv_symm_apply (r : ι) {n : ℕ} (hn : Even n)
    (c : cyclicCohomology R (Matrix ι ι R) M n) :
    (cyclicCohomology.matrixSelfEquiv R M ι hn).symm c =
      (cyclicCohomology.selfEquiv R M hn ((show IsUnit (2 : R) by
        simpa using isUnit_natCast_of_ne_zero (K := R) (m := 2) two_ne_zero).isSMulRegular
        M)).symm (cyclicCohomology.cornerRestriction M n r c) :=
  cyclicCohomology.matrixSelfEquivOfIsUnit_symm_apply R M ι r hn
    (fun q _ => isUnit_natCast_add_one q) _ c

end Rational

end TauCeti
