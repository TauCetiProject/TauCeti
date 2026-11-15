/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HochschildCohomology.Matrix
public import TauCeti.RingTheory.CyclicCohomology.PeriodicCohomology
import Mathlib.Algebra.FiveLemma
import TauCeti.Algebra.Algebra.NatCast

/-!
# Matrix Morita invariance of cyclic and periodic cyclic cohomology

Generalized matrix trace `TauCeti.matrixCochainExtension` commutes with Connes' cochain periodicity
operator `S₀` and extends row by row to Connes' cyclic bicomplex
(`TauCeti.matrixCyclicTotalCochainExtension`), inducing `R`-linear maps
`TauCeti.cyclicTotalHomologyMatrixExtension` on `Hⁿ(Tot)` and
`TauCeti.periodicCyclicCohomology.matrixExtension` on `HPⁿ` compatible with the SBI sequence,
`2`-periodicity, and `fromCyclicCohomology`.

For unital `A` and nonempty finite `ι`, Hochschild Morita invariance and the five lemma along the
SBI sequence yield bijectivity on `Hⁿ(Tot)` and `HPⁿ` over *every* commutative ring `R`, and via
`TauCeti.quasiIsoAt_cyclicCochainComplexToTotal` on `HCⁿ` whenever `∀ q < n, IsUnit ((q : R) + 1)`
(hence in all degrees over any `ℚ`-algebra).

## Main definitions

* `TauCeti.matrixCyclicTotalCochainExtension`: rowwise generalized matrix trace on total cochains.
* `TauCeti.cyclicTotalHomologyMatrixExtension`, `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`:
  induced map and `R`-linear equivalence on `Hⁿ(Tot)`.
* `TauCeti.cyclicCohomology.matrixExtensionEquiv`: `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a
  `ℚ`-algebra.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`: induced map and `R`-linear equivalence
  `HPⁿ(A; M) ≃ₗ[R] HPⁿ(Matrix ι ι A; M)` over any commutative ring `R`.

## Main results

* `TauCeti.matrixCochainExtension_cochainPeriodicity`: generalized matrix trace commutes with `S₀`.
* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix Morita invariance of `Hⁿ(Tot)`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of `HCⁿ(A; M)`.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of
  `HPⁿ(A; M)` over any commutative ring `R`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.2, 2.2, 5.1.
* R. McCarthy, *Morita equivalence and cyclic homology*, C. R. Acad. Sci. Paris Sér. I Math. 307
  (1988), 211–215.
-/

public section

open CategoryTheory

namespace TauCeti

/-! ### Cochain-level compatibilities with `S₀` and `S` -/

/-- Generalized matrix trace commutes with Connes' unaveraged cochain periodicity operator `S₀`. -/
theorem matrixCochainExtension_cochainPeriodicity {R A M : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M] [SMulCommClass R R M] (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 2) (cochainPeriodicity R A M n φ) =
      cochainPeriodicity R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  simp only [cochainPeriodicity_def, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, map_sum, map_zsmul, matrixCochainExtension_hochschildCoface]

section Assoc

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  (ι : Type*) [Fintype ι] (n : ℕ)

/-- Matrix extension of cyclic cochains commutes with Connes' operator `S = (n + 3)⁻¹ N S₀`. -/
theorem matrixCyclicCochainExtension_connesS [Invertible (n + 3 : R)] (ψ : cyclicCochains R A M n) :
    matrixCyclicCochainExtension ι (n + 2) (connesS R A M n ψ) =
      connesS R (Matrix ι ι A) M n (matrixCyclicCochainExtension ι n ψ) := by
  ext1; rw [coe_matrixCyclicCochainExtension_apply, coe_connesS_apply, coe_connesS_apply,
    coe_matrixCyclicCochainExtension_apply, map_smul, matrixCochainExtension_cyclicNorm,
    matrixCochainExtension_cochainPeriodicity]

/-- Matrix extension of cyclic cocycles commutes with `cyclicCocyclesPeriodicity`. -/
theorem matrixCyclicCochainExtension_cyclicCocyclesPeriodicity (φ : cyclicCocycles R A M n) :
    matrixCyclicCochainExtension ι (n + 2) (cyclicCocyclesPeriodicity R A M n φ).1 =
      (cyclicCocyclesPeriodicity R (Matrix ι ι A) M n
        ⟨matrixCyclicCochainExtension ι n φ.1,
          matrixCyclicCochainExtension_mem_cyclicCocycles φ.2⟩).1 := by
  ext1; simp [coe_cyclicCocyclesPeriodicity_apply, matrixCochainExtension_cochainPeriodicity]

end Assoc

/-! ### Matrix extension on the cyclic bicomplex -/

section Additive

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M] (ι : Type*) [Fintype ι]

private theorem matrixCochainExtension_comp_mem_cyclicTotalCochains {m : ℕ}
    {x : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M}
    (hx : x ∈ cyclicTotalCochains R A M m) :
    (fun q ↦ matrixCochainExtension ι q (x q)) ∈ cyclicTotalCochains R (Matrix ι ι A) M m := by
  rw [mem_cyclicTotalCochains_iff] at hx ⊢; intro q hq; rw [hx q hq, map_zero]

/-- Rowwise generalized matrix trace on total cochains of the cyclic bicomplex. -/
noncomputable def matrixCyclicTotalCochainExtension (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  (LinearMap.pi fun q : ℕ ↦
    matrixCochainExtension (R := R) (A := A) (M := M) ι q ∘ₗ LinearMap.proj q).restrict
    fun _ ↦ matrixCochainExtension_comp_mem_cyclicTotalCochains ι

/-- Row `q` of `matrixCyclicTotalCochainExtension ι m x` is `matrixCochainExtension ι q (x q)`. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply {m : ℕ} (x : cyclicTotalCochains R A M m)
    (q : ℕ) : (matrixCyclicTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) :=
  (rfl)

/-- Rowwise matrix extension commutes with the periodicity shift on total cochains. -/
@[simp]
theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) :=
  Subtype.ext (funext fun _ ↦ by simp)

/-- Column-zero projection commutes with rowwise matrix extension on total cochains. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by simp

end Additive

section Horizontal

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M] (ι : Type*) [Fintype ι]

/-- Generalized matrix trace commutes with the horizontal differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp <;>
    simp [hp, matrixCochainExtension_cyclicOperator, matrixCochainExtension_cyclicNorm]

/-- Rowwise matrix extension commutes with the inclusion of cyclic cochains into column zero. -/
@[simp]
theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal {m : ℕ}
    (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  rcases eq_or_ne q m with rfl | hne <;> simp [Pi.single_eq_of_ne, *]

end Horizontal

section Differential

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι]

/-- Generalized matrix trace commutes with the vertical differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp <;>
    simp [hp, matrixCochainExtension_hochschildCoboundary, matrixCochainExtension_barCoboundary]

/-- Rowwise matrix extension commutes with the total differential `D = d_h + d_v`. -/
theorem cyclicTotalDifferential_matrixCyclicTotalCochainExtension {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  cases q <;> simp [map_add, matrixCochainExtension_cyclicBicomplexVertical,
    matrixCochainExtension_cyclicBicomplexHorizontal]

end Differential

/-! ### Compatibility of `cyclicCohomology.matrixExtension` with `I`, `B`, and `S` -/

namespace cyclicCohomology

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix extension on cyclic cohomology commutes with the map `I` to Hochschild cohomology. -/
@[simp] theorem toHochschild_matrixExtension (n : ℕ) (c : cyclicCohomology R A M n) :
    toHochschild R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n (toHochschild R A M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c; simp

/-- Matrix extension on cyclic cohomology commutes with Connes' operator `B`. -/
@[simp] theorem matrixExtension_connesB (n : ℕ) (c : hochschildCohomology R A M (n + 1)) :
    matrixExtension M ι n (hochschildCohomology.connesB R A M n c) =
      hochschildCohomology.connesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (n + 1) c
  simp only [hochschildCohomology.connesB_mk, matrixExtension_mk,
    hochschildCohomology.matrixExtension_mk]
  congr 1; refine Subtype.ext (Subtype.ext ?_)
  rw [coe_matrixCyclicCochainExtension_apply]; exact matrixCochainExtension_connesB ι n φ.1

/-- Matrix extension on cyclic cohomology over a `ℚ`-algebra commutes with `S`. -/
@[simp] theorem matrixExtension_periodicity [Algebra ℚ R] (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixExtension M ι (n + 2) (periodicity R A M n c) =
      periodicity R (Matrix ι ι A) M n (matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [periodicity_mk, matrixExtension_mk]
  congr 1; exact Subtype.ext (matrixCyclicCochainExtension_cyclicCocyclesPeriodicity ι n φ)

/-- Matrix extension on cyclic cohomology over a `ℚ`-algebra commutes with `S^(j - i)`. -/
@[simp] theorem matrixExtension_periodicTransition [Algebra ℚ R] (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : cyclicCohomology R A M (n + 2 * i)) :
    matrixExtension M ι (n + 2 * j) (periodicTransition R A M n h c) =
      periodicTransition R (Matrix ι ι A) M n h (matrixExtension M ι (n + 2 * i) c) := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [← periodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ← periodicTransition_comp R (Matrix ι ι A) M n hij (Nat.le_add_right j 1),
      periodicTransition_succ, periodicTransition_succ, ModuleCat.comp_apply,
      ModuleCat.comp_apply, ← ih, ← matrixExtension_periodicity]
    rfl

end Unital

end cyclicCohomology

/-! ### Matrix Morita invariance of the total cyclic bicomplex -/

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι]

/-- Rowwise matrix extension maps total cocycles to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker {m : ℕ} {x : cyclicTotalCochains R A M m}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M m)) :
    matrixCyclicTotalCochainExtension ι m x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hx, map_zero]

private theorem cyclicTotalHomologyMk_matrixExtension_eq_zero {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m))
    (hx0 : cyclicTotalHomologyMk R A M m x = 0) :
    cyclicTotalHomologyMk R (Matrix ι ι A) M m
      ⟨matrixCyclicTotalCochainExtension ι m x.1,
        matrixCyclicTotalCochainExtension_mem_ker ι x.2⟩ = 0 := by
  cases m with
  | zero => obtain rfl := (cyclicTotalHomologyMk_zero_eq_zero_iff x).1 hx0; simp
  | succ n =>
    obtain ⟨w, hw⟩ := (cyclicTotalHomologyMk_succ_eq_zero_iff x).1 hx0
    exact (cyclicTotalHomologyMk_succ_eq_zero_iff _).2 ⟨matrixCyclicTotalCochainExtension ι n w,
      by rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hw]⟩

variable (M) in
/-- Matrix extension on the cohomology `Hᵐ(Tot)` of the total cyclic bicomplex. -/
noncomputable def cyclicTotalHomologyMatrixExtension (m : ℕ) :
    (cyclicTotalComplex R A M).homology m →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  (cyclicTotalHomologyMk R A M m).liftOfSurjective (cyclicTotalHomologyMk_surjective m)
    ⟨cyclicTotalHomologyMk R (Matrix ι ι A) M m ∘ₗ
        (matrixCyclicTotalCochainExtension ι m).restrict
          (fun _ ↦ matrixCyclicTotalCochainExtension_mem_ker ι),
      fun x (hx : x ∈ LinearMap.ker (cyclicTotalHomologyMk R A M m)) ↦ LinearMap.mem_ker.2
        (cyclicTotalHomologyMk_matrixExtension_eq_zero ι x (LinearMap.mem_ker.1 hx))⟩

/-- `cyclicTotalHomologyMatrixExtension` maps `[x]` to the class of its rowwise matrix extension. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyMk R A M m x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M m
        ⟨matrixCyclicTotalCochainExtension ι m x.1,
          matrixCyclicTotalCochainExtension_mem_ker ι x.2⟩ :=
  LinearMap.equivOfSurjective_apply _ _

/-- Matrix extension on `Hᵐ(Tot)` commutes with the projection `I` onto Hochschild cohomology. -/
@[simp] theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension
    (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      hochschildCohomology.matrixExtension M ι m
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c; simp

/-- Matrix extension on `Hᵐ(Tot)` commutes with `S : Hᵐ(Tot) → Hᵐ⁺²(Tot)`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity (m : ℕ)
    (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyMatrixExtension M ι (m + 2) (cyclicTotalHomologyPeriodicity R A M m c) =
      cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m
        (cyclicTotalHomologyMatrixExtension M ι m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1; exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity ι x.1)

/-- Matrix extension on `Hᵐ(Tot)` commutes with the iterated transition maps `S^(j - i)`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicTransition
    (n : ℕ) {i j : ℕ} (h : i ≤ j) (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h c) =
      cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) c) := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hij (Nat.le_add_right j 1),
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ,
      ModuleCat.comp_apply, ModuleCat.comp_apply, ← ih,
      ← cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity]
    rfl

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  (ι : Type*) [Fintype ι]

/-- Matrix extension commutes with the comparison map `HCᵐ → Hᵐ(Tot)`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal
    [DecidableEq ι] (m : ℕ) (c : cyclicCohomology R A M m) :
    cyclicTotalHomologyMatrixExtension M ι m
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m c) =
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) m
        (cyclicCohomology.matrixExtension M ι m c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M m c
  simp only [homologyMap_cyclicCochainComplexToTotal_mk, cyclicCohomology.matrixExtension_mk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1; exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι φ.1)

/-- Matrix extension commutes with Connes' operator `B : HHᵐ⁺¹ → Hᵐ(Tot)`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB [DecidableEq ι]
    (m : ℕ) (c : hochschildCohomology R A M (m + 1)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyConnesB R A M m c) =
      cyclicTotalHomologyConnesB R (Matrix ι ι A) M m
        (hochschildCohomology.matrixExtension M ι (m + 1) c) := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.comp_apply,
    ModuleCat.comp_apply,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    cyclicCohomology.matrixExtension_connesB]

section Nonempty

variable [Nonempty ι]

private theorem bijective_cyclicTotalHomologyMatrixExtension_zero :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 0) := by
  classical
  have hIA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hIM : Function.Bijective (HomologicalComplex.homologyMap
      (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hcomm : (HomologicalComplex.homologyMap
      (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0) ∘
        cyclicTotalHomologyMatrixExtension M ι 0 =
      hochschildCohomology.matrixExtension M ι 0 ∘
        HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0 :=
    funext (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension ι 0)
  exact (hIM.of_comp_iff' _).1
    (hcomm ▸ (hochschildCohomology.bijective_matrixExtension ι 0).comp hIA)

private theorem bijective_cyclicTotalHomologyMatrixExtension_one :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 1) := by
  classical
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 1).hom
    (cyclicTotalHomologyConnesB R A M 0).hom
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 1).hom
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M 0).hom
    (cyclicTotalHomologyMatrixExtension M ι 1) (hochschildCohomology.matrixExtension M ι 1)
    (cyclicTotalHomologyMatrixExtension M ι 0)
    (LinearMap.ext
      (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension ι 1))
    (LinearMap.ext (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB ι 0)).symm
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
    (hochschildCohomology.bijective_matrixExtension ι 1)
    (bijective_cyclicTotalHomologyMatrixExtension_zero ι).1
    injective_homologyMap_cyclicTotalComplexToHochschild_one
    injective_homologyMap_cyclicTotalComplexToHochschild_one

/-- **Matrix Morita invariance of the total cyclic bicomplex** over any commutative ring `R`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (n : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => exact bijective_cyclicTotalHomologyMatrixExtension_zero ι
    | 1 => exact bijective_cyclicTotalHomologyMatrixExtension_one ι
    | m + 2 =>
      exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
        (cyclicTotalHomologyConnesB R A M m).hom (cyclicTotalHomologyPeriodicity R A M m).hom
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 2)).hom
        (cyclicTotalHomologyConnesB R A M (m + 1)).hom
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m).hom
        (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m).hom
        (HomologicalComplex.homologyMap
          (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) (m + 2)).hom
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M (m + 1)).hom
        (hochschildCohomology.matrixExtension M ι (m + 1))
        (cyclicTotalHomologyMatrixExtension M ι m) (cyclicTotalHomologyMatrixExtension M ι (m + 2))
        (hochschildCohomology.matrixExtension M ι (m + 2))
        (cyclicTotalHomologyMatrixExtension M ι (m + 1))
        (LinearMap.ext (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB ι m)).symm
        (LinearMap.ext (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity ι m)).symm
        (LinearMap.ext
          (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension ι (m + 2)))
        (LinearMap.ext
          (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB ι (m + 1))).symm
        (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m)
        (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M m)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m + 1))
        (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m)
        (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
          R (Matrix ι ι A) M m)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m + 1))
        (hochschildCohomology.bijective_matrixExtension ι (m + 1)).2 (ih m (by omega))
        (hochschildCohomology.bijective_matrixExtension ι (m + 2)) (ih (m + 1) (by omega)).1

variable (M) in
/-- **Matrix Morita equivalence on `Hⁿ(Tot)`** over any commutative ring `R`. -/
noncomputable def cyclicTotalHomologyMatrixExtensionEquiv (n : ℕ) :
    (cyclicTotalComplex R A M).homology n ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι n)
    (bijective_cyclicTotalHomologyMatrixExtension ι n)

/-- Underlying linear map of `cyclicTotalHomologyMatrixExtensionEquiv`. -/
@[simp]
theorem coe_cyclicTotalHomologyMatrixExtensionEquiv (n : ℕ) :
    (cyclicTotalHomologyMatrixExtensionEquiv (R := R) (A := A) M ι n :
      (cyclicTotalComplex R A M).homology n →ₗ[R]
        (cyclicTotalComplex R (Matrix ι ι A) M).homology n) =
      cyclicTotalHomologyMatrixExtension M ι n := (rfl)

/-- `cyclicTotalHomologyMatrixExtensionEquiv` acts by `cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_apply (n : ℕ)
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixExtensionEquiv M ι n c =
      cyclicTotalHomologyMatrixExtension M ι n c := (rfl)

/-- Applying `cyclicTotalHomologyMatrixExtension` to the inverse equivalence recovers `c`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMatrixExtensionEquiv_symm (n : ℕ)
    (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology n) :
    cyclicTotalHomologyMatrixExtension M ι n
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι n).symm c) = c := by
  rw [← cyclicTotalHomologyMatrixExtensionEquiv_apply, LinearEquiv.apply_symm_apply]

/-- Applying `(cyclicTotalHomologyMatrixExtensionEquiv M ι n).symm` after extension recovers `c`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_cyclicTotalHomologyMatrixExtension (n : ℕ)
    (c : (cyclicTotalComplex R A M).homology n) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι n).symm
        (cyclicTotalHomologyMatrixExtension M ι n c) = c := by
  rw [← cyclicTotalHomologyMatrixExtensionEquiv_apply, LinearEquiv.symm_apply_apply]

/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` commutes with `I`. -/
@[simp]
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtensionEquiv_symm
    (m : ℕ) (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology m) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm c) =
      (hochschildCohomology.matrixExtensionEquiv M ι m).symm
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) m c) :=
  (hochschildCohomology.matrixExtensionEquiv M ι m).injective <| by
    rw [LinearEquiv.apply_symm_apply, hochschildCohomology.matrixExtensionEquiv_apply,
      ← homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension,
      cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMatrixExtensionEquiv_symm]

/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` commutes with `S`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_cyclicTotalHomologyPeriodicity (m : ℕ)
    (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology m) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι (m + 2)).symm
        (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m c) =
      cyclicTotalHomologyPeriodicity R A M m
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm c) :=
  (cyclicTotalHomologyMatrixExtensionEquiv M ι (m + 2)).injective (by simp)

/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` commutes with `S^(j - i)`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_cyclicTotalHomologyPeriodicTransition
    (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology (n + 2 * i)) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * j)).symm
        (cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h c) =
      cyclicTotalHomologyPeriodicTransition R A M n h
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * i)).symm c) :=
  (cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * j)).injective (by simp)

/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` commutes with Connes' `B`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_cyclicTotalHomologyConnesB [DecidableEq ι]
    (m : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M (m + 1)) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m c) =
      cyclicTotalHomologyConnesB R A M m
        ((hochschildCohomology.matrixExtensionEquiv M ι (m + 1)).symm c) :=
  (cyclicTotalHomologyMatrixExtensionEquiv M ι m).injective
    (by simp [← hochschildCohomology.matrixExtensionEquiv_apply])

end Nonempty

end Unital

/-! ### Matrix Morita invariance of cyclic cohomology -/

namespace cyclicCohomology

section Morita

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Matrix Morita invariance of cyclic cohomology under invertibility of `1, …, n`.** -/
theorem bijective_matrixExtension_of_isUnit (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have hjA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have hjM : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  have hcomm : (HomologicalComplex.homologyMap
      (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) ∘ matrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι n ∘
        HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n :=
    funext fun c ↦
      (cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal ι n c).symm
  exact (hjM.of_comp_iff' _).1 (hcomm ▸ (bijective_cyclicTotalHomologyMatrixExtension ι n).comp hjA)

/-- In degree zero, `cyclicCohomology.matrixExtension` is bijective over every commutative ring. -/
theorem bijective_matrixExtension_zero :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 (by simp)

/-- In degree one, `cyclicCohomology.matrixExtension` is bijective over every commutative ring. -/
theorem bijective_matrixExtension_one :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 1) :=
  bijective_matrixExtension_of_isUnit ι 1 fun q hq ↦ by obtain rfl := Nat.lt_one_iff.1 hq; simp

section RatAlgebra

variable [Algebra ℚ R]

/-- **Matrix Morita invariance of cyclic cohomology** over a `ℚ`-algebra `R`. -/
theorem bijective_matrixExtension (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦ isUnit_natCast_add_one q

variable (M) in
/-- **Matrix Morita equivalence on cyclic cohomology** over a `ℚ`-algebra `R`. -/
noncomputable def matrixExtensionEquiv (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The underlying linear map of `cyclicCohomology.matrixExtensionEquiv` is `matrixExtension`. -/
@[simp]
theorem coe_matrixExtensionEquiv (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := (rfl)

/-- `cyclicCohomology.matrixExtensionEquiv` acts by `cyclicCohomology.matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c := (rfl)

/-- Applying `cyclicCohomology.matrixExtension` to the inverse equivalence recovers `c`. -/
@[simp]
theorem matrixExtension_matrixExtensionEquiv_symm (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n ((matrixExtensionEquiv M ι n).symm c) = c := by
  rw [← matrixExtensionEquiv_apply, LinearEquiv.apply_symm_apply]

/-- Applying `(matrixExtensionEquiv M ι n).symm` after `matrixExtension` recovers `c`. -/
@[simp]
theorem matrixExtensionEquiv_symm_matrixExtension (n : ℕ) (c : cyclicCohomology R A M n) :
    (matrixExtensionEquiv M ι n).symm (matrixExtension M ι n c) = c := by
  rw [← matrixExtensionEquiv_apply, LinearEquiv.symm_apply_apply]

/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` commutes with `I`. -/
@[simp]
theorem toHochschild_matrixExtensionEquiv_symm (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    toHochschild R A M n ((matrixExtensionEquiv M ι n).symm c) =
      (hochschildCohomology.matrixExtensionEquiv M ι n).symm
        (toHochschild R (Matrix ι ι A) M n c) :=
  (hochschildCohomology.matrixExtensionEquiv M ι n).injective <| by
    rw [LinearEquiv.apply_symm_apply, hochschildCohomology.matrixExtensionEquiv_apply,
      ← toHochschild_matrixExtension, matrixExtension_matrixExtensionEquiv_symm]

/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` commutes with Connes' `B`. -/
@[simp]
theorem matrixExtensionEquiv_symm_connesB (n : ℕ)
    (c : hochschildCohomology R (Matrix ι ι A) M (n + 1)) :
    (matrixExtensionEquiv M ι n).symm (hochschildCohomology.connesB R (Matrix ι ι A) M n c) =
      hochschildCohomology.connesB R A M n
        ((hochschildCohomology.matrixExtensionEquiv M ι (n + 1)).symm c) :=
  (matrixExtensionEquiv M ι n).injective
    (by simp [← hochschildCohomology.matrixExtensionEquiv_apply])

/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` commutes with `S`. -/
@[simp]
theorem matrixExtensionEquiv_symm_periodicity (n : ℕ) (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι (n + 2)).symm (periodicity R (Matrix ι ι A) M n c) =
      periodicity R A M n ((matrixExtensionEquiv M ι n).symm c) :=
  (matrixExtensionEquiv M ι (n + 2)).injective (by simp)

/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` commutes with `S^(j - i)`. -/
@[simp]
theorem matrixExtensionEquiv_symm_periodicTransition (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : cyclicCohomology R (Matrix ι ι A) M (n + 2 * i)) :
    (matrixExtensionEquiv M ι (n + 2 * j)).symm (periodicTransition R (Matrix ι ι A) M n h c) =
      periodicTransition R A M n h ((matrixExtensionEquiv M ι (n + 2 * i)).symm c) :=
  (matrixExtensionEquiv M ι (n + 2 * j)).injective (by simp)

end RatAlgebra

end Morita

end cyclicCohomology

/-- Over a `ℚ`-algebra, `(cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm` commutes with
`HCᵐ → Hᵐ(Tot)`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_homologyMap_cyclicCochainComplexToTotal
    {R A M : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A] [AddCommGroup M]
    [Module R M] (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (m : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M m) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) m c) =
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m
        ((cyclicCohomology.matrixExtensionEquiv M ι m).symm c) :=
  (cyclicTotalHomologyMatrixExtensionEquiv M ι m).injective (by simp)

/-! ### Matrix Morita invariance of periodic cyclic cohomology -/

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι]

variable (M) in
/-- Matrix extension `HPⁿ(A; M) →ₗ[R] HPⁿ(Matrix ι ι A; M)` on periodic cyclic cohomology. -/
noncomputable def matrixExtension (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  mapStages (fun k ↦ cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun k ↦ cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity ι (n + 2 * k)

/-- On stage `Hⁿ⁺²ᵏ(Tot)`, `matrixExtension` acts via `cyclicTotalHomologyMatrixExtension`. -/
@[simp] theorem matrixExtension_ι (n k : ℕ) (x : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k x) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) x) := mapStages_ι _ _ k x

/-- Matrix extension on `HPⁿ` commutes with `(shiftIso R A M n).hom`. -/
@[simp] theorem matrixExtension_shiftIso_hom (n : ℕ) (z : periodicCyclicCohomology R A M (n + 2)) :
    matrixExtension M ι n ((shiftIso R A M n).hom z) =
      (shiftIso R (Matrix ι ι A) M n).hom (matrixExtension M ι (n + 2) z) :=
  mapStages_shiftIso_hom (cyclicTotalHomologyMatrixExtension M ι)
    (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity ι) n z

/-- Matrix extension on `HPⁿ` commutes with `(shiftIso R A M n).inv`. -/
@[simp] theorem matrixExtension_shiftIso_inv (n : ℕ) (z : periodicCyclicCohomology R A M n) :
    matrixExtension M ι (n + 2) ((shiftIso R A M n).inv z) =
      (shiftIso R (Matrix ι ι A) M n).inv (matrixExtension M ι n z) :=
  mapStages_shiftIso_inv (cyclicTotalHomologyMatrixExtension M ι)
    (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity ι) n z

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  (ι : Type*) [Fintype ι]

/-- Matrix extension on `HPⁿ` commutes with the normalized stage maps `fromCyclicCohomology`. -/
@[simp] theorem matrixExtension_fromCyclicCohomology [Algebra ℚ R] [DecidableEq ι] (n k : ℕ)
    (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix ι ι A) M n k
        (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by
  rw [fromCyclicCohomology_def, fromCyclicCohomology_def]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, matrixExtension_ι,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]

section Nonempty

variable [Nonempty ι]

variable (M) in
/-- **Matrix Morita equivalence on periodic cyclic cohomology** over every commutative ring `R`. -/
noncomputable def matrixExtensionEquiv (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  congrStages (fun k ↦ cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * k)) fun k x ↦ by
    rw [cyclicTotalHomologyMatrixExtensionEquiv_apply,
      cyclicTotalHomologyMatrixExtensionEquiv_apply]
    exact cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity ι (n + 2 * k) x

/-- Underlying linear map of `periodicCyclicCohomology.matrixExtensionEquiv`. -/
@[simp] theorem coe_matrixExtensionEquiv (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := by rw [matrixExtensionEquiv, coe_congrStages]; rfl

/-- `periodicCyclicCohomology.matrixExtensionEquiv` acts by `matrixExtension`. -/
@[simp] theorem matrixExtensionEquiv_apply (n : ℕ) (c : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  DFunLike.congr_fun (coe_matrixExtensionEquiv ι n) c

/-- Applying `periodicCyclicCohomology.matrixExtension` to the inverse equivalence recovers `c`. -/
@[simp] theorem matrixExtension_matrixExtensionEquiv_symm (n : ℕ)
    (c : periodicCyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n ((matrixExtensionEquiv M ι n).symm c) = c := by
  rw [← matrixExtensionEquiv_apply, LinearEquiv.apply_symm_apply]

/-- Applying `(matrixExtensionEquiv M ι n).symm` after `matrixExtension` recovers `c`. -/
@[simp] theorem matrixExtensionEquiv_symm_matrixExtension (n : ℕ)
    (c : periodicCyclicCohomology R A M n) :
    (matrixExtensionEquiv M ι n).symm (matrixExtension M ι n c) = c := by
  rw [← matrixExtensionEquiv_apply, LinearEquiv.symm_apply_apply]

/-- Stagewise action of `(matrixExtensionEquiv M ι n).symm`. -/
@[simp] theorem matrixExtensionEquiv_symm_ι (n k : ℕ)
    (y : (cyclicTotalComplex R (Matrix ι ι A) M).homology (n + 2 * k)) :
    (matrixExtensionEquiv M ι n).symm (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k y) =
      periodicCyclicCohomology.ι R A M n k
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * k)).symm y) :=
  congrStages_symm_ι _ _ k y

/-- The inverse of `periodicCyclicCohomology.matrixExtensionEquiv` commutes with `shiftIso.hom`. -/
@[simp] theorem matrixExtensionEquiv_symm_shiftIso_hom (n : ℕ)
    (z : periodicCyclicCohomology R (Matrix ι ι A) M (n + 2)) :
    (matrixExtensionEquiv M ι n).symm ((shiftIso R (Matrix ι ι A) M n).hom z) =
      (shiftIso R A M n).hom ((matrixExtensionEquiv M ι (n + 2)).symm z) :=
  (matrixExtensionEquiv M ι n).injective (by simp)

/-- The inverse of `periodicCyclicCohomology.matrixExtensionEquiv` commutes with `shiftIso.inv`. -/
@[simp] theorem matrixExtensionEquiv_symm_shiftIso_inv (n : ℕ)
    (z : periodicCyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι (n + 2)).symm ((shiftIso R (Matrix ι ι A) M n).inv z) =
      (shiftIso R A M n).inv ((matrixExtensionEquiv M ι n).symm z) :=
  (matrixExtensionEquiv M ι (n + 2)).injective (by simp)

/-- **Matrix Morita invariance of periodic cyclic cohomology** over every commutative ring `R`. -/
theorem bijective_matrixExtension (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  rw [← coe_matrixExtensionEquiv]; exact (matrixExtensionEquiv M ι n).bijective

/-- `(periodicCyclicCohomology.matrixExtensionEquiv M ι n).symm` commutes with
`fromCyclicCohomology`. -/
@[simp] theorem matrixExtensionEquiv_symm_fromCyclicCohomology [Algebra ℚ R] [DecidableEq ι]
    (n k : ℕ) (c : cyclicCohomology R (Matrix ι ι A) M (n + 2 * k)) :
    (matrixExtensionEquiv M ι n).symm (fromCyclicCohomology R (Matrix ι ι A) M n k c) =
      fromCyclicCohomology R A M n k
        ((cyclicCohomology.matrixExtensionEquiv M ι (n + 2 * k)).symm c) :=
  (matrixExtensionEquiv M ι n).injective (by simp)

end Nonempty

end Unital

end periodicCyclicCohomology

end TauCeti
