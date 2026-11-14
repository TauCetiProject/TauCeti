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

Generalized matrix trace `TauCeti.matrixCochainExtension` commutes not only with the Hochschild
coboundary `b`, cyclic operator `λ`, cyclic norm `N`, and Connes' operator `B`, but also with the
bar coboundary `b'` and Connes' cochain periodicity operator `S₀`. Consequently it extends row by
row to a cochain map on Connes' cyclic bicomplex (`TauCeti.matrixCyclicTotalCochainExtension`),
inducing `R`-linear maps `TauCeti.cyclicTotalHomologyMatrixExtension` on the cohomology `Hⁿ(Tot)`
of the total cyclic bicomplex and `TauCeti.periodicCyclicCohomology.matrixExtension` on periodic
cyclic cohomology `HPⁿ`, compatible with all morphisms of Connes' SBI sequence and with the
normalized stage maps from cyclic cohomology.

For a unital `R`-algebra `A` and a nonempty finite index type `ι`, matrix Morita invariance of
Hochschild cohomology (`TauCeti.hochschildCohomology.bijective_matrixExtension`) together with the
five lemma along the SBI long exact sequence of the cyclic bicomplex implies that
`cyclicTotalHomologyMatrixExtension` is bijective in every degree over *every* commutative ring `R`,
hence so is `periodicCyclicCohomology.matrixExtension` on the direct limit `HPⁿ`.

For Connes' cyclic cochain model `HCⁿ(A; M)`, comparison with the total cyclic bicomplex
(`TauCeti.quasiIsoAt_cyclicCochainComplexToTotal`) yields bijectivity of
`TauCeti.cyclicCohomology.matrixExtension` in degree `n` whenever `(q : R) + 1` is a unit in `R`
for all `q < n` — in particular unconditionally in degrees `0` and `1` over any commutative ring,
and in all degrees when `R` is a `ℚ`-algebra (`TauCeti.cyclicCohomology.bijective_matrixExtension`).

## Main definitions

* `TauCeti.matrixCyclicTotalCochainExtension`: rowwise generalized matrix trace on total cochains
  of the cyclic bicomplex.
* `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`: the induced map and `R`-linear equivalence
  on the cohomology `Hⁿ(Tot)` of the total cyclic bicomplex.
* `TauCeti.cyclicCohomology.matrixExtensionEquiv`: the `R`-linear equivalence
  `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a `ℚ`-algebra.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`: the induced map and `R`-linear
  equivalence `HPⁿ(A; M) ≃ₗ[R] HPⁿ(Matrix ι ι A; M)` over any commutative ring `R`.

## Main results

* `TauCeti.matrixCochainExtension_barCoboundary`,
  `TauCeti.matrixCochainExtension_cochainPeriodicity`: generalized matrix trace commutes with `b'`
  and `S₀`.
* `TauCeti.cyclicCohomology.toHochschild_matrixExtension`,
  `TauCeti.cyclicCohomology.matrixExtension_connesB`,
  `TauCeti.cyclicCohomology.matrixExtension_periodicity`: compatibility of
  `cyclicCohomology.matrixExtension` with the SBI operators `I`, `B`, and `S`.
* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix Morita invariance of `Hⁿ(Tot)`
  over any commutative ring `R`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of `HCⁿ(A; M)`
  when `∀ q < n, IsUnit ((q : R) + 1)`, and in all degrees over a `ℚ`-algebra.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of
  `HPⁿ(A; M)` over any commutative ring `R`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.2, 2.2, 5.1.
-/

public section

open CategoryTheory

namespace TauCeti

/-! ### Cochain-level compatibilities with `b'` and `S₀` -/

section CochainCompatibilities

section NonAssoc

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

private theorem barCoboundary_eq_sum_hochschildCoface {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    barCoboundary R A M n φ =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • hochschildCoface R A M j.castSucc φ := by
  ext a
  simp [barCoboundary_apply, hochschildFace_castSucc]

private theorem cochainPeriodicity_eq_sum_hochschildCoface {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cochainPeriodicity R A M n φ =
      ∑ j : Fin (n + 1), ∑ r ∈ Finset.Iic j,
        (-1 : ℤ) ^ ((j : ℕ) - r) •
          hochschildCoface R A M j.succ.castSucc (hochschildCoface R A M r.castSucc φ) := by
  ext a
  simp [cochainPeriodicity_apply]

/-- Generalized matrix trace commutes with the bar coboundary `b'`. -/
theorem matrixCochainExtension_barCoboundary (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 1) (barCoboundary R A M n φ) =
      barCoboundary R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  rw [barCoboundary_eq_sum_hochschildCoface, barCoboundary_eq_sum_hochschildCoface]
  simp only [map_sum, map_zsmul, matrixCochainExtension_hochschildCoface]

/-- Generalized matrix trace commutes with Connes' unaveraged cochain periodicity operator `S₀`. -/
theorem matrixCochainExtension_cochainPeriodicity (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 2) (cochainPeriodicity R A M n φ) =
      cochainPeriodicity R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  rw [cochainPeriodicity_eq_sum_hochschildCoface, cochainPeriodicity_eq_sum_hochschildCoface]
  simp only [map_sum, map_zsmul, matrixCochainExtension_hochschildCoface]

end NonAssoc

section Assoc

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension of cyclic cochains commutes with Connes' operator `S = (n + 3)⁻¹ N S₀`. -/
theorem matrixCyclicCochainExtension_connesS (ι : Type*) [Fintype ι] (n : ℕ)
    [Invertible (n + 3 : R)] (ψ : cyclicCochains R A M n) :
    matrixCyclicCochainExtension ι (n + 2) (connesS R A M n ψ) =
      connesS R (Matrix ι ι A) M n (matrixCyclicCochainExtension ι n ψ) := by
  ext1
  rw [coe_matrixCyclicCochainExtension_apply, coe_connesS_apply, coe_connesS_apply,
    coe_matrixCyclicCochainExtension_apply, map_smul, matrixCochainExtension_cyclicNorm,
    matrixCochainExtension_cochainPeriodicity]

/-- Matrix extension of cyclic cocycles commutes with `cyclicCocyclesPeriodicity`. -/
theorem matrixCyclicCochainExtension_cyclicCocyclesPeriodicity (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : cyclicCocycles R A M n) :
    matrixCyclicCochainExtension ι (n + 2) (cyclicCocyclesPeriodicity R A M n φ).1 =
      (cyclicCocyclesPeriodicity R (Matrix ι ι A) M n
        ⟨matrixCyclicCochainExtension ι n φ.1,
          matrixCyclicCochainExtension_mem_cyclicCocycles φ.2⟩).1 := by
  ext1
  rw [coe_matrixCyclicCochainExtension_apply, coe_cyclicCocyclesPeriodicity_apply,
    coe_cyclicCocyclesPeriodicity_apply, Subtype.coe_mk, coe_matrixCyclicCochainExtension_apply,
    matrixCochainExtension_cochainPeriodicity]

end Assoc

end CochainCompatibilities

/-! ### Matrix extension on the cyclic bicomplex -/

section TotalCochains

section Additive

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M]

private theorem matrixCochainExtension_comp_mem_cyclicTotalCochains (ι : Type*) [Fintype ι]
    {m : ℕ} {x : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M}
    (hx : x ∈ cyclicTotalCochains R A M m) :
    (fun q ↦ matrixCochainExtension ι q (x q)) ∈ cyclicTotalCochains R (Matrix ι ι A) M m := by
  rw [mem_cyclicTotalCochains_iff] at hx ⊢
  intro q hq
  rw [hx q hq, map_zero]

/-- Rowwise generalized matrix trace on total cochains of the cyclic bicomplex. -/
noncomputable def matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  (LinearMap.pi fun q : ℕ ↦
    matrixCochainExtension (R := R) (A := A) (M := M) ι q ∘ₗ LinearMap.proj q).restrict
    fun _ ↦ matrixCochainExtension_comp_mem_cyclicTotalCochains ι

/-- Row `q` of `matrixCyclicTotalCochainExtension ι m x` is `matrixCochainExtension ι q (x q)`. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixCyclicTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) :=
  (rfl)

/-- Rowwise matrix extension commutes with the periodicity shift on total cochains. -/
@[simp]
theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity (ι : Type*) [Fintype ι]
    {m : ℕ} (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) := by
  apply Subtype.ext
  funext q
  simp

/-- Projecting a matrix-extended total cochain onto column zero gives the matrix extension of its
column-zero component. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι]
    {m : ℕ} (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by
  simp

end Additive

section Horizontal

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M]

/-- Generalized matrix trace commutes with the horizontal differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_cyclicOperator]
  · simp [hp, matrixCochainExtension_cyclicNorm]

/-- Rowwise matrix extension commutes with the inclusion of cyclic cochains into column zero. -/
@[simp]
theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal (ι : Type*) [Fintype ι]
    {m : ℕ} (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  apply Subtype.ext
  funext q
  rcases eq_or_ne q m with rfl | hne
  · simp
  · simp [Pi.single_eq_of_ne hne]

end Horizontal

section Differential

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Generalized matrix trace commutes with the vertical differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_hochschildCoboundary]
  · simp [hp, matrixCochainExtension_barCoboundary]

/-- Rowwise matrix extension commutes with the total differential `D = d_h + d_v` of the cyclic
bicomplex. -/
theorem cyclicTotalDifferential_matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι]
    {m : ℕ} (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) := by
  apply Subtype.ext
  funext q
  cases q with
  | zero =>
    simp [matrixCochainExtension_cyclicBicomplexHorizontal]
  | succ q =>
    simp [map_add, matrixCochainExtension_cyclicBicomplexVertical,
      matrixCochainExtension_cyclicBicomplexHorizontal]

end Differential

end TotalCochains

/-! ### Compatibility of `cyclicCohomology.matrixExtension` with `I`, `B`, and `S` -/

namespace cyclicCohomology

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix extension on cyclic cohomology commutes with the map `I` to Hochschild cohomology. -/
@[simp]
theorem toHochschild_matrixExtension (n : ℕ) (c : cyclicCohomology R A M n) :
    toHochschild R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n (toHochschild R A M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp

/-- Matrix extension on cyclic cohomology commutes with Connes' operator `B` on Hochschild
cohomology. -/
@[simp]
theorem matrixExtension_connesB (n : ℕ) (c : hochschildCohomology R A M (n + 1)) :
    matrixExtension M ι n (hochschildCohomology.connesB R A M n c) =
      hochschildCohomology.connesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (n + 1) c
  simp only [hochschildCohomology.connesB_mk, matrixExtension_mk,
    hochschildCohomology.matrixExtension_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_matrixCyclicCochainExtension_apply]
  exact matrixCochainExtension_connesB ι n φ.1

/-- Matrix extension on cyclic cohomology over a `ℚ`-algebra commutes with Connes' periodicity
operator `S`. -/
@[simp]
theorem matrixExtension_periodicity [Algebra ℚ R] (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixExtension M ι (n + 2) (periodicity R A M n c) =
      periodicity R (Matrix ι ι A) M n (matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [periodicity_mk, matrixExtension_mk]
  congr 1
  exact Subtype.ext (matrixCyclicCochainExtension_cyclicCocyclesPeriodicity ι n φ)

/-- Matrix extension on cyclic cohomology over a `ℚ`-algebra commutes with the iterated periodicity
transitions `S^(j - i)`. -/
theorem matrixExtension_periodicTransition [Algebra ℚ R] (n : ℕ) {i j : ℕ} (h : i ≤ j)
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

section TotalCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Rowwise matrix extension maps total cocycles to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker (ι : Type*) [Fintype ι] {m : ℕ}
    {x : cyclicTotalCochains R A M m}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M m)) :
    matrixCyclicTotalCochainExtension ι m x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hx, map_zero]

private theorem cyclicTotalHomologyMk_matrixExtension_eq_zero (ι : Type*) [Fintype ι] {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m))
    (hx0 : cyclicTotalHomologyMk R A M m x = 0) :
    cyclicTotalHomologyMk R (Matrix ι ι A) M m
      ⟨matrixCyclicTotalCochainExtension ι m x.1,
        matrixCyclicTotalCochainExtension_mem_ker ι x.2⟩ = 0 := by
  cases m with
  | zero =>
    obtain rfl := (cyclicTotalHomologyMk_zero_eq_zero_iff x).1 hx0
    simp
  | succ n =>
    obtain ⟨w, hw⟩ := (cyclicTotalHomologyMk_succ_eq_zero_iff x).1 hx0
    refine (cyclicTotalHomologyMk_succ_eq_zero_iff _).2
      ⟨matrixCyclicTotalCochainExtension ι n w, ?_⟩
    rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hw]

variable (M) in
/-- Matrix extension on the cohomology `Hᵐ(Tot)` of the total cyclic bicomplex, induced by
`matrixCyclicTotalCochainExtension`. -/
noncomputable def cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    (cyclicTotalComplex R A M).homology m →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  (cyclicTotalHomologyMk R A M m).liftOfSurjective (cyclicTotalHomologyMk_surjective m)
    ⟨cyclicTotalHomologyMk R (Matrix ι ι A) M m ∘ₗ
        (matrixCyclicTotalCochainExtension ι m).restrict
          (fun _ ↦ matrixCyclicTotalCochainExtension_mem_ker ι),
      fun x (hx : x ∈ LinearMap.ker (cyclicTotalHomologyMk R A M m)) ↦
        LinearMap.mem_ker.2
          (cyclicTotalHomologyMk_matrixExtension_eq_zero ι x (LinearMap.mem_ker.1 hx))⟩

/-- `cyclicTotalHomologyMatrixExtension` sends the class of a total cocycle to the class of its
rowwise matrix extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk (ι : Type*) [Fintype ι]
    {m : ℕ} (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyMk R A M m x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M m
        ⟨matrixCyclicTotalCochainExtension ι m x.1,
          matrixCyclicTotalCochainExtension_mem_ker ι x.2⟩ :=
  LinearMap.equivOfSurjective_apply _ _

/-- Matrix extension on `Hᵐ(Tot)` commutes with the projection `I` onto Hochschild cohomology. -/
@[simp]
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      hochschildCohomology.matrixExtension M ι m
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp

/-- Matrix extension on `Hᵐ(Tot)` commutes with the periodicity map `S : Hᵐ(Tot) → Hᵐ⁺²(Tot)`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity
    (ι : Type*) [Fintype ι] (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyMatrixExtension M ι (m + 2) (cyclicTotalHomologyPeriodicity R A M m c) =
      cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m
        (cyclicTotalHomologyMatrixExtension M ι m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity ι x.1)

/-- Matrix extension on `Hᵐ(Tot)` commutes with the iterated transition maps `S^(j - i)`. -/
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicTransition
    (ι : Type*) [Fintype ι] (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h c) =
      cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) c) := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hij
        (Nat.le_add_right j 1),
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ,
      ModuleCat.comp_apply, ModuleCat.comp_apply, ← ih,
      ← cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity]
    rfl

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Matrix extension commutes with the comparison map `HCᵐ → Hᵐ(Tot)` from cyclic cohomology to
the cohomology of the total cyclic bicomplex. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal
    (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) (c : cyclicCohomology R A M m) :
    cyclicTotalHomologyMatrixExtension M ι m
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m c) =
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) m
        (cyclicCohomology.matrixExtension M ι m c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M m c
  simp only [homologyMap_cyclicCochainComplexToTotal_mk, cyclicCohomology.matrixExtension_mk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι φ.1)

/-- Matrix extension commutes with Connes' operator `B : HHᵐ⁺¹ → Hᵐ(Tot)` on the cyclic
bicomplex. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB
    (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ)
    (c : hochschildCohomology R A M (m + 1)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyConnesB R A M m c) =
      cyclicTotalHomologyConnesB R (Matrix ι ι A) M m
        (hochschildCohomology.matrixExtension M ι (m + 1) c) := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.comp_apply,
    ModuleCat.comp_apply,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    cyclicCohomology.matrixExtension_connesB]

private theorem bijective_cyclicTotalHomologyMatrixExtension_zero (ι : Type*) [Fintype ι]
    [Nonempty ι] :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 0) := by
  classical
  have hIA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hIM : Function.Bijective
      (HomologicalComplex.homologyMap
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

private theorem bijective_cyclicTotalHomologyMatrixExtension_one (ι : Type*) [Fintype ι]
    [Nonempty ι] :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 1) := by
  classical
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 1).hom
    (cyclicTotalHomologyConnesB R A M 0).hom
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 1).hom
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M 0).hom
    (cyclicTotalHomologyMatrixExtension M ι 1)
    (hochschildCohomology.matrixExtension M ι 1)
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

/-- **Matrix Morita invariance of the total cyclic bicomplex.** Over every commutative ring `R`,
for a unital `R`-algebra `A` and a nonempty finite index type `ι`,
`cyclicTotalHomologyMatrixExtension` is bijective in every degree. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) :
    Function.Bijective
      (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => exact bijective_cyclicTotalHomologyMatrixExtension_zero ι
    | 1 => exact bijective_cyclicTotalHomologyMatrixExtension_one ι
    | m + 2 =>
      exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
        (cyclicTotalHomologyConnesB R A M m).hom
        (cyclicTotalHomologyPeriodicity R A M m).hom
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 2)).hom
        (cyclicTotalHomologyConnesB R A M (m + 1)).hom
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m).hom
        (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m).hom
        (HomologicalComplex.homologyMap
          (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) (m + 2)).hom
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M (m + 1)).hom
        (hochschildCohomology.matrixExtension M ι (m + 1))
        (cyclicTotalHomologyMatrixExtension M ι m)
        (cyclicTotalHomologyMatrixExtension M ι (m + 2))
        (hochschildCohomology.matrixExtension M ι (m + 2))
        (cyclicTotalHomologyMatrixExtension M ι (m + 1))
        (LinearMap.ext (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB ι m)).symm
        (LinearMap.ext
          (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity ι m)).symm
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
        (hochschildCohomology.bijective_matrixExtension ι (m + 1)).2
        (ih m (by omega))
        (hochschildCohomology.bijective_matrixExtension ι (m + 2))
        (ih (m + 1) (by omega)).1

variable (M) in
/-- **Matrix Morita equivalence on the cohomology of the total cyclic bicomplex.** The `R`-linear
equivalence `Hⁿ(Tot A) ≃ₗ[R] Hⁿ(Tot (Matrix ι ι A))` over any commutative ring `R` for unital `A`
and nonempty finite `ι`. -/
noncomputable def cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) :
    (cyclicTotalComplex R A M).homology n ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι n)
    (bijective_cyclicTotalHomologyMatrixExtension ι n)

/-- The underlying linear map of `cyclicTotalHomologyMatrixExtensionEquiv` is
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem coe_cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) :
    (cyclicTotalHomologyMatrixExtensionEquiv (R := R) (A := A) M ι n :
      (cyclicTotalComplex R A M).homology n →ₗ[R]
        (cyclicTotalComplex R (Matrix ι ι A) M).homology n) =
      cyclicTotalHomologyMatrixExtension M ι n :=
  (rfl)

/-- `cyclicTotalHomologyMatrixExtensionEquiv` acts by `cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixExtensionEquiv M ι n c =
      cyclicTotalHomologyMatrixExtension M ι n c :=
  (rfl)

end Unital

end TotalCohomology

/-! ### Matrix Morita invariance of cyclic cohomology -/

namespace cyclicCohomology

section Morita

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of cyclic cohomology under invertibility of `1, …, n`.** If
`(q : R) + 1` is a unit in `R` for every `q < n`, then `cyclicCohomology.matrixExtension` is
bijective in degree `n` for any unital `R`-algebra `A` and nonempty finite index type `ι`. -/
theorem bijective_matrixExtension_of_isUnit (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have hjA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have hjM : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  have hcomm : (HomologicalComplex.homologyMap
      (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) ∘ matrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι n ∘
        HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n :=
    funext fun c ↦
      (cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal ι n c).symm
  exact (hjM.of_comp_iff' _).1
    (hcomm ▸ (bijective_cyclicTotalHomologyMatrixExtension ι n).comp hjA)

/-- In degree zero, `cyclicCohomology.matrixExtension` is bijective over every commutative ring
`R`. -/
theorem bijective_matrixExtension_zero (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 (by simp)

/-- In degree one, `cyclicCohomology.matrixExtension` is bijective over every commutative ring
`R`. -/
theorem bijective_matrixExtension_one (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 1) :=
  bijective_matrixExtension_of_isUnit ι 1 fun q hq ↦ by
    obtain rfl : q = 0 := Nat.lt_one_iff.1 hq
    simp

/-- **Matrix Morita invariance of cyclic cohomology.** Over a `ℚ`-algebra `R`, for any unital
`R`-algebra `A` and nonempty finite index type `ι`, `cyclicCohomology.matrixExtension` is bijective
in every degree. -/
theorem bijective_matrixExtension [Algebra ℚ R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have hjA := bijective_homologyMap_cyclicCochainComplexToTotal R A M n
  have hjM := bijective_homologyMap_cyclicCochainComplexToTotal R (Matrix ι ι A) M n
  have hcomm : (HomologicalComplex.homologyMap
      (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) ∘ matrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι n ∘
        HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n :=
    funext fun c ↦
      (cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal ι n c).symm
  exact (hjM.of_comp_iff' _).1
    (hcomm ▸ (bijective_cyclicTotalHomologyMatrixExtension ι n).comp hjA)

variable (M) in
/-- **Matrix Morita equivalence on cyclic cohomology.** The `R`-linear equivalence
`HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a `ℚ`-algebra `R` for unital `A` and nonempty finite
`ι`. -/
noncomputable def matrixExtensionEquiv [Algebra ℚ R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The underlying linear map of `cyclicCohomology.matrixExtensionEquiv` is
`cyclicCohomology.matrixExtension`. -/
@[simp]
theorem coe_matrixExtensionEquiv [Algebra ℚ R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

/-- `cyclicCohomology.matrixExtensionEquiv` acts by `cyclicCohomology.matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply [Algebra ℚ R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

end Morita

end cyclicCohomology

/-! ### Matrix Morita invariance of periodic cyclic cohomology -/

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

private theorem linearMap_ext {n : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    {f₁ f₂ : periodicCyclicCohomology R A M n →ₗ[R] N}
    (h : ∀ k x, f₁ (periodicCyclicCohomology.ι R A M n k x) =
      f₂ (periodicCyclicCohomology.ι R A M n k x)) :
    f₁ = f₂ := by
  ext z
  obtain ⟨k, x, rfl⟩ := exists_ι_eq z
  exact h k x

private theorem apply_eq_of_ι_eq {n : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) (x),
      g j (cyclicTotalHomologyPeriodicTransition R A M n h x) = g i x)
    {k₁ k₂ : ℕ} {x₁ : (cyclicTotalComplex R A M).homology (n + 2 * k₁)}
    {x₂ : (cyclicTotalComplex R A M).homology (n + 2 * k₂)}
    (h : periodicCyclicCohomology.ι R A M n k₁ x₁ =
      periodicCyclicCohomology.ι R A M n k₂ x₂) :
    g k₁ x₁ = g k₂ x₂ := by
  have hι0 : periodicCyclicCohomology.ι R A M n (max k₁ k₂)
      (cyclicTotalHomologyPeriodicTransition R A M n (le_max_left k₁ k₂) x₁ -
        cyclicTotalHomologyPeriodicTransition R A M n (le_max_right k₁ k₂) x₂) = 0 := by
    rw [map_sub, cyclicTotalHomologyPeriodicTransition_ι_apply,
      cyclicTotalHomologyPeriodicTransition_ι_apply, h, sub_self]
  obtain ⟨K, hjK, hK⟩ := (ι_eq_zero_iff _).1 hι0
  have hgK := congrArg (g K) hK
  rw [map_sub, map_sub, map_zero, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    cyclicTotalHomologyPeriodicTransition_comp, cyclicTotalHomologyPeriodicTransition_comp,
    hg, hg, sub_eq_zero] at hgK
  exact hgK

private noncomputable def liftLinearMapFun (n : ℕ) {N : Type*} [AddCommGroup N] [Module R N]
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (z : periodicCyclicCohomology R A M n) : N :=
  g (exists_ι_eq z).choose (exists_ι_eq z).choose_spec.choose

private theorem liftLinearMapFun_ι {n : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) (x),
      g j (cyclicTotalHomologyPeriodicTransition R A M n h x) = g i x)
    (k : ℕ) (x : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    liftLinearMapFun n g (periodicCyclicCohomology.ι R A M n k x) = g k x :=
  apply_eq_of_ι_eq g hg (exists_ι_eq _).choose_spec.choose_spec

private noncomputable def liftLinearMap (n : ℕ) {N : Type*} [AddCommGroup N] [Module R N]
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) (x),
      g j (cyclicTotalHomologyPeriodicTransition R A M n h x) = g i x) :
    periodicCyclicCohomology R A M n →ₗ[R] N where
  toFun := liftLinearMapFun n g
  map_add' z₁ z₂ := by
    obtain ⟨k₁, x₁, rfl⟩ := exists_ι_eq z₁
    obtain ⟨k₂, x₂, rfl⟩ := exists_ι_eq z₂
    rw [← cyclicTotalHomologyPeriodicTransition_ι_apply (le_max_left k₁ k₂) x₁,
      ← cyclicTotalHomologyPeriodicTransition_ι_apply (le_max_right k₁ k₂) x₂,
      ← map_add, liftLinearMapFun_ι g hg, liftLinearMapFun_ι g hg, liftLinearMapFun_ι g hg,
      map_add]
  map_smul' r z := by
    obtain ⟨k, x, rfl⟩ := exists_ι_eq z
    rw [← map_smul, liftLinearMapFun_ι g hg, liftLinearMapFun_ι g hg, map_smul,
      RingHom.id_apply]

private theorem liftLinearMap_ι (n : ℕ) {N : Type*} [AddCommGroup N] [Module R N]
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) (x),
      g j (cyclicTotalHomologyPeriodicTransition R A M n h x) = g i x)
    (k : ℕ) (x : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    liftLinearMap n g hg (periodicCyclicCohomology.ι R A M n k x) = g k x :=
  liftLinearMapFun_ι g hg k x

variable (M) in
/-- Matrix extension `HPⁿ(A; M) →ₗ[R] HPⁿ(Matrix ι ι A; M)` on periodic cyclic cohomology,
induced on the direct limit by `cyclicTotalHomologyMatrixExtension` at each stage `n + 2k`. -/
noncomputable def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  liftLinearMap n
    (fun k ↦ (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun _ _ h x ↦ by
      change periodicCyclicCohomology.ι R (Matrix ι ι A) M n _
          (cyclicTotalHomologyMatrixExtension M ι _
            (cyclicTotalHomologyPeriodicTransition R A M n h x)) =
        periodicCyclicCohomology.ι R (Matrix ι ι A) M n _
          (cyclicTotalHomologyMatrixExtension M ι _ x)
      rw [cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicTransition,
        cyclicTotalHomologyPeriodicTransition_ι_apply]

/-- On the `k`-th stage `Hⁿ⁺²ᵏ(Tot)`, `periodicCyclicCohomology.matrixExtension` acts via
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem matrixExtension_ι (ι : Type*) [Fintype ι] (n k : ℕ)
    (x : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k x) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) x) :=
  liftLinearMap_ι n _ _ k x

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

private theorem symm_cyclicTotalHomologyMatrixExtensionEquiv_transition (ι : Type*) [Fintype ι]
    [Nonempty ι] (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (y : (cyclicTotalComplex R (Matrix ι ι A) M).homology (n + 2 * i)) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * j)).symm
        (cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h y) =
      cyclicTotalHomologyPeriodicTransition R A M n h
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * i)).symm y) := by
  apply (cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * j)).injective
  rw [LinearEquiv.apply_symm_apply, cyclicTotalHomologyMatrixExtensionEquiv_apply,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicTransition,
    ← cyclicTotalHomologyMatrixExtensionEquiv_apply, LinearEquiv.apply_symm_apply]

private noncomputable def matrixExtensionInv (M : Type*) [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R (Matrix ι ι A) M n →ₗ[R] periodicCyclicCohomology R A M n :=
  liftLinearMap n
    (fun k ↦ (periodicCyclicCohomology.ι R A M n k).hom ∘ₗ
      (cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * k)).symm.toLinearMap)
    fun _ _ h y ↦ by
      change periodicCyclicCohomology.ι R A M n _
          ((cyclicTotalHomologyMatrixExtensionEquiv M ι _).symm
            (cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h y)) =
        periodicCyclicCohomology.ι R A M n _
          ((cyclicTotalHomologyMatrixExtensionEquiv M ι _).symm y)
      rw [symm_cyclicTotalHomologyMatrixExtensionEquiv_transition,
        cyclicTotalHomologyPeriodicTransition_ι_apply]

variable (M) in
/-- **Matrix Morita equivalence on periodic cyclic cohomology.** Over every commutative ring `R`,
for any unital `R`-algebra `A` and nonempty finite index type `ι`,
`periodicCyclicCohomology.matrixExtension` is an `R`-linear equivalence
`HPⁿ(A; M) ≃ₗ[R] HPⁿ(Matrix ι ι A; M)`. -/
noncomputable def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofLinearMap (matrixExtension M ι n) (matrixExtensionInv M ι n)
    (linearMap_ext fun k y ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      dsimp only [matrixExtensionInv]
      rw [liftLinearMap_ι]
      change matrixExtension M ι n
        (periodicCyclicCohomology.ι R A M n k
          ((cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * k)).symm y)) = _
      rw [matrixExtension_ι, ← cyclicTotalHomologyMatrixExtensionEquiv_apply,
        LinearEquiv.apply_symm_apply])
    (linearMap_ext fun k x ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, matrixExtension_ι]
      dsimp only [matrixExtensionInv]
      rw [liftLinearMap_ι]
      change periodicCyclicCohomology.ι R A M n k
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * k)).symm
          (cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * k) x)) = _
      rw [LinearEquiv.symm_apply_apply])

/-- The underlying linear map of `periodicCyclicCohomology.matrixExtensionEquiv` is
`periodicCyclicCohomology.matrixExtension`. -/
@[simp]
theorem coe_matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  LinearMap.ext fun _ ↦ rfl

/-- `periodicCyclicCohomology.matrixExtensionEquiv` acts by
`periodicCyclicCohomology.matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- **Matrix Morita invariance of periodic cyclic cohomology.** Over every commutative ring `R`,
for any unital `R`-algebra `A` and nonempty finite index type `ι`,
`periodicCyclicCohomology.matrixExtension` is bijective in every degree. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  (matrixExtensionEquiv M ι n).bijective

/-- Matrix extension on periodic cyclic cohomology commutes with the normalized stage maps
`fromCyclicCohomology` from cyclic cohomology. -/
@[simp]
theorem matrixExtension_fromCyclicCohomology [Algebra ℚ R] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (n k : ℕ) (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix ι ι A) M n k
        (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by
  rw [fromCyclicCohomology_def, fromCyclicCohomology_def]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, matrixExtension_ι,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]

end Unital

end periodicCyclicCohomology

end TauCeti
