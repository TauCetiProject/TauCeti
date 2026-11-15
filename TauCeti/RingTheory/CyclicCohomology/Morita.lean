/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.PeriodicCohomology
public import TauCeti.RingTheory.HochschildCohomology.Morita
import Mathlib.Algebra.FiveLemma

/-!
# Matrix Morita invariance of cyclic and periodic cyclic cohomology

Let `A` be a unital algebra over a commutative ring `R`, `M` an `R`-module, and `ι` a nonempty
finite index type. Extending multilinear cochains on `A` to `Matrix ι ι A` by the generalized
matrix trace `φ ↦ φ#Tr` commutes with all differentials of Connes' cyclic bicomplex (`1 - λ`, `N`,
`b`, and `-b'`), hence induces an `R`-linear map `cyclicTotalHomologyMatrixExtension` on the
cohomology `H^m(Tot)` of the total cyclic bicomplex that intertwines the operators `I`, `B`, and
`S` of the SBI exact sequence.

By `TauCeti.hochschildCohomology.bijective_matrixExtension`, matrix extension is an isomorphism on
Hochschild cohomology in every degree over any commutative ring `R`. Applying the five lemma
along the SBI exact sequence

`0 → H^0(Tot) →I HH^0 → 0 → H^1(Tot) →I HH^1 →B H^0(Tot) →S H^2(Tot) →I HH^2 →B H^1(Tot) → ⋯`

proves by two-step induction on `m` that `cyclicTotalHomologyMatrixExtension` is bijective in
every degree over every commutative ring `R`.

Two consequences follow directly:

* Whenever `1, 2, …, n` are invertible in `R`, the inclusion of Connes' cyclic cochain complex
  into column zero of the total cyclic bicomplex is a quasi-isomorphism in degree `n`
  (`TauCeti.quasiIsoAt_cyclicCochainComplexToTotal`), so
  `TauCeti.cyclicCohomology.matrixExtension` is bijective in degree `n`. In particular, over any
  `ℚ`-algebra `R`, `HC^n(A; M) → HC^n(Matrix ι ι A; M)` is bijective in all degrees `n`
  (`TauCeti.cyclicCohomology.bijective_matrixExtension`).
* Passing to the direct limit along the bicomplex periodicity maps `S`, matrix extension induces a
  linear equivalence `HP^n(A; M) ≃ₗ[R] HP^n(Matrix ι ι A; M)` on periodic cyclic cohomology over
  every commutative ring `R` (`TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`), compatible
  over `ℚ`-algebras with the normalized maps `periodicCyclicCohomology.fromCyclicCohomology`.

Because `Matrix ι ι A` lives in the universe `max u_ι u_A`, the matrix extension maps and
equivalences are stated as `R`-linear maps and equivalences rather than morphisms in a single
`ModuleCat R` universe, keeping `R`, `A`, `M`, and `ι` in independent universes.

## Main definitions

* `TauCeti.matrixTotalCochainExtension`: rowwise generalized matrix trace on total cochains of
  Connes' cyclic bicomplex.
* `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`: the induced map and linear equivalence on
  `H^m(Tot)` over any commutative ring `R`.
* `TauCeti.cyclicCohomology.matrixExtensionEquiv`: the linear equivalence
  `HC^n(A; M) ≃ₗ[R] HC^n(Matrix ι ι A; M)` over a `ℚ`-algebra.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`: the induced map and linear equivalence
  `HP^n(A; M) ≃ₗ[R] HP^n(Matrix ι ι A; M)` over any commutative ring `R`.

## Main results

* `TauCeti.matrixCochainExtension_barCoboundary`,
  `TauCeti.matrixCochainExtension_cochainPeriodicity`: matrix extension commutes with the bar
  coboundary `b'` and Connes' cochain periodicity operator `S₀`.
* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix Morita invariance of the total
  cyclic bicomplex cohomology over any commutative ring `R`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of Connes' cyclic
  cohomology when `1, …, n` are units in `R`, and in all degrees over a `ℚ`-algebra.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of
  periodic cyclic cohomology over any commutative ring `R`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, Corollary 22.
* J.-L. Loday, *Cyclic Homology*, §1.2 and Theorem 2.2.9.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

/-! ### Compatibility of matrix extension with cochain operators and total cochains -/

section CochainOperators

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- Matrix extension commutes with the bar coboundary: `(b' φ)#Tr = b'(φ#Tr)`. -/
theorem matrixCochainExtension_barCoboundary (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 1) (barCoboundary R A M n φ) =
      barCoboundary R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  have hbA := eq_sub_of_add_eq (hochschildCoboundary_eq_barCoboundary_add (R := R) φ).symm
  have hbM := eq_sub_of_add_eq
    (hochschildCoboundary_eq_barCoboundary_add (R := R) (matrixCochainExtension ι n φ)).symm
  rw [hbA, hbM, map_sub, map_zsmul, matrixCochainExtension_hochschildCoboundary,
    matrixCochainExtension_hochschildCoface]

private theorem cochainPeriodicity_eq_sum (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cochainPeriodicity R A M n φ =
      ∑ j : Fin (n + 1), ∑ r ∈ Finset.Iic j,
        (-1 : ℤ) ^ ((j : ℕ) - r) •
          hochschildCoface R A M j.succ.castSucc (hochschildCoface R A M r.castSucc φ) := by
  ext b
  simp [cochainPeriodicity_apply]

/-- Matrix extension commutes with Connes' cochain periodicity operator `S₀`. -/
theorem matrixCochainExtension_cochainPeriodicity (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 2) (cochainPeriodicity R A M n φ) =
      cochainPeriodicity R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  rw [cochainPeriodicity_eq_sum, cochainPeriodicity_eq_sum]
  simp only [map_sum, map_zsmul, matrixCochainExtension_hochschildCoface]

end CochainOperators

section BicomplexDifferentials

/-- Matrix extension commutes with the horizontal differentials of the cyclic bicomplex. -/
private theorem matrixCochainExtension_cyclicBicomplexHorizontal
    {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexHorizontal_of_even hp, cyclicBicomplexHorizontal_of_even hp,
      LinearMap.sub_apply, LinearMap.sub_apply, _root_.one_apply_eq_self, _root_.one_apply_eq_self,
      map_sub, matrixCochainExtension_cyclicOperator]
  · rw [cyclicBicomplexHorizontal_of_odd hp, cyclicBicomplexHorizontal_of_odd hp,
      matrixCochainExtension_cyclicNorm]

/-- Matrix extension commutes with the vertical differentials of the cyclic bicomplex. -/
private theorem matrixCochainExtension_cyclicBicomplexVertical
    {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexVertical_of_even hp, cyclicBicomplexVertical_of_even hp,
      matrixCochainExtension_hochschildCoboundary]
  · rw [cyclicBicomplexVertical_of_odd hp, cyclicBicomplexVertical_of_odd hp,
      LinearMap.neg_apply, LinearMap.neg_apply, map_neg, matrixCochainExtension_barCoboundary]

end BicomplexDifferentials

section TotalCochains

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

section Monoid

variable [AddCommMonoid M] [Module R M]

/-- Rowwise extension of total cochains of the cyclic bicomplex to `Matrix ι ι A` by the
generalized matrix trace. -/
def matrixTotalCochainExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  LinearMap.codRestrict (cyclicTotalCochains R (Matrix ι ι A) M m)
    (LinearMap.pi fun q ↦
      matrixCochainExtension ι q ∘ₗ LinearMap.proj q ∘ₗ (cyclicTotalCochains R A M m).subtype)
    fun x ↦ mem_cyclicTotalCochains_iff.2 fun q hq ↦ by
      simp [coe_cyclicTotalCochains_apply_of_lt x hq]

/-- In row `q`, `matrixTotalCochainExtension` applies `matrixCochainExtension ι q`. -/
@[simp]
theorem coe_matrixTotalCochainExtension_apply {ι : Type*} [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) :=
  (rfl)

/-- `matrixTotalCochainExtension` is injective for every nonempty matrix index type. -/
theorem matrixTotalCochainExtension_injective (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    Function.Injective (matrixTotalCochainExtension (R := R) (A := A) (M := M) ι m) := by
  intro x y h
  refine Subtype.ext (funext fun q ↦ matrixCochainExtension_injective ι q ?_)
  exact congrArg (fun z : cyclicTotalCochains R (Matrix ι ι A) M m ↦ z.1 q) h

/-- `matrixTotalCochainExtension` commutes with the bicomplex periodicity shift on total
cochains. -/
@[simp]
theorem matrixTotalCochainExtension_cyclicTotalPeriodicity {ι : Type*} [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    matrixTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixTotalCochainExtension ι m x) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  simp

/-- Projecting a matrix-extended total cochain onto column zero gives the matrix extension of its
column-zero component. -/
theorem cyclicTotalToHochschild_matrixTotalCochainExtension {ι : Type*} [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by
  rw [cyclicTotalToHochschild_apply, cyclicTotalToHochschild_apply,
    coe_matrixTotalCochainExtension_apply]

end Monoid

section Group

variable [AddCommGroup M] [Module R M]

/-- Including a cyclic cochain into column zero commutes with matrix extension. -/
@[simp]
theorem matrixTotalCochainExtension_cyclicCochainsToTotal {ι : Type*} [Fintype ι] {m : ℕ}
    (φ : cyclicCochains R A M m) :
    matrixTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  by_cases hq : q = m
  · subst hq
    simp
  · simp [Pi.single_eq_of_ne hq]

end Group

end TotalCochains

section TotalDifferential

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Rowwise matrix extension commutes with the total differential of the cyclic bicomplex. -/
@[simp]
theorem cyclicTotalDifferential_matrixTotalCochainExtension {ι : Type*} [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R (Matrix ι ι A) M m (matrixTotalCochainExtension ι m x) =
      matrixTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  cases q with
  | zero =>
    simp [matrixCochainExtension_cyclicBicomplexHorizontal]
  | succ q =>
    simp [matrixCochainExtension_cyclicBicomplexHorizontal,
      matrixCochainExtension_cyclicBicomplexVertical]

/-- Rowwise matrix extension maps total cocycles to total cocycles. -/
theorem matrixTotalCochainExtension_mem_ker {ι : Type*} [Fintype ι] {m : ℕ}
    {x : cyclicTotalCochains R A M m}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M m)) :
    matrixTotalCochainExtension ι m x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [cyclicTotalDifferential_matrixTotalCochainExtension, hx, map_zero]

end TotalDifferential

/-! ### Cohomology of the total cyclic bicomplex -/

section TotalHomology

section NonUnital

variable {R A : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Universal property descending a linear map on total cocycles that vanishes on total
coboundaries to `(cyclicTotalComplex R A M).homology m`, into an `R`-module in any universe. -/
private def cyclicTotalHomologyDesc {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (m : ℕ)
    (f : LinearMap.ker (cyclicTotalDifferential R A M m) →ₗ[R] N)
    (hf : ∀ x, cyclicTotalHomologyMk R A M m x = 0 → f x = 0) :
    (cyclicTotalComplex R A M).homology m →ₗ[R] N :=
  (cyclicTotalHomologyMk R A M m).liftOfSurjective (cyclicTotalHomologyMk_surjective m)
    ⟨f, fun x hx ↦ LinearMap.mem_ker.2 (hf x (LinearMap.mem_ker.1 hx))⟩

private theorem cyclicTotalHomologyDesc_mk {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (m : ℕ)
    (f : LinearMap.ker (cyclicTotalDifferential R A M m) →ₗ[R] N)
    (hf : ∀ x, cyclicTotalHomologyMk R A M m x = 0 → f x = 0)
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyDesc m f hf (cyclicTotalHomologyMk R A M m x) = f x :=
  LinearMap.equivOfSurjective_apply _ _

private theorem cyclicTotalHomologyMk_matrixTotalCochainExtension_eq_zero
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] {m : ℕ}
    {x : LinearMap.ker (cyclicTotalDifferential R A M m)}
    (hx : cyclicTotalHomologyMk R A M m x = 0) :
    cyclicTotalHomologyMk R (Matrix ι ι A) M m
      ⟨matrixTotalCochainExtension ι m x.1, matrixTotalCochainExtension_mem_ker x.2⟩ = 0 := by
  cases m with
  | zero =>
    rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hx ⊢
    subst hx
    exact Subtype.ext (by simp)
  | succ n =>
    obtain ⟨w, hw⟩ := (cyclicTotalHomologyMk_succ_eq_zero_iff x).1 hx
    refine (cyclicTotalHomologyMk_succ_eq_zero_iff _).2
      ⟨matrixTotalCochainExtension ι n w, ?_⟩
    rw [cyclicTotalDifferential_matrixTotalCochainExtension, hw]

/-- The `R`-linear map on the cohomology `H^m(Tot)` of Connes' total cyclic bicomplex induced by
the generalized matrix trace. -/
def cyclicTotalHomologyMatrixExtension (M : Type*) [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] (m : ℕ) :
    (cyclicTotalComplex R A M).homology m →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  cyclicTotalHomologyDesc m
    (cyclicTotalHomologyMk R (Matrix ι ι A) M m ∘ₗ
      (matrixTotalCochainExtension ι m).restrict (fun _ ↦ matrixTotalCochainExtension_mem_ker))
    fun _ hx ↦ cyclicTotalHomologyMk_matrixTotalCochainExtension_eq_zero hx

/-- `cyclicTotalHomologyMatrixExtension` sends the class of a total cocycle to the class of its
rowwise matrix extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_mk {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyMk R A M m x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M m
        ⟨matrixTotalCochainExtension ι m x.1, matrixTotalCochainExtension_mem_ker x.2⟩ :=
  cyclicTotalHomologyDesc_mk _ _ _ x

/-- Matrix extension on total cyclic cohomology commutes with the projection `I : H^m(Tot) → HH^m`
onto column zero. -/
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] (m : ℕ)
    (c : (cyclicTotalComplex R A M).homology m) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      hochschildCohomology.matrixExtension M ι m
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [cyclicTotalHomologyMatrixExtension_mk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk]
  congr 1

/-- Linear-map form of
`homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension`. -/
theorem homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension
    (M : Type*) [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι] (m : ℕ) :
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) m).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι m =
      hochschildCohomology.matrixExtension M ι m ∘ₗ
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m).hom :=
  LinearMap.ext (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension m)

/-- Matrix extension on total cyclic cohomology commutes with the bicomplex periodicity map
`S : H^m(Tot) → H^(m+2)(Tot)`. -/
theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] (m : ℕ)
    (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      cyclicTotalHomologyMatrixExtension M ι (m + 2)
        (cyclicTotalHomologyPeriodicity R A M m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [cyclicTotalHomologyMatrixExtension_mk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk,
    matrixTotalCochainExtension_cyclicTotalPeriodicity]

/-- Linear-map form of `cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension`. -/
theorem cyclicTotalHomologyMatrixExtension_comp_cyclicTotalHomologyPeriodicity
    (M : Type*) [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalHomologyMatrixExtension M ι (m + 2) ∘ₗ
        (cyclicTotalHomologyPeriodicity R A M m).hom =
      (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι m :=
  LinearMap.ext fun c ↦ (cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension m c).symm

/-- Matrix extension on total cyclic cohomology commutes with all transition maps `S^(j-i)` of the
periodic direct system. -/
theorem cyclicTotalHomologyMatrixExtension_comp_cyclicTotalHomologyPeriodicTransition
    (M : Type*) [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι] (n : ℕ) {i j : ℕ}
    (h : i ≤ j) :
    cyclicTotalHomologyMatrixExtension M ι (n + 2 * j) ∘ₗ
        (cyclicTotalHomologyPeriodicTransition R A M n h).hom =
      (cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) := by
  induction j, h using Nat.le_induction with
  | base =>
    simp [cyclicTotalHomologyPeriodicTransition_self]
  | succ j hij ih =>
    have hstep :
        cyclicTotalHomologyMatrixExtension M ι (n + 2 * (j + 1)) ∘ₗ
          (cyclicTotalHomologyPeriodicity R A M (n + 2 * j)).hom =
        (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M (n + 2 * j)).hom ∘ₗ
          cyclicTotalHomologyMatrixExtension M ι (n + 2 * j) :=
      cyclicTotalHomologyMatrixExtension_comp_cyclicTotalHomologyPeriodicity M ι (n + 2 * j)
    rw [← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hij
        (Nat.le_add_right j 1),
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ,
      ModuleCat.hom_comp, ModuleCat.hom_comp, ← LinearMap.comp_assoc, hstep,
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Matrix extension on cyclic cohomology commutes with the inclusion into column zero of the
total cyclic bicomplex. -/
theorem homologyMap_cyclicCochainComplexToTotal_matrixExtension
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (c : cyclicCohomology R A M m) :
    HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) m
        (cyclicCohomology.matrixExtension M ι m c) =
      cyclicTotalHomologyMatrixExtension M ι m
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M m c
  simp only [cyclicCohomology.matrixExtension_mk, homologyMap_cyclicCochainComplexToTotal_mk,
    cyclicTotalHomologyMatrixExtension_mk]
  congr 1
  exact Subtype.ext (matrixTotalCochainExtension_cyclicCochainsToTotal φ.1).symm

/-- Matrix extension commutes with Connes' operator `B : HH^(n+1) → HC^n`. -/
theorem cyclicCohomology.matrixExtension_connesB
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (c : hochschildCohomology R A M (n + 1)) :
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

/-- Matrix extension commutes with the connecting operator `B : HH^(m+1) → H^m(Tot)` of the
bicomplex SBI sequence. -/
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (c : hochschildCohomology R A M (m + 1)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyConnesB R A M m c) =
      cyclicTotalHomologyConnesB R (Matrix ι ι A) M m
        (hochschildCohomology.matrixExtension M ι (m + 1) c) := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.comp_apply,
    ModuleCat.comp_apply, ← homologyMap_cyclicCochainComplexToTotal_matrixExtension,
    cyclicCohomology.matrixExtension_connesB]

/-- Linear-map form of `cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB`. -/
theorem cyclicTotalHomologyConnesB_comp_matrixExtension
    (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) :
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m).hom ∘ₗ
        hochschildCohomology.matrixExtension M ι (m + 1) =
      cyclicTotalHomologyMatrixExtension M ι m ∘ₗ (cyclicTotalHomologyConnesB R A M m).hom :=
  LinearMap.ext fun c ↦ (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB m c).symm

private theorem bijective_cyclicTotalHomologyMatrixExtension_zero (ι : Type*) [Fintype ι]
    [Nonempty ι] :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 0) := by
  have hIA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hIM : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hHH := hochschildCohomology.bijective_matrixExtension (R := R) (A := A) (M := M) ι 0
  refine (hIM.of_comp_iff' (cyclicTotalHomologyMatrixExtension M ι 0)).1 ?_
  have hcomm :
      HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0 ∘
        cyclicTotalHomologyMatrixExtension M ι 0 =
      hochschildCohomology.matrixExtension M ι 0 ∘
        HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0 :=
    funext (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension 0)
  rw [hcomm]
  exact hHH.comp hIA

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
    (homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension M ι 1)
    (cyclicTotalHomologyConnesB_comp_matrixExtension ι 0)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
    (hochschildCohomology.bijective_matrixExtension ι 1)
    (bijective_cyclicTotalHomologyMatrixExtension_zero ι).1
    injective_homologyMap_cyclicTotalComplexToHochschild_one
    injective_homologyMap_cyclicTotalComplexToHochschild_one

private theorem bijective_cyclicTotalHomologyMatrixExtension_add_two (ι : Type*) [Fintype ι]
    [Nonempty ι] (m : ℕ)
    (hm : Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι m))
    (hm1 : Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι (m + 1))) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι (m + 2)) := by
  classical
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (cyclicTotalHomologyConnesB R A M m).hom
    (cyclicTotalHomologyPeriodicity R A M m).hom
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 2)).hom
    (cyclicTotalHomologyConnesB R A M (m + 1)).hom
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m).hom
    (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m).hom
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M)
      (m + 2)).hom
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M (m + 1)).hom
    (hochschildCohomology.matrixExtension M ι (m + 1))
    (cyclicTotalHomologyMatrixExtension M ι m)
    (cyclicTotalHomologyMatrixExtension M ι (m + 2))
    (hochschildCohomology.matrixExtension M ι (m + 2))
    (cyclicTotalHomologyMatrixExtension M ι (m + 1))
    (cyclicTotalHomologyConnesB_comp_matrixExtension ι m)
    (cyclicTotalHomologyMatrixExtension_comp_cyclicTotalHomologyPeriodicity M ι m).symm
    (homologyMap_cyclicTotalComplexToHochschild_comp_cyclicTotalHomologyMatrixExtension M ι
      (m + 2))
    (cyclicTotalHomologyConnesB_comp_matrixExtension ι (m + 1))
    (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m)
    (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M m)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m + 1))
    (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m)
    (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
      R (Matrix ι ι A) M m)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m + 1))
    (hochschildCohomology.bijective_matrixExtension ι (m + 1)).2
    hm
    (hochschildCohomology.bijective_matrixExtension ι (m + 2))
    hm1.1

/-- **Matrix Morita invariance of total cyclic cohomology.** Over any commutative ring `R`,
`cyclicTotalHomologyMatrixExtension` is bijective in every degree `m` for every unital `R`-algebra
`A` and nonempty finite index type `ι`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] [Nonempty ι] :
    ∀ m : ℕ, Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι m)
  | 0 => bijective_cyclicTotalHomologyMatrixExtension_zero ι
  | 1 => bijective_cyclicTotalHomologyMatrixExtension_one ι
  | m + 2 => bijective_cyclicTotalHomologyMatrixExtension_add_two ι m
      (bijective_cyclicTotalHomologyMatrixExtension ι m)
      (bijective_cyclicTotalHomologyMatrixExtension ι (m + 1))

variable (R A M) in
/-- **Matrix Morita equivalence for total cyclic cohomology:** the linear equivalence
`H^m(Tot(A)) ≃ₗ[R] H^m(Tot(Matrix ι ι A))` over any commutative ring `R`. -/
def cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    (cyclicTotalComplex R A M).homology m ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι m)
    (bijective_cyclicTotalHomologyMatrixExtension ι m)

/-- Applying `cyclicTotalHomologyMatrixExtensionEquiv` applies
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_apply
    (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyMatrixExtensionEquiv R A M ι m c =
      cyclicTotalHomologyMatrixExtension M ι m c :=
  (rfl)

/-- The underlying linear map of `cyclicTotalHomologyMatrixExtensionEquiv` is
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem toLinearMap_cyclicTotalHomologyMatrixExtensionEquiv
    (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    (cyclicTotalHomologyMatrixExtensionEquiv R A M ι m).toLinearMap =
      cyclicTotalHomologyMatrixExtension M ι m :=
  (rfl)

end Unital

end TotalHomology

/-! ### Matrix Morita invariance of cyclic cohomology -/

namespace cyclicCohomology

section CommRing

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Matrix extension on cyclic cohomology commutes with `I : HC^n → HH^n`. -/
theorem toHochschild_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    toHochschild R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n (toHochschild R A M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [matrixExtension_mk, toHochschild_mk, hochschildCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (coe_matrixCyclicCochainExtension_apply ι n φ.1)

/-- **Matrix Morita invariance of cyclic cohomology in invertible degrees.** Whenever `1, 2, …, n`
are invertible in `R`, `matrixExtension : HC^n(A; M) → HC^n(Matrix ι ι A; M)` is bijective. -/
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
  have hTot := bijective_cyclicTotalHomologyMatrixExtension (R := R) (A := A) (M := M) ι n
  refine (hM.of_comp_iff' (matrixExtension M ι n)).1 ?_
  have hcomm :
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n ∘
        matrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι n ∘
        HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n :=
    funext (homologyMap_cyclicCochainComplexToTotal_matrixExtension n)
  rw [hcomm]
  exact hTot.comp hA

/-- In degree zero, `matrixExtension : HC^0(A; M) → HC^0(Matrix ι ι A; M)` is bijective over every
commutative ring `R`. -/
theorem bijective_matrixExtension_zero (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 fun _ hq ↦ absurd hq (Nat.not_lt_zero _)

end CommRing

section Rational

variable {R : Type*} [CommRing R] [Algebra ℚ R] {A : Type*} [Ring A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Over a `ℚ`-algebra, matrix extension on cyclic cohomology commutes with Connes' periodicity
operator `S : HC^n → HC^(n+2)`. -/
theorem matrixExtension_periodicity {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    matrixExtension M ι (n + 2) (periodicity R A M n c) =
      periodicity R (Matrix ι ι A) M n (matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [periodicity_mk, matrixExtension_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [Subtype.coe_mk, Subtype.coe_mk, coe_matrixCyclicCochainExtension_apply,
    coe_cyclicCocyclesPeriodicity_apply, coe_cyclicCocyclesPeriodicity_apply, Subtype.coe_mk,
    coe_matrixCyclicCochainExtension_apply]
  exact matrixCochainExtension_cochainPeriodicity ι n φ.1.1

/-- Over a `ℚ`-algebra, matrix extension commutes with every transition map `S^(j-i)` of cyclic
cohomology. -/
theorem matrixExtension_periodicTransition {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    {i j : ℕ} (h : i ≤ j) (c : cyclicCohomology R A M (n + 2 * i)) :
    matrixExtension M ι (n + 2 * j) (periodicTransition R A M n h c) =
      periodicTransition R (Matrix ι ι A) M n h (matrixExtension M ι (n + 2 * i) c) := by
  induction j, h using Nat.le_induction with
  | base =>
    simp [periodicTransition_self]
  | succ j hij ih =>
    rw [← periodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ← periodicTransition_comp R (Matrix ι ι A) M n hij (Nat.le_add_right j 1),
      periodicTransition_succ, periodicTransition_succ, ModuleCat.comp_apply, ModuleCat.comp_apply]
    exact (matrixExtension_periodicity (n + 2 * j) _).trans (congrArg _ ih)

/-- **Matrix Morita invariance of cyclic cohomology.** Over a `ℚ`-algebra `R`, for any unital
`R`-algebra `A`, `R`-module `M`, and nonempty finite index type `ι`, the generalized matrix trace
induces a bijection `HC^n(A; M) → HC^n(Matrix ι ι A; M)` in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦ by
    simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

variable (R A M) in
/-- **Matrix Morita equivalence for cyclic cohomology:** the linear equivalence
`HC^n(A; M) ≃ₗ[R] HC^n(Matrix ι ι A; M)` over a `ℚ`-algebra. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Applying `matrixExtensionEquiv` applies `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv R A M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- The underlying linear map of `cyclicCohomology.matrixExtensionEquiv` is
`cyclicCohomology.matrixExtension`. -/
@[simp]
theorem toLinearMap_matrixExtensionEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) :
    (matrixExtensionEquiv R A M ι n).toLinearMap = matrixExtension M ι n :=
  (rfl)

end Rational

end cyclicCohomology

/-! ### Matrix Morita invariance of periodic cyclic cohomology -/

namespace periodicCyclicCohomology

section LinearDesc

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

private theorem surjective_toModule_ι (n : ℕ) :
    Function.Surjective (DirectSum.toModule R ℕ (periodicCyclicCohomology R A M n)
      fun k ↦ (periodicCyclicCohomology.ι R A M n k).hom) := fun x ↦ by
  obtain ⟨k, y, rfl⟩ := exists_ι_eq x
  exact ⟨DirectSum.lof R ℕ _ k y, by simp⟩

private theorem exists_toModule_ι_and_apply {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ i j (h : i ≤ j),
      g j ∘ₗ (cyclicTotalHomologyPeriodicTransition R A M n h).hom = g i)
    (z : DirectSum ℕ fun k ↦ (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    ∃ (K : ℕ) (y : (cyclicTotalComplex R A M).homology (n + 2 * K)),
      DirectSum.toModule R ℕ (periodicCyclicCohomology R A M n)
          (fun k ↦ (periodicCyclicCohomology.ι R A M n k).hom) z =
        periodicCyclicCohomology.ι R A M n K y ∧
      DirectSum.toModule R ℕ N g z = g K y := by
  refine DirectSum.induction_on z ⟨0, 0, by simp, by simp⟩
    (fun k x ↦ ⟨k, x, by rw [← DirectSum.lof_eq_of R, DirectSum.toModule_lof],
      by rw [← DirectSum.lof_eq_of R, DirectSum.toModule_lof]⟩) ?_
  rintro p q ⟨i, x, hx₁, hx₂⟩ ⟨j, y, hy₁, hy₂⟩
  refine ⟨max i j,
    cyclicTotalHomologyPeriodicTransition R A M n (le_max_left i j) x +
      cyclicTotalHomologyPeriodicTransition R A M n (le_max_right i j) y, ?_, ?_⟩
  · rw [map_add, map_add, hx₁, hy₁, cyclicTotalHomologyPeriodicTransition_ι_apply,
      cyclicTotalHomologyPeriodicTransition_ι_apply]
  · have hgx := LinearMap.congr_fun (hg i (max i j) (le_max_left i j)) x
    have hgy := LinearMap.congr_fun (hg j (max i j) (le_max_right i j)) y
    simp only [LinearMap.comp_apply] at hgx hgy
    rw [map_add, map_add, hx₂, hy₂, hgx, hgy]

/-- Universe-polymorphic descent of a compatible family of `R`-linear maps out of the stages
`H^(n+2k)(Tot)` to `periodicCyclicCohomology R A M n`. -/
private def linearDesc {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ i j (h : i ≤ j),
      g j ∘ₗ (cyclicTotalHomologyPeriodicTransition R A M n h).hom = g i) :
    periodicCyclicCohomology R A M n →ₗ[R] N :=
  (DirectSum.toModule R ℕ (periodicCyclicCohomology R A M n)
      fun k ↦ (periodicCyclicCohomology.ι R A M n k).hom).liftOfSurjective
    (surjective_toModule_ι n)
    ⟨DirectSum.toModule R ℕ N g, fun z hz ↦ by
      rw [LinearMap.mem_ker] at hz ⊢
      obtain ⟨K, y, hy₁, hy₂⟩ := exists_toModule_ι_and_apply g hg z
      rw [hz, eq_comm, ι_eq_zero_iff] at hy₁
      obtain ⟨J, hKJ, hJ⟩ := hy₁
      have hgJ := LinearMap.congr_fun (hg K J hKJ) y
      simp only [LinearMap.comp_apply] at hgJ
      rw [hy₂, ← hgJ, hJ, map_zero]⟩

private theorem linearDesc_ι {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ i j (h : i ≤ j),
      g j ∘ₗ (cyclicTotalHomologyPeriodicTransition R A M n h).hom = g i)
    (k : ℕ) (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    linearDesc g hg (periodicCyclicCohomology.ι R A M n k y) = g k y := by
  let z := DirectSum.lof R ℕ (fun i ↦ (cyclicTotalComplex R A M).homology (n + 2 * i)) k y
  have h1 : periodicCyclicCohomology.ι R A M n k y =
      DirectSum.toModule R ℕ (periodicCyclicCohomology R A M n)
        (fun j ↦ (periodicCyclicCohomology.ι R A M n j).hom) z := by
    simp [z]
  rw [h1, linearDesc, LinearMap.equivOfSurjective_apply (m := z)]
  simp [z]

private theorem linearMap_ext {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    {f₁ f₂ : periodicCyclicCohomology R A M n →ₗ[R] N}
    (h : ∀ k y, f₁ (periodicCyclicCohomology.ι R A M n k y) =
      f₂ (periodicCyclicCohomology.ι R A M n k y)) :
    f₁ = f₂ := by
  ext x
  obtain ⟨k, y, rfl⟩ := exists_ι_eq x
  exact h k y

end LinearDesc

section NonUnital

variable {R A : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The `R`-linear map `HP^n(A; M) → HP^n(Matrix ι ι A; M)` on periodic cyclic cohomology induced
by `cyclicTotalHomologyMatrixExtension` on the stages `H^(n+2k)(Tot)`. -/
def matrixExtension (M : Type*) [AddCommGroup M] [Module R M] (ι : Type*) [Fintype ι] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  linearDesc
    (fun k ↦ (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun i j h ↦ by
      rw [LinearMap.comp_assoc,
        cyclicTotalHomologyMatrixExtension_comp_cyclicTotalHomologyPeriodicTransition M ι n h,
        ← LinearMap.comp_assoc, ← ModuleCat.hom_comp, cyclicTotalHomologyPeriodicTransition_ι]

/-- On the `k`-th stage `H^(n+2k)(Tot)`, `periodicCyclicCohomology.matrixExtension` is
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem matrixExtension_ι {M : Type*} [AddCommGroup M] [Module R M] {κ : Type*} [Fintype κ]
    (n k : ℕ) (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M κ n (periodicCyclicCohomology.ι R A M n k y) =
      periodicCyclicCohomology.ι R (Matrix κ κ A) M n k
        (cyclicTotalHomologyMatrixExtension M κ (n + 2 * k) y) :=
  linearDesc_ι _ _ k y

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

private def matrixExtensionInv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R (Matrix ι ι A) M n →ₗ[R] periodicCyclicCohomology R A M n :=
  linearDesc
    (fun k ↦ (periodicCyclicCohomology.ι R A M n k).hom ∘ₗ
      (cyclicTotalHomologyMatrixExtensionEquiv R A M ι (n + 2 * k)).symm.toLinearMap)
    fun i j h ↦ by
      have hcomm :
          (cyclicTotalHomologyMatrixExtensionEquiv R A M ι (n + 2 * j)).symm.toLinearMap ∘ₗ
            (cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h).hom =
          (cyclicTotalHomologyPeriodicTransition R A M n h).hom ∘ₗ
            (cyclicTotalHomologyMatrixExtensionEquiv R A M ι (n + 2 * i)).symm.toLinearMap := by
        rw [LinearEquiv.toLinearMap_symm_comp_eq, ← LinearMap.comp_assoc]
        have h1 := cyclicTotalHomologyMatrixExtension_comp_cyclicTotalHomologyPeriodicTransition
          (R := R) (A := A) M ι n h
        rw [← toLinearMap_cyclicTotalHomologyMatrixExtensionEquiv ι (n + 2 * j),
          ← toLinearMap_cyclicTotalHomologyMatrixExtensionEquiv ι (n + 2 * i)] at h1
        rw [h1, LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
          LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
      rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc, ← ModuleCat.hom_comp,
        cyclicTotalHomologyPeriodicTransition_ι]

private theorem matrixExtensionInv_ι {κ : Type*} [Fintype κ] [Nonempty κ]
    (n k : ℕ) (y : (cyclicTotalComplex R (Matrix κ κ A) M).homology (n + 2 * k)) :
    matrixExtensionInv κ n (periodicCyclicCohomology.ι R (Matrix κ κ A) M n k y) =
      periodicCyclicCohomology.ι R A M n k
        ((cyclicTotalHomologyMatrixExtensionEquiv R A M κ (n + 2 * k)).symm y) :=
  linearDesc_ι _ _ k y

variable (R A M) in
/-- **Matrix Morita equivalence for periodic cyclic cohomology:** the linear equivalence
`HP^n(A; M) ≃ₗ[R] HP^n(Matrix ι ι A; M)` over any commutative ring `R`. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofLinearMap (matrixExtension M ι n) (matrixExtensionInv ι n)
    (linearMap_ext fun k y ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, matrixExtensionInv_ι, matrixExtension_ι,
        ← cyclicTotalHomologyMatrixExtensionEquiv_apply ι (n + 2 * k),
        LinearEquiv.apply_symm_apply])
    (linearMap_ext fun k y ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, matrixExtension_ι, matrixExtensionInv_ι,
        ← cyclicTotalHomologyMatrixExtensionEquiv_apply ι (n + 2 * k),
        LinearEquiv.symm_apply_apply])

/-- Applying `periodicCyclicCohomology.matrixExtensionEquiv` applies
`periodicCyclicCohomology.matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (x : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv R A M ι n x = matrixExtension M ι n x :=
  (rfl)

/-- The underlying linear map of `periodicCyclicCohomology.matrixExtensionEquiv` is
`periodicCyclicCohomology.matrixExtension`. -/
@[simp]
theorem toLinearMap_matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv R A M ι n).toLinearMap = matrixExtension M ι n :=
  (rfl)

/-- **Matrix Morita invariance of periodic cyclic cohomology.** Over every commutative ring `R`,
for any unital `R`-algebra `A`, `R`-module `M`, and nonempty finite index type `ι`,
`periodicCyclicCohomology.matrixExtension` is bijective in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  (matrixExtensionEquiv R A M ι n).bijective

end Unital

section Rational

variable {R : Type*} [CommRing R] [Algebra ℚ R] {A : Type*} [Ring A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Over a `ℚ`-algebra, `periodicCyclicCohomology.matrixExtension` commutes with the normalized
maps `fromCyclicCohomology : HC^(n+2k) → HP^n`. -/
@[simp]
theorem matrixExtension_fromCyclicCohomology {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n k : ℕ) (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M κ n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix κ κ A) M n k
        (cyclicCohomology.matrixExtension M κ (n + 2 * k) c) := by
  rw [fromCyclicCohomology_def, fromCyclicCohomology_def]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, matrixExtension_ι, homologyMap_cyclicCochainComplexToTotal_matrixExtension]

end Rational

end periodicCyclicCohomology

end TauCeti
