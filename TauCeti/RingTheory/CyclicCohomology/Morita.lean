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

Let `A` be a unital algebra over a commutative ring `R`, `M` an `R`-module of coefficients, and `ι`
a nonempty finite index type. The generalized matrix trace `φ ↦ φ#Tr`
(`TauCeti.matrixCochainExtension`) commutes with the cyclic operator `λ`, the cyclic norm `N`, the
Hochschild coboundary `b`, and the bar coboundary `b'`, and therefore induces a map of Connes'
cyclic bicomplexes from `A` to `Matrix ι ι A`. On the total complex this gives an `R`-linear map
`cyclicTotalHomologyMatrixExtension : Hⁿ(Tot(A)) → Hⁿ(Tot(Matrix ι ι A))` compatible with all three
maps `I`, `B`, and `S` of the SBI exact sequence.

Since matrix extension is already an isomorphism on Hochschild cohomology in every degree
(`TauCeti.hochschildCohomology.bijective_matrixExtension`), the SBI long exact sequence of the
bicomplex (`TauCeti.RingTheory.CyclicCohomology.ExactSequence`) transfers bijectivity to the total
cyclic cohomology `Hⁿ(Tot)` over **every** commutative ring `R`:
* in degree `0`, `I : H⁰(Tot) → HH⁰` is an isomorphism;
* in degree `1`, `0 → H¹(Tot) →I HH¹ →B H⁰(Tot)` is exact, so the left-exact four lemma gives
  bijectivity on `H¹(Tot)`;
* from degrees `m` and `m + 1` to degree `m + 2`, the five lemma on
  `HHᵐ⁺¹ →B Hᵐ(Tot) →S Hᵐ⁺²(Tot) →I HHᵐ⁺² →B Hᵐ⁺¹(Tot)` completes the induction.

Passing to direct limits along `S` yields matrix Morita invariance of periodic cyclic cohomology
`HPⁿ(A; M) ≃ₗ[R] HPⁿ(Matrix ι ι A; M)` over every commutative ring `R`. Whenever `1, 2, …, n` are
units in `R` — in particular in degrees `0` and `1` over any commutative ring, and in all degrees
when `R` is a `ℚ`-algebra — the inclusion of cyclic cochains into column zero of the bicomplex is a
quasi-isomorphism in degree `n` (`TauCeti.quasiIsoAt_cyclicCochainComplexToTotal`), yielding matrix
Morita invariance `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` on Connes' cyclic cohomology, with inverse
given by corner restriction (`cyclicCohomology.cornerRestriction`) at any index `r : ι`.

At the cochain level, `matrixCochainExtension` and `cornerCochainRestriction` also commute
identically with Connes' double-face operator `cochainPeriodicity`, so
`cyclicCohomology.matrixExtension` and `cyclicCohomology.cornerRestriction` commute with Connes'
periodicity operator `cyclicCohomology.periodicity`.

## Main definitions

* `TauCeti.cornerCyclicCochainRestriction`: restriction of cyclic cochains on `Matrix ι ι A` to the
  `(r, r)` diagonal corner.
* `TauCeti.cyclicCohomology.cornerRestriction`: corner restriction on cyclic cohomology.
* `TauCeti.matrixCyclicTotalCochainExtension`, `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`: matrix extension on total cochains and total
  cyclic cohomology, and the resulting linear equivalence.
* `TauCeti.cyclicCohomology.matrixExtensionEquiv`: the matrix Morita linear equivalence
  `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a `ℚ`-algebra.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`: matrix extension on periodic cyclic
  cohomology and the resulting linear equivalence over any commutative ring.

## Main results

* `TauCeti.matrixCochainExtension_cochainPeriodicity`,
  `TauCeti.cyclicCohomology.matrixExtension_periodicity`: matrix extension commutes with Connes'
  periodicity operator `S`.
* `TauCeti.cyclicCohomology.injective_matrixExtension`: matrix extension on `HCⁿ` is injective over
  every commutative ring.
* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix extension on `Hⁿ(Tot)` is bijective
  over every commutative ring.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix extension on `HCⁿ` is bijective when
  `1, …, n` are units in `R`, and in all degrees over a `ℚ`-algebra.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix extension on `HPⁿ` is
  bijective over every commutative ring.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, Corollary 20.
* J.-L. Loday, *Cyclic Homology*, §§1.2, 2.2, 5.1.
-/

public section

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace TauCeti

/-- If `g ∘ f = k ∘ h` with `g`, `h`, and `k` bijective, then `f` is bijective. -/
private theorem bijective_of_comp_bijective {α β γ δ : Type*} {f : α → β} {g : β → γ}
    {h : α → δ} {k : δ → γ} (hcomm : ∀ x, g (f x) = k (h x))
    (hg : Function.Bijective g) (hh : Function.Bijective h) (hk : Function.Bijective k) :
    Function.Bijective f := by
  refine ⟨fun x y hxy ↦ hh.1 (hk.1 ?_), fun y ↦ ?_⟩
  · rw [← hcomm x, ← hcomm y, hxy]
  · obtain ⟨d, hd⟩ := hk.2 (g y)
    obtain ⟨x, rfl⟩ := hh.2 d
    exact ⟨x, hg.1 ((hcomm x).trans hd)⟩

/-! ### Cochain-level periodicity compatibility and cyclic corner restriction -/

section CochainLevel

variable {R A M ι : Type*}

section Periodicity

variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M]

private theorem cochainPeriodicity_eq_sum_coface {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cochainPeriodicity R A M n φ =
      ∑ j : Fin (n + 1), ∑ r ∈ Finset.Iic j,
        (-1 : ℤ) ^ ((j : ℕ) - r) •
          hochschildCoface R A M j.succ.castSucc (hochschildCoface R A M r.castSucc φ) := by
  ext a
  simp [cochainPeriodicity_apply]

/-- Matrix extension commutes with Connes' unaveraged periodicity operator `S₀` on multilinear
cochains: `(S₀ φ)#Tr = S₀ (φ#Tr)`. -/
theorem matrixCochainExtension_cochainPeriodicity (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainExtension ι (n + 2) (cochainPeriodicity R A M n φ) =
      cochainPeriodicity R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  rw [cochainPeriodicity_eq_sum_coface φ, map_sum]
  simp_rw [map_sum, map_zsmul, matrixCochainExtension_hochschildCoface]
  exact (cochainPeriodicity_eq_sum_coface (matrixCochainExtension ι n φ)).symm

/-- Corner restriction commutes with each Hochschild coface. -/
theorem cornerCochainRestriction_hochschildCoface [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (i : Fin (n + 2))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    cornerCochainRestriction r (n + 1) (hochschildCoface R (Matrix ι ι A) M i φ) =
      hochschildCoface R A M i (cornerCochainRestriction r n φ) := by
  let cornerHom : A →ₙₐ[R] Matrix ι ι A :=
    { Matrix.singleLinearMap R r r with
      map_zero' := (Matrix.singleLinearMap R r r).map_zero
      map_mul' := fun x y ↦ (Matrix.single_mul_single_same x r r r y).symm }
  ext x
  simp only [cornerCochainRestriction_apply, hochschildCoface_apply]
  exact congrArg φ (comp_hochschildFace cornerHom i x).symm

/-- Corner restriction commutes with Connes' unaveraged periodicity operator `S₀`. -/
theorem cornerCochainRestriction_cochainPeriodicity [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    cornerCochainRestriction r (n + 2) (cochainPeriodicity R (Matrix ι ι A) M n φ) =
      cochainPeriodicity R A M n (cornerCochainRestriction r n φ) := by
  rw [cochainPeriodicity_eq_sum_coface φ, map_sum]
  simp_rw [map_sum, map_zsmul, cornerCochainRestriction_hochschildCoface]
  exact (cochainPeriodicity_eq_sum_coface (cornerCochainRestriction r n φ)).symm

end Periodicity

section CyclicCorner

variable [Semiring R] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [DecidableEq ι]

/-- Restrict a cyclic `n`-cochain on `Matrix ι ι A` to the `(r, r)` diagonal corner. -/
def cornerCyclicCochainRestriction [AddCommMonoid A] [Module R A] (r : ι) (n : ℕ) :
    cyclicCochains R (Matrix ι ι A) M n →ₗ[R] cyclicCochains R A M n :=
  cyclicCochainsMap M (Matrix.singleLinearMap R r r) n

/-- The underlying cochain of `cornerCyclicCochainRestriction` is `cornerCochainRestriction`. -/
@[simp]
theorem coe_cornerCyclicCochainRestriction_apply [AddCommMonoid A] [Module R A] (r : ι) (n : ℕ)
    (φ : cyclicCochains R (Matrix ι ι A) M n) :
    (cornerCyclicCochainRestriction r n φ :
        MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) =
      cornerCochainRestriction r n φ.1 := by
  ext x
  simp [cornerCyclicCochainRestriction]

/-- Restricting the matrix extension of a cyclic cochain to any diagonal corner recovers the
original cyclic cochain. -/
@[simp]
theorem cornerCyclicCochainRestriction_matrixCyclicCochainExtension [AddCommMonoid A] [Module R A]
    [Fintype ι] (r : ι) (n : ℕ) (φ : cyclicCochains R A M n) :
    cornerCyclicCochainRestriction r n (matrixCyclicCochainExtension ι n φ) = φ :=
  Subtype.ext (by simp)

section Coboundary

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [Fintype ι] {n : ℕ}

/-- Corner restriction of cyclic cochains commutes with the Hochschild coboundary. -/
theorem cyclicHochschildCoboundary_cornerCyclicCochainRestriction (r : ι)
    (φ : cyclicCochains R (Matrix ι ι A) M n) :
    cyclicHochschildCoboundary R A M n (cornerCyclicCochainRestriction r n φ) =
      cornerCyclicCochainRestriction r (n + 1)
        (cyclicHochschildCoboundary R (Matrix ι ι A) M n φ) :=
  Subtype.ext (by simp [cornerCochainRestriction_hochschildCoboundary])

/-- Corner restriction maps cyclic cocycles to cyclic cocycles. -/
theorem cornerCyclicCochainRestriction_mem_cyclicCocycles (r : ι)
    {φ : cyclicCochains R (Matrix ι ι A) M n}
    (hφ : φ ∈ cyclicCocycles R (Matrix ι ι A) M n) :
    cornerCyclicCochainRestriction r n φ ∈ cyclicCocycles R A M n := by
  rw [mem_cyclicCocycles_iff] at hφ ⊢
  rw [coe_cornerCyclicCochainRestriction_apply, ← cornerCochainRestriction_hochschildCoboundary,
    hφ, map_zero]

/-- Corner restriction maps cyclic coboundaries to cyclic coboundaries. -/
theorem cornerCyclicCochainRestriction_mem_cyclicCoboundaries (r : ι)
    {φ : cyclicCochains R (Matrix ι ι A) M n}
    (hφ : φ ∈ cyclicCoboundaries R (Matrix ι ι A) M n) :
    cornerCyclicCochainRestriction r n φ ∈ cyclicCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ d =>
    obtain ⟨ψ, rfl⟩ := (mem_cyclicCoboundaries_succ_iff _ _ _).1 hφ
    exact (mem_cyclicCoboundaries_succ_iff _ _ _).2
      ⟨cornerCyclicCochainRestriction r d ψ,
        cyclicHochschildCoboundary_cornerCyclicCochainRestriction r ψ⟩

end Coboundary

end CyclicCorner

section CyclicCocyclesPeriodicity

variable [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] {n : ℕ}

/-- Matrix extension of cyclic cocycles commutes with `cyclicCocyclesPeriodicity`. -/
theorem matrixCyclicCochainExtension_cyclicCocyclesPeriodicity [Fintype ι]
    (φ : cyclicCocycles R A M n) :
    matrixCyclicCochainExtension ι (n + 2) (cyclicCocyclesPeriodicity R A M n φ).1 =
      (cyclicCocyclesPeriodicity R (Matrix ι ι A) M n
        ⟨matrixCyclicCochainExtension ι n φ.1,
          matrixCyclicCochainExtension_mem_cyclicCocycles φ.2⟩).1 :=
  Subtype.ext (by simp [matrixCochainExtension_cochainPeriodicity])

/-- Corner restriction of cyclic cocycles commutes with `cyclicCocyclesPeriodicity`. -/
theorem cornerCyclicCochainRestriction_cyclicCocyclesPeriodicity [Fintype ι] [DecidableEq ι]
    (r : ι) (φ : cyclicCocycles R (Matrix ι ι A) M n) :
    cornerCyclicCochainRestriction r (n + 2)
        (cyclicCocyclesPeriodicity R (Matrix ι ι A) M n φ).1 =
      (cyclicCocyclesPeriodicity R A M n
        ⟨cornerCyclicCochainRestriction r n φ.1,
          cornerCyclicCochainRestriction_mem_cyclicCocycles r φ.2⟩).1 :=
  Subtype.ext (by simp [cornerCochainRestriction_cochainPeriodicity])

end CyclicCocyclesPeriodicity

end CochainLevel

/-! ### Matrix extension on the cyclic bicomplex and total cyclic cohomology -/

section Bicomplex

variable {R A M : Type*}

section Horizontal

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M]

/-- Matrix extension commutes with the horizontal differentials of Connes' cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_cyclicOperator]
  · simp [hp, matrixCochainExtension_cyclicNorm]

end Horizontal

section Vertical

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension commutes with the vertical differentials of Connes' cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_hochschildCoboundary]
  · simp [hp, matrixCochainExtension_barCoboundary]

end Vertical

section TotalCochains

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M] [Module R M]

/-- Matrix extension on total cochains of Connes' cyclic bicomplex, applying
`matrixCochainExtension ι q` to the component in row `q`. -/
def matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  LinearMap.codRestrict (cyclicTotalCochains R (Matrix ι ι A) M m)
    (LinearMap.pi fun q ↦
      matrixCochainExtension ι q ∘ₗ LinearMap.proj q ∘ₗ (cyclicTotalCochains R A M m).subtype)
    fun x ↦ mem_cyclicTotalCochains_iff.2 fun q hq ↦ by
      simp [coe_cyclicTotalCochains_apply_of_lt x hq]

/-- In row `q`, `matrixCyclicTotalCochainExtension` applies `matrixCochainExtension ι q`. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply {ι : Type*} [Fintype ι] (m : ℕ)
    (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixCyclicTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) :=
  (rfl)

/-- Matrix extension on total cochains is injective for every nonempty finite index type. -/
theorem matrixCyclicTotalCochainExtension_injective (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    Function.Injective
      (matrixCyclicTotalCochainExtension (R := R) (A := A) (M := M) ι m) := fun x y h ↦
  Subtype.ext <| funext fun q ↦ matrixCochainExtension_injective ι q <| by
    simpa only [coe_matrixCyclicTotalCochainExtension_apply] using
      congrFun (congrArg Subtype.val h) q

/-- Matrix extension on total cochains commutes with the bicomplex periodicity shift. -/
theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity {ι : Type*} [Fintype ι] (m : ℕ)
    (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) := by
  apply Subtype.ext
  funext q
  simp

/-- Projecting onto column zero commutes with matrix extension on total cochains. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension {ι : Type*} [Fintype ι] (m : ℕ)
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by
  simp

end TotalCochains

section TotalInclusion

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M]

/-- Including cyclic cochains into column zero commutes with matrix extension. -/
theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal {ι : Type*} [Fintype ι] (m : ℕ)
    (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  apply Subtype.ext
  funext q
  rcases eq_or_ne q m with rfl | hq
  · simp
  · simp [hq]

end TotalInclusion

section TotalDifferential

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension on total cochains commutes with the total differential `D = d_h + d_v`. -/
theorem cyclicTotalDifferential_matrixCyclicTotalCochainExtension {ι : Type*} [Fintype ι] (m : ℕ)
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) := by
  apply Subtype.ext
  funext q
  cases q with
  | zero => simp [matrixCochainExtension_cyclicBicomplexHorizontal]
  | succ q =>
    simp [matrixCochainExtension_cyclicBicomplexVertical,
      matrixCochainExtension_cyclicBicomplexHorizontal]

end TotalDifferential

section TotalHomology

variable [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension maps total cocycles to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker (ι : Type*) [Fintype ι] {n : ℕ}
    {x : cyclicTotalCochains R A M n}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M n)) :
    matrixCyclicTotalCochainExtension ι n x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hx, map_zero]

private theorem cyclicTotalHomologyMk_matrixCyclicTotalCochainExtension_eq_zero
    {ι : Type*} [Fintype ι] {n : ℕ} (x : LinearMap.ker (cyclicTotalDifferential R A M n))
    (hx : cyclicTotalHomologyMk R A M n x = 0) :
    cyclicTotalHomologyMk R (Matrix ι ι A) M n
      ⟨matrixCyclicTotalCochainExtension ι n x.1,
        matrixCyclicTotalCochainExtension_mem_ker ι x.2⟩ = 0 := by
  cases n with
  | zero =>
    obtain rfl := (cyclicTotalHomologyMk_zero_eq_zero_iff x).1 hx
    exact (cyclicTotalHomologyMk_zero_eq_zero_iff _).2 (Subtype.ext (map_zero _))
  | succ m =>
    obtain ⟨w, hw⟩ := (cyclicTotalHomologyMk_succ_eq_zero_iff x).1 hx
    refine (cyclicTotalHomologyMk_succ_eq_zero_iff _).2
      ⟨matrixCyclicTotalCochainExtension ι m w, ?_⟩
    rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hw]

private def cyclicTotalHomologyDesc {N : Type*} [AddCommGroup N] [Module R N] (n : ℕ)
    (f : LinearMap.ker (cyclicTotalDifferential R A M n) →ₗ[R] N)
    (hf : ∀ x : LinearMap.ker (cyclicTotalDifferential R A M n),
      cyclicTotalHomologyMk R A M n x = 0 → f x = 0) :
    (cyclicTotalComplex R A M).homology n →ₗ[R] N :=
  (cyclicTotalHomologyMk R A M n).liftOfSurjective (cyclicTotalHomologyMk_surjective n)
    ⟨f, fun x hx ↦ LinearMap.mem_ker.2 (hf x (LinearMap.mem_ker.1 hx))⟩

private theorem cyclicTotalHomologyDesc_mk {N : Type*} [AddCommGroup N] [Module R N] (n : ℕ)
    (f : LinearMap.ker (cyclicTotalDifferential R A M n) →ₗ[R] N)
    (hf : ∀ x : LinearMap.ker (cyclicTotalDifferential R A M n),
      cyclicTotalHomologyMk R A M n x = 0 → f x = 0)
    (x : LinearMap.ker (cyclicTotalDifferential R A M n)) :
    cyclicTotalHomologyDesc n f hf (cyclicTotalHomologyMk R A M n x) = f x :=
  LinearMap.equivOfSurjective_apply _ _

variable (M) in
/-- **Matrix extension on the cohomology of the total cyclic bicomplex**, sending the class of a
total cocycle `x` to the class of its rowwise matrix extension. -/
def cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    (cyclicTotalComplex R A M).homology n →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  cyclicTotalHomologyDesc n
    (cyclicTotalHomologyMk R (Matrix ι ι A) M n ∘ₗ
      (matrixCyclicTotalCochainExtension ι n).restrict
        fun _ ↦ matrixCyclicTotalCochainExtension_mem_ker ι)
    fun x hx ↦ cyclicTotalHomologyMk_matrixCyclicTotalCochainExtension_eq_zero x hx

/-- `cyclicTotalHomologyMatrixExtension` sends `[x]` to the class of its rowwise matrix
extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk {ι : Type*} [Fintype ι] {n : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M n)) :
    cyclicTotalHomologyMatrixExtension M ι n (cyclicTotalHomologyMk R A M n x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixCyclicTotalCochainExtension ι n x.1,
          matrixCyclicTotalCochainExtension_mem_ker ι x.2⟩ :=
  cyclicTotalHomologyDesc_mk n _ _ x

/-- Projection `I : Hⁿ(Tot) → HHⁿ` onto column zero commutes with matrix extension. -/
@[simp]
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension
    {ι : Type*} [Fintype ι] (n : ℕ) (c : (cyclicTotalComplex R A M).homology n) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) n
        (cyclicTotalHomologyMatrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  simp only [cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk]
  congr 1

/-- The bicomplex periodicity map `S : Hᵐ(Tot) → Hᵐ⁺²(Tot)` commutes with matrix extension. -/
@[simp]
theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension {ι : Type*} [Fintype ι]
    (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      cyclicTotalHomologyMatrixExtension M ι (m + 2)
        (cyclicTotalHomologyPeriodicity R A M m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity m x.1).symm

/-- Every transition map `S^(j-i) : H^(n+2i)(Tot) → H^(n+2j)(Tot)` of the periodic bicomplex system
commutes with matrix extension. -/
@[simp]
theorem cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension {ι : Type*}
    [Fintype ι] {n i j : ℕ} (h : i ≤ j) (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) c) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h c) := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hij
        (Nat.le_add_right j 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ModuleCat.comp_apply, ModuleCat.comp_apply, cyclicTotalHomologyPeriodicTransition_succ,
      cyclicTotalHomologyPeriodicTransition_succ, ih]
    exact cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension (n + 2 * j) _

end TotalHomology

section UnitalSBI

variable [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Connes' operator `B : HHⁿ⁺¹ → HCⁿ` commutes with matrix extension. -/
@[simp]
theorem hochschildCohomology.connesB_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (c : hochschildCohomology R A M (n + 1)) :
    hochschildCohomology.connesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) =
      cyclicCohomology.matrixExtension M ι n (hochschildCohomology.connesB R A M n c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (n + 1) c
  simp only [hochschildCohomology.matrixExtension_mk, hochschildCohomology.connesB_mk,
    cyclicCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (Subtype.ext (by simp [matrixCochainExtension_connesB]))

/-- The inclusion `HCⁿ → Hⁿ(Tot)` of cyclic cochains into column zero commutes with matrix
extension. -/
@[simp]
theorem homologyMap_cyclicCochainComplexToTotal_matrixExtension {ι : Type*} [Fintype ι]
    [DecidableEq ι] (n : ℕ) (c : cyclicCohomology R A M n) :
    HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n
        (cyclicCohomology.matrixExtension M ι n c) =
      cyclicTotalHomologyMatrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M n c
  simp only [cyclicCohomology.matrixExtension_mk, homologyMap_cyclicCochainComplexToTotal_mk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal n φ.1).symm

/-- The connecting map `B : HHᵐ⁺¹ → Hᵐ(Tot)` of the bicomplex SBI sequence commutes with matrix
extension. -/
@[simp]
theorem cyclicTotalHomologyConnesB_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (c : hochschildCohomology R A M (m + 1)) :
    cyclicTotalHomologyConnesB R (Matrix ι ι A) M m
        (hochschildCohomology.matrixExtension M ι (m + 1) c) =
      cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyConnesB R A M m c) := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.comp_apply,
    ModuleCat.comp_apply, hochschildCohomology.connesB_matrixExtension,
    homologyMap_cyclicCochainComplexToTotal_matrixExtension]

/-- **Matrix Morita invariance of total cyclic cohomology.** For a unital algebra `A` over any
commutative ring `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`,
`cyclicTotalHomologyMatrixExtension` is bijective in every degree `n`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  classical
  have h0 : Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 0) :=
    bijective_of_comp_bijective
      (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension 0)
      ((ConcreteCategory.isIso_iff_bijective _).1
        (isIso_homologyMap_cyclicTotalComplexToHochschild_zero R (Matrix ι ι A) M))
      ((ConcreteCategory.isIso_iff_bijective _).1
        (isIso_homologyMap_cyclicTotalComplexToHochschild_zero R A M))
      (hochschildCohomology.bijective_matrixExtension ι 0)
  have h1 : Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 1) :=
    LinearMap.bijective_of_bijective_of_injective_of_left_exact
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 1).hom
      (cyclicTotalHomologyConnesB R A M 0).hom
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 1).hom
      (cyclicTotalHomologyConnesB R (Matrix ι ι A) M 0).hom
      (cyclicTotalHomologyMatrixExtension M ι 1)
      (hochschildCohomology.matrixExtension M ι 1)
      (cyclicTotalHomologyMatrixExtension M ι 0)
      (LinearMap.ext <|
        homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension 1)
      (LinearMap.ext <| cyclicTotalHomologyConnesB_matrixExtension 0)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
      (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
      (hochschildCohomology.bijective_matrixExtension ι 1) h0.1
      injective_homologyMap_cyclicTotalComplexToHochschild_one
      injective_homologyMap_cyclicTotalComplexToHochschild_one
  have hpair : ∀ k,
      Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι k) ∧
        Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι (k + 1)) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
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
        (LinearMap.ext <| cyclicTotalHomologyConnesB_matrixExtension k)
        (LinearMap.ext <| cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension k)
        (LinearMap.ext <|
          homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension (k + 2))
        (LinearMap.ext <| cyclicTotalHomologyConnesB_matrixExtension (k + 1))
        (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity k)
        (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M k)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (k + 1))
        (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity k)
        (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
          R (Matrix ι ι A) M k)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (k + 1))
        (hochschildCohomology.bijective_matrixExtension ι (k + 1)).2
        ih.1
        (hochschildCohomology.bijective_matrixExtension ι (k + 2))
        ih.2.1⟩
  exact (hpair n).1

variable (M) in
/-- **Matrix Morita equivalence for total cyclic cohomology** as an `R`-linear equivalence
`Hⁿ(Tot(A)) ≃ₗ[R] Hⁿ(Tot(Matrix ι ι A))`, valid over every commutative ring `R`. -/
def cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (cyclicTotalComplex R A M).homology n ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι n)
    (bijective_cyclicTotalHomologyMatrixExtension ι n)

/-- Applying `cyclicTotalHomologyMatrixExtensionEquiv` agrees with
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixExtensionEquiv M ι n c =
      cyclicTotalHomologyMatrixExtension M ι n c :=
  (rfl)

end UnitalSBI

end Bicomplex

/-! ### Matrix Morita invariance on cyclic cohomology -/

namespace cyclicCohomology

section GeneralRing

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

variable (M) in
/-- **Corner restriction on cyclic cohomology**, sending the class of a cyclic cocycle on
`Matrix ι ι A` to the class of its restriction to the `(r, r)` diagonal corner. -/
def cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    cyclicCohomology R (Matrix ι ι A) M n →ₗ[R] cyclicCohomology R A M n :=
  desc n
    (mk R A M n ∘ₗ (cornerCyclicCochainRestriction r n).restrict
      fun _ ↦ cornerCyclicCochainRestriction_mem_cyclicCocycles r)
    fun _ hφ ↦ (mk_eq_zero_iff R A M n _).2
      (cornerCyclicCochainRestriction_mem_cyclicCoboundaries r hφ)

/-- `cornerRestriction` sends `[φ]` to `[cornerCyclicCochainRestriction r n φ]`. -/
@[simp]
theorem cornerRestriction_mk {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}
    (φ : cyclicCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M r n (mk R (Matrix ι ι A) M n φ) =
      mk R A M n
        ⟨cornerCyclicCochainRestriction r n φ.1,
          cornerCyclicCochainRestriction_mem_cyclicCocycles r φ.2⟩ :=
  desc_mk _ _ _ φ

/-- Corner restriction is a left inverse to matrix extension on cyclic cohomology over every
commutative ring `R`. -/
@[simp]
theorem cornerRestriction_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : cyclicCohomology R A M n) :
    cornerRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, cornerRestriction_mk]
  congr 1
  exact Subtype.ext (cornerCyclicCochainRestriction_matrixCyclicCochainExtension r n φ.1)

/-- Matrix extension on cyclic cohomology is injective for every nonempty finite index type over
every commutative ring `R`. -/
theorem injective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (cornerRestriction_matrixExtension r n)

/-- The map `I : HCⁿ → HHⁿ` commutes with matrix extension. -/
@[simp]
theorem toHochschild_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    toHochschild R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n (toHochschild R A M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [matrixExtension_mk, toHochschild_mk, hochschildCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (by simp)

/-- The map `I : HCⁿ → HHⁿ` commutes with corner restriction. -/
@[simp]
theorem toHochschild_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    toHochschild R A M n (cornerRestriction M r n c) =
      hochschildCohomology.cornerRestriction M r n (toHochschild R (Matrix ι ι A) M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  simp only [cornerRestriction_mk, toHochschild_mk, hochschildCohomology.cornerRestriction_mk]
  congr 1
  exact Subtype.ext (by simp)

/-- **Matrix Morita invariance of cyclic cohomology in a degree with invertible row weights.** If
`q + 1` is invertible in `R` for every `q < n`, then `cyclicCohomology.matrixExtension` is
bijective in degree `n`. -/
theorem bijective_matrixExtension_of_isUnit (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_of_comp_bijective
    (homologyMap_cyclicCochainComplexToTotal_matrixExtension n)
    ((ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR)))
    ((ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR)))
    (bijective_cyclicTotalHomologyMatrixExtension ι n)

/-- Matrix extension on `HC⁰` is bijective over every commutative ring `R`. -/
theorem bijective_matrixExtension_zero (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 fun q hq ↦ absurd hq (Nat.not_lt_zero q)

/-- Matrix extension on `HC¹` is bijective over every commutative ring `R`. -/
theorem bijective_matrixExtension_one (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 1) :=
  bijective_matrixExtension_of_isUnit ι 1 fun q hq ↦ by
    obtain rfl : q = 0 := by omega
    simp

/-- When `q + 1` is invertible in `R` for every `q < n`, matrix extension is also a left inverse to
corner restriction on `HCⁿ`. -/
theorem matrixExtension_cornerRestriction_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1))
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M r n c) = c := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨x, rfl⟩ := (bijective_matrixExtension_of_isUnit ι n hR).2 c
  rw [cornerRestriction_matrixExtension]

end GeneralRing

section Rational

variable {R A M : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- **Compatibility of matrix extension with Connes' periodicity operator `S`.** Over a `ℚ`-algebra,
`matrixExtension` commutes with `cyclicCohomology.periodicity` in every degree. -/
@[simp]
theorem matrixExtension_periodicity (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    matrixExtension M ι (n + 2) (periodicity R A M n c) =
      periodicity R (Matrix ι ι A) M n (matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [periodicity_mk, matrixExtension_mk]
  congr 1
  exact Subtype.ext (matrixCyclicCochainExtension_cyclicCocyclesPeriodicity φ)

/-- Corner restriction on cyclic cohomology commutes with Connes' periodicity operator `S`. -/
@[simp]
theorem cornerRestriction_periodicity {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    cornerRestriction M r (n + 2) (periodicity R (Matrix ι ι A) M n c) =
      periodicity R A M n (cornerRestriction M r n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  simp only [periodicity_mk, cornerRestriction_mk]
  congr 1
  exact Subtype.ext (cornerCyclicCochainRestriction_cyclicCocyclesPeriodicity r φ)

/-- Over a `ℚ`-algebra, matrix extension is a left inverse to corner restriction on `HCⁿ`. -/
@[simp]
theorem matrixExtension_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M r n c) = c :=
  matrixExtension_cornerRestriction_of_isUnit r n
    (fun q _ ↦ by simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)) c

/-- **Matrix Morita invariance of cyclic cohomology.** For a unital algebra `A` over a commutative
`ℚ`-algebra `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`,
`cyclicCohomology.matrixExtension` is bijective in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦ by
    simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

variable (M) in
/-- **Matrix Morita equivalence for cyclic cohomology** as an `R`-linear equivalence
`HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a `ℚ`-algebra. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Applying `cyclicCohomology.matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` is corner restriction at any index
`r : ι`. -/
theorem matrixExtensionEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (r : ι) (n : ℕ) (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = cornerRestriction M r n c := by
  apply (matrixExtensionEquiv M ι n).injective
  rw [LinearEquiv.apply_symm_apply, matrixExtensionEquiv_apply, matrixExtension_cornerRestriction]

/-- Over a `ℚ`-algebra, corner restriction on cyclic cohomology is independent of the chosen
diagonal corner. -/
theorem cornerRestriction_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (r s : ι) (n : ℕ) :
    cornerRestriction (R := R) (A := A) M r n = cornerRestriction (R := R) (A := A) M s n := by
  have : Nonempty ι := ⟨r⟩
  refine LinearMap.ext fun c ↦ ?_
  rw [← matrixExtensionEquiv_symm_apply r n c, ← matrixExtensionEquiv_symm_apply s n c]

end Rational

end cyclicCohomology

/-! ### Matrix Morita invariance on periodic cyclic cohomology -/

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Two linear maps out of periodic cyclic cohomology agree once they agree on every stage `ι`. -/
@[ext]
theorem linearMap_ext {P : Type*} [AddCommGroup P] [Module R P] {n : ℕ}
    {f g : periodicCyclicCohomology R A M n →ₗ[R] P}
    (h : ∀ k, f ∘ₗ (ι R A M n k).hom = g ∘ₗ (ι R A M n k).hom) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨k, y, rfl⟩ := exists_ι_eq x
  exact LinearMap.congr_fun (h k) y

private theorem liftLinear_unique {P : Type*} [AddCommGroup P] [Module R P] {n : ℕ}
    {g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] P}
    (hg : ∀ {i j : ℕ} (h : i ≤ j) (y),
      g j (cyclicTotalHomologyPeriodicTransition R A M n h y) = g i y)
    {k₁ k₂ : ℕ} {y₁ : (cyclicTotalComplex R A M).homology (n + 2 * k₁)}
    {y₂ : (cyclicTotalComplex R A M).homology (n + 2 * k₂)}
    (h : ι R A M n k₁ y₁ = ι R A M n k₂ y₂) :
    g k₁ y₁ = g k₂ y₂ := by
  let z : (cyclicTotalComplex R A M).homology (n + 2 * max k₁ k₂) :=
    cyclicTotalHomologyPeriodicTransition R A M n (le_max_left k₁ k₂) y₁ -
      cyclicTotalHomologyPeriodicTransition R A M n (le_max_right k₁ k₂) y₂
  have hz : ι R A M n (max k₁ k₂) z = 0 := by
    simp only [z, map_sub, cyclicTotalHomologyPeriodicTransition_ι_apply, h, sub_self]
  obtain ⟨J, hJ, hzJ⟩ := (ι_eq_zero_iff z).1 hz
  have hsub : g k₁ y₁ - g k₂ y₂ = 0 := by
    rw [← hg (le_max_left k₁ k₂) y₁, ← hg (le_max_right k₁ k₂) y₂, ← map_sub,
      ← hg hJ z, hzJ, map_zero]
  exact sub_eq_zero.1 hsub

private def liftLinearFun {P : Type*} [AddCommGroup P] [Module R P] (n : ℕ)
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] P)
    (x : periodicCyclicCohomology R A M n) : P :=
  g (exists_ι_eq x).choose (exists_ι_eq x).choose_spec.choose

private theorem liftLinearFun_ι {P : Type*} [AddCommGroup P] [Module R P] (n : ℕ)
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] P)
    (hg : ∀ {i j : ℕ} (h : i ≤ j) (y),
      g j (cyclicTotalHomologyPeriodicTransition R A M n h y) = g i y)
    (k : ℕ) (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    liftLinearFun n g (ι R A M n k y) = g k y :=
  liftLinear_unique hg (exists_ι_eq (ι R A M n k y)).choose_spec.choose_spec

/-- Universe-polymorphic descent of a compatible family of linear maps out of the stages
`H^(n+2k)(Tot)` to `HPⁿ(A; M)`. -/
private def liftLinear {P : Type*} [AddCommGroup P] [Module R P] (n : ℕ)
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] P)
    (hg : ∀ {i j : ℕ} (h : i ≤ j) (y),
      g j (cyclicTotalHomologyPeriodicTransition R A M n h y) = g i y) :
    periodicCyclicCohomology R A M n →ₗ[R] P where
  toFun := liftLinearFun n g
  map_add' x₁ x₂ := by
    obtain ⟨k₁, y₁, rfl⟩ := exists_ι_eq x₁
    obtain ⟨k₂, y₂, rfl⟩ := exists_ι_eq x₂
    have hadd : ι R A M n k₁ y₁ + ι R A M n k₂ y₂ =
        ι R A M n (max k₁ k₂)
          (cyclicTotalHomologyPeriodicTransition R A M n (le_max_left k₁ k₂) y₁ +
            cyclicTotalHomologyPeriodicTransition R A M n (le_max_right k₁ k₂) y₂) := by
      simp [map_add]
    rw [hadd, liftLinearFun_ι n g hg, liftLinearFun_ι n g hg, liftLinearFun_ι n g hg,
      map_add, hg (le_max_left k₁ k₂), hg (le_max_right k₁ k₂)]
  map_smul' r x := by
    obtain ⟨k, y, rfl⟩ := exists_ι_eq x
    have hsmul : r • ι R A M n k y = ι R A M n k (r • y) :=
      ((ι R A M n k).hom.map_smul r y).symm
    rw [hsmul, liftLinearFun_ι n g hg, liftLinearFun_ι n g hg, map_smul, RingHom.id_apply]

private theorem liftLinear_ι {P : Type*} [AddCommGroup P] [Module R P] (n : ℕ)
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] P)
    (hg : ∀ {i j : ℕ} (h : i ≤ j) (y),
      g j (cyclicTotalHomologyPeriodicTransition R A M n h y) = g i y)
    (k : ℕ) (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    liftLinear n g hg (ι R A M n k y) = g k y :=
  liftLinearFun_ι n g hg k y

private theorem matrixExtension_compat {κ : Type*} [Fintype κ] {n i j : ℕ} (h : i ≤ j)
    (y : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    ((ι R (Matrix κ κ A) M n j).hom ∘ₗ cyclicTotalHomologyMatrixExtension M κ (n + 2 * j))
        (cyclicTotalHomologyPeriodicTransition R A M n h y) =
      ((ι R (Matrix κ κ A) M n i).hom ∘ₗ cyclicTotalHomologyMatrixExtension M κ (n + 2 * i)) y := by
  simp only [LinearMap.comp_apply]
  change ι R (Matrix κ κ A) M n j _ = ι R (Matrix κ κ A) M n i _
  rw [← cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension h y,
    cyclicTotalHomologyPeriodicTransition_ι_apply]

variable (M) in
/-- **Matrix extension on periodic cyclic cohomology**, induced stagewise by
`cyclicTotalHomologyMatrixExtension`. -/
def matrixExtension (κ : Type*) [Fintype κ] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix κ κ A) M n :=
  liftLinear n
    (fun k ↦ (ι R (Matrix κ κ A) M n k).hom ∘ₗ cyclicTotalHomologyMatrixExtension M κ (n + 2 * k))
    fun h y ↦ matrixExtension_compat h y

/-- On the `k`-th stage `H^(n+2k)(Tot)`, `periodicCyclicCohomology.matrixExtension` acts by
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem matrixExtension_ι {κ : Type*} [Fintype κ] (n k : ℕ)
    (y : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M κ n (ι R A M n k y) =
      ι R (Matrix κ κ A) M n k (cyclicTotalHomologyMatrixExtension M κ (n + 2 * k) y) := by
  rw [matrixExtension]
  exact liftLinear_ι n _ _ k y

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of periodic cyclic cohomology.** For a unital algebra `A` over any
commutative ring `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `κ`,
`periodicCyclicCohomology.matrixExtension` is bijective in every degree `n`. -/
theorem bijective_matrixExtension (κ : Type*) [Fintype κ] [Nonempty κ] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M κ n) := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨k, y, rfl⟩ := exists_ι_eq x
    rw [matrixExtension_ι, ι_eq_zero_iff] at hx
    obtain ⟨j, hkj, hj⟩ := hx
    rw [cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension] at hj
    exact (ι_eq_zero_iff y).2 ⟨j, hkj,
      (bijective_cyclicTotalHomologyMatrixExtension κ (n + 2 * j)).1 (hj.trans (map_zero _).symm)⟩
  · obtain ⟨k, z, rfl⟩ := exists_ι_eq x
    obtain ⟨y, rfl⟩ := (bijective_cyclicTotalHomologyMatrixExtension κ (n + 2 * k)).2 z
    exact ⟨ι R A M n k y, matrixExtension_ι n k y⟩

variable (M) in
/-- **Matrix Morita equivalence for periodic cyclic cohomology** as an `R`-linear equivalence
`HPⁿ(A; M) ≃ₗ[R] HPⁿ(Matrix κ κ A; M)`, valid over every commutative ring `R`. -/
def matrixExtensionEquiv (κ : Type*) [Fintype κ] [Nonempty κ] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix κ κ A) M n :=
  LinearEquiv.ofBijective (matrixExtension M κ n) (bijective_matrixExtension κ n)

/-- Applying `periodicCyclicCohomology.matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (κ : Type*) [Fintype κ] [Nonempty κ] (n : ℕ)
    (x : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv M κ n x = matrixExtension M κ n x :=
  (rfl)

/-- At stage zero (`k = 0`), `periodicCyclicCohomology.matrixExtension` commutes with
`fromCyclicCohomology`. -/
theorem matrixExtension_fromCyclicCohomology_zero [Algebra ℚ R] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixExtension M κ n (fromCyclicCohomology R A M n 0 c) =
      fromCyclicCohomology R (Matrix κ κ A) M n 0 (cyclicCohomology.matrixExtension M κ n c) := by
  rw [fromCyclicCohomology_zero, fromCyclicCohomology_zero, ModuleCat.comp_apply,
    ModuleCat.comp_apply, matrixExtension_ι,
    homologyMap_cyclicCochainComplexToTotal_matrixExtension]
  rfl

end Unital

end periodicCyclicCohomology

end TauCeti
