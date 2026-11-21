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

Generalized matrix trace `TauCeti.matrixCochainExtension` commutes with `S₀` and extends rowwise to
Connes' cyclic bicomplex (`TauCeti.matrixCyclicTotalCochainExtension`), inducing `R`-linear maps on
`Hⁿ(Tot)` and `HPⁿ` with `(r, r)` corner-restriction left inverses. For unital `A` and nonempty
finite `ι`, Hochschild Morita invariance and the five lemma yield Morita equivalences on `Hⁿ(Tot)`
and `HPⁿ` over every commutative ring `R`, and on `HCⁿ` whenever `∀ q < n, IsUnit ((q : R) + 1)`.

## Main definitions

* `TauCeti.matrixCyclicTotalCochainExtension`: rowwise generalized matrix trace on total cochains.
* `TauCeti.cyclicTotalHomologyMatrixExtension`, `TauCeti.cyclicTotalHomologyMatrixRestriction`,
  `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`: Morita maps and equivalence on `Hⁿ(Tot)`.
* `TauCeti.cyclicCohomology.matrixExtensionEquiv`: `HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)`.
* `TauCeti.periodicCyclicCohomology.matrixExtension`, `matrixRestriction`, `matrixExtensionEquiv`:
  Morita maps and equivalence on `HPⁿ`.

## Main results

* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix Morita invariance of `Hⁿ(Tot)`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of `HCⁿ(A; M)`.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of `HPⁿ`.

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
  ext1; simp [matrixCochainExtension_cyclicNorm, matrixCochainExtension_cochainPeriodicity]
/-- Matrix extension of cyclic cocycles commutes with `cyclicCocyclesPeriodicity`. -/
theorem matrixCyclicCochainExtension_cyclicCocyclesPeriodicity (φ : cyclicCocycles R A M n) :
    matrixCyclicCochainExtension ι (n + 2) (cyclicCocyclesPeriodicity R A M n φ).val =
      (cyclicCocyclesPeriodicity R (Matrix ι ι A) M n ⟨matrixCyclicCochainExtension ι n φ.val,
        matrixCyclicCochainExtension_mem_cyclicCocycles φ.property⟩).val := by
  ext1; simp [coe_cyclicCocyclesPeriodicity_apply, matrixCochainExtension_cochainPeriodicity]
end Assoc

/-! ### Matrix extension on the cyclic bicomplex -/

section Additive
variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M] (ι : Type*) [Fintype ι]

/-- Rowwise generalized matrix trace on total cochains of the cyclic bicomplex. -/
noncomputable def matrixCyclicTotalCochainExtension (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  cyclicTotalCochainsMapRows (fun q ↦ matrixCochainExtension ι q) m
/-- Row `q` of `matrixCyclicTotalCochainExtension ι m x` is `matrixCochainExtension ι q (x q)`. -/
@[simp] theorem coe_matrixCyclicTotalCochainExtension_apply {m : ℕ}
    (x : cyclicTotalCochains R A M m) (q : ℕ) : (matrixCyclicTotalCochainExtension ι m x).val q =
      matrixCochainExtension ι q (x.val q) := coe_cyclicTotalCochainsMapRows_apply _ x q
/-- Rowwise matrix extension commutes with the periodicity shift on total cochains. -/
@[simp] theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) :=
  Subtype.ext (funext fun q ↦ by simp)
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
@[simp] theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal {m : ℕ}
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
      matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) :=
  cyclicTotalDifferential_cyclicTotalCochainsMapRows _
    (matrixCochainExtension_cyclicBicomplexHorizontal ι)
    (matrixCochainExtension_cyclicBicomplexVertical ι) x
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
  exact congrArg (mk R (Matrix ι ι A) M n) (Subtype.ext <| Subtype.ext <| by
    simp [matrixCochainExtension_connesB])
/-- Matrix extension on cyclic cohomology over a `ℚ`-algebra commutes with `S`. -/
@[simp] theorem matrixExtension_periodicity [Algebra ℚ R] (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixExtension M ι (n + 2) (periodicity R A M n c) =
      periodicity R (Matrix ι ι A) M n (matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [periodicity_mk, matrixExtension_mk]
  exact congrArg (mk R (Matrix ι ι A) M (n + 2))
    (Subtype.ext (matrixCyclicCochainExtension_cyclicCocyclesPeriodicity ι n φ))
/-- Matrix extension on cyclic cohomology over a `ℚ`-algebra commutes with `S^(j - i)`. -/
@[simp] theorem matrixExtension_periodicTransition [Algebra ℚ R] (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : cyclicCohomology R A M (n + 2 * i)) :
    matrixExtension M ι (n + 2 * j) (periodicTransition R A M n h c) =
      periodicTransition R (Matrix ι ι A) M n h (matrixExtension M ι (n + 2 * i) c) :=
  LinearMap.congr_fun (stage_comp_periodicTransition_of_periodicity
    (fun k ↦ matrixExtension M ι (n + 2 * k))
    (fun k ↦ matrixExtension_periodicity (n + 2 * k)) i j h) c
end Unital
end cyclicCohomology

/-! ### Matrix Morita invariance of the total cyclic bicomplex -/

section NonUnital
variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]

/-- Rowwise matrix extension maps total cocycles to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker {m : ℕ} {x : cyclicTotalCochains R A M m}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M m)) :
    matrixCyclicTotalCochainExtension ι m x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m) :=
  cyclicTotalCochainsMapRows_mem_ker _ (matrixCochainExtension_cyclicBicomplexHorizontal ι)
    (matrixCochainExtension_cyclicBicomplexVertical ι) hx
variable (M ι) in
/-- Matrix extension on the cohomology `Hᵐ(Tot)` of the total cyclic bicomplex. -/
noncomputable def cyclicTotalHomologyMatrixExtension (m : ℕ) :
    (cyclicTotalComplex R A M).homology m →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  cyclicTotalHomologyMapRows (fun q ↦ matrixCochainExtension ι q)
    (matrixCochainExtension_cyclicBicomplexHorizontal ι)
    (matrixCochainExtension_cyclicBicomplexVertical ι) m
/-- `cyclicTotalHomologyMatrixExtension` maps `[x]` to the class of its rowwise matrix extension. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyMk R A M m x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M m
        ⟨matrixCyclicTotalCochainExtension ι m x.val,
          matrixCyclicTotalCochainExtension_mem_ker x.property⟩ :=
  cyclicTotalHomologyMapRows_cyclicTotalHomologyMk _ _ _ x
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
        (cyclicTotalHomologyMatrixExtension M ι m c) :=
  cyclicTotalHomologyMapRows_cyclicTotalHomologyPeriodicity _ _ _ m c
/-- Matrix extension on `Hᵐ(Tot)` commutes with the iterated transition maps `S^(j - i)`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicTransition
    (n : ℕ) {i j : ℕ} (h : i ≤ j) (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h c) =
      cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) c) :=
  LinearMap.congr_fun (periodicCyclicCohomology.stage_comp_transition_of_periodicity
    (fun k ↦ cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    (fun k ↦ cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity (n + 2 * k))
    i j h) c

omit [IsScalarTower R A A] [SMulCommClass R A A] [Fintype ι] in
private theorem matrixCochainRestriction_cyclicBicomplexHorizontal [DecidableEq ι] (r : ι)
    (p q : ℕ) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ Matrix ι ι A) M) :
    matrixCochainRestriction r q (cyclicBicomplexHorizontal R (Matrix ι ι A) M p q φ) =
      cyclicBicomplexHorizontal R A M p q (matrixCochainRestriction r q φ) := by
  ext a; rcases Nat.even_or_odd p with hp | hp <;>
    simp [hp, cyclicOperator_apply, cyclicNorm_apply, Function.comp_def]
private theorem matrixCochainRestriction_cyclicBicomplexVertical [DecidableEq ι] (r : ι)
    (p q : ℕ) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ Matrix ι ι A) M) :
    matrixCochainRestriction r (q + 1) (cyclicBicomplexVertical R (Matrix ι ι A) M p q φ) =
      cyclicBicomplexVertical R A M p q (matrixCochainRestriction r q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainRestriction_hochschildCoboundary]
  · simp [hp, barCoboundary_def, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul,
      matrixCochainRestriction_hochschildCoface]
/-- Rowwise corner restriction maps total cocycles on `Matrix ι ι A` to total cocycles on `A`. -/
theorem cyclicTotalCochainsMapRows_matrixCochainRestriction_mem_ker [DecidableEq ι] (r : ι) {m : ℕ}
    {x : cyclicTotalCochains R (Matrix ι ι A) M m}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m)) :
    cyclicTotalCochainsMapRows (fun q ↦ matrixCochainRestriction r q) m x ∈
      LinearMap.ker (cyclicTotalDifferential R A M m) :=
  cyclicTotalCochainsMapRows_mem_ker _ (matrixCochainRestriction_cyclicBicomplexHorizontal r)
    (matrixCochainRestriction_cyclicBicomplexVertical r) hx
variable (M) in
/-- Corner restriction on `Hᵐ(Tot)` along `x ↦ Matrix.single r r x`. -/
noncomputable def cyclicTotalHomologyMatrixRestriction [DecidableEq ι] (r : ι) (m : ℕ) :
    (cyclicTotalComplex R (Matrix ι ι A) M).homology m →ₗ[R]
      (cyclicTotalComplex R A M).homology m :=
  cyclicTotalHomologyMapRows (fun q ↦ matrixCochainRestriction r q)
    (matrixCochainRestriction_cyclicBicomplexHorizontal r)
    (matrixCochainRestriction_cyclicBicomplexVertical r) m
/-- `cyclicTotalHomologyMatrixRestriction` sends `[x]` to the class of its corner restriction. -/
@[simp] theorem cyclicTotalHomologyMatrixRestriction_cyclicTotalHomologyMk [DecidableEq ι] (r : ι)
    {m : ℕ} (x : LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m)) :
    cyclicTotalHomologyMatrixRestriction M r m (cyclicTotalHomologyMk R (Matrix ι ι A) M m x) =
      cyclicTotalHomologyMk R A M m
        ⟨cyclicTotalCochainsMapRows (fun q ↦ matrixCochainRestriction r q) m x.val,
          cyclicTotalCochainsMapRows_matrixCochainRestriction_mem_ker r x.property⟩ :=
  cyclicTotalHomologyMapRows_cyclicTotalHomologyMk _ _ _ x
/-- Corner restriction on `Hᵐ(Tot)` commutes with `S : Hᵐ(Tot) → Hᵐ⁺²(Tot)`. -/
@[simp] theorem cyclicTotalHomologyMatrixRestriction_cyclicTotalHomologyPeriodicity [DecidableEq ι]
    (r : ι) (m : ℕ) (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology m) :
    cyclicTotalHomologyMatrixRestriction M r (m + 2)
        (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m c) =
      cyclicTotalHomologyPeriodicity R A M m (cyclicTotalHomologyMatrixRestriction M r m c) :=
  cyclicTotalHomologyMapRows_cyclicTotalHomologyPeriodicity _ _ _ m c
/-- Corner restriction is a left inverse to matrix extension on `Hᵐ(Tot)`. -/
@[simp] theorem cyclicTotalHomologyMatrixRestriction_cyclicTotalHomologyMatrixExtension
    [DecidableEq ι] (r : ι) (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyMatrixRestriction M r m (cyclicTotalHomologyMatrixExtension M ι m c) =
      c := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    cyclicTotalHomologyMatrixRestriction_cyclicTotalHomologyMk]
  exact congrArg (cyclicTotalHomologyMk R A M m)
    (Subtype.ext <| Subtype.ext <| funext fun q ↦ by simp)
end NonUnital

section Unital
variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι]

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
  exact congrArg (cyclicTotalHomologyMk R (Matrix ι ι A) M m)
    (Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι φ.val))
/-- Matrix extension commutes with Connes' operator `B : HHᵐ⁺¹ → Hᵐ(Tot)`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB [DecidableEq ι]
    (m : ℕ) (c : hochschildCohomology R A M (m + 1)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyConnesB R A M m c) =
      cyclicTotalHomologyConnesB R (Matrix ι ι A) M m
        (hochschildCohomology.matrixExtension M ι (m + 1) c) := by
  simp [cyclicTotalHomologyConnesB_def]

section Nonempty
variable [Nonempty ι]

variable (ι) in
/-- **Matrix Morita invariance of the total cyclic bicomplex** over any commutative ring `R`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (n : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  classical
  let E := cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι
  let H := hochschildCohomology.matrixExtension (R := R) (A := A) M ι
  let iA k := HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) k
  let iM k := HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) k
  let BA k := (cyclicTotalHomologyConnesB R A M k).hom
  let BM k := (cyclicTotalHomologyConnesB R (Matrix ι ι A) M k).hom
  let SA k := (cyclicTotalHomologyPeriodicity R A M k).hom
  let SM k := (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M k).hom
  have hI k : (iM k).hom ∘ₗ E k = H k ∘ₗ (iA k).hom :=
    LinearMap.ext (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension k)
  have hB k : BM k ∘ₗ H (k + 1) = E k ∘ₗ BA k :=
    (LinearMap.ext (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyConnesB k)).symm
  have hS k : SM k ∘ₗ E k = E (k + 2) ∘ₗ SA k :=
    (LinearMap.ext (cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity k)).symm
  have hH k := hochschildCohomology.bijective_matrixExtension (R := R) (A := A) (M := M) ι k
  have h0 : Function.Bijective (E 0) :=
    (((ConcreteCategory.isIso_iff_bijective (iM 0)).1 inferInstance).of_comp_iff' _).1 <| by
      rw [show (iM 0 : _ → _) ∘ E 0 = (H 0 : _ → _) ∘ iA 0 from funext (LinearMap.congr_fun (hI 0))]
      exact (hH 0).comp ((ConcreteCategory.isIso_iff_bijective (iA 0)).1 inferInstance)
  induction n using Nat.strong_induction_on with
  | ind n ih => match n with
    | 0 => exact h0
    | 1 =>
      exact LinearMap.bijective_of_bijective_of_injective_of_left_exact (iA 1).hom (BA 0) (iM 1).hom
        (BM 0) (E 1) (H 1) (E 0) (hI 1) (hB 0)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB R A M 0)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB R
          (Matrix ι ι A) M 0) (hH 1) h0.1
        (injective_homologyMap_cyclicTotalComplexToHochschild_one R A M)
        (injective_homologyMap_cyclicTotalComplexToHochschild_one R (Matrix ι ι A) M)
    | m + 2 =>
      exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
        (BA m) (SA m) (iA (m + 2)).hom (BA (m + 1)) (BM m) (SM m) (iM (m + 2)).hom (BM (m + 1))
        (H (m + 1)) (E m) (E (m + 2)) (H (m + 2)) (E (m + 1)) (hB m) (hS m) (hI (m + 2))
        (hB (m + 1)) (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity R A M m)
        (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M m)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB R A M (m + 1))
        (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m)
        (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
          R (Matrix ι ι A) M m)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB R
          (Matrix ι ι A) M (m + 1))
        (hH (m + 1)).2 (ih m (by omega)) (hH (m + 2)) (ih (m + 1) (by omega)).1

variable (M ι) in
/-- **Matrix Morita equivalence on `Hⁿ(Tot)`** over any commutative ring `R`. -/
noncomputable def cyclicTotalHomologyMatrixExtensionEquiv (n : ℕ) :
    (cyclicTotalComplex R A M).homology n ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι n)
    (bijective_cyclicTotalHomologyMatrixExtension ι n)
/-- Underlying linear map of `cyclicTotalHomologyMatrixExtensionEquiv`. -/
@[simp] theorem coe_cyclicTotalHomologyMatrixExtensionEquiv (n : ℕ) :
    (cyclicTotalHomologyMatrixExtensionEquiv (R := R) (A := A) M ι n :
      (cyclicTotalComplex R A M).homology n →ₗ[R]
        (cyclicTotalComplex R (Matrix ι ι A) M).homology n) =
      cyclicTotalHomologyMatrixExtension M ι n := (rfl)
/-- `cyclicTotalHomologyMatrixExtensionEquiv` acts by `cyclicTotalHomologyMatrixExtension`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtensionEquiv_apply (n : ℕ)
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixExtensionEquiv M ι n c =
      cyclicTotalHomologyMatrixExtension M ι n c := (rfl)
/-- Applying `cyclicTotalHomologyMatrixExtension` to the inverse equivalence recovers `c`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMatrixExtensionEquiv_symm
    (n : ℕ) (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology n) :
    cyclicTotalHomologyMatrixExtension M ι n
      ((cyclicTotalHomologyMatrixExtensionEquiv M ι n).symm c) = c :=
  LinearEquiv.apply_symm_apply (cyclicTotalHomologyMatrixExtensionEquiv M ι n) c
/-- Applying `(cyclicTotalHomologyMatrixExtensionEquiv M ι n).symm` after extension recovers `c`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_cyclicTotalHomologyMatrixExtension
    (n : ℕ) (c : (cyclicTotalComplex R A M).homology n) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι n).symm
      (cyclicTotalHomologyMatrixExtension M ι n c) = c :=
  LinearEquiv.symm_apply_apply (cyclicTotalHomologyMatrixExtensionEquiv M ι n) c
/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` is corner restriction at any `r`. -/
theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_apply [DecidableEq ι] (r : ι) (n : ℕ)
    (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology n) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι n).symm c =
      cyclicTotalHomologyMatrixRestriction M r n c := by
  rw [← cyclicTotalHomologyMatrixRestriction_cyclicTotalHomologyMatrixExtension r n
    ((cyclicTotalHomologyMatrixExtensionEquiv M ι n).symm c),
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMatrixExtensionEquiv_symm]
/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` commutes with `I`. -/
@[simp]
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtensionEquiv_symm
    (m : ℕ) (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology m) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm c) =
      (hochschildCohomology.matrixExtensionEquiv M ι m).symm
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) m c) :=
  (hochschildCohomology.matrixExtensionEquiv M ι m).injective
    (by simp [← homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension])
/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` commutes with `S`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_cyclicTotalHomologyPeriodicity (m : ℕ)
    (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology m) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι (m + 2)).symm
        (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m c) =
      cyclicTotalHomologyPeriodicity R A M m
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm c) :=
  (cyclicTotalHomologyMatrixExtensionEquiv M ι (m + 2)).injective (by simp)
/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` commutes with `S^(j - i)`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_cyclicTotalHomologyPeriodicTransition
    (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology (n + 2 * i)) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * j)).symm
        (cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h c) =
      cyclicTotalHomologyPeriodicTransition R A M n h
        ((cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * i)).symm c) :=
  (cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * j)).injective (by simp)
/-- The inverse of `cyclicTotalHomologyMatrixExtensionEquiv` commutes with Connes' `B`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_cyclicTotalHomologyConnesB
    [DecidableEq ι] (m : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M (m + 1)) :
    (cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm
        (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m c) =
      cyclicTotalHomologyConnesB R A M m
        ((hochschildCohomology.matrixExtensionEquiv M ι (m + 1)).symm c) :=
  (cyclicTotalHomologyMatrixExtensionEquiv M ι m).injective (by simp)
end Nonempty
end Unital

/-! ### Matrix Morita invariance of cyclic cohomology -/

namespace cyclicCohomology
section Morita
variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable (ι) in
/-- **Matrix Morita invariance of cyclic cohomology under invertibility of `1, …, n`.** -/
theorem bijective_matrixExtension_of_isUnit (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  let jA := HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n
  let jM := HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n
  have hjA : Function.Bijective jA := (ConcreteCategory.isIso_iff_bijective _).1
    ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have hjM : Function.Bijective jM := (ConcreteCategory.isIso_iff_bijective _).1
    ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  have hcomm : jM ∘ matrixExtension M ι n = cyclicTotalHomologyMatrixExtension M ι n ∘ jA :=
    funext fun c ↦
      (cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal n c).symm
  exact (hjM.of_comp_iff' _).1 <| by
    rw [hcomm]; exact (bijective_cyclicTotalHomologyMatrixExtension ι n).comp hjA

variable (ι) in
/-- In degree zero, `cyclicCohomology.matrixExtension` is bijective over every commutative ring. -/
theorem bijective_matrixExtension_zero :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 (by simp)
variable (ι) in
/-- In degree one, `cyclicCohomology.matrixExtension` is bijective over every commutative ring. -/
theorem bijective_matrixExtension_one :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 1) :=
  bijective_matrixExtension_of_isUnit ι 1 fun q hq ↦ by obtain rfl := Nat.lt_one_iff.1 hq; simp

section RatAlgebra
variable [Algebra ℚ R]

variable (ι) in
/-- **Matrix Morita invariance of cyclic cohomology** over a `ℚ`-algebra `R`. -/
theorem bijective_matrixExtension (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦ isUnit_natCast_add_one q
variable (M ι) in
/-- **Matrix Morita equivalence on cyclic cohomology** over a `ℚ`-algebra `R`. -/
noncomputable def matrixExtensionEquiv (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)
/-- The underlying linear map of `cyclicCohomology.matrixExtensionEquiv` is `matrixExtension`. -/
@[simp] theorem coe_matrixExtensionEquiv (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := (rfl)
/-- `cyclicCohomology.matrixExtensionEquiv` acts by `cyclicCohomology.matrixExtension`. -/
@[simp] theorem matrixExtensionEquiv_apply (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c := (rfl)
/-- Applying `cyclicCohomology.matrixExtension` to the inverse equivalence recovers `c`. -/
@[simp] theorem matrixExtension_matrixExtensionEquiv_symm (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n ((matrixExtensionEquiv M ι n).symm c) = c :=
  LinearEquiv.apply_symm_apply (matrixExtensionEquiv M ι n) c
/-- Applying `(matrixExtensionEquiv M ι n).symm` after `matrixExtension` recovers `c`. -/
@[simp] theorem matrixExtensionEquiv_symm_matrixExtension (n : ℕ) (c : cyclicCohomology R A M n) :
    (matrixExtensionEquiv M ι n).symm (matrixExtension M ι n c) = c :=
  LinearEquiv.symm_apply_apply (matrixExtensionEquiv M ι n) c
/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` is corner restriction at any `r : ι`. -/
theorem matrixExtensionEquiv_symm_apply (r : ι) (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = matrixRestriction M r n c := by
  rw [← matrixRestriction_matrixExtension r n ((matrixExtensionEquiv M ι n).symm c),
    matrixExtension_matrixExtensionEquiv_symm]
/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` commutes with `I`. -/
@[simp] theorem toHochschild_matrixExtensionEquiv_symm (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    toHochschild R A M n ((matrixExtensionEquiv M ι n).symm c) =
      (hochschildCohomology.matrixExtensionEquiv M ι n).symm
        (toHochschild R (Matrix ι ι A) M n c) :=
  (hochschildCohomology.matrixExtensionEquiv M ι n).injective
    (by simp [← toHochschild_matrixExtension])
/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` commutes with Connes' `B`. -/
@[simp] theorem matrixExtensionEquiv_symm_connesB (n : ℕ)
    (c : hochschildCohomology R (Matrix ι ι A) M (n + 1)) :
    (matrixExtensionEquiv M ι n).symm (hochschildCohomology.connesB R (Matrix ι ι A) M n c) =
      hochschildCohomology.connesB R A M n
        ((hochschildCohomology.matrixExtensionEquiv M ι (n + 1)).symm c) :=
  (matrixExtensionEquiv M ι n).injective (by simp)
/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` commutes with `S`. -/
@[simp] theorem matrixExtensionEquiv_symm_periodicity (n : ℕ)
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι (n + 2)).symm (periodicity R (Matrix ι ι A) M n c) =
      periodicity R A M n ((matrixExtensionEquiv M ι n).symm c) :=
  (matrixExtensionEquiv M ι (n + 2)).injective (by simp)
/-- The inverse of `cyclicCohomology.matrixExtensionEquiv` commutes with `S^(j - i)`. -/
@[simp] theorem matrixExtensionEquiv_symm_periodicTransition (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : cyclicCohomology R (Matrix ι ι A) M (n + 2 * i)) :
    (matrixExtensionEquiv M ι (n + 2 * j)).symm (periodicTransition R (Matrix ι ι A) M n h c) =
      periodicTransition R A M n h ((matrixExtensionEquiv M ι (n + 2 * i)).symm c) :=
  (matrixExtensionEquiv M ι (n + 2 * j)).injective (by simp)
end RatAlgebra
end Morita
end cyclicCohomology

/-- `(cyclicTotalHomologyMatrixExtensionEquiv M ι m).symm` commutes with `HCᵐ → Hᵐ(Tot)`. -/
@[simp] theorem cyclicTotalHomologyMatrixExtensionEquiv_symm_homologyMap_cyclicCochainComplexToTotal
    {R A M : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A] [AddCommGroup M]
    [Module R M] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (m : ℕ)
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
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]

variable (M ι) in
/-- Matrix extension `HPⁿ(A; M) →ₗ[R] HPⁿ(Matrix ι ι A; M)` on periodic cyclic cohomology. -/
noncomputable def matrixExtension (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  mapStages (fun k ↦ cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun k ↦ cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity (n + 2 * k)
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
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity n z
/-- Matrix extension on `HPⁿ` commutes with `(shiftIso R A M n).inv`. -/
@[simp] theorem matrixExtension_shiftIso_inv (n : ℕ) (z : periodicCyclicCohomology R A M n) :
    matrixExtension M ι (n + 2) ((shiftIso R A M n).inv z) =
      (shiftIso R (Matrix ι ι A) M n).inv (matrixExtension M ι n z) :=
  mapStages_shiftIso_inv (cyclicTotalHomologyMatrixExtension M ι)
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity n z

variable (M) in
/-- Corner restriction `HPⁿ(Matrix ι ι A; M) →ₗ[R] HPⁿ(A; M)` along `x ↦ Matrix.single r r x`. -/
noncomputable def matrixRestriction [DecidableEq ι] (r : ι) (n : ℕ) :
    periodicCyclicCohomology R (Matrix ι ι A) M n →ₗ[R] periodicCyclicCohomology R A M n :=
  mapStages (fun k ↦ cyclicTotalHomologyMatrixRestriction M r (n + 2 * k))
    fun k ↦ cyclicTotalHomologyMatrixRestriction_cyclicTotalHomologyPeriodicity r (n + 2 * k)
/-- On stage `Hⁿ⁺²ᵏ(Tot)`, `matrixRestriction` acts via `cyclicTotalHomologyMatrixRestriction`. -/
@[simp] theorem matrixRestriction_ι [DecidableEq ι] (r : ι) (n k : ℕ)
    (x : (cyclicTotalComplex R (Matrix ι ι A) M).homology (n + 2 * k)) :
    matrixRestriction M r n (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k x) =
      periodicCyclicCohomology.ι R A M n k
        (cyclicTotalHomologyMatrixRestriction M r (n + 2 * k) x) := mapStages_ι _ _ k x
/-- Corner restriction is a left inverse to matrix extension on `HPⁿ`. -/
@[simp] theorem matrixRestriction_matrixExtension [DecidableEq ι] (r : ι) (n : ℕ)
    (c : periodicCyclicCohomology R A M n) : matrixRestriction M r n (matrixExtension M ι n c) =
      c := by obtain ⟨k, x, rfl⟩ := exists_ι_eq c; simp
end NonUnital

section Unital
variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι]

/-- Matrix extension on `HPⁿ` commutes with the normalized stage maps `fromCyclicCohomology`. -/
@[simp] theorem matrixExtension_fromCyclicCohomology [Algebra ℚ R] [DecidableEq ι] (n k : ℕ)
    (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix ι ι A) M n k
        (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by simp [fromCyclicCohomology_def]

section Nonempty
variable [Nonempty ι]

variable (M ι) in
/-- **Matrix Morita equivalence on periodic cyclic cohomology** over every commutative ring `R`. -/
noncomputable def matrixExtensionEquiv (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  congrStages (fun k ↦ cyclicTotalHomologyMatrixExtensionEquiv M ι (n + 2 * k))
    (by intro k x; exact cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyPeriodicity _ x)
/-- Underlying linear map of `periodicCyclicCohomology.matrixExtensionEquiv`. -/
@[simp] theorem coe_matrixExtensionEquiv (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := by
  ext k x; exact (congrStages_ι _ _ k x).trans (by simp)
/-- `periodicCyclicCohomology.matrixExtensionEquiv` acts by `matrixExtension`. -/
@[simp] theorem matrixExtensionEquiv_apply (n : ℕ) (c : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  DFunLike.congr_fun (coe_matrixExtensionEquiv n) c
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
/-- The inverse of `periodicCyclicCohomology.matrixExtensionEquiv` is corner restriction. -/
theorem matrixExtensionEquiv_symm_apply [DecidableEq ι] (r : ι) (n : ℕ)
    (c : periodicCyclicCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = matrixRestriction M r n c := by
  rw [← matrixRestriction_matrixExtension r n ((matrixExtensionEquiv M ι n).symm c),
    matrixExtension_matrixExtensionEquiv_symm]
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
variable (ι) in
/-- **Matrix Morita invariance of periodic cyclic cohomology** over every commutative ring `R`. -/
theorem bijective_matrixExtension (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  rw [← coe_matrixExtensionEquiv]; exact (matrixExtensionEquiv M ι n).bijective
/-- `(matrixExtensionEquiv M ι n).symm` commutes with `fromCyclicCohomology`. -/
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
