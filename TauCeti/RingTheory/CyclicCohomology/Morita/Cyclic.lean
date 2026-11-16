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

For a unital algebra `A` over a commutative ring `R`, an `R`-module `M`, and a nonempty finite
index type `ι`, the generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`)
induces isomorphisms on the cohomology `Hⁿ(Tot)` of the total complex of Connes' cyclic bicomplex
and on periodic cyclic cohomology `HPⁿ(A; M)` in every degree `n`. When `1, 2, …, n` are
invertible in `R` — in particular over every `ℚ`-algebra — it induces an isomorphism on cyclic
cohomology `HCⁿ(A; M)` (`TauCeti.cyclicCohomology.matrixExtension`).

## Strategy

1. **Total cyclic bicomplex:** Applying `matrixCochainExtension` rowwise defines a map of total
   cochains commuting with the total differential `D` and the maps `I`, `S`, and `B` of the SBI
   exact sequence. Strong induction on the degree `n` using the degree-zero isomorphism
   `H⁰(Tot) ≃ HH⁰`, the left-exact four lemma in degree one, the five lemma along the SBI sequence
   in degrees `m + 2`, and matrix Morita invariance of Hochschild cohomology
   (`TauCeti.hochschildCohomology.bijective_matrixExtension`) shows that matrix extension is
   bijective on `Hⁿ(Tot)` in every degree over every commutative ring `R`.
2. **Cyclic cohomology:** Under `∀ q < n, IsUnit ((q : R) + 1)` — and in particular when `R` is
   a `ℚ`-algebra — the inclusion `cyclicCochainComplexToTotal` is a quasi-isomorphism in degree
   `n` (`TauCeti.quasiIsoAt_cyclicCochainComplexToTotal`), transferring bijectivity to
   `TauCeti.cyclicCohomology.matrixExtension`.
3. **Periodic cyclic cohomology:** Since matrix extension on `Hⁿ(Tot)` commutes with the
   periodicity operator `S`, it descends to a bijection on the direct limit `HPⁿ(A; M)` over every
   commutative ring `R`.

## Main definitions

* `TauCeti.matrixCyclicTotalCochainExtension`, `TauCeti.matrixCyclicTotalCochainCornerRestriction`,
  `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixCornerRestriction`, `TauCeti.cyclicTotalHomologyMatrixEquiv`:
  matrix extension, diagonal corner restriction, and Morita equivalence on the total cyclic
  bicomplex and its cohomology.
* `TauCeti.cyclicCohomology.matrixCornerRestriction`, `TauCeti.cyclicCohomology.matrixEquiv`:
  diagonal corner restriction and the Morita linear equivalence on cyclic cohomology.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixCornerRestriction`,
  `TauCeti.periodicCyclicCohomology.matrixEquiv`: matrix extension, diagonal corner restriction,
  and Morita equivalence on periodic cyclic cohomology.

## Main results

* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix Morita invariance of the
  cohomology of the total cyclic bicomplex over any commutative ring.
* `TauCeti.cyclicCohomology.matrixExtension_injective`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: injectivity over any commutative ring and
  matrix Morita invariance of cyclic cohomology.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of
  periodic cyclic cohomology over any commutative ring.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II,
  Corollary 24, p. 113.
* J.-L. Loday, *Cyclic Homology*, §§2.2.9, 5.1.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

/-! ### Matrix extension on the total complex of Connes' cyclic bicomplex -/

section TotalCochains

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M]

/-- Rowwise matrix extension on total cochains of degree `m` of the cyclic bicomplex. -/
def matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m where
  toFun x := ⟨fun q ↦ matrixCochainExtension ι q (x.1 q),
    mem_cyclicTotalCochains_iff.2 fun q hq ↦ by
      rw [coe_cyclicTotalCochains_apply_of_lt x hq, map_zero]⟩
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)
  map_smul' c x := Subtype.ext (funext fun q ↦ by
    simp only [SetLike.val_smul, Pi.smul_apply, map_smul, RingHom.id_apply])

/-- Matrix extension of a total cochain applies `matrixCochainExtension` to every row. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply (ι : Type*) [Fintype ι] (m : ℕ)
    (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixCyclicTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) := by
  rfl

/-- Matrix extension on total cochains commutes with the periodicity shift `S`. -/
theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity (ι : Type*) [Fintype ι] (m : ℕ)
    (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) :=
  Subtype.ext (funext fun _ ↦ by simp)

/-- Matrix extension on total cochains commutes with projection onto column zero. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι]
    (m : ℕ) (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by
  simp

/-- Rowwise diagonal corner restriction on total cochains of degree `m` of the cyclic
bicomplex. -/
def matrixCyclicTotalCochainCornerRestriction {ι : Type*} [DecidableEq ι] (r : ι) (m : ℕ) :
    cyclicTotalCochains R (Matrix ι ι A) M m →ₗ[R] cyclicTotalCochains R A M m where
  toFun x := ⟨fun q ↦ matrixCornerCochainRestriction r q (x.1 q),
    mem_cyclicTotalCochains_iff.2 fun q hq ↦ by
      rw [coe_cyclicTotalCochains_apply_of_lt x hq, map_zero]⟩
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)
  map_smul' c x := Subtype.ext (funext fun q ↦ by
    simp only [SetLike.val_smul, Pi.smul_apply, map_smul, RingHom.id_apply])

/-- Diagonal corner restriction of a total cochain applies `matrixCornerCochainRestriction` to
every row. -/
@[simp]
theorem coe_matrixCyclicTotalCochainCornerRestriction_apply {ι : Type*} [DecidableEq ι] (r : ι)
    (m : ℕ) (x : cyclicTotalCochains R (Matrix ι ι A) M m) (q : ℕ) :
    (matrixCyclicTotalCochainCornerRestriction r m x).1 q =
      matrixCornerCochainRestriction r q (x.1 q) := by
  rfl

/-- Diagonal corner restriction is a left inverse to matrix extension on total cochains. -/
@[simp]
theorem matrixCyclicTotalCochainCornerRestriction_matrixCyclicTotalCochainExtension
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (m : ℕ) (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainCornerRestriction r m (matrixCyclicTotalCochainExtension ι m x) = x :=
  Subtype.ext (funext fun _ ↦ by simp)

/-- Diagonal corner restriction on total cochains commutes with the periodicity shift `S`. -/
theorem matrixCyclicTotalCochainCornerRestriction_cyclicTotalPeriodicity
    {ι : Type*} [DecidableEq ι] (r : ι) (m : ℕ) (x : cyclicTotalCochains R (Matrix ι ι A) M m) :
    matrixCyclicTotalCochainCornerRestriction r (m + 2)
        (cyclicTotalPeriodicity R (Matrix ι ι A) M m x) =
      cyclicTotalPeriodicity R A M m (matrixCyclicTotalCochainCornerRestriction r m x) :=
  Subtype.ext (funext fun _ ↦ by simp)

/-- Diagonal corner restriction on total cochains commutes with projection onto column zero. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainCornerRestriction
    {ι : Type*} [DecidableEq ι] (r : ι) (m : ℕ) (x : cyclicTotalCochains R (Matrix ι ι A) M m) :
    cyclicTotalToHochschild R A M m (matrixCyclicTotalCochainCornerRestriction r m x) =
      matrixCornerCochainRestriction r m (cyclicTotalToHochschild R (Matrix ι ι A) M m x) := by
  simp

end TotalCochains

section TotalHorizontal

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M]

/-- Matrix extension commutes with the horizontal differentials `1 - λ` and `N` of the cyclic
bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal (ι : Type*) [Fintype ι]
    (p q : ℕ) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_cyclicOperator]
  · simp [hp, matrixCochainExtension_cyclicNorm]

/-- Matrix extension on total cochains intertwines inclusion of cyclic cochains into column
zero. -/
theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal (ι : Type*) [Fintype ι] (m : ℕ)
    (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  by_cases hq : q = m
  · subst hq; simp
  · simp [Pi.single_eq_of_ne hq]

/-- Diagonal corner restriction commutes with the horizontal differentials `1 - λ` and `N` of the
cyclic bicomplex. -/
theorem matrixCornerCochainRestriction_cyclicBicomplexHorizontal {ι : Type*} [DecidableEq ι]
    (r : ι) (p q : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ Matrix ι ι A) M) :
    matrixCornerCochainRestriction r q (cyclicBicomplexHorizontal R (Matrix ι ι A) M p q ψ) =
      cyclicBicomplexHorizontal R A M p q (matrixCornerCochainRestriction r q ψ) := by
  ext a
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, cyclicOperator_apply, Function.comp_def]
  · simp [hp, cyclicNorm_apply, Function.comp_def]

end TotalHorizontal

section TotalDifferential

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension commutes with the vertical differentials `b` and `-b'` of the cyclic
bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (ι : Type*) [Fintype ι]
    (p q : ℕ) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_hochschildCoboundary]
  · simp [hp, matrixCochainExtension_barCoboundary]

/-- Matrix extension on total cochains commutes with the total differential of the cyclic
bicomplex. -/
theorem matrixCyclicTotalCochainExtension_cyclicTotalDifferential (ι : Type*) [Fintype ι]
    (m : ℕ) (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) =
      cyclicTotalDifferential R (Matrix ι ι A) M m
        (matrixCyclicTotalCochainExtension ι m x) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  cases q with
  | zero =>
    simp [cyclicTotalDifferential_apply_zero, matrixCochainExtension_cyclicBicomplexHorizontal]
  | succ q =>
    simp [cyclicTotalDifferential_apply_succ, map_add,
      matrixCochainExtension_cyclicBicomplexVertical,
      matrixCochainExtension_cyclicBicomplexHorizontal]

/-- Matrix extension maps total cocycles of the cyclic bicomplex to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker (ι : Type*) [Fintype ι] (m : ℕ)
    {x : cyclicTotalCochains R A M m}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M m)) :
    matrixCyclicTotalCochainExtension ι m x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← matrixCyclicTotalCochainExtension_cyclicTotalDifferential, hx, map_zero]

/-- Diagonal corner restriction commutes with the vertical differentials `b` and `-b'` of the
cyclic bicomplex. -/
theorem matrixCornerCochainRestriction_cyclicBicomplexVertical {ι : Type*} [Fintype ι]
    [DecidableEq ι] (r : ι) (p q : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ Matrix ι ι A) M) :
    matrixCornerCochainRestriction r (q + 1) (cyclicBicomplexVertical R (Matrix ι ι A) M p q ψ) =
      cyclicBicomplexVertical R A M p q (matrixCornerCochainRestriction r q ψ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCornerCochainRestriction_hochschildCoboundary]
  · simp only [cyclicBicomplexVertical_of_odd hp, LinearMap.neg_apply, map_neg]
    congr 1
    rw [eq_sub_of_add_eq (hochschildCoboundary_eq_barCoboundary_add ψ).symm,
      eq_sub_of_add_eq
        (hochschildCoboundary_eq_barCoboundary_add (matrixCornerCochainRestriction r q ψ)).symm,
      map_sub, map_zsmul, matrixCornerCochainRestriction_hochschildCoboundary,
      matrixCornerCochainRestriction_hochschildCoface]

/-- Diagonal corner restriction on total cochains commutes with the total differential of the
cyclic bicomplex. -/
theorem matrixCyclicTotalCochainCornerRestriction_cyclicTotalDifferential {ι : Type*} [Fintype ι]
    [DecidableEq ι] (r : ι) (m : ℕ) (x : cyclicTotalCochains R (Matrix ι ι A) M m) :
    matrixCyclicTotalCochainCornerRestriction r (m + 1)
        (cyclicTotalDifferential R (Matrix ι ι A) M m x) =
      cyclicTotalDifferential R A M m (matrixCyclicTotalCochainCornerRestriction r m x) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  cases q with
  | zero =>
    simp [cyclicTotalDifferential_apply_zero,
      matrixCornerCochainRestriction_cyclicBicomplexHorizontal]
  | succ q =>
    simp [cyclicTotalDifferential_apply_succ, map_add,
      matrixCornerCochainRestriction_cyclicBicomplexVertical,
      matrixCornerCochainRestriction_cyclicBicomplexHorizontal]

/-- Diagonal corner restriction maps matrix total cocycles of the cyclic bicomplex to total
cocycles. -/
theorem matrixCyclicTotalCochainCornerRestriction_mem_ker {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (m : ℕ) {x : cyclicTotalCochains R (Matrix ι ι A) M m}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m)) :
    matrixCyclicTotalCochainCornerRestriction r m x ∈
      LinearMap.ker (cyclicTotalDifferential R A M m) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← matrixCyclicTotalCochainCornerRestriction_cyclicTotalDifferential, hx, map_zero]

end TotalDifferential

/-! ### Matrix Morita invariance for the total complex of the cyclic bicomplex -/

section TotalHomology

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- Matrix extension on the cohomology `Hⁿ(Tot)` of the total complex of Connes' cyclic
bicomplex. -/
def cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    (cyclicTotalComplex R A M).homology n →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  (cyclicTotalHomologyMk R A M n).liftOfSurjective
    (M := LinearMap.ker (cyclicTotalDifferential R A M n)) (cyclicTotalHomologyMk_surjective n)
    ⟨cyclicTotalHomologyMk R (Matrix ι ι A) M n ∘ₗ
        (matrixCyclicTotalCochainExtension (R := R) (A := A) (M := M) ι n).restrict
          fun _ hx ↦ matrixCyclicTotalCochainExtension_mem_ker ι n hx,
      fun x hx ↦ by
        rw [LinearMap.mem_ker] at hx ⊢
        rw [LinearMap.comp_apply]
        cases n with
        | zero =>
          rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hx ⊢
          exact Subtype.ext (by simp [congrArg Subtype.val hx])
        | succ m =>
          rw [cyclicTotalHomologyMk_succ_eq_zero_iff] at hx ⊢
          obtain ⟨w, hw⟩ := hx
          exact ⟨matrixCyclicTotalCochainExtension ι m w, by
            rw [← matrixCyclicTotalCochainExtension_cyclicTotalDifferential, hw,
              LinearMap.restrict_apply]⟩⟩

/-- Matrix extension on total cohomology sends the class of a total cocycle to the class of its
rowwise matrix extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_mk {ι : Type*} [Fintype ι] {n : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M n)) :
    cyclicTotalHomologyMatrixExtension M ι n (cyclicTotalHomologyMk R A M n x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixCyclicTotalCochainExtension ι n x.1,
          matrixCyclicTotalCochainExtension_mem_ker ι n x.2⟩ := by
  exact LinearMap.equivOfSurjective_apply
    (M := LinearMap.ker (cyclicTotalDifferential R A M n)) (cyclicTotalHomologyMk_surjective n) _

variable (M) in
/-- Diagonal corner restriction on the cohomology `Hⁿ(Tot)` of the total complex of Connes'
cyclic bicomplex. -/
def cyclicTotalHomologyMatrixCornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) :
    (cyclicTotalComplex R (Matrix ι ι A) M).homology n →ₗ[R]
      (cyclicTotalComplex R A M).homology n :=
  (cyclicTotalHomologyMk R (Matrix ι ι A) M n).liftOfSurjective
    (M := LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n))
    (cyclicTotalHomologyMk_surjective n)
    ⟨cyclicTotalHomologyMk R A M n ∘ₗ
        (matrixCyclicTotalCochainCornerRestriction (R := R) (A := A) (M := M) r n).restrict
          fun _ hx ↦ matrixCyclicTotalCochainCornerRestriction_mem_ker r n hx,
      fun x hx ↦ by
        rw [LinearMap.mem_ker] at hx ⊢
        rw [LinearMap.comp_apply]
        cases n with
        | zero =>
          rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hx ⊢
          exact Subtype.ext (by simp [congrArg Subtype.val hx])
        | succ m =>
          rw [cyclicTotalHomologyMk_succ_eq_zero_iff] at hx ⊢
          obtain ⟨w, hw⟩ := hx
          exact ⟨matrixCyclicTotalCochainCornerRestriction r m w, by
            rw [← matrixCyclicTotalCochainCornerRestriction_cyclicTotalDifferential, hw,
              LinearMap.restrict_apply]⟩⟩

/-- Diagonal corner restriction on total cohomology sends the class of a matrix total cocycle to
the class of its restriction to the `(r, r)` diagonal corner. -/
@[simp]
theorem cyclicTotalHomologyMatrixCornerRestriction_mk {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) {n : ℕ} (x : LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n)) :
    cyclicTotalHomologyMatrixCornerRestriction M r n
        (cyclicTotalHomologyMk R (Matrix ι ι A) M n x) =
      cyclicTotalHomologyMk R A M n
        ⟨matrixCyclicTotalCochainCornerRestriction r n x.1,
          matrixCyclicTotalCochainCornerRestriction_mem_ker r n x.2⟩ := by
  exact LinearMap.equivOfSurjective_apply
    (M := LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n))
    (cyclicTotalHomologyMk_surjective n) _

/-- Diagonal corner restriction is a left inverse to matrix extension on total cohomology. -/
@[simp]
theorem cyclicTotalHomologyMatrixCornerRestriction_cyclicTotalHomologyMatrixExtension
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixCornerRestriction M r n
        (cyclicTotalHomologyMatrixExtension M ι n c) = c := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  simp only [cyclicTotalHomologyMatrixExtension_mk, cyclicTotalHomologyMatrixCornerRestriction_mk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainCornerRestriction_matrixCyclicTotalCochainExtension
    r n x.1)

/-- Matrix extension on total cohomology commutes with projection `I : Hⁿ(Tot) → HHⁿ`. -/
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (n : ℕ) (c : (cyclicTotalComplex R A M).homology n) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) n
        (cyclicTotalHomologyMatrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  simp only [cyclicTotalHomologyMatrixExtension_mk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk, coe_matrixCyclicTotalCochainExtension_apply]

/-- Matrix extension on total cohomology commutes with the periodicity operator
`S : Hᵐ(Tot) → Hᵐ⁺²(Tot)`. -/
theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      cyclicTotalHomologyMatrixExtension M ι (m + 2)
        (cyclicTotalHomologyPeriodicity R A M m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [cyclicTotalHomologyMatrixExtension_mk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity ι m x.1).symm

/-- Diagonal corner restriction on total cohomology commutes with the periodicity operator
`S : Hᵐ(Tot) → Hᵐ⁺²(Tot)`. -/
theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixCornerRestriction
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (m : ℕ)
    (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology m) :
    cyclicTotalHomologyPeriodicity R A M m (cyclicTotalHomologyMatrixCornerRestriction M r m c) =
      cyclicTotalHomologyMatrixCornerRestriction M r (m + 2)
        (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [cyclicTotalHomologyMatrixCornerRestriction_mk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainCornerRestriction_cyclicTotalPeriodicity r m x.1).symm

/-- Matrix extension on total cohomology commutes with the transition maps `S^(j - i)`. -/
theorem cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (n : ℕ) {i j : ℕ} (h : i ≤ j)
    (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
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
      ModuleCat.comp_apply, ModuleCat.comp_apply, ih,
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ,
      cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension]
    -- `n + 2 * (j + 1)` is definitionally `(n + 2 * j) + 2` (`Nat.mul_succ`).
    rfl

end TotalHomology

section TotalMorita

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Matrix extension intertwines Connes' operator `B : HHᵐ⁺¹ → Hᵐ(Tot)`. -/
theorem cyclicTotalHomologyConnesB_hochschildCohomology_matrixExtension
    (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ)
    (c : hochschildCohomology R A M (m + 1)) :
    cyclicTotalHomologyConnesB R (Matrix ι ι A) M m
        (hochschildCohomology.matrixExtension M ι (m + 1) c) =
      cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyConnesB R A M m c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (m + 1) c
  simp only [hochschildCohomology.matrixExtension_mk, cyclicTotalHomologyConnesB_mk,
    cyclicTotalHomologyMatrixExtension_mk]
  congr 1
  refine Subtype.ext (Subtype.ext (funext fun q ↦ ?_))
  by_cases hq : q = m
  · subst hq; simp [matrixCochainExtension_connesB]
  · simp [Pi.single_eq_of_ne hq]

/-- Matrix extension on cyclic cohomology and on total cohomology intertwine the inclusion
`cyclicCochainComplexToTotal`. -/
theorem cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal
    (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) (c : cyclicCohomology R A M n) :
    cyclicTotalHomologyMatrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n c) =
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n
        (cyclicCohomology.matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M n c
  simp only [homologyMap_cyclicCochainComplexToTotal_mk, cyclicTotalHomologyMatrixExtension_mk,
    cyclicCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι n φ.1)

/-- **Matrix Morita invariance of the total cyclic bicomplex.** For a unital algebra `A` over any
commutative ring `R`, any `R`-module `M`, and any nonempty finite index type `ι`, matrix extension
induces a bijection `(cyclicTotalComplex R A M).homology n →
(cyclicTotalComplex R (Matrix ι ι A) M).homology n` in every degree `n`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  classical
  let IA (k : ℕ) := (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) k).hom
  let IM (k : ℕ) :=
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) k).hom
  let BA (k : ℕ) := (cyclicTotalHomologyConnesB R A M k).hom
  let BM (k : ℕ) := (cyclicTotalHomologyConnesB R (Matrix ι ι A) M k).hom
  let SA (k : ℕ) := (cyclicTotalHomologyPeriodicity R A M k).hom
  let SM (k : ℕ) := (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M k).hom
  let tE (k : ℕ) := cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι k
  let hE (k : ℕ) := hochschildCohomology.matrixExtension (R := R) (A := A) M ι k
  have hcI (k : ℕ) : (IM k).comp (tE k) = (hE k).comp (IA k) := LinearMap.ext
    (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension ι k)
  have hcB (k : ℕ) : (BM k).comp (hE (k + 1)) = (tE k).comp (BA k) :=
    LinearMap.ext (cyclicTotalHomologyConnesB_hochschildCohomology_matrixExtension ι k)
  have hcS (k : ℕ) : (SM k).comp (tE k) = (tE (k + 2)).comp (SA k) :=
    LinearMap.ext (cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension ι k)
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 =>
      -- Degree 0: reduce to Hochschild cohomology via the isomorphism `I₀ : H⁰(Tot) ≃ HH⁰`.
      have hIA : Function.Bijective (IA 0) :=
        (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
      have hIM : Function.Bijective (IM 0) :=
        (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
      have hcomm : IM 0 ∘ tE 0 = hE 0 ∘ IA 0 := funext fun x ↦ LinearMap.congr_fun (hcI 0) x
      exact (Function.Bijective.of_comp_iff' hIM _).1
        (hcomm.symm ▸ (hochschildCohomology.bijective_matrixExtension ι 0).comp hIA)
    | 1 =>
      -- Degree 1: left-exact four lemma along `0 → H¹(Tot) → HH¹ → H⁰(Tot)`.
      exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
        (IA 1) (BA 0) (IM 1) (BM 0) (tE 1) (hE 1) (tE 0) (hcI 1) (hcB 0)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
        (hochschildCohomology.bijective_matrixExtension ι 1) (ih 0 (by omega)).1
        injective_homologyMap_cyclicTotalComplexToHochschild_one
        injective_homologyMap_cyclicTotalComplexToHochschild_one
    | m + 2 =>
      -- Degree `m + 2`: five lemma along the SBI exact sequence.
      exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
        (BA m) (SA m) (IA (m + 2)) (BA (m + 1)) (BM m) (SM m) (IM (m + 2)) (BM (m + 1))
        (hE (m + 1)) (tE m) (tE (m + 2)) (hE (m + 2)) (tE (m + 1))
        (hcB m) (hcS m) (hcI (m + 2)) (hcB (m + 1))
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
/-- **Matrix Morita equivalence of the total cyclic bicomplex**, as an `R`-linear equivalence
`Hⁿ(Tot(A)) ≃ₗ[R] Hⁿ(Tot(Matrix ι ι A))`. -/
def cyclicTotalHomologyMatrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (cyclicTotalComplex R A M).homology n ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι n)
    (bijective_cyclicTotalHomologyMatrixExtension ι n)

/-- The Morita linear equivalence on total cohomology is given by
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixEquiv_apply {ι : Type*} [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : (cyclicTotalComplex R A M).homology n) :
    cyclicTotalHomologyMatrixEquiv M ι n c = cyclicTotalHomologyMatrixExtension M ι n c := by
  rfl

/-- For a unital algebra, matrix extension is a left inverse to diagonal corner restriction on
total cohomology. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMatrixCornerRestriction
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology n) :
    cyclicTotalHomologyMatrixExtension M ι n
        (cyclicTotalHomologyMatrixCornerRestriction M r n c) = c := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨c', rfl⟩ := (bijective_cyclicTotalHomologyMatrixExtension (R := R) (A := A) (M := M)
    ι n).2 c
  rw [cyclicTotalHomologyMatrixCornerRestriction_cyclicTotalHomologyMatrixExtension]

/-- The inverse of `cyclicTotalHomologyMatrixEquiv` is given by diagonal corner restriction at any
index `r : ι`. -/
theorem cyclicTotalHomologyMatrixEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (r : ι) (n : ℕ) (c : (cyclicTotalComplex R (Matrix ι ι A) M).homology n) :
    (cyclicTotalHomologyMatrixEquiv M ι n).symm c =
      cyclicTotalHomologyMatrixCornerRestriction M r n c :=
  (bijective_cyclicTotalHomologyMatrixExtension ι n).1 <| by
    rw [← cyclicTotalHomologyMatrixEquiv_apply, LinearEquiv.apply_symm_apply,
      cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMatrixCornerRestriction]

end TotalMorita

/-! ### Matrix Morita invariance of cyclic cohomology -/

namespace cyclicCohomology

section General

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M]

private theorem coe_cyclicCochainsMap_singleLinearMap {ι : Type*} [DecidableEq ι] (r : ι) (n : ℕ)
    (ψ : cyclicCochains R (Matrix ι ι A) M n) :
    (cyclicCochainsMap M (Matrix.singleLinearMap R r r) n ψ :
        MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) =
      matrixCornerCochainRestriction r n ψ.1 := by
  ext; simp

variable (M) in
/-- Restriction to the `(r, r)` diagonal corner on cyclic cohomology. -/
def matrixCornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    cyclicCohomology R (Matrix ι ι A) M n →ₗ[R] cyclicCohomology R A M n :=
  desc n (mk R A M n ∘ₗ
      (cyclicCochainsMap (R := R) (A := A) (B := Matrix ι ι A) M
        (Matrix.singleLinearMap R r r) n).restrict
      fun ψ hψ ↦ by
        rw [mem_cyclicCocycles_iff] at hψ ⊢
        rw [coe_cyclicCochainsMap_singleLinearMap,
          ← matrixCornerCochainRestriction_hochschildCoboundary, hψ, map_zero])
    fun ψ hψ ↦ (mk_eq_zero_iff _ _ _ n _).2 <| by
      cases n with
      | zero =>
        rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hψ ⊢
        simp [hψ]
      | succ m =>
        obtain ⟨η, hη⟩ := (mem_cyclicCoboundaries_succ_iff _ _ _).1 hψ
        refine (mem_cyclicCoboundaries_succ_iff _ _ _).2
          ⟨cyclicCochainsMap M (Matrix.singleLinearMap R r r) m η, Subtype.ext ?_⟩
        rw [LinearMap.restrict_apply, coe_cyclicHochschildCoboundary_apply,
          coe_cyclicCochainsMap_singleLinearMap, coe_cyclicCochainsMap_singleLinearMap,
          ← matrixCornerCochainRestriction_hochschildCoboundary, ← hη,
          coe_cyclicHochschildCoboundary_apply]

/-- Diagonal corner restriction on cyclic cohomology sends the class of a matrix cyclic cocycle to
the class of its pullback along the `(r, r)` corner embedding. -/
@[simp]
theorem matrixCornerRestriction_mk {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}
    (ψ : cyclicCocycles R (Matrix ι ι A) M n) :
    matrixCornerRestriction M r n (mk R (Matrix ι ι A) M n ψ) =
      mk R A M n ⟨cyclicCochainsMap M (Matrix.singleLinearMap R r r) n ψ.1, by
        rw [mem_cyclicCocycles_iff,
          show (cyclicCochainsMap M (Matrix.singleLinearMap R r r) n ψ.1 :
              MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) =
              matrixCornerCochainRestriction r n ψ.1.1 by ext; simp,
          ← matrixCornerCochainRestriction_hochschildCoboundary,
          (mem_cyclicCocycles_iff R (Matrix ι ι A) M).1 ψ.2, map_zero]⟩ := by
  exact desc_mk _ _ _ ψ

/-- Diagonal corner restriction is a left inverse to matrix extension on cyclic cohomology. -/
@[simp]
theorem matrixCornerRestriction_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixCornerRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [matrixExtension_mk, matrixCornerRestriction_mk]
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  ext x
  simp [matrixCochainExtension_single]

/-- Over any commutative ring `R`, matrix extension on cyclic cohomology is injective. -/
theorem matrixExtension_injective (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (matrixCornerRestriction_matrixExtension r n)

/-- Matrix extension on cyclic cohomology commutes with `I : HCⁿ → HHⁿ`. -/
theorem toHochschild_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    toHochschild R (Matrix ι ι A) M n (matrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n (toHochschild R A M n c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [matrixExtension_mk, toHochschild_mk, hochschildCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (coe_matrixCyclicCochainExtension_apply ι n φ.1)

/-- Matrix extension intertwines Connes' operator `B : HHⁿ⁺¹ → HCⁿ`. -/
theorem matrixExtension_connesB (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (c : hochschildCohomology R A M (n + 1)) :
    matrixExtension M ι n (hochschildCohomology.connesB R A M n c) =
      hochschildCohomology.connesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (n + 1) c
  simp only [hochschildCohomology.connesB_mk, matrixExtension_mk,
    hochschildCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (Subtype.ext (by simp [matrixCochainExtension_connesB]))

/-- **Matrix Morita invariance of cyclic cohomology (finite invertibility).** When `1, 2, …, n`
are invertible in `R`, the generalized matrix trace induces a bijection
`HCⁿ(A; M) → HCⁿ(Matrix ι ι A; M)`. In particular, in degrees `0` and `1` this holds over
every commutative ring `R`. -/
theorem bijective_matrixExtension_of_isUnit
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
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
  have hTot : Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) :=
    bijective_cyclicTotalHomologyMatrixExtension ι n
  have hcomm :
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n ∘
        matrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι n ∘
        HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n :=
    funext fun c ↦
      (cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal ι n c).symm
  exact (Function.Bijective.of_comp_iff' hjM _).1 (hcomm.symm ▸ hTot.comp hjA)

/-- When `1, 2, …, n` are invertible in `R`, matrix extension is a left inverse to diagonal corner
restriction on cyclic cohomology. -/
theorem matrixExtension_matrixCornerRestriction_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1))
    (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (matrixCornerRestriction M r n c) = c := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨c', rfl⟩ := (bijective_matrixExtension_of_isUnit (R := R) (A := A) (M := M) ι n hR).2 c
  rw [matrixCornerRestriction_matrixExtension]

end General

section Rational

variable {R : Type*} [CommRing R] [Algebra ℚ R] {A : Type*} [Ring A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of cyclic cohomology.** For a unital algebra `A` over a commutative
`ℚ`-algebra `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`, the
matrix extension `φ ↦ φ#Tr` induces a bijection `HCⁿ(A; M) → HCⁿ(Matrix ι ι A; M)` in every
degree `n`. -/
theorem bijective_matrixExtension
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦ by
    simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

/-- Over a `ℚ`-algebra, matrix extension is a left inverse to diagonal corner restriction on cyclic
cohomology. -/
@[simp]
theorem matrixExtension_matrixCornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (c : cyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (matrixCornerRestriction M r n c) = c := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨c', rfl⟩ := (bijective_matrixExtension (R := R) (A := A) (M := M) ι n).2 c
  rw [matrixCornerRestriction_matrixExtension]

/-- Over a `ℚ`-algebra, matrix extension on cyclic cohomology commutes with Connes' periodicity
operator `S : HCᵐ → HCᵐ⁺²`. -/
theorem periodicity_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ)
    (c : cyclicCohomology R A M m) :
    periodicity R (Matrix ι ι A) M m (matrixExtension M ι m c) =
      matrixExtension M ι (m + 2) (periodicity R A M m c) := by
  apply (bijective_homologyMap_cyclicCochainComplexToTotal R (Matrix ι ι A) M (m + 2)).1
  rw [← cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]
  have hM := periodicity_comp_homologyMap_cyclicCochainComplexToTotal_apply
    R (Matrix ι ι A) M m (matrixExtension M ι m c)
  have hA := periodicity_comp_homologyMap_cyclicCochainComplexToTotal_apply R A M m c
  rw [hM, hA, map_neg, map_smul,
    ← cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension]

/-- Over a `ℚ`-algebra, matrix extension on cyclic cohomology commutes with the transition maps
`S^(j - i)`. -/
theorem periodicTransition_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ)
    {i j : ℕ} (h : i ≤ j) (c : cyclicCohomology R A M (n + 2 * i)) :
    periodicTransition R (Matrix ι ι A) M n h (matrixExtension M ι (n + 2 * i) c) =
      matrixExtension M ι (n + 2 * j) (periodicTransition R A M n h c) := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [← periodicTransition_comp R (Matrix ι ι A) M n hij (Nat.le_add_right j 1),
      ← periodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ModuleCat.comp_apply, ModuleCat.comp_apply, ih,
      periodicTransition_succ, periodicTransition_succ, periodicity_matrixExtension]
    -- `n + 2 * (j + 1)` is definitionally `(n + 2 * j) + 2` (`Nat.mul_succ`).
    rfl

variable (M) in
/-- **Matrix Morita equivalence of cyclic cohomology**, as an `R`-linear equivalence
`HCⁿ(A; M) ≃ₗ[R] HCⁿ(Matrix ι ι A; M)` over a `ℚ`-algebra. -/
def matrixEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The Morita linear equivalence on cyclic cohomology is given by `matrixExtension`. -/
@[simp]
theorem matrixEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    matrixEquiv M ι n c = matrixExtension M ι n c := by
  rfl

/-- The inverse of `matrixEquiv` is given by diagonal corner restriction at any index `r : ι`. -/
theorem matrixEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (r : ι)
    (n : ℕ) (c : cyclicCohomology R (Matrix ι ι A) M n) :
    (matrixEquiv M ι n).symm c = matrixCornerRestriction M r n c :=
  (bijective_matrixExtension ι n).1 <| by
    rw [← matrixEquiv_apply, LinearEquiv.apply_symm_apply, matrixExtension_matrixCornerRestriction]

end Rational

end cyclicCohomology

/-! ### Matrix Morita invariance of periodic cyclic cohomology -/

namespace periodicCyclicCohomology

section Map

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- Matrix extension `HPⁿ(A; M) → HPⁿ(Matrix ι ι A; M)` on periodic cyclic cohomology, induced
on the direct limit by matrix extension on the total cyclic bicomplex. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  periodicCyclicCohomology.lift
    (fun k ↦ (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun k x ↦ by
      simp only [LinearMap.comp_apply]
      refine (congrArg (periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1))
        (cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension
          ι (n + 2 * k) x).symm).trans ?_
      rw [← ModuleCat.comp_apply, cyclicTotalHomologyPeriodicity_ι]

/-- Matrix extension on periodic cyclic cohomology commutes with the canonical stage maps
`H^(n+2k)(Tot) → HPⁿ`. -/
@[simp]
theorem matrixExtension_ι (ι : Type*) [Fintype ι] (n k : ℕ)
    (x : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k x) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) x) :=
  periodicCyclicCohomology.lift_ι _ _ k x

private theorem cyclicTotalHomologyMatrixExtension_eqToHom {ι : Type*} [Fintype ι]
    {m₁ m₂ : ℕ} (h : m₁ = m₂) (x : (cyclicTotalComplex R A M).homology m₁) :
    cyclicTotalHomologyMatrixExtension M ι m₂
        (eqToHom (congrArg (fun m ↦ (cyclicTotalComplex R A M).homology m) h) x) =
      eqToHom (congrArg (fun m ↦ (cyclicTotalComplex R (Matrix ι ι A) M).homology m) h)
        (cyclicTotalHomologyMatrixExtension M ι m₁ x) := by
  subst h
  simp

/-- Matrix extension on periodic cyclic cohomology commutes with the `2`-periodicity
isomorphism `(shiftIso _ _ _ n).hom : HP^(n+2) → HP^n`. -/
theorem shiftIso_hom_matrixExtension (ι : Type*) [Fintype ι] (n : ℕ)
    (x : periodicCyclicCohomology R A M (n + 2)) :
    (shiftIso R (Matrix ι ι A) M n).hom (matrixExtension M ι (n + 2) x) =
      matrixExtension M ι n ((shiftIso R A M n).hom x) := by
  obtain ⟨k, z, rfl⟩ := exists_ι_eq x
  rw [matrixExtension_ι, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ι_shiftIso_hom,
    ι_shiftIso_hom, ModuleCat.comp_apply, ModuleCat.comp_apply, matrixExtension_ι,
    cyclicTotalHomologyMatrixExtension_eqToHom (show n + 2 + 2 * k = n + 2 * (k + 1) by omega)]

/-- Matrix extension on periodic cyclic cohomology commutes with the inverse `2`-periodicity
isomorphism `(shiftIso _ _ _ n).inv : HP^n → HP^(n+2)`. -/
theorem shiftIso_inv_matrixExtension (ι : Type*) [Fintype ι] (n : ℕ)
    (x : periodicCyclicCohomology R A M n) :
    (shiftIso R (Matrix ι ι A) M n).inv (matrixExtension M ι n x) =
      matrixExtension M ι (n + 2) ((shiftIso R A M n).inv x) := by
  apply ((ConcreteCategory.isIso_iff_bijective (shiftIso R (Matrix ι ι A) M n).hom).1
    inferInstance).1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    shiftIso_hom_matrixExtension, ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]

variable (M) in
/-- Diagonal corner restriction `HPⁿ(Matrix ι ι A; M) → HPⁿ(A; M)` on periodic cyclic cohomology,
induced on the direct limit by diagonal corner restriction on the total cyclic bicomplex. -/
def matrixCornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    periodicCyclicCohomology R (Matrix ι ι A) M n →ₗ[R] periodicCyclicCohomology R A M n :=
  periodicCyclicCohomology.lift
    (fun k ↦ (periodicCyclicCohomology.ι R A M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixCornerRestriction M r (n + 2 * k))
    fun k x ↦ by
      simp only [LinearMap.comp_apply]
      refine (congrArg (periodicCyclicCohomology.ι R A M n (k + 1))
        (cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixCornerRestriction
          r (n + 2 * k) x).symm).trans ?_
      rw [← ModuleCat.comp_apply, cyclicTotalHomologyPeriodicity_ι]

/-- Diagonal corner restriction on periodic cyclic cohomology commutes with the canonical stage
maps `H^(n+2k)(Tot) → HPⁿ`. -/
@[simp]
theorem matrixCornerRestriction_ι {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n k : ℕ)
    (x : (cyclicTotalComplex R (Matrix ι ι A) M).homology (n + 2 * k)) :
    matrixCornerRestriction M r n (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k x) =
      periodicCyclicCohomology.ι R A M n k
        (cyclicTotalHomologyMatrixCornerRestriction M r (n + 2 * k) x) :=
  periodicCyclicCohomology.lift_ι _ _ k x

/-- Diagonal corner restriction is a left inverse to matrix extension on periodic cyclic
cohomology. -/
@[simp]
theorem matrixCornerRestriction_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (x : periodicCyclicCohomology R A M n) :
    matrixCornerRestriction M r n (matrixExtension M ι n x) = x := by
  obtain ⟨k, z, rfl⟩ := exists_ι_eq x
  simp

end Map

section Morita

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Over a `ℚ`-algebra, matrix extension on periodic cyclic cohomology commutes with the
normalized stage maps `fromCyclicCohomology : HC^(n+2k) → HPⁿ`. -/
theorem matrixExtension_fromCyclicCohomology [Algebra ℚ R] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (n k : ℕ) (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix ι ι A) M n k
        (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by
  simp only [fromCyclicCohomology_apply, map_smul, matrixExtension_ι,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]

/-- **Matrix Morita invariance of periodic cyclic cohomology.** For a unital algebra `A` over any
commutative ring `R`, any `R`-module `M`, and any nonempty finite index type `ι`, matrix extension
induces a bijection `HPⁿ(A; M) → HPⁿ(Matrix ι ι A; M)` in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨k, z, rfl⟩ := exists_ι_eq x
    rw [matrixExtension_ι, ι_eq_zero_iff] at hx
    obtain ⟨j, hkj, hj⟩ := hx
    rw [cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension] at hj
    have hz : cyclicTotalHomologyPeriodicTransition R A M n hkj z = 0 :=
      (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * j)).1 (hj.trans (map_zero _).symm)
    exact (ι_eq_zero_iff z).2 ⟨j, hkj, hz⟩
  · obtain ⟨k, z, rfl⟩ := exists_ι_eq y
    obtain ⟨w, rfl⟩ := (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * k)).2 z
    exact ⟨periodicCyclicCohomology.ι R A M n k w, matrixExtension_ι ι n k w⟩

/-- For a unital algebra, matrix extension is a left inverse to diagonal corner restriction on
periodic cyclic cohomology. -/
@[simp]
theorem matrixExtension_matrixCornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (x : periodicCyclicCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (matrixCornerRestriction M r n x) = x := by
  have : Nonempty ι := ⟨r⟩
  obtain ⟨x', rfl⟩ := (bijective_matrixExtension (R := R) (A := A) (M := M) ι n).2 x
  rw [matrixCornerRestriction_matrixExtension]

variable (M) in
/-- **Matrix Morita equivalence of periodic cyclic cohomology**, as an `R`-linear equivalence
`HPⁿ(A; M) ≃ₗ[R] HPⁿ(Matrix ι ι A; M)` over any commutative ring `R`. -/
def matrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The Morita linear equivalence on periodic cyclic cohomology is given by `matrixExtension`. -/
@[simp]
theorem matrixEquiv_apply {ι : Type*} [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : periodicCyclicCohomology R A M n) :
    matrixEquiv M ι n c = matrixExtension M ι n c := by
  rfl

/-- The inverse of `matrixEquiv` is given by diagonal corner restriction at any index `r : ι`. -/
theorem matrixEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (r : ι)
    (n : ℕ) (c : periodicCyclicCohomology R (Matrix ι ι A) M n) :
    (matrixEquiv M ι n).symm c = matrixCornerRestriction M r n c :=
  (bijective_matrixExtension ι n).1 <| by
    rw [← matrixEquiv_apply, LinearEquiv.apply_symm_apply, matrixExtension_matrixCornerRestriction]

end Morita

end periodicCyclicCohomology

end TauCeti
