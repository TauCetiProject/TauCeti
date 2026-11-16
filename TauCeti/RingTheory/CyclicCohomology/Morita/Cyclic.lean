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

For a unital `R`-algebra `A`, an `R`-module `M`, and a nonempty finite index type `ι`, the
generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`) induces bijections on the
cohomology of the total cyclic bicomplex, on periodic cyclic cohomology, and (when `1, …, n` are
invertible in `R`, in particular over any `ℚ`-algebra) on Connes' cyclic cohomology.

Because matrix extension commutes with the Hochschild coboundary, the bar coboundary, the cyclic
operator, the cyclic norm, and Connes' operator `B`, it extends rowwise to the total cyclic
bicomplex (`TauCeti.matrixTotalCochainExtension`) and induces maps
`TauCeti.cyclicTotalHomologyMatrixExtension` on total cohomology commuting with `I`, `B`, and `S`
in the SBI sequence. Strong induction using the five lemma along the SBI sequence, combined with
matrix Morita invariance of Hochschild cohomology
(`TauCeti.hochschildCohomology.bijective_matrixExtension`) and the base case `H⁰(Tot) ≅ HH⁰`,
shows that matrix extension is bijective on `Hⁿ(Tot)` in every degree over any commutative ring
`R`. Transferring along `TauCeti.quasiIsoAt_cyclicCochainComplexToTotal` proves matrix Morita
invariance of Connes' cyclic cohomology `HCⁿ` whenever `1, …, n` are units in `R` (in particular
over any `ℚ`-algebra), and passing to the direct limit along `S` proves matrix Morita invariance
of periodic cyclic cohomology `HPⁿ`.

## Main definitions

* `TauCeti.matrixTotalCochainExtension`, `TauCeti.cyclicTotalHomologyMatrixExtension`: matrix
  extension on the total complex of the cyclic bicomplex and on its cohomology.
* `TauCeti.periodicCyclicCohomology.matrixExtension`: matrix extension on periodic cyclic
  cohomology.

## Main results

* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix Morita invariance of the
  cohomology of the total cyclic bicomplex over any commutative ring `R`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`,
  `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of cyclic
  cohomology.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of
  periodic cyclic cohomology.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II,
  Corollary 24, p. 113.
* J.-L. Loday, *Cyclic Homology*, §2.2.9.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

/-! ### Matrix extension on the total cyclic bicomplex -/

section BicomplexCochains

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] {ι : Type*} [Fintype ι]

/-- Matrix extension of total cochains of the cyclic bicomplex, applied row by row. -/
def matrixTotalCochainExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m where
  toFun x :=
    ⟨fun q ↦ matrixCochainExtension ι q (x.1 q),
      mem_cyclicTotalCochains_iff.2 fun q hq ↦ by
        rw [coe_cyclicTotalCochains_apply_of_lt x hq, map_zero]⟩
  map_add' _ _ := Subtype.ext (funext fun q ↦ by simp)
  map_smul' _ _ := Subtype.ext (funext fun q ↦ by simp)

/-- In row `q`, the matrix extension of a total cochain is the matrix extension of its `q`-th
component. -/
@[simp]
theorem coe_matrixTotalCochainExtension_apply {m : ℕ} (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) :=
  (rfl)

/-- Matrix extension commutes with the periodicity shift on total cochains. -/
theorem matrixTotalCochainExtension_cyclicTotalPeriodicity {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    matrixTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixTotalCochainExtension ι m x) :=
  Subtype.ext (funext fun q ↦ by simp)

/-- Matrix extension commutes with the projection of total cochains onto column zero. -/
theorem cyclicTotalToHochschild_matrixTotalCochainExtension {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by
  simp

end BicomplexCochains

section BicomplexHorizontal

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]

/-- Matrix extension commutes with the horizontal differentials of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, map_sub, matrixCochainExtension_cyclicOperator]
  · simp [hp, matrixCochainExtension_cyclicNorm]

/-- Matrix extension commutes with the inclusion of cyclic cochains into column zero of the total
complex. -/
theorem matrixTotalCochainExtension_cyclicCochainsToTotal {m : ℕ} (φ : cyclicCochains R A M m) :
    matrixTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  rcases eq_or_ne q m with rfl | hq
  · simp
  · simp [Pi.single_eq_of_ne hq]

end BicomplexHorizontal

section BicomplexDifferential

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι]

/-- Matrix extension commutes with the vertical differentials of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp, matrixCochainExtension_hochschildCoboundary]
  · simp [hp, map_neg, matrixCochainExtension_barCoboundary]

/-- Matrix extension commutes with the differential of the total complex of the cyclic
bicomplex. -/
theorem matrixTotalCochainExtension_cyclicTotalDifferential {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    matrixTotalCochainExtension ι (m + 1) (cyclicTotalDifferential R A M m x) =
      cyclicTotalDifferential R (Matrix ι ι A) M m (matrixTotalCochainExtension ι m x) := by
  refine Subtype.ext (funext fun q ↦ ?_)
  cases q with
  | zero =>
    simp [matrixCochainExtension_cyclicBicomplexHorizontal]
  | succ q =>
    simp [map_add, matrixCochainExtension_cyclicBicomplexVertical,
      matrixCochainExtension_cyclicBicomplexHorizontal]

end BicomplexDifferential

section TotalCohomology

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι]

/-- Matrix extension maps total cocycles to total cocycles. -/
theorem matrixTotalCochainExtension_mem_ker {m : ℕ} {x : cyclicTotalCochains R A M m}
    (hx : x ∈ LinearMap.ker (cyclicTotalDifferential R A M m)) :
    matrixTotalCochainExtension ι m x ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← matrixTotalCochainExtension_cyclicTotalDifferential, hx, map_zero]

/-- Two total cocycles with the same class in `Hⁿ(Tot(A; M))` have matrix extensions with the same
class in `Hⁿ(Tot(M_ι(A); M))`. -/
private theorem cyclicTotalHomologyMk_matrixTotalCochainExtension_eq {n : ℕ}
    {x y : LinearMap.ker (cyclicTotalDifferential R A M n)}
    (hxy : cyclicTotalHomologyMk R A M n x = cyclicTotalHomologyMk R A M n y) :
    cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixTotalCochainExtension ι n x.1, matrixTotalCochainExtension_mem_ker x.2⟩ =
      cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixTotalCochainExtension ι n y.1, matrixTotalCochainExtension_mem_ker y.2⟩ := by
  have hsub : cyclicTotalHomologyMk R A M n (x + (-1 : R) • y) = 0 := by
    rw [map_add, map_smul, neg_one_smul, hxy, add_neg_cancel]
  suffices h : cyclicTotalHomologyMk R (Matrix ι ι A) M n
      ⟨matrixTotalCochainExtension ι n (x + (-1 : R) • y).1,
        matrixTotalCochainExtension_mem_ker (x + (-1 : R) • y).2⟩ = 0 by
    have hmap :
        (⟨matrixTotalCochainExtension ι n (x + (-1 : R) • y).1,
            matrixTotalCochainExtension_mem_ker (x + (-1 : R) • y).2⟩ :
          LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M n)) =
          ⟨matrixTotalCochainExtension ι n x.1, matrixTotalCochainExtension_mem_ker x.2⟩ +
            (-1 : R) •
              ⟨matrixTotalCochainExtension ι n y.1, matrixTotalCochainExtension_mem_ker y.2⟩ :=
      Subtype.ext (by simp [map_add, map_smul])
    rw [hmap, map_add, map_smul, neg_one_smul, add_neg_eq_zero] at h
    exact h
  cases n with
  | zero =>
    rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hsub
    rw [hsub]
    exact (cyclicTotalHomologyMk_zero_eq_zero_iff _).2 (Subtype.ext (map_zero _))
  | succ n =>
    rw [cyclicTotalHomologyMk_succ_eq_zero_iff] at hsub
    obtain ⟨w, hw⟩ := hsub
    exact (cyclicTotalHomologyMk_succ_eq_zero_iff _).2 ⟨matrixTotalCochainExtension ι n w, by
      rw [← matrixTotalCochainExtension_cyclicTotalDifferential, hw]⟩

variable (M ι) in
/-- Matrix extension on the cohomology of the total complex of the cyclic bicomplex:
`Hⁿ(Tot(A; M)) → Hⁿ(Tot(Matrix ι ι A; M))`. -/
def cyclicTotalHomologyMatrixExtension (n : ℕ) :
    (cyclicTotalComplex R A M).homology n →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology n where
  toFun c :=
    let x := (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n c).choose
    cyclicTotalHomologyMk R (Matrix ι ι A) M n
      ⟨matrixTotalCochainExtension ι n x.1, matrixTotalCochainExtension_mem_ker x.2⟩
  map_add' c₁ c₂ := by
    let x₁ := (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n c₁).choose
    let x₂ := (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n c₂).choose
    let x₁₂ := (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n (c₁ + c₂)).choose
    have h := cyclicTotalHomologyMk_matrixTotalCochainExtension_eq (ι := ι)
      (x := x₁₂) (y := x₁ + x₂) (by
        rw [map_add,
          (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n c₁).choose_spec,
          (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n c₂).choose_spec,
          (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n (c₁ + c₂)).choose_spec])
    refine h.trans ?_
    rw [← map_add]
    congr 1
    exact Subtype.ext (map_add _ _ _)
  map_smul' r c := by
    let x := (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n c).choose
    let rx := (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n (r • c)).choose
    have h := cyclicTotalHomologyMk_matrixTotalCochainExtension_eq (ι := ι)
      (x := rx) (y := r • x) (by
        rw [map_smul,
          (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n c).choose_spec,
          (cyclicTotalHomologyMk_surjective (R := R) (A := A) (M := M) n (r • c)).choose_spec])
    refine h.trans ?_
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (map_smul _ _ _)

/-- Matrix extension on total cohomology sends the class of a total cocycle to the class of its
rowwise matrix extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk {n : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M n)) :
    cyclicTotalHomologyMatrixExtension M ι n (cyclicTotalHomologyMk R A M n x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M n
        ⟨matrixTotalCochainExtension ι n x.1, matrixTotalCochainExtension_mem_ker x.2⟩ :=
  cyclicTotalHomologyMk_matrixTotalCochainExtension_eq
    (cyclicTotalHomologyMk_surjective n (cyclicTotalHomologyMk R A M n x)).choose_spec

/-- Matrix extension commutes with the column-zero projection `I : Hⁿ(Tot) → HHⁿ`. -/
theorem homologyMap_cyclicTotalComplexToHochschild_comp_matrixExtension (n : ℕ) :
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) n).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι n =
      hochschildCohomology.matrixExtension M ι n ∘ₗ
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n).hom := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective n c
  simp only [LinearMap.comp_apply, cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk, coe_matrixTotalCochainExtension_apply]

/-- Matrix extension commutes with the periodicity map `S : Hᵐ(Tot) → Hᵐ⁺²(Tot)`. -/
theorem cyclicTotalHomologyPeriodicity_comp_matrixExtension (m : ℕ) :
    (cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι m =
      cyclicTotalHomologyMatrixExtension M ι (m + 2) ∘ₗ
        (cyclicTotalHomologyPeriodicity R A M m).hom := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  simp only [LinearMap.comp_apply, cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixTotalCochainExtension_cyclicTotalPeriodicity x.1).symm

end TotalCohomology

section TotalCohomologyUnital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι]

/-- Matrix extension commutes with the inclusion of cyclic cohomology into the cohomology of the
total complex. -/
theorem homologyMap_cyclicCochainComplexToTotal_comp_matrixExtension [DecidableEq ι] (n : ℕ) :
    (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n).hom ∘ₗ
        cyclicCohomology.matrixExtension M ι n =
      cyclicTotalHomologyMatrixExtension M ι n ∘ₗ
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n).hom := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M n c
  simp only [LinearMap.comp_apply, cyclicCohomology.matrixExtension_mk,
    homologyMap_cyclicCochainComplexToTotal_mk,
    cyclicTotalHomologyMatrixExtension_cyclicTotalHomologyMk]
  congr 1
  exact Subtype.ext (matrixTotalCochainExtension_cyclicCochainsToTotal φ.1).symm

/-- Matrix extension commutes with the connecting map `B : HHᵐ⁺¹ → Hᵐ(Tot)` of the SBI
sequence. -/
theorem cyclicTotalHomologyConnesB_comp_matrixExtension [DecidableEq ι] (m : ℕ) :
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M m).hom ∘ₗ
        hochschildCohomology.matrixExtension M ι (m + 1) =
      cyclicTotalHomologyMatrixExtension M ι m ∘ₗ (cyclicTotalHomologyConnesB R A M m).hom := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.hom_comp,
    ModuleCat.hom_comp, LinearMap.comp_assoc, hochschildCohomology.connesB_comp_matrixExtension,
    ← LinearMap.comp_assoc, homologyMap_cyclicCochainComplexToTotal_comp_matrixExtension,
    LinearMap.comp_assoc]

/-- Base case `n = 0` of matrix Morita invariance for `Hⁿ(Tot)`, from `H⁰(Tot) ≅ HH⁰`. -/
private theorem bijective_cyclicTotalHomologyMatrixExtension_zero [Nonempty ι] :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 0) := by
  have hI₁ : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hI₂ : Function.Bijective
      (HomologicalComplex.homologyMap
        (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hcomp :
      Function.Bijective
        ((HomologicalComplex.homologyMap
          (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0).hom ∘ₗ
          cyclicTotalHomologyMatrixExtension M ι 0) := by
    rw [homologyMap_cyclicTotalComplexToHochschild_comp_matrixExtension]
    exact (hochschildCohomology.bijective_matrixExtension ι 0).comp hI₁
  exact (Function.Bijective.of_comp_iff' hI₂ _).1 hcomp

/-- Base case `n = 1` of matrix Morita invariance for `Hⁿ(Tot)`, from the left-exact tail
`0 → H¹(Tot) → HH¹ → H⁰(Tot)`. -/
private theorem bijective_cyclicTotalHomologyMatrixExtension_one [Nonempty ι]
    (h0 : Function.Injective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 0)) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι 1) :=
  open scoped Classical in
  LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 1).hom
    (cyclicTotalHomologyConnesB R A M 0).hom
    (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 1).hom
    (cyclicTotalHomologyConnesB R (Matrix ι ι A) M 0).hom
    (cyclicTotalHomologyMatrixExtension M ι 1)
    (hochschildCohomology.matrixExtension M ι 1)
    (cyclicTotalHomologyMatrixExtension M ι 0)
    (homologyMap_cyclicTotalComplexToHochschild_comp_matrixExtension 1)
    (cyclicTotalHomologyConnesB_comp_matrixExtension 0)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
    (hochschildCohomology.bijective_matrixExtension ι 1) h0
    injective_homologyMap_cyclicTotalComplexToHochschild_one
    injective_homologyMap_cyclicTotalComplexToHochschild_one

/-- Inductive step `m + 2` of matrix Morita invariance for `Hⁿ(Tot)`, by the five lemma on
`HHᵐ⁺¹ → Hᵐ(Tot) → Hᵐ⁺²(Tot) → HHᵐ⁺² → Hᵐ⁺¹(Tot)`. -/
private theorem bijective_cyclicTotalHomologyMatrixExtension_add_two [Nonempty ι] (m : ℕ)
    (hm : Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι m))
    (hm1 : Function.Injective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι (m + 1))) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι (m + 2)) :=
  open scoped Classical in
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
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
    (cyclicTotalHomologyConnesB_comp_matrixExtension m)
    (cyclicTotalHomologyPeriodicity_comp_matrixExtension m)
    (homologyMap_cyclicTotalComplexToHochschild_comp_matrixExtension (m + 2))
    (cyclicTotalHomologyConnesB_comp_matrixExtension (m + 1))
    (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m)
    (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M m)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m + 1))
    (exact_cyclicTotalHomologyConnesB_cyclicTotalHomologyPeriodicity m)
    (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild
      R (Matrix ι ι A) M m)
    (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB (m + 1))
    (hochschildCohomology.bijective_matrixExtension ι (m + 1)).2 hm
    (hochschildCohomology.bijective_matrixExtension ι (m + 2)) hm1

/-- **Matrix Morita invariance of the total cyclic bicomplex.** For a unital algebra `A` over any
commutative ring `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`,
matrix extension induces a bijection `Hⁿ(Tot(A; M)) → Hⁿ(Tot(M_ι(A); M))` in every degree `n`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact bijective_cyclicTotalHomologyMatrixExtension_zero
    | 1 => exact bijective_cyclicTotalHomologyMatrixExtension_one (ih 0 Nat.zero_lt_one).1
    | m + 2 =>
      exact bijective_cyclicTotalHomologyMatrixExtension_add_two m
        (ih m (by omega)) (ih (m + 1) (by omega)).1

end TotalCohomologyUnital

/-! ### Matrix Morita invariance of cyclic cohomology -/

namespace cyclicCohomology

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of cyclic cohomology (invertible-degrees form).** For a unital
algebra `A` over a commutative ring `R` in which `1, …, n` are invertible, coefficients in an
`R`-module `M`, and a nonempty finite index type `ι`, matrix extension induces a bijection
`HCⁿ(A; M) → HCⁿ(M_ι(A); M)`. -/
theorem bijective_matrixExtension_of_isUnit (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have hq₁ : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have hq₂ : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  have hcomp :
      Function.Bijective
        ((HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n).hom ∘ₗ
          matrixExtension M ι n) := by
    rw [homologyMap_cyclicCochainComplexToTotal_comp_matrixExtension]
    exact (bijective_cyclicTotalHomologyMatrixExtension ι n).comp hq₁
  exact (Function.Bijective.of_comp_iff' hq₂ _).1 hcomp

/-- **Matrix Morita invariance of cyclic cohomology.** For a unital algebra `A` over a commutative
`ℚ`-algebra `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`, the
matrix extension `φ ↦ φ#Tr` induces a bijection `HCⁿ(A; M) → HCⁿ(M_ι(A); M)` in every degree
`n`. -/
theorem bijective_matrixExtension [Algebra ℚ R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦ by
    simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

end cyclicCohomology

/-! ### Matrix Morita invariance of periodic cyclic cohomology -/

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι]

/-- Matrix extension commutes with the transition maps of the periodic direct system. -/
private theorem cyclicTotalHomologyPeriodicTransition_matrixExtension (n : ℕ) {i j : ℕ}
    (h : i ≤ j) (x : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) x) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h x) := by
  induction j, h using Nat.le_induction with
  | base =>
    simp
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hij
        (Nat.le_add_right j 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ModuleCat.comp_apply, ModuleCat.comp_apply, ih,
      cyclicTotalHomologyPeriodicTransition_succ, cyclicTotalHomologyPeriodicTransition_succ]
    exact LinearMap.congr_fun
      (cyclicTotalHomologyPeriodicity_comp_matrixExtension (R := R) (A := A) (M := M) (ι := ι)
        (n + 2 * j)) _

variable (M ι) in
/-- Matrix extension on periodic cyclic cohomology: `HPⁿ(A; M) → HPⁿ(Matrix ι ι A; M)`. -/
def matrixExtension (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  descLinear
    (fun k ↦ (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun k ↦ by
      ext x
      have h := LinearMap.congr_fun
        (cyclicTotalHomologyPeriodicity_comp_matrixExtension (R := R) (A := A) (M := M) (ι := ι)
          (n + 2 * k)) x
      exact (congrArg (periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1)).hom h.symm).trans
        (congrArg (fun f ↦ f.hom (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) x))
          (cyclicTotalHomologyPeriodicity_ι R (Matrix ι ι A) M n k))

/-- On the `k`-th stage `H^(n+2k)(Tot)`, matrix extension on periodic cyclic cohomology is the
total-cohomology matrix extension followed by the canonical map to `HPⁿ`. -/
@[simp]
theorem matrixExtension_ι (n k : ℕ) (x : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k x) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) x) :=
  descLinear_ι _ _ k x

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Matrix Morita invariance of periodic cyclic cohomology.** For a unital algebra `A` over any
commutative ring `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`,
matrix extension induces a bijection `HPⁿ(A; M) → HPⁿ(M_ι(A); M)` in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨k, z, rfl⟩ := exists_ι_eq x
    rw [matrixExtension_ι, ι_eq_zero_iff] at hx
    obtain ⟨j, hkj, hj⟩ := hx
    rw [cyclicTotalHomologyPeriodicTransition_matrixExtension] at hj
    rw [ι_eq_zero_iff]
    exact ⟨j, hkj, (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * j)).1
      (hj.trans (map_zero _).symm)⟩
  · obtain ⟨k, z, rfl⟩ := exists_ι_eq y
    obtain ⟨w, rfl⟩ := (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * k)).2 z
    exact ⟨periodicCyclicCohomology.ι R A M n k w, matrixExtension_ι n k w⟩

end Unital

end periodicCyclicCohomology

end TauCeti
