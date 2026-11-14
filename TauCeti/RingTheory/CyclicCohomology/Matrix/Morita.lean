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

For an algebra `A` over a commutative ring `R`, an `R`-module `M` of coefficients, and a finite
index type `ι`, the generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`) commutes
with all four operators `b`, `b'`, `1 - λ`, and `N` of Connes' cyclic bicomplex. Extending total
cochains componentwise across rows therefore defines a cochain map on the total cyclic bicomplex
and an induced `R`-linear map `TauCeti.cyclicTotalHomologyMatrixExtension` on total cohomology
`Hᵐ(Tot)`, compatible with the operators `I`, `B`, and `S` of the SBI exact sequence.

When `A` is unital and `ι` is nonempty, `TauCeti.hochschildCohomology.bijective_matrixExtension`
shows that matrix extension is bijective on Hochschild cohomology `HHᵐ(A, Hom_R(A, M))` in every
degree. Induction on `m` along the SBI exact sequence of the cyclic bicomplex
(`TauCeti.RingTheory.CyclicCohomology.ExactSequence`) via the four and five lemmas then proves
that `TauCeti.cyclicTotalHomologyMatrixExtension` is bijective in every degree over an arbitrary
commutative ring `R` (`TauCeti.bijective_cyclicTotalHomologyMatrixExtension`).

Passing to the direct limit along `S` yields matrix Morita invariance of periodic cyclic
cohomology `HPⁿ(A; M)` over every commutative ring `R`
(`TauCeti.periodicCyclicCohomology.bijective_matrixExtension`). Whenever `1, 2, …, n` are
invertible in `R` — in particular over any `ℚ`-algebra — Connes' cyclic cochain complex is
quasi-isomorphic to the total cyclic bicomplex (`TauCeti.quasiIsoAt_cyclicCochainComplexToTotal`),
giving matrix Morita invariance of cyclic cohomology `HCⁿ(A; M)`
(`TauCeti.cyclicCohomology.bijective_matrixExtension`).

## Main definitions

* `TauCeti.matrixCyclicTotalCochainExtension`: rowwise extension of total cochains of the cyclic
  bicomplex from `A` to `Matrix ι ι A`.
* `TauCeti.cyclicTotalHomologyMatrixExtension`,
  `TauCeti.cyclicTotalHomologyMatrixExtensionEquiv`: the induced map and Morita linear equivalence
  on total cyclic bicomplex cohomology `Hᵐ(Tot)`.
* `TauCeti.periodicCyclicCohomology.descLinearMap`: universe-polymorphic linear descent out of
  periodic cyclic cohomology `HPⁿ(A; M)`.
* `TauCeti.periodicCyclicCohomology.matrixExtension`,
  `TauCeti.periodicCyclicCohomology.matrixExtensionEquiv`: the induced map and Morita linear
  equivalence on periodic cyclic cohomology `HPⁿ(A; M)`.
* `TauCeti.cyclicCohomology.matrixExtensionEquiv`: the Morita linear equivalence on cyclic
  cohomology `HCⁿ(A; M)` over a `ℚ`-algebra.

## Main results

* `TauCeti.cyclicTotalDifferential_matrixCyclicTotalCochainExtension`: rowwise matrix extension of
  total cochains commutes with the total differential `D = d_h + d_v`.
* `TauCeti.bijective_cyclicTotalHomologyMatrixExtension`: matrix Morita invariance of `Hᵐ(Tot)`
  over any commutative ring `R`.
* `TauCeti.periodicCyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of
  `HPⁿ(A; M)` over any commutative ring `R`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension_of_isUnit`: matrix Morita invariance of
  `HCⁿ(A; M)` whenever `1, 2, …, n` are invertible in `R`.
* `TauCeti.cyclicCohomology.bijective_matrixExtension`: matrix Morita invariance of `HCⁿ(A; M)`
  over a `ℚ`-algebra (Connes 1985, Part II, Corollary 24).

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II,
  Corollary 24, p. 113.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.2, Theorem 2.2.15.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

/-! ### Rowwise matrix extension on the cyclic bicomplex -/

section BicomplexCochains

section Horizontal

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommGroup M] [Module R M]

/-- Matrix cochain extension commutes with the horizontal differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexHorizontal (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι q (cyclicBicomplexHorizontal R A M p q φ) =
      cyclicBicomplexHorizontal R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexHorizontal_of_even hp, cyclicBicomplexHorizontal_of_even hp,
      LinearMap.sub_apply, LinearMap.sub_apply, map_sub, one_apply_eq_self, one_apply_eq_self,
      matrixCochainExtension_cyclicOperator]
  · rw [cyclicBicomplexHorizontal_of_odd hp, cyclicBicomplexHorizontal_of_odd hp,
      matrixCochainExtension_cyclicNorm]

/-- Rowwise extension of degree-`m` total cochains of the cyclic bicomplex from `A` to
`Matrix ι ι A`. -/
def matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R (Matrix ι ι A) M m :=
  LinearMap.codRestrict _
    (LinearMap.pi fun q ↦
      matrixCochainExtension ι q ∘ₗ LinearMap.proj q ∘ₗ (cyclicTotalCochains R A M m).subtype)
    fun x ↦ by
      rw [mem_cyclicTotalCochains_iff]
      intro q hq
      simp [coe_cyclicTotalCochains_apply_of_lt x hq]

/-- In row `q`, the extended total cochain applies `matrixCochainExtension ι q` to row `q`. -/
@[simp]
theorem coe_matrixCyclicTotalCochainExtension_apply (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (matrixCyclicTotalCochainExtension ι m x).1 q = matrixCochainExtension ι q (x.1 q) :=
  (rfl)

/-- Rowwise matrix extension commutes with the inclusion of cyclic cochains into column zero. -/
theorem matrixCyclicTotalCochainExtension_cyclicCochainsToTotal (ι : Type*) [Fintype ι] {m : ℕ}
    (φ : cyclicCochains R A M m) :
    matrixCyclicTotalCochainExtension ι m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R (Matrix ι ι A) M m (matrixCyclicCochainExtension ι m φ) := by
  apply Subtype.ext
  funext q
  simp only [coe_matrixCyclicTotalCochainExtension_apply, coe_cyclicCochainsToTotal_apply]
  by_cases hq : q = m
  · subst hq
    simp
  · rw [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne hq, map_zero]

/-- Rowwise matrix extension commutes with the periodicity shift on total cochains. -/
theorem matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    matrixCyclicTotalCochainExtension ι (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) := by
  apply Subtype.ext
  funext q
  simp

/-- Rowwise matrix extension commutes with projection onto column zero. -/
theorem cyclicTotalToHochschild_matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R (Matrix ι ι A) M m (matrixCyclicTotalCochainExtension ι m x) =
      matrixCochainExtension ι m (cyclicTotalToHochschild R A M m x) := by
  rw [cyclicTotalToHochschild_apply, cyclicTotalToHochschild_apply,
    coe_matrixCyclicTotalCochainExtension_apply]

end Horizontal

section Vertical

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix cochain extension commutes with the vertical differential of the cyclic bicomplex. -/
theorem matrixCochainExtension_cyclicBicomplexVertical (ι : Type*) [Fintype ι] (p q : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    matrixCochainExtension ι (q + 1) (cyclicBicomplexVertical R A M p q φ) =
      cyclicBicomplexVertical R (Matrix ι ι A) M p q (matrixCochainExtension ι q φ) := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexVertical_of_even hp, cyclicBicomplexVertical_of_even hp,
      matrixCochainExtension_hochschildCoboundary]
  · rw [cyclicBicomplexVertical_of_odd hp, cyclicBicomplexVertical_of_odd hp,
      LinearMap.neg_apply, LinearMap.neg_apply, map_neg, matrixCochainExtension_barCoboundary]

/-- Rowwise matrix extension of total cochains commutes with the total differential `D`. -/
theorem cyclicTotalDifferential_matrixCyclicTotalCochainExtension (ι : Type*) [Fintype ι] {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
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

end Vertical

end BicomplexCochains

/-! ### Induced map and SBI naturality on total cyclic bicomplex cohomology -/

section TotalCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Rowwise matrix extension maps total cocycles to total cocycles. -/
theorem matrixCyclicTotalCochainExtension_mem_ker
    (ι : Type*) [Fintype ι] {m : ℕ} (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    matrixCyclicTotalCochainExtension ι m x.1 ∈
      LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m) := by
  rw [LinearMap.mem_ker, cyclicTotalDifferential_matrixCyclicTotalCochainExtension,
    LinearMap.mem_ker.1 x.2, map_zero]

variable (M) in
/-- The `R`-linear map `Hᵐ(Tot(A)) → Hᵐ(Tot(Matrix ι ι A))` on the cohomology of the total cyclic
bicomplex induced by rowwise matrix cochain extension. -/
def cyclicTotalHomologyMatrixExtension (ι : Type*) [Fintype ι] (m : ℕ) :
    (cyclicTotalComplex R A M).homology m →ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  (cyclicTotalHomologyMk R A M m).liftOfSurjective (cyclicTotalHomologyMk_surjective m)
    ⟨cyclicTotalHomologyMk R (Matrix ι ι A) M m ∘ₗ
        LinearMap.codRestrict (LinearMap.ker (cyclicTotalDifferential R (Matrix ι ι A) M m))
          (matrixCyclicTotalCochainExtension ι m ∘ₗ
            (LinearMap.ker (cyclicTotalDifferential R A M m)).subtype)
          (fun x ↦ matrixCyclicTotalCochainExtension_mem_ker ι x),
      fun x hx ↦ by
        rw [LinearMap.mem_ker] at hx ⊢
        simp only [LinearMap.comp_apply]
        cases m with
        | zero =>
          rw [cyclicTotalHomologyMk_zero_eq_zero_iff] at hx ⊢
          subst hx
          ext1
          exact map_zero _
        | succ n =>
          obtain ⟨w, hw⟩ := (cyclicTotalHomologyMk_succ_eq_zero_iff x).1 hx
          refine (cyclicTotalHomologyMk_succ_eq_zero_iff _).2
            ⟨matrixCyclicTotalCochainExtension ι n w, ?_⟩
          rw [cyclicTotalDifferential_matrixCyclicTotalCochainExtension, hw]
          rfl⟩

/-- Matrix extension on `Hᵐ(Tot)` sends the class of a total cocycle `x` to the class of its
rowwise matrix extension. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtension_mk
    (ι : Type*) [Fintype ι] {m : ℕ} (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyMk R A M m x) =
      cyclicTotalHomologyMk R (Matrix ι ι A) M m
        ⟨matrixCyclicTotalCochainExtension ι m x.1,
          matrixCyclicTotalCochainExtension_mem_ker ι x⟩ := by
  simp only [cyclicTotalHomologyMatrixExtension, LinearMap.equivOfSurjective_apply,
    LinearMap.comp_apply]
  rfl

/-- Matrix extension on `Hᵐ(Tot)` commutes with the projection `I : Hᵐ(Tot) → HHᵐ` onto column
zero. -/
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      hochschildCohomology.matrixExtension M ι m
        (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  rw [cyclicTotalHomologyMatrixExtension_mk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
    hochschildCohomology.matrixExtension_mk]
  congr 1

/-- Matrix extension on `Hᵐ(Tot)` commutes with the bicomplex periodicity map
`S : Hᵐ(Tot) → Hᵐ⁺²(Tot)`. -/
theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (m : ℕ) (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M m
        (cyclicTotalHomologyMatrixExtension M ι m c) =
      cyclicTotalHomologyMatrixExtension M ι (m + 2)
        (cyclicTotalHomologyPeriodicity R A M m c) := by
  obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective m c
  rw [cyclicTotalHomologyMatrixExtension_mk, cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk,
    cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk, cyclicTotalHomologyMatrixExtension_mk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicTotalPeriodicity ι x.1).symm

/-- Matrix extension on `Hᵐ(Tot)` commutes with every transition map `S^(j-i)` of the periodic
direct system. -/
theorem cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension
    (ι : Type*) [Fintype ι] (n : ℕ) {i j : ℕ}
    (h : i ≤ j) (c : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    cyclicTotalHomologyPeriodicTransition R (Matrix ι ι A) M n h
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * i) c) =
      cyclicTotalHomologyMatrixExtension M ι (n + 2 * j)
        (cyclicTotalHomologyPeriodicTransition R A M n h c) := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ← cyclicTotalHomologyPeriodicTransition_comp R (Matrix ι ι A) M n hij (Nat.le_add_right j 1),
      ModuleCat.comp_apply, ModuleCat.comp_apply, cyclicTotalHomologyPeriodicTransition_succ,
      cyclicTotalHomologyPeriodicTransition_succ, ih,
      cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension]
    rfl

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Matrix extension on cyclic cohomology commutes with `I : HCⁿ(A; M) → HHⁿ(A, Hom_R(A, M))`. -/
theorem cyclicCohomology.toHochschild_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (c : cyclicCohomology R A M n) :
    cyclicCohomology.toHochschild R (Matrix ι ι A) M n
        (cyclicCohomology.matrixExtension M ι n c) =
      hochschildCohomology.matrixExtension M ι n (cyclicCohomology.toHochschild R A M n c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M n c
  rw [cyclicCohomology.matrixExtension_mk, cyclicCohomology.toHochschild_mk,
    cyclicCohomology.toHochschild_mk, hochschildCohomology.matrixExtension_mk]
  congr 1
  apply Subtype.ext
  simpa only [Subtype.coe_mk] using coe_matrixCyclicCochainExtension_apply ι n φ.1

/-- Matrix extension on cyclic cohomology commutes with Connes' operator
`B : HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)`. -/
theorem cyclicCohomology.matrixExtension_connesB (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (c : hochschildCohomology R A M (n + 1)) :
    cyclicCohomology.matrixExtension M ι n (hochschildCohomology.connesB R A M n c) =
      hochschildCohomology.connesB R (Matrix ι ι A) M n
        (hochschildCohomology.matrixExtension M ι (n + 1) c) := by
  obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M (n + 1) c
  rw [hochschildCohomology.connesB_mk, cyclicCohomology.matrixExtension_mk,
    hochschildCohomology.matrixExtension_mk, hochschildCohomology.connesB_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  simpa only [Subtype.coe_mk, coe_matrixCyclicCochainExtension_apply] using
    matrixCochainExtension_connesB ι n φ.1

/-- Matrix extension commutes with the inclusion of cyclic cohomology into total bicomplex
cohomology. -/
theorem cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal
    (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) (c : cyclicCohomology R A M n) :
    cyclicTotalHomologyMatrixExtension M ι n
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n c) =
      HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n
        (cyclicCohomology.matrixExtension M ι n c) := by
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R A M n c
  rw [homologyMap_cyclicCochainComplexToTotal_mk, cyclicTotalHomologyMatrixExtension_mk,
    cyclicCohomology.matrixExtension_mk, homologyMap_cyclicCochainComplexToTotal_mk]
  congr 1
  exact Subtype.ext (matrixCyclicTotalCochainExtension_cyclicCochainsToTotal ι φ.1)

/-- Matrix extension on `Hᵐ(Tot)` commutes with Connes' connecting map
`B : HHᵐ⁺¹(A, Hom_R(A, M)) → Hᵐ(Tot)`. -/
theorem cyclicTotalHomologyConnesB_matrixExtension (ι : Type*) [Fintype ι] [DecidableEq ι]
    (m : ℕ) (c : hochschildCohomology R A M (m + 1)) :
    cyclicTotalHomologyConnesB R (Matrix ι ι A) M m
        (hochschildCohomology.matrixExtension M ι (m + 1) c) =
      cyclicTotalHomologyMatrixExtension M ι m (cyclicTotalHomologyConnesB R A M m c) := by
  rw [cyclicTotalHomologyConnesB_def, cyclicTotalHomologyConnesB_def, ModuleCat.comp_apply,
    ModuleCat.comp_apply,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    cyclicCohomology.matrixExtension_connesB]

/-! ### Morita invariance on total cyclic bicomplex cohomology -/

private theorem bijective_of_comp_bijective {α β γ δ : Type*} {f : α → β} {g : β → δ}
    {h : α → γ} {k : γ → δ} (hcomm : ∀ x, k (h x) = g (f x)) (hf : Function.Bijective f)
    (hg : Function.Bijective g) (hk : Function.Bijective k) :
    Function.Bijective h := by
  have hkh : Function.Bijective (k ∘ h) := by
    have heq : k ∘ h = g ∘ f := funext hcomm
    rw [heq]
    exact hg.comp hf
  exact (Function.Bijective.of_comp_iff' hk h).1 hkh

/-- **Matrix Morita invariance of total cyclic bicomplex cohomology.** For a unital algebra `A` over
any commutative ring `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`,
rowwise matrix extension induces a bijection `Hᵐ(Tot(A)) → Hᵐ(Tot(Matrix ι ι A))` in every degree
`m`. -/
theorem bijective_cyclicTotalHomologyMatrixExtension {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A] {M : Type*} [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    Function.Bijective (cyclicTotalHomologyMatrixExtension (R := R) (A := A) M ι m) := by
  classical
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    match m with
    | 0 =>
      have hI_A : Function.Bijective
          (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) 0) :=
        (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
      have hI_Mat : Function.Bijective
          (HomologicalComplex.homologyMap
            (cyclicTotalComplexToHochschild R (Matrix ι ι A) M) 0) :=
        (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
      exact bijective_of_comp_bijective
        (homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMatrixExtension ι 0)
        hI_A (hochschildCohomology.bijective_matrixExtension ι 0) hI_Mat
    | 1 =>
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
        (LinearMap.ext (cyclicTotalHomologyConnesB_matrixExtension ι 0))
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
        (exact_homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyConnesB 0)
        (hochschildCohomology.bijective_matrixExtension ι 1)
        (ih 0 (by omega)).1
        injective_homologyMap_cyclicTotalComplexToHochschild_one
        injective_homologyMap_cyclicTotalComplexToHochschild_one
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
        (hochschildCohomology.bijective_matrixExtension ι (m + 1)).2
        (ih m (by omega))
        (hochschildCohomology.bijective_matrixExtension ι (m + 2))
        (ih (m + 1) (by omega)).1

variable (M) in
/-- **Matrix Morita linear equivalence on total cyclic bicomplex cohomology.** -/
def cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    (cyclicTotalComplex R A M).homology m ≃ₗ[R]
      (cyclicTotalComplex R (Matrix ι ι A) M).homology m :=
  LinearEquiv.ofBijective (cyclicTotalHomologyMatrixExtension M ι m)
    (bijective_cyclicTotalHomologyMatrixExtension ι m)

variable (M) in
/-- Coercing `cyclicTotalHomologyMatrixExtensionEquiv` to a linear map recovers
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem coe_cyclicTotalHomologyMatrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ) :
    (cyclicTotalHomologyMatrixExtensionEquiv (R := R) (A := A) M ι m :
      (cyclicTotalComplex R A M).homology m →ₗ[R]
        (cyclicTotalComplex R (Matrix ι ι A) M).homology m) =
      cyclicTotalHomologyMatrixExtension M ι m :=
  (rfl)

variable (M) in
/-- Applying `cyclicTotalHomologyMatrixExtensionEquiv` agrees with
`cyclicTotalHomologyMatrixExtension`. -/
@[simp]
theorem cyclicTotalHomologyMatrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (m : ℕ)
    (c : (cyclicTotalComplex R A M).homology m) :
    cyclicTotalHomologyMatrixExtensionEquiv M ι m c =
      cyclicTotalHomologyMatrixExtension M ι m c :=
  (rfl)

end Unital

end TotalCohomology

/-! ### Matrix Morita invariance of periodic cyclic cohomology -/

namespace periodicCyclicCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

private theorem map_periodicTransition_of_periodicity {N : Type*} [AddCommGroup N] [Module R N]
    {n : ℕ} (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ k x, g (k + 1) (cyclicTotalHomologyPeriodicity R A M (n + 2 * k) x) = g k x)
    {i j : ℕ} (h : i ≤ j) (x : (cyclicTotalComplex R A M).homology (n + 2 * i)) :
    g j (cyclicTotalHomologyPeriodicTransition R A M n h x) = g i x := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [← cyclicTotalHomologyPeriodicTransition_comp R A M n hij (Nat.le_add_right j 1),
      ModuleCat.comp_apply, cyclicTotalHomologyPeriodicTransition_succ, hg, ih]

private theorem eq_of_ι_eq {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ k x, g (k + 1) (cyclicTotalHomologyPeriodicity R A M (n + 2 * k) x) = g k x)
    {k₁ k₂ : ℕ} {y₁ : (cyclicTotalComplex R A M).homology (n + 2 * k₁)}
    {y₂ : (cyclicTotalComplex R A M).homology (n + 2 * k₂)}
    (h : periodicCyclicCohomology.ι R A M n k₁ y₁ = periodicCyclicCohomology.ι R A M n k₂ y₂) :
    g k₁ y₁ = g k₂ y₂ := by
  have hsub :
      periodicCyclicCohomology.ι R A M n (max k₁ k₂)
        (cyclicTotalHomologyPeriodicTransition R A M n (le_max_left k₁ k₂) y₁ -
          cyclicTotalHomologyPeriodicTransition R A M n (le_max_right k₁ k₂) y₂) = 0 := by
    rw [map_sub, cyclicTotalHomologyPeriodicTransition_ι_apply,
      cyclicTotalHomologyPeriodicTransition_ι_apply, h, sub_self]
  obtain ⟨j, hmj, hj⟩ := (ι_eq_zero_iff _).1 hsub
  rw [map_sub, sub_eq_zero, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    cyclicTotalHomologyPeriodicTransition_comp,
    cyclicTotalHomologyPeriodicTransition_comp] at hj
  rw [← map_periodicTransition_of_periodicity g hg ((le_max_left k₁ k₂).trans hmj) y₁,
    ← map_periodicTransition_of_periodicity g hg ((le_max_right k₁ k₂).trans hmj) y₂, hj]

/-- Universe-polymorphic universal property of periodic cyclic cohomology: a family of `R`-linear
maps out of the stages `H^(n+2k)(Tot)` into an arbitrary `R`-module `N` compatible with `S`
factors through `HPⁿ(A; M)`. -/
def descLinearMap {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ k x, g (k + 1) (cyclicTotalHomologyPeriodicity R A M (n + 2 * k) x) = g k x) :
    periodicCyclicCohomology R A M n →ₗ[R] N where
  toFun z := g (exists_ι_eq z).choose (exists_ι_eq z).choose_spec.choose
  map_add' z₁ z₂ := by
    obtain ⟨k₁, y₁, rfl⟩ := exists_ι_eq z₁
    obtain ⟨k₂, y₂, rfl⟩ := exists_ι_eq z₂
    have h₁ := eq_of_ι_eq g hg
      (exists_ι_eq (periodicCyclicCohomology.ι R A M n k₁ y₁)).choose_spec.choose_spec
    have h₂ := eq_of_ι_eq g hg
      (exists_ι_eq (periodicCyclicCohomology.ι R A M n k₂ y₂)).choose_spec.choose_spec
    have h₁₂ :
        periodicCyclicCohomology.ι R A M n (max k₁ k₂)
          (cyclicTotalHomologyPeriodicTransition R A M n (le_max_left k₁ k₂) y₁ +
            cyclicTotalHomologyPeriodicTransition R A M n (le_max_right k₁ k₂) y₂) =
          periodicCyclicCohomology.ι R A M n k₁ y₁ +
            periodicCyclicCohomology.ι R A M n k₂ y₂ := by
      rw [map_add, cyclicTotalHomologyPeriodicTransition_ι_apply,
        cyclicTotalHomologyPeriodicTransition_ι_apply]
    rw [h₁, h₂,
      eq_of_ι_eq g hg
        ((exists_ι_eq
          (periodicCyclicCohomology.ι R A M n k₁ y₁ +
            periodicCyclicCohomology.ι R A M n k₂ y₂)).choose_spec.choose_spec.trans h₁₂.symm),
      map_add, map_periodicTransition_of_periodicity g hg,
      map_periodicTransition_of_periodicity g hg]
  map_smul' r z := by
    obtain ⟨k, y, rfl⟩ := exists_ι_eq z
    have h₁ := eq_of_ι_eq g hg
      (exists_ι_eq (periodicCyclicCohomology.ι R A M n k y)).choose_spec.choose_spec
    have hr :
        periodicCyclicCohomology.ι R A M n k (r • y) =
          r • periodicCyclicCohomology.ι R A M n k y :=
      map_smul _ r y
    rw [RingHom.id_apply, h₁,
      eq_of_ι_eq g hg
        ((exists_ι_eq
          (r • periodicCyclicCohomology.ι R A M n k y)).choose_spec.choose_spec.trans hr.symm),
      map_smul]

/-- `descLinearMap` restricts to the given linear map on each stage `H^(n+2k)(Tot)`. -/
@[simp]
theorem descLinearMap_ι {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    (g : ∀ k, (cyclicTotalComplex R A M).homology (n + 2 * k) →ₗ[R] N)
    (hg : ∀ k x, g (k + 1) (cyclicTotalHomologyPeriodicity R A M (n + 2 * k) x) = g k x)
    (k : ℕ) (x : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    descLinearMap g hg (periodicCyclicCohomology.ι R A M n k x) = g k x :=
  eq_of_ι_eq g hg (exists_ι_eq (periodicCyclicCohomology.ι R A M n k x)).choose_spec.choose_spec

/-- Two `R`-linear maps out of `HPⁿ(A; M)` agree once they agree on every stage `ι R A M n k`. -/
@[ext]
theorem linearMap_ext {N : Type*} [AddCommGroup N] [Module R N] {n : ℕ}
    {f₁ f₂ : periodicCyclicCohomology R A M n →ₗ[R] N}
    (h : ∀ k x, f₁ (periodicCyclicCohomology.ι R A M n k x) =
      f₂ (periodicCyclicCohomology.ι R A M n k x)) : f₁ = f₂ :=
  LinearMap.ext fun z ↦ by
    obtain ⟨k, x, rfl⟩ := exists_ι_eq z
    exact h k x

variable (M) in
/-- The `R`-linear map `HPⁿ(A; M) → HPⁿ(Matrix ι ι A; M)` on periodic cyclic cohomology induced by
rowwise matrix extension on the cyclic bicomplex. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  descLinearMap
    (fun k ↦
      (periodicCyclicCohomology.ι R (Matrix ι ι A) M n k).hom ∘ₗ
        cyclicTotalHomologyMatrixExtension M ι (n + 2 * k))
    fun k x ↦ by
      change periodicCyclicCohomology.ι R (Matrix ι ι A) M n (k + 1)
          (cyclicTotalHomologyMatrixExtension M ι (n + 2 * (k + 1))
            (cyclicTotalHomologyPeriodicity R A M (n + 2 * k) x)) =
        periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
          (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) x)
      have hS :
          cyclicTotalHomologyMatrixExtension M ι (n + 2 * (k + 1))
              (cyclicTotalHomologyPeriodicity R A M (n + 2 * k) x) =
            cyclicTotalHomologyPeriodicity R (Matrix ι ι A) M (n + 2 * k)
              (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) x) :=
        (cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension ι (n + 2 * k) x).symm
      rw [hS, ← ModuleCat.comp_apply, cyclicTotalHomologyPeriodicity_ι]

/-- Matrix extension on `HPⁿ` commutes with the canonical stage maps `ι`. -/
@[simp]
theorem matrixExtension_ι (ι : Type*) [Fintype ι] (n k : ℕ)
    (x : (cyclicTotalComplex R A M).homology (n + 2 * k)) :
    matrixExtension M ι n (periodicCyclicCohomology.ι R A M n k x) =
      periodicCyclicCohomology.ι R (Matrix ι ι A) M n k
        (cyclicTotalHomologyMatrixExtension M ι (n + 2 * k) x) :=
  descLinearMap_ι _ _ k x

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Over a `ℚ`-algebra, matrix extension on `HPⁿ` commutes with the normalized stage maps
`fromCyclicCohomology` from `HC^(n+2k)`. -/
theorem matrixExtension_fromCyclicCohomology [Algebra ℚ R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n k : ℕ) (c : cyclicCohomology R A M (n + 2 * k)) :
    matrixExtension M ι n (fromCyclicCohomology R A M n k c) =
      fromCyclicCohomology R (Matrix ι ι A) M n k
        (cyclicCohomology.matrixExtension M ι (n + 2 * k) c) := by
  rw [fromCyclicCohomology_def, fromCyclicCohomology_def]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, matrixExtension_ι,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]

/-- **Matrix Morita invariance of periodic cyclic cohomology.** For a unital algebra `A` over any
commutative ring `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`,
matrix extension induces a bijection `HPⁿ(A; M) → HPⁿ(Matrix ι ι A; M)`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨k, y, rfl⟩ := exists_ι_eq x
    rw [matrixExtension_ι, ι_eq_zero_iff] at hx
    obtain ⟨j, hkj, hj⟩ := hx
    rw [cyclicTotalHomologyPeriodicTransition_cyclicTotalHomologyMatrixExtension] at hj
    exact (ι_eq_zero_iff y).2 ⟨j, hkj,
      (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * j)).1
        (hj.trans (map_zero _).symm)⟩
  · obtain ⟨k, w, rfl⟩ := exists_ι_eq z
    obtain ⟨y, rfl⟩ := (bijective_cyclicTotalHomologyMatrixExtension ι (n + 2 * k)).2 w
    exact ⟨periodicCyclicCohomology.ι R A M n k y, matrixExtension_ι ι n k y⟩

variable (M) in
/-- **Matrix Morita linear equivalence on periodic cyclic cohomology.** -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    periodicCyclicCohomology R A M n ≃ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

variable (M) in
/-- Coercing `periodicCyclicCohomology.matrixExtensionEquiv` to a linear map recovers
`periodicCyclicCohomology.matrixExtension`. -/
@[simp]
theorem coe_matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      periodicCyclicCohomology R A M n →ₗ[R] periodicCyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

variable (M) in
/-- Applying `periodicCyclicCohomology.matrixExtensionEquiv` agrees with
`periodicCyclicCohomology.matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : periodicCyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

end Unital

end periodicCyclicCohomology

/-! ### Matrix Morita invariance of cyclic cohomology -/

namespace cyclicCohomology

/-- Over a `ℚ`-algebra, matrix extension on cyclic cohomology commutes with Connes' periodicity
operator `S : HCⁿ(A; M) → HCⁿ⁺²(A; M)`. -/
theorem matrixExtension_periodicity {R A M : Type*} [CommRing R] [Algebra ℚ R]
    [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) (c : cyclicCohomology R A M n) :
    matrixExtension M ι (n + 2) (periodicity R A M n c) =
      periodicity R (Matrix ι ι A) M n (matrixExtension M ι n c) := by
  apply (bijective_homologyMap_cyclicCochainComplexToTotal R (Matrix ι ι A) M (n + 2)).1
  rw [← cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal,
    periodicity_comp_homologyMap_cyclicCochainComplexToTotal_apply,
    periodicity_comp_homologyMap_cyclicCochainComplexToTotal_apply, map_neg, map_smul,
    ← cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMatrixExtension,
    cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal]

/-- **Matrix Morita invariance of cyclic cohomology under invertibility of `1, …, n`.** For a
unital algebra `A` over a commutative ring `R` in which `q + 1` is a unit for every `q < n`,
coefficients in an `R`-module `M`, and a nonempty finite index type `ι`, the matrix extension
`φ ↦ φ#Tr` induces a bijection `HCⁿ(A; M) → HCⁿ(Matrix ι ι A; M)`. -/
theorem bijective_matrixExtension_of_isUnit {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A] {M : Type*} [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  have hA : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_cyclicCochainComplexToTotal R A M n hR))
  have hMat : Function.Bijective
      (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R (Matrix ι ι A) M) n) :=
    (ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_cyclicCochainComplexToTotal R (Matrix ι ι A) M n hR))
  exact bijective_of_comp_bijective
    (fun c ↦
      (cyclicTotalHomologyMatrixExtension_homologyMap_cyclicCochainComplexToTotal ι n c).symm)
    hA (bijective_cyclicTotalHomologyMatrixExtension ι n) hMat

/-- In degree zero, matrix extension `HC⁰(A; M) → HC⁰(Matrix ι ι A; M)` is bijective over every
commutative ring `R`: every `M`-valued trace on `Matrix ι ι A` is of the form `τ ∘ Matrix.trace`
for a unique `M`-valued trace `τ` on `A`. -/
theorem bijective_matrixExtension_zero {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A] {M : Type*} [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι 0) :=
  bijective_matrixExtension_of_isUnit ι 0 fun _ hq ↦ absurd hq (Nat.not_lt_zero _)

/-- **Matrix Morita invariance of cyclic cohomology.** For a unital algebra `A` over a commutative
`ℚ`-algebra `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`, the
generalized matrix trace `φ ↦ φ#Tr` induces a bijection `HCⁿ(A; M) → HCⁿ(Matrix ι ι A; M)` in
every degree `n`. -/
theorem bijective_matrixExtension {R : Type*} [CommRing R] [Algebra ℚ R]
    {A : Type*} [Ring A] [Algebra R A] {M : Type*} [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) :=
  bijective_matrixExtension_of_isUnit ι n fun q _ ↦
    by simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

/-- **Matrix Morita linear equivalence on cyclic cohomology.** -/
def matrixExtensionEquiv {R : Type*} [CommRing R] [Algebra ℚ R]
    {A : Type*} [Ring A] [Algebra R A] (M : Type*) [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    cyclicCohomology R A M n ≃ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Coercing `cyclicCohomology.matrixExtensionEquiv` to a linear map recovers
`cyclicCohomology.matrixExtension`. -/
@[simp]
theorem coe_matrixExtensionEquiv {R : Type*} [CommRing R] [Algebra ℚ R]
    {A : Type*} [Ring A] [Algebra R A] (M : Type*) [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

/-- Applying `cyclicCohomology.matrixExtensionEquiv` agrees with
`cyclicCohomology.matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply {R : Type*} [CommRing R] [Algebra ℚ R]
    {A : Type*} [Ring A] [Algebra R A] (M : Type*) [AddCommGroup M] [Module R M]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ)
    (c : cyclicCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

end cyclicCohomology

end TauCeti
