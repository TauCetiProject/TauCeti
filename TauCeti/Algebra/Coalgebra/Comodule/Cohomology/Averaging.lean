/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cohomology.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Cointegral
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.Algebra.HopfAlgebra.Integral.Sweedler

/-!
# Algebraic averaging on Hochschild cochains

Let `I : H →ₗ[R] R` be a left invariant integral on a bialgebra. Integrating out the last
variable of an `(n + 1)`-cochain, with sign `(-1)^(n + 1)`, gives a homotopy for multiplication
by `I 1` in positive degrees. When `I 1 = 1`, this gives a primitive for every positive-degree
cocycle. In degree zero the same identity involves averaging the coaction on the coefficients.
The equivalence to the fixed submodule in degree zero uses `Homotopy.mkCochainComplex`,
with the degree-zero maps assembled as in `Comodule.hochschildComplexCofreeHomotopyEquiv`.

Over a field, a linearly reductive bialgebra has Sweedler's normalized invariant integral.
Its Hochschild cohomology therefore vanishes in positive degrees for arbitrary comodules.
In degrees one and two the primitive solves the coboundary equations for conjugating sections
and splitting extensions by vector groups.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, §§4.7, 4.14–4.16.
* M. Sweedler, *Hopf Algebras*, Chapter XIV, for the invariant integral.
-/

public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Comodule.Cohomology

universe u v

variable {R : Type u} [CommRing R] {H : Type v} [Ring H] [Bialgebra R H]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Integration in the last variable of a Hochschild cochain, with the sign for a
degree-lowering homotopy. -/
def averagingHomotopy (I : H →ₗ[R] R) (n : ℕ) :
    cochains R H M (n + 1) →ₗ[R] cochains R H M n :=
  (-1 : R) ^ (n + 1) • LinearMap.tensorComponent I

/-- The signed integral sends `x ⊗ a` to the scalar multiple `(-1)^(n + 1) I(a) x`. -/
@[simp]
theorem averagingHomotopy_tmul (I : H →ₗ[R] R) (n : ℕ) (x : cochains R H M n) (a : H) :
    averagingHomotopy M I n (x ⊗ₜ[R] a) = (-1 : R) ^ (n + 1) • (I a • x) := by
  simp [averagingHomotopy]

variable [Comodule R H M]

/-- Integrating the last variable commutes with a morphism on the coefficient factor. -/
theorem averagingHomotopy_cochainsMap {N : Type v} [AddCommGroup N] [Module R N]
    [Comodule R H N] (f : Hom R H M N) (I : H →ₗ[R] R) (n : ℕ) (z : cochains R H M (n + 1)) :
    averagingHomotopy N I n (cochainsMap f (n + 1) z) =
      cochainsMap f n (averagingHomotopy M I n z) := by
  rw [cochainsMap_succ]
  simp [averagingHomotopy]

/-- In degree zero, the homotopy measures the difference between scalar multiplication by
`I 1` and the integral applied to the coaction. -/
theorem averagingHomotopy_d_zero (I : H →ₗ[R] R) (m : M) :
    averagingHomotopy M I 0 (d R H M 0 m) =
      I 1 • m - coactComponent (M := M) I m := by
  rw [d_zero_apply R H M m]
  simp [averagingHomotopy, coactComponent_apply]

/-- In positive degrees, integrating a coboundary and differentiating the integral sum to
multiplication by the mass of the integral. The normalization `I 1 = 1` gives a contraction. -/
theorem averagingHomotopy_d_add_d_averagingHomotopy {I : H →ₗ[R] R}
    (hI : I.IsLeftInvariantIntegral) (n : ℕ) (z : cochains R H M (n + 1)) :
    averagingHomotopy M I (n + 1) (d R H M (n + 1) z) +
      d R H M n (averagingHomotopy M I n z) = I 1 • z := by
  have hinv (a : H) : LinearMap.tensorComponent I (Coalgebra.comul a) = I a • (1 : H) := by
    simpa only [LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe]
      using LinearMap.isLeftInvariantIntegral_iff.mp hI a
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add, smul_add, add_add_add_comm] using congrArg₂ (· + ·) hx hy
  | tmul x a =>
    rw [d_succ_tmul]
    simp only [averagingHomotopy, LinearMap.smul_apply, map_add, map_smul, map_sub,
      LinearMap.tensorComponent_tmul, LinearMap.tensorComponent_assoc_symm,
      LinearMap.lTensor_tmul, hinv, TensorProduct.tmul_smul]
    rw [sub_self, zero_sub]
    rcases neg_one_pow_eq_or R n with h | h <;> simp [pow_succ, h]

/-- Integrating a cocycle gives a primitive of its multiple by `I 1`. For a normalized
integral this is a primitive of the original cocycle. -/
theorem d_averagingHomotopy_of_cocycle {I : H →ₗ[R] R} (hI : I.IsLeftInvariantIntegral)
    (n : ℕ) {z : cochains R H M (n + 1)} (hz : d R H M (n + 1) z = 0) :
    d R H M n (averagingHomotopy M I n z) = I 1 • z := by
  simpa [hz] using averagingHomotopy_d_add_d_averagingHomotopy M hI n z

/-- A left invariant integral of invertible mass makes the Hochschild complex of every comodule
exact in all positive degrees. -/
theorem exactAt_of_isLeftInvariantIntegral {I : H →ₗ[R] R} (hI : I.IsLeftInvariantIntegral)
    (h1 : IsUnit (I 1)) (n : ℕ) : (cochainComplex R H M).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [cochainComplex_d_succ]
  refine fun (z : cochains R H M (n + 1)) hz ↦ ?_
  obtain ⟨a, ha⟩ := h1
  refine ⟨(↑a⁻¹ : R) • averagingHomotopy M I n z, ?_⟩
  exact (map_smul (d R H M n) _ _).trans (by
    rw [d_averagingHomotopy_of_cocycle M hI n hz, ← ha, smul_smul, a.inv_mul, one_smul])

/-- A normalized left invariant integral retracts the Hochschild complex onto the fixed
submodule placed in degree zero. The projection in degree zero is the Reynolds operator. -/
def homotopyEquivFixed {I : H →ₗ[R] R} (hI : I.IsLeftInvariantIntegral) (h1 : I 1 = 1) :
    HomotopyEquiv (cochainComplex R H M)
      ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (fixedSubcomodule R H M))) := by
  let hP := (LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mp hI).isProj_coactComponent
    h1 M
  let p := (CochainComplex.toSingle₀Equiv (cochainComplex R H M) _).symm
    (ConcreteCategory.ofHom (C := ModuleCat R) (X := (cochainComplex R H M).X 0)
      (Y := ModuleCat.of R (fixedSubcomodule R H M)) hP.codRestrict)
  let i := (CochainComplex.fromSingle₀Equiv (cochainComplex R H M) _).symm
    ⟨ConcreteCategory.ofHom (C := ModuleCat R) (X := ModuleCat.of R (fixedSubcomodule R H M))
      (Y := (cochainComplex R H M).X 0) (fixedSubcomodule R H M).toSubmodule.subtype,
      by
        rw [cochainComplex_d_succ]
        exact ModuleCat.hom_ext (LinearMap.ext fun m ↦ d_zero_eq_zero_of_mem_fixedSubcomodule
          m.property)⟩
  refine ⟨p, i, Homotopy.symm (Homotopy.equivSubZero.symm ?_), Homotopy.ofEq ?_⟩
  · refine Homotopy.mkCochainComplex _ (fun n ↦ ConcreteCategory.ofHom (C := ModuleCat R)
      (X := (cochainComplex R H M).X (n + 1)) (Y := (cochainComplex R H M).X n)
      (averagingHomotopy M I n)) ?_ ?_
    · simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
        p, i, CochainComplex.toSingle₀Equiv_symm_apply_f_zero,
        CochainComplex.fromSingle₀Equiv_symm_apply_f_zero, cochainComplex_d_succ]
      apply ModuleCat.hom_ext
      ext (m : M)
      -- The bundled difference has degree-zero object K.X 0. Expose its value in M so
      -- that the projection lemma matches the codomain restriction.
      change m - (hP.codRestrict m : M) = averagingHomotopy M I 0 (d R H M 0 m)
      rw [LinearMap.IsProj.codRestrict_apply, averagingHomotopy_d_zero, h1, one_smul]
    · intro n
      simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
        p, CochainComplex.toSingle₀Equiv_symm_apply_f_succ, Limits.zero_comp, sub_zero,
        cochainComplex_d_succ]
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun (z : cochains R H M (n + 1)) ↦ ?_
      -- Rewrite the bundled maps on K.X (n + 1) as the linear maps on cochains
      -- appearing in the positive-degree identity.
      change z = averagingHomotopy M I (n + 1) (d R H M (n + 1) z) +
        d R H M n (averagingHomotopy M I n z)
      rw [averagingHomotopy_d_add_d_averagingHomotopy M hI, h1, one_smul]
  · apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, i, p,
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
      CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
    exact ModuleCat.hom_ext (LinearMap.ext hP.codRestrict_apply_cod)

/-- In degree zero the retraction is the Reynolds projection with codomain the invariants. -/
@[simp]
theorem homotopyEquivFixed_hom_f_zero {I : H →ₗ[R] R} (hI : I.IsLeftInvariantIntegral)
    (h1 : I 1 = 1) :
    (homotopyEquivFixed M hI h1).hom.f 0 =
      ConcreteCategory.ofHom (C := ModuleCat R) (X := (cochainComplex R H M).X 0)
        (Y := ModuleCat.of R (fixedSubcomodule R H M))
        (((LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mp hI).isProj_coactComponent
          h1 M).codRestrict) :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_zero _

/-- In degree zero the inverse is the inclusion of the fixed vectors. -/
@[simp]
theorem homotopyEquivFixed_inv_f_zero {I : H →ₗ[R] R} (hI : I.IsLeftInvariantIntegral)
    (h1 : I 1 = 1) :
    (homotopyEquivFixed M hI h1).inv.f 0 =
      ConcreteCategory.ofHom (C := ModuleCat R) (X := ModuleCat.of R (fixedSubcomodule R H M))
        (Y := (cochainComplex R H M).X 0) (fixedSubcomodule R H M).toSubmodule.subtype :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end TauCeti.Comodule.Cohomology

namespace TauCeti.Coalgebra.IsLinearlyReductive

open Comodule.Cohomology

/-- The positive-degree Hochschild cohomology of a linearly reductive bialgebra vanishes for
every coefficient comodule. -/
theorem isZero_cohomology_succ {k : Type u} [Field k] {H : Type v} [Ring H] [Bialgebra k H]
    (hH : IsLinearlyReductive.{u, v, u} k H) (M : Type v) [AddCommGroup M] [Module k M]
    [Comodule k H M] (n : ℕ) : Limits.IsZero (cohomology k H M (n + 1)) :=
  (exactAt_of_isLeftInvariantIntegral M
    (isLeftInvariantIntegral_sweedlerIntegral hH.sSup_simpleCoefficientSubmodules_eq_top)
    (by simp) n).isZero_homology

end TauCeti.Coalgebra.IsLinearlyReductive
