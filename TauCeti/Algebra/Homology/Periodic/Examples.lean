/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.Periodic.DifferentialModule

/-!
# Acyclic differential modules need not be contractible

Over the dual numbers over any field `k`, multiplication by `ε` gives a differential module whose
one-periodic complex is exact and whose underlying module is free. No linear homotopy contracts
the differential. This example separates acyclicity from contractibility at the boundary between
homotopy and derived categories.

## References

* Luchezar L. Avramov, Ragnar-Olaf Buchweitz and Srikanth Iyengar, *Class and rank of differential
  modules*, Inventiones Mathematicae **169** (2007), 1–35, Sections 1–2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

/-- The algebra of dual numbers over `k`. -/
abbrev DualNumbers (k : Type*) := DualNumber k

variable {k : Type*} [Field k]

/-- The differential module on the regular dual-number module with differential multiplication
by `ε`. -/
def dualNumberDifferentialModule : DifferentialModule (ModuleCat (DualNumbers k)) where
  X := ModuleCat.of (DualNumbers k) (DualNumbers k)
  d := ModuleCat.ofHom
    (LinearMap.toSpanSingleton (DualNumbers k) (DualNumbers k) DualNumber.eps)
  d_comp_d := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_assoc]

/-- The underlying module of `dualNumberDifferentialModule` is projective. -/
theorem dualNumberDifferentialModule_projective :
    Projective (dualNumberDifferentialModule (k := k)).X := by
  -- Expose the regular module so its projectivity can be supplied by the free module instance.
  change CategoryTheory.Projective (ModuleCat.of (DualNumbers k) (DualNumbers k))
  let _ : Module.Projective (DualNumbers k) (DualNumbers k) :=
    Module.Projective.of_basis (Module.Free.chooseBasis (DualNumbers k) (DualNumbers k))
  exact inferInstance

/-- The one-periodic complex associated to multiplication by `ε` on the dual numbers. -/
abbrev dualNumberPeriodicComplex :=
  (DifferentialModule.toOnePeriodicComplex (ModuleCat (DualNumbers k))).obj
    dualNumberDifferentialModule

private theorem dualNumber_mul_eps_exact :
    Function.Exact
      (LinearMap.toSpanSingleton (DualNumbers k) (DualNumbers k) DualNumber.eps)
      (LinearMap.toSpanSingleton (DualNumbers k) (DualNumbers k) DualNumber.eps) := by
  intro x
  constructor
  · intro hx
    have hx' : x.fst = 0 := by
      have h := congrArg TrivSqZeroExt.snd hx
      simpa [LinearMap.toSpanSingleton_apply] using h
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x, hx']
    simp [LinearMap.toSpanSingleton_apply, DualNumber.inr_eq_smul_eps,
      ← TrivSqZeroExt.inl_mul_eq_smul]
  · rintro ⟨y, rfl⟩
    simp [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_assoc]

/-- The one-periodic complex of the dual-number differential module is acyclic. -/
theorem dualNumberPeriodicComplex_acyclic :
    (dualNumberPeriodicComplex (k := k)).Acyclic := by
  intro i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hprev : (ComplexShape.up (ZMod 1)).prev 0 = 0 := Subsingleton.elim _ _
  have hnext : (ComplexShape.up (ZMod 1)).next 0 = 0 := Subsingleton.elim _ _
  rw [HomologicalComplex.exactAt_iff' _ 0 0 0 hprev hnext,
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact (dualNumber_mul_eps_exact x).mp hx

/-- Multiplication by `ε` on the regular module admits no contracting homotopy: there is no
linear map `h` with `d h + h d = 1`. -/
theorem dualNumberDifferentialModule_not_contractible :
    ¬ ∃ h : (DualNumbers k) →ₗ[DualNumbers k] (DualNumbers k),
      LinearMap.id =
        (LinearMap.toSpanSingleton (DualNumbers k) (DualNumbers k) DualNumber.eps).comp h +
          h.comp (LinearMap.toSpanSingleton (DualNumbers k) (DualNumbers k) DualNumber.eps) := by
  rintro ⟨h, hh⟩
  have hone := congrArg (fun f : (DualNumbers k) →ₗ[DualNumbers k] (DualNumbers k) => f 1) hh
  have hone' : (1 : DualNumbers k) = h DualNumber.eps + h DualNumber.eps := by
    simpa [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply] using hone
  have hlin : h DualNumber.eps = (DualNumber.eps : DualNumbers k) • h 1 := by
    simpa [smul_eq_mul] using map_smul h (DualNumber.eps : DualNumbers k) (1 : DualNumbers k)
  have hfst := congrArg TrivSqZeroExt.fst hone'
  rw [hlin] at hfst
  -- The scalar action on `h 1` is multiplication in the dual-number ring.
  change (1 : k) = TrivSqZeroExt.fst
    (DualNumber.eps * h 1 + DualNumber.eps * h 1) at hfst
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul,
    DualNumber.fst_eps, zero_mul] at hfst
  rw [zero_add] at hfst
  exact one_ne_zero hfst

end TauCeti
