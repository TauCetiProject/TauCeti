/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.Algebra.MvPolynomial.Rename

/-!
# Modules over multivariate polynomial rings

This file records finiteness criteria for modules over multivariate polynomial rings:

* When every variable acts by zero, every polynomial acts through its constant coefficient, so a
  finitely generated `A[X_σ]`-module is finitely generated over `A`
  (`TauCeti.MvPolynomial.smul_eq_constantCoeff_smul`,
  `TauCeti.MvPolynomial.finite_of_forall_X_smul_eq_zero`).
* When variables outside the range of an injective renaming `f : σ → τ` act by zero, restricting
  scalars along `MvPolynomial.rename f` preserves finite generation
  (`TauCeti.MvPolynomial.moduleFinite_compHom_rename`,
  `TauCeti.MvPolynomial.moduleFinite_compHom_rename_castSucc`).

## Main results

* `TauCeti.MvPolynomial.smul_eq_constantCoeff_smul`: a polynomial acts through its constant
  coefficient.
* `TauCeti.MvPolynomial.finite_of_forall_X_smul_eq_zero`: a finitely generated module on which
  all variables act by zero is finitely generated over the coefficients.
* `TauCeti.MvPolynomial.moduleFinite_compHom_rename`: a finitely generated `MvPolynomial τ A`-module
  annihilated by every variable outside `Set.range f` (for injective `f : σ → τ`) is finitely
  generated over `MvPolynomial σ A` via `MvPolynomial.rename f`.
* `TauCeti.MvPolynomial.moduleFinite_compHom_rename_castSucc`: specialization to
  `Fin.castSucc : Fin e → Fin (e + 1)` when `X (Fin.last e)` annihilates the module.
-/

public section

open _root_.MvPolynomial

namespace TauCeti.MvPolynomial

section ZeroAction

variable {σ A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
  [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]

/-- A polynomial acts through its constant coefficient on a module on which every variable acts
by zero. -/
theorem smul_eq_constantCoeff_smul
    (h : ∀ (i : σ) (m : M), (X i : MvPolynomial σ A) • m = 0) {p : MvPolynomial σ A} (m : M) :
    p • m = constantCoeff p • m := by
  induction p using _root_.MvPolynomial.induction_on with
  | C a => rw [constantCoeff_C, ← algebraMap_eq, algebraMap_smul]
  | add p q hp hq => rw [add_smul, hp, hq, map_add, add_smul]
  | mul_X p i _ => rw [mul_smul, h, smul_zero, map_mul, constantCoeff_X, mul_zero, zero_smul]

/-- A finitely generated module over a polynomial ring on which every variable acts by zero is
finitely generated over the coefficients. -/
theorem finite_of_forall_X_smul_eq_zero [Module.Finite (MvPolynomial σ A) M]
    (h : ∀ (i : σ) (m : M), (X i : MvPolynomial σ A) • m = 0) : Module.Finite A M := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := MvPolynomial σ A) (M := M)
  refine ⟨⟨s, Submodule.eq_top_iff'.mpr fun m ↦ ?_⟩⟩
  have hm : m ∈ Submodule.span (MvPolynomial σ A) (s : Set M) := hs ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul p x _ hx =>
    rw [smul_eq_constantCoeff_smul h]
    exact Submodule.smul_mem _ _ hx

end ZeroAction

section Rename

/-- A finitely generated `MvPolynomial τ A`-module `N` annihilated by every variable outside the
range of an injective map `f : σ → τ` is finitely generated over `MvPolynomial σ A` via
`MvPolynomial.rename f`. -/
theorem moduleFinite_compHom_rename {A σ τ N : Type*} [CommSemiring A] [AddCommMonoid N]
    [Module (MvPolynomial τ A) N] [Module.Finite (MvPolynomial τ A) N]
    {f : σ → τ} (hf : Function.Injective f)
    (hkill : ∀ i ∉ Set.range f, ∀ z : N, (X i : MvPolynomial τ A) • z = 0) :
    let : Module (MvPolynomial σ A) N :=
      Module.compHom N (rename (R := A) f).toRingHom
    Module.Finite (MvPolynomial σ A) N := by
  classical
  let ι : MvPolynomial σ A →ₐ[A] MvPolynomial τ A := rename f
  let π : MvPolynomial τ A →ₐ[A] MvPolynomial σ A := killCompl hf
  let : Module (MvPolynomial σ A) N := Module.compHom N ι.toRingHom
  let : Algebra (MvPolynomial τ A) (MvPolynomial σ A) := π.toRingHom.toAlgebra
  have hact (p : MvPolynomial τ A) (z : N) : ι (π p) • z = p • z := by
    induction p using _root_.MvPolynomial.induction_on generalizing z with
    | C a => simp [ι, π]
    | add p q hp hq => simp [add_smul, hp, hq]
    | mul_X p i hp =>
      by_cases hi : i ∈ Set.range f
      · obtain ⟨j, rfl⟩ := hi
        rw [map_mul, map_mul, mul_smul, hp, mul_smul]
        simp only [ι, π]
        rw [← rename_X f j, killCompl_rename_app, rename_X]
      · rw [mul_smul, hkill i hi z, smul_zero, map_mul, map_mul]
        simp only [π]
        rw [killCompl_X_of_notMem_range hf hi, map_zero, mul_zero, zero_smul]
  have : IsScalarTower (MvPolynomial τ A) (MvPolynomial σ A) N :=
    IsScalarTower.of_algebraMap_smul fun p z ↦ by
      simpa [RingHom.algebraMap_toAlgebra, MulAction.compHom_smul_def] using hact p z
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial τ A) (MvPolynomial σ A) N

/-- A finitely generated module over `MvPolynomial (Fin (e + 1)) A` annihilated by the last
variable `X (Fin.last e)` is finitely generated over `MvPolynomial (Fin e) A` via `Fin.castSucc`. -/
theorem moduleFinite_compHom_rename_castSucc {A : Type*} [CommSemiring A] {e : ℕ}
    {N : Type*} [AddCommMonoid N] [Module (MvPolynomial (Fin (e + 1)) A) N]
    [Module.Finite (MvPolynomial (Fin (e + 1)) A) N]
    (hkill : ∀ z : N, (X (Fin.last e) : MvPolynomial (Fin (e + 1)) A) • z = 0) :
    let : Module (MvPolynomial (Fin e) A) N :=
      Module.compHom N (rename (R := A) Fin.castSucc).toRingHom
    Module.Finite (MvPolynomial (Fin e) A) N :=
  moduleFinite_compHom_rename (Fin.castSucc_injective e) fun i hi z ↦ by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact (hi ⟨j, rfl⟩).elim
    · exact hkill z

end Rename

end TauCeti.MvPolynomial
