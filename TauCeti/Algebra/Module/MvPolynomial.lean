/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Algebra.MvPolynomial.Rename

/-!
# Modules over multivariate polynomial rings

This file records finiteness criteria for modules over a multivariate polynomial ring
`MvPolynomial τ A` when variables outside the range of an injective renaming `f : σ → τ` act by
zero: restricting scalars along `MvPolynomial.rename f` preserves finite generation.

## Main results

* `TauCeti.MvPolynomial.moduleFinite_compHom_rename`: a finitely generated `MvPolynomial τ A`-module
  annihilated by every variable outside `Set.range f` (for injective `f : σ → τ`) is finitely
  generated over `MvPolynomial σ A` via `MvPolynomial.rename f`.
* `TauCeti.MvPolynomial.moduleFinite_compHom_rename_castSucc`: specialization to
  `Fin.castSucc : Fin e → Fin (e + 1)` when `X (Fin.last e)` annihilates the module.
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

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

end TauCeti.MvPolynomial
