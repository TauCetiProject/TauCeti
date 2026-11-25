/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.SupportedKernel
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Example: a module supported at the origin of the plane

On `Spec k[x, y]`, let `J = (x, y)` and `N = k[x, y]/(x², y³)`. The module `N` is killed by `x²`
and by `y³`, so its localization at every prime off the origin `V(J)` vanishes, and the sheaf `N~`
restricts to zero on the complement `D(x) ∪ D(y)` of the origin: every section of `N~` vanishes
there, so the supported kernel of `N~` along the inclusion of `D(x) ∪ D(y)` is all of `N~`.
Consistently with the description of the supported kernel as `J`-power torsion
(`AlgebraicGeometry.Scheme.Modules.map_eq_zero_iff_mem_primaryComponent`), `J⁴ N = 0`, since
every monomial of degree four is divisible by `x²` or by `y³`.
-/

public section

open AlgebraicGeometry MvPolynomial TauCeti.AlgebraicGeometry

namespace TauCeti.SupportedKernelTorsionExample

universe u

variable (k : Type u) [Field k]

/-- The ideal `(x², y³)` of `k[x, y]`. -/
noncomputable abbrev I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0 ^ 2, X 1 ^ 3}

/-- The module `N = k[x, y]/(x², y³)`. -/
noncomputable abbrev N : ModuleCat.{u} (CommRingCat.of (MvPolynomial (Fin 2) k)) :=
  ModuleCat.of _ (MvPolynomial (Fin 2) k ⧸ I k)

/-- The complement `D(x) ∪ D(y)` of the origin in `Spec k[x, y]`. -/
noncomputable abbrev punctured : (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).Opens :=
  PrimeSpectrum.basicOpen (X 0) ⊔ PrimeSpectrum.basicOpen (X 1)

/-- If `f` kills the `R`-module `M` and does not lie in the prime `p`, then `M_p = 0`. -/
private theorem subsingleton_localizedModule {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {p : Ideal R} [p.IsPrime] {f : R} (hf : f ∉ p) (hfM : ∀ m : M, f • m = 0) :
    Subsingleton (LocalizedModule p.primeCompl M) :=
  (IsLocalizedModule.subsingleton_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).2 fun m ↦ ⟨f, hf, hfM m⟩

/-- `x²` kills `N`. -/
private theorem X_zero_sq_smul (m : N k) : (X 0 ^ 2 : MvPolynomial (Fin 2) k) • m = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (m : MvPolynomial (Fin 2) k ⧸ I k)
  change Ideal.Quotient.mk (I k) _ * Ideal.Quotient.mk (I k) a = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- `y³` kills `N`. -/
private theorem X_one_cube_smul (m : N k) : (X 1 ^ 3 : MvPolynomial (Fin 2) k) • m = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (m : MvPolynomial (Fin 2) k ⧸ I k)
  change Ideal.Quotient.mk (I k) _ * Ideal.Quotient.mk (I k) a = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- **`N~` vanishes off the origin.** The sections of `N~` over any open contained in
`D(x) ∪ D(y)` vanish. -/
theorem subsingleton_tilde_of_le_punctured
    {W : (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).Opens} (hW : W ≤ punctured k) :
    Subsingleton Γ(tilde (N k), W) := by
  refine subsingleton_tilde_of_forall_subsingleton fun p hp ↦ ?_
  rcases hW hp with hx | hy
  · exact subsingleton_localizedModule
      (fun h ↦ hx (p.isPrime.mem_of_pow_mem 2 h)) (X_zero_sq_smul k)
  · exact subsingleton_localizedModule
      (fun h ↦ hy (p.isPrime.mem_of_pow_mem 3 h)) (X_one_cube_smul k)

/-- **The supported kernel of `N~` off the origin is everything.** Every section of `N~` vanishes
on `D(x) ∪ D(y)`, so lies in the supported kernel along the inclusion of `D(x) ∪ D(y)`. -/
theorem mem_range_supportedKernelι_app
    {W : (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).Opens} (s : Γ(tilde (N k), W)) :
    s ∈ Set.range (((tilde (N k)).supportedKernelι (punctured k).ι).app W) := by
  rw [Scheme.Modules.mem_range_supportedKernelι_app_iff]
  have := subsingleton_tilde_of_le_punctured k
    (W := (punctured k).ι ''ᵁ ((punctured k).ι ⁻¹ᵁ W)) (Scheme.Hom.image_le_opensRange _ _ |>.trans
      (by simp))
  exact Subsingleton.elim _ _

/-- **`J⁴ N = 0`** for `J = (x, y)`: every monomial of degree four in `x` and `y` is divisible by
`x²` or by `y³`. -/
theorem span_pow_four_smul_eq_bot :
    (Ideal.span {X 0, X 1} : Ideal (MvPolynomial (Fin 2) k)) ^ 4 •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) (N k)) = ⊥ := by
  set A : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0}
  set B : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 1}
  have hA : A ^ 2 ≤ I k := by
    rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (by simp)
  have hB : B ^ 3 ≤ I k := by
    rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (by simp)
  -- Expand `(A + B) ⁴`: each term `Aᵐ Bⁿ` with `m + n = 4` has `m ≥ 2` or `n ≥ 3`.
  have hJ : (Ideal.span {X 0, X 1} : Ideal (MvPolynomial (Fin 2) k)) ^ 4 ≤ I k := by
    rw [Ideal.span_insert, ← Submodule.add_eq_sup, add_pow]
    refine Finset.sum_induction _ (· ≤ I k) (fun a b ha hb ↦ Submodule.add_eq_sup a b ▸
      sup_le ha hb) bot_le fun m _ ↦ Ideal.mul_le_left.trans ?_
    rcases le_or_gt 2 m with h | h
    · exact Ideal.mul_le_left.trans (le_trans (Ideal.pow_le_pow_right h) hA)
    · exact Ideal.mul_le_right.trans
        (le_trans (Ideal.pow_le_pow_right (show 3 ≤ 4 - m by omega)) hB)
  refine eq_bot_iff.mpr (Submodule.smul_le.mpr fun r hr n _ ↦ ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (n : MvPolynomial (Fin 2) k ⧸ I k)
  rw [Submodule.mem_bot]
  change Ideal.Quotient.mk (I k) r * Ideal.Quotient.mk (I k) a = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (hJ hr)

end TauCeti.SupportedKernelTorsionExample
