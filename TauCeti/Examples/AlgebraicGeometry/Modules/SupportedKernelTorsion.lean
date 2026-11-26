/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.SupportedKernel.Basic
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

/-- Every element of `I` kills `N`, since `I` is the annihilator of `k[x, y]/I`. -/
private theorem smul_eq_zero_of_mem {r : MvPolynomial (Fin 2) k} (hr : r ∈ I k) (m : N k) :
    r • m = 0 :=
  Module.mem_annihilator.mp (by rwa [Ideal.annihilator_quotient]) m

/-- **`N~` vanishes off the origin.** The sections of `N~` over any open contained in
`D(x) ∪ D(y)` vanish. -/
theorem subsingleton_tilde_of_le_punctured
    {W : (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).Opens} (hW : W ≤ punctured k) :
    Subsingleton Γ(tilde (N k), W) := by
  refine subsingleton_tilde_of_forall_notMem_support fun p hp ↦
    Module.notMem_support_iff'.mpr fun m ↦ ?_
  rcases hW hp with hx | hy
  · exact ⟨X 0 ^ 2, fun h ↦ hx (p.isPrime.mem_of_pow_mem 2 h),
      smul_eq_zero_of_mem k (Ideal.subset_span (by simp)) m⟩
  · exact ⟨X 1 ^ 3, fun h ↦ hy (p.isPrime.mem_of_pow_mem 3 h),
      smul_eq_zero_of_mem k (Ideal.subset_span (by simp)) m⟩

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
  exact eq_bot_iff.mpr (Submodule.smul_le.mpr fun r hr n _ ↦
    (Submodule.mem_bot _).mpr (smul_eq_zero_of_mem k (hJ hr) n))

end TauCeti.SupportedKernelTorsionExample
