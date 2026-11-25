/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.Kaehler.Basic
import TauCeti.Algebra.CharP.Two

/-!
# Surjections from the differentials of the cusp in characteristic `2`

Let `k` be a field of characteristic `2` and `A = k[x, y]/(y² − x³)` the coordinate ring of the
cusp, here `(k[x])[y]/(y² − x³)`. Its Kähler differentials are spanned by `dx` and `dy`, since
`x` and `y` generate `A`, and `d(y² − x³) = 2y dy − 3x² dx = x² dx`, so `x² dx = 0`. Since `A` is
free over `k[x]` (on `1, y`), `x²` is a nonzerodivisor on `A`. So every `A`-linear map
`g : Ω[A⁄k] → A` sends `dx` to `0`, and if `g` is surjective, then `g(dy)` is a unit and the kernel
of `g` is `A dx`. Hence all quotients of the differentials isomorphic to `A` (the surjections
`Ω[A⁄k] → A`) have the same kernel `A dx`, as the uniqueness of locally free quotients over a
dense smooth locus predicts. The torsion section `dx` shows that the differentials themselves are
not locally free.
-/

public section

open Polynomial KaehlerDifferential

namespace TauCeti.CuspDifferentialsExample

universe u

noncomputable section

variable (k : Type u) [Field k]

/-- The polynomial `y² − x³` over `k[x]`. -/
abbrev cuspPolynomial : (Polynomial k)[X] := X ^ 2 - C (X ^ 3)

/-- The coordinate ring `k[x, y]/(y² − x³)` of the cusp. -/
abbrev CuspRing : Type u := AdjoinRoot (cuspPolynomial k)

/-- The coordinate `x` on the cusp. -/
def cuspX : CuspRing k := AdjoinRoot.of _ X

/-- The coordinate `y` on the cusp. -/
def cuspY : CuspRing k := AdjoinRoot.root _

/-- `x` is the image of the polynomial variable of `k[x]`. -/
theorem cuspX_def : cuspX k = AdjoinRoot.of _ X := (rfl)

/-- `y` is the adjoined root of `y² − x³`. -/
theorem cuspY_def : cuspY k = AdjoinRoot.root _ := (rfl)

/-- `y` is the class of the variable `Y` of `(k[x])[Y]`. -/
theorem mk_X_eq_cuspY : AdjoinRoot.mk (cuspPolynomial k) X = cuspY k := by
  rw [cuspY_def, AdjoinRoot.mk_X]

/-- The equation of the cusp. -/
theorem cuspY_sq : cuspY k ^ 2 = cuspX k ^ 3 := by
  have h := AdjoinRoot.eval₂_root (cuspPolynomial k)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [cuspY_def, cuspX_def, ← map_pow, sub_eq_zero.mp h]

/-- The cusp ring is free over `k[x]`, on `1, y`. -/
instance free_cuspRing : Module.Free (Polynomial k) (CuspRing k) :=
  (monic_X_pow_sub_C (X ^ 3) two_ne_zero).free_adjoinRoot

/-- `x² c = 0` forces `c = 0` on the cusp: the ring is torsion-free over `k[x]`. -/
theorem eq_zero_of_cuspX_sq_mul_eq_zero {c : CuspRing k} (h : cuspX k ^ 2 * c = 0) : c = 0 := by
  rw [cuspX_def, ← map_pow, ← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def] at h
  exact (smul_eq_zero.mp h).resolve_left (pow_ne_zero 2 X_ne_zero)

/-- The coordinates `x` and `y` generate the cusp ring as a `k`-algebra. -/
theorem adjoin_cuspX_cuspY_eq_top : Algebra.adjoin k {cuspX k, cuspY k} = ⊤ := by
  refine Algebra.eq_top_iff.mpr fun a ↦ ?_
  have hx : cuspX k ∈ Algebra.adjoin k {cuspX k, cuspY k} := Algebra.subset_adjoin (by simp)
  have hy : cuspY k ∈ Algebra.adjoin k {cuspX k, cuspY k} := Algebra.subset_adjoin (by simp)
  induction a using AdjoinRoot.induction_on with | ih p => ?_
  induction p using Polynomial.induction_on with
  | C r =>
    rw [AdjoinRoot.mk_C]
    induction r using Polynomial.induction_on with
    | C c => exact Subalgebra.algebraMap_mem _ c
    | add r s hr hs => rw [map_add]; exact add_mem hr hs
    | monomial n c h =>
      rw [pow_succ, ← mul_assoc, map_mul, ← cuspX_def]
      exact mul_mem h hx
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n r h =>
    rw [pow_succ, ← mul_assoc, map_mul, mk_X_eq_cuspY]
    exact mul_mem h hy

/-- The differentials of the cusp are spanned by `dx` and `dy`. -/
theorem span_D_eq_top :
    Submodule.span (CuspRing k) {D k (CuspRing k) (cuspX k), D k (CuspRing k) (cuspY k)} = ⊤ := by
  rw [← Set.image_pair]
  exact KaehlerDifferential.span_image_D_eq_top_of_adjoin_eq_top (adjoin_cuspX_cuspY_eq_top k)

variable {k}

/-- In characteristic `2`, `x² dx = 0` on the cusp: `d(y²) = 2y dy = 0` and `d(x³) = 3x² dx`. -/
theorem cuspX_sq_smul_D_cuspX_eq_zero (h2 : (2 : k) = 0) :
    cuspX k ^ 2 • D k (CuspRing k) (cuspX k) = 0 := by
  have h2' : (2 : CuspRing k) = 0 := two_eq_zero_of_algebra h2
  have h3 : (3 : CuspRing k) = 1 := by
    linear_combination h2'
  have h := congrArg (D k (CuspRing k)) (cuspY_sq k)
  rw [Derivation.leibniz_pow, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (CuspRing k),
    ← Nat.cast_smul_eq_nsmul (CuspRing k)] at h
  simp only [Nat.add_one_sub_one, pow_one, Nat.cast_ofNat, h2', h3, zero_smul, one_smul] at h
  exact h.symm

/-- **Every linear form on the differentials of the cusp kills `dx`** in characteristic `2`. -/
theorem map_D_cuspX_eq_zero (h2 : (2 : k) = 0) (g : Ω[CuspRing k⁄k] →ₗ[CuspRing k] CuspRing k) :
    g (D k (CuspRing k) (cuspX k)) = 0 := by
  refine eq_zero_of_cuspX_sq_mul_eq_zero k ?_
  rw [← smul_eq_mul, ← map_smul, cuspX_sq_smul_D_cuspX_eq_zero h2, map_zero]

/-- In characteristic `2`, a linear form on the differentials of the cusp sends `a dx + b dy` to
`b g(dy)`. -/
theorem map_smul_D_cuspX_add_smul_D_cuspY (h2 : (2 : k) = 0)
    (g : Ω[CuspRing k⁄k] →ₗ[CuspRing k] CuspRing k) (a b : CuspRing k) :
    g (a • D k (CuspRing k) (cuspX k) + b • D k (CuspRing k) (cuspY k)) =
      b * g (D k (CuspRing k) (cuspY k)) := by
  simp [map_D_cuspX_eq_zero h2]

/-- In characteristic `2`, every surjective linear form on the differentials of the cusp sends `dy`
to a unit. -/
theorem isUnit_map_D_cuspY (h2 : (2 : k) = 0) (g : Ω[CuspRing k⁄k] →ₗ[CuspRing k] CuspRing k)
    (hg : Function.Surjective g) : IsUnit (g (D k (CuspRing k) (cuspY k))) := by
  obtain ⟨ω, hω⟩ := hg 1
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp (span_D_eq_top k ▸ Submodule.mem_top (x := ω))
  rw [map_smul_D_cuspX_add_smul_D_cuspY h2, mul_comm] at hω
  exact IsUnit.of_mul_eq_one b hω

/-- In characteristic `2`, every surjective linear form on the differentials of the cusp has
kernel `A dx`. -/
theorem ker_eq_span_D_cuspX (h2 : (2 : k) = 0) (g : Ω[CuspRing k⁄k] →ₗ[CuspRing k] CuspRing k)
    (hg : Function.Surjective g) :
    LinearMap.ker g = Submodule.span (CuspRing k) {D k (CuspRing k) (cuspX k)} := by
  refine le_antisymm (fun ω hker ↦ ?_) ?_
  · obtain ⟨a, b, rfl⟩ :=
      Submodule.mem_span_pair.mp (span_D_eq_top k ▸ Submodule.mem_top (x := ω))
    rw [LinearMap.mem_ker, map_smul_D_cuspX_add_smul_D_cuspY h2,
      (isUnit_map_D_cuspY h2 g hg).mul_left_eq_zero] at hker
    rw [hker, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact map_D_cuspX_eq_zero h2 g

-- In characteristic `2`, any two surjective linear forms on the differentials of the cusp have
-- the same kernel.
example (h2 : (2 : k) = 0) (g₁ g₂ : Ω[CuspRing k⁄k] →ₗ[CuspRing k] CuspRing k)
    (hg₁ : Function.Surjective g₁) (hg₂ : Function.Surjective g₂) :
    LinearMap.ker g₁ = LinearMap.ker g₂ :=
  (ker_eq_span_D_cuspX h2 g₁ hg₁).trans (ker_eq_span_D_cuspX h2 g₂ hg₂).symm

end

end TauCeti.CuspDifferentialsExample
