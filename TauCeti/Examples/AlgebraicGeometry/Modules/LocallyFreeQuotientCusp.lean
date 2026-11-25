/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Check: rank-one quotients of the differentials of the cusp in characteristic `2`

Let `k` be a field of characteristic `2` and `A = k[x, y]/(y² − x³)` the coordinate ring of the
cusp, here `(k[x])[y]/(y² − x³)`. Its Kähler differentials are spanned by `dx` and `dy`, and
`d(y² − x³) = 2y dy − 3x² dx = x² dx`, so `x² dx = 0`. Since `A` is free over `k[x]` (on `1, y`),
`x²` is a nonzerodivisor on `A`. So every `A`-linear map `g : Ω[A⁄k] → A` sends `dx` to `0`, and
if `g` is surjective, then `g(dy)` is a unit and the kernel of `g` is `A dx`: all rank-one
quotients of the differentials of the cusp have the same kernel, as the uniqueness of locally free
quotients over a dense smooth locus predicts (NashBlowups §0.7). The torsion section `dx` shows
that the differentials themselves are not locally free.
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

/-- The equation of the cusp. -/
theorem cuspY_sq : cuspY k ^ 2 = cuspX k ^ 3 := by
  have h := AdjoinRoot.eval₂_root (cuspPolynomial k)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [cuspY, cuspX, ← map_pow, sub_eq_zero.mp h]

/-- The cusp ring is free over `k[x]`, on `1, y`. -/
instance free_cuspRing : Module.Free (Polynomial k) (CuspRing k) :=
  .of_basis (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (X ^ 3) two_ne_zero)).basis

/-- `x² c = 0` forces `c = 0` on the cusp: the ring is torsion-free over `k[x]`. -/
theorem eq_zero_of_cuspX_sq_mul_eq_zero {c : CuspRing k} (h : cuspX k ^ 2 * c = 0) : c = 0 := by
  rw [cuspX, ← map_pow, ← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def] at h
  exact (smul_eq_zero.mp h).resolve_left (pow_ne_zero 2 X_ne_zero)

/-- The differentials of the cusp are spanned by `dx` and `dy`. -/
theorem span_D_eq_top :
    Submodule.span (CuspRing k) {D k (CuspRing k) (cuspX k), D k (CuspRing k) (cuspY k)} = ⊤ := by
  set N := Submodule.span (CuspRing k) {D k (CuspRing k) (cuspX k), D k (CuspRing k) (cuspY k)}
  -- The elements whose differential lies in `N` form a subalgebra containing `x` and `y`.
  let T : Subalgebra k (CuspRing k) :=
    { carrier := {a | D k (CuspRing k) a ∈ N}
      mul_mem' {a b} ha hb := by
        change D k _ (a * b) ∈ N
        rw [Derivation.leibniz]
        exact N.add_mem (N.smul_mem _ hb) (N.smul_mem _ ha)
      add_mem' {a b} ha hb := by
        change D k _ (a + b) ∈ N
        rw [map_add]
        exact N.add_mem ha hb
      algebraMap_mem' c := by simp }
  have hx : cuspX k ∈ T := Submodule.subset_span (by simp)
  have hy : cuspY k ∈ T := Submodule.subset_span (by simp)
  have hT (a : CuspRing k) : a ∈ T := by
    induction a using AdjoinRoot.induction_on with | ih p => ?_
    induction p using Polynomial.induction_on with
    | C r =>
      rw [AdjoinRoot.mk_C]
      induction r using Polynomial.induction_on with
      | C c => exact T.algebraMap_mem c
      | add r s hr hs => rw [map_add]; exact T.add_mem hr hs
      | monomial n c h =>
        rw [pow_succ, ← mul_assoc, map_mul]
        exact T.mul_mem h hx
    | add p q hp hq => rw [map_add]; exact T.add_mem hp hq
    | monomial n r h =>
      rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      exact T.mul_mem h hy
  rw [eq_top_iff, ← span_range_derivation k (CuspRing k), Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact hT a

variable {k}

/-- In characteristic `2`, `x² dx = 0` on the cusp: `d(y²) = 2y dy = 0` and `d(x³) = 3x² dx`. -/
theorem cuspX_sq_smul_D_cuspX (h2 : (2 : k) = 0) :
    cuspX k ^ 2 • D k (CuspRing k) (cuspX k) = 0 := by
  have h2' : (2 : CuspRing k) = 0 := by
    rw [← map_ofNat (algebraMap k (CuspRing k)) 2, h2, map_zero]
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
  rw [← smul_eq_mul, ← map_smul, cuspX_sq_smul_D_cuspX h2, map_zero]

/-- **Check.** In characteristic `2`, every surjective linear form on the differentials of the
cusp has kernel `A dx`, and sends `dy` to a unit. -/
theorem ker_eq_span_D_cuspX (h2 : (2 : k) = 0) (g : Ω[CuspRing k⁄k] →ₗ[CuspRing k] CuspRing k)
    (hg : Function.Surjective g) :
    IsUnit (g (D k (CuspRing k) (cuspY k))) ∧
      LinearMap.ker g = Submodule.span (CuspRing k) {D k (CuspRing k) (cuspX k)} := by
  have hx := map_D_cuspX_eq_zero h2 g
  -- Every differential is `a dx + b dy`.
  have hω (ω : Ω[CuspRing k⁄k]) : ∃ a b : CuspRing k,
      a • D k (CuspRing k) (cuspX k) + b • D k (CuspRing k) (cuspY k) = ω :=
    Submodule.mem_span_pair.mp (by rw [span_D_eq_top]; exact Submodule.mem_top)
  obtain ⟨ω, hω1⟩ := hg 1
  obtain ⟨a, b, rfl⟩ := hω ω
  rw [map_add, map_smul, map_smul, hx, smul_zero, zero_add, smul_eq_mul, mul_comm] at hω1
  have hu : IsUnit (g (D k (CuspRing k) (cuspY k))) := IsUnit.of_mul_eq_one b hω1
  refine ⟨hu, le_antisymm (fun ω hker ↦ ?_) ?_⟩
  · obtain ⟨a, b, rfl⟩ := hω ω
    rw [LinearMap.mem_ker, map_add, map_smul, map_smul, hx, smul_zero, zero_add, smul_eq_mul,
      hu.mul_left_eq_zero] at hker
    rw [hker, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx

-- **Check.** In characteristic `2`, any two surjective linear forms on the differentials of the
-- cusp have the same kernel.
example (h2 : (2 : k) = 0) (g₁ g₂ : Ω[CuspRing k⁄k] →ₗ[CuspRing k] CuspRing k)
    (hg₁ : Function.Surjective g₁) (hg₂ : Function.Surjective g₂) :
    LinearMap.ker g₁ = LinearMap.ker g₂ :=
  (ker_eq_span_D_cuspX h2 g₁ hg₁).2.trans (ker_eq_span_D_cuspX h2 g₂ hg₂).2.symm

end

end TauCeti.CuspDifferentialsExample
