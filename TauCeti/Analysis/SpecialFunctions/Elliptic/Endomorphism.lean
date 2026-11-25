/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.ScalarMap
public import TauCeti.RingTheory.IntegralOrder.LeftOrder
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# The multiplier ring of a period lattice and its analytic endomorphisms

The **multiplier ring** of a lattice `Λ ⊆ ℂ` is the subring `{α ∈ ℂ | α Λ ⊆ Λ}`, the left order
`L.lattice.leftOrder` of the lattice (`Submodule.leftOrder`). Through the scalar maps of
`PeriodPair.scalarPointHom`, it acts on the points `E_Λ(ℂ)` of the Weierstrass curve of `Λ`: this
is the ring homomorphism `PeriodPair.endRingHom`, which is injective. These are the analytic
endomorphisms of the complex uniformization.

Writing `α ω₁ = a ω₁ + b ω₂` and `α ω₂ = e ω₁ + f ω₂` with integers `a, b, e, f`, the integer
matrix `[[a, e], [b, f]]` is the matrix of multiplication by `α` in the `ℝ`-basis `ω₁, ω₂` of `ℂ`,
so its trace `a + f` and determinant `a f - b e` are the trace `2 Re α` and norm `|α|²` of `α` over
`ℝ`. Hence `α² - (a + f) α + (a f - b e) = 0`. If `α` is real, the linear independence of
`ω₁, ω₂` over `ℝ` forces `b = e = 0` and `α = a = f`. So every multiplier is an algebraic integer
of degree at most two, the real multipliers are exactly the integers, and the degree `[Λ : α Λ]`
of the endomorphism of `α ≠ 0`, that is the cardinality of its kernel, is `|α|²`. In particular
the multiplier ring is either `ℤ` or contains a non-real algebraic integer of degree two: the
curve has complex multiplication.

## Main definitions

* `PeriodPair.endRingHom`: the action of the multiplier ring `L.lattice.leftOrder` on `E_Λ(ℂ)` by
  the scalar maps.

## Main results

* `PeriodPair.endRingHom_injective`: the action is faithful.
* `PeriodPair.sq_sub_trace_mul_add_norm_eq_zero`: `α² - (2 Re α) α + |α|² = 0` with integer
  trace and norm.
* `PeriodPair.isIntegral_of_mem_leftOrder_lattice`: every multiplier is an algebraic integer.
* `PeriodPair.exists_intCast_eq_of_im_eq_zero`, `PeriodPair.leftOrder_lattice_eq_bot_iff`: the
  real multipliers are the integers, and the multiplier ring is `ℤ` exactly when all multipliers
  are real.
* `PeriodPair.natCard_ker_endRingHom`: the degree of the endomorphism of `α ≠ 0` is `|α|²`
  (stated with `Nat.card`, so that it also holds at `α = 0`).

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.5.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  §VII.2.
-/

public noncomputable section

open ComplexConjugate

namespace PeriodPair

variable {L L' : PeriodPair}

/-! ### The action of the multiplier ring -/

variable (L)

/-- The action of the multiplier ring `L.lattice.leftOrder = {α | α Λ ⊆ Λ}` on the points of the
Weierstrass curve by the scalar maps: these are the analytic endomorphisms of `E_Λ(ℂ)`. -/
def endRingHom : L.lattice.leftOrder →+* AddMonoid.End L.weierstrassCurve.toAffine.Point where
  toFun α := scalarPointHom (α : ℂ) (Submodule.mem_leftOrder_iff.mp α.property)
  map_one' := scalarPointHom_one
  map_mul' α β := (scalarPointHom_comp (Submodule.mem_leftOrder_iff.mp β.property)
    (Submodule.mem_leftOrder_iff.mp α.property)).symm
  map_zero' := scalarPointHom_zero
  map_add' α β := scalarPointHom_add (Submodule.mem_leftOrder_iff.mp α.property)
    (Submodule.mem_leftOrder_iff.mp β.property)

/-- The endomorphism of a multiplier `α` is the scalar map of `α`. -/
lemma endRingHom_apply (α : L.lattice.leftOrder) :
    L.endRingHom α = scalarPointHom (α : ℂ) (Submodule.mem_leftOrder_iff.mp α.property) :=
  (rfl)

/-- The endomorphism of a multiplier `α` sends `P(z)` to `P(α z)`. -/
@[simp]
lemma endRingHom_weierstrassPoint (α : L.lattice.leftOrder) (z : ℂ) :
    L.endRingHom α (L.weierstrassPoint z) = L.weierstrassPoint (α * z) :=
  scalarPointHom_weierstrassPoint _ (Submodule.mem_leftOrder_iff.mp α.property) z

/-- The action of the multiplier ring is faithful. -/
theorem endRingHom_injective : Function.Injective L.endRingHom := by
  refine (injective_iff_map_eq_zero _).mpr fun α hα ↦ ?_
  rw [endRingHom_apply] at hα
  exact Subtype.ext ((scalarPointHom_eq_zero_iff _).mp hα)

/-! ### Multipliers are imaginary quadratic integers -/

variable {L}

/-- The integer matrix `[[a, e], [b, f]]` of a multiplier `α` is the matrix of multiplication by
`α` in the `ℝ`-basis `ω₁, ω₂` of `ℂ`. -/
private lemma leftMulMatrix_basis {α : ℂ} {a b e f : ℤ}
    (hab : (a : ℂ) * L.ω₁ + b * L.ω₂ = α * L.ω₁) (hef : (e : ℂ) * L.ω₁ + f * L.ω₂ = α * L.ω₂) :
    Algebra.leftMulMatrix L.basis α = !![(a : ℝ), e; b, f] := by
  have h₁ : α * L.basis 0 = (a : ℝ) • L.basis 0 + (b : ℝ) • L.basis 1 := by
    simp [Complex.real_smul, hab]
  have h₂ : α * L.basis 1 = (e : ℝ) • L.basis 0 + (f : ℝ) • L.basis 1 := by
    simp [Complex.real_smul, hef]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Algebra.leftMulMatrix_eq_repr_mul, Fin.zero_eta, Fin.mk_one, h₁, h₂, map_add,
      map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply] <;> simp

/-- The determinant `a f - b e` of the integer matrix of a multiplier `α` is its norm `|α|²` over
`ℝ`, and its trace `a + f` is the trace `2 Re α`. -/
private lemma det_eq_normSq {α : ℂ} {a b e f : ℤ}
    (hab : (a : ℂ) * L.ω₁ + b * L.ω₂ = α * L.ω₁) (hef : (e : ℂ) * L.ω₁ + f * L.ω₂ = α * L.ω₂) :
    ((a * f - b * e : ℤ) : ℝ) = Complex.normSq α ∧ ((a + f : ℤ) : ℝ) = 2 * α.re := by
  rw [← Algebra.norm_complex_apply, ← Algebra.trace_complex_apply,
    Algebra.norm_eq_matrix_det L.basis, Algebra.trace_eq_matrix_trace L.basis,
    leftMulMatrix_basis hab hef, Matrix.det_fin_two_of, Matrix.trace_fin_two_of]
  push_cast
  exact ⟨by ring, rfl⟩

/-- A real multiplier is the integer `a = f`, with `b = e = 0`. -/
private lemma eq_intCast_of_im_eq_zero {α : ℂ} (him : α.im = 0) {a b e f : ℤ}
    (hab : (a : ℂ) * L.ω₁ + b * L.ω₂ = α * L.ω₁) (hef : (e : ℂ) * L.ω₁ + f * L.ω₂ = α * L.ω₂) :
    α = a ∧ b = 0 ∧ e = 0 ∧ α = f := by
  have hα : α = (α.re : ℂ) := Complex.ext rfl (by simp [him])
  have hind := LinearIndependent.pair_iff.mp L.indep
  obtain ⟨h₁, h₂⟩ := hind (α.re - a) (-b) (by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_intCast]
    rw [← hα]
    linear_combination -hab)
  obtain ⟨h₃, h₄⟩ := hind (-e) (α.re - f) (by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_intCast]
    rw [← hα]
    linear_combination -hef)
  refine ⟨?_, by exact_mod_cast neg_eq_zero.mp h₂, by exact_mod_cast neg_eq_zero.mp h₃, ?_⟩
  · rw [hα, sub_eq_zero.mp h₁, Complex.ofReal_intCast]
  · rw [hα, sub_eq_zero.mp h₄, Complex.ofReal_intCast]

/-- **The characteristic equation of a multiplier.** A multiplier `α` satisfies
`α² - t α + n = 0` with integers `t = 2 Re α` and `n = |α|²`. -/
theorem sq_sub_trace_mul_add_norm_eq_zero {α : ℂ} (hα : α ∈ L.lattice.leftOrder) :
    ∃ t n : ℤ, α ^ 2 - t * α + n = 0 ∧ (t : ℝ) = 2 * α.re ∧ (n : ℝ) = Complex.normSq α := by
  obtain ⟨a, b, hab⟩ := mem_lattice.mp (Submodule.mem_leftOrder_iff.mp hα _ L.ω₁_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp (Submodule.mem_leftOrder_iff.mp hα _ L.ω₂_mem_lattice)
  obtain ⟨hn, ht⟩ := det_eq_normSq hab hef
  have ht' : ((a + f : ℤ) : ℂ) = α + conj α := by
    rw [Complex.add_conj, ← ht]; norm_cast
  have hn' : ((a * f - b * e : ℤ) : ℂ) = α * conj α := by
    rw [Complex.mul_conj, ← hn]; norm_cast
  exact ⟨a + f, a * f - b * e, by linear_combination hn' - α * ht', ht, hn⟩

/-- Every multiplier is an algebraic integer. -/
theorem isIntegral_of_mem_leftOrder_lattice {α : ℂ} (hα : α ∈ L.lattice.leftOrder) :
    IsIntegral ℤ α :=
  isIntegral_of_smul_mem_submodule L.lattice
    (fun h ↦ L.ω₁_ne_zero ((Submodule.eq_bot_iff _).mp h _ L.ω₁_mem_lattice))
    (Submodule.fg_span (Set.toFinite _)) α (Submodule.mem_leftOrder_iff.mp hα)

/-- The real multipliers are the integers. -/
theorem exists_intCast_eq_of_im_eq_zero {α : ℂ} (hα : α ∈ L.lattice.leftOrder) (him : α.im = 0) :
    ∃ m : ℤ, (m : ℂ) = α := by
  obtain ⟨a, b, hab⟩ := mem_lattice.mp (Submodule.mem_leftOrder_iff.mp hα _ L.ω₁_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp (Submodule.mem_leftOrder_iff.mp hα _ L.ω₂_mem_lattice)
  exact ⟨a, (eq_intCast_of_im_eq_zero him hab hef).1.symm⟩

variable (L)

/-- **No complex multiplication.** The multiplier ring is `ℤ` exactly when every multiplier is
real. -/
theorem leftOrder_lattice_eq_bot_iff :
    L.lattice.leftOrder = ⊥ ↔ ∀ α ∈ L.lattice.leftOrder, α.im = 0 := by
  refine ⟨fun h α hα ↦ ?_, fun h ↦ ?_⟩
  · rw [h, Algebra.mem_bot] at hα
    obtain ⟨m, rfl⟩ := hα
    simp
  · refine le_antisymm (fun α hα ↦ ?_) bot_le
    obtain ⟨m, hm⟩ := exists_intCast_eq_of_im_eq_zero hα (h α hα)
    exact Algebra.mem_bot.mpr ⟨m, by simpa using hm⟩

/-- **The degree of an endomorphism is the norm.** The `Nat.card` of the kernel of the
endomorphism of a multiplier `α` is `|α|²`: for `α ≠ 0` the kernel is finite with `|α|²` elements,
and for `α = 0` both sides vanish, since the kernel is the whole infinite group of points and
`Nat.card` of an infinite type is `0`. -/
theorem natCard_ker_endRingHom (α : L.lattice.leftOrder) :
    (Nat.card (L.endRingHom α).ker : ℝ) = Complex.normSq α := by
  obtain rfl | hα := eq_or_ne α 0
  · have hker : (L.endRingHom 0).ker = ⊤ := by rw [map_zero]; exact AddMonoidHom.ker_zero
    rw [hker, Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_eq_zero_of_infinite]
    simp
  have hα' : (α : ℂ) ≠ 0 := fun h ↦ hα (Subtype.ext h)
  have hαΛ := Submodule.mem_leftOrder_iff.mp α.property
  obtain ⟨a, b, hab⟩ := mem_lattice.mp (hαΛ _ L.ω₁_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp (hαΛ _ L.ω₂_mem_lattice)
  have h := natCard_ker_scalarPointHom (Units.mk0 _ hα') hαΛ
  rw [relIndex_lattice_smul_eq_natAbs (Units.mk0 _ hα') hab hef] at h
  simp only [Units.val_mk0] at h
  rw [endRingHom_apply, h, Nat.cast_natAbs, Int.cast_abs, (det_eq_normSq hab hef).1,
    abs_of_nonneg (Complex.normSq_nonneg _)]

end PeriodPair
