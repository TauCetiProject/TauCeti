/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.ScalarMap
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Algebra.Ring.Subgroup
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# The multiplier ring of a period lattice

The **multiplier ring** of a lattice `Λ ⊆ ℂ` is the subring `{α ∈ ℂ | α Λ ⊆ Λ}`. Through the scalar
maps of `PeriodPair.scalarPointHom`, it acts on the points `E_Λ(ℂ)` of the Weierstrass curve of
`Λ`: this is the ring homomorphism `PeriodPair.endRingHom`, which is injective. These are the
analytic endomorphisms of the complex uniformization.

Writing `α ω₁ = a ω₁ + b ω₂` and `α ω₂ = e ω₁ + f ω₂` with integers `a, b, e, f`, the multiplier
`α` is an eigenvalue of the integer matrix `[[a, b], [e, f]]`, so

  `α² - (a + f) α + (a f - b e) = 0`.

If `α` is not real, its conjugate is the other root, so `a + f = 2 Re α` and `a f - b e = |α|²`. If
`α` is real, the linear independence of `ω₁, ω₂` over `ℝ` forces `b = e = 0` and `α = a = f`.
Hence every multiplier is an algebraic integer of degree at most two, the real multipliers are
exactly the integers, and the degree `[Λ : α Λ]` of the endomorphism of `α ≠ 0`, that is the
cardinality of its kernel, is `|α|²`. In particular the multiplier ring is either `ℤ` or contains a
non-real algebraic integer of degree two: the curve has complex multiplication.

## Main definitions

* `PeriodPair.multiplierRing`: the subring `{α | α Λ ⊆ Λ}` of `ℂ`.
* `PeriodPair.endRingHom`: its action on `E_Λ(ℂ)` by the scalar maps.

## Main results

* `PeriodPair.scalarPointHom_add`, `PeriodPair.scalarPointHom_eq_zero_iff`: the scalar maps are
  additive in the scalar and vanish only for the scalar `0`.
* `PeriodPair.endRingHom_injective`: the action is faithful.
* `PeriodPair.multiplierRing_smul`: the multiplier ring depends only on the homothety class.
* `PeriodPair.sq_sub_trace_mul_add_norm_eq_zero`: `α² - (2 Re α) α + |α|² = 0` with integer
  trace and norm.
* `PeriodPair.isIntegral_of_mem_multiplierRing`: every multiplier is an algebraic integer.
* `PeriodPair.exists_intCast_eq_of_im_eq_zero`, `PeriodPair.multiplierRing_eq_bot_iff`: the real
  multipliers are the integers, and the multiplier ring is `ℤ` exactly when all multipliers are
  real.
* `PeriodPair.natCard_ker_endRingHom`: the degree of the endomorphism of `α` is `|α|²`.

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

/-! ### Additivity in the scalar -/

/-- The scalar maps are additive in the scalar. -/
lemma scalarPointHom_add {α β : ℂ} (hα : ∀ z ∈ L.lattice, α * z ∈ L'.lattice)
    (hβ : ∀ z ∈ L.lattice, β * z ∈ L'.lattice) :
    scalarPointHom (α + β) (fun z hz ↦ by rw [add_mul]; exact add_mem (hα z hz) (hβ z hz)) =
      scalarPointHom α hα + scalarPointHom β hβ :=
  L.pointHom_ext fun z ↦ by simp [add_mul]

/-- The scalar `0` induces the zero map. -/
@[simp]
lemma scalarPointHom_zero : scalarPointHom (L := L) (L' := L') 0 (fun z _ ↦ by simp) = 0 :=
  L.pointHom_ext fun z ↦ by simp [weierstrassPoint_zero]

/-- A scalar map vanishes only for the scalar `0`: the map of `α ≠ 0` is surjective, and the
curve of `Λ'` has the nonzero point `P(ω₁' / 2)`. -/
lemma scalarPointHom_eq_zero_iff {α : ℂ} (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    scalarPointHom α h = 0 ↔ α = 0 := by
  refine ⟨fun h0 ↦ by_contra fun hα ↦ ?_, fun hα ↦ by subst hα; exact scalarPointHom_zero⟩
  obtain ⟨P, hP⟩ := scalarPointHom_surjective hα h (L'.weierstrassPoint (L'.ω₁ / 2))
  rw [h0, AddMonoidHom.zero_apply, eq_comm, weierstrassPoint_eq_zero_iff] at hP
  exact L'.ω₁_div_two_notMem_lattice hP

/-! ### The multiplier ring and its action -/

variable (L)

/-- The **multiplier ring** `{α ∈ ℂ | α Λ ⊆ Λ}` of the lattice of `L`: the multiplier ring
`AddSubgroup.multiplierRing` of the lattice as an additive subgroup of `ℂ`. -/
def multiplierRing : Subring ℂ :=
  L.lattice.toAddSubgroup.multiplierRing

variable {L}

/-- Membership in the multiplier ring: `α Λ ⊆ Λ`. -/
@[simp]
lemma mem_multiplierRing {α : ℂ} : α ∈ L.multiplierRing ↔ ∀ z ∈ L.lattice, α * z ∈ L.lattice :=
  AddSubgroup.mem_multiplierRing

variable (L)

/-- The multiplier ring depends only on the homothety class of the lattice. -/
@[simp]
lemma multiplierRing_smul (c : ℂˣ) : (c • L).multiplierRing = L.multiplierRing := by
  ext α
  simp only [mem_multiplierRing, lattice_smul, Submodule.mem_map, LinearMap.mulLeft_apply,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun z _ ↦ ?_
  rw [mul_left_comm]
  exact ⟨fun ⟨w, hw, hwz⟩ ↦ mul_left_cancel₀ c.ne_zero hwz ▸ hw, fun h ↦ ⟨_, h, rfl⟩⟩

/-- The action of the multiplier ring on the points of the Weierstrass curve by the scalar maps:
these are the analytic endomorphisms of `E_Λ(ℂ)`. -/
def endRingHom : L.multiplierRing →+* AddMonoid.End L.weierstrassCurve.toAffine.Point where
  toFun α := scalarPointHom (α : ℂ) (mem_multiplierRing.mp α.property)
  map_one' := scalarPointHom_one
  map_mul' α β :=
    (scalarPointHom_comp (mem_multiplierRing.mp β.property) (mem_multiplierRing.mp α.property)).symm
  map_zero' := scalarPointHom_zero
  map_add' α β :=
    scalarPointHom_add (mem_multiplierRing.mp α.property) (mem_multiplierRing.mp β.property)

/-- The endomorphism of a multiplier `α` is the scalar map of `α`. -/
lemma endRingHom_apply (α : L.multiplierRing) :
    L.endRingHom α = scalarPointHom (α : ℂ) (mem_multiplierRing.mp α.property) :=
  (rfl)

/-- The endomorphism of a multiplier `α` sends `P(z)` to `P(α z)`. -/
@[simp]
lemma endRingHom_weierstrassPoint (α : L.multiplierRing) (z : ℂ) :
    L.endRingHom α (L.weierstrassPoint z) = L.weierstrassPoint (α * z) :=
  scalarPointHom_weierstrassPoint _ (mem_multiplierRing.mp α.property) z

/-- The action of the multiplier ring is faithful. -/
theorem endRingHom_injective : Function.Injective L.endRingHom := by
  refine (injective_iff_map_eq_zero _).mpr fun α hα ↦ ?_
  rw [endRingHom_apply] at hα
  exact Subtype.ext ((scalarPointHom_eq_zero_iff _).mp hα)

/-! ### Multipliers are imaginary quadratic integers -/

variable {L}

/-- A multiplier is a root of the characteristic polynomial `X² - (a + f) X + (a f - b e)` of its
integer matrix. -/
private lemma sq_sub_mul_add_eq_zero {α : ℂ} {a b e f : ℤ}
    (hab : (a : ℂ) * L.ω₁ + b * L.ω₂ = α * L.ω₁) (hef : (e : ℂ) * L.ω₁ + f * L.ω₂ = α * L.ω₂) :
    α ^ 2 - (a + f : ℤ) * α + (a * f - b * e : ℤ) = 0 := by
  refine mul_right_cancel₀ L.ω₁_ne_zero ?_
  push_cast
  linear_combination (f - α) * hab - (b : ℂ) * hef

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

/-- The determinant `a f - b e` of the integer matrix of a multiplier `α` is `|α|²`, and its trace
`a + f` is `2 Re α`. -/
private lemma det_eq_normSq {α : ℂ} {a b e f : ℤ}
    (hab : (a : ℂ) * L.ω₁ + b * L.ω₂ = α * L.ω₁) (hef : (e : ℂ) * L.ω₁ + f * L.ω₂ = α * L.ω₂) :
    ((a * f - b * e : ℤ) : ℝ) = Complex.normSq α ∧ ((a + f : ℤ) : ℝ) = 2 * α.re := by
  by_cases him : α.im = 0
  · obtain ⟨ha, hb, he, hf⟩ := eq_intCast_of_im_eq_zero him hab hef
    have hre : α.re = a := by rw [ha]; simp
    have hre' : α.re = f := by rw [hf]; simp
    simp only [Complex.normSq_apply, him, hb, he]
    push_cast
    constructor <;> rw [← hre, ← hre'] <;> ring
  · have h := sq_sub_mul_add_eq_zero hab hef
    have hc : conj α ^ 2 - (a + f : ℤ) * conj α + (a * f - b * e : ℤ) = 0 := by
      simpa using congrArg conj h
    have hne : α - conj α ≠ 0 := by
      rw [sub_ne_zero, ne_comm, Ne, Complex.conj_eq_iff_im]
      exact him
    have ht : ((a + f : ℤ) : ℂ) = α + conj α := by
      refine (mul_left_cancel₀ hne ?_).symm
      linear_combination h - hc
    have hn : ((a * f - b * e : ℤ) : ℂ) = (Complex.normSq α : ℂ) := by
      rw [← Complex.mul_conj]
      linear_combination h + α * ht
    refine ⟨by exact_mod_cast hn, ?_⟩
    have := congrArg Complex.re ht
    simp only [Complex.intCast_re, Complex.add_re, Complex.conj_re] at this
    rw [Int.cast_add] at this ⊢
    linarith

/-- **The characteristic equation of a multiplier.** A multiplier `α` satisfies
`α² - t α + n = 0` with integers `t = 2 Re α` and `n = |α|²`. -/
theorem sq_sub_trace_mul_add_norm_eq_zero {α : ℂ} (hα : α ∈ L.multiplierRing) :
    ∃ t n : ℤ, α ^ 2 - t * α + n = 0 ∧ (t : ℝ) = 2 * α.re ∧ (n : ℝ) = Complex.normSq α := by
  obtain ⟨a, b, hab⟩ := mem_lattice.mp (mem_multiplierRing.mp hα _ L.ω₁_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp (mem_multiplierRing.mp hα _ L.ω₂_mem_lattice)
  obtain ⟨hn, ht⟩ := det_eq_normSq hab hef
  exact ⟨a + f, a * f - b * e, sq_sub_mul_add_eq_zero hab hef, ht, hn⟩

/-- Every multiplier is an algebraic integer. -/
theorem isIntegral_of_mem_multiplierRing {α : ℂ} (hα : α ∈ L.multiplierRing) :
    IsIntegral ℤ α :=
  isIntegral_of_smul_mem_submodule L.lattice
    (fun h ↦ L.ω₁_ne_zero ((Submodule.eq_bot_iff _).mp h _ L.ω₁_mem_lattice))
    (Submodule.fg_span (Set.toFinite _)) α (mem_multiplierRing.mp hα)

/-- The real multipliers are the integers. -/
theorem exists_intCast_eq_of_im_eq_zero {α : ℂ} (hα : α ∈ L.multiplierRing) (him : α.im = 0) :
    ∃ m : ℤ, (m : ℂ) = α := by
  obtain ⟨a, b, hab⟩ := mem_lattice.mp (mem_multiplierRing.mp hα _ L.ω₁_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp (mem_multiplierRing.mp hα _ L.ω₂_mem_lattice)
  exact ⟨a, (eq_intCast_of_im_eq_zero him hab hef).1.symm⟩

variable (L)

/-- **No complex multiplication.** The multiplier ring is `ℤ` exactly when every multiplier is
real. -/
theorem multiplierRing_eq_bot_iff :
    L.multiplierRing = ⊥ ↔ ∀ α ∈ L.multiplierRing, α.im = 0 := by
  refine ⟨fun h α hα ↦ ?_, fun h ↦ ?_⟩
  · rw [h, Subring.mem_bot] at hα
    obtain ⟨m, rfl⟩ := hα
    simp
  · refine le_antisymm (fun α hα ↦ ?_) bot_le
    exact Subring.mem_bot.mpr (exists_intCast_eq_of_im_eq_zero hα (h α hα))

/-- **The degree of an endomorphism is the norm.** The kernel of the endomorphism of a
multiplier `α` has `|α|²` elements. For `α = 0` both sides vanish: the kernel is the whole infinite
group of points, whose `Nat.card` is `0`. -/
theorem natCard_ker_endRingHom (α : L.multiplierRing) :
    (Nat.card (L.endRingHom α).ker : ℝ) = Complex.normSq α := by
  obtain rfl | hα := eq_or_ne α 0
  · have hker : (L.endRingHom 0).ker = ⊤ := by
      ext P
      rw [map_zero]
      exact iff_of_true (AddMonoidHom.mem_ker.mpr (AddMonoid.End.zero_apply P)) trivial
    rw [hker, Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_eq_zero_of_infinite]
    simp
  have hα' : (α : ℂ) ≠ 0 := fun h ↦ hα (Subtype.ext h)
  obtain ⟨a, b, hab⟩ := mem_lattice.mp (mem_multiplierRing.mp α.property _ L.ω₁_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp (mem_multiplierRing.mp α.property _ L.ω₂_mem_lattice)
  have h := natCard_ker_scalarPointHom (Units.mk0 _ hα') (mem_multiplierRing.mp α.property)
  rw [relIndex_lattice_smul_eq_natAbs (Units.mk0 _ hα') hab hef] at h
  simp only [Units.val_mk0] at h
  rw [endRingHom_apply, h, Nat.cast_natAbs, Int.cast_abs, (det_eq_normSq hab hef).1,
    abs_of_nonneg (Complex.normSq_nonneg _)]

end PeriodPair
