/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
import TauCeti.GroupTheory.Index.Endomorphism
import TauCeti.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Regular.Pi
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic

/-!
# Finite-index subrings: principal quotients and non-zero-divisors

Let `S` be a subring of finite additive index in a commutative ring `R`.

1. **Principal quotients.** If `x ∈ S` is a non-zero-divisor in the ambient ring `R`,
   multiplication by `x` is an injective additive endomorphism of `R` stabilizing `S`, so
   `S ⧸ Ideal.span {x}` and `R ⧸ Ideal.span {(x : R)}` have the same `Nat.card` and one is finite
   if and only if the other is (`Subring.natCard_quotient_span_singleton`,
   `Subring.finite_quotient_span_singleton_iff`).

2. **Lifting non-zero-divisors to products of infinite domains.** When `R = ∏ i, D i` is a product
   of infinite integral domains, every `x ∈ nonZeroDivisors S` already has nonzero coordinates in
   every factor, hence remains a non-zero-divisor in `∏ i, D i`
   (`Subring.mem_nonZeroDivisors_iff_forall_ne_zero`, `Subring.coe_mem_nonZeroDivisors_iff`): if
   `x i₀ = 0`, the infinite subgroup embedded in coordinate `i₀` meets `S` nontrivially by
   pigeonhole on `(∏ i, D i) ⧸ S`, producing a nonzero annihilator of `x` in `S`.

3. **Separating finite factors.** Infiniteness of the factors in (2) cannot be dropped: the
   diagonal image of `ℤ` inside `ℤ × ZMod 2` has index `2` and is a domain, yet `(2, 0)` is regular
   in the subring and a zero-divisor in `ℤ × ZMod 2`. For a general finite product `∏ i, R i`,
   projecting `S` onto the infinite factors via `Subring.restrictInfiniteHom` has finite kernel and
   finite-index image, isolating the finite torsion ideal before applying (2).

## Main definitions and results

* `Subring.finite_quotient_span_singleton_iff`, `Subring.natCard_quotient_span_singleton`:
  comparing `S ⧸ (x)` and `R ⧸ (x)` when `S` has finite index in `R` and `(x : R) ∈ R⁰`.
* `Subring.mem_nonZeroDivisors_iff_forall_ne_zero`, `Subring.coe_mem_nonZeroDivisors_iff`: in a
  finite-index subring of a product of infinite domains, `x ∈ S⁰ ↔ ∀ i, x i ≠ 0` and
  `(x : ∏ i, D i) ∈ (∏ i, D i)⁰ ↔ x ∈ S⁰`.
* `Subring.restrictInfiniteHom`, `Subring.finite_ker_restrictInfiniteHom`,
  `Subring.finiteIndex_range_restrictInfiniteHom`: projection of `S ≤ ∏ i, R i` onto the infinite
  factors, with finite kernel (for `[Finite ι]`) and finite-index range.
-/

public section

namespace Subring

section PrincipalQuotient

variable {R : Type*} [CommRing R] (S : Subring R) [S.toAddSubgroup.FiniteIndex]

/-- **Index of a principal ideal in a finite-index subring.** If `S` has finite additive index in
`R` and `(x : R)` is a non-zero-divisor in `R`, then `S ⧸ Ideal.span {x}` and
`R ⧸ Ideal.span {(x : R)}` have the same cardinality (`0` when infinite). -/
theorem natCard_quotient_span_singleton {x : S} (hx : (x : R) ∈ nonZeroDivisors R) :
    Nat.card (S ⧸ Ideal.span {x}) = Nat.card (R ⧸ Ideal.span {(x : R)}) := by
  have hrange {A : Type _} [CommRing A] (a : A) :
      (AddMonoidHom.mulRight a).range = (Ideal.span {a}).toAddSubgroup := by
    ext y
    exact Ideal.mem_span_singleton'.symm
  have hinj : Function.Injective (AddMonoidHom.mulRight (x : R)) := fun a b hab ↦
    sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hx _ (by rw [sub_mul, sub_eq_zero]; exact hab))
  have hcomp : (AddMonoidHom.mulRight (x : R)).comp S.toAddSubgroup.subtype =
      S.toAddSubgroup.subtype.comp (AddMonoidHom.mulRight x) := by
    ext y
    simpa using (Subring.coe_mul S y x).symm
  have h := AddSubgroup.natCard_quotient_range_eq_of_comp_subtype
    (H := S.toAddSubgroup) (g := AddMonoidHom.mulRight x) hinj hcomp
  rwa [hrange x, hrange (x : R)] at h

/-- If `S` has finite additive index in `R` and `(x : R)` is a non-zero-divisor in `R`, then
`S ⧸ Ideal.span {x}` is finite if and only if `R ⧸ Ideal.span {(x : R)}` is finite. -/
theorem finite_quotient_span_singleton_iff {x : S} (hx : (x : R) ∈ nonZeroDivisors R) :
    Finite (S ⧸ Ideal.span {x}) ↔ Finite (R ⧸ Ideal.span {(x : R)}) :=
  TauCeti.finite_iff_of_natCard_eq (S.natCard_quotient_span_singleton hx)

end PrincipalQuotient

section InfiniteDomains

variable {ι : Type*} {D : ι → Type*} [∀ i, CommRing (D i)] [∀ i, IsDomain (D i)]
  [∀ i, Infinite (D i)] (S : Subring (∀ i, D i)) [S.toAddSubgroup.FiniteIndex]

/-- **Non-zero-divisors in a finite-index subring of a product of infinite domains.** An element of
`S` is a non-zero-divisor in `S` if and only if all of its coordinates in `∏ i, D i` are nonzero.
The index type `ι` need not be finite. -/
theorem mem_nonZeroDivisors_iff_forall_ne_zero {x : S} :
    x ∈ nonZeroDivisors S ↔ ∀ i, (x : ∀ i, D i) i ≠ 0 := by
  classical
  refine ⟨fun hx i₀ hi₀ ↦ ?_, fun hx ↦ mem_nonZeroDivisors_iff_left.mpr fun y hy ↦ ?_⟩
  · have : Finite ((∀ i, D i) ⧸ S.toAddSubgroup) :=
      AddSubgroup.finite_quotient_of_finiteIndex
    obtain ⟨d₁, d₂, hne, hquot⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun d : D i₀ ↦ (QuotientAddGroup.mk (Pi.single i₀ d) : (∀ i, D i) ⧸ S.toAddSubgroup))
    have hmem : Pi.single i₀ (d₁ - d₂) ∈ S := by
      have hsub : -Pi.single i₀ d₁ + Pi.single i₀ d₂ ∈ S.toAddSubgroup :=
        QuotientAddGroup.eq.mp hquot
      have hneg : Pi.single i₀ d₁ - Pi.single i₀ d₂ ∈ S := by
        simpa [sub_eq_add_neg, add_comm] using S.neg_mem hsub
      rwa [← Pi.single_sub] at hneg
    let z : S := ⟨Pi.single i₀ (d₁ - d₂), hmem⟩
    have hxz : x * z = 0 := by
      ext i
      rcases eq_or_ne i i₀ with rfl | hi
      · simp [z, hi₀]
      · simp [z, Pi.single_eq_of_ne hi]
    have hz0 : z = 0 := mem_nonZeroDivisors_iff_left.mp hx z hxz
    have hd0 : d₁ - d₂ = 0 := by
      simpa [z] using congr_fun (congrArg Subtype.val hz0) i₀
    exact hne (sub_eq_zero.mp hd0)
  · ext i
    have hmul : (x : ∀ i, D i) i * (y : ∀ i, D i) i = 0 :=
      congr_fun (congrArg Subtype.val hy) i
    exact (mul_eq_zero.mp hmul).resolve_left (hx i)

/-- For a finite-index subring `S` of a product of infinite domains, `(x : ∏ i, D i)` is a
non-zero-divisor in `∏ i, D i` if and only if `x` is a non-zero-divisor in `S`. -/
theorem coe_mem_nonZeroDivisors_iff {x : S} :
    (x : ∀ i, D i) ∈ nonZeroDivisors (∀ i, D i) ↔ x ∈ nonZeroDivisors S := by
  rw [← isRegular_iff_mem_nonZeroDivisors, Pi.isRegular_iff,
    S.mem_nonZeroDivisors_iff_forall_ne_zero]
  simp [isRegular_iff_ne_zero]

end InfiniteDomains

section RestrictInfinite

variable {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)] (S : Subring (∀ i, R i))

/-- Restriction of a subring `S ≤ ∏ i, R i` to the factors `R i` that are infinite. -/
def restrictInfiniteHom : S →+* ∀ j : {i : ι // Infinite (R i)}, R j.val :=
  (RingHom.pi fun j : {i : ι // Infinite (R i)} ↦ Pi.evalRingHom R j.val).comp S.subtype

/-- Evaluating `S.restrictInfiniteHom x` at an infinite factor `j` reads coordinate `j.val`. -/
@[simp]
theorem restrictInfiniteHom_apply (x : S) (j : {i : ι // Infinite (R i)}) :
    S.restrictInfiniteHom x j = (x : ∀ i, R i) j.val :=
  (rfl)

/-- An element of `S` lies in `ker S.restrictInfiniteHom` iff it vanishes on every infinite factor.
-/
theorem mem_ker_restrictInfiniteHom {x : S} :
    x ∈ RingHom.ker S.restrictInfiniteHom ↔ ∀ i, Infinite (R i) → (x : ∀ i, R i) i = 0 := by
  simp [RingHom.mem_ker, funext_iff]

/-- When the index set `ι` is finite, the kernel of `Subring.restrictInfiniteHom` is finite, since
its elements vanish on every infinite factor and inject into the product of the finite factors. -/
instance finite_ker_restrictInfiniteHom [Finite ι] :
    Finite (RingHom.ker S.restrictInfiniteHom) := by
  have (j : {i : ι // ¬ Infinite (R i)}) : Finite (R j.val) :=
    not_infinite_iff_finite.mp j.property
  refine Finite.of_injective
    (fun x : RingHom.ker S.restrictInfiniteHom ↦
      fun j : {i : ι // ¬ Infinite (R i)} ↦ (x.val : ∀ i, R i) j.val)
    fun x y hxy ↦ ?_
  ext i
  by_cases hi : Infinite (R i)
  · exact ((S.mem_ker_restrictInfiniteHom.mp x.property) i hi).trans
      ((S.mem_ker_restrictInfiniteHom.mp y.property) i hi).symm
  · exact congr_fun hxy ⟨i, hi⟩

/-- If `S` has finite additive index in `∏ i, R i`, its image under `Subring.restrictInfiniteHom`
has finite additive index in `∏ j : {i // Infinite (R i)}, R j`. -/
instance finiteIndex_range_restrictInfiniteHom [S.toAddSubgroup.FiniteIndex] :
    S.restrictInfiniteHom.range.toAddSubgroup.FiniteIndex := by
  classical
  let proj : (∀ i, R i) →+* ∀ j : {i : ι // Infinite (R i)}, R j.val :=
    RingHom.pi fun j ↦ Pi.evalRingHom R j.val
  have hsurj : Function.Surjective proj.toAddMonoidHom := fun y ↦
    ⟨fun i ↦ if hi : Infinite (R i) then y ⟨i, hi⟩ else 0,
      funext fun j ↦ by simp [proj, j.property]⟩
  have hrange : S.restrictInfiniteHom.range.toAddSubgroup =
      S.toAddSubgroup.map proj.toAddMonoidHom := by
    ext y
    simp [restrictInfiniteHom, proj]
  rw [hrange]
  exact AddSubgroup.FiniteIndex.map_of_surjective S.toAddSubgroup hsurj

end RestrictInfinite

end Subring

section Counterexample

-- Infiniteness of every factor cannot be omitted in `Subring.coe_mem_nonZeroDivisors_iff`:
-- the diagonal image of `ℤ` inside `ℤ × ZMod 2` has finite index (`2`) and is a domain, so
-- `(2, 0)` is regular in the subring, yet `(2, 0) * (0, 1) = 0` in `ℤ × ZMod 2`.
example :
    let S : Subring (ℤ × ZMod 2) :=
      (RingHom.prod (RingHom.id ℤ) (Int.castRingHom (ZMod 2))).range
    S.toAddSubgroup.FiniteIndex ∧
      ∃ x : S, x ∈ nonZeroDivisors S ∧ (x : ℤ × ZMod 2) ∉ nonZeroDivisors (ℤ × ZMod 2) := by
  intro S
  have hindex : S.toAddSubgroup.FiniteIndex := by
    refine @AddSubgroup.finiteIndex_of_finite_quotient _ _ S.toAddSubgroup ?_
    refine Finite.of_surjective
      (fun b : ZMod 2 ↦ (QuotientAddGroup.mk ((0 : ℤ), b) : (ℤ × ZMod 2) ⧸ S.toAddSubgroup))
      fun q ↦ ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨b - (a : ZMod 2), QuotientAddGroup.eq.mpr ?_⟩
    exact ⟨a, by ext <;> simp⟩
  refine ⟨hindex, ⟨(2, 0), ⟨2, by ext <;> rfl⟩⟩, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_left]
    rintro ⟨_, ⟨n, rfl⟩⟩ hmul
    have h2n : (2 : ℤ) * n = 0 := congrArg (Prod.fst ∘ Subtype.val) hmul
    have hn : n = 0 := (mul_eq_zero.mp h2n).resolve_left (by decide)
    subst hn
    ext <;> simp
  · intro hmem
    have h0 : ((0 : ℤ), (1 : ZMod 2)) = 0 :=
      mem_nonZeroDivisors_iff_left.mp hmem (0, 1) (by ext <;> simp)
    exact one_ne_zero (congrArg Prod.snd h0)

end Counterexample
