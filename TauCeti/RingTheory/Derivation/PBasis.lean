/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.FieldTheory.Frobenius.PBasis
public import TauCeti.RingTheory.Derivation.Frobenius
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Derivations and `p`-bases

Given a `p`-basis `b : ι → k` of a field `k` of prime characteristic `p`, the `p`-monomials
`∏ i, b i ^ (e i : ℕ)` (`e : ι →₀ Fin p`) form a basis of `k` over `k ^ p`. Differentiating
each `p`-monomial in the `j`-th variable—returning `0` when `e j = 0`, and otherwise decrementing
that exponent and multiplying by its original value to give
`(e j : k) * ∏ i, b i ^ (e i - δ_{ij} : ℕ)`—defines a `k ^ p`-derivation `hb.coordDerivation j`
satisfying `hb.coordDerivation j (b j) = 1` and `hb.coordDerivation j (b i) = 0` for `i ≠ j`.

Conversely, any `R`-derivation out of `k` maps `k ^ p(range b)` into the `k`-span of its values
on `b`, and two `R`-derivations out of `k` agreeing on a `p`-basis are equal.

## Main definitions

* `TauCeti.IsPBasis.coordDerivation`: the coordinate `k ^ p`-derivation associated to a member of a
  `p`-basis.

## Main results

* `Derivation.map_mem_span_of_mem_adjoin`: derivatives on `k ^ p(range b)` lie in the `k`-span of
  the derivatives of `b`.
* `TauCeti.IsPBasis.derivation_ext`: two `R`-derivations out of `k` into a `k`-module that agree
  on a `p`-basis are equal.
* `TauCeti.IsPBasis.coordDerivation_apply_pMonomial`: evaluation of `coordDerivation` on a
  `p`-monomial.
* `TauCeti.IsPBasis.coordDerivation_apply_self`: `hb.coordDerivation j (b j) = 1`.
* `TauCeti.IsPBasis.coordDerivation_apply_ne`: `hb.coordDerivation j (b i) = 0` for `i ≠ j`.
-/

public section

noncomputable section

namespace TauCeti

section CoordDerivation

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [ExpChar k p] {ι : Type*}

private def coordDerivationLinear {b : ι → k} (hb : IsPBasis p b) (j : ι) :
    k →ₗ[(frobenius k p).fieldRange] k :=
  hb.basis.constr (frobenius k p).fieldRange fun e ↦
    ((e j : ℕ) : k) * pMonomial p b (e - Finsupp.single j ⟨1, (Fact.out : p.Prime).one_lt⟩)

private theorem coordDerivationLinear_apply_pMonomial {b : ι → k} (hb : IsPBasis p b) (j : ι)
    (e : ι →₀ Fin p) :
    coordDerivationLinear hb j (pMonomial p b e) =
      ((e j : ℕ) : k) * pMonomial p b (e - Finsupp.single j ⟨1, (Fact.out : p.Prime).one_lt⟩) := by
  rw [← hb.basis_apply, coordDerivationLinear, hb.basis.constr_basis]

private theorem mul_coordDerivationLinear_pMonomial {b : ι → k} (hb : IsPBasis p b) (j : ι)
    (e : ι →₀ Fin p) :
    b j * coordDerivationLinear hb j (pMonomial p b e) = ((e j : ℕ) : k) * pMonomial p b e := by
  rw [coordDerivationLinear_apply_pMonomial]
  by_cases hj : e j = 0
  · simp [hj]
  · rw [mul_left_comm, mul_pMonomial_sub_single p (Fact.out : p.Prime).one_lt b e hj]

private theorem coordDerivationLinear_leibniz_pMonomial {b : ι → k} (hb : IsPBasis p b) (j : ι)
    (e e' : ι →₀ Fin p) :
    coordDerivationLinear hb j (pMonomial p b e * pMonomial p b e') =
      pMonomial p b e * coordDerivationLinear hb j (pMonomial p b e') +
        pMonomial p b e' * coordDerivationLinear hb j (pMonomial p b e) := by
  have : CharP k p := (expChar_prime_iff k Fact.out).mp ‹_›
  obtain ⟨c, hc⟩ := exists_mul_pMonomial_eq_pow_mul_pMonomial_add p b e e'
  have hsmul : coordDerivationLinear hb j (c ^ p * pMonomial p b (e + e')) =
      c ^ p * coordDerivationLinear hb j (pMonomial p b (e + e')) :=
    (coordDerivationLinear hb j).map_smul ⟨c ^ p, c, frobenius_def ..⟩ (pMonomial p b (e + e'))
  refine mul_left_cancel₀ (hb.isPIndependent.ne_zero j) ?_
  calc
    b j * coordDerivationLinear hb j (pMonomial p b e * pMonomial p b e')
        = c ^ p * (b j * coordDerivationLinear hb j (pMonomial p b (e + e'))) := by
          rw [hc, hsmul, mul_left_comm]
    _ = (((e + e') j : ℕ) : k) * (pMonomial p b e * pMonomial p b e') := by
          rw [mul_coordDerivationLinear_pMonomial, hc]; ring
    _ = (((e j : ℕ) : k) + ((e' j : ℕ) : k)) * (pMonomial p b e * pMonomial p b e') := by
          rw [Finsupp.add_apply, Fin.val_add, ← CharP.cast_eq_mod k p, Nat.cast_add]
    _ = b j * (pMonomial p b e * coordDerivationLinear hb j (pMonomial p b e') +
          pMonomial p b e' * coordDerivationLinear hb j (pMonomial p b e)) := by
          rw [mul_add, mul_left_comm (b j) (pMonomial p b e), mul_coordDerivationLinear_pMonomial,
            mul_left_comm (b j) (pMonomial p b e'), mul_coordDerivationLinear_pMonomial]
          ring

private theorem coordDerivationLinear_leibniz {b : ι → k} (hb : IsPBasis p b) (j : ι) (x y : k) :
    coordDerivationLinear hb j (x * y) =
      x * coordDerivationLinear hb j y + y * coordDerivationLinear hb j x := by
  let R := (frobenius k p).fieldRange
  let f := coordDerivationLinear hb j
  let mul := LinearMap.mul R k
  let B₁ : k →ₗ[R] k →ₗ[R] k := mul.compr₂ f
  let B₂ : k →ₗ[R] k →ₗ[R] k := mul.compl₂ f + (mul.compl₂ f).flip
  have heq : B₁ = B₂ := hb.basis.ext fun e ↦ hb.basis.ext fun e' ↦ by
    rw [hb.basis_apply, hb.basis_apply]
    rw [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.compl₂_apply, LinearMap.flip_apply, LinearMap.compl₂_apply,
      LinearMap.mul_apply', LinearMap.mul_apply']
    exact coordDerivationLinear_leibniz_pMonomial hb j e e'
  exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y

/-- The `j`-th coordinate `k ^ p`-derivation associated to a `p`-basis `b : ι → k`, returning `0`
on `∏ i, b i ^ (e i)` when `e j = 0`, and otherwise decrementing the `j`-th exponent and
multiplying by its original value `(e j : k) * ∏ i, b i ^ (e i - δ_{ij})`. -/
def IsPBasis.coordDerivation {b : ι → k} (hb : IsPBasis p b) (j : ι) :
    Derivation (frobenius k p).fieldRange k k :=
  Derivation.mk' (coordDerivationLinear hb j) (coordDerivationLinear_leibniz hb j)

/-- Evaluating `IsPBasis.coordDerivation` on a `p`-monomial returns `0` when `e j = 0`, and
otherwise decrements the `j`-th exponent and multiplies by its original value. -/
theorem IsPBasis.coordDerivation_apply_pMonomial {b : ι → k} (hb : IsPBasis p b) (j : ι)
    (e : ι →₀ Fin p) :
    hb.coordDerivation j (pMonomial p b e) =
      ((e j : ℕ) : k) * pMonomial p b (e - Finsupp.single j ⟨1, (Fact.out : p.Prime).one_lt⟩) :=
  coordDerivationLinear_apply_pMonomial hb j e

/-- The `j`-th coordinate derivation maps `b j` to `1`. -/
@[simp]
theorem IsPBasis.coordDerivation_apply_self {b : ι → k} (hb : IsPBasis p b) (j : ι) :
    hb.coordDerivation j (b j) = 1 := by
  have h := hb.coordDerivation_apply_pMonomial j
    (Finsupp.single j ⟨1, (Fact.out : p.Prime).one_lt⟩)
  simpa using h

/-- The `j`-th coordinate derivation vanishes on `b i` for `i ≠ j`. -/
@[simp]
theorem IsPBasis.coordDerivation_apply_ne {b : ι → k} (hb : IsPBasis p b) {i j : ι}
    (hij : i ≠ j) : hb.coordDerivation j (b i) = 0 := by
  have h := hb.coordDerivation_apply_pMonomial j
    (Finsupp.single i ⟨1, (Fact.out : p.Prime).one_lt⟩)
  simpa [Finsupp.single_apply, hij] using h

end CoordDerivation

section Ext

variable {p : ℕ} [Fact p.Prime] {R k : Type*} [CommSemiring R] [Field k] [ExpChar k p]
  [Algebra R k] {ι : Type*}

/-- For any family `b : ι → k` and any `R`-derivation `d : Derivation R k M` into a `k`-module,
every element of the intermediate field `k ^ p(range b)` has derivative in the `k`-linear span of
`{d (b i)}`. -/
theorem _root_.Derivation.map_mem_span_of_mem_adjoin {M : Type*} [AddCommMonoid M] [Module R M]
    [Module k M] (d : Derivation R k M) (b : ι → k) {x : k}
    (hx : x ∈ IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b)) :
    d x ∈ Submodule.span k (Set.range fun i ↦ d (b i)) := by
  set S : Submodule k M := Submodule.span k (Set.range fun i ↦ d (b i))
  rw [← IntermediateField.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    ← span_range_pMonomial_eq_adjoin] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨e, rfl⟩ := hu
    rw [pMonomial_def, Finsupp.prod]
    induction e.support using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih =>
      rw [Finset.prod_cons, d.leibniz]
      refine S.add_mem (S.smul_mem _ ih) (S.smul_mem _ ?_)
      rw [d.leibniz_pow, ← Nat.cast_smul_eq_nsmul k]
      exact S.smul_mem _ (S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact S.add_mem hu hv
  | smul c u _ hu =>
    rw [Subfield.smul_def, smul_eq_mul, d.leibniz,
      d.map_eq_zero_of_mem_fieldRange_frobenius c.property, smul_zero, add_zero]
    exact S.smul_mem (c : k) hu

/-- Two `R`-derivations out of `k` into a `k`-module that agree on a `p`-basis `b` are equal. -/
theorem IsPBasis.derivation_ext {b : ι → k} (hb : IsPBasis p b) {M : Type*} [AddCommMonoid M]
    [Module R M] [Module k M] {d₁ d₂ : Derivation R k M} (h : ∀ i, d₁ (b i) = d₂ (b i)) :
    d₁ = d₂ := by
  have : IsScalarTower (frobenius k p).fieldRange k M :=
    ⟨fun c x m ↦ by rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_smul]⟩
  let d₁' : Derivation (frobenius k p).fieldRange k M :=
    d₁.ofMapAlgebraMap fun c ↦ d₁.map_eq_zero_of_mem_fieldRange_frobenius c.property
  let d₂' : Derivation (frobenius k p).fieldRange k M :=
    d₂.ofMapAlgebraMap fun c ↦ d₂.map_eq_zero_of_mem_fieldRange_frobenius c.property
  have hadj : Algebra.adjoin (frobenius k p).fieldRange (Set.range b) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x _ ↦
      (IsIntegral.of_pow (Fact.out : p.Prime).pos
        (isIntegral_algebraMap
          (x := (⟨x ^ p, x, frobenius_def ..⟩ : (frobenius k p).fieldRange)))).isAlgebraic,
      hb.adjoin_eq_top, IntermediateField.top_toSubalgebra]
  have heq : d₁' = d₂' :=
    Derivation.ext_of_adjoin_eq_top (Set.range b) hadj (by rintro _ ⟨i, rfl⟩; simp [d₁', d₂', h i])
  ext x
  simpa [d₁', d₂'] using congrArg (fun d : Derivation (frobenius k p).fieldRange k M ↦ d x) heq

end Ext

end TauCeti

end
