/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import TauCeti.LinearAlgebra.Trace.Basic
public import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# The trace modulo an ideal

Let `S` be a finite free `R`-algebra and `I` an ideal of `R`. The trace of `S ⧸ IS` over `R ⧸ I`
of the class of `x` is the class of the trace of `x`. Mathlib's `Algebra.trace_quotient_mk` is the
case where `R` is local and `I` is its maximal ideal; here `I` is arbitrary, which is what a
computation of the trace modulo a power `𝔪 ^ n` of a maximal ideal needs. It is the trace
counterpart of `TauCeti.Algebra.norm_quotient_mk`.

It also computes the trace modulo `I` of an element whose multiplication maps `S ⧸ IS` into a
free submodule with a known basis, such as a summand of `S ⧸ IS` through which it acts, which is
how the trace of a finite extension of function fields is computed locally at one place.

## Main results

* `TauCeti.Algebra.trace_quotient_map_mk`: the trace of `S ⧸ IS` over `R ⧸ I` of the class of `x`
  is the class of the trace of `x`.
* `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`: if, modulo `IS`, multiplication
  by `z` maps into the span of linearly independent `b j` and acts on them by the matrix `a`,
  then `Tr_{S/R} z ≡ ∑ j, a j j` modulo `I`.
* `TauCeti.Algebra.trace_sub_one_mem_of_mul_self_sub_mem`: its rank-one case, an idempotent of
  rank one modulo `I` has trace `1` modulo `I`.
-/

public section

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

/-- **The trace commutes with reduction modulo an ideal.** For a finite free algebra `S` over `R`
and an ideal `I` of `R`, the trace of `S ⧸ IS` over `R ⧸ I` of the class of `x` is the class of the
trace of `x`. -/
@[simp]
theorem Algebra.trace_quotient_map_mk (I : Ideal R) (x : S) :
    Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk I (Algebra.trace R S x) := by
  -- `S ⧸ IS` is the base change `(R ⧸ I) ⊗[R] S`, on which multiplication by `1 ⊗ x` is the base
  -- change of multiplication by `x`; the trace commutes with base change.
  rw [← Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I),
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.trace_apply, Algebra.trace_apply,
    ← Ideal.Quotient.algebraMap_eq, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]

/-- The trace of an element of `IS` lies in `I`. -/
theorem Algebra.trace_mem_of_mem_map {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    Algebra.trace R S x ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← trace_quotient_map_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- **The trace on a free submodule with a known basis, modulo an ideal.** Let `J = IS`. Suppose
that modulo `J`, multiplication by `z` maps `S` into the span of the `b j`, that the `b j` are
linearly independent over `R ⧸ I`, and that `z` acts on them by the matrix `a`: every `z * s` is
congruent to some `∑ c j * b j`, `∑ c j * b j ∈ J` only when every `c j ∈ I`, and
`z * b j ≡ ∑ l, a j l * b l`. Then `Tr_{S/R} z ≡ ∑ j, a j j` modulo `I`.

Modulo `J`, the class of `z` maps `S ⧸ J` into the submodule spanned by the classes of the `b j`,
which is free with that basis, so its trace is the trace of the matrix `a`. No hypothesis on
`R ⧸ I` is needed: the basis of that submodule is given. Typically `z` acts through a projection
`w` onto a summand of `S ⧸ J`, that is `z * w ≡ z`, and every `w * s` lies in the span of the
`b j`. -/
theorem Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem {ι : Type*} [Fintype ι]
    {I : Ideal R} {z : S} {b : ι → S} {a : ι → ι → R}
    (hspan : ∀ s : S, ∃ c : ι → R,
      z * s - ∑ j, algebraMap R S (c j) * b j ∈ I.map (algebraMap R S))
    (hindep : ∀ c : ι → R, ∑ j, algebraMap R S (c j) * b j ∈ I.map (algebraMap R S) →
      ∀ j, c j ∈ I)
    (hzb : ∀ j, z * b j - ∑ l, algebraMap R S (a j l) * b l ∈ I.map (algebraMap R S)) :
    Algebra.trace R S z - ∑ j, a j j ∈ I := by
  classical
  set J := I.map (algebraMap R S)
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  have : Module.Free (R ⧸ I) (S ⧸ J) := .of_equiv e.symm.toLinearEquiv
  have : Module.Finite (R ⧸ I) (S ⧸ J) := .equiv e.symm.toLinearEquiv
  -- The classes of the `b j` give an injective linear map `φ : (ι → R ⧸ I) → S ⧸ J`.
  let φ : (ι → R ⧸ I) →ₗ[R ⧸ I] S ⧸ J :=
    Fintype.linearCombination (R ⧸ I) fun j ↦ Ideal.Quotient.mk J (b j)
  have hφ (c : ι → R) : φ (fun j ↦ Ideal.Quotient.mk I (c j)) =
      Ideal.Quotient.mk J (∑ j, algebraMap R S (c j) * b j) :=
    Ideal.Quotient.linearCombination_mk_map_apply I b c
  have hlift : Function.Surjective fun (c : ι → R) j ↦ Ideal.Quotient.mk I (c j) :=
    .piMap fun _ ↦ Ideal.Quotient.mk_surjective
  have hφinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun c hc ↦ ?_
    obtain ⟨c, rfl⟩ := hlift c
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem] at hc
    exact funext fun j ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hindep c hc j)
  -- Multiplication by the class of `z` lands in the range of `φ`, and acts there by `a`.
  let L := Algebra.lmul (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J z)
  have hLa (s : S ⧸ J) : L s = Ideal.Quotient.mk J z * s := rfl
  have hrange : LinearMap.range L ≤ LinearMap.range φ := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨c, hc⟩ := hspan s
    refine ⟨fun j ↦ Ideal.Quotient.mk I (c j), ?_⟩
    rw [hφ, hLa, ← map_mul]
    exact (Ideal.Quotient.eq.mpr hc).symm
  have hL (j : ι) : L (φ (Pi.single j 1)) = φ fun l ↦ Ideal.Quotient.mk I (a j l) := by
    have hb : φ (Pi.single j 1) = Ideal.Quotient.mk J (b j) := by
      simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
    rw [hb, hφ, hLa, ← map_mul]
    exact Ideal.Quotient.eq.mpr (hzb j)
  have htr := LinearMap.trace_eq_sum_of_range_le_of_apply_single_eq hφinj hrange hL
  rw [← Ideal.Quotient.eq, map_sum, ← trace_quotient_map_mk]
  exact htr

/-- **An idempotent of rank one modulo an ideal has trace one.** Suppose the class of `w` in
`S ⧸ IS` is idempotent, and that the ideal it generates is free of rank one over `R ⧸ I` with basis
that class: every `w * b` is congruent to some `c * w` with `c ∈ R`, and `c * w ∈ IS` only for
`c ∈ I`. Then `Tr_{S/R} w ≡ 1` modulo `I`.

This is the rank-one case of `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem` for
`z = w`, with the single basis vector `w` on which `w` acts by `1`. -/
theorem Algebra.trace_sub_one_mem_of_mul_self_sub_mem {I : Ideal R} {w : S}
    (hw : w * w - w ∈ I.map (algebraMap R S))
    (hspan : ∀ b : S, ∃ c : R, w * b - algebraMap R S c * w ∈ I.map (algebraMap R S))
    (hinj : ∀ c : R, algebraMap R S c * w ∈ I.map (algebraMap R S) → c ∈ I) :
    Algebra.trace R S w - 1 ∈ I := by
  simpa using Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem (ι := Unit) (z := w)
    (b := fun _ ↦ w) (a := fun _ _ ↦ 1)
    (fun s ↦ let ⟨c, hc⟩ := hspan s; ⟨fun _ ↦ c, by simpa using hc⟩)
    (fun c hc _ ↦ hinj (c ()) (by simpa using hc)) (fun _ ↦ by simpa using hw)

end TauCeti
