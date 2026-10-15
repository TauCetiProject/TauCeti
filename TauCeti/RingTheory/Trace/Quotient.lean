/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The trace modulo an ideal

Let `S` be a finite free `R`-algebra and `I` an ideal of `R`. The trace of `S ⧸ IS` over `R ⧸ I`
of the class of `x` is the class of the trace of `x`. Mathlib's `Algebra.trace_quotient_mk` is the
case where `R` is local and `I` is its maximal ideal; here `I` is arbitrary, which is what a
computation of the trace modulo a power `𝔪 ^ n` of a maximal ideal needs. It is the trace
counterpart of `TauCeti.Algebra.norm_quotient_mk`.

It also computes the trace modulo `I` of an element acting through a summand of `S ⧸ IS` with a
known basis, which is how the trace of a finite extension of function fields is computed locally
at one place.

## Main results

* `TauCeti.Algebra.trace_quotient_map_mk`: the trace of `S ⧸ IS` over `R ⧸ I` of the class of `x`
  is the class of the trace of `x`.
* `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`: if, modulo `IS`, multiplication
  by `w` projects onto the span of linearly independent `b j`, and `z` acts through that
  projection by the matrix `a`, then `Tr_{S/R} z ≡ ∑ j, a j j` modulo `I`.
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
    ← Ideal.Quotient.algebraMap_eq, ← LinearMap.trace_baseChange]
  congr 1
  ext y
  simp

/-- The trace of an element of `IS` lies in `I`. -/
theorem Algebra.trace_mem_of_mem_map {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    Algebra.trace R S x ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← trace_quotient_map_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- **The trace on a summand with a known basis, modulo an ideal.** Let `J = IS`. Suppose that
modulo `J`, multiplication by `w` maps `S` onto the span of `b j`, fixes every `b j`, and that the
`b j` are linearly independent over `R ⧸ I`: every `w * s` is congruent to some `∑ c j * b j`, and
`∑ c j * b j ∈ J` only when every `c j ∈ I`. If `z` is congruent to `z * w` and acts on the `b j`
by the matrix `a`, that is `z * b j ≡ ∑ l, a j l * b l`, then `Tr_{S/R} z ≡ ∑ j, a j j` modulo `I`.

Modulo `J`, the class of `z` acts through the projection `w`, whose range is free with basis the
classes of the `b j`, so its trace is the trace of the matrix `a`. No hypothesis on `R ⧸ I` is
needed: the basis of the range is given. -/
theorem Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem {ι : Type*} [Fintype ι]
    {I : Ideal R} {w z : S} {b : ι → S} {a : ι → ι → R}
    (hwb : ∀ j, w * b j - b j ∈ I.map (algebraMap R S))
    (hspan : ∀ s : S, ∃ c : ι → R,
      w * s - ∑ j, algebraMap R S (c j) * b j ∈ I.map (algebraMap R S))
    (hindep : ∀ c : ι → R, ∑ j, algebraMap R S (c j) * b j ∈ I.map (algebraMap R S) →
      ∀ j, c j ∈ I)
    (hz : z * w - z ∈ I.map (algebraMap R S))
    (hzb : ∀ j, z * b j - ∑ l, algebraMap R S (a j l) * b l ∈ I.map (algebraMap R S)) :
    Algebra.trace R S z - ∑ j, a j j ∈ I := by
  classical
  set J := I.map (algebraMap R S)
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  have : Module.Free (R ⧸ I) (S ⧸ J) := .of_equiv e.symm.toLinearEquiv
  have : Module.Finite (R ⧸ I) (S ⧸ J) := .equiv e.symm.toLinearEquiv
  have hmk (c : R) : Ideal.Quotient.mk J (algebraMap R S c) =
      algebraMap (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk I c) :=
    (Ideal.Quotient.algebraMap_quotient_map_quotient c).symm
  -- The classes of the `b j` give a linear map `φ : (ι → R ⧸ I) → S ⧸ J`.
  let φ : (ι → R ⧸ I) →ₗ[R ⧸ I] S ⧸ J :=
    Fintype.linearCombination (R ⧸ I) fun j ↦ Ideal.Quotient.mk J (b j)
  have hφ (c : ι → R) : φ (fun j ↦ Ideal.Quotient.mk I (c j)) =
      Ideal.Quotient.mk J (∑ j, algebraMap R S (c j) * b j) := by
    simp [φ, Fintype.linearCombination_apply, map_sum, hmk, Algebra.smul_def]
  have hlift (c : ι → R ⧸ I) : ∃ c' : ι → R, (fun j ↦ Ideal.Quotient.mk I (c' j)) = c :=
    ⟨fun j ↦ (Ideal.Quotient.mk_surjective (c j)).choose,
      funext fun j ↦ (Ideal.Quotient.mk_surjective (c j)).choose_spec⟩
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨c, rfl⟩ := hlift c
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem] at hc
    exact funext fun j ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hindep c hc j)
  -- Multiplication by the class of `w` lands in the range of `φ` and fixes it.
  let W := Algebra.lmul (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J w)
  have hWa (s : S ⧸ J) : W s = Ideal.Quotient.mk J w * s := rfl
  have hW (s : S ⧸ J) : W s ∈ LinearMap.range φ := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨c, hc⟩ := hspan s
    refine ⟨fun j ↦ Ideal.Quotient.mk I (c j), ?_⟩
    rw [hφ]
    exact (Ideal.Quotient.eq.mpr hc).symm
  have hWφ (c : ι → R ⧸ I) : W (φ c) = φ c := by
    obtain ⟨c, rfl⟩ := hlift c
    rw [hφ, hWa, ← map_mul, Finset.mul_sum]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← Finset.sum_sub_distrib]
    exact J.sum_mem fun j _ ↦ by
      rw [mul_left_comm, ← mul_sub]
      exact J.mul_mem_left _ (hwb j)
  -- So `W = φ ∘ ρ` with `ρ ∘ φ = id`.
  let ψ := LinearEquiv.ofInjective φ hφinj
  let ρ : S ⧸ J →ₗ[R ⧸ I] ι → R ⧸ I :=
    ψ.symm.toLinearMap ∘ₗ W.codRestrict (LinearMap.range φ) hW
  have hφρ' (s : S ⧸ J) : φ (ρ s) = W s := by
    have h := congrArg Subtype.val (ψ.apply_symm_apply ⟨W s, hW s⟩)
    rwa [LinearEquiv.ofInjective_apply] at h
  have hφρ : φ ∘ₗ ρ = W := LinearMap.ext hφρ'
  have hρφ (c : ι → R ⧸ I) : ρ (φ c) = c := hφinj (by rw [hφρ', hWφ])
  -- The class of `z` acts through `W`.
  let L := Algebra.lmul (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J z)
  have hL : Algebra.lmul (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J z) = L := rfl
  have hLa (s : S ⧸ J) : L s = Ideal.Quotient.mk J z * s := rfl
  have hLW : L ∘ₗ W = L := by
    refine LinearMap.ext fun s ↦ ?_
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [LinearMap.comp_apply, hLa, hLa, hWa, ← map_mul, ← map_mul, ← map_mul]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← mul_assoc, ← sub_mul]
    exact J.mul_mem_right _ hz
  -- On the coordinates, `z` acts by the transpose of `a`.
  have hmat : ρ ∘ₗ L ∘ₗ φ =
      Matrix.toLin' (Matrix.of fun l j ↦ Ideal.Quotient.mk I (a j l)) := by
    ext j l
    have hb : φ (Pi.single j 1) = Ideal.Quotient.mk J (b j) := by
      simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
    have hzbj : L (Ideal.Quotient.mk J (b j)) = φ fun l ↦ Ideal.Quotient.mk I (a j l) := by
      rw [hφ, hLa, ← map_mul]
      exact Ideal.Quotient.eq.mpr (hzb j)
    simp only [LinearMap.comp_apply, LinearMap.coe_single, hb, hzbj, hρφ, Matrix.toLin'_apply,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.of_apply]
  have htr : Algebra.trace (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J z) =
      ∑ j, Ideal.Quotient.mk I (a j j) := by
    rw [Algebra.trace_apply, hL, ← hLW, ← hφρ, ← LinearMap.comp_assoc,
      LinearMap.trace_comp_comm', hmat, Matrix.trace_toLin'_eq]
    simp [Matrix.trace]
  rw [← Ideal.Quotient.eq, map_sum, ← trace_quotient_map_mk, htr]

/-- **An idempotent of rank one modulo an ideal has trace one.** Suppose the class of `w` in
`S ⧸ IS` is idempotent, and that the ideal it generates is free of rank one over `R ⧸ I` with basis
that class: every `w * b` is congruent to some `c * w` with `c ∈ R`, and `c * w ∈ IS` only for
`c ∈ I`. Then `Tr_{S/R} w ≡ 1` modulo `I`.

This is the rank-one case of `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`, with
the single basis vector `w` acting on itself by `1`. -/
theorem Algebra.trace_sub_one_mem_of_mul_self_sub_mem {I : Ideal R} {w : S}
    (hw : w * w - w ∈ I.map (algebraMap R S))
    (hspan : ∀ b : S, ∃ c : R, w * b - algebraMap R S c * w ∈ I.map (algebraMap R S))
    (hinj : ∀ c : R, algebraMap R S c * w ∈ I.map (algebraMap R S) → c ∈ I) :
    Algebra.trace R S w - 1 ∈ I := by
  simpa using Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem (ι := Unit) (w := w) (z := w)
    (b := fun _ ↦ w) (a := fun _ _ ↦ 1) (fun _ ↦ hw)
    (fun s ↦ let ⟨c, hc⟩ := hspan s; ⟨fun _ ↦ c, by simpa using hc⟩)
    (fun c hc _ ↦ hinj (c ()) (by simpa using hc)) hw (fun _ ↦ by simpa using hw)

end TauCeti
