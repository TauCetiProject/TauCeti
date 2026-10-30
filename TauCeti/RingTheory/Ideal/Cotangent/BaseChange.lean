/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.CotangentBaseChange

/-!
# Relations in the cotangent space after flat base change

Let `S` be a flat `R`-algebra and `I` an ideal of `R`. Mathlib's
`Ideal.tensorCotangentHom_injective_of_flat` says that `S ⊗[R] I / I²` embeds into the cotangent
space of the extended ideal of `S ⊗[R] R`. Transporting along `S ⊗[R] R ≃ S`, this file states
the result as a criterion inside `S`: an element `∑ cᵢ ⊗ xᵢ` of `S ⊗[R] I / I²` vanishes if and
only if `∑ cᵢ xᵢ` lies in `(IS)²`.

## Main results

* `Ideal.sum_tmul_toCotangent_eq_zero_iff_of_flat`: over a flat `R`-algebra `S`,
  `∑ cᵢ ⊗ xᵢ = 0` in `S ⊗[R] I / I²` if and only if `∑ cᵢ xᵢ ∈ (IS)²`.
-/

public section

open TensorProduct

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Over a flat `R`-algebra `S`, an element `∑ cᵢ ⊗ xᵢ` of `S ⊗[R] I / I²` vanishes if and only
if `∑ cᵢ xᵢ` lies in the square of the extension of `I` to `S`. -/
theorem sum_tmul_toCotangent_eq_zero_iff_of_flat [Module.Flat R S] (I : Ideal R) {ι : Type*}
    (t : Finset ι) (c : ι → S) (x : ι → I) :
    ∑ i ∈ t, c i ⊗ₜ[R] I.toCotangent (x i) = 0 ↔
      ∑ i ∈ t, c i * algebraMap R S (x i) ∈ I.map (algebraMap R S) ^ 2 := by
  -- Transport the membership in `S ⊗[R] R` along `S ⊗[R] R ≃ S`.
  let e := (Algebra.TensorProduct.rid R S S).toRingEquiv
  have he : (e : S ⊗[R] R →+* S).comp Algebra.TensorProduct.includeRight.toRingHom =
      algebraMap R S := by ext; simp [e, Algebra.smul_def]
  rw [← (tensorCotangentHom_injective_of_flat R S I).eq_iff, map_zero, map_sum]
  simp only [tensorCotangentHom_tmul, ← LinearMap.map_smul_of_tower, ← map_sum,
    toCotangent_eq_zero, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [← apply_mem_of_equiv_iff (f := e), Ideal.map_pow, ← Ideal.map_coe, Ideal.map_map, he]
  simp [e, Algebra.smul_def, mul_comm]

end Ideal
