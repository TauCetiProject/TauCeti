/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.VectorValued
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace

/-!
# The divergence of a Bianchi family of two-forms in dimension four

Let `E` be an oriented real inner product space of dimension four and `W` a real vector space. A
family of `W`-valued two-forms depending linearly on a vector, `T : E →ₗ[ℝ] (⋀² E →ₗ[ℝ] W)`,
satisfies the **Bianchi identity** when

`T u (v ∧ w) + T v (w ∧ u) + T w (u ∧ v) = 0`

for all `u, v, w`. This is the pointwise form of the closedness `dF = 0` of a two-form `F`, read on
the covariant derivative `T v = ∇_v F`, and of the second Bianchi identity
`(∇_u R)(v, w) + (∇_v R)(w, u) + (∇_w R)(u, v) = 0` for the curvature `R` of a connection. Its
**divergence** along an orthonormal basis `(eᵢ)` is `a ↦ ∑ᵢ T eᵢ (a ∧ eᵢ)`; for `T v = ∇_v F` this
is `(d^* F)(a)`, with the convention `d^* F = -∑ᵢ ι_{eᵢ} ∇_{eᵢ} F`.

The Hodge star of `W`-valued forms (`Orientation.vectorFormHodgeStar`) acts on the form side. This
file shows that the divergence of the Hodge dual of a Bianchi family vanishes
(`Orientation.sum_vectorFormHodgeStar_apply_ιMulti_eq_zero`):

`∑ᵢ (⋆T eᵢ) (a ∧ eᵢ) = 0`,

the pointwise form of `d^* ⋆F = ± ⋆ d F = 0`. In coordinates,
`(⋆T eᵢ) (a ∧ eᵢ) = ½ ∑ₖ ∑ₗ vol(a, eᵢ, eₖ, eₗ) T eᵢ (eₖ ∧ eₗ)`, and the coefficient
`vol(a, eᵢ, eₖ, eₗ)` is invariant under cyclic permutations of `(i, k, l)`, so summing over all
`(i, k, l)` only sees the cyclic sums of `T`, which vanish
(`Fintype.sum_sum_sum_smul_eq_zero_of_cyclic`).

Consequently the divergence of a Bianchi family is carried equally by its self-dual and
anti-self-dual parts `T⁺ = (T + ⋆T) / 2` and `T⁻ = (T - ⋆T) / 2`
(`Orientation.vectorFormSelfDualPart`, `Orientation.vectorFormAntiSelfDualPart`):

`∑ᵢ T eᵢ (a ∧ eᵢ) = 2 ∑ᵢ T⁺ eᵢ (a ∧ eᵢ) = 2 ∑ᵢ T⁻ eᵢ (a ∧ eᵢ)`

(`Orientation.sum_apply_ιMulti_eq_two_smul_sum_vectorFormSelfDualPart`,
`Orientation.sum_apply_ιMulti_eq_two_smul_sum_vectorFormAntiSelfDualPart`). For the curvature of a
connection this is the identity `d_∇^* F = 2 d_∇^* F⁺ = 2 d_∇^* F⁻` of four-dimensional gauge
theory: an equation prescribing the self-dual part of the curvature, such as the curvature
equation of the Seiberg–Witten equations, controls the divergence of the whole curvature, although
it says nothing about its anti-self-dual part. The manifold form, for the covariant derivative of
the curvature of a connection, is
`CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormSelfDualPart`.

## Main results

* `Fintype.sum_sum_sum_smul_eq_zero_of_cyclic`: a triple sum of a cyclically invariant coefficient
  against a family with vanishing cyclic sums is zero.
* `Orientation.sum_vectorFormHodgeStar_apply_ιMulti_eq_zero`: the divergence of the Hodge dual of a
  Bianchi family vanishes.
* `Orientation.sum_apply_ιMulti_eq_two_smul_sum_vectorFormSelfDualPart`,
  `Orientation.sum_apply_ιMulti_eq_two_smul_sum_vectorFormAntiSelfDualPart`: the divergence of a
  Bianchi family is twice that of its self-dual part, and twice that of its anti-self-dual part.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 2.1 (the Bianchi identity and `d_A^* F_A^+ = d_A^* F_A^-`).
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

namespace Fintype

/-- **Cyclic sums.** If the coefficient `c` is invariant under the cyclic permutation of its three
indices and the family `x` has vanishing cyclic sums, `x i k l + x k l i + x l i k = 0`, then
`∑ i, ∑ k, ∑ l, c i k l • x i k l = 0`. -/
theorem sum_sum_sum_smul_eq_zero_of_cyclic {ι W : Type*} [Fintype ι] [AddCommGroup W]
    [Module ℝ W] (c : ι → ι → ι → ℝ) (x : ι → ι → ι → W) (hc : ∀ i k l, c k l i = c i k l)
    (hx : ∀ i k l, x i k l + x k l i + x l i k = 0) :
    ∑ i, ∑ k, ∑ l, c i k l • x i k l = 0 := by
  -- Reindexing the sum cyclically moves each cyclic shift of `x` onto `x` itself.
  have h₁ : ∑ i, ∑ k, ∑ l, c i k l • x k l i = ∑ i, ∑ k, ∑ l, c i k l • x i k l := by
    calc ∑ i, ∑ k, ∑ l, c i k l • x k l i = ∑ i, ∑ k, ∑ l, c k l i • x k l i :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦
            Finset.sum_congr rfl fun l _ ↦ by rw [hc i k l]
      _ = ∑ k, ∑ i, ∑ l, c k l i • x k l i := Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ i, c k l i • x k l i := Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
  have h₂ : ∑ i, ∑ k, ∑ l, c i k l • x l i k = ∑ i, ∑ k, ∑ l, c i k l • x i k l := by
    calc ∑ i, ∑ k, ∑ l, c i k l • x l i k = ∑ i, ∑ k, ∑ l, c l i k • x l i k :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦
            Finset.sum_congr rfl fun l _ ↦ by rw [hc l i k]
      _ = ∑ i, ∑ l, ∑ k, c l i k • x l i k := Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ k, c l i k • x l i k := Finset.sum_comm
  -- So three times the sum is the sum against the cyclic sums of `x`, which vanish.
  have h : ∑ i, ∑ k, ∑ l, c i k l • (x i k l + x k l i + x l i k) = 0 := by simp [hx]
  simp only [smul_add, Finset.sum_add_distrib, h₁, h₂] at h
  have h₃ : (3 : ℝ) • ∑ i, ∑ k, ∑ l, c i k l • x i k l = 0 := by
    rw [← h]
    module
  exact (smul_eq_zero.1 h₃).resolve_left three_ne_zero

end Fintype

namespace Orientation

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (finrank ℝ E = 4)]
  [AddCommGroup W] [Module ℝ W] (o : Orientation ℝ E (Fin 4)) (hkl : 2 + 2 = finrank ℝ E)
  {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- The volume form is invariant under a cyclic permutation of its last three arguments. -/
private theorem volumeForm_cyclic (a u v w : E) :
    o.volumeForm ![a, v, w, u] = o.volumeForm ![a, u, v, w] := by
  have h₁ := o.volumeForm.map_swap ![a, v, w, u] (i := 1) (j := 3) (by decide)
  have h₂ := o.volumeForm.map_swap (![a, v, w, u] ∘ Equiv.swap 1 3) (i := 2) (j := 3) (by decide)
  have e : (![a, v, w, u] ∘ Equiv.swap 1 3) ∘ Equiv.swap 2 3 = ![a, u, v, w] := by
    ext j
    fin_cases j <;> rfl
  rw [e, h₁, neg_neg] at h₂
  exact h₂.symm

/-- The Hodge dual of a `W`-valued two-form on `u ∧ w`, expanded over the ordered pairs of an
orthonormal basis: `(⋆F) (u ∧ w) = ½ ∑ₖ ∑ₗ vol(u, w, eₖ, eₗ) F (eₖ ∧ eₗ)`. -/
theorem vectorFormHodgeStar_apply_ιMulti_two (b : OrthonormalBasis ι ℝ E)
    (F : ⋀[ℝ]^2 E →ₗ[ℝ] W) (u w : E) :
    o.vectorFormHodgeStar hkl F (ιMulti ℝ 2 ![u, w]) =
      (2⁻¹ : ℝ) • ∑ k, ∑ l, o.volumeForm ![u, w, b k, b l] • F (ιMulti ℝ 2 ![b k, b l]) := by
  rw [o.vectorFormHodgeStar_apply_of_even even_two hkl]
  have h := b.sum_sum_inner_smul_ιMulti_two (o.hodgeStar hkl (ιMulti ℝ 2 ![u, w]))
  simp_rw [o.inner_hodgeStar_ιMulti_two hkl] at h
  rw [eq_inv_smul_iff₀ two_ne_zero, ← map_smul, ← h]
  simp only [map_sum, map_smul]

/-- **The divergence of the Hodge dual of a Bianchi family vanishes.** If a linear family of
`W`-valued two-forms on an oriented four-dimensional inner product space satisfies the Bianchi
identity `T u (v ∧ w) + T v (w ∧ u) + T w (u ∧ v) = 0`, then for every orthonormal basis `(eᵢ)`
and every vector `a`, `∑ᵢ (⋆T eᵢ) (a ∧ eᵢ) = 0`. -/
theorem sum_vectorFormHodgeStar_apply_ιMulti_eq_zero (b : OrthonormalBasis ι ℝ E)
    (T : E →ₗ[ℝ] ⋀[ℝ]^2 E →ₗ[ℝ] W)
    (hT : ∀ u v w, T u (ιMulti ℝ 2 ![v, w]) + T v (ιMulti ℝ 2 ![w, u]) +
      T w (ιMulti ℝ 2 ![u, v]) = 0) (a : E) :
    ∑ i, o.vectorFormHodgeStar hkl (T (b i)) (ιMulti ℝ 2 ![a, b i]) = 0 := by
  simp_rw [o.vectorFormHodgeStar_apply_ιMulti_two hkl b, ← Finset.smul_sum]
  rw [Fintype.sum_sum_sum_smul_eq_zero_of_cyclic (fun i k l ↦ o.volumeForm ![a, b i, b k, b l])
    (fun i k l ↦ T (b i) (ιMulti ℝ 2 ![b k, b l])) (fun i k l ↦ o.volumeForm_cyclic _ _ _ _)
    (fun i k l ↦ hT _ _ _), smul_zero]

/-- **The divergence of a Bianchi family is twice that of its self-dual part.** Under the Bianchi
identity, `∑ᵢ T eᵢ (a ∧ eᵢ) = 2 ∑ᵢ T⁺ eᵢ (a ∧ eᵢ)` with `T⁺ = (T + ⋆T) / 2`: for the curvature of
a connection, `d_∇^* F = 2 d_∇^* F⁺`. -/
theorem sum_apply_ιMulti_eq_two_smul_sum_vectorFormSelfDualPart (b : OrthonormalBasis ι ℝ E)
    (T : E →ₗ[ℝ] ⋀[ℝ]^2 E →ₗ[ℝ] W)
    (hT : ∀ u v w, T u (ιMulti ℝ 2 ![v, w]) + T v (ιMulti ℝ 2 ![w, u]) +
      T w (ιMulti ℝ 2 ![u, v]) = 0) (a : E) :
    ∑ i, T (b i) (ιMulti ℝ 2 ![a, b i]) =
      (2 : ℝ) • ∑ i, o.vectorFormSelfDualPart hkl (T (b i)) (ιMulti ℝ 2 ![a, b i]) := by
  simp_rw [vectorFormSelfDualPart_apply, LinearMap.smul_apply, LinearMap.add_apply,
    ← Finset.smul_sum, Finset.sum_add_distrib,
    o.sum_vectorFormHodgeStar_apply_ιMulti_eq_zero hkl b T hT a, add_zero, smul_smul]
  norm_num

/-- **The divergence of a Bianchi family is twice that of its anti-self-dual part.** Under the
Bianchi identity, `∑ᵢ T eᵢ (a ∧ eᵢ) = 2 ∑ᵢ T⁻ eᵢ (a ∧ eᵢ)` with `T⁻ = (T - ⋆T) / 2`: for the
curvature of a connection, `d_∇^* F = 2 d_∇^* F⁻`. -/
theorem sum_apply_ιMulti_eq_two_smul_sum_vectorFormAntiSelfDualPart (b : OrthonormalBasis ι ℝ E)
    (T : E →ₗ[ℝ] ⋀[ℝ]^2 E →ₗ[ℝ] W)
    (hT : ∀ u v w, T u (ιMulti ℝ 2 ![v, w]) + T v (ιMulti ℝ 2 ![w, u]) +
      T w (ιMulti ℝ 2 ![u, v]) = 0) (a : E) :
    ∑ i, T (b i) (ιMulti ℝ 2 ![a, b i]) =
      (2 : ℝ) • ∑ i, o.vectorFormAntiSelfDualPart hkl (T (b i)) (ιMulti ℝ 2 ![a, b i]) := by
  simp_rw [vectorFormAntiSelfDualPart_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    ← Finset.smul_sum, Finset.sum_sub_distrib,
    o.sum_vectorFormHodgeStar_apply_ιMulti_eq_zero hkl b T hT a, sub_zero, smul_smul]
  norm_num

end Orientation
