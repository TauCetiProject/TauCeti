/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
public import TauCeti.LinearAlgebra.TensorProduct.Prod

/-!
# The generator dictionary of the dimension-raising equivalence

Mathlib's `CliffordAlgebra.equivEven` identifies a Clifford algebra `Cℓ(M, Q)` with the even
subalgebra of `Cℓ(M × R, Q')`, where `Q' = CliffordAlgebra.EquivEven.Q' Q` sends `(m, r)` to
`Q m - r²`. The new direction is spanned by `e₀ = CliffordAlgebra.EquivEven.e0 Q`, with
`e₀² = -1`, and the vector `m` is sent to `e₀ v(m)`, where `v(m) = ι Q' (m, 0)`
(`CliffordAlgebra.toEven_ι`). For the negative-metric convention `Q = -g` of spin geometry the form
`Q'` is again negative definite, `Q' (m, r) = -(g(m, m) + r²)`, so this is the identification
`Cℓₙ ≅ Cℓ⁰ₙ₊₁` used to compare odd-dimensional Clifford modules with even-dimensional ones.

This file writes that identification in terms of the Clifford map
`CliffordAlgebra.map (QuadraticMap.Isometry.inl Q _) : Cℓ(M, Q) →ₐ Cℓ(M × R, Q')` induced by the
inclusion `M → M × R`, which sends `ι Q m` to `v(m)`. An even element `x⁰` is sent to its own
image `x⁰`, and an odd element `x¹` to `e₀ x¹`, so a general element `x⁰ + x¹` is sent to
`x⁰ + e₀ x¹`. The grade involution of `Cℓ(M, Q)` corresponds to conjugation by the unit `e₀`,
whose inverse is `-e₀`. In particular the volume element `e₁ ⋯ eₙ` of an odd number of vectors
is sent to `e₀ e₁ ⋯ eₙ = -(e₁ ⋯ eₙ e₀)`, minus the volume element of the list `e₁, …, eₙ, e₀`.
After complexification and the normalization `ω_ℂ = i^(ℓ+1) e₁ ⋯ eₙ` for `n = 2ℓ + 1`, this sign is
what makes the odd-dimensional volume element correspond to minus the chirality element of
`M × R` in that order.

The last part of the file sets up that complexification for a real inner product space `V`. On the
`L²` product `V ⊕ ℝ = WithLp 2 (V × ℝ)`, a form `Q₁` agreeing with `Q'` has polar form
`((m, r), (m', r')) ↦ B_Q(m, m') - r r'`, and appending the new unit vector `e₀` to a `Q`-orthogonal
orthonormal basis of `V` gives a `Q₁`-orthogonal basis of `V ⊕ ℝ`. The quadratic isometry
`CliffordAlgebra.EquivEven.complexProdIsometryEquiv` between `ℂ ⊗ (V ⊕ ℝ)` with `Q₁_ℂ` and
`(ℂ ⊗ V) × ℂ` with `Q'(Q_ℂ)` identifies the target of `toEven (Q.baseChange ℂ)` with the
complexified Clifford algebra of `V ⊕ ℝ`, and the resulting map
`ψ : Cℓ(ℂ ⊗ V, Q_ℂ) → Cℓ(ℂ ⊗ (V ⊕ ℝ), Q₁_ℂ)` sends `c(v)` to `c(e₀) c(v)`.

## Main definitions

* `CliffordAlgebra.EquivEven.complexProdIsometryEquiv`: the quadratic isometry
  `ℂ ⊗ (V ⊕ ℝ) ≃ (ℂ ⊗ V) × ℂ` from `Q₁_ℂ` to `Q'(Q_ℂ)`.

## Main results

* `CliffordAlgebra.EquivEven.e0_mul_map_inl`: `e₀` conjugates the image of `Cℓ(M, Q)` by the
  grade involution.
* `CliffordAlgebra.coe_toEven_of_mem_even`: an even element is sent to its image under the
  inclusion.
* `CliffordAlgebra.coe_toEven_of_mem_odd`: an odd element `x` is sent to `e₀ x`.
* `CliffordAlgebra.coe_toEven_involute`: the grade involution becomes conjugation by `e₀`.
* `CliffordAlgebra.coe_toEven_prod_map_ι_of_even_length` and
  `CliffordAlgebra.coe_toEven_prod_map_ι_of_odd_length`: an even ordered product of vectors is
  sent to the same product, and an odd one to minus the product with `e₀` appended.
* `CliffordAlgebra.EquivEven.associated_apply_eq_associated_sub_mul`: the polar form of `Q₁` on
  `V ⊕ ℝ`.
* `CliffordAlgebra.EquivEven.isOrthoᵢ_associated_prod_singleton`: appending `e₀` to a
  `Q`-orthogonal basis of `V` gives a `Q₁`-orthogonal basis of `V ⊕ ℝ`.
* `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_ι`: `ψ(c(v)) = c(e₀) c(v)`.
* `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_prod_of_odd_length` and
  `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_prod_eq_neg_mul_of_odd_length`: `ψ` on an odd
  ordered product of real vectors.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §3.
-/

public section

namespace CliffordAlgebra

open EquivEven

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

namespace EquivEven

/-- Left multiplication by `e₀` twice is negation, since `e₀² = -1`. -/
@[simp]
theorem e0_mul_e0_mul (y : CliffordAlgebra (Q' Q)) : e0 Q * (e0 Q * y) = -y := by
  rw [← mul_assoc, e0_mul_e0, neg_one_mul]

/-- The inclusion `M → M × R` sends the generator `ι Q m` to `v(m)`. -/
theorem map_inl_ι (m : M) :
    map (QuadraticMap.Isometry.inl Q (-QuadraticMap.sq)) (ι Q m) = v Q m := by
  rw [map_apply_ι, QuadraticMap.Isometry.inl_apply, v, LinearMap.comp_apply, LinearMap.inl_apply]

/-- The inclusion `M → M × R` sends the ordered product `ι m₁ ⋯ ι mₙ` to `v(m₁) ⋯ v(mₙ)`. -/
theorem map_inl_prod_map_ι (l : List M) :
    map (QuadraticMap.Isometry.inl Q (-QuadraticMap.sq)) (l.map (ι Q)).prod =
      (l.map (v Q)).prod := by
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, map_inl_ι]

/-- **`e₀` conjugates the image of `Cℓ(M, Q)` by the grade involution**: for every `x`,
`e₀ x = x̂ e₀` in `Cℓ(M × R, Q')`, where `x̂ = involute x`. -/
theorem e0_mul_map_inl (x : CliffordAlgebra Q) :
    e0 Q * map (QuadraticMap.Isometry.inl Q (-QuadraticMap.sq)) x =
      map (QuadraticMap.Isometry.inl Q (-QuadraticMap.sq)) (involute x) * e0 Q := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι m => rw [involute_ι, map_neg, map_inl_ι, neg_mul, neg_v_mul_e0]
  | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]
  | mul x y hx hy =>
    simp only [map_mul, ← mul_assoc, hx]
    simp only [mul_assoc, hy]

end EquivEven

/-- **An even element is sent to its own image**: for `x` in the even part of `Cℓ(M, Q)`, the
dimension-raising equivalence sends `x` to its image under the inclusion `M → M × R`. -/
theorem coe_toEven_of_mem_even {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 0) :
    (toEven Q x : CliffordAlgebra (Q' Q)) =
      map (QuadraticMap.Isometry.inl Q (-QuadraticMap.sq)) x := by
  induction x, hx using even_induction with
  | algebraMap r => simp
  | add x y hx hy ihx ihy => simp only [map_add, Subalgebra.coe_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    simp only [map_mul, Subalgebra.coe_mul, toEven_ι, ih, map_inl_ι]
    rw [← mul_assoc (e0 Q * v Q m₁), e0_mul_v_mul_e0]

/-- **An odd element `x` is sent to `e₀ x`**: for `x` in the odd part of `Cℓ(M, Q)`, the
dimension-raising equivalence sends `x` to `e₀` times its image under the inclusion
`M → M × R`. -/
theorem coe_toEven_of_mem_odd {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 1) :
    (toEven Q x : CliffordAlgebra (Q' Q)) =
      e0 Q * map (QuadraticMap.Isometry.inl Q (-QuadraticMap.sq)) x := by
  induction x, hx using odd_induction with
  | ι m => rw [toEven_ι, map_inl_ι]
  | add x y hx hy ihx ihy => simp only [map_add, Subalgebra.coe_add, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h := e0_mul_map_inl (ι Q m₁ * ι Q m₂)
    simp only [map_mul, involute_ι, neg_mul_neg, map_inl_ι] at h
    simp only [map_mul, Subalgebra.coe_mul, toEven_ι, ih, map_inl_ι]
    rw [← mul_assoc (e0 Q * v Q m₁), e0_mul_v_mul_e0, ← mul_assoc (e0 Q), h]
    simp only [mul_assoc]

/-- **The grade involution becomes conjugation by `e₀`**: since `e₀⁻¹ = -e₀`, the
dimension-raising equivalence sends `x̂ = involute x` to `e₀ x e₀⁻¹ = -(e₀ x e₀)`. -/
theorem coe_toEven_involute (x : CliffordAlgebra Q) :
    (toEven Q (involute x) : CliffordAlgebra (Q' Q)) =
      -(e0 Q * toEven Q x * e0 Q) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes r (e0 Q), mul_assoc]
  | ι m => simp [toEven_ι, ← neg_e0_mul_v]
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy, mul_add, add_mul, neg_add]
  | mul x y hx hy => simp [hx, hy, mul_assoc]

/-- **An even ordered product of vectors is sent to the same product in `Cℓ(M × R, Q')`.** -/
theorem coe_toEven_prod_map_ι_of_even_length {l : List M} (hl : Even l.length) :
    (toEven Q (l.map (ι Q)).prod : CliffordAlgebra (Q' Q)) = (l.map (v Q)).prod := by
  rw [coe_toEven_of_mem_even (prod_map_ι_mem_evenOdd_zero_of_even_length hl), map_inl_prod_map_ι]

/-- **An odd ordered product of vectors is sent to minus the product with `e₀` appended**: for
`l = [m₁, …, mₙ]` with `n` odd, the image of `ι m₁ ⋯ ι mₙ` is
`e₀ v(m₁) ⋯ v(mₙ) = -(v(m₁) ⋯ v(mₙ) e₀)`. For an orthogonal basis this is the volume element
of `M` going to minus the volume element of `M × R` in the order that puts `e₀` last. -/
theorem coe_toEven_prod_map_ι_of_odd_length {l : List M} (hl : Odd l.length) :
    (toEven Q (l.map (ι Q)).prod : CliffordAlgebra (Q' Q)) = -((l.map (v Q)).prod * e0 Q) := by
  have hodd := prod_map_ι_mem_evenOdd_one_of_odd_length (Q := Q) hl
  rw [coe_toEven_of_mem_odd hodd, e0_mul_map_inl, involute_eq_of_mem_odd hodd, map_neg,
    neg_mul, map_inl_prod_map_ι]

end CliffordAlgebra

/-! ### Complexifying `V ⊕ ℝ` -/

noncomputable section

open scoped TensorProduct

namespace CliffordAlgebra.EquivEven

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {Q₁ : QuadraticForm ℝ (WithLp 2 (V × ℝ))}

/-- For the negative-metric convention `Q v = -‖v‖²`, the form `Q' Q` on the `L²` product
`V ⊕ ℝ` is again `x ↦ -‖x‖²`, so `Q₁ x = -‖x‖²` satisfies the hypothesis
`Q₁ x = Q' Q (WithLp.ofLp x)` of the results below. -/
theorem Q'_ofLp_eq_neg_norm_sq (hQ : ∀ v, Q v = -‖v‖ ^ 2) (x : WithLp 2 (V × ℝ)) :
    Q' Q (WithLp.ofLp x) = -‖x‖ ^ 2 := by
  simp only [Q'_apply, hQ, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd,
    Real.norm_eq_abs, sq_abs]
  ring

variable (hQ₁ : ∀ x, Q₁ x = Q' Q (WithLp.ofLp x))
include hQ₁

/-- **The polar form on `V ⊕ ℝ`**: the polar form of `Q₁ (m, r) = Q m - r²` is
`((m, r), (m', r')) ↦ B_Q(m, m') - r r'`. -/
theorem associated_apply_eq_associated_sub_mul (x y : WithLp 2 (V × ℝ)) :
    QuadraticMap.associated Q₁ x y =
      QuadraticMap.associated Q (WithLp.ofLp x).1 (WithLp.ofLp y).1 -
        (WithLp.ofLp x).2 * (WithLp.ofLp y).2 := by
  have hcomp : Q₁ = (Q' Q).comp (WithLp.linearEquiv 2 ℝ (V × ℝ)).toLinearMap :=
    QuadraticMap.ext fun x ↦ by
      rw [hQ₁, QuadraticMap.comp_apply, LinearEquiv.coe_coe, WithLp.coe_linearEquiv]
  rw [hcomp, QuadraticMap.associated_comp, QuadraticMap.associated_prod]
  simp [sub_eq_add_neg]

/-- **Appending `e₀` to an orthogonal basis**: appending `e₀ = (0, 1)` to a `Q`-orthogonal
orthonormal basis of `V` gives a `Q₁`-orthogonal basis of `V ⊕ ℝ`, in any indexing. -/
theorem isOrthoᵢ_associated_prod_singleton {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis)
    {κ : Type*} [Fintype κ] (e : ι ⊕ Fin 1 ≃ κ) :
    (QuadraticMap.associated Q₁).IsOrthoᵢ
      ((b.prod (OrthonormalBasis.singleton (Fin 1) ℝ)).reindex e).toBasis := by
  rw [LinearMap.isOrthoᵢ_def] at hQb ⊢
  intro i j hij
  have hij' : e.symm i ≠ e.symm j := e.symm.injective.ne hij
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.reindex_apply,
    associated_apply_eq_associated_sub_mul hQ₁]
  generalize e.symm i = p, e.symm j = q at hij'
  rcases p with p | p <;> rcases q with q | q
  · simpa using hQb p q (Sum.inl.inj_iff.not.1 hij')
  · simp
  · simp
  · exact absurd (congrArg Sum.inr (Subsingleton.elim p q)) hij'

/-- **The complexification of `V ⊕ ℝ`**: when `Q₁` is the form `Q₁ (m, r) = Q m - r²` on the
`L²` product `V ⊕ ℝ`, the map `z ⊗ (m, r) ↦ (z ⊗ m, r z)` is a quadratic isometry from
`ℂ ⊗ (V ⊕ ℝ)` with `Q₁_ℂ` onto `(ℂ ⊗ V) × ℂ` with `Q'(Q_ℂ)`, the form Mathlib's
`CliffordAlgebra.toEven` uses for `Q_ℂ`. The underlying linear equivalence is
`TensorProduct.prodRightRid` after the base change of `WithLp.linearEquiv`. -/
def complexProdIsometryEquiv : (Q₁.baseChange ℂ).IsometryEquiv (Q' (Q.baseChange ℂ)) :=
  let e := (WithLp.linearEquiv 2 ℝ (V × ℝ)).baseChange ℝ ℂ _ _ ≪≫ₗ
    TensorProduct.prodRightRid ℝ ℂ ℂ V
  { toLinearEquiv := e
    map_app' := by
      have h : (Q' (Q.baseChange ℂ)).comp e.toLinearMap = Q₁.baseChange ℂ := by
        ext x
        simp [e, hQ₁, Algebra.smul_def]
      exact fun x ↦ congr($h x) }

@[simp]
theorem complexProdIsometryEquiv_tmul (z : ℂ) (x : WithLp 2 (V × ℝ)) :
    complexProdIsometryEquiv hQ₁ (z ⊗ₜ x) = (z ⊗ₜ (WithLp.ofLp x).1, (WithLp.ofLp x).2 • z) := by
  rw [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
  simp [complexProdIsometryEquiv]

/-- The Clifford algebra equivalence induced by `complexProdIsometryEquiv` sends `v(z ⊗ m)`, the
generator of `(z ⊗ m, 0)`, to the generator of `z ⊗ (m, 0)`. This is not a `simp` lemma, because
`simp` rewrites `equivOfIsometry e x` to `map e.toIsometry x` by `equivOfIsometry_apply`. -/
theorem equivOfIsometry_v (z : ℂ) (m : V) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm (v (Q.baseChange ℂ) (z ⊗ₜ m)) =
      ι (Q₁.baseChange ℂ) (z ⊗ₜ WithLp.toLp 2 (m, 0)) := by
  rw [v, LinearMap.comp_apply, LinearMap.inl_apply, equivOfIsometry_apply, map_apply_ι]
  exact congrArg _ ((QuadraticMap.IsometryEquiv.symm_apply_eq _).2 (by simp))

/-- The Clifford algebra equivalence induced by `complexProdIsometryEquiv` sends `e₀`, the
generator of `(0, 1)`, to the generator of `1 ⊗ (0, 1)`. Like
`CliffordAlgebra.EquivEven.equivOfIsometry_v`, this is not a `simp` lemma. -/
theorem equivOfIsometry_e0 :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm (e0 (Q.baseChange ℂ)) =
      ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, 1)) := by
  rw [e0, equivOfIsometry_apply, map_apply_ι]
  exact congrArg _ ((QuadraticMap.IsometryEquiv.symm_apply_eq _).2 (by simp))

/-- **The complexified dimension-raising map on generators**: `ψ(c(z ⊗ m)) = c(e₀) c(z ⊗ m)`,
where `e₀ = 1 ⊗ (0, 1)` and `m` is included in `V ⊕ ℝ` as `(m, 0)`. -/
theorem equivOfIsometry_toEven_ι (z : ℂ) (m : V) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) (ι (Q.baseChange ℂ) (z ⊗ₜ m))) =
      ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, 1)) *
        ι (Q₁.baseChange ℂ) (z ⊗ₜ WithLp.toLp 2 (m, 0)) := by
  rw [toEven_ι, map_mul, equivOfIsometry_e0, equivOfIsometry_v]

/-- **The complexified dimension-raising map on an odd product of real vectors**:
`ψ(c(m₁) ⋯ c(mₙ)) = c(e₀) c(m₁) ⋯ c(mₙ)` for `n` odd. -/
theorem equivOfIsometry_toEven_prod_of_odd_length {l : List V} (hl : Odd l.length) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) ((l.map fun m ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ m)).prod)) =
      ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, 1)) *
        (l.map fun m ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (m, 0))).prod := by
  have h := coe_toEven_of_mem_odd (prod_map_ι_mem_evenOdd_one_of_odd_length
    (Q := Q.baseChange ℂ) (l := l.map ((1 : ℂ) ⊗ₜ ·)) (by simpa using hl))
  rw [map_inl_prod_map_ι] at h
  simp only [List.map_map, Function.comp_def] at h
  rw [h, map_mul, equivOfIsometry_e0, map_list_prod, List.map_map]
  simp only [Function.comp_def, equivOfIsometry_v]

/-- **The same product with `c(e₀)` moved to the end**:
`ψ(c(m₁) ⋯ c(mₙ)) = -c(m₁) ⋯ c(mₙ) c(e₀)` for `n` odd. -/
theorem equivOfIsometry_toEven_prod_eq_neg_mul_of_odd_length {l : List V} (hl : Odd l.length) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) ((l.map fun m ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ m)).prod)) =
      -((l.map fun m ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (m, 0))).prod *
        ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, 1))) := by
  have h := coe_toEven_prod_map_ι_of_odd_length (Q := Q.baseChange ℂ)
    (l := l.map ((1 : ℂ) ⊗ₜ ·)) (by simpa using hl)
  simp only [List.map_map, Function.comp_def] at h
  rw [h, map_neg, map_mul, equivOfIsometry_e0, map_list_prod, List.map_map]
  simp only [Function.comp_def, equivOfIsometry_v]

end CliffordAlgebra.EquivEven

end
