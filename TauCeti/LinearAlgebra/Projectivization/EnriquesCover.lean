/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus

import TauCeti.LinearAlgebra.Vandermonde

/-!
# The K3 cover of an Enriques surface by three diagonal quadrics

Write `tᵢ = i + 1` for `i : Fin 6`. The three diagonal quadrics

`qⱼ(z) = ∑ᵢ tᵢ ^ j zᵢ²`, `j = 0, 1, 2`

(`TauCeti.enriquesQuadric`) cut out a surface `Y ⊆ ℂℙ⁵`, the common zero locus
`TauCeti.enriquesZeroSet` in native complex projective space. The linear sign change `σ` negating
the first three coordinates (`TauCeti.enriquesInvolutionLinear`) preserves each quadric, so its
projectivization (`TauCeti.enriquesProjectiveInvolution`) is an involution of `ℂℙ⁵` mapping `Y` to
itself. This is the classical model of the K3 cover of an Enriques surface, the quotient of `Y` by
this involution. This file proves the two polynomial facts on which that construction rests.

* **Regularity**: at every nonzero common zero `v` of the three quadrics the cone Jacobian, with
  rows `(2 tᵢ ^ j vᵢ)ᵢ`, is surjective (`TauCeti.mulVec_surjective_jacobiMatrixAt_enriquesQuadric`
  and `TauCeti.enriquesQuadricJacobian_surjective`). This is the smoothness hypothesis under which
  `TauCeti.complexProjectiveZeroLocusChartedSpace` makes `Y` a complex surface.
* **Freeness**: the projective involution has no fixed point on `Y`
  (`TauCeti.enriquesProjectiveInvolution_no_fixed_point`).

Both follow from one observation: a common zero `v` with at most three nonzero coordinates is
zero (`TauCeti.eq_zero_of_forall_eval_enriquesQuadric_eq_zero_of_card_le_three`). Indeed the
squares `vᵢ²` of its coordinates on a set `s` of at most three indices satisfy
`∑_{i ∈ s} tᵢ ^ j vᵢ² = 0` for `j < #s`, a Vandermonde system with distinct nodes `tᵢ` and hence
only the trivial solution
(`TauCeti.exists_lt_card_sum_mul_pow_ne_zero`). So a nonzero common zero has at least four nonzero
coordinates. Three of them have distinct nodes, so the corresponding columns
`2 vᵢ (1, tᵢ, tᵢ²)` of the Jacobian are independent and the Jacobian is onto. A line fixed by the
sign change lies in one of its two eigenspaces, each spanned by three coordinate vectors, so it
cannot meet `Y`.

The equations cannot be dropped from these statements. The class of the first coordinate vector
`e₀` is fixed by the involution, but the quadrics take the values `(1, 1, 1)` there, so it does not
lie on `Y`; the Jacobian at `e₀` has rank one, so its surjectivity uses the equations.

## Main definitions

* `TauCeti.enriquesQuadric`: the quadric `∑ᵢ (i + 1) ^ j zᵢ²`, for `j : Fin 3`.
* `TauCeti.enriquesZeroSet`: their common zero locus in `ℙ ℂ (Fin 6 → ℂ)`.
* `TauCeti.enriquesInvolutionLinear`: the linear involution negating the first three coordinates.
* `TauCeti.enriquesProjectiveInvolution`: the induced involution of `ℙ ℂ (Fin 6 → ℂ)`.

## Main results

* `TauCeti.mk_mem_enriquesZeroSet_iff`: a nonzero vector spans a line of `Y` exactly when it is a
  common zero of the three quadrics.
* `TauCeti.eq_zero_of_forall_eval_enriquesQuadric_eq_zero_of_card_le_three`: a common zero
  supported on at most three coordinates is zero.
* `TauCeti.mulVec_surjective_jacobiMatrixAt_enriquesQuadric` and
  `TauCeti.enriquesQuadricJacobian_surjective`: the cone Jacobian is onto away from the vertex of
  the cone.
* `TauCeti.mulVec_surjective_jacobiMatrixAt_rep_of_mem_enriquesZeroSet`: the same at the chosen
  representative of every point of `Y`, the form in which the zero-locus atlas consumes it.
* `TauCeti.enriquesProjectiveInvolution_involutive` and
  `TauCeti.mapsTo_enriquesProjectiveInvolution`: the sign change is an involution preserving `Y`.
* `TauCeti.enriquesProjectiveInvolution_no_fixed_point`: it acts on `Y` without fixed points.

## References

* I. Dolgachev, *A brief introduction to Enriques surfaces*, arXiv:1412.7744v2, §3, pp. 8–9
  (the K3 cover of an Enriques surface as an intersection of three quadrics in `ℙ⁵` invariant
  under the change of sign of three coordinates).
-/

public section

open MvPolynomial Finset
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-! ### The three quadrics -/

/-- **The quadrics of the Enriques K3 cover**: `qⱼ = ∑ᵢ (i + 1) ^ j Xᵢ²` for `j = 0, 1, 2`, the
diagonal quadrics in six variables whose coefficient vectors are the rows of the Vandermonde
matrix of the nodes `1, …, 6`. -/
noncomputable def enriquesQuadric (j : Fin 3) : MvPolynomial (Fin 6) ℂ :=
  ∑ i : Fin 6, ((i.val + 1 : ℂ) ^ j.val) • X i ^ 2

/-- The value of the quadric `qⱼ` at a vector `v` is `∑ᵢ (i + 1) ^ j vᵢ²`. -/
@[simp]
theorem eval_enriquesQuadric (v : Fin 6 → ℂ) (j : Fin 3) :
    eval v (enriquesQuadric j) = ∑ i : Fin 6, ((i.val + 1 : ℂ) ^ j.val) * v i ^ 2 := by
  simp [enriquesQuadric]

/-- Each quadric `qⱼ` is homogeneous of degree two. -/
theorem isHomogeneous_enriquesQuadric (j : Fin 3) : (enriquesQuadric j).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ ↦ by
    rw [smul_eq_C_mul]
    exact ((isHomogeneous_X ℂ i).pow 2).C_mul _

/-- Rescaling a vector by `c` rescales the value of each quadric by `c²`. -/
theorem eval_smul_enriquesQuadric (c : ℂ) (v : Fin 6 → ℂ) (j : Fin 3) :
    eval (c • v) (enriquesQuadric j) = c ^ 2 * eval v (enriquesQuadric j) :=
  (isHomogeneous_enriquesQuadric j).eval_smul c v

/-- The partial derivatives of the quadrics, the entries of their cone Jacobian:
`∂qⱼ/∂zᵢ (v) = (i + 1) ^ j (2 vᵢ)`. -/
@[simp]
theorem eval_pderiv_enriquesQuadric (v : Fin 6 → ℂ) (j : Fin 3) (i : Fin 6) :
    eval v (pderiv i (enriquesQuadric j)) = (i.val + 1 : ℂ) ^ j.val * (2 * v i) := by
  simp [enriquesQuadric, pderiv_X, Pi.single_apply]

/-! ### The zero set -/

/-- **The Enriques K3 cover**: the common zero locus of the three quadrics `enriquesQuadric` in
complex projective five-space, the set of lines in `ℂ⁶` on every vector of which all three
quadrics vanish. -/
noncomputable def enriquesZeroSet : Set (ℙ ℂ (Fin 6 → ℂ)) :=
  complexProjectiveZeroLocus enriquesQuadric

/-- The Enriques K3 cover is the projective zero locus of the three quadrics. -/
theorem enriquesZeroSet_eq : enriquesZeroSet = complexProjectiveZeroLocus enriquesQuadric :=
  (rfl)

/-- A line belongs to the Enriques K3 cover exactly when the three quadrics vanish on each of its
vectors. -/
theorem mem_enriquesZeroSet {L : ℙ ℂ (Fin 6 → ℂ)} :
    L ∈ enriquesZeroSet ↔ ∀ v ∈ L.submodule, ∀ j, eval v (enriquesQuadric j) = 0 := by
  rw [enriquesZeroSet_eq, mem_complexProjectiveZeroLocus]
  exact ⟨fun h v hv j ↦ h j v hv, fun h j v hv ↦ h v hv j⟩

/-- The line spanned by a nonzero vector `v` belongs to the Enriques K3 cover exactly when `v` is a
common zero of the three quadrics. -/
theorem mk_mem_enriquesZeroSet_iff (v : Fin 6 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ enriquesZeroSet ↔ ∀ j, eval v (enriquesQuadric j) = 0 :=
  complexProjectiveZeroLocus_mk_iff isHomogeneous_enriquesQuadric v hv

/-- Membership in the Enriques K3 cover can be tested on the chosen representative of a line. -/
theorem mem_enriquesZeroSet_iff_eval_rep (L : ℙ ℂ (Fin 6 → ℂ)) :
    L ∈ enriquesZeroSet ↔ ∀ j, eval L.rep (enriquesQuadric j) = 0 :=
  mem_complexProjectiveZeroLocus_iff_eval_rep isHomogeneous_enriquesQuadric L

/-- The nodes `i ↦ i + 1` of the quadrics are distinct. -/
private theorem enriquesNode_injective : Function.Injective fun i : Fin 6 ↦ (i.val + 1 : ℂ) :=
  (add_left_injective 1).comp (Nat.cast_injective.comp Fin.val_injective)

/-- **Common zeros with small support vanish.** A common zero of the three quadrics whose nonzero
coordinates lie in a set `s` of at most three indices is zero: the squares of its coordinates
solve the Vandermonde system `∑_{i ∈ s} (i + 1) ^ j vᵢ² = 0`, `j < #s`, with distinct nodes. -/
theorem eq_zero_of_forall_eval_enriquesQuadric_eq_zero_of_card_le_three {v : Fin 6 → ℂ}
    (hv : ∀ j, eval v (enriquesQuadric j) = 0) {s : Finset (Fin 6)} (hs : #s ≤ 3)
    (hvs : ∀ i ∉ s, v i = 0) : v = 0 := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  obtain ⟨k, hk, hne'⟩ := exists_lt_card_sum_mul_pow_ne_zero (w := fun i ↦ v i ^ 2)
    enriquesNode_injective.injOn
    ⟨i₀, by_contra fun h ↦ hi₀ (hvs i₀ h), pow_ne_zero 2 hi₀⟩
  apply hne'
  have h := hv ⟨k, by omega⟩
  rw [eval_enriquesQuadric] at h
  rw [← h, ← sum_subset (subset_univ s) fun i _ hi ↦ by simp [hvs i hi]]
  exact sum_congr rfl fun i _ ↦ mul_comm _ _

/-- A nonzero common zero of the three quadrics has at least four nonzero coordinates. -/
theorem four_le_card_filter_ne_zero_of_forall_eval_enriquesQuadric_eq_zero {v : Fin 6 → ℂ}
    (hv0 : v ≠ 0) (hv : ∀ j, eval v (enriquesQuadric j) = 0) : 4 ≤ #{i | v i ≠ 0} := by
  by_contra! h
  exact hv0 (eq_zero_of_forall_eval_enriquesQuadric_eq_zero_of_card_le_three hv (s := {i | v i ≠ 0})
    (by omega) fun i hi ↦ by simpa using hi)

/-! ### Regularity -/

/-- **The Enriques K3 cover is smooth: the cone Jacobian is onto.** At every nonzero common zero
`v` of the three quadrics, the Jacobian matrix `(2 (i + 1) ^ j vᵢ)` has rank three. -/
theorem mulVec_surjective_jacobiMatrixAt_enriquesQuadric {v : Fin 6 → ℂ} (hv0 : v ≠ 0)
    (hv : ∀ j, eval v (enriquesQuadric j) = 0) :
    (jacobiMatrixAt enriquesQuadric v).mulVec.Surjective := by
  -- Three coordinates where `v` does not vanish.
  obtain ⟨t, ht, htc⟩ := exists_subset_card_eq
    ((Nat.le_succ 3).trans (four_le_card_filter_ne_zero_of_forall_eval_enriquesQuadric_eq_zero
      hv0 hv))
  let e : Fin 3 ≃ t := (t.equivFinOfCardEq htc).symm
  have hve (k : Fin 3) : v (e k) ≠ 0 := by simpa using ht (e k).property
  -- The rows are independent: a relation `∑ⱼ cⱼ (2 (i + 1) ^ j vᵢ) = 0` makes the polynomial
  -- `∑ⱼ cⱼ Xʲ` vanish at the three distinct nodes `e k + 1`.
  refine LinearIndependent.mulVec_surjective (Fintype.linearIndependent_iff.mpr fun c hc ↦ ?_)
  refine congrFun (Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
    (f := fun k ↦ ((e k : Fin 6).val + 1 : ℂ))
    (enriquesNode_injective.comp (Subtype.val_injective.comp e.injective)) fun k ↦ ?_)
  have h := congrFun hc (e k)
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row_apply, jacobiMatrixAt_apply,
    eval_pderiv_enriquesQuadric, smul_eq_mul, Pi.zero_apply] at h
  have h' : (2 * v (e k)) * ∑ j, c j * ((e k : Fin 6).val + 1 : ℂ) ^ (j : ℕ) = 0 := by
    rw [← h, mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero two_ne_zero (hve k))

/-- **Regularity in derivative form.** At every nonzero common zero `v` of the three quadrics, the
derivative of the map `w ↦ (q₀(w), q₁(w), q₂(w))` from `ℂ⁶` to `ℂ³` is surjective. The equations
are needed: at the first coordinate vector the derivative has rank one. -/
theorem enriquesQuadricJacobian_surjective (v : Fin 6 → ℂ) (hv : v ≠ 0)
    (hz : ∀ j : Fin 3, eval v (enriquesQuadric j) = 0) :
    Function.Surjective
      (fderiv ℂ (fun w : Fin 6 → ℂ => fun j : Fin 3 => eval w (enriquesQuadric j)) v) :=
  (surjective_fderiv_eval_family_iff enriquesQuadric v).mpr
    (mulVec_surjective_jacobiMatrixAt_enriquesQuadric hv hz)

/-- At the chosen representative of each point of the Enriques K3 cover, the cone Jacobian of the
three quadrics is onto. This is the smoothness hypothesis of the complex atlas on a projective
zero locus. -/
theorem mulVec_surjective_jacobiMatrixAt_rep_of_mem_enriquesZeroSet {L : ℙ ℂ (Fin 6 → ℂ)}
    (hL : L ∈ enriquesZeroSet) : (jacobiMatrixAt enriquesQuadric L.rep).mulVec.Surjective :=
  mulVec_surjective_jacobiMatrixAt_enriquesQuadric L.rep_ne_zero
    ((mem_enriquesZeroSet_iff_eval_rep L).mp hL)

/-! ### The sign involution -/

/-- **The Enriques sign change**: the linear involution of `ℂ⁶` negating the first three
coordinates and fixing the last three. -/
def enriquesInvolutionLinear : (Fin 6 → ℂ) ≃ₗ[ℂ] (Fin 6 → ℂ) where
  toFun v i := if i.val < 3 then -v i else v i
  invFun v i := if i.val < 3 then -v i else v i
  left_inv v := funext fun i ↦ by by_cases h : i.val < 3 <;> simp [h]
  right_inv v := funext fun i ↦ by by_cases h : i.val < 3 <;> simp [h]
  map_add' v w := funext fun i ↦ by by_cases h : i.val < 3 <;> simp [h, add_comm]
  map_smul' c v := funext fun i ↦ by by_cases h : i.val < 3 <;> simp [h]

@[simp]
theorem enriquesInvolutionLinear_apply (v : Fin 6 → ℂ) (i : Fin 6) :
    enriquesInvolutionLinear v i = if i.val < 3 then -v i else v i :=
  (rfl)

/-- The sign change is its own inverse. -/
@[simp]
theorem enriquesInvolutionLinear_symm :
    enriquesInvolutionLinear.symm = enriquesInvolutionLinear :=
  (rfl)

/-- The sign change squares to the identity. -/
@[simp]
theorem enriquesInvolutionLinear_enriquesInvolutionLinear (v : Fin 6 → ℂ) :
    enriquesInvolutionLinear (enriquesInvolutionLinear v) = v :=
  enriquesInvolutionLinear.apply_symm_apply v

/-- The sign change preserves each of the three quadrics. -/
theorem eval_enriquesInvolutionLinear_enriquesQuadric (v : Fin 6 → ℂ) (j : Fin 3) :
    eval (enriquesInvolutionLinear v) (enriquesQuadric j) = eval v (enriquesQuadric j) := by
  simp only [eval_enriquesQuadric, enriquesInvolutionLinear_apply]
  exact sum_congr rfl fun i _ ↦ by split_ifs <;> simp

/-- **The Enriques involution** of complex projective five-space: the projectivization of the sign
change `enriquesInvolutionLinear`. -/
noncomputable def enriquesProjectiveInvolution :
    ℙ ℂ (Fin 6 → ℂ) → ℙ ℂ (Fin 6 → ℂ) :=
  Projectivization.map enriquesInvolutionLinear.toLinearMap enriquesInvolutionLinear.injective

@[simp]
theorem enriquesProjectiveInvolution_mk (v : Fin 6 → ℂ) (hv : v ≠ 0) :
    enriquesProjectiveInvolution (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (enriquesInvolutionLinear v)
        ((map_ne_zero_iff _ enriquesInvolutionLinear.injective).mpr hv) :=
  Projectivization.map_mk _ _ v hv

/-- The Enriques involution squares to the identity. -/
theorem enriquesProjectiveInvolution_involutive :
    Function.Involutive enriquesProjectiveInvolution := fun L ↦ by
  induction L using Projectivization.ind with
  | h v hv => simp

/-- The Enriques involution squares to the identity, pointwise. -/
@[simp]
theorem enriquesProjectiveInvolution_enriquesProjectiveInvolution (p : ℙ ℂ (Fin 6 → ℂ)) :
    enriquesProjectiveInvolution (enriquesProjectiveInvolution p) = p :=
  enriquesProjectiveInvolution_involutive p

/-- The Enriques involution maps the K3 cover to itself. -/
theorem mapsTo_enriquesProjectiveInvolution :
    Set.MapsTo enriquesProjectiveInvolution enriquesZeroSet enriquesZeroSet := fun L hL ↦ by
  induction L using Projectivization.ind with
  | h v hv =>
    rw [enriquesProjectiveInvolution_mk, mk_mem_enriquesZeroSet_iff]
    simpa only [eval_enriquesInvolutionLinear_enriquesQuadric, mk_mem_enriquesZeroSet_iff] using hL

/-- **The Enriques involution acts freely on the K3 cover.** A line fixed by the sign change lies
in one of its two eigenspaces, each spanned by three coordinate vectors, and the only common zero
of the three quadrics supported on three coordinates is zero. -/
theorem enriquesProjectiveInvolution_no_fixed_point
    (p : ℙ ℂ (Fin 6 → ℂ)) (hp : p ∈ enriquesZeroSet) :
    enriquesProjectiveInvolution p ≠ p := by
  induction p using Projectivization.ind with
  | h v hv =>
  intro hfix
  have hz := (mk_mem_enriquesZeroSet_iff v hv).mp hp
  rw [enriquesProjectiveInvolution_mk, Projectivization.mk_eq_mk_iff] at hfix
  obtain ⟨a, ha⟩ := hfix
  -- Coordinatewise, `a vᵢ = -vᵢ` for `i < 3` and `a vᵢ = vᵢ` for `i ≥ 3`.
  have hcoord (i : Fin 6) : (a : ℂ) * v i = if i.val < 3 then -v i else v i := by
    simpa [Units.smul_def] using congrFun ha i
  by_cases ha1 : (a : ℂ) = 1
  · -- Eigenvalue `1`: the first three coordinates vanish.
    refine hv (eq_zero_of_forall_eval_enriquesQuadric_eq_zero_of_card_le_three hz
      (s := {i | 3 ≤ i.val}) (by decide) fun i hi ↦ ?_)
    have h := hcoord i
    simp only [ha1, one_mul, show i.val < 3 by simpa using hi, ite_true] at h
    exact CharZero.eq_neg_self_iff.mp h
  · -- Any other eigenvalue: the last three coordinates vanish.
    refine hv (eq_zero_of_forall_eval_enriquesQuadric_eq_zero_of_card_le_three hz
      (s := {i | i.val < 3}) (by decide) fun i hi ↦ ?_)
    have h := hcoord i
    simp only [show ¬ i.val < 3 by simpa using hi, ite_false] at h
    exact (mul_left_eq_self₀.mp h).resolve_left ha1

end TauCeti
