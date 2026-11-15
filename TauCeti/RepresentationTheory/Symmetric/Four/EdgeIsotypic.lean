/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Four.Cube
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.RingTheory.SimpleModule.Isotypic

/-!
# The two copies of the standard representation in the cube edge representation

The standard representation `V₄` of `S₄` (the sum-zero vectors of `k[Fin 4]`) occurs twice in the
permutation representation `k[Y]` of `S₄` on the twelve edges of the cube
(`TauCeti.finrank_intertwiningMap_standardRepresentation_cubeEdgeRepresentation`). Character
pairings give this multiplicity, but not two particular copies. This file writes down a basis of the
two-dimensional space of intertwiners `V₄ → k[Y]` and the resulting explicit splitting of the
`V₄`-isotypic component of `k[Y]` into two copies of `V₄`.

Both intertwiners send a vector `u` of `V₄` to a function on the edges built from the four body
diagonals of the cube, labelled as in `TauCeti.cubeBodyDiagonal`.

* The **incidence copy** `TauCeti.cubeEdgeIncidence` gives the edge `{v, w}` the coefficient
  `u_i + u_j`, where `i` and `j` are the diagonals through `v` and `w`.
* The **oriented copy** `TauCeti.cubeEdgeOriented` gives it the coefficient `∑ₗ o(e, l) u_l` for the
  integer `o(e, l) = det(v, w, d) · ⟨v - w, d⟩` (`TauCeti.cubeEdgeOrientation`), where `d` is an
  endpoint of the diagonal `l`. It vanishes for the two diagonals through `v` and `w` and is `±8`
  for the other two, with opposite signs. The determinant is what keeps it invariant: a rotation has
  determinant one, while a reflection of the cube reverses the sign of `o`.

The two diagonals through an edge `{v, w}` form a pair `{i, j}`, and the two antipodal edges
`{v, w}` and `{-v, -w}` are the edges with this pair; the incidence copy takes the same value
`u_i + u_j` on them, while the oriented copy changes sign. Reading the coefficients on these pairs
of edges shows that `(a, b) ↦ incidence a + oriented b` is injective once `2` is not a zero
divisor
(`TauCeti.cubeEdgeStandardEval_injective`). In characteristic zero, where the space of intertwiners
is two-dimensional, the two copies are a basis of it (`TauCeti.cubeEdgeStandardBasis`) and their
images span the `V₄`-isotypic component, which is six-dimensional
(`TauCeti.asSubmodule_range_cubeEdgeStandardEval`).

## Main definitions

* `TauCeti.cubeEdgeOrientation`: the orientation `det(v, w, d) · ⟨v - w, d⟩` of an edge relative to
  a body diagonal.
* `TauCeti.cubeEdgeIncidence`, `TauCeti.cubeEdgeOriented`: the two intertwiners `V₄ → k[Y]`.
* `TauCeti.cubeEdgeStandardEval`: their sum, an intertwiner `V₄ ⊕ V₄ → k[Y]`.
* `TauCeti.cubeEdgeStandardBasis`: in characteristic zero, the basis of the intertwiners
  `V₄ → k[Y]` formed by the two copies.

## Main results

* `TauCeti.cubeEdgeOrientation_smul`: the orientation is invariant under the rotations.
* `TauCeti.cubeEdgeStandardEval_injective`: the two copies are independent once `2` is not a
  zero divisor.
* `TauCeti.asSubmodule_range_cubeEdgeStandardEval`: in characteristic zero, the image of
  `V₄ ⊕ V₄` is the `V₄`-isotypic component of `k[Y]`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §2.3.
* G. James and M. Liebeck, *Representations and Characters of Groups*, Chapter 18.
-/

public section

namespace TauCeti

open Equiv Matrix

/-! ### The orientation of an edge relative to a body diagonal -/

/-- The integer `det(a, b, c) · ⟨a - b, c⟩`, whose value on an edge `{a, b}` and a diagonal
endpoint `c` is the orientation of the edge. -/
private def orientedWeight (a b c : Fin 3 → ℤ) : ℤ :=
  (Matrix.of ![a, b, c]).det * ((a - b) ⬝ᵥ c)

private theorem orientedWeight_comm (a b c : Fin 3 → ℤ) :
    orientedWeight b a c = orientedWeight a b c := by
  simp [orientedWeight, det_fin_three, dotProduct, Fin.sum_univ_three]
  ring

private theorem orientedWeight_neg_right (a b c : Fin 3 → ℤ) :
    orientedWeight a b (-c) = orientedWeight a b c := by
  simp [orientedWeight, det_fin_three, dotProduct, Fin.sum_univ_three]
  ring

/-- The oriented weight is invariant under the rotations: they preserve both the determinant and
the dot product. -/
private theorem orientedWeight_mulVec {A : SpecialLinearGroup (Fin 3) ℤ}
    (hA : A ∈ cubeRotationGroup) (a b c : Fin 3 → ℤ) :
    orientedWeight ((A : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ a) ((A : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ b)
      ((A : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ c) = orientedWeight a b c := by
  have hdet : Matrix.of ![(A : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ a,
      (A : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ b, (A : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ c] =
      Matrix.of ![a, b, c] * (A : Matrix (Fin 3) (Fin 3) ℤ)ᵀ := by
    ext r i
    fin_cases r <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [orientedWeight, orientedWeight, hdet, det_mul, det_transpose, SpecialLinearGroup.det_coe,
    mul_one, ← mulVec_sub, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
    transpose_mul_self_of_mem_cubeRotationGroup hA, one_mulVec]

/-- **The orientation of an edge relative to a body diagonal.** For an edge `{v, w}` of the cube
and the body diagonal `j`, with endpoint `d = TauCeti.cubeBodyDiagonal j`, it is the integer
`det(v, w, d) · ⟨v - w, d⟩`. Both factors change sign when `v` and `w` are exchanged, so the
product depends only on the edge; it is `0` when `j` is the diagonal through `v` or through `w`,
and `±8` with opposite signs for the other two diagonals. Rotations preserve it
(`TauCeti.cubeEdgeOrientation_smul`). -/
def cubeEdgeOrientation (e : cubeEdgeSet) (j : Fin 4) : ℤ :=
  Sym2.lift (α := Fin 3 → ℤˣ) (β := ℤ)
    ⟨fun v w ↦ orientedWeight (fun i ↦ (v i : ℤ)) (fun i ↦ (w i : ℤ))
      (fun i ↦ (cubeBodyDiagonal j i : ℤ)), fun v w ↦ orientedWeight_comm (fun i ↦ (w i : ℤ))
      (fun i ↦ (v i : ℤ)) (fun i ↦ (cubeBodyDiagonal j i : ℤ))⟩ (e : Sym2 (Fin 3 → ℤˣ))

/-- The orientation of the edge `{v, w}` relative to the diagonal `j` is
`det(v, w, d) · ⟨v - w, d⟩` for `d = TauCeti.cubeBodyDiagonal j`. -/
theorem cubeEdgeOrientation_mk {v w : Fin 3 → ℤˣ} (h : s(v, w) ∈ cubeEdgeSet) (j : Fin 4) :
    cubeEdgeOrientation ⟨s(v, w), h⟩ j =
      (Matrix.of ![fun i ↦ (v i : ℤ), fun i ↦ (w i : ℤ), fun i ↦ (cubeBodyDiagonal j i : ℤ)]).det *
        (((fun i ↦ (v i : ℤ)) - fun i ↦ (w i : ℤ)) ⬝ᵥ fun i ↦ (cubeBodyDiagonal j i : ℤ)) :=
  (rfl)

/-- **The orientation is invariant under the rotations**: a rotation `A` carries an edge and a
diagonal `j` to an edge and the diagonal `A j` with the same orientation. -/
theorem cubeEdgeOrientation_smul (A : cubeRotationGroup) (e : cubeEdgeSet) (j : Fin 4) :
    cubeEdgeOrientation (A • e) (cubeBodyDiagonalHom A j) = cubeEdgeOrientation e j := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ v w =>
    have hvec (x : Fin 3 → ℤˣ) : (fun i ↦ ((A • x) i : ℤ)) =
        (A.1 : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ fun i ↦ (x i : ℤ) :=
      funext (coe_cubeRotationGroup_smul_apply A x)
    -- The endpoint of the diagonal `A j` is `± A d` for the endpoint `d` of `j`.
    have hd : orientedWeight (fun i ↦ ((A • v) i : ℤ)) (fun i ↦ ((A • w) i : ℤ))
        (fun i ↦ (cubeBodyDiagonal (cubeBodyDiagonalHom A j) i : ℤ)) =
        orientedWeight (fun i ↦ ((A • v) i : ℤ)) (fun i ↦ ((A • w) i : ℤ))
          (fun i ↦ ((A • cubeBodyDiagonal j) i : ℤ)) := by
      rcases cubeBodyDiagonalIndex_eq_iff.mp (cubeBodyDiagonalHom_apply A j).symm with h | h
      · rw [h]
      · rw [h, ← orientedWeight_neg_right]
        congr 1
    simp only [cubeEdgeOrientation, coe_cubeRotationGroup_smul_cubeEdgeSet, Sym2.map_mk,
      Sym2.lift_mk]
    rw [hd, hvec, hvec, hvec, orientedWeight_mulVec A.2]

/-- An antipodal edge has the opposite orientation. -/
private theorem cubeEdgeOrientation_neg {v w : Fin 3 → ℤˣ} (h : s(v, w) ∈ cubeEdgeSet)
    (h' : s(-v, -w) ∈ cubeEdgeSet) (j : Fin 4) :
    cubeEdgeOrientation ⟨s(-v, -w), h'⟩ j = -cubeEdgeOrientation ⟨s(v, w), h⟩ j := by
  simp [cubeEdgeOrientation_mk, det_fin_three, dotProduct, Fin.sum_univ_three]
  ring

/-! ### The two intertwiners -/

section Intertwiners

section CommSemiring

variable (k : Type*) [CommSemiring k]

/-- The linear map `k[Fin 4] → k[Y]` whose coefficient at the edge `e` is `∑ⱼ K e j f_j`. -/
private noncomputable def edgeKernelMap (K : cubeEdgeSet → Fin 4 → k) :
    MonoidAlgebra k (Fin 4) →ₗ[k] MonoidAlgebra k cubeEdgeSet where
  toFun f := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun e ↦ ∑ j, K e j * f.coeff j)
  map_add' f g := by ext e; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext e; simp [Finset.mul_sum, mul_left_comm]

private theorem coeff_edgeKernelMap (K : cubeEdgeSet → Fin 4 → k) (f : MonoidAlgebra k (Fin 4))
    (e : cubeEdgeSet) : (edgeKernelMap k K f).coeff e = ∑ j, K e j * f.coeff j := by
  simp [edgeKernelMap]

/-- A kernel invariant under the rotations gives an intertwiner `k[Fin 4] → k[Y]`. -/
private theorem edgeKernelMap_ofMulAction (K : cubeEdgeSet → Fin 4 → k)
    (hK : ∀ A e j, K (A • e) (cubeBodyDiagonalHom A j) = K e j) (σ : Perm (Fin 4))
    (f : MonoidAlgebra k (Fin 4)) :
    edgeKernelMap k K (Representation.ofMulAction k (Perm (Fin 4)) (Fin 4) σ f) =
      cubeEdgeRepresentation k σ (edgeKernelMap k K f) := by
  ext e
  rw [cubeEdgeRepresentation_apply, Representation.coeff_ofMulAction, coeff_edgeKernelMap,
    coeff_edgeKernelMap, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h := hK (cubeRotationEquiv.symm σ) ((cubeRotationEquiv.symm σ)⁻¹ • e) j
  rw [smul_inv_smul, ← cubeRotationEquiv_apply, MulEquiv.apply_symm_apply] at h
  simp only [Representation.coeff_ofMulAction, Perm.smul_def, h, Perm.inv_def, symm_apply_apply]

/-- The restriction to the standard representation of the intertwiner given by an invariant
kernel. -/
private noncomputable def standardKernelMap (K : cubeEdgeSet → Fin 4 → k)
    (hK : ∀ A e j, K (A • e) (cubeBodyDiagonalHom A j) = K e j) :
    (standardRepresentation k (Fin 4)).IntertwiningMap (cubeEdgeRepresentation k) :=
  (edgeKernelMap k K ∘ₗ
      (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule.subtype)
    |>.intertwiningMap_of_isIntertwiningMap _ _ fun σ u ↦ by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, coe_standardRepresentation_apply]
      exact edgeKernelMap_ofMulAction k K hK σ u

private theorem coeff_standardKernelMap (K : cubeEdgeSet → Fin 4 → k)
    (hK : ∀ A e j, K (A • e) (cubeBodyDiagonalHom A j) = K e j)
    (u : (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule) (e : cubeEdgeSet) :
    (standardKernelMap k K hK u).coeff e = ∑ j, K e j * (u : MonoidAlgebra k (Fin 4)).coeff j :=
  coeff_edgeKernelMap k K u e

/-- The number of endpoints of an edge on a body diagonal. -/
private noncomputable def incidenceKernel (e : cubeEdgeSet) (j : Fin 4) : k :=
  Sym2.lift (α := Fin 3 → ℤˣ) (β := k)
    ⟨fun v w ↦ (if cubeBodyDiagonalIndex v = j then 1 else 0) +
      (if cubeBodyDiagonalIndex w = j then 1 else 0), fun _ _ ↦ add_comm _ _⟩
    (e : Sym2 (Fin 3 → ℤˣ))

private theorem incidenceKernel_smul (A : cubeRotationGroup) (e : cubeEdgeSet) (j : Fin 4) :
    incidenceKernel k (A • e) (cubeBodyDiagonalHom A j) = incidenceKernel k e j := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ v w =>
    simp only [incidenceKernel, coe_cubeRotationGroup_smul_cubeEdgeSet, Sym2.map_mk, Sym2.lift_mk,
      ← cubeBodyDiagonalHom_apply_cubeBodyDiagonalIndex, EmbeddingLike.apply_eq_iff_eq]

/-- **The incidence copy of the standard representation in the edge representation**: the
intertwiner `V₄ → k[Y]` giving the edge `{v, w}` the coefficient `u_i + u_j`, where `i` and `j`
are the body diagonals through `v` and `w` (`TauCeti.coeff_cubeEdgeIncidence_mk`). -/
noncomputable def cubeEdgeIncidence :
    (standardRepresentation k (Fin 4)).IntertwiningMap (cubeEdgeRepresentation k) :=
  standardKernelMap k (incidenceKernel k) (incidenceKernel_smul k)

/-- The incidence copy gives the edge `{v, w}` the coefficient `u_i + u_j`, where `i` and `j` are
the body diagonals through `v` and `w`. -/
@[simp]
theorem coeff_cubeEdgeIncidence_mk
    (u : (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule)
    {v w : Fin 3 → ℤˣ} (h : s(v, w) ∈ cubeEdgeSet) :
    (cubeEdgeIncidence k u).coeff ⟨s(v, w), h⟩ =
      (u : MonoidAlgebra k (Fin 4)).coeff (cubeBodyDiagonalIndex v) +
        (u : MonoidAlgebra k (Fin 4)).coeff (cubeBodyDiagonalIndex w) := by
  simp [cubeEdgeIncidence, coeff_standardKernelMap, incidenceKernel, add_mul,
    Finset.sum_add_distrib]

end CommSemiring

variable (k : Type*) [CommRing k]

/-- **The oriented copy of the standard representation in the edge representation**: the
intertwiner `V₄ → k[Y]` giving the edge `e` the coefficient `∑ₗ o(e, l) u_l`, where `o` is the
orientation `TauCeti.cubeEdgeOrientation` (`TauCeti.coeff_cubeEdgeOriented`). -/
noncomputable def cubeEdgeOriented :
    (standardRepresentation k (Fin 4)).IntertwiningMap (cubeEdgeRepresentation k) :=
  standardKernelMap k (fun e j ↦ (cubeEdgeOrientation e j : k)) fun A e j ↦ by
    rw [cubeEdgeOrientation_smul]

/-- The oriented copy gives the edge `e` the coefficient `∑ₗ o(e, l) u_l`, where `o` is the
orientation `TauCeti.cubeEdgeOrientation`. -/
@[simp]
theorem coeff_cubeEdgeOriented
    (u : (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule) (e : cubeEdgeSet) :
    (cubeEdgeOriented k u).coeff e =
      ∑ j, (cubeEdgeOrientation e j : k) * (u : MonoidAlgebra k (Fin 4)).coeff j :=
  coeff_standardKernelMap k _ _ u e

/-- **The two copies of the standard representation together**: the intertwiner
`V₄ ⊕ V₄ → k[Y]`, `(a, b) ↦ TauCeti.cubeEdgeIncidence a + TauCeti.cubeEdgeOriented b`. -/
noncomputable def cubeEdgeStandardEval :
    ((standardRepresentation k (Fin 4)).prod (standardRepresentation k (Fin 4))).IntertwiningMap
      (cubeEdgeRepresentation k) :=
  ((cubeEdgeIncidence k).toLinearMap.coprod (cubeEdgeOriented k).toLinearMap)
    |>.intertwiningMap_of_isIntertwiningMap _ _ fun σ p ↦ by
      simp [Representation.IntertwiningMap.isIntertwining]

/-- The evaluation of the two copies at `(a, b)` is `cubeEdgeIncidence a + cubeEdgeOriented b`. -/
@[simp]
theorem cubeEdgeStandardEval_apply
    (p : (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule ×
      (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    cubeEdgeStandardEval k p = cubeEdgeIncidence k p.1 + cubeEdgeOriented k p.2 :=
  (rfl)

end Intertwiners

/-! ### Independence of the two copies -/

section Injective

variable {k : Type*} [CommRing k]

private theorem sum_coeff_eq_zero
    (u : (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    ∑ j, (u : MonoidAlgebra k (Fin 4)).coeff j = 0 := by
  have hu : (u : MonoidAlgebra k (Fin 4)) ∈
      LinearMap.ker (MonoidAlgebra.basis (Fin 4) k).sumCoords := by
    simpa only [toSubmodule_augmentationSubrepresentation] using u.2
  rw [LinearMap.mem_ker, Module.Basis.coe_sumCoords_of_fintype] at hu
  simpa using hu

private theorem eq_zero_of_coeff_eq_zero
    {u : (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule}
    (h₀ : (u : MonoidAlgebra k (Fin 4)).coeff 0 = 0)
    (h₁ : (u : MonoidAlgebra k (Fin 4)).coeff 1 = 0)
    (h₂ : (u : MonoidAlgebra k (Fin 4)).coeff 2 = 0)
    (h₃ : (u : MonoidAlgebra k (Fin 4)).coeff 3 = 0) :
    u = 0 := by
  ext j
  fin_cases j <;> simpa

/-- Reading `cubeEdgeIncidence a + cubeEdgeOriented b = 0` on an edge `{v, w}` and on its
antipodal edge `{-v, -w}`: the incidence copy takes the same value on both and the oriented copy
opposite values, so both values vanish. -/
private theorem coeff_eq_zero_of_cubeEdgeStandardEval_eq_zero (h2 : IsLeftRegular (2 : k))
    {p : (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule ×
      (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule}
    (hp : cubeEdgeStandardEval k p = 0) {v w : Fin 3 → ℤˣ} (h : s(v, w) ∈ cubeEdgeSet) :
    (p.1 : MonoidAlgebra k (Fin 4)).coeff (cubeBodyDiagonalIndex v) +
        (p.1 : MonoidAlgebra k (Fin 4)).coeff (cubeBodyDiagonalIndex w) = 0 ∧
      ∑ j, (cubeEdgeOrientation ⟨s(v, w), h⟩ j : k) * (p.2 : MonoidAlgebra k (Fin 4)).coeff j =
        0 := by
  have h' : s(-v, -w) ∈ cubeEdgeSet := mk_mem_cubeEdgeSet.mpr <|
    (hammingDist_comp (fun _ ↦ Neg.neg) (fun _ ↦ neg_injective)).trans (mk_mem_cubeEdgeSet.mp h)
  have he := congr(($hp).coeff ⟨s(v, w), h⟩)
  have he' := congr(($hp).coeff ⟨s(-v, -w), h'⟩)
  simp only [cubeEdgeStandardEval_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_cubeEdgeIncidence_mk, coeff_cubeEdgeOriented, cubeBodyDiagonalIndex_neg,
    cubeEdgeOrientation_neg h h', Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
    MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at he he'
  exact ⟨h2.mul_left_eq_zero_iff.mp (by linear_combination he + he'),
    h2.mul_left_eq_zero_iff.mp (by linear_combination he - he')⟩

/-- **The two copies of `V₄` in `k[Y]` are independent** when `2` is not a zero divisor:
`(a, b) ↦ TauCeti.cubeEdgeIncidence a + TauCeti.cubeEdgeOriented b` is injective. Reading its
coefficients on the edges whose diagonals are `{0, 1}`, `{0, 2}` and `{1, 2}` gives
`a₀ + a₁ = a₀ + a₂ = a₁ + a₂ = 0` and `b₀ = b₁ = b₂ = b₃`, and the coefficients of `a` and of `b`
sum to zero. -/
theorem cubeEdgeStandardEval_injective (h2 : IsLeftRegular (2 : k)) :
    Function.Injective (cubeEdgeStandardEval k) := by
  rw [← Representation.IntertwiningMap.coe_toLinearMap, ← LinearMap.ker_eq_bot,
    LinearMap.ker_eq_bot']
  rintro ⟨a, b⟩ hab
  have h8 : IsLeftRegular (8 : k) := by simpa [show (8 : k) = 2 ^ 3 by norm_num] using h2.pow 3
  obtain ⟨ha₀₁, hb₂₃⟩ := coeff_eq_zero_of_cubeEdgeStandardEval_eq_zero h2 hab
    (v := cubeBodyDiagonal 0) (w := -cubeBodyDiagonal 1)
    (mk_mem_cubeEdgeSet.mpr (by rw [cubeBodyDiagonal_def]; decide))
  obtain ⟨ha₀₂, hb₁₃⟩ := coeff_eq_zero_of_cubeEdgeStandardEval_eq_zero h2 hab
    (v := cubeBodyDiagonal 0) (w := -cubeBodyDiagonal 2)
    (mk_mem_cubeEdgeSet.mpr (by rw [cubeBodyDiagonal_def]; decide))
  obtain ⟨ha₁₂, hb₀₃⟩ := coeff_eq_zero_of_cubeEdgeStandardEval_eq_zero h2 hab
    (v := -cubeBodyDiagonal 1) (w := cubeBodyDiagonal 2)
    (mk_mem_cubeEdgeSet.mpr (by rw [cubeBodyDiagonal_def]; decide))
  simp only [cubeBodyDiagonalIndex_neg, cubeBodyDiagonalIndex_cubeBodyDiagonal] at ha₀₁ ha₀₂ ha₁₂
  -- The orientations of the three edges are `(0, 0, 8, -8)`, `(0, -8, 0, 8)` and `(-8, 0, 0, 8)`.
  replace hb₂₃ : 8 * (b : MonoidAlgebra k (Fin 4)).coeff 2 +
      -(8 * (b : MonoidAlgebra k (Fin 4)).coeff 3) = 0 := by
    simp only [cubeEdgeOrientation_mk, Fin.sum_univ_four] at hb₂₃
    simpa [cubeBodyDiagonal_def, det_fin_three, dotProduct, Fin.sum_univ_three] using hb₂₃
  replace hb₁₃ : -(8 * (b : MonoidAlgebra k (Fin 4)).coeff 1) +
      8 * (b : MonoidAlgebra k (Fin 4)).coeff 3 = 0 := by
    simp only [cubeEdgeOrientation_mk, Fin.sum_univ_four] at hb₁₃
    simpa [cubeBodyDiagonal_def, det_fin_three, dotProduct, Fin.sum_univ_three] using hb₁₃
  replace hb₀₃ : -(8 * (b : MonoidAlgebra k (Fin 4)).coeff 0) +
      8 * (b : MonoidAlgebra k (Fin 4)).coeff 3 = 0 := by
    simp only [cubeEdgeOrientation_mk, Fin.sum_univ_four] at hb₀₃
    simpa [cubeBodyDiagonal_def, det_fin_three, dotProduct, Fin.sum_univ_three] using hb₀₃
  have h32 : IsLeftRegular (32 : k) := by simpa [show (32 : k) = 2 ^ 5 by norm_num] using h2.pow 5
  have hsa := sum_coeff_eq_zero a
  have hsb := sum_coeff_eq_zero b
  rw [Fin.sum_univ_four] at hsa hsb
  have ha₀ : (a : MonoidAlgebra k (Fin 4)).coeff 0 = 0 :=
    h2.mul_left_eq_zero_iff.mp (by linear_combination ha₀₁ + ha₀₂ - ha₁₂)
  have hb₃ : (b : MonoidAlgebra k (Fin 4)).coeff 3 = 0 :=
    h32.mul_left_eq_zero_iff.mp (by linear_combination 8 * hsb - hb₂₃ + hb₁₃ + hb₀₃)
  refine Prod.ext (eq_zero_of_coeff_eq_zero ha₀ (by linear_combination ha₀₁ - ha₀)
    (by linear_combination ha₀₂ - ha₀) (by linear_combination hsa - ha₀₁ - ha₀₂ + ha₀))
    (eq_zero_of_coeff_eq_zero (h8.mul_left_eq_zero_iff.mp (by linear_combination -hb₀₃ + 8 * hb₃))
    (h8.mul_left_eq_zero_iff.mp (by linear_combination -hb₁₃ + 8 * hb₃))
    (h8.mul_left_eq_zero_iff.mp (by linear_combination hb₂₃ + 8 * hb₃)) hb₃)

/-- **The two copies of `V₄` in `k[Y]` are linearly independent intertwiners** when `2` is not a
zero divisor. -/
theorem linearIndependent_cubeEdgeIncidence_cubeEdgeOriented (h2 : IsLeftRegular (2 : k)) :
    LinearIndependent k ![cubeEdgeIncidence k, cubeEdgeOriented k] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  -- Evaluate at `u = e₀ - e₁`, whose coefficient at `0` is `1`.
  let u : (augmentationSubrepresentation k (Perm (Fin 4)) (Fin 4)).toSubmodule :=
    ⟨MonoidAlgebra.single 0 1 - MonoidAlgebra.single 1 1,
      single_sub_single_mem_augmentationSubrepresentation 0 1⟩
  have hu := cubeEdgeStandardEval_injective h2 (a₁ := (s • u, t • u)) (a₂ := 0) <| by
    simpa using congr($hst u)
  obtain ⟨hs, ht⟩ := Prod.mk_eq_zero.mp hu
  have hs0 := congrArg (fun x ↦ MonoidAlgebra.coeff (Subtype.val x) 0) hs
  have ht0 := congrArg (fun x ↦ MonoidAlgebra.coeff (Subtype.val x) 0) ht
  simp only [u, Submodule.coe_smul, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sub,
    MonoidAlgebra.coeff_single, Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_apply,
    smul_eq_mul, Submodule.coe_zero, MonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply] at hs0 ht0
  simpa using And.intro hs0 ht0

end Injective

/-! ### A basis of the multiplicity space and the isotypic component -/

section Isotypic

open scoped MonoidAlgebra

variable (k : Type*) [Field k] [CharZero k]

/-- **A basis of the multiplicity space of `V₄` in `k[Y]`** in characteristic zero: the incidence
and oriented copies `TauCeti.cubeEdgeIncidence` and `TauCeti.cubeEdgeOriented`. -/
noncomputable def cubeEdgeStandardBasis :
    Module.Basis (Fin 2) k
      ((standardRepresentation k (Fin 4)).IntertwiningMap (cubeEdgeRepresentation k)) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_cubeEdgeIncidence_cubeEdgeOriented two_ne_zero.isUnit.isRegular.left)
    (by rw [finrank_intertwiningMap_standardRepresentation_cubeEdgeRepresentation,
      Fintype.card_fin])

/-- The two members of `TauCeti.cubeEdgeStandardBasis` are the incidence and oriented copies. -/
@[simp]
theorem coe_cubeEdgeStandardBasis :
    ⇑(cubeEdgeStandardBasis k) = ![cubeEdgeIncidence k, cubeEdgeOriented k] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- **The two copies of `V₄` span its isotypic component in `k[Y]`**: in characteristic zero the
image of `(a, b) ↦ TauCeti.cubeEdgeIncidence a + TauCeti.cubeEdgeOriented b` is the
`V₄`-isotypic component of the edge representation, and by
`TauCeti.cubeEdgeStandardEval_injective` the map is an isomorphism onto it. -/
theorem asSubmodule_range_cubeEdgeStandardEval :
    (cubeEdgeStandardEval k).range.asSubmodule =
      isotypicComponent k[Perm (Fin 4)] (cubeEdgeRepresentation k).asModule
        (standardRepresentation k (Fin 4)).asModule := by
  have := isIrreducible_standardRepresentation (k := k) (α := Fin 4) (by decide)
    (Or.inr (by norm_num))
  have hle : (cubeEdgeStandardEval k).range.asSubmodule ≤
      isotypicComponent k[Perm (Fin 4)] (cubeEdgeRepresentation k).asModule
        (standardRepresentation k (Fin 4)).asModule := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    -- `ρ.asModule` is a type synonym for the carrier and `equivLinearMapAsModule` keeps the
    -- underlying function, so the two summands are values of `k[S₄]`-linear maps out of `V₄`.
    exact add_mem
      ((Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (cubeEdgeIncidence k)).apply_mem_isotypicComponent
          ((standardRepresentation k (Fin 4)).asModuleEquiv.symm a))
      ((Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (cubeEdgeOriented k)).apply_mem_isotypicComponent
          ((standardRepresentation k (Fin 4)).asModuleEquiv.symm b))
  refine Submodule.restrictScalars_injective k _ _ <|
    Submodule.eq_of_le_of_finrank_le (Submodule.restrictScalars_mono k hle) ?_
  have hrange : Module.finrank k (LinearMap.range (cubeEdgeStandardEval k).toLinearMap) = 6 := by
    rw [LinearMap.finrank_range_of_inj
        (cubeEdgeStandardEval_injective two_ne_zero.isUnit.isRegular.left),
      Module.finrank_prod, finrank_augmentationSubrepresentation]
    simp
  -- The range of the intertwiner, restricted to `k`, is the range of its underlying linear map.
  exact (finrank_isotypicComponent_cubeEdgeRepresentation_standardRepresentation k).trans_le
    hrange.ge

end Isotypic

end TauCeti
