/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Lattice
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Discriminants of lattices in the finite adeles of a CM field

Let `E` be a CM field, `𝔸_f` its finite adeles, `Ô` the integral ones, `κ` a finite set and
`x ↦ conj x` the complex conjugation, extended to the finite adeles
(`NumberField.IsCMField.finiteAdeleConj`, which permutes the finite places). For a lattice `L` of
rank `r` in `𝔸_f^κ`, the `Ô`-span of the columns of `B = x a`
(`NumberField.FiniteAdeleRing.IsLatticeOfRank`), the *discriminant* is
`d_r(L) = [det(B^*B)]^(1/2)`, with `B^*` the conjugate transpose and `[·]` the generalised index
(`NumberField.IsCMField.latticeDiscriminant`). It does not depend on the choice of `B`, because two
such matrices spanning `L` differ by a matrix in `GL_r(Ô)`, whose determinant has index `1`. It is
positive, and for an `Ô`-submodule `M` of finite index of `L`, `d_r(M) = d_r(L)·[L : M]`: a basis
of `M` is `B u` with `[det u] = [L : M]`
(`NumberField.FiniteAdeleRing.exists_span_col_mul_eq_of_le`).

## Main declarations

* `NumberField.IsCMField.genIndex_finiteAdeleConj`: the generalised index is invariant under
  complex conjugation.
* `NumberField.IsCMField.gramDet`: the Gram determinant `det(B^*B)` of an adelic matrix.
* `NumberField.IsCMField.latticeDiscriminant`: the discriminant of a lattice of rank `r`.
* `NumberField.IsCMField.latticeDiscriminant_span_col`: the discriminant computed from any basis.
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.latticeDiscriminant_pos`: the discriminant is
  positive.
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.latticeDiscriminant_eq_mul_relIndex`: the
  discriminant of a sublattice of finite index.

## Attribution

Adapted from the file `src/New/Spanning/RemainingTerms/Discriminants.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC):

* `NumberField.IsCMField.latticeDiscriminant` from `New.Filling.discriminant`;
* `NumberField.IsCMField.genIndex_gramDet_eq_of_span_eq` and
  `NumberField.IsCMField.latticeDiscriminant_span_col` from
  `New.Filling.genIndex_det_gram_eq_of_colLattice_eq` and `New.Filling.discriminant_colLattice`;
* `NumberField.IsCMField.det_transpose_map_complexConj_mul_ne_zero` from
  `New.Filling.det_gram_ne_zero`;
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.latticeDiscriminant_pos` from
  `New.Filling.IsLatticeOfRank.discriminant_pos`;
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.latticeDiscriminant_eq_mul_relIndex` from (the
  second half of) `New.Filling.IsLatticeOfRank.of_le_and_discriminant_eq_mul_index`.

The invariance of the generalised index under complex conjugation
(`NumberField.IsCMField.genIndex_finiteAdeleConj`) is `New.genIndex_star` in
`src/Lib/General/Measure/HaarModulus.lean` of grh-lean. In grh-lean `E` is also assumed to contain
a primitive root of unity of order `5040`; nothing here needs it.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.FiniteAdeleRing
open Matrix
open scoped NumberField.AdeleRing

namespace NumberField.IsCMField

open TauCeti.GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- The generalised index is invariant under complex conjugation. -/
@[simp]
theorem genIndex_finiteAdeleConj (a : 𝔸ᶠ[E]) : genIndex E (finiteAdeleConj E a) = genIndex E a :=
  genIndex_map _ (fun _ ↦ by rw [coe_finiteAdeleConj]; exact star_mem_integralAdeles_iff) a

variable {κ : Type*} [Fintype κ] {r : ℕ}

/-- The Gram determinant `det(B^*B)` of a matrix `B` over the finite adeles of a CM field, where
`B^*` is the conjugate transpose for complex conjugation. -/
def gramDet (B : Matrix κ (Fin r) 𝔸ᶠ[E]) : 𝔸ᶠ[E] :=
  ((B.map (finiteAdeleConj E))ᵀ * B).det

theorem gramDet_def (B : Matrix κ (Fin r) 𝔸ᶠ[E]) :
    gramDet B = ((B.map (finiteAdeleConj E))ᵀ * B).det :=
  (rfl)

/-- Changing the columns of `B` by a square matrix `M` multiplies the Gram determinant by
`conj (det M) · det M`. -/
theorem gramDet_mul (B : Matrix κ (Fin r) 𝔸ᶠ[E]) (M : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) :
    gramDet (B * M) = finiteAdeleConj E M.det * gramDet B * M.det := by
  have h_map : (B * M).map (finiteAdeleConj E) =
      B.map (finiteAdeleConj E) * M.map (finiteAdeleConj E) :=
    Matrix.map_mul (f := (finiteAdeleConj E).toRingHom)
  have h_det : (M.map (finiteAdeleConj E)).det = finiteAdeleConj E M.det :=
    (RingHom.map_det (finiteAdeleConj E).toRingHom M).symm
  calc gramDet (B * M)
    _ = ((M.map (finiteAdeleConj E))ᵀ * ((B.map (finiteAdeleConj E))ᵀ * B) * M).det := by
      rw [gramDet_def, h_map, transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = finiteAdeleConj E M.det * gramDet B * M.det := by
      rw [det_mul, det_mul, det_transpose, h_det, gramDet_def B]

/-- Changing the columns of `B` by a square matrix `M` multiplies the generalised index of the
Gram determinant by `[det M]²`. -/
theorem genIndex_gramDet_mul (B : Matrix κ (Fin r) 𝔸ᶠ[E]) (M : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) :
    genIndex E (gramDet (B * M)) = genIndex E M.det ^ 2 * genIndex E (gramDet B) := by
  rw [gramDet_mul, map_mul, map_mul, genIndex_finiteAdeleConj]
  ring

/-- Two matrices over the finite adeles whose columns span the same `Ô`-submodule, the first with
a left inverse, have Gram determinants of the same generalised index. -/
theorem genIndex_gramDet_eq_of_span_eq {B C : Matrix κ (Fin r) 𝔸ᶠ[E]}
    (hB : ∃ l : Matrix (Fin r) κ 𝔸ᶠ[E], l * B = 1)
    (h : Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col) =
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range C.col)) :
    genIndex E (gramDet B) = genIndex E (gramDet C) := by
  obtain ⟨l, hl⟩ := hB
  obtain ⟨U, rfl⟩ := Matrix.exists_mul_map_eq_of_span_le h.ge
  obtain ⟨V, hV⟩ := Matrix.exists_mul_map_eq_of_span_le h.le
  set ι := algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E]
  have hUV : U * V = 1 := by
    refine Matrix.map_injective (f := ι) (fun x y hxy ↦ Subtype.ext (by simpa [ι] using hxy)) ?_
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]
    calc U.map ι * V.map ι
      _ = l * B * (U.map ι * V.map ι) := by rw [hl, Matrix.one_mul]
      _ = l * (B * U.map ι * V.map ι) := by rw [Matrix.mul_assoc l, Matrix.mul_assoc B]
      _ = 1 := by rw [hV, hl]
  rw [genIndex_gramDet_mul, genIndex_det_map_eq_one hUV, one_pow, one_mul]

open Classical in
/-- The **discriminant** `d_r(L) = [det(B^*B)]^(1/2)` of a lattice `L` of rank `r` in `𝔸_f^κ`, for
a basis `B = x a` of `L` as in `IsLatticeOfRank`; here `[·]` is the generalised index. It does not
depend on the choice of `B` (`latticeDiscriminant_span_col`). It is `0` if `L` is not a lattice of
rank `r`. -/
def latticeDiscriminant (r : ℕ) (L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])) : ℝ :=
  if h : IsLatticeOfRank r L then
    √(genIndex E (gramDet ((isLatticeOfRank_iff.1 h).choose.map (algebraMap E 𝔸ᶠ[E]) *
      ((isLatticeOfRank_iff.1 h).choose_spec.choose : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]))) : ℝ)
  else 0

/-- The discriminant of a submodule that is not a lattice of rank `r` is `0`. -/
theorem latticeDiscriminant_of_not_isLatticeOfRank
    {L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])} (h : ¬ IsLatticeOfRank r L) :
    latticeDiscriminant r L = 0 := by
  rw [latticeDiscriminant, dite_eq_right h]

/-- The discriminant is nonnegative. -/
theorem latticeDiscriminant_nonneg (L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])) :
    0 ≤ latticeDiscriminant r L := by
  by_cases h : IsLatticeOfRank r L
  · rw [latticeDiscriminant, dite_eq_left h]
    exact Real.sqrt_nonneg _
  · exact (latticeDiscriminant_of_not_isLatticeOfRank h).ge

/-- The discriminant of the lattice spanned by the columns of `x a` is `[det((x a)^*(x a))]^(1/2)`.
-/
theorem latticeDiscriminant_span_col {x : Matrix κ (Fin r) E} (hx : LinearIndependent E x.col)
    (a : GL (Fin r) 𝔸ᶠ[E]) :
    latticeDiscriminant r (Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col)) =
      √(genIndex E (gramDet (x.map (algebraMap E 𝔸ᶠ[E]) *
        (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]))) : ℝ) := by
  have hL := isLatticeOfRank_span_col hx a
  rw [latticeDiscriminant, dite_eq_left hL]
  obtain ⟨hy, h_span⟩ := (isLatticeOfRank_iff.1 hL).choose_spec.choose_spec
  rw [genIndex_gramDet_eq_of_span_eq (Matrix.exists_mul_map_mul_eq_one_of_linearIndependent_col hy
    (isLatticeOfRank_iff.1 hL).choose_spec.choose) h_span]

open ComplexOrder in
/-- The Gram determinant `det(x^*x)` of a matrix `x` over the CM field `E` with independent
columns is not zero. -/
theorem det_transpose_map_complexConj_mul_ne_zero {x : Matrix κ (Fin r) E}
    (hx : LinearIndependent E x.col) : ((x.map (complexConj E))ᵀ * x).det ≠ 0 := by
  classical
  -- At a complex embedding, `det(x^*x)` is the Gram determinant of independent vectors for a
  -- positive definite hermitian form.
  obtain ⟨l, hl⟩ := Matrix.exists_mul_eq_one_of_linearIndependent_col hx
  let φ : E →+* ℂ := Classical.choice inferInstance
  have h_map : ((x.map (complexConj E))ᵀ * x).map φ = (x.map φ)ᴴ * x.map φ := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp [conjTranspose_apply]
  intro h_zero
  obtain ⟨v, hv, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.2
    (show ((x.map φ)ᴴ * x.map φ).det = 0 by
      rw [← h_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h_zero, map_zero])
  rw [conjTranspose_mul_self_mulVec_eq_zero] at hv_zero
  refine hv ?_
  have h_inv : l.map φ * x.map φ = 1 := by
    rw [← Matrix.map_mul, hl, Matrix.map_one _ (map_zero φ) (map_one φ)]
  rw [← Matrix.one_mulVec v, ← h_inv, ← Matrix.mulVec_mulVec, hv_zero, Matrix.mulVec_zero]

end NumberField.IsCMField

namespace NumberField.FiniteAdeleRing.IsLatticeOfRank

open NumberField.IsCMField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {κ : Type*} [Fintype κ] {r : ℕ}

/-- The discriminant of a lattice of rank `r` is positive. -/
theorem latticeDiscriminant_pos
    {L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])} (hL : IsLatticeOfRank r L) :
    0 < latticeDiscriminant r L := by
  obtain ⟨x, a, hx, rfl⟩ := isLatticeOfRank_iff.1 hL
  have h_gram : gramDet (x.map (algebraMap E 𝔸ᶠ[E])) =
      algebraMap E 𝔸ᶠ[E] ((x.map (complexConj E))ᵀ * x).det := by
    have h_conj : (x.map (algebraMap E 𝔸ᶠ[E])).map (finiteAdeleConj E) =
        (x.map (complexConj E)).map (algebraMap E 𝔸ᶠ[E]) := by
      ext i j : 1
      simp
    rw [gramDet_def, h_conj, ← Matrix.transpose_map, ← Matrix.map_mul, RingHom.map_det,
      RingHom.mapMatrix_apply]
  rw [latticeDiscriminant_span_col hx, genIndex_gramDet_mul, h_gram, genIndex_algebraMap]
  refine Real.sqrt_pos.2 (Rat.cast_pos.2 (mul_pos (pow_pos (genIndex_units_pos a.det) 2) ?_))
  exact abs_pos.2 ((Algebra.norm_ne_zero_iff).2 (det_transpose_map_complexConj_mul_ne_zero hx))

/-- **Discriminants of sublattices.** For an `Ô`-submodule `M` of finite index of a lattice `L`
of rank `r`, `d_r(M) = d_r(L)·[L : M]`. -/
theorem latticeDiscriminant_eq_mul_relIndex
    {L M : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])} (hL : IsLatticeOfRank r L)
    (hML : M ≤ L) (h_index : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    latticeDiscriminant r M =
      latticeDiscriminant r L * M.toAddSubgroup.relIndex L.toAddSubgroup := by
  obtain ⟨x, a, hx, rfl⟩ := isLatticeOfRank_iff.1 hL
  obtain ⟨u, hu_span, hu_index⟩ := exists_span_col_mul_eq_of_le hML h_index
  -- In `ℚ`: `[det((x a u)^*(x a u))] = [L : M]² · [det((x a)^*(x a))]`.
  conv_lhs => rw [← hu_span, latticeDiscriminant_span_col hx, Units.val_mul, ← Matrix.mul_assoc,
    genIndex_gramDet_mul, hu_index]
  -- Then take square roots in `ℝ`.
  rw [latticeDiscriminant_span_col hx]
  push_cast
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]

end NumberField.FiniteAdeleRing.IsLatticeOfRank
