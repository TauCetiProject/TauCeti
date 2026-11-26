/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.LinearAlgebra.Submodule.Zeta
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GeneralizedIndex
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Lattices in the finite adeles of a CM field, their discriminants, and sums over sublattices

Let `E` be a CM field, `𝔸_f` its finite adeles, `Ô` the integral ones, `κ` a finite set and
`x ↦ conj x` the complex conjugation, which acts on `𝔸_f` place by place
(`NumberField.IsCMField.finiteAdeleConj`). An `Ô`-submodule `L` of `𝔸_f^κ` is a *lattice of rank
`r`* if it is the `Ô`-span of the columns of `B = x a`, with `x` a `κ × r` matrix over `E` with
independent columns and `a ∈ GL_r(𝔸_f)` (`NumberField.IsCMField.IsLatticeOfRank`). Its
*discriminant* is `d_r(L) = [det(B^*B)]^(1/2)`, with `B^*` the conjugate transpose and `[·]` the
generalised index (`NumberField.IsCMField.latticeDiscriminant`); it does not depend on the choice
of `B`, because two such matrices spanning `L` differ by a matrix in `GL_r(Ô)`, whose determinant
has index `1`.

* **Sublattices of finite index.** An `Ô`-submodule `M` of finite index of a lattice `L` of rank
  `r` is a lattice of rank `r` (`NumberField.IsCMField.IsLatticeOfRank.of_le`), and
  `d_r(M) = d_r(L)·[L : M]`
  (`NumberField.IsCMField.IsLatticeOfRank.latticeDiscriminant_eq_mul_relIndex`). In the
  coordinates of a basis `B` of `L`, `M` is a submodule of finite index of `Ô^r`; since the ideals
  of finite index of `Ô` are principal, it is the image of a lower triangular matrix `A` with
  `[Ô^r : M] = ∏ᵢ [Ô : (A i i)] = [det A]` (`NumberField.FiniteAdeleRing.exists_span_col_mul_eq`),
  so `B A` is a basis of `M`.
* **Sums over sublattices.** `∑_{M ⊂ L} [L : M]^(-(r+μ)) ≤ ζ_Ô(μ)^r` over the submodules of finite
  index of a lattice of rank `r`, with `ζ_Ô(μ) = ∑_I [Ô : I]^(-μ)` over the ideals of finite index
  (`NumberField.IsCMField.IsLatticeOfRank.submoduleZeta_le`). This follows from
  `Module.submoduleZeta_pi_le` together with
  `IsDedekindDomain.FiniteAdeleRing.isPrincipal_of_cardQuot_ne_zero`.

## Main declarations

* `NumberField.IsCMField.finiteAdeleConj`: complex conjugation on the finite adeles.
* `NumberField.IsCMField.gramDet`: the Gram determinant `det(B^*B)` of an adelic matrix.
* `NumberField.IsCMField.IsLatticeOfRank`, `NumberField.IsCMField.latticeDiscriminant`: lattices of
  rank `r` in `𝔸_f^κ` and their discriminants.
* `NumberField.IsCMField.latticeDiscriminant_span_col`: the discriminant computed from any basis.
* `NumberField.IsCMField.IsLatticeOfRank.latticeDiscriminant_pos`: the discriminant is positive.
* `NumberField.IsCMField.IsLatticeOfRank.of_le`,
  `NumberField.IsCMField.IsLatticeOfRank.latticeDiscriminant_eq_mul_relIndex`: sublattices of
  finite index and their discriminants.
* `NumberField.IsCMField.IsLatticeOfRank.submoduleZeta_le`: the bound on sums over sublattices.

## References

* E. Hey, *Analytische Zahlentheorie in Systemen hyperkomplexer Zahlen*, Dissertation,
  Göttingen, 1929.

## Attribution

Adapted from the file `src/New/Spanning/RemainingTerms/Discriminants.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC):

* `NumberField.IsCMField.IsLatticeOfRank` from `New.Filling.IsLatticeOfRank`;
* `NumberField.IsCMField.latticeDiscriminant` from `New.Filling.discriminant`;
* `NumberField.IsCMField.genIndex_gramDet_eq_of_span_eq` and
  `NumberField.IsCMField.latticeDiscriminant_span_col` from
  `New.Filling.genIndex_det_gram_eq_of_colLattice_eq` and `New.Filling.discriminant_colLattice`;
* `NumberField.IsCMField.det_transpose_map_complexConj_mul_ne_zero` from
  `New.Filling.det_gram_ne_zero`;
* `NumberField.IsCMField.IsLatticeOfRank.latticeDiscriminant_pos` from
  `New.Filling.IsLatticeOfRank.discriminant_pos`;
* `NumberField.IsCMField.IsLatticeOfRank.of_le` and
  `NumberField.IsCMField.IsLatticeOfRank.latticeDiscriminant_eq_mul_relIndex` from
  `New.Filling.IsLatticeOfRank.of_le_and_discriminant_eq_mul_index`;
* `NumberField.IsCMField.IsLatticeOfRank.submoduleZeta_le` from
  `New.Filling.IsLatticeOfRank.tsum_submoduleIndex_inv_pow_le`.

That complex conjugation preserves `Ô`
(`NumberField.IsCMField.finiteAdeleConj_mem_integralAdeles_iff`) is `New.star_mem_Ô` in
`src/Lib/Adelic/Adeles/Basic.lean` of grh-lean, and the invariance of the generalised index under
it (`NumberField.IsCMField.genIndex_finiteAdeleConj`) is `New.genIndex_star` in
`src/Lib/General/Measure/HaarModulus.lean`. In grh-lean `E` is also assumed to contain a
primitive root of unity of order `5040`; nothing here needs it.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.FiniteAdeleRing
open Matrix
open scoped NumberField.AdeleRing

namespace NumberField.FiniteAdeleRing

variable {E : Type*} [Field E] [NumberField E] {κ : Type*} {r : ℕ}

/-- The `Ô`-linear map `Ô^r → 𝔸_f^κ` sending `c` to `∑ⱼ cⱼ Bⱼ`, for the columns `Bⱼ` of `B`. -/
private abbrev colMap (B : Matrix κ (Fin r) 𝔸ᶠ[E]) :
    (Fin r → integralAdeles (𝓞 E) E) →ₗ[integralAdeles (𝓞 E) E] κ → 𝔸ᶠ[E] :=
  Fintype.linearCombination (integralAdeles (𝓞 E) E) B.col

private theorem range_colMap (B : Matrix κ (Fin r) 𝔸ᶠ[E]) :
    LinearMap.range (colMap B) =
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col) :=
  Fintype.range_linearCombination _ _

private theorem colMap_col (B : Matrix κ (Fin r) 𝔸ᶠ[E])
    (A : Matrix (Fin r) (Fin r) (integralAdeles (𝓞 E) E)) (j : Fin r) :
    colMap B (A.col j) = (B * A.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E])).col j := by
  funext k
  simp [Fintype.linearCombination_apply, Finset.sum_apply, Subalgebra.smul_def, Matrix.mul_apply,
    mul_comm]

/-- In the coordinates of `B`, the columns of `B A` span the image of the columns of `A`. -/
private theorem map_colMap_span_col (B : Matrix κ (Fin r) 𝔸ᶠ[E])
    (A : Matrix (Fin r) (Fin r) (integralAdeles (𝓞 E) E)) :
    (LinearMap.range A.mulVecLin).map (colMap B) =
      Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range (B * A.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E])).col) := by
  rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
  congr 2
  exact funext (colMap_col B A)

/-- Let `B` be a matrix over the finite adeles, and `M` an `Ô`-submodule of finite index of the
`Ô`-span of its columns. Then `M` is spanned by the columns of `B A` for a
square matrix `A` with invertible determinant, and `[det A]` is the index of `M`. -/
theorem exists_span_col_mul_eq {B : Matrix κ (Fin r) 𝔸ᶠ[E]}
    {M : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hM : M ≤ Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col))
    (h_index : M.toAddSubgroup.relIndex
      (Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col)).toAddSubgroup ≠ 0) :
    ∃ A : Matrix (Fin r) (Fin r) 𝔸ᶠ[E], IsUnit A.det ∧
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range (B * A).col) = M ∧
      genIndex E A.det = M.toAddSubgroup.relIndex
        (Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col)).toAddSubgroup := by
  -- Pull `M` back to `Ô^r` along the coordinates of `B` and take a triangular basis there.
  have h_comap : (M.comap (colMap B)).cardQuot = M.toAddSubgroup.relIndex
      (Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col)).toAddSubgroup := by
    rw [← range_colMap]
    exact M.toAddSubgroup.index_comap (colMap B).toAddMonoidHom
  obtain ⟨A, hA_tri, hA_range, hA_index⟩ :=
    Submodule.exists_isLowerTriangular_range_mulVecLin_eq
      (fun I hI ↦ isPrincipal_of_cardQuot_ne_zero hI) _ (h_comap.trans_ne h_index)
  have h_entry (i : Fin r) : (Ideal.span {A i i}).cardQuot ≠ 0 :=
    Finset.prod_ne_zero_iff.1 (hA_index ▸ h_comap ▸ h_index) i (Finset.mem_univ i)
  have h_det : (A.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E])).det =
      ∏ i, algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E] (A i i) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_of_isLowerTriangular _ hA_tri, map_prod]
  refine ⟨A.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E]), ?_, ?_, ?_⟩
  · rw [h_det]
    exact IsUnit.prod_univ_iff.2 fun i ↦ isUnit_coe_of_cardQuot_span_singleton_ne_zero (h_entry i)
  · rw [← map_colMap_span_col, hA_range, Submodule.map_comap_eq_self (range_colMap B ▸ hM)]
  · rw [h_det, map_prod, ← h_comap, hA_index, Nat.cast_prod]
    exact Finset.prod_congr rfl fun i _ ↦
      genIndex_eq_cardQuot (isUnit_coe_of_cardQuot_span_singleton_ne_zero (h_entry i))

end NumberField.FiniteAdeleRing

namespace NumberField.IsCMField

open TauCeti.GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

variable (E) in
/-- Complex conjugation on the finite adeles of a CM field, acting place by place. -/
def finiteAdeleConj : 𝔸ᶠ[E] ≃+* 𝔸ᶠ[E] :=
  finiteAdeleEquiv E E (complexConj E).toRingEquiv

theorem finiteAdeleConj_def :
    finiteAdeleConj E = finiteAdeleEquiv E E (complexConj E).toRingEquiv :=
  (rfl)

/-- Complex conjugation on the finite adeles extends that of `E`. -/
@[simp]
theorem finiteAdeleConj_algebraMap (x : E) :
    finiteAdeleConj E (algebraMap E 𝔸ᶠ[E] x) = algebraMap E 𝔸ᶠ[E] (complexConj E x) :=
  finiteAdeleEquiv_algebraMap E E _ x

/-- Complex conjugation on the finite adeles is an involution. -/
@[simp]
theorem finiteAdeleConj_finiteAdeleConj (a : 𝔸ᶠ[E]) :
    finiteAdeleConj E (finiteAdeleConj E a) = a := by
  have h : (complexConj E).toRingEquiv.trans (complexConj E).toRingEquiv = RingEquiv.refl E :=
    RingEquiv.ext fun x ↦ complexConj_apply_apply (K := E) x
  rw [finiteAdeleConj_def, ← RingEquiv.trans_apply, finiteAdeleEquiv_trans, h,
    finiteAdeleEquiv_refl, RingEquiv.refl_apply]

/-- Complex conjugation preserves the integral finite adeles. -/
theorem finiteAdeleConj_mem_integralAdeles_iff {x : 𝔸ᶠ[E]} :
    finiteAdeleConj E x ∈ integralAdeles (𝓞 E) E ↔ x ∈ integralAdeles (𝓞 E) E :=
  finiteAdeleEquiv_mem_integralAdeles_iff _

/-- The generalised index is invariant under complex conjugation. -/
@[simp]
theorem genIndex_finiteAdeleConj (a : 𝔸ᶠ[E]) : genIndex E (finiteAdeleConj E a) = genIndex E a :=
  genIndex_map _ (fun _ ↦ finiteAdeleConj_mem_integralAdeles_iff) a

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
  rw [gramDet_def, gramDet_def, h_map, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ B,
    det_mul, det_mul, det_transpose, ← mul_assoc]
  congr 2
  exact (RingHom.map_det (finiteAdeleConj E).toRingHom M).symm

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

/-- An `Ô`-submodule `L` of `𝔸_f^κ` is a **lattice of rank `r`** if it is the `Ô`-span of the
columns of `x a`, where `x` is a `κ × r` matrix over the CM field `E` with independent columns (of
rank `r`) and `a ∈ GL_r(𝔸_f)`. -/
def IsLatticeOfRank (r : ℕ) (L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])) : Prop :=
  ∃ (x : Matrix κ (Fin r) E) (a : GL (Fin r) 𝔸ᶠ[E]), LinearIndependent E x.col ∧
    Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col) = L

omit [IsCMField E] [Fintype κ] in
theorem isLatticeOfRank_iff {L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])} :
    IsLatticeOfRank r L ↔ ∃ (x : Matrix κ (Fin r) E) (a : GL (Fin r) 𝔸ᶠ[E]),
      LinearIndependent E x.col ∧ Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col) = L :=
  Iff.rfl

omit [IsCMField E] [Fintype κ] in
/-- The `Ô`-span of the columns of `x a`, for `x` over `E` with independent columns and
`a ∈ GL_r(𝔸_f)`, is a lattice of rank `r`. -/
theorem isLatticeOfRank_span_col {x : Matrix κ (Fin r) E} (hx : LinearIndependent E x.col)
    (a : GL (Fin r) 𝔸ᶠ[E]) :
    IsLatticeOfRank r (Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col)) :=
  isLatticeOfRank_iff.2 ⟨x, a, hx, rfl⟩

open Classical in
/-- The **discriminant** `d_r(L) = [det(B^*B)]^(1/2)` of a lattice `L` of rank `r` in `𝔸_f^κ`, for
a basis `B = x a` of `L` as in `IsLatticeOfRank`; here `[·]` is the generalised index. It does not
depend on the choice of `B` (`latticeDiscriminant_span_col`). It is `0` if `L` is not a lattice of
rank `r`. -/
def latticeDiscriminant (r : ℕ) (L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])) : ℝ :=
  if h : IsLatticeOfRank r L then
    √(genIndex E (gramDet (h.choose.map (algebraMap E 𝔸ᶠ[E]) *
      (h.choose_spec.choose : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]))) : ℝ)
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
  obtain ⟨hy, h_span⟩ := hL.choose_spec.choose_spec
  rw [genIndex_gramDet_eq_of_span_eq
    (Matrix.exists_mul_map_mul_eq_one_of_linearIndependent_col hy hL.choose_spec.choose) h_span]

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

/-- The discriminant of a lattice of rank `r` is positive. -/
theorem IsLatticeOfRank.latticeDiscriminant_pos
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

omit [IsCMField E] [Fintype κ] in
/-- For a sublattice `M` of finite index of a lattice `L = span(x a)` of rank `r`, there is
`u ∈ GL_r(𝔸_f)` with `M = span(x (a u))` and `[det u] = [L : M]`. -/
private theorem exists_span_col_mul_eq_of_le {x : Matrix κ (Fin r) E} {a : GL (Fin r) 𝔸ᶠ[E]}
    {M : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hML : M ≤ Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col))
    (h_index : M.toAddSubgroup.relIndex (Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) *
        (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col)).toAddSubgroup ≠ 0) :
    ∃ u : GL (Fin r) 𝔸ᶠ[E], Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * ((a * u : GL (Fin r) 𝔸ᶠ[E]) :
          Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col) = M ∧
      genIndex E (u : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]).det = M.toAddSubgroup.relIndex
        (Submodule.span (integralAdeles (𝓞 E) E) (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) *
          (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col)).toAddSubgroup := by
  obtain ⟨A, hA_unit, hA_span, hA_index⟩ := exists_span_col_mul_eq hML h_index
  let u : GL (Fin r) 𝔸ᶠ[E] := ((Matrix.isUnit_iff_isUnit_det A).2 hA_unit).unit
  have hu : (u : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) = A := IsUnit.unit_spec _
  refine ⟨u, ?_, by rw [hu, hA_index]⟩
  rw [Units.val_mul, hu, ← Matrix.mul_assoc, hA_span]

omit [IsCMField E] [Fintype κ] in
/-- **Sublattices of finite index.** An `Ô`-submodule of finite index of a lattice of rank `r` is a
lattice of rank `r`. -/
theorem IsLatticeOfRank.of_le {L M : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hL : IsLatticeOfRank r L) (hML : M ≤ L)
    (h_index : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) : IsLatticeOfRank r M := by
  obtain ⟨x, a, hx, rfl⟩ := isLatticeOfRank_iff.1 hL
  obtain ⟨u, hu_span, -⟩ := exists_span_col_mul_eq_of_le hML h_index
  exact hu_span ▸ isLatticeOfRank_span_col hx (a * u)

/-- **Discriminants of sublattices.** For an `Ô`-submodule `M` of finite index of a lattice `L`
of rank `r`, `d_r(M) = d_r(L)·[L : M]`. -/
theorem IsLatticeOfRank.latticeDiscriminant_eq_mul_relIndex
    {L M : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])} (hL : IsLatticeOfRank r L)
    (hML : M ≤ L) (h_index : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    latticeDiscriminant r M =
      latticeDiscriminant r L * M.toAddSubgroup.relIndex L.toAddSubgroup := by
  obtain ⟨x, a, hx, rfl⟩ := isLatticeOfRank_iff.1 hL
  obtain ⟨u, hu_span, hu_index⟩ := exists_span_col_mul_eq_of_le hML h_index
  conv_lhs => rw [← hu_span, latticeDiscriminant_span_col hx]
  rw [latticeDiscriminant_span_col hx, Units.val_mul, ← Matrix.mul_assoc, genIndex_gramDet_mul,
    ← Rat.cast_natCast, ← hu_index, Rat.cast_mul,
    Rat.cast_pow, Real.sqrt_mul' _ (Rat.cast_nonneg.2 (genIndex_nonneg _)),
    Real.sqrt_sq (Rat.cast_nonneg.2 (genIndex_nonneg _)), mul_comm]

omit [IsCMField E] [Fintype κ] in
/-- **Sums over sublattices.** For a lattice `L` of rank `r` and every `μ ∈ ℕ`,
`∑_{M ⊂ L} [L : M]^(-(r+μ)) ≤ ζ_Ô(μ)^r`, the sum running over the submodules of finite index of
`L` and `ζ_Ô(μ) = ∑_I [Ô : I]^(-μ)` over the ideals of finite index of `Ô`. -/
theorem IsLatticeOfRank.submoduleZeta_le {L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hL : IsLatticeOfRank r L) (μ : ℕ) :
    Module.submoduleZeta (integralAdeles (𝓞 E) E) L (r + μ) ≤
      Module.submoduleZeta (integralAdeles (𝓞 E) E) (integralAdeles (𝓞 E) E) μ ^ r := by
  obtain ⟨x, a, -, rfl⟩ := isLatticeOfRank_iff.1 hL
  set B := x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])
  -- `Ô^r` maps onto `L` by the coordinates of `B`.
  have h_surj : Function.Surjective ((colMap B).codRestrict _ fun c ↦
      range_colMap B ▸ LinearMap.mem_range_self (colMap B) c) := by
    rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := (range_colMap B ▸ hy : y ∈ LinearMap.range (colMap B))
    exact ⟨c, rfl⟩
  exact (Module.submoduleZeta_le_of_surjective h_surj _).trans
    (Module.submoduleZeta_pi_le (fun I hI ↦ isPrincipal_of_cardQuot_ne_zero hI) r μ)

end NumberField.IsCMField
