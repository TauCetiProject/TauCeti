/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Submodule.Zeta
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GeneralizedIndex
import Mathlib.Topology.Instances.Matrix
import TauCeti.LinearAlgebra.Matrix.Range
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Lattices in the finite adeles of a number field and sums over their sublattices

Let `E` be a number field, `𝔸_f` its finite adeles, `Ô` the integral ones and `κ` a finite set.
An `Ô`-submodule `L` of `𝔸_f^κ` is a *lattice of rank `r`* if it is the `Ô`-span of the columns of
`B = x a`, with `x` a `κ × r` matrix over `E` with independent columns and `a ∈ GL_r(𝔸_f)`
(`NumberField.FiniteAdeleRing.IsLatticeOfRank`).

* **Sublattices of finite index.** An `Ô`-submodule `M` of finite index of a lattice `L` of rank
  `r` is a lattice of rank `r` (`NumberField.FiniteAdeleRing.IsLatticeOfRank.of_le`). In the
  coordinates of a basis `B` of `L`, `M` is a submodule of finite index of `Ô^r`; since the ideals
  of finite index of `Ô` are principal, it is the image of a lower triangular matrix `A` with
  `[Ô^r : M] = ∏ᵢ [Ô : (A i i)] = [det A]` (`NumberField.FiniteAdeleRing.exists_span_col_mul_eq`),
  so `B A` is a basis of `M`.
* **Lattices spanned by invertible matrices.** For `w ∈ GL_n(𝔸_f)`, the `Ô`-span `w Ôⁿ` of the
  columns of `w` is open and compact in `𝔸_fⁿ`, and every submodule of finite index of it is
  `w a Ôⁿ` with `[det a]` the index (`NumberField.FiniteAdeleRing.exists_mul_span_col_eq`). For
  integral `u`, `[Ôⁿ : u Ôⁿ] = [det u]` (`NumberField.FiniteAdeleRing.genIndex_det_eq_relIndex`).
* **Sums over sublattices.** `∑_{M ⊂ L} [L : M]^(-(r+μ)) ≤ ζ_Ô(μ)^r` over the submodules of finite
  index of a lattice of rank `r`, with `ζ_Ô(μ) = ∑_I [Ô : I]^(-μ)` over the ideals of finite index
  (`NumberField.FiniteAdeleRing.IsLatticeOfRank.submoduleZeta_le`). This follows from
  `Module.submoduleZeta_pi_le` together with
  `IsDedekindDomain.FiniteAdeleRing.isPrincipal_of_cardQuot_ne_zero`.

The discriminant of a lattice, for a CM field, is in
`TauCeti.NumberTheory.NumberField.CMField.AdelicLattice`.

## Main declarations

* `NumberField.FiniteAdeleRing.exists_span_col_mul_eq`: a submodule of finite index of the span of
  the columns of `B` is spanned by the columns of `B A`, with `[det A]` its index.
* `NumberField.FiniteAdeleRing.IsLatticeOfRank`: lattices of rank `r` in `𝔸_f^κ`.
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.of_le`: sublattices of finite index.
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.submoduleZeta_le`: the bound on sums over
  sublattices.
* `NumberField.FiniteAdeleRing.isOpen_span_col`, `NumberField.FiniteAdeleRing.isCompact_span_col`:
  the `Ô`-span of the columns of `w ∈ GL_n(𝔸_f)` is open and compact.
* `NumberField.FiniteAdeleRing.exists_mul_span_col_eq`: its submodules of finite index are spanned
  by the columns of `w a`, with `[det a]` the index.
* `NumberField.FiniteAdeleRing.genIndex_det_eq_relIndex`: `[det u] = [Ôⁿ : u Ôⁿ]` for an integral
  `u ∈ GL_n(𝔸_f)`.

## References

* E. Hey, *Analytische Zahlentheorie in Systemen hyperkomplexer Zahlen*, Dissertation,
  Göttingen, 1929.

## Attribution

Adapted from the file `src/New/Spanning/RemainingTerms/Discriminants.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC):

* `NumberField.FiniteAdeleRing.IsLatticeOfRank` from `New.Filling.IsLatticeOfRank`;
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.of_le` from (the first half of)
  `New.Filling.IsLatticeOfRank.of_le_and_discriminant_eq_mul_index`;
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.submoduleZeta_le` from
  `New.Filling.IsLatticeOfRank.tsum_submoduleIndex_inv_pow_le`.

In grh-lean `E` is a CM field containing a primitive root of unity of order `5040`; nothing here
needs either assumption.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField
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

/-- An `Ô`-submodule `L` of `𝔸_f^κ` is a **lattice of rank `r`** if it is the `Ô`-span of the
columns of `x a`, where `x` is a `κ × r` matrix over the number field `E` with independent columns
(of rank `r`) and `a ∈ GL_r(𝔸_f)`. -/
def IsLatticeOfRank (r : ℕ) (L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])) : Prop :=
  ∃ (x : Matrix κ (Fin r) E) (a : GL (Fin r) 𝔸ᶠ[E]), LinearIndependent E x.col ∧
    Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col) = L

theorem isLatticeOfRank_iff {L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])} :
    IsLatticeOfRank r L ↔ ∃ (x : Matrix κ (Fin r) E) (a : GL (Fin r) 𝔸ᶠ[E]),
      LinearIndependent E x.col ∧ Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col) = L :=
  Iff.rfl

/-- The `Ô`-span of the columns of `x a`, for `x` over `E` with independent columns and
`a ∈ GL_r(𝔸_f)`, is a lattice of rank `r`. -/
theorem isLatticeOfRank_span_col {x : Matrix κ (Fin r) E} (hx : LinearIndependent E x.col)
    (a : GL (Fin r) 𝔸ᶠ[E]) :
    IsLatticeOfRank r (Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col)) :=
  isLatticeOfRank_iff.2 ⟨x, a, hx, rfl⟩

/-- For a submodule `M` of finite index of the `Ô`-span `L` of the columns of `x a`, there is
`u ∈ GL_r(𝔸_f)` with `M = span(x (a u))` and `[det u] = [L : M]`. -/
theorem exists_span_col_mul_eq_of_le {x : Matrix κ (Fin r) E} {a : GL (Fin r) 𝔸ᶠ[E]}
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

/-- **Sublattices of finite index.** An `Ô`-submodule of finite index of a lattice of rank `r` is a
lattice of rank `r`. -/
theorem IsLatticeOfRank.of_le {L M : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hL : IsLatticeOfRank r L) (hML : M ≤ L)
    (h_index : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) : IsLatticeOfRank r M := by
  obtain ⟨x, a, hx, rfl⟩ := isLatticeOfRank_iff.1 hL
  obtain ⟨u, hu_span, -⟩ := exists_span_col_mul_eq_of_le hML h_index
  exact hu_span ▸ isLatticeOfRank_span_col hx (a * u)

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


/-! ### Lattices spanned by invertible matrices -/

section InvertibleMatrices

open Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `Ô`-span of the columns of `w ∈ GL_n(𝔸_f)` is the preimage of `Ôⁿ` under `w⁻¹`. -/
theorem coe_span_col_eq_preimage (w : GL n 𝔸ᶠ[E]) :
    (Submodule.span (integralAdeles (𝓞 E) E) (Set.range (w : Matrix n n 𝔸ᶠ[E]).col) :
      Set (n → 𝔸ᶠ[E])) = (fun x ↦ ((w⁻¹ : GL n 𝔸ᶠ[E]) : Matrix n n 𝔸ᶠ[E]) *ᵥ x) ⁻¹'
        Set.univ.pi fun _ ↦ (integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E]) := by
  ext x
  simp [mem_span_col_iff_mulVec_inv_mem]

/-- The `Ô`-span of the columns of `w ∈ GL_n(𝔸_f)` is open. -/
theorem isOpen_span_col (w : GL n 𝔸ᶠ[E]) :
    IsOpen (Submodule.span (integralAdeles (𝓞 E) E) (Set.range (w : Matrix n n 𝔸ᶠ[E]).col) :
      Set (n → 𝔸ᶠ[E])) := by
  rw [coe_span_col_eq_preimage]
  exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_integralAdeles (𝓞 E) E).preimage
    (continuous_const.matrix_mulVec continuous_id)

/-- The `Ô`-span of the columns of `w ∈ GL_n(𝔸_f)` is compact. -/
theorem isCompact_span_col (w : GL n 𝔸ᶠ[E]) :
    IsCompact (Submodule.span (integralAdeles (𝓞 E) E) (Set.range (w : Matrix n n 𝔸ᶠ[E]).col) :
      Set (n → 𝔸ᶠ[E])) := by
  have h : (Submodule.span (integralAdeles (𝓞 E) E) (Set.range (w : Matrix n n 𝔸ᶠ[E]).col) :
      Set (n → 𝔸ᶠ[E])) = (fun y ↦ (w : Matrix n n 𝔸ᶠ[E]) *ᵥ y) ''
        Set.univ.pi fun _ ↦ (integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E]) := by
    ext x
    simp [mem_span_col_iff, Set.mem_image]
  rw [h]
  exact (isCompact_univ_pi fun _ ↦ isCompact_integralAdeles).image
    (continuous_const.matrix_mulVec continuous_id)

/-- An `Ô`-submodule of the column span of `w ∈ GL_n(𝔸_f)` of finite index in it is spanned by the
columns of `w a`, for some `a ∈ GL_n(𝔸_f)` with `[det a]` the index. This is
`NumberField.FiniteAdeleRing.exists_span_col_mul_eq` with the columns indexed by `n`. -/
theorem exists_mul_span_col_eq (w : GL n 𝔸ᶠ[E])
    {M : Submodule (integralAdeles (𝓞 E) E) (n → 𝔸ᶠ[E])}
    (hM : M ≤ Submodule.span (integralAdeles (𝓞 E) E) (Set.range (w : Matrix n n 𝔸ᶠ[E]).col))
    (h_index : M.toAddSubgroup.relIndex (Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (w : Matrix n n 𝔸ᶠ[E]).col)).toAddSubgroup ≠ 0) :
    ∃ a : GL n 𝔸ᶠ[E], Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range ((w * a : GL n 𝔸ᶠ[E]) : Matrix n n 𝔸ᶠ[E]).col) = M ∧
      genIndex E (det a : 𝔸ᶠ[E]) = M.toAddSubgroup.relIndex (Submodule.span
        (integralAdeles (𝓞 E) E) (Set.range (w : Matrix n n 𝔸ᶠ[E]).col)).toAddSubgroup := by
  -- Index the columns of `w` by `Fin r` through `e`.
  let e := Fintype.equivFin n
  have h_range : Set.range ((w : Matrix n n 𝔸ᶠ[E]).submatrix id e.symm).col =
      Set.range (w : Matrix n n 𝔸ᶠ[E]).col :=
    e.symm.surjective.range_comp (w : Matrix n n 𝔸ᶠ[E]).col
  rw [← h_range] at hM h_index ⊢
  obtain ⟨A, hA, hA_span, hA_index⟩ := exists_span_col_mul_eq hM h_index
  have ha : IsUnit (A.submatrix e e).det := by rwa [det_submatrix_equiv_self]
  refine ⟨((isUnit_iff_isUnit_det _).2 ha).unit, ?_, ?_⟩
  · -- The columns of `w (A.submatrix e e)` are those of `(w.submatrix id e.symm) A`.
    have h_mul : (w : Matrix n n 𝔸ᶠ[E]) * A.submatrix e e =
        ((w : Matrix n n 𝔸ᶠ[E]).submatrix id e.symm * A).submatrix id e := by
      rw [submatrix_mul _ _ _ e _ e.bijective, submatrix_submatrix, Function.comp_id,
        e.symm_comp_self, submatrix_id_id]
    rw [Units.val_mul, IsUnit.unit_spec, h_mul, ← hA_span]
    exact congrArg _ (e.surjective.range_comp
      ((w : Matrix n n 𝔸ᶠ[E]).submatrix id e.symm * A).col)
  · rw [val_det_apply, IsUnit.unit_spec, det_submatrix_equiv_self, hA_index]

/-- **The index of an integral lattice.** For `u ∈ GL_n(𝔸_f)` with integral entries, the
generalised index of `det u` is the index `[Ôⁿ : u Ôⁿ]` of the span of the columns of `u`. -/
theorem genIndex_det_eq_relIndex {u : GL n 𝔸ᶠ[E]}
    (hu : (u : Matrix n n 𝔸ᶠ[E]) ∈ (integralAdeles (𝓞 E) E).matrix) :
    genIndex E (det u : 𝔸ᶠ[E]) = (Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (u : Matrix n n 𝔸ᶠ[E]).col)).toAddSubgroup.relIndex
        (Submodule.span (integralAdeles (𝓞 E) E)
          (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col)).toAddSubgroup := by
  have h_le : Submodule.span (integralAdeles (𝓞 E) E) (Set.range (u : Matrix n n 𝔸ᶠ[E]).col) ≤
      Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range ((1 : GL n 𝔸ᶠ[E]) : Matrix n n 𝔸ᶠ[E]).col) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact mem_span_col_one_iff.2 fun i ↦ hu i j
  obtain ⟨a, ha_span, ha_index⟩ := exists_mul_span_col_eq 1 h_le
    (AddSubgroup.relIndex_ne_zero_of_isOpen_of_isCompact (isOpen_span_col u)
      (isCompact_span_col 1))
  rw [one_mul] at ha_span
  -- `u` differs from `a` by an element `k` of `GL_n(Ô)`, whose determinant has index `1`.
  obtain ⟨k, rfl⟩ := exists_eq_mul_map_of_span_col_eq ha_span
  rw [map_mul, Units.val_mul, map_mul, ha_index, Units.val_one]
  have hk : genIndex E (det (map (integralAdeles (𝓞 E) E).val.toRingHom k) : 𝔸ᶠ[E]) = 1 := by
    rw [val_det_apply]
    exact genIndex_det_map_eq_one (k.mul_inv)
  rw [hk, mul_one]

end InvertibleMatrices

end NumberField.FiniteAdeleRing
