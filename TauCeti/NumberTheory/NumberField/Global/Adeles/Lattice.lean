/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Submodule.Zeta
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GeneralizedIndex
import TauCeti.LinearAlgebra.Matrix.Range

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
* **Sums over sublattices.** `∑_{M ⊂ L} [L : M]^(-(r+μ)) ≤ ζ_Ô(μ)^r` over the submodules of finite
  index of a lattice of rank `r`, with `ζ_Ô(μ) = ∑_I [Ô : I]^(-μ)` over the ideals of finite index
  (`NumberField.FiniteAdeleRing.IsLatticeOfRank.submoduleZeta_le`). This follows from
  `Module.submoduleZeta_pi_le` together with
  `IsDedekindDomain.FiniteAdeleRing.isPrincipal_of_cardQuot_ne_zero`.

The discriminant of a lattice, for a CM field, is in
`TauCeti.NumberTheory.NumberField.CMField.AdelicLattice`.

## Main declarations

* `NumberField.FiniteAdeleRing.exists_range_mulVecLin_eq_genIndex_det`: a submodule `N` of finite
  index of `Ô^r` is `A Ô^r` for a square matrix `A` over `Ô` with `[det A] = [Ô^r : N]`.
* `NumberField.FiniteAdeleRing.cardQuot_range_mulVecLin_eq_genIndex_det`: `[Ô^r : C Ô^r] = [det C]`
  for a square matrix `C` over `Ô` (both sides `0` when `det C` is not a unit of `𝔸_f`).
* `NumberField.FiniteAdeleRing.exists_span_col_mul_eq`: a submodule of finite index of the span of
  the columns of `B` is spanned by the columns of `B A`, with `[det A]` its index.
* `NumberField.FiniteAdeleRing.IsLatticeOfRank`: lattices of rank `r` in `𝔸_f^κ`.
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.of_le`: sublattices of finite index.
* `NumberField.FiniteAdeleRing.IsLatticeOfRank.submoduleZeta_le`: the bound on sums over
  sublattices.

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

/-- **A basis of a submodule of finite index of `Ô^r`.** An `Ô`-submodule `N` of finite index of
`Ô^r` is the image of a square matrix `A` over `Ô` whose determinant is a unit of `𝔸_f`, with
`[det A] = [Ô^r : N]`; `A` can be taken lower triangular, since the ideals of finite index of `Ô`
are principal. -/
theorem exists_range_mulVecLin_eq_genIndex_det
    {N : Submodule (integralAdeles (𝓞 E) E) (Fin r → integralAdeles (𝓞 E) E)}
    (hN : N.cardQuot ≠ 0) :
    ∃ A : Matrix (Fin r) (Fin r) (integralAdeles (𝓞 E) E), LinearMap.range A.mulVecLin = N ∧
      IsUnit (A.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E])).det ∧
      genIndex E (A.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E])).det = N.cardQuot := by
  obtain ⟨A, hA_tri, hA_range, hA_index⟩ :=
    Submodule.exists_isLowerTriangular_range_mulVecLin_eq
      (fun I hI ↦ isPrincipal_of_cardQuot_ne_zero hI) _ hN
  have h_entry (i : Fin r) : (Ideal.span {A i i}).cardQuot ≠ 0 :=
    Finset.prod_ne_zero_iff.1 (hA_index ▸ hN) i (Finset.mem_univ i)
  have h_det : (A.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E])).det =
      ∏ i, algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E] (A i i) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_of_isLowerTriangular _ hA_tri, map_prod]
  refine ⟨A, hA_range, ?_, ?_⟩
  · rw [h_det]
    exact IsUnit.prod_univ_iff.2 fun i ↦ isUnit_coe_of_cardQuot_span_singleton_ne_zero (h_entry i)
  · rw [h_det, map_prod, hA_index, Nat.cast_prod]
    exact Finset.prod_congr rfl fun i _ ↦
      genIndex_eq_cardQuot (isUnit_coe_of_cardQuot_span_singleton_ne_zero (h_entry i))

/-- The image `C Ô^r` of a square matrix over `Ô` with determinant a unit of `𝔸_f` has finite
index in `Ô^r`: it contains `(det C) Ô^r`. -/
private theorem cardQuot_range_mulVecLin_ne_zero
    {C : Matrix (Fin r) (Fin r) (integralAdeles (𝓞 E) E)}
    (hC : IsUnit (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E] C.det)) :
    (LinearMap.range C.mulVecLin).cardQuot ≠ 0 := by
  set I := Ideal.span {C.det}
  have hI : Nat.card (integralAdeles (𝓞 E) E ⧸ I) ≠ 0 := by
    have h0 : genIndex E (C.det : 𝔸ᶠ[E]) ≠ 0 := by simpa using (genIndex_units_pos hC.unit).ne'
    rw [genIndex_eq_cardQuot hC] at h0
    rw [← Submodule.cardQuot_apply]
    exact_mod_cast h0
  -- `(det C) Ô^r ≤ C Ô^r` by Cramer's rule.
  have hle : ∀ x ∈ Ideal.pi fun _ : Fin r ↦ I, x ∈ LinearMap.range C.mulVecLin := by
    intro x hx
    choose y hy using fun i ↦ Ideal.mem_span_singleton'.1 (hx i)
    refine ⟨C.cramer y, funext fun i ↦ ?_⟩
    rw [mulVecLin_apply, mulVec_cramer, Pi.smul_apply, smul_eq_mul, mul_comm, hy]
  have hpi : (Ideal.pi fun _ : Fin r ↦ I).cardQuot ≠ 0 := by
    rw [Submodule.cardQuot_apply, Nat.card_congr (Ideal.piQuotEquiv (Fin r) I).toEquiv,
      Nat.card_pi]
    exact Finset.prod_ne_zero_iff.2 fun _ _ ↦ hI
  exact ne_zero_of_dvd_ne_zero hpi
    (AddSubgroup.index_dvd_of_le (K := (LinearMap.range C.mulVecLin).toAddSubgroup) hle)

/-- **The index of the image of a square matrix over `Ô`.** For a square matrix `C` over the
integral finite adeles `Ô`, the index of the image `C Ô^r` in `Ô^r` is the generalised index of
`det C`; both sides are `0` when `det C` is not a unit of the finite adeles. -/
theorem cardQuot_range_mulVecLin_eq_genIndex_det
    {C : Matrix (Fin r) (Fin r) (integralAdeles (𝓞 E) E)} :
    ((LinearMap.range C.mulVecLin).cardQuot : ℚ) =
      genIndex E (C.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E])).det := by
  set ι := algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E]
  have hι : Function.Injective ι := Subtype.val_injective
  have hdet : (C.map ι).det = ι C.det := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  by_cases h0 : (LinearMap.range C.mulVecLin).cardQuot = 0
  · -- infinite index: a unit determinant would make the index finite
    rw [h0, Nat.cast_zero, eq_comm, genIndex_eq_zero_iff]
    exact fun hC ↦ cardQuot_range_mulVecLin_ne_zero (hdet ▸ hC) h0
  obtain ⟨A, hA_range, hA_unit, hA_index⟩ := exists_range_mulVecLin_eq_genIndex_det h0
  -- `A = C V` and `C = A U`; `det C` is a unit as `det A` is, so `V U = 1`.
  obtain ⟨U, hU⟩ := exists_mul_eq_of_range_le fun j ↦ hA_range ▸ col_mem_range_mulVecLin C j
  obtain ⟨V, hV⟩ := exists_mul_eq_of_range_le fun j ↦ hA_range.symm ▸ col_mem_range_mulVecLin A j
  have hC : IsUnit (C.map ι).det :=
    isUnit_of_mul_isUnit_left (by rwa [← det_mul, ← Matrix.map_mul, hV])
  have hVU : V * U = 1 := by
    refine Matrix.map_injective hι ?_
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]
    refine ((Matrix.isUnit_iff_isUnit_det _).2 hC).mul_left_cancel ?_
    rw [Matrix.mul_one, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, hV, hU]
  rw [← hA_index, ← hV, Matrix.map_mul, det_mul, map_mul, genIndex_det_map_eq_one hVU, mul_one]

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
  obtain ⟨A, hA_range, hA_unit, hA_index⟩ :=
    exists_range_mulVecLin_eq_genIndex_det (h_comap.trans_ne h_index)
  refine ⟨A.map (algebraMap (integralAdeles (𝓞 E) E) 𝔸ᶠ[E]), hA_unit, ?_, by rw [hA_index, h_comap]⟩
  rw [← map_colMap_span_col, hA_range, Submodule.map_comap_eq_self (range_colMap B ▸ hM)]

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

end NumberField.FiniteAdeleRing
