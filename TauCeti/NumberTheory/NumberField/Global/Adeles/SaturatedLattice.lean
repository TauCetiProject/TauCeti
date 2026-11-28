/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Lattice
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Saturated lattices of subspaces in the finite adeles

Let `E` be a number field, `𝔸_f` its finite adeles, `Ô` the integral ones and `κ` a finite set.
For a subspace `U ⊂ E^κ` and an adelic matrix `H`, the *saturated lattice* of `U` for `H` is the
`Ô`-module of the points `u` of `U ⊗ 𝔸_f` (the `𝔸_f`-span of `U` in `𝔸_f^κ`) with `H u` integral
(`NumberField.FiniteAdeleRing.saturatedLattice`). If `H` has a left inverse, it is a lattice of
rank `dim U` in the sense of `NumberField.FiniteAdeleRing.IsLatticeOfRank`.

The proof: write `U ⊗ 𝔸_f` as the column space of the matrix `X` of a basis of `U`. If `K` is a
left inverse of `H X` and `β ∈ 𝓞_E` clears the denominators of `K`, every point `X c` of the
saturated lattice has `β c` integral, so the saturated lattice lies in the lattice spanned by the
columns of `β⁻¹ X`. If `b ∈ 𝓞_E` clears the denominators of `H β⁻¹ X`, it contains `b` times that
lattice, which has finite index (`NumberField.FiniteAdeleRing.IsLatticeOfRank.of_le`).

The discriminant of a saturated lattice, for a CM field, is in
`TauCeti.NumberTheory.NumberField.CMField.SaturatedLattice`. Not to be confused with the saturated
lattices over a nonarchimedean field in `TauCeti.Analysis.Normed.Field.SaturatedLattice`.

## Main declarations

* `NumberField.FiniteAdeleRing.saturatedLattice`: the saturated lattice of `U` for `H`.
* `NumberField.FiniteAdeleRing.mem_saturatedLattice`: its membership criterion.
* `NumberField.FiniteAdeleRing.saturatedLattice_mono`: it is monotone in `U`.
* `NumberField.FiniteAdeleRing.isLatticeOfRank_saturatedLattice`: it is a lattice of rank
  `dim U` when `H` has a left inverse.

## References

* The formal proof that the roadmap credits for this statement: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (`New.Filling.isLatticeOfRank_saturatedLattice` in
  `New/Spanning/RemainingTerms/Discriminants.lean`).
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField
open Matrix
open scoped NumberField.AdeleRing

namespace NumberField.FiniteAdeleRing

variable {E : Type*} [Field E] [NumberField E]

variable {κ ι : Type*} [Fintype κ]

/-- The **saturated lattice** of a subspace `U ⊂ E^κ` for an adelic matrix `H`: the `Ô`-module of
the points `u` of `U ⊗ 𝔸_f`, the `𝔸_f`-span of `U` in `𝔸_f^κ`, with `H u` integral. -/
def saturatedLattice (U : Submodule E (κ → E)) (H : Matrix ι κ 𝔸ᶠ[E]) :
    Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E]) where
  carrier := {u | u ∈ Submodule.span 𝔸ᶠ[E] ((fun (v : κ → E) k ↦ algebraMap E 𝔸ᶠ[E] (v k)) '' U) ∧
    ∀ i, (H *ᵥ u) i ∈ integralAdeles (𝓞 E) E}
  add_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    refine ⟨Submodule.add_mem _ hu.1 hv.1, fun i ↦ ?_⟩
    rw [mulVec_add, Pi.add_apply]
    exact add_mem (hu.2 i) (hv.2 i)
  zero_mem' := by simp
  smul_mem' c u hu := by
    simp only [Set.mem_ofPred_eq] at hu ⊢
    refine ⟨Submodule.smul_of_tower_mem _ c hu.1, fun i ↦ ?_⟩
    rw [mulVec_smul, Pi.smul_apply]
    exact mul_mem c.property (hu.2 i)

/-- A vector lies in the saturated lattice of `U` for `H` if and only if it lies in `U ⊗ 𝔸_f` and
`H u` is integral. -/
@[simp]
theorem mem_saturatedLattice {U : Submodule E (κ → E)} {H : Matrix ι κ 𝔸ᶠ[E]} {u : κ → 𝔸ᶠ[E]} :
    u ∈ saturatedLattice U H ↔
      u ∈ Submodule.span 𝔸ᶠ[E] ((fun (v : κ → E) k ↦ algebraMap E 𝔸ᶠ[E] (v k)) '' U) ∧
        ∀ i, (H *ᵥ u) i ∈ integralAdeles (𝓞 E) E :=
  Iff.rfl

/-- The saturated lattice is monotone in the subspace. -/
theorem saturatedLattice_mono {U V : Submodule E (κ → E)} (hUV : U ≤ V) (H : Matrix ι κ 𝔸ᶠ[E]) :
    saturatedLattice U H ≤ saturatedLattice V H :=
  fun _ hu ↦ ⟨Submodule.span_mono (Set.image_mono hUV) hu.1, hu.2⟩

/-- Let `K` be a left inverse of `H X`, and let `β` clear the denominators of `K`. If `H X c` is
integral, then `X c` lies in the `Ô`-span of the columns of `β⁻¹ X`. -/
private theorem mulVec_mem_span_col {r : ℕ} [Fintype ι] {X : Matrix κ (Fin r) 𝔸ᶠ[E]}
    {H : Matrix ι κ 𝔸ᶠ[E]} {K : Matrix (Fin r) ι 𝔸ᶠ[E]} (hK : K * (H * X) = 1)
    {β β' : 𝔸ᶠ[E]} (hβ' : β' * β = 1) (hβ : ∀ j i, K j i * β ∈ integralAdeles (𝓞 E) E)
    {c : Fin r → 𝔸ᶠ[E]} (hc : ∀ i, (H *ᵥ (X *ᵥ c)) i ∈ integralAdeles (𝓞 E) E) :
    X *ᵥ c ∈ Submodule.span (integralAdeles (𝓞 E) E) (Set.range (β' • X).col) := by
  have hc' : K *ᵥ (H *ᵥ (X *ᵥ c)) = c := by
    simp only [mulVec_mulVec, hK, one_mulVec]
  have hd (j : Fin r) : c j * β ∈ integralAdeles (𝓞 E) E := by
    rw [← hc', mulVec, dotProduct, Finset.sum_mul]
    exact sum_mem fun i _ ↦ by
      rw [mul_right_comm]
      exact mul_mem (hβ j i) (hc i)
  rw [← Fintype.range_linearCombination]
  refine ⟨fun j ↦ ⟨_, hd j⟩, ?_⟩
  rw [linearCombination_col_eq_mulVec]
  funext k
  simp only [mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Subalgebra.algebraMap_apply]
  exact Finset.sum_congr rfl fun j _ ↦ by linear_combination X k j * c j * hβ'

omit [Fintype κ] in
/-- If `S` contains `B (b e)` for every integral vector `e`, where `b ≠ 0` is an integer of `E`,
then `S` has finite index in the `Ô`-span of the columns of `B`. -/
private theorem relIndex_span_col_ne_zero {r : ℕ} {B : Matrix κ (Fin r) 𝔸ᶠ[E]}
    {S : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])} {b : 𝓞 E} (hb : b ≠ 0)
    (hS : ∀ e : Fin r → integralAdeles (𝓞 E) E,
      (B *ᵥ fun j ↦ (e j : 𝔸ᶠ[E]) * algebraMap (𝓞 E) 𝔸ᶠ[E] b) ∈ S) :
    S.toAddSubgroup.relIndex
      (Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col)).toAddSubgroup ≠ 0 := by
  rw [← Fintype.range_linearCombination]
  let φ := Fintype.linearCombination (integralAdeles (𝓞 E) E) B.col
  refine ne_of_eq_of_ne (S.toAddSubgroup.index_comap φ.toAddMonoidHom).symm ?_
  let β : integralAdeles (𝓞 E) E := algebraMap (𝓞 E) _ b
  -- The coordinates of `S` contain `b Ô^r`, which has finite index.
  have hP : AddSubgroup.pi Set.univ (fun _ : Fin r ↦ (Ideal.span {β}).toAddSubgroup) ≤
      S.toAddSubgroup.comap φ.toAddMonoidHom := by
    intro d hd
    choose e he using fun j ↦ Ideal.mem_span_singleton'.1 (hd j (Set.mem_univ j))
    rw [AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe]
    -- `d = b e`, so its image is `B (b e)`.
    rw [linearCombination_col_eq_mulVec, ← funext he]
    exact hS e
  refine ne_zero_of_dvd_ne_zero ?_ (AddSubgroup.index_dvd_of_le hP)
  rw [AddSubgroup.index_pi]
  refine Finset.prod_ne_zero_iff.2 fun _ _ ↦ ?_
  have hunit : IsUnit (β : 𝔸ᶠ[E]) := by
    -- `β` is `b`, read in `Ô`.
    change IsUnit (algebraMap (𝓞 E) 𝔸ᶠ[E] b)
    rw [IsScalarTower.algebraMap_apply (𝓞 E) E 𝔸ᶠ[E]]
    exact (show (b : E) ≠ 0 by simpa using hb).isUnit.map _
  exact cardQuot_span_singleton_ne_zero hunit

/-- The `Ô`-module of the vectors `u = X c` in the column space of `X`, the matrix `x` over `E`
with independent columns read over `𝔸_f`, such that `H u` is integral, is a lattice of rank `r` if
`H` has a left inverse. -/
private theorem isLatticeOfRank_of_forall_mem_iff [Fintype ι] [DecidableEq κ] {r : ℕ}
    {x : Matrix κ (Fin r) E} (hx : LinearIndependent E x.col) {H : Matrix ι κ 𝔸ᶠ[E]}
    (hH : ∃ H' : Matrix κ ι 𝔸ᶠ[E], H' * H = 1)
    {S : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hS : ∀ u, u ∈ S ↔ (∃ c, x.map (algebraMap E 𝔸ᶠ[E]) *ᵥ c = u) ∧
      ∀ i, (H *ᵥ u) i ∈ integralAdeles (𝓞 E) E) :
    IsLatticeOfRank r S := by
  classical
  obtain ⟨H', hH'⟩ := hH
  obtain ⟨y, hy⟩ := exists_mul_eq_one_of_linearIndependent_col hx
  set X := x.map (algebraMap E 𝔸ᶠ[E])
  have hYX : y.map (algebraMap E 𝔸ᶠ[E]) * X = 1 := by
    rw [← Matrix.map_mul, hy]
    simp
  have hK : y.map (algebraMap E 𝔸ᶠ[E]) * H' * (H * X) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc H', hH', Matrix.one_mul, hYX]
  -- `b₂` clears the denominators of the left inverse `Y H'` of `H X`.
  obtain ⟨b₂, hb₂, hK'⟩ := exists_mem_nonZeroDivisors_forall_mul_mem_integralAdeles
    fun p : Fin r × ι ↦ (y.map (algebraMap E 𝔸ᶠ[E]) * H') p.1 p.2
  have hβ : (b₂ : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb₂
  have hββ : algebraMap E 𝔸ᶠ[E] (b₂ : E)⁻¹ * algebraMap (𝓞 E) 𝔸ᶠ[E] b₂ = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 E) E 𝔸ᶠ[E], ← map_mul]
    simp [hβ]
  have hX' : ((b₂ : E)⁻¹ • x).map (algebraMap E 𝔸ᶠ[E]) = algebraMap E 𝔸ᶠ[E] (b₂ : E)⁻¹ • X := by
    ext k j
    simp [X]
  -- `b₁` clears the denominators of `H X'`, for `X' = b₂⁻¹ X`.
  obtain ⟨b₁, hb₁, hG⟩ := exists_mem_nonZeroDivisors_forall_mul_mem_integralAdeles
    fun p : ι × Fin r ↦ (H * (algebraMap E 𝔸ᶠ[E] (b₂ : E)⁻¹ • X)) p.1 p.2
  have hL := isLatticeOfRank_span_col (x := (b₂ : E)⁻¹ • x)
    (hx.units_smul fun _ ↦ Units.mk0 _ (inv_ne_zero hβ)) 1
  rw [Units.val_one, Matrix.mul_one, hX'] at hL
  refine hL.of_le (fun u hu ↦ ?_) (relIndex_span_col_ne_zero (nonZeroDivisors.ne_zero hb₁)
    fun e ↦ (hS _).2 ⟨?_, fun i ↦ ?_⟩)
  · obtain ⟨⟨c, rfl⟩, hint⟩ := (hS u).1 hu
    exact mulVec_mem_span_col hK hββ (fun j i ↦ hK' (j, i)) hint
  · exact ⟨_, by rw [smul_mulVec, ← mulVec_smul]⟩
  · rw [mulVec_mulVec, mulVec, dotProduct]
    exact sum_mem fun j _ ↦ by
      rw [← mul_assoc, mul_right_comm]
      exact mul_mem (hG (i, j)) (e j).property

/-- **Saturated lattices are lattices.** If `H` has a left inverse, the saturated lattice of a
subspace `U ⊂ E^κ` for `H` is a lattice of rank `dim U`. -/
theorem isLatticeOfRank_saturatedLattice [Fintype ι] [DecidableEq κ] {U : Submodule E (κ → E)}
    {H : Matrix ι κ 𝔸ᶠ[E]} (hH : ∃ H' : Matrix κ ι 𝔸ᶠ[E], H' * H = 1) :
    IsLatticeOfRank (Module.finrank E U) (saturatedLattice U H) := by
  let b := Module.finBasis E U
  refine isLatticeOfRank_of_forall_mem_iff (x := Matrix.of fun k j ↦ (b j : κ → E) k) ?_ hH
    fun u ↦ ?_
  · exact b.linearIndependent.map' U.subtype U.ker_subtype
  · rw [mem_saturatedLattice, span_image_algebraMap_eq_range_mulVecLin U b, LinearMap.mem_range]
    simp only [mulVecLin_apply]

end NumberField.FiniteAdeleRing
