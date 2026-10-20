/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Hyperbolic
public import TauCeti.NumberTheory.IntegralLattice.EvenUnimodularGenus
import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Two
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.D8Plus.Isometry

/-!
# Cancellation fails over `ℤ`

The two even unimodular positive definite lattices `E₈ ⊕ E₈` and `D₁₆⁺` of rank sixteen are not
isometric, but they become isometric after adding a hyperbolic plane:

```text
E₈ ⊕ E₈ ⊕ U ≅ D₁₆⁺ ⊕ U.
```

So `L ⊕ N ≅ M ⊕ N` does not imply `L ≅ M` for integral lattices, in contrast with Witt
cancellation over a field.

The proof is explicit. Split the coordinates of `ℚ¹⁶` into two blocks of eight, and let `v` be
the vector with entries `1` on the first block and `0` on the second. It lies in `D₁₆⁺`, has norm
`8`, and pairs oddly with `e₁ + e₉`, so its two-neighbor `M` is defined and is an even neighbor of
`D₁₆⁺`. Placing the eight `E₈` glue roots `TauCeti.IntegralLattice.e8GlueRoot` of `D₈⁺` in each
block gives sixteen vectors of `M` with Gram matrix that of `E₈ ⊕ E₈`; since `E₈ ⊕ E₈` is
unimodular and `M` is integral they span `M`, so `M ≅ E₈ ⊕ E₈`. The general theorem
`TauCeti.IntegralLattice.nonempty_isometry_orthogonalSum_hyperbolicPlane_neighbor` then gives
`D₁₆⁺ ⊕ U ≅ M ⊕ U`.

## Main results

* `TauCeti.IntegralLattice.nonempty_isometry_orthogonalSum_hyperbolicPlane_e8PowLattice`:
  `E₈ ⊕ E₈ ⊕ U ≅ D₁₆⁺ ⊕ U`.
* `TauCeti.IntegralLattice.not_forall_nonempty_isometry_of_orthogonalSum`: cancellation of an
  orthogonal summand fails for integral lattices.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II.
* J.-P. Serre, *A Course in Arithmetic*, Chapter V.
-/

public section

namespace TauCeti.IntegralLattice

open Module

/-- The vector of `ℚ¹⁶` with `g` on the block `a` and zero on the other block. -/
private def blockVector (a : Fin 2) (g : Fin 8 → ℚ) : Fin (8 * 2) → ℚ :=
  fun j ↦ if (e8PowIndexEquiv 2 j).1 = a then g (e8PowIndexEquiv 2 j).2 else 0

private theorem blockVector_apply_symm (a b : Fin 2) (g : Fin 8 → ℚ) (i : Fin 8) :
    blockVector a g ((e8PowIndexEquiv 2).symm (b, i)) = if b = a then g i else 0 := by
  simp [blockVector]

/-- A sum over `Fin 16` is the sum over the two blocks. -/
private theorem sum_eq_sum_blocks (f : Fin (8 * 2) → ℚ) :
    ∑ j, f j = ∑ i, f ((e8PowIndexEquiv 2).symm (0, i)) +
      ∑ i, f ((e8PowIndexEquiv 2).symm (1, i)) := by
  rw [← (e8PowIndexEquiv 2).symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- A vector all of whose coordinates are integers. -/
private theorem forall_exists_intCast_of_blocks {x : Fin (8 * 2) → ℚ}
    (h : ∀ b i, ∃ z : ℤ, x ((e8PowIndexEquiv 2).symm (b, i)) = z) :
    ∀ j, ∃ z : ℤ, x j = z := by
  intro j
  rw [← (e8PowIndexEquiv 2).symm_apply_apply j]
  exact h _ _

/-- A vector with integral coordinates and even coordinate sum lies in `D₁₆⁺`. -/
private theorem mem_checkerboardPlusLattice_of {x : Fin (8 * 2) → ℚ}
    (h : ∀ b i, ∃ z : ℤ, x ((e8PowIndexEquiv 2).symm (b, i)) = z) (m : ℤ)
    (hm : ∑ j, x j = 2 * m) :
    x ∈ (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).carrier := by
  rw [checkerboardPlusLattice_carrier, mem_checkerboardPlusCarrier_iff _ (by decide)]
  exact Or.inl ((mem_checkerboardLattice_carrier_iff x).mpr
    ⟨forall_exists_intCast_of_blocks h, m, hm⟩)

/-- The neighbor vector: `1` on the first block and `0` on the second. -/
private noncomputable def neighborVector : checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2) :=
  ⟨blockVector 0 1, mem_checkerboardPlusLattice_of
    (fun b i ↦ ⟨if b = 0 then 1 else 0, by rw [blockVector_apply_symm]; split_ifs <;> simp⟩) 4
    (by simp only [sum_eq_sum_blocks, blockVector_apply_symm]; simp; norm_num)⟩

private theorem coe_neighborVector : (neighborVector : Fin (8 * 2) → ℚ) = blockVector 0 1 :=
  (rfl)

/-- Pairing with the neighbor vector is the sum of the coordinates on the first block. -/
private theorem form_neighborVector (x : Fin (8 * 2) → ℚ) :
    (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).form neighborVector x =
      ∑ i, x ((e8PowIndexEquiv 2).symm (0, i)) := by
  rw [checkerboardPlusLattice_form, checkerboardLattice_form_apply, sum_eq_sum_blocks]
  simp only [coe_neighborVector, blockVector_apply_symm]
  simp

private theorem integralNorm_neighborVector :
    (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).integralNorm neighborVector = 8 := by
  have h := form_neighborVector (neighborVector : Fin (8 * 2) → ℚ)
  rw [← integralForm_cast, ← integralNorm_apply] at h
  have h' : ((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).integralNorm neighborVector :
      ℚ) = 8 := by
    simp only [h, coe_neighborVector, blockVector_apply_symm]
    simp
  exact_mod_cast h'

private theorem two_sq_dvd_integralNorm_neighborVector :
    (2 : ℤ) ^ 2 ∣ (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).integralNorm
      neighborVector := by
  rw [integralNorm_neighborVector]
  norm_num

/-- The neighbor `M` of `D₁₆⁺` along `neighborVector`, which will turn out to be `E₈ ⊕ E₈`. -/
private noncomputable abbrev neighborLattice : IntegralLattice (Fin (8 * 2) → ℚ) :=
  (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).neighbor 2 neighborVector
    two_sq_dvd_integralNorm_neighborVector

/-- A vector of `D₁₆⁺` whose first-block coordinate sum is even lies in the neighbor kernel. -/
private theorem mem_neighborKernel_of {x : Fin (8 * 2) → ℚ}
    (hx : x ∈ (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).carrier) (m : ℤ)
    (hm : ∑ i, x ((e8PowIndexEquiv 2).symm (0, i)) = 2 * m) :
    x ∈ (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).neighborKernel 2 neighborVector := by
  rw [mem_neighborKernel_iff]
  refine ⟨⟨x, hx⟩, rfl, m, ?_⟩
  have h : (((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).integralForm neighborVector
      ⟨x, hx⟩ : ℤ) : ℚ) = 2 * m := by
    rw [integralForm_cast, form_neighborVector, hm]
  exact_mod_cast h

/-- A vector which differs from the spinor vector by an integral vector of even coordinate sum
lies in `D₁₆⁺`. -/
private theorem mem_checkerboardPlusLattice_of_sub {x : Fin (8 * 2) → ℚ}
    (h : ∀ b i, ∃ z : ℤ, x ((e8PowIndexEquiv 2).symm (b, i)) - 1 / 2 = z) (m : ℤ)
    (hm : ∑ j, (x j - 1 / 2) = 2 * m) :
    x ∈ (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).carrier := by
  rw [checkerboardPlusLattice_carrier, mem_checkerboardPlusCarrier_iff _ (by decide)]
  refine Or.inr ((mem_checkerboardLattice_carrier_iff _).mpr
    ⟨forall_exists_intCast_of_blocks fun b i ↦ ?_, m, ?_⟩)
  · simpa only [Pi.sub_apply, checkerboardSpinor_apply] using h b i
  · simpa only [Pi.sub_apply, checkerboardSpinor_apply] using hm

/-- A vector of `D₁₆⁺` with even first-block coordinate sum lies in the neighbor. -/
private theorem mem_neighborLattice_of {x : Fin (8 * 2) → ℚ}
    (hx : x ∈ (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).carrier) (m : ℤ)
    (hm : ∑ i, x ((e8PowIndexEquiv 2).symm (0, i)) = 2 * m) : x ∈ neighborLattice.carrier :=
  (mem_neighbor_two_carrier_iff_mem_or_sub_mem _ _ x).mpr (Or.inl (mem_neighborKernel_of hx m hm))

/-- A vector whose difference with half the neighbor vector lies in `D₁₆⁺` with even first-block
coordinate sum lies in the neighbor. -/
private theorem mem_neighborLattice_of_sub {x : Fin (8 * 2) → ℚ}
    (hx : x - blockVector 0 (fun _ ↦ 1 / 2) ∈
      (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).carrier) (m : ℤ)
    (hm : ∑ i, (x - blockVector 0 (fun _ ↦ 1 / 2)) ((e8PowIndexEquiv 2).symm (0, i)) = 2 * m) :
    x ∈ neighborLattice.carrier := by
  have h : x - (2 : ℚ)⁻¹ • (neighborVector : Fin (8 * 2) → ℚ) =
      x - blockVector 0 (fun _ ↦ 1 / 2) := by
    funext j
    simp only [coe_neighborVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, blockVector]
    split_ifs <;> simp
  refine (mem_neighbor_two_carrier_iff_mem_or_sub_mem _ _ x).mpr (Or.inr ?_)
  rw [h]
  exact mem_neighborKernel_of hx m hm

/-- The `E₈` glue roots placed in either block lie in the neighbor. -/
private theorem blockVector_e8GlueRoot_mem (a : Fin 2) (i : Fin 8) :
    blockVector a (e8GlueRoot i) ∈ neighborLattice.carrier := by
  have hg := e8GlueRoot_mem_d8PlusCarrier i
  rw [mem_checkerboardPlusCarrier_iff _ (by decide), mem_checkerboardLattice_carrier_iff,
    mem_checkerboardLattice_carrier_iff] at hg
  simp only [Pi.sub_apply, checkerboardSpinor_apply] at hg
  obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  all_goals rcases hg with ⟨hz, m, hm⟩ | ⟨hz, m, hm⟩
  · refine mem_neighborLattice_of (mem_checkerboardPlusLattice_of (fun b j ↦ ?_) m ?_) m ?_
    · rw [blockVector_apply_symm]
      split_ifs
      exacts [(hz j).imp fun _ h ↦ h, ⟨0, by simp⟩]
    · simp only [sum_eq_sum_blocks, blockVector_apply_symm]
      simpa using hm
    · simp only [blockVector_apply_symm]
      simpa using hm
  · refine mem_neighborLattice_of_sub (mem_checkerboardPlusLattice_of (fun b j ↦ ?_) m ?_) m ?_
    · simp only [Pi.sub_apply, blockVector_apply_symm]
      split_ifs
      exacts [(hz j).imp fun _ h ↦ h, ⟨0, by simp⟩]
    · simp only [sum_eq_sum_blocks, Pi.sub_apply, blockVector_apply_symm]
      simpa using hm
    · simp only [Pi.sub_apply, blockVector_apply_symm]
      simpa using hm
  · refine mem_neighborLattice_of (mem_checkerboardPlusLattice_of (fun b j ↦ ?_) m ?_) 0 ?_
    · rw [blockVector_apply_symm]
      split_ifs
      exacts [(hz j).imp fun _ h ↦ h, ⟨0, by simp⟩]
    · simp only [sum_eq_sum_blocks, blockVector_apply_symm]
      simpa using hm
    · simp only [blockVector_apply_symm]
      simp
  · refine mem_neighborLattice_of_sub
      (mem_checkerboardPlusLattice_of_sub (fun b j ↦ ?_) (m - 4) ?_) (-2) ?_
    · simp only [Pi.sub_apply, blockVector_apply_symm]
      fin_cases b
      · exact ⟨-1, by norm_num⟩
      · simpa using hz j
    · simp only [sum_eq_sum_blocks, Pi.sub_apply, blockVector_apply_symm]
      simp only [Finset.sum_sub_distrib] at hm
      simp [-e8GlueRoot_apply, Finset.sum_sub_distrib]
      linear_combination hm
    · simp only [Pi.sub_apply, blockVector_apply_symm]
      simp
      norm_num

/-- The image of the `k`-th standard basis vector of `E₈ ⊕ E₈`: the corresponding glue root of
`D₈⁺`, placed in its block. -/
private def glueVector (k : Fin (8 * 2)) : Fin (8 * 2) → ℚ :=
  blockVector (e8PowIndexEquiv 2 k).1 (e8GlueRoot (e8PowIndexEquiv 2 k).2)

/-- The glue vectors have the Gram matrix of `E₈ ⊕ E₈`. -/
private theorem form_glueVector (k l : Fin (8 * 2)) :
    neighborLattice.form (glueVector k) (glueVector l) =
      (e8PowLattice 2).form (Pi.basisFun ℚ _ k) (Pi.basisFun ℚ _ l) := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (e8PowIndexEquiv 2).symm.surjective k
  obtain ⟨⟨b, j⟩, rfl⟩ := (e8PowIndexEquiv 2).symm.surjective l
  have key := form_e8GlueRoot_e8GlueRoot i j
  rw [checkerboardLattice_form_apply] at key
  rw [Pi.basisFun_apply, Pi.basisFun_apply, form_e8PowLattice_basisFun]
  simp only [glueVector, Equiv.apply_symm_apply, neighbor_form, checkerboardPlusLattice_form,
    checkerboardLattice_form_apply, sum_eq_sum_blocks, blockVector_apply_symm]
  fin_cases a <;> fin_cases b <;> simp [key, -e8GlueRoot_apply]

/-- The rational linear map sending the standard basis of `E₈ ⊕ E₈` to the glue vectors. -/
private noncomputable def glueMap : (Fin (8 * 2) → ℚ) →ₗ[ℚ] (Fin (8 * 2) → ℚ) :=
  (Pi.basisFun ℚ (Fin (8 * 2))).constr ℚ glueVector

private theorem glueMap_basisFun (k : Fin (8 * 2)) :
    glueMap (Pi.basisFun ℚ _ k) = glueVector k :=
  (Pi.basisFun ℚ (Fin (8 * 2))).constr_basis ℚ glueVector k

private theorem form_glueMap (x y : Fin (8 * 2) → ℚ) :
    neighborLattice.form (glueMap x) (glueMap y) = (e8PowLattice 2).form x y := by
  have h : neighborLattice.form.comp glueMap glueMap = (e8PowLattice 2).form :=
    LinearMap.BilinForm.ext_basis (Pi.basisFun ℚ (Fin (8 * 2))) fun k l ↦ by
      rw [LinearMap.BilinForm.comp_apply, glueMap_basisFun, glueMap_basisFun, form_glueVector]
  rw [← h, LinearMap.BilinForm.comp_apply]

private theorem glueMap_injective : Function.Injective glueMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine (isUnimodular_e8PowLattice 2).nondegenerate.1 x fun y ↦ ?_
  rw [← form_glueMap x y, hx, map_zero, LinearMap.zero_apply]

/-- The glue map as a rational linear equivalence. -/
private noncomputable def glueEquiv : (Fin (8 * 2) → ℚ) ≃ₗ[ℚ] (Fin (8 * 2) → ℚ) :=
  LinearEquiv.ofBijective glueMap
    ⟨glueMap_injective, LinearMap.injective_iff_surjective.mp glueMap_injective⟩

private theorem glueEquiv_apply (x : Fin (8 * 2) → ℚ) : glueEquiv x = glueMap x :=
  LinearEquiv.ofBijective_apply _ _

/-- The glue map carries the carrier of `E₈ ⊕ E₈` onto the integral span of the glue vectors. -/
private theorem map_carrier_glueEquiv :
    (e8PowLattice 2).carrier.map (glueEquiv.restrictScalars ℤ).toLinearMap =
      Submodule.span ℤ (Set.range glueVector) := by
  have hrange : ⇑(glueEquiv.restrictScalars ℤ).toLinearMap ∘ ⇑(Pi.basisFun ℚ (Fin (8 * 2))) =
      glueVector := by
    funext k
    exact (glueEquiv_apply _).trans (glueMap_basisFun k)
  rw [e8PowLattice_carrier, Submodule.map_span, ← Set.range_comp, hrange]

private theorem span_range_glueVector_le :
    Submodule.span ℤ (Set.range glueVector) ≤ neighborLattice.carrier := by
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact blockVector_e8GlueRoot_mem _ _

/-- **The glue vectors span the neighbor.** A vector of the neighbor has a rational preimage which
pairs integrally with the carrier of `E₈ ⊕ E₈`, because the neighbor is integral; so it lies in
the dual of `E₈ ⊕ E₈`, which is `E₈ ⊕ E₈` itself. -/
private theorem span_range_glueVector :
    Submodule.span ℤ (Set.range glueVector) = neighborLattice.carrier := by
  refine le_antisymm span_range_glueVector_le fun x hx ↦ ?_
  have hxu : glueMap (glueEquiv.symm x) = x := by
    rw [← glueEquiv_apply]
    exact glueEquiv.apply_symm_apply x
  have hdual : glueEquiv.symm x ∈ (e8PowLattice 2).dualCarrier := by
    intro y hy
    have hy' : glueMap y ∈ neighborLattice.carrier := by
      refine span_range_glueVector_le ?_
      rw [← map_carrier_glueEquiv]
      exact ⟨y, hy, glueEquiv_apply y⟩
    have hpair := neighborLattice.le_dual hx (glueMap y) hy'
    rwa [← form_glueMap _ y, hxu]
  rw [← (isUnimodular_def _).mp (isUnimodular_e8PowLattice 2)] at hdual
  rw [← map_carrier_glueEquiv]
  exact ⟨glueEquiv.symm x, hdual, (glueEquiv_apply _).trans hxu⟩

/-- `E₈ ⊕ E₈` is isometric to the two-neighbor of `D₁₆⁺` along `neighborVector`. -/
private noncomputable def e8PowLatticeIsometryNeighborLattice :
    Isometry (e8PowLattice 2) neighborLattice where
  toIsometryEquiv :=
    { toLinearEquiv := glueEquiv
      map_app' := form_glueMap }
  map_carrier := by
    rw [map_carrier_glueEquiv, span_range_glueVector]

/-- **`E₈ ⊕ E₈ ⊕ U ≅ D₁₆⁺ ⊕ U`.** Adding the hyperbolic plane `U` makes the two non-isometric even
unimodular lattices of rank sixteen isometric. -/
theorem nonempty_isometry_orthogonalSum_hyperbolicPlane_e8PowLattice :
    Nonempty (Isometry ((e8PowLattice 2).orthogonalSum hyperbolicPlane)
      ((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).orthogonalSum hyperbolicPlane)) := by
  have hv₂ : 2 * (2 : ℤ) ^ 2 ∣
      (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).integralNorm neighborVector := by
    rw [integralNorm_neighborVector]
    norm_num
  -- The vector `e₁ + e₉` of `D₁₆⁺`, pairing to `1` with the neighbor vector.
  let w : Fin (8 * 2) → ℚ := fun j ↦ if (e8PowIndexEquiv 2 j).2 = 0 then 1 else 0
  have hw' (b : Fin 2) (i : Fin 8) :
      w ((e8PowIndexEquiv 2).symm (b, i)) = if i = 0 then 1 else 0 := by
    simp only [w, Equiv.apply_symm_apply]
  have hw : w ∈ (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).carrier := by
    refine mem_checkerboardPlusLattice_of
      (fun b i ↦ ⟨if i = 0 then 1 else 0, by rw [hw']; split_ifs <;> simp⟩) 1 ?_
    simp only [sum_eq_sum_blocks, hw']
    simp
    norm_num
  have hvw : (checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).integralForm neighborVector
      ⟨w, hw⟩ = 1 := by
    have h : (((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).integralForm neighborVector
        ⟨w, hw⟩ : ℤ) : ℚ) = 1 := by
      rw [integralForm_cast, form_neighborVector]
      simp only [hw']
      simp
    exact_mod_cast h
  obtain ⟨e⟩ := nonempty_isometry_orthogonalSum_hyperbolicPlane_neighbor
    two_sq_dvd_integralNorm_neighborVector (isEven_checkerboardPlusLattice _ _) hv₂
    (w := ⟨w, hw⟩) (by rw [hvw]; exact isCoprime_one_left)
  exact ⟨(e8PowLatticeIsometryNeighborLattice.orthogonalSum (Isometry.refl _)).trans e.symm⟩

/-- **Cancellation fails over `ℤ`.** There are integral lattices `L`, `M` and `N` with
`L ⊕ N ≅ M ⊕ N` but `L ≇ M`: take `L = E₈ ⊕ E₈`, `M = D₁₆⁺` and `N = U`. -/
theorem not_forall_nonempty_isometry_of_orthogonalSum :
    ¬ ∀ (L M : IntegralLattice (Fin (8 * 2) → ℚ)) (N : IntegralLattice (Fin 2 → ℚ)),
      Nonempty (Isometry (L.orthogonalSum N) (M.orthogonalSum N)) → Nonempty (Isometry L M) :=
  fun h ↦ (isEmpty_isometry_e8PowLattice_checkerboardPlusLattice le_rfl).false
    (h _ _ _ nonempty_isometry_orthogonalSum_hyperbolicPlane_e8PowLattice).some

end TauCeti.IntegralLattice
