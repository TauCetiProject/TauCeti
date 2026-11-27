/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.IsotropicSplitting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The two opposite Siegel parabolics generate the unitary group

Let `K` be a field with an involution and `A` a hermitian matrix on `n` with an isotropic
splitting `D` over the empty core (`TauCeti.IsotropicSplitting` with `n₀` empty): frames
`k, l : Matrix n p K` with `kᴴ A k = 0`, `lᴴ A l = 0`, `lᴴ A k = 1` and `|n| = 2 |p|`, so that
`K^n = l K^p ⊕ k K^p` is a complete polarization of the form. The **Siegel parabolic subgroups**
of the splitting are the stabilizers `D.parabolic` of the span of `k` and `D.swap.parabolic` of the
span of `l` in the unitary group `Matrix.unitaryGroupOf A`.

The main result, `TauCeti.IsotropicSplitting.parabolic_sup_swap_parabolic_eq_top`, is that these
two opposite parabolic subgroups generate the unitary group, provided the involution admits a
nonzero skew element `j` (`star j = -j`), as a purely imaginary element of a CM field does. Some
such element is needed: for the trivial involution on `ℚ` and `|p| = 1` the unitary group is the
split orthogonal group `O(1, 1)`, both Siegel parabolics are its diagonal torus, and they miss the
element exchanging `k` and `l`.

## Implementation notes

Write the image of the frame `k` under `g` as `g k = l β + k δ`, with `β = lCoord g k` and
`δ = kCoord g k`; the isotropy of `g k` reads `βᴴ δ + δᴴ β = 0`.

* If `δ` is invertible, `β δ⁻¹` is skew-hermitian and the shear along `l` by `-β δ⁻¹`, an element
  of the opposite parabolic, carries `g` into the parabolic of `k`. This is the big cell.
* Otherwise pick `w ≠ 0` with `δ w = 0`; then `β w ≠ 0`, say `(β w)ᵢ ≠ 0`. The product of
  shears `ω = s_l(j Eᵢ) s_k(-j⁻¹ Eᵢ) s_l(j Eᵢ)` (with `Eᵢ` the matrix unit at `(i, i)`) exchanges
  the `i`-th columns of `k` and `l` up to scalars, and replaces `δ` by a matrix whose kernel is
  strictly contained in the kernel of `δ`: the isotropy relation shows that it is contained, and
  `w` is not in it. Induction on the dimension of the kernel concludes.

This is the step of the mixed models of the Weil representation that reduces the invariance of a
theta functional under the rational points of a split unitary group to its invariance under the
two opposite Siegel parabolics.

## Provenance

The statement follows `New.Space.Splitting.siegelParabolic` and
`New.Space.Splitting.siegelParabolic_sup_symm_eq_top` (file
`grh/src/Lib/Weil/MixedModel/IsotropicSplitting.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where it is
stated for hermitian spaces with adelic frames over a CM field. Here it is stated for an arbitrary
hermitian Gram matrix with a complete polarization over a field with involution, and proved by
the reduction to the big cell described above.
-/

public section

open Matrix

namespace TauCeti

namespace IsotropicSplitting

variable {K : Type*} [Field K] [StarRing K]
  {n n₀ p : Type*} [Fintype n] [Fintype n₀] [Fintype p] [DecidableEq n] [DecidableEq n₀]
  [DecidableEq p] {A : Matrix n n K} {A₀ : Matrix n₀ n₀ K} (D : IsotropicSplitting A A₀ p)

/-- The coordinate along `k` of the product `s_l(Y) s_k(X) s_l(Y)` of shears. -/
private theorem kCoord_mul_swap_shear_mul_shear_mul_swap_shear {X Y : Matrix p p K}
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    D.kCoord * (((D.swap.shear Y hY * D.shear X hX * D.swap.shear Y hY : unitaryGroupOf A) :
        GL n K) : Matrix n n K) =
      (1 + X * Y) * D.kCoord + X * D.lCoord := by
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, kCoord_mul_swap_shear, kCoord_mul_shear,
    Matrix.add_mul, kCoord_mul_swap_shear, Matrix.mul_assoc X, lCoord_mul_swap_shear]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul]
  abel

/-! ### The blocks of an element of the unitary group -/

variable [IsEmpty n₀]

omit [DecidableEq n] in
/-- Without core, the image `g k` of the frame `k` is `l β + k δ` with `β = lCoord g k` and
`δ = kCoord g k`. -/
private theorem mul_k_eq (G : Matrix n n K) :
    G * D.k = D.l * (D.lCoord * G * D.k) + D.k * (D.kCoord * G * D.k) := by
  rw [Matrix.mul_assoc D.lCoord, Matrix.mul_assoc D.kCoord, add_comm]
  exact (D.k_mul_kCoord_mul_add_l_mul_lCoord_mul (G * D.k)).symm

omit [DecidableEq n] in
/-- The isotropy of `G k` for `G` preserving the form, in terms of the blocks `β = lCoord G k`
and `δ = kCoord G k`: `βᴴ δ + δᴴ β = 0`. -/
private theorem isotropy {G : Matrix n n K} (hG : star G * A * G = A) :
    (D.lCoord * G * D.k)ᴴ * (D.kCoord * G * D.k) + (D.kCoord * G * D.k)ᴴ * (D.lCoord * G * D.k) =
      0 := by
  have h := conjTranspose_mul_mul_mul_of_star_mul_mul_eq hG D.k D.k
  rw [D.gram_kk, D.mul_k_eq] at h
  generalize D.lCoord * G * D.k = β at h ⊢
  generalize D.kCoord * G * D.k = δ at h ⊢
  rw [← h]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, conjTranspose_l_mul_mul, conjTranspose_k_mul_mul, kCoord_mul_l_mul,
    kCoord_mul_k_mul, lCoord_mul_l_mul, lCoord_mul_k_mul, Matrix.mul_zero, zero_add, add_zero]
  exact add_comm _ _

/-! ### The big cell -/

/-- **The big cell**: an element `g` of the unitary group whose block `kCoord g k` is invertible
lies in the subgroup generated by the two opposite parabolics. -/
private theorem mem_sup_of_isUnit (g : unitaryGroupOf A)
    (hδ : IsUnit (D.kCoord * ((g : GL n K) : Matrix n n K) * D.k)) :
    g ∈ D.parabolic ⊔ D.swap.parabolic := by
  have hiso := D.isotropy (mem_unitaryGroupOf_iff.mp g.property)
  generalize hβ : D.lCoord * ((g : GL n K) : Matrix n n K) * D.k = β at hiso
  generalize hδ' : D.kCoord * ((g : GL n K) : Matrix n n K) * D.k = δ at hiso hδ
  have hδδ : δ * δ⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det δ).mp hδ)
  -- `Y = -β δ⁻¹` is skew-hermitian, by the isotropy relation `βᴴ δ = -δᴴ β`.
  have hY : (-(β * δ⁻¹))ᴴ = -(-(β * δ⁻¹)) := by
    have h1 : δ⁻¹ᴴ * δᴴ = 1 := by rw [← conjTranspose_mul, hδδ, conjTranspose_one]
    calc (-(β * δ⁻¹))ᴴ = -(δ⁻¹ᴴ * βᴴ) := by rw [conjTranspose_neg, conjTranspose_mul]
      _ = -(δ⁻¹ᴴ * (βᴴ * δ) * δ⁻¹) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hδδ, Matrix.mul_one]
      _ = -(δ⁻¹ᴴ * -(δᴴ * β) * δ⁻¹) := by rw [eq_neg_of_add_eq_zero_left hiso]
      _ = -(-(β * δ⁻¹)) := by
        rw [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  -- The shear along `l` by `Y` carries `g k = l β + k δ` to `k δ`.
  obtain ⟨t, ht⟩ := hδ
  have hmem : D.swap.shear _ hY * g ∈ D.parabolic := by
    refine D.mem_parabolic_iff.mpr ⟨t, ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, D.mul_k_eq, hβ, hδ', Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, swap_shear_mul_l, swap_shear_mul_k, ht]
    rw [Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det δ).mp ⟨t, ht⟩), Matrix.mul_one]
    abel
  have hg : g = (D.swap.shear _ hY)⁻¹ * (D.swap.shear _ hY * g) := by group
  rw [hg]
  exact mul_mem (le_sup_right (a := D.parabolic) (inv_mem (D.swap.shear_mem_parabolic _ hY)))
    (le_sup_left (b := D.swap.parabolic) hmem)

/-! ### Shrinking the kernel of the block `δ` -/

omit [DecidableEq n] [DecidableEq n₀] [IsEmpty n₀] in
/-- **The kernel shrinks**: let `β, δ` satisfy the isotropy relation `βᴴ δ + δᴴ β = 0`, and let
`w` be in the kernel of `δ` with `(β w)ᵢ ≠ 0`. Replacing the `i`-th row of `δ` by `c` times the
`i`-th row of `β`, for `c ≠ 0`, gives a matrix whose kernel is strictly contained in that of `δ`. -/
private theorem ker_lt_ker {β δ : Matrix p p K} (hiso : βᴴ * δ + δᴴ * β = 0) {w : p → K}
    (hw : δ *ᵥ w = 0) {i : p} (hi : (β *ᵥ w) i ≠ 0) {c : K} (hc : c ≠ 0) :
    LinearMap.ker ((1 - single i i (1 : K)) * δ + c • single i i (1 : K) * β).mulVecLin <
      LinearMap.ker δ.mulVecLin := by
  -- The isotropy relation, tested on `w` and a vector `v`.
  have hiso_v (v : p → K) : star (β *ᵥ w) ⬝ᵥ (δ *ᵥ v) + star (δ *ᵥ w) ⬝ᵥ (β *ᵥ v) = 0 := by
    have h := congrArg (fun M ↦ star w ⬝ᵥ (M *ᵥ v)) hiso
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add, dotProduct_mulVec,
      ← star_mulVec, Matrix.zero_mulVec, dotProduct_zero] at h
    rwa [← dotProduct_mulVec, ← dotProduct_mulVec] at h
  have hmulVec (v : p → K) : ((1 - single i i (1 : K)) * δ + c • single i i (1 : K) * β) *ᵥ v =
      δ *ᵥ v - Function.update (0 : p → K) i ((δ *ᵥ v) i) +
        Function.update (0 : p → K) i (c * (β *ᵥ v) i) := by
    simp [Matrix.add_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, single_mulVec]
  refine IsConcreteLE.lt_iff_le_and_exists.mpr ⟨fun v hv ↦ ?_, w, by simpa using hw, fun hw' ↦ ?_⟩
  · simp only [LinearMap.mem_ker, mulVecLin_apply, hmulVec] at hv ⊢
    -- Off `i` the new matrix agrees with `δ`, and at `i` it reads `c (β v)ᵢ`.
    have hoff (m : p) (hm : m ≠ i) : (δ *ᵥ v) m = 0 := by
      simpa [Function.update_apply, hm] using congrFun hv m
    have hβv : (β *ᵥ v) i = 0 := by
      simpa [hc] using congrFun hv i
    -- So `δ v` is supported at `i`, and the isotropy relation with `w` kills its value there.
    have hδv : δ *ᵥ v = Pi.single i ((δ *ᵥ v) i) := by
      ext m
      by_cases hm : m = i
      · subst hm; simp
      · simp [hoff m hm, hm]
    have h := hiso_v v
    rw [hw, star_zero, zero_dotProduct, add_zero, hδv, dotProduct_single, Pi.star_apply,
      mul_eq_zero, star_eq_zero] at h
    rw [hδv, h.resolve_left hi, Pi.single_zero]
  · simp only [LinearMap.mem_ker, mulVecLin_apply, hmulVec, hw] at hw'
    simpa [hc, hi] using congrFun hw' i

/-! ### One step of the reduction -/

/-- If `w ≠ 0` lies in the kernel of the block `δ = kCoord g k`, then `β w ≠ 0` for the block
`β = lCoord g k`: otherwise `g k w = l (β w) + k (δ w)` would vanish. -/
private theorem exists_lCoord_mul_mul_k_mulVec_apply_ne_zero (g : unitaryGroupOf A) {w : p → K}
    (hw0 : w ≠ 0) (hw : (D.kCoord * ((g : GL n K) : Matrix n n K) * D.k) *ᵥ w = 0) :
    ∃ i, ((D.lCoord * ((g : GL n K) : Matrix n n K) * D.k) *ᵥ w) i ≠ 0 := by
  by_contra! hβw
  have hβw' : (D.lCoord * ((g : GL n K) : Matrix n n K) * D.k) *ᵥ w = 0 := funext hβw
  have hgkw : ((g : GL n K) : Matrix n n K) *ᵥ (D.k *ᵥ w) = 0 := by
    rw [mulVec_mulVec, D.mul_k_eq, add_mulVec, ← mulVec_mulVec w D.l, ← mulVec_mulVec w D.k,
      hβw', hw, mulVec_zero, mulVec_zero, add_zero]
  -- So `k w = g⁻¹ g k w = 0`, and `w = kCoord k w = 0`.
  have hkw : D.k *ᵥ w = 0 := by
    rw [← Matrix.one_mulVec (D.k *ᵥ w), ← Units.inv_mul (g : GL n K), ← mulVec_mulVec, hgkw,
      mulVec_zero]
  exact hw0 (by rw [← Matrix.one_mulVec w, ← D.kCoord_mul_k, ← mulVec_mulVec, hkw, mulVec_zero])

/-- **One step of the reduction**: if the block `kCoord g k` of `g` is not invertible, a product
`ω` of shears along `k` and `l` makes the kernel of the block `kCoord (ω g) k` strictly smaller. -/
private theorem exists_mem_sup_finrank_ker_lt {j : Kˣ} (hj : star (j : K) = -j)
    (g : unitaryGroupOf A) (hδ : ¬IsUnit (D.kCoord * ((g : GL n K) : Matrix n n K) * D.k)) :
    ∃ ω ∈ D.parabolic ⊔ D.swap.parabolic,
      Module.finrank K (LinearMap.ker
          (D.kCoord * (((ω * g : unitaryGroupOf A) : GL n K) : Matrix n n K) * D.k).mulVecLin) <
        Module.finrank K
          (LinearMap.ker (D.kCoord * ((g : GL n K) : Matrix n n K) * D.k).mulVecLin) := by
  -- A nonzero vector `w` of the kernel of `δ`, and a coordinate `i` where `β w` does not vanish.
  obtain ⟨w, hw0, hw⟩ : ∃ w ≠ 0, (D.kCoord * ((g : GL n K) : Matrix n n K) * D.k) *ᵥ w = 0 := by
    rw [exists_mulVec_eq_zero_iff, ← not_ne_iff, ← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det]
    exact hδ
  obtain ⟨i, hi⟩ := D.exists_lCoord_mul_mul_k_mulVec_apply_ne_zero g hw0 hw
  -- The product `ω = s_l(j Eᵢ) s_k(c Eᵢ) s_l(j Eᵢ)` of shears, with `c = -j⁻¹`.
  have hY : ((j : K) • single i i (1 : K))ᴴ = -((j : K) • single i i (1 : K)) := by
    rw [conjTranspose_smul, conjTranspose_single, star_one, hj, neg_smul]
  have hX : (-((j⁻¹ : Kˣ) : K) • single i i (1 : K))ᴴ =
      -(-((j⁻¹ : Kˣ) : K) • single i i (1 : K)) := by
    rw [conjTranspose_smul, conjTranspose_single, star_one, star_neg, Units.val_inv_eq_inv_val,
      star_inv₀, hj, inv_neg, neg_neg, neg_smul, neg_neg]
  set E := single i i (1 : K) with hE
  set c := -((j⁻¹ : Kˣ) : K) with hc
  refine ⟨D.swap.shear _ hY * D.shear _ hX * D.swap.shear _ hY,
    mul_mem (mul_mem (le_sup_right (a := D.parabolic) (D.swap.shear_mem_parabolic _ hY))
      (le_sup_left (b := D.swap.parabolic) (D.shear_mem_parabolic _ hX)))
      (le_sup_right (a := D.parabolic) (D.swap.shear_mem_parabolic _ hY)), ?_⟩
  -- The block `δ` of `ω g` is `δ` with its `i`-th row replaced by `c` times that of `β`.
  have hδω : D.kCoord * (((D.swap.shear _ hY * D.shear _ hX * D.swap.shear _ hY * g :
        unitaryGroupOf A) : GL n K) : Matrix n n K) * D.k =
      (1 - E) * (D.kCoord * ((g : GL n K) : Matrix n n K) * D.k) +
        c • E * (D.lCoord * ((g : GL n K) : Matrix n n K) * D.k) := by
    have hXY : c • E * ((j : K) • E) = -E := by simp [hc, hE]
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mul_assoc,
      D.kCoord_mul_swap_shear_mul_shear_mul_swap_shear, hXY]
    simp only [Matrix.add_mul, Matrix.mul_assoc, sub_eq_add_neg]
  rw [hδω]
  exact Submodule.finrank_lt_finrank_of_lt <| ker_lt_ker
    (D.isotropy (mem_unitaryGroupOf_iff.mp g.property)) hw hi (neg_ne_zero.mpr (Units.ne_zero _))

/-! ### The generation theorem -/

/-- **The two opposite Siegel parabolics generate the unitary group**: for an isotropic splitting
of a hermitian matrix `A` over a field with involution, with empty core, the stabilizers of the
spans of the frames `k` and `l` generate the unitary group of `A`, provided the involution has a
nonzero skew element `j` (`star j = -j`). -/
theorem parabolic_sup_swap_parabolic_eq_top {j : Kˣ} (hj : star (j : K) = -j) :
    D.parabolic ⊔ D.swap.parabolic = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ ?_
  -- Induction on the dimension of the kernel of the block `kCoord g k`.
  induction hr : Module.finrank K
      (LinearMap.ker (D.kCoord * ((g : GL n K) : Matrix n n K) * D.k).mulVecLin)
    using Nat.strong_induction_on generalizing g with
  | _ r ih =>
  by_cases hδ : IsUnit (D.kCoord * ((g : GL n K) : Matrix n n K) * D.k)
  · exact D.mem_sup_of_isUnit g hδ
  obtain ⟨ω, hω, hlt⟩ := D.exists_mem_sup_finrank_ker_lt hj g hδ
  rw [hr] at hlt
  have hg : g = ω⁻¹ * (ω * g) := by group
  rw [hg]
  exact mul_mem (inv_mem hω) (ih _ hlt (ω * g) (Subgroup.mem_top _) rfl)

end IsotropicSplitting

end TauCeti
