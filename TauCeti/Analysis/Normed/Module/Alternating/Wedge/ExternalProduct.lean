/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Append

/-!
# External products of forms

For a real `k`-form `φ` on `E` and a real `l`-form `ψ` on `F`, the external product
`φ ⊠ ψ = pr₁*φ ∧ pr₂*ψ` is the `(k + l)`-form on the direct sum `E ⊕ F`, realized as the `L²`
product `WithLp 2 (E × F)`. On a product frame, with the frame of the first factor first, it is
the product of the two values:

`(φ ⊠ ψ)((v₁, 0), …, (v_k, 0), (0, w₁), …, (0, w_l)) = φ(v) ψ(w)`.

Its comass, the operator norm, satisfies `‖φ‖ ‖ψ‖ ≤ ‖φ ⊠ ψ‖ ≤ binomial(k + l, k) ‖φ‖ ‖ψ‖`.
The lower bound comes from product frames, the upper bound from the shuffle expansion of the
wedge. On a frame where the external product splits into a value of each factor, its value is
bounded by `‖φ‖ ‖ψ‖` once the projected components have norm at most one. Exchanging the factors
multiplies values by `(-1) ^ (k * l)` and preserves the comass.
None of this needs an inner product; the comass equalities for a decomposable or top-degree
factor, and products of calibrated frames, are in
`TauCeti.Analysis.InnerProductSpace.Orthonormal.ExternalProduct`.

## Main definitions

* `ContinuousAlternatingMap.externalProduct φ ψ`: the external product `pr₁*φ ∧ pr₂*ψ`.

## Main results

* `ContinuousAlternatingMap.externalProduct_apply_append`: the value on a product frame.
* `ContinuousAlternatingMap.norm_externalProduct_apply_append_le`: the bound on a split frame.
* `ContinuousAlternatingMap.norm_externalProduct_le`: the binomial upper bound.
* `ContinuousAlternatingMap.norm_mul_norm_le_norm_externalProduct`: the lower bound.
* `ContinuousAlternatingMap.externalProduct_apply_eq_neg_one_pow_mul` and
  `ContinuousAlternatingMap.norm_externalProduct_comm`: exchanging the factors.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §II.7.
-/

public section

namespace ContinuousAlternatingMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {k l : ℕ}

/-- The **external product** `φ ⊠ ψ = pr₁*φ ∧ pr₂*ψ` of a `k`-form `φ` on `E` and an `l`-form `ψ`
on `F`, a `(k + l)`-form on the `L²` product `E ⊕ F`. -/
noncomputable def externalProduct (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    WithLp 2 (E × F) [⋀^Fin (k + l)]→L[ℝ] ℝ :=
  wedge (φ.compContinuousLinearMap (WithLp.fstL 2 ℝ E F))
    (ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F))

/-- The external product is the wedge of the pullbacks of the factors along the projections. -/
theorem externalProduct_def (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalProduct φ ψ = wedge (φ.compContinuousLinearMap (WithLp.fstL 2 ℝ E F))
      (ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F)) :=
  (rfl)

/-- The external product is additive in its first factor. -/
@[simp]
theorem externalProduct_add_left (φ φ' : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalProduct (φ + φ') ψ = externalProduct φ ψ + externalProduct φ' ψ := by
  simp only [externalProduct_def, ← compContinuousLinearMapLinear_apply (S := ℝ), map_add,
    wedge_add_left]

/-- The external product is additive in its second factor. -/
@[simp]
theorem externalProduct_add_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ ψ' : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalProduct φ (ψ + ψ') = externalProduct φ ψ + externalProduct φ ψ' := by
  simp only [externalProduct_def, ← compContinuousLinearMapLinear_apply (S := ℝ), map_add,
    wedge_add_right]

/-- The external product is homogeneous in its first factor. -/
@[simp]
theorem externalProduct_smul_left (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalProduct (c • φ) ψ = c • externalProduct φ ψ := by
  simp only [externalProduct_def, ← compContinuousLinearMapLinear_apply (S := ℝ), map_smul,
    wedge_smul_left]

/-- The external product is homogeneous in its second factor. -/
@[simp]
theorem externalProduct_smul_right (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalProduct φ (c • ψ) = c • externalProduct φ ψ := by
  simp only [externalProduct_def, ← compContinuousLinearMapLinear_apply (S := ℝ), map_smul,
    wedge_smul_right]

/-- The external product vanishes when its first factor is zero. -/
@[simp]
theorem externalProduct_zero_left (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalProduct (0 : E [⋀^Fin k]→L[ℝ] ℝ) ψ = 0 := by
  rw [← zero_smul ℝ (0 : E [⋀^Fin k]→L[ℝ] ℝ), externalProduct_smul_left, zero_smul]

/-- The external product vanishes when its second factor is zero. -/
@[simp]
theorem externalProduct_zero_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) :
    externalProduct φ (0 : F [⋀^Fin l]→L[ℝ] ℝ) = 0 := by
  rw [← zero_smul ℝ (0 : F [⋀^Fin l]→L[ℝ] ℝ), externalProduct_smul_right, zero_smul]

/-- The external product on a concatenated frame `(a, b)` splits as a value of `φ` on the first
components of `a` times a value of `ψ` on the second components of `b`, provided `ψ` vanishes on
every frame having the second component of one of the `aᵢ` as an entry. -/
theorem externalProduct_apply_append_of_forall (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (a : Fin k → WithLp 2 (E × F)) (b : Fin l → WithLp 2 (E × F))
    (h : ∀ (y : Fin l → F) (i : Fin k) (j : Fin l), ψ (Function.update y j (a i).snd) = 0) :
    externalProduct φ ψ (Fin.append a b) = φ (fun i ↦ (a i).fst) * ψ (fun j ↦ (b j).snd) := by
  classical
  rw [externalProduct_def, wedge_def, pairedWedge_apply_append_of_forall _ _ _ _ a b fun y i j ↦ ?_]
  · simp [Function.comp_def]
  simpa [Function.comp_update] using h (WithLp.sndL 2 ℝ E F ∘ y) i j

/-- On a concatenated frame `(a, b)` on which the external product splits, as in
`externalProduct_apply_append_of_forall`, and whose projected components `(a i).fst` and
`(b j).snd` have norm at most one, the value of `φ ⊠ ψ` has norm at most `‖φ‖ ‖ψ‖`. -/
theorem norm_externalProduct_apply_append_le (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    {a : Fin k → WithLp 2 (E × F)} {b : Fin l → WithLp 2 (E × F)} (ha : ∀ i, ‖(a i).fst‖ ≤ 1)
    (hb : ∀ j, ‖(b j).snd‖ ≤ 1)
    (h : ∀ (y : Fin l → F) (i : Fin k) (j : Fin l), ψ (Function.update y j (a i).snd) = 0) :
    ‖externalProduct φ ψ (Fin.append a b)‖ ≤ ‖φ‖ * ‖ψ‖ := by
  have hφ : ‖φ fun i ↦ (a i).fst‖ ≤ ‖φ‖ := by
    simpa using φ.le_opNorm_mul_pow_of_le (m := fun i ↦ (a i).fst) (pi_norm_le_iff_of_nonneg
      zero_le_one |>.2 ha)
  have hψ : ‖ψ fun j ↦ (b j).snd‖ ≤ ‖ψ‖ := by
    simpa using ψ.le_opNorm_mul_pow_of_le (m := fun j ↦ (b j).snd) (pi_norm_le_iff_of_nonneg
      zero_le_one |>.2 hb)
  rw [externalProduct_apply_append_of_forall φ ψ a b h, norm_mul]
  exact mul_le_mul hφ hψ (norm_nonneg _) (norm_nonneg _)

/-- **The external product on a product frame** is the product of the values of the factors:
`(φ ⊠ ψ)((v₁, 0), …, (v_k, 0), (0, w₁), …, (0, w_l)) = φ v * ψ w`. -/
@[simp]
theorem externalProduct_apply_append (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (v : Fin k → E) (w : Fin l → F) :
    externalProduct φ ψ (Fin.append (fun i ↦ WithLp.toLp 2 (v i, 0))
      (fun j ↦ WithLp.toLp 2 (0, w j))) = φ v * ψ w := by
  classical
  rw [externalProduct_apply_append_of_forall _ _ _ _ fun y i j ↦ by simp]
  simp

/-- **The binomial bound** for the comass of an external product:
`‖φ ⊠ ψ‖ ≤ binomial(k + l, k) ‖φ‖ ‖ψ‖`. -/
theorem norm_externalProduct_le (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖externalProduct φ ψ‖ ≤ (k + l).choose k * ‖φ‖ * ‖ψ‖ := by
  have hfst : ‖WithLp.fstL 2 ℝ E F‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
      simpa using WithLp.norm_fst_le (x := x)
  have hsnd : ‖WithLp.sndL 2 ℝ E F‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
      simpa using WithLp.norm_snd_le (x := x)
  have hφ : ‖φ.compContinuousLinearMap (WithLp.fstL 2 ℝ E F)‖ ≤ ‖φ‖ :=
    (φ.norm_compContinuousLinearMap_le _).trans
      (mul_le_of_le_one_right (norm_nonneg φ) (pow_le_one₀ (norm_nonneg _) hfst))
  have hψ : ‖ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F)‖ ≤ ‖ψ‖ :=
    (ψ.norm_compContinuousLinearMap_le _).trans
      (mul_le_of_le_one_right (norm_nonneg ψ) (pow_le_one₀ (norm_nonneg _) hsnd))
  refine (norm_wedge_le _ _).trans ?_
  gcongr

/-- **Graded commutativity of the external product**: exchanging the two factors of the form and
the two components of `E ⊕ F`, keeping the frame order, multiplies the value by `(-1) ^ (k * l)`. -/
theorem externalProduct_apply_eq_neg_one_pow_mul (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) (u : Fin (k + l) → WithLp 2 (E × F)) :
    externalProduct φ ψ u = (-1) ^ (k * l) * externalProduct ψ φ
      (LinearIsometryEquiv.withLpProdComm 2 ℝ E F ∘ u ∘ Fin.cast (Nat.add_comm l k)) := by
  let σ : WithLp 2 (E × F) →L[ℝ] WithLp 2 (F × E) :=
    (LinearIsometryEquiv.withLpProdComm 2 ℝ E F).toLinearIsometry.toContinuousLinearMap
  have hψ : ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F) =
      (ψ.compContinuousLinearMap (WithLp.fstL 2 ℝ F E)).compContinuousLinearMap σ := by
    ext; simp [σ, Function.comp_def]
  have hφ : φ.compContinuousLinearMap (WithLp.fstL 2 ℝ E F) =
      (φ.compContinuousLinearMap (WithLp.sndL 2 ℝ F E)).compContinuousLinearMap σ := by
    ext; simp [σ, Function.comp_def]
  rw [externalProduct_def, wedge_comm, smul_eq_mul, hψ, hφ, wedge_compContinuousLinearMap,
    compContinuousLinearMap_apply, ← externalProduct_def]
  simp only [σ, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

/-- One inequality of `norm_externalProduct_comm`. -/
private lemma norm_externalProduct_le_norm_externalProduct_swap (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) : ‖externalProduct φ ψ‖ ≤ ‖externalProduct ψ φ‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun u ↦ ?_
  rw [externalProduct_apply_eq_neg_one_pow_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  refine ((externalProduct ψ φ).le_opNorm _).trans_eq ?_
  simp only [Function.comp_apply, LinearIsometryEquiv.norm_map]
  exact congrArg _ ((finCongr (Nat.add_comm l k)).prod_comp fun i ↦ ‖u i‖)

/-- Exchanging the factors does not change the comass of an external product. -/
theorem norm_externalProduct_comm (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖externalProduct φ ψ‖ = ‖externalProduct ψ φ‖ :=
  le_antisymm (norm_externalProduct_le_norm_externalProduct_swap φ ψ)
    (norm_externalProduct_le_norm_externalProduct_swap ψ φ)

/-- **The lower bound** for the comass of an external product: `‖φ‖ ‖ψ‖ ≤ ‖φ ⊠ ψ‖`. It is tested
on product frames. -/
theorem norm_mul_norm_le_norm_externalProduct (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) : ‖φ‖ * ‖ψ‖ ≤ ‖externalProduct φ ψ‖ := by
  set C := ‖externalProduct φ ψ‖
  have hframe (v : Fin k → E) (w : Fin l → F) :
      ‖φ v‖ * ‖ψ w‖ ≤ C * (∏ i, ‖v i‖) * ∏ j, ‖w j‖ := by
    simpa [Fin.prod_univ_add, mul_assoc] using
      (externalProduct φ ψ).le_opNorm (Fin.append (fun i ↦ WithLp.toLp 2 (v i, (0 : F)))
        (fun j ↦ WithLp.toLp 2 ((0 : E), w j)))
  have hψ (w : Fin l → F) : ‖ψ w‖ * ‖φ‖ ≤ C * ∏ j, ‖w j‖ := by
    simpa [norm_smul] using (‖ψ w‖ • φ).opNorm_le_bound (by positivity) fun v ↦ by
      rw [smul_apply, norm_smul, norm_norm, mul_comm]
      exact (hframe v w).trans_eq (by ring)
  simpa [norm_smul, mul_comm] using
    (‖φ‖ • ψ).opNorm_le_bound (norm_nonneg (externalProduct φ ψ)) fun w ↦ by
      rw [smul_apply, norm_smul, norm_norm, mul_comm]
      exact hψ w


end ContinuousAlternatingMap
