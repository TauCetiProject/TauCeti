/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Plucker
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import TauCeti.Analysis.AbsoluteValue.LinearForms
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.InnerProductSpace.Gram.Fischer
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import TauCeti.Order.Hom.PowersetCard

/-!
# Local bounds for Plücker coordinates

The Euclidean norm of the Plücker vector is at most the product of the Euclidean
norms of the original vectors. For a nonarchimedean absolute value, the analogous
statement holds for maximum norms, while an arbitrary absolute value incurs at most
the factorial of the exterior degree; columnwise entry bounds on a subset `s` pass
to the minor on `s` in the same way, and coordinate bounds controlled by a linearly
independent system of linear forms pass to uniform power bounds on the Plücker sup
norm (`AbsoluteValue.iSup_plucker_le_of_forall_apply_le`,
`AbsoluteValue.exists_one_le_forall_iSup_plucker_le`). These are the local estimates
underlying the height bound for a subspace in terms of a spanning family or an
approximation domain. The overlapping-family inequality compares the common rows and
their two extensions; it supplies the archimedean factor of subspace-height
submodularity.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, Ann. of Math. 177 (2013), §6.1, (6.11)–(6.12).
-/

public section

open scoped BigOperators
open Set

namespace TauCeti

/-- Cauchy–Binet identifies the squared Euclidean Plücker norm with the real part
of the Gram determinant, including empty and dependent families. -/
theorem sum_norm_plucker_sq_eq_re_det_gram {𝕜 ι : Type*} [RCLike 𝕜]
    [LinearOrder ι] [Fintype ι] {p : ℕ} (x : Fin p → ι → 𝕜) :
    ∑ s, ‖plucker x s‖ ^ 2 =
      RCLike.re (Matrix.gram 𝕜 (fun i ↦ WithLp.toLp 2 (x i))).det := by
  have hgram : Matrix.gram 𝕜 (fun i ↦ WithLp.toLp 2 (x i)) =
      (Matrix.of x * (Matrix.of x).conjTranspose).transpose := by
    ext i j
    simp [Matrix.gram_apply, Matrix.mul_apply, EuclideanSpace.inner_toLp_toLp, dotProduct]
  rw [hgram, Matrix.det_transpose, det_mul_conjTranspose_eq_sum_plucker_mul_star]
  simp only [map_sum, RCLike.star_def, RCLike.mul_conj, RCLike.re_ofReal_pow]

/-- The squared Euclidean norm of a real or complex Plücker vector is bounded by the
product of the squared Euclidean row norms, including empty and dependent families. -/
theorem sum_norm_plucker_sq_le {𝕜 ι : Type*} [RCLike 𝕜] [LinearOrder ι] [Fintype ι] {p : ℕ}
    (x : Fin p → ι → 𝕜) :
    ∑ s, ‖plucker x s‖ ^ 2 ≤ ∏ i, ∑ j, ‖x i j‖ ^ 2 := by
  rw [sum_norm_plucker_sq_eq_re_det_gram]
  simpa only [EuclideanSpace.norm_sq_eq, WithLp.ofLp_toLp] using
    Matrix.re_det_gram_le_prod_norm_sq (𝕜 := 𝕜) (fun i ↦ WithLp.toLp 2 (x i))

/-- The squared Euclidean Plücker norms satisfy the overlapping-family inequality.
No independence assumption is needed, and empty families are included. -/
theorem sum_norm_plucker_sq_overlap_le {𝕜 ι : Type*} [RCLike 𝕜]
    [LinearOrder ι] [Fintype ι] {p q r : ℕ}
    (x : Fin p → ι → 𝕜) (y : Fin q → ι → 𝕜) (z : Fin r → ι → 𝕜) :
    (∑ s, ‖plucker x s‖ ^ 2) *
        (∑ s, ‖plucker (Fin.append x (Fin.append y z)) s‖ ^ 2) ≤
      (∑ s, ‖plucker (Fin.append x y) s‖ ^ 2) *
        (∑ s, ‖plucker (Fin.append x z) s‖ ^ 2) := by
  have hdet {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α ≃ β) (f : β → EuclideanSpace 𝕜 ι) :
      (Matrix.gram 𝕜 (f ∘ e)).det = (Matrix.gram 𝕜 f).det :=
    Matrix.det_submatrix_equiv_self e (Matrix.gram 𝕜 f)
  have happ {a b : ℕ} (u : Fin a → ι → 𝕜) (v : Fin b → ι → 𝕜) :
      Sum.elim (fun i ↦ WithLp.toLp 2 (u i)) (fun i ↦ WithLp.toLp 2 (v i)) =
        (fun i ↦ WithLp.toLp 2 (Fin.append u v i)) ∘ finSumFinEquiv := by
    have h := congrArg (fun f ↦ WithLp.toLp 2 ∘ f)
      (Fin.append_comp_sumElim (xs := u) (ys := v)).symm
    rw [Sum.comp_elim] at h
    -- Align the equivalence coercion with Mathlib's explicit sum eliminator.
    simpa only [Function.comp_def, finSumFinEquiv, Equiv.coe_fn_mk] using h
  have h := Matrix.re_det_gram_mul_re_det_gram_sumElim_le (𝕜 := 𝕜)
    (fun i ↦ WithLp.toLp 2 (x i)) (fun i ↦ WithLp.toLp 2 (y i))
    (fun i ↦ WithLp.toLp 2 (z i))
  rw [happ, happ, happ] at h
  -- Reindex the inner and outer sum types together in the full Gram matrix.
  have hfull : Sum.elim (fun i ↦ WithLp.toLp 2 (x i))
      ((fun i ↦ WithLp.toLp 2 (Fin.append y z i)) ∘ finSumFinEquiv) =
      (fun i ↦ WithLp.toLp 2 (Fin.append x (Fin.append y z) i)) ∘
        ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv) := by
    ext i
    rcases i with i | (i | i) <;> simp
  rw [hfull, hdet, hdet, hdet] at h
  simpa only [sum_norm_plucker_sq_eq_re_det_gram] using h

end TauCeti

namespace AbsoluteValue

open Set.powersetCard TauCeti

/-- Every Plücker coordinate is bounded by the product of the maximum row norms
for a nonarchimedean real-valued absolute value. -/
theorem plucker_le_prod_iSup {R ι : Type*} [CommRing R] [LinearOrder ι] [Finite ι]
    {p : ℕ} (v : AbsoluteValue R ℝ) (hv : IsNonarchimedean v)
    (x : Fin p → ι → R) (s : powersetCard ι p) :
    v (plucker x s) ≤ ∏ i, ⨆ j, v (x i j) := by
  rw [plucker_apply]
  exact Matrix.abv_det_le_prod_of_le _ hv fun i j ↦ Finite.le_ciSup_of_le _ le_rfl

/-- Every Plücker coordinate is bounded by `p!` times the product of the maximum row norms
for any real-valued absolute value. -/
theorem plucker_le_factorial_mul_prod_iSup {R ι : Type*} [CommRing R] [LinearOrder ι] [Finite ι]
    {p : ℕ} (v : AbsoluteValue R ℝ) (x : Fin p → ι → R) (s : powersetCard ι p) :
    v (plucker x s) ≤ p.factorial * ∏ i, ⨆ j, v (x i j) := by
  rw [plucker_apply]
  simpa using Matrix.abv_det_le_factorial_prod _ v fun i j ↦
    Finite.le_ciSup_of_le (ofFinEmbEquiv.symm s j) le_rfl

/-- Columnwise bounds on the coordinates in `s` bound the Plücker coordinate at `s` by `p!` times
their product over `s`, for any absolute value. -/
theorem plucker_le_factorial_mul_prod {R S ι : Type*} [CommRing R] [CommRing S] [LinearOrder S]
    [IsStrictOrderedRing S] [LinearOrder ι] {p : ℕ} (v : AbsoluteValue R S) (x : Fin p → ι → R)
    (s : powersetCard ι p) {b : ι → S} (hb : ∀ i, ∀ j ∈ s, v (x i j) ≤ b j) :
    v (plucker x s) ≤ p.factorial * ∏ j ∈ (s : Finset ι), b j := by
  rw [plucker_apply, ← prod_comp_ofFinEmbEquiv_symm s b]
  simpa only [Fintype.card_fin] using
    Matrix.abv_det_le_factorial_prod' (Matrix.of fun i j ↦ x i (ofFinEmbEquiv.symm s j)) v
      (b := fun j ↦ b (ofFinEmbEquiv.symm s j)) fun i j ↦ hb i _
        ((mem_range_ofFinEmbEquiv_symm_iff_mem s (ofFinEmbEquiv.symm s j)).1 ⟨j, rfl⟩)

/-- Columnwise bounds on the coordinates in `s` bound the Plücker coordinate at `s` by their
product over `s`, for a nonarchimedean absolute value. -/
theorem plucker_le_prod {R S ι : Type*} [CommRing R] [CommRing S] [LinearOrder S]
    [IsStrictOrderedRing S] [LinearOrder ι] {p : ℕ} (v : AbsoluteValue R S)
    (hv : IsNonarchimedean v) (x : Fin p → ι → R) (s : powersetCard ι p) {b : ι → S}
    (hb : ∀ i, ∀ j ∈ s, v (x i j) ≤ b j) :
    v (plucker x s) ≤ ∏ j ∈ (s : Finset ι), b j := by
  rw [plucker_apply, ← prod_comp_ofFinEmbEquiv_symm s b]
  exact Matrix.abv_det_le_prod_of_le' _ hv (b := fun j ↦ b (ofFinEmbEquiv.symm s j))
    fun i j ↦ hb i _
      ((mem_range_ofFinEmbEquiv_symm_iff_mem s (ofFinEmbEquiv.symm s j)).1 ⟨j, rfl⟩)

/-- If every coordinate `v (x j)` is bounded by `C * ⨆ i, v (l i x)` (`1 ≤ C`) and each row
satisfies `v (l i (x r)) ≤ Q ^ e i` (`1 ≤ Q`), then every `p`-Plücker coordinate of `x` is bounded
by `(#ι)! * C ^ #ι * Q ^ (p * ⨆ i, e i)`. Empty index types and arbitrary exterior degrees `p` are
included. -/
theorem iSup_plucker_le_of_forall_apply_le {R ι : Type*} [CommRing R] [LinearOrder ι] [Fintype ι]
    {p : ℕ} (v : AbsoluteValue R ℝ) {l : ι → Module.Dual R (ι → R)} {C Q : ℝ} (hC1 : 1 ≤ C)
    (hQ : 1 ≤ Q) (hl : ∀ (x : ι → R) (j : ι), v (x j) ≤ C * ⨆ i, v (l i x)) (e : ι → ℝ)
    {x : Fin p → ι → R} (hx : ∀ (r : Fin p) (i : ι), v (l i (x r)) ≤ Q ^ e i) :
    ⨆ s, v (plucker x s) ≤
      ((Fintype.card ι).factorial * C ^ Fintype.card ι) * Q ^ ((p : ℝ) * ⨆ i, e i) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA1 : 1 ≤ (Fintype.card ι).factorial * C ^ Fintype.card ι :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos _) (one_le_pow₀ hC1)
  refine Real.iSup_le (fun s ↦ ?_) (mul_nonneg (zero_le_one.trans hA1) (by positivity))
  have hp : p ≤ Fintype.card ι := by simpa using (s : Finset ι).card_le_univ
  have hrow (r : Fin p) : ⨆ j, v (x r j) ≤ C * Q ^ (⨆ i, e i) := by
    have : Nonempty ι := Fintype.card_pos_iff.mp (lt_of_lt_of_le r.pos hp)
    exact ciSup_le fun j ↦ (hl (x r) j).trans <| mul_le_mul_of_nonneg_left
      (ciSup_le fun i ↦ (hx r i).trans
        (Real.rpow_le_rpow_of_exponent_le hQ (Finite.le_ciSup_of_le i le_rfl)))
      (zero_le_one.trans hC1)
  calc v (plucker x s)
      ≤ p.factorial * ∏ r : Fin p, ⨆ j, v (x r j) := v.plucker_le_factorial_mul_prod_iSup x s
    _ ≤ p.factorial * ∏ _r : Fin p, (C * Q ^ (⨆ i, e i)) :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun _ _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) fun r _ ↦ hrow r)
          (Nat.cast_nonneg _)
    _ = (p.factorial * C ^ p) * Q ^ ((p : ℝ) * ⨆ i, e i) := by
        rw [Finset.prod_const, Finset.card_fin, mul_pow, ← Real.rpow_natCast (Q ^ _),
          ← Real.rpow_mul hQ0.le, mul_comm (⨆ i, e i)]
        ring
    _ ≤ ((Fintype.card ι).factorial * C ^ Fintype.card ι) * Q ^ ((p : ℝ) * ⨆ i, e i) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul (by exact_mod_cast Nat.factorial_le hp)
          (pow_le_pow_right₀ hC1 hp) (by positivity) (Nat.cast_nonneg _)

/-- At any real-valued absolute value where `#ι` linear forms `l` on `ι → K` are linearly
independent, some `A ≥ 1` (independent of `e`, `Q`, `p`, and `x`) bounds `⨆ s, v (plucker x s)` by
`A * Q ^ (p * ⨆ i, e i)` whenever `1 ≤ Q` and `v (l i (x r)) ≤ Q ^ e i`. -/
theorem exists_one_le_forall_iSup_plucker_le {K ι : Type*} [Field K] [LinearOrder ι] [Finite ι]
    (v : AbsoluteValue K ℝ) {l : ι → Module.Dual K (ι → K)} (hl : LinearIndependent K l) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (e : ι → ℝ) ⦃Q : ℝ⦄, 1 ≤ Q → ∀ {p : ℕ} {x : Fin p → ι → K},
      (∀ r i, v (l i (x r)) ≤ Q ^ e i) →
      ⨆ s, v (plucker x s) ≤ A * Q ^ ((p : ℝ) * ⨆ i, e i) := by
  cases nonempty_fintype ι
  obtain ⟨C, hC1, hC⟩ := v.exists_one_le_forall_apply_le_mul_iSup hl
  refine ⟨(Fintype.card ι).factorial * C ^ Fintype.card ι,
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos _) (one_le_pow₀ hC1),
    fun e Q hQ _ _ hx ↦ v.iSup_plucker_le_of_forall_apply_le hC1 hQ hC e hx⟩

end AbsoluteValue
