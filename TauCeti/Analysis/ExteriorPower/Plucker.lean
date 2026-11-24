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
public import Mathlib.LinearAlgebra.Dual.Defs
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
to the minor on `s` in the same way. Conversely, when evaluations `v (l i (x r))`
are uniformly bounded by `M` and `l` controls all coordinates (in particular, when
a finite family `l` spans the dual space), `AbsoluteValue.iSup_plucker_le_of_forall_apply_le`
and `AbsoluteValue.exists_one_le_forall_iSup_plucker_le` bound the Plücker sup norm
`⨆ s, v (plucker x s)` in terms of `M ^ p`. These are the local estimates underlying
the height bound for a subspace in terms of a spanning family. The overlapping-family
inequality compares the common rows and their two extensions; it supplies the
archimedean factor of subspace-height submodularity.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §7.5.
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

/-- Rowwise bounds bound every Plücker coordinate: if every coordinate of the `i`-th vector of a
family of `p` vectors is at most `b i` at an absolute value `v`, then every Plücker coordinate of
the family is at most `p! * ∏ i, b i` there. -/
theorem plucker_le_factorial_mul_prod_of_row_le {R S ι : Type*} [CommRing R] [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] [LinearOrder ι] {p : ℕ} (v : AbsoluteValue R S)
    {x : Fin p → ι → R} {b : Fin p → S} (hx : ∀ i j, v (x i j) ≤ b i) (s : powersetCard ι p) :
    v (plucker x s) ≤ p.factorial * ∏ i, b i := by
  rw [plucker_apply]
  exact (Matrix.abv_det_le_factorial_prod _ v fun i j ↦ hx i _).trans_eq (by rw [Fintype.card_fin])

/-- Every Plücker coordinate is bounded by `p!` times the product of the maximum row norms
for any real-valued absolute value. -/
theorem plucker_le_factorial_mul_prod_iSup {R ι : Type*} [CommRing R] [LinearOrder ι] [Finite ι]
    {p : ℕ} (v : AbsoluteValue R ℝ) (x : Fin p → ι → R) (s : powersetCard ι p) :
    v (plucker x s) ≤ p.factorial * ∏ i, ⨆ j, v (x i j) :=
  v.plucker_le_factorial_mul_prod_of_row_le (fun _ j ↦ Finite.le_ciSup_of_le j le_rfl) s

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

/-- If every coordinate `v (x j)` is bounded by `C * ⨆ i, v (l i x)` (`0 ≤ C`) and each row
satisfies `v (l i (x r)) ≤ M` (`0 ≤ M`), then every `p`-Plücker coordinate of `x` is bounded by
`p! * (C * M) ^ p`. Empty index types and arbitrary exterior degrees `p` are included. -/
theorem iSup_plucker_le_of_forall_apply_le {R ι κ : Type*} [CommRing R] [LinearOrder ι]
    [Finite ι] {p : ℕ} (v : AbsoluteValue R ℝ) {l : κ → Module.Dual R (ι → R)} {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hl : ∀ (x : ι → R) (j : ι), v (x j) ≤ C * ⨆ i, v (l i x))
    {x : Fin p → ι → R} (hx : ∀ (r : Fin p) (i : κ), v (l i (x r)) ≤ M) :
    ⨆ s, v (plucker x s) ≤ p.factorial * (C * M) ^ p := by
  refine Real.iSup_le (fun s ↦ ?_) (by positivity)
  have hrow (r : Fin p) : ⨆ j, v (x r j) ≤ C * M :=
    Real.iSup_le
      (fun j ↦ (hl (x r) j).trans <| mul_le_mul_of_nonneg_left (Real.iSup_le (hx r) hM) hC)
      (mul_nonneg hC hM)
  exact (v.plucker_le_factorial_mul_prod_iSup x s).trans <|
    (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) fun r _ ↦ hrow r)
      (Nat.cast_nonneg _)).trans_eq (by simp)

/-- At any real-valued absolute value where a finite family of linear forms `l` on `ι → R` spans
the dual space, some `A ≥ 1` (independent of `M`, `p`, and `x`) bounds `⨆ s, v (plucker x s)` by
`A * M ^ p` whenever `0 ≤ M` and `v (l i (x r)) ≤ M` for all `r` and `i`. -/
theorem exists_one_le_forall_iSup_plucker_le {R ι κ : Type*} [CommRing R] [LinearOrder ι]
    [Finite ι] [Finite κ] (v : AbsoluteValue R ℝ) {l : κ → Module.Dual R (ι → R)}
    (hl : Submodule.span R (Set.range l) = ⊤) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ ⦃M : ℝ⦄, 0 ≤ M → ∀ {p : ℕ} {x : Fin p → ι → R},
      (∀ r i, v (l i (x r)) ≤ M) → ⨆ s, v (plucker x s) ≤ A * M ^ p := by
  cases nonempty_fintype ι
  obtain ⟨C, hC1, hC⟩ := v.exists_one_le_forall_apply_le_mul_iSup hl
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hA1 : 1 ≤ (Fintype.card ι).factorial * C ^ Fintype.card ι :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos _) (one_le_pow₀ hC1)
  refine ⟨(Fintype.card ι).factorial * C ^ Fintype.card ι, hA1, fun M hM p x hx ↦ ?_⟩
  refine Real.iSup_le (fun s ↦ ?_) (mul_nonneg (zero_le_one.trans hA1) (pow_nonneg hM p))
  have hp : p ≤ Fintype.card ι := by simpa using (s : Finset ι).card_le_univ
  calc v (plucker x s)
      ≤ ⨆ t, v (plucker x t) := Finite.le_ciSup_of_le s le_rfl
    _ ≤ p.factorial * (C * M) ^ p := v.iSup_plucker_le_of_forall_apply_le hC0 hM hC hx
    _ = (p.factorial * C ^ p) * M ^ p := by rw [mul_pow, mul_assoc]
    _ ≤ ((Fintype.card ι).factorial * C ^ Fintype.card ι) * M ^ p := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hM p)
        exact mul_le_mul (by exact_mod_cast Nat.factorial_le hp) (pow_le_pow_right₀ hC1 hp)
          (pow_nonneg hC0 p) (Nat.cast_nonneg _)

end AbsoluteValue
