/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# Fixed points of linear automorphisms of a torus

Let `p > 0` and let `A ∈ GL(ι, ℤ)` act on the torus `Tⁿ = ι → AddCircle p` by
`x ↦ A • x` (`AddCircle.instDistribMulActionGeneralLinearGroup`). Through the covering map
`t ↦ ([t i])ᵢ` this is multiplication of real vectors by `A`, so `[t]` is fixed exactly when
`(1 - A) t` has all its coordinates in `pℤ`. When `det (1 - A) ≠ 0`, the map
`v ↦ [p (1 - A)⁻¹ v]` from `ℤⁿ` onto the fixed points has kernel `(1 - A) ℤⁿ`, so the fixed points
form a group isomorphic to `ℤⁿ / (1 - A) ℤⁿ`, of order `|det (1 - A)|`
(`AddCircle.nat_card_fixedPoints_generalLinearGroup_smul`). When `det (1 - A) = 0`, an integer
vector `k ≠ 0` with `(1 - A) k = 0` gives the circle of fixed points `[s k]`, `s ∈ ℝ`, so the fixed
points are infinite. Hence `x ↦ A • x` has finitely many fixed points exactly when
`det (1 - A) ≠ 0` (`AddCircle.finite_fixedPoints_generalLinearGroup_smul_iff`), and in all cases
their number, in the convention `Nat.card` of an infinite set being `0`, is `|det (1 - A)|`.

The derivative of `x ↦ A • x` is the matrix `A` at every point
(`AddCircle.mfderiv_generalLinearGroup_smul_apply`), so at every fixed point the fixed-point
derivative is `A` and `det (1 - df_x) = det (1 - A)`
(`AddCircle.det_id_sub_fixedPointDerivative_generalLinearGroup_smul`). Every fixed point is
therefore nondegenerate exactly when `det (1 - A) ≠ 0`, and then every fixed point has the same
Lefschetz sign `sgn det (1 - A)`. Since there are `|det (1 - A)|` of them, their signed count is

`∑_{A • x = x} sgn det (1 - df_x) = det (1 - A)`

(`AddCircle.finsum_sign_det_id_sub_fixedPointDerivative_generalLinearGroup_smul`). This is the
fixed-point side of the Lefschetz formula for linear automorphisms of a torus: `A` acts on
`H_k(Tⁿ; ℚ) = Λᵏ ℚⁿ` by `Λᵏ A`, and `∑ₖ (-1)ᵏ tr Λᵏ A = det (1 - A)` is its Lefschetz number. The
homological side is not formalized here.

The iterates of `x ↦ A • x` are `x ↦ Aⁿ • x`, so the map is nondegenerate up to period `N`
exactly when `det (1 - Aᵏ) ≠ 0` for `0 < k ≤ N`
(`AddCircle.isNondegenerateUpToPeriod_generalLinearGroup_smul_iff`); the point `0` is fixed by
every iterate, so the condition is also necessary. A hyperbolic matrix, such as Arnold's cat map
`!![2, 1; 1, 1]`, has no root of unity among its eigenvalues and gives a map nondegenerate up to
every period.

## Main results

* `AddCircle.generalLinearGroup_smul_coe_pi_eq_iff`: `[t]` is fixed by `A` exactly when `(1 - A) t`
  lies in `pℤⁿ`.
* `AddCircle.nat_card_fixedPoints_generalLinearGroup_smul`: there are `|det (1 - A)|` fixed points.
* `AddCircle.finite_fixedPoints_generalLinearGroup_smul_iff`: they are finite exactly when
  `det (1 - A) ≠ 0`.
* `AddCircle.det_id_sub_fixedPointDerivative_generalLinearGroup_smul`: `det (1 - df_x) =
  det (1 - A)` at every fixed point.
* `AddCircle.isNondegenerateFixedPt_generalLinearGroup_smul_iff`: a fixed point is nondegenerate
  exactly when `det (1 - A) ≠ 0`.
* `AddCircle.finsum_sign_det_id_sub_fixedPointDerivative_generalLinearGroup_smul`: for
  `det (1 - A) ≠ 0`, the signed count of the fixed points is `det (1 - A)`.
* `AddCircle.isNondegenerateUpToPeriod_generalLinearGroup_smul_iff`: nondegeneracy up to period
  `N` exactly when `det (1 - Aᵏ) ≠ 0` for `0 < k ≤ N`.

## References

* A. Katok and B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge University Press, 1995, Section 1.8 (hyperbolic toral automorphisms and the number of
  their periodic points).
-/

public section

noncomputable section

open Function Matrix TauCeti
open scoped Manifold

namespace AddCircle

variable (p : ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)`, `t ↦ ([t i])ᵢ`, as an additive map. -/
private def coePiHom : (ι → ℝ) →+ (ι → AddCircle p) :=
  AddMonoidHom.compLeft (QuotientAddGroup.mk' (AddSubgroup.zmultiples p)) ι

omit [Fintype ι] [DecidableEq ι] in
private theorem coePiHom_apply (t : ι → ℝ) : coePiHom p t = fun i ↦ (t i : AddCircle p) :=
  (rfl)

omit [Fintype ι] in
/-- The real matrix `1 - A` of an integer matrix `A`. -/
private theorem map_one_sub (A : Matrix ι ι ℤ) :
    (1 - A).map ((↑) : ℤ → ℝ) = 1 - A.map ((↑) : ℤ → ℝ) := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- The determinant of an integer matrix is that of the real matrix with the same entries. -/
private theorem det_map_intCast (A : Matrix ι ι ℤ) : (A.map ((↑) : ℤ → ℝ)).det = A.det := by
  simpa using ((Int.castRingHom ℝ).map_det A).symm

/-- **Fixed points through the covering map.** The point `[t]` of the torus is fixed by `A`
exactly when every coordinate of `(1 - A) t` is an integer multiple of `p`. -/
theorem generalLinearGroup_smul_coe_pi_eq_iff (A : GL ι ℤ) (t : ι → ℝ) :
    A • (fun i ↦ (t i : AddCircle p)) = (fun i ↦ (t i : AddCircle p)) ↔
      ∃ v : ι → ℤ, (1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)) *ᵥ t = fun i ↦ (v i : ℝ) * p := by
  rw [generalLinearGroup_smul_coe_pi, funext_iff]
  simp only [sub_mulVec, one_mulVec, Pi.sub_apply, funext_iff]
  refine ⟨fun h ↦ ?_, fun ⟨v, hv⟩ i ↦ ?_⟩
  · have hi (i : ι) : ∃ n : ℤ,
        (n : ℝ) * p = t i - ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ t) i := by
      obtain ⟨n, hn⟩ := (coe_eq_zero_iff (p := p)
        (x := t i - ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ t) i)).1
        (by rw [coe_sub, ← h i, sub_self])
      exact ⟨n, by rw [← zsmul_eq_mul, hn]⟩
    choose v hv using hi
    exact ⟨v, fun i ↦ (hv i).symm⟩
  · rw [← sub_eq_zero, ← coe_sub, coe_eq_zero_iff]
    exact ⟨-v i, by rw [zsmul_eq_mul, Int.cast_neg, neg_mul, ← hv i, neg_sub]⟩

variable [Fact (0 < p)]

/-- The fixed points of `x ↦ A • x` form an additive subgroup of the torus. -/
private def fixedSubgroup (A : GL ι ℤ) : AddSubgroup (ι → AddCircle p) :=
  (DistribSMul.toAddMonoidHom (ι → AddCircle p) A - AddMonoidHom.id _).ker

omit [Fact (0 < p)] in
private theorem mem_fixedSubgroup (A : GL ι ℤ) (x : ι → AddCircle p) :
    x ∈ fixedSubgroup p A ↔ A • x = x := by
  simp [fixedSubgroup, sub_eq_zero]

/-- When `det (1 - A) ≠ 0`, the integer vectors parametrize the fixed points by
`v ↦ [p (1 - A)⁻¹ v]`. -/
private def fixedParam (A : GL ι ℤ) : (ι → ℤ) →+ (ι → AddCircle p) :=
  (coePiHom p).comp <|
    (p • (1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))⁻¹.mulVecLin).toAddMonoidHom.comp
      (AddMonoidHom.compLeft (Int.castAddHom ℝ) ι)

omit [Fact (0 < p)] in
private theorem fixedParam_apply (A : GL ι ℤ) (v : ι → ℤ) :
    fixedParam p A v = fun i ↦
      ((p • ((1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))⁻¹ *ᵥ fun j ↦ (v j : ℝ))) i :
        AddCircle p) :=
  (rfl)

variable {p}

/-- For `det (1 - A) ≠ 0` the real matrix `1 - A` is invertible. -/
private theorem isUnit_det_one_sub_map {A : GL ι ℤ} (hA : (1 - (A : Matrix ι ι ℤ)).det ≠ 0) :
    IsUnit (1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)).det := by
  rw [← map_one_sub, det_map_intCast, isUnit_iff_ne_zero]
  exact_mod_cast hA

omit [Fact (0 < p)] in
private theorem range_fixedParam {A : GL ι ℤ} (hA : (1 - (A : Matrix ι ι ℤ)).det ≠ 0) :
    (fixedParam p A).range = fixedSubgroup p A := by
  have hu := isUnit_det_one_sub_map hA
  set M := 1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)
  -- `M (p M⁻¹ v) = p v` and, conversely, `M t = p v` gives `t = p M⁻¹ v`.
  have hM (v : ι → ℤ) (t : ι → ℝ) :
      (M *ᵥ t = fun i ↦ (v i : ℝ) * p) ↔ p • (M⁻¹ *ᵥ fun j ↦ (v j : ℝ)) = t := by
    have hv : (fun i ↦ (v i : ℝ) * p) = p • fun j ↦ (v j : ℝ) := by
      ext i
      simp [mul_comm]
    rw [hv]
    constructor
    · intro h
      rw [← mulVec_smul, ← h, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    · rintro rfl
      rw [mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  ext x
  rw [AddMonoidHom.mem_range, mem_fixedSubgroup]
  obtain ⟨t, rfl⟩ : ∃ t : ι → ℝ, (fun i ↦ (t i : AddCircle p)) = x :=
    ⟨fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose,
      funext fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose_spec⟩
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv, fixedParam_apply]
    exact (generalLinearGroup_smul_coe_pi_eq_iff p A _).2 ⟨v, (hM v _).2 rfl⟩
  · intro h
    obtain ⟨v, hv⟩ := (generalLinearGroup_smul_coe_pi_eq_iff p A t).1 h
    exact ⟨v, by rw [fixedParam_apply, (hM v t).1 hv]⟩

private theorem ker_fixedParam {A : GL ι ℤ} (hA : (1 - (A : Matrix ι ι ℤ)).det ≠ 0) :
    (fixedParam p A).ker = (LinearMap.range (1 - (A : Matrix ι ι ℤ)).mulVecLin).toAddSubgroup := by
  have hu := isUnit_det_one_sub_map hA
  have hp : p ≠ 0 := (Fact.out : 0 < p).ne'
  have hcast (k : ι → ℤ) : (1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)) *ᵥ (fun j ↦ (k j : ℝ)) =
      fun i ↦ (((1 - (A : Matrix ι ι ℤ)) *ᵥ k) i : ℝ) := by
    rw [← map_one_sub]
    ext i
    simp [mulVec, dotProduct]
  set M := 1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)
  ext v
  simp only [AddMonoidHom.mem_ker, fixedParam_apply, Submodule.mem_toAddSubgroup,
    LinearMap.mem_range, mulVecLin_apply, funext_iff, Pi.zero_apply, coe_eq_zero_iff,
    Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
  constructor
  · intro h
    choose k hk using h
    refine ⟨k, fun i ↦ ?_⟩
    have hk' : M⁻¹ *ᵥ (fun j ↦ (v j : ℝ)) = fun j ↦ (k j : ℝ) :=
      funext fun j ↦ mul_left_cancel₀ hp (by rw [← hk j, mul_comm])
    have := congrFun (hcast k) i
    rw [← hk', mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec] at this
    exact_mod_cast this.symm
  · rintro ⟨k, hk⟩ i
    obtain rfl : (1 - (A : Matrix ι ι ℤ)) *ᵥ k = v := funext hk
    refine ⟨k i, ?_⟩
    have : M⁻¹ *ᵥ (fun j ↦ (((1 - (A : Matrix ι ι ℤ)) *ᵥ k) j : ℝ)) = fun j ↦ (k j : ℝ) := by
      rw [← hcast, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    rw [this, mul_comm]

variable (p) in
/-- **The number of fixed points of a toral automorphism.** If `det (1 - A) ≠ 0`, the map
`x ↦ A • x` of the torus `ι → AddCircle p` has exactly `|det (1 - A)|` fixed points. -/
private theorem nat_card_fixedPoints_of_det_ne_zero {A : GL ι ℤ}
    (hA : (1 - (A : Matrix ι ι ℤ)).det ≠ 0) :
    Nat.card (fixedPoints fun x : ι → AddCircle p ↦ A • x) =
      (1 - (A : Matrix ι ι ℤ)).det.natAbs := by
  have hset : (fixedPoints fun x : ι → AddCircle p ↦ A • x) = (fixedSubgroup p A : Set _) := by
    ext x
    exact (mem_fixedSubgroup p A x).symm
  rw [hset, ← range_fixedParam hA, SetLike.coe_sort_coe,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (fixedParam p A)).toEquiv,
    ← AddSubgroup.index, ker_fixedParam hA,
    LinearMap.index_range_eq_natAbs_det_toMatrix (Pi.basisFun ℤ ι) (Pi.basisFun ℤ ι),
    LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

/-- If `det (1 - A) = 0`, the toral automorphism `x ↦ A • x` has infinitely many fixed points:
an integer vector `k ≠ 0` with `(1 - A) k = 0` gives the fixed points `[s k]` for `s ∈ ℝ`, which
are pairwise distinct for `0 ≤ s < p / |k i|` when `k i ≠ 0`. -/
private theorem infinite_fixedPoints_of_det_eq_zero {A : GL ι ℤ}
    (hA : (1 - (A : Matrix ι ι ℤ)).det = 0) :
    (fixedPoints fun x : ι → AddCircle p ↦ A • x).Infinite := by
  have hp : 0 < p := Fact.out
  obtain ⟨k, hk0, hk⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hA
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra! h
    exact hk0 (funext h)
  have hki : (0 : ℝ) < |(k i : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hi)
  set f : ℝ → ι → AddCircle p := fun s j ↦ ((s * k j : ℝ) : AddCircle p)
  -- Every `f s` is fixed, since `(1 - A) (s k) = s (1 - A) k = 0`.
  have hfix (s : ℝ) : f s ∈ fixedPoints fun x : ι → AddCircle p ↦ A • x := by
    refine (generalLinearGroup_smul_coe_pi_eq_iff p A _).2 ⟨0, ?_⟩
    have : (1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)) *ᵥ (fun j ↦ (k j : ℝ)) = 0 := by
      rw [← map_one_sub]
      ext j
      have := congrFun hk j
      simp only [mulVec, dotProduct, Pi.zero_apply, Matrix.map_apply] at this ⊢
      exact_mod_cast this
    have hsk : (fun j ↦ s * (k j : ℝ)) = s • fun j ↦ (k j : ℝ) := rfl
    rw [hsk, mulVec_smul, this, smul_zero]
    ext j
    simp
  -- `f` is injective on `[0, p / |k i|)`, an infinite set.
  have hinj : Set.InjOn f (Set.Ico 0 (p / |(k i : ℝ)|)) := by
    intro s hs s' hs' hss'
    have h := congrFun hss' i
    simp only [f] at h
    rw [← sub_eq_zero, ← coe_sub, coe_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    rw [zsmul_eq_mul, ← sub_mul] at hn
    have hlt : |(s - s') * (k i : ℝ)| < p := by
      rw [Set.mem_Ico, lt_div_iff₀ hki] at hs hs'
      have h1 := mul_nonneg hs.1 hki.le
      have h2 := mul_nonneg hs'.1 hki.le
      rw [abs_mul]
      rcases abs_cases (s - s') with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith
    have hn0 : n = 0 := by
      rw [← hn, abs_mul, abs_of_pos hp] at hlt
      have h1 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left hp).1 hlt
      rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h1
      exact Int.abs_lt_one_iff.1 h1
    rw [hn0, Int.cast_zero, zero_mul, eq_comm, mul_eq_zero] at hn
    exact sub_eq_zero.1 (hn.resolve_right (Int.cast_ne_zero.2 hi))
  exact ((Set.Ico_infinite (div_pos hp hki)).image hinj).mono (Set.image_subset_iff.2 fun s _ ↦
    hfix s)

variable (p)

/-- **Finitely many fixed points.** The toral automorphism `x ↦ A • x` has finitely many fixed
points exactly when `det (1 - A) ≠ 0`. -/
theorem finite_fixedPoints_generalLinearGroup_smul_iff (A : GL ι ℤ) :
    (fixedPoints fun x : ι → AddCircle p ↦ A • x).Finite ↔ (1 - (A : Matrix ι ι ℤ)).det ≠ 0 := by
  refine ⟨fun h hA ↦ infinite_fixedPoints_of_det_eq_zero hA h, fun hA ↦ ?_⟩
  refine Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero ?_)
  rw [nat_card_fixedPoints_of_det_ne_zero p hA]
  exact Int.natAbs_ne_zero.2 hA

/-- **The number of fixed points of a toral automorphism.** The map `x ↦ A • x` of the torus
`ι → AddCircle p` has `|det (1 - A)|` fixed points. When `det (1 - A) = 0` there are infinitely
many, and both sides are `0`. -/
theorem nat_card_fixedPoints_generalLinearGroup_smul (A : GL ι ℤ) :
    Nat.card (fixedPoints fun x : ι → AddCircle p ↦ A • x) =
      (1 - (A : Matrix ι ι ℤ)).det.natAbs := by
  by_cases hA : (1 - (A : Matrix ι ι ℤ)).det = 0
  · rw [hA, Int.natAbs_zero]
    exact Set.Infinite.card_eq_zero (infinite_fixedPoints_of_det_eq_zero hA)
  · exact nat_card_fixedPoints_of_det_ne_zero p hA

/-! ### Nondegeneracy and the Lefschetz signs -/

/-- At every fixed point of the toral automorphism `x ↦ A • x`, `det (1 - df_x) = det (1 - A)`. -/
theorem det_id_sub_fixedPointDerivative_generalLinearGroup_smul (A : GL ι ℤ)
    (x : {x : ι → AddCircle p // A • x = x}) :
    LinearMap.det (LinearMap.id -
        fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) x) =
      ((1 - (A : Matrix ι ι ℤ)).det : ℝ) := by
  have h : fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) x =
      Matrix.toLin' ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)) := LinearMap.ext fun v ↦ by
    rw [fixedPointDerivative_apply]
    exact (mfderiv_generalLinearGroup_smul_apply p A x.1 v).trans (Matrix.toLin'_apply _ v).symm
  have hdet : LinearMap.det (LinearMap.id -
      Matrix.toLin' ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)) : (ι → ℝ) →ₗ[ℝ] ι → ℝ) =
      ((1 - (A : Matrix ι ι ℤ)).det : ℝ) := by
    rw [← Matrix.toLin'_one, ← map_sub, LinearMap.det_toLin', ← map_one_sub, det_map_intCast]
  rw [h]
  -- The tangent spaces of the torus are `ι → ℝ`.
  exact hdet

/-- A fixed point of the toral automorphism `x ↦ A • x` is nondegenerate exactly when
`det (1 - A) ≠ 0`. -/
theorem isNondegenerateFixedPt_generalLinearGroup_smul_iff (A : GL ι ℤ) {x : ι → AddCircle p}
    (hx : A • x = x) :
    IsNondegenerateFixedPt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) x ↔
      (1 - (A : Matrix ι ι ℤ)).det ≠ 0 := by
  rw [isNondegenerateFixedPt_iff_det_id_sub_ne_zero (f := fun y ↦ A • y) ⟨x, hx⟩
    ((hasMFDerivAt_generalLinearGroup_smul p A x).mdifferentiableAt),
    det_id_sub_fixedPointDerivative_generalLinearGroup_smul p A ⟨x, hx⟩, Int.cast_ne_zero]

/-- **The signed count of the fixed points of a toral automorphism.** If `det (1 - A) ≠ 0`, the
fixed points of `x ↦ A • x`, each counted with its Lefschetz sign `sgn det (1 - df_x)`, add up to
`det (1 - A)`. This is the fixed-point side of the Lefschetz formula for `x ↦ A • x`. -/
theorem finsum_sign_det_id_sub_fixedPointDerivative_generalLinearGroup_smul (A : GL ι ℤ)
    (hA : (1 - (A : Matrix ι ι ℤ)).det ≠ 0) :
    ∑ᶠ x : {x : ι → AddCircle p // A • x = x}, (SignType.sign (LinearMap.det (LinearMap.id -
        fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) x)) : ℤ) =
      (1 - (A : Matrix ι ι ℤ)).det := by
  have : Finite {x : ι → AddCircle p // A • x = x} :=
    Set.finite_coe_iff.2 ((finite_fixedPoints_generalLinearGroup_smul_iff p A).2 hA)
  have : Fintype {x : ι → AddCircle p // A • x = x} := Fintype.ofFinite _
  simp_rw [det_id_sub_fixedPointDerivative_generalLinearGroup_smul, sign_intCast]
  -- The fixed-point subtype is the set of fixed points, of cardinality `|det (1 - A)|`.
  have hcard : Nat.card {x : ι → AddCircle p // A • x = x} =
      (1 - (A : Matrix ι ι ℤ)).det.natAbs :=
    nat_card_fixedPoints_generalLinearGroup_smul p A
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    hcard, nsmul_eq_mul, Int.natCast_natAbs, ← Int.sign_eq_sign, mul_comm]
  exact Int.sign_mul_abs _

/-- **Nondegeneracy up to a period.** The toral automorphism `x ↦ A • x` is nondegenerate up to
period `N` exactly when `det (1 - Aᵏ) ≠ 0` for every `0 < k ≤ N`. -/
theorem isNondegenerateUpToPeriod_generalLinearGroup_smul_iff (A : GL ι ℤ) (N : ℕ) :
    IsNondegenerateUpToPeriod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (fun x : ι → AddCircle p ↦ A • x) N ↔
      ∀ k, 0 < k → k ≤ N → (1 - (A : Matrix ι ι ℤ) ^ k).det ≠ 0 := by
  simp only [isNondegenerateUpToPeriod_iff, smul_iterate, IsPeriodicPt, IsFixedPt]
  constructor
  · intro h k hk hkN
    rw [← Units.val_pow_eq_pow_val]
    -- The point `0` is fixed by every iterate.
    exact (isNondegenerateFixedPt_generalLinearGroup_smul_iff p (A ^ k) (smul_zero _)).1
      (h hk hkN (smul_zero _))
  · intro h k hk hkN x hx
    refine (isNondegenerateFixedPt_generalLinearGroup_smul_iff p (A ^ k) hx).2 ?_
    rw [Units.val_pow_eq_pow_val]
    exact h k hk hkN

end AddCircle
