/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import TauCeti.Topology.Instances.AddCircle.Torus

/-!
# Fixed points of linear automorphisms of a torus

Let `p > 0` and let `A ∈ GL(ι, ℤ)` act on the torus `Tⁿ = ι → AddCircle p` by
`x ↦ A • x` (`AddCircle.instDistribMulActionGeneralLinearGroup`). Through the covering map
`t ↦ ([t i])ᵢ` this is multiplication of real vectors by `A`, so `[t]` is fixed exactly when
`(1 - A) t` has all its coordinates in `pℤ`. The fixed points are the kernel of the map of the
torus induced by the integer matrix `1 - A`, which has `|det (1 - A)|` points
(`Matrix.natCard_ker_smulVecHom`): when `det (1 - A) ≠ 0` the fixed points form a group
isomorphic to `ℤⁿ / (1 - A) ℤⁿ`, of order `|det (1 - A)|`
(`AddCircle.nat_card_fixedPoints_generalLinearGroup_smul`), and when `det (1 - A) = 0` an integer
vector `k ≠ 0` with `(1 - A) k = 0` gives a circle of fixed points, so the fixed points are
infinite (`Matrix.infinite_ker_smulVecHom`). Hence `x ↦ A • x` has finitely many fixed points
exactly when `det (1 - A) ≠ 0` (`AddCircle.finite_fixedPoints_generalLinearGroup_smul_iff`), and in
all cases their number, in the convention `Nat.card` of an infinite set being `0`, is
`|det (1 - A)|`.

The derivative of `x ↦ A • x` is the matrix `A` at every point
(`AddCircle.mfderiv_generalLinearGroup_smul_apply`), so at every fixed point the fixed-point
derivative is `A` and `det (1 - df_x) = det (1 - A)`
(`AddCircle.det_id_sub_fixedPointDerivative_generalLinearGroup_smul`). Every fixed point is
therefore nondegenerate exactly when `det (1 - A) ≠ 0`, and then every fixed point has the same
Lefschetz sign `sgn det (1 - A)`. Since there are `|det (1 - A)|` of them, their signed count is

`∑_{A • x = x} sgn det (1 - df_x) = det (1 - A)`

(`AddCircle.finsum_sign_det_id_sub_fixedPointDerivative_generalLinearGroup_smul`); when
`det (1 - A) = 0` every sign is `0` and both sides vanish. This is the
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
* `AddCircle.finsum_sign_det_id_sub_fixedPointDerivative_generalLinearGroup_smul`: the signed
  count of the fixed points is `det (1 - A)`.
* `AddCircle.finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul`: the
  signed count of the fixed points of the `n`-th iterate is `det (1 - Aⁿ)`.
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

omit [Fintype ι] in
/-- The real matrix `1 - A` of an integer matrix `A`. -/
private theorem map_one_sub (A : Matrix ι ι ℤ) :
    (1 - A).map ((↑) : ℤ → ℝ) = 1 - A.map ((↑) : ℤ → ℝ) := by
  rw [Matrix.map_sub _ Int.cast_sub, Matrix.map_one _ Int.cast_zero Int.cast_one]

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

omit [Fact (0 < p)] in
/-- The fixed points of `x ↦ A • x` are the kernel of the map of the torus induced by the integer
matrix `1 - A`. -/
private theorem fixedPoints_generalLinearGroup_smul_eq_ker (A : GL ι ℤ) :
    (fixedPoints fun x : ι → AddCircle p ↦ A • x) =
      ((1 - (A : Matrix ι ι ℤ)).smulVecHom (AddCircle p)).toAddMonoidHom.ker := by
  ext x
  rw [mem_fixedPoints_iff, SetLike.mem_coe, AddMonoidHom.mem_ker,
    ContinuousAddMonoidHom.coe_toAddMonoidHom, AddMonoidHom.coe_ofClass, smulVecHom_sub_apply,
    smulVecHom_one, ContinuousAddMonoidHom.coe_id, id_eq, sub_eq_zero,
    generalLinearGroup_smul_eq_smulVecHom, eq_comm]

/-- **Finitely many fixed points.** The toral automorphism `x ↦ A • x` has finitely many fixed
points exactly when `det (1 - A) ≠ 0`. -/
theorem finite_fixedPoints_generalLinearGroup_smul_iff (A : GL ι ℤ) :
    (fixedPoints fun x : ι → AddCircle p ↦ A • x).Finite ↔ (1 - (A : Matrix ι ι ℤ)).det ≠ 0 := by
  rw [fixedPoints_generalLinearGroup_smul_eq_ker, ← Set.finite_coe_iff, SetLike.coe_sort_coe]
  refine ⟨fun h hA ↦ not_finite_iff_infinite.2 (infinite_ker_smulVecHom p hA) h,
    fun hA ↦ Nat.finite_of_card_ne_zero ?_⟩
  rw [natCard_ker_smulVecHom p _ (Fact.out : 0 < p).ne']
  exact Int.natAbs_ne_zero.2 hA

/-- **The number of fixed points of a toral automorphism.** The map `x ↦ A • x` of the torus
`ι → AddCircle p` has `|det (1 - A)|` fixed points. When `det (1 - A) = 0` there are infinitely
many, and both sides are `0`. -/
theorem nat_card_fixedPoints_generalLinearGroup_smul (A : GL ι ℤ) :
    Nat.card (fixedPoints fun x : ι → AddCircle p ↦ A • x) =
      (1 - (A : Matrix ι ι ℤ)).det.natAbs := by
  rw [fixedPoints_generalLinearGroup_smul_eq_ker, SetLike.coe_sort_coe,
    natCard_ker_smulVecHom p _ (Fact.out : 0 < p).ne']

/-! ### Nondegeneracy and the Lefschetz signs -/

/-- At every fixed point of the toral automorphism `x ↦ A • x`, `det (1 - df_x) = det (1 - A)`. -/
theorem det_id_sub_fixedPointDerivative_generalLinearGroup_smul (A : GL ι ℤ)
    (x : {x : ι → AddCircle p // A • x = x}) :
    LinearMap.det (LinearMap.id -
        fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) x) =
      ((1 - (A : Matrix ι ι ℤ)).det : ℝ) := by
  have h := (hasMFDerivAt_generalLinearGroup_smul p A x.val).fixedPointDerivative_eq (x := x)
  have hdet : LinearMap.det (LinearMap.id -
      (LinearMap.toContinuousLinearMap (Matrix.toLin' ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))) :
        (ι → ℝ) →ₗ[ℝ] ι → ℝ)) = ((1 - (A : Matrix ι ι ℤ)).det : ℝ) := by
    rw [LinearMap.coe_toContinuousLinearMap, ← Matrix.toLin'_one, ← map_sub,
      LinearMap.det_toLin', ← map_one_sub, ← Int.cast_det]
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

/-- **The signed count of the fixed points of a toral automorphism.** The fixed points of
`x ↦ A • x`, each counted with its Lefschetz sign `sgn det (1 - df_x)`, add up to `det (1 - A)`.
This is the fixed-point side of the Lefschetz formula for `x ↦ A • x`. When `det (1 - A) = 0`,
every sign is `0` and both sides are `0`. -/
theorem finsum_sign_det_id_sub_fixedPointDerivative_generalLinearGroup_smul (A : GL ι ℤ) :
    ∑ᶠ x : {x : ι → AddCircle p // A • x = x}, (SignType.sign (LinearMap.det (LinearMap.id -
        fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) x)) : ℤ) =
      (1 - (A : Matrix ι ι ℤ)).det := by
  simp_rw [det_id_sub_fixedPointDerivative_generalLinearGroup_smul, sign_intCast]
  by_cases hA : (1 - (A : Matrix ι ι ℤ)).det = 0
  · simp [hA]
  -- The fixed-point subtype is the set of fixed points, finite of cardinality `|det (1 - A)|`.
  let e : {x : ι → AddCircle p // A • x = x} ≃ fixedPoints fun x : ι → AddCircle p ↦ A • x :=
    Equiv.subtypeEquivRight fun _ ↦ mem_fixedPoints_iff.symm
  have : Finite (fixedPoints fun x : ι → AddCircle p ↦ A • x) :=
    Set.finite_coe_iff.2 ((finite_fixedPoints_generalLinearGroup_smul_iff p A).2 hA)
  have : Finite {x : ι → AddCircle p // A • x = x} := .of_equiv _ e.symm
  have : Fintype {x : ι → AddCircle p // A • x = x} := Fintype.ofFinite _
  have hcard : Nat.card {x : ι → AddCircle p // A • x = x} =
      (1 - (A : Matrix ι ι ℤ)).det.natAbs :=
    (Nat.card_congr e).trans (nat_card_fixedPoints_generalLinearGroup_smul p A)
  -- A constant sum of `sgn d` over `|d|` points is `|d| sgn d = d`.
  simp [finsum_eq_sum_of_fintype, ← Nat.card_eq_fintype_card, hcard]

/-- **The signed fixed-point counts of the iterates of a toral automorphism.** The fixed points of
the `n`-th iterate of `x ↦ A • x`, each counted with its Lefschetz sign, add up to
`det (1 - Aⁿ)`. -/
theorem finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul (A : GL ι ℤ)
    (n : ℕ) :
    ∑ᶠ x : {x : ι → AddCircle p // (fun y ↦ A • y)^[n] x = x},
        (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
          (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y)^[n] x)) : ℤ) =
      (1 - (A : Matrix ι ι ℤ) ^ n).det := by
  rw [smul_iterate, finsum_sign_det_id_sub_fixedPointDerivative_generalLinearGroup_smul,
    Units.val_pow_eq_pow_val]

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
