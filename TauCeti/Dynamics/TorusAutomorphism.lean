/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LefschetzNumber.Torus
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Zeta
import Mathlib.Algebra.CharP.Algebra
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.Topology.Instances.AddCircle.Torus

/-!
# Fixed points of linear automorphisms of a torus

Let `p > 0` and let `A ∈ GL(ι, ℤ)` act on the torus `Tⁿ = ι → AddCircle p` by `x ↦ A • x`
(`AddCircle.instDistribMulActionGeneralLinearGroup`). Through the covering map `t ↦ ([t i])ᵢ` this
is multiplication of real vectors by `A`, so `[t]` is fixed exactly when `(1 - A) t` has all its
coordinates in `pℤ`. The fixed points are the kernel of the map of the torus induced by the integer
matrix `1 - A` (`AddCircle.fixedPoints_generalLinearGroup_smul_eq_ker`), whose `Nat.card` is
`|det (1 - A)|` (`Matrix.natCard_ker_smulVecHom`). When `det (1 - A) ≠ 0` the fixed points form a
finite group isomorphic to `ℤⁿ / (1 - A) ℤⁿ`, with `|det (1 - A)|` elements
(`AddCircle.nat_card_fixedPoints_generalLinearGroup_smul`). When `det (1 - A) = 0` an integer vector
`k ≠ 0` with `(1 - A) k = 0` gives a circle of fixed points, so the fixed points are infinite
(`Matrix.infinite_ker_smulVecHom`). Hence `x ↦ A • x` has finitely many fixed points exactly when
`det (1 - A) ≠ 0` (`AddCircle.finite_fixedPoints_generalLinearGroup_smul_iff`), and in all cases
the `Nat.card` of the set of fixed points, `0` for an infinite set, is `|det (1 - A)|`. Applied to
`Aⁿ`, the map has finitely many periodic points of period `n` exactly when `det (1 - Aⁿ) ≠ 0`
(`AddCircle.finite_ptsOfPeriod_generalLinearGroup_smul_iff`).

The derivative of `x ↦ A • x` is the matrix `A` at every point
(`AddCircle.mfderiv_generalLinearGroup_smul_apply`), so at every fixed point the fixed-point
derivative is `A` and `det (1 - df_x) = det (1 - A)`
(`AddCircle.det_id_sub_fixedPointDerivative_generalLinearGroup_smul`). Every fixed point is
therefore nondegenerate exactly when `det (1 - A) ≠ 0`, and then every fixed point has the same
Lefschetz sign `sgn det (1 - A)`. Since there are `|det (1 - A)|` of them, their signed count is

`∑_{A • x = x} sgn det (1 - df_x) = det (1 - A)`

(`AddCircle.finsum_sign_det_id_sub_fixedPointDerivative_generalLinearGroup_smul`); when
`det (1 - A) = 0` every sign is `0` and both sides vanish. This is the
fixed-point side of the Lefschetz formula for linear automorphisms of a torus. On the homological
side, over a field `k` of characteristic zero, `A` acts on `H_r(Tⁿ; k) = Λʳ kⁿ` by `Λʳ A`, and
`∑ᵣ (-1)ʳ tr Λʳ A = det (1 - A)` is its Lefschetz number (`Matrix.lefschetzNumber_smulVecHom`). So
the Lefschetz fixed-point formula holds for every iterate of `x ↦ A • x` (`AddCircle.`
`finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber`),
and the Lefschetz zeta function of `x ↦ A • x` is its dynamical zeta function, built from the fixed
points of its iterates and their Lefschetz signs (`AddCircle.`
`lefschetzZeta_generalLinearGroup_smul_eq_subst_exp_finsum_sign_det_id_sub_fixedPointDerivative`).

On the two-torus `ι = Fin 2` these signed counts determine the dynamical zeta function
`ζ = exp (∑ₙ (∑_{φⁿ x = x} sgn det (1 - dφⁿ_x)) tⁿ / n)` of `φ(x) = A • x`. Since
`det (1 - Aⁿ) = 1 - tr (Aⁿ) + (det A)ⁿ` is the alternating sum of the traces of the actions of `φⁿ`
on `H₀`, `H₁` and `H₂` of the torus, `ζ` is the homological zeta function

`ζ = det (1 - t A) / ((1 - t) (1 - det A t))`

for every `A ∈ GL(2, ℤ)`, degenerate iterates included: for those, both sides of the `n`-th
Lefschetz identity vanish (`AddCircle.`
`subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_mul`).
For an area-preserving `A`, `det A = 1`, this is `det (1 - t A) / (1 - t) ^ 2`, whose coefficient of
`tⁿ` is `n det (1 - A)` for `n ≠ 0`. For the identity of the torus, all of whose points are
degenerate fixed points, and more generally whenever `det (1 - A) = 0`, the zeta function is `1`.

The iterates of `x ↦ A • x` are `x ↦ Aⁿ • x`, so the map is nondegenerate up to period `N`
exactly when `det (1 - Aᵏ) ≠ 0` for `0 < k ≤ N`
(`AddCircle.isNondegenerateUpToPeriod_generalLinearGroup_smul_iff`); the point `0` is fixed by
every iterate, so the condition is also necessary. A hyperbolic matrix, such as Arnold's cat map
`!![2, 1; 1, 1]`, has no root of unity among its eigenvalues and gives a map nondegenerate up to
every period.

## Main results

* `AddCircle.fixedPoints_generalLinearGroup_smul_eq_ker`: the fixed points are the kernel of the
  map of the torus induced by `1 - A`.
* `AddCircle.generalLinearGroup_smul_coe_pi_eq_iff`: `[t]` is fixed by `A` exactly when `(1 - A) t`
  lies in `pℤⁿ`.
* `AddCircle.nat_card_fixedPoints_generalLinearGroup_smul`: the set of fixed points has `Nat.card`
  equal to `|det (1 - A)|`.
* `AddCircle.finite_fixedPoints_generalLinearGroup_smul_iff`: they are finite exactly when
  `det (1 - A) ≠ 0`.
* `AddCircle.finite_ptsOfPeriod_generalLinearGroup_smul_iff`: the periodic points of period `n` are
  finite exactly when `det (1 - Aⁿ) ≠ 0`.
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
* `AddCircle.`
  `finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber`:
  the Lefschetz fixed-point formula for every iterate.
* `AddCircle.`
  `lefschetzZeta_generalLinearGroup_smul_eq_subst_exp_finsum_sign_det_id_sub_fixedPointDerivative`:
  the Lefschetz zeta function is the dynamical zeta function.
* `AddCircle.`
  `subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_mul`:
  the dynamical zeta function of a linear map of the two-torus is
  `det (1 - t A) / ((1 - t) (1 - det A t))`.
* `AddCircle.`
  `subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul`,
  `AddCircle.`
  `coeff_subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul`:
  for `det A = 1` it is `det (1 - t A) / (1 - t) ^ 2`, with coefficients `n det (1 - A)` for
  `n ≠ 0`.

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

/-- The fixed points of `x ↦ A • x` are the kernel of the map of the torus induced by the integer
matrix `1 - A`. -/
theorem fixedPoints_generalLinearGroup_smul_eq_ker (A : GL ι ℤ) :
    (fixedPoints fun x : ι → AddCircle p ↦ A • x) =
      ((1 - (A : Matrix ι ι ℤ)).smulVecHom (AddCircle p) :
        (ι → AddCircle p) →+ (ι → AddCircle p)).ker := by
  ext x
  simp [IsFixedPt, smulVecHom_sub_apply, sub_eq_zero, generalLinearGroup_smul_eq_smulVecHom,
    eq_comm (a := x)]

/-- **Fixed points through the covering map.** The point `[t]` of the torus is fixed by `A`
exactly when every coordinate of `(1 - A) t` is an integer multiple of `p`. -/
theorem generalLinearGroup_smul_coe_pi_eq_iff (A : GL ι ℤ) (t : ι → ℝ) :
    A • (fun i ↦ (t i : AddCircle p)) = (fun i ↦ (t i : AddCircle p)) ↔
      ∃ v : ι → ℤ, (1 - (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)) *ᵥ t = fun i ↦ (v i : ℝ) * p := by
  rw [← mem_fixedPoints_iff (f := fun x ↦ A • x), fixedPoints_generalLinearGroup_smul_eq_ker,
    SetLike.mem_coe, coe_mem_ker_smulVecHom_iff, map_one_sub]

/-- **Finitely many fixed points.** The toral automorphism `x ↦ A • x` has finitely many fixed
points exactly when `det (1 - A) ≠ 0`. -/
theorem finite_fixedPoints_generalLinearGroup_smul_iff (A : GL ι ℤ) :
    (fixedPoints fun x : ι → AddCircle p ↦ A • x).Finite ↔ (1 - (A : Matrix ι ι ℤ)).det ≠ 0 := by
  rw [fixedPoints_generalLinearGroup_smul_eq_ker, ← Set.finite_coe_iff, SetLike.coe_sort_coe,
    finite_ker_smulVecHom_iff]

/-- **Finitely many periodic points of a given period.** The toral automorphism `x ↦ A • x` has
finitely many periodic points of period `n` exactly when `det (1 - Aⁿ) ≠ 0`. -/
theorem finite_ptsOfPeriod_generalLinearGroup_smul_iff (A : GL ι ℤ) (n : ℕ) :
    (ptsOfPeriod (fun x : ι → AddCircle p ↦ A • x) n).Finite ↔
      (1 - (A : Matrix ι ι ℤ) ^ n).det ≠ 0 := by
  -- The periodic points of period `n` are the fixed points of `x ↦ Aⁿ • x`.
  have h : ptsOfPeriod (fun x : ι → AddCircle p ↦ A • x) n = fixedPoints fun x ↦ (A ^ n) • x := by
    ext x
    simp [IsPeriodicPt, IsFixedPt, smul_iterate]
  rw [h, finite_fixedPoints_generalLinearGroup_smul_iff, Units.val_pow_eq_pow_val]

/-- **The number of fixed points of a toral automorphism.** For `p ≠ 0`, the set of fixed points of
the map `x ↦ A • x` of the torus `ι → AddCircle p` has `Nat.card` equal to `|det (1 - A)|`. When
`det (1 - A) ≠ 0` there are exactly `|det (1 - A)|` fixed points; when `det (1 - A) = 0` there are
infinitely many, and both sides are `0`. -/
theorem nat_card_fixedPoints_generalLinearGroup_smul (A : GL ι ℤ) (hp : p ≠ 0) :
    Nat.card (fixedPoints fun x : ι → AddCircle p ↦ A • x) =
      (1 - (A : Matrix ι ι ℤ)).det.natAbs := by
  rw [fixedPoints_generalLinearGroup_smul_eq_ker, SetLike.coe_sort_coe,
    natCard_ker_smulVecHom p _ hp]

variable [Fact (0 < p)]

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
    (Nat.card_congr e).trans
      (nat_card_fixedPoints_generalLinearGroup_smul p A (Fact.out : 0 < p).ne')
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

/-! ### The zeta function of a linear map of the two-torus -/

section FinTwo

/-- The signed fixed-point count of the `n`-th iterate of `x ↦ A • x` on the two-torus, as a
rational number, is `det (1 - Bⁿ)` for the rational matrix `B` of `A`. -/
private theorem intCast_finsum_sign_det_id_sub_fixedPointDerivative_iterate (A : GL (Fin 2) ℤ)
    (n : ℕ) :
    ((∑ᶠ x : {x : Fin 2 → AddCircle p // (fun y ↦ A • y)^[n] x = x},
        (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
          (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (fun y ↦ A • y)^[n] x)) : ℤ) : ℤ) : ℚ) =
      (1 - ((A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) ^ n).det := by
  rw [finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul,
    Matrix.intCast_det_one_sub, Matrix.map_pow]

/-- **The dynamical zeta function of a linear map of the two-torus.** Let `A ∈ GL(2, ℤ)` act on
the torus `Fin 2 → AddCircle p` by `φ(x) = A • x`. Its dynamical zeta function
`ζ = exp (∑ₙ (∑_{φⁿ x = x} sgn det (1 - dφⁿ_x)) tⁿ / n)`, built from the fixed points of the
iterates and their Lefschetz signs, is the homological zeta function

`ζ = det (1 - t A) / ((1 - t) (1 - det A t))`,

stated without inverses. The three factors are the actions of `φ` on `H₁`, `H₀` and `H₂` of the
torus. No hypothesis on `A` is needed: when an iterate is degenerate, `det (1 - Aⁿ) = 0`, every
fixed point of `φⁿ` has sign `0`, and both sides of the `n`-th Lefschetz identity vanish. -/
theorem subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_mul
    (A : GL (Fin 2) ℤ) :
    (PowerSeries.exp ℚ).subst (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ •
        ((∑ᶠ x : {x : Fin 2 → AddCircle p // (fun y ↦ A • y)^[n] x = x},
          (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
            (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (fun y ↦ A • y)^[n] x)) : ℤ) : ℤ) : ℚ)) *
        ((1 - PowerSeries.X) *
          (1 - PowerSeries.C (((A : Matrix (Fin 2) (Fin 2) ℤ).det : ℤ) : ℚ) * PowerSeries.X)) =
      (((A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)).charpolyRev : PowerSeries ℚ) := by
  simp_rw [intCast_finsum_sign_det_id_sub_fixedPointDerivative_iterate]
  rw [Int.cast_det]
  exact Matrix.subst_exp_det_one_sub_pow_mul_fin_two _

/-- **The dynamical zeta function of an area-preserving linear map of the two-torus.** For
`A ∈ SL(2, ℤ)` acting on the torus, the dynamical zeta function is
`ζ = det (1 - t A) / (1 - t) ^ 2`. -/
theorem subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul
    {A : GL (Fin 2) ℤ} (hA : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1) :
    (PowerSeries.exp ℚ).subst (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ •
        ((∑ᶠ x : {x : Fin 2 → AddCircle p // (fun y ↦ A • y)^[n] x = x},
          (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
            (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (fun y ↦ A • y)^[n] x)) : ℤ) : ℤ) : ℚ)) =
      (((A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)).charpolyRev : PowerSeries ℚ) *
        PowerSeries.mk 1 ^ 2 := by
  simp_rw [intCast_finsum_sign_det_id_sub_fixedPointDerivative_iterate]
  exact Matrix.subst_exp_det_one_sub_pow_fin_two_of_det_eq_one
    ((Int.castRingHom ℚ).det_map_eq_one hA)

/-- **The coefficients of the dynamical zeta function of an area-preserving linear map of the
two-torus.** For `A ∈ SL(2, ℤ)` acting on the torus and `n ≠ 0`, the coefficient of `tⁿ` in the
dynamical zeta function is `n det (1 - A)`. In particular, when `det (1 - A) = 0`, as for the
identity of the torus, whose fixed points are all degenerate, the zeta function is `1`. -/
theorem coeff_subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul
    {A : GL (Fin 2) ℤ} (hA : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n ((PowerSeries.exp ℚ).subst (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ •
        ((∑ᶠ x : {x : Fin 2 → AddCircle p // (fun y ↦ A • y)^[n] x = x},
          (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
            (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (fun y ↦ A • y)^[n] x)) : ℤ) : ℤ) : ℚ))) =
      n * (1 - (A : Matrix (Fin 2) (Fin 2) ℤ)).det := by
  simp_rw [intCast_finsum_sign_det_id_sub_fixedPointDerivative_iterate]
  rw [Matrix.coeff_subst_exp_det_one_sub_pow_fin_two_of_det_eq_one
    ((Int.castRingHom ℚ).det_map_eq_one hA) hn, Matrix.intCast_det_one_sub]

end FinTwo

end AddCircle

/-! ### The Lefschetz fixed-point formula -/

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The Lefschetz fixed-point formula for the iterates of a toral automorphism.** For
`A ∈ GL(ι, ℤ)` acting on the torus `ι → AddCircle p` by `φ(x) = A • x` and a field `k` of
characteristic zero, the signed count of the fixed points of the `n`-th iterate `φⁿ`, each with its
Lefschetz sign `sgn det (1 - dφⁿ_x)`, is the Lefschetz number of `φⁿ`: both are `det (1 - Aⁿ)`. No
nondegeneracy is needed: when `det (1 - Aⁿ) = 0`, every sign is `0` and both sides vanish. -/
theorem
    finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber
    (k : Type) [Field k] [CharZero k] (A : GL ι ℤ) (n : ℕ) :
    ((∑ᶠ x : {x : ι → AddCircle p // (fun y ↦ A • y)^[n] x = x},
      (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y)^[n] x)) : ℤ) : ℤ) : k) =
      (⟨(fun y ↦ A • y)^[n], (continuous_const_smul A).iterate n⟩ :
        C(ι → AddCircle p, ι → AddCircle p)).lefschetzNumber k := by
  -- `φ` is the map `x ↦ A • x` induced by the matrix `A`
  have h : (⟨(fun y ↦ A • y)^[n], (continuous_const_smul A).iterate n⟩ :
      C(ι → AddCircle p, ι → AddCircle p)) =
      ⟨(⇑((A : Matrix ι ι ℤ).smulVecHom (AddCircle p)))^[n],
        ((A : Matrix ι ι ℤ).smulVecHom (AddCircle p)).continuous.iterate n⟩ :=
    ContinuousMap.ext fun x ↦ congrFun (congrArg (·^[n])
      (funext (generalLinearGroup_smul_eq_smulVecHom p A))) x
  rw [finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul, h,
    Matrix.lefschetzNumber_iterate_smulVecHom _ k (Fact.out : 0 < p).ne']

/-- **The Lefschetz zeta function of a toral automorphism is its dynamical zeta function.** For
`A ∈ GL(ι, ℤ)` acting on the torus `ι → AddCircle p` by `φ(x) = A • x` and a field `k` of
characteristic zero, the Lefschetz zeta function `exp (∑ₙ L(φⁿ) tⁿ / n)` of `φ` is
`exp (∑ₙ (∑_{φⁿ x = x} sgn det (1 - dφⁿ_x)) tⁿ / n)`, built from the fixed points of the iterates
of `φ` and their Lefschetz signs. -/
theorem
    lefschetzZeta_generalLinearGroup_smul_eq_subst_exp_finsum_sign_det_id_sub_fixedPointDerivative
    (k : Type) [Field k] [Algebra ℚ k] (A : GL ι ℤ) :
    (⟨fun y ↦ A • y, continuous_const_smul A⟩ :
        C(ι → AddCircle p, ι → AddCircle p)).lefschetzZeta k =
      (PowerSeries.exp k).subst (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ •
        ((∑ᶠ x : {x : ι → AddCircle p // (fun y ↦ A • y)^[n] x = x},
          (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
            (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y)^[n] x)) : ℤ) : ℤ) : k)) := by
  have := algebraRat.charZero k
  simp_rw [ContinuousMap.lefschetzZeta_def, ContinuousMap.coe_mk,
    finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber]

end AddCircle
