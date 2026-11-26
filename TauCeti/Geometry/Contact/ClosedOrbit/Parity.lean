/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ClosedOrbit.Basic
import TauCeti.Geometry.Symplectic.Darboux.Basis
import TauCeti.LinearAlgebra.Matrix.Charpoly.DetSign

/-!
# The parity of closed Reeb orbits and the even-cover criterion

Let `α` be a contact form with complete Reeb flow, and let `γ` be a closed Reeb orbit with
linearized return map `A_γ` on the contact hyperplane `ξ = ker α`. The characteristic polynomial
of `A_γ` does not depend on the periodic trajectory representing `γ`
(`TauCeti.SmoothForm.IsContactForm.returnCharpoly`), and neither does the sign of
`det (1 - A_γ)`. This sign is the **parity** of `γ`
(`TauCeti.SmoothForm.IsContactForm.orbitParity`): it is nonzero exactly when `γ` is
nondegenerate, and then equals `(-1) ^ i₊`, where `i₊` is the number of real eigenvalues of
`A_γ` in `(1, ∞)`, counted with algebraic multiplicity. In a trivialization of `ξ` along `γ`, the
linearized Reeb flow is a path of symplectic matrices from the identity to a matrix conjugate to
`A_γ`, so when `ξ` has dimension `2n - 2` the matrix identity
`TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq_of_one` identifies this sign with
`(-1) ^ (CZ(γ) + n - 3)`; this file uses no trivialization.

The parity of an iterate is governed by the eigenvalues of `A_γ` in `(-1, 0)`. Write `N_γ` for
their number, counted with algebraic multiplicity. If the `k`-fold iterate `γ^k` is nondegenerate,
then

`parity (γ^k) = parity (γ) * (-1) ^ ((k + 1) N_γ)`

(`TauCeti.SmoothForm.IsContactForm.orbitParity_iterate`). The sign formula
`LinearMap.sign_det_one_sub_pow` expresses the parity of `γ^k` through the eigenvalues in
`(-∞, -1)` instead; the two counts have the same parity because `det A_γ = 1`, the return map being
a linear symplectomorphism of `(ξ, dα)` (`LinearMap.neg_one_pow_card_filter_lt_neg_one_of_det_pos`).
Hence the parity of `γ^k` differs from that of `γ` exactly when `k` is even and `N_γ` is odd
(`TauCeti.SmoothForm.IsContactForm.orbitParity_iterate_ne_iff`). Applied to the primitive orbit
underlying `γ`, this is the even-cover criterion of Eliashberg–Givental–Hofer and Pardon: a
nondegenerate closed Reeb orbit has a parity different from that of its underlying simple orbit if
and only if its multiplicity is even and the return map of the simple orbit has an odd number of
eigenvalues in `(-1, 0)`
(`TauCeti.SmoothForm.IsContactForm.orbitParity_ne_orbitParity_primitive_iff`).
Eliashberg–Givental–Hofer call these orbits bad; the description of bad orbits through the action
of the covering group on orientation lines is not formalized here. For example, in dimension three
the double cover of a negative hyperbolic orbit, with eigenvalues `λ ∈ (-1, 0)` and `1 / λ`,
changes parity, while the double covers of elliptic and positive hyperbolic orbits do not.

## Main definitions

* `TauCeti.SmoothForm.IsContactForm.returnCharpoly`: the characteristic polynomial of the
  linearized return map of a closed Reeb orbit.
* `TauCeti.SmoothForm.IsContactForm.orbitParity`: the sign of `det (1 - A_γ)`.

## Main results

* `TauCeti.SmoothForm.IsContactForm.orbitParity_ne_zero_iff`: the parity is nonzero exactly for
  nondegenerate orbits.
* `TauCeti.SmoothForm.IsContactForm.det_periodicLinearizedReturn`: the return map has
  determinant `1`.
* `TauCeti.SmoothForm.IsContactForm.orbitParity_eq_neg_one_pow`: the parity is `(-1) ^ i₊`.
* `TauCeti.SmoothForm.IsContactForm.orbitParity_iterate`: the parity of an iterate.
* `TauCeti.SmoothForm.IsContactForm.orbitParity_iterate_ne_iff` and
  `TauCeti.SmoothForm.IsContactForm.orbitParity_ne_orbitParity_primitive_iff`: the even-cover
  criterion.

## References

* Y. Eliashberg, A. Givental and H. Hofer, *Introduction to symplectic field theory*, Geom. Funct.
  Anal. (2000), Special Volume, Part II, 560–673, Lemma 1.8.8 and Remark 1.9.2.
* J. Pardon, *Contact homology and virtual fundamental cycles*, J. Amer. Math. Soc. **32**
  (2019), 825–919, Definitions 2.48 and 2.49 and (2.59).
-/

public section

open Polynomial
open scoped ContDiff

namespace TauCeti.SmoothForm

namespace IsContactForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)

/-- The characteristic polynomial of the linearized Reeb return map of a closed Reeb orbit `γ` on
the contact hyperplane, common to all periodic trajectories representing `γ`. -/
noncomputable def returnCharpoly (γ : Flow.ClosedOrbit (hα.reebFlow hc)) : ℝ[X] :=
  (hα.periodicLinearizedReturn hc (Flow.ClosedOrbit.mk_surjective γ).choose).charpoly

@[simp]
theorem returnCharpoly_mk (δ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    hα.returnCharpoly hc (Flow.ClosedOrbit.mk δ) = (hα.periodicLinearizedReturn hc δ).charpoly :=
  hα.charpoly_periodicLinearizedReturn_eq_of_mk_eq hc (Flow.ClosedOrbit.mk_surjective _).choose_spec

/-- The return map of the `k`-fold iterate of a closed Reeb orbit has the characteristic
polynomial of the `k`-th power of the return map of the orbit. -/
theorem returnCharpoly_iterate_mk (δ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) :
    hα.returnCharpoly hc ((Flow.ClosedOrbit.mk δ).iterate k) =
      (hα.periodicLinearizedReturn hc δ ^ (k : ℕ)).charpoly := by
  rw [Flow.ClosedOrbit.iterate_mk, returnCharpoly_mk,
    hα.charpoly_periodicLinearizedReturn_iterate hc δ k]

/-- A closed Reeb orbit is nondegenerate exactly when `1` is not a root of the characteristic
polynomial of its return map. -/
theorem isNondegenerateOrbit_iff_eval_one_returnCharpoly_ne_zero
    (γ : Flow.ClosedOrbit (hα.reebFlow hc)) :
    hα.IsNondegenerateOrbit hc γ ↔ (hα.returnCharpoly hc γ).eval 1 ≠ 0 := by
  induction γ using Flow.ClosedOrbit.ind with | h δ => _
  rw [isNondegenerateOrbit_mk_iff, returnCharpoly_mk, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    IsRoot.def]

/-- The **parity** of a closed Reeb orbit `γ`: the sign of `det (1 - A_γ)` for its linearized
return map `A_γ` on the contact hyperplane. It is nonzero exactly when `γ` is nondegenerate. -/
noncomputable def orbitParity (γ : Flow.ClosedOrbit (hα.reebFlow hc)) : SignType :=
  SignType.sign ((hα.returnCharpoly hc γ).eval 1)

/-- The parity of a closed Reeb orbit is the sign of the characteristic polynomial of its return
map evaluated at `1`. -/
theorem orbitParity_def (γ : Flow.ClosedOrbit (hα.reebFlow hc)) :
    hα.orbitParity hc γ = SignType.sign ((hα.returnCharpoly hc γ).eval 1) :=
  (rfl)

/-- The parity of the closed orbit of a periodic Reeb trajectory `δ` is the sign of
`det (1 - A_δ)`. -/
@[simp]
theorem orbitParity_mk (δ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    hα.orbitParity hc (Flow.ClosedOrbit.mk δ) =
      SignType.sign (1 - hα.periodicLinearizedReturn hc δ).det := by
  rw [orbitParity_def, returnCharpoly_mk, LinearMap.eval_charpoly, map_one]

/-- The parity of the `k`-fold iterate of the closed orbit of a periodic Reeb trajectory `δ` is the
sign of `det (1 - A_δ ^ k)`. -/
theorem orbitParity_iterate_mk (δ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) :
    hα.orbitParity hc ((Flow.ClosedOrbit.mk δ).iterate k) =
      SignType.sign (1 - hα.periodicLinearizedReturn hc δ ^ (k : ℕ)).det := by
  rw [orbitParity_def, returnCharpoly_iterate_mk, LinearMap.eval_charpoly, map_one]

/-- The parity of a closed Reeb orbit is nonzero exactly when the orbit is nondegenerate. -/
theorem orbitParity_ne_zero_iff (γ : Flow.ClosedOrbit (hα.reebFlow hc)) :
    hα.orbitParity hc γ ≠ 0 ↔ hα.IsNondegenerateOrbit hc γ := by
  rw [orbitParity_def, sign_ne_zero, isNondegenerateOrbit_iff_eval_one_returnCharpoly_ne_zero]

/-- The closed orbit of a periodic Reeb trajectory `δ` is nondegenerate exactly when
`det (1 - A_δ) ≠ 0`. -/
theorem isNondegenerateOrbit_mk_iff_det_one_sub_ne_zero
    (δ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    hα.IsNondegenerateOrbit hc (Flow.ClosedOrbit.mk δ) ↔
      (1 - hα.periodicLinearizedReturn hc δ).det ≠ 0 := by
  rw [← orbitParity_ne_zero_iff, orbitParity_mk, sign_ne_zero]

/-- The `k`-fold iterate of the closed orbit of a periodic Reeb trajectory `δ` is nondegenerate
exactly when `det (1 - A_δ ^ k) ≠ 0`. -/
theorem isNondegenerateOrbit_iterate_mk_iff_det_one_sub_ne_zero
    (δ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) :
    hα.IsNondegenerateOrbit hc ((Flow.ClosedOrbit.mk δ).iterate k) ↔
      (1 - hα.periodicLinearizedReturn hc δ ^ (k : ℕ)).det ≠ 0 := by
  rw [← orbitParity_ne_zero_iff, orbitParity_iterate_mk, sign_ne_zero]

/-- The linearized return map of a periodic Reeb trajectory is a linear symplectomorphism of the
contact hyperplane, so its determinant is `1`. -/
@[simp]
theorem det_periodicLinearizedReturn (δ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    (hα.periodicLinearizedReturn hc δ).det = 1 := by
  rw [periodicLinearizedReturn_def, ← toLinearMap_linearizedReebReturnEquiv]
  exact (hα.isSymplectomorphism_linearizedReebReturnEquiv _ _).det_eq_one

/-- The parity of a nondegenerate closed Reeb orbit is `(-1) ^ i₊`, where `i₊` is the number of
real eigenvalues of its return map in `(1, ∞)`, counted with algebraic multiplicity. -/
theorem orbitParity_eq_neg_one_pow {γ : Flow.ClosedOrbit (hα.reebFlow hc)}
    (hγ : hα.IsNondegenerateOrbit hc γ) :
    hα.orbitParity hc γ = (-1) ^ ((hα.returnCharpoly hc γ).roots.filter (1 < ·)).card := by
  induction γ using Flow.ClosedOrbit.ind with | h δ => _
  rw [isNondegenerateOrbit_mk_iff_det_one_sub_ne_zero] at hγ
  rw [orbitParity_mk, LinearMap.sign_det_one_sub _ hγ, returnCharpoly_mk]

/-- **The parity of an iterate.** If the `k`-fold iterate `γ^k` of a closed Reeb orbit `γ` is
nondegenerate, then `parity (γ^k) = parity (γ) * (-1) ^ ((k + 1) N_γ)`, where `N_γ` is the number
of real eigenvalues of the return map of `γ` in `(-1, 0)`, counted with algebraic multiplicity. -/
theorem orbitParity_iterate {γ : Flow.ClosedOrbit (hα.reebFlow hc)} {k : ℕ+}
    (hγ : hα.IsNondegenerateOrbit hc (γ.iterate k)) :
    hα.orbitParity hc (γ.iterate k) = hα.orbitParity hc γ *
      (-1) ^ (((k : ℕ) + 1) *
        ((hα.returnCharpoly hc γ).roots.filter (· ∈ Set.Ioo (-1) 0)).card) := by
  induction γ using Flow.ClosedOrbit.ind with | h δ => _
  rw [orbitParity_iterate_mk,
    hα.orbitParity_eq_neg_one_pow hc (hα.isNondegenerateOrbit_of_iterate hc hγ),
    LinearMap.sign_det_one_sub_pow _ k
      ((hα.isNondegenerateOrbit_iterate_mk_iff_det_one_sub_ne_zero hc δ k).1 hγ),
    returnCharpoly_mk]
  congr 1
  rcases Nat.even_or_odd (k : ℕ) with he | ho
  · -- For even `k`, `1 + A` is invertible for the return map `A`, and `det A = 1` relates its
    -- eigenvalues in `(-∞, -1)` to those in `(-1, 0)`.
    have hneg := LinearMap.det_one_add_ne_zero_of_det_one_sub_pow_ne_zero _ he
      ((hα.isNondegenerateOrbit_iterate_mk_iff_det_one_sub_ne_zero hc δ k).1 hγ)
    rw [pow_mul', pow_mul', LinearMap.neg_one_pow_card_filter_lt_neg_one_of_det_pos _
      (by rw [hα.det_periodicLinearizedReturn hc δ]; exact one_pos) hneg]
  · -- For odd `k`, both sides are even powers of `-1`.
    rw [pow_mul, pow_mul, ho.add_one.neg_one_pow, one_pow, one_pow]

/-- **The even-cover criterion for iterates.** If the `k`-fold iterate `γ^k` of a closed Reeb
orbit `γ` is nondegenerate, its parity differs from that of `γ` exactly when `k` is even and the
return map of `γ` has an odd number of real eigenvalues in `(-1, 0)`, counted with algebraic
multiplicity. -/
theorem orbitParity_iterate_ne_iff {γ : Flow.ClosedOrbit (hα.reebFlow hc)} {k : ℕ+}
    (hγ : hα.IsNondegenerateOrbit hc (γ.iterate k)) :
    hα.orbitParity hc (γ.iterate k) ≠ hα.orbitParity hc γ ↔
      Even (k : ℕ) ∧ Odd ((hα.returnCharpoly hc γ).roots.filter (· ∈ Set.Ioo (-1) 0)).card := by
  have h0 : hα.orbitParity hc γ ≠ 0 :=
    (hα.orbitParity_ne_zero_iff hc γ).2 (hα.isNondegenerateOrbit_of_iterate hc hγ)
  rw [hα.orbitParity_iterate hc hγ, ne_eq, mul_eq_left₀ h0, neg_one_pow_eq_one_iff_even (by decide),
    Nat.even_mul, Nat.even_add_one, ← Nat.not_even_iff_odd]
  tauto

/-- **The even-cover criterion.** A nondegenerate closed Reeb orbit `γ` has a parity different from
that of its underlying primitive orbit `γ₀` exactly when its multiplicity is even and the return
map of `γ₀` has an odd number of real eigenvalues in `(-1, 0)`, counted with algebraic
multiplicity. -/
theorem orbitParity_ne_orbitParity_primitive_iff {γ : Flow.ClosedOrbit (hα.reebFlow hc)}
    (hγ : hα.IsNondegenerateOrbit hc γ) :
    hα.orbitParity hc γ ≠ hα.orbitParity hc γ.primitive ↔
      Even (γ.multiplicity : ℕ) ∧
        Odd ((hα.returnCharpoly hc γ.primitive).roots.filter (· ∈ Set.Ioo (-1) 0)).card := by
  have h := hα.orbitParity_iterate_ne_iff hc (γ := γ.primitive) (k := γ.multiplicity)
    (by rwa [γ.primitive_iterate_multiplicity])
  rwa [γ.primitive_iterate_multiplicity] at h

end IsContactForm

end TauCeti.SmoothForm
