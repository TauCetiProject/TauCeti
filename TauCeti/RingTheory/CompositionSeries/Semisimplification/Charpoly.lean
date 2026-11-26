/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.LinearAlgebra.Charpoly.Lsmul
public import TauCeti.LinearAlgebra.Charpoly.Quotient
public import TauCeti.LinearAlgebra.Charpoly.Trace
public import TauCeti.RingTheory.CompositionSeries.Semisimplification.Basic

/-!
# Characteristic polynomials on the semisimplification

Let `A` be an algebra over a field `k` and `M` an `A`-module that is finite-dimensional over `k`.
The semisimplification `M^ss` is again a finite-dimensional `k`-vector space
(`TauCeti.semisimplification.instModule`), and every `a : A` has the same characteristic polynomial
on `M^ss` as on `M` (`TauCeti.charpoly_lsmul_semisimplification`). Applied to `A = k[Γ]`, a
finite-dimensional representation and its semisimplification have the same characteristic
polynomial, hence the same trace and determinant, at every element of `Γ`
(`TauCeti.trace_lsmul_semisimplification`, `TauCeti.det_lsmul_semisimplification`).

The proof is by induction on the dimension: a nonzero proper submodule `P` gives
`M^ss ≅ P^ss × (M/P)^ss`, and the characteristic polynomial is multiplicative on `P` and `M/P`
(`Submodule.charpoly_lsmul_eq_mul_quotient`); a module with no such submodule is zero or simple,
hence semisimple and isomorphic to `M^ss`.

## Main results

* `TauCeti.charpoly_lsmul_semisimplification`: `charpoly (a | M^ss) = charpoly (a | M)`.
* `TauCeti.trace_lsmul_semisimplification`: `trace (a | M^ss) = trace (a | M)`.
* `TauCeti.det_lsmul_semisimplification`: `det (a | M^ss) = det (a | M)`.
-/

public section

namespace TauCeti

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

section Instances

variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [IsNoetherian A M] [IsArtinian A M]

/-- The `k`-vector space structure of the semisimplification of an `A`-module, for a
`k`-algebra `A`. -/
noncomputable instance semisimplification.instModule : Module k (semisimplification A M) :=
  inferInstanceAs (Module k (seriesSemisimplification _))

/-- The `k`- and `A`-actions on the semisimplification are compatible. -/
instance semisimplification.instIsScalarTower : IsScalarTower k A (semisimplification A M) :=
  inferInstanceAs (IsScalarTower k A (seriesSemisimplification _))

/-- The semisimplification of a finite-dimensional module is finite-dimensional. -/
instance semisimplification.instFiniteDimensional [FiniteDimensional k M] :
    FiniteDimensional k (semisimplification A M) :=
  inferInstanceAs (FiniteDimensional k (seriesSemisimplification _))

end Instances

section Charpoly

variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [FiniteDimensional k M] [IsNoetherian A M] [IsArtinian A M]

/-- **The semisimplification has the characteristic polynomials of the module.** For an
`A`-module `M` that is finite-dimensional over a field `k` (with `A` a `k`-algebra), every
`a : A` has the same characteristic polynomial on `M^ss` as on `M`. -/
theorem charpoly_lsmul_semisimplification (a : A) :
    (Algebra.lsmul k k (semisimplification A M) a).charpoly =
      (Algebra.lsmul k k M a).charpoly := by
  induction hn : Module.finrank k M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  by_cases hP : ∃ P : Submodule A M, P ≠ ⊥ ∧ P ≠ ⊤
  · obtain ⟨P, hbot, htop⟩ := hP
    obtain ⟨e⟩ := nonempty_linearEquiv_semisimplification_prod_quotient P
    have hW : Module.finrank k P = Module.finrank k (P.restrictScalars k) :=
      ((P.restrictScalarsEquiv k A M).restrictScalars k).finrank_eq.symm
    have hsum : Module.finrank k (M ⧸ P) = n - Module.finrank k P :=
      hn ▸ Submodule.finrank_quotient (R := k) P
    have hP : Module.finrank k P < n := by
      rw [← hn, hW]
      exact Submodule.finrank_lt (by rwa [Ne, Submodule.restrictScalars_eq_top_iff])
    have hQ : Module.finrank k (M ⧸ P) < n := by
      have : Module.finrank k P ≠ 0 := by
        rwa [hW, Ne, Submodule.finrank_eq_zero, Submodule.restrictScalars_eq_bot_iff]
      omega
    rw [e.charpoly_lsmul_eq, Algebra.charpoly_lsmul_prod, ih _ hP rfl, ih _ hQ rfl,
      P.charpoly_lsmul_eq_mul_quotient]
  · have : IsSemisimpleModule A M :=
      { exists_isCompl P := by
          rcases eq_or_ne P ⊥ with rfl | hbot
          · exact ⟨⊤, isCompl_bot_top⟩
          · obtain rfl : P = ⊤ := by_contra fun htop ↦ hP ⟨P, hbot, htop⟩
            exact ⟨⊥, isCompl_top_bot⟩ }
    obtain ⟨e⟩ := nonempty_linearEquiv_semisimplification_of_isSemisimpleModule (R := A) (M := M)
    exact e.charpoly_lsmul_eq a

/-- Every `a : A` has the same trace over `k` on the semisimplification `M^ss` as on `M`. -/
theorem trace_lsmul_semisimplification (a : A) :
    LinearMap.trace k (semisimplification A M) (Algebra.lsmul k k (semisimplification A M) a) =
      LinearMap.trace k M (Algebra.lsmul k k M a) := by
  rw [LinearMap.trace_eq_neg_charpoly_nextCoeff, LinearMap.trace_eq_neg_charpoly_nextCoeff,
    charpoly_lsmul_semisimplification]

/-- Every `a : A` has the same determinant over `k` on the semisimplification `M^ss` as on `M`. -/
theorem det_lsmul_semisimplification (a : A) :
    LinearMap.det (Algebra.lsmul k k (semisimplification A M) a) =
      LinearMap.det (Algebra.lsmul k k M a) := by
  rw [LinearMap.det_eq_sign_charpoly_coeff, LinearMap.det_eq_sign_charpoly_coeff,
    ← LinearMap.charpoly_natDegree (Algebra.lsmul k k (semisimplification A M) a),
    ← LinearMap.charpoly_natDegree (Algebra.lsmul k k M a), charpoly_lsmul_semisimplification]

end Charpoly

end TauCeti
