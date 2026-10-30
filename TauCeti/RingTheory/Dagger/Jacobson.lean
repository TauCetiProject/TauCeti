/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Noetherian
public import TauCeti.RingTheory.Jacobson.Ring

/-!
# Monsky–Washnitzer algebras are Jacobson rings

Over a complete ultrametric normed field `K`, the Monsky–Washnitzer algebra `K⟨X⟩†` in finitely
many variables is a Jacobson ring: every prime ideal is an intersection of maximal ideals.
Together with the finiteness of residue fields,
`TauCeti.Dagger.washnitzerAlgebra.finite_quotient_of_isMaximal`, this lets the maximal ideals
detect every radical ideal of `K⟨X⟩†` and of its quotients. In particular every dagger algebra,
being such a quotient, is a Jacobson ring.

The proof is by induction on the number of variables, applying
`TauCeti.isJacobsonRing_of_quotient_span_singleton` to `K⟨X, Y⟩†` with `Y = X none`.

* The Jacobson radical of `K⟨X, Y⟩†` vanishes. If `f` lies in it, then `1 + f * a Y` is a unit
  for every `a ∈ K`, so by the unit criterion its constant coefficient `1` strictly dominates all
  its other coefficients. Choosing `a` as the inverse of a nonzero coefficient of `f` produces a
  coefficient equal to `1`, unless `f = 0`.
* For a nonzero `f`, a triangular automorphism makes `f` distinguished in `Y` with a unit
  coefficient in the distinguished degree, and overconvergent Weierstrass division makes
  `K⟨X, Y⟩† ⧸ (f)` finite over `K⟨X⟩†`, which is Jacobson by induction. Integral extensions of
  Jacobson rings are Jacobson.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.isJacobsonRing`: `K⟨X⟩†` is a Jacobson ring for finitely
  many variables.
* `TauCeti.Dagger.IsDaggerAlgebra.isJacobsonRing`: dagger algebras are Jacobson rings.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.4 (1).
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.2.5–5.2.6
  (the same argument for Tate algebras).

The argument follows `TauCeti.MvPowerSeries.isJacobsonRing` in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Jacobson`, with overconvergent division and
the overconvergent unit criterion in place of their Tate-algebra counterparts.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W " σ:max => washnitzerAlgebra σ K

/-- The Jacobson radical of `K⟨X, Y⟩†` vanishes: a nonzero element `f` has a multiple `f * a Y`
for which `1 + f * a Y` has a nonconstant coefficient equal to `1`, so it is not a unit. -/
private theorem jacobson_bot_option {σ : Type*} :
    (⊥ : Ideal (W (Option σ))).jacobson = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ (Ideal.mem_bot).mpr ?_
  by_contra hf0
  obtain ⟨t, ht⟩ : ∃ t, coeff t (f : MvPowerSeries (Option σ) K) ≠ 0 := by
    by_contra! h
    exact hf0 (Subtype.ext (MvPowerSeries.ext fun t ↦ by simpa using h t))
  set b := coeff t (f : MvPowerSeries (Option σ) K)
  let y : W (Option σ) := algebraMap K _ b⁻¹ * X (Option σ) K none
  have hy : (y : MvPowerSeries (Option σ) K) = monomial (Finsupp.single none 1) b⁻¹ := by
    simp [y, coe_X, X_def, ← Algebra.smul_def, ← map_smul]
  classical
  have hu := (isUnit_washnitzerAlgebra_iff _).mp (Ideal.mem_jacobson_bot.mp hf y)
  -- The constant coefficient of `1 + f * y` is `1`, and its coefficient at `t + single none 1` is
  -- `b * b⁻¹ = 1`.
  have h0 : constantCoeff ((f * y + 1 : W (Option σ)) : MvPowerSeries (Option σ) K) = 1 := by
    have hy0 : constantCoeff (y : MvPowerSeries (Option σ) K) = 0 := by
      rw [hy, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial]
      simp [eq_comm (a := (0 : Option σ →₀ ℕ))]
    simp [hy0]
  have h1 : coeff (t + Finsupp.single none 1)
      ((f * y + 1 : W (Option σ)) : MvPowerSeries (Option σ) K) = 1 := by
    simp [hy, coeff_add_mul_monomial, b, ht, coeff_one]
  have hlt := hu.2 (t + Finsupp.single none 1) (by simp)
  rw [h0, h1] at hlt
  exact hlt.false

/-- The inductive step: if `K⟨X⟩†` is Jacobson, so is `K⟨X, Y⟩†`. -/
private theorem isJacobsonRing_option {σ : Type*} [Finite σ] [IsJacobsonRing (W σ)] :
    IsJacobsonRing (W (Option σ)) := by
  refine isJacobsonRing_of_quotient_span_singleton jacobson_bot_option fun f hf ↦ ?_
  -- Make `f` distinguished in `Y`; then `K⟨X, Y⟩† ⧸ (e f)` is finite over `K⟨X⟩†`.
  obtain ⟨α, hα, s, hd, hu⟩ := exists_triangularEquiv_isDistinguished_isUnit f hf
  let e := triangularEquiv (R := K) α hα
  let J : Ideal (W (Option σ)) := Ideal.span {e f}
  let π : W (Option σ) →ₐ[K] W (Option σ) ⧸ J := Ideal.Quotient.mkₐ K J
  have hz : π (e f) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hfin := finite_comp_optionC_of_isDistinguished (A := W (Option σ) ⧸ J) (π := π) hd hu
    (RingHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective K J)) hz
  have : IsJacobsonRing (W (Option σ) ⧸ J) :=
    isJacobsonRing_of_isIntegral' (π.comp optionC).toRingHom hfin.to_isIntegral
  have hmap : (Ideal.span {f}).map (e : W (Option σ) ≃+* W (Option σ)) = J := by
    simp [J, Ideal.map_span]
  exact (isJacobsonRing_iso (Ideal.quotientEquiv _ _ e.toRingEquiv hmap.symm)).mpr this

/-- **Monsky–Washnitzer algebras are Jacobson rings.** Over a complete ultrametric normed field
`K`, every prime ideal of the algebra `K⟨X⟩†` of overconvergent power series in finitely many
variables is the intersection of the maximal ideals containing it. -/
instance isJacobsonRing {σ : Type*} [Finite σ] : IsJacobsonRing (W σ) :=
  Finite.induction_empty_option (P := fun σ ↦ ∀ [Finite σ], IsJacobsonRing (W σ))
    (fun {α β} e h _ ↦
      have : Finite α := .of_equiv β e.symm
      (isJacobsonRing_iso (renameAlgEquiv (R := K) e).toRingEquiv).mp h)
    (isJacobsonRing_of_surjective ⟨algebraMap K (W PEmpty), algebraMap_surjective⟩)
    (fun {_} _ h _ ↦
      have := h
      isJacobsonRing_option) σ

end TauCeti.Dagger.washnitzerAlgebra

namespace TauCeti.Dagger.IsDaggerAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

include K in
/-- **Dagger algebras are Jacobson rings.** Over a complete ultrametric normed field `K`, every
prime ideal of a `K`-dagger algebra is the intersection of the maximal ideals containing it. -/
theorem isJacobsonRing : IsJacobsonRing A := by
  obtain ⟨n, π, hπ⟩ := exists_surjective (K := K) (A := A)
  exact isJacobsonRing_of_surjective ⟨π.toRingHom, hπ⟩

end TauCeti.Dagger.IsDaggerAlgebra
