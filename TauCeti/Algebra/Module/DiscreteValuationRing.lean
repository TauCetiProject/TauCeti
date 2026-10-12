/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.LinearAlgebra.Pi

/-!
# Finitely generated modules over a discrete valuation ring

Mathlib's structure theorem `Module.equiv_free_prod_directSum` writes a finitely generated
module over a principal ideal domain as a free module plus a direct sum of cyclic modules
`R ⧸ R ∙ q ^ e` with `q` irreducible. Over a discrete valuation ring every irreducible element
is associated to a fixed uniformizer `ϖ`, so all the cyclic summands are quotients by powers of
the single ideal `(ϖ)`. This file records that specialisation, with the free part and the
torsion part written as function types indexed by `Fin`, and with the trivial summands
`R ⧸ (ϖ ^ 0)` discarded, so that the exponents `e i ≥ 1` are the elementary divisors of the
torsion part.

## Main result

* `TauCeti.Module.equiv_pi_prod_pi_quotient_span_pow`: a finitely generated module over a
  discrete valuation ring with uniformizer `ϖ` is `R ^ n × ∏ i, R ⧸ (ϖ ^ e i)` with all `e i ≥ 1`.
-/

public section

namespace TauCeti

universe u v

/-- **Structure theorem for finitely generated modules over a discrete valuation ring.** A
finitely generated module over a discrete valuation ring `R` with uniformizer `ϖ` is isomorphic
to `R ^ n × ∏ i : Fin m, R ⧸ (ϖ ^ e i)` with every exponent `e i` positive. -/
theorem Module.equiv_pi_prod_pi_quotient_span_pow (R : Type u) (M : Type v) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ (n m : ℕ) (e : Fin m → ℕ), (∀ i, 0 < e i) ∧
      Nonempty (M ≃ₗ[R] (Fin n → R) × ((i : Fin m) → R ⧸ R ∙ ϖ ^ e i)) := by
  classical
  obtain ⟨n, ι, _, q, hq, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum R M
  -- Every irreducible element is associated to `ϖ`, so each cyclic summand is a quotient by a
  -- power of `(ϖ)`.
  have hspan : ∀ i, R ∙ q i ^ e i = R ∙ ϖ ^ e i := fun i ↦ by
    rw [Ideal.submodule_span_eq, Ideal.submodule_span_eq]
    exact Ideal.span_singleton_eq_span_singleton.mpr
      ((IsDiscreteValuationRing.associated_of_irreducible (R := R) (hq i) hϖ).pow_pow)
  -- The summands with exponent `0` are trivial.
  have _ : ∀ i : {i : ι // ¬0 < e i}, Unique (R ⧸ R ∙ ϖ ^ e i.1) := fun i ↦
    @Unique.mk' _ ⟨0⟩ (Submodule.Quotient.subsingleton_iff.mpr (by
      rw [Nat.eq_zero_of_not_pos i.2, pow_zero, Ideal.submodule_span_eq, Ideal.span_singleton_one]))
  let s := {i : ι // 0 < e i}
  let g : (DirectSum ι fun i ↦ R ⧸ R ∙ q i ^ e i) ≃ₗ[R]
      ((j : Fin (Fintype.card s)) → R ⧸ R ∙ ϖ ^ e ((Fintype.equivFin s).symm j).1) :=
    (DirectSum.linearEquivFunOnFintype R ι fun i ↦ R ⧸ R ∙ q i ^ e i).trans <|
      (LinearEquiv.piCongrRight fun i ↦ Submodule.quotEquivOfEq _ _ (hspan i)).trans <|
        (LinearEquiv.piEquivPiSubtypeProd R (fun i ↦ 0 < e i) fun i ↦ R ⧸ R ∙ ϖ ^ e i).trans <|
          LinearEquiv.prodUnique.trans (LinearEquiv.piCongrLeft R (fun i : s ↦ R ⧸ R ∙ ϖ ^ e i.1)
            (Fintype.equivFin s).symm).symm
  exact ⟨n, Fintype.card s, fun j ↦ e ((Fintype.equivFin s).symm j).1,
    fun j ↦ ((Fintype.equivFin s).symm j).2,
    ⟨f.trans ((Finsupp.linearEquivFunOnFinite R R (Fin n)).prodCongr g)⟩⟩

end TauCeti
