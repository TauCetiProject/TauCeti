/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Tate algebras in finitely many variables are noetherian

Over a complete nonarchimedean field `K`, the Tate algebra `K⟨X₁, …, Xₙ⟩` of unit-radius
restricted power series in finitely many variables is a noetherian ring.

The proof is the induction on the number of variables of Bosch–Güntzer–Remmert. A Tate algebra
in no variables is `K`. For the inductive step, let `I` be a nonzero ideal of the Tate algebra in
the variables `Option σ`, and `f ∈ I` nonzero. After an automorphism of the Tate algebra, `f` is a
restricted series in the variable `none` over the Tate algebra `T` in the variables `σ` which is
distinguished with a unit dominant coefficient
(`TauCeti.MvPowerSeries.exists_algEquiv_isDistinguished_isUnit`). Weierstrass division then makes
the quotient by `f` a finite `T`-module (`TauCeti.PowerSeries.IsDistinguished.finite_quotient`), so
it is a noetherian ring when `T` is, and the image of `I` in it is finitely generated. Together
with the generator `f` of the kernel, this shows that `I` is finitely generated.

## Main results

* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`: the Tate algebra in finitely many
  variables over a complete nonarchimedean field is noetherian.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, Theorem 1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- The Tate algebra in no variables is noetherian: it consists of the constants. -/
private theorem isNoetherianRing_isRestricted_subring_of_isEmpty {σ : Type*} [IsEmpty σ] :
    IsNoetherianRing (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) := by
  refine isNoetherianRing_of_surjective K _ (algebraMap K _) fun f ↦
    ⟨coeff 0 (f : MvPowerSeries σ K), Subtype.ext ?_⟩
  ext d
  rw [Subsingleton.elim d 0, coe_algebraMap_isRestrictedSubring, coeff_C, ite_eq_left rfl]

omit [CompleteSpace K] in
/-- Renaming the variables along an equivalence preserves noetherianity of Tate algebras. -/
private theorem isNoetherianRing_isRestricted_subring_of_equiv {σ τ : Type*} [Finite σ]
    [Finite τ] (e : σ ≃ τ)
    (h : IsNoetherianRing (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) :
    IsNoetherianRing (IsRestricted.subring (R := K) (fun _ : τ ↦ 1)) := by
  classical
  let E : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) ≃ₐ[K]
      IsRestricted.subring (R := K) (fun _ : τ ↦ 1) :=
    restrictedSubstEquiv (fun s ↦ MvPolynomial.X (e s)) (fun _ ↦ MvPolynomial.constantCoeff_X _ _)
      (fun _ _ ↦ by rw [MvPolynomial.coeff_X]; split_ifs <;> simp)
      (fun t ↦ MvPolynomial.X (e.symm t)) (fun _ ↦ MvPolynomial.constantCoeff_X _ _)
      (fun _ _ ↦ by rw [MvPolynomial.coeff_X]; split_ifs <;> simp)
      (fun s ↦ by simp) (fun t ↦ by simp)
  exact isNoetherianRing_of_ringEquiv _ E.toRingEquiv

/-- The inductive step: adjoining one variable to a noetherian Tate algebra gives a noetherian
Tate algebra. -/
private theorem isNoetherianRing_isRestricted_subring_option {σ : Type*} [Finite σ]
    (h : IsNoetherianRing (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) :
    IsNoetherianRing (IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1)) := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact Submodule.fg_bot
  obtain ⟨f, hfI, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨e, s, hd, hu⟩ := exists_algEquiv_isDistinguished_isUnit f hf
  let ψ := e.toRingEquiv.trans Huber.restrictedOptionEquiv
  -- The quotient by the distinguished series `ψ f` is finite over the noetherian Tate algebra in
  -- the variables `σ`, hence a noetherian ring.
  have : Module.Finite (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) (_ ⧸ Ideal.span {ψ f}) :=
    hd.finite_quotient zero_lt_one hu
  have hQ : IsNoetherianRing (_ ⧸ Ideal.span {ψ f}) :=
    isNoetherian_of_tower (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
      (isNoetherian_of_isNoetherianRing_of_finite _ _)
  have hJ : (I.map ψ).FG := by
    refine Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
      ((isNoetherianRing_iff_ideal_fg _).mp hQ _) ?_ Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_map_of_mem ψ hfI))]
    exact Submodule.fg_span_singleton _
  rw [← Ideal.map_of_equiv (I := I) ψ]
  exact hJ.map _

/-- **Tate algebras are noetherian.** Over a complete nonarchimedean field `K`, the Tate algebra
`K⟨X₁, …, Xₙ⟩` of unit-radius restricted power series in finitely many variables is a noetherian
ring. -/
theorem isNoetherianRing_isRestricted_subring (σ : Type*) [Finite σ] :
    IsNoetherianRing (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) := by
  refine Finite.induction_empty_option
    (P := fun σ ↦ Finite σ → IsNoetherianRing (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))
    (fun {α β} e hα _ ↦ ?_) (fun _ ↦ isNoetherianRing_isRestricted_subring_of_isEmpty)
    (fun {α} _ hα _ ↦ isNoetherianRing_isRestricted_subring_option (hα inferInstance)) σ
    inferInstance
  have : Finite α := Finite.of_equiv β e.symm
  exact isNoetherianRing_isRestricted_subring_of_equiv e (hα this)

end TauCeti.MvPowerSeries
