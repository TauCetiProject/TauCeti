/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Finite algebras over affinoid algebras

Adjoining a root of a monic polynomial to an affinoid algebra gives an affinoid algebra, and
consequently every finite algebra over an affinoid algebra is affinoid. Together with
`TauCeti.IsAffinoidAlgebra.quotient`, this closes the class of affinoid algebras under the
two basic algebraic operations used to build finite morphisms of affinoid spaces.

For a monic `p` over `A = K⟨X₁, …, Xₙ⟩ ⧸ I`, lift `p` to a monic polynomial `P` over the Tate
algebra and rescale its roots by a small nonzero scalar, so that all coefficients have Gauss norm
at most one. The rescaled polynomial is distinguished, so Weierstrass division identifies its
polynomial quotient with the quotient of `K⟨X₁, …, Xₙ, Y⟩` by it. This quotient maps onto
`A[Y] ⧸ (p)`, sending `Y` to the rescaled root. A finite algebra is reached from `A` by adjoining
finitely many integral generators one at a time.

The coefficient field must be nontrivially normed, to rescale the roots. No reducedness,
characteristic, or nontriviality assumption is placed on the algebras.

## Main results

* `TauCeti.IsAffinoidAlgebra.adjoinRoot`: `A[X] ⧸ (p)` is affinoid for monic `p`.
* `TauCeti.IsAffinoidAlgebra.of_finite`: a finite algebra over an affinoid algebra is affinoid.
* `TauCeti.IsAffinoidAlgebra.of_algHom_finite`: the target of a finite algebra homomorphism
  from an affinoid algebra is affinoid.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries Polynomial

universe u v

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

omit [CompleteSpace K] in
/-- Rescaling the roots of a polynomial over a Tate algebra by a small nonzero scalar makes all
of its coefficients below the degree have Gauss norm at most one. -/
private theorem exists_norm_coeff_scaleRoots_le_one {σ : Type*} (P : (Tate σ)[X]) :
    ∃ c : K, c ≠ 0 ∧ ∀ k < P.natDegree,
      ‖(P.scaleRoots (algebraMap K (Tate σ) c)).coeff k‖ ≤ 1 := by
  set M := 1 + ∑ k ∈ Finset.range P.natDegree, ‖P.coeff k‖
  have hM : 0 < M := by positivity
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt K (inv_pos.mpr hM)
  refine ⟨c, norm_pos_iff.mp hc0, fun k hk ↦ ?_⟩
  have hk' : ‖P.coeff k‖ ≤ M := by
    have := Finset.single_le_sum (f := fun k ↦ ‖P.coeff k‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_range.mpr hk)
    linarith
  have hc1 : ‖c‖ ≤ 1 := hc.le.trans (inv_le_one_of_one_le₀ (by
    simp only [M, le_add_iff_nonneg_right]; positivity))
  rw [coeff_scaleRoots, norm_mul, norm_pow, norm_algebraMap']
  calc ‖P.coeff k‖ * ‖c‖ ^ (P.natDegree - k) ≤ M * ‖c‖ :=
        mul_le_mul hk' (pow_le_of_le_one (norm_nonneg c) hc1 (by omega)) (by positivity)
          hM.le
    _ ≤ M * M⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hM.ne'

variable {A : Type u} [CommRing A] [Algebra K A]

/-- Adjoining a root of a monic polynomial to an affinoid algebra gives an affinoid algebra. -/
theorem adjoinRoot (hA : IsAffinoidAlgebra K A) {p : A[X]} (hp : p.Monic) :
    IsAffinoidAlgebra K (AdjoinRoot p) := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  let R := Tate (Fin n)
  -- Lift `p` to a monic polynomial over the Tate algebra and make its coefficients small.
  obtain ⟨P, hPp, -, hPm⟩ := lifts_and_natDegree_eq_and_monic
    (f := π.toRingHom) (p := p) ((lifts_iff_coeff_lifts p).mpr fun k ↦ hπ _) hp
  obtain ⟨c, hc0, hc⟩ := exists_norm_coeff_scaleRoots_le_one P
  set Q := P.scaleRoots (algebraMap K R c)
  have hQm : Q.IsMonicOfDegree P.natDegree :=
    ⟨natDegree_scaleRoots _ _, (monic_scaleRoots_iff _).mpr hPm⟩
  have hQ : PowerSeries.IsDistinguished 1 P.natDegree (Q : PowerSeries R) :=
    PowerSeries.isDistinguished_of_isMonicOfDegree one_pos hQm (by simpa using hc)
  -- Evaluate at the rescaled root of `p`.
  let ev : R[X] →+* AdjoinRoot p := eval₂RingHom ((AdjoinRoot.of p).comp π.toRingHom)
    (AdjoinRoot.of p (algebraMap K A c) * AdjoinRoot.root p)
  have hevQ : ev Q = 0 := by
    have h := scaleRoots_eval₂_eq_zero ((AdjoinRoot.of p).comp π.toRingHom)
      (r := AdjoinRoot.root p) (s := algebraMap K R c) (p := P) (by
        rw [← eval₂_map, hPp]
        exact AdjoinRoot.eval₂_root p)
    have hc' : π.toRingHom (algebraMap K R c) = algebraMap K A c := π.commutes c
    rwa [RingHom.comp_apply, hc'] at h
  have hev : Function.Surjective ev := by
    have hof (a : A) : AdjoinRoot.of p a ∈ ev.range := by
      obtain ⟨r, rfl⟩ := hπ a
      exact ⟨Polynomial.C r, by simp [ev]⟩
    have hroot : AdjoinRoot.root p ∈ ev.range := by
      refine ⟨Polynomial.C (algebraMap K R c⁻¹) * Polynomial.X, ?_⟩
      simp [ev, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0]
    refine fun y ↦ RingHom.mem_range.mp ?_
    induction y using AdjoinRoot.induction_on with | ih q => ?_
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | monomial k a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      exact mul_mem (hof a) (pow_mem hroot k)
  -- Assemble the presentation by `K⟨X₁, …, Xₙ, Y⟩`, using Weierstrass division by `Q`.
  have hker : ∀ a ∈ Ideal.span {Q}, ev a = 0 := fun a ha ↦ by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hevQ, mul_zero]
  let g : R[X] ⧸ Ideal.span {Q} →+* AdjoinRoot p := Ideal.Quotient.lift _ ev hker
  let e := hQ.polynomialQuotientEquiv one_pos hQm
  let ψ : Tate (Option (Fin n)) →+* AdjoinRoot p :=
    g.comp (e.symm.toRingHom.comp ((Ideal.Quotient.mk _).comp
      (Huber.restrictedOptionEquiv (σ := Fin n) (R := K)).toRingHom))
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.lift_surjective_of_surjective _ hker hev).comp <|
      e.symm.surjective.comp <| Ideal.Quotient.mk_surjective.comp <| RingEquiv.surjective _
  have hψc (r : K) : ψ (algebraMap K _ r) = algebraMap K (AdjoinRoot p) r := by
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv, Huber.restrictedOptionEquiv_algebraMap,
      Ideal.Quotient.mk_algebraMap, AlgEquiv.commutes]
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.lift_mk]
    simp only [ev, coe_eval₂RingHom, Polynomial.algebraMap_apply, Polynomial.eval₂_C,
      RingHom.comp_apply, IsScalarTower.algebraMap_apply K A (AdjoinRoot p),
      AdjoinRoot.algebraMap_eq]
    exact congrArg _ (π.commutes r)
  let ψ' : Tate (Option (Fin n)) →ₐ[K] AdjoinRoot p := { ψ with commutes' := hψc }
  exact isAffinoidAlgebra_tate.of_surjective ψ' hψ

variable {B : Type v} [CommRing B] [Algebra K B]

/-- An integral algebra generated by a finite set over an affinoid algebra is affinoid. The
generators are adjoined one at a time. -/
private theorem of_adjoin_eq_top (s : Finset B) :
    ∀ (A : Type u) [CommRing A] [Algebra K A] [Algebra A B] [IsScalarTower K A B]
      [Algebra.IsIntegral A B], IsAffinoidAlgebra K A → Algebra.adjoin A (s : Set B) = ⊤ →
      IsAffinoidAlgebra K B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro A _ _ _ _ _ hA hs
    refine hA.of_surjective (IsScalarTower.toAlgHom K A B) fun b ↦ ?_
    have hb : b ∈ (⊥ : Subalgebra A B) := by
      rw [← Algebra.adjoin_empty, ← Finset.coe_empty, hs]
      exact Algebra.mem_top
    exact Algebra.mem_bot.mp hb
  | insert b s _ ih =>
    intro A _ _ _ _ _ hA hs
    obtain ⟨p, hpm, hpb⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    let : Algebra (AdjoinRoot p) B := (AdjoinRoot.lift (algebraMap A B) b hpb).toAlgebra
    have hmap (x : AdjoinRoot p) :
        algebraMap (AdjoinRoot p) B x = AdjoinRoot.lift (algebraMap A B) b hpb x := by
      rw [RingHom.algebraMap_toAlgebra]
    have : IsScalarTower A (AdjoinRoot p) B :=
      IsScalarTower.of_algebraMap_eq fun a ↦ by
        rw [hmap, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
    have : IsScalarTower K (AdjoinRoot p) B :=
      IsScalarTower.of_algebraMap_eq fun r ↦ by
        rw [IsScalarTower.algebraMap_apply K A (AdjoinRoot p),
          ← IsScalarTower.algebraMap_apply A (AdjoinRoot p) B,
          ← IsScalarTower.algebraMap_apply K A B]
    have : Algebra.IsIntegral (AdjoinRoot p) B := Algebra.IsIntegral.tower_top A
    refine ih (AdjoinRoot p) (hA.adjoinRoot hpm) (eq_top_iff.mpr fun x _ ↦ ?_)
    have hle : Algebra.adjoin A (insert b (s : Set B)) ≤
        (Algebra.adjoin (AdjoinRoot p) (s : Set B)).restrictScalars A := by
      rw [Algebra.adjoin_le_iff, Set.insert_subset_iff]
      refine ⟨?_, Algebra.subset_adjoin⟩
      have hb : algebraMap (AdjoinRoot p) B (AdjoinRoot.root p) = b := by
        rw [hmap, AdjoinRoot.lift_root]
      rw [← hb, SetLike.mem_coe, Subalgebra.mem_restrictScalars]
      exact Subalgebra.algebraMap_mem _ _
    rw [← Finset.coe_insert, hs] at hle
    exact hle Algebra.mem_top

/-- A finite algebra over an affinoid algebra is affinoid. -/
theorem of_finite [Algebra A B] [IsScalarTower K A B] [Module.Finite A B]
    (hA : IsAffinoidAlgebra K A) : IsAffinoidAlgebra K B := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  exact of_adjoin_eq_top s A hA hs

/-- The target of a finite algebra homomorphism from an affinoid algebra is affinoid. -/
theorem of_algHom_finite (hA : IsAffinoidAlgebra K A) (f : A →ₐ[K] B) (hf : f.Finite) :
    IsAffinoidAlgebra K B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : Module.Finite A B := hf
  exact hA.of_finite

end TauCeti.IsAffinoidAlgebra
