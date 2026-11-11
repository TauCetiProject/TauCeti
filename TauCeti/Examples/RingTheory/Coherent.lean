/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.Algebra.Module.FinitePresentation
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.RingTheory.Coherent.MvPolynomial
import TauCeti.RingTheory.MvPolynomial.Evaluation.Single
import TauCeti.RingTheory.MvPolynomial.Noetherian

/-!
# Checks and counterexamples for coherent modules and coherent rings

Noetherian rings are coherent, and over them coherence coincides with finite generation. The zero
module is coherent over every ring, and the zero ring is coherent. Polynomial rings in countably
many variables such as `ℤ[X_0, X_1, …]` (`MvPolynomial ℕ ℤ`) are coherent without being Noetherian,
and localization preserves coherence for arbitrary localization carriers.

In the opposite direction, the quotient `R[x, y_0, y_1, …] ⧸ (x y_0, x y_1, …)` over any nontrivial
commutative ring `R` (for instance a field `k`) is not coherent: its principal ideal `(x)` is
finitely generated, whereas the `x`-torsion ideal annihilating `x` contains the infinitely many
independent classes `y_0, y_1, …` and is not finitely generated, so `(x)` is not finitely
presented. In particular, as a module over itself this quotient is finitely presented (free of rank
one) without being coherent, separating coherence from finite presentation over non-Noetherian
rings.
-/

namespace TauCeti.CoherentChecks

/-- *coherent_test_noetherian*: a Noetherian ring is coherent, and over it coherence coincides with
finite generation. -/
example (R M : Type*) [Ring R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] :
    IsCoherentRing R ∧ (Module.IsCoherent R M ↔ Module.Finite R M) :=
  ⟨inferInstance, Module.isCoherent_iff_finite⟩

/-- *coherent_test_zero*: the zero module is coherent over every ring, and the zero ring is a
coherent ring. -/
example (R : Type*) [Ring R] :
    Module.IsCoherent R PUnit ∧ IsCoherentRing PUnit :=
  ⟨inferInstance, inferInstance⟩

/-- *coherent_test_infinitePolynomial*: `ℤ[X_0, X_1, …]` (`MvPolynomial ℕ ℤ`) is a coherent ring
that is not Noetherian. -/
example : IsCoherentRing (MvPolynomial ℕ ℤ) ∧ ¬ IsNoetherianRing (MvPolynomial ℕ ℤ) :=
  ⟨inferInstance, MvPolynomial.not_isNoetherianRing⟩

/-- Localization preserves ring coherence for any localization carrier, not just
`Localization T`. -/
example (R : Type*) [CommRing R] [IsCoherentRing R] (T : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S] : IsCoherentRing S :=
  IsCoherentRing.of_isLocalization T

/-- *coherent_test_nonCoherentRing* (*coherent_test_notJustFinitelyPresented*): over any nontrivial
commutative ring `R` (such as a field `k`), in `S = R[x, y_0, y_1, …] ⧸ (x y_0, x y_1, …)` (Stacks,
Section 10.90, Tag 05CU) the principal ideal `(x)` is finitely generated without being finitely
presented, so `S` is finitely presented over itself (free of rank one) yet is neither a coherent
`S`-module nor a coherent ring. -/
example (R : Type*) [CommRing R] [Nontrivial R] :
    let relIdeal : Ideal (MvPolynomial (Option ℕ) R) :=
      Ideal.span (Set.range fun n : ℕ ↦ MvPolynomial.X none * MvPolynomial.X (some n))
    let S := MvPolynomial (Option ℕ) R ⧸ relIdeal
    let xClass : S := Ideal.Quotient.mk relIdeal (MvPolynomial.X none)
    (Ideal.span {xClass}).FG ∧
      ¬ Module.FinitePresentation S ↥(Ideal.span {xClass}) ∧
      Module.FinitePresentation S S ∧
      ¬ Module.IsCoherent S S ∧
      ¬ IsCoherentRing S := by
  classical
  intro relIdeal S xClass
  let yClass (n : ℕ) : S := Ideal.Quotient.mk relIdeal (MvPolynomial.X (some n))
  have hx_mul_y (n : ℕ) : xClass * yClass n = 0 := by
    dsimp only [xClass, yClass]
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨n, rfl⟩
  -- Sending `x ↦ T` and `y_n ↦ 0` in `R[T]` shows any lift of an `x`-torsion element has zero
  -- constant term.
  let evalXHom : S →+* Polynomial R :=
    Ideal.Quotient.lift relIdeal
      (MvPolynomial.eval₂Hom (Polynomial.C (R := R))
        fun o ↦ Option.elim o Polynomial.X fun _ ↦ 0)
      fun _ hp ↦ RingHom.mem_ker.mp <|
        Ideal.span_le.mpr (by rintro _ ⟨n, rfl⟩; simp) hp
  have hc0_of_x_mul {p : MvPolynomial (Option ℕ) R}
      (hp : xClass * Ideal.Quotient.mk relIdeal p = 0) :
      MvPolynomial.constantCoeff p = 0 := by
    have hmul : Polynomial.X * evalXHom (Ideal.Quotient.mk relIdeal p) = 0 := by
      simpa only [S, xClass, evalXHom, map_mul, map_zero, Ideal.Quotient.lift_mk,
        MvPolynomial.eval₂Hom_X', Option.elim_none] using congrArg evalXHom hp
    have hcoeff : (evalXHom (Ideal.Quotient.mk relIdeal p)).coeff 0 = 0 := by
      simpa [Polynomial.coeff_X_mul] using congrArg (fun q : Polynomial R ↦ q.coeff 1) hmul
    have hcomp :
        (Polynomial.constantCoeff (R := R)).comp
          (MvPolynomial.eval₂Hom (Polynomial.C (R := R)) fun o : Option ℕ ↦
            Option.elim o Polynomial.X fun _ ↦ 0) =
          MvPolynomial.constantCoeff :=
      MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun o ↦ by cases o <;> simp)
    have hev : (evalXHom (Ideal.Quotient.mk relIdeal p)).coeff 0 =
        MvPolynomial.constantCoeff p := by
      simpa only [S, evalXHom, Ideal.Quotient.lift_mk, RingHom.comp_apply,
        Polynomial.constantCoeff_apply] using DFunLike.congr_fun hcomp p
    exact hev.symm.trans hcoeff
  -- Sending `x ↦ 0`, `y_N ↦ 1`, and `y_n ↦ 0` for `n ≠ N` separates `y_N` from any finite set of
  -- generators of the `x`-torsion submodule.
  let evalYHom (N : ℕ) : S →+* R :=
    Ideal.Quotient.lift relIdeal
      (MvPolynomial.eval₂Hom (RingHom.id R) (Pi.single (some N) 1))
      fun _ hp ↦ RingHom.mem_ker.mp <|
        Ideal.span_le.mpr (by rintro _ ⟨n, rfl⟩; simp [Pi.single_eq_of_ne]) hp
  have hnot_fg : ¬ (Submodule.torsionBy S S xClass).FG := by
    intro ⟨s, hs⟩
    choose p hp using Ideal.Quotient.mk_surjective (I := relIdeal)
    let V₀ : Finset ℕ :=
      ((s.image p).biUnion MvPolynomial.vars).preimage some (Option.some_injective ℕ).injOn
    obtain ⟨N, hN⟩ := Infinite.exists_notMem_finset V₀
    have hspan_map : (Ideal.span (s.image p : Set _)).map (Ideal.Quotient.mk relIdeal) =
        Submodule.torsionBy S S xClass := by
      rw [Finset.coe_image, Ideal.map_span, ← Set.image_comp, Function.comp_def,
        funext hp, Set.image_id']
      exact hs
    have hle : Submodule.torsionBy S S xClass ≤ RingHom.ker (evalYHom N) := by
      rw [← hspan_map, Ideal.map_le_iff_le_comap]
      refine (MvPolynomial.span_le_ker_eval₂Hom_single (RingHom.id R) (i := some N) 1
        (fun g hg ↦ ?_) (fun g hg hgN ↦ hN (Finset.mem_preimage.mpr
          (Finset.mem_biUnion.mpr ⟨g, hg, hgN⟩)))).trans fun g hg ↦ ?_
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hg
        refine hc0_of_x_mul ?_
        rw [hp z, ← smul_eq_mul]
        exact (Submodule.mem_torsionBy_iff xClass z).mp (hs ▸ Submodule.subset_span hz)
      · simpa only [S, evalYHom, RingHom.mem_ker, Ideal.mem_comap,
          Ideal.Quotient.lift_mk] using hg
    have hyN_mem : yClass N ∈ Submodule.torsionBy S S xClass := by
      rw [Submodule.mem_torsionBy_iff, smul_eq_mul, hx_mul_y]
    have hyN_zero : evalYHom N (yClass N) = 0 := RingHom.mem_ker.mp (hle hyN_mem)
    simp only [S, yClass, evalYHom, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X',
      Pi.single_eq_same, one_ne_zero] at hyN_zero
  have hnot_fp : ¬ Module.FinitePresentation S ↥(Ideal.span {xClass}) := by
    intro hfp
    let mulX : S →ₗ[S] S := LinearMap.lsmul S S xClass
    have hrng : LinearMap.range mulX = Ideal.span {xClass} := by
      ext u
      simp only [LinearMap.mem_range, Ideal.mem_span_singleton, dvd_def, mulX,
        LinearMap.lsmul_apply, smul_eq_mul, eq_comm]
    have : Module.FinitePresentation S (LinearMap.range mulX) :=
      .of_equiv (LinearEquiv.ofEq _ _ hrng).symm
    have hker := Module.FinitePresentation.fg_ker_of_range mulX
    dsimp only [mulX] at hker
    rw [← Submodule.torsionBy_eq_ker_lsmul] at hker
    exact hnot_fg hker
  have hnot_coh : ¬ IsCoherentRing S := fun h ↦
    hnot_fp (h.finitePresentation_of_fg (Submodule.fg_span_singleton xClass))
  exact ⟨Submodule.fg_span_singleton xClass, hnot_fp, inferInstance, hnot_coh, hnot_coh⟩

end TauCeti.CoherentChecks
