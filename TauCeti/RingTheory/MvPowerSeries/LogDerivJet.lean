/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.Derivation.Adjoin
import TauCeti.RingTheory.MvPowerSeries.DifferentialSubalgebra
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# A differential algebra for jets of theta products

Let `f' = g * f`, and suppose `d * g'` is an integral series in a formal parameter `y`
whose derivative is itself an integral series in `y`. Pull back `f`, `g`, and the integral
series in `y` along linear forms with coefficients divisible by `d`. The algebra they generate
is closed under partial derivatives and has integral constant terms. In particular, testing
integrality of derivatives of products of the pullbacks requires no coefficientwise integrality
of `f` or `g` themselves.

This is the differential-algebra step (`New.CMLattice.jetRing`, `New.CMLattice.pderiv_mem_jetRing`)
of `grh/src/New/Derivatives/Vacuum/JetIntegrality.lean` in
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

namespace MvPowerSeries

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Suppose `f' = g * f` and the scaled derivative `d • g'` is an `R`-series in `y`.
Substituting forms `b j` with zero constant term and partial derivatives in `dR` into `f`, `g`,
and `R`-series in `y` puts the results in a single subalgebra. It is stable under all partial
derivatives and its constant coefficients lie in the image of `R`.

In the theta application, `f` is the theta series, `g` its logarithmic derivative, and the
forms are integral linear forms multiplied by `d`. -/
theorem exists_subalgebra_closed_pderiv_of_derivative_eq_mul [Finite ι]
    {y f g : PowerSeries S} {Y G : PowerSeries R} {b : ι → MvPowerSeries σ S}
    {d : R} {c : σ → ι → R}
    (hy : PowerSeries.constantCoeff y = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (hY : PowerSeries.derivative y = PowerSeries.subst y Y)
    (hf : PowerSeries.derivative f = g * f)
    (hg : d • PowerSeries.derivative g = PowerSeries.subst y G)
    (hf₀ : PowerSeries.constantCoeff f ∈ Set.range (algebraMap R S))
    (hg₀ : PowerSeries.constantCoeff g ∈ Set.range (algebraMap R S))
    (hc : ∀ i j, pderiv i (b j) = algebraMap R (MvPowerSeries σ S) (d * c i j)) :
    ∃ B : Subalgebra R (MvPowerSeries σ S),
      (∀ H : MvPowerSeries ι R, subst (fun j ↦ PowerSeries.subst (b j) y) H ∈ B) ∧
      (∀ j, PowerSeries.subst (b j) f ∈ B ∧ PowerSeries.subst (b j) g ∈ B) ∧
      (∀ i : σ, Set.MapsTo (pderiv (R := S) i) (B : Set _) B) ∧
      ∀ F ∈ B, constantCoeff F ∈ Set.range (algebraMap R S) := by
  let a : ι → MvPowerSeries σ S := fun j ↦ PowerSeries.subst (b j) y
  have ha₀ : ∀ j, constantCoeff (a j) = 0 := fun j ↦
    PowerSeries.constantCoeff_subst_eq_zero (hb j) y hy
  let ha := hasSubst_of_constantCoeff_zero ha₀
  let A := (substAlgHom (R := R) ha).range
  have hparam (H : MvPowerSeries ι R) : subst a H ∈ A := ⟨H, substAlgHom_apply ha H⟩
  let s : Set (MvPowerSeries σ S) :=
    (A : Set _) ∪ Set.range (fun j ↦ PowerSeries.subst (b j) f) ∪
      Set.range (fun j ↦ PowerSeries.subst (b j) g)
  let B := Algebra.adjoin R s
  have hA : A ≤ B := fun _ h ↦ Algebra.subset_adjoin (Or.inl (Or.inl h))
  have hfg (j : ι) : PowerSeries.subst (b j) f ∈ B ∧ PowerSeries.subst (b j) g ∈ B :=
    ⟨Algebra.subset_adjoin (Or.inl (Or.inr ⟨j, rfl⟩)), Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩
  refine ⟨B, fun H ↦ hA (hparam H), hfg, fun i ↦ ?_, ?_⟩
  · have hb' (j : ι) := PowerSeries.HasSubst.of_constantCoeff_zero (hb j)
    have hstable : Set.MapsTo (pderiv (R := S) i) (A : Set _) A := by
      simpa only [A, a, PowerSeries.coe_substAlgHom] using
        mapsTo_pderiv_range_substAlgHom_of_derivative_eq_subst (R := R)
          (PowerSeries.HasSubst.of_constantCoeff_zero hy) hb' hY (hc i)
    refine (((pderiv (R := S) i).restrictScalars R).mapsTo_adjoin_iff s).2 ?_
    rintro _ ((h | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · exact hA (hstable h)
    · rw [Derivation.restrictScalars_apply, PowerSeries.pderiv_subst (hb' j), hf,
        PowerSeries.subst_mul (hb' j), hc]
      exact mul_mem (mul_mem (hfg j).2 (hfg j).1) (B.algebraMap_mem _)
    · -- The factor `d` from differentiating the form absorbs the denominator in `g'`.
      have he : PowerSeries.subst (b j) (d • PowerSeries.derivative g) =
          PowerSeries.subst (a j) G := (congrArg (PowerSeries.subst (b j)) hg).trans
        (PowerSeries.subst_comp_subst_apply
          (PowerSeries.HasSubst.of_constantCoeff_zero hy) (hb' j) G)
      rw [PowerSeries.subst_smul (hb' j), Algebra.smul_def, ← subst_X (R := R) ha j,
        ← subst_powerSeriesSubst ha (PowerSeries.HasSubst.X (S := R) j)] at he
      rw [Derivation.restrictScalars_apply, PowerSeries.pderiv_subst (hb' j), hc,
        map_mul, mul_left_comm, ← mul_assoc, he]
      exact mul_mem (hA (hparam _)) (B.algebraMap_mem _)
  · let C₀ : MvPowerSeries σ S →ₐ[R] S :=
      { constantCoeff with commutes' := fun r ↦ by simp [algebraMap_apply] }
    let I := (⊥ : Subalgebra R S).comap C₀
    have hI (F : MvPowerSeries σ S) : F ∈ I ↔ constantCoeff F ∈ Set.range (algebraMap R S) :=
      (Subalgebra.mem_comap _ _ _).trans Algebra.mem_bot
    suffices hB : B ≤ I from fun F hF ↦ (hI F).1 (hB hF)
    refine Algebra.adjoin_le ?_
    rintro F ((h | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · obtain ⟨H, rfl⟩ := (AlgHom.mem_range (substAlgHom (R := R) ha)).mp h
      exact (hI _).2 ⟨constantCoeff H, by
        rw [substAlgHom_apply, constantCoeff_subst_of_constantCoeff_zero ha ha₀]⟩
    · simpa only [SetLike.mem_coe, hI, PowerSeries.constantCoeff_subst_of_constantCoeff_zero (hb j),
        Algebra.algebraMap_self, RingHom.id_apply] using hf₀
    · simpa only [SetLike.mem_coe, hI, PowerSeries.constantCoeff_subst_of_constantCoeff_zero (hb j),
        Algebra.algebraMap_self, RingHom.id_apply] using hg₀

end MvPowerSeries
