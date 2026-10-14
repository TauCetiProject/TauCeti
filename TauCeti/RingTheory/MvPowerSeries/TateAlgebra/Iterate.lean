/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.TateAlgebra
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Iteration of Gauss-normed Tate algebras

Separating one variable identifies unit-radius restricted series in `Option σ` with univariate
restricted series whose coefficients are unit-radius restricted series in `σ`. The comparison
preserves the Gauss norm, so it identifies the Banach rings when the coefficient ring is complete.
It allows Weierstrass division and preparation to be applied with a Tate algebra in the remaining
variables as coefficient ring.

The construction restricts Mathlib's `MvPowerSeries.optionEquivLeft`; restrictedness of the
coefficient slices and convergence of their Gauss norms are both required. Merely requiring each
slice to be restricted would not characterize multivariate restricted series.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.1.1 and 5.2.1.
-/

public section

namespace TauCeti.Huber

open Filter MvPowerSeries
open scoped Topology

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

local notation "Tate" => IsRestricted.subring (R := R) (fun _ : σ ↦ 1)
local notation "ExtraTate" => IsRestricted.subring (R := R) (fun _ : Option σ ↦ 1)
local notation "IteratedTate" => PowerSeries.IsRestricted.subring (R := Tate) 1

omit [IsUltrametricDist R] in
/-- Each coefficient slice obtained by separating one variable is restricted. -/
theorem isRestricted_coeff_optionEquivLeft {f : MvPowerSeries (Option σ) R}
    (hf : IsRestricted (fun _ ↦ 1) f) (n : ℕ) :
    IsRestricted (fun _ ↦ 1) (PowerSeries.coeff n (optionEquivLeft σ R f)) := by
  have hi : Function.Injective (fun t : σ →₀ ℕ ↦ t.optionElim n) := by
    intro t u h
    simpa using congrArg Finsupp.some h
  simpa [IsRestricted, Function.comp_def, coeff_coeff_optionEquivLeft] using
    hf.comp hi.tendsto_cofinite

/-- The coefficient slices, regarded as a formal univariate series over the restricted subring. -/
private noncomputable def restrictedOptionSeries (f : ExtraTate) : PowerSeries Tate := by
  refine PowerSeries.mk fun n ↦ ?_
  refine ⟨PowerSeries.coeff n (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)), ?_⟩
  exact isRestricted_coeff_optionEquivLeft (σ := σ) (R := R) f.2 n

private theorem coeff_restrictedOptionSeries (f : ExtraTate) (n : ℕ) :
    (PowerSeries.coeff (R := Tate) n (restrictedOptionSeries f) : MvPowerSeries σ R) =
      PowerSeries.coeff n (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)) := by
  simp [restrictedOptionSeries]

private theorem isRestricted_restrictedOptionSeries (f : ExtraTate) :
    PowerSeries.IsRestricted 1 (restrictedOptionSeries f) := by
  rw [PowerSeries.isRestricted_iff]
  simp only [one_pow, mul_one]
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun n ↦ hb.trans_le (norm_nonneg _), ?_⟩
  intro ε hε
  have hfinite : {t | ε / 2 ≤ ‖coeff t (f : MvPowerSeries (Option σ) R)‖}.Finite := by
    have h := f.2.eventually (gt_mem_nhds (half_pos hε))
    simpa [eventually_cofinite, not_lt] using h
  have hout : ∀ᶠ n : ℕ in cofinite, n ∉ (fun t : Option σ →₀ ℕ ↦ t none) ''
      {t | ε / 2 ≤ ‖coeff t (f : MvPowerSeries (Option σ) R)‖} :=
    (hfinite.image _).compl_mem_cofinite
  filter_upwards [hout] with n hn
  refine lt_of_le_of_lt (norm_le_iff (half_pos hε).le |>.mpr fun t ↦ ?_) (half_lt_self hε)
  simp only [one_pow, Finsupp.prod_fun_one, mul_one]
  rw [coeff_restrictedOptionSeries, coeff_coeff_optionEquivLeft]
  exact le_of_lt (lt_of_not_ge fun ht ↦ hn ⟨t.optionElim n, ht, by simp⟩)

/-- Flattening a restricted series over a restricted-series coefficient ring is restricted. -/
private theorem isRestricted_optionEquivLeft_symm (g : IteratedTate) :
    IsRestricted (fun _ ↦ 1) ((optionEquivLeft σ R).symm
      (PowerSeries.map (Tate).subtype (g : PowerSeries Tate))) := by
  classical
  let h := (optionEquivLeft σ R).symm (PowerSeries.map (Tate).subtype (g : PowerSeries Tate))
  have hcoeff (t : Option σ →₀ ℕ) : coeff t h =
      coeff t.some (PowerSeries.coeff (R := Tate) (t none) (g : PowerSeries Tate) :
        MvPowerSeries σ R) := by
    rw [← Finsupp.optionElim_some t, ← coeff_coeff_optionEquivLeft]
    simp [h]
  rw [IsRestricted]
  simp only [one_pow, Finsupp.prod_fun_one, mul_one]
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun t ↦ hb.trans_le (norm_nonneg _), ?_⟩
  intro ε hε
  have hg : Tendsto (fun n ↦ ‖PowerSeries.coeff (R := Tate) n (g : PowerSeries Tate)‖)
      cofinite (𝓝 0) := by
    have hg' : PowerSeries.IsRestricted 1 (g : PowerSeries Tate) := g.2
    simpa only [PowerSeries.isRestricted_iff, one_pow, mul_one] using hg'
  have houter : {n | ε ≤ ‖PowerSeries.coeff (R := Tate) n (g : PowerSeries Tate)‖}.Finite := by
    simpa [eventually_cofinite, not_lt] using hg.eventually (gt_mem_nhds hε)
  have hinner (n : ℕ) : {t | ε ≤ ‖coeff t
      (PowerSeries.coeff (R := Tate) n (g : PowerSeries Tate) : MvPowerSeries σ R)‖}.Finite := by
    simpa [eventually_cofinite, not_lt] using
      (PowerSeries.coeff n (g : PowerSeries Tate)).2.eventually (gt_mem_nhds hε)
  have hbad : {t : Option σ →₀ ℕ | ε ≤ ‖coeff t h‖}.Finite := by
    refine ((houter.biUnion fun n _ ↦ (hinner n).image
      (fun t : σ →₀ ℕ ↦ t.optionElim n))).subset ?_
    intro t ht
    rw [Set.mem_ofPred_eq, hcoeff] at ht
    have hle := norm_coeff_mul_prod_le (PowerSeries.coeff (t none) (g : PowerSeries Tate)) t.some
    simp only [one_pow, Finsupp.prod_fun_one, mul_one] at hle
    exact Set.mem_iUnion₂.mpr ⟨t none, ht.trans hle,
      ⟨t.some, ht, Finsupp.optionElim_some t⟩⟩
  simpa [eventually_cofinite, not_lt] using hbad

/-- Flattening the iterated restricted-series ring into the multivariate restricted-series ring. -/
private noncomputable def restrictedOptionFlatten : IteratedTate →+* ExtraTate := by
  refine (((optionEquivLeft σ R).symm.toRingHom.comp (PowerSeries.map (Tate).subtype)).comp
    (IteratedTate).subtype).codRestrict _ ?_
  exact isRestricted_optionEquivLeft_symm

private theorem restrictedOptionFlatten_bijective :
    Function.Bijective (restrictedOptionFlatten (σ := σ) (R := R)) := by
  constructor
  · intro g h heq
    apply Subtype.ext
    apply PowerSeries.map_injective (Tate).subtype Subtype.val_injective
    apply (optionEquivLeft σ R).symm.injective
    exact congrArg Subtype.val heq
  · intro f
    refine ⟨⟨restrictedOptionSeries f, isRestricted_restrictedOptionSeries f⟩, ?_⟩
    apply Subtype.ext
    apply (optionEquivLeft σ R).injective
    simp only [restrictedOptionFlatten]
    apply PowerSeries.ext
    intro n
    simp [coeff_restrictedOptionSeries]

/-- The unit-radius Tate algebra with one extra variable is the univariate Tate algebra over
its remaining-variable Tate algebra. No completeness or finiteness of the variable type is
needed. -/
noncomputable def restrictedOptionEquiv : ExtraTate ≃+* IteratedTate :=
  (RingEquiv.ofBijective (restrictedOptionFlatten (σ := σ) (R := R))
    (restrictedOptionFlatten_bijective (σ := σ) (R := R))).symm

/-- Flattening the comparison recovers Mathlib's inverse formal-series comparison. -/
@[simp]
theorem coe_restrictedOptionEquiv_symm (g : IteratedTate) :
    (restrictedOptionEquiv.symm g : MvPowerSeries (Option σ) R) =
      (optionEquivLeft σ R).symm (PowerSeries.map (Tate).subtype (g : PowerSeries Tate)) := (rfl)

/-- The iterated series has exactly the coefficient slices of Mathlib's formal-series comparison. -/
@[simp]
theorem coeff_restrictedOptionEquiv (f : ExtraTate) (n : ℕ) :
    (PowerSeries.coeff (R := Tate) n (restrictedOptionEquiv f : PowerSeries Tate) :
      MvPowerSeries σ R) =
      PowerSeries.coeff n (optionEquivLeft σ R (f : MvPowerSeries (Option σ) R)) := by
  have h := (restrictedOptionEquiv (σ := σ) (R := R)).symm_apply_apply f
  have h' := congrArg (fun a : ExtraTate ↦ PowerSeries.coeff n (optionEquivLeft σ R
    (a : MvPowerSeries (Option σ) R))) h
  rw [coe_restrictedOptionEquiv_symm, AlgEquiv.apply_symm_apply, PowerSeries.coeff_map] at h'
  exact h'

/-- The Fubini comparison preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedOptionEquiv (f : ExtraTate) : ‖restrictedOptionEquiv f‖ = ‖f‖ := by
  apply le_antisymm
  · rw [TauCeti.PowerSeries.norm_le_iff (norm_nonneg _)]
    intro n
    simp only [one_pow, mul_one]
    rw [norm_le_iff (norm_nonneg _)]
    intro t
    simp only [one_pow, Finsupp.prod_fun_one, mul_one]
    rw [coeff_restrictedOptionEquiv, coeff_coeff_optionEquivLeft]
    simpa using norm_coeff_mul_prod_le f (t.optionElim n)
  · rw [norm_le_iff (norm_nonneg _)]
    intro t
    simp only [one_pow, Finsupp.prod_fun_one, mul_one]
    rw [← Finsupp.optionElim_some t, ← coeff_coeff_optionEquivLeft,
      ← coeff_restrictedOptionEquiv]
    have h₁ := norm_coeff_mul_prod_le
      (PowerSeries.coeff (t none) (restrictedOptionEquiv f : PowerSeries Tate)) t.some
    have h₂ := TauCeti.PowerSeries.norm_coeff_mul_pow_le (restrictedOptionEquiv f) (t none)
    simpa using h₁.trans (by simpa using h₂)

/-- The Fubini ring isomorphism is an isometry for the Gauss norms. -/
theorem isometry_restrictedOptionEquiv :
    Isometry (restrictedOptionEquiv (σ := σ) (R := R)) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr norm_restrictedOptionEquiv

end TauCeti.Huber
