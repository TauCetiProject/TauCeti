/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Measure
public import Mathlib.Analysis.Distribution.Distribution

/-!
# Mass of finite atomic distributions

A finite sum of real point masses has mass equal to the sum of the absolute values of its
coefficients. On an open set, only the atoms in that set contribute to local mass. Consequently
its mass measure is the sum of the corresponding weighted Dirac measures on the domain.

The points are indexed by a finite set, so coincident atoms have already been combined: opposite
coefficients at the same point cancel before taking absolute values. These formulas supply the
normalization of finite atomic zero-dimensional currents, using scalar test functions rather
than introducing another current carrier. They hold for every native test-function regularity.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (mass of zero-dimensional currents).
-/

public section

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions ENNReal

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {Ω : Opens E} {n : ℕ∞} {s : Finset E}

/-- The mass of finitely many point evaluations at distinct points is the sum of the absolute
coefficients. There is no positivity assumption on the coefficients. -/
theorem mass_sum_mul_apply (a : E → ℝ) (hs : (s : Set E) ⊆ Ω) :
    mass (fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x) = ∑ x ∈ s, ‖a x‖ₑ := by
  classical
  refine le_antisymm (mass_le_iff.2 fun φ hφ => ?_) ?_
  · exact (enorm_sum_le _ _).trans <| Finset.sum_le_sum fun x _ => by
      rw [enorm_mul]
      have hb : ‖φ x‖ₑ ≤ 1 := by
        simpa only [← ofReal_norm, ← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hφ x)
      simpa using mul_le_mul' (le_refl ‖a x‖ₑ) hb
  · obtain ⟨φ, hφ, hsign⟩ := TestFunction.exists_norm_le_one_mul_eq_abs (n := n) a hs
    have heval : (∑ x ∈ s, a x * φ x) = ∑ x ∈ s, |a x| :=
      Finset.sum_congr rfl hsign
    have habs : ‖∑ x ∈ s, |a x|‖ₑ = ∑ x ∈ s, ‖a x‖ₑ := by
      rw [Real.enorm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _),
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      simp [Real.enorm_eq_ofReal_abs]
    simpa only [heval, habs] using (enorm_le_mass (f := fun φ : 𝓓^{n}(Ω, ℝ) =>
      ∑ x ∈ s, a x * φ x) hφ)

open scoped Classical in
/-- Local mass of a finite atomic functional on an open set: exactly the atoms inside the
open set contribute. Atoms on its frontier do not contribute. -/
theorem localMass_sum_mul_apply (a : E → ℝ) (hs : (s : Set E) ⊆ Ω)
    {U : Set E} (hU : IsOpen U) :
    localMass (fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x) U =
      ∑ x ∈ s.filter (· ∈ U), ‖a x‖ₑ := by
  classical
  let Ω' : Opens E := Ω ⊓ ⟨U, hU⟩
  have hΩ' : Ω' ≤ Ω := inf_le_left
  have hfilter : (↑(s.filter (· ∈ U)) : Set E) ⊆ Ω' := by
    intro x hx
    exact ⟨hs (Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩
  have heq (φ : 𝓓^{n}(Ω', ℝ)) :
      (∑ x ∈ s, a x * (TestFunction.monoCLM ℝ φ : 𝓓^{n}(Ω, ℝ)) x) =
        ∑ x ∈ s.filter (· ∈ U), a x * φ x := by
    simp only [TestFunction.monoCLM_apply, hΩ', le_refl, and_self, ↓reduceIte]
    symm
    apply Finset.sum_filter_of_ne
    intro x _ hax
    exact (φ.tsupport_subset (subset_tsupport _ (by aesop))).2
  have hlocal : localMass (fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x) Ω' =
      localMass (fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x) U := by
    refine le_antisymm (localMass_mono inter_subset_right) (localMass_le_iff.2 ?_)
    intro φ hφU hφ
    exact enorm_le_localMass (f := fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x)
      (subset_inter φ.tsupport_subset hφU) hφ
  rw [← hlocal, ← mass_comp_monoCLM hΩ']
  have hfun : ((fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x) ∘ TestFunction.monoCLM ℝ) =
      (fun φ : 𝓓^{n}(Ω', ℝ) => ∑ x ∈ s.filter (· ∈ U), a x * φ x) := funext heq
  rw [hfun]
  exact mass_sum_mul_apply a hfilter

/-- The mass of a finite sum of scalar Dirac distributions is the sum of the absolute
coefficients. -/
theorem mass_sum_smul_delta (a : E → ℝ) (hs : (s : Set E) ⊆ Ω) :
    mass (∑ x ∈ s, a x • delta x : 𝓓'^{n}(Ω, ℝ)) = ∑ x ∈ s, ‖a x‖ₑ := by
  classical
  convert mass_sum_mul_apply (n := n) a hs using 1
  congr 1
  ext φ
  simp [delta_apply]

open scoped Classical in
/-- Local mass of a finite sum of scalar Dirac distributions on an open set is the sum of the
absolute coefficients at the atoms in that set. -/
theorem localMass_sum_smul_delta (a : E → ℝ) (hs : (s : Set E) ⊆ Ω)
    {U : Set E} (hU : IsOpen U) :
    localMass (∑ x ∈ s, a x • delta x : 𝓓'^{n}(Ω, ℝ)) U =
      ∑ x ∈ s.filter (· ∈ U), ‖a x‖ₑ := by
  classical
  convert localMass_sum_mul_apply (n := n) a hs hU using 1
  congr 1
  ext φ
  simp [delta_apply]

/-- The same normalization on actual test zero-forms: a finite atomic real zero-current has
mass equal to the sum of the absolute values of its coefficients. In particular this applies
to integer coefficients without changing the ambient real current space. -/
theorem mass_sum_mul_apply_finZero (a : E → ℝ) (hs : (s : Set E) ⊆ Ω) :
    mass (fun ω : 𝓓^{n}(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) => ∑ x ∈ s, a x * ω x ![]) =
      ∑ x ∈ s, ‖a x‖ₑ := by
  classical
  let e := ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)
  have heval (ω : E [⋀^Fin 0]→L[ℝ] ℝ) : e.symm ω = ω ![] := by
    rw [ContinuousAlternatingMap.constOfIsEmptyLIE_symm_apply]
    exact congrArg ω (Subsingleton.elim _ _)
  simpa [Function.comp_def, heval] using
    (mass_comp_postcompCLM_linearIsometryEquiv
      (fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x) e.symm).trans (mass_sum_mul_apply a hs)

variable [MeasurableSpace E] [BorelSpace E]

/-- The mass measure of a finite atomic distribution is the sum of the Dirac measures weighted
by the absolute coefficients. The measure lives on the open domain, not on its closure. -/
theorem massMeasure_sum_smul_delta (a : E → ℝ) (hs : (s : Set E) ⊆ Ω) :
    massMeasure (∑ x ∈ s, a x • (delta x : 𝓓'^{n}(Ω, ℝ))) =
      ∑ x : s, ‖a x‖₊ • Measure.dirac (⟨x, hs x.property⟩ : Ω) := by
  classical
  let T := ∑ x ∈ s, a x • (delta x : 𝓓'^{n}(Ω, ℝ))
  have hfinite : HasLocallyFiniteMass T := hasLocallyFiniteMass_of_mass_ne_top T (by
    rw [mass_sum_smul_delta a hs]
    exact ENNReal.sum_ne_top.mpr fun _ _ => enorm_ne_top)
  refine (eq_massMeasure_of_preimage_coe hfinite _ fun U hU => ?_).symm
  rw [localMass_sum_smul_delta a hs hU]
  conv_rhs => rw [Finset.sum_filter, ← Finset.sum_attach]
  simp [Set.indicator_apply, smul_ite, enorm_eq_nnnorm]

end Distribution
