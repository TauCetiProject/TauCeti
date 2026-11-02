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

/-- A test bounded by one can simultaneously realize the signs of finitely many coefficients.
This is the finite atomic mass norming test, with support in the specified domain. -/
private theorem exists_atomic_norming_test (a : E → ℝ) (hs : (s : Set E) ⊆ Ω) :
    ∃ φ : 𝓓^{n}(Ω, ℝ), (∀ x, ‖φ x‖ ≤ 1) ∧ ∀ x ∈ s, a x * φ x = |a x| := by
  classical
  obtain ⟨χ, hχ, hχ01⟩ := TestFunction.exists_eventually_eq_one (n := n) s.finite_toSet.isCompact hs
  let p := s.filter fun x => 0 ≤ a x
  let q := s.filter fun x => a x < 0
  let U : Opens E := ⟨(Ω : Set E) \ (q : Set E), Ω.isOpen.sdiff q.finite_toSet.isClosed⟩
  have hpU : (p : Set E) ⊆ U := by
    intro x hx
    simp only [p, Finset.mem_coe, Finset.mem_filter] at hx
    exact ⟨hs hx.1, by simp [q, hx.1, not_lt.mpr hx.2]⟩
  obtain ⟨ψ, hψ, hψ01⟩ :=
    TestFunction.exists_eventually_eq_one (n := n) p.finite_toSet.isCompact hpU
  let φ : 𝓓^{n}(Ω, ℝ) :=
    ⟨fun x => χ x * (2 * ψ x - 1),
      χ.contDiff.mul ((contDiff_const.mul ψ.contDiff).sub contDiff_const),
      χ.hasCompactSupport.mul_right,
      tsupport_mul_subset_left.trans χ.tsupport_subset⟩
  refine ⟨φ, fun x => ?_, fun x hx => ?_⟩
  · have h₁ := hχ01 x
    have h₂ := hψ01 x
    rw [Real.norm_eq_abs, abs_le]
    dsimp [φ]
    constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · have hχx : χ x = 1 := hχ.self_of_nhdsSet x hx
    by_cases hxpos : 0 ≤ a x
    · have hψx : ψ x = 1 := hψ.self_of_nhdsSet x (by simp [p, hx, hxpos])
      norm_num [φ, hχx, hψx, abs_of_nonneg hxpos]
    · have hxU : x ∉ U := by simp [U, q, hx, lt_of_not_ge hxpos]
      have hψx : ψ x = 0 := ψ.zero_on_compl hxU
      simp [φ, hχx, hψx, abs_of_neg (lt_of_not_ge hxpos)]

/-- The mass of finitely many point evaluations at distinct points is the sum of the absolute
coefficients. There is no positivity assumption on the coefficients. -/
theorem mass_sum_mul_apply (a : E → ℝ) (hs : (s : Set E) ⊆ Ω) :
    mass (fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x) = ∑ x ∈ s, ‖a x‖ₑ := by
  classical
  refine le_antisymm (mass_le_iff.2 fun φ hφ => ?_) ?_
  · exact (enorm_sum_le _ _).trans <| Finset.sum_le_sum fun x hx => by
      rw [enorm_mul]
      have hb : ‖φ x‖ₑ ≤ 1 := by
        simpa only [← ofReal_norm, ← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hφ x)
      simpa using mul_le_mul' (le_refl ‖a x‖ₑ) hb
  · obtain ⟨φ, hφ, hsign⟩ := exists_atomic_norming_test (n := n) a hs
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
    intro x hx hax
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
  refine le_antisymm (mass_le_iff.2 fun ω hω => ?_) ?_
  · let φ := TestFunction.postcompCLM e.symm.toContinuousLinearEquiv.toContinuousLinearMap ω
    have hφ : ∀ x, ‖φ x‖ ≤ 1 := by simpa [φ] using hω
    have h := enorm_le_mass (f := fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x) hφ
    simpa [mass_sum_mul_apply a hs, φ, heval] using h
  · rw [← mass_sum_mul_apply (n := n) a hs]
    refine mass_le_iff.2 fun φ hφ => ?_
    let ω := TestFunction.postcompCLM e.toContinuousLinearEquiv.toContinuousLinearMap φ
    have hω : ∀ x, ‖ω x‖ ≤ 1 := by simpa [ω] using hφ
    simpa [ω, e] using (enorm_le_mass (f := fun ω : 𝓓^{n}(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) =>
      ∑ x ∈ s, a x * ω x ![]) hω)

variable [MeasurableSpace E] [BorelSpace E]

/-- The mass measure of a finite atomic distribution is the sum of the Dirac measures weighted
by the absolute coefficients. The measure lives on the open domain, not on its closure. -/
theorem massMeasure_sum_smul_delta (a : E → ℝ) (hs : (s : Set E) ⊆ Ω) :
    massMeasure (∑ x ∈ s, a x • (delta x : 𝓓'^{n}(Ω, ℝ))) =
      ∑ x : s, ‖a x‖₊ • Measure.dirac (⟨x, hs x.property⟩ : Ω) := by
  classical
  let T := ∑ x ∈ s, a x • (delta x : 𝓓'^{n}(Ω, ℝ))
  have hT (φ : 𝓓^{n}(Ω, ℝ)) : T φ = ∑ x ∈ s, a x * φ x := by
    simp [T, delta_apply]
  have hcoe : ⇑T = fun φ : 𝓓^{n}(Ω, ℝ) => ∑ x ∈ s, a x * φ x := funext hT
  have hmass : mass T = ∑ x ∈ s, ‖a x‖ₑ := by
    rw [hcoe, mass_sum_mul_apply a hs]
  have hfinite : HasLocallyFiniteMass T := hasLocallyFiniteMass_of_mass_ne_top T (by
    rw [hmass]
    exact ENNReal.sum_ne_top.mpr fun _ _ => enorm_ne_top)
  refine (eq_massMeasure_of_preimage_coe hfinite _ fun U hU => ?_).symm
  have hlocal : localMass T U = ∑ x ∈ s.filter (· ∈ U), ‖a x‖ₑ := by
    rw [hcoe, localMass_sum_mul_apply a hs hU]
  rw [hlocal]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (hU.preimage continuous_subtype_val).measurableSet,
    Set.indicator_apply, Set.mem_preimage, Pi.one_apply, smul_ite, smul_zero]
  rw [Finset.sum_coe_sort s (fun x => if x ∈ U then ‖a x‖₊ • (1 : ℝ≥0∞) else 0),
    Finset.sum_filter]
  simp [enorm_eq_nnnorm]

end Distribution
