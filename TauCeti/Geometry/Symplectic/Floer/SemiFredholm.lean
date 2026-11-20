/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
public import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.MeasureTheory.Integral.Rectangle
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The semi-Fredholm estimate of the linearized Floer operator on a cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space and let `D_u` be the linearized Floer
operator (`TauCeti.SymplecticForm.floerLinearization`) along a map `u : ℝ × ℝ → V` of period one
in `t`. The Fredholm property of `D_u` on the cylinder `ℝ × S¹` rests on the estimate

`‖ξ‖²_{W^{1,2}} ≤ C (‖D_u ξ‖²_{L²} + ‖ξ‖²_{L²([-T, T] × S¹)})`

for sections `ξ` of compact support, with `C` and `T` independent of `ξ`. Since restriction to
the compact cylinder `[-T, T] × S¹` is compact from `W^{1,2}` to `L²`, Peetre's compact-error
estimate (`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`) turns such an estimate
into finite dimensional kernel and closed range of the extension of `D_u` to `W^{1,2}`. This file
proves the estimate by patching the two estimates already available:

* on the far parts of the ends, where `u` is close to a nondegenerate orbit, `D_u` controls the
  whole `W^{1,2}` norm
  (`TauCeti.SymplecticForm.exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization`);
* on a compact cylinder `[-T, T] × S¹`, `D_u` and the `L²` norm of `ξ` control the derivatives of
  `ξ`, by the interior estimate
  `exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_periodic`.

Cut `ξ` into three pieces `β₊ ξ`, `β₋ ξ` and `β₀ ξ` with smooth cutoffs `β₊`, `β₋`, `β₀` in `s`
summing to one, supported near `+∞`, near `-∞` and in `[-T, T]`. The operator differentiates the
cutoffs only in the `s` direction: `D_u (β ξ) = β D_u ξ + β' ξ`
(`TauCeti.SymplecticForm.floerLinearization_smul_fst`), and `β'` is supported in `[-T, T]`, so the
error terms are controlled by the `L²` norm of `ξ` over the compact cylinder.

* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_ends` is the
  patching argument: for any data `J`, `K_s`, `K_t` that are regular along `u`, with `J` compatible
  along `u`, and any bounded continuous `c`, estimates of `D_u - c(s)` on the two ends imply the
  semi-Fredholm estimate of `D_u - c(s)`. On the compact cylinder the term `c(s) ξ` is absorbed
  into the `L²` norm of `ξ`. The case `c = 0` is
  `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_ends`.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical` is the
  semi-Fredholm estimate for Floer data that are cylindrical near the ends: the data are
  `(J₋_t, 0, H₋_t)` for `s ≤ -R` and `(J₊_t, 0, H₊_t)` for `s ≥ R`, possibly with different
  Hamiltonians and almost complex structures at the two ends, as for a continuation cylinder, and
  `u` is asymptotic at `±∞` to nondegenerate one-periodic orbits of `H±`. Beyond `±R` the operator
  `D_u` is the operator of the end data
  (`TauCeti.SymplecticForm.floerLinearization_congr_data`), so its end estimates are those of
  `exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq`, in the norm of
  `V`.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add` is the case of a Floer
  trajectory: `K = H_t dt` with `J_t` independent of `s`.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add` is the
  semi-Fredholm estimate along a Floer trajectory between the Sobolev spaces with an exponential
  weight `e^{κ(s)}`, read as the estimate of `D_u - κ'(s)`, when the slope `κ'` equals constants
  `δ±` near `±∞` for which the shifted fields `dX_{H_t}(x±(t)) - δ± J_t(x±(t))` have
  nondegenerate return maps; for one-periodic data this says that `δ±` are not eigenvalues of the
  asymptotic operators at the ends. It is a case of
  `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_cylindrical`,
  the same estimate for data that are cylindrical near the ends, whose end estimates are
  `exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sub_smul_sq` and whose
  case `c = 0` is
  `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical`.

Sections are `C²` maps `ξ : ℝ × ℝ → V` of period one in `t` that vanish outside a strip
`(a, b) × ℝ`, and the integrals are over the fundamental domain `[a, b] × [0, 1]`. The Sobolev
completion and the Fredholm property itself are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)` along a Floer
  trajectory.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate.
-/

public section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The `W^{1,2}` energy over `[a', b'] × [0, 1]` of a map vanishing for `s ∉ (a, b)` is its
energy over `[a, b] × [0, 1]`. -/
private theorem setIntegral_sobolev_eq {ξ : ℝ × ℝ → V} {a b a' b' : ℝ}
    (hξ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) (ha : a' ≤ a) (hb : b ≤ b') :
    ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) =
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) :=
  setIntegral_Icc_prod_eq_of_forall_fst_notMem_eq_zero measurableSet_Icc ha hb fun z hz ↦ by
    have h := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hξ hz
    simp [h.fderiv_eq, h.eq_of_nhds]

/-- The `L²` norm of `D_u ξ - c(s) ξ` over `[a', b'] × [0, 1]`, for `ξ` vanishing for
`s ∉ (a, b)`, is its norm over `[a, b] × [0, 1]`. -/
private theorem setIntegral_norm_floerLinearization_sub_smul_sq_eq (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (c : ℝ → ℝ)
    {ξ : ℝ × ℝ → V} {a b a' b' : ℝ} (hξ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) (ha : a' ≤ a)
    (hb : b ≤ b') :
    ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2 =
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2 :=
  setIntegral_Icc_prod_eq_of_forall_fst_notMem_eq_zero measurableSet_Icc ha hb fun z hz ↦ by
    have h := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hξ hz
    rw [ω.floerLinearization_congr_of_eventuallyEq J Ks Kt u h, floerLinearization_zero,
      h.eq_of_nhds]
    simp

/-- **The `L²` norm of `D_u - c(s)` on a cut-off section.** For a cutoff `β(s)` with `|β| ≤ 1`,
`|β'| ≤ M` and `β'` supported in `[-T, T]`, the `L²` norm of
`(D_u - c) (β ξ) = β (D_u - c) ξ + β' ξ` is bounded by those of `(D_u - c) ξ` and of `ξ` over
`[-T, T] × [0, 1]`. -/
private theorem setIntegral_norm_floerLinearization_sub_smul_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) {c : ℝ → ℝ}
    (hc : Continuous c) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) {a b : ℝ} (hξ₀ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0)
    {β β' : ℝ → ℝ} (hβ : ∀ s, HasDerivAt β (β' s) s) (hβ'c : Continuous β')
    (hβ₁ : ∀ s, |β s| ≤ 1) {M T : ℝ} (hM : ∀ s, |β' s| ≤ M)
    (hβT : ∀ s, s < -T ∨ T < s → β' s = 0) {a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b')
    (hTa : a' ≤ -T) (hTb : T ≤ b') :
    ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1,
        ‖ω.floerLinearization J Ks Kt u (fun w ↦ β w.1 • ξ w) z - c z.1 • β z.1 • ξ z‖ ^ 2 ≤
      2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
          ‖ω.floerLinearization J Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2) +
        2 * M ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 := by
  set P : ℝ × ℝ → V := fun z ↦ ω.floerLinearization J Ks Kt u ξ z - c z.1 • ξ z
  have hD (z : ℝ × ℝ) : ω.floerLinearization J Ks Kt u (fun w ↦ β w.1 • ξ w) z -
      c z.1 • β z.1 • ξ z = β z.1 • P z + β' z.1 • ξ z := by
    rw [ω.floerLinearization_smul_fst J Ks Kt u ξ (hβ z.1) (hξ.differentiable one_ne_zero z)]
    simp only [P, smul_sub, smul_comm (c z.1) (β z.1)]
    abel
  have hPc : Continuous P :=
    (ω.continuous_floerLinearization hJ hKs hKt hu hξ).sub
      ((hc.comp continuous_fst).smul hξ.continuous)
  have hβ'ξ : Continuous fun z : ℝ × ℝ ↦ β' z.1 ^ 2 * ‖ξ z‖ ^ 2 := by
    have := hξ.continuous
    fun_prop
  have hrect : MeasurableSet (Icc a' b' ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  simp_rw [hD]
  calc _ ≤ ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (2 * ‖P z‖ ^ 2 + 2 * (β' z.1 ^ 2 * ‖ξ z‖ ^ 2)) := by
        refine setIntegral_mono_on ?_ ?_ hrect fun z _ ↦ ?_
        · refine Continuous.integrableOn_Icc_prod_Icc ?_
          have hβc : Continuous β := continuous_iff_continuousAt.2 fun s ↦ (hβ s).continuousAt
          have := hξ.continuous
          fun_prop
        · exact Continuous.integrableOn_Icc_prod_Icc (by fun_prop)
        have h : ‖β z.1 • P z + β' z.1 • ξ z‖ ≤ ‖P z‖ + |β' z.1| * ‖ξ z‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
          exact mul_le_of_le_one_left (norm_nonneg _) (hβ₁ z.1)
        calc _ ≤ (‖P z‖ + |β' z.1| * ‖ξ z‖) ^ 2 := by gcongr
          _ ≤ 2 * (‖P z‖ ^ 2 + (|β' z.1| * ‖ξ z‖) ^ 2) := add_sq_le
          _ = _ := by rw [mul_pow, sq_abs]; ring
    _ = 2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P z‖ ^ 2) +
          2 * ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, β' z.1 ^ 2 * ‖ξ z‖ ^ 2 := by
        rw [integral_add (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
            (Continuous.integrableOn_Icc_prod_Icc (by fun_prop)), integral_const_mul,
          integral_const_mul,
          setIntegral_norm_floerLinearization_sub_smul_sq_eq ω J Ks Kt u c hξ₀ ha hb,
          setIntegral_Icc_prod_eq_of_forall_fst_notMem_eq_zero measurableSet_Icc hTa hTb
            fun z hz ↦ by
              rw [mem_Icc, not_and_or, not_le, not_le] at hz
              simp [hβT z.1 hz]]
    _ ≤ _ := by
        have h : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, β' z.1 ^ 2 * ‖ξ z‖ ^ 2 ≤
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, M ^ 2 * ‖ξ z‖ ^ 2 := by
          refine setIntegral_mono_on hβ'ξ.integrableOn_Icc_prod_Icc
            (Continuous.integrableOn_Icc_prod_Icc (by have := hξ.continuous; fun_prop))
            (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
          have h₁ : β' z.1 ^ 2 ≤ M ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hM z.1) 2
          gcongr
        rw [integral_const_mul] at h
        linarith

omit [FiniteDimensional ℝ V] in
/-- **Removing a bounded zeroth-order term.** If `|c| ≤ B`, then pointwise
`‖f‖² ≤ 2 ‖f - c(s) g‖² + 2 B² ‖g‖²`, so the same bound holds for the `L²` norms over
`[p, q] × [0, 1]`. -/
private theorem setIntegral_norm_sq_le_two_mul_setIntegral_norm_sub_smul_sq_add
    {f g : ℝ × ℝ → V} (hf : Continuous f) (hg : Continuous g) {c : ℝ → ℝ} (hc : Continuous c)
    {B : ℝ} (hcB : ∀ s, ‖c s‖ ≤ B) (p q : ℝ) :
    ∫ z in Icc p q ×ˢ Icc (0 : ℝ) 1, ‖f z‖ ^ 2 ≤
      2 * (∫ z in Icc p q ×ˢ Icc (0 : ℝ) 1, ‖f z - c z.1 • g z‖ ^ 2) +
        2 * B ^ 2 * ∫ z in Icc p q ×ˢ Icc (0 : ℝ) 1, ‖g z‖ ^ 2 := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
      (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))]
  refine setIntegral_mono_on (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
    (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
    (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
  have h := norm_sub_sq_le_two_mul (f z) 0 (c z.1 • g z)
  rw [sub_zero, zero_sub, norm_neg, norm_smul, mul_pow] at h
  have hB := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hcB z.1) 2)
    (sq_nonneg ‖g z‖)
  linarith

/-- **Patching end estimates into the semi-Fredholm estimate, with a zeroth-order weight term.**
Let `J(z)` be compatible along `u`, with `J` `C¹` and `K_s`, `K_t` `C²` at the points `(z, u z)`,
and `u` `C¹`, and let `c : ℝ → ℝ` be continuous and bounded by `B`. Consider the operator
`P ξ = D_u ξ - c(s) ξ`; for `c = κ'` it is the linearized Floer operator `D_u` conjugated by the
exponential weight `e^{κ(s)}`. Suppose that `P` controls the `W^{1,2}` norm on the two ends: there
are constants `Cp`, `Cm` such that every `C²` map `ξ` of period one in `t`, vanishing on two slices
`s = a ≤ b` with `Rp ≤ a`, respectively with `b ≤ Rm`, satisfies
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ Cp ∫ ‖P ξ‖²`, respectively `≤ Cm ∫ ‖P ξ‖²`, over
`[a, b] × [0, 1]`. Then there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in
`t` vanishing for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖P ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_ends
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {c : ℝ → ℝ} (hcc : Continuous c) {B : ℝ}
    (hcB : ∀ s, ‖c s‖ ≤ B) {Cp Cm Rp Rm : ℝ}
    (hp : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, Rp ≤ a → a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cp * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2)
    (hm : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → b ≤ Rm → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cm * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  set R := max (max Rp (-Rm)) 0
  have hR₀ : 0 ≤ R := le_max_right _ _
  have hRp : Rp ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRm : -R ≤ Rm := by
    have := (le_max_right Rp (-Rm)).trans (le_max_left _ (0 : ℝ))
    linarith
  -- The cutoffs `βp`, `βm`, `β₀`, near `+∞`, near `-∞` and on `[-T, T]`, sum to one.
  obtain ⟨M, βp, βm, β₀, hβsum, hβpR, hβmR, hβ₀T, hβ⟩ := exists_cutoffs_add_add_eq_one hR₀
  set T := R + 1
  obtain ⟨hβpc, hβp1, hβpM, hβpT⟩ := hβ βp (by simp)
  obtain ⟨hβmc, hβm1, hβmM, hβmT⟩ := hβ βm (by simp)
  obtain ⟨hβ₀c, hβ₀1, hβ₀M, hβ₀T'⟩ := hβ β₀ (by simp)
  -- The estimate on the compact cylinder `[-T, T] × [0, 1]`.
  obtain ⟨C₀, hC₀, hcore⟩ :=
    ω.exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_periodic
      (a := -T) (b := T) (by linarith) (fun z _ ↦ hJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z)
      (fun z _ ↦ hu.contDiffAt) (fun z _ ↦ hc z)
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  set L := 2 + 2 * M ^ 2
  refine ⟨3 * ((max Cp 0 + max Cm 0) * L + C₀ * (2 * L + 2 * B ^ 2 + 1) + 1), by positivity, T,
    fun ξ hξ hper a b hab hξ₀ ↦ ?_⟩
  have hξ₀' (s t : ℝ) (h : s ≤ a ∨ b ≤ s) : ξ (s, t) = 0 :=
    hξ₀ s t fun h' ↦ by rcases h with h | h <;> linarith [h'.1, h'.2]
  -- The three pieces of `ξ`.
  set ξp : ℝ × ℝ → V := fun w ↦ βp w.1 • ξ w
  set ξm : ℝ × ℝ → V := fun w ↦ βm w.1 • ξ w
  set ξ₀ : ℝ × ℝ → V := fun w ↦ β₀ w.1 • ξ w
  have hξp : ContDiff ℝ 2 ξp := (hβpc.comp contDiff_fst).smul hξ
  have hξm : ContDiff ℝ 2 ξm := (hβmc.comp contDiff_fst).smul hξ
  have hξ₀c : ContDiff ℝ 2 ξ₀ := (hβ₀c.comp contDiff_fst).smul hξ
  have hsplit : ξ = fun w ↦ ξp w + ξm w + ξ₀ w := funext fun w ↦ by
    simp only [ξp, ξm, ξ₀, ← add_smul, hβsum, one_smul]
  -- Each piece vanishes outside a window: near `+∞`, near `-∞`, and in `[-T, T]`.
  have hvp (s t : ℝ) (hs : s ∉ Ioo (max a R) (max b R)) : ξp (s, t) = 0 := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    simp only [ξp]
    rcases hs with hs | hs
    · rcases le_max_iff.1 hs with h | h
      · rw [hξ₀' s t (Or.inl h), smul_zero]
      · rw [hβpR s h, zero_smul]
    · rw [hξ₀' s t (Or.inr (max_le_iff.1 hs).1), smul_zero]
  have hvm (s t : ℝ) (hs : s ∉ Ioo (min a (-R)) (min b (-R))) : ξm (s, t) = 0 := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    simp only [ξm]
    rcases hs with hs | hs
    · rw [hξ₀' s t (Or.inl (le_min_iff.1 hs).1), smul_zero]
    · rcases min_le_iff.1 hs with h | h
      · rw [hξ₀' s t (Or.inr h), smul_zero]
      · rw [hβmR s h, zero_smul]
  have hv₀ (s t : ℝ) (hs : s ∉ Ioo (-T) T) : ξ₀ (s, t) = 0 := by
    simp only [ξ₀, hβ₀T s hs, zero_smul]
  have hper₀ (s t : ℝ) : ξ₀ (s, t + 1) = ξ₀ (s, t) := by simp only [ξ₀, hper]
  -- The window `[a', b'] ⊇ [a, b] ∪ [-T, T]` carrying all the pieces.
  set a' := min a (-T)
  set b' := max b T
  have hrect : MeasurableSet (Icc a' b' ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  set X := ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J' Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2
  set Y := ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2
  have hX : 0 ≤ X := setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
    fun _ _ ↦ sq_nonneg _
  have hY : 0 ≤ Y := setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
    fun _ _ ↦ sq_nonneg _
  have hcut {β : ℝ → ℝ} (hβc : ContDiff ℝ 2 β) (hβ₁ : ∀ s, |β s| ≤ 1)
      (hβM : ∀ s, |deriv β s| ≤ M) (hβT : ∀ s, s < -T ∨ T < s → deriv β s = 0) :
      ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1,
          ‖ω.floerLinearization J' Ks Kt u (fun w ↦ β w.1 • ξ w) z - c z.1 • β z.1 • ξ z‖ ^ 2 ≤
            L * (X + Y) := by
    have h := ω.setIntegral_norm_floerLinearization_sub_smul_smul_sq_le (J := J') hJ hKs hKt hu hcc
      (hξ.of_le one_le_two) hξ₀ (fun s ↦ (hβc.differentiable two_ne_zero s).hasDerivAt)
      (hβc.continuous_deriv one_le_two) hβ₁ hβM hβT (min_le_left _ _) (le_max_left _ _)
      (min_le_right _ _) (le_max_right _ _)
    nlinarith [mul_nonneg (sq_nonneg M) hX]
  -- The pointwise splitting of the `W^{1,2}` energy density.
  have hE (z : ℝ × ℝ) :
      ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2 ≤
        3 * ((‖fderiv ℝ ξp z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξp z stdComplexLineImag‖ ^ 2 +
            ‖ξp z‖ ^ 2) +
          (‖fderiv ℝ ξm z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξm z stdComplexLineImag‖ ^ 2 +
            ‖ξm z‖ ^ 2) +
          (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2 +
            ‖ξ₀ z‖ ^ 2)) := by
    have dp := hξp.differentiable two_ne_zero z
    have dm := hξm.differentiable two_ne_zero z
    have d₀ := hξ₀c.differentiable two_ne_zero z
    have hval : ξ z = ξp z + ξm z + ξ₀ z := congrFun hsplit z
    have hder : fderiv ℝ ξ z = fderiv ℝ ξp z + fderiv ℝ ξm z + fderiv ℝ ξ₀ z := by
      rw [hsplit, fderiv_fun_add (dp.fun_add dm) d₀, fderiv_fun_add dp dm]
    rw [hval, hder]
    simp only [add_apply]
    linarith [norm_add_add_sq_le_three_mul (fderiv ℝ ξp z stdComplexLineReal)
      (fderiv ℝ ξm z stdComplexLineReal) (fderiv ℝ ξ₀ z stdComplexLineReal),
      norm_add_add_sq_le_three_mul (fderiv ℝ ξp z stdComplexLineImag)
      (fderiv ℝ ξm z stdComplexLineImag) (fderiv ℝ ξ₀ z stdComplexLineImag),
      norm_add_add_sq_le_three_mul (ξp z) (ξm z) (ξ₀ z)]
  have hint {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η) (p q : ℝ) :
      IntegrableOn (fun z ↦ ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) (Icc p q ×ˢ Icc (0 : ℝ) 1) :=
    (Floer.continuous_sobolev (hη.of_le one_le_two)).integrableOn_Icc_prod_Icc
  -- The piece near `+∞`.
  have hPp : ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξp z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξp z stdComplexLineImag‖ ^ 2 + ‖ξp z‖ ^ 2) ≤ max Cp 0 * (L * (X + Y)) := by
    rw [setIntegral_sobolev_eq (a' := a') (b' := b') hvp
      ((min_le_left _ _).trans (le_max_left _ _)) (max_le_max le_rfl (by linarith))]
    refine (hp hξp (fun s t ↦ by simp only [ξp, hper]) (hRp.trans (le_max_right _ _))
      (max_le_max hab le_rfl) (fun t ↦ hvp _ t fun h ↦ lt_irrefl _ h.1)
      (fun t ↦ hvp _ t fun h ↦ lt_irrefl _ h.2)).trans ?_
    rw [← setIntegral_norm_floerLinearization_sub_smul_sq_eq (a' := a') (b' := b') ω J' Ks Kt u c
      hvp ((min_le_left _ _).trans (le_max_left _ _)) (max_le_max le_rfl (by linarith))]
    exact mul_le_mul (le_max_left _ _) (hcut hβpc hβp1 hβpM hβpT)
      (setIntegral_nonneg hrect fun _ _ ↦ sq_nonneg _) (le_max_right _ _)
  -- The piece near `-∞`.
  have hPm : ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξm z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξm z stdComplexLineImag‖ ^ 2 + ‖ξm z‖ ^ 2) ≤ max Cm 0 * (L * (X + Y)) := by
    rw [setIntegral_sobolev_eq (a' := a') (b' := b') hvm (min_le_min le_rfl (by linarith))
      ((min_le_left _ _).trans (le_max_left _ _))]
    refine (hm hξm (fun s t ↦ by simp only [ξm, hper]) (min_le_min hab le_rfl)
      ((min_le_right _ _).trans hRm) (fun t ↦ hvm _ t fun h ↦ lt_irrefl _ h.1)
      (fun t ↦ hvm _ t fun h ↦ lt_irrefl _ h.2)).trans ?_
    rw [← setIntegral_norm_floerLinearization_sub_smul_sq_eq (a' := a') (b' := b') ω J' Ks Kt u c
      hvm (min_le_min le_rfl (by linarith)) ((min_le_left _ _).trans (le_max_left _ _))]
    exact mul_le_mul (le_max_left _ _) (hcut hβmc hβm1 hβmM hβmT)
      (setIntegral_nonneg hrect fun _ _ ↦ sq_nonneg _) (le_max_right _ _)
  -- The piece on the compact cylinder `[-T, T] × [0, 1]`.
  have hP₀ : ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2 + ‖ξ₀ z‖ ^ 2) ≤
        C₀ * ((2 * L + 2 * B ^ 2 + 1) * (X + Y)) + (X + Y) := by
    have hξ₀1 : Continuous ξ₀ := hξ₀c.continuous
    have hdξ₀ := hξ₀c.continuous_fderiv two_ne_zero
    have hDξ₀ := ω.continuous_floerLinearization (J := J') hJ hKs hKt hu (hξ₀c.of_le one_le_two)
    rw [setIntegral_sobolev_eq (a' := a') (b' := b') hv₀ (min_le_right _ _) (le_max_right _ _),
      integral_add (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
        (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))]
    have hcore' := hcore hξ₀c (fun s _ ↦ by rw [← zero_add (1 : ℝ), hper₀])
      (fun t ↦ hv₀ _ t fun h ↦ lt_irrefl _ h.1) (fun t ↦ hv₀ _ t fun h ↦ lt_irrefl _ h.2)
    rw [integral_add (Continuous.integrableOn_Icc_prod_Icc
      (f := fun z ↦ ‖ω.floerLinearization J' Ks Kt u ξ₀ z‖ ^ 2) (by fun_prop))
      (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))] at hcore'
    have hP₀' : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1,
        ‖ω.floerLinearization J' Ks Kt u ξ₀ z - c z.1 • ξ₀ z‖ ^ 2 ≤ L * (X + Y) := by
      rw [← setIntegral_norm_floerLinearization_sub_smul_sq_eq (a' := a') (b' := b') ω J' Ks Kt u
        c hv₀ (min_le_right a _) (le_max_right b _)]
      exact hcut hβ₀c hβ₀1 hβ₀M hβ₀T'
    have hξ₀Y : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ₀ z‖ ^ 2 ≤ Y := by
      refine setIntegral_mono_on (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
        (Continuous.integrableOn_Icc_prod_Icc (by have := hξ.continuous; fun_prop))
        (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
      simp only [ξ₀, norm_smul, Real.norm_eq_abs]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) (hβ₀1 z.1)
    have hD₀ := setIntegral_norm_sq_le_two_mul_setIntegral_norm_sub_smul_sq_add hDξ₀ hξ₀1 hcc
      hcB (-T) T
    have h₁ : C₀ * ((∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1,
        ‖ω.floerLinearization J' Ks Kt u ξ₀ z‖ ^ 2) +
          ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ₀ z‖ ^ 2) ≤
        C₀ * ((2 * L + 2 * B ^ 2 + 1) * (X + Y)) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₀
      nlinarith [mul_nonneg (sq_nonneg B) hX, mul_le_mul_of_nonneg_left hξ₀Y (sq_nonneg B)]
    linarith
  -- Summing the three pieces.
  have hsum : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
        3 * ((∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξp z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξp z stdComplexLineImag‖ ^ 2 + ‖ξp z‖ ^ 2)) +
        (∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξm z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξm z stdComplexLineImag‖ ^ 2 + ‖ξm z‖ ^ 2)) +
        ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2 + ‖ξ₀ z‖ ^ 2)) := by
    have := hξp.continuous
    have := hξm.continuous
    have := hξ₀c.continuous
    have := hξp.continuous_fderiv two_ne_zero
    have := hξm.continuous_fderiv two_ne_zero
    have := hξ₀c.continuous_fderiv two_ne_zero
    rw [← setIntegral_sobolev_eq (a' := a') (b' := b') hξ₀ (min_le_left a _) (le_max_left b _)]
    calc _ ≤ ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1,
          3 * ((‖fderiv ℝ ξp z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξp z stdComplexLineImag‖ ^ 2 + ‖ξp z‖ ^ 2) +
          (‖fderiv ℝ ξm z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξm z stdComplexLineImag‖ ^ 2 +
            ‖ξm z‖ ^ 2) +
          (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2 +
            ‖ξ₀ z‖ ^ 2)) :=
        setIntegral_mono_on (hint hξ _ _) (Continuous.integrableOn_Icc_prod_Icc (by fun_prop)) hrect
          fun z _ ↦ hE z
      _ = _ := by
        rw [integral_const_mul,
          integral_add (Continuous.integrableOn_Icc_prod_Icc (by fun_prop)) (hint hξ₀c _ _),
          integral_add (hint hξp _ _) (hint hξm _ _)]
  calc _ ≤ _ := hsum
    _ ≤ 3 * (max Cp 0 * (L * (X + Y)) + max Cm 0 * (L * (X + Y)) +
        (C₀ * ((2 * L + 2 * B ^ 2 + 1) * (X + Y)) + (X + Y))) := by gcongr
    _ = _ := by ring

/-- **Patching end estimates into the semi-Fredholm estimate.** Let `J(z)` be compatible along
`u`, with `J` `C¹` and `K_s`, `K_t` `C²` at the points `(z, u z)`, and `u` `C¹`. Suppose that the
linearized Floer operator `D_u` controls the `W^{1,2}` norm on the two ends: there are constants
`Cp`, `Cm` such that every `C²` map `ξ` of period one in `t`, vanishing on two slices `s = a ≤ b`
with `Rp ≤ a`, respectively with `b ≤ Rm`, satisfies
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ Cp ∫ ‖D_u ξ‖²`, respectively `≤ Cm ∫ ‖D_u ξ‖²`, over
`[a, b] × [0, 1]`. Then there are `C ≥ 0` and
`T` such that every `C²` map `ξ` of period one in `t` vanishing for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`. This is the case `c = 0` of
`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_ends`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_ends
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {Cp Cm Rp Rm : ℝ}
    (hp : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, Rp ≤ a → a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cp * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2)
    (hm : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → b ≤ Rm → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cm * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  simpa only [Pi.zero_apply, zero_smul, sub_zero] using
    ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_ends hJ hKs
      hKt hu hc (c := 0) continuous_const (B := 0) (fun _ ↦ by simp)
      (fun ξ hξ hper a b ha hab hsa hsb ↦ by
        simpa only [Pi.zero_apply, zero_smul, sub_zero] using hp hξ hper ha hab hsa hsb)
      (fun ξ hξ hper a b hab hb hsa hsb ↦ by
        simpa only [Pi.zero_apply, zero_smul, sub_zero] using hm hξ hper hab hb hsa hsb)

/-- **The weighted semi-Fredholm estimate for Floer data that are cylindrical near the ends.**
Let `J(z)`, `K_s`, `K_t` be Floer data on the cylinder that agree with the cylindrical data
`(J₋_t, 0, H₋_t)` for `s ≤ -R` and with `(J₊_t, 0, H₊_t)` for `s ≥ R`, as for a continuation
cylinder from `H₋` to `H₊`. Suppose that `J` is `C¹` and `K_s`, `K_t` are `C²` at the points
`(z, u z)`, where `u` is a `C¹` map along which `J` is `ω`-compatible. Let `c : ℝ → ℝ` be
continuous, equal to `δm` for `s ≤ -R` and to `δp` for `s ≥ R`. Let the end Hamiltonians `H±`
be jointly `C²`, the end structures `J±_t(y)` be `C¹` families compatible along continuous loops
`x±`, such that the shifted fields `dX_{H±_t}(x±(t)) - δ± J±_t(x±(t))` have nondegenerate return
maps, and let the loops of `u` converge uniformly to `xm` at `-∞` and to `xp` at `+∞` while the
slice defects `∂t u - X_{H±_t}(u)` tend uniformly to zero there. Then there are `C ≥ 0` and `T`
such that every `C²` map `ξ` of period one in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ - c(s) ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the data `(J, K_s, K_t)`. Beyond
`±R` the operator `D_u - c(s)` is the operator `D_u - δ±` of the end data, so its end estimates are
those of `exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sub_smul_sq`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_cylindrical
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ}
    (hJm_eq : ∀ z : ℝ × ℝ, z.1 ≤ -R → J z = Jm z.2) (hJp_eq : ∀ z : ℝ × ℝ, R ≤ z.1 → J z = Jp z.2)
    (hKs_eq : ∀ z : ℝ × ℝ, z.1 ∉ Ioo (-R) R → Ks z = 0)
    (hKtm_eq : ∀ z : ℝ × ℝ, z.1 ≤ -R → Kt z = Hm z.2)
    (hKtp_eq : ∀ z : ℝ × ℝ, R ≤ z.1 → Kt z = Hp z.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hJu : ∀ z, ω.Compatible (J z (u z))) {c : ℝ → ℝ} (hc : Continuous c) {δm δp : ℝ}
    (hcm : ∀ s ≤ -R, c s = δm) (hcp : ∀ s, R ≤ s → c s = δp)
    (hHm : ContDiff ℝ 2 (Function.uncurry Hm)) {xm : ℝ → V} (hxm : Continuous xm)
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (Jm t (xm t)))
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hm t)) (xm t) -
        δm • (Jm t (xm t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hHp : ContDiff ℝ 2 (Function.uncurry Hp)) {xp : ℝ → V} (hxp : Continuous xp)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxp : ∀ t, ω.Compatible (Jp t (xp t)))
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hp t)) (xp t) -
        δp • (Jp t (xp t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  obtain ⟨B, hcB⟩ := exists_forall_norm_le_of_eventually_eq hc
    (eventually_atBot.2 ⟨-R, hcm⟩) (eventually_atTop.2 ⟨R, hcp⟩)
  have hu' (l : Filter ℝ) : ∀ᶠ s in l, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 u (s, t) :=
    Eventually.of_forall fun _ _ _ ↦ hu.contDiffAt
  obtain ⟨Cp, -, Up, hUp, hp⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sub_smul_sq hHp hxp
      hJp hJxp hdetp (hu' atTop) huxp hδp
  obtain ⟨Cm, -, Um, hUm, hm⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sub_smul_sq hHm hxm
      hJm hJxm hdetm (hu' atBot) huxm hδm
  obtain ⟨Rp, hRp⟩ := mem_atTop_sets.1 hUp
  obtain ⟨Rm, hRm⟩ := mem_atBot_sets.1 hUm
  -- Beyond `R` the operator `D_u - c(s)` of `(J, K_s, K_t)` is the operator `D_u - δ±` of the
  -- cylindrical end data.
  have hD {J' : ℝ → V → AlmostComplexStructure V} {H : ℝ → V → ℝ} {δ : ℝ} {ξ : ℝ × ℝ → V}
      {S : Set ℝ} (hS : ∀ s ∈ S, s ∉ Ioo (-R) R) (hJS : ∀ z : ℝ × ℝ, z.1 ∈ S → J z = J' z.2)
      (hKtS : ∀ z : ℝ × ℝ, z.1 ∈ S → Kt z = H z.2) (hcS : ∀ s ∈ S, c s = δ) :
      EqOn (fun z ↦ ‖ω.floerLinearization (fun w y ↦ (J' w.2 y).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z - δ • ξ z‖ ^ 2)
        (fun z ↦ ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z - c z.1 • ξ z‖ ^ 2) (S ×ˢ Icc (0 : ℝ) 1) := fun z hz ↦ by
    beta_reduce
    rw [hcS z.1 hz.1, ω.floerLinearization_congr_data (Ks' := Ks) (Kt' := Kt)
      (J' := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u ξ ?_
      (hKs_eq z (hS z.1 hz.1)).symm (hKtS z hz.1).symm]
    simp only [hJS z hz.1]
  refine ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_ends hJ
    hKs hKt hu hJu hc hcB (Cp := Cp) (Cm := Cm) (Rp := max Rp R) (Rm := min Rm (-R))
    (fun ξ hξ hper a b ha hab hsa hsb ↦ ?_) (fun ξ hξ hper a b hab hb hsa hsb ↦ ?_)
  · have hR : ∀ s ∈ Icc a b, R ≤ s := fun s hs ↦ (le_max_right Rp R).trans (ha.trans hs.1)
    refine (hp hξ hper hab (fun s hs ↦ hRp s ((le_max_left Rp R).trans (ha.trans hs.1))) hsa
      hsb).trans_eq ?_
    rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      (hD (fun s hs h ↦ (hR s hs).not_gt h.2) (fun z hz ↦ hJp_eq z (hR _ hz))
        (fun z hz ↦ hKtp_eq z (hR _ hz)) (fun s hs ↦ hcp s (hR s hs)))]
  · have hR : ∀ s ∈ Icc a b, s ≤ -R := fun s hs ↦ hs.2.trans (hb.trans (min_le_right Rm _))
    refine (hm hξ hper hab (fun s hs ↦ hRm s (hs.2.trans (hb.trans (min_le_left Rm _)))) hsa
      hsb).trans_eq ?_
    rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      (hD (fun s hs h ↦ (hR s hs).not_gt h.1) (fun z hz ↦ hJm_eq z (hR _ hz))
        (fun z hz ↦ hKtm_eq z (hR _ hz)) (fun s hs ↦ hcm s (hR s hs)))]

/-- **The semi-Fredholm estimate for Floer data that are cylindrical near the ends.** Let
`J(z)`, `K_s`, `K_t` be Floer data on the cylinder that agree with the cylindrical data
`(J₋_t, 0, H₋_t)` for `s ≤ -R` and with `(J₊_t, 0, H₊_t)` for `s ≥ R`, as for a continuation
cylinder from `H₋` to `H₊`. Suppose that `J` is `C¹` and `K_s`, `K_t` are `C²` at the points
`(z, u z)`, where `u` is a `C¹` map along which `J` is `ω`-compatible. Let the end Hamiltonians
`H±` be jointly `C²` with globally Lipschitz suspended vector fields, the end structures `J±_t(y)`
be `C¹` families compatible along orbits `x±` of `H±` that start at nondegenerate fixed points of
the time-one maps, and let the loops of `u` converge uniformly to `xm` at `-∞` and to `xp` at
`+∞` while the slice defects `∂t u - X_{H±_t}(u)` tend uniformly to zero there. Then there are
`C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` that vanishes for `s ∉ (a, b)`
satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the data `(J, K_s, K_t)`. This
is the case `c = 0` of
`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_cylindrical`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ}
    (hJm_eq : ∀ z : ℝ × ℝ, z.1 ≤ -R → J z = Jm z.2) (hJp_eq : ∀ z : ℝ × ℝ, R ≤ z.1 → J z = Jp z.2)
    (hKs_eq : ∀ z : ℝ × ℝ, z.1 ∉ Ioo (-R) R → Ks z = 0)
    (hKtm_eq : ∀ z : ℝ × ℝ, z.1 ≤ -R → Kt z = Hm z.2)
    (hKtp_eq : ∀ z : ℝ × ℝ, R ≤ z.1 → Kt z = Hp z.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hJu : ∀ z, ω.Compatible (J z (u z))) {Km : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 2 (Function.uncurry Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (Jm t (xm t)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1)) {Kp : ℝ≥0}
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 2 (Function.uncurry Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxp : ∀ t, ω.Compatible (Jp t (xp t)))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  have hcont {H : ℝ → V → ℝ} {x : ℝ → V}
      (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) : Continuous x :=
    continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  simpa only [Pi.zero_apply, zero_smul, sub_zero] using
    ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_cylindrical
      hJm_eq hJp_eq hKs_eq hKtm_eq hKtp_eq hJ hKs hKt hu hJu (c := 0) continuous_const
      (δm := 0) (δp := 0) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hHm (hcont hxm) hJm hJxm
      (ω.det_one_sub_dysonSeriesLeft_sub_zero_smul_ne_zero_of_isNondegenerateFixedPt
        hXm hHm hxm hndm _)
      huxm hδm hHp (hcont hxp) hJp hJxp
      (ω.det_one_sub_dysonSeriesLeft_sub_zero_smul_ne_zero_of_isNondegenerateFixedPt
        hXp hHp hxp hndp _)
      huxp hδp

/-- **The semi-Fredholm estimate along a Floer trajectory.** Let `H` be a jointly `C²`
Hamiltonian whose suspended vector field is globally Lipschitz, and let `J_t(y)` be a `C¹` family
of almost complex structures. Let `u : ℝ × ℝ → V` be a `C¹` map along which `J_t` is
`ω`-compatible, whose loops converge uniformly to orbits `xm` at `-∞` and `xp` at `+∞` starting at
nondegenerate fixed points of the time-one map, as for nondegenerate one-periodic orbits of a
one-periodic Hamiltonian, with `J_t` compatible along them, while its slice defect
`∂t u - X_{H_t}(u)` tends uniformly to zero at both ends, as for a Floer trajectory from `xm` to
`xp`. Then there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` that
vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the datum `K = H_t dt`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u ξ z‖ ^ 2) + ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical
    (J := fun w y ↦ J w.2 y) (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) (R := 0)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
    (fun _ ↦ contDiffAt_const) (fun _ ↦ (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
    hu hJu hX hH hxm hndm hJ hJxm huxm hδm hX hH hxp hndp hJ hJxp huxp hδp

/-- **The weighted semi-Fredholm estimate along a Floer trajectory.** Let `H` be a jointly `C²`
Hamiltonian, `J_t(y)` a `C¹` family of almost complex structures and `u : ℝ × ℝ → V` a `C¹` map
along which `J_t` is `ω`-compatible, whose loops converge uniformly to continuous loops `xm` at
`-∞` and `xp` at `+∞`, with `J_t` compatible along them, while its slice defect
`∂t u - X_{H_t}(u)` tends uniformly to zero at both ends, as for a Floer trajectory from `xm` to
`xp`. Let `c : ℝ → ℝ` be continuous, equal to `δm` for `s ≤ -R` and to `δp` for `s ≥ R`, where the
end weights are such that `S±_t - δ± J_t(x±(t))` have nondegenerate return maps, for
`S±_t = dX_{H_t}(x±(t))`; when `H`, `J` and `x±` are one-periodic in `t`, this says that `δ±` is
not an eigenvalue of the asymptotic operator at `x±`. Then
there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` that vanishes for
`s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ - c(s) ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the datum `K = H_t dt`. For
`c = κ'` the operator `D_u - κ'` is `D_u` conjugated by the weight `e^{κ(s)}`
(`floerLinearization_exp_neg_smul`), so this is the semi-Fredholm estimate of `D_u` between the
Sobolev spaces with weight `e^{κ(s)}`, whose slopes at the ends are `δ±`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H))
    {xm xp : ℝ → V} (hxm : Continuous xm) (hxp : Continuous xp)
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1))
    {c : ℝ → ℝ} (hc : Continuous c) {R δm δp : ℝ} (hcm : ∀ s ≤ -R, c s = δm)
    (hcp : ∀ s, R ≤ s → c s = δp)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xm t) -
        δm • (J t (xm t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xp t) -
        δp • (J t (xp t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u ξ z - c z.1 • ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_cylindrical
    (J := fun w y ↦ J w.2 y) (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) (R := R)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
    (fun _ ↦ contDiffAt_const) (fun _ ↦ (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
    hu hJu hc hcm hcp hH hxm hJ hJxm hdetm huxm hδm hH hxp hJ hJxp hdetp huxp hδp

end TauCeti.SymplecticForm
