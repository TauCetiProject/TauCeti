/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cutoff
public import TauCeti.Geometry.Symplectic.Floer.Neck
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The cutoff and neck-stretching family of Hamiltonian perturbations

The comparison between the pair-of-pants product and the quantum product deforms the
unperturbed (pseudoholomorphic) problem on a sphere into broken Floer configurations through a
one-parameter family of perturbation data `K_R`, `R ≥ 0`. For `0 ≤ R ≤ 1` the perturbation is
switched on, `K_R = ρ(R) K`, by a cutoff `ρ` with `ρ(R) = R` near `0` and `ρ = 1` near `1`. For
`R ≥ 1` a cylindrical neck of length `L(R)` is inserted, where `L` vanishes near `1` and
`L(R) = R - 1` for large `R`. Both phases are one formula,

`K_R = ρ(R) K ∘ (σ_{L(R)} × id)`,

with `σ_L = TauCeti.Floer.neckCollapse c L` the neck-collapsing map at the line `s = c`
(`TauCeti.Floer.cutoffNeckFamily`). On the collar where `ρ = 1` and `L = 0` the family is
constant, equal to `K`, so the two phases fit together smoothly.

The endpoint `R = 0` is the zero perturbation, and as `R → ∞` the neck becomes arbitrarily long.
Compactness for this family needs an energy bound that is uniform in `R`. If `K` is cylindrical
near the line `s = c` (`K_s = 0` and `K_t` independent of `s` there), then for every `R` with
`ρ(R) ∈ [0, 1]` and `L(R) ≥ 0` the integrated curvature of `K_R` over the stretched rectangle is
at most `∫ (|R_K| + |{K_s, K_t}| / 4)` over the original rectangle. This combines the bound for
scaled perturbations (`TauCeti.SmoothTwoForm.abs_hamiltonianCurvature_const_mul_le`) with the
vanishing of curvature along a cylindrical neck
(`TauCeti.SmoothTwoForm.integral_abs_hamiltonianCurvature_neckStretch_le`). By the energy
identity the Floer energy then differs from its topological part by at most the same constant.

The file also fixes one choice of `ρ` and `L`: `TauCeti.Floer.comparisonCutoff` and
`TauCeti.Floer.comparisonNeckLength`, built from `Real.smoothTransition`.

The domain here is a coordinate rectangle with a single neck: this is the model near one neck.
The curvature and energy bounds hold for data on the product of the domain with a manifold
carrying a two-form, such as a closed symplectic manifold, with the vector-space statements as the
case of a constant form. The matching almost complex structures are in
`TauCeti.Geometry.Symplectic.Floer.ComparisonFamily.AlmostComplex`. The family on a sphere with
three necks is not treated here.

## Main definitions

* `TauCeti.Floer.cutoffNeckFamily ρ L c K R`: the datum `ρ(R) K ∘ (σ_{L(R)} × id)`.
* `TauCeti.Floer.comparisonCutoff`: the cutoff `ρ(R) = R + (1 - R) β(3R - 1)`.
* `TauCeti.Floer.comparisonNeckLength`: the neck length `L(R) = (R - 1) β(2R - 3)`.

## Main results

* `TauCeti.Floer.contMDiff_cutoffNeckFamily`: the family is smooth jointly in `R`, the domain
  point and the point of a manifold target; `TauCeti.Floer.contDiff_cutoffNeckFamily` is the
  vector-space case.
* `TauCeti.Floer.cutoffNeckFamily_comparison_zero`,
  `TauCeti.Floer.cutoffNeckFamily_comparison_of_mem_Icc`,
  `TauCeti.Floer.cutoffNeckFamily_comparison_of_two_le`: for the chosen `ρ` and `L`, the family
  is the zero perturbation at `R = 0`, equals `K` on the collar `2/3 ≤ R ≤ 3/2`, and has a neck of
  length `R - 1` for `R ≥ 2`.
* `TauCeti.SmoothTwoForm.hamiltonianCurvature_cutoffNeckFamily`: the curvature of `K_R`.
* `TauCeti.SmoothTwoForm.integral_abs_hamiltonianCurvature_cutoffNeckFamily_le`: the integrated
  curvature bound, uniform over the family.
* `TauCeti.SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_cutoffNeckFamily_sub_le`:
  the resulting energy estimate, uniform over the family, for a nondegenerate two-form.
* The declarations of the same names in the `TauCeti.SymplecticForm` namespace are the
  vector-space cases.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti

namespace Floer

section Choice

open Real

/-- The cutoff `ρ(R) = R + (1 - R) β(3R - 1)`, with `β = Real.smoothTransition`, which switches
on a perturbation: `ρ(R) = R` for `R ≤ 1/3` and `ρ(R) = 1` for `R ≥ 2/3`. -/
noncomputable def comparisonCutoff (R : ℝ) : ℝ :=
  R + (1 - R) * smoothTransition (3 * R - 1)

theorem comparisonCutoff_def (R : ℝ) :
    comparisonCutoff R = R + (1 - R) * smoothTransition (3 * R - 1) :=
  (rfl)

theorem comparisonCutoff_of_le {R : ℝ} (hR : R ≤ 1 / 3) : comparisonCutoff R = R := by
  rw [comparisonCutoff_def, smoothTransition.zero_of_nonpos (by linarith), mul_zero, add_zero]

theorem comparisonCutoff_of_ge {R : ℝ} (hR : 2 / 3 ≤ R) : comparisonCutoff R = 1 := by
  rw [comparisonCutoff_def, smoothTransition.one_of_one_le (by linarith)]
  ring

@[simp]
theorem comparisonCutoff_zero : comparisonCutoff 0 = 0 :=
  comparisonCutoff_of_le (by norm_num)

/-- The cutoff takes values in `[0, 1]` for `R ≥ 0`. -/
theorem comparisonCutoff_mem_Icc {R : ℝ} (hR : 0 ≤ R) : comparisonCutoff R ∈ Icc (0 : ℝ) 1 := by
  rcases le_total (2 / 3) R with h | h
  · rw [comparisonCutoff_of_ge h]
    exact ⟨zero_le_one, le_rfl⟩
  · have h₀ := smoothTransition.nonneg (3 * R - 1)
    have h₁ := smoothTransition.le_one (3 * R - 1)
    rw [comparisonCutoff_def]
    constructor <;> nlinarith

/-- The cutoff has absolute value at most `1` for `R ≥ -1`: it is `R` itself on `[-1, 0]`. -/
theorem abs_comparisonCutoff_le_one {R : ℝ} (hR : -1 ≤ R) : |comparisonCutoff R| ≤ 1 := by
  rcases le_total 0 R with h | h
  · obtain ⟨h₀, h₁⟩ := comparisonCutoff_mem_Icc h
    exact abs_le.2 ⟨by linarith, h₁⟩
  · rw [comparisonCutoff_of_le (by linarith)]
    exact abs_le.2 ⟨hR, by linarith⟩

theorem contDiff_comparisonCutoff {n : ℕ∞} : ContDiff ℝ n comparisonCutoff :=
  contDiff_id.add ((contDiff_const.sub contDiff_id).mul
    (smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))

/-- The neck length `L(R) = (R - 1) β(2R - 3)`, with `β = Real.smoothTransition`: it vanishes for
`R ≤ 3/2` and equals `R - 1` for `R ≥ 2`. -/
noncomputable def comparisonNeckLength (R : ℝ) : ℝ :=
  (R - 1) * smoothTransition (2 * R - 3)

theorem comparisonNeckLength_def (R : ℝ) :
    comparisonNeckLength R = (R - 1) * smoothTransition (2 * R - 3) :=
  (rfl)

theorem comparisonNeckLength_of_le {R : ℝ} (hR : R ≤ 3 / 2) : comparisonNeckLength R = 0 := by
  rw [comparisonNeckLength_def, smoothTransition.zero_of_nonpos (by linarith), mul_zero]

theorem comparisonNeckLength_of_ge {R : ℝ} (hR : 2 ≤ R) : comparisonNeckLength R = R - 1 := by
  rw [comparisonNeckLength_def, smoothTransition.one_of_one_le (by linarith), mul_one]

theorem comparisonNeckLength_nonneg (R : ℝ) : 0 ≤ comparisonNeckLength R := by
  rcases le_total R (3 / 2) with h | h
  · rw [comparisonNeckLength_of_le h]
  · exact mul_nonneg (by linarith) (smoothTransition.nonneg _)

theorem contDiff_comparisonNeckLength {n : ℕ∞} : ContDiff ℝ n comparisonNeckLength :=
  (contDiff_id.sub contDiff_const).mul
    (smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

end Choice

section Family

variable {X : Type*} {ρ L : ℝ → ℝ} {c R : ℝ}

/-- The one-parameter family `K_R = ρ(R) K ∘ (σ_{L(R)} × id)`: the datum `K` scaled by `ρ(R)`,
with a neck of length `L(R)` inserted at the line `s = c` (`TauCeti.Floer.neckStretch`). -/
def cutoffNeckFamily (ρ L : ℝ → ℝ) (c : ℝ) (K : ℝ × ℝ → X → ℝ) (R : ℝ) (z : ℝ × ℝ) (x : X) :
    ℝ :=
  ρ R * neckStretch c (L R) K z x

@[simp]
theorem cutoffNeckFamily_apply (K : ℝ × ℝ → X → ℝ) (z : ℝ × ℝ) (x : X) :
    cutoffNeckFamily ρ L c K R z x = ρ R * K (neckCollapse c (L R) z.1, z.2) x := by
  rw [cutoffNeckFamily, neckStretch_apply]

/-- Each member of the family is the scaled datum `ρ(R) K` with a neck inserted. -/
theorem cutoffNeckFamily_eq_neckStretch (K : ℝ × ℝ → X → ℝ) :
    cutoffNeckFamily ρ L c K R = neckStretch c (L R) fun w y ↦ ρ R * K w y := by
  funext z x
  rw [cutoffNeckFamily_apply, neckStretch_apply]

/-- Where the cutoff vanishes, the family is the zero perturbation. -/
theorem cutoffNeckFamily_of_cutoff_eq_zero (K : ℝ × ℝ → X → ℝ) (h : ρ R = 0) :
    cutoffNeckFamily ρ L c K R = 0 := by
  funext z x
  simp [h]

/-- Where the neck length vanishes, the family is the scaled datum `ρ(R) K`. -/
theorem cutoffNeckFamily_of_neckLength_eq_zero (K : ℝ × ℝ → X → ℝ) (h : L R = 0) :
    cutoffNeckFamily ρ L c K R = fun w y ↦ ρ R * K w y := by
  rw [cutoffNeckFamily_eq_neckStretch, h, neckStretch_zero]

/-- Where the cutoff is `1`, the family is the datum `K` with a neck of length `L(R)`. -/
theorem cutoffNeckFamily_of_cutoff_eq_one (K : ℝ × ℝ → X → ℝ) (h : ρ R = 1) :
    cutoffNeckFamily ρ L c K R = neckStretch c (L R) K := by
  funext z x
  simp [h]

/-- A datum that is independent of `s` near the line `s = c` stays so after scaling. -/
private theorem eventually_const_mul_eq {K : ℝ × ℝ → X → ℝ} (r : ℝ)
    (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t)) :
    ∀ᶠ s in 𝓝 c, ∀ t, (fun y ↦ r * K (s, t) y) = fun y ↦ r * K (c, t) y := by
  filter_upwards [hK] with s hs t
  rw [hs t]

/-- A datum vanishing near the line `s = c` stays so after scaling. -/
private theorem eventually_const_mul_eq_zero {K : ℝ × ℝ → X → ℝ} (r : ℝ)
    (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = 0) :
    ∀ᶠ s in 𝓝 c, ∀ t, (fun y ↦ r * K (s, t) y) = 0 := by
  filter_upwards [hK] with s hs t
  funext y
  simp [hs t]

/-- **Smoothness of the family, for a manifold target.** For smooth `ρ` and `L ≥ 0`, and a
smooth datum `K` on the product of the domain with a manifold `M` which is independent of `s` near
the line `s = c`, the family is smooth jointly in the parameter `R`, the domain point and the
point of `M`. -/
theorem contMDiff_cutoffNeckFamily {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (hL : ContDiff ℝ n L) (hL₀ : ∀ R, 0 ≤ L R)
    {K : ℝ × ℝ → M → ℝ} (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t))
    (hKd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n (uncurry K)) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) n
      fun q : ℝ × (ℝ × ℝ) × M ↦ cutoffNeckFamily ρ L c K q.1 q.2.1 q.2.2 :=
  (hρ.contMDiff.comp contMDiff_fst).smul (contMDiff_neckStretch_family hL hL₀ hK hKd)

/-- **Smoothness of the family.** For smooth `ρ` and `L ≥ 0`, and a smooth datum `K` which is
independent of `s` near the line `s = c`, the family is smooth jointly in the parameter `R`, the
domain point and the target point. -/
theorem contDiff_cutoffNeckFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (hL : ContDiff ℝ n L) (hL₀ : ∀ R, 0 ≤ L R)
    {K : ℝ × ℝ → E → ℝ} (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t))
    (hKd : ContDiff ℝ n (uncurry K)) :
    ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) × E ↦ cutoffNeckFamily ρ L c K q.1 q.2.1 q.2.2 :=
  (hρ.comp contDiff_fst).mul (contDiff_neckStretch_family hL hL₀ hK hKd)

/-- For the chosen cutoff and neck length, the family starts at the zero perturbation. -/
@[simp]
theorem cutoffNeckFamily_comparison_zero (K : ℝ × ℝ → X → ℝ) :
    cutoffNeckFamily comparisonCutoff comparisonNeckLength c K 0 = 0 :=
  cutoffNeckFamily_of_cutoff_eq_zero K comparisonCutoff_zero

/-- For the chosen cutoff and neck length, the family is constant, equal to `K`, on the collar
`2/3 ≤ R ≤ 3/2` joining the cutoff phase to the neck-stretching phase. -/
theorem cutoffNeckFamily_comparison_of_mem_Icc (K : ℝ × ℝ → X → ℝ)
    (hR : R ∈ Icc (2 / 3 : ℝ) (3 / 2)) :
    cutoffNeckFamily comparisonCutoff comparisonNeckLength c K R = K := by
  rw [cutoffNeckFamily_of_cutoff_eq_one K (comparisonCutoff_of_ge hR.1),
    comparisonNeckLength_of_le hR.2, neckStretch_zero]

/-- For the chosen cutoff and neck length, for `R ≥ 2` the family is `K` with a neck of length
`R - 1`. -/
theorem cutoffNeckFamily_comparison_of_two_le (K : ℝ × ℝ → X → ℝ) (hR : 2 ≤ R) :
    cutoffNeckFamily comparisonCutoff comparisonNeckLength c K R = neckStretch c (R - 1) K := by
  rw [cutoffNeckFamily_of_cutoff_eq_one K (comparisonCutoff_of_ge (by linarith)),
    comparisonNeckLength_of_ge hR]

end Family

end Floer

namespace SmoothTwoForm

open Floer

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {ρ L : ℝ → ℝ} {c R : ℝ}

/-- **Curvature of the family, for a manifold target.** If the datum on the product of the domain
with a manifold is independent of `s` near the line `s = c` and `L(R) ≥ 0`, the curvature of `K_R`
at `z` is the curvature of the scaled datum `ρ(R) K` at `(σ s, t)`, namely
`ρ(R) R_K + (ρ(R) - ρ(R)²) {K_s, K_t}` there. -/
theorem hamiltonianCurvature_cutoffNeckFamily (ω : SmoothTwoForm I M) (hL : 0 ≤ L R)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = Ks (c, t))
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature (cutoffNeckFamily ρ L c Ks R) (cutoffNeckFamily ρ L c Kt R) z x =
      ρ R * ω.hamiltonianCurvature Ks Kt (neckCollapse c (L R) z.1, z.2) x +
        (ρ R - ρ R ^ 2) * ω.poissonBracket (Ks (neckCollapse c (L R) z.1, z.2))
          (Kt (neckCollapse c (L R) z.1, z.2)) x := by
  rw [cutoffNeckFamily_eq_neckStretch, cutoffNeckFamily_eq_neckStretch,
    ω.hamiltonianCurvature_neckStretch hL (eventually_const_mul_eq _ hKs)
      (eventually_const_mul_eq _ hKt), hamiltonianCurvature_const_mul]

/-- **Uniform curvature bound for the family, for a manifold target.** Let `K` be a datum on the
product of the domain with a manifold, cylindrical near the line `s = c`, that is `K_s = 0` and
`K_t` independent of `s` there, and let `B` bound `|R_K| + |{K_s, K_t}| / 4` pointwise over the
rectangle `[a₁, b₁] × [a₂, b₂]` containing that line. Then for every `R` with `ρ(R) ∈ [0, 1]` and
`L(R) ≥ 0`, and every map `u`, the integrated curvature of `K_R` along `u` over the stretched
rectangle `[a₁, b₁ + L(R)] × [a₂, b₂]` is at most `∫ B` over the original rectangle. -/
theorem integral_abs_hamiltonianCurvature_cutoffNeckFamily_le (ω : SmoothTwoForm I M)
    (hρ : ρ R ∈ Icc (0 : ℝ) 1) (hL : 0 ≤ L R) (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0)
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (u : ℝ × ℝ → M) {B : ℝ × ℝ → ℝ}
    {a b : ℝ × ℝ} (hac : a.1 ≤ c) (hcb : c ≤ b.1)
    (hB : ∀ z ∈ Icc a b, ∀ x,
      |ω.hamiltonianCurvature Ks Kt z x| + |ω.poissonBracket (Ks z) (Kt z) x| / 4 ≤ B z)
    (hBi : IntegrableOn B (Icc a b)) :
    ∫ z in Icc a (b.1 + L R, b.2),
        |ω.hamiltonianCurvature (cutoffNeckFamily ρ L c Ks R) (cutoffNeckFamily ρ L c Kt R) z
          (u z)| ≤
      ∫ z in Icc a b, B z := by
  rw [cutoffNeckFamily_eq_neckStretch, cutoffNeckFamily_eq_neckStretch]
  exact ω.integral_abs_hamiltonianCurvature_neckStretch_le hL (eventually_const_mul_eq_zero _ hKs)
    (eventually_const_mul_eq _ hKt) u hac hcb
    (fun z hz x ↦ (ω.abs_hamiltonianCurvature_const_mul_le hρ z x).trans (hB z hz x)) hBi

/-- **Uniform energy estimate for the family, for a manifold target.** Let `ω` be a nondegenerate
two-form on a finite-dimensional manifold. Under the hypotheses of
`TauCeti.SmoothTwoForm.integral_abs_hamiltonianCurvature_cutoffNeckFamily_le`, for `C¹` data `K`
and a map `u` that is `C¹` near the stretched rectangle, with integrable energy density and
curvature for `K_R` there, the Floer energy of `u` for `K_R` differs from its symplectic area plus
the boundary integral of the pulled-back one-form `K_R(u)` by at most `∫ B` over the original
rectangle, for every `R` with `ρ(R) ∈ [0, 1]` and `L(R) ≥ 0`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_cutoffNeckFamily_sub_le
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) (hρ : ρ R ∈ Icc (0 : ℝ) 1) (hL : 0 ≤ L R)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0) (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t))
    (hKsd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks))
    (hKtd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt)) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) {B : ℝ × ℝ → ℝ}
    {a b : ℝ × ℝ} (hac : a.1 ≤ c) (hcb : c ≤ b.1) (hab : a.2 ≤ b.2)
    (habU : Icc a (b.1 + L R, b.2) ⊆ U)
    (hE : IntegrableOn
      (ω.floerEnergyDensity (cutoffNeckFamily ρ L c Ks R) (cutoffNeckFamily ρ L c Kt R) u)
      (Icc a (b.1 + L R, b.2)))
    (hR : IntegrableOn (fun z ↦
      ω.hamiltonianCurvature (cutoffNeckFamily ρ L c Ks R) (cutoffNeckFamily ρ L c Kt R) z (u z))
      (Icc a (b.1 + L R, b.2)))
    (hB : ∀ z ∈ Icc a b, ∀ x,
      |ω.hamiltonianCurvature Ks Kt z x| + |ω.poissonBracket (Ks z) (Kt z) x| / 4 ≤ B z)
    (hBi : IntegrableOn B (Icc a b)) :
    |(∫ z in Icc a (b.1 + L R, b.2),
        ω.floerEnergyDensity (cutoffNeckFamily ρ L c Ks R) (cutoffNeckFamily ρ L c Kt R) u z) -
      ((∫ z in Icc a (b.1 + L R, b.2), (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∫ s in a.1..b.1 + L R, cutoffNeckFamily ρ L c Ks R (s, a.2) (u (s, a.2))) +
          (∫ t in a.2..b.2, cutoffNeckFamily ρ L c Kt R (b.1 + L R, t) (u (b.1 + L R, t))) -
          (∫ s in a.1..b.1 + L R, cutoffNeckFamily ρ L c Ks R (s, b.2) (u (s, b.2))) -
          ∫ t in a.2..b.2, cutoffNeckFamily ρ L c Kt R (a.1, t) (u (a.1, t))))| ≤
      ∫ z in Icc a b, B z := by
  have hscale {K : ℝ × ℝ → M → ℝ} (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K)) :
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry fun w y ↦ ρ R * K w y) :=
    (contMDiff_const (c := ρ R) (I := 𝓘(ℝ, ℝ × ℝ).prod I) (I' := 𝓘(ℝ))).smul hK
  rw [cutoffNeckFamily_eq_neckStretch, cutoffNeckFamily_eq_neckStretch] at hE hR ⊢
  exact hω.abs_integral_floerEnergyDensity_neckStretch_sub_le hL
    (eventually_const_mul_eq_zero _ hKs) (eventually_const_mul_eq _ hKt) (hscale hKsd)
    (hscale hKtd) hU hu hac hcb hab habU hE hR
    (fun z hz x ↦ (ω.abs_hamiltonianCurvature_const_mul_le hρ z x).trans (hB z hz x)) hBi

end SmoothTwoForm

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {ρ L : ℝ → ℝ} {c R : ℝ}

/-- **Curvature of the family.** If the datum is independent of `s` near the line `s = c` and
`L(R) ≥ 0`, the curvature of `K_R` at `z` is the curvature of the scaled datum `ρ(R) K` at
`(σ s, t)`, namely `ρ(R) R_K + (ρ(R) - ρ(R)²) {K_s, K_t}` there. -/
theorem hamiltonianCurvature_cutoffNeckFamily (ω : SymplecticForm V) (hL : 0 ≤ L R)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = Ks (c, t))
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature (cutoffNeckFamily ρ L c Ks R) (cutoffNeckFamily ρ L c Kt R) z x =
      ρ R * ω.hamiltonianCurvature Ks Kt (neckCollapse c (L R) z.1, z.2) x +
        (ρ R - ρ R ^ 2) * ω.poissonBracket (Ks (neckCollapse c (L R) z.1, z.2))
          (Kt (neckCollapse c (L R) z.1, z.2)) x := by
  simpa [poissonBracket_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_cutoffNeckFamily (ρ := ρ) hL hKs hKt z x

/-- **Uniform curvature bound for the family.** Let `K` be cylindrical near the line `s = c`,
that is `K_s = 0` and `K_t` independent of `s` there, and let `M` bound `|R_K| + |{K_s, K_t}| / 4`
pointwise over the rectangle `[a₁, b₁] × [a₂, b₂]` containing that line. Then for every `R` with
`ρ(R) ∈ [0, 1]` and `L(R) ≥ 0`, and every map `u`, the integrated curvature of `K_R` along `u`
over the stretched rectangle `[a₁, b₁ + L(R)] × [a₂, b₂]` is at most `∫ M` over the original
rectangle. -/
theorem integral_abs_hamiltonianCurvature_cutoffNeckFamily_le (ω : SymplecticForm V)
    (hρ : ρ R ∈ Icc (0 : ℝ) 1) (hL : 0 ≤ L R) (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0)
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (u : ℝ × ℝ → V) {M : ℝ × ℝ → ℝ}
    {a b : ℝ × ℝ} (hac : a.1 ≤ c) (hcb : c ≤ b.1)
    (hM : ∀ z ∈ Icc a b, ∀ x,
      |ω.hamiltonianCurvature Ks Kt z x| + |ω.poissonBracket (Ks z) (Kt z) x| / 4 ≤ M z)
    (hMi : IntegrableOn M (Icc a b)) :
    ∫ z in Icc a (b.1 + L R, b.2),
        |ω.hamiltonianCurvature (cutoffNeckFamily ρ L c Ks R) (cutoffNeckFamily ρ L c Kt R) z
          (u z)| ≤
      ∫ z in Icc a b, M z := by
  simpa using ω.constSmooth.integral_abs_hamiltonianCurvature_cutoffNeckFamily_le hρ hL hKs hKt u
    hac hcb (by simpa [poissonBracket_constSmooth] using hM) hMi

/-- **Uniform energy estimate for the family.** Under the hypotheses of
`integral_abs_hamiltonianCurvature_cutoffNeckFamily_le`, for `C¹` data `K` and a map `u` that
is `C¹` near the stretched rectangle, the Floer energy of `u` for `K_R` differs from its
symplectic area plus the boundary integral of the pulled-back one-form `K_R(u)` by at most `∫ M`
over the original rectangle, for every `R` with `ρ(R) ∈ [0, 1]` and `L(R) ≥ 0`. -/
theorem abs_integral_floerEnergyDensity_cutoffNeckFamily_sub_le (ω : SymplecticForm V)
    (hρ : ρ R ∈ Icc (0 : ℝ) 1) (hL : 0 ≤ L R) (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0)
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (hKsd : ContDiff ℝ 1 (uncurry Ks))
    (hKtd : ContDiff ℝ 1 (uncurry Kt)) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u U) {M : ℝ × ℝ → ℝ} {a b : ℝ × ℝ} (hac : a.1 ≤ c) (hcb : c ≤ b.1)
    (hab : a.2 ≤ b.2) (habU : Icc a (b.1 + L R, b.2) ⊆ U)
    (hM : ∀ z ∈ Icc a b, ∀ x,
      |ω.hamiltonianCurvature Ks Kt z x| + |ω.poissonBracket (Ks z) (Kt z) x| / 4 ≤ M z)
    (hMi : IntegrableOn M (Icc a b)) :
    |(∫ z in Icc a (b.1 + L R, b.2),
        ω.floerEnergyDensity (cutoffNeckFamily ρ L c Ks R) (cutoffNeckFamily ρ L c Kt R) u z) -
      ((∫ z in Icc a (b.1 + L R, b.2),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ((∫ s in a.1..b.1 + L R, cutoffNeckFamily ρ L c Ks R (s, a.2) (u (s, a.2))) +
          (∫ t in a.2..b.2, cutoffNeckFamily ρ L c Kt R (b.1 + L R, t) (u (b.1 + L R, t))) -
          (∫ s in a.1..b.1 + L R, cutoffNeckFamily ρ L c Ks R (s, b.2) (u (s, b.2))) -
          ∫ t in a.2..b.2, cutoffNeckFamily ρ L c Kt R (a.1, t) (u (a.1, t))))| ≤
      ∫ z in Icc a b, M z := by
  rw [cutoffNeckFamily_eq_neckStretch, cutoffNeckFamily_eq_neckStretch]
  exact ω.abs_integral_floerEnergyDensity_neckStretch_sub_le hL
    (eventually_const_mul_eq_zero _ hKs) (eventually_const_mul_eq _ hKt)
    (contDiff_const.mul hKsd) (contDiff_const.mul hKtd) hU hu hac hcb hab habU
    (fun z hz x ↦ (ω.abs_hamiltonianCurvature_const_mul_le hρ z x).trans (hM z hz x)) hMi

end SymplecticForm

end TauCeti
