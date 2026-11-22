/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Convolution.ConeDecay
import TauCeti.Analysis.Distribution.TestFunction.FourierAtom
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.Normed.Module.OppositeCones

/-!
# Products of distributions under the wave front condition

Two distributions cannot be multiplied in general: the product `δ₀ · δ₀` has no meaning.
Hörmander's criterion (Hörmander I, Theorem 8.2.10) says that the product of `S` and `T` exists
near a point `x` when no covector `(x, ξ)` of the wave front set of `S` is the negative of a
covector `(x, -ξ)` of the wave front set of `T`. The reason is the convolution formula
`(φ² S T)^ = (φ S)^ * (φ T)^` for a cutoff `φ`: the localized Fourier transform
`η ↦ S (φ e_η)` decays rapidly away from the directions of the wave front set of `S` over the
support of `φ`, that of `T` away from the directions of `WF(T)`, and the condition says that in
every direction `η` one of the two factors `S (φ e_η)` and `T (φ e_(-η))` decays rapidly.

This file constructs the product `φ² S T` of the cut-off distributions and glues these into the
product `S T` on `Ω`. Write
`NoOppositeCovectorsOn S T K` (`Distribution.NoOppositeCovectorsOn`) when there are no covectors
`(x, ξ)` of `WF(S)` and `(y, -ξ)` of `WF(T)` over points `x, y ∈ K`. If this holds over the support
of `φ`, then `Distribution.cutoffProduct S T φ h` is the distribution

`ψ ↦ ∫ S (φ e_η) T (ψ φ e_(-η)) dη`,

with `e_η x = 𝐞 (-⟪x, η⟫)` and `η ↦ T (φ e_η)` the localized Fourier transform
`Distribution.localFourier`. The integral converges absolutely
(`Distribution.NoOppositeCovectorsOn.exists_integrable_and_norm_integral_le`), with a bound by
finitely many derivatives of `ψ`, so that `cutoffProduct` is continuous. The pointwise
condition of Hörmander implies the uniform one on a neighbourhood
(`Distribution.exists_mem_nhds_noOppositeCovectorsOn`), and a distribution without wave front set
over `K` satisfies it against every other distribution
(`Distribution.noOppositeCovectorsOn_of_forall_notMem_waveFrontSet_right`), for instance a smooth
function (`Distribution.noOppositeCovectorsOn_of_apply_eq_integral_right`).

The product extends multiplication by smooth functions in either factor: if `T` coincides near the
support of `φ` with a smooth function `g`, then `φ² S T` is the distribution `ψ ↦ S (ψ φ² g)`
(`Distribution.cutoffProduct_apply_of_apply_eq_integral_right`), and symmetrically in `S`
(`Distribution.cutoffProduct_apply_of_apply_eq_integral_left`). Both rest on Fourier inversion for
cut-off distributions, `∫ 𝓕⁻ f η T (φ e_η) dη = T (φ f)`
(`Distribution.integral_fourierInv_mul_localFourier`). For the point mass, the condition fails at
its point in every positive dimension (`Distribution.not_noOppositeCovectorsOn_delta_delta`), so
`δ₀ · δ₀` is not covered.

The wave front set of the product lies in the sums of the frequencies of the factors. Writing
`Σ_K(S)` for the frequencies of `WF(S)` over `K`, pooled over all points of `K`,

`WF(φ² S T) ⊆ supp φ × ((Σ_K(S) ∪ {0}) + (Σ_K(T) ∪ {0}))`, with `K = supp φ`

(`Distribution.waveFrontSet_cutoffProduct_subset`). This is a cut-off analogue of Hörmander I,
Theorem 8.2.10, and its proof follows Hörmander's; it is not pointwise, since the frequencies of
`WF(S)` and `WF(T)` added here may come from different points of `supp φ`. The global pointwise
bound, where both come from the same point, is not proved here.

The proof starts from the convolution formula
`(χ φ² S T)^(ζ) = ∫ S (φ e_η) T (χ φ e_(ζ - η)) dη` (`Distribution.localFourier_cutoffProduct`).
Thicken `Σ_K(S)` and `Σ_K(T)` to open cones `U₁` and `U₂`, off which the two factors decay
rapidly (`TauCeti.exists_cones_of_notMem_add`). If `ζ` lies in a small cone around a frequency
outside the sum, then for each `η` at most one of `η ∈ U₁` and `ζ - η ∈ U₂` holds, and the
decaying factor is evaluated at a frequency comparable to `ζ`, so the convolution decays
(`TauCeti.exists_one_add_norm_pow_mul_norm_integral_mul_le`). This rests on the fact that
`Σ_K(S)` and `Σ_K(T)`, together with `0`, are closed
(`Distribution.isClosed_insert_zero_image_snd_waveFrontSet_inter`) cones without opposite
directions, so that their sum is closed (`TauCeti.isClosed_add_of_forall_neg_mem_imp_eq_zero`).
The same bound holds with any such closed cones in place of `Σ_K(S)` and `Σ_K(T)`
(`Distribution.waveFrontSet_cutoffProduct_subset_of_cones`). This is a cut-off analogue, with one
pair of cones over all of `supp φ`, of Brouder, Dang and Hélein, Theorem 6.1, whose cones are
taken at each point.

The cut-off products glue to the product `S T` on all of `Ω`. The key identity moves a Schwartz
multiplier `a` from one factor to the other,
`∫ S (a φ e_η) T (g e_(-η)) dη = ∫ S (φ e_η) T (a g e_(-η)) dη`
(`Distribution.NoOppositeCovectorsOn.integral_localFourier_mul_localFourier_neg_eq`): writing `a`
as the Fourier integral of `𝓕⁻ a` on both sides gives the same absolutely convergent double
integral. Hence on a test function `ψ` supported where `φ = 1`, the value `(φ² S T) ψ` is
`∫ S (χ e_η) T (ψ e_(-η)) dη` for any real cutoff `χ` equal to one on `tsupport ψ` and supported
where `φ = 1` (`Distribution.cutoffProduct_apply_eq_integral`), and so does not depend on `φ`
(`Distribution.cutoffProduct_congr`). If Hörmander's condition holds at every point, the local
products glue (`Distribution.existsUnique_gluing`) to `Distribution.product S T h`, characterized
by agreeing with `φ² S T` where `φ = 1` (`Distribution.product_apply_of_eventuallyEq_one`,
`Distribution.eq_product_iff`).

## Main declarations

* `Distribution.NoOppositeCovectorsOn S T K`: no opposite covectors of `WF(S)` and `WF(T)` over `K`,
  with `noOppositeCovectorsOn_iff`.
* `Distribution.exists_mem_nhds_noOppositeCovectorsOn`: Hörmander's pointwise condition at `x`
  gives the condition on a neighbourhood of `x`.
* `Distribution.NoOppositeCovectorsOn.exists_forall_one_add_norm_pow_mul_le`: under the condition
  over the support of `φ`, `S (φ e_η) T (φ' e_(-η))` decays rapidly in `η`, uniformly over the
  cutoffs `φ'` supported in the support of `φ` with bounded derivatives.
* `Distribution.cutoffProduct S T φ h`: the product `φ² S T`, with `cutoffProduct_apply`.
* `Distribution.cutoffProduct_add_left`, `Distribution.cutoffProduct_smul_left`,
  `Distribution.cutoffProduct_add_right`, `Distribution.cutoffProduct_smul_right`: bilinearity.
* `Distribution.dsupport_cutoffProduct_subset`: the support lies in `supp φ ∩ supp T`.
* `Distribution.cutoffProduct_apply_of_apply_eq_integral_right`,
  `Distribution.cutoffProduct_apply_of_apply_eq_integral_left`: agreement with multiplication by
  a smooth function.
* `Distribution.complexPairing_cutoffProduct`, `Distribution.localFourier_cutoffProduct`: the
  product on complex test functions, and its localized Fourier transforms as convolutions.
* `Distribution.waveFrontSet_cutoffProduct_subset_of_cones`,
  `Distribution.waveFrontSet_cutoffProduct_subset`: the wave front set of the product.
* `Distribution.NoOppositeCovectorsOn.integral_localFourier_mul_localFourier_neg_eq`: a Schwartz
  multiplier moves across the product integral.
* `Distribution.cutoffProduct_apply_eq_integral`, `Distribution.cutoffProduct_congr`: where `φ = 1`,
  the product `φ² S T` does not depend on `φ`.
* `Distribution.product S T h`: the product of `S` and `T` under Hörmander's condition at every
  point, with `product_apply_of_eventuallyEq_one` and the characterization `eq_product_iff`.
* `Distribution.product_add_left`, `Distribution.product_smul_left`,
  `Distribution.product_add_right`, `Distribution.product_smul_right`: bilinearity.
* `Distribution.dsupport_product_subset`: the support lies in `supp S ∩ supp T`.
* `Distribution.product_apply_of_apply_eq_integral_right`,
  `Distribution.product_apply_of_apply_eq_integral_left`: the product with a smooth function is
  multiplication by that function.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.10 and its proof (the product of distributions); the bounds here are
  cut-off, non-pointwise analogues.
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, Studia Math. 232 (2016), arXiv:1409.7662v2, Theorem 6.1,
  whose cone form is followed here with one pair of cones over the support of the cutoff.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory Module
open scoped Distributions Topology FourierTransform ContDiff SchwartzMap Pointwise NNReal
open scoped RealInnerProductSpace

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}
  {S S' T T' : 𝓓'(Ω, ℂ)} {K K' : Set E}

/-! ### The wave front condition -/

/-- The distributions `S` and `T` have **no opposite covectors over `K`** if no covector `(x, ξ)`
of the wave front set of `S` is opposite to a covector `(y, -ξ)` of the wave front set of `T`, for
points `x, y ∈ K`. Over a single point this is Hörmander's condition for the product `S T`; over
the support of a cutoff `φ` it is the condition under which `φ² S T` is constructed. -/
def NoOppositeCovectorsOn (S T : 𝓓'(Ω, ℂ)) (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ ξ : E, (x, ξ) ∈ S.waveFrontSet → (y, -ξ) ∉ T.waveFrontSet

/-- Unfolding `NoOppositeCovectorsOn`. -/
theorem noOppositeCovectorsOn_iff : NoOppositeCovectorsOn S T K ↔
    ∀ x ∈ K, ∀ y ∈ K, ∀ ξ : E, (x, ξ) ∈ S.waveFrontSet → (y, -ξ) ∉ T.waveFrontSet :=
  Iff.rfl

/-- Over a single point `x`, `S` and `T` have no opposite covectors if and only if no covector
`(x, ξ)` of the wave front set of `S` has its opposite `(x, -ξ)` in the wave front set of `T`. -/
theorem noOppositeCovectorsOn_singleton_iff {x : E} : NoOppositeCovectorsOn S T {x} ↔
    ∀ ξ : E, (x, ξ) ∈ S.waveFrontSet → (x, -ξ) ∉ T.waveFrontSet := by
  simp [noOppositeCovectorsOn_iff]

theorem NoOppositeCovectorsOn.mono (h : NoOppositeCovectorsOn S T K) (hK : K' ⊆ K) :
    NoOppositeCovectorsOn S T K' :=
  fun x hx y hy ξ hξ ↦ h x (hK hx) y (hK hy) ξ hξ

theorem NoOppositeCovectorsOn.symm (h : NoOppositeCovectorsOn S T K) :
    NoOppositeCovectorsOn T S K := fun x hx y hy ξ hT hS ↦
  h y hy x hx (-ξ) hS (by rwa [neg_neg])

theorem noOppositeCovectorsOn_comm :
    NoOppositeCovectorsOn S T K ↔ NoOppositeCovectorsOn T S K :=
  ⟨.symm, .symm⟩

theorem NoOppositeCovectorsOn.smul_left (h : NoOppositeCovectorsOn S T K) (c : ℂ) :
    NoOppositeCovectorsOn (c • S) T K :=
  fun x hx y hy ξ hξ ↦ h x hx y hy ξ (waveFrontSet_smul_subset c S hξ)

theorem NoOppositeCovectorsOn.smul_right (h : NoOppositeCovectorsOn S T K) (c : ℂ) :
    NoOppositeCovectorsOn S (c • T) K :=
  (h.symm.smul_left c).symm

/-- If `T` has no wave front set over `K`, then `S` and `T` have no opposite covectors over `K`,
whatever `S` is. -/
theorem noOppositeCovectorsOn_of_forall_notMem_waveFrontSet_right
    (hT : ∀ y ∈ K, ∀ ξ : E, (y, ξ) ∉ T.waveFrontSet) : NoOppositeCovectorsOn S T K :=
  fun _ _ y hy ξ _ ↦ hT y hy (-ξ)

/-- If `S` has no wave front set over `K`, then `S` and `T` have no opposite covectors over `K`,
whatever `T` is. -/
theorem noOppositeCovectorsOn_of_forall_notMem_waveFrontSet_left
    (hS : ∀ x ∈ K, ∀ ξ : E, (x, ξ) ∉ S.waveFrontSet) : NoOppositeCovectorsOn S T K :=
  (noOppositeCovectorsOn_of_forall_notMem_waveFrontSet_right hS).symm

/-- If `(x, ν)` and `(y, -ν)` are not both in the wave front sets of `S` and `T` and `S` is not
microlocally smooth at `(x, ν)`, then `T` is microlocally smooth at `(y, -ν)`. -/
private theorem isMicrolocallySmoothAt_neg_of_not_isMicrolocallySmoothAt {x y ν : E} (hx : x ∈ Ω)
    (hy : y ∈ Ω) (hν : ν ≠ 0) (h : (x, ν) ∈ S.waveFrontSet → (y, -ν) ∉ T.waveFrontSet)
    (hS : ¬ S.IsMicrolocallySmoothAt x ν) : T.IsMicrolocallySmoothAt y (-ν) := by
  by_contra hT
  exact h (mem_waveFrontSet_iff.2 ⟨hx, hν, hS⟩) (mem_waveFrontSet_iff.2 ⟨hy, neg_ne_zero.2 hν, hT⟩)

variable [FiniteDimensional ℝ E]

theorem NoOppositeCovectorsOn.add_left (h : NoOppositeCovectorsOn S T K)
    (h' : NoOppositeCovectorsOn S' T K) : NoOppositeCovectorsOn (S + S') T K :=
  fun x hx y hy ξ hξ ↦ (waveFrontSet_add_subset S S' hξ).elim (h x hx y hy ξ) (h' x hx y hy ξ)

theorem NoOppositeCovectorsOn.add_right (h : NoOppositeCovectorsOn S T K)
    (h' : NoOppositeCovectorsOn S T' K) : NoOppositeCovectorsOn S (T + T') K :=
  (h.symm.add_left h'.symm).symm

/-- **Hörmander's pointwise condition is open.** If no covector `(x, ξ)` of `WF(S)` is opposite to a
covector `(x, -ξ)` of `WF(T)` at a point `x ∈ Ω`, then `S` and `T` have no opposite covectors over
some neighbourhood of `x`. -/
theorem exists_mem_nhds_noOppositeCovectorsOn {x : E} (hx : x ∈ Ω)
    (h : ∀ ξ : E, (x, ξ) ∈ S.waveFrontSet → (x, -ξ) ∉ T.waveFrontSet) :
    ∃ U ∈ 𝓝 x, NoOppositeCovectorsOn S T U := by
  -- Near each unit covector one of the two distributions is microlocally smooth on a
  -- neighbourhood of `x` and an open cone: the cutoff and cone witnessing microlocal smoothness
  -- at `x` witness it wherever the cutoff is nonzero.
  have hloc : ∀ ν ∈ sphere (0 : E) 1, ∃ V ∈ 𝓝 x, ∃ G : Set E, IsOpen G ∧ ν ∈ G ∧
      (∀ t : ℝ, 0 < t → ∀ ζ ∈ G, t • ζ ∈ G) ∧
      ((∀ y ∈ V, ∀ ζ ∈ G, S.IsMicrolocallySmoothAt y ζ) ∨
        ∀ y ∈ V, ∀ ζ ∈ G, T.IsMicrolocallySmoothAt y (-ζ)) := by
    intro ν hν
    have hν0 : ν ≠ 0 := ne_of_mem_sphere hν one_ne_zero
    by_cases hS : S.IsMicrolocallySmoothAt x ν
    · obtain ⟨φ, hφ, Γ, hΓ, hνΓ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hS
      exact ⟨{y | φ y ≠ 0}, (isOpen_ne_fun φ.continuous continuous_const).mem_nhds hφ, Γ, hΓ, hνΓ,
        hcone, Or.inl fun y hy ζ hζ ↦
          isMicrolocallySmoothAt_iff.2 ⟨φ, hy, Γ, hΓ, hζ, hcone, hdecay⟩⟩
    · obtain ⟨φ, hφ, Γ, hΓ, hνΓ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1
        (isMicrolocallySmoothAt_neg_of_not_isMicrolocallySmoothAt hx hx hν0 (h ν) hS)
      exact ⟨{y | φ y ≠ 0}, (isOpen_ne_fun φ.continuous continuous_const).mem_nhds hφ, -Γ,
        hΓ.neg, Set.mem_neg.2 hνΓ, TauCeti.forall_smul_mem_neg hcone,
        Or.inr fun y hy ζ hζ ↦
          isMicrolocallySmoothAt_iff.2 ⟨φ, hy, Γ, hΓ, Set.mem_neg.1 hζ, hcone, hdecay⟩⟩
  choose! V hV G hG hνG hcone hVG using hloc
  obtain ⟨t, ht⟩ := TauCeti.exists_finset_compl_singleton_subset_biUnion
    (Γ := fun ν : sphere (0 : E) 1 ↦ G ν) (fun ν ↦ hG ν ν.property) (fun ν ↦ hνG ν ν.property)
    fun ν ↦ hcone ν ν.property
  refine ⟨⋂ ν ∈ t, V ν, (biInter_finset_mem t).2 fun ν _ ↦ hV ν ν.property,
      fun y hy z hz ξ hS hT ↦ ?_⟩
  -- The nonzero covector `ξ` lies in one of the finitely many cones `G ν`.
  obtain ⟨ν, hνt, hξG⟩ := mem_iUnion₂.1 (ht (mem_waveFrontSet_iff.1 hS).2.1)
  rcases hVG ν ν.property with hS' | hT'
  · exact (mem_waveFrontSet_iff.1 hS).2.2 (hS' y (mem_iInter₂.1 hy ν hνt) ξ hξG)
  · exact (mem_waveFrontSet_iff.1 hT).2.2 (hT' z (mem_iInter₂.1 hz ν hνt) ξ hξG)

/-- The point mass and itself have opposite covectors over every set containing its point, in every
positive dimension: `δ_{x₀} · δ_{x₀}` is not covered by the wave front condition. -/
theorem not_noOppositeCovectorsOn_delta_delta [Nontrivial E] {x₀ : E} (hx₀ : x₀ ∈ Ω)
    (hK : x₀ ∈ K) :
    ¬ NoOppositeCovectorsOn (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ)))
      (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))) K := fun h ↦ by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  refine h x₀ hK x₀ hK ξ ?_ ?_
  · rw [waveFrontSet_delta hx₀]
    exact ⟨rfl, hξ⟩
  · rw [waveFrontSet_delta hx₀]
    exact ⟨rfl, neg_ne_zero.2 hξ⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- If `T` coincides with a smooth function `g` on an open set `U ⊇ K`, then `S` and `T` have no
opposite covectors over `K`, whatever `S` is: `T` has no wave front set over `U`. -/
theorem noOppositeCovectorsOn_of_apply_eq_integral_right {U : Set E} (hU : IsOpen U) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (hT : ∀ χ : 𝓓(Ω, ℝ), tsupport χ ⊆ U → T χ = ∫ y, χ y • g y)
    (hKU : K ⊆ U) : NoOppositeCovectorsOn S T K :=
  noOppositeCovectorsOn_of_forall_notMem_waveFrontSet_right fun _ hy _ hT' ↦
    (mem_waveFrontSet_iff.1 hT').2.2 (isMicrolocallySmoothAt_of_apply_eq_integral hU hg hT
      (hKU hy) (mem_waveFrontSet_iff.1 hT').1 _)

/-- If `S` coincides with a smooth function `g` on an open set `U ⊇ K`, then `S` and `T` have no
opposite covectors over `K`, whatever `T` is. -/
theorem noOppositeCovectorsOn_of_apply_eq_integral_left {U : Set E} (hU : IsOpen U) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (hS : ∀ χ : 𝓓(Ω, ℝ), tsupport χ ⊆ U → S χ = ∫ y, χ y • g y)
    (hKU : K ⊆ U) : NoOppositeCovectorsOn S T K :=
  (noOppositeCovectorsOn_of_apply_eq_integral_right hU hg hS hKU).symm

omit [MeasurableSpace E] [BorelSpace E] in
/-- Near a nonzero covector `ν`, one of the two factors `S (φ e_η)` and `T (φ' e_(-η))` decays
rapidly in a cone and the other grows at most polynomially, uniformly over the cutoffs `φ'`
supported in the support of `φ` with bounded derivatives. The polynomial growth of both factors,
uniform in `φ'` for `T`, is given by `hS` and `hT`. -/
private theorem NoOppositeCovectorsOn.exists_isOpen_cone_forall_one_add_norm_pow_mul_le
    {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ)) {CS : ℝ} {kS : ℕ}
    (hCS0 : 0 ≤ CS) (hS : ∀ η, ‖S.localFourier φ η‖ ≤ CS * (1 + ‖η‖) ^ kS) {kT : ℕ} {CT : ℝ}
    (hCT0 : 0 ≤ CT) (hT : ∀ φ' : 𝓓(Ω, ℂ), tsupport φ' ⊆ tsupport φ → ∀ B : ℝ,
      (∀ i ≤ kT, ∀ y, ‖iteratedFDeriv ℝ i φ' y‖ ≤ B) →
        ∀ η, ‖T.localFourier φ' η‖ ≤ CT * B * (1 + ‖η‖) ^ kT)
    (N : ℕ) {ν : E} (hν0 : ν ≠ 0) :
    ∃ Γ : Set E, IsOpen Γ ∧ ν ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ (r : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ' : 𝓓(Ω, ℂ), tsupport φ' ⊆ tsupport φ → ∀ B : ℝ,
        (∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i φ' y‖ ≤ B) → ∀ η ∈ Γ,
          (1 + ‖η‖) ^ N * (‖S.localFourier φ η‖ * ‖T.localFourier φ' (-η)‖) ≤ C * B := by
  have hK : IsCompact (tsupport (φ : E → ℂ)) := φ.hasCompactSupport
  by_cases hSν : ∀ x ∈ tsupport φ, S.IsMicrolocallySmoothAt x ν
  · -- `S (φ e_η)` decays near `ν`, and `T (φ' e_(-η))` grows at most polynomially.
    obtain ⟨W, -, hKW, Γ, hΓ, hνΓ, hcone, hdecay⟩ :=
      exists_isOpen_cone_forall_decay_of_isCompact hK hSν
    obtain ⟨C, hC⟩ := hdecay φ (hKW.trans subset_union_left) (N + kT)
    refine ⟨Γ, hΓ, hνΓ, hcone, kT, CT * max C 0, by positivity, fun φ' hφ' B hB η hη ↦ ?_⟩
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
    have hT' := hT φ' hφ' B hB (-η)
    rw [norm_neg] at hT'
    calc (1 + ‖η‖) ^ N * (‖S.localFourier φ η‖ * ‖T.localFourier φ' (-η)‖)
        ≤ (1 + ‖η‖) ^ N * (‖S.localFourier φ η‖ * (CT * B * (1 + ‖η‖) ^ kT)) := by gcongr
      _ = CT * B * ((1 + ‖η‖) ^ (N + kT) * ‖S.localFourier φ η‖) := by ring
      _ ≤ CT * B * max C 0 := by
          gcongr
          exact (hC η hη).trans (le_max_left _ _)
      _ = CT * max C 0 * B := by ring
  · -- Otherwise `S` is singular at some `(x, ν)` over the support of `φ`, so `T` is microlocally
    -- smooth at every `(y, -ν)` there, uniformly in the cutoff.
    push Not at hSν
    obtain ⟨x, hx, hSx⟩ := hSν
    have hTν : ∀ y ∈ tsupport φ, T.IsMicrolocallySmoothAt y (-ν) := fun y hy ↦
      isMicrolocallySmoothAt_neg_of_not_isMicrolocallySmoothAt (φ.tsupport_subset hx)
        (φ.tsupport_subset hy) hν0 (h x hx y hy ν) hSx
    obtain ⟨Γ, hΓ, hνΓ, hcone, hdecay⟩ :=
      exists_isOpen_cone_forall_one_add_norm_pow_mul_norm_localFourier_le_of_isCompact hK hTν
    obtain ⟨r, C, hC0, hC⟩ := hdecay (N + kS)
    refine ⟨-Γ, hΓ.neg, Set.mem_neg.2 hνΓ, TauCeti.forall_smul_mem_neg hcone, r, CS * C,
      by positivity, fun φ' hφ' B hB η hη ↦ ?_⟩
    have hT' := hC φ' hφ' B hB (-η) (Set.mem_neg.1 hη)
    rw [norm_neg] at hT'
    calc (1 + ‖η‖) ^ N * (‖S.localFourier φ η‖ * ‖T.localFourier φ' (-η)‖)
        ≤ (1 + ‖η‖) ^ N * (CS * (1 + ‖η‖) ^ kS * ‖T.localFourier φ' (-η)‖) := by
          gcongr
          exact hS η
      _ = CS * ((1 + ‖η‖) ^ (N + kS) * ‖T.localFourier φ' (-η)‖) := by ring
      _ ≤ CS * (C * B) := by gcongr
      _ = CS * C * B := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Rapid decay of the product of localized Fourier transforms.** If `S` and `T` have no opposite
covectors over the support of `φ`, then `S (φ e_η) T (φ' e_(-η))` decays rapidly in `η`, uniformly
over the cutoffs `φ'` supported in the support of `φ` with bounded derivatives: for every `N` there
are `r` and `C` such that `(1 + ‖η‖) ^ N ‖S (φ e_η)‖ ‖T (φ' e_(-η))‖ ≤ C B` whenever the
derivatives of `φ'` of order at most `r` are bounded by `B`. -/
theorem NoOppositeCovectorsOn.exists_forall_one_add_norm_pow_mul_le {φ : 𝓓(Ω, ℂ)}
    (h : NoOppositeCovectorsOn S T (tsupport φ)) (N : ℕ) :
    ∃ (r : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ' : 𝓓(Ω, ℂ), tsupport φ' ⊆ tsupport φ → ∀ B : ℝ,
      (∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i φ' y‖ ≤ B) →
        ∀ η, (1 + ‖η‖) ^ N * (‖S.localFourier φ η‖ * ‖T.localFourier φ' (-η)‖) ≤ C * B := by
  -- Polynomial growth of both localized Fourier transforms, uniform in `φ'` for `T`; in particular
  -- both factors are bounded at the zero frequency.
  obtain ⟨CS, kS, hS⟩ := exists_norm_localFourier_le S φ
  obtain ⟨kT, CT, hCT0, hT⟩ := exists_forall_norm_localFourier_le T
    (K := ⟨tsupport φ, φ.hasCompactSupport⟩) φ.tsupport_subset
  have hCS0 : 0 ≤ CS := by simpa using (norm_nonneg _).trans (hS 0)
  -- Finitely many cones given by `exists_isOpen_cone_forall_one_add_norm_pow_mul_le` cover the
  -- unit sphere, hence every nonzero frequency.
  choose! Γ hΓ hνΓ hcone r C hC0 hC using fun ν (hν : ν ∈ sphere (0 : E) 1) ↦
    h.exists_isOpen_cone_forall_one_add_norm_pow_mul_le hCS0 hS hCT0 hT N
      (ne_of_mem_sphere hν one_ne_zero)
  obtain ⟨t, ht⟩ := TauCeti.exists_finset_compl_singleton_subset_biUnion
    (Γ := fun ν : sphere (0 : E) 1 ↦ Γ ν) (fun ν ↦ hΓ ν ν.property) (fun ν ↦ hνΓ ν ν.property)
    fun ν ↦ hcone ν ν.property
  have hC0' : 0 ≤ ∑ ν ∈ t, C ν := Finset.sum_nonneg fun ν _ ↦ hC0 ν ν.property
  refine ⟨max kT (t.sup fun ν ↦ r ν), CS * CT + ∑ ν ∈ t, C ν,
    add_nonneg (mul_nonneg hCS0 hCT0) hC0', fun φ' hφ' B hB η ↦ ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  by_cases hη : η = 0
  · subst hη
    have hT0 := hT φ' hφ' B (fun i hi ↦ hB i (hi.trans (le_max_left _ _))) (-0)
    simp only [norm_zero, add_zero, one_pow, mul_one, one_mul, neg_zero] at hS hT0 ⊢
    calc ‖S.localFourier φ 0‖ * ‖T.localFourier φ' 0‖ ≤ CS * (CT * B) := by
          gcongr
          · simpa using hS 0
      _ ≤ (CS * CT + ∑ ν ∈ t, C ν) * B := by nlinarith
  · obtain ⟨ν, hνt, hηΓ⟩ := mem_iUnion₂.1 (ht hη)
    calc (1 + ‖η‖) ^ N * (‖S.localFourier φ η‖ * ‖T.localFourier φ' (-η)‖) ≤ C ν * B :=
          hC ν ν.property φ' hφ' B (fun i hi ↦ hB i (hi.trans ((Finset.le_sup
            (f := fun ν : sphere (0 : E) 1 ↦ r ν) hνt).trans (le_max_right _ _)))) η hηΓ
      _ ≤ (CS * CT + ∑ ν ∈ t, C ν) * B := by
          gcongr
          exact le_add_of_nonneg_of_le (mul_nonneg hCS0 hCT0)
            (Finset.single_le_sum (f := fun ν : sphere (0 : E) 1 ↦ C ν)
              (fun ν _ ↦ hC0 ν ν.property) hνt)

/-- **Absolute convergence of the product integral.** If `S` and `T` have no opposite covectors over
the support of `φ`, then `η ↦ S (φ e_η) T (φ' e_(-η))` is integrable for every cutoff `φ'`
supported in the support of `φ`, and its integral is bounded by `C B` whenever the derivatives of
`φ'` of order at most `r` are bounded by `B`. -/
theorem NoOppositeCovectorsOn.exists_integrable_and_norm_integral_le {φ : 𝓓(Ω, ℂ)}
    (h : NoOppositeCovectorsOn S T (tsupport φ)) :
    ∃ (r : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ' : 𝓓(Ω, ℂ), tsupport φ' ⊆ tsupport φ → ∀ B : ℝ,
      (∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i φ' y‖ ≤ B) →
        Integrable (fun η ↦ S.localFourier φ η * T.localFourier φ' (-η)) ∧
          ‖∫ η, S.localFourier φ η * T.localFourier φ' (-η)‖ ≤ C * B := by
  set d := finrank ℝ E + 1
  obtain ⟨r, C, hC0, hC⟩ := h.exists_forall_one_add_norm_pow_mul_le d
  have hint : Integrable fun η : E ↦ (1 + ‖η‖) ^ (-(d : ℝ)) :=
    integrable_one_add_norm (by simp [d])
  refine ⟨r, C * ∫ η : E, (1 + ‖η‖) ^ (-(d : ℝ)),
    mul_nonneg hC0 (integral_nonneg fun _ ↦ by positivity), fun φ' hφ' B hB ↦ ?_⟩
  have hbound (η : E) : ‖S.localFourier φ η * T.localFourier φ' (-η)‖ ≤
      C * B * (1 + ‖η‖) ^ (-(d : ℝ)) := by
    have hpos : 0 < (1 + ‖η‖) ^ d := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, norm_mul, ← div_eq_mul_inv,
      le_div_iff₀ hpos, mul_comm]
    exact hC φ' hφ' B hB η
  have hmeas : AEStronglyMeasurable (fun η ↦ S.localFourier φ η * T.localFourier φ' (-η)) :=
    ((S.continuous_localFourier φ).mul
      ((T.continuous_localFourier φ').comp continuous_neg)).aestronglyMeasurable
  refine ⟨(hint.const_mul (C * B)).mono' hmeas (ae_of_all _ hbound),
    (norm_integral_le_of_norm_le (hint.const_mul (C * B)) (ae_of_all _ hbound)).trans_eq ?_⟩
  rw [integral_const_mul]
  ring

/-- The integrand of the product of `S` and `T` cut off by `φ` and `φ'` is integrable when `S` and
`T` have no opposite covectors over the support of `φ ⊇ supp φ'`. -/
theorem NoOppositeCovectorsOn.integrable_localFourier_mul_localFourier {φ φ' : 𝓓(Ω, ℂ)}
    (h : NoOppositeCovectorsOn S T (tsupport φ)) (hφ' : tsupport φ' ⊆ tsupport φ) :
    Integrable (fun η ↦ S.localFourier φ η * T.localFourier φ' (-η)) := by
  obtain ⟨r, _, _, hC⟩ := h.exists_integrable_and_norm_integral_le
  obtain ⟨B, -, hB⟩ := φ'.hasCompactSupport.exists_bound_iteratedFDeriv φ'.contDiff r
  exact (hC φ' hφ' B hB).1

/-! ### The product -/

/-- The integrand `η ↦ S (φ e_η) T (ψ φ e_(-η))` of the product `φ² S T` is integrable. -/
private theorem NoOppositeCovectorsOn.integrable_localFourier_mul_localFourier_smulLeftCLM
    {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ)) (ψ : 𝓓(Ω, ℝ)) :
    Integrable fun η ↦
      S.localFourier φ η * T.localFourier (TestFunction.smulLeftCLM ψ.contDiff φ) (-η) :=
  h.integrable_localFourier_mul_localFourier (tsupport_smulLeftCLM_subset_right _ φ)

/-- On real test functions `ψ` supported in a compact set `K`, the integral
`∫ S (φ e_η) T (ψ φ e_(-η)) dη` defining `φ² S T` is bounded by finitely many of the seminorms
of `ψ`. -/
private theorem NoOppositeCovectorsOn.exists_norm_integral_le_seminorm {φ : 𝓓(Ω, ℂ)}
    (h : NoOppositeCovectorsOn S T (tsupport φ)) {K : Compacts E} (hK : (K : Set E) ⊆ Ω) :
    ∃ (r : ℕ) (C : ℝ≥0), ∀ f : 𝓓_{K}(E, ℝ), ‖∫ η, S.localFourier φ η *
      T.localFourier (TestFunction.smulLeftCLM (ofSupportedIn hK f).contDiff φ) (-η)‖ ≤
        C * (Finset.Iic r).sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) f := by
  obtain ⟨r, C, hC0, hC⟩ := h.exists_integrable_and_norm_integral_le
  obtain ⟨A, hA0, hA⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff r
  refine ⟨r, (C * (2 ^ r * A)).toNNReal, fun f ↦ ?_⟩
  set M := (Finset.Iic r).sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) f
  -- The derivatives of `f` of order at most `r` are bounded by `M`, so those of `f φ` are
  -- bounded by `2 ^ r M A`.
  have hM : ∀ i ≤ r, ∀ y ∈ tsupport φ,
      ‖iteratedFDeriv ℝ i (fun z ↦ ((ofSupportedIn hK f z : ℝ) : ℂ)) y‖ ≤ M := fun i hi y _ ↦ by
    rw [show (fun z ↦ ((ofSupportedIn hK f z : ℝ) : ℂ)) = ofRealLI ∘ f from
        funext fun z ↦ by simp [coe_ofSupportedIn],
      ofRealLI.norm_iteratedFDeriv_comp_left f.contDiff.contDiffAt (mod_cast le_top)]
    exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
      (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hi))
  have hbound := (hC _ (tsupport_smulLeftCLM_subset_right (ofSupportedIn hK f).contDiff φ) _
    (TestFunction.norm_iteratedFDeriv_smulLeftCLM_le (ofSupportedIn hK f).contDiff φ subset_rfl
      (apply_nonneg _ _) hM hA)).2
  rw [Real.coe_toNNReal _ (by positivity)]
  exact hbound.trans_eq (by ring)

/-- **The product of cut-off distributions** `φ² S T`, for distributions `S` and `T` without
opposite covectors over the support of the cutoff `φ` (Hörmander I, Theorem 8.2.10): the
distribution

`ψ ↦ ∫ S (φ e_η) T (ψ φ e_(-η)) dη`,

where `η ↦ S (φ e_η)` is the localized Fourier transform. When `T` is a smooth function `g` near
the support of `φ`, it is `ψ ↦ S (ψ φ² g)`, and symmetrically in `S`. -/
def cutoffProduct (S T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (h : NoOppositeCovectorsOn S T (tsupport φ)) :
    𝓓'(Ω, ℂ) :=
  let Λ : 𝓓(Ω, ℝ) →ₗ[ℝ] ℂ :=
    { toFun ψ := ∫ η, S.localFourier φ η *
        T.localFourier (TestFunction.smulLeftCLM ψ.contDiff φ) (-η)
      map_add' ψ₁ ψ₂ := by
        -- The multiplier `⇑(ψ₁ + ψ₂)` of `(ψ₁ + ψ₂).contDiff` is definitionally `⇑ψ₁ + ⇑ψ₂`,
        -- since addition of test functions is pointwise, so `rw` matches `smulLeftCLM_add`.
        rw [TestFunction.smulLeftCLM_add ψ₁.contDiff ψ₂.contDiff]
        simp only [_root_.add_apply, localFourier_add_cutoff, mul_add]
        exact integral_add (h.integrable_localFourier_mul_localFourier_smulLeftCLM ψ₁)
          (h.integrable_localFourier_mul_localFourier_smulLeftCLM ψ₂)
      map_smul' c ψ := by
        -- Likewise `⇑(c • ψ)` is definitionally `c • ⇑ψ`, so `rw` matches `smulLeftCLM_smul`.
        rw [TestFunction.smulLeftCLM_smul ψ.contDiff c]
        simp only [_root_.smul_apply, ← Complex.coe_smul, localFourier_smul_cutoff,
          RingHom.id_apply, mul_left_comm _ (c : ℂ)]
        exact integral_const_mul _ _ }
  TestFunction.mkCLM ℝ Λ (map_add Λ) (map_smul Λ) fun K hK ↦ by
    obtain ⟨r, C, hC⟩ := h.exists_norm_integral_le_seminorm hK
    -- The seminorm inequality, evaluated at `f`, is `hC f` after unfolding `Λ`.
    exact WithSeminorms.continuous_normedSpace_rng ℂ
      (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) (Λ ∘ₗ (ofSupportedInCLM ℝ hK).toLinearMap)
      ⟨Finset.Iic r, C, fun f ↦ hC f⟩

/-- The value of the product `φ² S T` on a test function `ψ`:
`∫ S (φ e_η) T (ψ φ e_(-η)) dη`. -/
theorem cutoffProduct_apply (φ : 𝓓(Ω, ℂ)) (h : NoOppositeCovectorsOn S T (tsupport φ))
    (ψ : 𝓓(Ω, ℝ)) :
    S.cutoffProduct T φ h ψ =
      ∫ η, S.localFourier φ η * T.localFourier (TestFunction.smulLeftCLM ψ.contDiff φ) (-η) :=
  (rfl)

/-- The product `φ² S T` is additive in `S`. -/
theorem cutoffProduct_add_left {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    (h' : NoOppositeCovectorsOn S' T (tsupport φ)) :
    (S + S').cutoffProduct T φ (h.add_left h') =
      S.cutoffProduct T φ h + S'.cutoffProduct T φ h' := by
  ext ψ
  simp only [cutoffProduct_apply, add_apply, localFourier_add, add_mul]
  exact integral_add (h.integrable_localFourier_mul_localFourier_smulLeftCLM ψ)
    (h'.integrable_localFourier_mul_localFourier_smulLeftCLM ψ)

/-- The product `φ² S T` is complex-linear in `S`. -/
theorem cutoffProduct_smul_left {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    (c : ℂ) : (c • S).cutoffProduct T φ (h.smul_left c) = c • S.cutoffProduct T φ h := by
  ext ψ
  simp only [cutoffProduct_apply, smul_apply, localFourier_smul, mul_assoc,
    smul_eq_mul]
  exact integral_const_mul _ _

/-- The product `φ² S T` is additive in `T`. -/
theorem cutoffProduct_add_right {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    (h' : NoOppositeCovectorsOn S T' (tsupport φ)) :
    S.cutoffProduct (T + T') φ (h.add_right h') =
      S.cutoffProduct T φ h + S.cutoffProduct T' φ h' := by
  ext ψ
  simp only [cutoffProduct_apply, add_apply, localFourier_add, mul_add]
  exact integral_add (h.integrable_localFourier_mul_localFourier_smulLeftCLM ψ)
    (h'.integrable_localFourier_mul_localFourier_smulLeftCLM ψ)

/-- The product `φ² S T` is complex-linear in `T`. -/
theorem cutoffProduct_smul_right {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    (c : ℂ) : S.cutoffProduct (c • T) φ (h.smul_right c) = c • S.cutoffProduct T φ h := by
  ext ψ
  simp only [cutoffProduct_apply, smul_apply, localFourier_smul,
    mul_left_comm _ c, smul_eq_mul]
  exact integral_const_mul _ _

/-- **The support of the product.** The product `φ² S T` is supported in the support of `φ` and in
the support of `T`. -/
theorem dsupport_cutoffProduct_subset {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ)) :
    dsupport (S.cutoffProduct T φ h) ⊆ tsupport φ ∩ dsupport T := by
  have hc : IsClosed (tsupport (φ : E → ℂ) ∩ dsupport T) :=
    (isClosed_tsupport _).inter isClosed_dsupport
  -- A test function supported off this set makes the cutoff `ψ φ` vanish on the support of `T`.
  have hvan : IsVanishingOn (S.cutoffProduct T φ h) (tsupport φ ∩ dsupport T)ᶜ := fun ψ hψ ↦ by
    have hdis : Disjoint (tsupport (TestFunction.smulLeftCLM ψ.contDiff φ)) (dsupport T) :=
      disjoint_left.2 fun x hx hxT ↦ by
        have hx' := TestFunction.tsupport_smulLeftCLM_subset _ φ hx
        exact hψ hx'.1 ⟨hx'.2, hxT⟩
    simp [cutoffProduct_apply, localFourier_eq_zero_of_disjoint_dsupport hdis]
  have h' := (hvan.disjoint_dsupport hc.isOpen_compl).subset_compl_left
  rwa [compl_compl] at h'

/-! ### Agreement with multiplication by smooth functions -/

/-- If `T` coincides with a function `g` smooth on an open set `U` containing the support of `φ`,
then `φ g` is a Schwartz function `f` and `T (φ e_(-η)) = 𝓕⁻ f η`. -/
private theorem exists_schwartzMap_localFourier_neg_eq_fourierInv {U : Set E} (hU : IsOpen U)
    {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    (hT : ∀ χ : 𝓓(Ω, ℝ), tsupport χ ⊆ U → T χ = ∫ y, χ y • g y) {φ : 𝓓(Ω, ℂ)}
    (hφU : tsupport φ ⊆ U) :
    ∃ f : 𝓢(E, ℂ), (∀ y, f y = φ y * g y) ∧ ∀ η, T.localFourier φ (-η) = 𝓕⁻ f η := by
  have hfc : HasCompactSupport fun y ↦ φ y * g y := φ.hasCompactSupport.mul_right
  have hfd : ContDiff ℝ ∞ fun y ↦ φ y * g y := by
    simpa [mul_comm] using (ContinuousLinearMap.mul ℝ ℂ).contDiff_of_tsupport_subset_right hg
      φ.contDiff.contDiffOn hU hφU
  have hf := hfc.toSchwartzMap_toFun hfd
  refine ⟨hfc.toSchwartzMap hfd, hf, fun η ↦ ?_⟩
  rw [localFourier_eq_fourier (hg.continuousOn.locallyIntegrableOn hU.measurableSet) hT hφU,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, funext hf]

/-- **The product with a smooth function, on the right.** If `T` coincides with a function `g`
smooth on an open set `U` containing the support of `φ`, then `φ² S T` is the distribution
`ψ ↦ S (ψ φ² g)`: the product extends multiplication of `S` by smooth functions. -/
theorem cutoffProduct_apply_of_apply_eq_integral_right {U : Set E} (hU : IsOpen U) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (hT : ∀ χ : 𝓓(Ω, ℝ), tsupport χ ⊆ U → T χ = ∫ y, χ y • g y)
    {φ : 𝓓(Ω, ℂ)} (hφU : tsupport φ ⊆ U) (h : NoOppositeCovectorsOn S T (tsupport φ))
    (ψ : 𝓓(Ω, ℝ)) {χ : 𝓓(Ω, ℂ)} (hχ : ∀ x, χ x = ψ x * φ x ^ 2 * g x) :
    S.cutoffProduct T φ h ψ = S.complexPairing χ := by
  rw [cutoffProduct_apply]
  set φ' := TestFunction.smulLeftCLM ψ.contDiff φ
  have hφ'U : tsupport φ' ⊆ U := (tsupport_smulLeftCLM_subset_right ψ.contDiff φ).trans hφU
  -- `ψ φ g` is a Schwartz function `f`, and `T (ψ φ e_(-η)) = 𝓕⁻ f η`.
  obtain ⟨f, hf, hT'⟩ := exists_schwartzMap_localFourier_neg_eq_fourierInv hU hg hT hφ'U
  simp only [hT', mul_comm (S.localFourier φ _)]
  rw [integral_fourierInv_mul_localFourier, cutoffTempered_apply]
  intro x
  rw [hχ, hf]
  simp only [φ', TestFunction.smulLeftCLM_apply, Complex.real_smul]
  ring

/-- **The product with a smooth function, on the left.** If `S` coincides with a function `g`
smooth on an open set `U` containing the support of `φ`, then `φ² S T` is the distribution
`ψ ↦ T (ψ φ² g)`: the product extends multiplication of `T` by smooth functions. -/
theorem cutoffProduct_apply_of_apply_eq_integral_left {U : Set E} (hU : IsOpen U) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (hS : ∀ χ : 𝓓(Ω, ℝ), tsupport χ ⊆ U → S χ = ∫ y, χ y • g y)
    {φ : 𝓓(Ω, ℂ)} (hφU : tsupport φ ⊆ U) (h : NoOppositeCovectorsOn S T (tsupport φ))
    (ψ : 𝓓(Ω, ℝ)) {χ : 𝓓(Ω, ℂ)} (hχ : ∀ x, χ x = ψ x * φ x ^ 2 * g x) :
    S.cutoffProduct T φ h ψ = T.complexPairing χ := by
  -- `φ g` is a Schwartz function `f`, and `S (φ e_η) = 𝓕⁻ f (-η)`.
  obtain ⟨f, hf, hS''⟩ := exists_schwartzMap_localFourier_neg_eq_fourierInv hU hg hS hφU
  have hS' (η : E) : S.localFourier φ η = 𝓕⁻ f (-η) := by
    simpa using hS'' (-η)
  simp only [cutoffProduct_apply, hS']
  rw [← integral_neg_eq_self]
  simp only [neg_neg]
  rw [integral_fourierInv_mul_localFourier, cutoffTempered_apply]
  · intro x
    rw [hχ, hf]
    simp only [TestFunction.smulLeftCLM_apply, Complex.real_smul]
    ring

/-! ### The localized Fourier transform of the product -/

/-- The product `φ² S T` paired with a complex test function `f`:
`∫ S (φ e_η) T (f φ e_(-η)) dη`. -/
theorem complexPairing_cutoffProduct {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    (f : 𝓓(Ω, ℂ)) :
    (S.cutoffProduct T φ h).complexPairing f = ∫ η, S.localFourier φ η *
      T.localFourier (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff f) (-η) := by
  set f₁ := postcompCLM (𝕜 := ℝ) reCLM f
  set f₂ := postcompCLM (𝕜 := ℝ) imCLM f
  rw [complexPairing_apply, cutoffProduct_apply, cutoffProduct_apply, ← integral_const_mul,
    ← integral_add (h.integrable_localFourier_mul_localFourier
      (tsupport_smulLeftCLM_subset_right f₁.contDiff φ))
      ((h.integrable_localFourier_mul_localFourier
      (tsupport_smulLeftCLM_subset_right f₂.contDiff φ)).const_mul I)]
  congr 1
  ext η
  rw [mul_left_comm I, ← mul_add, ← localFourier_smul_cutoff, ← localFourier_add_cutoff]
  congr 2
  ext x
  simp only [_root_.add_apply, _root_.smul_apply, TestFunction.smulLeftCLM_apply,
    bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', f₁, f₂, postcompCLM_apply,
    Function.comp_apply, reCLM_apply, imCLM_apply, Complex.real_smul, smul_eq_mul]
  conv_rhs => rw [← re_add_im (f x)]
  ring

/-- **The localized Fourier transform of the product is a convolution.** For a cutoff `χ`, the
Fourier transform of `χ φ² S T` is the convolution of the Fourier transforms of `φ S` and `χ φ T`:

`(χ φ² S T)^(ζ) = ∫ S (φ e_η) T (χ φ e_(ζ - η)) dη`. -/
theorem localFourier_cutoffProduct {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    (χ : 𝓓(Ω, ℂ)) (ζ : E) :
    (S.cutoffProduct T φ h).localFourier χ ζ = ∫ η, S.localFourier φ η *
      T.localFourier (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff χ) (ζ - η) := by
  rw [localFourier_def, complexPairing_cutoffProduct]
  congr 1
  ext η
  congr 1
  rw [localFourier_def]
  refine (localFourier_eq T _ fun x ↦ ?_).symm
  simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
    TauCeti.fourierAtom_eq_fourierChar]
  rw [show -⟪x, ζ - η⟫ = -⟪x, ζ⟫ + -⟪x, -η⟫ by rw [inner_sub_right, inner_neg_right]; ring,
    AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/-! ### The wave front set of the product -/

/-- The product `φ² S T` is microlocally smooth at `(x, ζ)` whenever `ζ ∉ Γ₁ + Γ₂`, for closed cones
`Γ₁ ∋ 0` and `Γ₂ ∋ 0` without opposite nonzero vectors containing the frequencies of the wave front
sets of `S` and `T` over the support of `φ`. -/
private theorem isMicrolocallySmoothAt_cutoffProduct_of_notMem_add {φ : 𝓓(Ω, ℂ)}
    (h : NoOppositeCovectorsOn S T (tsupport φ)) {Γ₁ Γ₂ : Set E} (h₁ : IsClosed Γ₁)
    (h₂ : IsClosed Γ₂) (h0₁ : (0 : E) ∈ Γ₁) (h0₂ : (0 : E) ∈ Γ₂)
    (hc₁ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₁, t • ξ ∈ Γ₁) (hc₂ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₂, t • ξ ∈ Γ₂)
    (hopp : ∀ ξ ∈ Γ₁, -ξ ∈ Γ₂ → ξ = 0)
    (hS : ∀ x ∈ tsupport φ, ∀ ξ, (x, ξ) ∈ S.waveFrontSet → ξ ∈ Γ₁)
    (hT : ∀ x ∈ tsupport φ, ∀ ξ, (x, ξ) ∈ T.waveFrontSet → ξ ∈ Γ₂) {x ζ : E} (hx : x ∈ Ω)
    (hζ : ζ ∉ Γ₁ + Γ₂) : (S.cutoffProduct T φ h).IsMicrolocallySmoothAt x ζ := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hsub₁, hsub₂, hcU₁, hcU₂, Γ, hΓ, hζΓ, hΓc, c, hc, hgeom⟩ :=
    TauCeti.exists_cones_of_notMem_add h₁ h₂ h0₁ h0₂ hc₁ hc₂ hopp hζ
  -- A cutoff at `x`, and the localized Fourier transforms of `φ S` and of `χ φ T`.
  obtain ⟨χ, -, hχx⟩ := exists_tsupport_subset_apply_eq (n := ⊤) (Ω.isOpen.mem_nhds hx)
    subset_rfl (1 : ℂ)
  set ψ := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff χ
  have hψ : tsupport ψ ⊆ tsupport φ := by
    simp only [ψ, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']
    exact tsupport_mul_subset_right
  obtain ⟨A, kS, hA⟩ := exists_norm_localFourier_le S φ
  obtain ⟨B, kT, hB⟩ := exists_norm_localFourier_le T ψ
  have hA0 : 0 ≤ A := by simpa using (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := by simpa using (norm_nonneg _).trans (hB 0)
  have hpow {k k' : ℕ} (hk : k ≤ k') (η : E) : (1 + ‖η‖) ^ k ≤ (1 + ‖η‖) ^ k' :=
    pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg η)) hk
  -- They decay off `U₁` and `U₂`, where there is no wave front set.
  have hdS : Disjoint (tsupport φ ×ˢ U₁ᶜ) S.waveFrontSet := disjoint_left.2 fun p hp hwf ↦
    hp.2 (hsub₁ ⟨hS p.1 hp.1 p.2 hwf, (mem_waveFrontSet_iff.1 hwf).2.1⟩)
  have hdT : Disjoint (tsupport ψ ×ˢ U₂ᶜ) T.waveFrontSet := disjoint_left.2 fun p hp hwf ↦
    hp.2 (hsub₂ ⟨hT p.1 (hψ hp.1) p.2 hwf, (mem_waveFrontSet_iff.1 hwf).2.1⟩)
  refine isMicrolocallySmoothAt_iff.2 ⟨χ, by simp [hχx], Γ, hΓ, hζΓ, hΓc, fun M ↦ ?_⟩
  simp_rw [localFourier_cutoffProduct]
  exact TauCeti.exists_one_add_norm_pow_mul_norm_integral_mul_le (k := max kS kT) hA0 hB0
    (fun η ↦ (hA η).trans (mul_le_mul_of_nonneg_left (hpow (le_max_left _ _) η) hA0))
    (fun θ ↦ (hB θ).trans (mul_le_mul_of_nonneg_left (hpow (le_max_right _ _) θ) hB0))
    (fun N ↦ exists_forall_one_add_norm_pow_mul_norm_localFourier_le_of_disjoint
      hU₁.isClosed_compl hcU₁ hdS N)
    (fun N ↦ exists_forall_one_add_norm_pow_mul_norm_localFourier_le_of_disjoint
      hU₂.isClosed_compl hcU₂ hdT N) hc hgeom M

/-- **The wave front set of a cut-off product, for closed cones.** Let `Γ₁` and `Γ₂` be closed
sets of frequencies, closed under multiplication by positive reals and without opposite nonzero
vectors, containing the frequencies of the wave front sets of `S` and of `T` at all points of the
support of `φ`. Then the frequencies of the wave front set of `φ² S T` lie in
`(Γ₁ ∪ {0}) + (Γ₂ ∪ {0})`, that is, in `Γ₁`, in `Γ₂` or in `Γ₁ + Γ₂`. This is a cut-off analogue,
with one pair of cones over the whole support of `φ`, of the pointwise cone form in Brouder, Dang
and Hélein, Theorem 6.1; the proof follows that of Hörmander I, Theorem 8.2.10. -/
theorem waveFrontSet_cutoffProduct_subset_of_cones {φ : 𝓓(Ω, ℂ)}
    (h : NoOppositeCovectorsOn S T (tsupport φ)) {Γ₁ Γ₂ : Set E} (h₁ : IsClosed Γ₁)
    (h₂ : IsClosed Γ₂) (hc₁ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₁, t • ξ ∈ Γ₁)
    (hc₂ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₂, t • ξ ∈ Γ₂) (hopp : ∀ ξ ∈ Γ₁, -ξ ∈ Γ₂ → ξ = 0)
    (hS : ∀ x ∈ tsupport φ, ∀ ξ, (x, ξ) ∈ S.waveFrontSet → ξ ∈ Γ₁)
    (hT : ∀ x ∈ tsupport φ, ∀ ξ, (x, ξ) ∈ T.waveFrontSet → ξ ∈ Γ₂) :
    (S.cutoffProduct T φ h).waveFrontSet ⊆ tsupport φ ×ˢ (insert 0 Γ₁ + insert 0 Γ₂) := by
  rintro ⟨x, ζ⟩ hp
  obtain ⟨hx, -, hns⟩ := mem_waveFrontSet_iff.1 hp
  refine ⟨(dsupport_cutoffProduct_subset h (waveFrontSet_subset_dsupport _ hp).1).1,
    by_contra fun hζ ↦ hns ?_⟩
  -- Adjoin `0` to both cones.
  exact isMicrolocallySmoothAt_cutoffProduct_of_notMem_add h
    (insert_eq (0 : E) Γ₁ ▸ isClosed_singleton.union h₁)
    (insert_eq (0 : E) Γ₂ ▸ isClosed_singleton.union h₂) (mem_insert _ _) (mem_insert _ _)
    (TauCeti.forall_smul_mem_insert_zero hc₁) (TauCeti.forall_smul_mem_insert_zero hc₂)
    (TauCeti.forall_neg_mem_insert_zero_imp_eq_zero hopp)
    (fun x hx ξ hwf ↦ mem_insert_of_mem _ (hS x hx ξ hwf))
    (fun x hx ξ hwf ↦ mem_insert_of_mem _ (hT x hx ξ hwf)) hx hζ

/-- **The wave front set of a cut-off product.** If `S` and `T` have no opposite covectors over
the support of `φ`, the wave front set of `φ² S T` lies over the support of `φ`, with frequencies
`ξ + η` where `ξ` is `0` or a frequency of `WF(S)` over the support of `φ`, and `η` is `0` or a
frequency of `WF(T)` over the support of `φ`. The frequencies `ξ` and `η` are pooled over the
support of `φ` and may come from different points, so this is a cut-off, non-pointwise analogue of
Hörmander I, Theorem 8.2.10, proved along the lines of Hörmander's proof. -/
theorem waveFrontSet_cutoffProduct_subset {φ : 𝓓(Ω, ℂ)}
    (h : NoOppositeCovectorsOn S T (tsupport φ)) :
    (S.cutoffProduct T φ h).waveFrontSet ⊆ tsupport φ ×ˢ
      (insert 0 (Prod.snd '' (S.waveFrontSet ∩ tsupport φ ×ˢ univ)) +
        insert 0 (Prod.snd '' (T.waveFrontSet ∩ tsupport φ ×ˢ univ))) := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport.isCompact
  -- The frequencies of `WF(R)` over the support of `φ` form a cone, and those of `S` and `T` have
  -- no opposite nonzero vectors.
  have hcone (R : 𝓓'(Ω, ℂ)) : ∀ t : ℝ, 0 < t →
      ∀ ξ ∈ Prod.snd '' (R.waveFrontSet ∩ tsupport φ ×ˢ univ),
        t • ξ ∈ Prod.snd '' (R.waveFrontSet ∩ tsupport φ ×ˢ univ) := by
    rintro t ht _ ⟨⟨x, ξ⟩, ⟨hwf, hx, -⟩, rfl⟩
    exact ⟨(x, t • ξ), ⟨(smul_mem_waveFrontSet_iff ht).2 hwf, hx, mem_univ _⟩, rfl⟩
  have hopp : ∀ ξ ∈ Prod.snd '' (S.waveFrontSet ∩ tsupport φ ×ˢ univ),
      -ξ ∈ Prod.snd '' (T.waveFrontSet ∩ tsupport φ ×ˢ univ) → ξ = 0 := by
    rintro _ ⟨⟨x, ξ⟩, ⟨hwf, hx, -⟩, rfl⟩ ⟨⟨y, ξ'⟩, ⟨hwf', hy, -⟩, hξ'eq⟩
    exact (noOppositeCovectorsOn_iff.1 h x hx y hy ξ hwf (by simpa [← hξ'eq] using hwf')).elim
  have hsub := waveFrontSet_cutoffProduct_subset_of_cones h
    (isClosed_insert_zero_image_snd_waveFrontSet_inter hK φ.tsupport_subset S)
    (isClosed_insert_zero_image_snd_waveFrontSet_inter hK φ.tsupport_subset T)
    (TauCeti.forall_smul_mem_insert_zero (hcone S)) (TauCeti.forall_smul_mem_insert_zero (hcone T))
    (TauCeti.forall_neg_mem_insert_zero_imp_eq_zero hopp)
    (fun x hx ξ hwf ↦ mem_insert_of_mem _ ⟨(x, ξ), ⟨hwf, hx, mem_univ _⟩, rfl⟩)
    (fun x hx ξ hwf ↦ mem_insert_of_mem _ ⟨(x, ξ), ⟨hwf, hx, mem_univ _⟩, rfl⟩)
  simpa only [insert_idem] using hsub

/-! ### Independence of the cutoff -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `S` and `T` have no opposite covectors over the support of `φ ⊇ supp g`, then
`S (φ e_η) T (g e_(ζ - η))` decays rapidly in `η` and grows at most polynomially in `ζ`. -/
private theorem NoOppositeCovectorsOn.exists_one_add_norm_pow_mul_localFourier_sub_le
    {φ g : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ)) (hg : tsupport g ⊆ tsupport φ)
    (N : ℕ) : ∃ (r : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ ζ η : E,
      (1 + ‖η‖) ^ N * (‖S.localFourier φ η‖ * ‖T.localFourier g (ζ - η)‖) ≤ C * (1 + ‖ζ‖) ^ r := by
  -- `T (g e_(ζ - η))` is `T` applied to the modulated cutoff `(g e_ζ) e_(-η)`, whose derivatives
  -- grow polynomially in `ζ`, and the decay of
  -- `NoOppositeCovectorsOn.exists_forall_one_add_norm_pow_mul_le` is uniform over such cutoffs.
  obtain ⟨r, C, hC0, hC⟩ := h.exists_forall_one_add_norm_pow_mul_le N
  obtain ⟨A, hA0, hA⟩ := exists_forall_norm_iteratedFDeriv_bilinLeftCLM_fourierAtom_le g r
  refine ⟨r, C * A * (2 * Real.pi) ^ r, by positivity, fun ζ η ↦ ?_⟩
  set gζ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom ζ) g
  have hgζ : T.localFourier g (ζ - η) = T.localFourier gζ (-η) := by
    rw [localFourier_bilinLeftCLM_fourierAtom, sub_eq_add_neg]
  -- `(1 + 2π ‖ζ‖) ^ r ≤ (2π) ^ r (1 + ‖ζ‖) ^ r`, since `2π ≥ 1`.
  have hpi : (1 + 2 * Real.pi * ‖ζ‖) ^ r ≤ (2 * Real.pi) ^ r * (1 + ‖ζ‖) ^ r := by
    rw [← mul_pow]
    gcongr
    nlinarith [Real.two_le_pi, norm_nonneg ζ]
  rw [hgζ]
  calc (1 + ‖η‖) ^ N * (‖S.localFourier φ η‖ * ‖T.localFourier gζ (-η)‖)
      ≤ C * (A * (1 + 2 * Real.pi * ‖ζ‖) ^ r) :=
        hC gζ ((tsupport_mul_subset_left (f := (g : E → ℂ))).trans hg) _ (hA ζ) η
    _ ≤ C * (A * ((2 * Real.pi) ^ r * (1 + ‖ζ‖) ^ r)) := by gcongr
    _ = C * A * (2 * Real.pi) ^ r * (1 + ‖ζ‖) ^ r := by ring

/-- The integrand of `NoOppositeCovectorsOn.integral_localFourier_mul_localFourier_neg_eq`, as a
function of `(ζ, η)`, is integrable for every Schwartz function `b`. -/
private theorem NoOppositeCovectorsOn.integrable_mul_localFourier_mul_localFourier
    {φ g : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ)) (hg : tsupport g ⊆ tsupport φ)
    (b : 𝓢(E, ℂ)) :
    Integrable (fun p : E × E ↦
      b p.1 * (S.localFourier φ p.2 * T.localFourier g (p.1 - p.2))) (volume.prod volume) := by
  -- The decay of the Schwartz function `b` in `ζ` beats the polynomial growth of
  -- `S (φ e_η) T (g e_(ζ - η))` in `ζ`, which decays rapidly in `η`.
  set d := finrank ℝ E + 1
  obtain ⟨r, C, hC0, hC⟩ := h.exists_one_add_norm_pow_mul_localFourier_sub_le hg d
  set M := 2 ^ (r + d) * (Finset.Iic (r + d, 0)).sup
    (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) b
  have hM (ζ : E) : (1 + ‖ζ‖) ^ (r + d) * ‖b ζ‖ ≤ M := by
    simpa using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (r + d, 0)) le_rfl
      le_rfl b ζ
  have hint : Integrable (fun η : E ↦ ((1 + ‖η‖) ^ d)⁻¹) := by
    refine (integrable_one_add_norm (E := E) (r := d) (by simp [d])).congr
      (ae_of_all _ fun η ↦ ?_)
    dsimp only
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hcont : Continuous (fun p : E × E ↦
      b p.1 * (S.localFourier φ p.2 * T.localFourier g (p.1 - p.2))) :=
    (b.continuous.comp continuous_fst).mul (((S.continuous_localFourier φ).comp continuous_snd).mul
      ((T.continuous_localFourier g).comp (continuous_fst.sub continuous_snd)))
  refine ((hint.mul_prod hint).const_mul (M * C)).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun p ↦ ?_)
  obtain ⟨ζ, η⟩ := p
  have h1 : ‖S.localFourier φ η‖ * ‖T.localFourier g (ζ - η)‖ ≤
      C * (1 + ‖ζ‖) ^ r * ((1 + ‖η‖) ^ d)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), mul_comm]
    exact hC ζ η
  have h2 : ‖b ζ‖ * (1 + ‖ζ‖) ^ r ≤ M * ((1 + ‖ζ‖) ^ d)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), mul_assoc, ← pow_add, mul_comm]
    exact hM ζ
  simp only [norm_mul]
  calc ‖b ζ‖ * (‖S.localFourier φ η‖ * ‖T.localFourier g (ζ - η)‖)
      ≤ ‖b ζ‖ * (C * (1 + ‖ζ‖) ^ r * ((1 + ‖η‖) ^ d)⁻¹) := by gcongr
    _ = C * ((1 + ‖η‖) ^ d)⁻¹ * (‖b ζ‖ * (1 + ‖ζ‖) ^ r) := by ring
    _ ≤ C * ((1 + ‖η‖) ^ d)⁻¹ * (M * ((1 + ‖ζ‖) ^ d)⁻¹) := by gcongr
    _ = M * C * (((1 + ‖ζ‖) ^ d)⁻¹ * ((1 + ‖η‖) ^ d)⁻¹) := by ring

/-- **Moving a multiplier across the product integral.** If `S` and `T` have no opposite covectors
over the support of `φ`, `g` is a cutoff supported in the support of `φ`, and `a` is a Schwartz
function, then

`∫ S (a φ e_η) T (g e_(-η)) dη = ∫ S (φ e_η) T (a g e_(-η)) dη`.

Both sides are the pairing of `φ S` with `g T` multiplied by `a`, formally `∫ a φ g S T`. -/
theorem NoOppositeCovectorsOn.integral_localFourier_mul_localFourier_neg_eq
    {φ g φa ga : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    (hg : tsupport g ⊆ tsupport φ) (a : 𝓢(E, ℂ)) (hφa : ∀ x, φa x = a x * φ x)
    (hga : ∀ x, ga x = a x * g x) :
    ∫ η, S.localFourier φa η * T.localFourier g (-η) =
      ∫ η, S.localFourier φ η * T.localFourier ga (-η) := by
  -- Write `a` as the Fourier integral of `𝓕⁻ a` (`integral_fourierInv_mul_localFourier_add`) on
  -- either side and exchange the order of integration.
  set F : E × E → ℂ := fun p ↦
    𝓕⁻ a p.1 * (S.localFourier φ p.2 * T.localFourier g (p.1 - p.2))
  have hF : Integrable F (volume.prod volume) :=
    h.integrable_mul_localFourier_mul_localFourier hg (𝓕⁻ a)
  have hG : Integrable (fun p : E × E ↦ F (p.1, p.1 + p.2)) (volume.prod volume) :=
    ((measurePreserving_prod_add volume volume).integrable_comp hF.aestronglyMeasurable).2 hF
  -- Integrating `F` first in `ζ` gives the right side.
  have hR : ∫ η, S.localFourier φ η * T.localFourier ga (-η) = ∫ η, ∫ ζ, F (ζ, η) := by
    refine integral_congr_ae (ae_of_all _ fun η ↦ ?_)
    dsimp only
    rw [← integral_fourierInv_mul_localFourier_add T g a hga (-η), ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
    simp only [F, sub_eq_neg_add]
    ring
  -- Integrating `F` first in `η`, after the shift `η = ζ + ν`, gives the left side.
  have hL : ∫ η, S.localFourier φa η * T.localFourier g (-η) = ∫ ζ, ∫ ν, F (ζ, ζ + ν) := by
    rw [integral_integral_swap hG]
    refine integral_congr_ae (ae_of_all _ fun ν ↦ ?_)
    dsimp only
    rw [← integral_fourierInv_mul_localFourier_add S φ a hφa ν, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
    simp only [F, sub_add_cancel_left, add_comm ν ζ]
    ring
  rw [hL, hR, ← integral_integral_swap (f := fun ζ η ↦ F (ζ, η)) hF]
  refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
  exact integral_add_left_eq_self (μ := volume) (fun η ↦ F (ζ, η)) ζ

/-- **The product `φ² S T` where `φ = 1`.** If `φ` is one on the support of a real cutoff `χ`, and
`χ` is one on the support of `ψ`, then `(φ² S T) ψ = ∫ S (χ e_η) T (ψ e_(-η)) dη`. The right side
does not involve `φ`. -/
theorem cutoffProduct_apply_eq_integral {φ : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    {ψ χ : 𝓓(Ω, ℝ)} (hφχ : ∀ x ∈ tsupport χ, φ x = 1) (hχψ : ∀ x ∈ tsupport ψ, χ x = 1) :
    S.cutoffProduct T φ h ψ = ∫ η, S.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM χ) η *
      T.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM ψ) (-η) := by
  have hψχ : tsupport ψ ⊆ tsupport χ := fun x hx ↦
    subset_tsupport _ (by simp [hχψ x hx] : χ x ≠ 0)
  rw [cutoffProduct_apply]
  refine (h.integral_localFourier_mul_localFourier_neg_eq ?_
    (toSchwartzMapCLM ℂ (postcompCLM (𝕜 := ℝ) ofRealCLM χ)) (fun x ↦ ?_) (fun x ↦ ?_)).symm
  · refine (tsupport_comp_subset ofReal_zero _).trans
      (hψχ.trans fun x hx ↦ subset_tsupport _ ?_)
    simp [hφχ x hx]
  · by_cases hx : x ∈ tsupport χ
    · simp [hφχ x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · by_cases hx : x ∈ tsupport ψ
    · simp [hχψ x hx, hφχ x (hψχ hx), TestFunction.smulLeftCLM_apply]
    · simp [image_eq_zero_of_notMem_tsupport hx, TestFunction.smulLeftCLM_apply]

/-- **Independence of the cutoff.** The products `φ² S T` and `φ'² S T` agree on a test function
`ψ` if both cutoffs are one near the support of `ψ`. -/
theorem cutoffProduct_congr {φ φ' : 𝓓(Ω, ℂ)} (h : NoOppositeCovectorsOn S T (tsupport φ))
    (h' : NoOppositeCovectorsOn S T (tsupport φ')) {ψ : 𝓓(Ω, ℝ)}
    (hφ : (φ : E → ℂ) =ᶠ[𝓝ˢ (tsupport ψ)] 1) (hφ' : (φ' : E → ℂ) =ᶠ[𝓝ˢ (tsupport ψ)] 1) :
    S.cutoffProduct T φ h ψ = S.cutoffProduct T φ' h' ψ := by
  obtain ⟨U, hU, hψU, hUφ⟩ := mem_nhdsSet_iff_exists.1 (hφ.and hφ')
  obtain ⟨χ, -, hχψ, hχU⟩ := exists_cutoff_tsupport_subset ψ.hasCompactSupport.isCompact
    (hU.inter Ω.isOpen) (subset_inter hψU ψ.tsupport_subset) inter_subset_right
  rw [cutoffProduct_apply_eq_integral h (fun x hx ↦ (hUφ (hχU hx).1).1) fun x hx ↦
      hχψ.self_of_nhdsSet x hx,
    cutoffProduct_apply_eq_integral h' (fun x hx ↦ (hUφ (hχU hx).1).2) fun x hx ↦
      hχψ.self_of_nhdsSet x hx]

/-! ### The product -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Near a point satisfying Hörmander's condition there is a cutoff equal to one on an open
neighbourhood of the point, over whose support `S` and `T` have no opposite covectors. -/
private theorem exists_eqOn_one_noOppositeCovectorsOn {x : E} (hx : x ∈ Ω)
    (h : NoOppositeCovectorsOn S T {x}) :
    ∃ (U : Opens E) (φ : 𝓓(Ω, ℂ)), x ∈ U ∧ U ≤ Ω ∧ EqOn φ 1 U ∧
      NoOppositeCovectorsOn S T (tsupport φ) := by
  obtain ⟨W, hW, hWc⟩ := exists_mem_nhds_noOppositeCovectorsOn hx
    (noOppositeCovectorsOn_singleton_iff.1 h)
  obtain ⟨φ, V, hV, hxV, hφV, hφW⟩ := exists_eqOn_one_tsupport_subset (𝕜 := ℂ) hW hx
  exact ⟨⟨V ∩ Ω, hV.inter Ω.isOpen⟩, φ, ⟨hxV, hx⟩, fun y hy ↦ hy.2, hφV.mono inter_subset_left,
    hWc.mono hφW⟩

/-- The cutoff products `φ² S T` glue to a distribution which agrees with `φ² S T` on the test
functions `ψ` such that `φ = 1` near the support of `ψ`. -/
private theorem exists_forall_apply_eq_cutoffProduct (h : ∀ x, NoOppositeCovectorsOn S T {x}) :
    ∃ P : 𝓓'(Ω, ℂ), ∀ ⦃φ : 𝓓(Ω, ℂ)⦄ (hφ : NoOppositeCovectorsOn S T (tsupport φ))
      ⦃ψ : 𝓓(Ω, ℝ)⦄, (φ : E → ℂ) =ᶠ[𝓝ˢ (tsupport ψ)] 1 → P ψ = S.cutoffProduct T φ hφ ψ := by
  choose U φ hxU hUΩ hφ1 hφc using fun x : Ω ↦
    exists_eqOn_one_noOppositeCovectorsOn x.property (h x)
  have hcov : ⨆ x, U x = Ω := le_antisymm (iSup_le hUΩ) fun y hy ↦ by
    rw [← SetLike.mem_coe, Opens.coe_iSup, mem_iUnion]
    exact ⟨⟨y, hy⟩, hxU _⟩
  -- The local products `φ_x² S T` agree on overlaps by independence of the cutoff.
  obtain ⟨P, hP, -⟩ := existsUnique_gluing (T := fun x ↦
    (ContinuousLinearMap.toUniformConvergenceCLM _ ℂ _).symm (S.cutoffProduct T (φ x) (hφc x)) ∘L
      (monoCLM ℝ : 𝓓(U x, ℝ) →L[ℝ] 𝓓(Ω, ℝ))) hcov fun x y ψ ↦ by
    have hmono (z : Ω) (hz : U x ⊓ U y ≤ U z) :
        (monoCLM ℝ (monoCLM ℝ ψ : 𝓓(U z, ℝ)) : 𝓓(Ω, ℝ)) = monoCLM ℝ ψ :=
      TestFunction.ext fun t ↦ by simp [hz, hUΩ z, hz.trans (hUΩ z)]
    have hsupp : tsupport (monoCLM ℝ ψ : 𝓓(Ω, ℝ)) ⊆ (U x : Set E) ∩ U y := by
      simpa [(inf_le_left : U x ⊓ U y ≤ U x).trans (hUΩ x)] using ψ.tsupport_subset
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toUniformConvergenceCLM_symm_apply,
      ContinuousLinearMap.toUniformConvergenceCLM_symm_apply, hmono x inf_le_left,
      hmono y inf_le_right]
    exact cutoffProduct_congr _ _
      ((hφ1 x).eventuallyEq_of_mem ((U x).isOpen.mem_nhdsSet.2 (hsupp.trans inter_subset_left)))
      ((hφ1 y).eventuallyEq_of_mem ((U y).isOpen.mem_nhdsSet.2 (hsupp.trans inter_subset_right)))
  set P' : 𝓓'(Ω, ℂ) := ContinuousLinearMap.toUniformConvergenceCLM _ ℂ _ P
  have hPx (x : Ω) (ψ : 𝓓(Ω, ℝ)) (hψ : tsupport ψ ⊆ U x) :
      P' ψ = S.cutoffProduct T (φ x) (hφc x) ψ := by
    obtain ⟨ψ', rfl⟩ := exists_monoCLM_eq_of_tsupport_subset (hUΩ x) hψ
    simpa [P'] using DFunLike.congr_fun (hP x) ψ'
  -- On an open set where `φ = 1`, the glued distribution is `φ² S T` near every point.
  refine ⟨P', fun φ' hφ' ψ hφ'ψ ↦ ?_⟩
  obtain ⟨V, hV, hψV, hφ'V⟩ := mem_nhdsSet_iff_exists.1 hφ'ψ
  have hvan : IsVanishingOn (P' - S.cutoffProduct T φ' hφ') V :=
    isVanishingOn_of_forall_inter _ (fun x ↦ (U x).isOpen) hxU hV fun x χ hχ ↦ by
      have hm : (U x : Set E) ∩ V ∈ 𝓝ˢ (tsupport χ) := ((U x).isOpen.inter hV).mem_nhdsSet.2 hχ
      rw [sub_apply, hPx x χ (hχ.trans inter_subset_left),
        cutoffProduct_congr (hφc x) hφ' (((hφ1 x).mono inter_subset_left).eventuallyEq_of_mem hm)
          (Filter.mem_of_superset hm fun y hy ↦ hφ'V hy.2), sub_self]
  rw [← sub_eq_zero, ← sub_apply]
  exact hvan ψ hψV

/-- **The product of distributions** (Hörmander I, Theorem 8.2.10). If at every point `x` no
covector `(x, ξ)` of the wave front set of `S` is opposite to a covector `(x, -ξ)` of the wave
front set of `T`, the product `S T` is the distribution which agrees with the cut-off product
`φ² S T` on the test functions `ψ` such that `φ = 1` near the support of `ψ`, for every cutoff `φ`
over whose support `S` and `T` have no opposite covectors
(`Distribution.product_apply_of_eventuallyEq_one`). It is
characterized by this property (`Distribution.eq_product_iff`), and it extends multiplication by
smooth functions in either factor. -/
def product (S T : 𝓓'(Ω, ℂ)) (h : ∀ x, NoOppositeCovectorsOn S T {x}) : 𝓓'(Ω, ℂ) :=
  (exists_forall_apply_eq_cutoffProduct h).choose

/-- **The product agrees with the cut-off products.** On a test function `ψ` such that `φ = 1` near
the support of `ψ`, the product `S T` is `(φ² S T) ψ`. -/
theorem product_apply_of_eventuallyEq_one (h : ∀ x, NoOppositeCovectorsOn S T {x})
    {φ : 𝓓(Ω, ℂ)} (hφ : NoOppositeCovectorsOn S T (tsupport φ)) {ψ : 𝓓(Ω, ℝ)}
    (hφψ : (φ : E → ℂ) =ᶠ[𝓝ˢ (tsupport ψ)] 1) :
    S.product T h ψ = S.cutoffProduct T φ hφ ψ :=
  (exists_forall_apply_eq_cutoffProduct h).choose_spec hφ hφψ

/-- **Characterization of the product.** A distribution `P` is the product `S T` exactly when every
point `x ∈ Ω` has an open neighbourhood `U` and a cutoff `φ` equal to one on `U`, over whose support
`S` and `T` have no opposite covectors, such that `P` agrees with `φ² S T` on the test functions
supported in `U`. -/
theorem eq_product_iff (h : ∀ x, NoOppositeCovectorsOn S T {x}) {P : 𝓓'(Ω, ℂ)} :
    P = S.product T h ↔ ∀ x ∈ Ω, ∃ (φ : 𝓓(Ω, ℂ)) (hφ : NoOppositeCovectorsOn S T (tsupport φ))
      (U : Set E), IsOpen U ∧ x ∈ U ∧ EqOn φ 1 U ∧
        ∀ ψ : 𝓓(Ω, ℝ), tsupport ψ ⊆ U → P ψ = S.cutoffProduct T φ hφ ψ := by
  refine ⟨fun hP x hx ↦ ?_, fun hP ↦ ?_⟩
  · obtain ⟨U, φ, hxU, -, hφU, hφ⟩ := exists_eqOn_one_noOppositeCovectorsOn hx (h x)
    exact ⟨φ, hφ, U, U.isOpen, hxU, hφU, fun ψ hψ ↦ hP ▸ product_apply_of_eventuallyEq_one h hφ
      (hφU.eventuallyEq_of_mem (U.isOpen.mem_nhdsSet.2 hψ))⟩
  · have hzero := AddMonoidHom.eq_zero_of_locally_vanishing
      (AddMonoidHom.ofClass P - AddMonoidHom.ofClass (S.product T h)) fun x hx ↦ by
        obtain ⟨φ, hφ, U, hU, hxU, hφU, hPU⟩ := hP x hx
        refine ⟨U, hU, hxU, fun ψ hψ ↦ ?_⟩
        simp [hPU ψ hψ, product_apply_of_eventuallyEq_one h hφ
          (hφU.eventuallyEq_of_mem (hU.mem_nhdsSet.2 hψ))]
    ext ψ
    simpa [sub_eq_zero] using DFunLike.congr_fun hzero ψ

/-- A distribution `P` is the product `S T` if every cutoff `φ` over whose support the pairs
`(S₁, T₁)` and `(S₂, T₂)` have no opposite covectors is a cutoff for `S` and `T` such that `P`
agrees with `φ² S T` on the test functions `ψ` with `φ = 1` near the support of `ψ`. -/
private theorem eq_product_of_forall_cutoffProduct {S₁ T₁ S₂ T₂ : 𝓓'(Ω, ℂ)}
    (h₁ : ∀ x, NoOppositeCovectorsOn S₁ T₁ {x}) (h₂ : ∀ x, NoOppositeCovectorsOn S₂ T₂ {x})
    (h : ∀ x, NoOppositeCovectorsOn S T {x}) {P : 𝓓'(Ω, ℂ)}
    (hP : ∀ ⦃φ : 𝓓(Ω, ℂ)⦄, NoOppositeCovectorsOn S₁ T₁ (tsupport φ) →
      NoOppositeCovectorsOn S₂ T₂ (tsupport φ) → ∃ hφ : NoOppositeCovectorsOn S T (tsupport φ),
        ∀ ⦃ψ : 𝓓(Ω, ℝ)⦄, (φ : E → ℂ) =ᶠ[𝓝ˢ (tsupport ψ)] 1 → P ψ = S.cutoffProduct T φ hφ ψ) :
    P = S.product T h := by
  refine (eq_product_iff h).2 fun x hx ↦ ?_
  obtain ⟨W₁, hW₁, hWc₁⟩ := exists_mem_nhds_noOppositeCovectorsOn hx
    (noOppositeCovectorsOn_singleton_iff.1 (h₁ x))
  obtain ⟨W₂, hW₂, hWc₂⟩ := exists_mem_nhds_noOppositeCovectorsOn hx
    (noOppositeCovectorsOn_singleton_iff.1 (h₂ x))
  obtain ⟨φ, U, hU, hxU, hφU, hφW⟩ := exists_eqOn_one_tsupport_subset (𝕜 := ℂ)
    (inter_mem hW₁ hW₂) hx
  obtain ⟨hφ, hPφ⟩ := hP (hWc₁.mono (hφW.trans inter_subset_left))
    (hWc₂.mono (hφW.trans inter_subset_right))
  exact ⟨φ, hφ, U, hU, hxU, hφU, fun ψ hψ ↦ hPφ (hφU.eventuallyEq_of_mem (hU.mem_nhdsSet.2 hψ))⟩

/-- The product is additive in the first factor. -/
theorem product_add_left (h : ∀ x, NoOppositeCovectorsOn S T {x})
    (h' : ∀ x, NoOppositeCovectorsOn S' T {x}) :
    (S + S').product T (fun x ↦ (h x).add_left (h' x)) = S.product T h + S'.product T h' := by
  refine (eq_product_of_forall_cutoffProduct h h' _ fun φ hφ hφ' ↦
    ⟨hφ.add_left hφ', fun ψ hφψ ↦ ?_⟩).symm
  rw [add_apply, product_apply_of_eventuallyEq_one h hφ hφψ,
    product_apply_of_eventuallyEq_one h' hφ' hφψ, cutoffProduct_add_left hφ hφ', add_apply]

/-- The product is additive in the second factor. -/
theorem product_add_right (h : ∀ x, NoOppositeCovectorsOn S T {x})
    (h' : ∀ x, NoOppositeCovectorsOn S T' {x}) :
    S.product (T + T') (fun x ↦ (h x).add_right (h' x)) = S.product T h + S.product T' h' := by
  refine (eq_product_of_forall_cutoffProduct h h' _ fun φ hφ hφ' ↦
    ⟨hφ.add_right hφ', fun ψ hφψ ↦ ?_⟩).symm
  rw [add_apply, product_apply_of_eventuallyEq_one h hφ hφψ,
    product_apply_of_eventuallyEq_one h' hφ' hφψ, cutoffProduct_add_right hφ hφ', add_apply]

/-- The product is complex-linear in the first factor. -/
theorem product_smul_left (h : ∀ x, NoOppositeCovectorsOn S T {x}) (c : ℂ) :
    (c • S).product T (fun x ↦ (h x).smul_left c) = c • S.product T h := by
  refine (eq_product_of_forall_cutoffProduct h h _ fun φ hφ _ ↦
    ⟨hφ.smul_left c, fun ψ hφψ ↦ ?_⟩).symm
  rw [smul_apply, product_apply_of_eventuallyEq_one h hφ hφψ, cutoffProduct_smul_left hφ c,
    smul_apply]

/-- The product is complex-linear in the second factor. -/
theorem product_smul_right (h : ∀ x, NoOppositeCovectorsOn S T {x}) (c : ℂ) :
    S.product (c • T) (fun x ↦ (h x).smul_right c) = c • S.product T h := by
  refine (eq_product_of_forall_cutoffProduct h h _ fun φ hφ _ ↦
    ⟨hφ.smul_right c, fun ψ hφψ ↦ ?_⟩).symm
  rw [smul_apply, product_apply_of_eventuallyEq_one h hφ hφψ, cutoffProduct_smul_right hφ c,
    smul_apply]

/-- If the products `φ² S T` vanish on `U ∩ W` for every cutoff `φ` equal to one on an open set
`U`, then the product `S T` vanishes on `W`. -/
private theorem isVanishingOn_product (h : ∀ x, NoOppositeCovectorsOn S T {x}) {W : Set E}
    (hW : IsOpen W)
    (hloc : ∀ ⦃φ : 𝓓(Ω, ℂ)⦄ (hφ : NoOppositeCovectorsOn S T (tsupport φ)) ⦃U : Set E⦄,
      IsOpen U → EqOn φ 1 U → IsVanishingOn (S.cutoffProduct T φ hφ) (U ∩ W)) :
    IsVanishingOn (S.product T h) W := by
  choose U φ hxU _ hφ1 hφc using fun x : Ω ↦
    exists_eqOn_one_noOppositeCovectorsOn x.property (h x)
  refine isVanishingOn_of_forall_inter _ (fun x ↦ (U x).isOpen) hxU hW fun x χ hχ ↦ ?_
  rw [product_apply_of_eventuallyEq_one h (hφc x) (((hφ1 x).mono
    inter_subset_left).eventuallyEq_of_mem (((U x).isOpen.inter hW).mem_nhdsSet.2 hχ))]
  exact hloc (hφc x) (U x).isOpen (hφ1 x) χ hχ

/-- **The support of the product.** The product `S T` is supported in the intersection of the
supports of `S` and `T`. -/
theorem dsupport_product_subset (h : ∀ x, NoOppositeCovectorsOn S T {x}) :
    dsupport (S.product T h) ⊆ dsupport S ∩ dsupport T := by
  -- Off the support of `S`, `φ² S T` is `∫ S (χ e_η) T (ψ e_(-η)) dη` with `χ` supported off the
  -- support of `S`, where `S (χ e_η) = 0`.
  have hS : IsVanishingOn (S.product T h) (dsupport S)ᶜ :=
    isVanishingOn_product h isClosed_dsupport.isOpen_compl fun φ hφ U hU hφU ψ hψ ↦ by
      obtain ⟨χ, -, hχψ, hχ⟩ := exists_cutoff_tsupport_subset ψ.hasCompactSupport.isCompact
        ((hU.inter isClosed_dsupport.isOpen_compl).inter Ω.isOpen)
        (subset_inter hψ ψ.tsupport_subset) inter_subset_right
      have hdis : Disjoint (tsupport (postcompCLM (𝕜 := ℝ) ofRealCLM χ)) (dsupport S) :=
        disjoint_compl_left.mono_left ((tsupport_comp_subset ofReal_zero _).trans
          (hχ.trans (inter_subset_left.trans inter_subset_right)))
      rw [cutoffProduct_apply_eq_integral hφ (fun x hx ↦ hφU (hχ hx).1.1) fun x hx ↦
        hχψ.self_of_nhdsSet x hx]
      simp [localFourier_eq_zero_of_disjoint_dsupport hdis]
  have hT : IsVanishingOn (S.product T h) (dsupport T)ᶜ :=
    isVanishingOn_product h isClosed_dsupport.isOpen_compl fun φ hφ U _ _ ψ hψ ↦
      map_eq_zero_of_disjoint_dsupport _ ((disjoint_compl_left.mono_left
        (hψ.trans inter_subset_right)).mono_right ((dsupport_cutoffProduct_subset hφ).trans
          inter_subset_right))
  refine subset_inter ?_ ?_
  · simpa using (hS.disjoint_dsupport isClosed_dsupport.isOpen_compl).subset_compl_left
  · simpa using (hT.disjoint_dsupport isClosed_dsupport.isOpen_compl).subset_compl_left

/-- **The product with a smooth function, on the right.** If `T` coincides with a function `g`
smooth on an open set `U`, then on the test functions `ψ` supported in `U` the product `S T` is
`S (ψ g)`. -/
theorem product_apply_of_apply_eq_integral_right (h : ∀ x, NoOppositeCovectorsOn S T {x})
    {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    (hT : ∀ χ : 𝓓(Ω, ℝ), tsupport χ ⊆ U → T χ = ∫ y, χ y • g y) {ψ : 𝓓(Ω, ℝ)}
    (hψU : tsupport ψ ⊆ U) {χ : 𝓓(Ω, ℂ)} (hχ : ∀ x, χ x = ψ x * g x) :
    S.product T h ψ = S.complexPairing χ := by
  obtain ⟨φ, hφ1, hφU⟩ := exists_complex_cutoff_tsupport_subset ψ.hasCompactSupport.isCompact
    (hU.inter Ω.isOpen) (subset_inter hψU ψ.tsupport_subset) inter_subset_right
  have hφ : NoOppositeCovectorsOn S T (tsupport φ) :=
    noOppositeCovectorsOn_of_apply_eq_integral_right hU hg hT (hφU.trans inter_subset_left)
  rw [product_apply_of_eventuallyEq_one h hφ hφ1,
    cutoffProduct_apply_of_apply_eq_integral_right hU hg hT (hφU.trans inter_subset_left) hφ ψ
      fun x ↦ ?_]
  by_cases hx : x ∈ tsupport ψ
  · simp [hχ, hφ1.self_of_nhdsSet x hx]
  · simp [hχ, image_eq_zero_of_notMem_tsupport hx]

/-- **The product with a smooth function, on the left.** If `S` coincides with a function `g`
smooth on an open set `U`, then on the test functions `ψ` supported in `U` the product `S T` is
`T (ψ g)`. -/
theorem product_apply_of_apply_eq_integral_left (h : ∀ x, NoOppositeCovectorsOn S T {x})
    {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    (hS : ∀ χ : 𝓓(Ω, ℝ), tsupport χ ⊆ U → S χ = ∫ y, χ y • g y) {ψ : 𝓓(Ω, ℝ)}
    (hψU : tsupport ψ ⊆ U) {χ : 𝓓(Ω, ℂ)} (hχ : ∀ x, χ x = ψ x * g x) :
    S.product T h ψ = T.complexPairing χ := by
  obtain ⟨φ, hφ1, hφU⟩ := exists_complex_cutoff_tsupport_subset ψ.hasCompactSupport.isCompact
    (hU.inter Ω.isOpen) (subset_inter hψU ψ.tsupport_subset) inter_subset_right
  have hφ : NoOppositeCovectorsOn S T (tsupport φ) :=
    noOppositeCovectorsOn_of_apply_eq_integral_left hU hg hS (hφU.trans inter_subset_left)
  rw [product_apply_of_eventuallyEq_one h hφ hφ1,
    cutoffProduct_apply_of_apply_eq_integral_left hU hg hS (hφU.trans inter_subset_left) hφ ψ
      fun x ↦ ?_]
  by_cases hx : x ∈ tsupport ψ
  · simp [hχ, hφ1.self_of_nhdsSet x hx]
  · simp [hχ, image_eq_zero_of_notMem_tsupport hx]

end Distribution
