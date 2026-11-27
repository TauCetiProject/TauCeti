/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
public import TauCeti.Analysis.Fredholm.Spectral.Neg
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The spectral flow of the negated path on a common domain

Let `ι : D →L H` be a compact operator from a Banach space into a Hilbert space, and let
`A : ℝ → (D →L H)` be a continuous path of operators symmetric through `ι`,
`⟪A t x, ι y⟫ = ⟪ι x, A t y⟫`, each with some invertible shift `c₀ ι - A t`. This file computes
the spectral flow `TauCeti.domainSpectralFlow ι` of the negated path `t ↦ -A t`:

`SF(-A; a, b) = dim ker A(b) - dim ker A(a) - SF(A; a, b)`

(`TauCeti.domainSpectralFlow_neg`). When the endpoints `A a` and `A b` are injective, negating the
path negates its spectral flow (`TauCeti.domainSpectralFlow_neg_of_ker_eq_bot`). This connects the
index formulas for the two sign conventions `∂ₛ + A` and `∂ₛ - A` of the trajectory operator.

Over an interval with an admissible shift `c ≠ 0` for `-A`, the shift `-c` is admissible for `A`,
and `τ_c (-A) = -τ_{-c} A` (`ContinuousLinearMap.shiftedResolventTransform_neg`). At any invertible
shift `c ι - A` with `c ≠ 0`, `ι` maps `ker A` isomorphically onto `ker (τ_c A)`, so both have
the same finite dimension (`ContinuousLinearMap.finrank_ker_shiftedResolventTransform`). Applying
the bounded negation identity `TauCeti.spectralFlow_neg` to the shifted resolvent transforms shows
that `t ↦ dim ker A(t) - F t` is a spectral flow potential of `-A` whenever `F` is a potential of
`A` (`TauCeti.IsDomainSpectralFlowPotential.neg`).

## Main results

* `ContinuousLinearMap.finrank_ker_shiftedResolventTransform`: the kernel of `τ_c A` has the same
  dimension as the kernel of `A`.
* `TauCeti.IsDomainSpectralFlowPotential.neg`: spectral flow potentials of the negated path.
* `TauCeti.domainSpectralFlow_neg`: the spectral flow of `-A` on a common domain.
* `TauCeti.domainSpectralFlow_neg_of_ker_eq_bot`: with injective endpoints, negating the path
  negates its spectral flow.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4.
-/

public section

open Filter Set Topology

section ShiftedResolventTransform

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace ContinuousLinearMap

/-- At an invertible shift `c ι - A` with `c ≠ 0`, the kernel of the shifted resolvent transform
`τ_c A` has the same dimension over `𝕜` as the kernel of `A`, since `ι` maps `ker A`
injectively onto `ker (τ_c A)`. -/
theorem finrank_ker_shiftedResolventTransform {ι A : D →L[𝕜] H} {c : ℝ}
    (h : ((c : 𝕜) • ι - A).IsInvertible) (hc : c ≠ 0) :
    Module.finrank 𝕜 (ι.shiftedResolventTransform A c).ker = Module.finrank 𝕜 A.ker := by
  have hrange : (A.ker.map (ι : D →ₗ[𝕜] H)) =
      LinearMap.range ((ι : D →ₗ[𝕜] H) ∘ₗ A.ker.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [ker_shiftedResolventTransform h hc, hrange]
  exact LinearMap.finrank_range_of_inj
    (injective_comp_subtype_ker_of_injective_smul_sub h.injective)

end ContinuousLinearMap

end ShiftedResolventTransform

namespace TauCeti

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] {ι : D →L[𝕜] H} {A : ℝ → D →L[𝕜] H}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Spectral flow potentials of the negated path.** If `F` is a spectral flow potential of `A` on
`[a, b]`, then `t ↦ dim ker A(t) - F t` is a spectral flow potential of `-A` on `[a, b]`. -/
theorem IsDomainSpectralFlowPotential.neg (hι : IsCompactOperator ι) {a b : ℝ} {F : ℝ → ℤ}
    (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (hFp : IsDomainSpectralFlowPotential ι A a b F) :
    IsDomainSpectralFlowPotential ι (fun t ↦ -A t) a b
      fun t ↦ (Module.finrank 𝕜 (A t).ker : ℤ) - F t := by
  rw [isDomainSpectralFlowPotential_iff]
  intro s t c has hst htb hc hinv
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hinv' (u : ℝ) (hu : u ∈ Icc s t) : (((-c : ℝ) : 𝕜) • ι - A u).IsInvertible := by
    have hu' := hinv u hu
    have heq : (c : 𝕜) • ι - (-A u) = -(((-c : ℝ) : 𝕜) • ι - A u) := by
      rw [RCLike.ofReal_neg, neg_smul]
      abel
    rwa [heq, ContinuousLinearMap.isInvertible_neg_iff] at hu'
  have hc' : -c ≠ 0 := neg_ne_zero.2 hc
  obtain ⟨hτ, hsa, hF⟩ := regular_shiftedResolventTransform hι (hA.mono hsub)
    (fun u hu ↦ hsymm u (hsub hu)) hc' hinv'
  have hcongr : EqOn (fun u ↦ ι.shiftedResolventTransform (-A u) c)
      (fun u ↦ -ι.shiftedResolventTransform (A u) (-c)) (Icc s t) := fun u _ ↦ by
    dsimp only
    rw [← neg_neg c, ContinuousLinearMap.shiftedResolventTransform_neg, neg_neg]
  rw [spectralFlow_congr hcongr, spectralFlow_neg hst hτ hsa hF,
    ContinuousLinearMap.finrank_ker_shiftedResolventTransform (hinv' s ⟨le_rfl, hst⟩) hc',
    ContinuousLinearMap.finrank_ker_shiftedResolventTransform (hinv' t ⟨hst, le_rfl⟩) hc',
    ← isDomainSpectralFlowPotential_iff.1 hFp has hst htb hc' hinv']
  ring

/-- **The spectral flow of the negated path on a common domain.** For a continuous path `A` of
operators on `[a, b]`, symmetric through a compact `ι` and each with some invertible shift,

`SF(-A; a, b) = dim ker A(b) - dim ker A(a) - SF(A; a, b)`.

The correction comes from Phillips' convention, which places the eigenvalue `0` with the
nonnegative ones for both `A` and `-A`. -/
theorem domainSpectralFlow_neg (hι : IsCompactOperator ι) {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    domainSpectralFlow ι (fun t ↦ -A t) a b =
      (Module.finrank 𝕜 (A b).ker : ℤ) - Module.finrank 𝕜 (A a).ker -
        domainSpectralFlow ι A a b := by
  obtain ⟨F, hFp⟩ := exists_isDomainSpectralFlowPotential hι hA hsymm h₀
  have h₀' (t : ℝ) (ht : t ∈ Icc a b) : ∃ c₀ : 𝕜, (c₀ • ι - (-A t)).IsInvertible := by
    obtain ⟨c₀, hc₀⟩ := h₀ t ht
    have heq : (-c₀) • ι - (-A t) = -(c₀ • ι - A t) := by
      rw [neg_smul]
      abel
    exact ⟨-c₀, by rwa [heq, ContinuousLinearMap.isInvertible_neg_iff]⟩
  rw [domainSpectralFlow_eq_sub (A := fun t ↦ -A t) hι hab hA.neg h₀' (hFp.neg hι hA hsymm),
    domainSpectralFlow_eq_sub hι hab hA h₀ hFp]
  ring

/-- **Negation with injective endpoints.** For a continuous path `A` of operators on `[a, b]`,
symmetric through a compact `ι` and each with some invertible shift, whose endpoints are injective,
the spectral flow of `-A` is minus that of `A`. -/
theorem domainSpectralFlow_neg_of_ker_eq_bot (hι : IsCompactOperator ι) {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible)
    (ha : (A a).ker = ⊥) (hb : (A b).ker = ⊥) :
    domainSpectralFlow ι (fun t ↦ -A t) a b = -domainSpectralFlow ι A a b := by
  rw [domainSpectralFlow_neg hι hab hA hsymm h₀, ha, hb, finrank_bot]
  ring

end TauCeti
