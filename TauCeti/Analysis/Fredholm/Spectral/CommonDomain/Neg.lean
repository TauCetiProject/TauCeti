/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
public import TauCeti.Analysis.Fredholm.Spectral.Neg
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The spectral flow of the negated path on a common domain

Let `ι : D →L H` be a compact embedding of a Banach space `D` into a Hilbert space `H`, and `A` a
continuous path of operators `D →L H` symmetric through `ι`, each with some invertible shift. Its
spectral flow `TauCeti.domainSpectralFlow ι A a b` counts the eigenvalues of the unbounded operators
`A t` crossing `0` upwards; along `-A` they cross downwards. As for bounded paths
(`TauCeti.spectralFlow_neg`), the count places the eigenvalue `0` with the nonnegative ones, so
an eigenvalue reaching `0` at an endpoint counts for one of the two paths and not the other, and

`SF(-A; a, b) = dim ker A(b) - dim ker A(a) - SF(A; a, b)`

(`TauCeti.domainSpectralFlow_neg`). With invertible endpoints, negating the path negates its
spectral flow (`TauCeti.domainSpectralFlow_neg_of_ker_eq_bot`). This relates the two conventions
for the trajectory operator: `d/ds + A`, whose index is the spectral flow of `A`, and the
`d/ds - A` of the Floer equation, whose coefficient is the negated path.

The proof reduces to the bounded case through the shifted resolvent transforms. A shift `c` is
admissible for `-A` exactly when `-c` is admissible for `A`
(`ContinuousLinearMap.isInvertible_smul_sub_neg_iff`), and the transform of `-A` at `c` is
minus the transform of `A` at `-c` (`ContinuousLinearMap.shiftedResolventTransform_neg`), whose
kernel has the dimension of the kernel of `A`
(`ContinuousLinearMap.finrank_ker_shiftedResolventTransform`). So if `F` is a spectral flow
potential of `A`, then `t ↦ dim ker A(t) - F t` is one of `-A`
(`TauCeti.IsDomainSpectralFlowPotential.neg`).

## Main results

* `TauCeti.IsDomainSpectralFlowPotential.neg`: spectral flow potentials of the negated path.
* `TauCeti.domainSpectralFlow_neg`: the spectral flow of `-A`.
* `TauCeti.domainSpectralFlow_neg_of_ker_eq_bot`: with invertible endpoints, negating the path
  negates its spectral flow.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4.
-/

public section

open Set

namespace TauCeti

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  {ι : D →L[𝕜] H} {A : ℝ → D →L[𝕜] H} {a b : ℝ}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Spectral flow potentials of the negated path.** If `F` is a spectral flow potential of `A` on
`[a, b]`, then `t ↦ dim ker A(t) - F t` is one of `-A`. Over an interval with an admissible shift
`c` for `-A`, the shift `-c` is admissible for `A`, and the transforms of `-A` at `c` are the
negated transforms of `A` at `-c`, whose kernels have the dimensions of those of `A`. -/
theorem IsDomainSpectralFlowPotential.neg (hι : IsCompactOperator ι) {F : ℝ → ℤ}
    (hFp : IsDomainSpectralFlowPotential ι A a b F) (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫) :
    IsDomainSpectralFlowPotential ι (fun t ↦ -A t) a b
      fun t ↦ (Module.finrank 𝕜 (A t).ker : ℤ) - F t := by
  rw [isDomainSpectralFlowPotential_iff]
  intro s t c has hst htb hc hinv
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hc' : -c ≠ 0 := neg_ne_zero.2 hc
  have hinv' (u : ℝ) (hu : u ∈ Icc s t) : (((-c : ℝ) : 𝕜) • ι - A u).IsInvertible := by
    rw [RCLike.ofReal_neg]
    exact ContinuousLinearMap.isInvertible_smul_sub_neg_iff.1 (hinv u hu)
  obtain ⟨hτ, hsa, hF⟩ := regular_shiftedResolventTransform hι (hA.mono hsub)
    (fun u hu ↦ hsymm u (hsub hu)) hc' hinv'
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have ht : t ∈ Icc s t := ⟨hst, le_rfl⟩
  simp only [ContinuousLinearMap.shiftedResolventTransform_neg]
  rw [spectralFlow_neg hst hτ hsa hF,
    ContinuousLinearMap.finrank_ker_shiftedResolventTransform (hinv' s hs) hc',
    ContinuousLinearMap.finrank_ker_shiftedResolventTransform (hinv' t ht) hc',
    ← isDomainSpectralFlowPotential_iff.1 hFp has hst htb hc' hinv']
  ring

variable (hι : IsCompactOperator ι)
include hι

/-- **The spectral flow of the negated path.** For a continuous path `A` of operators on a common
domain, symmetric through a compact `ι` and each with some invertible shift,

`SF(-A; a, b) = dim ker A(b) - dim ker A(a) - SF(A; a, b)`.

The correction comes from the convention which counts the eigenvalue `0` with the nonnegative
ones, for `A` as for `-A`. -/
theorem domainSpectralFlow_neg (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    domainSpectralFlow ι (fun t ↦ -A t) a b =
      (Module.finrank 𝕜 (A b).ker : ℤ) - Module.finrank 𝕜 (A a).ker -
        domainSpectralFlow ι A a b := by
  obtain ⟨F, hFp⟩ := exists_isDomainSpectralFlowPotential hι hA hsymm h₀
  -- A shift `c₀` is admissible for `A` exactly when `-c₀` is admissible for `-A`.
  have h₀' (t : ℝ) (ht : t ∈ Icc a b) : ∃ c₀ : 𝕜, (c₀ • ι - -A t).IsInvertible := by
    obtain ⟨c₀, hc₀⟩ := h₀ t ht
    exact ⟨-c₀, ContinuousLinearMap.isInvertible_smul_sub_neg_iff.2 (by rwa [neg_neg])⟩
  rw [domainSpectralFlow_eq_sub (A := fun t ↦ -A t) hι hab hA.neg h₀' (hFp.neg hι hA hsymm),
    domainSpectralFlow_eq_sub hι hab hA h₀ hFp]
  ring

/-- **Negation with invertible endpoints.** For a continuous path `A` of operators on a common
domain, symmetric through a compact `ι` and each with some invertible shift, whose endpoints are
injective, the spectral flow of `-A` is minus that of `A`. -/
theorem domainSpectralFlow_neg_of_ker_eq_bot (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) (ha : (A a).ker = ⊥)
    (hb : (A b).ker = ⊥) :
    domainSpectralFlow ι (fun t ↦ -A t) a b = -domainSpectralFlow ι A a b := by
  rw [domainSpectralFlow_neg hι hab hA hsymm h₀, ha, hb, finrank_bot]
  ring

end TauCeti
