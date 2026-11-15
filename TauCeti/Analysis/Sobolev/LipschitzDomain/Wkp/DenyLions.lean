/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.LinearIsometry
public import TauCeti.Analysis.Sobolev.Wkp.DenyLions

/-!
# The Deny–Lions lemma on bounded Lipschitz domains

Let `Ω ⊆ F` be a bounded open set whose image under a linear isometry
`e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)` is a Lipschitz domain, and let `1 ≤ p ≤ ∞`. Writing `N` for the
kernel of the highest weak derivative `D^{m+1}` on `W^{m+1,p}(Ω)`, this file proves the
**Deny–Lions lemma**: `N` is finite-dimensional, and the quotient norm on `W^{m+1,p}(Ω) ⧸ N` is
equivalent to the top seminorm,

`‖D^{m+1} u‖_{Lᵖ} ≤ ‖[u]‖ ≤ C * ‖D^{m+1} u‖_{Lᵖ}`,

with a constant `C` depending on `Ω`, `m` and `p` but not on `u`. Equivalently, there is a
continuous projection `P` onto `N` with `‖u - P u‖_{m+1,p} ≤ C * ‖D^{m+1} u‖_{Lᵖ}`.

Classically, on a connected `Ω` the kernel `N` consists of the polynomials of degree at most `m`;
the statements here do not use that identification. The model case `F = WithLp 2 (ℝ × E)` is
`e = LinearIsometryEquiv.refl`.

The proof combines the higher-order Rellich–Kondrachov theorem
`TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image` with the
compactness form of the lemma in `TauCeti.Analysis.Sobolev.Wkp.DenyLions`. The constant is not
explicit.

## Main declarations

* `TauCeti.Wkp.finiteDimensional_ker_iteratedGradientL_of_isLipschitzDomainWith_image`
* `TauCeti.Wkp.exists_projection_norm_sub_le_of_isLipschitzDomainWith_image`
* `TauCeti.Wkp.exists_norm_mk_le_of_isLipschitzDomainWith_image`

## References

* J. Deny, J.-L. Lions, *Les espaces du type de Beppo Levi*, Ann. Inst. Fourier 5 (1954),
  305–370, Chapitre III, §2, Théorème 2.1.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, SIAM (2002), Theorem 3.1.1.
-/

public section

noncomputable section

namespace TauCeti

open Bornology MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- On a bounded open set whose isometric image in the model space is a Lipschitz domain, the
kernel of the highest weak derivative on `W^{m+1,p}(Ω)` is finite-dimensional, for every
`1 ≤ p ≤ ∞`. -/
theorem finiteDimensional_ker_iteratedGradientL_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (m : ℕ) :
    FiniteDimensional ℝ (iteratedGradientL (mu := volume) (Omega := Ω) (p := p) m).ker :=
  finiteDimensional_ker_iteratedGradientL_of_isCompactOperator m
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb m)

/-- **The Deny–Lions lemma on Lipschitz domains, projection form.** Let `Ω` be a bounded open set
whose isometric image in the model space is a Lipschitz domain, and `1 ≤ p ≤ ∞`. There are a
continuous linear projection `P` of `W^{m+1,p}(Ω)` onto the kernel of the highest weak derivative
`D^{m+1}` and a constant `C` with `‖u - P u‖ ≤ C * ‖D^{m+1} u‖` for every `u ∈ W^{m+1,p}(Ω)`. -/
theorem exists_projection_norm_sub_le_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (m : ℕ) :
    ∃ (P : Wkp volume Ω p (m + 1) →L[ℝ] Wkp volume Ω p (m + 1)) (C : ℝ), 0 ≤ C ∧
      (∀ u, iteratedGradient m (P u) = 0) ∧ (∀ u, iteratedGradient m u = 0 → P u = u) ∧
      ∀ u, ‖u - P u‖ ≤ C * ‖iteratedGradient m u‖ :=
  exists_projection_norm_sub_le_of_isCompactOperator m
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb m)

/-- **The Deny–Lions lemma on Lipschitz domains.** Let `Ω` be a bounded open set whose isometric
image in the model space is a Lipschitz domain, and `1 ≤ p ≤ ∞`. The quotient norm of
`u ∈ W^{m+1,p}(Ω)` modulo the kernel of the highest weak derivative `D^{m+1}` is bounded by a
constant multiple of `‖D^{m+1} u‖`; together with `TauCeti.Wkp.norm_iteratedGradient_le_norm_mk`,
the quotient norm and the descended top seminorm are equivalent. -/
theorem exists_norm_mk_le_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Wkp volume Ω p (m + 1),
      ‖(Submodule.Quotient.mk u : Wkp volume Ω p (m + 1) ⧸
        (iteratedGradientL (mu := volume) (Omega := Ω) (p := p) m).ker)‖ ≤
        C * ‖iteratedGradient m u‖ :=
  exists_norm_mk_le_of_isCompactOperator m
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb m)

end Wkp

end TauCeti
