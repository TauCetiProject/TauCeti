/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Polynomial
public import Mathlib.Analysis.Normed.Group.Quotient
import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.LinearIsometry
import TauCeti.Analysis.Sobolev.Wkp.DenyLions

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

The statements about `N` need no connectedness. On a preconnected `Ω ⊆ EuclideanSpace ℝ ι`, `N`
consists of the classes of polynomials of total degree at most `m`, which gives the classical form
of the lemma: the quotient norm modulo these polynomial classes and the descended top seminorm
`TauCeti.Wkp.quotientSeminorm m` are equivalent norms, and, when `Ω` is moreover nonempty, a
continuous linear projection onto the polynomials of degree at most `m` approximates `u` to within a
multiple of `|u|_{m+1,p}`. The model case `F = WithLp 2 (ℝ × E)` is `e = LinearIsometryEquiv.refl`.

The proof combines the higher-order Rellich–Kondrachov theorem
`TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image` with the
compactness form of the lemma in `TauCeti.Analysis.Sobolev.Wkp.DenyLions`. The constant is not
explicit.

## Main declarations

* `TauCeti.Wkp.finiteDimensional_ker_iteratedGradientL_of_isLipschitzDomainWith_image`
* `TauCeti.Wkp.exists_projection_norm_sub_le_of_isLipschitzDomainWith_image`
* `TauCeti.Wkp.exists_norm_quotientMk_ker_le_of_isLipschitzDomainWith_image`
* `TauCeti.Wkp.exists_norm_le_quotientSeminorm_of_isLipschitzDomainWith_image`
* `TauCeti.Wkp.exists_polynomialProjection_norm_sub_le_of_isLipschitzDomainWith_image`

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
constant multiple of `‖D^{m+1} u‖`; together with
`TauCeti.Wkp.norm_iteratedGradient_le_norm_quotientMk_of_le_ker`, the quotient norm and the
descended top seminorm are equivalent. -/
theorem exists_norm_quotientMk_ker_le_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Wkp volume Ω p (m + 1),
      ‖(Submodule.Quotient.mk u : Wkp volume Ω p (m + 1) ⧸
        (iteratedGradientL (mu := volume) (Omega := Ω) (p := p) m).ker)‖ ≤
        C * ‖iteratedGradient m u‖ :=
  exists_norm_quotientMk_ker_le_of_isCompactOperator m
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb m)

/-! ### The Deny–Lions lemma modulo polynomials -/

section Polynomial

variable {ι : Type*} [Fintype ι] {Ω : Opens (EuclideanSpace ℝ ι)}

/-- **The Deny–Lions lemma modulo polynomials on Lipschitz domains.** Let
`Ω ⊆ EuclideanSpace ℝ ι` be a bounded, preconnected open set whose isometric image in the model
space is a Lipschitz domain, and `1 ≤ p ≤ ∞`. On the quotient of `W^{m+1,p}(Ω)` by the polynomial
classes of degree at most `m`, the quotient norm `inf_q ‖u - q‖` is bounded by a constant multiple
of the descended top seminorm `|u|_{m+1,p}`. With `TauCeti.Wkp.quotientSeminorm_le_norm`, the two
are equivalent norms on the quotient. -/
theorem exists_norm_le_quotientSeminorm_of_isLipschitzDomainWith_image
    (e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E))
    (hΩ : (e '' (Ω : Set (EuclideanSpace ℝ ι))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ ι))) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Wkp volume Ω p (m + 1) ⧸ polynomialClasses (m + 1) m,
      ‖x‖ ≤ C * quotientSeminorm m x :=
  exists_norm_le_quotientSeminorm_of_isCompactOperator hc m
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb m)

/-- **The Deny–Lions lemma on Lipschitz domains, polynomial projection form.** Let
`Ω ⊆ EuclideanSpace ℝ ι` be a nonempty, bounded, preconnected open set whose isometric image in the
model space is a Lipschitz domain, and `1 ≤ p ≤ ∞`. There are a continuous linear map `π` from
`W^{m+1,p}(Ω)` to the polynomial functions of total degree at most `m`, which recovers every such
polynomial from its Sobolev class, and a constant `C` such that the Sobolev class of `π u`
approximates `u` with `‖u - π u‖_{m+1,p} ≤ C * |u|_{m+1,p}`. -/
theorem exists_polynomialProjection_norm_sub_le_of_isLipschitzDomainWith_image
    (e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E))
    (hΩ : (e '' (Ω : Set (EuclideanSpace ℝ ι))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ ι)))
    (hne : (Ω : Set (EuclideanSpace ℝ ι)).Nonempty) (m : ℕ) :
    ∃ (π : Wkp volume Ω p (m + 1) →L[ℝ] polynomialsDegLE ι m) (C : ℝ), 0 ≤ C ∧
      (∀ q, π (polynomialL hb (m + 1) m q) = q) ∧
      ∀ u, ‖u - polynomialL hb (m + 1) m (π u)‖ ≤ C * seminorm (m + 1) (m + 1) le_rfl u :=
  exists_polynomialProjection_norm_sub_le_of_isCompactOperator hb hc hne m
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb m)

end Polynomial

end Wkp

end TauCeti
