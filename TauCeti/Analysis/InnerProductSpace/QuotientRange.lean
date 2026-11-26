/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.Normed.Operator.QuotientRange

/-!
# Orthogonal complements to nearby operator ranges on Hilbert spaces

This file specializes the Banach-space restricted-coproduct invertibility and neighborhood
stability API of `TauCeti.Analysis.Normed.Operator.QuotientRange` to operators taking values in a
Hilbert space `F`, where the complementary subspace `W ≤ F` is chosen canonically as an orthogonal
complement.

Given a continuous linear operator `T₀ : E →L[𝕜] F` into a Hilbert space `F` and a complete
subspace `V ≤ E` transverse to `ker T₀` (`Disjoint V T₀.ker`), whenever `T₀(V)` admits an
orthogonal projection in `F`, `(T₀(V))ᗮ` is a closed algebraic complement of `T₀(V)`. Hence the
restricted coproduct `(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is invertible at `T = T₀`
(`ContinuousLinearMap.isInvertible_coprod_domRestrict_orthogonal`) and on an operator-norm
neighborhood of `T₀`
(`ContinuousLinearMap.eventually_nhds_isInvertible_coprod_domRestrict_orthogonal`).

Two common cases require no explicit `HasOrthogonalProjection` hypothesis:

* **Finite-dimensional `V`** (Atiyah–Singer I, §6, pp. 519–520): completeness of `V` and `T₀(V)`
  are automatic, yielding basepoint invertibility and neighborhood stability of
  `(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL`.
* **Closed-range operators between Hilbert spaces**: taking `V = (ker T₀)ᗮ` and
  `W = ker T₀† = (range T₀)ᗮ` (via `LinearMap.map_orthogonal_ker_eq_range` in
  `TauCeti.Analysis.InnerProductSpace.Projection.Basic` and `ContinuousLinearMap.orthogonal_range`)
  yields basepoint invertibility and neighborhood stability of
  `(T.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL`.

## Main declarations

In `ContinuousLinearMap`:

* `isInvertible_coprod_domRestrict_orthogonal`,
  `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal`: basepoint invertibility and
  neighborhood stability of `(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` when `V` is complete,
  `Disjoint V T₀.ker`, and `T₀(V)` admits an orthogonal projection.
* `isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional`,
  `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional`: the
  Atiyah–Singer finite-dimensional transverse-subspace lemma.
* `isInvertible_coprod_domRestrict_orthogonal_ker`,
  `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_ker`: basepoint invertibility and
  neighborhood stability of `(T.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL` for a closed-range
  operator between Hilbert spaces.

## References

* M. F. Atiyah, I. M. Singer, *The Index of Elliptic Operators: I*, Annals of Mathematics **87**
  (1968), 484–530, §6, pp. 519–520.
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1.
-/

public section

open Filter Topology
open scoped InnerProduct

namespace ContinuousLinearMap

/-! ### Hilbert-target orthogonal restricted coproducts -/

section HilbertCodomain

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- When `V` is complete, `T₀(V)` admits an orthogonal projection in `F`, and `Disjoint V T₀.ker`,
the Hilbert transverse coproduct `(T₀.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is invertible. -/
theorem isInvertible_coprod_domRestrict_orthogonal {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [CompleteSpace V] [(V.map (T₀ : E →ₗ[𝕜] F)).HasOrthogonalProjection]
    (hdisj : Disjoint V T₀.ker) :
    ((T₀.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  isInvertible_coprod_domRestrict (V.map (T₀ : E →ₗ[𝕜] F)).isCompl_orthogonal hdisj

/-- Under the hypotheses of `isInvertible_coprod_domRestrict_orthogonal`,
`(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is invertible throughout a neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_coprod_domRestrict_orthogonal {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} [CompleteSpace V] [(V.map (T₀ : E →ₗ[𝕜] F)).HasOrthogonalProjection]
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  eventually_nhds_isInvertible_coprod_domRestrict
    (V.map (T₀ : E →ₗ[𝕜] F)).isCompl_orthogonal hdisj

/-- Basepoint invertibility of `(T₀.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` for a
finite-dimensional subspace `V` disjoint from `ker T₀`. -/
theorem isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ((T₀.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible := by
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  have : FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F)) := Module.Finite.map V (T₀ : E →ₗ[𝕜] F)
  have : CompleteSpace (V.map (T₀ : E →ₗ[𝕜] F)) := FiniteDimensional.completeSpace 𝕜 _
  exact isInvertible_coprod_domRestrict_orthogonal hdisj

/-- **Atiyah–Singer finite-dimensional transverse-subspace lemma.** If `V ≤ E` is
finite-dimensional and `Disjoint V T₀.ker`, then `(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is
invertible for every `T` in an operator-norm neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional
    {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E} [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  (continuous_coprod_domRestrict V _).tendsto T₀ |>.eventually
    (isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional hdisj).eventually_nhds

end HilbertCodomain

/-! ### Closed-range operators between Hilbert spaces -/

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For a closed-range operator `T₀ : E →L[𝕜] F` between Hilbert spaces, the restricted coproduct
`(T₀.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL` is invertible. -/
theorem isInvertible_coprod_domRestrict_orthogonal_ker {T₀ : E →L[𝕜] F}
    (hT₀ : IsClosed (T₀.range : Set F)) :
    ((T₀.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL).IsInvertible := by
  let : CompleteSpace T₀.range := hT₀.isComplete.completeSpace_coe
  have hCompl : IsCompl (T₀.kerᗮ.map (T₀ : E →ₗ[𝕜] F)) (T₀†).ker := by
    rw [LinearMap.map_orthogonal_ker_eq_range, ← T₀.orthogonal_range]
    exact T₀.range.isCompl_orthogonal
  exact isInvertible_coprod_domRestrict hCompl T₀.ker.isCompl_orthogonal.symm.disjoint

/-- **Orthogonal-kernel transverse coproduct stability.** For any closed-range operator
`T₀ : E →L[𝕜] F` between Hilbert spaces, `(T.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL`
remains invertible for every `T` in an operator-norm neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_ker {T₀ : E →L[𝕜] F}
    (hT₀ : IsClosed (T₀.range : Set F)) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL).IsInvertible :=
  (continuous_coprod_domRestrict T₀.kerᗮ (T₀†).ker).tendsto T₀ |>.eventually
    (isInvertible_coprod_domRestrict_orthogonal_ker hT₀).eventually_nhds

end Hilbert

end ContinuousLinearMap
