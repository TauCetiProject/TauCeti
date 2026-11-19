/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The left regular representation of a compact group on `L²(G)`

A compact group `G` acts on `L²(G)` by left translation, `(λ g f) x = f (g⁻¹ * x)`; the inverse is
what makes it a representation rather than an antirepresentation. Left translation preserves
normalized Haar measure, so the action is unitary, and it is *strongly* continuous: for each fixed
`f` the orbit map is continuous. Continuity in the operator norm is neither proved nor needed here;
the uses of `L²(G)` that do need it obtain it only after restricting to a finite-dimensional
invariant subspace.

For the commuting right regular representation on `L²(G)`, see
`TauCeti.RepresentationTheory.Continuous.RightRegular`;
`TauCeti.RepresentationTheory.Compact.BiregularRepresentation` bundles the two into a single action
of `G × G`.

## Main definitions

* `TauCeti.leftRegularLp`: the left regular representation of `G` on `L²(G)`, specializing
  `MeasureTheory.Measure.leftRegular` to `haarProb G`.

## Main statements

* `TauCeti.leftRegularLp_apply`: `λ g` is `Lp.compMeasurePreserving (g⁻¹ * ·)`, the form in which
  Mathlib and `TauCeti.RepresentationTheory.Compact.Convolution` phrase left translation.
* `TauCeti.coeFn_leftRegularLp`: `λ g f` is represented by `x ↦ f (g⁻¹ * x)`.
* `TauCeti.leftRegularLp_toLp`: on the class of a continuous function, `λ g` is left translation by
  `g⁻¹`.
* `TauCeti.isUnitary_leftRegularLp`: left translation preserves the `L²` inner product.
* `TauCeti.continuous_leftRegularLp_apply`: the action is strongly continuous.
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (𝕜 G) in
/-- **The left regular representation** of a compact group on `L²(G)`: the element `g` acts by
`f ↦ (x ↦ f (g⁻¹ * x))`. The inverse makes this a representation rather than an
antirepresentation.

This is the general left regular representation `MeasureTheory.Measure.leftRegular` for normalized
Haar measure and scalar coefficients. Only strong continuity is asserted; operator-norm continuity
is not needed and generally fails for infinite compact groups. -/
noncomputable def leftRegularLp : ContRepresentation 𝕜 G (Lp 𝕜 2 (haarProb G)) :=
  (haarProb G).leftRegular 𝕜 𝕜 2

/-- **Left translation on `L²(G)`, unfolded to the underlying `Lp.compMeasurePreserving`.** The
body of `leftRegularLp` is not exposed, so this is the lemma that moves a statement between the
representation and its raw `Lp.compMeasurePreserving` form. -/
theorem leftRegularLp_apply (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    leftRegularLp 𝕜 G g f =
      Lp.compMeasurePreserving (g⁻¹ * ·) (measurePreserving_mul_left (haarProb G) g⁻¹) f :=
  (haarProb G).leftRegular_apply 2 g f

/-- Left translation on `L²(G)` is represented by left translation of functions. -/
theorem coeFn_leftRegularLp (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    leftRegularLp 𝕜 G g f =ᵐ[haarProb G] fun x => f (g⁻¹ * x) :=
  (haarProb G).coeFn_leftRegular 2 g f

/-- **On a continuous function, the left regular representation is left translation by the
inverse.** -/
@[simp]
theorem leftRegularLp_toLp (F : C(G, 𝕜)) (g : G) :
    leftRegularLp 𝕜 G g (ContinuousMap.toLp 2 (haarProb G) 𝕜 F) =
      ContinuousMap.toLp 2 (haarProb G) 𝕜 (F.comp (.mulLeft g⁻¹)) := by
  rw [leftRegularLp_apply]
  exact Lp.compMeasurePreserving_toLp 𝕜 F (.mulLeft g⁻¹)
    (measurePreserving_mul_left (haarProb G) g⁻¹)

variable (𝕜 G) in
/-- **The left regular representation is unitary**, because left translation preserves normalized
Haar measure. -/
theorem isUnitary_leftRegularLp : ContRepresentation.IsUnitary (leftRegularLp 𝕜 G) :=
  (haarProb G).isUnitary_leftRegular

/-- **The left regular representation is strongly continuous:** every orbit map `g ↦ g · f` is
continuous. -/
theorem continuous_leftRegularLp_apply (f : Lp 𝕜 2 (haarProb G)) :
    Continuous fun g : G => leftRegularLp 𝕜 G g f :=
  (haarProb G).continuous_leftRegular_apply 2 ENNReal.ofNat_ne_top f

end CompactGroup

end TauCeti
