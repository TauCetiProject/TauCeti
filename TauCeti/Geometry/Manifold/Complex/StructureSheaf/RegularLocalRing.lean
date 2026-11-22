/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cotangent
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Dimension
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Noetherian
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Regular
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import Mathlib.Algebra.Module.SpanRankOperations

/-!
# Coordinate parameters of regular holomorphic local rings

The local ring of holomorphic germs on a finite-dimensional complex manifold without boundary
is regular, of Krull dimension equal to the complex dimension of the model
(`TauCeti.holomorphicStructureSheaf.stalkIsRegularLocalRing`,
`TauCeti.holomorphicStructureSheaf.ringKrullDim_stalk`). Its maximal ideal needs exactly that many
generators (`TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_stalk`), and its
embedding dimension (the dimension of the cotangent space) equals `Module.finrank ℂ E`
(`TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_stalk`).

The same regularity, Krull dimension, and maximal-ideal rank facts hold at any point in the
domain of a single holomorphic chart (`OpenPartialHomeomorph.isRegularLocalRing_holomorphicStalk`,
`OpenPartialHomeomorph.ringKrullDim_holomorphicStalk`,
`OpenPartialHomeomorph.spanFinrank_maximalIdeal_holomorphicStalk`), without a global manifold
instance.

Centered coordinates in any holomorphic chart along any duplicate-free list of basis indices form
a regular sequence, not merely a generating family of the maximal ideal
(`OpenPartialHomeomorph.isRegular_map_holomorphicLinearCoordinateGerm`). Thus successive
coordinate equations are non-zero-divisors on the successive quotients. This is the local algebra
underlying smooth holomorphic zero sets. The generator count and embedding dimension also apply to
the native complex-smooth sheaf stalks through their canonical comparison with holomorphic germs.

## Main declarations

* `OpenPartialHomeomorph.spanFinrank_maximalIdeal_holomorphicStalk`: chart-local maximal-ideal
  generator count.
* `TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_stalk`,
  `TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_stalk`: the minimal number of
  generators of the maximal ideal and the embedding dimension equal `Module.finrank ℂ E`.
* `TauCeti.holomorphicStructureSheaf.spanFinrank_ker_eval`: the kernel of evaluation needs
  `Module.finrank ℂ E` generators.
* `TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_smoothStalk`,
  `TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_smoothStalk`: the corresponding results
  for Mathlib's complex-smooth structure sheaf.
* `OpenPartialHomeomorph.isRegular_map_holomorphicLinearCoordinateGerm`,
  `OpenPartialHomeomorph.isRegular_ofFn_holomorphicLinearCoordinateGerm`: any duplicate-free tuple
  of centered coordinate germs of a holomorphic chart along a basis forms a regular sequence on
  `𝒪_{X, x}`.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II.
-/

public noncomputable section

open IsLocalRing
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

section Boundaryless

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]

/-- The minimal number of generators of the maximal ideal of the holomorphic stalk at any point in
the domain of a holomorphic chart equals `Module.finrank ℂ E`. -/
theorem spanFinrank_maximalIdeal_holomorphicStalk (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I 1 X) {x : X} (hx : x ∈ e.source) :
    (maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := (holomorphicStructureSheaf I X).presheaf.stalk x)).trans
    (e.ringKrullDim_holomorphicStalk he hx)

end Boundaryless

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]

/-- **Centered local coordinates form a regular sequence.** For any holomorphic chart `e` at `x`,
any basis `b` of `E`, and any duplicate-free list `l` of indices of `b`, the centered linear
coordinate germs `y ↦ b.coord i (e y - e x)` along `l` form a regular sequence on `𝒪_{X, x}`. -/
theorem isRegular_map_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) {ι : Type*} (b : Module.Basis ι ℂ E) {x : X}
    (hx : x ∈ e.source) {l : List ι} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      (l.map fun i ↦ e.holomorphicLinearCoordinateGerm he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 1 X :=
    IsManifold.maximalAtlas_subset_of_le le_top he
  have := e.isRegularLocalRing_holomorphicStalk he₁ hx
  have := Module.Finite.finite_basis b
  exact TauCeti.IsRegularLocalRing.isRegular_map_of_span_range_eq_maximalIdeal
    (by rw [maximalIdeal_stalk, e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hx])
    (by rw [e.spanFinrank_maximalIdeal_holomorphicStalk he₁ hx, Module.finrank_eq_nat_card_basis b])
    hl

/-- Centered coordinates of a holomorphic chart, in any ordered basis, form a regular sequence
in the holomorphic local ring. In particular each coordinate is a non-zero-divisor after
quotienting by the preceding coordinates. -/
theorem isRegular_ofFn_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {n : ℕ} (b : Module.Basis (Fin n) ℂ E) :
    RingTheory.Sequence.IsRegular ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      (List.ofFn fun i ↦ e.holomorphicLinearCoordinateGerm he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  rw [List.ofFn_eq_map]
  exact e.isRegular_map_holomorphicLinearCoordinateGerm he b hx (List.nodup_finRange n)

end Coordinates

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The minimal number of generators of the maximal ideal of a holomorphic stalk equals the
complex dimension of the manifold model. -/
theorem spanFinrank_maximalIdeal_stalk (x : X) :
    (maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E :=
  (chartAt H x).spanFinrank_maximalIdeal_holomorphicStalk
    (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source H x)

/-- The embedding dimension of a holomorphic stalk on any finite-dimensional complex manifold
without boundary equals the complex dimension of its model space. -/
@[simp]
theorem finrank_cotangentSpace_stalk (x : X) :
    Module.finrank (ResidueField ((holomorphicStructureSheaf I X).presheaf.stalk x))
        (CotangentSpace ((holomorphicStructureSheaf I X).presheaf.stalk x)) =
      Module.finrank ℂ E := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact spanFinrank_maximalIdeal_stalk x

/-- The kernel of evaluation on a holomorphic stalk needs as many generators as the complex
model dimension. This is the generator count in the simp normal form of the maximal ideal. -/
@[simp]
theorem spanFinrank_ker_eval (x : X) :
    (RingHom.ker (eval I X x)).spanFinrank = Module.finrank ℂ E := by
  rw [← maximalIdeal_stalk, spanFinrank_maximalIdeal_stalk]

/-- The maximal ideal of the native complex-smooth stalk needs as many generators as the
complex model dimension. -/
@[simp]
theorem spanFinrank_maximalIdeal_smoothStalk (x : X) :
    (maximalIdeal ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E := by
  exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)).trans (ringKrullDim_smoothStalk x)

/-- The embedding dimension of a stalk of Mathlib's complex-smooth structure sheaf equals the
complex dimension of its model. -/
@[simp]
theorem finrank_cotangentSpace_smoothStalk (x : X) :
    Module.finrank (ResidueField ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x))
        (CotangentSpace ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)) =
      Module.finrank ℂ E := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact spanFinrank_maximalIdeal_smoothStalk x

end TauCeti.holomorphicStructureSheaf
