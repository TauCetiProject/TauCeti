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
import TauCeti.RingTheory.Regular.RegularSequence

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

* `TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_stalk`,
  `TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_stalk`: the minimal number of
  generators of the maximal ideal and the embedding dimension equal `Module.finrank ℂ E`.
* `TauCeti.holomorphicStructureSheaf.spanFinrank_ker_eval`: the kernel of evaluation needs
  `Module.finrank ℂ E` generators.
* `TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_smoothStalk`,
  `TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_smoothStalk`: the corresponding results
  for Mathlib's complex-smooth structure sheaf.
* `OpenPartialHomeomorph.isRegularLocalRing_holomorphicStalk`,
  `OpenPartialHomeomorph.ringKrullDim_holomorphicStalk`,
  `OpenPartialHomeomorph.spanFinrank_maximalIdeal_holomorphicStalk`: chart-local regularity,
  Krull dimension, and maximal-ideal generator count.
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

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The minimal number of generators of the maximal ideal of a holomorphic stalk equals the
complex dimension of the manifold model. -/
theorem spanFinrank_maximalIdeal_stalk (x : X) :
    (maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E := by
  exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := (holomorphicStructureSheaf I X).presheaf.stalk x)).trans (ringKrullDim_stalk x)

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

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

section Boundaryless

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]

/-- Identifies the holomorphic stalk at a point of a chart with a stalk on `Fin d → ℂ`. -/
private def holomorphicStalkEquivFin (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I ω X) {x : X} (hx : x ∈ e.source) :
    (holomorphicStructureSheaf I X).presheaf.stalk x ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, Fin (Module.finrank ℂ E) → ℂ)
        (Fin (Module.finrank ℂ E) → ℂ)).presheaf.stalk
        ((ContinuousLinearEquiv.ofFinrankEq (by simp) :
          E ≃L[ℂ] Fin (Module.finrank ℂ E) → ℂ) (e.extend I x)) :=
  e.holomorphicStalkEquivModelSpace (V := Fin (Module.finrank ℂ E) → ℂ) he x hx
    (ContinuousLinearEquiv.ofFinrankEq (by simp))

/-- The holomorphic stalk at any point in the domain of a holomorphic chart is a regular local
ring, with no global manifold assumption beyond the chart itself. -/
theorem isRegularLocalRing_holomorphicStalk (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I ω X) {x : X} (hx : x ∈ e.source) :
    IsRegularLocalRing ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  IsRegularLocalRing.of_ringEquiv (e.holomorphicStalkEquivFin he hx).symm

/-- The Krull dimension of the holomorphic stalk at any point in the domain of a holomorphic chart
equals `Module.finrank ℂ E`. -/
theorem ringKrullDim_holomorphicStalk (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I ω X) {x : X} (hx : x ∈ e.source) :
    ringKrullDim ((holomorphicStructureSheaf I X).presheaf.stalk x) =
      Module.finrank ℂ E := by
  rw [(e.holomorphicStalkEquivFin he hx).ringKrullDim, ringKrullDim_stalk]
  simp

/-- The minimal number of generators of the maximal ideal of the holomorphic stalk at any point in
the domain of a holomorphic chart equals `Module.finrank ℂ E`. -/
theorem spanFinrank_maximalIdeal_holomorphicStalk (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I ω X) {x : X} (hx : x ∈ e.source) :
    (maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      Module.finrank ℂ E := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := (holomorphicStructureSheaf I X).presheaf.stalk x)).trans
    (e.ringKrullDim_holomorphicStalk he hx)

end Boundaryless

section Coordinates

/-- Completes a duplicate-free list over a finite type to a duplicate-free list covering every
element. -/
private theorem exists_nodup_append_forall_mem {ι : Type*} [Finite ι]
    {l : List ι} (hl : l.Nodup) :
    ∃ l' : List ι, (l ++ l').Nodup ∧ ∀ i : ι, i ∈ l ++ l' := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let all := (Finset.univ : Finset ι).toList
  have hperm : List.Perm (l ++ all.diff l) all :=
    List.subperm_append_diff_self_of_count_le (List.subperm_ext_iff.mp
      (hl.subperm fun i _ ↦ Finset.mem_toList.2 (Finset.mem_univ i)))
  exact ⟨all.diff l, hperm.nodup_iff.2 (Finset.nodup_toList _),
    fun i ↦ hperm.mem_iff.2 (Finset.mem_toList.2 (Finset.mem_univ i))⟩

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
  classical
  have := e.isRegularLocalRing_holomorphicStalk he hx
  have := Module.Finite.finite_basis b
  let : Fintype ι := Fintype.ofFinite ι
  let z : ι → (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x :=
    fun i ↦ e.holomorphicLinearCoordinateGerm he x
      (LinearMap.toContinuousLinearMap (b.coord i)) hx
  obtain ⟨l', hnodup, hmem⟩ := exists_nodup_append_forall_mem hl
  have hspan : Ideal.ofList ((l ++ l').map z) =
      maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) := by
    rw [maximalIdeal_stalk, e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hx]
    exact Ideal.ofList_map_eq_span_range hmem z
  have hlen : ((l ++ l').map z).length ≤
      (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)).spanFinrank := by
    rw [List.length_map, e.spanFinrank_maximalIdeal_holomorphicStalk he hx,
      Module.finrank_eq_card_basis b]
    exact hnodup.length_le_card
  have hfull := TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal hspan hlen
  rw [List.map_append] at hfull
  exact hfull.of_append_left

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
