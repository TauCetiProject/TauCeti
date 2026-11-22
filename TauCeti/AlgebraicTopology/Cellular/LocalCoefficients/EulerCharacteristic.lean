/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finite
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Coproduct
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Homology
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic

/-!
# Finiteness and Euler--Poincaré for homology with local coefficients

Let `L` be a local coefficient system on a CW complex `C` whose fibres are finitely generated
modules. The cellular chain group `Hₙ(Xⁿ, Xⁿ⁻¹; L)` is the direct sum of the fibres of `L` at the
centres of the `n`-cells (`TauCeti.twistedCellularChainGroupIso`), so it is finitely generated
when there are finitely many `n`-cells, and its rank is `#(n-cells) · r` when every fibre is free
of rank `r` (over a ring with the strong rank condition). Through the comparison of cellular and
singular homology with local coefficients (`TauCeti.twistedCellularSingularHomologyIso`), this
gives, as for constant coefficients:

* over a noetherian ring, with finitely generated fibres, the singular homology `Hₙ(C; L)` of a CW
  complex is finitely generated in every degree with finitely many cells;
* over any ring, `Hₙ(C; L)` vanishes in every degree without cells;
* over a division ring, for a finite CW complex and a system whose fibres all have dimension `r`,
  the alternating sum of the dimensions of `Hᵢ(C; L)` is `r` times the alternating count of the
  cells (Euler--Poincaré).

Homology with local coefficients is a homotopy invariant
(`ContinuousMap.HomotopyEquiv.isIso_twistedHomologyMap`), so the same holds for every space `X` of
finite CW type: `Hₙ(X; L)` is finitely generated, vanishes in all large degrees, and its
alternating sum of dimensions is `r · χ(X)`, with `χ(X)` the Euler characteristic
`TauCeti.eulerChar X`. A local system has isomorphic fibres along each path, so a system on a
path-connected space has constant rank, the dimension of any one fibre. For a system of rank one,
such as the orientation system of a real vector bundle with coefficients in a field, the twisted
Euler characteristic is therefore the ordinary one.

Compact Hausdorff boundaryless smooth manifolds with a finite-dimensional model have finite CW
type (`TauCeti.FiniteCWType.of_isManifold`), so these results apply to the homology of such a
manifold with coefficients in any local system. Mathematically, this includes homology twisted by
the orientation system of a vector bundle over the manifold, a local system that this file does
not construct. Twisted homology of this kind is what the Thom isomorphism of a nonorientable bundle
produces, for instance the contribution of a critical submanifold of a Morse--Bott function, so its
dimensions are finite.

## Main results

* `TauCeti.finrank_twistedCellularChainGroup`: the rank of the cellular chain group with local
  coefficients whose fibres are free of constant rank `r` is `#(n-cells) · r`.
* `TauCeti.finite_twistedHomology_complexBasePair`,
  `TauCeti.isZero_twistedHomology_complexBasePair_of_isEmpty_cell` and
  `TauCeti.eventually_isZero_twistedHomology_complexBasePair`: finite generation and vanishing of
  relative homology with local coefficients of a relative CW complex.
* `TauCeti.finite_twistedHomology_of_cwComplex`, `TauCeti.isZero_twistedHomology_of_isEmpty_cell`
  and `TauCeti.finsum_finrank_twistedHomology_of_finite_cwComplex`: the same, and Euler--Poincaré,
  for the homology with local coefficients of a CW complex.
* `TauCeti.finsum_finrank_twistedHomology_complexBasePair`: Euler--Poincaré with local
  coefficients for a finite relative CW complex.
* `TauCeti.twistedHomologyIsoComplexBasePair` and
  `TauCeti.finrank_twistedHomology_eq_complexBasePair`: the homology with local coefficients of a
  CW complex is its homology relative to the empty subspace.
* `TauCeti.finite_twistedHomology_of_finiteCWType`,
  `TauCeti.eventually_isZero_twistedHomology_of_finiteCWType` and
  `TauCeti.finsum_finrank_twistedHomology_of_finiteCWType`: the same for the homology with local
  coefficients of a space of finite CW type.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Theorems 2.35 and 2.44, and Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Module Topology Topology.RelCWComplex
open scoped DirectSum

universe w v u

namespace TauCeti

section Relative

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

section Ring

variable {R : Type u} [Ring R] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C))

open scoped Classical in
/-- The cellular chain group with local coefficients, as an `R`-module, is the direct sum of the
fibres of `L` at the centres of the `n`-cells. -/
private def twistedCellularChainGroupLinearEquiv (n : ℕ) :
    twistedCellularChainGroup C L n ≃ₗ[R] ⨁ (j : cell C n), L.obj (FundamentalGroupoid.mk
      ⟨map n j 0, openCell_subset_complex n j (map_zero_mem_openCell n j)⟩) :=
  (twistedCellularChainGroupIso C L n ≪≫ ModuleCat.coprodIsoDirectSum _).toLinearEquiv

/-- The cellular chain group with local coefficients vanishes in a degree without cells. -/
theorem isZero_twistedCellularChainGroup (n : ℕ) [IsEmpty (cell C n)] :
    IsZero (twistedCellularChainGroup C L n) :=
  have := (twistedCellularChainGroupLinearEquiv C L n).injective.subsingleton
  ModuleCat.isZero_of_subsingleton _

/-- With finitely generated fibres, the cellular chain group with local coefficients in a degree
with finitely many cells is finitely generated. -/
instance finite_twistedCellularChainGroup [∀ x, Module.Finite R (L.obj x)] (n : ℕ)
    [Finite (cell C n)] : Module.Finite R (twistedCellularChainGroup C L n) :=
  .equiv (twistedCellularChainGroupLinearEquiv C L n).symm

/-- The cellular chain complex with local coefficients vanishes in a degree without cells. -/
theorem isZero_twistedCellularChainComplex_X (n : ℕ) [IsEmpty (cell C n)] :
    IsZero ((twistedCellularChainComplex C L).X n) := by
  rw [twistedCellularChainComplex_X]
  exact isZero_twistedCellularChainGroup C L n

/-- With finitely generated fibres, the cellular chain complex with local coefficients is finitely
generated in a degree with finitely many cells. -/
instance finite_twistedCellularChainComplex_X [∀ x, Module.Finite R (L.obj x)] (n : ℕ)
    [Finite (cell C n)] : Module.Finite R ((twistedCellularChainComplex C L).X n) := by
  rw [twistedCellularChainComplex_X]
  infer_instance

/-- If every fibre of `L` is free of rank `r`, the cellular chain group with coefficients in `L` in
a degree with finitely many cells has rank `#(n-cells) · r`. -/
theorem finrank_twistedCellularChainGroup [StrongRankCondition R] [∀ x, Module.Free R (L.obj x)]
    [∀ x, Module.Finite R (L.obj x)] {r : ℕ} (hL : ∀ x, finrank R (L.obj x) = r) (n : ℕ)
    [Finite (cell C n)] :
    finrank R (twistedCellularChainGroup C L n) = Nat.card (cell C n) * r := by
  have := Fintype.ofFinite (cell C n)
  rw [(twistedCellularChainGroupLinearEquiv C L n).finrank_eq, finrank_directSum]
  simp [hL, Nat.card_eq_fintype_card]

/-- Over a noetherian ring, with finitely generated fibres, the cellular homology with local
coefficients in a degree with finitely many cells is finitely generated. -/
theorem finite_twistedCellularHomology [IsNoetherianRing R] [∀ x, Module.Finite R (L.obj x)]
    (n : ℕ) [Finite (cell C n)] :
    Module.Finite R ((twistedCellularChainComplex C L).homology n) :=
  have : Module.Finite R ((twistedCellularChainComplex C L).sc n).X₂ :=
    finite_twistedCellularChainComplex_X C L n
  ((twistedCellularChainComplex C L).sc n).finite_homology

/-- Over a noetherian ring, with finitely generated fibres, the relative homology with local
coefficients of a relative CW complex is finitely generated in each degree with finitely many
cells. -/
theorem finite_twistedHomology_complexBasePair [IsNoetherianRing R]
    [∀ x, Module.Finite R (L.obj x)] (n : ℕ) [Finite (cell C n)] :
    Module.Finite R ((complexBasePair C).twistedHomology L n) :=
  have := finite_twistedCellularHomology C L n
  .equiv (twistedCellularSingularHomologyIso C L n).toLinearEquiv

/-- The relative homology with local coefficients of a relative CW complex vanishes in each degree
without cells. -/
theorem isZero_twistedHomology_complexBasePair_of_isEmpty_cell (n : ℕ) [IsEmpty (cell C n)] :
    IsZero ((complexBasePair C).twistedHomology L n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (isZero_twistedCellularChainComplex_X C L n)).isZero_homology.of_iso
      (twistedCellularSingularHomologyIso C L n).symm

/-- The relative homology with local coefficients of a finite-dimensional relative CW complex
vanishes in all sufficiently large degrees. -/
theorem eventually_isZero_twistedHomology_complexBasePair [FiniteDimensional C] :
    ∀ᶠ n in Filter.atTop, IsZero ((complexBasePair C).twistedHomology L n) :=
  FiniteDimensional.eventually_isEmpty_cell.mono fun n hn ↦
    have : IsEmpty (cell C n) := hn
    isZero_twistedHomology_complexBasePair_of_isEmpty_cell C L n

end Ring

section DivisionRing

variable {k : Type u} [DivisionRing k] (L : LocalCoefficientSystem.{u, w, max w v} k (TopCat.of C))
  [∀ x, Module.Finite k (L.obj x)] {r : ℕ}

/-- **Euler--Poincaré for cellular chains with local coefficients.** For a finite relative CW
complex and a local system whose fibres all have dimension `r`, the alternating sum of the
dimensions of the cellular homology groups is `r` times the alternating count of the cells. -/
theorem homologyEulerChar_twistedCellularChainComplex [RelCWComplex.Finite C]
    (hL : ∀ x, finrank k (L.obj x) = r) :
    (twistedCellularChainComplex C L).homologyEulerChar = r * cwEulerChar C := by
  have (i : ℕ) : Module.Finite k ((twistedCellularChainComplex C L).X i) :=
    have := FiniteType.finite_cell (C := C) (D := D) i
    finite_twistedCellularChainComplex_X C L i
  have hzero : ∀ᶠ n in Filter.atTop, IsZero ((twistedCellularChainComplex C L).X n) :=
    FiniteDimensional.eventually_isEmpty_cell.mono fun n hn ↦
      have : IsEmpty (cell C n) := hn
      isZero_twistedCellularChainComplex_X C L n
  rw [← HomologicalComplex.eulerChar_eq_homologyEulerChar _
      (HomologicalComplex.finite_not_isZero_X_of_eventually_isZero _ hzero),
    ChainComplex.eulerChar_eq_finsum_finrank, cwEulerChar_def, mul_finsum]
  refine finsum_congr fun i ↦ ?_
  have := FiniteType.finite_cell (C := C) (D := D) i
  rw [twistedCellularChainComplex_X, finrank_twistedCellularChainGroup C L hL]
  push_cast
  ring

/-- **Euler--Poincaré for relative homology with local coefficients.** For a finite relative CW
complex and a local system whose fibres all have dimension `r`, the alternating sum of the
dimensions of the relative homology groups is `r` times the alternating count of the relative
cells. -/
theorem finsum_finrank_twistedHomology_complexBasePair [RelCWComplex.Finite C]
    (hL : ∀ x, finrank k (L.obj x) = r) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k ((complexBasePair C).twistedHomology L i) =
      r * cwEulerChar C := by
  simp_rw [← (twistedCellularSingularHomologyIso C L _).toLinearEquiv.finrank_eq]
  rw [← ChainComplex.homologyEulerChar_eq_finsum_finrank]
  exact homologyEulerChar_twistedCellularChainComplex C L hL

end DivisionRing

end Relative

section Absolute

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

section Ring

variable {R : Type u} [Ring R] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C))

/-- The homology with local coefficients of a CW complex is its relative homology modulo the empty
base. -/
def twistedHomologyIsoComplexBasePair (n : ℕ) :
    L.twistedHomology n ≅ (complexBasePair C).twistedHomology L n :=
  -- Instance search does not see `L` as a system on `(complexBasePair C).fst`, so the instance
  -- is supplied explicitly.
  @asIso _ _ _ _ ((complexBasePair C).twistedHomologyπ L n)
    (TopPair.isIso_twistedHomologyπ_of_isEmpty (complexBasePair C) L n)

@[simp]
lemma twistedHomologyIsoComplexBasePair_hom (n : ℕ) :
    (twistedHomologyIsoComplexBasePair C L n).hom = (complexBasePair C).twistedHomologyπ L n := by
  rw [twistedHomologyIsoComplexBasePair]
  exact @asIso_hom _ _ _ _ _ (TopPair.isIso_twistedHomologyπ_of_isEmpty (complexBasePair C) L n)

/-- The homology with local coefficients of a CW complex has the dimension of its homology
relative to the empty subspace. -/
theorem finrank_twistedHomology_eq_complexBasePair (n : ℕ) :
    finrank R (L.twistedHomology n) = finrank R ((complexBasePair C).twistedHomology L n) :=
  (twistedHomologyIsoComplexBasePair C L n).toLinearEquiv.finrank_eq

/-- Over a noetherian ring, with finitely generated fibres, the homology with local coefficients
of a CW complex is finitely generated in each degree with finitely many cells. -/
theorem finite_twistedHomology_of_cwComplex [IsNoetherianRing R]
    [∀ x, Module.Finite R (L.obj x)] (n : ℕ) [Finite (cell C n)] :
    Module.Finite R (L.twistedHomology n) :=
  have := finite_twistedHomology_complexBasePair C L n
  .equiv (twistedHomologyIsoComplexBasePair C L n).symm.toLinearEquiv

/-- The homology with local coefficients of a CW complex vanishes in each degree without cells. -/
theorem isZero_twistedHomology_of_isEmpty_cell (n : ℕ) [IsEmpty (cell C n)] :
    IsZero (L.twistedHomology n) :=
  (isZero_twistedHomology_complexBasePair_of_isEmpty_cell C L n).of_iso
    (twistedHomologyIsoComplexBasePair C L n)

end Ring

/-- **Euler--Poincaré for homology with local coefficients.** For a finite CW complex and a local
system whose fibres all have dimension `r`, the alternating sum of the dimensions of the homology
groups with coefficients in the system is `r` times the alternating count of the cells. -/
theorem finsum_finrank_twistedHomology_of_finite_cwComplex [RelCWComplex.Finite C] {k : Type u}
    [DivisionRing k] (L : LocalCoefficientSystem.{u, w, max w v} k (TopCat.of C))
    [∀ x, Module.Finite k (L.obj x)] {r : ℕ} (hL : ∀ x, finrank k (L.obj x) = r) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k (L.twistedHomology i) = r * cwEulerChar C := by
  simp_rw [finrank_twistedHomology_eq_complexBasePair C L]
  exact finsum_finrank_twistedHomology_complexBasePair C L hL

end Absolute

section FiniteCWType

variable {R : Type u} [Ring R] (X : Type w) [TopologicalSpace X] [h : FiniteCWType X]

/-- Over a noetherian ring, the homology of a space of finite CW type with coefficients in a local
system of finitely generated modules is finitely generated in every degree. -/
theorem finite_twistedHomology_of_finiteCWType [IsNoetherianRing R]
    (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of X)) [∀ x, Module.Finite R (L.obj x)]
    (n : ℕ) : Module.Finite R (L.twistedHomology n) := by
  obtain ⟨Y, _, _, C, _, _, ⟨e⟩⟩ := h.exists_homotopyEquiv
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  have := finite_twistedHomology_of_cwComplex C
    ((LocalCoefficientSystem.pullback (TopCat.ofHom e.symm.toFun).hom).obj L) n
  exact .equiv (e.symm.twistedHomologyIso L n).toLinearEquiv

/-- The homology of a space of finite CW type with coefficients in any local system vanishes in
all sufficiently large degrees. -/
theorem eventually_isZero_twistedHomology_of_finiteCWType
    (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of X)) :
    ∀ᶠ n in Filter.atTop, IsZero (L.twistedHomology n) := by
  obtain ⟨Y, _, _, C, _, _, ⟨e⟩⟩ := h.exists_homotopyEquiv
  refine (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)).mono fun n hn ↦ ?_
  have : IsEmpty (cell C n) := hn
  exact (isZero_twistedHomology_of_isEmpty_cell C
    ((LocalCoefficientSystem.pullback (TopCat.ofHom e.symm.toFun).hom).obj L) n).of_iso
      (e.symm.twistedHomologyIso L n).symm

/-- **Euler--Poincaré for homology with local coefficients of a space of finite CW type.** If
every fibre of the local system `L` has dimension `r`, the alternating sum of the dimensions of the
homology groups of `X` with coefficients in `L` is `r` times the Euler characteristic of `X`. -/
theorem finsum_finrank_twistedHomology_of_finiteCWType {k : Type u} [DivisionRing k]
    (L : LocalCoefficientSystem.{u, w, max w v} k (TopCat.of X)) [∀ x, Module.Finite k (L.obj x)]
    {r : ℕ} (hL : ∀ x, finrank k (L.obj x) = r) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k (L.twistedHomology i) = r * eulerChar X := by
  obtain ⟨Y, _, _, C, _, _, ⟨e⟩⟩ := h.exists_homotopyEquiv
  rw [eulerChar_eq_cwEulerChar e, ← finsum_finrank_twistedHomology_of_finite_cwComplex C
    ((LocalCoefficientSystem.pullback (TopCat.ofHom e.symm.toFun).hom).obj L) fun x ↦ hL _]
  refine finsum_congr fun i ↦ ?_
  rw [(e.symm.twistedHomologyIso L i).toLinearEquiv.finrank_eq]

end FiniteCWType

end TauCeti
