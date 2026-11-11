/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Data.ENat.Lattice
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus

/-!
# The minimal genus of a degree-two homology class

A closed, connected, oriented surface `S` embedded in a space `Y` by `f : S → Y` **represents** the
integral class `f_*[S] ∈ H₂(Y; ℤ)`, the image of its fundamental class
(`TauCeti.HomologicalOrientation.mapFundamentalClass`). The **minimal genus** of a class
`c ∈ H₂(Y; ℤ)` (`TauCeti.minimalGenus c`) is the least genus of an embedded surface representing
it, or `⊤` if there is none. It is the invariant of Kirby's problem 1.41 (B): Giffen conjectured,
and Gabai proved, that a generator of `H₂(S³₀(K); ℤ) ≅ ℤ` has minimal genus the genus of the knot
`K`; on a `3`-manifold it is also the quantity measured, up to the correction by spheres and tori,
by the Thurston norm.

A representing surface (`TauCeti.RepresentingSurface c`) bundles a compact, connected, Hausdorff
topological surface without boundary, modelled on `ℝ²`, a homological orientation of it
(`TauCeti.HomologicalOrientation`), and a topological embedding into `Y` carrying its fundamental
class to `c`. Its **genus** (`TauCeti.RepresentingSurface.genus`) is read off its rational singular
homology: a closed, connected, orientable surface of genus `g` has `H₁(S; ℚ) ≅ ℚ²ᵍ`, so its genus
is half the dimension of `H₁(S; ℚ)`, the same convention as for Seifert and slice surfaces.

The embeddings are only asked to be topological, so that the definition applies to topological
spaces such as Dehn fillings. In a `3`-manifold nothing is lost: by Bing's approximation theorem
every embedded surface is approximated by a tame one, which is isotopic to a smooth one and, being
homotopic to the first, represents the same class with the same genus.

Reversing the orientation negates the represented class, so a class and its negative have the same
minimal genus (`TauCeti.minimalGenus_neg`). In particular the two generators of an infinite cyclic
`H₂(Y; ℤ)` have the same minimal genus.

## Main definitions

* `TauCeti.RepresentingSurface c`: a closed, connected, oriented surface embedded in `Y`
  representing `c ∈ H₂(Y; ℤ)`.
* `TauCeti.RepresentingSurface.genus`: its genus `dim H₁(S; ℚ) / 2` (`TauCeti.surfaceGenus`).
* `TauCeti.RepresentingSurface.neg`: the same surface with the reversed orientation, representing
  `-c`.
* `TauCeti.minimalGenus c`: the least genus of a surface representing `c`, in `ℕ∞`.

## Main results

* `TauCeti.minimalGenus_le_genus`, `TauCeti.le_minimalGenus_iff`: the minimal genus is the infimum
  of the genera of the representing surfaces.
* `TauCeti.minimalGenus_lt_top_iff`, `TauCeti.exists_genus_eq_minimalGenus`: it is finite exactly
  when a representing surface exists, and is then attained.
* `TauCeti.minimalGenus_neg`: a class and its negative have the same minimal genus.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, in *Geometric Topology*, AMS/IP Stud.
  Adv. Math. 2.2 (1997), Problem 1.41.
* W. P. Thurston, *A norm for the homology of 3-manifolds*, Mem. Amer. Math. Soc. 59 (1986).
* R. H. Bing, *Approximating surfaces with polyhedral ones*, Ann. of Math. 65 (1957).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Module Topology

namespace TauCeti

variable {Y : Type} [TopologicalSpace Y]

/-- The second integral singular homology `H₂(Y; ℤ)` of a space `Y`, as a `ℤ`-module: the home of
the classes represented by embedded closed oriented surfaces. -/
abbrev secondHomology (Y : Type) [TopologicalSpace Y] : ModuleCat.{0} ℤ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
    (TopCat.of Y)

/-- A **representing surface** of a class `c ∈ H₂(Y; ℤ)`: a compact, connected, Hausdorff
topological surface without boundary, modelled on `ℝ²`, with a homological orientation and a
topological embedding into `Y` carrying its fundamental class to `c`. -/
structure RepresentingSurface (c : secondHomology Y) where
  /-- The underlying surface. -/
  carrier : Type
  /-- The topology of the surface. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The surface is Hausdorff. -/
  [t2Space : T2Space carrier]
  /-- The charts of the surface, modelled on the plane. -/
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) carrier]
  /-- The surface is compact. -/
  [compactSpace : CompactSpace carrier]
  /-- The surface is connected. -/
  [connectedSpace : ConnectedSpace carrier]
  /-- The orientation of the surface. -/
  orientation : HomologicalOrientation carrier (EuclideanSpace ℝ (Fin 2)) 2
  /-- The embedding of the surface into `Y`. -/
  toFun : C(carrier, Y)
  /-- The map is a topological embedding. -/
  isEmbedding : IsEmbedding toFun
  /-- The embedded surface represents `c`. -/
  mapFundamentalClass_eq : orientation.mapFundamentalClass finrank_euclideanSpace_fin toFun = c

namespace RepresentingSurface

attribute [instance] topologicalSpace t2Space chartedSpace compactSpace connectedSpace

variable {c : secondHomology Y}

/-- The **genus** of a representing surface: half the dimension of its first rational homology
(`TauCeti.surfaceGenus`), which is `ℚ²ᵍ` for a closed, connected, orientable surface of genus
`g`. -/
def genus (S : RepresentingSurface c) : ℕ :=
  surfaceGenus S.carrier

/-- The genus of a representing surface is the genus `TauCeti.surfaceGenus` of its carrier. -/
theorem genus_def (S : RepresentingSurface c) : S.genus = surfaceGenus S.carrier :=
  (rfl)

/-- A surface representing `c`, with its orientation reversed, represents `-c`. -/
@[expose] def neg (S : RepresentingSurface c) : RepresentingSurface (-c) where
  carrier := S.carrier
  orientation := -S.orientation
  toFun := S.toFun
  isEmbedding := S.isEmbedding
  mapFundamentalClass_eq := by
    rw [HomologicalOrientation.mapFundamentalClass_neg, S.mapFundamentalClass_eq]

/-- Reversing the orientation of a representing surface keeps its genus. -/
@[simp]
theorem genus_neg (S : RepresentingSurface c) : S.neg.genus = S.genus :=
  (rfl)

end RepresentingSurface

/-- The **minimal genus** of a class `c ∈ H₂(Y; ℤ)`: the least genus of a closed, connected,
oriented surface embedded in `Y` representing `c`, or `⊤` if there is none. -/
def minimalGenus (c : secondHomology Y) : ℕ∞ :=
  ⨅ S : RepresentingSurface c, (S.genus : ℕ∞)

variable {c : secondHomology Y}

/-- The minimal genus is the infimum of the genera of all representing surfaces. -/
theorem minimalGenus_def : minimalGenus c = ⨅ S : RepresentingSurface c, (S.genus : ℕ∞) :=
  (rfl)

/-- The minimal genus of a class is at most the genus of any surface representing it. -/
theorem minimalGenus_le_genus (S : RepresentingSurface c) : minimalGenus c ≤ S.genus :=
  iInf_le _ S

/-- A lower bound for the minimal genus is a lower bound for the genus of every representing
surface. -/
@[simp]
theorem le_minimalGenus_iff {m : ℕ∞} :
    m ≤ minimalGenus c ↔ ∀ S : RepresentingSurface c, m ≤ S.genus :=
  le_iInf_iff

/-- The minimal genus is attained when a representing surface exists. -/
theorem exists_genus_eq_minimalGenus [Nonempty (RepresentingSurface c)] :
    ∃ S : RepresentingSurface c, (S.genus : ℕ∞) = minimalGenus c :=
  ENat.exists_eq_iInf _

/-- The minimal genus is finite exactly when a representing surface exists. -/
@[simp]
theorem minimalGenus_lt_top_iff : minimalGenus c < ⊤ ↔ Nonempty (RepresentingSurface c) :=
  ENat.iInf_natCast_lt_top

/-- **A class and its negative have the same minimal genus**: reversing the orientation of a
representing surface negates the class it represents. -/
@[simp]
theorem minimalGenus_neg : minimalGenus (-c) = minimalGenus c := by
  refine le_antisymm (le_minimalGenus_iff.2 fun S ↦ ?_) (le_minimalGenus_iff.2 fun S ↦ ?_)
  · simpa using minimalGenus_le_genus S.neg
  · simpa using minimalGenus_le_genus (c := - -c) S.neg

end TauCeti
