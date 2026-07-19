/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom
public import TauCeti.AlgebraicGeometry.GeometricallyIntegral
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# The trivial abelian variety

This file adds the **trivial abelian variety** over a field `K`: the terminal object `Spec K`,
carrying the unique (trivial) group-scheme structure. It is the zero-dimensional abelian variety,
the identity component of every abelian variety's group of connected components, and the target of
the constant map from any abelian variety.

Building it exercises the bundled `AbelianVariety` interface of
`TauCeti.AlgebraicGeometry.AbelianVariety.Basic` on its smallest example and provides two of the
roadmap's acceptance-style sanity checks at the bottom of the dimension tower:

* `AbelianVariety.trivial K`: the trivial abelian variety, with underlying scheme `Spec K` and the
  group structure of the monoidal unit of `Over (Spec K)`.
* `AbelianVariety.trivial_dim`: its dimension is `0`, computed through the topological Krull
  dimension of `Spec K` and `ringKrullDim K = 0` for a field. This is the base case of the
  roadmap's `dim (Jac X) = genus X` acceptance check.
* `AbelianVariety.isTerminalTrivial`: it is a terminal object of the category of abelian varieties
  over `K`; every abelian variety has a unique homomorphism to it (`AbelianVariety.toTrivial`),
  the constant map to the origin.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E ("Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API, `dim`"), giving the theory its
zero object and dimension-zero example. No external mathematics is vendored; the proofs reuse
Mathlib's monoidal-unit group object (`GrpObj.instTensorUnit`), the `IsProper` and
`GeometricallyIntegral` morphism-property API, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
and Tau Ceti's `AbelianVariety` and `AbelianVariety.Hom` interface.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
  MorphismProperty

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable (K : Type u) [Field K]

namespace AbelianVariety

/-- The **trivial abelian variety** over `K`: the terminal scheme `Spec K` with the group structure
of the monoidal unit of `Over (Spec K)`. Its structure morphism to `Spec K` is the identity, which
is proper and (by `geometricallyIntegral_id`) geometrically integral. -/
@[expose] noncomputable def trivial : AbelianVariety K where
  toOver := 𝟙_ (Over (Spec (.of K)))
  grpObj := inferInstance
  isProper := inferInstanceAs (IsProper (𝟙 (Spec (.of K))))
  geometricallyIntegral := geometricallyIntegral_id (Spec (.of K))

@[simp]
lemma trivial_toOver : (trivial K).toOver = 𝟙_ (Over (Spec (.of K))) := rfl

@[simp]
lemma trivial_toScheme : (trivial K).toScheme = Spec (.of K) :=
  (rfl)

/-- The trivial abelian variety is zero-dimensional: the topological Krull dimension of `Spec K` is
`ringKrullDim K = 0` for a field `K`. This is the base case of the roadmap's `dim (Jac X) = genus X`
acceptance check. -/
@[simp]
lemma trivial_dim : (trivial K).dim = 0 := by
  rw [dim_def, trivial_toScheme, ← ringKrullDim_eq_zero_of_field K,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim K]
  -- the topological space of `Spec (.of K)` is definitionally `PrimeSpectrum K`
  rfl

variable {K}

/-- The unique homomorphism from an abelian variety `A` to the trivial abelian variety: the constant
map to the origin, underlain by the terminal projection `A.toScheme → Spec K`. -/
noncomputable def toTrivial (A : AbelianVariety K) : A ⟶ trivial K :=
  Hom.mk' (toUnit A.toOver)

/-- The morphism over `Spec K` underlying `toTrivial` is the terminal projection to the unit. -/
@[simp]
lemma toOverHom_toTrivial (A : AbelianVariety K) :
    Hom.toOverHom (toTrivial A) = toUnit A.toOver :=
  Hom.toOverHom_mk' _

/-- Any homomorphism to the trivial abelian variety is the constant map `toTrivial`. -/
lemma hom_toTrivial_eq {A : AbelianVariety K} (m : A ⟶ trivial K) : m = toTrivial A :=
  Hom.ext <| congrArg Over.Hom.left
    ((isTerminalTensorUnit (C := Over (Spec (.of K)))).hom_ext _ _)

/-- Homomorphisms into the trivial abelian variety are unique: it is a terminal object. -/
noncomputable instance uniqueHomToTrivial (A : AbelianVariety K) : Unique (A ⟶ trivial K) where
  default := toTrivial A
  uniq := hom_toTrivial_eq

/-- The trivial abelian variety is a terminal object of the category of abelian varieties over `K`:
every abelian variety has a unique homomorphism to it. -/
noncomputable def isTerminalTrivial : Limits.IsTerminal (trivial K) :=
  Limits.IsTerminal.ofUniqueHom toTrivial fun _ m => hom_toTrivial_eq m

end AbelianVariety

end AlgebraicGeometry

end TauCeti
