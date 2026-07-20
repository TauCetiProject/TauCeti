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
the terminal object of the category of abelian varieties over `K`, and the target of the constant
map from any abelian variety.

Building it exercises the bundled `AbelianVariety` interface of
`TauCeti.AlgebraicGeometry.AbelianVariety.Basic` on its smallest example:

* `AbelianVariety.trivial K`: the trivial abelian variety, with underlying scheme `Spec K` and the
  group structure of the monoidal unit of `Over (Spec K)`.
* `AbelianVariety.trivial_dim`: its dimension is `0`, computed through the topological Krull
  dimension of `Spec K` and `ringKrullDim K = 0` for a field.
* `AbelianVariety.isTerminalTrivial`: it is a terminal object of the category of abelian varieties
  over `K`; every abelian variety has a unique homomorphism to it (`AbelianVariety.toTrivial`),
  the constant map to the origin.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E ("Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API, `dim`"), giving the theory its
terminal object and dimension-zero example. No external mathematics is vendored; the proofs reuse
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

/-- The structural morphism of the monoidal unit of `Over (Spec K)` is the identity, hence
proper. -/
instance isProperTensorUnitHom : IsProper (𝟙_ (Over (Spec (.of K)))).hom := by
  rw [Over.tensorUnit_hom]
  -- `infer_instance` fails on the post-`rw` goal (the failed synthesis attempt on the
  -- pre-`rw` goal is cached); `inferInstanceAs` re-elaborates the type and succeeds.
  exact inferInstanceAs (IsProper (𝟙 _))

/-- The structural morphism of the monoidal unit of `Over (Spec K)` is the identity, hence
geometrically integral. -/
instance geometricallyIntegralTensorUnitHom :
    GeometricallyIntegral (𝟙_ (Over (Spec (.of K)))).hom := by
  rw [Over.tensorUnit_hom]
  -- as above: `inferInstanceAs` re-elaborates the type, which `infer_instance` does not.
  exact inferInstanceAs (GeometricallyIntegral (𝟙 _))

/-- The **trivial abelian variety** over `K`: the scheme `Spec K`, structural morphism the
identity, with the group structure of the monoidal unit of `Over (Spec K)`. -/
noncomputable def trivial : AbelianVariety K :=
  ofGeometricallyIntegral (𝟙_ (Over (Spec (.of K))))

@[simp]
lemma trivial_toOver : (trivial K).toOver = 𝟙_ (Over (Spec (.of K))) :=
  ofGeometricallyIntegral_toOver _

/-- The underlying scheme of the trivial abelian variety is `Spec K`. -/
@[simp]
lemma trivial_toScheme : (trivial K).toScheme = Spec (.of K) := by
  simp only [toScheme, trivial_toOver, Over.tensorUnit_left]

/-- The trivial abelian variety is zero-dimensional: the topological Krull dimension of `Spec K` is
`ringKrullDim K = 0` for a field `K`. -/
@[simp]
lemma trivial_dim : (trivial K).dim = 0 := by
  rw [dim_def, trivial_toScheme, ← ringKrullDim_eq_zero_of_field K,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim K]
  -- the topological space of `Spec (.of K)` is `PrimeSpectrum K` (`Scheme.Spec_carrier`)
  rfl

/-- The scheme over `Spec K` underlying the trivial abelian variety is terminal: it is the monoidal
unit of `Over (Spec K)`. -/
noncomputable def isTerminalTrivialToOver : IsTerminal (trivial K).toOver :=
  isTerminalTensorUnit.ofIso (eqToIso (trivial_toOver K).symm)

variable {K}

/-- The unique homomorphism from an abelian variety `A` to the trivial abelian variety: the constant
map to the origin, underlain by the terminal projection `A.toScheme → Spec K`. -/
noncomputable def toTrivial (A : AbelianVariety K) : A ⟶ trivial K :=
  Hom.mk' ((isTerminalTrivialToOver K).from A.toOver)
    ((isTerminalTrivialToOver K).hom_ext _ _) ((isTerminalTrivialToOver K).hom_ext _ _)

namespace Hom

/-- The morphism over `Spec K` underlying `toTrivial` is the terminal projection. -/
@[simp]
lemma toOverHom_toTrivial (A : AbelianVariety K) :
    toOverHom (toTrivial A) = (isTerminalTrivialToOver K).from A.toOver :=
  toOverHom_mk' _ _ _

end Hom

/-- Any homomorphism to the trivial abelian variety is the constant map `toTrivial`. -/
lemma eq_toTrivial {A : AbelianVariety K} (m : A ⟶ trivial K) : m = toTrivial A :=
  Hom.ext <| congrArg Over.Hom.left <|
    (isTerminalTrivialToOver K).hom_ext (Hom.toOverHom m) (Hom.toOverHom (toTrivial A))

/-- Homomorphisms into the trivial abelian variety are unique: it is a terminal object. -/
noncomputable instance uniqueHomToTrivial (A : AbelianVariety K) : Unique (A ⟶ trivial K) where
  default := toTrivial A
  uniq := eq_toTrivial

/-- The trivial abelian variety is a terminal object of the category of abelian varieties over `K`:
every abelian variety has a unique homomorphism to it. -/
noncomputable def isTerminalTrivial : Limits.IsTerminal (trivial K) :=
  Limits.IsTerminal.ofUnique _

end AbelianVariety

end AlgebraicGeometry

end TauCeti
