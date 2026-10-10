/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# The real algebra structure on `E →L[𝕜] E`

Real continuous functional calculus on an operator algebra over an `RCLike` field needs the
algebra to be an `ℝ`-algebra, compatibly with its `𝕜`-action.  Mathlib does not register that:
`Module ℝ (E →L[𝕜] E)` is not even inferable for a general `RCLike 𝕜`, so every consumer of the
modulus, the polar decomposition and the angle operators has been carrying

```text
[Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
```

as hypotheses.  They are not hypotheses.  They are restriction of scalars along
`algebraMap ℝ 𝕜`, and this file registers them.

## Why these are `def`s and not instances

They agree with everything already in place: `Algebra.complexToReal` — which is what
`Algebra ℝ (E →L[ℂ] E)` already resolves to — *is* `RestrictScalars.algebra ℝ ℂ`, and
`RestrictScalars.algebra ℝ ℝ` reduces to `ContinuousLinearMap.algebra`.  Both facts are checked
by `rfl`, so there is no diamond.

Registering them globally is nevertheless wrong, and was tried on 2026-09-03.  The damage is
not a diamond, it is elaboration.  With `SMul ℝ (E →L[𝕜] E)` in scope, Lean's `•` elaborator
prefers the homogeneous reading and *discards* a scalar coercion the author wrote:

```text
((r : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E     elaborates to     r • ContinuousLinearMap.id 𝕜 E
```

with `r : ℝ`.  The two are propositionally equal and definitionally equal, but not the same
term, so every `simp` lemma about `𝕜`-scalar multiplication of operators silently stops firing
in files that never asked for a real algebra structure.  Three proofs in
`Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean` broke that way.

So a consumer activates them deliberately:

```lean
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower
```

The low priority keeps Mathlib's answer at `𝕜 = ℝ` and `Algebra.complexToReal` at `𝕜 = ℂ`, so
activating them changes nothing at the two concrete fields; they only fill the gap at an
abstract `RCLike 𝕜`.  A *definition* elaborated under them — the angle operators of
`DavisKahan/Geometry/Angle/OperatorAngleGeneric.lean`, say — carries them in its body, so its
consumers need nothing.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: none.  Written directly here, 2026-09-03, to remove the two-instance
  hypothesis block from the scalar-generic operator API.
* Extraction class: **new**.  It depends on nothing outside Mathlib.
* Namespace: `ContinuousLinearMap`, matching the object it structures.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none**.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **The operator algebra over an `RCLike` field is a real algebra**, by restriction of
scalars along `algebraMap ℝ 𝕜`.  Not an instance; see the module docstring. -/
@[expose, instance_reducible]
noncomputable def realAlgebra : Algebra ℝ (E →L[𝕜] E) :=
  RestrictScalars.algebra ℝ 𝕜 (E →L[𝕜] E)

attribute [local instance 100] realAlgebra

omit [CompleteSpace E] in
/-- The real action on operators factors through the `𝕜`-action.  Not an instance; see the
module docstring. -/
theorem realIsScalarTower : IsScalarTower ℝ 𝕜 (E →L[𝕜] E) :=
  RestrictScalars.isScalarTower ℝ 𝕜 (E →L[𝕜] E)

attribute [local instance 100] realIsScalarTower

/-! ## What this already unlocks

At `𝕜 = ℂ` these two are the whole gap between Mathlib's complex `C⋆`-algebra structure on
`E →L[ℂ] E` and its real continuous functional calculus: with them active the calculus is found
by synthesis, with no `scoped` instance and no explicit term.  The general `RCLike` case is
`ForTauCeti/Analysis/RCLike/ScalarTransportFunctionalCalculus.lean`, which transports this one.

The `example` is deliberate: it adds no name and fails loudly if the chain ever breaks. -/

example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    ContinuousFunctionalCalculus ℝ (F →L[ℂ] F) IsSelfAdjoint := inferInstance

end ContinuousLinearMap
