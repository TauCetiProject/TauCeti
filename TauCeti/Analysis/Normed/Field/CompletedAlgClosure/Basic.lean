/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import TauCeti.Analysis.Normed.Field.Completion
public import TauCeti.Topology.MetricSpace.Ultra.Completion

import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.Analysis.Normed.Field.Approximation

/-!
# The completed algebraic closure of a complete non-archimedean field

Let `K` be a field complete for a nontrivial ultrametric absolute value. Its algebraic closure
`K^alg` carries the spectral norm, the unique power-multiplicative extension of the absolute value
of `K` (Mathlib's `spectralNorm_unique`), and its uniform completion `C` is a complete normed
field and normed `K`-algebra. This file defines both and proves that the separable closure of
`K` is dense in `K^alg` and in `C`. The completion `C` is nontrivially normed and ultrametric by
the instances for completions of nontrivially normed fields and of ultrametric spaces.

## Main definitions

* `TauCeti.SpectralAlgClosure K`: a type synonym of `AlgebraicClosure K` whose normed-field and
  normed-algebra structures are Mathlib's `spectralNorm.normedField` and
  `spectralNorm.normedAlgebra`. The synonym keeps the spectral norm from becoming an instance on
  `AlgebraicClosure K` itself.
* `TauCeti.SpectralAlgClosure.algEquiv K`: the canonical `K`-algebra isomorphism
  `AlgebraicClosure K ≃ₐ[K] SpectralAlgClosure K`.
* `TauCeti.CompletedAlgClosure K`: the field `C`, the uniform completion of
  `SpectralAlgClosure K`.

## Main results

* `TauCeti.SpectralAlgClosure.dense_separableClosure`: `K^sep` is dense in `K^alg`.
* `TauCeti.CompletedAlgClosure.denseRange_separableClosure`: `K^sep` is dense in `C`.

## Implementation notes

The density statements specialise `TauCeti.dense_separableClosure` and
`TauCeti.denseRange_separableClosure_completion`, which hold for any algebraically closed normed
field algebraic over a nontrivially normed field.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
-/

public section

noncomputable section

namespace TauCeti

universe u

/-- The algebraic closure `K^alg` of a field `K`, as a type synonym of `AlgebraicClosure K`. For a
complete non-archimedean `K` it carries the spectral norm, the unique power-multiplicative
extension of the absolute value of `K`. The synonym keeps that norm from becoming an instance on
`AlgebraicClosure K` itself. -/
@[expose] def SpectralAlgClosure (K : Type u) [Field K] : Type u := AlgebraicClosure K

namespace SpectralAlgClosure

section Field

variable (K : Type u) [Field K]

/-- The field structure of `AlgebraicClosure K`. -/
instance instField : Field (SpectralAlgClosure K) :=
  inferInstanceAs (Field (AlgebraicClosure K))

/-- The `K`-algebra structure of `AlgebraicClosure K`. -/
instance instAlgebra : Algebra K (SpectralAlgClosure K) :=
  inferInstanceAs (Algebra K (AlgebraicClosure K))

/-- `K^alg` is algebraic over `K`. -/
instance instIsAlgebraic : Algebra.IsAlgebraic K (SpectralAlgClosure K) :=
  inferInstanceAs (Algebra.IsAlgebraic K (AlgebraicClosure K))

/-- `K^alg` is algebraically closed. -/
instance instIsAlgClosed : IsAlgClosed (SpectralAlgClosure K) :=
  inferInstanceAs (IsAlgClosed (AlgebraicClosure K))

/-- `K^alg` is an algebraic closure of `K`. -/
instance instIsAlgClosure : IsAlgClosure K (SpectralAlgClosure K) :=
  inferInstanceAs (IsAlgClosure K (AlgebraicClosure K))

/-- The canonical `K`-algebra isomorphism from `AlgebraicClosure K` to its type synonym
`SpectralAlgClosure K`, the identity on the underlying type. -/
def algEquiv : AlgebraicClosure K ≃ₐ[K] SpectralAlgClosure K :=
  AlgEquiv.refl

/-- `algEquiv K` is the identity of the underlying type of `AlgebraicClosure K`. -/
theorem algEquiv_apply (x : AlgebraicClosure K) : algEquiv K x = x :=
  (rfl)

/-- The inverse of `algEquiv K` is the identity of the underlying type of `AlgebraicClosure K`. -/
theorem algEquiv_symm_apply (x : SpectralAlgClosure K) : (algEquiv K).symm x = x :=
  (rfl)

/-- `σ ↦ algEquiv K ∘ σ ∘ (algEquiv K)⁻¹` is continuous for the Krull topologies: it is the
identity of the underlying type of `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`, and both Krull
topologies are defined from the same intermediate fields. -/
theorem continuous_autCongr_algEquiv : Continuous (AlgEquiv.autCongr (algEquiv K)) :=
  continuous_id

end Field

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The spectral norm on `K^alg`, for `K` complete for a nontrivial ultrametric absolute value. -/
instance instNormedField : NormedField (SpectralAlgClosure K) :=
  spectralNorm.normedField K (SpectralAlgClosure K)

/-- `K^alg` with the spectral norm is a normed `K`-algebra. -/
instance instNormedAlgebra : NormedAlgebra K (SpectralAlgClosure K) :=
  spectralNorm.normedAlgebra K (SpectralAlgClosure K)

/-- The spectral norm on `K^alg` is nontrivial, since it extends the norm of `K`. -/
instance instNontriviallyNormedField : NontriviallyNormedField (SpectralAlgClosure K) :=
  spectralNorm.nontriviallyNormedField K (SpectralAlgClosure K)

/-- The spectral norm on `K^alg` is ultrametric. -/
instance instIsUltrametricDist : IsUltrametricDist (SpectralAlgClosure K) :=
  IsUltrametricDist.of_normedAlgebra K

/-- The norm of `K^alg` is the spectral norm. -/
theorem norm_def (x : SpectralAlgClosure K) : ‖x‖ = spectralNorm K (SpectralAlgClosure K) x :=
  rfl

/-- **`K^sep` is dense in `K^alg`** (de Jong–van der Put, §3.6). -/
theorem dense_separableClosure :
    Dense (separableClosure K (SpectralAlgClosure K) : Set (SpectralAlgClosure K)) :=
  TauCeti.dense_separableClosure K (SpectralAlgClosure K)

end SpectralAlgClosure

/-- The completed algebraic closure `C` of a complete non-archimedean field `K`: the uniform
completion of `K^alg` for the spectral norm, a complete normed field and normed `K`-algebra. For
`K = ℚ_p` this is the construction of Mathlib's `PadicComplex p`. -/
abbrev CompletedAlgClosure (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] : Type u :=
  UniformSpace.Completion (SpectralAlgClosure K)

namespace CompletedAlgClosure

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **`K^sep` is dense in `C`**. -/
theorem denseRange_separableClosure :
    DenseRange fun x : separableClosure K (SpectralAlgClosure K) ↦
      ((x : SpectralAlgClosure K) : CompletedAlgClosure K) :=
  denseRange_separableClosure_completion K (SpectralAlgClosure K)

end CompletedAlgClosure

end TauCeti
