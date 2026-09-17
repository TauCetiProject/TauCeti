/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.NumberTheory.NumberField.FinitePlace

/-!
# Scalar extension at places of a number field

This file defines the scalar extension of a vector space over a number field to a finite
completion, to `ℝ` through a real place, and to `ℂ` through a chosen infinite-place embedding.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped TensorProduct

universe u v

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar extension of `V` to the finite completion of `K` at `v`. -/
abbrev FiniteScalarExtension [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :=
  v.adicCompletion K ⊗[K] V

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar extension of `V` to `ℝ` through the embedding belonging to a real place. -/
abbrev RealScalarExtension (w : {w : InfinitePlace K // w.IsReal}) :=
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  ℝ ⊗[K] V

end TauCeti

namespace NumberField.InfinitePlace

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar extension of `V` to `ℂ` through the chosen embedding of an infinite place. -/
abbrev ComplexScalarExtension (w : InfinitePlace K) :=
  letI : Algebra K ℂ := w.embedding.toAlgebra
  ℂ ⊗[K] V

end NumberField.InfinitePlace
