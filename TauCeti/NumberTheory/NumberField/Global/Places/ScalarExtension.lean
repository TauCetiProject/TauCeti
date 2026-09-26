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

These are the local vector spaces `K_v ⊗[K] V` attached to a global vector space `V`. They are
shared by the localization of quadratic forms at the places of `K` and by weak approximation of
vectors at finite and real places, so that both speak about the same local spaces. Their finite
dimensions are preserved by each scalar extension.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.finrank_FiniteScalarExtension`,
  `TauCeti.finrank_atRealPlace`, and
  `NumberField.InfinitePlace.finrank_ComplexScalarExtension`: scalar extension preserves finite
  dimension at finite, real, and complex places.
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

/-- The finite rank of `V` is unchanged by extension to a finite-place completion. -/
@[simp high]
theorem finrank_FiniteScalarExtension [NumberField K] [FiniteDimensional K V]
    (v : HeightOneSpectrum (𝓞 K)) :
    Module.finrank (v.adicCompletion K) (v.FiniteScalarExtension (V := V)) =
      Module.finrank K V := by
  simp

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

/-- The finite rank of `V` is unchanged by extension through a complex embedding. -/
@[simp]
theorem finrank_ComplexScalarExtension [FiniteDimensional K V]
    (w : InfinitePlace K) :
    Module.finrank ℂ (w.ComplexScalarExtension (V := V)) =
      Module.finrank K V := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  simp

end NumberField.InfinitePlace

namespace TauCeti

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The finite rank of `V` is unchanged by extension through a real place. -/
@[simp]
theorem finrank_atRealPlace [FiniteDimensional K V]
    (w : {w : InfinitePlace K // w.IsReal}) :
    Module.finrank ℝ (RealScalarExtension (V := V) w) =
      Module.finrank K V := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  simp

end TauCeti
