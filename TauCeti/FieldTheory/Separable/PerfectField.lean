/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# Finite extensions with a perfect top field are separable

A finite extension `L / K` whose top field `L` is perfect is separable. Over the separable closure
`S` of `K` in `L`, the field `L` is finite and purely inseparable, so it has an exponent `e`: every
`q ^ e`-th power of `L` lies in `S`, where `q` is the exponential characteristic. When `L` is
perfect every element of `L` is such a power, so `S = L`.

Finiteness cannot be dropped: the perfect closure of `𝔽_p(t)` is perfect but purely inseparable
over `𝔽_p(t)`. Mathlib's `Algebra.IsAlgebraic.isSeparable_of_perfectField` is the statement for a
perfect base field; here only the top field is perfect.

In particular a finite extension whose top field is algebraically closed is Galois
(`IsGalois.of_isAlgClosed_top`): it is separable, and normal because every polynomial splits in an
algebraically closed field.
-/

public section

namespace Algebra.IsSeparable

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- A finite field extension whose top field is perfect is separable. -/
theorem of_perfectField_top [PerfectField L] [FiniteDimensional K L] : Algebra.IsSeparable K L := by
  obtain ⟨q, _⟩ := ExpChar.exists K
  have : ExpChar L q := expChar_of_injective_algebraMap (algebraMap K L).injective q
  -- `L` is finite purely inseparable over the separable closure, so it has an exponent `e`.
  obtain ⟨e, he⟩ := (IsPurelyInseparable.hasExponent_iff' (separableClosure K L) L q).1
    inferInstance
  rw [← separableClosure.eq_top_iff]
  refine _root_.eq_top_iff.2 fun x _ ↦ ?_
  -- As `L` is perfect, `x` is a `q ^ e`-th power, hence lies in the separable closure.
  obtain ⟨y, rfl⟩ := (iterateFrobeniusEquiv L q e).surjective x
  obtain ⟨s, hs⟩ := he y
  rw [iterateFrobeniusEquiv_def, ← hs]
  exact s.property

end Algebra.IsSeparable

/-- A finite field extension whose top field is algebraically closed is Galois. -/
theorem IsGalois.of_isAlgClosed_top (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    [FiniteDimensional K L] : IsGalois K L :=
  have : Algebra.IsSeparable K L := .of_perfectField_top K L
  have : IsAlgClosure K L := ⟨inferInstance, Algebra.IsAlgebraic.of_finite K L⟩
  isGalois_iff.2 ⟨inferInstance, IsAlgClosure.normal K L⟩
