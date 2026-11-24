/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.FieldDivision
import TauCeti.RingTheory.Localization.PrincipalIdealRing

/-!
# Laurent polynomial rings over a field are principal ideal domains

Over a field `K`, the polynomial ring `K[X]` is a principal ideal domain, and `K[T;T⁻¹]` is the
localization of `K[X]` away from `X`. Since localizations of principal ideal rings are principal
ideal rings (`IsLocalization.isPrincipalIdealRing`), `K[T;T⁻¹]` is a principal ideal domain (hence
a Dedekind domain and an integrally closed domain).

## Main declarations

* `LaurentPolynomial.instIsPrincipalIdealRing`: `K[T;T⁻¹]` is a principal ideal ring for every
  field `K`.
-/

public section

open Polynomial
open scoped LaurentPolynomial

namespace LaurentPolynomial

/-- Over a field `K`, the Laurent polynomial ring `K[T;T⁻¹]` is a principal ideal domain, being the
localization of `K[X]` away from `X`. -/
instance instIsPrincipalIdealRing (K : Type*) [Field K] : IsPrincipalIdealRing K[T;T⁻¹] :=
  IsLocalization.isPrincipalIdealRing (Submonoid.powers (X : K[X])) K[T;T⁻¹]

end LaurentPolynomial
