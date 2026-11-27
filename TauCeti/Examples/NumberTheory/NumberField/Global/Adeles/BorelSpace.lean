/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Countable
public import TauCeti.NumberTheory.NumberField.Global.Adeles.BorelSpace

/-!
# Checks for the Borel structure of the adeles

Checks of the second countability and Borel structure of the adeles of a number field `K`:

* the product of a Borel set of infinite adeles and a Borel set of finite adeles is a Borel set
  of adeles, since the adeles carry the product σ-algebra
  (`NumberField.AdeleRing.instMeasurableSpace`), which is their Borel σ-algebra
  (`NumberField.AdeleRing.instBorelSpace`);
* `GL₀(𝔸_K)` is a singleton, and it is second countable.
-/

public section

open MeasureTheory NumberField IsDedekindDomain

namespace TauCeti.Examples

variable (K : Type*) [Field K] [NumberField K]

/-- A product of a Borel set of infinite adeles and a Borel set of finite adeles is a Borel set of
adeles. -/
example {s : Set (InfiniteAdeleRing K)} {t : Set (FiniteAdeleRing (𝓞 K) K)}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (show Set (AdeleRing (𝓞 K) K) from s ×ˢ t) :=
  hs.prod ht

/-- `GL₀(𝔸_K)` is a singleton. -/
example : Subsingleton (GL (Fin 0) (AdeleRing (𝓞 K) K)) :=
  inferInstance

/-- `GL₀(𝔸_K)` is second countable. -/
example : SecondCountableTopology (GL (Fin 0) (AdeleRing (𝓞 K) K)) :=
  inferInstance

end TauCeti.Examples
