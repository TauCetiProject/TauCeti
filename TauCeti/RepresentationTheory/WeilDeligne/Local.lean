/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Topology
public import TauCeti.RepresentationTheory.WeilDeligne.Basic

/-!
# Raw Weil–Deligne parameters of a local field

This file specializes the raw Weil–Deligne parameters of
`TauCeti.RepresentationTheory.WeilDeligne.Basic` to the local Weil group `W_K` of a
nonarchimedean local field `K`, with its degree `TauCeti.ClassFieldTheory.weilDegree K`
(normalized so that arithmetic Frobenius lifts have degree `1`,
`TauCeti.ClassFieldTheory.weilDegree_eq_ofAdd_one_iff`) and `q` the cardinality of the residue
field.

## Main definitions

* `TauCeti.LocalWeilDeligneParameter K E V`: the raw Weil–Deligne parameters of the local Weil
  group of `K` on `V`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §4.1.
-/

public section

namespace TauCeti

open _root_.ValuativeRel in
/-- **Raw Weil–Deligne parameters of a nonarchimedean local field** `K`: the parameters of the
local Weil group `W_K` with its Weil topology and arithmetic degree, and `q` the cardinality of the
residue field of `K`. -/
abbrev LocalWeilDeligneParameter (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (E V : Type*) [Field E] [CharZero E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] :=
  WeilDeligneParameter E (ClassFieldTheory.WeilGroup K) V (ClassFieldTheory.weilDegree K)
    (Nat.card 𝓀[K])

end TauCeti
