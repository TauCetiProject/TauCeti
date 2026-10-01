/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Cycles and homology of homological complexes of modules

For a homological complex `K` of modules over a ring, the inclusion of the degree-`n` cycles into
`K.X n` is injective and the class map from the cycles onto the degree-`n` homology is surjective.
These are the elementwise forms of the facts that `K.iCycles n` is a monomorphism and
`K.homologyπ n` is an epimorphism.  Conversely, an element of `K.X n` killed by the differential
is a cycle, `TauCeti.moduleCatCyclesMk`.  This constructor directly returns
an element of `K.cycles n` for modules over a ring in any universe, whereas Mathlib's
`HomologicalComplex.cyclesMk` returns an element of `(forget₂ C Ab).obj (K.cycles n)`.

Use `TauCeti.moduleCatCyclesMk K x m hm hx` to construct a cycle and
`TauCeti.iCycles_moduleCatCyclesMk K n x m hm hx` to recover its underlying element.
-/

public section

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c) (n : ι)

/-- The inclusion of the degree-`n` cycles of a homological complex of modules into its degree-`n`
term is injective. -/
lemma moduleCat_iCycles_injective : Function.Injective (K.iCycles n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The class map from the degree-`n` cycles of a homological complex of modules onto its
degree-`n` homology is surjective. -/
lemma moduleCat_homologyπ_surjective : Function.Surjective (K.homologyπ n) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

end HomologicalComplex

namespace TauCeti

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : _root_.HomologicalComplex (ModuleCat R) c) (n : ι)

variable {n} in
/-- An element `x` of `K.X n` killed by the differential `K.d n m` out of degree `n`, as a cycle
of degree `n`. -/
noncomputable def moduleCatCyclesMk (x : K.X n) (m : ι) (hm : c.next n = m)
    (hx : K.d n m x = 0) : K.cycles n :=
  (K.sc n).moduleCatCyclesIso.inv ⟨x, by subst hm; exact hx⟩

/-- The cycle `TauCeti.moduleCatCyclesMk K x` has underlying element `x`. -/
@[simp]
lemma iCycles_moduleCatCyclesMk (x : K.X n) (m : ι) (hm : c.next n = m)
    (hx : K.d n m x = 0) : K.iCycles n (moduleCatCyclesMk K x m hm hx) = x :=
  (K.sc n).moduleCatCyclesIso_inv_iCycles_apply _

end TauCeti
