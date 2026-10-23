/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.LocalRing.Module

/-!
# Detecting formal unramifiedness on field-valued fibres

A finite-type algebra is formally unramified if all its base changes to fields are formally
unramified. This criterion passes from fibre computations to relative unramifiedness without
requiring flatness or finite presentation.

The proof uses finite generation of Kähler differentials, their base-change equivalence
`KaehlerDifferential.tensorKaehlerEquivBase`, and the residue-field description of module support
`Module.mem_support_iff_nontrivial_residueField_tensorProduct`.

`Algebra.IsUnramifiedIn.formallyUnramified_fiber` gives the converse comparison at one prime:
unramifiedness at every prime over `p` implies formal unramifiedness of the fibre over `p`,
without a finiteness assumption.

## References

* The Stacks Project, Tag 02G8 (the fibre criterion for unramified morphisms).
-/

public section

open scoped TensorProduct

namespace Algebra

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- If an algebra is unramified at every prime over `p`, its fibre over `p` is formally
unramified. No finiteness hypothesis is needed. -/
theorem IsUnramifiedIn.formallyUnramified_fiber {p : Ideal R} [p.IsPrime]
    (h : IsUnramifiedIn S p) : FormallyUnramified p.ResidueField (p.Fiber S) := by
  -- Use the right-factor algebra structure so that contraction to `S` and its lies-over
  -- instances apply; its algebra map is `includeRight`, as identified explicitly below.
  let : Algebra S (p.Fiber S) := TensorProduct.rightAlgebra
  apply formallyUnramified_iff_forall.mpr
  intro q
  let Q := q.asIdeal.under S
  have : Q.IsPrime := inferInstance
  have : Q.LiesOver p := inferInstance
  have : IsUnramifiedAt R Q := h Q inferInstance inferInstance
  apply IsUnramifiedAt.residueField p Q q.asIdeal
  dsimp only [Q]
  rw [Ideal.under_def, TensorProduct.algebraMap_eq_includeRight, AlgHom.toRingHom_eq_coe]

/-- A finite-type algebra is formally unramified if every base change to a field is formally
unramified. No flatness assumption is required. -/
theorem FormallyUnramified.of_formallyUnramified_baseChange_field [FiniteType R S]
    (h : ∀ (K : Type v) [Field K] [Algebra R K],
      FormallyUnramified K (K ⊗[R] S)) : FormallyUnramified R S := by
  constructor
  apply (Module.support_eq_empty_iff (R := S) (M := Ω[S⁄R])).mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q
  let K := q.asIdeal.ResidueField
  let : Algebra S (K ⊗[R] S) := TensorProduct.rightAlgebra
  have : FormallyUnramified K (K ⊗[R] S) := h K
  have : Subsingleton (K ⊗[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R K S (K ⊗[R] S)).subsingleton
  have : Subsingleton (K ⊗[S] Ω[S⁄R]) :=
    (_root_.TensorProduct.mapOfCompatibleSMul_surjective S R K K Ω[S⁄R]).subsingleton
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact not_nontrivial_iff_subsingleton.mpr this

end Algebra
