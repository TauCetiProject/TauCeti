/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.Lattice
import TauCeti.Algebra.Lie.Sl2.RangeKer

/-!
# All-root admissibility of Kostant-stable lattices

In a finite-dimensional rational module of the pinned Lie algebra, stability under the
simple-generator Kostant form implies stability under divided powers of every named Chevalley
root vector. In particular the full-weight lattice is admissible for the all-root Kostant form,
not merely for the simple-generator form used to construct it.

The argument combines `DynkinType.chevalleySystem_induction` with
`UniversalEnvelopingAlgebra.dividedPower_weylAut_smul_mem`: simple Weyl elements and their
inverses preserve a Kostant-stable subgroup. Nilpotence follows from the represented sl₂
triples, without requiring a weight decomposition of the module. No equality of the two
integral subrings of the universal enveloping algebra is asserted.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieModule
open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable (t : DynkinType) (ht : t.Valid)
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  [LieRingModule (t.lieAlgebra ht) V] [LieModule ℚ (t.lieAlgebra ht) V]
  [FiniteDimensional ℚ V]

/-- The all-root Kostant form preserves every subgroup stable under the simple-generator
form. The Cartan generators are unchanged. -/
theorem kostantForm_chevalleySystem_apply_mem (M : AddSubgroup V)
    (hM : ∀ u ∈ t.kostantForm ht, ∀ v ∈ M,
      representation ℚ (t.lieAlgebra ht) V u v ∈ M)
    {u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht)}
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (t.chevalleySystem ht) (t.lieBasis ht).h)
    {v : V} (hv : v ∈ M) :
    representation ℚ (t.lieAlgebra ht) V u v ∈ M := by
  refine kostantForm_chevalleySystem_apply_mem_of_isNilpotent
    (representation ℚ (t.lieAlgebra ht) V) M
    (by simpa only [kostantForm_def, LieAlgebra.Basis.kostantForm_def] using hM) ?_ u hu v hv
  rintro (i | i)
  · simpa only [representation_ι] using
      ((t.lieBasis ht).isSl2Triple_rootGenerator i).isNilpotent_toEnd_e (K := ℚ) (M := V)
  · simpa only [representation_ι] using
      ((t.lieBasis ht).isSl2Triple_rootGenerator i).isNilpotent_toEnd_f (K := ℚ) (M := V)

/-- The full-weight lattice is preserved by the all-root Kostant form of the pinned
Chevalley system. -/
theorem kostantForm_chevalleySystem_apply_mem_scLattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht)}
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (t.chevalleySystem ht) (t.lieBasis ht).h)
    {v : t.scModule ht} (hv : v ∈ t.scLattice ht) :
    representation ℚ (t.lieAlgebra ht) (t.scModule ht) u v ∈ t.scLattice ht :=
  t.kostantForm_chevalleySystem_apply_mem ht (t.scLattice ht).toAddSubgroup
    (fun _ hu _ hv ↦ t.representation_mem_scLattice ht hu hv) hu hv

end

end TauCeti.DynkinType
