/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.Lattice
import TauCeti.Algebra.Lie.Sl2.RangeKer
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Conjugate

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

/-- Every Chevalley root vector acts with integral divided powers on any additive subgroup
stable under the simple-generator Kostant form. -/
theorem dividedPower_chevalleySystem_apply_mem (M : AddSubgroup V)
    (hM : ∀ u ∈ t.kostantForm ht, ∀ v ∈ M,
      representation ℚ (t.lieAlgebra ht) V u v ∈ M)
    (γ : Fin t.numRoots) (n : ℕ) {v : V} (hv : v ∈ M) :
    Associative.dividedPower n (toEnd ℚ (t.lieAlgebra ht) V
      (t.chevalleySystem ht γ)) v ∈ M := by
  let b := t.lieBasis ht
  let ρ := representation ℚ (t.lieAlgebra ht) V
  have hstable : ∀ u ∈ UniversalEnvelopingAlgebra.kostantForm b.rootGenerator b.h,
      ∀ v ∈ M, ρ u v ∈ M := by
    simpa only [kostantForm_def, LieAlgebra.Basis.kostantForm_def] using hM
  -- Root induction reduces integrality to negation, simple roots, and simple Weyl transforms.
  have hall : ∀ γ, ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (t.chevalleySystem ht γ))) • v ∈ M := by
    intro γ
    refine chevalleySystem_induction
      (p := fun z ↦ ∀ n, ∀ v ∈ M,
        Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) • v ∈ M)
      ?_ ?_ ?_ γ
    · intro z hz n
      simpa only [map_neg] using Associative.dividedPower_neg_smul_mem
        (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M (hz n)
    · intro i n v hv
      simpa only [LieAlgebra.Basis.rootGenerator_inl, Module.End.smul_def, b] using
        dividedPower_apply_mem_of_kostantForm_apply_mem b.rootGenerator b.h ρ
          hstable (.inl i) n hv
    · intro i z hz n
      -- Match the root-indexed triple with the positive/negative simple-generator family.
      have he := (t.isSl2Triple_chevalleySystem ht
        (t.simpleIndex ht i)).isNilpotent_toEnd_e (K := ℚ) (M := V)
      have hf := (t.isSl2Triple_chevalleySystem ht
        (t.simpleIndex ht i)).isNilpotent_toEnd_f (K := ℚ) (M := V)
      have st : IsSl2Triple
          ((LieAlgebra.IsKilling.coroot (t.rootEquiv ht (t.simpleIndex ht i) :
            Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) : t.cartanSubalgebra ht) :
            t.lieAlgebra ht) (b.rootGenerator (.inl i)) (b.rootGenerator (.inr i)) := by
        simpa only [LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr, b,
          chevalleySystem_simpleIndex, chevalleySystem_reflectionPerm_simpleIndex] using
          t.isSl2Triple_chevalleySystem ht (t.simpleIndex ht i)
      have hai : IsNilpotent (ad ℚ (t.lieAlgebra ht) (b.rootGenerator (.inl i))) := by
        simpa only [LieAlgebra.Basis.rootGenerator_inl, b, chevalleySystem_simpleIndex] using
          t.isNilpotent_ad_chevalleySystem ht (t.simpleIndex ht i)
      have haj : IsNilpotent (ad ℚ (t.lieAlgebra ht) (b.rootGenerator (.inr i))) := by
        simpa only [LieAlgebra.Basis.rootGenerator_inr, b,
          chevalleySystem_reflectionPerm_simpleIndex] using
          t.isNilpotent_ad_chevalleySystem ht
            ((t.simplyConnectedRootDatum ht).reflectionPerm
              (t.simpleIndex ht i) (t.simpleIndex ht i))
      simpa only [LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr, b,
        chevalleySystem_simpleIndex, chevalleySystem_reflectionPerm_simpleIndex] using
        dividedPower_weylAut_smul_mem b.rootGenerator b.h ρ M hstable
          (i := .inl i) (j := .inr i)
          (by simpa only [LieAlgebra.Basis.rootGenerator_inl, b, ρ, representation_ι,
            chevalleySystem_simpleIndex] using he)
          (by simpa only [LieAlgebra.Basis.rootGenerator_inr, b, ρ, representation_ι,
            chevalleySystem_reflectionPerm_simpleIndex] using hf) st hai.exists_pow_apply_eq_zero
          haj.exists_pow_apply_eq_zero n (hz n)
  simpa only [ρ, representation_ι, Module.End.smul_def] using hall γ n v hv

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
  apply kostantForm_chevalleySystem_apply_mem_of_isNilpotent
    (representation ℚ (t.lieAlgebra ht) V) M ?_ ?_ u hu v hv
  · simpa only [kostantForm_def, LieAlgebra.Basis.kostantForm_def] using hM
  · intro i
    rcases i with i | i
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
