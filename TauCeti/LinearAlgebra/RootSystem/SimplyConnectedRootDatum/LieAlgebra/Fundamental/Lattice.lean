/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Lattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.Basic

/-!
# The admissible lattices of the fundamental modules

For a valid Dynkin type `t` and a Bourbaki node `i`, the **fundamental lattice**
`TauCeti.DynkinType.fundamentalLattice t ht i` is the orbit `U_ℤ · v⁺ᵢ` of the highest weight
vector of the fundamental module `L(ϖᵢ)` under the simple-generator Kostant form
`TauCeti.DynkinType.kostantForm` of the pinned rational Lie algebra. It is the integral structure
on `L(ϖᵢ)` from which the root subgroups and the torus of the simply connected Chevalley group act
over every commutative ring.

This file proves the properties that make it an admissible lattice in the sense of Steinberg,
Chapter 2, and Humphreys, §27:

* it is stable under the Kostant form, by construction;
* it is the `ℤ`-span of the lowering words `fⱼ₁⁽ⁿ¹⁾ ⋯ fⱼₖ⁽ⁿᵏ⁾ v⁺ᵢ` (Steinberg's `U_ℤ v = U⁻_ℤ v`);
* it is a full lattice: finitely generated over `ℤ`, and spanning `L(ϖᵢ)` over `ℚ`;
* it lies in the span of the integral weight spaces of the Cartan generators.

The last two are exactly the inputs of `TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis`,
which therefore gives `fundamentalLattice t ht i` a basis of weight vectors.

## Main declarations

* `TauCeti.DynkinType.fundamentalLattice`: the orbit `U_ℤ · v⁺ᵢ` in `L(ϖᵢ)`.
* `TauCeti.DynkinType.representation_mem_fundamentalLattice`: its stability under the Kostant form.
* `TauCeti.DynkinType.fundamentalLattice_eq_span_loweringWord`: its description by lowering words.
* `TauCeti.DynkinType.instIsLatticeFundamentalLattice`: it is a full lattice in `L(ϖᵢ)`.
* `TauCeti.DynkinType.mem_iSup_jointWeightSpace_of_mem_fundamentalLattice`: it lies in the span of
  the integral weight spaces.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2, Corollary 1 to Theorem 2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §27.1.
-/

public section

namespace TauCeti.DynkinType

open Set _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The fundamental lattice** `U_ℤ · v⁺ᵢ`: the integral orbit of the highest weight vector of the
fundamental module `L(ϖᵢ)` under the simple-generator Kostant form of the pinned rational Lie
algebra, acting through the enveloping-algebra representation of `L(ϖᵢ)`. -/
def fundamentalLattice (i : Fin t.rank) : Submodule ℤ (t.fundamentalModule ht i) :=
  (t.lieBasis ht).highestWeightLattice (t.fundamentalWeight ht i)

/-- The fundamental lattice is the represented orbit of the highest weight vector. -/
theorem fundamentalLattice_def (i : Fin t.rank) :
    t.fundamentalLattice ht i = Subring.orbitOfRep (t.kostantForm ht)
      (representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i))
      {t.fundamentalModuleGenerator ht i} := by
  rw [fundamentalLattice, LieAlgebra.Basis.highestWeightLattice_def, t.kostantForm_def ht]

/-- The highest weight vector `v⁺ᵢ` lies in the fundamental lattice. -/
theorem fundamentalModuleGenerator_mem_fundamentalLattice (i : Fin t.rank) :
    t.fundamentalModuleGenerator ht i ∈ t.fundamentalLattice ht i := by
  rw [fundamentalLattice]
  exact (t.lieBasis ht).irreducibleQuotientGenerator_mem_highestWeightLattice _

/-- **The fundamental lattice is stable under the Kostant form.** -/
theorem representation_mem_fundamentalLattice {i : Fin t.rank}
    {u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht)} (hu : u ∈ t.kostantForm ht)
    {x : t.fundamentalModule ht i} (hx : x ∈ t.fundamentalLattice ht i) :
    representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i) u x ∈
      t.fundamentalLattice ht i := by
  rw [fundamentalLattice] at hx ⊢
  exact (t.lieBasis ht).representation_mem_highestWeightLattice _
    (by rwa [← t.kostantForm_def ht]) hx

/-- `v⁺ᵢ` is a weight vector of weight `Pi.single i 1 = (δᵢⱼ)ⱼ` for the Cartan generators `hⱼ`:
in the coordinates `μ ↦ (μ(hⱼ))ⱼ`, the fundamental weight `ϖᵢ` is the `i`-th standard basis
vector. -/
theorem isCartanWeightVector_fundamentalModuleGenerator (i : Fin t.rank) :
    IsCartanWeightVector (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i))
      (Pi.single i 1) (t.fundamentalModuleGenerator ht i) := by
  refine (isCartanWeightVector_iff _ _).2 fun j => ?_
  rw [representation_ι_apply]
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

/-- **The fundamental lattice is spanned by the lowering words applied to `v⁺ᵢ`**: it is the
`ℤ`-span of the vectors `fⱼ₁⁽ⁿ¹⁾ ⋯ fⱼₖ⁽ⁿᵏ⁾ v⁺ᵢ` (Steinberg's `U_ℤ v⁺ = U⁻_ℤ v⁺`). -/
theorem fundamentalLattice_eq_span_loweringWord (i : Fin t.rank) :
    t.fundamentalLattice ht i = Submodule.span ℤ (range fun l =>
      representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i)
        ((t.lieBasis ht).loweringWord l) (t.fundamentalModuleGenerator ht i)) := by
  rw [fundamentalLattice]
  exact (t.lieBasis ht).highestWeightLattice_eq_span_loweringWord _
    (t.isDominantIntegral_fundamentalWeight ht i).isIntegralWeight

/-- **The fundamental lattice is a full lattice in `L(ϖᵢ)`**: it is finitely generated over `ℤ`
and spans `L(ϖᵢ)` over `ℚ`. Finite generation comes from finite-dimensionality of `L(ϖᵢ)`:
only lowering words of bounded degree survive on `v⁺ᵢ`. -/
instance instIsLatticeFundamentalLattice (i : Fin t.rank) :
    Submodule.IsLattice ℚ (t.fundamentalLattice ht i) := by
  rw [fundamentalLattice]
  exact (t.lieBasis ht).isLattice_highestWeightLattice _
    (t.isDominantIntegral_fundamentalWeight ht i)

/-- **The fundamental lattice lies in the span of the integral weight spaces** of the Cartan
generators. With finite generation and stability under the Kostant form, this is what
`TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis` needs to give the fundamental lattice a
basis of weight vectors. -/
theorem mem_iSup_jointWeightSpace_of_mem_fundamentalLattice {i : Fin t.rank}
    {x : t.fundamentalModule ht i} (hx : x ∈ t.fundamentalLattice ht i) :
    x ∈ ⨆ μ : Fin t.rank → ℤ, jointWeightSpace (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i)) μ := by
  rw [fundamentalLattice] at hx
  exact (t.lieBasis ht).mem_iSup_jointWeightSpace_of_mem_highestWeightLattice _
    (t.isDominantIntegral_fundamentalWeight ht i).isIntegralWeight hx

end

end TauCeti.DynkinType
