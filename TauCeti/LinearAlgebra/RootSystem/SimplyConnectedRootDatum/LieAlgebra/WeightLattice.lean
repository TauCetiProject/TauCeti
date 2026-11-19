/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.RootLattice

/-!
# The root lattice lies in the weight lattice of a faithful representation

For a valid Dynkin type, a faithful rational representation with an admissible lattice and a
weight basis has a weight lattice containing the root lattice of the numbered simply connected
root datum. Indeed each simple raising generator acts nontrivially, so its root is a difference
of two weights of the representation. The simple roots span the entire root lattice.

This inclusion lets the roots be evaluated on the torus with character lattice equal to the
span of the representation weights, even when that lattice is smaller than the full weight
lattice. In particular it does not assert that every faithful Lie algebra representation has
full weight lattice: the adjoint representation generally does not.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 27.
-/

public section

namespace TauCeti.DynkinType

open Module

variable {t : DynkinType} (ht : t.Valid)
variable {V η : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ UniversalEnvelopingAlgebra.kostantForm
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h, ∀ v ∈ M, ρ u v ∈ M)
variable (b : Basis η ℤ M) (wt : η → Fin t.rank → ℤ)

include hM in
/-- The root lattice of the pinned datum lies in the lattice spanned by the weights of any
faithful rational representation with a rationally spanning, Kostant-stable weight lattice.
Faithfulness is required only on the Lie algebra, not on its enveloping algebra. -/
theorem rootSpan_le_span_weight
    (hρ : Function.Injective fun x : t.lieAlgebra ht =>
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
    (hspan : Submodule.span ℚ (M : Set V) = ⊤)
    (hwt : ∀ x, UniversalEnvelopingAlgebra.IsCartanWeightVector
      (t.lieBasis ht).h ρ (wt x) (b x : V)) :
    (t.simplyConnectedRootDatum ht).rootSpan ℤ ≤ Submodule.span ℤ (Set.range wt) := by
  rw [RootPairing.rootSpan, ← (t.simplyConnectedBase ht).span_int_root_support]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨i, hi⟩ := (t.simpleSupportEquivSimplyConnectedBase ht).surjective ⟨a, ha⟩
  have hindex : t.simpleIndex ht i = a := by
    simpa only [coe_simpleSupportEquivSimplyConnectedBase] using congrArg Subtype.val hi
  rw [← hindex, ← rootGeneratorWeight_inl_eq_root_simpleIndex]
  apply UniversalEnvelopingAlgebra.rootWeight_mem_span_of_representation_ne_zero
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h ρ M hM b wt hspan hwt (.inl i)
    (t.lie_lieBasis_h_rootGenerator ht (.inl i))
  intro hz
  have he : (t.lieBasis ht).e i = 0 := hρ (by simpa using hz)
  exact ((t.lieBasis ht).sl2 i).e_ne_zero he

end TauCeti.DynkinType
