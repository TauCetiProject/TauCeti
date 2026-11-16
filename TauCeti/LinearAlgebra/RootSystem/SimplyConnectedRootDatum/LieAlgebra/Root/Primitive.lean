/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.Algebra.Module.Primitive

/-!
# Primitive images of root vectors and Weyl transport

If every positive simple-root operator on a Kostant-stable lattice has a primitive
vector in its image, so does every root operator. Integral Weyl automorphisms preserve
primitivity, and changing the sign of a root vector changes only the sign of its image.
This transports integral detection of root operators beyond the simple roots.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra

variable {t : DynkinType} {ht : t.Valid}
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

include hM hnil

/-- Primitive images of the positive simple-root operators transport to every root operator
on a Kostant-stable lattice. -/
theorem exists_isPrimitive_chevalleySystem_apply_of_simple
    (hprim : ∀ i, ∃ v w : M,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).e i)) (v : V) = (w : V) ∧
        IsPrimitive w) (γ : Fin t.numRoots) :
    ∃ v w : M,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ)) (v : V) = (w : V) ∧
        IsPrimitive w := by
  refine chevalleySystem_induction
    (p := fun z => ∃ v w : M,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z) (v : V) = (w : V) ∧ IsPrimitive w)
    ?_ hprim ?_ γ
  · rintro z ⟨v, w, hvw, hw⟩
    exact ⟨v, -w, by rw [map_neg, map_neg, LinearMap.neg_apply, hvw]; rfl, hw.neg⟩
  · rintro i z ⟨v, w, hvw, hw⟩
    let n := kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h ρ M hM
      (hnil (.inl i)) (hnil (.inr i))
    refine ⟨n v, n w, ?_, n.isPrimitive_iff.mpr hw⟩
    rw [weylAut_simpleIndex_eq i ((t.lieBasis ht).isSl2Triple_rootGenerator i)
      (isNilpotent_ad_rootGenerator_inl i) (isNilpotent_ad_rootGenerator_inr i),
      apply_ι_weylAut_eq_weylUnit_conj (t.lieBasis ht).rootGenerator ρ
        (hnil (.inl i)) (hnil (.inr i))]
    simp only [n, coe_kostantWeylRestrict_apply, mul_apply_eq_comp,
      ← Module.End.smul_def, ← mul_smul, Units.inv_mul, one_smul, hvw]

end TauCeti.DynkinType
