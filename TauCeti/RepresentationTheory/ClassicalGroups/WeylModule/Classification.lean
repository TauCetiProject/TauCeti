/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.HighestWeight

/-!
# The highest-weight classification of the irreducible rational representations of `GL n`

Every irreducible rational representation of `GL n ℂ` is isomorphic to the rational Weyl module
`V_λ = det ^ λₙ ⊗ 𝕊^{λ - λₙ}(ℂⁿ)` of exactly one dominant weight `λ`
(`TauCeti.IsRationalRep.existsUnique_nonempty_equiv_rationalWeylRep`). Together with
`TauCeti.rationalWeylFDRepClass_injective` this is the theorem of the highest weight for `GL n`:
`λ ↦ V_λ` is a bijection from the weakly decreasing integer sequences onto the isomorphism classes
of irreducible rational representations.

## The argument

Uniqueness is `TauCeti.nonempty_equiv_rationalWeylRep_iff`: the dominant weight is recovered from
`V_λ` as its highest weight. Existence goes through the Lie algebra `𝔤𝔩ₙ(ℂ)`, where the highest
weight determines an irreducible module (`TauCeti.lieModuleEquivOfIsGlHighestWeightVector`), and
it is here that `𝔤𝔩ₙ` being reductive rather than semisimple is harmless: that theorem is proved for
the matrix-unit positive system directly, with the diagonal Cartan subalgebra including the
centre.

Let `ρ` be irreducible and rational. It has a highest weight vector `w`: a nonzero vector of a
dominant weight `λ` fixed by every transvection `xᵢⱼ(c)` with `i < j`
(`TauCeti.IsRationalRep.exists_highestWeightVector`). The rational Weyl module `V_λ` has a nonzero
vector `v` of weight `λ`, and since every weight of `V_λ` is dominated by `λ`, no weight
`λ + m (εᵢ - εⱼ)` with `m > 0` and `i < j` occurs in it, so `v` is fixed by those transvections
too (`TauCeti.rationalWeylRep_apply_transvectionUnit_eq_self`). Two irreducible rational
representations with highest weight vectors of the same weight are equivalent
(`TauCeti.IsRationalRep.nonempty_equiv_of_highestWeightVector`), by the following argument.
Differentiating (`TauCeti.IsRationalRep.differential`), both `w` and `v` become highest weight
vectors of weight `λ` for `𝔤𝔩ₙ`: `Eᵢᵢ` acts by `λᵢ`
(`TauCeti.IsRationalRep.differential_single_self_apply_of_mem_weightSpace`) and `Eᵢⱼ` with `i < j`
kills them (`TauCeti.IsRationalRep.differential_single_apply_eq_zero`), which is
`TauCeti.IsRationalRep.isGlHighestWeightVector_differential`.
Both modules are irreducible for `𝔤𝔩ₙ` (`TauCeti.IsRationalRep.isIrreducible_differential`),
because the invariant subspaces of a rational representation are its `𝔤𝔩ₙ`-stable subspaces
(`TauCeti.IsRationalRep.mem_invtSubmodule_iff_forall_mem_invtSubmodule_differential`). So the
`𝔤𝔩ₙ`-modules are isomorphic, and a `𝔤𝔩ₙ`-intertwiner between rational representations
intertwines the group actions
(`TauCeti.IsRationalRep.isIntertwiningMap_iff_forall_map_differential`).

## Main results

* `TauCeti.IsRationalRep.exists_nonempty_equiv_rationalWeylRep`: **every irreducible rational
  representation of `GL n ℂ` is a rational Weyl module.**
* `TauCeti.IsRationalRep.existsUnique_nonempty_equiv_rationalWeylRep`: it is the rational Weyl
  module of exactly one dominant weight.
* `FDRep.existsUnique_nonempty_iso_rationalWeylFDRep`: the same for simple objects of
  `FDRep ℂ (GL (Fin n) ℂ)` whose representation is rational.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15,
  Theorem 15.47 and Proposition 15.15.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 3.2.
-/

public section

open CategoryTheory

namespace TauCeti

variable {n : ℕ}

namespace IsRationalRep

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **Every irreducible rational representation of `GL n ℂ` is a rational Weyl module**: it is
equivalent to `V_λ` for the dominant weight `λ` of any of its highest weight vectors. -/
theorem exists_nonempty_equiv_rationalWeylRep (hρ : IsRationalRep ρ) [ρ.IsIrreducible] :
    ∃ l : DominantWeight n, Nonempty (ρ.Equiv (rationalWeylRep ℂ n l)) := by
  have := Representation.IsIrreducible.nontrivial (ρ := ρ) inferInstance
  obtain ⟨l, w, hw0, hwl, hw⟩ := hρ.exists_highestWeightVector
  obtain ⟨v, hvl, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (weightSpace_rationalWeylRep_self_ne_bot ℂ l)
  exact ⟨l, hρ.nonempty_equiv_of_highestWeightVector (isRationalRep_rationalWeylRep n l)
    hw0 hwl hw hv0 hvl fun _ _ hij ↦
      rationalWeylRep_apply_transvectionUnit_eq_self l hij hvl⟩

/-- **The highest-weight classification of the irreducible rational representations of
`GL n ℂ`**: an irreducible rational representation is equivalent to the rational Weyl module of
exactly one dominant weight. -/
theorem existsUnique_nonempty_equiv_rationalWeylRep (hρ : IsRationalRep ρ) [ρ.IsIrreducible] :
    ∃! l : DominantWeight n, Nonempty (ρ.Equiv (rationalWeylRep ℂ n l)) := by
  obtain ⟨l, ⟨e⟩⟩ := hρ.exists_nonempty_equiv_rationalWeylRep
  exact ⟨l, ⟨e⟩, fun l' ⟨e'⟩ ↦
    ((nonempty_equiv_rationalWeylRep_iff ℂ).mp ⟨e.symm.trans e'⟩).symm⟩

end IsRationalRep

end TauCeti

namespace FDRep

open TauCeti

variable {n : ℕ}

/-- **The highest-weight classification in `FDRep`**: a simple finite-dimensional representation
of `GL n ℂ` whose action is rational is isomorphic to the rational Weyl module of exactly one
dominant weight. -/
theorem existsUnique_nonempty_iso_rationalWeylFDRep (V : FDRep ℂ (GL (Fin n) ℂ)) [Simple V]
    (hV : IsRationalRep V.ρ) :
    ∃! l : DominantWeight n, Nonempty (V ≅ rationalWeylFDRep ℂ n l) := by
  have := (simple_iff_isIrreducible V).mp inferInstance
  obtain ⟨l, ⟨e⟩, hl⟩ := hV.existsUnique_nonempty_equiv_rationalWeylRep
  refine ⟨l, ⟨e.toLinearEquiv.toFDRepIso fun g x ↦ ?_⟩, fun l' ⟨i⟩ ↦
    hl l' ⟨isoToEquiv i⟩⟩
  exact LinearMap.congr_fun (e.isIntertwining' g) x

end FDRep
