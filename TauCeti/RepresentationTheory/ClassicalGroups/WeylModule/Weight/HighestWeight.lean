/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.Basic

/-!
# The highest weight determines a Weyl module

Over a field `k` that is a `ℚ`-algebra, the rational Weyl module `V_λ = det ^ λₙ ⊗ 𝕊^μ(kⁿ)` of a
dominant weight `λ` of `GL n k` has `λ` as its **highest weight** in the dominance order: `λ` is a
weight of `V_λ`, and every weight `a` of `V_λ` satisfies

`∑_{j < m} a j ≤ ∑_{j < m} λ j` for every bound `m`.

The weights of a representation are an isomorphism invariant
(`Representation.Equiv.weightSpace_eq_bot_iff`), and the dominance order is antisymmetric, so a
representation has at most one weight that occurs and dominates all of its weights. Hence
**distinct dominant weights give non-isomorphic rational Weyl modules**: `V_λ ≅ V_λ'` exactly when
`λ = λ'`. In the same way, when `μ` has at most `n` rows, the Weyl module `𝕊^ν(kⁿ)` of a Young
diagram `ν` is isomorphic to `𝕊^μ(kⁿ)` exactly when `ν = μ`; the row bound is needed, since every
diagram with more than `n` rows has the zero Weyl module.

Together with the irreducibility of `V_λ` (`TauCeti.isIrreducible_rationalWeylRep`), this says
that `λ ↦ V_λ` is an injective map from the dominant weights of `GL n` to the isomorphism classes
of irreducible representations: half of the theorem of the highest weight for `GL n`. That every
irreducible rational representation is some `V_λ` is not proved here.

## Main results

* `TauCeti.eq_of_forall_sum_filter_lt_le`: the dominance order on integer vectors is
  antisymmetric.
* `TauCeti.eq_of_equiv_of_forall_sum_filter_lt_le`: a weight that occurs in a representation and
  dominates all of its weights is an isomorphism invariant.
* `TauCeti.weightSpace_rationalWeylRep_self_ne_bot` and
  `TauCeti.sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot`: **`λ` is the highest weight of the
  rational Weyl module of `λ`.**
* `TauCeti.nonempty_equiv_rationalWeylRep_iff` and `TauCeti.nonempty_iso_rationalWeylFDRep_iff`:
  **rational Weyl modules of distinct dominant weights are not isomorphic.**
* `TauCeti.nonempty_equiv_weylRepOfShape_iff` and `TauCeti.nonempty_iso_weylFDRepOfShape_iff`:
  a Young diagram with at most `n` rows is recovered from its Weyl module.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  Weyl modules are identified as the irreducible representations of `GL n` with given highest
  weight, and their determinant twists as the rational ones.
-/

public section

open Matrix CategoryTheory

universe u

namespace TauCeti

variable {n : ℕ}

/-! ## The dominance order -/

/-- **The dominance order on integer vectors is antisymmetric**: two vectors each of whose partial
sums `∑_{j < m}` bounds the other's agree. -/
theorem eq_of_forall_sum_filter_lt_le {a b : Fin n → ℤ}
    (hab : ∀ m : ℕ, ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, a j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, b j)
    (hba : ∀ m : ℕ, ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, b j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, a j) :
    a = b := by
  have heq (m : ℕ) := le_antisymm (hab m) (hba m)
  funext i
  have hset : (Finset.univ.filter fun j : Fin n => (j : ℕ) < i + 1) =
      insert i (Finset.univ.filter fun j : Fin n => (j : ℕ) < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hi : i ∉ Finset.univ.filter fun j : Fin n => (j : ℕ) < i := by simp
  have h := heq (i + 1)
  rw [hset, Finset.sum_insert hi, Finset.sum_insert hi, heq i] at h
  exact add_right_cancel h

section CommRing

variable {k : Type u} [CommRing k]
variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **A highest weight is an isomorphism invariant.** If the weight `a` occurs in `ρ` and dominates
every weight of `ρ`, and `b` plays the same role for `σ`, then a representation equivalence
`ρ ≃ σ` forces `a = b`. -/
theorem eq_of_equiv_of_forall_sum_filter_lt_le {ρ : Representation k (GL (Fin n) k) V}
    {σ : Representation k (GL (Fin n) k) W} (e : ρ.Equiv σ) {a b : Fin n → ℤ}
    (ha : weightSpace ρ a ≠ ⊥)
    (hρ : ∀ l, weightSpace ρ l ≠ ⊥ → ∀ m : ℕ,
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l j ≤
        ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, a j)
    (hb : weightSpace σ b ≠ ⊥)
    (hσ : ∀ l, weightSpace σ l ≠ ⊥ → ∀ m : ℕ,
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l j ≤
        ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, b j) :
    a = b :=
  eq_of_forall_sum_filter_lt_le (hσ a ((e.weightSpace_eq_bot_iff a).not.mp ha))
    (hρ b ((e.weightSpace_eq_bot_iff b).not.mpr hb))

end CommRing

/-! ## The highest weight of a rational Weyl module -/

/-- **A dominant weight is a weight of its own rational Weyl module**: the twist by `det ^ λₙ`
moves the highest weight of the Weyl module of the polynomial part of `λ` back to `λ`. -/
theorem weightSpace_rationalWeylRep_self_ne_bot (k : Type u) [CommRing k] [Algebra ℚ k]
    [Nontrivial k] (l : DominantWeight n) :
    weightSpace (W := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (rationalWeylRep k n l) l.1 ≠ ⊥ := by
  have h : l.1 - (fun _ ↦ l.detShift) = (weightOfShape n l.detShiftShape).1 := by
    funext i
    rw [Pi.sub_apply, weightOfShape_apply, ← l.natCast_rowLen_detShiftShape_add_detShift i,
      add_sub_cancel_right]
  rw [weightSpace_rationalWeylRep, h]
  exact weightSpace_weylRepOfShape_weightOfShape_ne_bot l.colLen_zero_detShiftShape_le

/-- **Every weight of the rational Weyl module of `λ` is dominated by `λ`**: the weights are those
of the Weyl module of the polynomial part of `λ`, which are dominated by its shape, translated by
the constant `λₙ`. -/
theorem sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot {k : Type u} [Field k] [Algebra ℚ k]
    {l : DominantWeight n} {a : Fin n → ℤ}
    (ha : weightSpace (W := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (rationalWeylRep k n l) a ≠ ⊥) (m : ℕ) :
    ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, a j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, l.1 j := by
  rw [weightSpace_rationalWeylRep] at ha
  have h := sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot ha m
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, weightOfShape_apply] at h
  have hl (j : Fin n) : (l.detShiftShape.rowLen j : ℤ) = l.1 j - l.detShift := by
    rw [← l.natCast_rowLen_detShiftShape_add_detShift j, add_sub_cancel_right]
  simp only [hl, Finset.sum_sub_distrib] at h
  linarith

section Field

variable (k : Type u) [Field k] [Algebra ℚ k]

/-! ## Distinct highest weights give non-isomorphic Weyl modules -/

/-- **Rational Weyl modules of distinct dominant weights are not isomorphic**: the dominant weight
is recovered from the representation as its highest weight. -/
theorem nonempty_equiv_rationalWeylRep_iff {l l' : DominantWeight n} :
    Nonempty ((rationalWeylRep k n l).Equiv (rationalWeylRep k n l')) ↔ l = l' := by
  refine ⟨fun ⟨e⟩ => Subtype.ext ?_, fun h => h ▸ ⟨.refl _⟩⟩
  exact eq_of_equiv_of_forall_sum_filter_lt_le e (weightSpace_rationalWeylRep_self_ne_bot k l)
    (fun _ ha => sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot ha)
    (weightSpace_rationalWeylRep_self_ne_bot k l')
    (fun _ ha => sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot ha)

/-- **The rational Weyl modules of distinct dominant weights are non-isomorphic objects of
`FDRep`.** -/
theorem nonempty_iso_rationalWeylFDRep_iff {l l' : DominantWeight n} :
    Nonempty (rationalWeylFDRep k n l ≅ rationalWeylFDRep k n l') ↔ l = l' := by
  refine ⟨fun ⟨i⟩ => (nonempty_equiv_rationalWeylRep_iff k).mp ⟨FDRep.isoToEquiv i⟩,
    fun h => h ▸ ⟨Iso.refl _⟩⟩

/-- **A Young diagram with at most `n` rows is recovered from its Weyl module**: a Weyl module
isomorphic to that of `μ` is the Weyl module of `μ` itself. The Weyl module of `μ` is nonzero, so
the other diagram has at most `n` rows as well, and the shape is then read off as the highest
weight. Without the row bound the statement fails, since all diagrams with more than `n` rows have
the zero Weyl module. -/
theorem nonempty_equiv_weylRepOfShape_iff {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n) :
    Nonempty ((weylRepOfShape k n μ).Equiv (weylRepOfShape k n ν)) ↔ μ = ν := by
  refine ⟨fun ⟨e⟩ => ?_, fun h => h ▸ ⟨.refl _⟩⟩
  have hν : ν.colLen 0 ≤ n := by
    have := nontrivial_weylModuleOfShape k n μ hμ
    have : Nontrivial (weylModuleOfShape k n ν).toSubmodule :=
      e.toLinearEquiv.symm.toEquiv.nontrivial
    refine not_lt.mp fun hn => Submodule.nontrivial_iff_ne_bot.mp this ?_
    rw [(weylModuleOfShape_eq_bot_iff k n ν).mpr hn, Subrepresentation.toSubmodule_bot]
  have h := eq_of_equiv_of_forall_sum_filter_lt_le e
    (weightSpace_weylRepOfShape_weightOfShape_ne_bot hμ)
    (fun _ ha => sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot ha)
    (weightSpace_weylRepOfShape_weightOfShape_ne_bot hν)
    (fun _ ha => sum_le_sum_weightOfShape_of_weightSpace_weylRepOfShape_ne_bot ha)
  rw [← shape_weightOfShape hμ, ← shape_weightOfShape hν, Subtype.ext h]

/-- **A Young diagram with at most `n` rows is recovered from its Weyl module as an object of
`FDRep`.** -/
theorem nonempty_iso_weylFDRepOfShape_iff {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n) :
    Nonempty (weylFDRepOfShape k n μ ≅ weylFDRepOfShape k n ν) ↔ μ = ν := by
  refine ⟨fun ⟨i⟩ => (nonempty_equiv_weylRepOfShape_iff k hμ).mp ⟨FDRep.isoToEquiv i⟩,
    fun h => h ▸ ⟨Iso.refl _⟩⟩

end Field

end TauCeti
