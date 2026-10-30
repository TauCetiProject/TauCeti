/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.Algebra.Lie.GeneralLinear.Uniqueness
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Differential
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
too. Differentiating (`TauCeti.IsRationalRep.differential`), both `w` and `v` become highest weight
vectors of weight `λ` for `𝔤𝔩ₙ`: `Eᵢᵢ` acts by `λᵢ`
(`TauCeti.IsRationalRep.differential_single_self_apply_of_mem_weightSpace`) and `Eᵢⱼ` with `i < j`
kills them (`TauCeti.IsRationalRep.differential_single_apply_eq_zero`).
Both modules are irreducible for `𝔤𝔩ₙ`, because the invariant subspaces of a rational
representation are its `𝔤𝔩ₙ`-stable subspaces
(`TauCeti.IsRationalRep.mem_invtSubmodule_iff_forall_mem_invtSubmodule_differential`). So the
`𝔤𝔩ₙ`-modules are isomorphic, and a `𝔤𝔩ₙ`-intertwiner between rational representations
intertwines the group actions
(`TauCeti.IsRationalRep.isIntertwiningMap_iff_forall_map_differential`).

## Main results

* `TauCeti.IsRationalRep.exists_nonempty_equiv_rationalWeylRep`: **every irreducible rational
  representation of `GL n ℂ` is a rational Weyl module.**
* `TauCeti.IsRationalRep.existsUnique_nonempty_equiv_rationalWeylRep`: it is the rational Weyl
  module of exactly one dominant weight.
* `TauCeti.existsUnique_nonempty_iso_rationalWeylFDRep`: the same for simple objects of
  `FDRep ℂ (GL (Fin n) ℂ)` whose representation is rational.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15,
  Theorem 15.47 and Proposition 15.15.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 3.2.
-/

public section

open CategoryTheory

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : ℕ}

/-- **The vectors of weight `λ` in the rational Weyl module `V_λ` are highest weight vectors**:
every transvection `xᵢⱼ(c)` with `i < j` fixes each vector of weight `λ`. -/
theorem rationalWeylRep_apply_transvectionUnit_eq_self (l : DominantWeight n)
    {i j : Fin n} (hij : i < j) {v : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule}
    (hv : v ∈ weightSpace (rationalWeylRep ℂ n l) l.1) (c : ℂ) :
    rationalWeylRep ℂ n l (transvectionUnit hij.ne c) v = v := by
  classical
  refine (isRationalRep_rationalWeylRep n l).apply_transvectionUnit_eq_self hij.ne hv
    (fun m hm ↦ ?_) c
  by_contra hne
  have h := sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot hne ((i : ℕ) + 1)
  have hsingle (a : Fin n) :
      ∑ k ∈ Finset.univ.filter fun k : Fin n ↦ (k : ℕ) < (i : ℕ) + 1,
        (Pi.single a (1 : ℤ) : Fin n → ℤ) k = if (a : ℕ) < (i : ℕ) + 1 then 1 else 0 := by
    rw [Finset.sum_pi_single']
    simp
  have hj : ¬ (j : ℕ) < (i : ℕ) + 1 := by have := Fin.lt_def.mp hij; omega
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum, hsingle, Nat.lt_succ_self, ite_true, hj,
    ite_false] at h
  rw [nsmul_zero, sub_zero, Int.nsmul_eq_mul, mul_one] at h
  omega

namespace IsRationalRep

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- An irreducible rational representation is irreducible as a module over `𝔤𝔩ₙ(ℂ)` through its
differential. -/
private theorem isIrreducible_differential (hρ : IsRationalRep ρ) [ρ.IsIrreducible] :
    letI := LieRingModule.compLieHom W hρ.differential
    LieModule.IsIrreducible ℂ (Matrix (Fin n) (Fin n) ℂ) W := by
  let _ := LieRingModule.compLieHom W hρ.differential
  have := Representation.IsIrreducible.nontrivial (ρ := ρ) inferInstance
  refine LieModule.IsIrreducible.mk fun N hN ↦ ?_
  have hN' : N.toSubmodule ∈ ρ.invtSubmodule :=
    (hρ.mem_invtSubmodule_iff_forall_mem_invtSubmodule_differential _).mpr
      fun X _ hw ↦ N.lie_mem (x := X) hw
  let S : Subrepresentation ρ :=
    ⟨N.toSubmodule, fun g _ hw ↦ (Representation.mem_invtSubmodule ρ).mp hN' g hw⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · exact absurd ((LieSubmodule.toSubmodule_eq_bot N).mp
      (congrArg Subrepresentation.toSubmodule h)) hN
  · exact (LieSubmodule.toSubmodule_eq_top N).mp (congrArg Subrepresentation.toSubmodule h)

/-- A highest weight vector for the transvections, of weight `l`, is a highest weight vector of
weight `l` for `𝔤𝔩ₙ(ℂ)` through the differential. -/
private theorem isGlHighestWeightVector_differential (hρ : IsRationalRep ρ) {l : Fin n → ℤ}
    {w : W} (hw0 : w ≠ 0) (hwl : w ∈ weightSpace ρ l)
    (hw : ∀ (i j : Fin n) (hij : i < j) (c : ℂ), ρ (transvectionUnit hij.ne c) w = w) :
    letI := LieRingModule.compLieHom W hρ.differential
    IsGlHighestWeightVector (fun k ↦ (l k : ℂ)) w := by
  let _ := LieRingModule.compLieHom W hρ.differential
  refine isGlHighestWeightVector_iff.mpr ⟨hw0, fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · rw [LieRingModule.compLieHom_apply, Module.End.lie_apply,
      hρ.differential_single_self_apply_of_mem_weightSpace hwl]
  · rw [LieRingModule.compLieHom_apply, Module.End.lie_apply,
      hρ.differential_single_apply_eq_zero hij.ne (hw i j hij)]

/-- **An irreducible rational representation is determined by its highest weight**: two
irreducible rational representations of `GL n ℂ`, each with a nonzero vector of weight `l` fixed
by every transvection `xᵢⱼ(c)` with `i < j`, are equivalent. -/
theorem nonempty_equiv_of_highestWeightVector {V : Type*} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    [ρ.IsIrreducible] [σ.IsIrreducible] {l : Fin n → ℤ} {w : W} {v : V}
    (hw0 : w ≠ 0) (hwl : w ∈ weightSpace ρ l)
    (hw : ∀ (i j : Fin n) (hij : i < j) (c : ℂ), ρ (transvectionUnit hij.ne c) w = w)
    (hv0 : v ≠ 0) (hvl : v ∈ weightSpace σ l)
    (hv : ∀ (i j : Fin n) (hij : i < j) (c : ℂ), σ (transvectionUnit hij.ne c) v = v) :
    Nonempty (ρ.Equiv σ) := by
  let _ := LieRingModule.compLieHom W hρ.differential
  let _ := LieModule.compLieHom W hρ.differential
  let _ := LieRingModule.compLieHom V hσ.differential
  let _ := LieModule.compLieHom V hσ.differential
  have _ := hρ.isIrreducible_differential
  have _ := hσ.isIrreducible_differential
  let e := lieModuleEquivOfIsGlHighestWeightVector
    (hρ.isGlHighestWeightVector_differential hw0 hwl hw)
    (hσ.isGlHighestWeightVector_differential hv0 hvl hv)
  refine ⟨.mk e.toLinearEquiv fun g ↦ LinearMap.ext fun x ↦ ?_⟩
  have hint := (hρ.isIntertwiningMap_iff_forall_map_differential hσ
    e.toLinearEquiv.toLinearMap).mpr fun X x ↦ by
      simpa only [LieRingModule.compLieHom_apply, Module.End.lie_apply,
        LieModuleEquiv.coe_toLieModuleHom, LieModuleEquiv.coe_toLinearEquiv,
        LinearEquiv.coe_coe] using e.toLieModuleHom.map_lie X x
  exact (Representation.isIntertwiningMap_iff _ _ _).mp hint g x

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

/-- **The highest-weight classification in `FDRep`**: a simple finite-dimensional representation
of `GL n ℂ` whose action is rational is isomorphic to the rational Weyl module of exactly one
dominant weight. -/
theorem existsUnique_nonempty_iso_rationalWeylFDRep (V : FDRep ℂ (GL (Fin n) ℂ)) [Simple V]
    (hV : IsRationalRep V.ρ) :
    ∃! l : DominantWeight n, Nonempty (V ≅ rationalWeylFDRep ℂ n l) := by
  have := (FDRep.simple_iff_isIrreducible V).mp inferInstance
  obtain ⟨l, ⟨e⟩, hl⟩ := hV.existsUnique_nonempty_equiv_rationalWeylRep
  refine ⟨l, ⟨e.toLinearEquiv.toFDRepIso fun g x ↦ ?_⟩, fun l' ⟨i⟩ ↦
    hl l' ⟨FDRep.isoToEquiv i⟩⟩
  exact LinearMap.congr_fun (e.isIntertwining' g) x

end TauCeti
