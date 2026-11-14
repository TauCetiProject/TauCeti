/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Perfect
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Primitive
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Simplicity of the projective special unitary groups

Let `σ` be a nontrivial involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix
over `K` on an index type `n` with `3 ≤ Fintype.card n`, and assume that the `ε`-trace
`t ↦ t + ε σ(t)` is onto `{s | σ(s) = ε s}` with a nonzero kernel element and the norm
`b ↦ b σ(b)` is onto `K^σ`. Whenever either `K^σ` has at least three elements or
`4 ≤ Fintype.card n`, all inputs to Iwasawa's central-quotient criterion
`MulAction.IwasawaStructure.isSimpleGroup_quotient_center` hold for the action of
`Matrix.specialIsometryGroup Q σ` on `Matrix.isotropicPoints Q σ`:

* `Matrix.isotropicPoints Q σ` is nonempty (`Matrix.nonempty_isotropicPoints`) and
  `Matrix.specialIsometryGroup Q σ` is nontrivial (`Matrix.nontrivial_specialIsometryGroup`);
* the action is primitive (`Matrix.isPreprimitive_isotropicPoints`), hence quasiprimitive;
* every element fixing all isotropic points is central
  (`Matrix.mem_center_specialIsometryGroup_of_forall_smul_eq`);
* the unitary transvection groups form an Iwasawa structure
  (`Matrix.specialIsometryIwasawaStructure`);
* `Matrix.specialIsometryGroup Q σ` is perfect (`Matrix.commutator_specialIsometryGroup_eq_top`).

Consequently, both the central quotient
`Q.specialIsometryGroup σ ⧸ Subgroup.center (Q.specialIsometryGroup σ)` and the derived central
quotient `TauCeti.DerivedCentralQuotient (Q.specialIsometryGroup σ)` are simple groups, and the
centre of `Q.specialIsometryGroup σ` is precisely the kernel of its action on isotropic points.

## Main results

* `Matrix.nonempty_isotropicPoints`: `Q.isotropicPoints σ` is nonempty when `2 ≤ Fintype.card n`.
* `Matrix.nontrivial_specialIsometryGroup`: `Q.specialIsometryGroup σ` is nontrivial when
  `Q.isotropicPoints σ` is nonempty.
* `Matrix.isSimpleGroup_quotient_center_specialIsometryGroup`: the central quotient of
  `Q.specialIsometryGroup σ` is simple.
* `Matrix.isSimpleGroup_derivedCentralQuotient_specialIsometryGroup`:
  `TauCeti.DerivedCentralQuotient (Q.specialIsometryGroup σ)` is simple.
* `Matrix.mem_center_specialIsometryGroup_iff`: an element of `Q.specialIsometryGroup σ` is central
  if and only if it fixes every isotropic point.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen*, Proc. Imp. Acad. Tokyo
  **17** (1941), 57--59.
* J. Dieudonné, *On the structure of unitary groups*, Trans. Amer. Math. Soc. **72** (1952),
  367--385.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), §10.4 and §11.5.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-- **In dimension at least two, isotropic points exist** under trace and norm surjectivity. -/
theorem nonempty_isotropicPoints (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hn : 2 ≤ Fintype.card n) :
    Nonempty (Q.isotropicPoints σ) := by
  have : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  have hε : ε * ε = 1 := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  obtain ⟨u, -, hu0, hu⟩ :=
    exists_mem_ne_zero_comp_dotProduct_mulVec_self_eq_zero (U := ⊤) hσ hQ hε hnorm
      (fun x _ hx ↦
        eq_zero_of_forall_comp_dotProduct_mulVec_eq_zero hdet fun y ↦ hx y trivial)
      (by rw [finrank_top, Module.finrank_pi]; exact hn)
  exact ⟨⟨Projectivization.mk K u hu0, (mk_mem_isotropicPoints_iff hu0).mpr hu⟩⟩

/-- **The special unitary group is nontrivial** once an isotropic point and a nonzero admissible
transvection parameter exist. -/
theorem nontrivial_specialIsometryGroup (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) [Nonempty (Q.isotropicPoints σ)] :
    Nontrivial (Q.specialIsometryGroup σ) := by
  obtain ⟨p⟩ := ‹Nonempty (Q.isotropicPoints σ)›
  set u := (p : ℙ K (n → K)).rep
  have hu0 : u ≠ 0 := (p : ℙ K (n → K)).rep_ne_zero
  have hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 := comp_rep_dotProduct_mulVec_rep p
  obtain ⟨d, hd0, hd⟩ := hadm
  obtain ⟨g, hg, hM⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hu hd
  obtain ⟨y, huy⟩ : ∃ y : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
    by_contra! h0
    exact hu0 (eq_zero_of_forall_comp_dotProduct_mulVec_eq_zero hdet h0)
  refine ⟨⟨g, hg⟩, 1, fun h1 ↦ ?_⟩
  have hmat : (g : Matrix n n K) = 1 := by
    have := congrArg (fun k : Q.specialIsometryGroup σ ↦
      ((k : SpecialLinearGroup n K) : Matrix n n K)) h1
    simpa using this
  have hact := congrArg (· *ᵥ y) (hM.symm.trans hmat)
  rw [unitaryTransvection_mulVec, one_mulVec, add_eq_left] at hact
  exact smul_ne_zero (mul_ne_zero hd0 huy) hu0 hact

/-- **Iwasawa's theorem for the projective special unitary group.** Let `σ` be a nontrivial
involution of `K`, let `Q` be an invertible `ε`-Hermitian matrix on an index type `n` with
`3 ≤ Fintype.card n`, and assume trace surjectivity, existence of a nonzero admissible parameter,
and norm surjectivity onto `K^σ`. If either `K^σ` has at least three elements or
`4 ≤ Fintype.card n`, then `Q.specialIsometryGroup σ` modulo its centre is a simple group. -/
theorem isSimpleGroup_quotient_center_specialIsometryGroup (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (hn : 3 ≤ Fintype.card n)
    (hgen : (∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ σ t = t) ∨ 4 ≤ Fintype.card n) :
    IsSimpleGroup (Q.specialIsometryGroup σ ⧸ Subgroup.center (Q.specialIsometryGroup σ)) := by
  have : Nonempty (Q.isotropicPoints σ) :=
    nonempty_isotropicPoints hσ hQ hdet htr hnorm (by omega)
  have : Nontrivial (Q.specialIsometryGroup σ) :=
    nontrivial_specialIsometryGroup hσ hQ hdet hadm
  have := isPreprimitive_isotropicPoints hσ hQ hdet htr hadm
  have : Group.IsPerfect (Q.specialIsometryGroup σ) :=
    ⟨commutator_specialIsometryGroup_eq_top hσ hQ hdet htr hadm hnorm hσ_ne hn hgen⟩
  exact (specialIsometryIwasawaStructure hσ hQ hdet htr hadm hnorm hσ_ne
    hgen).isSimpleGroup_quotient_center fun _ hg ↦
      mem_center_specialIsometryGroup_of_forall_smul_eq hσ hQ hdet htr hadm hg

/-- **The derived central quotient of the special unitary group is simple** under the hypotheses of
`Matrix.isSimpleGroup_quotient_center_specialIsometryGroup`. -/
theorem isSimpleGroup_derivedCentralQuotient_specialIsometryGroup (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (hn : 3 ≤ Fintype.card n)
    (hgen : (∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ σ t = t) ∨ 4 ≤ Fintype.card n) :
    IsSimpleGroup (TauCeti.DerivedCentralQuotient (Q.specialIsometryGroup σ)) := by
  have : Nonempty (Q.isotropicPoints σ) :=
    nonempty_isotropicPoints hσ hQ hdet htr hnorm (by omega)
  have : Nontrivial (Q.specialIsometryGroup σ) :=
    nontrivial_specialIsometryGroup hσ hQ hdet hadm
  have := isPreprimitive_isotropicPoints hσ hQ hdet htr hadm
  have : Group.IsPerfect (Q.specialIsometryGroup σ) :=
    ⟨commutator_specialIsometryGroup_eq_top hσ hQ hdet htr hadm hnorm hσ_ne hn hgen⟩
  exact (specialIsometryIwasawaStructure hσ hQ hdet htr hadm hnorm hσ_ne
    hgen).isSimpleGroup_derivedCentralQuotient fun _ hg ↦
      mem_center_specialIsometryGroup_of_forall_smul_eq hσ hQ hdet htr hadm hg

/-- **The centre of the special unitary group is the kernel of its action on isotropic points**
under the hypotheses of `Matrix.isSimpleGroup_quotient_center_specialIsometryGroup`. -/
theorem mem_center_specialIsometryGroup_iff (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (hn : 3 ≤ Fintype.card n)
    (hgen : (∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ σ t = t) ∨ 4 ≤ Fintype.card n)
    {g : Q.specialIsometryGroup σ} :
    g ∈ Subgroup.center (Q.specialIsometryGroup σ) ↔ ∀ p : Q.isotropicPoints σ, g • p = p := by
  have : Nonempty (Q.isotropicPoints σ) :=
    nonempty_isotropicPoints hσ hQ hdet htr hnorm (by omega)
  have := isPreprimitive_isotropicPoints hσ hQ hdet htr hadm
  have : Group.IsPerfect (Q.specialIsometryGroup σ) :=
    ⟨commutator_specialIsometryGroup_eq_top hσ hQ hdet htr hadm hnorm hσ_ne hn hgen⟩
  exact (specialIsometryIwasawaStructure hσ hQ hdet htr hadm hnorm hσ_ne
    hgen).mem_center_iff fun _ hg ↦
      mem_center_specialIsometryGroup_of_forall_smul_eq hσ hQ hdet htr hadm hg

end Matrix
