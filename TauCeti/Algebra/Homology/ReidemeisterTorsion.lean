/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.LinearAlgebra.Basis.Exact
import TauCeti.LinearAlgebra.Exact

/-!
# The torsion of a based chain complex over a field

Let `C` be a `ℤ`-graded chain complex of vector spaces over a field `F`, with an ordered basis
`c i : Basis (Fin (n i)) F (C.X i)` in each degree. Write `Bⱼ ⊆ Cⱼ` for the space of boundaries,
the image of `d : Cⱼ₊₁ → Cⱼ`. When `C` is acyclic, every sequence

`0 → Bⱼ₊₁ → Cⱼ₊₁ → Bⱼ → 0`

is short exact, so a basis `bⱼ₊₁` of `Bⱼ₊₁`, a basis `bⱼ` of `Bⱼ` and lifts `sⱼ` of `bⱼ` through
`d` give an ordered basis `(bⱼ₊₁, sⱼ)` of `Cⱼ₊₁`. The *bracket* `[bⱼ₊₁ sⱼ / cⱼ₊₁]` is its
determinant with respect to `cⱼ₊₁` (`HomologicalComplex.torsionBracket`), and the torsion of `C` is
the alternating product

`τ(C) = ∏ⱼ [bⱼ₊₁ sⱼ / cⱼ₊₁] ^ ((-1) ^ j)`,

so that the bracket in degree `i` carries the exponent `(-1) ^ (i + 1)`. With this convention a
complex concentrated in degrees `1` and `0` has torsion the inverse of the determinant of its
differential (`HomologicalComplex.reidemeisterTorsion_eq_det_zpow`); for instance multiplication
by `a ≠ 0` on `F`, from degree `1` to degree `0`, has torsion `a⁻¹`. The torsion of a complex
that is not acyclic is defined to be `0` (`HomologicalComplex.reidemeisterTorsion`), and so is
that of an unbounded complex, for which the alternating product is not defined.

For a bounded complex the alternating product does not depend on the boundary bases nor on the
lifts (`HomologicalComplex.reidemeisterTorsion_eq_finprod`): changing the lifts does not change
any bracket, and changing `bⱼ` multiplies the brackets in degrees `j + 1` and `j` by the same
determinant, which enters with opposite exponents. The torsion of a bounded complex vanishes
exactly when the complex is not acyclic (`HomologicalComplex.reidemeisterTorsion_eq_zero_iff`).

Replacing the chain bases `c i` by `c' i` multiplies the torsion by `∏ᵢ [c'ᵢ / cᵢ] ^ ((-1) ^ i)`,
where `[c'ᵢ / cᵢ]` is the determinant of `c' i` with respect to `c i`
(`HomologicalComplex.reidemeisterTorsion_eq_mul_finprod_det`). In particular reordering the chain
bases multiplies the torsion by the signs of the permutations, and rescaling the basis vectors by
units multiplies it by the alternating product of their products.

## Main declarations

* `HomologicalComplex.torsionBracket`: the bracket `[bⱼ₊₁ sⱼ / cⱼ₊₁]` of a degree.
* `HomologicalComplex.reidemeisterTorsion`: the torsion of a based chain complex.
* `HomologicalComplex.reidemeisterTorsion_eq_finprod`: for a bounded acyclic complex, the torsion
  is the alternating product of the brackets for any boundary bases and lifts.
* `HomologicalComplex.reidemeisterTorsion_eq_zero_iff`: the torsion of a bounded complex vanishes
  if and only if the complex is not acyclic.
* `HomologicalComplex.reidemeisterTorsion_eq_det_zpow`: the torsion of an acyclic complex
  concentrated in two consecutive degrees.
* `HomologicalComplex.reidemeisterTorsion_eq_mul_finprod_det`: the change of the torsion under a
  change of the chain bases.
* `HomologicalComplex.reidemeisterTorsion_reindex`: the change of the torsion under a reordering
  of the chain bases.
* `HomologicalComplex.reidemeisterTorsion_unitsSMul`: the change of the torsion under a rescaling
  of the chain basis vectors by units.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F] (C : ChainComplex (ModuleCat F) ℤ)

variable {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))

section Bracket

variable {C} {j : ℤ} (h : C.ExactAt (j + 1)) {p q : ℕ}
  (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
  (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom))
  (s : Fin q → C.X (j + 1)) (hs : ∀ k, (C.d (j + 1) j).hom (s k) = b₀ k)

/-- The basis `(b₁, s)` of `Cⱼ₊₁` made of a basis `b₁` of the boundaries `Bⱼ₊₁` followed by lifts
`s` of a basis `b₀` of the boundaries `Bⱼ`. -/
private def bracketBasis : Basis (Fin p ⊕ Fin q) F (C.X (j + 1)) :=
  Basis.ofExactLift (Submodule.injective_subtype _)
    (exact_subtype_rangeRestrict (by simp) (by simp) h) b₁ b₀ s fun k ↦ Subtype.ext (hs k)

include c h b₁ b₀ in
private theorem eq_add_of_exactAt : n (j + 1) = p + q := by
  let _ : Module.Finite F (C.X (j + 1)) := .of_basis (c (j + 1))
  have hdim := (exact_subtype_rangeRestrict (i := j + 1 + 1) (k := j)
    (by simp) (by simp) h).finrank_eq_add
    (Submodule.injective_subtype _) (C.d (j + 1) j).hom.surjective_rangeRestrict
  simpa only [finrank_eq_card_basis (c (j + 1)), finrank_eq_card_basis b₁,
    finrank_eq_card_basis b₀, Fintype.card_fin] using hdim

/-- The bracket `[b₁ s / cⱼ₊₁]`: the determinant, with respect to the basis `c (j + 1)` of `Cⱼ₊₁`,
of the family made of a basis `b₁` of the boundaries `Bⱼ₊₁ ⊆ Cⱼ₊₁` followed by lifts `s` of a
basis `b₀` of the boundaries `Bⱼ ⊆ Cⱼ`. -/
def torsionBracket : F :=
  ((c (j + 1)).reindex ((finCongr (eq_add_of_exactAt c h b₁ b₀)).trans
    finSumFinEquiv.symm)).det (bracketBasis h b₁ b₀ s hs)

/-- Replacing the boundary bases and the lifts in a bracket multiplies it by the determinants of
the new boundary bases with respect to the old ones; in particular the bracket does not depend on
the lifts. -/
theorem torsionBracket_eq_mul
    (b₁' : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (b₀' : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom))
    (s' : Fin q → C.X (j + 1)) (hs' : ∀ k, (C.d (j + 1) j).hom (s' k) = b₀' k) :
    torsionBracket c h b₁' b₀' s' hs' =
      torsionBracket c h b₁ b₀ s hs * (b₁.det b₁' * b₀.det b₀') := by
  simp only [torsionBracket, bracketBasis]
  exact Basis.det_ofExactLift _ _ _ _ _ _ _ _ _ _ _

/-- Replacing the basis `c (j + 1)` of `Cⱼ₊₁` by `c' (j + 1)` multiplies a bracket by the
determinant of `c (j + 1)` with respect to `c' (j + 1)`. -/
theorem torsionBracket_eq_det_mul (c' : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    torsionBracket c' h b₁ b₀ s hs =
      (c' (j + 1)).det (c (j + 1)) * torsionBracket c h b₁ b₀ s hs := by
  rw [torsionBracket, torsionBracket, ← Basis.det_mul_det _ ((c (j + 1)).reindex
    ((finCongr (eq_add_of_exactAt c h b₁ b₀)).trans finSumFinEquiv.symm))]
  simp [Basis.det_reindex, Function.comp_assoc, -Equiv.symm_trans, -Equiv.coe_trans]

/-- A bracket is nonzero. -/
theorem torsionBracket_ne_zero : torsionBracket c h b₁ b₀ s hs ≠ 0 :=
  (Basis.isUnit_det _ _).ne_zero

/-- The bracket in a degree where the complex vanishes is `1`. -/
@[simp]
theorem torsionBracket_eq_one (hn : n (j + 1) = 0) : torsionBracket c h b₁ b₀ s hs = 1 := by
  have : IsEmpty (Fin (n (j + 1))) := by rw [hn]; infer_instance
  simp [torsionBracket, Basis.det_reindex]

/-- In a degree `j + 1` where the boundaries `Bⱼ₊₁` fill `Cⱼ₊₁` (that is, `Bⱼ = 0`, as the
dimension `n (j + 1)` is `p`), the bracket is the determinant of the basis `b₁` of `Bⱼ₊₁`. -/
theorem torsionBracket_eq_det_left (hp : n (j + 1) = p) :
    torsionBracket c h b₁ b₀ s hs =
      (c (j + 1)).det fun k ↦ (b₁ (Fin.cast hp k) : C.X (j + 1)) := by
  have hq : q = 0 := by have := eq_add_of_exactAt c h b₁ b₀; omega
  subst hq
  rw [torsionBracket, Basis.det_reindex]
  congr 1
  ext k
  have : Fin.cast (eq_add_of_exactAt c h b₁ b₀) k = Fin.castAdd 0 (Fin.cast hp k) :=
    Fin.ext rfl
  rw [Function.comp_apply, Equiv.trans_apply, finCongr_apply, this,
    finSumFinEquiv_symm_apply_castAdd, bracketBasis, Basis.ofExactLift_inl]
  rfl

/-- In a degree `j + 1` where `Cⱼ₊₁` has no nonzero boundaries (that is, `Bⱼ₊₁ = 0`, as the
dimension `n (j + 1)` is `q`), the bracket is the determinant of the lifts `s` of the basis `b₀`
of `Bⱼ`. -/
theorem torsionBracket_eq_det_right (hq : n (j + 1) = q) :
    torsionBracket c h b₁ b₀ s hs = (c (j + 1)).det (s ∘ Fin.cast hq) := by
  have hp : p = 0 := by have := eq_add_of_exactAt c h b₁ b₀; omega
  subst hp
  rw [torsionBracket, Basis.det_reindex]
  congr 1
  ext k
  have : Fin.cast (eq_add_of_exactAt c h b₁ b₀) k = Fin.natAdd 0 (Fin.cast hq k) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, Equiv.trans_apply, finCongr_apply, this,
    finSumFinEquiv_symm_apply_natAdd, bracketBasis, Basis.ofExactLift_inr]
  rfl

end Bracket

/-- The basis `Module.finBasis` of the boundaries `Bⱼ`, used to define the torsion. -/
private def chosenBasis (j : ℤ) :
    Basis (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) F
      (LinearMap.range (C.d (j + 1) j).hom) :=
  haveI : Module.Finite F (C.X (j + 1)) := .of_basis (c (j + 1))
  finBasis F _

/-- Lifts of `chosenBasis C c j` through the differential, chosen by `Function.surjInv`. -/
private def chosenLift (j : ℤ) (k : Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) :
    C.X (j + 1) :=
  Function.surjInv (C.d (j + 1) j).hom.surjective_rangeRestrict (chosenBasis C c j k)

private theorem chosenLift_spec (j : ℤ) (k) :
    (C.d (j + 1) j).hom (chosenLift C c j k) = chosenBasis C c j k :=
  congrArg Subtype.val (Function.surjInv_eq (C.d (j + 1) j).hom.surjective_rangeRestrict _)

/-- The alternating product of the brackets of an acyclic complex, for the bases `chosenBasis`
of the boundaries and the lifts `chosenLift`. -/
private def torsionOfAcyclic (h : C.Acyclic) : F :=
  ∏ᶠ j : ℤ, torsionBracket c (h (j + 1)) (chosenBasis C c (j + 1)) (chosenBasis C c j)
    (chosenLift C c j) (chosenLift_spec C c j) ^ (j.negOnePow : ℤ)

/-- The torsion of a chain complex of vector spaces with ordered bases `c i` of each `C.X i`: the
alternating product `∏ⱼ [bⱼ₊₁ sⱼ / cⱼ₊₁] ^ ((-1) ^ j)` of the brackets when `C` is acyclic and
bounded (only finitely many `n i` are nonzero), for a choice of bases `bⱼ` of the boundaries and
lifts `sⱼ` of `bⱼ`, and `0` otherwise. The product does not depend on these choices
(`reidemeisterTorsion_eq_finprod`). -/
def reidemeisterTorsion : F := by
  classical
  exact if h : C.Acyclic ∧ {i | n i ≠ 0}.Finite then torsionOfAcyclic C c h.1 else 0

/-- The torsion of a complex that is not acyclic is `0`. -/
@[simp]
theorem reidemeisterTorsion_of_not_acyclic (h : ¬C.Acyclic) : C.reidemeisterTorsion c = 0 := by
  simp [reidemeisterTorsion, h]

/-- The torsion of an unbounded complex, one with infinitely many nonzero `n i`, is `0`. -/
@[simp]
theorem reidemeisterTorsion_of_not_finite (hn : ¬{i | n i ≠ 0}.Finite) :
    C.reidemeisterTorsion c = 0 := by
  simp [reidemeisterTorsion, hn]

/-- The torsion of a bounded acyclic complex is nonzero. -/
theorem reidemeisterTorsion_ne_zero (hn : {i | n i ≠ 0}.Finite) (h : C.Acyclic) :
    C.reidemeisterTorsion c ≠ 0 := by
  rw [reidemeisterTorsion, dite_eq_left ⟨h, hn⟩, torsionOfAcyclic]
  exact finprod_ne_zero fun j ↦ zpow_ne_zero _ (torsionBracket_ne_zero c _ _ _ _ _)

/-- The torsion of a bounded based complex vanishes if and only if the complex is not acyclic. -/
theorem reidemeisterTorsion_eq_zero_iff (hn : {i | n i ≠ 0}.Finite) :
    C.reidemeisterTorsion c = 0 ↔ ¬C.Acyclic :=
  ⟨fun h₀ h ↦ C.reidemeisterTorsion_ne_zero c hn h h₀, C.reidemeisterTorsion_of_not_acyclic c⟩

include c in
/-- The determinant of one basis of the boundaries with respect to another is `1` in a degree
where the complex vanishes. -/
private theorem det_eq_one_of_eq_zero {j : ℤ} (hj : n j = 0)
    (b b' : Basis (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) F
      (LinearMap.range (C.d (j + 1) j).hom)) : b.det b' = 1 := by
  have : Module.Finite F (C.X j) := .of_basis (c j)
  have hle := Submodule.finrank_le (LinearMap.range (C.d (j + 1) j).hom)
  rw [finrank_eq_card_basis (c j), Fintype.card_fin, hj, Nat.le_zero] at hle
  have : IsEmpty (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) := by
    rw [hle]; infer_instance
  simp

section Bounded

variable {C c} (hn : {i | n i ≠ 0}.Finite) (h : C.Acyclic)

include hn in
/-- For a bounded complex, the alternating brackets have finite multiplicative support. -/
private theorem hasFiniteMulSupport_torsionBracket
    (b : ∀ j, Basis (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) F
      (LinearMap.range (C.d (j + 1) j).hom))
    (s : ∀ j, Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom)) → C.X (j + 1))
    (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k) :
    Function.HasFiniteMulSupport fun j : ℤ ↦
      torsionBracket c (h (j + 1)) (b (j + 1)) (b j) (s j) (hs j) ^ (j.negOnePow : ℤ) :=
  (hn.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
    Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      rw [torsionBracket_eq_one c _ _ _ _ _ (by simpa using hj), one_zpow]

include hn h in
/-- For a bounded acyclic complex, the alternating product of the brackets does not depend on the
bases of the boundaries nor on the lifts. -/
private theorem finprod_torsionBracket_eq
    (b b' : ∀ j, Basis (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) F
      (LinearMap.range (C.d (j + 1) j).hom))
    (s s' : ∀ j, Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom)) → C.X (j + 1))
    (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k)
    (hs' : ∀ j k, (C.d (j + 1) j).hom (s' j k) = b' j k) :
    ∏ᶠ j : ℤ, torsionBracket c (h (j + 1)) (b' (j + 1)) (b' j) (s' j) (hs' j) ^
        (j.negOnePow : ℤ) =
      ∏ᶠ j : ℤ, torsionBracket c (h (j + 1)) (b (j + 1)) (b j) (s j) (hs j) ^
        (j.negOnePow : ℤ) := by
  set δ : ℤ → F := fun j ↦ (b j).det (b' j)
  have hδ (j : ℤ) : δ j ≠ 0 := (Basis.isUnit_det _ _).ne_zero
  have hδ_one {j : ℤ} (hj : n j = 0) : δ j = 1 := det_eq_one_of_eq_zero C c hj _ _
  have hn' : {j : ℤ | n (j + 1) ≠ 0}.Finite :=
    hn.preimage (add_left_injective (1 : ℤ)).injOn
  have hT := hasFiniteMulSupport_torsionBracket (c := c) hn h b s hs
  have hδ₀ : Function.HasFiniteMulSupport fun j : ℤ ↦ δ j ^ (j.negOnePow : ℤ) :=
    hn.subset <| Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      rw [hδ_one (by simpa using hj), one_zpow]
  have hδ₁ : Function.HasFiniteMulSupport fun j : ℤ ↦ δ (j + 1) ^ (j.negOnePow : ℤ) :=
    hn'.subset <| Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      rw [hδ_one (by simpa using hj), one_zpow]
  -- The factors `δ (j + 1)` enter with the exponents opposite to those of the factors `δ j`.
  have hshift :
      ∏ᶠ j : ℤ, δ (j + 1) ^ (j.negOnePow : ℤ) = (∏ᶠ j : ℤ, δ j ^ (j.negOnePow : ℤ))⁻¹ := by
    rw [← finprod_inv_distrib,
      ← finprod_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun j ↦ (δ j ^ (j.negOnePow : ℤ))⁻¹)]
    refine finprod_congr fun j ↦ ?_
    simp [Int.negOnePow_succ, zpow_neg]
  calc ∏ᶠ j : ℤ, torsionBracket c (h (j + 1)) (b' (j + 1)) (b' j) (s' j) (hs' j) ^
        (j.negOnePow : ℤ)
      = ∏ᶠ j : ℤ, torsionBracket c (h (j + 1)) (b (j + 1)) (b j) (s j) (hs j) ^
          (j.negOnePow : ℤ) * δ (j + 1) ^ (j.negOnePow : ℤ) * δ j ^ (j.negOnePow : ℤ) := by
        refine finprod_congr fun j ↦ ?_
        rw [torsionBracket_eq_mul c (h (j + 1)) (b (j + 1)) (b j) (s j) (hs j), mul_zpow, mul_zpow,
          mul_assoc]
    _ = ∏ᶠ j : ℤ, torsionBracket c (h (j + 1)) (b (j + 1)) (b j) (s j) (hs j) ^
          (j.negOnePow : ℤ) := by
        rw [finprod_mul_distrib (hT.fun_mul hδ₁) hδ₀, finprod_mul_distrib hT hδ₁, hshift, mul_assoc,
          inv_mul_cancel₀ (finprod_ne_zero fun j ↦ zpow_ne_zero _ (hδ j)), mul_one]

include hn in
/-- For a bounded acyclic complex, the torsion is the alternating product
`∏ⱼ [bⱼ₊₁ sⱼ / cⱼ₊₁] ^ ((-1) ^ j)` of the brackets, for any bases `bⱼ` of the boundaries and any
lifts `sⱼ` of `bⱼ`. -/
theorem reidemeisterTorsion_eq_finprod
    (b : ∀ j, Basis (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) F
      (LinearMap.range (C.d (j + 1) j).hom))
    (s : ∀ j, Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom)) → C.X (j + 1))
    (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k) :
    C.reidemeisterTorsion c =
      ∏ᶠ j : ℤ, torsionBracket c (h (j + 1)) (b (j + 1)) (b j) (s j) (hs j) ^
        (j.negOnePow : ℤ) := by
  rw [reidemeisterTorsion, dite_eq_left ⟨h, hn⟩, torsionOfAcyclic]
  exact finprod_torsionBracket_eq hn h b (chosenBasis C c) s (chosenLift C c) hs
    (chosenLift_spec C c)

end Bounded

section BasisChange

variable (c' : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The determinants of one family of bases with respect to another have finite multiplicative
support when the complex is bounded. -/
private theorem hasFiniteMulSupport_det_zpow (hn : {i | n i ≠ 0}.Finite) (e : ℤ → ℤ) :
    Function.HasFiniteMulSupport fun i : ℤ ↦ (c i).det (c' i) ^ e i :=
  hn.subset <| Function.mulSupport_subset_iff'.2 fun i hi ↦ by
    have : IsEmpty (Fin (n i)) := by rw [show n i = 0 by simpa using hi]; infer_instance
    simp

/-- The basis-change formula for the torsion: replacing the bases `c i` of `C` by `c' i`
multiplies the torsion by `∏ᵢ [c'ᵢ / cᵢ] ^ ((-1) ^ i)`, where `[c'ᵢ / cᵢ]` is the determinant of
`c' i` with respect to `c i`. This holds for every complex, both sides being `0` when `C` is
not acyclic or is unbounded. -/
theorem reidemeisterTorsion_eq_mul_finprod_det :
    C.reidemeisterTorsion c' =
      C.reidemeisterTorsion c * ∏ᶠ i : ℤ, (c i).det (c' i) ^ (i.negOnePow : ℤ) := by
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · simp [reidemeisterTorsion_of_not_finite _ _ hn]
  by_cases h : C.Acyclic
  swap
  · simp [reidemeisterTorsion_of_not_acyclic _ _ h]
  -- Compute both torsions with the same boundary bases and lifts; the brackets then differ by
  -- the factors `[cⱼ₊₁ / c'ⱼ₊₁] ^ ((-1) ^ j) = [c'ⱼ₊₁ / cⱼ₊₁] ^ ((-1) ^ (j + 1))`.
  have hD : Function.HasFiniteMulSupport fun j : ℤ ↦
      (c (j + 1)).det (c' (j + 1)) ^ ((j + 1).negOnePow : ℤ) :=
    (hasFiniteMulSupport_det_zpow C c c' hn fun i ↦ (i.negOnePow : ℤ)).preimage
      (add_left_injective 1).injOn
  have hshift : ∏ᶠ i : ℤ, (c i).det (c' i) ^ (i.negOnePow : ℤ) =
      ∏ᶠ j : ℤ, (c (j + 1)).det (c' (j + 1)) ^ ((j + 1).negOnePow : ℤ) :=
    (finprod_comp_equiv (Equiv.addRight 1)).symm
  rw [reidemeisterTorsion_eq_finprod (c := c) hn h (chosenBasis C c) (chosenLift C c)
      (chosenLift_spec C c),
    reidemeisterTorsion_eq_finprod (c := c') hn h (chosenBasis C c) (chosenLift C c)
      (chosenLift_spec C c),
    hshift]
  refine (finprod_congr fun j ↦ ?_).trans
    (finprod_mul_distrib (hasFiniteMulSupport_torsionBracket hn h _ _ _) hD)
  have hinv : (c (j + 1)).det (c' (j + 1)) = ((c' (j + 1)).det (c (j + 1)))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  rw [torsionBracket_eq_det_mul c (c' := c'), mul_zpow, mul_comm]
  simp only [Int.negOnePow_succ, Units.val_neg, zpow_neg]
  congr 1
  rw [hinv, inv_zpow, inv_inv]

/-- Reordering the bases `c i` of `C` by permutations `σ i` multiplies the torsion by the product
of the signs of the `σ i`. -/
theorem reidemeisterTorsion_reindex (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    C.reidemeisterTorsion (fun i ↦ (c i).reindex (σ i)) =
      C.reidemeisterTorsion c * ∏ᶠ i : ℤ, ((Equiv.Perm.sign (σ i) : ℤ) : F) := by
  rw [reidemeisterTorsion_eq_mul_finprod_det C c]
  congr 1
  refine finprod_congr fun i ↦ ?_
  rw [Basis.coe_reindex, AlternatingMap.map_perm, Basis.det_self, Equiv.Perm.sign_symm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (σ i)) with hσ | hσ <;>
    rcases Int.units_eq_one_or i.negOnePow with hi | hi <;>
    simp only [hσ, hi, one_smul, Units.val_one, Int.cast_one, Units.neg_smul,
      Units.val_neg, Int.cast_neg, zpow_neg, zpow_one, inv_neg, inv_one]

/-- Rescaling the vectors of the bases `c i` of `C` by units `w i k` multiplies the torsion by
`∏ᵢ (∏ₖ w i k) ^ ((-1) ^ i)`. -/
theorem reidemeisterTorsion_unitsSMul (w : ∀ i, Fin (n i) → Fˣ) :
    C.reidemeisterTorsion (fun i ↦ (c i).unitsSMul (w i)) =
      C.reidemeisterTorsion c * ∏ᶠ i : ℤ, (∏ k, (w i k : F)) ^ (i.negOnePow : ℤ) := by
  rw [reidemeisterTorsion_eq_mul_finprod_det C c]
  simp

end BasisChange

section TwoDegrees

variable {C c} {j : ℤ} (h : C.Acyclic) (hn : ∀ i, i ≠ j + 1 → i ≠ j + 1 + 1 → n i = 0)

include c in
private theorem eq_zero_of_eq_zero {i : ℤ} (hi : n i = 0) (x : C.X i) : x = 0 := by
  have : IsEmpty (Fin (n i)) := by rw [hi]; infer_instance
  exact (c i).repr.injective (Subsingleton.elim _ _)

include c h hn in
/-- For an acyclic complex concentrated in degrees `j + 1` and `j + 2`, the differential
`Cⱼ₊₂ → Cⱼ₊₁` is injective. -/
private theorem injective_d_of_concentrated :
    Function.Injective (C.d (j + 1 + 1) (j + 1)).hom := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_rangeRestrict,
    (exact_subtype_rangeRestrict (i := j + 1 + 1 + 1) (k := j + 1) (by simp) (by simp)
      (h (j + 1 + 1))).linearMap_ker_eq, Submodule.range_subtype, eq_bot_iff]
  rintro _ ⟨x, rfl⟩
  rw [eq_zero_of_eq_zero (c := c) (hn (j + 1 + 1 + 1) (by omega) (by omega)) x, map_zero]
  exact zero_mem _

variable (c) in
include c h hn in
/-- An acyclic complex concentrated in degrees `j + 1` and `j + 2` has bases of the same size in
both degrees, as its differential `Cⱼ₊₂ → Cⱼ₊₁` is then an isomorphism. -/
theorem card_eq_card_of_concentrated : n (j + 1) = n (j + 1 + 1) := by
  have hsurj : Function.Surjective (C.d (j + 1 + 1) (j + 1)).hom := fun y ↦ by
    obtain ⟨⟨_, x, rfl⟩, hx⟩ := ((exact_subtype_rangeRestrict (i := j + 1 + 1) (k := j)
      (by simp) (by simp) (h (j + 1))) y).1
        (Subtype.ext (eq_zero_of_eq_zero (c := c) (hn j (by omega) (by omega)) _))
    exact ⟨x, hx⟩
  have h₁ := finrank_eq_card_basis (c (j + 1))
  have h₂ := finrank_eq_card_basis ((c (j + 1 + 1)).map
    (LinearEquiv.ofBijective _ ⟨injective_d_of_concentrated (c := c) h hn, hsurj⟩))
  simp only [Fintype.card_fin] at h₁ h₂
  omega

include hn h in
/-- The torsion of an acyclic complex concentrated in two consecutive degrees `j + 1` and `j + 2`
is `det (d) ^ ((-1) ^ j)`, where `det (d)` is the determinant of the differential
`Cⱼ₊₂ → Cⱼ₊₁` in the bases `c (j + 2)` and `c (j + 1)`. For `j = -1` this is the normalization
of the torsion: a complex concentrated in degrees `1` and `0` has torsion `det (d)⁻¹`, so that
multiplication by `a ≠ 0` on `F`, from degree `1` to degree `0`, has torsion `a⁻¹`. -/
theorem reidemeisterTorsion_eq_det_zpow :
    C.reidemeisterTorsion c = ((c (j + 1)).det fun k ↦
      (C.d (j + 1 + 1) (j + 1)).hom (c (j + 1 + 1)
        (Fin.cast (card_eq_card_of_concentrated c h hn) k))) ^ (j.negOnePow : ℤ) := by
  classical
  -- The images of the basis `c (j + 2)` form a basis of the boundaries `Bⱼ₊₁ = Cⱼ₊₁`, with the
  -- basis `c (j + 2)` itself as lifts; elsewhere the boundaries vanish.
  let β := (c (j + 1 + 1)).map
    (LinearEquiv.ofInjective _ (injective_d_of_concentrated (c := c) h hn))
  have hr : n (j + 1 + 1) = finrank F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom) := by
    rw [finrank_eq_card_basis β, Fintype.card_fin]
  let b := Function.update (chosenBasis C c) (j + 1) (β.reindex (finCongr hr))
  let s := Function.update (chosenLift C c) (j + 1) (c (j + 1 + 1) ∘ Fin.cast hr.symm)
  have hs (i : ℤ) (k) : (C.d (i + 1) i).hom (s i k) = b i k := by
    by_cases hi : i = j + 1
    · subst hi
      simp [s, b, β]
    · simp only [s, b, Function.update_of_ne hi]
      exact chosenLift_spec C c i k
  have hfin : {i | n i ≠ 0}.Finite :=
    (Set.toFinite {j + 1, j + 1 + 1}).subset fun i hi ↦ by
      by_contra hi'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi'
      exact hi (hn i hi'.1 hi'.2)
  rw [reidemeisterTorsion_eq_finprod hfin h b s hs,
    finprod_eq_prod_of_mulSupport_subset (s := {j, j + 1}), Finset.prod_pair (by omega),
    torsionBracket_eq_det_left c (h (j + 1)) (b (j + 1)) (b j) (s j) (hs j)
      ((card_eq_card_of_concentrated c h hn).trans hr),
    torsionBracket_eq_det_right c (h (j + 1 + 1)) (b (j + 1 + 1)) (b (j + 1)) (s (j + 1))
      (hs (j + 1)) hr]
  · simp [s, b, β, Function.comp_def, Basis.det_self]
  · intro i hi
    by_contra hi'
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hi'
    refine hi ?_
    beta_reduce
    rw [torsionBracket_eq_one c _ _ _ _ _ (hn _ (by omega) (by omega)), one_zpow]

end TwoDegrees

end HomologicalComplex
