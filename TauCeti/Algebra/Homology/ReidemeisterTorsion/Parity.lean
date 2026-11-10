/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# The torsion of a based two-periodic complex over a field

A *parity complex* is a chain complex graded by `ZMod 2`: an even space `C₀`, an odd space `C₁`
and differentials `d : C₁ → C₀` and `d : C₀ → C₁` whose two composites vanish. Floer complexes
whose grading is only defined modulo two, such as the Floer–Novikov complexes of a
symplectomorphism, are of this kind. In Mathlib's indexing a parity complex is a
`ChainComplex (ModuleCat F) (ZMod 2)`, with `C.d 1 0 : C₁ → C₀` and `C.d 0 1 : C₀ → C₁`.

Let `C` be a parity complex of vector spaces over a field `F`, with ordered bases `c 0` and `c 1`
of `C₀` and `C₁`. Write `B₀ ⊆ C₀` and `B₁ ⊆ C₁` for the boundaries. When `C` is acyclic, the
sequences `0 → B₁ → C₁ → B₀ → 0` and `0 → B₀ → C₀ → B₁ → 0` are short exact, and the brackets
`[b₁ s₀ / c₁]` and `[b₀ s₁ / c₀]` (`HomologicalComplex.torsionBracket`) are defined for bases `bᵢ`
of the boundaries and lifts `sᵢ` of `bᵢ` through the differential. The torsion of `C`
(`HomologicalComplex.parityReidemeisterTorsion`) is

`τ(C) = [b₁ s₀ / c₁] / [b₀ s₁ / c₀]`,

the odd bracket over the even one, and it is `0` when `C` is not acyclic. This is the convention of
the `ℤ`-graded torsion `HomologicalComplex.reidemeisterTorsion`, in which the bracket in degree `i`
carries the exponent `(-1) ^ (i + 1)`. In particular an isomorphism `C₁ → C₀` with zero
differential `C₀ → C₁` has torsion the inverse of its determinant
(`HomologicalComplex.parityReidemeisterTorsion_eq_inv_det`): multiplication by `a ≠ 0` on `F`,
from odd to even, has torsion `a⁻¹`. The zero complex is acyclic and has torsion `1`
(`HomologicalComplex.parityReidemeisterTorsion_eq_one`).

The quotient does not depend on the boundary bases nor on the lifts
(`HomologicalComplex.parityReidemeisterTorsion_eq_div`): changing the lifts changes no bracket,
and changing the basis of `B₀` (or of `B₁`) multiplies both brackets by the same determinant, as
`B₀` contributes the boundary part of the even bracket and the lifted part of the odd one. Unlike
in the `ℤ`-graded case, no boundedness is needed, since a parity complex has only two degrees.
The torsion vanishes exactly when the complex is not acyclic
(`HomologicalComplex.parityReidemeisterTorsion_eq_zero_iff`).

Replacing the chain bases `c i` by `c' i` multiplies the torsion by `[c'₀ / c₀] / [c'₁ / c₁]`
(`HomologicalComplex.parityReidemeisterTorsion_eq_mul_div_det`), where `[c'ᵢ / cᵢ]` is the
determinant of `c' i` with respect to `c i`. In particular reordering the chain bases multiplies
the torsion by the signs of the permutations
(`HomologicalComplex.parityReidemeisterTorsion_reindex`).

The torsion is compatible with scalar extension along a homomorphism of fields `φ : F →+* K`
(`HomologicalComplex.map_parityReidemeisterTorsion`): if `D` is a parity complex over `K` whose
differentials have, in bases `e i`, the images under `φ` of the matrices of those of `C`, then
`τ(D) = φ(τ(C))`. Thus the torsion of a based parity complex over a ring with several residue or
fraction fields can be compared componentwise along the field homomorphisms between them. In
particular the torsion is invariant under isomorphisms of based parity complexes
(`HomologicalComplex.parityReidemeisterTorsion_map`).

## Main declarations

* `HomologicalComplex.parityReidemeisterTorsion`: the torsion of a based parity complex.
* `HomologicalComplex.parityReidemeisterTorsion_eq_div`: for an acyclic complex, the torsion is the
  quotient of the odd bracket by the even one, for any boundary bases and lifts.
* `HomologicalComplex.parityReidemeisterTorsion_eq_zero_iff`: the torsion vanishes if and only if
  the complex is not acyclic.
* `HomologicalComplex.parityReidemeisterTorsion_eq_one`: the zero complex has torsion `1`.
* `HomologicalComplex.parityReidemeisterTorsion_eq_inv_det`,
  `HomologicalComplex.parityReidemeisterTorsion_eq_det`: the torsion of an acyclic complex with
  one vanishing differential.
* `HomologicalComplex.parityReidemeisterTorsion_eq_mul_div_det`: the change of the torsion under a
  change of the chain bases.
* `HomologicalComplex.parityReidemeisterTorsion_reindex`: the change of the torsion under a
  reordering of the chain bases.
* `HomologicalComplex.map_parityReidemeisterTorsion`: the torsion of the scalar extension of a
  based parity complex along a homomorphism of fields is the image of its torsion.
* `HomologicalComplex.parityReidemeisterTorsion_map`: the torsion is invariant under isomorphisms
  of based parity complexes.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002).
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori, I*,
  J. Symplectic Geom. 3 (2005).
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F] (C : ChainComplex (ModuleCat F) (ZMod 2))

variable {n : ZMod 2 → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The torsion of a parity complex of vector spaces with ordered bases `c 0` and `c 1` of its even
and odd spaces: the quotient `[b₁ s₀ / c₁] / [b₀ s₁ / c₀]` of the odd bracket by the even one
when `C` is acyclic, for a choice of bases `bᵢ` of the boundaries and lifts `sᵢ` of `bᵢ`, and `0`
otherwise. The quotient does not depend on these choices
(`parityReidemeisterTorsion_eq_div`). -/
def parityReidemeisterTorsion : F := by
  classical
  exact if h : C.Acyclic then
    torsionBracket c (h (0 + 1)) (chosenBoundaryBasis C c (0 + 1)) (chosenBoundaryBasis C c 0)
        (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0) /
      torsionBracket c (h (1 + 1)) (chosenBoundaryBasis C c (1 + 1)) (chosenBoundaryBasis C c 1)
        (chosenBoundaryLift C c 1) (chosenBoundaryLift_spec C c 1)
  else 0

/-- The torsion of a parity complex that is not acyclic is `0`. -/
@[simp]
theorem parityReidemeisterTorsion_of_not_acyclic (h : ¬C.Acyclic) :
    C.parityReidemeisterTorsion c = 0 := by
  simp [parityReidemeisterTorsion, h]

section Acyclic

variable {C c} (h : C.Acyclic)

include h in
/-- For an acyclic parity complex, the torsion is the quotient `[b₁ s₀ / c₁] / [b₀ s₁ / c₀]` of the
odd bracket by the even one, for any bases `b₀` of `B₀ = d(C₁)` and `b₁` of `B₁ = d(C₀)`, and any
lifts `s₀ ⊆ C₁` of `b₀` and `s₁ ⊆ C₀` of `b₁`. -/
theorem parityReidemeisterTorsion_eq_div {p q : ℕ}
    (b₀ : Basis (Fin p) F (LinearMap.range (C.d 1 0).hom))
    (b₁ : Basis (Fin q) F (LinearMap.range (C.d 0 1).hom))
    (s₀ : Fin p → C.X 1) (hs₀ : ∀ k, (C.d 1 0).hom (s₀ k) = b₀ k)
    (s₁ : Fin q → C.X 0) (hs₁ : ∀ k, (C.d 0 1).hom (s₁ k) = b₁ k) :
    C.parityReidemeisterTorsion c =
      torsionBracket c (h (0 + 1)) b₁ b₀ s₀ hs₀ / torsionBracket c (h (1 + 1)) b₀ b₁ s₁ hs₁ := by
  have hp : p = finrank F (LinearMap.range (C.d 1 0).hom) := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hq : q = finrank F (LinearMap.range (C.d 0 1).hom) := by
    rw [finrank_eq_card_basis b₁, Fintype.card_fin]
  -- Compare with the chosen boundary bases and lifts: the bracket in each degree changes by the
  -- determinants of the changes of the bases of `B₀` and `B₁`, which enter both brackets.
  rw [← torsionBracket_reindex c (h (0 + 1)) b₁ b₀ s₀ hs₀ hq hp,
    ← torsionBracket_reindex c (h (1 + 1)) b₀ b₁ s₁ hs₁ hp hq, parityReidemeisterTorsion,
    dite_eq_left h,
    torsionBracket_eq_mul c (h (0 + 1)) (chosenBoundaryBasis C c (0 + 1))
      (chosenBoundaryBasis C c 0) (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0)
      (b₁.reindex (finCongr hq)),
    torsionBracket_eq_mul c (h (1 + 1)) (chosenBoundaryBasis C c (1 + 1))
      (chosenBoundaryBasis C c 1) (chosenBoundaryLift C c 1) (chosenBoundaryLift_spec C c 1)
      (b₀.reindex (finCongr hp))]
  set D₀ := (chosenBoundaryBasis C c 0).det (b₀.reindex (finCongr hp))
  set D₁ := (chosenBoundaryBasis C c 1).det (b₁.reindex (finCongr hq))
  rw [show (chosenBoundaryBasis C c (0 + 1)).det (b₁.reindex (finCongr hq)) = D₁ from rfl,
    show (chosenBoundaryBasis C c (1 + 1)).det (b₀.reindex (finCongr hp)) = D₀ from rfl,
    mul_comm D₀ D₁, mul_div_mul_right _ _
      (mul_ne_zero (Basis.isUnit_det _ _).ne_zero (Basis.isUnit_det _ _).ne_zero)]

include h in
/-- The torsion of an acyclic parity complex is nonzero. -/
theorem parityReidemeisterTorsion_ne_zero : C.parityReidemeisterTorsion c ≠ 0 := by
  rw [parityReidemeisterTorsion_eq_div h (chosenBoundaryBasis C c 0) (chosenBoundaryBasis C c 1)
    (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0) (chosenBoundaryLift C c 1)
    (chosenBoundaryLift_spec C c 1)]
  exact div_ne_zero (torsionBracket_ne_zero c _ _ _ _ _) (torsionBracket_ne_zero c _ _ _ _ _)

end Acyclic

/-- The torsion of a parity complex vanishes if and only if the complex is not acyclic. -/
theorem parityReidemeisterTorsion_eq_zero_iff :
    C.parityReidemeisterTorsion c = 0 ↔ ¬C.Acyclic :=
  ⟨fun h hC ↦ parityReidemeisterTorsion_ne_zero hC h,
    parityReidemeisterTorsion_of_not_acyclic C c⟩

section BasisChange

variable (c' : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The basis-change formula for the torsion of a parity complex: replacing the bases `c i` by
`c' i` multiplies the torsion by `[c'₀ / c₀] / [c'₁ / c₁]`, where `[c'ᵢ / cᵢ]` is the determinant
of `c' i` with respect to `c i`. This holds for every complex, both sides being `0` when `C` is not
acyclic. -/
theorem parityReidemeisterTorsion_eq_mul_div_det :
    C.parityReidemeisterTorsion c' =
      C.parityReidemeisterTorsion c * ((c 0).det (c' 0) / (c 1).det (c' 1)) := by
  by_cases h : C.Acyclic
  swap
  · simp [parityReidemeisterTorsion_of_not_acyclic _ _ h]
  -- Compute both torsions with the same boundary bases and lifts; the bracket in degree `i` then
  -- changes by `[cᵢ / c'ᵢ] = [c'ᵢ / cᵢ]⁻¹`.
  have hinv (i : ZMod 2) : (c' i).det (c i) = ((c i).det (c' i))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  have hne (i : ZMod 2) : (c i).det (c' i) ≠ 0 := (Basis.isUnit_det _ _).ne_zero
  rw [parityReidemeisterTorsion_eq_div (c := c) h (chosenBoundaryBasis C c 0)
      (chosenBoundaryBasis C c 1) (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0)
      (chosenBoundaryLift C c 1) (chosenBoundaryLift_spec C c 1),
    parityReidemeisterTorsion_eq_div (c := c') h (chosenBoundaryBasis C c 0)
      (chosenBoundaryBasis C c 1) (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0)
      (chosenBoundaryLift C c 1) (chosenBoundaryLift_spec C c 1),
    torsionBracket_eq_det_mul c (c' := c'), torsionBracket_eq_det_mul c (c' := c'),
    show (c' (0 + 1)).det (c (0 + 1)) = (c' 1).det (c 1) from rfl,
    show (c' (1 + 1)).det (c (1 + 1)) = (c' 0).det (c 0) from rfl, hinv, hinv]
  field_simp [hne 0, hne 1]

/-- Reordering the bases `c i` of a parity complex by permutations `σ i` multiplies the torsion by
the product of the signs of the `σ i`. -/
theorem parityReidemeisterTorsion_reindex (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    C.parityReidemeisterTorsion (fun i ↦ (c i).reindex (σ i)) =
      C.parityReidemeisterTorsion c *
        (((Equiv.Perm.sign (σ 0) : ℤ) : F) * ((Equiv.Perm.sign (σ 1) : ℤ) : F)) := by
  have hdet (i : ZMod 2) :
      (c i).det ((c i).reindex (σ i)) = ((Equiv.Perm.sign (σ i) : ℤ) : F) := by
    rw [Basis.coe_reindex, AlternatingMap.map_perm, Basis.det_self, Equiv.Perm.sign_symm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (σ i)) with hσ | hσ <;> simp [hσ]
  rw [parityReidemeisterTorsion_eq_mul_div_det C c, hdet, hdet]
  congr 1
  rcases Int.units_eq_one_or (Equiv.Perm.sign (σ 1)) with hσ | hσ <;> simp [hσ, div_neg]

end BasisChange

section Elementary

/-- The zero parity complex, in which both spaces have empty bases, is acyclic and has torsion
`1`. -/
theorem parityReidemeisterTorsion_eq_one (hn : ∀ i, n i = 0) :
    C.parityReidemeisterTorsion c = 1 := by
  have (i : ZMod 2) : Subsingleton (C.X i) := by
    have : IsEmpty (Fin (n i)) := by rw [hn i]; infer_instance
    exact (c i).repr.injective.subsingleton
  have h : C.Acyclic := fun i ↦
    (exactAt_iff _ _).2
      (ShortComplex.exact_of_isZero_X₂ _ (ModuleCat.isZero_of_subsingleton (C.X i)))
  rw [parityReidemeisterTorsion_eq_div h (chosenBoundaryBasis C c 0) (chosenBoundaryBasis C c 1)
      (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0) (chosenBoundaryLift C c 1)
      (chosenBoundaryLift_spec C c 1),
    torsionBracket_eq_one c _ _ _ _ _ (hn _), torsionBracket_eq_one c _ _ _ _ _ (hn _), div_one]

end Elementary

section TwoTerm

variable {C} (h : C.Acyclic)

include h in
/-- In an acyclic parity complex, the odd boundaries `d(C₁) ⊆ C₀` are the even cycles. -/
private theorem range_d_one_zero : LinearMap.range (C.d 1 0).hom = LinearMap.ker (C.d 0 1).hom :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    ((C.exactAt_iff' 1 0 1 (by rw [ChainComplex.prev]; rfl) (by rw [ChainComplex.next]; rfl)).1
      (h 0))

include h in
/-- In an acyclic parity complex, the even boundaries `d(C₀) ⊆ C₁` are the odd cycles. -/
private theorem range_d_zero_one : LinearMap.range (C.d 0 1).hom = LinearMap.ker (C.d 1 0).hom :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    ((C.exactAt_iff' 0 1 0 (by rw [ChainComplex.prev]; rfl) (by rw [ChainComplex.next]; rfl)).1
      (h 1))

include h in
/-- In an acyclic parity complex whose even-to-odd differential vanishes, the odd-to-even
differential `C₁ → C₀` is bijective. -/
theorem bijective_d_one_zero_of_d_zero_one_eq_zero (hd : C.d 0 1 = 0) :
    Function.Bijective (C.d 1 0).hom := by
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot, ← range_d_zero_one h, hd]
    exact LinearMap.range_zero
  · have hy : y ∈ LinearMap.ker (C.d 0 1).hom := by simp [hd]
    rw [← range_d_one_zero h] at hy
    exact hy

include h in
/-- In an acyclic parity complex whose odd-to-even differential vanishes, the even-to-odd
differential `C₀ → C₁` is bijective. -/
theorem bijective_d_zero_one_of_d_one_zero_eq_zero (hd : C.d 1 0 = 0) :
    Function.Bijective (C.d 0 1).hom := by
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot, ← range_d_one_zero h, hd]
    exact LinearMap.range_zero
  · have hy : y ∈ LinearMap.ker (C.d 1 0).hom := by simp [hd]
    rw [← range_d_zero_one h] at hy
    exact hy

include c h in
/-- An acyclic parity complex whose even-to-odd differential vanishes has bases of the same size
in both degrees, as its odd-to-even differential is then an isomorphism. -/
theorem card_zero_eq_card_one_of_d_zero_one_eq_zero (hd : C.d 0 1 = 0) : n 0 = n 1 := by
  have hd' :=
    (LinearEquiv.ofBijective _ (bijective_d_one_zero_of_d_zero_one_eq_zero h hd)).finrank_eq
  simpa using (finrank_eq_card_basis (c 0)).symm.trans
    (hd'.symm.trans (finrank_eq_card_basis (c 1)))

include c h in
/-- An acyclic parity complex whose odd-to-even differential vanishes has bases of the same size
in both degrees, as its even-to-odd differential is then an isomorphism. -/
theorem card_one_eq_card_zero_of_d_one_zero_eq_zero (hd : C.d 1 0 = 0) : n 1 = n 0 := by
  have hd' :=
    (LinearEquiv.ofBijective _ (bijective_d_zero_one_of_d_one_zero_eq_zero h hd)).finrank_eq
  simpa using (finrank_eq_card_basis (c 1)).symm.trans
    (hd'.symm.trans (finrank_eq_card_basis (c 0)))

include h in
/-- **Normalization of the parity torsion.** An acyclic parity complex whose even-to-odd
differential vanishes has torsion `det (d)⁻¹`, where `det (d)` is the determinant of the
isomorphism `d : C₁ → C₀` in the bases `c 1` and `c 0`. For instance multiplication by `a ≠ 0` on
`F`, from odd to even, has torsion `a⁻¹`. -/
theorem parityReidemeisterTorsion_eq_inv_det (hd : C.d 0 1 = 0) :
    C.parityReidemeisterTorsion c = ((c 0).det fun k ↦
      (C.d 1 0).hom (c 1 (Fin.cast (card_zero_eq_card_one_of_d_zero_one_eq_zero c h hd) k)))⁻¹ := by
  -- The images of the basis `c 1` form a basis of the boundaries `B₀ = C₀`, with the basis `c 1`
  -- itself as lifts; the boundaries `B₁` vanish.
  let β := (c 1).map
    (LinearEquiv.ofInjective _ (bijective_d_one_zero_of_d_zero_one_eq_zero h hd).1)
  have hβ (k : Fin (n 1)) : (C.d 1 0).hom (c 1 k) = β k := by simp [β]
  -- the degrees `1 + 1` and `0 + 1` of the brackets are `0` and `1`
  have hn : n (1 + 1) = n 1 := card_zero_eq_card_one_of_d_zero_one_eq_zero c h hd
  rw [parityReidemeisterTorsion_eq_div h β (chosenBoundaryBasis C c 1) (c 1) hβ
      (chosenBoundaryLift C c 1) (chosenBoundaryLift_spec C c 1),
    torsionBracket_eq_det_right c (h (0 + 1)) _ _ _ _ (rfl : n (0 + 1) = n 1),
    torsionBracket_eq_det_left c (h (1 + 1)) _ _ _ _ hn, Fin.cast_refl, Function.comp_id,
    show (c (0 + 1)).det (c 1) = 1 from (c 1).det_self, one_div]
  simp only [β, Basis.map_apply, LinearEquiv.ofInjective_apply]
  -- the two determinants differ only by the degree `1 + 1 = 0` of `ZMod 2`
  rfl

include h in
/-- An acyclic parity complex whose odd-to-even differential vanishes has torsion `det (d)`, where
`det (d)` is the determinant of the isomorphism `d : C₀ → C₁` in the bases `c 0` and `c 1`. -/
theorem parityReidemeisterTorsion_eq_det (hd : C.d 1 0 = 0) :
    C.parityReidemeisterTorsion c = (c 1).det fun k ↦
      (C.d 0 1).hom (c 0 (Fin.cast (card_one_eq_card_zero_of_d_one_zero_eq_zero c h hd) k)) := by
  -- The images of the basis `c 0` form a basis of the boundaries `B₁ = C₁`, with the basis `c 0`
  -- itself as lifts; the boundaries `B₀` vanish.
  let β := (c 0).map
    (LinearEquiv.ofInjective _ (bijective_d_zero_one_of_d_one_zero_eq_zero h hd).1)
  have hβ (k : Fin (n 0)) : (C.d 0 1).hom (c 0 k) = β k := by simp [β]
  -- the degrees `0 + 1` and `1 + 1` of the brackets are `1` and `0`
  have hn : n (0 + 1) = n 0 := card_one_eq_card_zero_of_d_one_zero_eq_zero c h hd
  rw [parityReidemeisterTorsion_eq_div h (chosenBoundaryBasis C c 0) β
      (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0) (c 0) hβ,
    torsionBracket_eq_det_left c (h (0 + 1)) _ _ _ _ hn,
    torsionBracket_eq_det_right c (h (1 + 1)) _ _ _ _ (rfl : n (1 + 1) = n 0), Fin.cast_refl,
    Function.comp_id, show (c (1 + 1)).det (c 0) = 1 from (c 0).det_self, div_one]
  simp only [β, Basis.map_apply, LinearEquiv.ofInjective_apply]
  -- the two determinants differ only by the degree `0 + 1 = 1` of `ZMod 2`
  rfl

end TwoTerm

section ScalarExtension

/-! ### Scalar extension along a homomorphism of fields -/

variable {C c} {K : Type*} [Field K] (φ : F →+* K) {D : ChainComplex (ModuleCat K) (ZMod 2)}
  {e : ∀ i, Basis (Fin (n i)) K (D.X i)}
  (hd : ∀ i, LinearMap.toMatrix (e (i + 1)) (e i) (D.d (i + 1) i).hom =
    (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map φ)

include hd in
/-- **Scalar extension of the parity torsion.** Let `φ : F →+* K` be a homomorphism of fields, and
let `D` be a parity complex of vector spaces over `K` with bases `e i` in which the matrices of the
differentials are the images under `φ` of the matrices of the differentials of `C` in the bases
`c i`. Then the torsion of `D` is the image under `φ` of the torsion of `C`. This holds for every
complex: `D` is acyclic exactly when `C` is, and both torsions are `0` otherwise. -/
theorem map_parityReidemeisterTorsion :
    φ (C.parityReidemeisterTorsion c) = D.parityReidemeisterTorsion e := by
  have hDC : D.Acyclic ↔ C.Acyclic :=
    acyclic_iff_of_toMatrix_eq φ fun i j (hij : j + 1 = i) ↦ hij ▸ hd j
  by_cases h : C.Acyclic
  swap
  · rw [parityReidemeisterTorsion_of_not_acyclic C c h,
      parityReidemeisterTorsion_of_not_acyclic D e (mt hDC.1 h), map_zero]
  have hD := hDC.2 h
  have : ∀ i, Module.Finite K (D.X i) := fun i ↦ .of_basis (e i)
  have hcomm (j : ZMod 2) (x : C.X (j + 1)) :
      (D.d (j + 1) j).hom ((c (j + 1)).semilinearMap φ (e (j + 1)) x) =
        (c j).semilinearMap φ (e j) ((C.d (j + 1) j).hom x) :=
    Basis.semilinearMap_comp_apply_of_toMatrix_eq (hd j) x
  -- The images of the chosen boundary bases of `C` are boundaries of `D`.
  have hmem (j : ZMod 2) (k) : (c j).semilinearMap φ (e j) (chosenBoundaryBasis C c j k) ∈
      LinearMap.range (D.d (j + 1) j).hom :=
    LinearMap.mem_range.2 ⟨_, by rw [hcomm, chosenBoundaryLift_spec]⟩
  -- The images of the chosen boundary bases of `C` form boundary bases of `D`, and the images of
  -- the chosen lifts are lifts of them.
  let b (j : ZMod 2) : Basis (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) K
      (LinearMap.range (D.d (j + 1) j).hom) :=
    basisOfLinearIndependentOfCardEqFinrank' (fun k ↦ ⟨_, hmem j k⟩)
      (LinearIndependent.of_comp (LinearMap.range (D.d (j + 1) j).hom).subtype
        (linearIndependent_semilinearMap_chosenBoundaryBasis φ h j))
      (by rw [Fintype.card_fin, finrank_range_d_eq_of_toMatrix_eq φ (hd j)])
  have hb (j : ZMod 2) (k) : (b j k : D.X j) =
      (c j).semilinearMap φ (e j) (chosenBoundaryBasis C c j k) := by
    simp [b]
  have hs (j : ZMod 2) (k) :
      (D.d (j + 1) j).hom ((c (j + 1)).semilinearMap φ (e (j + 1)) (chosenBoundaryLift C c j k)) =
        b j k := by
    rw [hb, hcomm, chosenBoundaryLift_spec]
  rw [parityReidemeisterTorsion_eq_div h (chosenBoundaryBasis C c 0) (chosenBoundaryBasis C c 1)
      (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0) (chosenBoundaryLift C c 1)
      (chosenBoundaryLift_spec C c 1),
    parityReidemeisterTorsion_eq_div hD (b 0) (b 1)
      ((c (0 + 1)).semilinearMap φ (e (0 + 1)) ∘ chosenBoundaryLift C c 0) (hs 0)
      ((c (1 + 1)).semilinearMap φ (e (1 + 1)) ∘ chosenBoundaryLift C c 1) (hs 1),
    map_div₀, torsionBracket_semilinearMap φ (h (0 + 1)) (hD (0 + 1)) _ _ _ _ _ _ (hb 1) (hs 0),
    torsionBracket_semilinearMap φ (h (1 + 1)) (hD (1 + 1)) _ _ _ _ _ _ (hb 0) (hs 1)]

end ScalarExtension

section Iso

variable {C} {D : ChainComplex (ModuleCat F) (ZMod 2)} (e : C ≅ D)

/-- The parity torsion is invariant under isomorphisms of based complexes: transporting the bases
`c i` of `C` along an isomorphism `e : C ≅ D` gives bases of `D` for which `D` has the same torsion
as `C`. -/
theorem parityReidemeisterTorsion_map :
    D.parityReidemeisterTorsion (fun i ↦ (c i).map (Hom.isoApp e i).toLinearEquiv) =
      C.parityReidemeisterTorsion c := by
  -- `D` with the transported bases is the scalar extension of `C` along the identity: the
  -- matrices of the differentials agree.
  refine (map_parityReidemeisterTorsion (RingHom.id F) fun i ↦ ?_).symm
  ext k l
  simp only [LinearMap.toMatrix_apply, Basis.map_repr, Iso.toLinearEquiv_symm, Basis.map_apply,
    Iso.toLinearEquiv_apply, Hom.isoApp_hom, Hom.comm_apply, LinearEquiv.trans_apply, Iso.symm_hom,
    Hom.isoApp_inv, RingHom.coe_id, Matrix.map_apply, id_eq]
  rw [← ConcreteCategory.comp_apply, ← comp_f, e.hom_inv_id, id_f, ConcreteCategory.id_apply]

end Iso

end HomologicalComplex
