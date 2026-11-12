/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# The torsion of a based two-periodic complex over a field

Let `C` be a two-periodic complex of vector spaces over a field `F`: a complex indexed by
`ZMod 2`, made of an even space `C₀`, an odd space `C₁` and differentials `d₀₁ : C₀ → C₁` and
`d₁₀ : C₁ → C₀` with both composites zero. Let `c i : Basis (Fin (n i)) F (C.X i)` be ordered bases.
Write `B₀ ⊆ C₀` for the image of `d₁₀` and `B₁ ⊆ C₁` for the image of `d₀₁`. When `C` is acyclic,
the sequences

`0 → B₀ → C₀ → B₁ → 0` and `0 → B₁ → C₁ → B₀ → 0`

are short exact, so bases `b₀` of `B₀`, `b₁` of `B₁` and lifts `s₀ ⊆ C₀` of `b₁` and `s₁ ⊆ C₁`
of `b₀` give ordered bases `(b₀, s₀)` of `C₀` and `(b₁, s₁)` of `C₁`. Their determinants with
respect to `c 0` and `c 1` are the *brackets* (`HomologicalComplex.torsionBracket`, shared with the
torsion of `ℤ`-graded complexes), and the torsion of `C` is their quotient

`τ(C) = [b₁ s₁ / c₁] / [b₀ s₀ / c₀]`

(`HomologicalComplex.periodicReidemeisterTorsion`). It does not depend on the boundary bases nor
on the lifts (`HomologicalComplex.periodicReidemeisterTorsion_eq`): changing `b₀` or `b₁`
multiplies both brackets by the same determinant. The torsion of a complex that is not acyclic is
defined to be `0`, and the torsion vanishes exactly in that case
(`HomologicalComplex.periodicReidemeisterTorsion_eq_zero_iff`). Unlike the torsion
`HomologicalComplex.reidemeisterTorsion` of a `ℤ`-graded complex, no boundedness hypothesis is
needed: a two-periodic complex has only two spaces. Both spaces of an acyclic two-periodic complex
have dimension `dim B₀ + dim B₁` (`HomologicalComplex.card_eq_card_of_periodic_acyclic`), so the
torsion vanishes when the two dimensions differ.

This is the torsion of complexes graded only by the parity of the index, such as Floer–Novikov
complexes, whose integer index is defined only modulo an even integer. The odd bracket enters with
exponent `1` and the even one with exponent `-1`, as for the degree-`1` and degree-`0` brackets of
`HomologicalComplex.reidemeisterTorsion`. So a complex with `d₀₁ = 0` has torsion `det (d₁₀)⁻¹`
(`HomologicalComplex.periodicReidemeisterTorsion_eq_inv_det`): multiplication by `a ≠ 0` on `F`,
from the odd space to the even one, has torsion `a⁻¹`. A complex with `d₁₀ = 0` has torsion
`det (d₀₁)` (`HomologicalComplex.periodicReidemeisterTorsion_eq_det`), and the zero complex has
torsion `1` (`HomologicalComplex.periodicReidemeisterTorsion_eq_one`).

Replacing the bases `c i` by `c' i` multiplies the torsion by `[c'₀ / c₀] / [c'₁ / c₁]`, where
`[c'ᵢ / cᵢ]` is the determinant of `c' i` with respect to `c i`
(`HomologicalComplex.periodicReidemeisterTorsion_eq_mul_det`); in particular reordering the bases
or rescaling their vectors by units changes the torsion by a sign or by a unit. The torsion is
compatible with scalar extension along a homomorphism of fields
(`HomologicalComplex.map_periodicReidemeisterTorsion`) and invariant under isomorphisms of based
complexes (`HomologicalComplex.periodicReidemeisterTorsion_map`).

## Main declarations

* `HomologicalComplex.periodicReidemeisterTorsion`: the torsion of a based two-periodic complex.
* `HomologicalComplex.periodicReidemeisterTorsion_of_acyclic`: the torsion of an acyclic complex is
  the quotient of the odd and even brackets for the chosen boundary bases and lifts.
* `HomologicalComplex.periodicReidemeisterTorsion_eq`: the torsion is the quotient of the odd and
  even brackets for any boundary bases and lifts.
* `HomologicalComplex.periodicReidemeisterTorsion_eq_zero_iff`: the torsion vanishes if and only
  if the complex is not acyclic.
* `HomologicalComplex.card_eq_card_of_periodic_acyclic`: the two spaces of an acyclic two-periodic
  complex have the same dimension.
* `HomologicalComplex.periodicReidemeisterTorsion_eq_inv_det`,
  `HomologicalComplex.periodicReidemeisterTorsion_eq_det`: the torsion of an acyclic complex with
  one vanishing differential.
* `HomologicalComplex.periodicReidemeisterTorsion_eq_mul_det`: the change of the torsion under a
  change of the bases.
* `HomologicalComplex.map_periodicReidemeisterTorsion`: the torsion of the scalar extension of a
  based complex along a homomorphism of fields is the image of its torsion.
* `HomologicalComplex.periodicReidemeisterTorsion_map`: the torsion is invariant under isomorphisms
  of based complexes.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori, I*,
  J. Symplectic Geom. 3 (2005), 221–311.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F] (C : CochainComplex (ModuleCat F) (ZMod 2))

variable {n : ZMod 2 → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The torsion of a two-periodic complex of vector spaces with ordered bases `c 0` of the even
space and `c 1` of the odd space: the quotient `[b₁ s₁ / c₁] / [b₀ s₀ / c₀]` of the odd and even
brackets when `C` is acyclic, for a choice of bases `bᵢ` of the boundaries `Bᵢ ⊆ Cᵢ` and lifts
`sᵢ ⊆ Cᵢ` of `bᵢ₊₁`, and `0` otherwise. The quotient does not depend on these choices
(`periodicReidemeisterTorsion_eq`). -/
def periodicReidemeisterTorsion : F := by
  classical
  exact if h : C.Acyclic then
    torsionBracket c (by simp +decide) (by simp +decide) (h 1) (chosenBoundaryBasis C c 0 1)
        (chosenBoundaryBasis C c 1 0) (chosenBoundaryLift C c 1 0)
        (chosenBoundaryLift_spec C c 1 0) /
      torsionBracket c (by simp +decide) (by simp +decide) (h 0) (chosenBoundaryBasis C c 1 0)
        (chosenBoundaryBasis C c 0 1) (chosenBoundaryLift C c 0 1)
        (chosenBoundaryLift_spec C c 0 1)
  else 0

/-- The torsion of an acyclic two-periodic complex is the quotient of the odd and even brackets,
for the bases `chosenBoundaryBasis` of the boundaries and the lifts `chosenBoundaryLift`. -/
theorem periodicReidemeisterTorsion_of_acyclic (h : C.Acyclic) :
    C.periodicReidemeisterTorsion c =
      torsionBracket c (by simp +decide) (by simp +decide) (h 1) (chosenBoundaryBasis C c 0 1)
          (chosenBoundaryBasis C c 1 0) (chosenBoundaryLift C c 1 0)
          (chosenBoundaryLift_spec C c 1 0) /
        torsionBracket c (by simp +decide) (by simp +decide) (h 0) (chosenBoundaryBasis C c 1 0)
          (chosenBoundaryBasis C c 0 1) (chosenBoundaryLift C c 0 1)
          (chosenBoundaryLift_spec C c 0 1) :=
  dite_eq_left h

/-- The torsion of a two-periodic complex that is not acyclic is `0`. -/
@[simp]
theorem periodicReidemeisterTorsion_of_not_acyclic (h : ¬C.Acyclic) :
    C.periodicReidemeisterTorsion c = 0 := by
  simp [periodicReidemeisterTorsion, h]

variable {C c} in
/-- **The torsion of a two-periodic complex does not depend on the choices.** For an acyclic
two-periodic complex, the torsion is the quotient `[b₁ s₁ / c₁] / [b₀ s₀ / c₀]` of the odd and
even brackets, for any bases `b₀` of the boundaries `B₀ ⊆ C₀` and `b₁` of `B₁ ⊆ C₁` and any lifts
`s₀ ⊆ C₀` of `b₁` and `s₁ ⊆ C₁` of `b₀`. -/
theorem periodicReidemeisterTorsion_eq (h : C.Acyclic) {p q : ℕ}
    (b₀ : Basis (Fin p) F (LinearMap.range (C.d 1 0).hom))
    (b₁ : Basis (Fin q) F (LinearMap.range (C.d 0 1).hom))
    (s₀ : Fin q → C.X 0) (hs₀ : ∀ k, (C.d 0 1).hom (s₀ k) = b₁ k)
    (s₁ : Fin p → C.X 1) (hs₁ : ∀ k, (C.d 1 0).hom (s₁ k) = b₀ k) :
    C.periodicReidemeisterTorsion c =
      torsionBracket c (by simp +decide) (by simp +decide) (h 1) b₁ b₀ s₁ hs₁ /
        torsionBracket c (by simp +decide) (by simp +decide) (h 0) b₀ b₁ s₀ hs₀ := by
  have hp : p = finrank F (LinearMap.range (C.d 1 0).hom) := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hq : q = finrank F (LinearMap.range (C.d 0 1).hom) := by
    rw [finrank_eq_card_basis b₁, Fintype.card_fin]
  -- Compare both brackets with those of the reindexed bases, and these with the chosen ones:
  -- the changes of boundary bases multiply both brackets by the same nonzero factor.
  rw [periodicReidemeisterTorsion_of_acyclic C c h,
    ← torsionBracket_reindex c _ _ (h 1) b₁ b₀ s₁ hs₁ hq hp,
    ← torsionBracket_reindex c _ _ (h 0) b₀ b₁ s₀ hs₀ hp hq,
    torsionBracket_eq_mul c _ _ (h 1) (chosenBoundaryBasis C c 0 1) (chosenBoundaryBasis C c 1 0)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0) (b₁.reindex (finCongr hq))
      (b₀.reindex (finCongr hp)),
    torsionBracket_eq_mul c _ _ (h 0) (chosenBoundaryBasis C c 1 0) (chosenBoundaryBasis C c 0 1)
      (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1) (b₀.reindex (finCongr hp))
      (b₁.reindex (finCongr hq)),
    mul_comm (Basis.det _ (b₀.reindex _)),
    mul_div_mul_right _ _ (mul_ne_zero (Basis.isUnit_det _ _).ne_zero
      (Basis.isUnit_det _ _).ne_zero)]

/-- The torsion of an acyclic two-periodic complex is nonzero. -/
theorem periodicReidemeisterTorsion_ne_zero (h : C.Acyclic) :
    C.periodicReidemeisterTorsion c ≠ 0 := by
  rw [periodicReidemeisterTorsion_of_acyclic C c h]
  exact div_ne_zero (torsionBracket_ne_zero _ _ _ _ _ _ _ _)
    (torsionBracket_ne_zero _ _ _ _ _ _ _ _)

/-- The torsion of a based two-periodic complex vanishes if and only if the complex is not
acyclic. -/
theorem periodicReidemeisterTorsion_eq_zero_iff :
    C.periodicReidemeisterTorsion c = 0 ↔ ¬C.Acyclic :=
  ⟨fun h₀ h ↦ C.periodicReidemeisterTorsion_ne_zero c h h₀,
    C.periodicReidemeisterTorsion_of_not_acyclic c⟩

section Acyclic

variable {C} (h : C.Acyclic)

include c h in
/-- An acyclic two-periodic complex has bases of the same size in both parities: both `C₀` and
`C₁` have dimension `dim B₀ + dim B₁`. -/
theorem card_eq_card_of_periodic_acyclic : n 0 = n 1 := by
  have h₀ := eq_add_of_exactAt c (by simp +decide) (by simp +decide) (h 0)
    (chosenBoundaryBasis C c 1 0) (chosenBoundaryBasis C c 0 1)
  have h₁ := eq_add_of_exactAt c (by simp +decide) (by simp +decide) (h 1)
    (chosenBoundaryBasis C c 0 1) (chosenBoundaryBasis C c 1 0)
  omega

end Acyclic

/-- A two-periodic complex whose even and odd spaces have different dimensions is not acyclic, so
its torsion is `0`. -/
theorem periodicReidemeisterTorsion_eq_zero_of_ne (hn : n 0 ≠ n 1) :
    C.periodicReidemeisterTorsion c = 0 :=
  C.periodicReidemeisterTorsion_of_not_acyclic c fun h ↦
    hn (card_eq_card_of_periodic_acyclic c h)

/-- The zero two-periodic complex, with bases of length zero, is acyclic and has torsion `1`. -/
theorem periodicReidemeisterTorsion_eq_one (h₀ : n 0 = 0) (h₁ : n 1 = 0) :
    C.periodicReidemeisterTorsion c = 1 := by
  have hn (i : ZMod 2) : n i = 0 := by fin_cases i <;> assumption
  have h : C.Acyclic := fun i ↦ ShortComplex.exact_of_isZero_X₂ _ <| by
    have : IsEmpty (Fin (n i)) := by rw [hn i]; infer_instance
    have : Subsingleton (C.X i) := (c i).repr.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton (C.X i)
  rw [periodicReidemeisterTorsion_of_acyclic C c h, torsionBracket_eq_one _ _ _ _ _ _ _ _ h₁,
    torsionBracket_eq_one _ _ _ _ _ _ _ _ h₀, div_one]

section OneDifferential

variable {C c}

/-- At a parity `i` where a two-periodic complex is exact and the incoming differential vanishes,
the outgoing differential is injective. -/
private theorem injective_d_of_d_eq_zero {i j : ZMod 2} (hi : (ComplexShape.up (ZMod 2)).prev i = j)
    (hk : (ComplexShape.up (ZMod 2)).next i = j) (h : C.ExactAt i) (hd : C.d j i = 0) :
    Function.Injective (C.d i j).hom := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_rangeRestrict,
    (exact_subtype_rangeRestrict hi hk h).linearMap_ker_eq, Submodule.range_subtype, hd]
  simp

/-- The image of a vanishing differential has a basis indexed by `Fin 0`. -/
private def emptyBoundaryBasis {i j : ZMod 2} (hd : C.d j i = 0) :
    Basis (Fin 0) F (LinearMap.range (C.d j i).hom) :=
  haveI : Subsingleton (LinearMap.range (C.d j i).hom) := by
    rw [hd, ModuleCat.hom_zero, LinearMap.range_zero]
    infer_instance
  Basis.empty _

/-- **The normalization of the torsion.** An acyclic two-periodic complex whose differential
`d₀₁ : C₀ → C₁` vanishes has torsion `det (d₁₀)⁻¹`, where `det (d₁₀)` is the determinant of the
odd-to-even differential `d₁₀ : C₁ → C₀` in the bases `c 1` and `c 0`. For instance
multiplication by `a ≠ 0` on `F`, from the odd space to the even one, has torsion `a⁻¹`. -/
theorem periodicReidemeisterTorsion_eq_inv_det (h : C.Acyclic) (hd : C.d 0 1 = 0) :
    C.periodicReidemeisterTorsion c = ((c 0).det fun k ↦
      (C.d 1 0).hom (c 1 (Fin.cast (card_eq_card_of_periodic_acyclic c h) k)))⁻¹ := by
  -- The images of the basis `c 1` form a basis of the boundaries `B₀ = C₀`, with the basis `c 1`
  -- itself as lifts; the boundaries `B₁` vanish.
  let β := (c 1).map
    (LinearEquiv.ofInjective _ (injective_d_of_d_eq_zero (by simp +decide)
      (by simp +decide) (h 1) hd))
  have hβ (k) : (C.d 1 0).hom (c 1 k) = β k := by simp [β]
  rw [periodicReidemeisterTorsion_eq h β (emptyBoundaryBasis hd) Fin.elim0 (fun k ↦ k.elim0)
      (c 1) hβ,
    torsionBracket_eq_det_right c _ _ _ _ _ _ _ rfl,
    torsionBracket_eq_det_left c _ _ _ _ _ _ _ (card_eq_card_of_periodic_acyclic c h)]
  simp [β, Basis.det_self]

/-- An acyclic two-periodic complex whose differential `d₁₀ : C₁ → C₀` vanishes has torsion
`det (d₀₁)`, the determinant of the even-to-odd differential `d₀₁ : C₀ → C₁` in the bases `c 0`
and `c 1`. -/
theorem periodicReidemeisterTorsion_eq_det (h : C.Acyclic) (hd : C.d 1 0 = 0) :
    C.periodicReidemeisterTorsion c = (c 1).det fun k ↦
      (C.d 0 1).hom (c 0 (Fin.cast (card_eq_card_of_periodic_acyclic c h).symm k)) := by
  -- The images of the basis `c 0` form a basis of the boundaries `B₁ = C₁`, with the basis `c 0`
  -- itself as lifts; the boundaries `B₀` vanish.
  let β := (c 0).map
    (LinearEquiv.ofInjective _ (injective_d_of_d_eq_zero (by simp +decide)
      (by simp +decide) (h 0) hd))
  have hβ (k) : (C.d 0 1).hom (c 0 k) = β k := by simp [β]
  rw [periodicReidemeisterTorsion_eq h (emptyBoundaryBasis hd) β (c 0) hβ Fin.elim0
      (fun k ↦ k.elim0),
    torsionBracket_eq_det_left c _ _ _ _ _ _ _ (card_eq_card_of_periodic_acyclic c h).symm,
    torsionBracket_eq_det_right c _ _ _ _ _ _ _ rfl]
  simp [β, Basis.det_self]

end OneDifferential

section BasisChange

variable (c' : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The basis-change formula for the torsion: replacing the bases `c i` of `C` by `c' i`
multiplies the torsion by `[c'₀ / c₀] / [c'₁ / c₁]`, where `[c'ᵢ / cᵢ]` is the determinant of
`c' i` with respect to `c i`. This holds for every complex, both sides being `0` when `C` is not
acyclic. -/
theorem periodicReidemeisterTorsion_eq_mul_det :
    C.periodicReidemeisterTorsion c' =
      C.periodicReidemeisterTorsion c * (c 0).det (c' 0) / (c 1).det (c' 1) := by
  by_cases h : C.Acyclic
  swap
  · simp [h]
  -- Compute both torsions with the same boundary bases and lifts: each bracket for `c'` is the
  -- bracket for `c` times `[cᵢ / c'ᵢ] = [c'ᵢ / cᵢ]⁻¹`.
  have hinv (i : ZMod 2) : (c' i).det (c i) = ((c i).det (c' i))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  rw [periodicReidemeisterTorsion_eq (c := c') h (chosenBoundaryBasis C c 1 0)
      (chosenBoundaryBasis C c 0 1) (chosenBoundaryLift C c 0 1)
      (chosenBoundaryLift_spec C c 0 1) (chosenBoundaryLift C c 1 0)
      (chosenBoundaryLift_spec C c 1 0),
    periodicReidemeisterTorsion_of_acyclic C c h, torsionBracket_eq_det_mul c _ _ (h 1) _ _ _ _ c',
    torsionBracket_eq_det_mul c _ _ (h 0) _ _ _ _ c', hinv, hinv]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- Reordering the bases `c i` of `C` by permutations `σ i` multiplies the torsion by the signs of
the `σ i`. -/
theorem periodicReidemeisterTorsion_reindex (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    C.periodicReidemeisterTorsion (fun i ↦ (c i).reindex (σ i)) =
      C.periodicReidemeisterTorsion c * ((Equiv.Perm.sign (σ 0) : ℤ) : F) *
        ((Equiv.Perm.sign (σ 1) : ℤ) : F) := by
  have hdet (i : ZMod 2) : (c i).det ((c i).reindex (σ i)) = ((Equiv.Perm.sign (σ i) : ℤ) : F) := by
    rw [Basis.coe_reindex, AlternatingMap.map_perm, Basis.det_self, Equiv.Perm.sign_symm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (σ i)) with hσ | hσ <;> simp [hσ]
  rw [periodicReidemeisterTorsion_eq_mul_det C c, hdet, hdet]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (σ 1)) with hσ | hσ <;> simp [hσ, div_neg]

/-- Rescaling the vectors of the bases `c i` of `C` by units `w i k` multiplies the torsion by
`(∏ₖ w 0 k) / (∏ₖ w 1 k)`. -/
theorem periodicReidemeisterTorsion_unitsSMul (w : ∀ i, Fin (n i) → Fˣ) :
    C.periodicReidemeisterTorsion (fun i ↦ (c i).unitsSMul (w i)) =
      C.periodicReidemeisterTorsion c * (∏ k, (w 0 k : F)) / ∏ k, (w 1 k : F) := by
  rw [periodicReidemeisterTorsion_eq_mul_det C c]
  simp

end BasisChange

section ScalarExtension

/-! ### Scalar extension along a homomorphism of fields -/

variable {C c} {K : Type*} [Field K] (φ : F →+* K) {D : CochainComplex (ModuleCat K) (ZMod 2)}
  {e : ∀ i, Basis (Fin (n i)) K (D.X i)}

/-- **Scalar extension of the torsion.** Let `φ : F →+* K` be a homomorphism of fields, and let
`D` be a two-periodic complex of vector spaces over `K` with bases `e i` in which the matrices of
the two differentials are the images under `φ` of the matrices of the differentials of `C` in the
bases `c i`; that is, `(D, e)` is the scalar extension of `(C, c)` along `φ`. Then the torsion of
`D` is the image under `φ` of the torsion of `C`. This holds for every complex: `D` is acyclic
exactly when `C` is, and both torsions are `0` otherwise. -/
theorem map_periodicReidemeisterTorsion
    (hd₀₁ : LinearMap.toMatrix (e 0) (e 1) (D.d 0 1).hom =
      (LinearMap.toMatrix (c 0) (c 1) (C.d 0 1).hom).map φ)
    (hd₁₀ : LinearMap.toMatrix (e 1) (e 0) (D.d 1 0).hom =
      (LinearMap.toMatrix (c 1) (c 0) (C.d 1 0).hom).map φ) :
    φ (C.periodicReidemeisterTorsion c) = D.periodicReidemeisterTorsion e := by
  -- The hypotheses cover every differential: the others vanish in both complexes.
  have hd (j i : ZMod 2) : LinearMap.toMatrix (e j) (e i) (D.d j i).hom =
      (LinearMap.toMatrix (c j) (c i) (C.d j i).hom).map φ := by
    by_cases hji : (ComplexShape.up (ZMod 2)).Rel j i
    · obtain rfl : j + 1 = i := hji
      fin_cases j
      · exact hd₀₁
      · exact hd₁₀
    · rw [C.shape _ _ hji, D.shape _ _ hji]
      ext
      simp
  have hDC : D.Acyclic ↔ C.Acyclic := acyclic_iff_of_toMatrix_eq φ fun j i _ ↦ hd j i
  by_cases h : C.Acyclic
  swap
  · rw [periodicReidemeisterTorsion_of_not_acyclic C c h,
      periodicReidemeisterTorsion_of_not_acyclic D e (mt hDC.1 h), map_zero]
  have hD := hDC.2 h
  -- The images of the chosen boundary bases of `C` form boundary bases of `D`, and the images of
  -- the chosen lifts are lifts of them.
  rw [periodicReidemeisterTorsion_of_acyclic C c h,
    periodicReidemeisterTorsion_eq hD
      (semilinearChosenBoundaryBasis φ (k := 1) (by simp +decide) (by simp +decide) (hd 1 0) (h 0))
      (semilinearChosenBoundaryBasis φ (k := 0) (by simp +decide) (by simp +decide) (hd 0 1) (h 1))
      ((c 0).semilinearMap φ (e 0) ∘ chosenBoundaryLift C c 0 1)
      (d_semilinearMap_chosenBoundaryLift φ _ _ (hd 0 1) (h 1))
      ((c 1).semilinearMap φ (e 1) ∘ chosenBoundaryLift C c 1 0)
      (d_semilinearMap_chosenBoundaryLift φ _ _ (hd 1 0) (h 0)),
    map_div₀,
    torsionBracket_semilinearMap φ _ _ (h 1) (hD 1) _ _ _ _ _ _
      (coe_semilinearChosenBoundaryBasis φ _ _ (hd 0 1) (h 1))
      (d_semilinearMap_chosenBoundaryLift φ _ _ (hd 1 0) (h 0)),
    torsionBracket_semilinearMap φ _ _ (h 0) (hD 0) _ _ _ _ _ _
      (coe_semilinearChosenBoundaryBasis φ _ _ (hd 1 0) (h 0))
      (d_semilinearMap_chosenBoundaryLift φ _ _ (hd 0 1) (h 1))]

end ScalarExtension

section Iso

variable {C} {D : CochainComplex (ModuleCat F) (ZMod 2)} (e : C ≅ D)

/-- The torsion is invariant under isomorphisms of based two-periodic complexes: transporting the
bases `c i` of `C` along an isomorphism `e : C ≅ D` gives bases of `D` for which `D` has the same
torsion as `C`. -/
theorem periodicReidemeisterTorsion_map :
    D.periodicReidemeisterTorsion (fun i ↦ (c i).map (Hom.isoApp e i).toLinearEquiv) =
      C.periodicReidemeisterTorsion c := by
  -- `D` with the transported bases is the scalar extension of `C` along the identity: the
  -- matrices of the differentials agree.
  have hd (j i : ZMod 2) : LinearMap.toMatrix ((c j).map (Hom.isoApp e j).toLinearEquiv)
      ((c i).map (Hom.isoApp e i).toLinearEquiv) (D.d j i).hom =
        (LinearMap.toMatrix (c j) (c i) (C.d j i).hom).map (RingHom.id F) := by
    ext k l
    simp only [LinearMap.toMatrix_apply, Basis.map_repr, Iso.toLinearEquiv_symm,
      Basis.map_apply, Iso.toLinearEquiv_apply, Hom.isoApp_hom, Hom.comm_apply,
      LinearEquiv.trans_apply, Iso.symm_hom, Hom.isoApp_inv, RingHom.coe_id, Matrix.map_apply,
      id_eq]
    rw [← ConcreteCategory.comp_apply, ← comp_f, e.hom_inv_id, id_f, ConcreteCategory.id_apply]
  exact (map_periodicReidemeisterTorsion (C := C) (c := c) (D := D)
    (e := fun i ↦ (c i).map (Hom.isoApp e i).toLinearEquiv) (RingHom.id F) (hd 0 1)
    (hd 1 0)).symm

/-- The torsion under an isomorphism `e : C ≅ D` of two-periodic complexes with bases `c i` and
`c' i`: if `Aᵢ` is the matrix of `eᵢ : Cᵢ → Dᵢ` in the bases `c i` and `c' i`, then
`τ(C, c) = τ(D, c') · det (A₀) / det (A₁)`. -/
theorem periodicReidemeisterTorsion_eq_mul_det_toMatrix (c' : ∀ i, Basis (Fin (n i)) F (D.X i)) :
    C.periodicReidemeisterTorsion c = D.periodicReidemeisterTorsion c' *
      (LinearMap.toMatrix (c 0) (c' 0) (e.hom.f 0).hom).det /
        (LinearMap.toMatrix (c 1) (c' 1) (e.hom.f 1).hom).det := by
  have hdet (i : ZMod 2) : (c' i).det ((c i).map (Hom.isoApp e i).toLinearEquiv) =
      (LinearMap.toMatrix (c i) (c' i) (e.hom.f i).hom).det := by
    rw [Basis.det_apply]
    congr 2
    ext k
    simp
  rw [← periodicReidemeisterTorsion_map c e, periodicReidemeisterTorsion_eq_mul_det D c', hdet,
    hdet]

end Iso

end HomologicalComplex
