/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Algebra.Homology.Periodic.ModuleCat
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.Algebra.Homology.ModuleCat.ToMatrix
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic

/-!
# The torsion of a based two-periodic complex over a field

A two-periodic complex `C` over a field `F` is a complex for the shape `ComplexShape.up (ZMod 2)`:
an even space `C₀`, an odd space `C₁`, and differentials `d₀ : C₀ → C₁` and `d₁ : C₁ → C₀` with
`d₁ d₀ = 0` and `d₀ d₁ = 0`. Fix an ordered basis `c i : Basis (Fin (n i)) F (C.X i)` of each of
the two spaces. Write `B₀ ⊆ C₀` and `B₁ ⊆ C₁` for the boundaries, the images of `d₁` and `d₀`.

When `C` is acyclic, in each degree `j` the sequence `0 → Bⱼ → Cⱼ → Bⱼ₊₁ → 0` is short exact, so
a basis `bⱼ` of `Bⱼ` followed by lifts `sⱼ` of a basis `bⱼ₊₁` of `Bⱼ₊₁` is an ordered basis of
`Cⱼ`. Its determinant with respect to `c j` is the *bracket* `[bⱼ sⱼ / cⱼ]`
(`HomologicalComplex.torsionBracket`, shared with the torsion of `ℤ`-graded complexes), and the
torsion of `C` is

`τ(C) = [b₁ s₁ / c₁] · [b₀ s₀ / c₀]⁻¹`

(`HomologicalComplex.parityTorsion`), the odd bracket over the even one; it is `0` when `C` is not
acyclic. The product does not depend on the boundary bases nor on the lifts
(`HomologicalComplex.parityTorsion_eq`): the lifts do not change the brackets, and changing `b₀`
or `b₁` multiplies both brackets by the same determinant, because each boundary space appears in
both degrees. Unlike the torsion of a `ℤ`-graded complex, no boundedness condition is needed.

The normalization is that of the `ℤ`-graded torsion
`HomologicalComplex.reidemeisterTorsion`, in which the bracket of degree `i` carries the exponent
`(-1) ^ (i + 1)`. An acyclic complex with `d₀ = 0` has torsion the inverse of the determinant of
`d₁ : C₁ → C₀` (`HomologicalComplex.parityTorsion_of_d_zero_one`); for instance multiplication by
`a ≠ 0` on `F`, from the odd to the even degree, has torsion `a⁻¹`. Dually, an acyclic complex with
`d₁ = 0` has torsion the determinant of `d₀` (`HomologicalComplex.parityTorsion_of_d_one_zero`),
and the zero complex has torsion `1` (`HomologicalComplex.parityTorsion_eq_one`). A complex
that is not acyclic has torsion `0`, and the torsion of an acyclic complex is nonzero
(`HomologicalComplex.parityTorsion_eq_zero_iff`).

Replacing the bases `c i` by `c' i` multiplies the torsion by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹`, where
`[c'ᵢ / cᵢ]` is the determinant of `c' i` with respect to `c i`
(`HomologicalComplex.parityTorsion_eq_mul_det`). In particular reordering the bases multiplies the
torsion by a sign, and rescaling the basis vectors by units multiplies it by a monomial in those
units; these are the ambiguities of torsion invariants defined from bases chosen up to signs and
deck transformations.

If `D` is a two-periodic complex over a field `K` with bases in which the matrices of the
differentials are the images of those of `C` under a homomorphism of fields `φ : F →+* K`, then
`τ(D) = φ (τ(C))` (`HomologicalComplex.map_parityTorsion`); this is how the torsion of a complex
over a ring is read in a residue field. In particular the torsion is invariant under isomorphisms
of based complexes (`HomologicalComplex.parityTorsion_map`).

Torsions of two-periodic complexes over Novikov rings, read in each field component of a total
quotient ring, are the Floer analogues of the Reidemeister torsion of a closed manifold.

## Main declarations

* `HomologicalComplex.parityTorsion`: the torsion of a based two-periodic complex.
* `HomologicalComplex.parityTorsion_eq`: the torsion of an acyclic complex is the quotient of the
  brackets for any boundary bases and lifts.
* `HomologicalComplex.parityTorsion_eq_zero_iff`: the torsion vanishes exactly when the complex is
  not acyclic.
* `HomologicalComplex.parityTorsion_eq_mul_det`: the change of the torsion under a change of the
  bases.
* `HomologicalComplex.parityTorsion_reindex`, `HomologicalComplex.parityTorsion_unitsSMul`: the
  change of the torsion under a reordering, and under a rescaling by units, of the bases.
* `HomologicalComplex.parityTorsion_of_d_zero_one`,
  `HomologicalComplex.parityTorsion_of_d_one_zero`: the torsion when one differential vanishes.
* `HomologicalComplex.parityTorsion_eq_one`: the zero complex has torsion `1`.
* `HomologicalComplex.map_parityTorsion`: the torsion of the scalar extension of a based complex
  along a homomorphism of fields is the image of its torsion.
* `HomologicalComplex.parityTorsion_map`: the torsion is invariant under isomorphisms of based
  complexes.

## References

* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), §2.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori, I*,
  J. Symplectic Geom. 3 (2005), §2.
* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F] {C : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))}
  {n : ZMod 2 → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))

section Torsion

variable (C)

/-- The torsion of a two-periodic complex of vector spaces with ordered bases `c 0` of the even
space and `c 1` of the odd space: the quotient `[b₁ s₁ / c₁] · [b₀ s₀ / c₀]⁻¹` of the odd bracket
by the even bracket when `C` is acyclic, for a choice of bases `b₀`, `b₁` of the boundaries and
lifts `s₀`, `s₁`, and `0` otherwise. The quotient does not depend on these choices
(`parityTorsion_eq`). -/
def parityTorsion : F := by
  classical
  exact if h : C.Acyclic then
    torsionBracket c ((ComplexShape.up _).prev_eq' (zero_add 1))
        ((ComplexShape.up _).next_eq' (CharTwo.add_self_eq_zero 1)) (h 1)
        (chosenBoundaryBasis C c 0 1) (chosenBoundaryBasis C c 1 0) (chosenBoundaryLift C c 1 0)
        (chosenBoundaryLift_spec C c 1 0) *
      (torsionBracket c ((ComplexShape.up _).prev_eq' (CharTwo.add_self_eq_zero 1))
        ((ComplexShape.up _).next_eq' (zero_add 1)) (h 0) (chosenBoundaryBasis C c 1 0)
        (chosenBoundaryBasis C c 0 1) (chosenBoundaryLift C c 0 1)
        (chosenBoundaryLift_spec C c 0 1))⁻¹
  else 0

/-- The torsion of a complex that is not acyclic is `0`. -/
@[simp]
theorem parityTorsion_of_not_acyclic (h : ¬C.Acyclic) : C.parityTorsion c = 0 := by
  simp [parityTorsion, h]

variable {C c}

/-- The torsion of an acyclic two-periodic complex is the quotient
`[b₁ s₁ / c₁] · [b₀ s₀ / c₀]⁻¹` of its odd bracket by its even bracket, for any bases `b₀` of the
even boundaries `B₀ = im d₁` and `b₁` of the odd boundaries `B₁ = im d₀`, and any lifts `s₁` of
`b₀` through `d₁` and `s₀` of `b₁` through `d₀`. -/
theorem parityTorsion_eq (h : C.Acyclic) {p q : ℕ}
    (b₀ : Basis (Fin p) F (LinearMap.range (C.d 1 0).hom))
    (b₁ : Basis (Fin q) F (LinearMap.range (C.d 0 1).hom))
    (s₀ : Fin q → C.X 0) (hs₀ : ∀ l, (C.d 0 1).hom (s₀ l) = b₁ l)
    (s₁ : Fin p → C.X 1) (hs₁ : ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l) :
    C.parityTorsion c =
      torsionBracket c ((ComplexShape.up _).prev_eq' (zero_add 1))
          ((ComplexShape.up _).next_eq' (CharTwo.add_self_eq_zero 1)) (h 1) b₁ b₀ s₁ hs₁ *
        (torsionBracket c ((ComplexShape.up _).prev_eq' (CharTwo.add_self_eq_zero 1))
          ((ComplexShape.up _).next_eq' (zero_add 1)) (h 0) b₀ b₁ s₀ hs₀)⁻¹ := by
  have hp : finrank F (LinearMap.range (C.d 1 0).hom) = p := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hq : finrank F (LinearMap.range (C.d 0 1).hom) = q := by
    rw [finrank_eq_card_basis b₁, Fintype.card_fin]
  -- Reindex the chosen boundary bases to `Fin p` and `Fin q`, then replace them by `b₀` and `b₁`
  -- and the chosen lifts by `s₀` and `s₁`.
  rw [parityTorsion, dite_eq_left h,
    ← torsionBracket_reindex c _ _ (h 1) _ _ _ (chosenBoundaryLift_spec C c 1 0) hq hp,
    ← torsionBracket_reindex c _ _ (h 0) _ _ _ (chosenBoundaryLift_spec C c 0 1) hp hq,
    torsionBracket_eq_mul c _ _ (h 1) b₁ b₀ s₁ hs₁,
    torsionBracket_eq_mul c _ _ (h 0) b₀ b₁ s₀ hs₀]
  -- Both brackets are multiplied by the same nonzero product of determinants, which cancels.
  have h₀ := (b₀.isUnit_det ((chosenBoundaryBasis C c 1 0).reindex (finCongr hp))).ne_zero
  have h₁ := (b₁.isUnit_det ((chosenBoundaryBasis C c 0 1).reindex (finCongr hq))).ne_zero
  field_simp

/-- The torsion of an acyclic two-periodic complex is nonzero. -/
theorem parityTorsion_ne_zero (h : C.Acyclic) : C.parityTorsion c ≠ 0 := by
  rw [parityTorsion, dite_eq_left h]
  exact mul_ne_zero (torsionBracket_ne_zero c _ _ _ _ _ _ _)
    (inv_ne_zero (torsionBracket_ne_zero c _ _ _ _ _ _ _))

/-- The torsion of a based two-periodic complex vanishes if and only if the complex is not
acyclic. -/
@[simp]
theorem parityTorsion_eq_zero_iff : C.parityTorsion c = 0 ↔ ¬C.Acyclic :=
  ⟨fun h₀ h ↦ parityTorsion_ne_zero h h₀, parityTorsion_of_not_acyclic C c⟩

end Torsion

section BasisChange

variable (c' : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The basis-change formula for the torsion: replacing the bases `c i` of `C` by `c' i`
multiplies the torsion by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹`, where `[c'ᵢ / cᵢ]` is the determinant of
`c' i` with respect to `c i`. This holds for every complex, both sides being `0` when `C` is not
acyclic. -/
theorem parityTorsion_eq_mul_det :
    C.parityTorsion c' = C.parityTorsion c * ((c 0).det (c' 0) * ((c 1).det (c' 1))⁻¹) := by
  by_cases h : C.Acyclic
  swap
  · simp [parityTorsion_of_not_acyclic _ _ h]
  -- Compute both torsions with the same boundary bases and lifts.
  rw [parityTorsion_eq (c := c) h (chosenBoundaryBasis C c 1 0) (chosenBoundaryBasis C c 0 1)
      (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0),
    parityTorsion_eq (c := c') h (chosenBoundaryBasis C c 1 0) (chosenBoundaryBasis C c 0 1)
      (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0),
    torsionBracket_eq_det_mul c _ _ _ _ _ _ _ c',
    torsionBracket_eq_det_mul c _ _ _ _ _ _ _ c']
  have hinv (i : ZMod 2) : (c' i).det (c i) = ((c i).det (c' i))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  rw [hinv, hinv, mul_inv, inv_inv]
  ring

/-- Reordering the bases `c i` of `C` by permutations `σ i` multiplies the torsion by the product
of the signs of `σ 0` and `σ 1`. -/
theorem parityTorsion_reindex (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    C.parityTorsion (fun i ↦ (c i).reindex (σ i)) =
      C.parityTorsion c *
        (((Equiv.Perm.sign (σ 0) : ℤ) : F) * ((Equiv.Perm.sign (σ 1) : ℤ) : F)) := by
  have hdet (i : ZMod 2) : (c i).det ((c i).reindex (σ i)) = ((Equiv.Perm.sign (σ i) : ℤ) : F) := by
    rw [Basis.coe_reindex, AlternatingMap.map_perm, Basis.det_self, Equiv.Perm.sign_symm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (σ i)) with hσ | hσ <;> simp [hσ]
  rw [parityTorsion_eq_mul_det c, hdet, hdet]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (σ 1)) with hσ | hσ <;> simp [hσ]

/-- Rescaling the vectors of the bases `c i` of `C` by units `w i l` multiplies the torsion by
`(∏ₗ w 0 l) · (∏ₗ w 1 l)⁻¹`. -/
theorem parityTorsion_unitsSMul (w : ∀ i, Fin (n i) → Fˣ) :
    C.parityTorsion (fun i ↦ (c i).unitsSMul (w i)) =
      C.parityTorsion c * ((∏ l, (w 0 l : F)) * (∏ l, (w 1 l : F))⁻¹) := by
  rw [parityTorsion_eq_mul_det c]
  simp

end BasisChange

section TwoTerm

include c in
private theorem eq_zero_of_dim_eq_zero {i : ZMod 2} (hi : n i = 0) (x : C.X i) : x = 0 := by
  have : IsEmpty (Fin (n i)) := by rw [hi]; infer_instance
  exact (c i).repr.injective (Subsingleton.elim _ _)

/-- A basis of the zero subspace, the boundaries of a vanishing differential. -/
private def rangeBasisOfEqZero {i i' : ZMod 2} (hd : C.d i i' = 0) :
    Basis (Fin 0) F (LinearMap.range (C.d i i').hom) :=
  haveI : Subsingleton (LinearMap.range (C.d i i').hom) := by
    rw [hd, ModuleCat.hom_zero, LinearMap.range_zero]
    infer_instance
  Basis.empty _

/-- When the differential `C.d i i'` is injective, the images of the basis `c i` form a basis of
its range. -/
private def rangeBasisOfInjective {i i' : ZMod 2} (hd : Function.Injective (C.d i i').hom) :
    Basis (Fin (n i)) F (LinearMap.range (C.d i i').hom) :=
  (c i).map (LinearEquiv.ofInjective _ hd)

@[simp]
private theorem coe_rangeBasisOfInjective {i i' : ZMod 2} (hd : Function.Injective (C.d i i').hom)
    (l : Fin (n i)) : (rangeBasisOfInjective c hd l : C.X i') = (C.d i i').hom (c i l) := by
  simp [rangeBasisOfInjective]

variable {c} in
/-- The torsion of an acyclic complex with one vanishing differential `C.d i i'`, when the other
differential `C.d i' i` is injective: it is the quotient of the determinants, in the bases `c`, of
the images of `c i'` by `C.d i' i` and of `c i'` itself, placed according to the parity of `i'`.
-/
private theorem parityTorsion_of_d_eq_zero_of_injective {i i' : ZMod 2} (hii' : i + 1 = i')
    (h : C.Acyclic) (hd : C.d i i' = 0) (hinj : Function.Injective (C.d i' i).hom)
    (hn : n i = n i') :
    torsionBracket c ((ComplexShape.up _).prev_eq' hii')
        ((ComplexShape.up _).next_eq' (hii' ▸ CharTwo.add_cancel_right i 1)) (h i')
        (rangeBasisOfEqZero hd) (rangeBasisOfInjective c hinj) (c i') (fun l ↦ by simp) = 1 ∧
      torsionBracket c ((ComplexShape.up _).prev_eq' (hii' ▸ CharTwo.add_cancel_right i 1))
          ((ComplexShape.up _).next_eq' hii') (h i) (rangeBasisOfInjective c hinj)
          (rangeBasisOfEqZero hd) Fin.elim0 (fun l ↦ l.elim0) =
        (c i).det fun l ↦ (C.d i' i).hom (c i' (Fin.cast hn l)) := by
  constructor
  · rw [torsionBracket_eq_det_right _ _ _ _ _ _ _ _ (by simp)]
    simp [Basis.det_self]
  · rw [torsionBracket_eq_det_left _ _ _ _ _ _ _ _ hn]
    simp

variable {c} in
/-- If the family of images of the basis `c i'` under `C.d i' i` has nonzero determinant with
respect to `c i`, and `C.d i i' = 0`, the complex is acyclic. -/
private theorem acyclic_of_det_ne_zero {i i' : ZMod 2} (hii' : i + 1 = i') (hd : C.d i i' = 0)
    (hn : n i = n i') (hdet : (c i).det (fun l ↦ (C.d i' i).hom (c i' (Fin.cast hn l))) ≠ 0) :
    C.Acyclic := by
  -- The images of `c i'` form a basis of `C i`, so `C.d i' i` is bijective.
  have hb := (c i).is_basis_iff_det.2 (isUnit_iff_ne_zero.2 hdet)
  have hsurj : Function.Surjective (C.d i' i).hom := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨_, rfl⟩
  have hinj : Function.Injective (C.d i' i).hom := by
    let _ : Module.Finite F (C.X i) := .of_basis (c i)
    let _ : Module.Finite F (C.X i') := .of_basis (c i')
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [finrank_eq_card_basis (c i), finrank_eq_card_basis (c i'), Fintype.card_fin,
        Fintype.card_fin, hn])).2 hsurj
  exact (C.acyclic_iff_bijective_of_d_eq_zero hii' hd).2 ⟨hinj, hsurj⟩

variable {c} in
/-- The torsion of a two-periodic complex whose even-to-odd differential `d₀` vanishes and whose two
spaces have the same dimension is the inverse of the determinant of the odd-to-even differential
`d₁` in the bases `c`. Both sides vanish when `C` is not acyclic, that is when `d₁` is not
invertible. For instance multiplication by `a` on `F` from the odd to the even degree has torsion
`a⁻¹`. -/
theorem parityTorsion_of_d_zero_one (hd : C.d 0 1 = 0) (hn : n 0 = n 1) :
    C.parityTorsion c = ((c 0).det fun l ↦ (C.d 1 0).hom (c 1 (Fin.cast hn l)))⁻¹ := by
  by_cases h : C.Acyclic
  · have hinj := ((C.acyclic_iff_bijective_of_d_eq_zero (zero_add 1) hd).1 h).1
    obtain ⟨h₁, h₀⟩ := parityTorsion_of_d_eq_zero_of_injective (c := c) (zero_add 1) h hd hinj hn
    rw [parityTorsion_eq h (rangeBasisOfInjective c hinj) (rangeBasisOfEqZero hd) Fin.elim0
      (fun l ↦ l.elim0) (c 1) (fun l ↦ by simp), h₁, h₀, one_mul]
  · rw [parityTorsion_of_not_acyclic C c h, eq_comm, inv_eq_zero]
    by_contra hdet
    exact h (acyclic_of_det_ne_zero (zero_add 1) hd hn hdet)

variable {c} in
/-- The torsion of a two-periodic complex whose odd-to-even differential `d₁` vanishes and whose two
spaces have the same dimension is the determinant of the even-to-odd differential `d₀` in the
bases `c`. Both sides vanish when `C` is not acyclic, that is when `d₀` is not invertible. -/
theorem parityTorsion_of_d_one_zero (hd : C.d 1 0 = 0) (hn : n 1 = n 0) :
    C.parityTorsion c = (c 1).det fun l ↦ (C.d 0 1).hom (c 0 (Fin.cast hn l)) := by
  by_cases h : C.Acyclic
  · have hinj := ((C.acyclic_iff_bijective_of_d_eq_zero (by decide) hd).1 h).1
    obtain ⟨h₀, h₁⟩ := parityTorsion_of_d_eq_zero_of_injective (c := c) (by decide) h hd hinj hn
    rw [parityTorsion_eq h (rangeBasisOfEqZero hd) (rangeBasisOfInjective c hinj) (c 0)
      (fun l ↦ by simp) Fin.elim0 (fun l ↦ l.elim0), h₀, h₁, inv_one, mul_one]
  · rw [parityTorsion_of_not_acyclic C c h, eq_comm]
    by_contra hdet
    exact h (acyclic_of_det_ne_zero (by decide) hd hn hdet)

variable {c} in
/-- The zero two-periodic complex, with the empty bases, has torsion `1`. -/
theorem parityTorsion_eq_one (h₀ : n 0 = 0) (h₁ : n 1 = 0) : C.parityTorsion c = 1 := by
  have hd : C.d 1 0 = 0 := by
    ext x
    exact eq_zero_of_dim_eq_zero c h₀ _
  have : IsEmpty (Fin (n 1)) := by rw [h₁]; infer_instance
  rw [parityTorsion_of_d_one_zero hd (h₁.trans h₀.symm)]
  simp [Basis.det_isEmpty]

end TwoTerm

section ScalarExtension

/-! ### Scalar extension along a homomorphism of fields -/

variable {c} {K : Type*} [Field K] (φ : F →+* K)
  {D : HomologicalComplex (ModuleCat K) (ComplexShape.up (ZMod 2))}
  {e : ∀ i, Basis (Fin (n i)) K (D.X i)}
  (hd₀ : LinearMap.toMatrix (e 0) (e 1) (D.d 0 1).hom =
    (LinearMap.toMatrix (c 0) (c 1) (C.d 0 1).hom).map φ)
  (hd₁ : LinearMap.toMatrix (e 1) (e 0) (D.d 1 0).hom =
    (LinearMap.toMatrix (c 1) (c 0) (C.d 1 0).hom).map φ)

include hd₀ hd₁ in
/-- **Scalar extension of the torsion.** Let `φ : F →+* K` be a homomorphism of fields, and let
`D` be a two-periodic complex of vector spaces over `K` with bases `e i` in which the matrices of
the two differentials are the images under `φ` of the matrices of the differentials of `C` in the
bases `c i`. Then the torsion of `D` is the image under `φ` of the torsion of `C`. This holds for
every complex: `D` is acyclic exactly when `C` is, and both torsions are `0` otherwise. -/
theorem map_parityTorsion : φ (C.parityTorsion c) = D.parityTorsion e := by
  have hDC : D.Acyclic ↔ C.Acyclic := acyclic_iff_of_toMatrix_eq φ fun i j hij ↦ by
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
      revert i j
      decide
    exacts [hd₀, hd₁]
  by_cases h : C.Acyclic
  swap
  · rw [parityTorsion_of_not_acyclic C c h, parityTorsion_of_not_acyclic D e (mt hDC.1 h),
      map_zero]
  have hD := hDC.2 h
  -- The images of the chosen boundary bases and lifts of `C` are boundary bases and lifts of `D`.
  rw [parityTorsion_eq h (chosenBoundaryBasis C c 1 0) (chosenBoundaryBasis C c 0 1)
      (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0),
    parityTorsion_eq hD (semilinearMapChosenBoundaryBasis φ hd₁)
      (semilinearMapChosenBoundaryBasis φ hd₀)
      ((c 0).semilinearMap φ (e 0) ∘ chosenBoundaryLift C c 0 1)
      (d_semilinearMap_chosenBoundaryLift φ hd₀)
      ((c 1).semilinearMap φ (e 1) ∘ chosenBoundaryLift C c 1 0)
      (d_semilinearMap_chosenBoundaryLift φ hd₁),
    map_mul, map_inv₀,
    torsionBracket_semilinearMap φ _ _ (h 1) (hD 1) _ _ _ _ _ _
      (coe_semilinearMapChosenBoundaryBasis φ hd₀) (d_semilinearMap_chosenBoundaryLift φ hd₁),
    torsionBracket_semilinearMap φ _ _ (h 0) (hD 0) _ _ _ _ _ _
      (coe_semilinearMapChosenBoundaryBasis φ hd₁) (d_semilinearMap_chosenBoundaryLift φ hd₀)]

end ScalarExtension

section Iso

variable {D : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))} (e : C ≅ D)

/-- The torsion is invariant under isomorphisms of based complexes: transporting the bases `c i`
of `C` along an isomorphism `e : C ≅ D` gives bases of `D` for which `D` has the same torsion as
`C`. -/
theorem parityTorsion_map :
    D.parityTorsion (fun i ↦ (c i).map (Hom.isoApp e i).toLinearEquiv) = C.parityTorsion c :=
  -- `D` with the transported bases is the scalar extension of `C` along the identity: the
  -- matrices of the differentials agree.
  (map_parityTorsion (RingHom.id F) (e := fun i ↦ (c i).map (Hom.isoApp e i).toLinearEquiv)
    ((toMatrix_map_isoApp_d e (c 0) (c 1)).trans (Matrix.map_id _).symm)
    ((toMatrix_map_isoApp_d e (c 1) (c 0)).trans (Matrix.map_id _).symm)).symm

end Iso

end HomologicalComplex
