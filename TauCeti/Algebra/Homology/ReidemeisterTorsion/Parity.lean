/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import TauCeti.Algebra.Homology.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.ModuleCat.Parity
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The torsion of a based parity complex over a field

A *parity complex* over a field `F` is a chain complex `C` indexed by `ZMod 2`: an even space
`C₀`, an odd space `C₁`, and differentials `C₁ → C₀` and `C₀ → C₁` whose composites vanish.
Floer complexes whose grading is only defined modulo two, such as the Floer–Novikov complexes of a
symplectomorphism, are of this kind. They are not bounded integer complexes, so the torsion
`HomologicalComplex.reidemeisterTorsion` of a based `ℤ`-graded complex does not apply to them;
this file defines their torsion with the same brackets. The chain-complex API lives in
`ChainComplex`; the ascending two-periodic API lives in `HomologicalComplex` in
`TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic`.

Let `C` have ordered bases `c 0` of `C₀` and `c 1` of `C₁`. Write `Bᵢ ⊆ Cᵢ` for the boundaries,
the images of the differentials into `Cᵢ`. When `C` is acyclic, a basis `bᵢ` of `Bᵢ` and lifts
`sᵢ` of `bᵢ` through the differential into `Cᵢ` give the brackets
`[b₁ s₀ / c₁]` and `[b₀ s₁ / c₀]` of `HomologicalComplex.torsionBracket`, the determinants of the
bases `(b₁, s₀)` of `C₁` and `(b₀, s₁)` of `C₀`. The torsion of `C` is

`τ(C) = [b₁ s₀ / c₁] · [b₀ s₁ / c₀]⁻¹`

(`ChainComplex.parityTorsion`), and `0` when `C` is not acyclic. As for `ℤ`-graded
complexes, the bracket of an odd degree enters with exponent `1` and that of an even degree with
exponent `-1`. The value does not depend on the bases of the boundaries nor on the lifts
(`ChainComplex.parityTorsion_eq_mul_inv`): changing `b₀` or `b₁` multiplies both brackets
by the same determinant.

With this normalization the complex `F → F` given by multiplication by `a ≠ 0` from the odd to
the even space has torsion `a⁻¹`, and the same map from the even to the odd space has torsion `a`
(`ChainComplex.parityTorsion_eq_inv_det`, `ChainComplex.parityTorsion_eq_det`). The
zero complex is acyclic and has torsion `1` (`ChainComplex.parityTorsion_eq_one`), whereas
a complex with nonzero homology, such as `F` placed in even degree, has torsion `0`
(`ChainComplex.parityTorsion_eq_zero_iff`).

## Main declarations

* `ChainComplex.parityTorsion`: the torsion of a based parity complex.
* `ChainComplex.parityTorsion_eq_mul_inv`: for an acyclic complex, the torsion is the ratio
  of the brackets for any bases of the boundaries and any lifts.
* `ChainComplex.parityTorsion_eq_zero_iff`: the torsion vanishes exactly when the complex is
  not acyclic.
* `ChainComplex.parityTorsion_eq_mul_det`: replacing the bases `c i` by `c' i` multiplies
  the torsion by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹`.
* `ChainComplex.parityTorsion_reindex`, `ChainComplex.parityTorsion_unitsSMul`: the
  effect of reordering and of rescaling the bases.
* `ChainComplex.parityTorsion_eq_inv_det`, `ChainComplex.parityTorsion_eq_det`: when
  one differential vanishes and the other one is bijective, the torsion is the determinant of the
  bijective differential, inverted when it goes from odd to even degree. Such a complex is acyclic
  by `HomologicalComplex.acyclic_iff_bijective_d_one_zero` and
  `HomologicalComplex.acyclic_iff_bijective_d_zero_one`.
* `ChainComplex.parityTorsion_eq_one`: the torsion of the zero complex is `1`.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
-/

public section

noncomputable section

open CategoryTheory Module

namespace ChainComplex

open HomologicalComplex

variable {F : Type*} [Field F] (C : ChainComplex (ModuleCat F) (ZMod 2))
  {n : ZMod 2 → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The ratio of the brackets of an acyclic parity complex, for the bases `chosenBoundaryBasis` of
the boundaries and the lifts `chosenBoundaryLift`. -/
private def parityTorsionOfAcyclic (h : C.Acyclic) : F :=
  torsionBracket c ((ComplexShape.down _).prev_eq' rfl) ((ComplexShape.down _).next_eq' rfl)
    (h (0 + 1)) (chosenBoundaryBasis C c ((0 + 1) + 1) (0 + 1)) (chosenBoundaryBasis C c (0 + 1) 0)
      (chosenBoundaryLift C c (0 + 1) 0) (chosenBoundaryLift_spec C c (0 + 1) 0) *
    (torsionBracket c ((ComplexShape.down _).prev_eq' rfl) ((ComplexShape.down _).next_eq' rfl)
      (h (1 + 1)) (chosenBoundaryBasis C c ((1 + 1) + 1) (1 + 1))
      (chosenBoundaryBasis C c (1 + 1) 1)
      (chosenBoundaryLift C c (1 + 1) 1) (chosenBoundaryLift_spec C c (1 + 1) 1))⁻¹

/-- The torsion of a parity complex of vector spaces with ordered bases `c 0` of its even space and
`c 1` of its odd space: when `C` is acyclic, the ratio `[b₁ s₀ / c₁] · [b₀ s₁ / c₀]⁻¹` of the
brackets of its odd and even degrees, for a choice of bases `bᵢ` of the boundaries and lifts `sᵢ`
of `bᵢ`, and `0` otherwise. The ratio does not depend on these choices
(`parityTorsion_eq_mul_inv`). -/
def parityTorsion : F := by
  classical
  exact if h : C.Acyclic then parityTorsionOfAcyclic C c h else 0

/-- The torsion of a parity complex that is not acyclic is `0`. -/
@[simp]
theorem parityTorsion_of_not_acyclic (h : ¬C.Acyclic) : C.parityTorsion c = 0 := by
  simp [parityTorsion, h]

/-- The torsion of an acyclic parity complex is nonzero. -/
theorem parityTorsion_ne_zero (h : C.Acyclic) : C.parityTorsion c ≠ 0 := by
  rw [parityTorsion, dite_eq_left h, parityTorsionOfAcyclic]
  exact mul_ne_zero (torsionBracket_ne_zero c _ _ _ _ _ _ _)
    (inv_ne_zero (torsionBracket_ne_zero c _ _ _ _ _ _ _))

/-- The torsion of a based parity complex vanishes if and only if the complex is not acyclic. -/
theorem parityTorsion_eq_zero_iff : C.parityTorsion c = 0 ↔ ¬C.Acyclic :=
  ⟨fun h₀ h ↦ C.parityTorsion_ne_zero c h h₀, C.parityTorsion_of_not_acyclic c⟩

variable {C c}

/-- For an acyclic parity complex, the torsion is the ratio `[b₁ s₀ / c₁] · [b₀ s₁ / c₀]⁻¹` of the
brackets for any bases `bⱼ` of the boundaries and any lifts `sⱼ` of `bⱼ`; the bases `bⱼ` may be
indexed by any `Fin (r j)`. -/
theorem parityTorsion_eq_mul_inv (h : C.Acyclic) {r : ZMod 2 → ℕ}
    (b : ∀ j, Basis (Fin (r j)) F (LinearMap.range (C.d (j + 1) j).hom))
    (s : ∀ j, Fin (r j) → C.X (j + 1)) (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k) :
    C.parityTorsion c =
      torsionBracket c ((ComplexShape.down _).prev_eq' rfl) ((ComplexShape.down _).next_eq' rfl)
        (h (0 + 1)) (b (0 + 1)) (b 0) (s 0) (hs 0) *
        (torsionBracket c ((ComplexShape.down _).prev_eq' rfl) ((ComplexShape.down _).next_eq' rfl)
          (h (1 + 1)) (b (1 + 1)) (b 1) (s 1) (hs 1))⁻¹ := by
  have hr (j : ZMod 2) : r j = finrank F (LinearMap.range (C.d (j + 1) j).hom) := by
    rw [finrank_eq_card_basis (b j), Fintype.card_fin]
  rw [← torsionBracket_reindex c ((ComplexShape.down _).prev_eq' rfl)
    ((ComplexShape.down _).next_eq' rfl) (h (0 + 1)) (b (0 + 1)) (b 0) (s 0) (hs 0) (hr (0 + 1))
    (hr 0),
    ← torsionBracket_reindex c ((ComplexShape.down _).prev_eq' rfl)
      ((ComplexShape.down _).next_eq' rfl) (h (1 + 1)) (b (1 + 1)) (b 1) (s 1) (hs 1) (hr (1 + 1))
      (hr 1),
    torsionBracket_eq_mul c ((ComplexShape.down _).prev_eq' rfl)
      ((ComplexShape.down _).next_eq' rfl) (h (0 + 1))
      (chosenBoundaryBasis C c ((0 + 1) + 1) (0 + 1))
      (chosenBoundaryBasis C c (0 + 1) 0) (chosenBoundaryLift C c (0 + 1) 0)
        (chosenBoundaryLift_spec C c (0 + 1) 0),
    torsionBracket_eq_mul c ((ComplexShape.down _).prev_eq' rfl)
      ((ComplexShape.down _).next_eq' rfl) (h (1 + 1))
      (chosenBoundaryBasis C c ((1 + 1) + 1) (1 + 1))
      (chosenBoundaryBasis C c (1 + 1) 1) (chosenBoundaryLift C c (1 + 1) 1)
        (chosenBoundaryLift_spec C c (1 + 1) 1),
    parityTorsion, dite_eq_left h, parityTorsionOfAcyclic]
  -- Changing the boundary bases multiplies the odd bracket by `[b'₁ / b₁] [b'₀ / b₀]` and the
  -- even bracket by `[b'₀ / b₀] [b'₁ / b₁]`, read in the degrees `0 + 1 = 1` and `1 + 1 = 0`.
  have hD {j j' : ZMod 2} (hj : j = j') :
      (chosenBoundaryBasis C c (j + 1) j).det ((b j).reindex (finCongr (hr j))) =
        (chosenBoundaryBasis C c (j' + 1) j').det ((b j').reindex (finCongr (hr j'))) := by
    subst hj; rfl
  have hD₀ :=
    (Basis.isUnit_det (chosenBoundaryBasis C c (0 + 1) 0) ((b 0).reindex (finCongr (hr 0)))).ne_zero
  have hD₁ :=
    (Basis.isUnit_det (chosenBoundaryBasis C c (1 + 1) 1) ((b 1).reindex (finCongr (hr 1)))).ne_zero
  rw [hD (zero_add 1), hD (CharTwo.add_self_eq_zero 1)]
  field_simp [torsionBracket_ne_zero]

variable (c) in
/-- The basis-change formula for the torsion of a parity complex: replacing the bases `c i` by
`c' i` multiplies the torsion by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹`, where `[c'ᵢ / cᵢ]` is the
determinant of `c' i` with respect to `c i`. This holds for every complex, both sides being `0`
when `C` is not acyclic. -/
theorem parityTorsion_eq_mul_det (c' : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    C.parityTorsion c' = C.parityTorsion c * ((c 0).det (c' 0) * ((c 1).det (c' 1))⁻¹) := by
  by_cases h : C.Acyclic
  swap
  · simp [parityTorsion_of_not_acyclic _ _ h]
  rw [parityTorsion_eq_mul_inv (c := c') h (fun j ↦ chosenBoundaryBasis C c (j + 1) j)
    (fun j ↦ chosenBoundaryLift C c (j + 1) j)
      (fun j ↦ chosenBoundaryLift_spec C c (j + 1) j),
    parityTorsion_eq_mul_inv (c := c) h (fun j ↦ chosenBoundaryBasis C c (j + 1) j)
      (fun j ↦ chosenBoundaryLift C c (j + 1) j)
      (fun j ↦ chosenBoundaryLift_spec C c (j + 1) j),
    torsionBracket_eq_det_mul c (c' := c'), torsionBracket_eq_det_mul c (c' := c')]
  -- The bracket in degree `j + 1` changes by `[cⱼ₊₁ / c'ⱼ₊₁]`, read in the degrees `0 + 1 = 1`
  -- and `1 + 1 = 0`.
  have hD {j j' : ZMod 2} (hj : j = j') : (c' j).det (c j) = (c' j').det (c j') := by
    subst hj; rfl
  have hinv (j : ZMod 2) : (c j).det (c' j) = ((c' j).det (c j))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  have hD₀ := (Basis.isUnit_det (c' 0) (c 0)).ne_zero
  have hD₁ := (Basis.isUnit_det (c' 1) (c 1)).ne_zero
  rw [hD (zero_add 1), hD (CharTwo.add_self_eq_zero 1), hinv, hinv]
  field_simp [torsionBracket_ne_zero]

variable (c) in
/-- Reordering the bases `c i` of a parity complex by permutations `σ i` multiplies the torsion by
the product of the signs of `σ 0` and `σ 1`. -/
theorem parityTorsion_reindex (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    C.parityTorsion (fun i ↦ (c i).reindex (σ i)) =
      C.parityTorsion c * (((Equiv.Perm.sign (σ 0) * Equiv.Perm.sign (σ 1) : ℤˣ) : ℤ) : F) := by
  rw [parityTorsion_eq_mul_det c]
  congr 1
  simp only [Basis.coe_reindex, AlternatingMap.map_perm, Basis.det_self, Equiv.Perm.sign_symm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (σ 0)) with h₀ | h₀ <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign (σ 1)) with h₁ | h₁ <;>
    simp [h₀, h₁]

variable (c) in
/-- Rescaling the vectors of the bases `c i` of a parity complex by units `w i k` multiplies the
torsion by `(∏ₖ w 0 k) · (∏ₖ w 1 k)⁻¹`. -/
theorem parityTorsion_unitsSMul (w : ∀ i, Fin (n i) → Fˣ) :
    C.parityTorsion (fun i ↦ (c i).unitsSMul (w i)) =
      C.parityTorsion c * ((∏ k, (w 0 k : F)) * (∏ k, (w 1 k : F))⁻¹) := by
  rw [parityTorsion_eq_mul_det c]
  simp

/-! ### Elementary complexes -/

/-- The bracket of a parity complex for the chosen bases of the boundaries and the chosen lifts
depends only on the index `j`, not on how it is written. -/
private theorem torsionBracket_chosen_congr (h : C.Acyclic) {j j' : ZMod 2} (hj : j = j') :
    torsionBracket c ((ComplexShape.down _).prev_eq' rfl) ((ComplexShape.down _).next_eq' rfl)
      (h (j + 1)) (chosenBoundaryBasis C c ((j + 1) + 1) (j + 1))
      (chosenBoundaryBasis C c (j + 1) j)
        (chosenBoundaryLift C c (j + 1) j) (chosenBoundaryLift_spec C c (j + 1) j) =
      torsionBracket c ((ComplexShape.down _).prev_eq' rfl) ((ComplexShape.down _).next_eq' rfl)
        (h (j' + 1)) (chosenBoundaryBasis C c ((j' + 1) + 1) (j' + 1))
        (chosenBoundaryBasis C c (j' + 1) j') (chosenBoundaryLift C c (j' + 1) j')
        (chosenBoundaryLift_spec C c (j' + 1) j') := by
  subst hj; rfl

/-- The determinant of the chosen basis of the boundaries `Bⱼ` depends only on the index `j`, not
on how it is written. -/
private theorem det_chosenBoundaryBasis_congr {j j' : ZMod 2} (hj : j = j')
    (hj₁ : n j = finrank F (LinearMap.range (C.d (j + 1) j).hom))
    (hj₂ : n j' = finrank F (LinearMap.range (C.d (j' + 1) j').hom)) :
    ((c j).det fun k ↦ (chosenBoundaryBasis C c (j + 1) j (Fin.cast hj₁ k) : C.X j)) =
      (c j').det fun k ↦ (chosenBoundaryBasis C c (j' + 1) j' (Fin.cast hj₂ k) : C.X j') := by
  subst hj; rfl

/-- The determinant of the images of the basis `c j` under the differential into `Cᵢ` depends only
on the index `j`, not on how it is written. -/
private theorem det_d_congr {i j j' : ZMod 2} (hj : j = j') (h₁ : n i = n j) (h₂ : n i = n j') :
    ((c i).det fun k ↦ (C.d j i).hom (c j (Fin.cast h₁ k))) =
      (c i).det fun k ↦ (C.d j' i).hom (c j' (Fin.cast h₂ k)) := by
  subst hj; rfl

/-- In an acyclic parity complex where `C.d (j + 1 + 1) (j + 1)` vanishes and `C.d (j + 1) j` is
bijective, the bracket in degree `j + 1 + 1 = j` is the bracket in degree `j + 1` times the
determinant of `C.d (j + 1) j` in the bases `c (j + 1)` and `c j`. -/
private theorem torsionBracket_chosen_eq_det_mul {j : ZMod 2} (h : C.Acyclic)
    (hd : C.d (j + 1 + 1) (j + 1) = 0) (hbij : Function.Bijective (C.d (j + 1) j).hom) :
    torsionBracket c ((ComplexShape.down _).prev_eq' rfl) ((ComplexShape.down _).next_eq' rfl)
      (h (j + 1 + 1)) (chosenBoundaryBasis C c ((j + 1 + 1) + 1) (j + 1 + 1))
        (chosenBoundaryBasis C c ((j + 1) + 1) (j + 1))
          (chosenBoundaryLift C c ((j + 1) + 1) (j + 1))
        (chosenBoundaryLift_spec C c ((j + 1) + 1) (j + 1)) =
      ((c j).det fun k ↦ (C.d (j + 1) j).hom
          (c (j + 1) (Fin.cast (card_eq_card_of_bijective_d (c (j + 1)) (c j) hbij).symm k))) *
        torsionBracket c ((ComplexShape.down _).prev_eq' rfl) ((ComplexShape.down _).next_eq' rfl)
          (h (j + 1)) (chosenBoundaryBasis C c ((j + 1) + 1) (j + 1))
          (chosenBoundaryBasis C c (j + 1) j) (chosenBoundaryLift C c (j + 1) j)
          (chosenBoundaryLift_spec C c (j + 1) j) := by
  have hj : j + 1 + 1 = j := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  -- The boundaries `Bⱼ₊₁` vanish, so the bracket in degree `j + 1` is the determinant of the lifts
  -- `sⱼ` of a basis `bⱼ` of `Bⱼ = Cⱼ`, and the bracket in degree `j + 1 + 1` is the determinant of
  -- `bⱼ`, read in degree `j + 1 + 1`.
  have hq₀ := eq_add_of_exactAt c ((ComplexShape.down _).prev_eq' rfl)
    ((ComplexShape.down _).next_eq' rfl) (h (j + 1)) (chosenBoundaryBasis C c ((j + 1) + 1) (j + 1))
    (chosenBoundaryBasis C c (j + 1) j)
  have hp₀ := eq_add_of_exactAt c ((ComplexShape.down _).prev_eq' rfl)
    ((ComplexShape.down _).next_eq' rfl) (h (j + 1 + 1))
    (chosenBoundaryBasis C c ((j + 1 + 1) + 1) (j + 1 + 1))
    (chosenBoundaryBasis C c ((j + 1) + 1) (j + 1))
  have hr : finrank F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom) = 0 := by
    rw [hd, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]
  have hq : n (j + 1) = finrank F (LinearMap.range (C.d (j + 1) j).hom) := by omega
  have hp : n (j + 1 + 1) = finrank F (LinearMap.range (C.d (j + 1 + 1 + 1) (j + 1 + 1)).hom) := by
    omega
  rw [torsionBracket_eq_det_right c ((ComplexShape.down _).prev_eq' rfl)
    ((ComplexShape.down _).next_eq' rfl) (h (j + 1)) _ _ _ _ hq,
    torsionBracket_eq_det_left c ((ComplexShape.down _).prev_eq' rfl)
      ((ComplexShape.down _).next_eq' rfl) (h (j + 1 + 1)) _ _ _ _ hp]
  have hn : n j = n (j + 1) := (card_eq_card_of_bijective_d (c (j + 1)) (c j) hbij).symm
  rw [det_chosenBoundaryBasis_congr hj hp (hn.trans hq)]
  -- The basis `bⱼ` of `Cⱼ` is the image of the lifts `sⱼ` under the differential `Cⱼ₊₁ → Cⱼ`.
  have hb : (fun k ↦ (chosenBoundaryBasis C c (j + 1) j (Fin.cast (hn.trans hq) k) : C.X j)) =
      (C.d (j + 1) j).hom ∘ (chosenBoundaryLift C c (j + 1) j ∘ Fin.cast (hn.trans hq)) := by
    ext k
    simp
  rw [hb, Basis.det_comp_eq_mul ((c (j + 1)).reindex (finCongr hn.symm)) (c j),
    Basis.det_reindex]
  have hs : (chosenBoundaryLift C c (j + 1) j ∘ Fin.cast (hn.trans hq)) ∘ finCongr hn.symm =
      chosenBoundaryLift C c (j + 1) j ∘ Fin.cast hq := by
    ext k
    simp
  have hc : (C.d (j + 1) j).hom ∘ (c (j + 1)).reindex (finCongr hn.symm) =
      fun k ↦ (C.d (j + 1) j).hom (c (j + 1) (Fin.cast hn k)) := by
    ext k
    simp
  rw [hs, hc]

/-- The torsion of an acyclic parity complex whose even-to-odd differential vanishes: its
odd-to-even differential `C₁ → C₀` is then an isomorphism, and the torsion is the inverse of the
determinant of that differential in the bases `c 1` and `c 0`. For instance multiplication by
`a ≠ 0` on `F`, from the odd to the even space, has torsion `a⁻¹`. -/
theorem parityTorsion_eq_inv_det (hd : C.d 0 1 = 0) (hbij : Function.Bijective (C.d 1 0).hom) :
    C.parityTorsion c = ((c 0).det fun k ↦
      (C.d 1 0).hom (c 1 (Fin.cast (card_eq_card_of_bijective_d (c 1) (c 0) hbij).symm k)))⁻¹ := by
  have h := (acyclic_iff_bijective_d_one_zero hd).2 hbij
  have hb : Function.Bijective (C.d (0 + 1) 0).hom := by rwa [zero_add]
  have hd' : C.d (0 + 1 + 1) (0 + 1) = 0 := by rwa [zero_add, CharTwo.add_self_eq_zero]
  rw [parityTorsion_eq_mul_inv h (fun j ↦ chosenBoundaryBasis C c (j + 1) j)
    (fun j ↦ chosenBoundaryLift C c (j + 1) j)
      (fun j ↦ chosenBoundaryLift_spec C c (j + 1) j),
    ← torsionBracket_chosen_congr h (zero_add 1), torsionBracket_chosen_eq_det_mul h hd' hb,
    det_d_congr (zero_add 1), mul_inv_rev,
    mul_inv_cancel_left₀ (torsionBracket_ne_zero c _ _ _ _ _ _ _)]

/-- The torsion of an acyclic parity complex whose odd-to-even differential vanishes: its
even-to-odd differential `C₀ → C₁` is then an isomorphism, and the torsion is the determinant of
that differential in the bases `c 0` and `c 1`. For instance multiplication by `a ≠ 0` on `F`, from
the even to the odd space, has torsion `a`. -/
theorem parityTorsion_eq_det (hd : C.d 1 0 = 0) (hbij : Function.Bijective (C.d 0 1).hom) :
    C.parityTorsion c = (c 1).det fun k ↦
      (C.d 0 1).hom (c 0 (Fin.cast (card_eq_card_of_bijective_d (c 0) (c 1) hbij).symm k)) := by
  have h := (acyclic_iff_bijective_d_zero_one hd).2 hbij
  have hb : Function.Bijective (C.d (1 + 1) 1).hom := by rwa [CharTwo.add_self_eq_zero]
  have hd' : C.d (1 + 1 + 1) (1 + 1) = 0 := by rwa [CharTwo.add_self_eq_zero, zero_add]
  rw [parityTorsion_eq_mul_inv h (fun j ↦ chosenBoundaryBasis C c (j + 1) j)
    (fun j ↦ chosenBoundaryLift C c (j + 1) j)
      (fun j ↦ chosenBoundaryLift_spec C c (j + 1) j),
    ← torsionBracket_chosen_congr h (CharTwo.add_self_eq_zero (1 : ZMod 2)),
    torsionBracket_chosen_eq_det_mul h hd' hb, det_d_congr (CharTwo.add_self_eq_zero 1),
    mul_inv_cancel_right₀ (torsionBracket_ne_zero c _ _ _ _ _ _ _)]

variable (c) in
/-- The zero parity complex, with empty bases, is acyclic and has torsion `1`. -/
theorem parityTorsion_eq_one (h₀ : n 0 = 0) (h₁ : n 1 = 0) : C.parityTorsion c = 1 := by
  have hn (i : ZMod 2) : n i = 0 := by
    fin_cases i
    exacts [h₀, h₁]
  have h : C.Acyclic := fun i ↦ by
    have : IsEmpty (Fin (n i)) := by rw [hn i]; infer_instance
    have : Subsingleton (C.X i) := ⟨fun x y ↦ (c i).ext_elem fun k ↦ isEmptyElim k⟩
    exact (C.sc i).exact_of_isZero_X₂ (ModuleCat.isZero_of_subsingleton (C.X i))
  rw [parityTorsion_eq_mul_inv h (fun j ↦ chosenBoundaryBasis C c (j + 1) j)
    (fun j ↦ chosenBoundaryLift C c (j + 1) j)
      (fun j ↦ chosenBoundaryLift_spec C c (j + 1) j),
    torsionBracket_eq_one c _ _ _ _ _ _ _ (hn _), torsionBracket_eq_one c _ _ _ _ _ _ _ (hn _),
      inv_one,
    mul_one]

end ChainComplex
