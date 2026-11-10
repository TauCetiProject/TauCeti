/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import TauCeti.Algebra.Homology.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The torsion of a based parity complex over a field

A *parity complex* over a field `F` is a chain complex `C` indexed by `ZMod 2`: an even space
`C₀`, an odd space `C₁`, and differentials `C₁ → C₀` and `C₀ → C₁` whose composites vanish.
Floer complexes whose grading is only defined modulo two, such as the Floer–Novikov complexes of a
symplectomorphism, are of this kind. They are not bounded integer complexes, so the torsion
`HomologicalComplex.reidemeisterTorsion` of a based `ℤ`-graded complex does not apply to them;
this file defines their torsion with the same brackets.

Let `C` have ordered bases `c 0` of `C₀` and `c 1` of `C₁`. Write `Bᵢ ⊆ Cᵢ` for the boundaries,
the images of the differentials into `Cᵢ`. When `C` is acyclic, a basis `bᵢ` of `Bᵢ` and lifts
`sᵢ` of `bᵢ` through the differential into `Cᵢ` give the brackets
`[b₁ s₀ / c₁]` and `[b₀ s₁ / c₀]` of `HomologicalComplex.torsionBracket`, the determinants of the
bases `(b₁, s₀)` of `C₁` and `(b₀, s₁)` of `C₀`. The torsion of `C` is

`τ(C) = [b₁ s₀ / c₁] · [b₀ s₁ / c₀]⁻¹`

(`HomologicalComplex.parityTorsion`), and `0` when `C` is not acyclic. As for `ℤ`-graded
complexes, the bracket of an odd degree enters with exponent `1` and that of an even degree with
exponent `-1`. The value does not depend on the bases of the boundaries nor on the lifts
(`HomologicalComplex.parityTorsion_eq`): changing `b₀` or `b₁` multiplies both brackets by the
same determinant.

With this normalization the complex `F → F` given by multiplication by `a ≠ 0` from the odd to
the even space has torsion `a⁻¹`, and the same map from the even to the odd space has torsion `a`
(`HomologicalComplex.parityTorsion_eq_inv_det`, `HomologicalComplex.parityTorsion_eq_det`). The
zero complex is acyclic and has torsion `1` (`HomologicalComplex.parityTorsion_eq_one`), whereas
a complex with nonzero homology, such as `F` placed in even degree, has torsion `0`
(`HomologicalComplex.parityTorsion_eq_zero_iff`).

## Main declarations

* `HomologicalComplex.parityTorsion`: the torsion of a based parity complex.
* `HomologicalComplex.parityTorsion_eq`: for an acyclic complex, the torsion is the ratio of the
  brackets for any bases of the boundaries and any lifts.
* `HomologicalComplex.parityTorsion_eq_zero_iff`: the torsion vanishes exactly when the complex is
  not acyclic.
* `HomologicalComplex.parityTorsion_eq_mul_det`: replacing the bases `c i` by `c' i` multiplies
  the torsion by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹`.
* `HomologicalComplex.parityTorsion_reindex`, `HomologicalComplex.parityTorsion_unitsSMul`: the
  effect of reordering and of rescaling the bases.
* `HomologicalComplex.acyclic_iff_bijective_d_one_zero`,
  `HomologicalComplex.acyclic_iff_bijective_d_zero_one`: when one differential vanishes, the
  complex is acyclic exactly when the other one is bijective.
* `HomologicalComplex.parityTorsion_eq_inv_det`, `HomologicalComplex.parityTorsion_eq_det`: the
  torsion of such an elementary complex is the determinant of its bijective differential, inverted
  when that differential goes from odd to even degree.
* `HomologicalComplex.parityTorsion_eq_one`: the torsion of the zero complex is `1`.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F] (C : ChainComplex (ModuleCat F) (ZMod 2))
  {n : ZMod 2 → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))

/-- The ratio of the brackets of an acyclic parity complex, for the bases `chosenBoundaryBasis` of
the boundaries and the lifts `chosenBoundaryLift`. -/
private def parityTorsionOfAcyclic (h : C.Acyclic) : F :=
  torsionBracket c (h (0 + 1)) (chosenBoundaryBasis C c (0 + 1)) (chosenBoundaryBasis C c 0)
      (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0) *
    (torsionBracket c (h (1 + 1)) (chosenBoundaryBasis C c (1 + 1)) (chosenBoundaryBasis C c 1)
      (chosenBoundaryLift C c 1) (chosenBoundaryLift_spec C c 1))⁻¹

/-- The torsion of a parity complex of vector spaces with ordered bases `c 0` of its even space and
`c 1` of its odd space: when `C` is acyclic, the ratio `[b₁ s₀ / c₁] · [b₀ s₁ / c₀]⁻¹` of the
brackets of its odd and even degrees, for a choice of bases `bᵢ` of the boundaries and lifts `sᵢ`
of `bᵢ`, and `0` otherwise. The ratio does not depend on these choices (`parityTorsion_eq`). -/
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
  exact mul_ne_zero (torsionBracket_ne_zero c _ _ _ _ _)
    (inv_ne_zero (torsionBracket_ne_zero c _ _ _ _ _))

/-- The torsion of a based parity complex vanishes if and only if the complex is not acyclic. -/
theorem parityTorsion_eq_zero_iff : C.parityTorsion c = 0 ↔ ¬C.Acyclic :=
  ⟨fun h₀ h ↦ C.parityTorsion_ne_zero c h h₀, C.parityTorsion_of_not_acyclic c⟩

/-- In `ZMod 2`, `0 + 1 = 1`; the brackets of a parity complex are indexed by `j + 1`. -/
private theorem zero_add_one : (0 + 1 : ZMod 2) = 1 := by decide

/-- In `ZMod 2`, `1 + 1 = 0`. -/
private theorem one_add_one : (1 + 1 : ZMod 2) = 0 := by decide

variable {C c}

/-- For an acyclic parity complex, the torsion is the ratio `[b₁ s₀ / c₁] · [b₀ s₁ / c₀]⁻¹` of the
brackets for any bases `bⱼ` of the boundaries and any lifts `sⱼ` of `bⱼ`; the bases `bⱼ` may be
indexed by any `Fin (r j)`. -/
theorem parityTorsion_eq (h : C.Acyclic) {r : ZMod 2 → ℕ}
    (b : ∀ j, Basis (Fin (r j)) F (LinearMap.range (C.d (j + 1) j).hom))
    (s : ∀ j, Fin (r j) → C.X (j + 1)) (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k) :
    C.parityTorsion c =
      torsionBracket c (h (0 + 1)) (b (0 + 1)) (b 0) (s 0) (hs 0) *
        (torsionBracket c (h (1 + 1)) (b (1 + 1)) (b 1) (s 1) (hs 1))⁻¹ := by
  have hr (j : ZMod 2) : r j = finrank F (LinearMap.range (C.d (j + 1) j).hom) := by
    rw [finrank_eq_card_basis (b j), Fintype.card_fin]
  rw [← torsionBracket_reindex c (h (0 + 1)) (b (0 + 1)) (b 0) (s 0) (hs 0) (hr (0 + 1)) (hr 0),
    ← torsionBracket_reindex c (h (1 + 1)) (b (1 + 1)) (b 1) (s 1) (hs 1) (hr (1 + 1)) (hr 1),
    torsionBracket_eq_mul c (h (0 + 1)) (chosenBoundaryBasis C c (0 + 1))
      (chosenBoundaryBasis C c 0) (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0),
    torsionBracket_eq_mul c (h (1 + 1)) (chosenBoundaryBasis C c (1 + 1))
      (chosenBoundaryBasis C c 1) (chosenBoundaryLift C c 1) (chosenBoundaryLift_spec C c 1),
    parityTorsion, dite_eq_left h, parityTorsionOfAcyclic]
  -- Changing the boundary bases multiplies the odd bracket by `[b'₁ / b₁] [b'₀ / b₀]` and the
  -- even bracket by `[b'₀ / b₀] [b'₁ / b₁]`, read in the degrees `0 + 1 = 1` and `1 + 1 = 0`.
  have hD {j j' : ZMod 2} (hj : j = j') :
      (chosenBoundaryBasis C c j).det ((b j).reindex (finCongr (hr j))) =
        (chosenBoundaryBasis C c j').det ((b j').reindex (finCongr (hr j'))) := by
    subst hj; rfl
  have hD₀ :=
    (Basis.isUnit_det (chosenBoundaryBasis C c 0) ((b 0).reindex (finCongr (hr 0)))).ne_zero
  have hD₁ :=
    (Basis.isUnit_det (chosenBoundaryBasis C c 1) ((b 1).reindex (finCongr (hr 1)))).ne_zero
  rw [hD zero_add_one, hD one_add_one]
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
  rw [parityTorsion_eq (c := c') h (chosenBoundaryBasis C c) (chosenBoundaryLift C c)
      (chosenBoundaryLift_spec C c),
    parityTorsion_eq (c := c) h (chosenBoundaryBasis C c) (chosenBoundaryLift C c)
      (chosenBoundaryLift_spec C c),
    torsionBracket_eq_det_mul c (c' := c'), torsionBracket_eq_det_mul c (c' := c')]
  -- The bracket in degree `j + 1` changes by `[cⱼ₊₁ / c'ⱼ₊₁]`, read in the degrees `0 + 1 = 1`
  -- and `1 + 1 = 0`.
  have hD {j j' : ZMod 2} (hj : j = j') : (c' j).det (c j) = (c' j').det (c j') := by
    subst hj; rfl
  have hinv (j : ZMod 2) : (c j).det (c' j) = ((c' j).det (c j))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  have hD₀ := (Basis.isUnit_det (c' 0) (c 0)).ne_zero
  have hD₁ := (Basis.isUnit_det (c' 1) (c 1)).ne_zero
  rw [hD zero_add_one, hD one_add_one, hinv, hinv]
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

/-- The determinant of the chosen basis of the boundaries `Bⱼ` depends only on the index `j`, not
on how it is written: the brackets of a parity complex read the even degree as `1 + 1`. -/
private theorem det_chosenBoundaryBasis_congr {j j' : ZMod 2} (hj : j = j')
    (hj₁ : n j = finrank F (LinearMap.range (C.d (j + 1) j).hom))
    (hj₂ : n j' = finrank F (LinearMap.range (C.d (j' + 1) j').hom)) :
    ((c j).det fun k ↦ (chosenBoundaryBasis C c j (Fin.cast hj₁ k) : C.X j)) =
      (c j').det fun k ↦ (chosenBoundaryBasis C c j' (Fin.cast hj₂ k) : C.X j') := by
  subst hj; rfl

/-- The determinant of the images of the basis `c j` under the differential into `Cᵢ` depends only
on the index `j`, not on how it is written. -/
private theorem det_d_congr {i j j' : ZMod 2} (hj : j = j') (h₁ : n i = n j) (h₂ : n i = n j') :
    ((c i).det fun k ↦ (C.d j i).hom (c j (Fin.cast h₁ k))) =
      (c i).det fun k ↦ (C.d j' i).hom (c j' (Fin.cast h₂ k)) := by
  subst hj; rfl

/-- A parity complex whose even-to-odd differential vanishes is acyclic exactly when its
odd-to-even differential is bijective. -/
theorem acyclic_iff_bijective_d_one_zero (hd : C.d 0 1 = 0) :
    C.Acyclic ↔ Function.Bijective (C.d 1 0).hom := by
  have e₀ := C.exactAt_iff' 1 0 1 ((ChainComplex.prev _ 0).trans zero_add_one)
    ((ChainComplex.next _ 0).trans (by decide))
  have e₁ := C.exactAt_iff' 0 1 0 ((ChainComplex.prev _ 1).trans one_add_one)
    ((ChainComplex.next _ 1).trans (sub_self 1))
  simp only [ShortComplex.moduleCat_exact_iff_range_eq_ker, shortComplexFunctor'_obj_f,
    shortComplexFunctor'_obj_g, hd, ModuleCat.hom_zero, LinearMap.range_zero,
    LinearMap.ker_zero] at e₀ e₁
  rw [Function.Bijective, ← LinearMap.ker_eq_bot, ← LinearMap.range_eq_top, eq_comm, ← e₀, ← e₁]
  constructor
  · exact fun h ↦ ⟨h 1, h 0⟩
  · rintro ⟨h₁, h₀⟩ i
    fin_cases i
    exacts [h₀, h₁]

/-- A parity complex whose odd-to-even differential vanishes is acyclic exactly when its
even-to-odd differential is bijective. -/
theorem acyclic_iff_bijective_d_zero_one (hd : C.d 1 0 = 0) :
    C.Acyclic ↔ Function.Bijective (C.d 0 1).hom := by
  have e₀ := C.exactAt_iff' 1 0 1 ((ChainComplex.prev _ 0).trans zero_add_one)
    ((ChainComplex.next _ 0).trans (by decide))
  have e₁ := C.exactAt_iff' 0 1 0 ((ChainComplex.prev _ 1).trans one_add_one)
    ((ChainComplex.next _ 1).trans (sub_self 1))
  simp only [ShortComplex.moduleCat_exact_iff_range_eq_ker, shortComplexFunctor'_obj_f,
    shortComplexFunctor'_obj_g, hd, ModuleCat.hom_zero, LinearMap.range_zero,
    LinearMap.ker_zero] at e₀ e₁
  rw [Function.Bijective, ← LinearMap.ker_eq_bot, ← LinearMap.range_eq_top, eq_comm, ← e₀, ← e₁]
  constructor
  · exact fun h ↦ ⟨h 0, h 1⟩
  · rintro ⟨h₀, h₁⟩ i
    fin_cases i
    exacts [h₀, h₁]

/-- The torsion of an acyclic parity complex whose even-to-odd differential vanishes: its
odd-to-even differential `C₁ → C₀` is then an isomorphism, and the torsion is the inverse of the
determinant of that differential in the bases `c 1` and `c 0`. For instance multiplication by
`a ≠ 0` on `F`, from the odd to the even space, has torsion `a⁻¹`. -/
theorem parityTorsion_eq_inv_det (hd : C.d 0 1 = 0) (hbij : Function.Bijective (C.d 1 0).hom) :
    C.parityTorsion c = ((c 0).det fun k ↦
      (C.d 1 0).hom (c 1 (Fin.cast (card_eq_card_of_bijective_d C c hbij).symm k)))⁻¹ := by
  have h := (acyclic_iff_bijective_d_one_zero hd).2 hbij
  have hb₁ : Function.Bijective (C.d (0 + 1) 0).hom := by rwa [zero_add_one]
  have hd₁ : C.d (0 + 1 + 1) (0 + 1) = 0 := by rwa [zero_add_one, one_add_one]
  have hd₂ : C.d (1 + 1) 1 = 0 := by rwa [one_add_one]
  -- The odd boundaries vanish, so the odd bracket is the determinant of the lifts `s₀` of a basis
  -- `b₀` of `B₀ = C₀`, and the even bracket is the determinant of `b₀`, read in degree `1 + 1`.
  have hq₀ := eq_add_of_exactAt c (h (0 + 1)) (chosenBoundaryBasis C c (0 + 1))
    (chosenBoundaryBasis C c 0)
  have hp₀ := eq_add_of_exactAt c (h (1 + 1)) (chosenBoundaryBasis C c (1 + 1))
    (chosenBoundaryBasis C c 1)
  have hr₁ : finrank F (LinearMap.range (C.d (0 + 1 + 1) (0 + 1)).hom) = 0 := by
    rw [hd₁, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]
  have hr₂ : finrank F (LinearMap.range (C.d (1 + 1) 1).hom) = 0 := by
    rw [hd₂, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]
  have hq : n (0 + 1) = finrank F (LinearMap.range (C.d (0 + 1) 0).hom) := by omega
  have hp : n (1 + 1) = finrank F (LinearMap.range (C.d (1 + 1 + 1) (1 + 1)).hom) := by omega
  have hX := torsionBracket_ne_zero c (h (0 + 1)) (chosenBoundaryBasis C c (0 + 1))
    (chosenBoundaryBasis C c 0) (chosenBoundaryLift C c 0) (chosenBoundaryLift_spec C c 0)
  rw [torsionBracket_eq_det_right c (h (0 + 1)) _ _ _ _ hq] at hX
  rw [parityTorsion_eq h (chosenBoundaryBasis C c) (chosenBoundaryLift C c)
      (chosenBoundaryLift_spec C c),
    torsionBracket_eq_det_right c (h (0 + 1)) _ _ _ _ hq,
    torsionBracket_eq_det_left c (h (1 + 1)) _ _ _ _ hp]
  have hn : n 0 = n (0 + 1) := (card_eq_card_of_bijective_d C c hb₁).symm
  rw [det_chosenBoundaryBasis_congr one_add_one hp (hn.trans hq)]
  -- The basis `b₀` of `C₀` is the image of the lifts `s₀` under the differential `C₁ → C₀`.
  have hb : (fun k ↦ (chosenBoundaryBasis C c 0 (Fin.cast (hn.trans hq) k) : C.X 0)) =
      (C.d (0 + 1) 0).hom ∘ (chosenBoundaryLift C c 0 ∘ Fin.cast (hn.trans hq)) := by
    ext k
    simp
  rw [hb, Basis.det_comp_eq_mul ((c (0 + 1)).reindex (finCongr hn.symm)) (c 0),
    Basis.det_reindex]
  have hs : (chosenBoundaryLift C c 0 ∘ Fin.cast (hn.trans hq)) ∘ finCongr hn.symm =
      chosenBoundaryLift C c 0 ∘ Fin.cast hq := by
    ext k
    simp
  have hc : (C.d (0 + 1) 0).hom ∘ (c (0 + 1)).reindex (finCongr hn.symm) =
      fun k ↦ (C.d (0 + 1) 0).hom (c (0 + 1) (Fin.cast hn k)) := by
    ext k
    simp
  rw [hs, hc, det_d_congr zero_add_one hn, mul_inv_rev, mul_inv_cancel_left₀ hX]


/-- The torsion of an acyclic parity complex whose odd-to-even differential vanishes: its
even-to-odd differential `C₀ → C₁` is then an isomorphism, and the torsion is the determinant of
that differential in the bases `c 0` and `c 1`. For instance multiplication by `a ≠ 0` on `F`, from
the even to the odd space, has torsion `a`. -/
theorem parityTorsion_eq_det (hd : C.d 1 0 = 0) (hbij : Function.Bijective (C.d 0 1).hom) :
    C.parityTorsion c = (c 1).det fun k ↦
      (C.d 0 1).hom (c 0 (Fin.cast (card_eq_card_of_bijective_d C c hbij).symm k)) := by
  have h := (acyclic_iff_bijective_d_zero_one hd).2 hbij
  have hb₁ : Function.Bijective (C.d (1 + 1) 1).hom := by rwa [one_add_one]
  have hd₁ : C.d (0 + 1) 0 = 0 := by rwa [zero_add_one]
  have hd₂ : C.d (1 + 1 + 1) (1 + 1) = 0 := by rwa [one_add_one, zero_add_one]
  -- The even boundaries vanish, so the odd bracket is the determinant of a basis `b₁` of
  -- `B₁ = C₁`, read in degree `0 + 1`, and the even bracket is the determinant of its lifts `s₁`.
  have hp₀ := eq_add_of_exactAt c (h (0 + 1)) (chosenBoundaryBasis C c (0 + 1))
    (chosenBoundaryBasis C c 0)
  have hq₀ := eq_add_of_exactAt c (h (1 + 1)) (chosenBoundaryBasis C c (1 + 1))
    (chosenBoundaryBasis C c 1)
  have hr₁ : finrank F (LinearMap.range (C.d (0 + 1) 0).hom) = 0 := by
    rw [hd₁, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]
  have hr₂ : finrank F (LinearMap.range (C.d (1 + 1 + 1) (1 + 1)).hom) = 0 := by
    rw [hd₂, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]
  have hp : n (0 + 1) = finrank F (LinearMap.range (C.d (0 + 1 + 1) (0 + 1)).hom) := by omega
  have hq : n (1 + 1) = finrank F (LinearMap.range (C.d (1 + 1) 1).hom) := by omega
  have hY := torsionBracket_ne_zero c (h (1 + 1)) (chosenBoundaryBasis C c (1 + 1))
    (chosenBoundaryBasis C c 1) (chosenBoundaryLift C c 1) (chosenBoundaryLift_spec C c 1)
  rw [torsionBracket_eq_det_right c (h (1 + 1)) _ _ _ _ hq] at hY
  rw [parityTorsion_eq h (chosenBoundaryBasis C c) (chosenBoundaryLift C c)
      (chosenBoundaryLift_spec C c),
    torsionBracket_eq_det_left c (h (0 + 1)) _ _ _ _ hp,
    torsionBracket_eq_det_right c (h (1 + 1)) _ _ _ _ hq]
  have hn : n 1 = n (1 + 1) := (card_eq_card_of_bijective_d C c hb₁).symm
  rw [det_chosenBoundaryBasis_congr zero_add_one hp (hn.trans hq)]
  -- The basis `b₁` of `C₁` is the image of the lifts `s₁` under the differential `C₀ → C₁`.
  have hb : (fun k ↦ (chosenBoundaryBasis C c 1 (Fin.cast (hn.trans hq) k) : C.X 1)) =
      (C.d (1 + 1) 1).hom ∘ (chosenBoundaryLift C c 1 ∘ Fin.cast (hn.trans hq)) := by
    ext k
    simp
  rw [hb, Basis.det_comp_eq_mul ((c (1 + 1)).reindex (finCongr hn.symm)) (c 1),
    Basis.det_reindex]
  have hs : (chosenBoundaryLift C c 1 ∘ Fin.cast (hn.trans hq)) ∘ finCongr hn.symm =
      chosenBoundaryLift C c 1 ∘ Fin.cast hq := by
    ext k
    simp
  have hc : (C.d (1 + 1) 1).hom ∘ (c (1 + 1)).reindex (finCongr hn.symm) =
      fun k ↦ (C.d (1 + 1) 1).hom (c (1 + 1) (Fin.cast hn k)) := by
    ext k
    simp
  rw [hs, hc, det_d_congr one_add_one hn, mul_inv_cancel_right₀ hY]

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
  rw [parityTorsion_eq h (chosenBoundaryBasis C c) (chosenBoundaryLift C c)
      (chosenBoundaryLift_spec C c),
    torsionBracket_eq_one c _ _ _ _ _ (hn _), torsionBracket_eq_one c _ _ _ _ _ (hn _), inv_one,
    mul_one]

end HomologicalComplex
