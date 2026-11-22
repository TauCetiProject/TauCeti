/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic

/-!
# The torsion of a based two-periodic complex with based homology

Let `C` be a two-periodic complex of vector spaces over a field `F`, indexed by `ZMod 2` with
differentials `d₀ : C₀ → C₁` and `d₁ : C₁ → C₀`, such as a Floer complex graded only modulo two.
Fix ordered bases `c 0`, `c 1` of the chain spaces and `h 0`, `h 1` of the homology. The bracket
`HomologicalComplex.torsionBracketWithHomology` of a degree `j` is the determinant with respect to
`c j` of a basis `bⱼ` of the boundaries, followed by cycles `zⱼ` representing `h j` and by lifts
`sⱼ` of a basis of the boundaries of the other degree. The torsion of `C` is the quotient

`τ(C, c, h) = [b₁ z₁ s₁ / c₁] · [b₀ z₀ s₀ / c₀]⁻¹`

of the odd bracket by the even one (`HomologicalComplex.parityTorsionWithHomology`), with the
normalization of `HomologicalComplex.parityTorsion`. It needs no boundedness condition and is
never `0` (`HomologicalComplex.parityTorsionWithHomology_ne_zero`), so it keeps a nonzero scalar
for complexes that are not acyclic, where `HomologicalComplex.parityTorsion` is `0`. It does not
depend on the choices (`HomologicalComplex.parityTorsionWithHomology_eq`), it is
`HomologicalComplex.parityTorsion` for an acyclic complex
(`HomologicalComplex.parityTorsionWithHomology_eq_parityTorsion`), and replacing the bases
multiplies it by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹` for the chain bases and by `[h'₁ / h₁] · [h'₀ / h₀]⁻¹`
for the homology bases, where `[x / y]` denotes the determinant of the basis `x` with respect to
the basis `y`. When both differentials vanish it is `[z₁ / c₁] · [z₀ / c₀]⁻¹` for cycles `z`
representing the homology bases (`HomologicalComplex.parityTorsionWithHomology_of_d_eq_zero`).

## Main declarations

* `HomologicalComplex.parityTorsionWithHomology`: the torsion `τ(C, c, h)` of a two-periodic
  complex.
* `HomologicalComplex.parityTorsionWithHomology_eq`: the torsion is the quotient of the brackets
  for any boundary bases, representatives and lifts.
* `HomologicalComplex.parityTorsionWithHomology_ne_zero`: the torsion is nonzero.
* `HomologicalComplex.parityTorsionWithHomology_eq_parityTorsion`: for an acyclic complex it is
  the torsion of the based acyclic complex.
* `HomologicalComplex.parityTorsionWithHomology_eq_mul_det` and
  `HomologicalComplex.parityTorsionWithHomology_eq_mul_det_homology`: the change of the torsion
  under a change of the chain bases and of the homology bases.
* `HomologicalComplex.parityTorsionWithHomology_of_d_eq_zero`: the torsion of a complex whose
  differentials vanish.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), §2.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F]

variable {C : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
  (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {m : ZMod 2 → ℕ}
  (h : ∀ i, Basis (Fin (m i)) F (C.homology i))

variable (C) in
/-- The torsion `τ(C, c, h)` of a two-periodic complex of vector spaces with ordered bases `c 0`
of the even space and `c 1` of the odd space, and ordered bases `h 0`, `h 1` of its even and odd
homology: the quotient `[b₁ z₁ s₁ / c₁] · [b₀ z₀ s₀ / c₀]⁻¹` of the odd bracket by the even
bracket, for a choice of bases `b₀`, `b₁` of the boundaries, of cycles `z₀`, `z₁` representing
`h 0`, `h 1`, and of lifts `s₀`, `s₁`. The quotient does not depend on these choices
(`parityTorsionWithHomology_eq`). -/
def parityTorsionWithHomology : F :=
  torsionBracketWithHomology c ((ComplexShape.up _).prev_eq' (zero_add 1))
      ((ComplexShape.up _).next_eq' (CharTwo.add_self_eq_zero 1)) (chosenBoundaryBasis C c 0 1)
      (h 1) (chosenCycle C h 1) (chosenCycle_spec C h 1) (chosenBoundaryBasis C c 1 0)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0) *
    (torsionBracketWithHomology c ((ComplexShape.up _).prev_eq' (CharTwo.add_self_eq_zero 1))
      ((ComplexShape.up _).next_eq' (zero_add 1)) (chosenBoundaryBasis C c 1 0) (h 0)
      (chosenCycle C h 0) (chosenCycle_spec C h 0) (chosenBoundaryBasis C c 0 1)
      (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1))⁻¹

/-- The torsion `τ(C, c, h)` of a two-periodic complex is the quotient
`[b₁ z₁ s₁ / c₁] · [b₀ z₀ s₀ / c₀]⁻¹` of its odd bracket by its even bracket, for any bases `b₀`
of the even boundaries `B₀ = im d₁` and `b₁` of the odd boundaries `B₁ = im d₀`, any cycles `z₀`,
`z₁` representing the homology bases `h 0`, `h 1`, and any lifts `s₁` of `b₀` through `d₁` and
`s₀` of `b₁` through `d₀`. -/
theorem parityTorsionWithHomology_eq {p q : ℕ}
    (b₀ : Basis (Fin p) F (LinearMap.range (C.d 1 0).hom))
    (b₁ : Basis (Fin q) F (LinearMap.range (C.d 0 1).hom))
    (z₀ : Fin (m 0) → C.cycles 0) (hz₀ : ∀ l, C.homologyπ 0 (z₀ l) = h 0 l)
    (z₁ : Fin (m 1) → C.cycles 1) (hz₁ : ∀ l, C.homologyπ 1 (z₁ l) = h 1 l)
    (s₀ : Fin q → C.X 0) (hs₀ : ∀ l, (C.d 0 1).hom (s₀ l) = b₁ l)
    (s₁ : Fin p → C.X 1) (hs₁ : ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l) :
    C.parityTorsionWithHomology c h =
      torsionBracketWithHomology c ((ComplexShape.up _).prev_eq' (zero_add 1))
          ((ComplexShape.up _).next_eq' (CharTwo.add_self_eq_zero 1)) b₁ (h 1) z₁ hz₁ b₀ s₁
          hs₁ *
        (torsionBracketWithHomology c ((ComplexShape.up _).prev_eq' (CharTwo.add_self_eq_zero 1))
          ((ComplexShape.up _).next_eq' (zero_add 1)) b₀ (h 0) z₀ hz₀ b₁ s₀ hs₀)⁻¹ := by
  have hp : finrank F (LinearMap.range (C.d 1 0).hom) = p := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hq : finrank F (LinearMap.range (C.d 0 1).hom) = q := by
    rw [finrank_eq_card_basis b₁, Fintype.card_fin]
  -- Reindex the chosen boundary bases to `Fin p` and `Fin q`, then replace them by `b₀` and `b₁`,
  -- the chosen cycles by `z₀` and `z₁`, and the chosen lifts by `s₀` and `s₁`.
  rw [parityTorsionWithHomology,
    ← torsionBracketWithHomology_reindex c _ _ _ (h 1) _ _ _ _ (chosenBoundaryLift_spec C c 1 0)
      hq hp,
    ← torsionBracketWithHomology_reindex c _ _ _ (h 0) _ _ _ _ (chosenBoundaryLift_spec C c 0 1)
      hp hq,
    torsionBracketWithHomology_eq_mul c _ _ b₁ (h 1) z₁ hz₁ b₀ s₁ hs₁,
    torsionBracketWithHomology_eq_mul c _ _ b₀ (h 0) z₀ hz₀ b₁ s₀ hs₀, Basis.det_self,
    Basis.det_self, mul_one, mul_one]
  -- Both brackets are multiplied by the same nonzero product of determinants, which cancels.
  have h₀ := (b₀.isUnit_det ((chosenBoundaryBasis C c 1 0).reindex (finCongr hp))).ne_zero
  have h₁ := (b₁.isUnit_det ((chosenBoundaryBasis C c 0 1).reindex (finCongr hq))).ne_zero
  field_simp

/-- The torsion `τ(C, c, h)` of a two-periodic complex is nonzero. -/
theorem parityTorsionWithHomology_ne_zero : C.parityTorsionWithHomology c h ≠ 0 :=
  mul_ne_zero (torsionBracketWithHomology_ne_zero c _ _ _ _ _ _ _ _ _)
    (inv_ne_zero (torsionBracketWithHomology_ne_zero c _ _ _ _ _ _ _ _ _))

/-- For an acyclic two-periodic complex, whose homology bases are necessarily empty, the torsion
`τ(C, c, h)` is the torsion `HomologicalComplex.parityTorsion` of the based acyclic complex. -/
theorem parityTorsionWithHomology_eq_parityTorsion (hC : C.Acyclic) :
    C.parityTorsionWithHomology c h = C.parityTorsion c := by
  rw [parityTorsionWithHomology, parityTorsion_eq hC (chosenBoundaryBasis C c 1 0)
      (chosenBoundaryBasis C c 0 1) (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0),
    torsionBracketWithHomology_eq_torsionBracket c _ _ _ _ _ _ _ _ _ (hC 1),
    torsionBracketWithHomology_eq_torsionBracket c _ _ _ _ _ _ _ _ _ (hC 0)]

/-- The torsion `τ(C, c, h)` of a two-periodic complex whose two differentials vanish: every
element is a cycle and the homology is the whole complex, and `τ(C, c, h)` is the quotient
`[z₁ / c₁] · [z₀ / c₀]⁻¹` of the determinants of the cycles `z₀`, `z₁` representing the homology
bases with respect to the chain bases. For instance the complex `F` placed in even degree, with
the basis `1` and the homology basis its class, has torsion `1`, whereas its torsion
`HomologicalComplex.parityTorsion` is `0`. -/
theorem parityTorsionWithHomology_of_d_eq_zero (hd₀ : C.d 0 1 = 0) (hd₁ : C.d 1 0 = 0)
    (z₀ : Fin (m 0) → C.cycles 0) (hz₀ : ∀ l, C.homologyπ 0 (z₀ l) = h 0 l)
    (z₁ : Fin (m 1) → C.cycles 1) (hz₁ : ∀ l, C.homologyπ 1 (z₁ l) = h 1 l)
    (hn₀ : n 0 = m 0) (hn₁ : n 1 = m 1) :
    C.parityTorsionWithHomology c h =
      (c 1).det (fun l ↦ C.iCycles 1 (z₁ (Fin.cast hn₁ l))) *
        ((c 0).det fun l ↦ C.iCycles 0 (z₀ (Fin.cast hn₀ l)))⁻¹ := by
  -- The boundaries vanish, so the boundary bases and the lifts are empty.
  have : Subsingleton (LinearMap.range (C.d 1 0).hom) := by
    rw [hd₁, ModuleCat.hom_zero, LinearMap.range_zero]
    infer_instance
  have : Subsingleton (LinearMap.range (C.d 0 1).hom) := by
    rw [hd₀, ModuleCat.hom_zero, LinearMap.range_zero]
    infer_instance
  rw [parityTorsionWithHomology_eq c h (Basis.empty _) (Basis.empty _) z₀ hz₀ z₁ hz₁ Fin.elim0
      (fun l ↦ l.elim0) Fin.elim0 (fun l ↦ l.elim0),
    torsionBracketWithHomology_eq_det_append c _ _ _ _ _ _ _ _ _ (by simpa using hn₁),
    torsionBracketWithHomology_eq_det_append c _ _ _ _ _ _ _ _ _ (by simpa using hn₀)]
  congr 3 <;> ext l <;> simp [Fin.append_left_nil _ _ rfl]

/-- The basis-change formula for the chain bases: replacing the bases `c i` of `C` by `c' i`
multiplies the torsion `τ(C, c, h)` by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹`, where `[c'ᵢ / cᵢ]` is the
determinant of `c' i` with respect to `c i`. -/
theorem parityTorsionWithHomology_eq_mul_det (c' : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    C.parityTorsionWithHomology c' h =
      C.parityTorsionWithHomology c h * ((c 0).det (c' 0) * ((c 1).det (c' 1))⁻¹) := by
  -- Compute both torsions with the same boundary bases, cycles and lifts.
  rw [parityTorsionWithHomology_eq (c := c') h (chosenBoundaryBasis C c 1 0)
      (chosenBoundaryBasis C c 0 1) (chosenCycle C h 0) (chosenCycle_spec C h 0)
      (chosenCycle C h 1) (chosenCycle_spec C h 1) (chosenBoundaryLift C c 0 1)
      (chosenBoundaryLift_spec C c 0 1) (chosenBoundaryLift C c 1 0)
      (chosenBoundaryLift_spec C c 1 0),
    parityTorsionWithHomology,
    torsionBracketWithHomology_eq_det_mul c _ _ _ _ _ _ _ _ _ c',
    torsionBracketWithHomology_eq_det_mul c _ _ _ _ _ _ _ _ _ c']
  simp only [← (c 0).det_inv (c' 0), ← (c 1).det_inv (c' 1), Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, mul_inv, inv_inv]
  ring

/-- The basis-change formula for the homology bases: replacing the bases `h i` of the homology
`Hᵢ(C)` by `h' i` multiplies the torsion `τ(C, c, h)` by `[h'₁ / h₁] · [h'₀ / h₀]⁻¹`, where
`[h'ᵢ / hᵢ]` is the determinant of `h' i` with respect to `h i`. -/
theorem parityTorsionWithHomology_eq_mul_det_homology
    (h' : ∀ i, Basis (Fin (m i)) F (C.homology i)) :
    C.parityTorsionWithHomology c h' =
      C.parityTorsionWithHomology c h * ((h 1).det (h' 1) * ((h 0).det (h' 0))⁻¹) := by
  -- Compute both torsions with the same boundary bases and lifts.
  rw [parityTorsionWithHomology, parityTorsionWithHomology,
    torsionBracketWithHomology_eq_mul c _ _ (chosenBoundaryBasis C c 0 1) _ _
      (chosenCycle_spec C h 1) _ _ (chosenBoundaryLift_spec C c 1 0) _ (h' 1),
    torsionBracketWithHomology_eq_mul c _ _ (chosenBoundaryBasis C c 1 0) _ _
      (chosenCycle_spec C h 0) _ _ (chosenBoundaryLift_spec C c 0 1) _ (h' 0)]
  simp only [Basis.det_self, one_mul, mul_one, mul_inv]
  ring

end HomologicalComplex
