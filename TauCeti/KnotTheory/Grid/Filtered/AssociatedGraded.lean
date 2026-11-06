/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.KnotTheory.Grid.Filtered.Alexander

/-!
# The associated graded of the Alexander filtration

The Alexander filtration on the filtered grid chain module has successive quotients
`F_a / F_{a-1}`. Each quotient is canonically isomorphic, over the coefficient ring, to the
Alexander-homogeneous piece of degree `a` of the unblocked grid chain module. The isomorphism
sends a class to its degree-`a` part; its inverse sends a homogeneous chain to its class.
It intertwines the differential induced by the filtered grid differential with the unblocked
differential restricted to the homogeneous piece. Thus the identification with the unblocked
complex is an actual linear equivalence, not just a congruence modulo lower filtration.

Each individual quotient is identified over `R`: multiplication by a polynomial variable has
Alexander degree `-1`, so the homogeneous piece is only an `R`-submodule of the chain module,
not a polynomial submodule. No characteristic assumption is needed for the identification or
the intertwining equation; square-zero requires characteristic two.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Chapter 13: the Alexander filtration and its associated
  graded grid complex.
-/

public section

namespace TauCeti.OddComponentGridDiagram

open MvPolynomial

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R]

/-- The degree-`a` associated graded piece `F_a / F_{a-1}` of the Alexander filtration.
The denominator is pulled back to the subtype `F_a`. -/
abbrev alexanderFiltrationGradedPiece (a : ℤ) : Type _ := by
  -- Pin the existing additive group before quotient instance search unfolds grid chains
  -- with a coefficient-ring output metavariable.
  letI : AddCommGroup (GridChainMinus R n) := inferInstance
  exact (G.alexanderFiltration R a) ⧸
    (G.alexanderFiltration R (a - 1)).comap (G.alexanderFiltration R a).subtype

-- The same specialization keeps nested instance search in the private quotient maps small.
private noncomputable local instance : AddCommGroup (GridChainMinus R n) := inferInstance

private theorem topPart_mem (a : ℤ) (c : GridChainMinus R n) :
    (DirectSum.decompose (G.alexanderChainMinusGrading R).piece c a :
      GridChainMinus R n) ∈ G.alexanderChainMinusPiece R a := by
  simpa only [alexanderChainMinusGrading_piece] using
    (DirectSum.decompose (G.alexanderChainMinusGrading R).piece c a).property

private theorem sub_topPart_mem {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderFiltration R a) :
    c - DirectSum.decompose (G.alexanderChainMinusGrading R).piece c a ∈
      G.alexanderFiltration R (a - 1) := by
  rw [mem_alexanderFiltration] at hc ⊢
  intro x e he
  rw [Finsupp.sub_apply, MvPolynomial.mem_support_iff, coeff_sub,
    G.coeff_decompose_alexanderChainMinusGrading] at he
  by_cases h : G.alexanderℤ x - (e.degree : ℤ) = a
  · simp [h] at he
  · have hcoeff : (c x).coeff e ≠ 0 := by simpa [h] using he
    have := hc x e (MvPolynomial.mem_support_iff.mpr hcoeff)
    omega

private theorem mk_topPart (a : ℤ) (c : G.alexanderFiltration R a) :
    (Submodule.Quotient.mk
      (⟨DirectSum.decompose (G.alexanderChainMinusGrading R).piece c a,
        G.alexanderChainMinusPiece_le_alexanderFiltration R a
          (G.topPart_mem R a c)⟩ :
          G.alexanderFiltration R a) : G.alexanderFiltrationGradedPiece R a) =
      Submodule.Quotient.mk c := by
  apply (Submodule.Quotient.eq _).mpr
  simpa only [Submodule.mem_comap, Submodule.coe_sub, Submodule.coe_subtype, neg_sub] using
    (G.alexanderFiltration R (a - 1)).neg_mem (G.sub_topPart_mem R c.property)

private noncomputable def homogeneousToGraded (a : ℤ) :
    G.alexanderChainMinusPiece R a →ₗ[R] G.alexanderFiltrationGradedPiece R a :=
  (((G.alexanderFiltration R (a - 1)).comap
    (G.alexanderFiltration R a).subtype).mkQ.restrictScalars R) ∘ₗ
      Submodule.inclusion (G.alexanderChainMinusPiece_le_alexanderFiltration R a)

private theorem homogeneousToGraded_apply (a : ℤ)
    (c : G.alexanderChainMinusPiece R a) :
    G.homogeneousToGraded R a c = Submodule.Quotient.mk
      (⟨c, G.alexanderChainMinusPiece_le_alexanderFiltration R a c.property⟩ :
        G.alexanderFiltration R a) := by rfl

private theorem homogeneousToGraded_bijective (a : ℤ) :
    Function.Bijective (G.homogeneousToGraded R a) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    rw [G.homogeneousToGraded_apply] at hc
    have hlow : (c : GridChainMinus R n) ∈ G.alexanderFiltration R (a - 1) :=
      (Submodule.Quotient.mk_eq_zero
        ((G.alexanderFiltration R (a - 1)).comap (G.alexanderFiltration R a).subtype)).mp hc
    apply Subtype.ext
    ext x e
    simp only [ZeroMemClass.coe_zero, Finsupp.zero_apply, AddMonoidAlgebra.coeff_zero]
    by_contra hne
    have he := MvPolynomial.mem_support_iff.mpr hne
    have h₁ := G.mem_alexanderChainMinusPiece.mp c.property x e he
    have h₂ := mem_alexanderFiltration.mp hlow x e he
    omega
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | _ c =>
      refine ⟨⟨DirectSum.decompose (G.alexanderChainMinusGrading R).piece c a,
        G.topPart_mem R a c⟩, ?_⟩
      rw [G.homogeneousToGraded_apply]
      exact G.mk_topPart R a c

/-- The degree-`a` quotient of the Alexander filtration is canonically the degree-`a`
Alexander-homogeneous chain module. Its inverse sends a homogeneous chain to its quotient class. -/
noncomputable def alexanderFiltrationGradedEquiv (a : ℤ) :
    G.alexanderFiltrationGradedPiece R a ≃ₗ[R] G.alexanderChainMinusPiece R a :=
  (LinearEquiv.ofBijective (G.homogeneousToGraded R a)
    (G.homogeneousToGraded_bijective R a)).symm

/-- The inverse equivalence sends a homogeneous chain to the class of that same chain in
`F_a / F_{a-1}`. -/
@[simp]
theorem alexanderFiltrationGradedEquiv_symm_apply (a : ℤ)
    (c : G.alexanderChainMinusPiece R a) :
    (G.alexanderFiltrationGradedEquiv R a).symm c =
      Submodule.Quotient.mk
        (⟨c, G.alexanderChainMinusPiece_le_alexanderFiltration R a c.property⟩ :
          G.alexanderFiltration R a) := by rfl

/-- The class of a homogeneous chain is identified with that chain. -/
@[simp]
theorem alexanderFiltrationGradedEquiv_apply_mk (a : ℤ)
    (c : G.alexanderChainMinusPiece R a) :
    G.alexanderFiltrationGradedEquiv R a
      (Submodule.Quotient.mk
        (⟨c, G.alexanderChainMinusPiece_le_alexanderFiltration R a c.property⟩ :
          G.alexanderFiltration R a)) = c :=
  (G.alexanderFiltrationGradedEquiv R a).apply_symm_apply c

/-- On any representative, the canonical identification is the degree-`a` component of
the Alexander grading. This structural rewrite is not a simp lemma: coefficient simplification
uses `coeff_alexanderFiltrationGradedEquiv_mk` instead. -/
theorem coe_alexanderFiltrationGradedEquiv_mk (a : ℤ) (c : G.alexanderFiltration R a) :
    (G.alexanderFiltrationGradedEquiv R a (Submodule.Quotient.mk c) :
      GridChainMinus R n) =
        DirectSum.decompose (G.alexanderChainMinusGrading R).piece c a := by
  have h : G.alexanderFiltrationGradedEquiv R a (Submodule.Quotient.mk c) =
      ⟨DirectSum.decompose (G.alexanderChainMinusGrading R).piece c a,
        G.topPart_mem R a c⟩ := by
    apply (G.alexanderFiltrationGradedEquiv R a).symm.injective
    rw [LinearEquiv.symm_apply_apply, G.alexanderFiltrationGradedEquiv_symm_apply]
    exact (G.mk_topPart R a c).symm
  rw [h]

/-- The canonical identification retains exactly the monomials of Alexander degree `a`
in any representative of a quotient class. -/
@[simp]
theorem coeff_alexanderFiltrationGradedEquiv_mk (a : ℤ) (c : G.alexanderFiltration R a)
    (x : GridState n) (e : Fin n →₀ ℕ) :
    ((G.alexanderFiltrationGradedEquiv R a (Submodule.Quotient.mk c) :
      GridChainMinus R n) x).coeff e =
        if G.alexanderℤ x - (e.degree : ℤ) = a then (c.val x).coeff e else 0 := by
  rw [G.coe_alexanderFiltrationGradedEquiv_mk]
  exact G.coeff_decompose_alexanderChainMinusGrading R a c x e

/-- The filtered grid differential induced on `F_a / F_{a-1}`. -/
noncomputable def alexanderFiltrationGradedDifferential (a : ℤ) :
    G.alexanderFiltrationGradedPiece R a →ₗ[MvPolynomial (Fin n) R]
      G.alexanderFiltrationGradedPiece R a :=
  let d := (G.1.filteredDifferential R).restrict
    (fun _ hc => G.filteredDifferential_mem_alexanderFiltration R hc)
  Submodule.mapQ _ _ d (fun _ hc => G.filteredDifferential_mem_alexanderFiltration R hc)

/-- On quotient representatives the induced differential is the class of the filtered
rectangle-counting differential. -/
@[simp]
theorem alexanderFiltrationGradedDifferential_mk (a : ℤ) (c : G.alexanderFiltration R a) :
    G.alexanderFiltrationGradedDifferential R a (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (⟨G.1.filteredDifferential R c,
          G.filteredDifferential_mem_alexanderFiltration R c.property⟩ :
            G.alexanderFiltration R a) := by rfl

/-- Under the canonical quotient identification, the associated graded differential is the
unblocked differential restricted to the Alexander-homogeneous piece. -/
@[simp]
theorem alexanderFiltrationGradedEquiv_differential (a : ℤ)
    (q : G.alexanderFiltrationGradedPiece R a) :
    G.alexanderFiltrationGradedEquiv R a (G.alexanderFiltrationGradedDifferential R a q) =
      ⟨G.1.unblockedDifferential R (G.alexanderFiltrationGradedEquiv R a q),
        G.unblockedDifferential_mem_alexanderChainMinusPiece
          (G.alexanderFiltrationGradedEquiv R a q).property⟩ := by
  obtain ⟨c, rfl⟩ := (G.alexanderFiltrationGradedEquiv R a).symm.surjective q
  apply (G.alexanderFiltrationGradedEquiv R a).symm.injective
  simp only [LinearEquiv.symm_apply_apply, alexanderFiltrationGradedEquiv_symm_apply,
    alexanderFiltrationGradedDifferential_mk, alexanderFiltrationGradedEquiv_apply_mk]
  apply (Submodule.Quotient.eq _).mpr
  exact G.filteredDifferential_sub_unblockedDifferential_mem_alexanderFiltration R
    (G.alexanderChainMinusPiece_le_alexanderFiltration R a c.property)

/-- The associated graded differential squares to zero in characteristic two. -/
theorem alexanderFiltrationGradedDifferential_comp_self_eq_zero [CharP R 2] (a : ℤ) :
    G.alexanderFiltrationGradedDifferential R a ∘ₗ
      G.alexanderFiltrationGradedDifferential R a = 0 := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ c =>
    rw [LinearMap.comp_apply, alexanderFiltrationGradedDifferential_mk,
      alexanderFiltrationGradedDifferential_mk]
    have hd := LinearMap.congr_fun (G.1.filteredDifferential_comp_self_eq_zero R) c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hd
    simp [hd]

end TauCeti.OddComponentGridDiagram
