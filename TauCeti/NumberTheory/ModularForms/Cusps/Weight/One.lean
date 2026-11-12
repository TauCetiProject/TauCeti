/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Codimension
public import TauCeti.NumberTheory.ModularForms.Cusps.Residue
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The weight-one cusp codimension bound

Let `H` be a finite-index subgroup of `SL(2, ℤ)`. In every weight `k` the cusp forms in `M_k(H)`
have codimension at most the number of cusps
(`TauCeti.ModularForm.finrank_le_card_cuspOrbit_of_disjoint`), and in weight two at most the number
of cusps minus one. In weight one the codimension is at most **half** the number of cusps:

`2 dim (M₁(H) / S₁(H)) ≤ ε∞`.

More precisely, it is at most half the size of any family of cusp representatives meeting every
cusp at which some weight-one form has a nonzero constant term. Not every cusp is of this kind: in
odd weight the constant term vanishes at every irregular cusp
(`ModularForm.constantTermAt_eq_zero_of_odd`), and at every cusp when `-1 ∈ H`. Applying the
bound to representatives of the regular cusps therefore gives `2 dim (M₁(H) / S₁(H)) ≤ ε∞^reg`,
where `ε∞^reg` is the number of regular cusps. This count can exceed the number of cusps carrying
a nonzero constant term in weight one, for instance when `-1 ∈ H`.

The constant terms of weight-one forms satisfy a quadratic relation. For `f, g ∈ M₁(H)` the
product `f g` has weight two, and the weight-two residue relation for `f g`
(`weight_two_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_eq_zero`)
says that the width-weighted sum, over all cusp translation orbits, of the products of the
constant terms of `f` and `g` vanishes. The constant term of a weight-one form at a cusp is
determined by the cusp up to a sign, which the product of two constant terms at the same
representative does not see. So, reading the constant terms at one representative of each cusp,
the image of `M₁(H)` is a totally isotropic subspace for a diagonal bilinear form with positive
weights, and its dimension is at most half the number of representatives.

Consequently, if `r : ι → SL(2, ℤ)` is a family of representatives as above, a family of
`Nat.card ι / 2` weight-one forms that is linearly independent modulo the cusp forms spans a
complement of `S₁(H)` in `M₁(H)`. This is the upper bound needed to show that weight-one
Eisenstein series span such a complement.

## Main results

* `weight_one_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_mul_eq_zero`:
  the quadratic relation between the constant terms of two weight-one forms.
* `TauCeti.ModularForm.two_mul_finrank_le_natCard_of_disjoint`: a subspace of `M₁(H)` disjoint
  from the cusp forms has dimension at most half the size of any family of cusp representatives
  meeting every cusp that carries a constant term in weight one.
* `TauCeti.ModularForm.two_mul_finrank_le_card_cuspOrbit_of_disjoint` and
  `TauCeti.ModularForm.two_mul_finrank_quotient_cuspFormSubmodule_le_card_cuspOrbit`: the same
  bound by the number of cusps of `H`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §3.6 for
  the dimensions of the spaces of weight-one forms, obtained there from the Riemann–Roch
  theorem, and §4.8 for the weight-one Eisenstein series.
-/

public noncomputable section

open Matrix.SpecialLinearGroup ModularForm
open scoped MatrixGroups

namespace ModularForm

open TauCeti.ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne]

/-- **The weight-one quadratic relation between constant terms.** For two weight-one forms `f`
and `g`, the width-weighted sum over all cusp translation orbits of the products of their
constant terms vanishes: it is the weight-two residue relation for `f g`. -/
theorem weight_one_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_mul_eq_zero
    (f g : ModularForm 𝒢 1) :
    ∑ c : CuspTranslationOrbit 𝒢, (cuspTranslationOrbitWidth c : ℂ) *
      (constantTermAtCuspTranslationOrbit f c * constantTermAtCuspTranslationOrbit g c) = 0 := by
  -- `f.mul g` has weight `1 + 1`, which is `2` only up to a computation.
  have key : ∀ {k : ℤ}, k = 2 → ∀ F : ModularForm 𝒢 k,
      ∑ c : CuspTranslationOrbit 𝒢,
        (cuspTranslationOrbitWidth c : ℂ) * constantTermAtCuspTranslationOrbit F c = 0 := by
    rintro k rfl F
    exact weight_two_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_eq_zero F
  simpa only [constantTermAtCuspTranslationOrbit_mul] using key (by norm_num) (f.mul g)

end ModularForm

namespace TauCeti.ModularForm

variable {H : Subgroup SL(2, ℤ)} [H.FiniteIndex]

/-- **The quadratic relation at representatives of distinct cusps.** If the `r i` represent
distinct cusps and meet every cusp carrying a constant term in weight one, then there are positive
integer weights `w i` with `∑ i, w i aᵢ(f) aᵢ(g) = 0` for all weight-one forms `f` and `g`, where
`aᵢ` is the constant term at `r i`. The weight `w i` is the total width of the cusp translation
orbits lying over the cusp of `r i`. -/
private lemma exists_sum_mul_constantTermAt_mul_eq_zero {ι : Type*} [Fintype ι]
    (r : ι → SL(2, ℤ))
    (hr : ∀ γ : SL(2, ℤ), (∃ i, H.cuspOrbitOfSL2Z (r i) = H.cuspOrbitOfSL2Z γ) ∨
      ∀ f, constantTermAt (Γ := H.map (mapGL ℝ)) (k := 1) γ f = 0)
    (hinj : ∀ i j, H.cuspOrbitOfSL2Z (r i) = H.cuspOrbitOfSL2Z (r j) → i = j) :
    ∃ w : ι → ℕ, (∀ i, 0 < w i) ∧ ∀ f g : ModularForm (H.map (mapGL ℝ)) 1,
      ∑ i, (w i : ℂ) * (constantTermAt (r i) f * constantTermAt (r i) g) = 0 := by
  classical
  -- The cusp translation orbits lying over the cusp of `r i`.
  let P (c : CuspTranslationOrbit (H.map (mapGL ℝ))) (i : ι) : Prop :=
    ∃ γ : SL(2, ℤ), c = ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ)⟧ ∧
      H.cuspOrbitOfSL2Z γ⁻¹ = H.cuspOrbitOfSL2Z (r i)
  have hP (γ : SL(2, ℤ)) (i : ι) :
      P ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ)⟧ i ↔
        H.cuspOrbitOfSL2Z γ⁻¹ = H.cuspOrbitOfSL2Z (r i) :=
    ⟨fun ⟨_, hc, hγ⟩ ↦ (cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq hc).trans hγ,
      fun hγ ↦ ⟨γ, rfl, hγ⟩⟩
  refine ⟨fun i ↦ ∑ c ∈ Finset.univ.filter (P · i), cuspTranslationOrbitWidth c,
    fun i ↦ Finset.sum_pos (fun c _ ↦ cuspTranslationOrbitWidth_pos c)
      ⟨⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict (r i)⁻¹)⟧,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hP _ i).mpr (by rw [inv_inv])⟩⟩,
    fun f g ↦ ?_⟩
  -- Each cusp translation orbit contributes the product of the constant terms at the
  -- representative of its cusp, the sign ambiguity cancelling in the product.
  have horbit (c : CuspTranslationOrbit (H.map (mapGL ℝ))) :
      constantTermAtCuspTranslationOrbit f c * constantTermAtCuspTranslationOrbit g c =
        ∑ i, if P c i then constantTermAt (r i) f * constantTermAt (r i) g else 0 := by
    induction c using CuspTranslationOrbit.induction_on with
    | h γ =>
      simp only [constantTermAtCuspTranslationOrbit_mk_mapGL, hP]
      obtain ⟨i, hi⟩ | h0 := hr γ⁻¹
      · have hiff (j : ι) : H.cuspOrbitOfSL2Z γ⁻¹ = H.cuspOrbitOfSL2Z (r j) ↔ i = j :=
          ⟨fun hj ↦ hinj i j (hi.trans hj), fun hj ↦ hj ▸ hi.symm⟩
        simp only [hiff, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        exact constantTermAt_mul_constantTermAt_eq_of_cuspOrbitOfSL2Z_eq (by norm_num) hi f g
      · rw [h0 f, zero_mul]
        refine (Finset.sum_eq_zero fun j _ ↦ ?_).symm
        split_ifs with hj
        · obtain ⟨u, hu⟩ :=
            exists_constantTermAt_eq_zpow_smul_of_cuspOrbitOfSL2Z_eq (k := 1) hj
          rw [hu, LinearMap.smul_apply, h0 f, smul_zero, zero_mul]
        · rfl
  -- Grouping the orbits by cusp turns the weight-one relation into the claim.
  have hrel :=
    weight_one_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_mul_eq_zero f g
  rw [← hrel]
  simp only [horbit, Finset.mul_sum, mul_ite, mul_zero, Nat.cast_sum, Finset.sum_mul,
    Finset.sum_filter, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  exact Finset.sum_comm

variable (H) in
/-- The bound of `two_mul_finrank_le_natCard_of_disjoint` for a family representing distinct
cusps: the constant terms at the family span a totally isotropic subspace of a nondegenerate
quadratic space. -/
private theorem two_mul_finrank_le_natCard_of_disjoint_of_injective {ι : Type*} [Finite ι]
    (r : ι → SL(2, ℤ))
    (hr : ∀ γ : SL(2, ℤ), (∃ i, H.cuspOrbitOfSL2Z (r i) = H.cuspOrbitOfSL2Z γ) ∨
      ∀ f, constantTermAt (Γ := H.map (mapGL ℝ)) (k := 1) γ f = 0)
    (hinj : ∀ i j, H.cuspOrbitOfSL2Z (r i) = H.cuspOrbitOfSL2Z (r j) → i = j)
    {V : Submodule ℂ (ModularForm (H.map (mapGL ℝ)) 1)}
    (hV : Disjoint V (cuspFormSubmodule (H.map (mapGL ℝ)) 1)) :
    2 * Module.finrank ℂ V ≤ Nat.card ι := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨w, hw, hiso⟩ := exists_sum_mul_constantTermAt_mul_eq_zero r hr hinj
  let L := (LinearMap.funLeft ℂ ℂ r).comp
    (constantTerms (Γ := H.map (mapGL ℝ)) (k := 1))
  let B := (Matrix.diagonal fun i ↦ (w i : ℂ)).toBilin'
  have hB : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ <| by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.cast_ne_zero.mpr (hw i).ne'
  have hle : LinearMap.range L ≤ B.orthogonal (LinearMap.range L) := by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro _ ⟨g, rfl⟩
    rw [Matrix.toBilin'_apply', ← hiso g f]
    simp only [Matrix.mulVec_diagonal, dotProduct, L, LinearMap.comp_apply,
      LinearMap.funLeft_apply, constantTerms_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h2 := LinearMap.BilinForm.two_mul_finrank_le_finrank_of_le_orthogonal hB hle
  have h1 : Module.finrank ℂ V ≤ Module.finrank ℂ (LinearMap.range L) :=
    finrank_le_finrank_range_constantTerms_of_disjoint H 1 r hr hV
  rw [Module.finrank_fintype_fun_eq_card] at h2
  rw [Nat.card_eq_fintype_card]
  omega

variable (H) in
/-- **The weight-one cusp codimension bound.** Let `r i` be finitely many cusp representatives
such that every cusp either is equivalent to some `r i` or carries no constant term in weight one
(an irregular cusp, `ModularForm.constantTermAt_eq_zero_of_odd`). Then a subspace of `M₁(H)` whose
intersection with the cusp forms is zero has dimension at most half the number of
representatives. -/
theorem two_mul_finrank_le_natCard_of_disjoint {ι : Type*} [Finite ι] (r : ι → SL(2, ℤ))
    (hr : ∀ γ : SL(2, ℤ), (∃ i, H.cuspOrbitOfSL2Z (r i) = H.cuspOrbitOfSL2Z γ) ∨
      ∀ f, constantTermAt (Γ := H.map (mapGL ℝ)) (k := 1) γ f = 0)
    {V : Submodule ℂ (ModularForm (H.map (mapGL ℝ)) 1)}
    (hV : Disjoint V (cuspFormSubmodule (H.map (mapGL ℝ)) 1)) :
    2 * Module.finrank ℂ V ≤ Nat.card ι := by
  -- Keep one representative of each cusp met by the family.
  let S := Set.range fun i ↦ H.cuspOrbitOfSL2Z (r i)
  have hspec (s : S) : H.cuspOrbitOfSL2Z (r s.2.choose) = s := s.2.choose_spec
  refine (two_mul_finrank_le_natCard_of_disjoint_of_injective H (fun s : S ↦ r s.2.choose)
    (fun γ ↦ ?_) (fun s t hst ↦ Subtype.ext ?_) hV).trans (Finite.card_range_le _)
  · obtain ⟨i, hi⟩ | h0 := hr γ
    · exact .inl ⟨⟨_, i, rfl⟩, (hspec _).trans hi⟩
    · exact .inr h0
  · rwa [hspec, hspec] at hst

variable (H) in
/-- A subspace of weight-one modular forms disjoint from the cusp forms has dimension at most
half the number of cusps of `H`. -/
theorem two_mul_finrank_le_card_cuspOrbit_of_disjoint
    {V : Submodule ℂ (ModularForm (H.map (mapGL ℝ)) 1)}
    (hV : Disjoint V (cuspFormSubmodule (H.map (mapGL ℝ)) 1)) :
    2 * Module.finrank ℂ V ≤ Nat.card (H.map sl2zToPSL2R).CuspOrbit :=
  two_mul_finrank_le_natCard_of_disjoint H (Function.surjInv H.cuspOrbitOfSL2Z_surjective)
    (fun _ ↦ .inl ⟨_, Function.surjInv_eq H.cuspOrbitOfSL2Z_surjective _⟩) hV

variable (H) in
/-- The quotient of the weight-one modular forms by the cusp forms has dimension at most half
the number of cusps of `H`. -/
theorem two_mul_finrank_quotient_cuspFormSubmodule_le_card_cuspOrbit :
    2 * Module.finrank ℂ
        (ModularForm (H.map (mapGL ℝ)) 1 ⧸ cuspFormSubmodule (H.map (mapGL ℝ)) 1) ≤
      Nat.card (H.map sl2zToPSL2R).CuspOrbit := by
  obtain ⟨V, hV⟩ := (cuspFormSubmodule (H.map (mapGL ℝ)) 1).exists_isCompl
  rw [(Submodule.quotientEquivOfIsCompl _ V hV).finrank_eq]
  exact two_mul_finrank_le_card_cuspOrbit_of_disjoint H hV.symm.disjoint

end TauCeti.ModularForm
