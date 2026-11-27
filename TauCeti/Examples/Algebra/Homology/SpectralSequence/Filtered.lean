/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.PairDifferential
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Checks on the spectral sequence of a filtered complex

The homological spectral sequence `CochainComplex.homologicalFiltrationSpectralSequence F hF` of
an increasing filtration `F` of a chain complex, regarded as a cochain complex `K` with
`K^{-n} = C_n`, has `E¹_{p,q} = H_{p+q}(F_p/F_{p-1})`, and its first differential is a connecting
map. This file computes it on three filtrations, which test its indexing and the hypotheses of its
convergence theorems.

* **The two-step filtration** `0 ⊆ A ⊆ K` of a subcomplex `A`
  (`TauCeti.Examples.FilteredComplex.twoStepFiltration`), with `F_p = 0` for `p < 0`, `F_0 = A`
  and `F_p = K` for `p > 0`. Its first page is concentrated in the columns `p = 0` and `p = 1`,
  with `E¹_{0,q} = H_q(A)` and `E¹_{1,q} = H_{q+1}(K/A)`
  (`TauCeti.Examples.FilteredComplex.twoStepFirstPageXZeroIso`,
  `TauCeti.Examples.FilteredComplex.twoStepFirstPageXOneIso`), and its first differential
  `E¹_{1,q} ⟶ E¹_{0,q}` is the connecting map `H_{q+1}(K/A) ⟶ H_q(A)` of the long exact sequence of
  the pair (`TauCeti.Examples.FilteredComplex.twoStepSpectralSequence_first_page_d`). An error
  in the bidegree `(1 - 2p - q, p - 1)` of the reindexing would put that map in the wrong
  bidegree. Every later differential vanishes, since it would join two columns at distance at
  least two (`TauCeti.Examples.FilteredComplex.twoStepSpectralSequence_page_d_eq_zero`), so
  `E² = E^∞`; and
  from the second page on, the objects are the graded pieces of the filtration
  `0 ⊆ im(H_n(A) ⟶ H_n(K)) ⊆ H_n(K)` of the abutment
  (`TauCeti.Examples.FilteredComplex.twoStepSpectralSequencePageXIsoGraded`).
* **The trivial filtration** `F_p = 0` for `p < 0` and `F_p = K` for `p ≥ 0`, the two-step
  filtration of `A = K`. Its first page is concentrated in the column `p = 0`, where it is the
  homology of `K` (`TauCeti.Examples.FilteredComplex.trivialFirstPageXZeroIso`,
  `TauCeti.Examples.FilteredComplex.isZero_trivialSpectralSequence_page_X`).
* **The constant filtration** `F_p = K` for every `p`. It is exhaustive but not bounded below, and
  every page of its spectral sequence vanishes
  (`TauCeti.Examples.FilteredComplex.isZero_constantSpectralSequence_page_X`), whatever the homology
  of `K`. For the complex `ℤ` concentrated in degree `0`, whose homology is not zero, a convergence
  theorem that dropped the lower bound would therefore be false
  (`TauCeti.Examples.FilteredComplex.exists_isZero_constantSpectralSequence_page_X_and_not_isZero`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994, §5.4
  and Theorem 5.5.1.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2.
-/

public section

noncomputable section

namespace TauCeti.Examples.FilteredComplex

open CategoryTheory Limits CochainComplex HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ}

/-! ### The two-step filtration -/

section TwoStep

variable (A : Subobject K)

/-- The **two-step filtration** `0 ⊆ A ⊆ K` of a subcomplex `A`: `F_p = 0` for `p < 0`, `F_0 = A`
and `F_p = K` for `p > 0`. -/
def twoStepFiltration (p : ℤ) : Subobject K :=
  if p < 0 then ⊥ else if p = 0 then A else ⊤

@[simp]
lemma twoStepFiltration_of_neg {p : ℤ} (hp : p < 0) : twoStepFiltration A p = ⊥ := by
  simp [twoStepFiltration, hp]

@[simp]
lemma twoStepFiltration_zero : twoStepFiltration A 0 = A := by
  simp [twoStepFiltration]

@[simp]
lemma twoStepFiltration_of_pos {p : ℤ} (hp : 0 < p) : twoStepFiltration A p = ⊤ := by
  simp [twoStepFiltration, hp.not_gt, hp.ne']

lemma monotone_twoStepFiltration : Monotone (twoStepFiltration A) := by
  intro p p' h
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · simp [hp]
  · rcases h.lt_or_eq with h | rfl
    · simp [h]
    · exact le_rfl
  · simp [hp, lt_of_lt_of_le hp h]

/-- The homological spectral sequence of the two-step filtration `0 ⊆ A ⊆ K`. -/
-- The monotonicity proof is eta-expanded, so that the stages of the first page, which apply it to
-- inequalities of indices, can be rewritten without unfolding `Monotone`.
abbrev twoStepSpectralSequence :=
  homologicalFiltrationSpectralSequence (twoStepFiltration A)
    (fun _ _ h ↦ monotone_twoStepFiltration A h)

/-- The first page of the spectral sequence of the two-step filtration vanishes outside the
columns `p = 0` and `p = 1`, where `F_{p-1} = F_p`. -/
lemma isZero_twoStepSpectralSequence_page_one_X {p : ℤ} (hp : p ≠ 0 ∧ p ≠ 1) (q : ℤ) :
    IsZero (((twoStepSpectralSequence A).page 1).X (p, q)) := by
  refine (Subobject.isZero_homology_cokernel_ofLE_of_eq ?_ _).of_iso
    (homologicalFiltrationSpectralSequenceFirstPageXIso _ _ p q)
  rcases lt_or_gt_of_ne hp.1 with h | h
  · rw [twoStepFiltration_of_neg A h, twoStepFiltration_of_neg A (by lia)]
  · rw [twoStepFiltration_of_pos A h, twoStepFiltration_of_pos A (by lia)]

/-- Every page of the spectral sequence of the two-step filtration vanishes outside the columns
`p = 0` and `p = 1`. -/
lemma isZero_twoStepSpectralSequence_page_X {p : ℤ} (hp : p ≠ 0 ∧ p ≠ 1) (q r : ℤ)
    (hr : 1 ≤ r) : IsZero (((twoStepSpectralSequence A).page r).X (p, q)) :=
  (twoStepSpectralSequence A).isZero_page_X_of_le le_rfl
    (isZero_twoStepSpectralSequence_page_one_X A hp q) r hr

/-- The cokernel projection of `F_{-1} ≤ F_0` is an isomorphism, since `F_{-1} = 0`. The stages are
written as `F (1 - 1 - 1)` and `F (1 - 1)`, the form in which the first differential out of the
column `1` reaches the column `0`. -/
private instance isIso_cokernel_π_twoStepFiltration_ofLE :
    IsIso (cokernel.π (Subobject.ofLE (twoStepFiltration A (1 - 1 - 1))
      (twoStepFiltration A (1 - 1)) (monotone_twoStepFiltration A (by lia)))) :=
  cokernel.π_of_zero (IsZero.eq_of_src (((isZero_zero _).of_iso Subobject.botCoeIsoZero).of_iso
    (Subobject.isoOfEq _ _ (twoStepFiltration_of_neg A (by lia)))) _ _)

/-- The inclusion `F_1 ⊆ K` is an isomorphism, since `F_1 = K`. -/
instance isIso_twoStepFiltration_one_arrow : IsIso (twoStepFiltration A 1).arrow := by
  rw [twoStepFiltration_of_pos A one_pos]
  infer_instance

/-- **The column `p = 0` of the first page of the two-step filtration** is the homology of `A`:
`E¹_{0,q} = H_q(A)`, the cohomology of `A` in degree `-q`. -/
def twoStepFirstPageXZeroIso (q : ℤ) :
    ((twoStepSpectralSequence A).page 1).X (0, q) ≅ (A : CochainComplex C ℤ).homology (-q) :=
  eqToIso (congrArg (fun x : ℤ ↦ ((twoStepSpectralSequence A).page 1).X (x, q)) (by lia)) ≪≫
    homologicalFiltrationSpectralSequenceFirstPageXIso (twoStepFiltration A)
      (fun _ _ h ↦ monotone_twoStepFiltration A h) (1 - 1) q ≪≫
    HomologicalComplex.homologyMapIso (asIso (cokernel.π _)).symm _ ≪≫
    eqToIso (by rw [sub_self, twoStepFiltration_zero, zero_add])

/-- The isomorphism between the cokernel of `F_0 ≤ F_1` and the quotient `K / F_0`, induced by the
inclusion `F_1 ⊆ K`. -/
private def twoStepCokernelIso :
    cokernel (Subobject.ofLE (twoStepFiltration A (1 - 1)) (twoStepFiltration A 1)
      (monotone_twoStepFiltration A (by lia))) ≅ cokernel (twoStepFiltration A (1 - 1)).arrow :=
  cokernel.mapIso _ _ (Iso.refl _) (asIso (twoStepFiltration A 1).arrow) (by simp)

/-- **The column `p = 1` of the first page of the two-step filtration** is the homology of the
quotient: `E¹_{1,q} = H_{q+1}(K/A)`, the cohomology of `K/A` in degree `-(q + 1)`. -/
def twoStepFirstPageXOneIso (q : ℤ) :
    ((twoStepSpectralSequence A).page 1).X (1, q) ≅ (cokernel A.arrow).homology (-(q + 1)) :=
  homologicalFiltrationSpectralSequenceFirstPageXIso (twoStepFiltration A)
      (fun _ _ h ↦ monotone_twoStepFiltration A h) 1 q ≪≫
    HomologicalComplex.homologyMapIso (twoStepCokernelIso A) _ ≪≫
    eqToIso (by rw [sub_self, twoStepFiltration_zero, add_comm])

/-- The connecting map of the pair `Y ⊆ K`, read through an equality of subobjects and equalities
of its indices. -/
private lemma δ_cokernelSequence_eq {Y Y' : Subobject K} (hY : Y = Y') {i j i' j' : ℤ}
    (hi : i = i') (hj : j = j') (hij : (ComplexShape.up ℤ).Rel i j)
    (hij' : (ComplexShape.up ℤ).Rel i' j') :
    (pairSequence_shortExact Y).δ i j hij =
      eqToHom (by rw [hY, hi]) ≫ (pairSequence_shortExact Y').δ i' j' hij' ≫
        eqToHom (by rw [hY, hj]) := by
  subst hY hi hj
  simp

/-- **The first differential of the two-step filtration is the connecting map of the pair.**
Under the identifications `E¹_{1,q} = H_{q+1}(K/A)` and `E¹_{0,q} = H_q(A)`, the differential
`d¹ : E¹_{1,q} ⟶ E¹_{0,q}` is the connecting map `H_{q+1}(K/A) ⟶ H_q(A)` of the short exact sequence
`A ⟶ K ⟶ K/A`, in cohomological degrees `-(q + 1) ⟶ -q`. -/
theorem twoStepSpectralSequence_first_page_d (q : ℤ) :
    ((twoStepSpectralSequence A).page 1).d (1, q) (0, q) =
      (twoStepFirstPageXOneIso A q).hom ≫
        (pairSequence_shortExact A).δ (-(q + 1)) (-q)
          (by simp only [ComplexShape.up_Rel]; lia) ≫
        (twoStepFirstPageXZeroIso A q).inv := by
  -- The target `(0, q)` is the position `(1 - 1, q)` of the first differential out of `(1, q)`.
  have hrel (x : ℤ) (hx : x = 0) :
      (ComplexShape.up' ((-1, 1 - 1) : ℤ × ℤ)).Rel (1, q) (x, q) := by
    simp only [ComplexShape.up'_Rel, Prod.mk_add_mk, Prod.mk.injEq]
    lia
  refine (HomologicalComplex.d_comp_eqToHom _ (hrel 0 rfl) (hrel (1 - 1) (by lia))).symm.trans ?_
  refine (congrArg (· ≫ _) (homologicalFiltrationSpectralSequence_first_page_d_eq_δ
    (twoStepFiltration A) (fun _ _ h ↦ monotone_twoStepFiltration A h) 1 q)).trans ?_
  rw [δ_cokernelSequence_eq (twoStepFiltration_zero A ▸ congrArg (twoStepFiltration A) (sub_self 1))
      (show -(1 + q) = -(q + 1) by lia) (show -(1 - 1 + q) = -q by lia) _
      (by simp only [ComplexShape.up_Rel]; lia)]
  simp [twoStepFirstPageXOneIso, twoStepFirstPageXZeroIso, twoStepCokernelIso]

/-- **The spectral sequence of the two-step filtration degenerates at `E²`.** Every differential
from the second page on vanishes: it joins the columns `p` and `p - r` with `r ≥ 2`, and the first
page, hence every later page, vanishes outside the columns `p = 0` and `p = 1`. -/
theorem twoStepSpectralSequence_page_d_eq_zero (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) :
    ((twoStepSpectralSequence A).page r).d pq pq' = 0 := by
  by_cases hrel : (ComplexShape.up' ((-r, r - 1) : ℤ × ℤ)).Rel pq pq'
  · have h₁ : pq'.1 = pq.1 - r := by
      rw [← hrel]
      simp only [Prod.fst_add]
      lia
    refine (twoStepSpectralSequence A).page_d_eq_zero_of_le le_rfl ?_ r (by lia)
    by_cases hp : pq.1 = 0 ∨ pq.1 = 1
    · exact Or.inr (isZero_twoStepSpectralSequence_page_one_X A (by lia) pq'.2)
    · exact Or.inl (isZero_twoStepSpectralSequence_page_one_X A (by lia) pq.2)
  · exact HomologicalComplex.shape _ _ _ hrel

/-- **From the second page on, the spectral sequence of the two-step filtration is the graded
abutment.** For `r ≥ 2` and `p = 0` or `p = 1`, the object at `(p, q)` on page `r` is the graded
piece `F_p H_{p+q} / F_{p-1} H_{p+q}` of the filtration of `H_{p+q}(K)` by the images of
`H_{p+q}(F_p)`: the image of `H_q(A)` for `p = 0`, and the quotient of `H_{q+1}(K)` by the image of
`H_{q+1}(A)` for `p = 1`. -/
def twoStepSpectralSequencePageXIsoGraded (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) :
    ((twoStepSpectralSequence A).page r).X (p, q) ≅
      cokernel ((spectralObject (filtrationFunctor (twoStepFiltration A)
        (fun _ _ h ↦ monotone_twoStepFiltration A h))).abutmentFiltrationMap (p - 1)
          (-(p + q))) :=
  homologicalFiltrationSpectralSequencePageXIsoGradedOfFinite _ _
    (twoStepFiltration_of_neg A (show (-1 : ℤ) < 0 by lia)) (twoStepFiltration_of_pos A one_pos)
    r (by lia) p q (by lia) (by lia)

end TwoStep

/-! ### The trivial filtration -/

section Trivial

variable (K)

/-- The spectral sequence of the **trivial filtration** `F_p = 0` for `p < 0` and `F_p = K` for
`p ≥ 0`, the two-step filtration of the subcomplex `K` itself. -/
abbrev trivialSpectralSequence := twoStepSpectralSequence (⊤ : Subobject K)

/-- **The first page of the trivial filtration** is the homology of `K` in the column `p = 0`:
`E¹_{0,q} = H_q(K)`, the cohomology of `K` in degree `-q`. -/
def trivialFirstPageXZeroIso (q : ℤ) :
    ((trivialSpectralSequence K).page 1).X (0, q) ≅ K.homology (-q) :=
  twoStepFirstPageXZeroIso ⊤ q ≪≫
    HomologicalComplex.homologyMapIso (asIso (⊤ : Subobject K).arrow) _

/-- **Every page of the trivial filtration vanishes outside the column `p = 0`.** In the column
`p = 1` the first page is the homology of `K / K = 0`. -/
lemma isZero_trivialSpectralSequence_page_X {p : ℤ} (hp : p ≠ 0) (q r : ℤ) (hr : 1 ≤ r) :
    IsZero (((trivialSpectralSequence K).page r).X (p, q)) := by
  refine (trivialSpectralSequence K).isZero_page_X_of_le le_rfl ?_ r hr
  by_cases hp₁ : p = 1
  · subst hp₁
    exact (Subobject.isZero_homology_cokernel_of_eq_top ⊤ rfl _).of_iso
      (twoStepFirstPageXOneIso ⊤ q)
  · exact isZero_twoStepSpectralSequence_page_one_X ⊤ ⟨hp, hp₁⟩ q

end Trivial

/-! ### The constant filtration -/

section Constant

variable (K)

/-- The spectral sequence of the **constant filtration** `F_p = K` for every `p`. It is exhaustive,
but no stage vanishes. -/
abbrev constantSpectralSequence :=
  homologicalFiltrationSpectralSequence (fun _ ↦ (⊤ : Subobject K)) (fun _ _ _ ↦ le_rfl)

/-- **Every page of the spectral sequence of the constant filtration vanishes**, whatever the
homology of `K`: the graded pieces `F_p / F_{p-1} = K / K` are zero. -/
lemma isZero_constantSpectralSequence_page_X (pq : ℤ × ℤ) (r : ℤ) (hr : 1 ≤ r) :
    IsZero (((constantSpectralSequence K).page r).X pq) :=
  (constantSpectralSequence K).isZero_page_X_of_le le_rfl
    ((Subobject.isZero_homology_cokernel_ofLE_of_eq rfl _).of_iso
      (homologicalFiltrationSpectralSequenceFirstPageXIso _ _ pq.1 pq.2)) r hr

/-- **A filtration that is not bounded below need not converge to the homology.** For the complex
`ℤ` concentrated in degree `0`, every page of the spectral sequence of the constant filtration
vanishes, while the homology in degree `0` does not. So the lower bound in the convergence
theorems for exhaustive filtrations cannot be dropped. -/
theorem exists_isZero_constantSpectralSequence_page_X_and_not_isZero :
    ∃ K : CochainComplex (ModuleCat.{0} ℤ) ℤ,
      (∀ (pq : ℤ × ℤ) (r : ℤ) (hr : 1 ≤ r), IsZero (((constantSpectralSequence K).page r).X pq)) ∧
        ¬ IsZero (K.homology 0) := by
  refine ⟨(HomologicalComplex.single _ _ 0).obj (ModuleCat.of ℤ ℤ),
    isZero_constantSpectralSequence_page_X _, fun h ↦ ?_⟩
  have := ModuleCat.isZero_iff_subsingleton.1
    (h.of_iso (HomologicalComplex.singleObjHomologySelfIso _ _ _).symm)
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

end Constant

end TauCeti.Examples.FilteredComplex
