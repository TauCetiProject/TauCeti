/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.FiniteType
public import TauCeti.RingTheory.MvPolynomial.Diagram.Division
public import TauCeti.RingTheory.MvPolynomial.Finrank
import TauCeti.Data.Finsupp.Weight

/-!
# Homogeneous diagram division endomorphisms and finite-jet cutoff determinants

For an upward-closed diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered `σ` and homogeneous
polynomials `H : D.diagramVertices → MvPolynomial σ A` of degrees `v.val.degree`,
`D.diagramDivisionEnd H hH ℓ` sends each monomial basis vector of `homogeneousSubmodule σ A ℓ` to
the corresponding member of `D.diagramSpanSet H ℓ`. Over a semiring with `OrzechProperty A`,
spanning, bijectivity, and unique homogeneous supported division in degree `ℓ` are equivalent
(`Set.bijective_diagramDivisionEnd_iff_span_eq`,
`Set.existsUnique_homogeneous_division_iff_span_eq`). Over a commutative ring `A`, Cramer's rule
identifies these with invertibility of `LinearMap.det (D.diagramDivisionEnd H hH ℓ)`
(`Set.isUnit_det_diagramDivisionEnd_iff_span_eq`), and for monotone `D`,
`Set.span_diagramSpanSet_eq_of_le` shows they hold in *every* degree iff `D.diagramCutoffDet H hH`
is a unit (`Set.isUnit_diagramCutoffDet_iff_forall_span_eq`), hence after any homomorphism
inverting it (`Set.existsUnique_homogeneous_division_of_isUnit_map_diagramCutoffDet`).

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Theorem 8.1 (pp. 274–275) and proof of Theorem 9.6 (p. 282).
-/

public section

open MvPolynomial

namespace Set

section CommSemiring

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommSemiring A]

private noncomputable instance fintypeDegreeEqSubtype (ℓ : ℕ) :
    Fintype {δ : σ →₀ ℕ // δ.degree = ℓ} := Fintype.ofFinite _

open scoped Classical in
/-- The `A`-linear endomorphism of `homogeneousSubmodule σ A ℓ` associated to `D` and `H`, sending
`monomial δ 1` to `monomial (δ - v.val) 1 * H v` when `δ ∈ D.diagramCell v.val` and fixing
`monomial δ 1` outside all vertex cells. -/
noncomputable def diagramDivisionEnd (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (ℓ : ℕ) :
    homogeneousSubmodule σ A ℓ →ₗ[A] homogeneousSubmodule σ A ℓ :=
  (TauCeti.homogeneousMonomialBasis ℓ).constr A fun s ↦
    if h : ∃ v : D.diagramVertices, s.val ∈ D.diagramCell v.val then
      ⟨monomial (s.val - h.choose.val) 1 * H h.choose, (mem_homogeneousSubmodule ℓ _).mpr <|
        (show (s.val - h.choose.val).degree + h.choose.val.degree = ℓ by
          rw [← map_add, tsub_add_cancel_of_le (le_of_mem_diagramCell h.choose_spec), s.property]) ▸
          (isHomogeneous_monomial 1 (by simp [Finsupp.degree_apply])).mul (hH h.choose)⟩
    else TauCeti.homogeneousMonomialBasis ℓ s

theorem coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ}
    (v : D.diagramVertices) {s : {δ : σ →₀ ℕ // δ.degree = ℓ}} (hs : s.val ∈ D.diagramCell v.val) :
    (D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ s) : MvPolynomial σ A) =
      monomial (s.val - v.val) 1 * H v := by
  classical
  have hex : ∃ w : D.diagramVertices, s.val ∈ D.diagramCell w.val := ⟨v, hs⟩
  simp only [diagramDivisionEnd, Module.Basis.constr_basis, hex, ↓reduceDIte,
    Subtype.ext (eq_of_mem_diagramCell hex.choose.property v.property hex.choose_spec hs)]

theorem diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ}
    {s : {δ : σ →₀ ℕ // δ.degree = ℓ}} (hs : ∀ v : D.diagramVertices, s.val ∉ D.diagramCell v.val) :
    D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ s) =
      TauCeti.homogeneousMonomialBasis ℓ s := by
  classical
  simp only [diagramDivisionEnd, Module.Basis.constr_basis,
    show ¬ ∃ w : D.diagramVertices, s.val ∈ D.diagramCell w.val from fun ⟨w, hw⟩ ↦ hs w hw,
    ↓reduceDIte]

/-- For an upward-closed diagram `D`, `D.diagramDivisionEnd H hH ℓ` fixes every monomial basis
vector whose exponent lies outside `D`. -/
theorem diagramDivisionEnd_homogeneousMonomialBasis_of_notMem {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ}
    {s : {δ : σ →₀ ℕ // δ.degree = ℓ}} (hs : s.val ∉ D) :
    D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ s) =
      TauCeti.homogeneousMonomialBasis ℓ s :=
  diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH
    fun v ↦ notMem_diagramCell_of_notMem hD_up v.property hs

/-- For the empty diagram `D = ∅`, `diagramDivisionEnd` is the identity endomorphism. -/
@[simp] theorem diagramDivisionEnd_empty
    (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) (ℓ : ℕ) :
    (∅ : Set (σ →₀ ℕ)).diagramDivisionEnd H hH ℓ = LinearMap.id :=
  (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).ext fun s ↦ by
    simpa using diagramDivisionEnd_homogeneousMonomialBasis_of_notMem isUpperSet_empty hH
      (s := s) (notMem_empty _)

/-- For an upward-closed diagram `D`, the image of `D.diagramDivisionEnd H hH ℓ` inside
`MvPolynomial σ A` is `Submodule.span A (D.diagramSpanSet H ℓ)`. -/
theorem map_range_diagramDivisionEnd_eq_span {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (ℓ : ℕ) :
    (LinearMap.range (D.diagramDivisionEnd H hH ℓ)).map (homogeneousSubmodule σ A ℓ).subtype =
      Submodule.span A (D.diagramSpanSet H ℓ) := by
  let b := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  rw [← LinearMap.range_comp, LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span,
    ← Set.range_comp, ← Set.image_univ]
  refine congrArg (Submodule.span A) (Set.ext fun p ↦ ?_)
  simp only [mem_image, mem_univ, true_and, Function.comp_apply, LinearMap.coe_comp,
    Submodule.coe_subtype, mem_diagramSpanSet_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    by_cases hsD : s.val ∈ D
    · obtain ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hsD
      rw [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v hv]
      exact Or.inl ⟨v, s.val - v.val, tsub_mem_diagramBox_of_mem_diagramCell hv,
        by rw [← map_add, add_tsub_cancel_of_le (le_of_mem_diagramCell hv), s.property], rfl⟩
    · rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem hD_up hH hsD,
        TauCeti.coe_homogeneousMonomialBasis]; exact Or.inr ⟨s.val, hsD, s.property, rfl⟩
  · rintro (⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
    · exact ⟨⟨v.val + β, by rw [map_add, hdeg]⟩, by
        simpa using coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v
          (s := ⟨v.val + β, by rw [map_add, hdeg]⟩) (add_mem_diagramCell_iff.mpr hβ)⟩
    · exact ⟨⟨γ, hdeg⟩, by
        rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem hD_up hH hγ,
          TauCeti.coe_homogeneousMonomialBasis]⟩

/-- For an upward-closed diagram `D`, `D.diagramDivisionEnd H hH ℓ` is surjective if and only if
`D.diagramSpanSet H ℓ` spans `homogeneousSubmodule σ A ℓ`. -/
theorem surjective_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} :
    Function.Surjective (D.diagramDivisionEnd H hH ℓ) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← LinearMap.range_eq_top,
    ← (Submodule.map_injective_of_injective (Submodule.injective_subtype _)).eq_iff,
    map_range_diagramDivisionEnd_eq_span hD_up hH ℓ, Submodule.map_top, Submodule.range_subtype]

open scoped Classical in
private noncomputable def diagramToQR (D : Set (σ →₀ ℕ)) {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A :=
  (fun v ↦ ∑ s ∈ Finset.univ.filter
      (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.val ∈ D.diagramCell v.val),
      monomial (s.val - v.val) (P.val.coeff s.val),
    ∑ s ∈ Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ ¬ s.val ∈ D),
      monomial s.val (P.val.coeff s.val))

private theorem diagramToQR_fst_mem {D : Set (σ →₀ ℕ)} {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ)
    (v : D.diagramVertices) :
    (D.diagramToQR P).1 v ∈
      restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ} := by
  classical
  refine Submodule.sum_mem _ fun s hs ↦ (mem_restrictSupport_iff A).mpr fun β hβ ↦ ?_
  rcases Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hβ)) with rfl
  have hsc := (Finset.mem_filter.mp hs).2
  exact ⟨tsub_mem_diagramBox_of_mem_diagramCell hsc,
    by rw [← map_add, add_tsub_cancel_of_le (le_of_mem_diagramCell hsc), s.property]⟩

private theorem diagramToQR_snd_mem {D : Set (σ →₀ ℕ)} {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramToQR P).2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} := by
  classical
  refine Submodule.sum_mem _ fun s hs ↦ (mem_restrictSupport_iff A).mpr fun γ hγ ↦ ?_
  rcases Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hγ)) with rfl
  exact ⟨(Finset.mem_filter.mp hs).2, s.property⟩

private theorem diagramToQR_coeff_cell {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) (v : D.diagramVertices)
    (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (hs : s.val ∈ D.diagramCell v.val) :
    P.val.coeff s.val = ((D.diagramToQR P).1 v).coeff (s.val - v.val) := by
  classical
  rw [diagramToQR, coeff_sum, Finset.sum_eq_single s (fun s' hs' hne ↦ ?_)
    (fun h ↦ absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩) h)]
  · simp
  · simp [coeff_monomial, show s'.val - v.val ≠ s.val - v.val from fun heq ↦ hne (Subtype.ext <| by
      rw [← add_tsub_cancel_of_le (le_of_mem_diagramCell (Finset.mem_filter.mp hs').2), heq,
        add_tsub_cancel_of_le (le_of_mem_diagramCell hs)])]

private theorem diagramToQR_coeff_rem {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (hs : s.val ∉ D) :
    P.val.coeff s.val = (D.diagramToQR P).2.coeff s.val := by
  classical
  rw [diagramToQR, coeff_sum, Finset.sum_eq_single s
    (fun s' _ hne ↦ by simp [coeff_monomial, Subtype.coe_ne_coe.mpr hne])
    (fun h ↦ absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩) h)]; simp

private theorem coe_diagramDivisionEnd_eq_diagramToQR {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramDivisionEnd H hH ℓ P : MvPolynomial σ A) =
      ∑ v, (D.diagramToQR P).1 v * H v + (D.diagramToQR P).2 := by
  classical
  conv_lhs =>
    rw [← (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).sum_repr P,
      map_sum, Submodule.coe_sum]
  simp_rw [map_smul, SetLike.val_smul, TauCeti.homogeneousMonomialBasis_repr_apply]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.val ∈ D)]
  congr 1
  · have hpart : Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.val ∈ D) =
        Finset.univ.biUnion fun v : D.diagramVertices ↦
          Finset.univ.filter (fun s ↦ s.val ∈ D.diagramCell v.val) := by
      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun hs ↦ let ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hs; ⟨v, hv⟩,
        fun ⟨v, hv⟩ ↦ diagramCell_subset hD_up v.property hv⟩
    rw [hpart, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun v _ ↦ by
        simp only [diagramToQR, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s hs ↦ by
          rw [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v
            (Finset.mem_filter.mp hs).2, ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
    · exact fun v₁ _ v₂ _ hne ↦ Finset.disjoint_left.mpr fun s h₁ h₂ ↦ hne (Subtype.ext
        (eq_of_mem_diagramCell v₁.property v₂.property
          (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2))
  · exact Finset.sum_congr rfl fun s hs ↦ by
      rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem hD_up hH
        (Finset.mem_filter.mp hs).2, TauCeti.coe_homogeneousMonomialBasis, smul_monomial,
        smul_eq_mul, mul_one]

open scoped Classical in
private noncomputable def diagramFromQR (D : Set (σ →₀ ℕ)) (ℓ : ℕ)
    (qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A) :
    homogeneousSubmodule σ A ℓ :=
  (TauCeti.homogeneousMonomialBasis ℓ).repr.symm (Finsupp.equivFunOnFinite.symm fun s ↦
    if h : ∃ v : D.diagramVertices, s.val ∈ D.diagramCell v.val then
      (qr.1 h.choose).coeff (s.val - h.choose.val)
    else qr.2.coeff s.val)

private theorem diagramToQR_injective {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    {P₁ P₂ : homogeneousSubmodule σ A ℓ} (heq : D.diagramToQR P₁ = D.diagramToQR P₂) :
    P₁ = P₂ := by
  refine (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).repr.injective
    (Finsupp.ext fun s ↦ ?_)
  simp only [TauCeti.homogeneousMonomialBasis_repr_apply]
  by_cases hsD : s.val ∈ D
  · obtain ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hsD
    rw [diagramToQR_coeff_cell P₁ v s hv, diagramToQR_coeff_cell P₂ v s hv, heq]
  · rw [diagramToQR_coeff_rem P₁ s hsD, diagramToQR_coeff_rem P₂ s hsD, heq]

private theorem diagramToQR_diagramFromQR {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    {qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A}
    (hQ : ∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ})
    (hR : qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ}) :
    D.diagramToQR (D.diagramFromQR ℓ qr) = qr := by
  classical
  have hcoeff (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) : (D.diagramFromQR ℓ qr).val.coeff s.val =
      if h : ∃ v : D.diagramVertices, s.val ∈ D.diagramCell v.val then
        (qr.1 h.choose).coeff (s.val - h.choose.val)
      else qr.2.coeff s.val := by
    rw [← TauCeti.homogeneousMonomialBasis_repr_apply ℓ _ s, diagramFromQR,
      LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
  refine Prod.ext (funext fun v ↦ (eq_of_mem_restrictSupport_of_coeff_eq (hQ v)
    (diagramToQR_fst_mem _ v) fun β hβ ↦ ?_).symm)
    (eq_of_mem_restrictSupport_of_coeff_eq hR (diagramToQR_snd_mem _) fun γ hγ ↦ ?_).symm
  · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨v.val + β, by rw [map_add, hβ.2]⟩
    have hs : s.val ∈ D.diagramCell v.val := add_mem_diagramCell_iff.mpr hβ.1
    have hex : ∃ w : D.diagramVertices, s.val ∈ D.diagramCell w.val := ⟨v, hs⟩
    simpa only [s, add_tsub_cancel_left, hex, ↓reduceDIte,
      Subtype.ext (eq_of_mem_diagramCell hex.choose.property v.property hex.choose_spec hs)] using
      (hcoeff s).symm.trans (diagramToQR_coeff_cell _ v s hs)
  · have hex : ¬ ∃ w : D.diagramVertices, γ ∈ D.diagramCell w.val :=
      fun ⟨w, hw⟩ ↦ notMem_diagramCell_of_notMem hD_up w.property hγ.1 hw
    simpa only [hex, ↓reduceDIte] using
      (hcoeff ⟨γ, hγ.2⟩).symm.trans (diagramToQR_coeff_rem _ ⟨γ, hγ.2⟩ hγ.1)

/-- `diagramDivisionEnd` commutes with changing coefficients along any ring homomorphism
`φ : A →+* B`. -/
theorem mapHomogeneousSubmodule_diagramDivisionEnd {B : Type*} [CommSemiring B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) (ℓ : ℕ)
    (P : homogeneousSubmodule σ A ℓ) :
    TauCeti.mapHomogeneousSubmodule φ ℓ (D.diagramDivisionEnd H hH ℓ P) =
      D.diagramDivisionEnd (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) ℓ
        (TauCeti.mapHomogeneousSubmodule φ ℓ P) := by
  classical
  rw [← (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).sum_repr P]
  simp only [map_sum, LinearMap.map_smulₛₗ,
    TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis]
  refine Finset.sum_congr rfl fun s _ ↦ congrArg _ (Subtype.ext ?_)
  by_cases hex : ∃ v : D.diagramVertices, s.val ∈ D.diagramCell v.val
  · obtain ⟨v, hv⟩ := hex
    simp only [TauCeti.coe_mapHomogeneousSubmodule_apply,
      coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell _ v hv,
      map_mul, map_monomial, map_one]
  · have hnot : ∀ v : D.diagramVertices, s.val ∉ D.diagramCell v.val := fun v hv ↦ hex ⟨v, hv⟩
    simp only [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell _ hnot,
      TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis]

end CommSemiring

section Orzech

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommSemiring A] [OrzechProperty A]

/-- For an upward-closed diagram `D` over a commutative semiring with `OrzechProperty A`,
`D.diagramDivisionEnd H hH ℓ` is bijective if and only if `D.diagramSpanSet H ℓ` spans
`homogeneousSubmodule σ A ℓ`. -/
theorem bijective_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} :
    Function.Bijective (D.diagramDivisionEnd H hH ℓ) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  ⟨fun h ↦ (surjective_diagramDivisionEnd_iff_span_eq hD_up hH).mp h.2,
    fun h ↦ OrzechProperty.bijective_of_surjective_endomorphism _
      ((surjective_diagramDivisionEnd_iff_span_eq hD_up hH).mpr h)⟩

/-- For an upward-closed diagram `D` over a commutative semiring with `OrzechProperty A`, spanning
in degree `ℓ` is equivalent to unique homogeneous supported division in degree `ℓ`. -/
theorem existsUnique_homogeneous_division_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} :
    (∀ G ∈ homogeneousSubmodule σ A ℓ,
      ∃! qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A,
        (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ∧
        qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
        ∑ v, qr.1 v * H v + qr.2 = G) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← bijective_diagramDivisionEnd_iff_span_eq hD_up hH]
  refine ⟨fun hdiv ↦ ⟨fun P₁ P₂ hP ↦ diagramToQR_injective hD_up ?_, fun G ↦ ?_⟩,
    fun hbij G hG ↦ ?_⟩
  · obtain ⟨_, _, huniq⟩ := hdiv _ (D.diagramDivisionEnd H hH ℓ P₁).property
    exact (huniq _ ⟨diagramToQR_fst_mem P₁, diagramToQR_snd_mem P₁,
        (coe_diagramDivisionEnd_eq_diagramToQR hD_up hH P₁).symm⟩).trans
      (huniq _ ⟨diagramToQR_fst_mem P₂, diagramToQR_snd_mem P₂,
        by rw [hP, coe_diagramDivisionEnd_eq_diagramToQR hD_up hH P₂]⟩).symm
  · obtain ⟨qr, ⟨hQ, hR, hsum⟩, _⟩ := hdiv G.val G.property
    exact ⟨D.diagramFromQR ℓ qr, Subtype.ext <| by
      rw [coe_diagramDivisionEnd_eq_diagramToQR hD_up hH,
        diagramToQR_diagramFromQR hD_up hQ hR, hsum]⟩
  · obtain ⟨P, hP⟩ := hbij.2 ⟨G, hG⟩
    exact ⟨D.diagramToQR P, ⟨diagramToQR_fst_mem P, diagramToQR_snd_mem P,
      by rw [← coe_diagramDivisionEnd_eq_diagramToQR hD_up hH P, hP]⟩,
      fun qr ⟨hQ, hR, hsum⟩ ↦ (diagramToQR_diagramFromQR hD_up hQ hR).symm.trans
        (congrArg D.diagramToQR (hbij.1 (Eq.trans (Subtype.ext <| by
          rw [coe_diagramDivisionEnd_eq_diagramToQR hD_up hH,
            diagramToQR_diagramFromQR hD_up hQ hR, hsum]) hP.symm)))⟩

end Orzech

section CommRing

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommRing A]

/-- For an upward-closed diagram `D` over a commutative ring `A`, the determinant of
`D.diagramDivisionEnd H hH ℓ` is a unit in `A` if and only if `D.diagramSpanSet H ℓ` spans
`homogeneousSubmodule σ A ℓ`. -/
theorem isUnit_det_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} :
    IsUnit (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff,
    bijective_diagramDivisionEnd_iff_span_eq hD_up hH]

/-- Changing coefficients along `φ : A →+* B` maps the block determinant of
`D.diagramDivisionEnd H hH ℓ` to the block determinant of `MvPolynomial.map φ ∘ H`. -/
theorem map_det_diagramDivisionEnd {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) (ℓ : ℕ) :
    φ (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) =
      LinearMap.det
        (D.diagramDivisionEnd (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) ℓ) := by
  classical
  let bA := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  rw [← LinearMap.det_toMatrix bA,
    ← LinearMap.det_toMatrix (TauCeti.homogeneousMonomialBasis (σ := σ) (R := B) ℓ),
    RingHom.map_det]
  congr 1; ext s t
  simpa [bA, LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    TauCeti.coe_mapHomogeneousSubmodule_apply,
    TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis, coeff_map] using
    congrArg (fun x : homogeneousSubmodule σ B ℓ ↦ x.val.coeff s.val)
      (mapHomogeneousSubmodule_diagramDivisionEnd φ hH ℓ (bA t))

/-- The finite-jet determinant product across degrees `ℓ ≤ D.diagramCutoff` controlling
homogeneous supported division in *all* degrees for a monotone upward-closed diagram `D`
(Bierstone–Milman, p. 282). -/
noncomputable def diagramCutoffDet (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.val.degree) : A :=
  ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1), LinearMap.det (D.diagramDivisionEnd H hH ℓ)

theorem diagramCutoffDet_def (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) : D.diagramCutoffDet H hH =
      ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1), LinearMap.det (D.diagramDivisionEnd H hH ℓ) := (rfl)

/-- For the empty diagram `D = ∅`, `diagramCutoffDet` equals `1`. -/
@[simp] theorem diagramCutoffDet_empty
    (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    (∅ : Set (σ →₀ ℕ)).diagramCutoffDet H hH = 1 := by simp [diagramCutoffDet_def]

/-- For `D = Set.univ`, `diagramCutoffDet` equals the constant coefficient of `H ⟨0, _⟩`. -/
@[simp] theorem diagramCutoffDet_univ
    (H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    (Set.univ : Set (σ →₀ ℕ)).diagramCutoffDet H hH = constantCoeff (H ⟨0, by simp⟩) := by
  let : Unique {δ : σ →₀ ℕ // δ.degree = 0} :=
    ⟨⟨0, by simp⟩, fun s ↦ Subtype.ext (by simpa [Finsupp.degree_eq_zero_iff] using s.property)⟩
  have h0 : (default : {δ : σ →₀ ℕ // δ.degree = 0}).val = 0 := rfl
  rw [diagramCutoffDet_def, diagramCutoff_univ, Finset.range_one, Finset.prod_singleton,
    ← LinearMap.det_toMatrix (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) 0),
    Matrix.det_unique, LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH ⟨0, by simp⟩
      (by rw [h0]; simp), h0]; simp [constantCoeff_eq]

theorem map_diagramCutoffDet {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) : φ (D.diagramCutoffDet H hH) =
      D.diagramCutoffDet (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) := by
  simp [diagramCutoffDet_def, map_prod, map_det_diagramDivisionEnd]

/-- For an upward-closed monotone diagram `D`, the single finite-jet determinant product
`D.diagramCutoffDet H hH` is a unit in `A` if and only if `D.diagramSpanSet H ℓ` spans
`homogeneousSubmodule σ A ℓ` in *every* degree `ℓ : ℕ`. -/
theorem isUnit_diagramCutoffDet_iff_forall_span_eq {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    IsUnit (D.diagramCutoffDet H hH) ↔
      ∀ ℓ : ℕ, Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  have hiff (ℓ : ℕ) := isUnit_det_diagramDivisionEnd_iff_span_eq (ℓ := ℓ) hD_up hH
  rw [diagramCutoffDet_def, IsUnit.prod_iff]
  refine ⟨fun h ℓ ↦ ?_, fun h ℓ _ ↦ (hiff ℓ).mpr (h ℓ)⟩
  by_cases hle : ℓ ≤ D.diagramCutoff
  · exact (hiff ℓ).mp (h ℓ (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)))
  · exact span_diagramSpanSet_eq_of_le hD_up hD_mono hH le_rfl
      ((hiff _).mp (h D.diagramCutoff (Finset.mem_range.mpr (Nat.lt_succ_self _))))
      (Nat.le_of_not_ge hle)

/-- For an upward-closed monotone diagram `D`, `D.diagramCutoffDet H hH` is a unit in `A` if and
only if unique homogeneous supported division holds in *every* degree `ℓ : ℕ`. -/
theorem isUnit_diagramCutoffDet_iff_forall_existsUnique_division {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    IsUnit (D.diagramCutoffDet H hH) ↔
      ∀ ℓ : ℕ, ∀ G ∈ homogeneousSubmodule σ A ℓ,
        ∃! qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A,
          (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ∧
          qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
          ∑ v, qr.1 v * H v + qr.2 = G := by
  rw [isUnit_diagramCutoffDet_iff_forall_span_eq hD_up hD_mono hH]
  exact forall_congr' fun ℓ ↦ (existsUnique_homogeneous_division_iff_span_eq hD_up hH).symm

/-- After any ring homomorphism `φ : A →+* B` (such as `algebraMap A (Localization.Away _)`) that
inverts `D.diagramCutoffDet H hH`, unique homogeneous supported division for
`MvPolynomial.map φ ∘ H` holds in *every* degree `ℓ : ℕ` (Bierstone–Milman, p. 282). -/
theorem existsUnique_homogeneous_division_of_isUnit_map_diagramCutoffDet
    {B : Type*} [CommRing B] (φ : A →+* B) {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (hunit : IsUnit (φ (D.diagramCutoffDet H hH))) (ℓ : ℕ)
    {G : MvPolynomial σ B} (hG : G ∈ homogeneousSubmodule σ B ℓ) :
    ∃! qr : (D.diagramVertices → MvPolynomial σ B) × MvPolynomial σ B,
      (∀ v, qr.1 v ∈ restrictSupport B {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ∧
      qr.2 ∈ restrictSupport B {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
      ∑ v, qr.1 v * MvPolynomial.map φ (H v) + qr.2 = G :=
  (isUnit_diagramCutoffDet_iff_forall_existsUnique_division hD_up hD_mono
    (fun v ↦ (hH v).map φ)).mp (map_diagramCutoffDet φ hH ▸ hunit) ℓ G hG

end CommRing

end Set
