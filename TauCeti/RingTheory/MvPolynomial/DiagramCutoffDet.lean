/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.RingTheory.MvPolynomial.DiagramDivision
public import TauCeti.RingTheory.MvPolynomial.Finrank
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.FiniteType

/-!
# Homogeneous diagram division endomorphisms and finite-jet cutoff determinants

For an upward-closed diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered variable set `σ` and
homogeneous polynomials `H : D.diagramVertices → MvPolynomial σ A` of degrees `v.1.degree` over a
commutative ring `A`, `D.diagramDivisionEnd H hH ℓ` is the `A`-linear endomorphism of
`homogeneousSubmodule σ A ℓ` sending each monomial basis vector to the corresponding member of
`D.diagramSpanSet H ℓ`. By the Orzech property and Cramer's rule, spanning in degree `ℓ`,
invertibility of `LinearMap.det (D.diagramDivisionEnd H hH ℓ)`, and unique homogeneous supported
division in degree `ℓ` are equivalent (`Set.isUnit_det_diagramDivisionEnd_iff_span_eq`,
`Set.existsUnique_homogeneous_division_iff_span_eq`). For an upward-closed monotone diagram `D`,
`Set.span_diagramSpanSet_eq_of_le` implies that these hold in *every* degree `ℓ : ℕ` if and only if
the finite-jet determinant product `D.diagramCutoffDet H hH` across `ℓ ≤ D.diagramCutoff` is a unit
(`Set.isUnit_diagramCutoffDet_iff_forall_span_eq`), hence after any ring homomorphism inverting
`D.diagramCutoffDet H hH` (`Set.existsUnique_homogeneous_division_of_isUnit_map_diagramCutoffDet`).

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Theorem 8.1 (pp. 274–275) and proof of Theorem 9.6 (p. 282).
-/

public section

open MvPolynomial

namespace Set

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommRing A]

private instance finiteDegreeEqSubtype (ℓ : ℕ) : Finite {δ : σ →₀ ℕ // δ.degree = ℓ} :=
  Finsupp.finite_of_degree_eq ℓ

private noncomputable instance fintypeDegreeEqSubtype (ℓ : ℕ) :
    Fintype {δ : σ →₀ ℕ // δ.degree = ℓ} :=
  Fintype.ofFinite _

open scoped Classical in
/-- The `A`-linear endomorphism of `homogeneousSubmodule σ A ℓ` associated to `D` and `H`, sending
`monomial δ 1` to `monomial (δ - v.1) 1 * H v` when `δ ∈ D.diagramCell v.1` and fixing
`monomial δ 1` outside all vertex cells. -/
noncomputable def diagramDivisionEnd (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    (ℓ : ℕ) :
    homogeneousSubmodule σ A ℓ →ₗ[A] homogeneousSubmodule σ A ℓ :=
  (TauCeti.homogeneousMonomialBasis ℓ).constr A fun s ↦
    if h : ∃ v : D.diagramVertices, s.1 ∈ D.diagramCell v.1 then
      ⟨monomial (s.1 - h.choose.1) 1 * H h.choose, by
        have hle : h.choose.1 ≤ s.1 := (D.mem_diagramCell_iff.mp h.choose_spec).1
        have hdeg : (s.1 - h.choose.1).degree + h.choose.1.degree = ℓ := by
          rw [← map_add, tsub_add_cancel_of_le hle, s.2]
        have hhom : (monomial (s.1 - h.choose.1) (1 : A) * H h.choose).IsHomogeneous
            ((s.1 - h.choose.1).degree + h.choose.1.degree) :=
          (isHomogeneous_monomial 1 (by simp [Finsupp.degree_apply])).mul (hH h.choose)
        rw [hdeg] at hhom
        exact (mem_homogeneousSubmodule ℓ _).mpr hhom⟩
    else
      TauCeti.homogeneousMonomialBasis ℓ s

theorem coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) {ℓ : ℕ}
    (v : D.diagramVertices) {s : {δ : σ →₀ ℕ // δ.degree = ℓ}} (hs : s.1 ∈ D.diagramCell v.1) :
    (D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ s) : MvPolynomial σ A) =
      monomial (s.1 - v.1) 1 * H v := by
  classical
  have hex : ∃ w : D.diagramVertices, s.1 ∈ D.diagramCell w.1 := ⟨v, hs⟩
  have hchoose : hex.choose = v := Subtype.ext <| by
    by_contra hne
    exact (disjoint_diagramCell hex.choose.2 v.2 hne).le_bot ⟨hex.choose_spec, hs⟩
  simp only [diagramDivisionEnd, Module.Basis.constr_basis, hex, ↓reduceDIte, hchoose]

theorem diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) {ℓ : ℕ}
    {s : {δ : σ →₀ ℕ // δ.degree = ℓ}} (hs : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1) :
    D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ s) =
      TauCeti.homogeneousMonomialBasis ℓ s := by
  classical
  have hex : ¬ ∃ w : D.diagramVertices, s.1 ∈ D.diagramCell w.1 := fun ⟨w, hw⟩ ↦ hs w hw
  simp only [diagramDivisionEnd, Module.Basis.constr_basis, hex, ↓reduceDIte]

/-- For an upward-closed diagram `D`, the image of `D.diagramDivisionEnd H hH ℓ` inside
`MvPolynomial σ A` is `Submodule.span A (D.diagramSpanSet H ℓ)`. -/
theorem map_range_diagramDivisionEnd_eq_span {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    (ℓ : ℕ) :
    (LinearMap.range (D.diagramDivisionEnd H hH ℓ)).map (homogeneousSubmodule σ A ℓ).subtype =
      Submodule.span A (D.diagramSpanSet H ℓ) := by
  let b := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  have hset : (fun s ↦ (D.diagramDivisionEnd H hH ℓ (b s) : MvPolynomial σ A)) '' Set.univ =
      D.diagramSpanSet H ℓ := by
    ext p
    simp only [mem_image, mem_univ, true_and, mem_diagramSpanSet_iff]
    constructor
    · rintro ⟨s, rfl⟩
      by_cases hsD : s.1 ∈ D
      · obtain ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hsD
        rw [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v hv]
        refine Or.inl ⟨v, s.1 - v.1, tsub_mem_diagramBox_of_mem_diagramCell hv, ?_, rfl⟩
        rw [← map_add, add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hv).1, s.2]
      · have hnot : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1 := fun v hv ↦
          hsD (hD_up (D.mem_diagramCell_iff.mp hv).1 (D.diagramVertices_subset v.2))
        rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH hnot,
          TauCeti.coe_homogeneousMonomialBasis]
        exact Or.inr ⟨s.1, hsD, s.2, rfl⟩
    · rintro (⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
      · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨v.1 + β, by rw [map_add, hdeg]⟩
        refine ⟨s, ?_⟩
        rw [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v
          (add_mem_diagramCell_iff.mpr hβ)]
        simp [s]
      · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨γ, hdeg⟩
        have hnot : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1 := fun v hv ↦
          hγ (hD_up (D.mem_diagramCell_iff.mp hv).1 (D.diagramVertices_subset v.2))
        refine ⟨s, ?_⟩
        rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH hnot,
          TauCeti.coe_homogeneousMonomialBasis]
  rw [← hset]
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [← b.sum_repr x, map_sum, map_sum]
    refine Submodule.sum_mem _ fun s _ ↦ ?_
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, trivial, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, _, rfl⟩
    exact ⟨D.diagramDivisionEnd H hH ℓ (b s), ⟨b s, rfl⟩, rfl⟩

theorem surjective_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} :
    Function.Surjective (D.diagramDivisionEnd H hH ℓ) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← LinearMap.range_eq_top, ← map_range_diagramDivisionEnd_eq_span hD_up hH ℓ]
  refine ⟨fun h ↦ by rw [h, Submodule.map_top, Submodule.range_subtype], fun h ↦ eq_top_iff.mpr ?_⟩
  intro y _
  have hy : (y : MvPolynomial σ A) ∈
      (LinearMap.range (D.diagramDivisionEnd H hH ℓ)).map (homogeneousSubmodule σ A ℓ).subtype := by
    rw [h]; exact y.2
  obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
  exact Subtype.ext hzy ▸ hz

theorem bijective_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} :
    Function.Bijective (D.diagramDivisionEnd H hH ℓ) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  ⟨fun h ↦ (surjective_diagramDivisionEnd_iff_span_eq hD_up hH).mp h.2,
    fun h ↦ OrzechProperty.bijective_of_surjective_endomorphism _
      ((surjective_diagramDivisionEnd_iff_span_eq hD_up hH).mpr h)⟩

theorem isUnit_det_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} :
    IsUnit (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff,
    bijective_diagramDivisionEnd_iff_span_eq hD_up hH]

open scoped Classical in
private noncomputable def diagramToQR (D : Set (σ →₀ ℕ)) {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A :=
  (fun v ↦ ∑ s ∈ Finset.univ.filter
      (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∈ D.diagramCell v.1),
      monomial (s.1 - v.1) (P.1.coeff s.1),
    ∑ s ∈ Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ ¬ s.1 ∈ D),
      monomial s.1 (P.1.coeff s.1))

private theorem diagramToQR_fst_mem {D : Set (σ →₀ ℕ)} {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ)
    (v : D.diagramVertices) :
    (D.diagramToQR P).1 v ∈
      restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ} := by
  classical
  rw [diagramToQR]
  refine Submodule.sum_mem _ fun s hs ↦ (mem_restrictSupport_iff A).mpr fun β hβ ↦ ?_
  have hsc : s.1 ∈ D.diagramCell v.1 := (Finset.mem_filter.mp hs).2
  rcases Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hβ)) with rfl
  exact ⟨tsub_mem_diagramBox_of_mem_diagramCell hsc, by
    rw [← map_add, add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hsc).1, s.2]⟩

private theorem diagramToQR_snd_mem {D : Set (σ →₀ ℕ)} {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramToQR P).2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} := by
  classical
  rw [diagramToQR]
  refine Submodule.sum_mem _ fun s hs ↦ (mem_restrictSupport_iff A).mpr fun γ hγ ↦ ?_
  rcases Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hγ)) with rfl
  exact ⟨(Finset.mem_filter.mp hs).2, s.2⟩

private theorem diagramToQR_coeff_cell {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) (v : D.diagramVertices)
    (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (hs : s.1 ∈ D.diagramCell v.1) :
    P.1.coeff s.1 = ((D.diagramToQR P).1 v).coeff (s.1 - v.1) := by
  classical
  rw [diagramToQR]
  simp only [coeff_sum]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' hs' hne
    have hs'c : s'.1 ∈ D.diagramCell v.1 := (Finset.mem_filter.mp hs').2
    have hne' : s'.1 - v.1 ≠ s.1 - v.1 := fun heq ↦ hne (Subtype.ext <| by
      rw [← add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hs'c).1, heq,
        add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hs).1])
    simp [coeff_monomial, hne']
  · exact fun habs ↦ absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩) habs

private theorem diagramToQR_coeff_rem {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (hs : s.1 ∉ D) :
    P.1.coeff s.1 = (D.diagramToQR P).2.coeff s.1 := by
  classical
  rw [diagramToQR]
  simp only [coeff_sum]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hne
    simp [coeff_monomial, Subtype.coe_ne_coe.mpr hne]
  · exact fun habs ↦ absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩) habs

private theorem coe_diagramDivisionEnd_eq_diagramToQR {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramDivisionEnd H hH ℓ P : MvPolynomial σ A) =
      ∑ v, (D.diagramToQR P).1 v * H v + (D.diagramToQR P).2 := by
  classical
  conv_lhs =>
    rw [← (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).sum_repr P,
      map_sum, Submodule.coe_sum]
  simp_rw [map_smul, SetLike.val_smul, TauCeti.homogeneousMonomialBasis_repr_apply]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∈ D)]
  congr 1
  · have hpart : Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∈ D) =
        Finset.univ.biUnion (fun v : D.diagramVertices ↦
          Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦
            s.1 ∈ D.diagramCell v.1)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun hs ↦ let ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hs; ⟨v, hv⟩,
        fun ⟨v, hv⟩ ↦ hD_up (D.mem_diagramCell_iff.mp hv).1 (D.diagramVertices_subset v.2)⟩
    rw [hpart, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp only [diagramToQR, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs ↦ ?_
      rw [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v
        (Finset.mem_filter.mp hs).2, ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
    · intro v₁ _ v₂ _ hne
      exact Finset.disjoint_left.mpr fun s hs₁ hs₂ ↦
        (disjoint_diagramCell v₁.2 v₂.2 (Subtype.coe_ne_coe.mpr hne)).le_bot
          ⟨(Finset.mem_filter.mp hs₁).2, (Finset.mem_filter.mp hs₂).2⟩
  · simp only [diagramToQR]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hsD : s.1 ∉ D := (Finset.mem_filter.mp hs).2
    have hnot : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1 := fun v hv ↦
      hsD (hD_up (D.mem_diagramCell_iff.mp hv).1 (D.diagramVertices_subset v.2))
    rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH hnot,
      TauCeti.coe_homogeneousMonomialBasis, smul_monomial, smul_eq_mul, mul_one]

open scoped Classical in
private noncomputable def diagramFromQR (D : Set (σ →₀ ℕ)) (ℓ : ℕ)
    (qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A) :
    homogeneousSubmodule σ A ℓ :=
  (TauCeti.homogeneousMonomialBasis ℓ).repr.symm (Finsupp.equivFunOnFinite.symm fun s ↦
    if h : ∃ v : D.diagramVertices, s.1 ∈ D.diagramCell v.1 then
      (qr.1 h.choose).coeff (s.1 - h.choose.1)
    else qr.2.coeff s.1)

private theorem diagramToQR_injective {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    {P₁ P₂ : homogeneousSubmodule σ A ℓ} (heq : D.diagramToQR P₁ = D.diagramToQR P₂) :
    P₁ = P₂ := by
  refine (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).repr.injective
    (Finsupp.ext fun s ↦ ?_)
  rw [TauCeti.homogeneousMonomialBasis_repr_apply, TauCeti.homogeneousMonomialBasis_repr_apply]
  by_cases hsD : s.1 ∈ D
  · obtain ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hsD
    rw [diagramToQR_coeff_cell P₁ v s hv, diagramToQR_coeff_cell P₂ v s hv, heq]
  · rw [diagramToQR_coeff_rem P₁ s hsD, diagramToQR_coeff_rem P₂ s hsD, heq]

private theorem diagramToQR_diagramFromQR {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    {qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A}
    (hQ : ∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ})
    (hR : qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ}) :
    D.diagramToQR (D.diagramFromQR ℓ qr) = qr := by
  classical
  refine Prod.ext (funext fun v ↦ (eq_of_mem_restrictSupport_of_coeff_eq (hQ v)
    (diagramToQR_fst_mem (D.diagramFromQR ℓ qr) v) fun β hβ ↦ ?_).symm)
    (eq_of_mem_restrictSupport_of_coeff_eq hR (diagramToQR_snd_mem (D.diagramFromQR ℓ qr))
      fun γ hγ ↦ ?_).symm
  · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨v.1 + β, by rw [map_add, hβ.2]⟩
    have hs : s.1 ∈ D.diagramCell v.1 := add_mem_diagramCell_iff.mpr hβ.1
    have hex : ∃ w : D.diagramVertices, s.1 ∈ D.diagramCell w.1 := ⟨v, hs⟩
    have hchoose : hex.choose = v := Subtype.ext <| by
      by_contra hne; exact (disjoint_diagramCell hex.choose.2 v.2 hne).le_bot ⟨hex.choose_spec, hs⟩
    have h₁ : (D.diagramFromQR ℓ qr).1.coeff s.1 = (qr.1 v).coeff β := by
      rw [← TauCeti.homogeneousMonomialBasis_repr_apply ℓ _ s, diagramFromQR,
        LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
      simp only [hex, ↓reduceDIte, hchoose, s, add_tsub_cancel_left]
    simpa only [s, add_tsub_cancel_left] using
      h₁.symm.trans (diagramToQR_coeff_cell (D.diagramFromQR ℓ qr) v s hs)
  · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨γ, hγ.2⟩
    have hex : ¬ ∃ w : D.diagramVertices, s.1 ∈ D.diagramCell w.1 := fun ⟨w, hw⟩ ↦
      hγ.1 (hD_up (D.mem_diagramCell_iff.mp hw).1 (D.diagramVertices_subset w.2))
    have h₁ : (D.diagramFromQR ℓ qr).1.coeff s.1 = qr.2.coeff γ := by
      rw [← TauCeti.homogeneousMonomialBasis_repr_apply ℓ _ s, diagramFromQR,
        LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
      simp only [hex, ↓reduceDIte, s]
    exact h₁.symm.trans (diagramToQR_coeff_rem (D.diagramFromQR ℓ qr) s hγ.1)

/-- Spanning in degree `ℓ` is equivalent to unique homogeneous supported division in degree `ℓ`. -/
theorem existsUnique_homogeneous_division_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} :
    (∀ G ∈ homogeneousSubmodule σ A ℓ,
      ∃! qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A,
        (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ}) ∧
        qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
        ∑ v, qr.1 v * H v + qr.2 = G) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← bijective_diagramDivisionEnd_iff_span_eq hD_up hH]
  constructor
  · intro hdiv
    refine ⟨fun P₁ P₂ hP ↦ diagramToQR_injective hD_up ?_, fun G ↦ ?_⟩
    · obtain ⟨_, _, huniq⟩ := hdiv (D.diagramDivisionEnd H hH ℓ P₁)
        (D.diagramDivisionEnd H hH ℓ P₁).2
      have h₁ := (coe_diagramDivisionEnd_eq_diagramToQR hD_up hH P₁).symm
      have h₂ : ∑ v, (D.diagramToQR P₂).1 v * H v + (D.diagramToQR P₂).2 =
          (D.diagramDivisionEnd H hH ℓ P₁ : MvPolynomial σ A) := by
        rw [hP, coe_diagramDivisionEnd_eq_diagramToQR hD_up hH P₂]
      exact (huniq _ ⟨diagramToQR_fst_mem P₁, diagramToQR_snd_mem P₁, h₁⟩).trans
        (huniq _ ⟨diagramToQR_fst_mem P₂, diagramToQR_snd_mem P₂, h₂⟩).symm
    · obtain ⟨qr, ⟨hQ, hR, hsum⟩, _⟩ := hdiv G.1 G.2
      refine ⟨D.diagramFromQR ℓ qr, Subtype.ext ?_⟩
      rw [coe_diagramDivisionEnd_eq_diagramToQR hD_up hH,
        diagramToQR_diagramFromQR hD_up hQ hR, hsum]
  · intro hbij G hG
    obtain ⟨P, hP⟩ := hbij.2 ⟨G, hG⟩
    refine ⟨D.diagramToQR P, ⟨diagramToQR_fst_mem P, diagramToQR_snd_mem P, ?_⟩,
      fun qr ⟨hQ, hR, hsum⟩ ↦ ?_⟩
    · rw [← coe_diagramDivisionEnd_eq_diagramToQR hD_up hH P, hP]
    · have hend : D.diagramDivisionEnd H hH ℓ (D.diagramFromQR ℓ qr) = ⟨G, hG⟩ := Subtype.ext <| by
        rw [coe_diagramDivisionEnd_eq_diagramToQR hD_up hH,
          diagramToQR_diagramFromQR hD_up hQ hR, hsum]
      exact (diagramToQR_diagramFromQR hD_up hQ hR).symm.trans
        (congrArg D.diagramToQR (hbij.1 (hend.trans hP.symm)))

/-- `diagramDivisionEnd` commutes with changing coefficients along any ring homomorphism
`φ : A →+* B`. -/
theorem mapHomogeneousSubmodule_diagramDivisionEnd {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) (ℓ : ℕ)
    (P : homogeneousSubmodule σ A ℓ) :
    TauCeti.mapHomogeneousSubmodule φ ℓ (D.diagramDivisionEnd H hH ℓ P) =
      D.diagramDivisionEnd (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) ℓ
        (TauCeti.mapHomogeneousSubmodule φ ℓ P) := by
  rw [← (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).sum_repr P,
    map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [LinearMap.map_smulₛₗ, TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis]
  congr 1; apply Subtype.ext
  classical
  by_cases hex : ∃ v : D.diagramVertices, s.1 ∈ D.diagramCell v.1
  · obtain ⟨v, hv⟩ := hex
    rw [TauCeti.coe_mapHomogeneousSubmodule_apply,
      coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v hv,
      coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell _ v hv,
      map_mul, map_monomial, map_one]
  · have hnot : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1 := fun v hv ↦ hex ⟨v, hv⟩
    rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH hnot,
      diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell _ hnot,
      TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis]

/-- Changing coefficients along `φ : A →+* B` maps the block determinant of
`D.diagramDivisionEnd H hH ℓ` to the block determinant of `MvPolynomial.map φ ∘ H`. -/
theorem map_det_diagramDivisionEnd {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) (ℓ : ℕ) :
    φ (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) =
      LinearMap.det
        (D.diagramDivisionEnd (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) ℓ) := by
  classical
  let bA := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  let bB := TauCeti.homogeneousMonomialBasis (σ := σ) (R := B) ℓ
  rw [← LinearMap.det_toMatrix bA, ← LinearMap.det_toMatrix bB, RingHom.map_det]
  congr 1; ext s t
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    TauCeti.homogeneousMonomialBasis_repr_apply]
  have hcomm := mapHomogeneousSubmodule_diagramDivisionEnd φ hH ℓ (bA t)
  rw [TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis] at hcomm
  simpa [TauCeti.coe_mapHomogeneousSubmodule_apply, coeff_map] using
    congrArg (fun x : homogeneousSubmodule σ B ℓ ↦ x.1.coeff s.1) hcomm

/-- The finite-jet determinant product across degrees `ℓ ≤ D.diagramCutoff` controlling
homogeneous supported division in *all* degrees for a monotone upward-closed diagram `D`
(Bierstone–Milman, p. 282). -/
noncomputable def diagramCutoffDet (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.1.degree) : A :=
  ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1), LinearMap.det (D.diagramDivisionEnd H hH ℓ)

theorem diagramCutoffDet_def (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    D.diagramCutoffDet H hH =
      ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1), LinearMap.det (D.diagramDivisionEnd H hH ℓ) :=
  (rfl)

theorem map_diagramCutoffDet {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    φ (D.diagramCutoffDet H hH) =
      D.diagramCutoffDet (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) := by
  simp [diagramCutoffDet_def, map_prod, map_det_diagramDivisionEnd]

/-- For an upward-closed monotone diagram `D`, the single finite-jet determinant product
`D.diagramCutoffDet H hH` is a unit in `A` if and only if `D.diagramSpanSet H ℓ` spans
`homogeneousSubmodule σ A ℓ` in *every* degree `ℓ : ℕ`. -/
theorem isUnit_diagramCutoffDet_iff_forall_span_eq {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    IsUnit (D.diagramCutoffDet H hH) ↔
      ∀ ℓ : ℕ, Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [diagramCutoffDet_def, IsUnit.prod_iff]
  refine ⟨fun h ℓ ↦ ?_, fun h ℓ _ ↦ (isUnit_det_diagramDivisionEnd_iff_span_eq hD_up hH).mpr (h ℓ)⟩
  by_cases hle : ℓ ≤ D.diagramCutoff
  · exact (isUnit_det_diagramDivisionEnd_iff_span_eq hD_up hH).mp
      (h ℓ (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)))
  · exact span_diagramSpanSet_eq_of_le hD_up hD_mono hH le_rfl
      ((isUnit_det_diagramDivisionEnd_iff_span_eq hD_up hH).mp
        (h D.diagramCutoff (Finset.mem_range.mpr (Nat.lt_succ_self _))))
      (Nat.le_of_not_ge hle)

/-- For an upward-closed monotone diagram `D`, `D.diagramCutoffDet H hH` is a unit in `A` if and
only if unique homogeneous supported division holds in *every* degree `ℓ : ℕ`. -/
theorem isUnit_diagramCutoffDet_iff_forall_existsUnique_division {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    IsUnit (D.diagramCutoffDet H hH) ↔
      ∀ ℓ : ℕ, ∀ G ∈ homogeneousSubmodule σ A ℓ,
        ∃! qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A,
          (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ}) ∧
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
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    (hunit : IsUnit (φ (D.diagramCutoffDet H hH))) (ℓ : ℕ)
    {G : MvPolynomial σ B} (hG : G ∈ homogeneousSubmodule σ B ℓ) :
    ∃! qr : (D.diagramVertices → MvPolynomial σ B) × MvPolynomial σ B,
      (∀ v, qr.1 v ∈ restrictSupport B {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ}) ∧
      qr.2 ∈ restrictSupport B {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
      ∑ v, qr.1 v * MvPolynomial.map φ (H v) + qr.2 = G := by
  rw [map_diagramCutoffDet] at hunit
  exact (isUnit_diagramCutoffDet_iff_forall_existsUnique_division hD_up hD_mono
    (fun v ↦ (hH v).map φ)).mp hunit ℓ G hG

end Set
