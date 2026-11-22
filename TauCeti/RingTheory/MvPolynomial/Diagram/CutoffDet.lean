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
the corresponding member of `D.diagramSpanSet H ℓ`. Over a commutative semiring with
`OrzechProperty A`, spanning, bijectivity, and unique homogeneous supported division in degree
`ℓ`—meaning a decomposition `∑ v, qr.1 v * H v + qr.2 = G` where each quotient `qr.1 v` is
supported in `D.diagramBox v.val` in the matching degree `v.val.degree + β.degree = ℓ` and the
homogeneous remainder `qr.2` is supported outside `D` in degree `ℓ`—are equivalent
(`Set.bijective_diagramDivisionEnd_iff_span_eq`,
`Set.existsUnique_homogeneous_division_iff_span_eq`). Over a commutative ring `A`, Cramer's rule
identifies these with invertibility of `LinearMap.det (D.diagramDivisionEnd H hH ℓ)`
(`Set.isUnit_det_diagramDivisionEnd_iff_span_eq`), and for monotone `D`,
`Set.span_diagramSpanSet_eq_of_le` shows they hold in *every* degree iff `D.diagramCutoffDet H hH`
is a unit (`Set.isUnit_diagramCutoffDet_iff_forall_span_eq`), which commutes with coefficient
homomorphisms (`Set.map_diagramCutoffDet`) and therefore persists after any homomorphism
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
      have hdeg : (s.val - h.choose.val).degree + h.choose.val.degree = ℓ := by
        rw [← map_add, tsub_add_cancel_of_le (le_of_mem_diagramCell h.choose_spec), s.property]
      ⟨monomial (s.val - h.choose.val) 1 * H h.choose, (mem_homogeneousSubmodule ℓ _).mpr <|
        hdeg ▸ (isHomogeneous_monomial 1 (by simp [Finsupp.degree_apply])).mul (hH h.choose)⟩
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
  have hnot : ¬ ∃ w : D.diagramVertices, s.val ∈ D.diagramCell w.val := fun ⟨w, hw⟩ ↦ hs w hw
  simp only [diagramDivisionEnd, Module.Basis.constr_basis, hnot, ↓reduceDIte]

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
  · rintro ⟨s, rfl⟩; by_cases hsD : s.val ∈ D
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
    · exact ⟨⟨γ, hdeg⟩, by rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem hD_up hH hγ,
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

private noncomputable instance fintypeDiagramBoxSubtype (D : Set (σ →₀ ℕ)) (v : D.diagramVertices)
    (ℓ : ℕ) : Fintype {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ} :=
  Fintype.ofInjective
    (fun β ↦ (⟨v.val + β.val, by rw [map_add, β.property.2]⟩ : {δ : σ →₀ ℕ // δ.degree = ℓ}))
    fun _ _ h ↦ Subtype.ext (add_left_cancel (congrArg Subtype.val h))

private noncomputable instance fintypeDiagramBoxElem (D : Set (σ →₀ ℕ)) (v : D.diagramVertices)
    (ℓ : ℕ) : Fintype ↥{β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ} :=
  fintypeDiagramBoxSubtype D v ℓ

private noncomputable instance fintypeDiagramRemSubtype (D : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    Fintype {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} :=
  Fintype.ofInjective (fun γ ↦ (⟨γ.val, γ.property.2⟩ : {δ : σ →₀ ℕ // δ.degree = ℓ}))
    fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)

private noncomputable instance fintypeDiagramRemElem (D : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    Fintype ↥{γ | γ ∉ D ∧ γ.degree = ℓ} := fintypeDiagramRemSubtype D ℓ

open scoped Classical in
private noncomputable def diagramIndexToFun {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ)
    (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) :
    ((v : D.diagramVertices) ×
      {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) ⊕
      {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} :=
  if hs : s.val ∈ D then
    let h := existsUnique_mem_diagramCell_of_mem hD_up hs
    Sum.inl ⟨h.choose, ⟨s.val - h.choose.val,
      tsub_mem_diagramBox_of_mem_diagramCell h.choose_spec.1, by rw [← map_add,
        add_tsub_cancel_of_le (le_of_mem_diagramCell h.choose_spec.1), s.property]⟩⟩
  else Sum.inr ⟨s.val, hs, s.property⟩

private noncomputable def diagramIndexInv {D : Set (σ →₀ ℕ)} {ℓ : ℕ} :
    ((v : D.diagramVertices) ×
      {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) ⊕
      {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} → {δ : σ →₀ ℕ // δ.degree = ℓ}
  | Sum.inl ⟨v, β⟩ => ⟨v.val + β.val, by rw [map_add, β.property.2]⟩
  | Sum.inr γ => ⟨γ.val, γ.property.2⟩

private theorem diagramIndexInv_injective {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ} :
    Function.Injective (diagramIndexInv (D := D) (ℓ := ℓ)) := by
  rintro (⟨v₁, β₁⟩ | γ₁) (⟨v₂, β₂⟩ | γ₂) h <;> dsimp [diagramIndexInv] at h <;>
    replace h := Subtype.mk.inj h
  · obtain rfl : v₁ = v₂ := Subtype.ext (eq_of_mem_diagramCell v₁.property v₂.property
      (add_mem_diagramCell_iff.mpr β₁.property.1) (h ▸ add_mem_diagramCell_iff.mpr β₂.property.1))
    exact congrArg (Sum.inl ∘ Sigma.mk v₁) (Subtype.ext (add_left_cancel h))
  · exact absurd (diagramCell_subset hD_up v₁.property (add_mem_diagramCell_iff.mpr β₁.property.1))
      (h ▸ γ₂.property.1)
  · exact absurd (diagramCell_subset hD_up v₂.property (add_mem_diagramCell_iff.mpr β₂.property.1))
      (h ▸ γ₁.property.1)
  · exact congrArg Sum.inr (Subtype.ext h)

private theorem diagramIndexInv_toFun {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ)
    (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) : diagramIndexInv (diagramIndexToFun hD_up ℓ s) = s := by
  classical
  by_cases hs : s.val ∈ D <;> simp only [diagramIndexToFun, hs, ↓reduceDIte, diagramIndexInv]
  exact Subtype.ext (add_tsub_cancel_of_le
    (le_of_mem_diagramCell (existsUnique_mem_diagramCell_of_mem hD_up hs).choose_spec.1))

/-- Canonical equivalence reindexing degree-`ℓ` exponent vectors by the supported quotient boxes
`D.diagramBox v.val` (`v ∈ D.diagramVertices`) and the degree-`ℓ` complement outside `D`. -/
noncomputable def diagramIndexEquiv {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ) :
    {δ : σ →₀ ℕ // δ.degree = ℓ} ≃
      ((v : D.diagramVertices) ×
        {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) ⊕
        {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} where
  toFun := diagramIndexToFun hD_up ℓ
  invFun := diagramIndexInv
  left_inv := diagramIndexInv_toFun hD_up ℓ
  right_inv _ := diagramIndexInv_injective hD_up (diagramIndexInv_toFun hD_up ℓ _)

/-- The inverse of `Set.diagramIndexEquiv` sends a supported quotient index `(v, β)` to
`v + β`. -/
@[simp] theorem diagramIndexEquiv_symm_inl {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ)
    (v : D.diagramVertices)
    (β : {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) :
    (D.diagramIndexEquiv hD_up ℓ).symm (Sum.inl ⟨v, β⟩) =
      ⟨v.val + β.val, by rw [map_add, β.property.2]⟩ := by rfl

/-- The inverse of `Set.diagramIndexEquiv` sends a remainder index `γ ∉ D` to `γ`. -/
@[simp] theorem diagramIndexEquiv_symm_inr {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ)
    (γ : {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ}) :
    (D.diagramIndexEquiv hD_up ℓ).symm (Sum.inr γ) = ⟨γ.val, γ.property.2⟩ := by rfl

open Classical in
private noncomputable def diagramQREquiv {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ) :
    homogeneousSubmodule σ A ℓ ≃
      ((v : D.diagramVertices) →
        restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ×
        restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} where
  toFun P :=
    (fun v ↦ (basisRestrictSupport A _).repr.symm (Finsupp.equivFunOnFinite.symm fun β ↦
      P.val.coeff ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inl ⟨v, β⟩)).val),
     (basisRestrictSupport A _).repr.symm (Finsupp.equivFunOnFinite.symm fun γ ↦
      P.val.coeff ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inr γ)).val))
  invFun qr :=
    (TauCeti.homogeneousMonomialBasis ℓ).repr.symm (Finsupp.equivFunOnFinite.symm fun s ↦
      match D.diagramIndexEquiv hD_up ℓ s with
      | Sum.inl ⟨v, β⟩ => (qr.1 v : MvPolynomial σ A).coeff β.val
      | Sum.inr γ => (qr.2 : MvPolynomial σ A).coeff γ.val)
  left_inv P := (TauCeti.homogeneousMonomialBasis ℓ).repr.injective <| Finsupp.ext fun s ↦ by
    simp only [TauCeti.homogeneousMonomialBasis_repr_apply, LinearEquiv.apply_symm_apply,
      Finsupp.coe_equivFunOnFinite_symm]
    rcases h : D.diagramIndexEquiv hD_up ℓ s with ⟨v, β⟩ | γ <;>
    · dsimp only; rw [← basisRestrictSupport_repr_apply, LinearEquiv.apply_symm_apply,
        Finsupp.coe_equivFunOnFinite_symm, ← h, (D.diagramIndexEquiv hD_up ℓ).symm_apply_apply]
  right_inv qr := by
    refine Prod.ext
      (funext fun v ↦ (basisRestrictSupport A _).repr.injective (Finsupp.ext fun β ↦ ?_))
      ((basisRestrictSupport A _).repr.injective (Finsupp.ext fun γ ↦ ?_)) <;>
    simp only [LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm,
      basisRestrictSupport_repr_apply, ← TauCeti.homogeneousMonomialBasis_repr_apply,
      (D.diagramIndexEquiv hD_up ℓ).apply_symm_apply]

private theorem coe_diagramDivisionEnd_eq_diagramQREquiv {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramDivisionEnd H hH ℓ P : MvPolynomial σ A) =
      ∑ v, ((diagramQREquiv hD_up ℓ P).1 v : MvPolynomial σ A) * H v +
        ((diagramQREquiv hD_up ℓ P).2 : MvPolynomial σ A) := by
  classical
  let e := D.diagramIndexEquiv hD_up ℓ
  conv_lhs => rw [← (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).sum_repr P,
    map_sum, Submodule.coe_sum]
  simp_rw [map_smul, SetLike.val_smul, TauCeti.homogeneousMonomialBasis_repr_apply]
  rw [← Equiv.sum_comp e.symm, Fintype.sum_sum_type, Fintype.sum_sigma]; congr 1
  · refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hsum := congrArg Subtype.val
      ((basisRestrictSupport A _).sum_repr ((diagramQREquiv hD_up ℓ P).1 v))
    rw [Submodule.coe_sum] at hsum; conv_rhs => rw [← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    simp only [e, diagramIndexEquiv_symm_inl, SetLike.val_smul, basisRestrictSupport_apply_coe,
      diagramQREquiv, Equiv.coe_fn_mk, LinearEquiv.apply_symm_apply,
      Finsupp.coe_equivFunOnFinite_symm, smul_monomial, smul_eq_mul, mul_one]
    rw [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v
      (s := ⟨v.val + β.val, by rw [map_add, β.property.2]⟩)
      (add_mem_diagramCell_iff.mpr β.property.1),
      add_tsub_cancel_left, ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  · have hsum := congrArg Subtype.val
      ((basisRestrictSupport A _).sum_repr (diagramQREquiv hD_up ℓ P).2)
    rw [Submodule.coe_sum] at hsum; conv_rhs => rw [← hsum]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    simp only [e, diagramIndexEquiv_symm_inr, SetLike.val_smul, basisRestrictSupport_apply_coe,
      diagramQREquiv, Equiv.coe_fn_mk, LinearEquiv.apply_symm_apply,
      Finsupp.coe_equivFunOnFinite_symm, smul_monomial, smul_eq_mul, mul_one]
    rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem hD_up hH
      (s := ⟨γ.val, γ.property.2⟩) γ.property.1,
      TauCeti.coe_homogeneousMonomialBasis, smul_monomial, smul_eq_mul, mul_one]

/-- `diagramDivisionEnd` commutes with changing coefficients along any ring homomorphism
`φ : A →+* B`. -/
theorem mapHomogeneousSubmodule_diagramDivisionEnd {B : Type*} [CommSemiring B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) (ℓ : ℕ) (P : homogeneousSubmodule σ A ℓ) :
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
    simp [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell _ v hv]
  · simp [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell _
      fun _ hv ↦ hex ⟨_, hv⟩]

end CommSemiring

section Orzech

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommSemiring A] [OrzechProperty A]

/-- For an upward-closed diagram `D` over a commutative semiring with `OrzechProperty A`,
`D.diagramDivisionEnd H hH ℓ` is bijective if and only if `D.diagramSpanSet H ℓ` spans
`homogeneousSubmodule σ A ℓ`. -/
theorem bijective_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ} :
    Function.Bijective (D.diagramDivisionEnd H hH ℓ) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  ⟨fun h ↦ (surjective_diagramDivisionEnd_iff_span_eq hD_up hH).mp h.2, fun h ↦
    OrzechProperty.bijective_of_surjective_endomorphism _
      ((surjective_diagramDivisionEnd_iff_span_eq hD_up hH).mpr h)⟩

/-- For an upward-closed diagram `D` over a commutative semiring with `OrzechProperty A`, spanning
in degree `ℓ` is equivalent to unique homogeneous supported division in degree `ℓ`. -/
theorem existsUnique_homogeneous_division_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ} :
    (∀ G ∈ homogeneousSubmodule σ A ℓ,
      ∃! qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A,
        (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ∧
        qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
        ∑ v, qr.1 v * H v + qr.2 = G) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← bijective_diagramDivisionEnd_iff_span_eq hD_up hH, Function.bijective_iff_existsUnique]
  let e : homogeneousSubmodule σ A ℓ ≃
      {qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A //
        (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ∧
        qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ}} := (diagramQREquiv hD_up ℓ).trans
      { toFun := fun qr ↦ ⟨(fun v ↦ (qr.1 v : MvPolynomial σ A), (qr.2 : MvPolynomial σ A)),
          fun v ↦ (qr.1 v).property, qr.2.property⟩
        invFun := fun qr ↦ (fun v ↦ ⟨qr.val.1 v, qr.property.1 v⟩, ⟨qr.val.2, qr.property.2⟩)
        left_inv _ := rfl, right_inv _ := rfl }
  have hdiv (P : homogeneousSubmodule σ A ℓ) : ∑ v, (e P).val.1 v * H v + (e P).val.2 =
      (D.diagramDivisionEnd H hH ℓ P : MvPolynomial σ A) :=
    (coe_diagramDivisionEnd_eq_diagramQREquiv hD_up hH P).symm
  refine ⟨fun h G ↦ ?_, fun h G hG ↦ ?_⟩
  · obtain ⟨qr, ⟨hQ, hR, hsum⟩, huniq⟩ := h G.val G.property
    refine ⟨e.symm ⟨qr, hQ, hR⟩, Subtype.ext (by simpa [← hdiv] using hsum), fun P hP ↦
      e.injective (Subtype.ext (by rw [e.apply_symm_apply]; exact huniq _ ⟨(e P).property.1,
        (e P).property.2, by rw [hdiv, hP]⟩))⟩
  · obtain ⟨P, hP, huniq⟩ := h ⟨G, hG⟩
    refine ⟨(e P).val, ⟨(e P).property.1, (e P).property.2, by rw [hdiv, hP]⟩,
      fun qr ⟨hQ, hR, hsum⟩ ↦ congrArg Subtype.val (e.symm_apply_eq.mp
        (huniq (e.symm ⟨qr, hQ, hR⟩) (Subtype.ext (by rw [← hdiv, e.apply_symm_apply, hsum]))))⟩

end Orzech

section CommRing

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommRing A]

/-- For an upward-closed diagram `D` over a commutative ring `A`, the determinant of
`D.diagramDivisionEnd H hH ℓ` is a unit in `A` if and only if `D.diagramSpanSet H ℓ` spans
`homogeneousSubmodule σ A ℓ`. -/
theorem isUnit_det_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ} :
    IsUnit (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff,
    bijective_diagramDivisionEnd_iff_span_eq hD_up hH]

/-- Changing coefficients along `φ : A →+* B` maps the block determinant of
`D.diagramDivisionEnd H hH ℓ` to the block determinant of `MvPolynomial.map φ ∘ H`. -/
theorem map_det_diagramDivisionEnd {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) (ℓ : ℕ) :
    φ (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) = LinearMap.det
      (D.diagramDivisionEnd (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) ℓ) := by
  classical
  let bA := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  rw [← LinearMap.det_toMatrix bA,
    ← LinearMap.det_toMatrix (TauCeti.homogeneousMonomialBasis (σ := σ) (R := B) ℓ),
    RingHom.map_det]
  congr 1; ext s t
  simpa [bA, LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    TauCeti.coe_mapHomogeneousSubmodule_apply, coeff_map,
    TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis] using
    congrArg (fun x : homogeneousSubmodule σ B ℓ ↦ x.val.coeff s.val)
      (mapHomogeneousSubmodule_diagramDivisionEnd φ hH ℓ (bA t))

/-- The finite-jet determinant product across degrees `ℓ ≤ D.diagramCutoff` controlling
homogeneous supported division in *all* degrees for a monotone upward-closed diagram `D`
(Bierstone–Milman, p. 282). -/
noncomputable def diagramCutoffDet (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.val.degree) : A :=
  ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1), LinearMap.det (D.diagramDivisionEnd H hH ℓ)

/-- For the empty diagram `D = ∅`, `diagramCutoffDet` equals `1`. -/
@[simp] theorem diagramCutoffDet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    (∅ : Set (σ →₀ ℕ)).diagramCutoffDet H hH = 1 := by simp [diagramCutoffDet]

/-- For `D = Set.univ`, `diagramCutoffDet` equals the constant coefficient of `H ⟨0, _⟩`. -/
@[simp] theorem diagramCutoffDet_univ
    (H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    (Set.univ : Set (σ →₀ ℕ)).diagramCutoffDet H hH = constantCoeff (H ⟨0, by simp⟩) := by
  have hprod : (Set.univ : Set (σ →₀ ℕ)).diagramCutoffDet H hH =
      LinearMap.det ((Set.univ : Set (σ →₀ ℕ)).diagramDivisionEnd H hH 0) := by
    rw [diagramCutoffDet, diagramCutoff_univ, Finset.range_one, Finset.prod_singleton]
  let : Unique {δ : σ →₀ ℕ // δ.degree = 0} :=
    ⟨⟨0, by simp⟩, fun s ↦ Subtype.ext (by simpa [Finsupp.degree_eq_zero_iff] using s.property)⟩
  rw [hprod, ← LinearMap.det_toMatrix (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) 0),
    Matrix.det_unique, LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    show (default : {δ : σ →₀ ℕ // δ.degree = 0}) = ⟨0, by simp⟩ from rfl,
    coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH
      (ℓ := 0) (v := ⟨0, by simp⟩) (s := ⟨0, by simp⟩) (by simp)]
  simp [constantCoeff_eq]

/-- Applying a ring homomorphism `φ : A →+* B` to `D.diagramCutoffDet H hH` gives the cutoff
determinant product of the coefficient-mapped family `MvPolynomial.map φ ∘ H` over the same
diagram `D`. -/
theorem map_diagramCutoffDet {B : Type*} [CommRing B] (φ : A →+* B) {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    φ (D.diagramCutoffDet H hH) =
      D.diagramCutoffDet (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) := by
  simp [diagramCutoffDet, map_prod, map_det_diagramDivisionEnd]

/-- For an upward-closed monotone diagram `D`, the single finite-jet determinant product
`D.diagramCutoffDet H hH` is a unit in `A` if and only if `D.diagramSpanSet H ℓ` spans
`homogeneousSubmodule σ A ℓ` in *every* degree `ℓ : ℕ`. -/
theorem isUnit_diagramCutoffDet_iff_forall_span_eq {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    IsUnit (D.diagramCutoffDet H hH) ↔
      ∀ ℓ : ℕ, Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  have hiff (ℓ : ℕ) := isUnit_det_diagramDivisionEnd_iff_span_eq (ℓ := ℓ) hD_up hH
  rw [diagramCutoffDet, IsUnit.prod_iff]; refine ⟨fun h ℓ ↦ ?_, fun h ℓ _ ↦ (hiff ℓ).mpr (h ℓ)⟩
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
    IsUnit (D.diagramCutoffDet H hH) ↔ ∀ ℓ : ℕ, ∀ G ∈ homogeneousSubmodule σ A ℓ,
      ∃! qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A,
        (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ∧
        qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} ∧ ∑ v, qr.1 v * H v + qr.2 = G := by
  rw [isUnit_diagramCutoffDet_iff_forall_span_eq hD_up hD_mono hH]
  exact forall_congr' fun ℓ ↦ (existsUnique_homogeneous_division_iff_span_eq hD_up hH).symm

/-- For an upward-closed monotone diagram `D`, after any ring homomorphism `φ : A →+* B` (such as
`algebraMap A (Localization.Away _)`) that inverts `D.diagramCutoffDet H hH`, unique homogeneous
supported division for `MvPolynomial.map φ ∘ H` holds in *every* degree `ℓ : ℕ`
(Bierstone–Milman, p. 282). -/
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
