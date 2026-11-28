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
    (ℓ : ℕ) : homogeneousSubmodule σ A ℓ →ₗ[A] homogeneousSubmodule σ A ℓ :=
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
  (TauCeti.homogeneousMonomialBasis ℓ).ext fun s ↦ by
    simpa using diagramDivisionEnd_homogeneousMonomialBasis_of_notMem isUpperSet_empty hH
      (s := s) (notMem_empty _)

private noncomputable instance fintypeDiagramBoxElem (D : Set (σ →₀ ℕ)) (v : D.diagramVertices)
    (ℓ : ℕ) : Fintype ↥{β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ} :=
  Fintype.ofFinite _

private noncomputable instance fintypeDiagramRemElem (D : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    Fintype ↥{γ | γ ∉ D ∧ γ.degree = ℓ} :=
  Fintype.ofFinite _

private noncomputable def diagramIndexEquivInvFun (D : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    ((v : D.diagramVertices) ×
      {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) ⊕
      {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} →
    {δ : σ →₀ ℕ // δ.degree = ℓ}
  | Sum.inl ⟨v, β⟩ => ⟨v.val + β.val, by rw [map_add, β.property.2]⟩
  | Sum.inr γ => ⟨γ.val, γ.property.2⟩

private theorem injective_diagramIndexEquivInvFun {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    (ℓ : ℕ) : Function.Injective (diagramIndexEquivInvFun D ℓ) := by
  rintro (⟨v₁, β₁⟩ | γ₁) (⟨v₂, β₂⟩ | γ₂) h <;> dsimp [diagramIndexEquivInvFun] at h <;>
    replace h := Subtype.mk.inj h
  · obtain rfl : v₁ = v₂ := Subtype.ext (eq_of_mem_diagramCell v₁.property v₂.property
      (add_mem_diagramCell_iff.mpr β₁.property.1) (h ▸ add_mem_diagramCell_iff.mpr β₂.property.1))
    exact congrArg (Sum.inl ∘ Sigma.mk v₁) (Subtype.ext (add_left_cancel h))
  · exact absurd (diagramCell_subset hD_up v₁.property
      (add_mem_diagramCell_iff.mpr β₁.property.1)) (h ▸ γ₂.property.1)
  · exact absurd (diagramCell_subset hD_up v₂.property
      (add_mem_diagramCell_iff.mpr β₂.property.1)) (h ▸ γ₁.property.1)
  · exact congrArg Sum.inr (Subtype.ext h)

open scoped Classical in
/-- Canonical equivalence reindexing degree-`ℓ` exponent vectors by the supported quotient boxes
`D.diagramBox v.val` (`v ∈ D.diagramVertices`) and the degree-`ℓ` complement outside `D`. -/
noncomputable def diagramIndexEquiv {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ) :
    {δ : σ →₀ ℕ // δ.degree = ℓ} ≃
      ((v : D.diagramVertices) ×
        {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) ⊕
        {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} :=
  let toFun (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) :
      ((v : D.diagramVertices) ×
        {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) ⊕
        {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} :=
    if hs : s.val ∈ D then let h := existsUnique_mem_diagramCell_of_mem hD_up hs
      Sum.inl ⟨h.choose, ⟨s.val - h.choose.val, tsub_mem_diagramBox_of_mem_diagramCell
        h.choose_spec.1, by rw [← map_add, add_tsub_cancel_of_le
          (le_of_mem_diagramCell h.choose_spec.1), s.property]⟩⟩
    else Sum.inr ⟨s.val, hs, s.property⟩
  have hleft (s) : diagramIndexEquivInvFun D ℓ (toFun s) = s := by
    by_cases hs : s.val ∈ D <;> simp only [toFun, hs, ↓reduceDIte, diagramIndexEquivInvFun]
    exact Subtype.ext (add_tsub_cancel_of_le
      (le_of_mem_diagramCell (existsUnique_mem_diagramCell_of_mem hD_up hs).choose_spec.1))
  ⟨toFun, diagramIndexEquivInvFun D ℓ, hleft,
    fun _ ↦ injective_diagramIndexEquivInvFun hD_up ℓ (hleft _)⟩

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

/-- For a degree-`ℓ` exponent `s` in the cell of `v`, `Set.diagramIndexEquiv` maps `s` to the
quotient index `(v, s - v)`. (Not `@[simp]` because `v` cannot be inferred from the LHS.) -/
theorem diagramIndexEquiv_of_mem_diagramCell {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    (ℓ : ℕ) {v : D.diagramVertices} {s : {δ : σ →₀ ℕ // δ.degree = ℓ}}
    (hs : s.val ∈ D.diagramCell v.val) :
    D.diagramIndexEquiv hD_up ℓ s = Sum.inl ⟨v, ⟨s.val - v.val,
      tsub_mem_diagramBox_of_mem_diagramCell hs, by
        rw [← map_add, add_tsub_cancel_of_le (le_of_mem_diagramCell hs), s.property]⟩⟩ :=
  ((D.diagramIndexEquiv hD_up ℓ).eq_symm_apply).mp <|
    Subtype.ext (add_tsub_cancel_of_le (le_of_mem_diagramCell hs)).symm

/-- For `β ∈ D.diagramBox v.val` with `(v.val + β).degree = ℓ`, `Set.diagramIndexEquiv` maps
`v.val + β` to `Sum.inl ⟨v, β⟩`. -/
@[simp] theorem diagramIndexEquiv_add {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ)
    (v : D.diagramVertices) {β : σ →₀ ℕ} (hβ : β ∈ D.diagramBox v.val)
    (hdeg : (v.val + β).degree = ℓ) :
    D.diagramIndexEquiv hD_up ℓ ⟨v.val + β, hdeg⟩ =
      Sum.inl ⟨v, ⟨β, hβ, by simpa [map_add] using hdeg⟩⟩ :=
  ((D.diagramIndexEquiv hD_up ℓ).eq_symm_apply).mp rfl

/-- For a degree-`ℓ` exponent `s` outside `D`, `Set.diagramIndexEquiv` maps `s` to the remainder
index `s`. -/
@[simp] theorem diagramIndexEquiv_of_notMem {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    (ℓ : ℕ) {s : {δ : σ →₀ ℕ // δ.degree = ℓ}} (hs : s.val ∉ D) :
    D.diagramIndexEquiv hD_up ℓ s = Sum.inr ⟨s.val, hs, s.property⟩ :=
  ((D.diagramIndexEquiv hD_up ℓ).eq_symm_apply).mp rfl

/-- Polynomial image of `D.diagramDivisionEnd H hH ℓ` on a `diagramIndexEquiv` supported quotient
basis vector `(v, β)`: `monomial β.val 1 * H v`. -/
theorem coe_diagramDivisionEnd_diagramIndexEquiv_symm_inl {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ} (v : D.diagramVertices)
    (β : {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) :
    (D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ
      ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inl ⟨v, β⟩))) : MvPolynomial σ A) =
      monomial β.val 1 * H v := by
  rw [diagramIndexEquiv_symm_inl,
    coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v
      (add_mem_diagramCell_iff.mpr β.property.1), add_tsub_cancel_left]

/-- Basis image of `D.diagramDivisionEnd H hH ℓ` on a `diagramIndexEquiv` remainder basis vector
`γ ∉ D`. -/
theorem diagramDivisionEnd_diagramIndexEquiv_symm_inr {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ}
    (γ : {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ}) :
    D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ
      ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inr γ))) =
      TauCeti.homogeneousMonomialBasis ℓ ⟨γ.val, γ.property.2⟩ := by
  rw [diagramIndexEquiv_symm_inr,
    diagramDivisionEnd_homogeneousMonomialBasis_of_notMem hD_up hH γ.property.1]

/-- Polynomial image of `D.diagramDivisionEnd H hH ℓ` on a `diagramIndexEquiv` remainder basis
vector `γ ∉ D`: `monomial γ.val 1`. -/
theorem coe_diagramDivisionEnd_diagramIndexEquiv_symm_inr {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ}
    (γ : {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ}) :
    (D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ
      ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inr γ))) : MvPolynomial σ A) =
      monomial γ.val 1 := by
  rw [diagramDivisionEnd_diagramIndexEquiv_symm_inr, TauCeti.coe_homogeneousMonomialBasis]

open scoped Classical in
/-- Monomial-row and `diagramIndexEquiv`-column coefficient of `D.diagramDivisionEnd H hH ℓ` on a
supported quotient column `(v, β)`: `(H v).coeff (s - β)` when `β ≤ s`, and `0` otherwise. -/
theorem coeff_diagramDivisionEnd_symm_inl {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} (s : σ →₀ ℕ) (v : D.diagramVertices)
    (β : {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) :
    (D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ
      ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inl ⟨v, β⟩))) : MvPolynomial σ A).coeff s =
      if β.val ≤ s then (H v).coeff (s - β.val) else 0 := by
  rw [coe_diagramDivisionEnd_diagramIndexEquiv_symm_inl, coeff_monomial_mul', one_mul]

/-- Monomial-row and `diagramIndexEquiv`-column coefficient of `D.diagramDivisionEnd H hH ℓ` on a
remainder column `γ ∉ D`: `1` if `γ = s` and `0` otherwise. -/
theorem coeff_diagramDivisionEnd_symm_inr {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} (s : σ →₀ ℕ) (γ : {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ}) :
    (D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ
      ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inr γ))) : MvPolynomial σ A).coeff s =
      if γ.val = s then 1 else 0 := by
  rw [coe_diagramDivisionEnd_diagramIndexEquiv_symm_inr, coeff_monomial]

open scoped Classical in
/-- Matrix entry of `D.diagramDivisionEnd H hH ℓ` in the monomial basis at row `s` and supported
quotient column `(v, β)`: `(H v).coeff (s - β)` when `β ≤ s`, and `0` otherwise. -/
theorem toMatrix_diagramDivisionEnd_symm_inl [Fintype {δ : σ →₀ ℕ // δ.degree = ℓ}]
    {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (v : D.diagramVertices)
    (β : {β : σ →₀ ℕ // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ}) :
    LinearMap.toMatrix (TauCeti.homogeneousMonomialBasis ℓ)
        (TauCeti.homogeneousMonomialBasis ℓ) (D.diagramDivisionEnd H hH ℓ) s
        ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inl ⟨v, β⟩)) =
      if β.val ≤ s.val then (H v).coeff (s.val - β.val) else 0 := by
  rw [LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    coeff_diagramDivisionEnd_symm_inl]

/-- Matrix entry of `D.diagramDivisionEnd H hH ℓ` in the monomial basis at row `s` and any
column `t` outside `D`: `1` if `t.val = s.val` and `0` otherwise. -/
theorem toMatrix_diagramDivisionEnd_of_notMem [Fintype {δ : σ →₀ ℕ // δ.degree = ℓ}]
    {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (s t : {δ : σ →₀ ℕ // δ.degree = ℓ}) (ht : t.val ∉ D) :
    LinearMap.toMatrix (TauCeti.homogeneousMonomialBasis ℓ)
        (TauCeti.homogeneousMonomialBasis ℓ) (D.diagramDivisionEnd H hH ℓ) s t =
      if t.val = s.val then 1 else 0 := by
  rw [LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    diagramDivisionEnd_homogeneousMonomialBasis_of_notMem hD_up hH ht,
    TauCeti.coe_homogeneousMonomialBasis, coeff_monomial]

/-- Matrix entry of `D.diagramDivisionEnd H hH ℓ` in the monomial basis at row `s` and remainder
column `γ ∉ D`: `1` if `γ = s` and `0` otherwise. -/
theorem toMatrix_diagramDivisionEnd_symm_inr [Fintype {δ : σ →₀ ℕ // δ.degree = ℓ}]
    {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (γ : {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ}) :
    LinearMap.toMatrix (TauCeti.homogeneousMonomialBasis ℓ)
        (TauCeti.homogeneousMonomialBasis ℓ) (D.diagramDivisionEnd H hH ℓ) s
        ((D.diagramIndexEquiv hD_up ℓ).symm (Sum.inr γ)) =
      if γ.val = s.val then 1 else 0 := by
  rw [LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    coeff_diagramDivisionEnd_symm_inr]

/-- The square restriction of the matrix of `D.diagramDivisionEnd H hH ℓ` (in the homogeneous
monomial basis) to degree-`ℓ` exponents lying in `D`. -/
noncomputable def diagramDivisionMatrix (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (ℓ : ℕ) :
    Matrix {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ} {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ} A :=
  fun s t ↦ (D.diagramDivisionEnd H hH ℓ
    (TauCeti.homogeneousMonomialBasis ℓ ⟨t.val, t.property.2⟩) : MvPolynomial σ A).coeff s.val

/-- Entry formula for `Set.diagramDivisionMatrix`. -/
theorem diagramDivisionMatrix_apply (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (ℓ : ℕ) (s t : {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ}) :
    D.diagramDivisionMatrix H hH ℓ s t =
      (D.diagramDivisionEnd H hH ℓ
        (TauCeti.homogeneousMonomialBasis ℓ ⟨t.val, t.property.2⟩) : MvPolynomial σ A).coeff
        s.val := by rw [diagramDivisionMatrix]

/-- `Set.diagramDivisionMatrix` is the principal submatrix of
`LinearMap.toMatrix (homogeneousMonomialBasis ℓ) (homogeneousMonomialBasis ℓ) (diagramDivisionEnd)`
on degree-`ℓ` exponents in `D`. -/
theorem diagramDivisionMatrix_eq_submatrix (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (ℓ : ℕ) [Fintype {δ : σ →₀ ℕ // δ.degree = ℓ}] :
    D.diagramDivisionMatrix H hH ℓ =
      (LinearMap.toMatrix (TauCeti.homogeneousMonomialBasis ℓ)
        (TauCeti.homogeneousMonomialBasis ℓ) (D.diagramDivisionEnd H hH ℓ)).submatrix
        (fun s ↦ ⟨s.val, s.property.2⟩) (fun t ↦ ⟨t.val, t.property.2⟩) := by
  ext s t
  simp [diagramDivisionMatrix, LinearMap.toMatrix_apply,
    TauCeti.homogeneousMonomialBasis_repr_apply]

open scoped Classical in
/-- Entry formula for `Set.diagramDivisionMatrix` when column `t` lies in `D.diagramCell v.val`. -/
theorem diagramDivisionMatrix_of_mem_diagramCell {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} (s t : {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ}) (v : D.diagramVertices)
    (ht : t.val ∈ D.diagramCell v.val) :
    D.diagramDivisionMatrix H hH ℓ s t =
      if t.val - v.val ≤ s.val then (H v).coeff (s.val - (t.val - v.val)) else 0 := by
  rw [diagramDivisionMatrix_apply,
    coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v ht,
    coeff_monomial_mul', one_mul]

/-- For an upward-closed diagram `D`, the image of `D.diagramDivisionEnd H hH ℓ` inside
`MvPolynomial σ A` is `Submodule.span A (D.diagramSpanSet H ℓ)`. -/
theorem map_range_diagramDivisionEnd_eq_span {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (ℓ : ℕ) :
    (LinearMap.range (D.diagramDivisionEnd H hH ℓ)).map (homogeneousSubmodule σ A ℓ).subtype =
      Submodule.span A (D.diagramSpanSet H ℓ) := by
  let b := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  rw [← LinearMap.range_comp, LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span,
    ← Set.range_comp, ← (D.diagramIndexEquiv hD_up ℓ).symm.surjective.range_comp]
  refine congrArg (Submodule.span A) (Set.ext fun p ↦ ?_)
  simp only [mem_range, Function.comp_apply, LinearMap.coe_comp, Submodule.coe_subtype,
    mem_diagramSpanSet_iff]
  refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun h ↦ h.elim
    (fun ⟨v, β, hβ, hdeg, hp⟩ ↦ ⟨Sum.inl ⟨v, ⟨β, hβ, hdeg⟩⟩, by
      rw [coe_diagramDivisionEnd_diagramIndexEquiv_symm_inl, ← hp]⟩)
    (fun ⟨γ, hγ, hdeg, hp⟩ ↦ ⟨Sum.inr ⟨γ, hγ, hdeg⟩, by
      rw [coe_diagramDivisionEnd_diagramIndexEquiv_symm_inr, ← hp]⟩)⟩
  rcases i with ⟨v, β⟩ | γ
  · rw [coe_diagramDivisionEnd_diagramIndexEquiv_symm_inl] at hi
    exact Or.inl ⟨v, β.val, β.property.1, β.property.2, hi.symm⟩
  · rw [coe_diagramDivisionEnd_diagramIndexEquiv_symm_inr] at hi
    exact Or.inr ⟨γ.val, γ.property.1, γ.property.2, hi.symm⟩

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

/-- The `A`-linear equivalence splitting `homogeneousSubmodule σ A ℓ` into supported quotient
components in `D.diagramBox v.val` (`v ∈ D.diagramVertices`) and a remainder supported outside `D`,
via `Set.diagramIndexEquiv`. -/
noncomputable def diagramQREquiv {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (ℓ : ℕ) :
    homogeneousSubmodule σ A ℓ ≃ₗ[A]
      ((v : D.diagramVertices) →
        restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ×
        restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} :=
  (TauCeti.homogeneousMonomialBasis ℓ).equivFun.trans <|
    (LinearEquiv.piCongrLeft' A (fun _ ↦ A) (D.diagramIndexEquiv hD_up ℓ)).trans <|
    (LinearEquiv.sumArrowLequivProdArrow _ _ A A).trans <|
    LinearEquiv.prodCongr
      ((LinearEquiv.piCurry A (fun _ _ ↦ A)).trans (LinearEquiv.piCongrRight fun v ↦
        (basisRestrictSupport A
          {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}).equivFun.symm))
      (basisRestrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ}).equivFun.symm

/-- Each quotient component of `Set.diagramQREquiv` reads off the coefficient at `v.val + β.val`. -/
@[simp] theorem coeff_diagramQREquiv_fst {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) (v : D.diagramVertices)
    (β : ↥{β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) :
    ((D.diagramQREquiv hD_up ℓ P).1 v : MvPolynomial σ A).coeff β.val =
      (P : MvPolynomial σ A).coeff (v.val + β.val) := by
  rw [← basisRestrictSupport_repr_apply, ← Module.Basis.equivFun_apply]
  simp [diagramQREquiv, Sigma.curry, LinearEquiv.piCongrLeft'_apply,
    TauCeti.homogeneousMonomialBasis_repr_apply, Finsupp.single_apply]

/-- The remainder component of `Set.diagramQREquiv` reads off the coefficient at `γ.val`. -/
@[simp] theorem coeff_diagramQREquiv_snd {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) (γ : ↥{γ | γ ∉ D ∧ γ.degree = ℓ}) :
    ((D.diagramQREquiv hD_up ℓ P).2 : MvPolynomial σ A).coeff γ.val =
      (P : MvPolynomial σ A).coeff γ.val := by
  rw [← basisRestrictSupport_repr_apply, ← Module.Basis.equivFun_apply]
  simp [diagramQREquiv, LinearEquiv.piCongrLeft'_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    Finsupp.single_apply]

/-- The inverse of `Set.diagramQREquiv` recovers the coefficient at `v.val + β.val` from the
`v`-quotient component at `β.val`. -/
@[simp] theorem coeff_diagramQREquiv_symm_fst {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    (qr : ((v : D.diagramVertices) →
      restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ×
      restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ})
    (v : D.diagramVertices) (β : ↥{β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) :
    (((D.diagramQREquiv hD_up ℓ).symm qr : homogeneousSubmodule σ A ℓ) : MvPolynomial σ A).coeff
        (v.val + β.val) =
      (qr.1 v : MvPolynomial σ A).coeff β.val := by
  simpa using (coeff_diagramQREquiv_fst hD_up ((D.diagramQREquiv hD_up ℓ).symm qr) v β).symm

/-- The inverse of `Set.diagramQREquiv` recovers the coefficient at a complement exponent `γ.val`
from the remainder component. -/
@[simp] theorem coeff_diagramQREquiv_symm_snd {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    (qr : ((v : D.diagramVertices) →
      restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}) ×
      restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ})
    (γ : ↥{γ | γ ∉ D ∧ γ.degree = ℓ}) :
    (((D.diagramQREquiv hD_up ℓ).symm qr : homogeneousSubmodule σ A ℓ) : MvPolynomial σ A).coeff
        γ.val =
      (qr.2 : MvPolynomial σ A).coeff γ.val := by
  simpa using (coeff_diagramQREquiv_snd hD_up ((D.diagramQREquiv hD_up ℓ).symm qr) γ).symm

/-- Assembly formula for `Set.diagramDivisionEnd`: applying `D.diagramDivisionEnd H hH ℓ` to `P`
combines the quotient components of `D.diagramQREquiv hD_up ℓ P` against `H` plus its remainder. -/
theorem coe_diagramDivisionEnd_eq_diagramQREquiv {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramDivisionEnd H hH ℓ P : MvPolynomial σ A) =
      ∑ v, ((D.diagramQREquiv hD_up ℓ P).1 v : MvPolynomial σ A) * H v +
        ((D.diagramQREquiv hD_up ℓ P).2 : MvPolynomial σ A) := by
  classical
  let (v : D.diagramVertices) :
      Fintype {β // β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ} :=
    D.fintypeDiagramBoxElem v ℓ
  let : Fintype {γ // γ ∉ D ∧ γ.degree = ℓ} := D.fintypeDiagramRemElem ℓ
  conv_lhs => rw [← (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).sum_repr P,
    map_sum, Submodule.coe_sum]
  simp_rw [map_smul, SetLike.val_smul, TauCeti.homogeneousMonomialBasis_repr_apply]
  rw [← Equiv.sum_comp (D.diagramIndexEquiv hD_up ℓ).symm, Fintype.sum_sum_type, Fintype.sum_sigma]
  refine congr_arg₂ (· + ·) (Finset.sum_congr rfl fun v _ ↦ ?_) ?_
  · conv_rhs => rw [← congrArg Subtype.val ((basisRestrictSupport A _).sum_repr
      ((D.diagramQREquiv hD_up ℓ P).1 v)), Submodule.coe_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun β _ ↦ by
      rw [coe_diagramDivisionEnd_diagramIndexEquiv_symm_inl]
      simp [smul_monomial, ← smul_mul_assoc]
  · conv_rhs => rw [← congrArg Subtype.val ((basisRestrictSupport A _).sum_repr
      (D.diagramQREquiv hD_up ℓ P).2), Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ ↦ by
      rw [coe_diagramDivisionEnd_diagramIndexEquiv_symm_inr]
      simp [smul_monomial]

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
  · simp [TauCeti.coe_mapHomogeneousSubmodule_apply,
      coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell _
        hex.choose hex.choose_spec]
  · simp [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell _
      fun _ hv ↦ hex ⟨_, hv⟩]

private theorem coeff_map_diagramDivisionEnd_homogeneousMonomialBasis {B : Type*} [CommSemiring B]
    (φ : A →+* B) {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) {ℓ : ℕ} (s : σ →₀ ℕ)
    (t : {δ : σ →₀ ℕ // δ.degree = ℓ}) :
    φ ((D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ t) :
        MvPolynomial σ A).coeff s) =
      (D.diagramDivisionEnd (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) ℓ
        (TauCeti.homogeneousMonomialBasis ℓ t) : MvPolynomial σ B).coeff s := by
  rw [← coeff_map, ← TauCeti.coe_mapHomogeneousSubmodule_apply,
    mapHomogeneousSubmodule_diagramDivisionEnd,
    TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis]

/-- Changing coefficients along `φ : A →+* B` maps `D.diagramDivisionMatrix H hH ℓ` entrywise
to the division matrix of `MvPolynomial.map φ ∘ H`. -/
theorem map_diagramDivisionMatrix {B : Type*} [CommSemiring B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) (ℓ : ℕ) :
    (D.diagramDivisionMatrix H hH ℓ).map φ =
      D.diagramDivisionMatrix (fun v ↦ MvPolynomial.map φ (H v))
        (fun v ↦ (hH v).map φ) ℓ := by
  ext s t
  simp only [Matrix.map_apply, diagramDivisionMatrix_apply]
  exact coeff_map_diagramDivisionEnd_homogeneousMonomialBasis φ hH s.val ⟨t.val, t.property.2⟩

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
  let Q (v : D.diagramVertices) :=
    restrictSupport A {β ∈ D.diagramBox v.val | v.val.degree + β.degree = ℓ}
  let R := restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ}
  let hsupp : ((∀ v, Q v) × R) ≃
      {qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A //
        (∀ v, qr.1 v ∈ Q v) ∧ qr.2 ∈ R} :=
    (Equiv.subtypeProdEquivProd.trans
      (Equiv.prodCongr Equiv.subtypePiEquivPi (Equiv.refl _))).symm
  have hsupp_fst (p : (∀ v, Q v) × R) (v : D.diagramVertices) :
      (hsupp p).val.1 v = (p.1 v : MvPolynomial σ A) := rfl
  have hsupp_snd (p : (∀ v, Q v) × R) :
      (hsupp p).val.2 = (p.2 : MvPolynomial σ A) := rfl
  let heqv (G : homogeneousSubmodule σ A ℓ) :=
    (((D.diagramQREquiv hD_up ℓ).toEquiv.trans hsupp).subtypeEquiv
      (p := fun P ↦ D.diagramDivisionEnd H hH ℓ P = G)
      (q := fun qr ↦ ∑ v, qr.val.1 v * H v + qr.val.2 = G.val) fun P ↦ by
        simp only [Subtype.ext_iff, coe_diagramDivisionEnd_eq_diagramQREquiv hD_up hH,
          Equiv.trans_apply, LinearEquiv.coe_toEquiv, hsupp_fst, hsupp_snd]).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter _
        (fun qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A ↦
          ∑ v, qr.1 v * H v + qr.2 = G.val)).trans (Equiv.subtypeEquivRight fun _ ↦ and_assoc)
  exact ⟨fun h G ↦ (Equiv.existsUnique_subtype_congr (heqv G)).mpr (h G.val G.property),
    fun h G hG ↦ (Equiv.existsUnique_subtype_congr (heqv ⟨G, hG⟩)).mp (h ⟨G, hG⟩)⟩

end Orzech

section CommRing

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommRing A]

open scoped Classical in
private noncomputable def degreeSplitEquiv (D : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    {δ : σ →₀ ℕ // δ.degree = ℓ} ≃
      {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ} ⊕ {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} where
  toFun s :=
    if hs : s.val ∈ D then Sum.inl ⟨s.val, hs, s.property⟩ else Sum.inr ⟨s.val, hs, s.property⟩
  invFun
    | Sum.inl s => ⟨s.val, s.property.2⟩
    | Sum.inr γ => ⟨γ.val, γ.property.2⟩
  left_inv s := by by_cases hs : s.val ∈ D <;> simp [hs]
  right_inv
    | Sum.inl s => by simp [s.property.1]
    | Sum.inr γ => by simp [γ.property.1]

omit [Finite σ] [LinearOrder σ] in
private theorem degreeSplitEquiv_symm_inl (D : Set (σ →₀ ℕ)) (ℓ : ℕ)
    (s : {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ}) :
    (degreeSplitEquiv D ℓ).symm (Sum.inl s) = ⟨s.val, s.property.2⟩ := rfl

omit [Finite σ] [LinearOrder σ] in
private theorem degreeSplitEquiv_symm_inr (D : Set (σ →₀ ℕ)) (ℓ : ℕ)
    (γ : {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ}) :
    (degreeSplitEquiv D ℓ).symm (Sum.inr γ) = ⟨γ.val, γ.property.2⟩ := rfl

/-- For an upward-closed diagram `D` over a commutative ring `A`, the determinant of the square
restriction `D.diagramDivisionMatrix H hH ℓ` equals
`LinearMap.det (D.diagramDivisionEnd H hH ℓ)`. -/
theorem det_diagramDivisionMatrix {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (ℓ : ℕ) [Fintype {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ}]
    [DecidableEq {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ}] :
    (D.diagramDivisionMatrix H hH ℓ).det = LinearMap.det (D.diagramDivisionEnd H hH ℓ) := by
  classical
  let b := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  let : Fintype {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ} := D.fintypeDiagramRemElem ℓ
  let e := degreeSplitEquiv D ℓ
  let M := LinearMap.toMatrix b b (D.diagramDivisionEnd H hH ℓ)
  let C : Matrix {γ : σ →₀ ℕ // γ ∉ D ∧ γ.degree = ℓ}
      {δ : σ →₀ ℕ // δ ∈ D ∧ δ.degree = ℓ} A :=
    fun s t ↦ M ⟨s.val, s.property.2⟩ ⟨t.val, t.property.2⟩
  have hre : Matrix.reindex e e M = Matrix.fromBlocks (D.diagramDivisionMatrix H hH ℓ) 0 C 1 := by
    ext i j
    rcases i with s | s <;> rcases j with t | t
    · simp [M, b, e, degreeSplitEquiv_symm_inl, diagramDivisionMatrix, LinearMap.toMatrix_apply,
        TauCeti.homogeneousMonomialBasis_repr_apply]
    · have hne : t.val ≠ s.val := fun h ↦ t.property.1 (h ▸ s.property.1)
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, M, b, e, degreeSplitEquiv_symm_inl, degreeSplitEquiv_symm_inr]
      rw [toMatrix_diagramDivisionEnd_of_notMem hD_up hH _ _ t.property.1, ite_eq_right hne]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
        e, degreeSplitEquiv_symm_inr, degreeSplitEquiv_symm_inl]
      dsimp only [C]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
        Matrix.one_apply, M, b, e, degreeSplitEquiv_symm_inr]
      rw [toMatrix_diagramDivisionEnd_of_notMem hD_up hH _ _ t.property.1]
      simp [Subtype.ext_iff, eq_comm]
  rw [← LinearMap.det_toMatrix b, ← Matrix.det_reindex_self e M, hre,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

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
  let bB := TauCeti.homogeneousMonomialBasis (σ := σ) (R := B) ℓ
  rw [← LinearMap.det_toMatrix bA, ← LinearMap.det_toMatrix bB, RingHom.map_det]
  congr 1; ext s t
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    TauCeti.homogeneousMonomialBasis_repr_apply, bA, bB]
  exact coeff_map_diagramDivisionEnd_homogeneousMonomialBasis φ hH s.val t

/-- The finite-jet determinant product across degrees `ℓ ≤ D.diagramCutoff` controlling
homogeneous supported division in *all* degrees for a monotone upward-closed diagram `D`
(Bierstone–Milman, p. 282). -/
noncomputable def diagramCutoffDet (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.val.degree) : A :=
  ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1), LinearMap.det (D.diagramDivisionEnd H hH ℓ)

/-- Unfolding formula for `Set.diagramCutoffDet` as the product of block division determinants
over degrees `ℓ ≤ D.diagramCutoff`. -/
theorem diagramCutoffDet_def (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    D.diagramCutoffDet H hH = ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1),
      LinearMap.det (D.diagramDivisionEnd H hH ℓ) := by rw [diagramCutoffDet]

/-- `D.diagramCutoffDet H hH` is a unit in `A` if and only if every block division determinant in
degrees `ℓ ≤ D.diagramCutoff` is a unit in `A`. -/
theorem isUnit_diagramCutoffDet_iff {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    IsUnit (D.diagramCutoffDet H hH) ↔
      ∀ ℓ ≤ D.diagramCutoff, IsUnit (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) := by
  simp [diagramCutoffDet, IsUnit.prod_iff]

/-- For the empty diagram `D = ∅`, `diagramCutoffDet` equals `1`. -/
@[simp] theorem diagramCutoffDet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    (∅ : Set (σ →₀ ℕ)).diagramCutoffDet H hH = 1 := by simp [diagramCutoffDet]

/-- For `D = Set.univ`, `diagramCutoffDet` equals the constant coefficient of `H ⟨0, _⟩`. -/
@[simp] theorem diagramCutoffDet_univ
    (H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    (Set.univ : Set (σ →₀ ℕ)).diagramCutoffDet H hH = constantCoeff (H ⟨0, by simp⟩) := by
  let z : {δ : σ →₀ ℕ // δ.degree = 0} := ⟨0, by simp⟩
  let : Unique {δ : σ →₀ ℕ // δ.degree = 0} :=
    ⟨⟨z⟩, fun s ↦ Subtype.ext (by simpa [z, Finsupp.degree_eq_zero_iff] using s.property)⟩
  rw [diagramCutoffDet, diagramCutoff_univ, Finset.range_one, Finset.prod_singleton,
    ← LinearMap.det_toMatrix (TauCeti.homogeneousMonomialBasis 0), Matrix.det_unique,
    Subsingleton.elim default z]
  simp [LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply, z,
    coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH
      (ℓ := 0) (v := ⟨0, by simp⟩) (s := z) (by simp), constantCoeff_eq]

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
  rw [isUnit_diagramCutoffDet_iff hH]; refine ⟨fun h ↦ ?_, fun h ℓ _ ↦ (hiff ℓ).mpr (h ℓ)⟩
  exact fun ℓ ↦ if hle : ℓ ≤ D.diagramCutoff then (hiff ℓ).mp (h ℓ hle) else
    span_diagramSpanSet_eq_of_le hD_up hD_mono hH le_rfl ((hiff _).mp (h _ le_rfl)) (by omega)

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
