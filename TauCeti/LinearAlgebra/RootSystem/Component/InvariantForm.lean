/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Pairing
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.MulAction
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.UniqueScale

/-!
# Invariant forms of a root system, component by component

A root system is the internal direct sum of the component spaces of its irreducible components,
and different component spaces are orthogonal under every invariant form. So an invariant form is
the orthogonal sum of its restrictions to the components, and conversely any family of invariant
forms on the component pairings sums to an invariant form on the whole system. This file proves
that restriction and orthogonal reconstruction are inverse bijections

`P.InvariantForm ≃ ∀ C, (P.componentPairing C).InvariantForm`,

and that they match positive-definite forms with families of positive-definite forms.

On an irreducible component an invariant form is a scalar multiple of any other. Measured against
a reference invariant form `B₀`, an invariant form `B` therefore has one scale per component,
`RootPairing.InvariantForm.componentScale B₀ B C`, with `B = c_C • B₀` on the component space of
`C`. When `B₀` is positive definite, for instance the canonical form `P.RootForm`, which restricts
to the canonical form of every component, this identifies the positive-definite invariant forms
with the families of positive scalars, one per component: the invariant metrics of a root system
have exactly one free positive parameter per irreducible component.

## Main definitions

* `RootPairing.InvariantForm.restrictComponent`: the restriction of an invariant form to the
  component pairing of `C`.
* `RootPairing.InvariantForm.ofComponent`: the orthogonal sum of invariant forms on the
  component pairings.
* `RootPairing.InvariantForm.componentEquiv`: restriction and orthogonal reconstruction as an
  equivalence.
* `RootPairing.InvariantForm.componentScale`: the scale of an invariant form against a reference
  form on a component.
* `RootPairing.InvariantForm.posDefEquivScale`: positive-definite invariant forms correspond to
  positive scales, one per component.

## Main results

* `RootPairing.rootForm_componentPairing`: the canonical form of a component pairing is the
  restriction of the canonical form of the root system.
* `RootPairing.InvariantForm.ofComponent_form_apply`: the reconstructed form is the sum of the
  component forms on the component projections.
* `RootPairing.InvariantForm.posDef_ofComponent_iff`: the reconstructed form is positive definite
  exactly when every component form is.
* `RootPairing.InvariantForm.form_apply_eq_componentScale_mul`: on the component space of `C`, an
  invariant form is `componentScale B₀ B C` times the reference form.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Appendix C, C.23, C(g) and
  C.55.
-/

public section

namespace RootPairing

/-- **The canonical form of a component pairing is the restriction of the canonical form of the
root system**, since the coroots of the other components vanish on the component space. -/
theorem rootForm_componentPairing {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {P : RootPairing ι K M N} [Fintype ι] [P.IsRootSystem]
    (C : P.Component) [Fintype C.supp] :
    (P.componentPairing C).RootForm = P.RootForm.restrict (P.componentSpace C) := by
  classical
  ext x y
  have hc (i : C.supp) (z : P.componentSpace C) :
      (P.componentPairing C).coroot' i z = P.coroot' i z := by
    simp [coroot']
  simp only [rootForm_apply_apply, LinearMap.BilinForm.restrict_apply,
    LinearMap.domRestrict_apply, hc]
  rw [← Finset.sum_filter_of_ne (p := (· ∈ C.supp)) fun i _ h ↦ ?_]
  · refine (Finset.sum_subtype (f := fun i ↦ P.coroot' i x * P.coroot' i y) _
      (fun i ↦ ?_)).symm
    simp
  · by_contra hi
    refine h ?_
    rw [coroot'_eq_zero_of_mem_componentSpace (fun h' ↦ hi ((C.mem_supp_iff i).mpr h')) x.2,
      zero_mul]

/-! ### Restriction and orthogonal reconstruction -/

namespace InvariantForm

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem]

/-- The restriction of an invariant form to the component pairing of `C`. -/
noncomputable def restrictComponent (B : P.InvariantForm) (C : P.Component) :
    (P.componentPairing C).InvariantForm where
  form := B.form.restrict (P.componentSpace C)
  symm := ⟨fun x y ↦ by simpa using B.symm.eq x y⟩
  ne_zero i := by simpa using B.ne_zero i
  isOrthogonal_reflection i x y := by simp

@[simp]
theorem restrictComponent_form_apply (B : P.InvariantForm) (C : P.Component)
    (x y : P.componentSpace C) : (B.restrictComponent C).form x y = B.form x y :=
  (rfl)

/-- The **orthogonal sum** of invariant forms on the component pairings: the invariant form of the
whole root system that is `F C` on the component space of `C`, and for which different component
spaces are orthogonal. -/
noncomputable def ofComponent (F : ∀ C, (P.componentPairing C).InvariantForm) : P.InvariantForm :=
  haveI := Fintype.ofFinite P.Component
  { form := ∑ C, (F C).form.compl₁₂ (P.componentProj C) (P.componentProj C)
    symm := ⟨fun x y ↦ by
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]
      exact Finset.sum_congr rfl fun C _ ↦ by simpa using (F C).symm.eq _ _⟩
    ne_zero i := by
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]
      rw [Finset.sum_eq_single (P.componentOf i), componentProj_root_self]
      · have hr : (P.componentPairing (P.componentOf i)).root ⟨i, rfl⟩ =
            ⟨P.root i, root_mem_componentSpace i⟩ :=
          Subtype.ext (coe_componentPairing_root _ _ _)
        rw [← hr]
        exact (F _).ne_zero _
      · intro C _ hC
        simp [componentProj_root_of_ne (Ne.symm hC)]
      · simp
    isOrthogonal_reflection i x y := by
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]
      refine Finset.sum_congr rfl fun C _ ↦ ?_
      by_cases h : P.componentOf i = C
      · rw [componentProj_reflection_of_eq h, componentProj_reflection_of_eq h]
        exact (F C).isOrthogonal_reflection ⟨i, h⟩ _ _
      · rw [componentProj_reflection_of_ne h, componentProj_reflection_of_ne h] }

/-- **The orthogonal sum is the sum of the component forms on the component projections.** -/
theorem ofComponent_form_apply [Fintype P.Component] (F : ∀ C, (P.componentPairing C).InvariantForm)
    (x y : M) :
    (ofComponent F).form x y = ∑ C, (F C).form (P.componentProj C x) (P.componentProj C y) := by
  obtain rfl : ‹Fintype P.Component› = Fintype.ofFinite _ := Subsingleton.elim _ _
  simp only [ofComponent, LinearMap.sum_apply, LinearMap.compl₁₂_apply]

/-- On a single component space, the orthogonal sum is the given component form. -/
theorem ofComponent_form_apply_of_mem (F : ∀ C, (P.componentPairing C).InvariantForm)
    {C : P.Component} {x y : M} (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace C) :
    (ofComponent F).form x y = (F C).form ⟨x, hx⟩ ⟨y, hy⟩ := by
  have := Fintype.ofFinite P.Component
  rw [ofComponent_form_apply, Finset.sum_eq_single C]
  · rw [componentProj_apply_of_mem hx, componentProj_apply_of_mem hy]
  · intro D _ hD
    simp [componentProj_apply_of_ne (Ne.symm hD) hx]
  · simp

@[simp]
theorem restrictComponent_ofComponent (F : ∀ C, (P.componentPairing C).InvariantForm)
    (C : P.Component) : (ofComponent F).restrictComponent C = F C := by
  ext x y
  rw [restrictComponent_form_apply, ofComponent_form_apply_of_mem _ x.2 y.2]

variable [NeZero (2 : K)]

@[simp]
theorem ofComponent_restrictComponent (B : P.InvariantForm) :
    ofComponent B.restrictComponent = B := by
  have := Fintype.ofFinite P.Component
  ext x y
  rw [ofComponent_form_apply]
  conv_rhs => rw [← sum_componentProj (P := P) x, ← sum_componentProj (P := P) y]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [restrictComponent_form_apply, Finset.sum_eq_single C]
  · exact fun D _ hD ↦ B.apply_eq_zero_of_mem_componentSpace hD (P.componentProj D x).2
      (P.componentProj C y).2
  · exact fun h ↦ absurd (Finset.mem_univ C) h

/-- **An invariant form is the same as a family of invariant forms on the components**: restriction
to the component pairings and orthogonal reconstruction are inverse bijections. -/
noncomputable def componentEquiv : P.InvariantForm ≃ ∀ C, (P.componentPairing C).InvariantForm where
  toFun B := B.restrictComponent
  invFun := ofComponent
  left_inv := ofComponent_restrictComponent
  right_inv F := funext (restrictComponent_ofComponent F)

@[simp]
theorem componentEquiv_apply (B : P.InvariantForm) (C : P.Component) :
    componentEquiv B C = B.restrictComponent C :=
  (rfl)

@[simp]
theorem componentEquiv_symm_apply (F : ∀ C, (P.componentPairing C).InvariantForm) :
    componentEquiv.symm F = ofComponent F :=
  (rfl)

/-! ### Positive definiteness -/

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

omit [NeZero (2 : K)] [IsStrictOrderedRing K] in
/-- The restriction of a positive-definite invariant form to a component is positive definite. -/
theorem posDef_restrictComponent {B : P.InvariantForm} (hB : B.form.toQuadraticMap.PosDef)
    (C : P.Component) : (B.restrictComponent C).form.toQuadraticMap.PosDef := fun x hx ↦ by
  simpa using hB x (by simpa using hx)

omit [NeZero (2 : K)] in
/-- **The orthogonal sum is positive definite exactly when every component form is.** -/
theorem posDef_ofComponent_iff {F : ∀ C, (P.componentPairing C).InvariantForm} :
    (ofComponent F).form.toQuadraticMap.PosDef ↔ ∀ C, (F C).form.toQuadraticMap.PosDef := by
  refine ⟨fun h C ↦ restrictComponent_ofComponent F C ▸ posDef_restrictComponent h C,
    fun h x hx ↦ ?_⟩
  have := Fintype.ofFinite P.Component
  have hne : ∃ C, P.componentProj C x ≠ 0 := by
    by_contra! H
    exact hx (by simpa [H] using (sum_componentProj (P := P) x).symm)
  obtain ⟨C, hC⟩ := hne
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ofComponent_form_apply]
  refine Finset.sum_pos' (fun D _ ↦ ?_) ⟨C, Finset.mem_univ _, h C _ hC⟩
  exact (h D).nonneg _

end Ordered

/-! ### One scale per component -/

/-- The **scale** of an invariant form `B` against a reference invariant form `B₀` on the component
`C`: the ratio of their values on a root of `C`. By
`RootPairing.InvariantForm.form_apply_eq_componentScale_mul` it is the scalar `c` with `B = c • B₀`
on the component space of `C`. -/
noncomputable def componentScale (B₀ B : P.InvariantForm) (C : P.Component) : K :=
  B.form (P.root C.nonempty_supp.some) (P.root C.nonempty_supp.some) /
    B₀.form (P.root C.nonempty_supp.some) (P.root C.nonempty_supp.some)

/-- **On the component space of `C`, an invariant form is its scale times the reference form.** -/
theorem form_apply_eq_componentScale_mul (B₀ B : P.InvariantForm) {C : P.Component} {x y : M}
    (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace C) :
    B.form x y = componentScale B₀ B C * B₀.form x y := by
  have hr := C.nonempty_supp.some_mem
  have h := form_eq_smul_of_apply_root_root_eq (B₀.restrictComponent C) (B.restrictComponent C)
    ⟨_, hr⟩ (c := componentScale B₀ B C) (by
      simp only [restrictComponent_form_apply, coe_componentPairing_root]
      rw [componentScale, div_mul_cancel₀ _ (B₀.ne_zero _)])
  simpa using LinearMap.congr_fun₂ h ⟨x, hx⟩ ⟨y, hy⟩

/-- The scale on a component is the ratio of the two forms at any root of that component. -/
theorem componentScale_eq_div (B₀ B : P.InvariantForm) (i : ι) :
    componentScale B₀ B (P.componentOf i) =
      B.form (P.root i) (P.root i) / B₀.form (P.root i) (P.root i) := by
  rw [form_apply_eq_componentScale_mul B₀ B (root_mem_componentSpace i)
    (root_mem_componentSpace i), mul_div_cancel_right₀ _ (B₀.ne_zero i)]

/-- The scale of the orthogonal sum of unit multiples of the restrictions of `B₀` is the given
unit. -/
@[simp]
theorem componentScale_ofComponent_smul (B₀ : P.InvariantForm) (c : P.Component → Kˣ)
    (C : P.Component) :
    componentScale B₀ (ofComponent fun D ↦ c D • B₀.restrictComponent D) C = c C := by
  obtain ⟨i, rfl⟩ : ∃ i, P.componentOf i = C := C.exists_rep
  rw [componentScale_eq_div,
    ofComponent_form_apply_of_mem _ (root_mem_componentSpace i) (root_mem_componentSpace i)]
  simp [B₀.ne_zero i]

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

omit [Finite ι] [P.IsRootSystem] in
/-- The scale of a positive-definite form against a positive-definite reference form is
positive. -/
theorem componentScale_pos {B₀ B : P.InvariantForm} (hB₀ : B₀.form.toQuadraticMap.PosDef)
    (hB : B.form.toQuadraticMap.PosDef) (C : P.Component) : 0 < componentScale B₀ B C :=
  div_pos (hB _ (P.ne_zero _)) (hB₀ _ (P.ne_zero _))

/-- **Positive-definite invariant forms are positive scales, one per component.** Relative to a
positive-definite reference form `B₀`, such as the canonical form `P.toInvariantForm` (positive
definite by `RootPairing.rootForm_posDef`), a positive-definite
invariant form is determined by its scales on the irreducible components, and every family of
positive scales occurs. -/
noncomputable def posDefEquivScale (B₀ : P.InvariantForm) (hB₀ : B₀.form.toQuadraticMap.PosDef) :
    {B : P.InvariantForm // B.form.toQuadraticMap.PosDef} ≃ (P.Component → {c : K // 0 < c}) where
  toFun B C := ⟨componentScale B₀ B C, componentScale_pos hB₀ B.2 C⟩
  invFun c := ⟨ofComponent fun C ↦ Units.mk0 (c C : K) (c C).2.ne' • B₀.restrictComponent C,
    posDef_ofComponent_iff.mpr fun C x hx ↦ by
      simpa using mul_pos (c C).2 (posDef_restrictComponent hB₀ C x hx)⟩
  left_inv B := by
    refine Subtype.ext ((componentEquiv (P := P)).injective (funext fun C ↦ ?_))
    ext x y
    simp [form_apply_eq_componentScale_mul B₀ B.1 x.2 y.2]
  right_inv c := by
    ext C
    simp

/-- The positive-definite form with prescribed scales is the given scale times `B₀` on each
component space. -/
theorem form_posDefEquivScale_symm_apply_of_mem (B₀ : P.InvariantForm)
    (hB₀ : B₀.form.toQuadraticMap.PosDef) (c : P.Component → {c : K // 0 < c}) {C : P.Component}
    {x y : M} (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace C) :
    ((posDefEquivScale B₀ hB₀).symm c).1.form x y = c C * B₀.form x y := by
  simp [posDefEquivScale, ofComponent_form_apply_of_mem _ hx hy]

@[simp]
theorem posDefEquivScale_apply_coe (B₀ : P.InvariantForm) (hB₀ : B₀.form.toQuadraticMap.PosDef)
    (B : {B : P.InvariantForm // B.form.toQuadraticMap.PosDef}) (C : P.Component) :
    (posDefEquivScale B₀ hB₀ B C : K) = componentScale B₀ B C :=
  (rfl)

end Ordered

end InvariantForm

end RootPairing
