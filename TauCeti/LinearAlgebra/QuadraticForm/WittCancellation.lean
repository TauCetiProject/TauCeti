/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# Witt cancellation

Over a field in which `2` is invertible, a regular summand may be cancelled from an orthogonal
sum: if `q ⊥ q₁` and `q ⊥ q₂` are isometric and `q` is regular and finite dimensional, then `q₁`
and `q₂` are isometric. This is Witt's cancellation theorem, and it is what makes the isometry
classes of regular forms cancellative under orthogonal sum, hence a monoid that embeds into its
Grothendieck group.

The proof follows Lam I.4.5-I.4.7 and runs in three steps.

The first step uses no reflection: an isometry `e` of `q ⊥ q₁` onto `q ⊥ q₂` that fixes the first
summand *pointwise* carries the second summand into the second summand, because the first
component of `e (0, v)` is orthogonal to the whole of the first summand and so lies in the radical
of `q`. The second component of `e (0, ·)` is then an isometry of `q₁` onto `q₂`
(`TauCeti.prodCancelIsometryEquiv`).

The second step makes an arbitrary isometry fix a line pointwise. Over a field of characteristic
different from two the orthogonal group of a form acts transitively on the vectors of a fixed
nonzero value (`QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq`): one of `x - y` and `x + y`
has nonzero norm, and the reflection in it carries `x` to `y` or to `-y`. Composing the given
isometry with such an element cancels a summand spanned by a single vector of nonzero value
(`TauCeti.equivalent_of_equivalent_prod_of_span_singleton_eq_top`).

The third step is induction on a diagonalization of the cancelled summand: peeling the first
weight off `⟨a₀, …, aₙ⟩` with `TauCeti.presentedFormConsIsometryEquiv` exhibits it as
`⟨a₀⟩ ⊥ ⟨a₁, …, aₙ⟩`, whose first factor is carried by the line `K` and is cancelled by the second
step.

## Main definitions

* `TauCeti.prodCancelIsometryEquiv`: the isometry obtained by cancelling a regular summand that an
  isometry of orthogonal sums fixes pointwise.

## Main results

* `TauCeti.equivalent_of_equivalent_prod_of_span_singleton_eq_top`: cancellation of a summand
  carried by a line spanned by a vector of nonzero value.
* `TauCeti.equivalent_of_equivalent_prod`: **Witt cancellation** for a regular finite-dimensional
  summand, and `TauCeti.equivalent_of_equivalent_prod_right` on the other side.
* `TauCeti.RegularFormClass` is cancellative under orthogonal sum.

## Implementation notes

Cancellation of a *degenerate* summand is not proved here, and is not a matter of weakening a
hypothesis: over a field in which `2` is invertible it reduces to the uniqueness half of the Witt
decomposition, which splits a form as a regular part orthogonal to the zero form on its radical.
That decomposition is a separate milestone, and the reflection route below genuinely needs
regularity, because a reflection is only defined in a vector of invertible value.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4.
-/

public section

open QuadraticMap

namespace TauCeti

universe u v v₀ v₁ v₂

/-! ### Cancelling a summand that is fixed pointwise -/

section CommRing

variable {R : Type u} [CommRing R] [Invertible (2 : R)]
  {P : Type v} [AddCommGroup P] [Module R P]
  {V₀ : Type v₀} [AddCommGroup V₀] [Module R V₀]
  {V₁ : Type v₁} [AddCommGroup V₁] [Module R V₁]
  {V₂ : Type v₂} [AddCommGroup V₂] [Module R V₂]
  {Q₀ : QuadraticMap R V₀ P} {Q₁ : QuadraticMap R V₁ P} {Q₂ : QuadraticMap R V₂ P}

-- The candidate isometry: transport the second summand through `e` and forget the first
-- coordinate. `TauCeti.isometryEquiv_prod_fst_eq_zero` shows that nothing is forgotten.
private def prodCancelMap (e : (Q₀.prod Q₁).IsometryEquiv (Q₀.prod Q₂)) : V₁ →ₗ[R] V₂ :=
  LinearMap.snd R V₀ V₂ ∘ₗ (e : (V₀ × V₁) ≃ₗ[R] V₀ × V₂).toLinearMap ∘ₗ LinearMap.inr R V₀ V₁

omit [Invertible (2 : R)] in
private theorem prodCancelMap_apply (e : (Q₀.prod Q₁).IsometryEquiv (Q₀.prod Q₂)) (v : V₁) :
    prodCancelMap e v = (e (0, v)).2 := (rfl)

omit [Invertible (2 : R)] in
private theorem isometryEquiv_symm_apply_inl (e : (Q₀.prod Q₁).IsometryEquiv (Q₀.prod Q₂))
    (he : ∀ u : V₀, e (u, 0) = (u, 0)) (u : V₀) : e.symm (u, 0) = (u, 0) := by
  rw [← he u, e.symm_apply_apply]

/-- An isometry of orthogonal sums that fixes the first summand pointwise carries the second
summand into the second summand, as soon as the first summand is regular: the first component of
`e (0, v)` is orthogonal to all of `V₀`, hence lies in the radical of `Q₀`. -/
theorem isometryEquiv_prod_fst_eq_zero (hQ₀ : Q₀.Nondegenerate)
    (e : (Q₀.prod Q₁).IsometryEquiv (Q₀.prod Q₂)) (he : ∀ u : V₀, e (u, 0) = (u, 0)) (v : V₁) :
    (e (0, v)).1 = 0 := by
  have hmem : (e (0, v)).1 ∈ Q₀.radical := by
    rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.mem_ker]
    ext u
    have h := QuadraticMap.Isometry.polar_apply e.toIsometry (0, v) (u, 0)
    simp only [QuadraticMap.IsometryEquiv.toIsometry_apply, he] at h
    simpa using h
  rw [hQ₀.radical_eq_bot] at hmem
  simpa using hmem

/-- Cancel the first summand of an orthogonal sum along an isometry that fixes it pointwise: the
second component of `e (0, ·)` is an isometry of the second summands. -/
def prodCancelIsometryEquiv (hQ₀ : Q₀.Nondegenerate)
    (e : (Q₀.prod Q₁).IsometryEquiv (Q₀.prod Q₂)) (he : ∀ u : V₀, e (u, 0) = (u, 0)) :
    Q₁.IsometryEquiv Q₂ where
  toLinearEquiv :=
    LinearEquiv.ofLinearMap (prodCancelMap e) (prodCancelMap e.symm)
      (LinearMap.ext fun w => by
        have hzero := isometryEquiv_prod_fst_eq_zero hQ₀ e.symm
          (isometryEquiv_symm_apply_inl e he) w
        have h : ((0 : V₀), (e.symm (0, w)).2) = e.symm (0, w) := Prod.ext hzero.symm rfl
        simp only [LinearMap.coe_comp, Function.comp_apply, prodCancelMap_apply, h,
          e.apply_symm_apply, LinearMap.id_coe, id_eq])
      (LinearMap.ext fun v => by
        have h : ((0 : V₀), (e (0, v)).2) = e (0, v) :=
          Prod.ext (isometryEquiv_prod_fst_eq_zero hQ₀ e he v).symm rfl
        simp only [LinearMap.coe_comp, Function.comp_apply, prodCancelMap_apply, h,
          e.symm_apply_apply, LinearMap.id_coe, id_eq])
  map_app' v := by
    have h := e.map_app (0, v)
    rw [QuadraticMap.prod_apply, QuadraticMap.prod_apply,
      isometryEquiv_prod_fst_eq_zero hQ₀ e he v] at h
    simpa [prodCancelMap_apply] using h

@[simp]
theorem prodCancelIsometryEquiv_apply (hQ₀ : Q₀.Nondegenerate)
    (e : (Q₀.prod Q₁).IsometryEquiv (Q₀.prod Q₂)) (he : ∀ u : V₀, e (u, 0) = (u, 0)) (v : V₁) :
    prodCancelIsometryEquiv hQ₀ e he v = (e (0, v)).2 := (rfl)

end CommRing

/-! ### Cancelling a line -/

section Line

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V₀ : Type v₀} [AddCommGroup V₀] [Module K V₀]
  {V₁ : Type v₁} [AddCommGroup V₁] [Module K V₁]
  {V₂ : Type v₂} [AddCommGroup V₂] [Module K V₂]

/-- A form on a line spanned by a vector of nonzero value is regular. -/
theorem nondegenerate_of_span_singleton_eq_top {Q₀ : QuadraticForm K V₀} {v₀ : V₀}
    (hspan : Submodule.span K {v₀} = ⊤) (hv₀ : Q₀ v₀ ≠ 0) : Q₀.Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_eq_ker_polarBilin,
    LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨c, rfl⟩ := (Submodule.span_singleton_eq_top_iff K v₀).mp hspan z
  have hpolar : polar Q₀ (c • v₀) v₀ = 0 := by
    simpa using congrArg (fun L : V₀ →ₗ[K] K => L v₀) hz
  rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_self] at hpolar
  have hc : c = 0 := by simpa [(isUnit_of_invertible (2 : K)).ne_zero, hv₀] using hpolar
  rw [hc, zero_smul]

/-- **Witt cancellation** for a summand carried by a line: a form on a space spanned by a single
vector of nonzero value cancels from an orthogonal sum.

Witt transitivity moves the image of the spanning vector back onto itself, after which the
isometry fixes the whole line and `TauCeti.prodCancelIsometryEquiv` applies. -/
theorem equivalent_of_equivalent_prod_of_span_singleton_eq_top {Q₀ : QuadraticForm K V₀} {v₀ : V₀}
    (hspan : Submodule.span K {v₀} = ⊤) (hv₀ : Q₀ v₀ ≠ 0) {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (h : (Q₀.prod Q₁).Equivalent (Q₀.prod Q₂)) : Q₁.Equivalent Q₂ := by
  have : NeZero (2 : K) := ⟨(isUnit_of_invertible (2 : K)).ne_zero⟩
  obtain ⟨e⟩ := h
  obtain ⟨f, hf⟩ := (Q₀.prod Q₂).exists_isometryEquiv_apply_eq_of_map_eq
    (x := e (v₀, 0)) (y := (v₀, 0)) (by simp) (by simpa using hv₀)
  have hfix : ∀ u : V₀, (e.trans f) (u, 0) = (u, 0) := by
    intro u
    obtain ⟨c, rfl⟩ := (Submodule.span_singleton_eq_top_iff K v₀).mp hspan u
    have hsmul : ((c • v₀ : V₀), (0 : V₁)) = c • ((v₀, 0) : V₀ × V₁) := by simp
    have hv : (e.trans f) (v₀, 0) = (v₀, 0) := hf
    rw [hsmul, map_smul, hv, Prod.smul_mk, smul_zero]
  exact ⟨prodCancelIsometryEquiv (nondegenerate_of_span_singleton_eq_top hspan hv₀)
    (e.trans f) hfix⟩

end Line

/-! ### Witt cancellation -/

section Cancellation

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V₀ : Type v₀} [AddCommGroup V₀] [Module K V₀]
  {V₁ : Type v₁} [AddCommGroup V₁] [Module K V₁]
  {V₂ : Type v₂} [AddCommGroup V₂] [Module K V₂]

private theorem equivalent_of_equivalent_presentedForm_prod {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (n : ℕ) (w : Fin n → Kˣ)
    (h : ((presentedForm ⟨n, w⟩).prod Q₁).Equivalent ((presentedForm ⟨n, w⟩).prod Q₂)) :
    Q₁.Equivalent Q₂ := by
  induction n with
  | zero =>
    have e₁ : ((presentedForm ⟨0, w⟩).prod Q₁).Equivalent Q₁ :=
      ⟨QuadraticMap.IsometryEquiv.uniqueProd _ Q₁⟩
    have e₂ : ((presentedForm ⟨0, w⟩).prod Q₂).Equivalent Q₂ :=
      ⟨QuadraticMap.IsometryEquiv.uniqueProd _ Q₂⟩
    exact e₁.symm.trans (h.trans e₂)
  | succ n ih =>
    set a : QuadraticForm K K := (w 0 : K) • QuadraticMap.sq with ha
    set B : QuadraticForm K (Fin n → K) := presentedForm ⟨n, fun i => w i.succ⟩
    have hcons : (a.prod B).Equivalent (presentedForm ⟨n + 1, w⟩) :=
      ⟨presentedFormConsIsometryEquiv w⟩
    have hassoc₁ : ((a.prod B).prod Q₁).Equivalent (a.prod (B.prod Q₁)) :=
      ⟨QuadraticMap.IsometryEquiv.prodAssoc a B Q₁⟩
    have hassoc₂ : ((a.prod B).prod Q₂).Equivalent (a.prod (B.prod Q₂)) :=
      ⟨QuadraticMap.IsometryEquiv.prodAssoc a B Q₂⟩
    have hstep : ((a.prod B).prod Q₁).Equivalent ((a.prod B).prod Q₂) :=
      (hcons.prod (QuadraticMap.Equivalent.refl Q₁)).trans
        (h.trans (hcons.prod (QuadraticMap.Equivalent.refl Q₂)).symm)
    have key : (a.prod (B.prod Q₁)).Equivalent (a.prod (B.prod Q₂)) :=
      hassoc₁.symm.trans (hstep.trans hassoc₂)
    have hspan : Submodule.span K {(1 : K)} = ⊤ :=
      (Submodule.span_singleton_eq_top_iff K (1 : K)).mpr fun x => ⟨x, by simp⟩
    exact ih (fun i => w i.succ)
      (equivalent_of_equivalent_prod_of_span_singleton_eq_top hspan (by simp [ha]) key)

/-- **Witt cancellation** (Lam I.4.2): a regular finite-dimensional summand cancels from an
orthogonal sum.

Regularity of the cancelled summand is Lam's hypothesis and is what the reflection argument needs;
see the implementation notes of this file for what cancelling a degenerate summand would take. -/
theorem equivalent_of_equivalent_prod [FiniteDimensional K V₀] {Q₀ : QuadraticForm K V₀}
    (hQ₀ : Q₀.Nondegenerate) {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : (Q₀.prod Q₁).Equivalent (Q₀.prod Q₂)) : Q₁.Equivalent Q₂ := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q₀ hQ₀
  exact equivalent_of_equivalent_presentedForm_prod p.1 p.2
    (((hp.symm.prod (QuadraticMap.Equivalent.refl Q₁)).trans h).trans
      (hp.prod (QuadraticMap.Equivalent.refl Q₂)))

/-- **Witt cancellation**, cancelling the summand on the right. -/
theorem equivalent_of_equivalent_prod_right [FiniteDimensional K V₀] {Q₀ : QuadraticForm K V₀}
    (hQ₀ : Q₀.Nondegenerate) {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : (Q₁.prod Q₀).Equivalent (Q₂.prod Q₀)) : Q₁.Equivalent Q₂ := by
  have hcomm₁ : (Q₀.prod Q₁).Equivalent (Q₁.prod Q₀) :=
    ⟨QuadraticMap.IsometryEquiv.prodComm Q₀ Q₁⟩
  have hcomm₂ : (Q₂.prod Q₀).Equivalent (Q₀.prod Q₂) :=
    ⟨QuadraticMap.IsometryEquiv.prodComm Q₂ Q₀⟩
  exact equivalent_of_equivalent_prod hQ₀ (hcomm₁.trans (h.trans hcomm₂))

private theorem isLeftCancelAdd_regularFormClass : IsLeftCancelAdd (RegularFormClass K) where
  add_left_cancel x y z h := by
    revert h
    refine Quotient.inductionOn₃ x y z fun p q r h => ?_
    simp only [RegularFormClass.mk_add_mk, RegularFormClass.mk_eq_mk_iff] at h ⊢
    exact equivalent_of_equivalent_prod (nondegenerate_presentedForm p)
      ((equivalent_presentedForm_append_prod p q).symm.trans
        (h.trans (equivalent_presentedForm_append_prod p r)))

/-- Orthogonal sum is cancellative on the isometry classes of regular forms: this is Witt
cancellation read on `TauCeti.RegularFormClass`, and it is what makes the canonical map from the
monoid of isometry classes into the Witt-Grothendieck ring injective. -/
instance : IsCancelAdd (RegularFormClass K) :=
  have := isLeftCancelAdd_regularFormClass (K := K)
  AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _

end Cancellation

end TauCeti
