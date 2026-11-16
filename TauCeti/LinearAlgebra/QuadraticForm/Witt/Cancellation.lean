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

The file also provides cancellation interfaces for a summand fixed pointwise and for a form on a
space spanned by one vector of nonzero value. The proof of the general theorem follows Lam
I.4.5–I.4.7.

## Main definitions

* `TauCeti.prodCancelIsometryEquiv`: the isometry obtained by cancelling a regular summand that an
  isometry of orthogonal sums fixes pointwise.

## Main results

* `TauCeti.equivalent_of_equivalent_prod_of_span_singleton_eq_top`: cancellation of a summand
  carried by a line spanned by a vector of nonzero value.
* `TauCeti.equivalent_of_equivalent_prod`: **Witt cancellation** for a regular finite-dimensional
  summand, and `TauCeti.equivalent_of_equivalent_prod_right` on the other side.
* `TauCeti.isRepresentedBy_of_prod_isRepresentedBy_prod`,
  `TauCeti.isRepresentedBy_of_prod_isRepresentedBy_prod_right`: **Witt cancellation for
  representation** for an arbitrary finite-dimensional summand (regular or degenerate).
* `TauCeti.RegularFormClass` is cancellative under orthogonal sum.

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

/-- If an isometry of orthogonal sums fixes a regular first summand pointwise, the first component
of the image of every vector in the second summand is zero. -/
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

/-- The inverse cancellation isometry is the second component of `e.symm` on the second
summand. -/
@[simp]
theorem prodCancelIsometryEquiv_symm_apply (hQ₀ : Q₀.Nondegenerate)
    (e : (Q₀.prod Q₁).IsometryEquiv (Q₀.prod Q₂)) (he : ∀ u : V₀, e (u, 0) = (u, 0)) (w : V₂) :
    (prodCancelIsometryEquiv hQ₀ e he).symm w = (e.symm (0, w)).2 := (rfl)

end CommRing

/-! ### Cancelling a line -/

section Line

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V₀ : Type v₀} [AddCommGroup V₀] [Module K V₀]
  {V₁ : Type v₁} [AddCommGroup V₁] [Module K V₁]
  {V₂ : Type v₂} [AddCommGroup V₂] [Module K V₂]

/-- **Witt cancellation** for a summand carried by a line: a form on a space spanned by a single
vector of nonzero value cancels from an orthogonal sum. -/
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

/-- **Witt cancellation for representation** for a summand carried by a line: a line spanned by a
vector of nonzero value cancels from a representation of orthogonal sums. -/
private theorem isRepresentedBy_of_prod_isRepresentedBy_prod_of_span_singleton_eq_top
    {Q₀ : QuadraticForm K V₀} {v₀ : V₀} (hspan : Submodule.span K {v₀} = ⊤) (hv₀ : Q₀ v₀ ≠ 0)
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : (Q₀.prod Q₁).IsRepresentedBy (Q₀.prod Q₂)) : Q₁.IsRepresentedBy Q₂ := by
  have : NeZero (2 : K) := ⟨(isUnit_of_invertible (2 : K)).ne_zero⟩
  obtain ⟨e₀, he_inj, he_map⟩ := (QuadraticMap.isRepresentedBy_iff _ _).mp h
  let e : (Q₀.prod Q₁) →qᵢ (Q₀.prod Q₂) := ⟨e₀, he_map⟩
  obtain ⟨f, hf⟩ := (Q₀.prod Q₂).exists_isometryEquiv_apply_eq_of_map_eq
    (x := e (v₀, 0)) (y := (v₀, 0)) (by simp [e.map_app]) (by simpa using hv₀)
  let g : (Q₀.prod Q₁) →qᵢ (Q₀.prod Q₂) := f.toIsometry.comp e
  have hg_inj : Function.Injective g := f.injective.comp he_inj
  have hfix : ∀ u : V₀, g (u, 0) = (u, 0) := by
    intro u
    obtain ⟨c, rfl⟩ := (Submodule.span_singleton_eq_top_iff K v₀).mp hspan u
    have hsmul : ((c • v₀ : V₀), (0 : V₁)) = c • ((v₀, 0) : V₀ × V₁) := by simp
    have hv : g (v₀, 0) = (v₀, 0) := hf
    rw [hsmul, map_smul, hv, Prod.smul_mk, smul_zero]
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_span_singleton_eq_top hspan hv₀
  have hfst : ∀ v : V₁, (g (0, v)).1 = 0 := by
    intro v
    have hmem : (g (0, v)).1 ∈ Q₀.radical := by
      rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.mem_ker]
      ext u
      have hp := g.polar_apply (0, v) (u, 0)
      simp only [hfix] at hp
      simpa using hp
    rw [hQ₀.radical_eq_bot] at hmem
    simpa using hmem
  let hlin : V₁ →ₗ[K] V₂ := LinearMap.snd K V₀ V₂ ∘ₗ g.toLinearMap ∘ₗ LinearMap.inr K V₀ V₁
  refine (QuadraticMap.isRepresentedBy_iff Q₁ Q₂).mpr ⟨hlin, ?_, ?_⟩
  · intro v₁ v₂ hv
    have hpair : g (0, v₁) = g (0, v₂) := Prod.ext (by rw [hfst v₁, hfst v₂]) hv
    exact congrArg Prod.snd (hg_inj hpair)
  · intro v
    have hmap := g.map_app (0, v)
    rw [QuadraticMap.prod_apply, QuadraticMap.prod_apply, hfst v] at hmap
    simpa [hlin] using hmap

omit [Invertible (2 : K)] in
private theorem exists_linearMap_apply_eq_one {v₀ : V₁} (hv₀ : v₀ ≠ 0) :
    ∃ φ : V₁ →ₗ[K] K, φ v₀ = 1 := by
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (Submodule.span K {v₀})
  refine ⟨(LinearEquiv.toSpanNonzeroSingleton K V₁ v₀ hv₀).symm.toLinearMap ∘ₗ
    LinearMap.fst K _ _ ∘ₗ (Submodule.prodEquivOfIsCompl _ U hU).symm.toLinearMap, ?_⟩
  have hsymm : ((Submodule.span K {v₀}).prodEquivOfIsCompl U hU).symm v₀ =
      (⟨v₀, Submodule.mem_span_singleton_self v₀⟩, 0) :=
    (LinearEquiv.symm_apply_eq _).mpr (by simp)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, LinearMap.fst_apply]
  exact (LinearEquiv.symm_apply_eq _).mpr (by simp)

omit [Invertible (2 : K)] in
/-- Cancelling a one-dimensional zero summand from a representation of orthogonal sums over any
field. -/
private theorem isRepresentedBy_of_zero_prod_isRepresentedBy_zero_prod
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : ((0 : QuadraticForm K K).prod Q₁).IsRepresentedBy ((0 : QuadraticForm K K).prod Q₂)) :
    Q₁.IsRepresentedBy Q₂ := by
  obtain ⟨e, he_inj, he_map⟩ := (QuadraticMap.isRepresentedBy_iff _ _).mp h
  have heQ : ∀ p : K × V₁, Q₂ (e p).2 = Q₁ p.2 := fun p ↦ by simpa using he_map p
  let g : V₁ →ₗ[K] V₂ := LinearMap.snd K K V₂ ∘ₗ e ∘ₗ LinearMap.inr K K V₁
  have hgQ : ∀ v, Q₂ (g v) = Q₁ v := fun v ↦ heQ (0, v)
  by_cases hginj : Function.Injective g
  · exact (QuadraticMap.isRepresentedBy_iff Q₁ Q₂).mpr ⟨g, hginj, hgQ⟩
  obtain ⟨v₀, hv₀_ker, hv₀⟩ : ∃ v₀, g v₀ = 0 ∧ v₀ ≠ 0 := by
    rw [injective_iff_map_eq_zero] at hginj; simpa [not_forall] using hginj
  have hv₀_snd : (e (0, v₀)).2 = 0 := hv₀_ker
  set c : K := (e (0, v₀)).1
  have hc : c ≠ 0 := fun hc0 ↦ hv₀ (congrArg Prod.snd
    (he_inj (show e (0, v₀) = e 0 by rw [map_zero]; exact Prod.ext hc0 hv₀_snd)))
  have hfst_eq : ∀ p : K × V₁, (e p).2 = 0 → p = (0, ((e p).1 / c) • v₀) := fun p hp ↦
    he_inj <| by
      rw [show ((0 : K), ((e p).1 / c) • v₀) = ((e p).1 / c) • ((0 : K), v₀) by simp, map_smul]
      exact Prod.ext (by simp [c, div_mul_cancel₀ _ hc]) (by simp [hp, hv₀_snd])
  let w₀ : V₂ := (e (1, 0)).2
  have hw₀Q : Q₂ w₀ = 0 := by simpa using heQ (1, 0)
  have hpol : ∀ v, QuadraticMap.polar Q₂ (g v) w₀ = 0 := fun v ↦ by
    have hsum : g v + w₀ = (e (1, v)).2 := by simp [g, w₀, ← Prod.snd_add, ← map_add]
    rw [QuadraticMap.polar, hsum, heQ (1, v), hgQ v, hw₀Q, sub_self, sub_zero]
  have hnotmem : ∀ v, g v ≠ w₀ := fun v hgv ↦ one_ne_zero <| congrArg Prod.fst <| hfst_eq (1, -v) <|
    by rw [show ((1 : K), -v) = ((1 : K), (0 : V₁)) - ((0 : K), v) by simp, map_sub, Prod.snd_sub,
      sub_eq_zero]; exact hgv.symm
  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_eq_one (K := K) hv₀
  refine (QuadraticMap.isRepresentedBy_iff Q₁ Q₂).mpr ⟨g + φ.smulRight w₀, ?_, fun v ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]; intro v hv
    have hv' : g v + φ v • w₀ = 0 := hv
    have hφv : φ v = 0 := by
      by_contra hne
      refine hnotmem (-(φ v)⁻¹ • v) ?_
      rw [map_smul, eq_neg_of_add_eq_zero_left hv', smul_neg, neg_smul, neg_neg, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    have hvr : v = ((e (0, v)).1 / c) • v₀ :=
      congrArg Prod.snd (hfst_eq (0, v) (by simpa [g, hφv] using hv'))
    have hcoeff : (e (0, v)).1 / c = 0 := by
      have := congrArg φ hvr; simpa [hφv, hφ] using this.symm
    rw [hvr, hcoeff, zero_smul]
  · simp [QuadraticMap.map_add, hgQ v, Q₂.map_smul, hw₀Q, QuadraticMap.polar_smul_right, hpol v]

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

private theorem isRepresentedBy_of_presentedForm_prod_isRepresentedBy_prod
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (n : ℕ) (w : Fin n → Kˣ)
    (h : ((presentedForm ⟨n, w⟩).prod Q₁).IsRepresentedBy ((presentedForm ⟨n, w⟩).prod Q₂)) :
    Q₁.IsRepresentedBy Q₂ := by
  induction n with
  | zero =>
    have e₁ : ((presentedForm ⟨0, w⟩).prod Q₁).Equivalent Q₁ :=
      ⟨QuadraticMap.IsometryEquiv.uniqueProd _ Q₁⟩
    have e₂ : ((presentedForm ⟨0, w⟩).prod Q₂).Equivalent Q₂ :=
      ⟨QuadraticMap.IsometryEquiv.uniqueProd _ Q₂⟩
    exact (QuadraticMap.Equivalent.isRepresentedBy_congr e₁ e₂).mp h
  | succ n ih =>
    set a : QuadraticForm K K := (w 0 : K) • QuadraticMap.sq with ha
    set B : QuadraticForm K (Fin n → K) := presentedForm ⟨n, fun i => w i.succ⟩
    have hcons : (a.prod B).Equivalent (presentedForm ⟨n + 1, w⟩) :=
      ⟨presentedFormConsIsometryEquiv w⟩
    have hstep : ((a.prod B).prod Q₁).IsRepresentedBy ((a.prod B).prod Q₂) :=
      (QuadraticMap.Equivalent.isRepresentedBy_congr
        (hcons.prod (QuadraticMap.Equivalent.refl Q₁))
        (hcons.prod (QuadraticMap.Equivalent.refl Q₂))).mpr h
    have key : (a.prod (B.prod Q₁)).IsRepresentedBy (a.prod (B.prod Q₂)) :=
      (QuadraticMap.Equivalent.isRepresentedBy_congr
        ⟨QuadraticMap.IsometryEquiv.prodAssoc a B Q₁⟩
        ⟨QuadraticMap.IsometryEquiv.prodAssoc a B Q₂⟩).mp hstep
    have hspan : Submodule.span K {(1 : K)} = ⊤ :=
      (Submodule.span_singleton_eq_top_iff K (1 : K)).mpr fun x => ⟨x, by simp⟩
    exact ih (fun i => w i.succ)
      (isRepresentedBy_of_prod_isRepresentedBy_prod_of_span_singleton_eq_top hspan
        (by simp [ha]) key)

omit [Invertible (2 : K)] in
private theorem isRepresentedBy_of_zero_fin_prod_isRepresentedBy_zero_fin_prod
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} :
    ∀ n : ℕ, ((0 : QuadraticForm K (Fin n → K)).prod Q₁).IsRepresentedBy
        ((0 : QuadraticForm K (Fin n → K)).prod Q₂) → Q₁.IsRepresentedBy Q₂
  | 0, h =>
    (QuadraticMap.Equivalent.isRepresentedBy_congr
      ⟨QuadraticMap.IsometryEquiv.uniqueProd _ Q₁⟩
      ⟨QuadraticMap.IsometryEquiv.uniqueProd _ Q₂⟩).mp h
  | n + 1, h => by
    have hsplit : (0 : QuadraticForm K (Fin (n + 1) → K)).Equivalent
        ((0 : QuadraticForm K K).prod (0 : QuadraticForm K (Fin n → K))) :=
      ⟨{ toLinearEquiv := LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_prod, add_comm])
         map_app' := fun _ ↦ by simp }⟩
    have hstep :
        (((0 : QuadraticForm K K).prod (0 : QuadraticForm K (Fin n → K))).prod Q₁).IsRepresentedBy
          (((0 : QuadraticForm K K).prod (0 : QuadraticForm K (Fin n → K))).prod Q₂) :=
      (QuadraticMap.Equivalent.isRepresentedBy_congr
        (hsplit.prod (QuadraticMap.Equivalent.refl Q₁))
        (hsplit.prod (QuadraticMap.Equivalent.refl Q₂))).mp h
    have hassoc : ((0 : QuadraticForm K K).prod
        ((0 : QuadraticForm K (Fin n → K)).prod Q₁)).IsRepresentedBy
        ((0 : QuadraticForm K K).prod ((0 : QuadraticForm K (Fin n → K)).prod Q₂)) :=
      (QuadraticMap.Equivalent.isRepresentedBy_congr
        ⟨QuadraticMap.IsometryEquiv.prodAssoc _ _ Q₁⟩
        ⟨QuadraticMap.IsometryEquiv.prodAssoc _ _ Q₂⟩).mp hstep
    exact isRepresentedBy_of_zero_fin_prod_isRepresentedBy_zero_fin_prod n
      (isRepresentedBy_of_zero_prod_isRepresentedBy_zero_prod hassoc)

/-- **Witt cancellation** (Lam I.4.2): a regular finite-dimensional summand cancels from an
orthogonal sum. -/
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

/-- **Witt cancellation for representation**: any finite-dimensional summand (regular or
degenerate) cancels from a representation of orthogonal sums. Neither finiteness nor nondegeneracy
of `Q₁` or `Q₂` is needed. -/
theorem isRepresentedBy_of_prod_isRepresentedBy_prod [FiniteDimensional K V₀]
    {Q₀ : QuadraticForm K V₀} {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : (Q₀.prod Q₁).IsRepresentedBy (Q₀.prod Q₂)) :
    Q₁.IsRepresentedBy Q₂ := by
  let r := Module.finrank K Q₀.radical
  have hrad : (0 : QuadraticForm K Q₀.radical).Equivalent (0 : QuadraticForm K (Fin r → K)) :=
    ⟨{ toLinearEquiv := LinearEquiv.ofFinrankEq _ _ (by simp [r]), map_app' := fun _ ↦ rfl }⟩
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent _ Q₀.nondegenerate_lift_radical
  have hQ₀ : Q₀.Equivalent ((0 : QuadraticForm K (Fin r → K)).prod (presentedForm p)) :=
    QuadraticMap.Equivalent.trans
      ⟨(QuadraticMap.IsometryEquiv.prodRadicalLift Q₀).symm⟩ (hrad.prod hp)
  have hstep :
      (((0 : QuadraticForm K (Fin r → K)).prod (presentedForm p)).prod Q₁).IsRepresentedBy
        (((0 : QuadraticForm K (Fin r → K)).prod (presentedForm p)).prod Q₂) :=
    (QuadraticMap.Equivalent.isRepresentedBy_congr
      (hQ₀.prod (QuadraticMap.Equivalent.refl Q₁))
      (hQ₀.prod (QuadraticMap.Equivalent.refl Q₂))).mp h
  have hassoc :
      ((0 : QuadraticForm K (Fin r → K)).prod ((presentedForm p).prod Q₁)).IsRepresentedBy
        ((0 : QuadraticForm K (Fin r → K)).prod ((presentedForm p).prod Q₂)) :=
    (QuadraticMap.Equivalent.isRepresentedBy_congr
      ⟨QuadraticMap.IsometryEquiv.prodAssoc _ _ Q₁⟩
      ⟨QuadraticMap.IsometryEquiv.prodAssoc _ _ Q₂⟩).mp hstep
  exact isRepresentedBy_of_presentedForm_prod_isRepresentedBy_prod p.1 p.2
    (isRepresentedBy_of_zero_fin_prod_isRepresentedBy_zero_fin_prod r hassoc)

/-- **Witt cancellation for representation**, cancelling the summand on the right. -/
theorem isRepresentedBy_of_prod_isRepresentedBy_prod_right [FiniteDimensional K V₀]
    {Q₀ : QuadraticForm K V₀} {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : (Q₁.prod Q₀).IsRepresentedBy (Q₂.prod Q₀)) :
    Q₁.IsRepresentedBy Q₂ :=
  isRepresentedBy_of_prod_isRepresentedBy_prod
    ((QuadraticMap.Equivalent.isRepresentedBy_congr
      ⟨QuadraticMap.IsometryEquiv.prodComm Q₀ Q₁⟩
      ⟨QuadraticMap.IsometryEquiv.prodComm Q₀ Q₂⟩).mpr h)

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
