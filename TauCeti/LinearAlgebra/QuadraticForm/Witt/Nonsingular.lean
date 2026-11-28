/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
import Mathlib.LinearAlgebra.Prod
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.QuadraticForm.CharTwo
import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.QuadraticForm.Representation
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Witt cancellation and decomposition in every characteristic

Over a field in which `2` is invertible, Witt cancellation and Witt decomposition are
`TauCeti.equivalent_of_equivalent_prod` and `TauCeti.exists_nsmul_hyperbolicClass_add`. Both proofs
diagonalize, which fails in characteristic two: there the polar form is alternating, diagonal forms
are singular, and a singular summand need not cancel. This file proves both theorems over an
arbitrary field: cancellation of the hyperbolic plane `ℍ = TauCeti.binaryQuadraticForm K 0 0`, with
value `x 0 * x 1`, and of every *nonsingular* summand, one whose polar bilinear form is
nondegenerate; and decomposition of every finite-dimensional form with trivial radical.

The basic object is a *hyperbolic pair* `e, f`: isotropic vectors with `polar Q e f = 1`. Its span
is a copy of `ℍ` and splits off orthogonally, with no hypothesis on the ambient form
(`QuadraticForm.equivalent_binaryQuadraticForm_zero_prod_restrict_orthogonal`, in
`TauCeti/LinearAlgebra/QuadraticForm/Hyperbolic.lean`). The orthogonal
complement of the span depends, up to isometry, only on `Q`
(`QuadraticForm.equivalent_restrict_orthogonal_span_pair`). For pairs `e, f` and `e, f'` sharing
their first vector, `u ↦ u - polar Q f' u • e` maps one complement isometrically onto the other. If
`polar Q e e' ≠ 0`, then `e` and `e'` themselves, suitably scaled, form hyperbolic pairs with the
same span. Two arbitrary pairs are joined through an isotropic vector pairing nontrivially with
both `e` and `e'`, which `f`, `f'` or `f + f' - polar Q f f' • e` provides. In particular `ℍ`
cancels from orthogonal sums of arbitrary quadratic forms, in every characteristic.

In characteristic two, a nonsingular form `Q₀` satisfies `Q₀ ⊥ Q₀ ≅ m ℍ`
(`QuadraticMap.equivalent_prod_self_pi_binaryQuadraticForm_zero`), so adding a second copy of `Q₀`
reduces cancellation of `Q₀` to cancellation of `ℍ`. Together with the case where `2` is
invertible, this gives **Witt cancellation** of a finite-dimensional nonsingular summand over every
field (`TauCeti.equivalent_of_equivalent_prod_of_nondegenerate_polarBilin`).

Finally, a finite-dimensional form with trivial radical is `m ℍ ⊥ A` with `A` anisotropic
(`QuadraticForm.exists_equivalent_pi_binaryQuadraticForm_zero_prod`), and in any decomposition
`m ℍ ⊥ A` with `A` anisotropic, the number `m` and the isometry class of `A` are determined by the
form (`TauCeti.eq_and_equivalent_of_equivalent_pi_binaryQuadraticForm_zero_prod`): this is the
**Witt decomposition**, with Witt index `m` and anisotropic part `A`.

## Main results

* `QuadraticForm.equivalent_restrict_orthogonal_span_pair`: the orthogonal complements of any two
  hyperbolic pairs are isometric.
* `QuadraticForm.exists_equivalent_binaryQuadraticForm_zero_prod`: a form with trivial radical and
  a nonzero isotropic vector splits as `ℍ` plus a form with trivial radical.
* `TauCeti.equivalent_of_equivalent_binaryQuadraticForm_zero_prod` and
  `TauCeti.equivalent_of_equivalent_pi_binaryQuadraticForm_zero_prod`: `ℍ` and `m ℍ` cancel from
  orthogonal sums of arbitrary quadratic forms, in every characteristic.
* `TauCeti.equivalent_of_equivalent_prod_of_nondegenerate_polarBilin`: **Witt cancellation** of a
  finite-dimensional nonsingular summand, over every field.
* `QuadraticForm.exists_equivalent_pi_binaryQuadraticForm_zero_prod` and
  `TauCeti.eq_and_equivalent_of_equivalent_pi_binaryQuadraticForm_zero_prod`: **Witt
  decomposition**, existence and uniqueness.

## References

* R. Elman, N. Karpenko and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  AMS Colloquium Publications 56 (2008), Chapter II, §§7–8 (Proposition 7.13, Theorems 8.4 and 8.5).
-/

public section

open QuadraticMap Module

universe u v v₀ v₁ v₂

/-! ### Hyperbolic pairs and their orthogonal complements -/

namespace QuadraticForm

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {e f e' f' : V}

/-- For hyperbolic pairs `e, f` and `e, f'`, the map `u ↦ u - polar Q f' u • e` sends the
orthogonal complement of the span of `e` and `f` into that of `e` and `f'`. -/
private def orthogonalSpanPairMap (e f f' : V) (he : Q e = 0) (hef' : polar Q e f' = 1) :
    LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e, f}) →ₗ[K]
      LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e, f'}) :=
  LinearMap.codRestrict _
    ((LinearMap.id - (Q.polarBilin f').smulRight e) ∘ₗ Submodule.subtype _) fun u ↦ by
      obtain ⟨hu₁, -⟩ : polar Q e u = 0 ∧ _ :=
        LinearMap.BilinForm.mem_orthogonal_span_pair_iff.1 u.property
      refine LinearMap.BilinForm.mem_orthogonal_span_pair_iff.2 ⟨?_, ?_⟩ <;>
      simp [polar_sub_right, polar_smul_right, polar_self, he, hu₁, polar_comm Q f' e, hef']

private theorem coe_orthogonalSpanPairMap (he : Q e = 0) (hef' : polar Q e f' = 1)
    (u : LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e, f})) :
    (orthogonalSpanPairMap e f f' he hef' u : V) = u - polar Q f' u • e :=
  (rfl)

private theorem orthogonalSpanPairMap_comp (he : Q e = 0) (hef : polar Q e f = 1)
    (hef' : polar Q e f' = 1) :
    orthogonalSpanPairMap e f' f he hef ∘ₗ orthogonalSpanPairMap e f f' he hef' =
      LinearMap.id := by
  ext u
  obtain ⟨-, hu₂⟩ : _ ∧ polar Q f u = 0 :=
    LinearMap.BilinForm.mem_orthogonal_span_pair_iff.1 u.property
  simp [coe_orthogonalSpanPairMap, polar_sub_right, polar_smul_right, hu₂, polar_comm Q f e, hef]

/-- The orthogonal complements of two hyperbolic pairs sharing their first vector are isometric. -/
private theorem equivalent_restrict_orthogonal_span_pair_of_eq (he : Q e = 0)
    (hef : polar Q e f = 1) (hef' : polar Q e f' = 1) :
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e, f}))).Equivalent
      (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e, f'}))) :=
  ⟨{ toLinearEquiv := LinearEquiv.ofLinearMap (orthogonalSpanPairMap e f f' he hef')
        (orthogonalSpanPairMap e f' f he hef) (orthogonalSpanPairMap_comp he hef' hef)
        (orthogonalSpanPairMap_comp he hef hef')
     map_app' u := by
        obtain ⟨hu₁, -⟩ : polar Q e u = 0 ∧ _ :=
          LinearMap.BilinForm.mem_orthogonal_span_pair_iff.1 u.property
        simp [coe_orthogonalSpanPairMap, sub_eq_add_neg, QuadraticMap.map_add,
          QuadraticMap.map_smul, he, polar_comm Q u, hu₁] }⟩

/-- The orthogonal complements of two hyperbolic pairs `e, f` and `e', f'` with
`polar Q e e' ≠ 0` are isometric: both are isometric to the complement of the span of `e`, `e'`. -/
private theorem equivalent_restrict_orthogonal_span_pair_of_polar_ne_zero (he : Q e = 0)
    (hef : polar Q e f = 1) (he' : Q e' = 0) (he'f' : polar Q e' f' = 1)
    (hee' : polar Q e e' ≠ 0) :
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e, f}))).Equivalent
      (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e', f'}))) := by
  set c := polar Q e e'
  have hspan : Submodule.span K {e, c⁻¹ • e'} = Submodule.span K {e', c⁻¹ • e} := by
    rw [Submodule.span_insert, Submodule.span_insert,
      Submodule.span_singleton_smul_eq (inv_ne_zero hee').isUnit,
      Submodule.span_singleton_smul_eq (inv_ne_zero hee').isUnit, sup_comm]
  have h₁ : polar Q e (c⁻¹ • e') = 1 := by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hee']
  have h₂ : polar Q e' (c⁻¹ • e) = 1 := by
    rw [polar_smul_right, smul_eq_mul, polar_comm, inv_mul_cancel₀ hee']
  refine (equivalent_restrict_orthogonal_span_pair_of_eq he hef h₁).trans ?_
  rw [hspan]
  exact equivalent_restrict_orthogonal_span_pair_of_eq he' h₂ he'f'

/-- **The orthogonal complement of a hyperbolic pair is unique up to isometry**: for any two
hyperbolic pairs `e, f` and `e', f'` (isotropic vectors with polar pairing one), the polar
orthogonal complements of their spans are isometric, in every characteristic and with no
hypothesis on `Q`. -/
theorem equivalent_restrict_orthogonal_span_pair (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (he' : Q e' = 0) (hf' : Q f' = 0) (he'f' : polar Q e' f' = 1) :
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e, f}))).Equivalent
      (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e', f'}))) := by
  by_cases hee' : polar Q e e' ≠ 0
  · exact equivalent_restrict_orthogonal_span_pair_of_polar_ne_zero he hef he' he'f' hee'
  rw [not_not] at hee'
  -- Join the two pairs through an isotropic `g` pairing nontrivially with `e` and with `e'`.
  obtain ⟨g, hg, heg, hge'⟩ : ∃ g, Q g = 0 ∧ polar Q e g ≠ 0 ∧ polar Q g e' ≠ 0 := by
    by_cases hef'0 : polar Q e f' ≠ 0
    · exact ⟨f', hf', hef'0, by rw [polar_comm, he'f']; exact one_ne_zero⟩
    by_cases he'f0 : polar Q e' f ≠ 0
    · exact ⟨f, hf, by rw [hef]; exact one_ne_zero, by rwa [polar_comm]⟩
    rw [not_not] at hef'0 he'f0
    refine ⟨f + f' - polar Q f f' • e, ?_, ?_, ?_⟩
    · simp [sub_eq_add_neg, QuadraticMap.map_add, QuadraticMap.map_smul, hf, hf', he,
        polar_add_left, polar_neg_right, polar_smul_right, polar_comm Q f e,
        polar_comm Q f' e, hef, hef'0]
    · simp [polar_sub_right, polar_add_right, polar_smul_right, polar_self, he, hef, hef'0]
    · simp [polar_sub_left, polar_add_left, polar_smul_left, polar_comm Q f e', he'f0,
        polar_comm Q f' e', he'f', hee']
  set a := polar Q g e
  have ha : a ≠ 0 := by rwa [polar_comm] at heg
  have hga : polar Q g (a⁻¹ • e) = 1 := by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ ha]
  exact (equivalent_restrict_orthogonal_span_pair_of_polar_ne_zero he hef hg hga heg).trans
    (equivalent_restrict_orthogonal_span_pair_of_polar_ne_zero hg hga he' he'f' hge')

end QuadraticForm

/-! ### Splitting off hyperbolic planes -/

namespace QuadraticForm

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- **Splitting off a hyperbolic plane** (Elman–Karpenko–Merkurjev, Proposition 7.13), in every
characteristic: a quadratic form with trivial radical and a nonzero isotropic vector is isometric to
the orthogonal sum of the hyperbolic plane `[0, 0]` and a form with trivial radical. If `Q` is
nonsingular, so is the second summand, by `QuadraticMap.nondegenerate_polarBilin_prod_iff`. -/
theorem exists_equivalent_binaryQuadraticForm_zero_prod (Q : QuadraticForm K V)
    (hQ : Q.radical = ⊥) (hiso : ¬Q.Anisotropic) :
    ∃ W : Submodule K V, (Q.restrict W).radical = ⊥ ∧
      Q.Equivalent ((TauCeti.binaryQuadraticForm K 0 0).prod (Q.restrict W)) := by
  obtain ⟨e, f, -, he, hf, hef⟩ := exists_isotropic_pair_of_radical_eq_bot hQ hiso
  obtain ⟨σ⟩ := equivalent_binaryQuadraticForm_zero_prod_restrict_orthogonal he hf hef
  refine ⟨_, ?_, ⟨σ⟩⟩
  have hprod := radical_prod_radical_le_radical_prod (TauCeti.binaryQuadraticForm K 0 0)
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {e, f})))
  rw [← σ.map_radical, hQ, Submodule.map_bot] at hprod
  refine eq_bot_iff.mpr fun v hv ↦ ?_
  have h0 := hprod (x := (0, v)) (Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hv⟩)
  rw [Submodule.mem_bot, Prod.mk_eq_zero] at h0
  exact (Submodule.mem_bot K).mpr h0.2

end QuadraticForm

/-! ### Witt cancellation -/

namespace TauCeti

variable {K : Type u} [Field K]
  {V₀ : Type v₀} [AddCommGroup V₀] [Module K V₀]
  {V₁ : Type v₁} [AddCommGroup V₁] [Module K V₁]
  {V₂ : Type v₂} [AddCommGroup V₂] [Module K V₂]

/-- The coordinate vectors `(e₀, 0)` and `(e₁, 0)` of `[0, 0] ⊥ Q₁` form a hyperbolic pair. -/
private theorem prod_apply_single_zero (Q₁ : QuadraticForm K V₁) (i : Fin 2) :
    ((binaryQuadraticForm K 0 0).prod Q₁) (Pi.single i 1, 0) = 0 := by
  fin_cases i <;> simp

private theorem polar_prod_single_zero_single_one (Q₁ : QuadraticForm K V₁) :
    polar ((binaryQuadraticForm K 0 0).prod Q₁) (Pi.single 0 1, 0) (Pi.single 1 1, 0) = 1 := by
  simp

/-- In `[0, 0] ⊥ Q₁`, the polar orthogonal complement of the coordinate hyperbolic pair of `[0, 0]`
is a copy of `Q₁`. -/
private theorem equivalent_restrict_orthogonal_span_pair_single (Q₁ : QuadraticForm K V₁) :
    (((binaryQuadraticForm K 0 0).prod Q₁).restrict
      (LinearMap.BilinForm.orthogonal ((binaryQuadraticForm K 0 0).prod Q₁).polarBilin
        (Submodule.span K {(Pi.single 0 1, 0), (Pi.single 1 1, 0)}))).Equivalent Q₁ := by
  have h : LinearMap.BilinForm.orthogonal ((binaryQuadraticForm K 0 0).prod Q₁).polarBilin
      (Submodule.span K {(Pi.single 0 1, 0), (Pi.single 1 1, 0)}) =
      LinearMap.range (LinearMap.inr K (Fin 2 → K) V₁) := by
    ext ⟨x, v⟩
    rw [LinearMap.BilinForm.mem_orthogonal_span_pair_iff, LinearMap.mem_range]
    constructor
    · rintro ⟨h₁, h₀⟩
      refine ⟨v, Prod.ext (funext fun i ↦ ?_) rfl⟩
      fin_cases i
      · simpa using h₀.symm
      · simpa using h₁.symm
    · rintro ⟨w, hw⟩
      rw [← hw]
      simp
  rw [h]
  exact ⟨({ toLinearEquiv := LinearEquiv.ofInjective _ LinearMap.inr_injective
            map_app' v := by simp } : Q₁.IsometryEquiv _).symm⟩

/-- **Witt cancellation of the hyperbolic plane**, in every characteristic and for arbitrary
quadratic forms: if `[0, 0] ⊥ Q₁ ≅ [0, 0] ⊥ Q₂`, then `Q₁ ≅ Q₂`. -/
theorem equivalent_of_equivalent_binaryQuadraticForm_zero_prod {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂}
    (h : ((binaryQuadraticForm K 0 0).prod Q₁).Equivalent
      ((binaryQuadraticForm K 0 0).prod Q₂)) : Q₁.Equivalent Q₂ := by
  obtain ⟨σ⟩ := h
  have hmap := σ.equivalent_restrict_map
    (LinearMap.BilinForm.orthogonal ((binaryQuadraticForm K 0 0).prod Q₁).polarBilin
      (Submodule.span K {(Pi.single 0 1, 0), (Pi.single 1 1, 0)}))
  rw [σ.map_orthogonal_polarBilin, Submodule.map_span, Set.image_pair] at hmap
  simp only [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv] at hmap
  refine (equivalent_restrict_orthogonal_span_pair_single Q₁).symm.trans (hmap.trans
    ((QuadraticForm.equivalent_restrict_orthogonal_span_pair ?_ ?_ ?_
      (prod_apply_single_zero Q₂ 0) (prod_apply_single_zero Q₂ 1)
      (polar_prod_single_zero_single_one Q₂)).trans
    (equivalent_restrict_orthogonal_span_pair_single Q₂)))
  · rw [σ.map_app, prod_apply_single_zero]
  · rw [σ.map_app, prod_apply_single_zero]
  · rw [σ.polar_apply, polar_prod_single_zero_single_one]

/-- Witt cancellation of `m` hyperbolic planes, in every characteristic and for arbitrary
quadratic forms. -/
theorem equivalent_of_equivalent_pi_binaryQuadraticForm_zero_prod {m : ℕ}
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : ((QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm K 0 0).prod Q₁).Equivalent
      ((QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm K 0 0).prod Q₂)) :
    Q₁.Equivalent Q₂ := by
  induction m with
  | zero =>
    exact (equivalent_pi_zero_prod _ Q₁).symm.trans (h.trans (equivalent_pi_zero_prod _ Q₂))
  | succ m ih =>
    exact ih (equivalent_of_equivalent_binaryQuadraticForm_zero_prod
      ((equivalent_pi_succ_prod _ Q₁).symm.trans (h.trans (equivalent_pi_succ_prod _ Q₂))))

/-- **Witt cancellation** (Elman–Karpenko–Merkurjev, Theorem 8.4) over every field: a
finite-dimensional summand whose polar bilinear form is nondegenerate cancels from an orthogonal
sum of arbitrary quadratic forms. When `2` is invertible this is
`TauCeti.equivalent_of_equivalent_prod`; in characteristic two, `Q₀ ⊥ Q₀` is hyperbolic, so
cancelling `Q₀` reduces to cancelling hyperbolic planes. The polar hypothesis is needed: over
`𝔽₂`, `[1, 1] ⊥ ⟨1⟩ ≅ [0, 0] ⊥ ⟨1⟩` while `[1, 1]` is anisotropic, so the singular summand `⟨1⟩`
does not cancel. -/
theorem equivalent_of_equivalent_prod_of_nondegenerate_polarBilin [FiniteDimensional K V₀]
    {Q₀ : QuadraticForm K V₀} (hQ₀ : Q₀.polarBilin.Nondegenerate) {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (h : (Q₀.prod Q₁).Equivalent (Q₀.prod Q₂)) : Q₁.Equivalent Q₂ := by
  by_cases h2 : (2 : K) = 0
  · have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have hH := QuadraticMap.equivalent_prod_self_pi_binaryQuadraticForm_zero hQ₀
    refine equivalent_of_equivalent_pi_binaryQuadraticForm_zero_prod (m := finrank K V₀) ?_
    exact (hH.symm.prod (QuadraticMap.Equivalent.refl Q₁)).trans (QuadraticMap.Equivalent.trans
      ⟨IsometryEquiv.prodAssoc Q₀ Q₀ Q₁⟩ (((QuadraticMap.Equivalent.refl Q₀).prod h).trans
        (QuadraticMap.Equivalent.trans ⟨(IsometryEquiv.prodAssoc Q₀ Q₀ Q₂).symm⟩
          (hH.prod (QuadraticMap.Equivalent.refl Q₂)))))
  · have := invertibleOfNonzero h2
    exact equivalent_of_equivalent_prod (nondegenerate_of_nondegenerate_polarBilin hQ₀) h

end TauCeti

/-! ### Witt decomposition -/

namespace QuadraticForm

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- **Witt decomposition**, existence, in every characteristic: a finite-dimensional quadratic form
with trivial radical is isometric to the orthogonal sum of `m` hyperbolic planes `[0, 0]` and an
anisotropic form, carried by a subspace. This is the case of trivial radical of
Elman–Karpenko–Merkurjev, Theorem 8.5. -/
theorem exists_equivalent_pi_binaryQuadraticForm_zero_prod [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.radical = ⊥) :
    ∃ (m : ℕ) (W : Submodule K V), (Q.restrict W).Anisotropic ∧
      Q.Equivalent
        ((QuadraticMap.pi fun _ : Fin m ↦ TauCeti.binaryQuadraticForm K 0 0).prod
          (Q.restrict W)) := by
  obtain ⟨n, hn⟩ : ∃ n, finrank K V = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  by_cases ha : Q.Anisotropic
  · refine ⟨0, ⊤, fun x hx ↦ Subtype.ext (ha x hx), ?_⟩
    exact QuadraticMap.Equivalent.trans
      ⟨{ toLinearEquiv := Submodule.topEquiv.symm, map_app' _ := rfl }⟩
      (equivalent_pi_zero_prod _ _).symm
  obtain ⟨W, hW, hQW⟩ := Q.exists_equivalent_binaryQuadraticForm_zero_prod hQ ha
  have hlt : finrank K W < n := by
    have := hQW.some.toLinearEquiv.finrank_eq
    rw [finrank_prod, finrank_fin_fun] at this
    omega
  obtain ⟨m, W', hW', hQW'⟩ := ih _ hlt (Q.restrict W) hW rfl
  have hmap : ((Q.restrict W).restrict W').Equivalent (Q.restrict (W'.map W.subtype)) :=
    (⟨W.subtype, fun _ ↦ rfl⟩ : (Q.restrict W) →qᵢ Q).equivalent_restrict_map
      W.injective_subtype W'
  exact ⟨m + 1, W'.map W.subtype, hmap.anisotropic_iff.mp hW', hQW.trans
    (((QuadraticMap.Equivalent.refl _).prod
      (hQW'.trans ((QuadraticMap.Equivalent.refl _).prod hmap))).trans
      (equivalent_pi_succ_prod (fun _ : Fin (m + 1) ↦ TauCeti.binaryQuadraticForm K 0 0)
        _).symm)⟩

end QuadraticForm

namespace TauCeti

variable {K : Type u} [Field K]
  {V₁ : Type v₁} [AddCommGroup V₁] [Module K V₁]
  {V₂ : Type v₂} [AddCommGroup V₂] [Module K V₂]

/-- **Witt decomposition**, uniqueness (Elman–Karpenko–Merkurjev, Theorem 8.5), in every
characteristic and for arbitrary anisotropic forms: if `m₁ [0, 0] ⊥ A₁ ≅ m₂ [0, 0] ⊥ A₂` with `A₁`
and `A₂` anisotropic, then `m₁ = m₂` and `A₁ ≅ A₂`. So the Witt index and the anisotropic part of a
quadratic form are invariants of its isometry class. -/
theorem eq_and_equivalent_of_equivalent_pi_binaryQuadraticForm_zero_prod
    {A₁ : QuadraticForm K V₁} {A₂ : QuadraticForm K V₂} (hA₁ : A₁.Anisotropic)
    (hA₂ : A₂.Anisotropic) {m₁ m₂ : ℕ}
    (h : ((QuadraticMap.pi fun _ : Fin m₁ ↦ binaryQuadraticForm K 0 0).prod A₁).Equivalent
      ((QuadraticMap.pi fun _ : Fin m₂ ↦ binaryQuadraticForm K 0 0).prod A₂)) :
    m₁ = m₂ ∧ A₁.Equivalent A₂ := by
  induction m₁ generalizing m₂ with
  | zero =>
    cases m₂ with
    | zero =>
      exact ⟨rfl,
        (equivalent_pi_zero_prod _ A₁).symm.trans (h.trans (equivalent_pi_zero_prod _ A₂))⟩
    | succ m₂ =>
      exact absurd (((equivalent_pi_zero_prod _ A₁).symm.trans
        (h.trans (equivalent_pi_succ_prod _ A₂))).anisotropic_iff.mp hA₁)
        (not_anisotropic_binaryQuadraticForm_zero_prod _)
  | succ m₁ ih =>
    cases m₂ with
    | zero =>
      exact absurd (((equivalent_pi_zero_prod _ A₂).symm.trans
        (h.symm.trans (equivalent_pi_succ_prod _ A₁))).anisotropic_iff.mp hA₂)
        (not_anisotropic_binaryQuadraticForm_zero_prod _)
    | succ m₂ =>
      obtain ⟨hm, hA⟩ := ih (equivalent_of_equivalent_binaryQuadraticForm_zero_prod
        ((equivalent_pi_succ_prod _ A₁).symm.trans (h.trans (equivalent_pi_succ_prod _ A₂))))
      exact ⟨congrArg (· + 1) hm, hA⟩

end TauCeti
