/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.ReflectionSubgroup
public import TauCeti.LinearAlgebra.QuadraticForm.Dual
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Low-dimensional Cartan--Dieudonné and Dieudonné's four-dimensional counterexample over `𝔽₂`

Over a field in which `2` is invertible, the Cartan--Dieudonné theorem
(`TauCeti.QuadraticMap.exists_reflectionOrthogonal_list_prod_eq` and
`TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem`) shows that every orthogonal
transformation of a finite-dimensional nondegenerate quadratic space is a product of at most the
dimension many reflections. In characteristic two `polar Q v v = 2 • Q v = 0`, so an orthogonal
reflection `reflectionOrthogonal Q v` in a vector of invertible norm fixes `v` and acts as a
symplectic transvection (or the identity when `polar Q v = 0`).

This file establishes both halves of the sharp dimension boundary due to Dickson, Dieudonné, and
Kneser:

1. **Positive generation without characteristic hypotheses on anisotropic spaces and in dimensions
   at most three:**
   - Over an arbitrary field `K` (including characteristic two), every orthogonal automorphism of a
     quadratic space `(V, Q)` with `Q.radical = ⊥` whose displaced subspace `range (g - 1)` has
     dimension one is a single orthogonal reflection
     (`QuadraticMap.eq_reflectionOrthogonal_of_finrank_range_sub_id_eq_one`).
   - Whenever `Q ((g : V ≃ₗ[K] V) a - a) ≠ 0`, precomposing `g` with the reflection in `g a - a`
     fixes `ker (g - 1) ⊔ (K ∙ a)` and strictly decreases the dimension of `range (g - 1)`
     (`QuadraticMap.finrank_range_sub_id_reflectionOrthogonal_mul_lt`).
   - Consequently, over an arbitrary field `K`, Cartan--Dieudonné holds in full (with the Scherk
     bound `l.length ≤ finrank (range (g - 1)) ≤ finrank V`) both for every finite-dimensional
     anisotropic form (`QuadraticMap.exists_reflectionOrthogonal_list_prod_eq_of_anisotropic`) and
     for every nondegenerate quadratic space of dimension at most three
     (`QuadraticMap.exists_reflectionOrthogonal_list_prod_eq_of_finrank_le_three`,
     `QuadraticMap.reflectionSubgroup_eq_top_of_finrank_le_three`).

2. **Dimension-four counterexample over `𝔽₂` (`ZMod 2`):**
   - For any two anisotropic quadratic forms `Q₁`, `Q₂` over `ZMod 2`, `1 + 1 = 0` prevents a sum
     of two nonzero values from being a unit, so `(Q₁.prod Q₂).reflectionSubgroup` splits as the
     block-diagonal image of `Q₁.reflectionSubgroup.prod Q₂.reflectionSubgroup`
     (`QuadraticMap.reflectionSubgroup_prod_of_anisotropic_zmod_two`), and for any nontrivial
     finite-dimensional anisotropic form `Q` over `ZMod 2`, `(Q.prod Q).reflectionSubgroup` has
     index two in `orthogonalGroup (Q.prod Q)`
     (`QuadraticMap.index_reflectionSubgroup_prod_self_eq_two_of_anisotropic_zmod_two`).
   - In characteristic two, the orthogonal sum of two copies of the anisotropic binary plane
     `u₀² + u₀ u₁ + u₁²` is explicitly isometric to the four-dimensional hyperbolic space
     `QuadraticForm.dualProd R (Fin 2 → R)`, carrying `prodCommOrthogonal` to the coordinate-swap
     isometry `TauCeti.dualProdSwapOrthogonal R`.
   - Over `ZMod 2`, `QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)` is nondegenerate of
     dimension four, its reflection subgroup has index two in its orthogonal group
     (`TauCeti.index_reflectionSubgroup_dualProd_fin_two_zmod_two`), and
     `TauCeti.dualProdSwapOrthogonal (ZMod 2)` cannot be written as a product of reflections of any
     length (`TauCeti.not_exists_reflectionOrthogonal_list_prod_eq_dualProdSwapOrthogonal`). Thus
     neither `exists_reflectionOrthogonal_list_prod_eq` nor `subgroup_eq_top_of_reflection_mem`
     extends to arbitrary fields in dimension four.

## Main definitions

* `TauCeti.dualProdSwapOrthogonal R`: the involutive orthogonal automorphism of
  `QuadraticForm.dualProd R (Fin 2 → R)` induced by swapping the two coordinates of `Fin 2 → R`.

## Main results

* `QuadraticMap.exists_reflectionOrthogonal_list_prod_eq_of_anisotropic` and
  `QuadraticMap.reflectionSubgroup_eq_top_of_anisotropic`: Cartan--Dieudonné for finite-dimensional
  anisotropic forms over any field.
* `QuadraticMap.exists_reflectionOrthogonal_list_prod_eq_of_finrank_le_three` and
  `QuadraticMap.reflectionSubgroup_eq_top_of_finrank_le_three`: Cartan--Dieudonné for nondegenerate
  forms of dimension at most three over any field.
* `QuadraticMap.index_reflectionSubgroup_prod_self_eq_two_of_anisotropic_zmod_two`: for any
  nontrivial finite-dimensional anisotropic form `Q` over `ZMod 2`,
  `(Q.prod Q).reflectionSubgroup` has index two in `orthogonalGroup (Q.prod Q)`.
* `TauCeti.index_reflectionSubgroup_dualProd_fin_two_zmod_two`,
  `TauCeti.dualProdSwapOrthogonal_notMem_reflectionSubgroup_zmod_two`, and
  `TauCeti.not_exists_reflectionOrthogonal_list_prod_eq_dualProdSwapOrthogonal`: Dieudonné's
  four-dimensional counterexample over `ZMod 2`.

## References

* L. E. Dickson, *Linear Groups: With an Exposition of the Galois Field Theory* (1901), §199.
* J. Dieudonné, *La géométrie des groupes classiques* (1955), Chapter II, §10.
* P. Scherk, *On the decomposition of orthogonalities into symmetries*, Proc. Amer. Math. Soc. 1
  (1950), 481–491.
* M. Kneser, *Quadratische Formen* (2002), §4.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §7.
* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*
  (2008), Example 11.5.
-/

public section

namespace QuadraticMap

open TauCeti.QuadraticMap

section Displacement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If an orthogonal transformation `g` fixes `z`, then the reflection in any invertible-norm
displacement `g a - a` also fixes `z`, because `g a - a` is polar-orthogonal to `z`. -/
theorem reflection_sub_apply_of_apply_eq_self (Q : QuadraticForm R M) (g : orthogonalGroup Q)
    (a z : M) [Invertible (Q ((g : M ≃ₗ[R] M) a - a))] (hz : (g : M ≃ₗ[R] M) z = z) :
    reflection Q ((g : M ≃ₗ[R] M) a - a) z = z := by
  refine reflection_apply_of_polar_eq_zero Q ((g : M ≃ₗ[R] M) a - a) ?_
  calc
    polar Q ((g : M ≃ₗ[R] M) a - a) z
        = polar Q ((g : M ≃ₗ[R] M) a) z - polar Q a z := polar_sub_left Q _ _ _
    _ = polar Q ((g : M ≃ₗ[R] M) a) ((g : M ≃ₗ[R] M) z) - polar Q a z := by rw [hz]
    _ = 0 := by rw [polar_apply_of_mem_orthogonalGroup g.2, sub_self]

/-- Over a field, precomposing `g ∈ O(Q)` with the reflection in an anisotropic displacement
`g a - a` strictly decreases the dimension of the displaced subspace `range (g - 1)`. -/
theorem finrank_range_sub_id_reflectionOrthogonal_mul_lt {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (g : orthogonalGroup Q) {a : V}
    (ha : Q ((g : V ≃ₗ[K] V) a - a) ≠ 0) :
    let d := (g : V ≃ₗ[K] V) a - a
    let _ : Invertible (Q d) := invertibleOfNonzero ha
    Module.finrank K
        (LinearMap.range (((reflectionOrthogonal Q d * g : orthogonalGroup Q) :
          V ≃ₗ[K] V).toLinearMap - LinearMap.id)) <
      Module.finrank K
        (LinearMap.range ((g : V ≃ₗ[K] V).toLinearMap - LinearMap.id)) := by
  intro d _
  set f : V →ₗ[K] V := (g : V ≃ₗ[K] V).toLinearMap - LinearMap.id
  set f' : V →ₗ[K] V :=
    ((reflectionOrthogonal Q d * g : orthogonalGroup Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id
  have hker_le : LinearMap.ker f ≤ LinearMap.ker f' := fun z hz ↦ by
    have hgz : (g : V ≃ₗ[K] V) z = z := sub_eq_zero.mp (LinearMap.mem_ker.mp hz)
    refine LinearMap.mem_ker.mpr (sub_eq_zero.mpr ?_)
    simpa [Subgroup.coe_mul, coe_reflectionOrthogonal, hgz] using
      reflection_sub_apply_of_apply_eq_self Q g a z hgz
  have ha_mem : a ∈ LinearMap.ker f' := by
    refine LinearMap.mem_ker.mpr (sub_eq_zero.mpr ?_)
    simpa [Subgroup.coe_mul, coe_reflectionOrthogonal, d] using
      reflection_sub_apply_eq_of_map_eq Q ((g : V ≃ₗ[K] V) a) a
        (map_app_of_mem_orthogonalGroup g.2 a)
  have ha_notMem : a ∉ LinearMap.ker f := fun hmem ↦ by
    have hfa : (g : V ≃ₗ[K] V) a - a = 0 := LinearMap.mem_ker.mp hmem
    exact ha (by rw [hfa, Q.map_zero])
  have hker_lt : Module.finrank K (LinearMap.ker f) < Module.finrank K (LinearMap.ker f') :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hker_le fun hge ↦ ha_notMem (hge ha_mem))
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hrank' := LinearMap.finrank_range_add_finrank_ker f'
  omega

end Displacement

section LowDimAndAnisotropic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If `g - 1` has zero-dimensional range on a finite-dimensional space, then `g = 1`. -/
private theorem eq_one_of_finrank_range_sub_id_eq_zero [FiniteDimensional K V]
    {Q : QuadraticForm K V} (g : orthogonalGroup Q)
    (hrange : Module.finrank K
      (LinearMap.range ((g : V ≃ₗ[K] V).toLinearMap - LinearMap.id)) = 0) :
    g = 1 := by
  set f : V →ₗ[K] V := (g : V ≃ₗ[K] V).toLinearMap - LinearMap.id
  have hbot : LinearMap.range f = ⊥ := Submodule.finrank_eq_zero.mp hrange
  refine Subtype.ext <| LinearEquiv.ext fun x ↦ sub_eq_zero.mp ?_
  have hx : f x ∈ (⊥ : Submodule K V) := hbot ▸ LinearMap.mem_range_self f x
  simpa [f] using hx

/-- **Rank-one orthogonal displacements over an arbitrary field are reflections.** Over any field
`K` (including characteristic two), if `Q` has trivial radical and `range (g - 1)` has dimension
one, then `g` is the reflection in any nonzero vector of `range (g - 1)`. -/
theorem eq_reflectionOrthogonal_of_finrank_range_sub_id_eq_one (Q : QuadraticForm K V)
    (hrad : Q.radical = ⊥) (g : orthogonalGroup Q)
    (hrange : Module.finrank K
      (LinearMap.range ((g : V ≃ₗ[K] V).toLinearMap - LinearMap.id)) = 1) :
    ∃ (v : V) (_ : Invertible (Q v)), reflectionOrthogonal Q v = g := by
  let f : V →ₗ[K] V := (g : V ≃ₗ[K] V).toLinearMap - LinearMap.id
  obtain ⟨⟨v, x₁, hx₁⟩, hv_ne, hv_span⟩ := (finrank_eq_one_iff' (K := K)).mp hrange
  have hv0 : v ≠ 0 := fun h ↦ hv_ne (Subtype.ext h)
  have hpolar_ne {x : V} {c : K} (hc : c ≠ 0) (hx : f x = c • v) :
      polar Q v x = -(c * Q v) := by
    have hgx : (g : V ≃ₗ[K] V) x = x + c • v := eq_add_of_sub_eq' hx
    have hQ := map_app_of_mem_orthogonalGroup g.2 x
    rw [hgx, QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, polar_comm Q x v,
      smul_eq_mul, smul_eq_mul] at hQ
    have hmul : c * (c * Q v + polar Q v x) = 0 := by linear_combination hQ
    exact eq_neg_of_add_eq_zero_right ((mul_eq_zero.mp hmul).resolve_left hc)
  have hpolar (x : V) (c : K) (hx : f x = c • v) : polar Q v x = -(c * Q v) := by
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul] at hx
      have h1 := hpolar_ne one_ne_zero (x := x₁ + x) (by rw [map_add, hx₁, hx, add_zero, one_smul])
      have h2 := hpolar_ne one_ne_zero (x := x₁) (by rw [hx₁, one_smul])
      rw [polar_add_right, h2] at h1
      simpa using add_eq_left.mp h1
    · exact hpolar_ne hc hx
  have hQv : Q v ≠ 0 := fun hQv0 ↦ hv0 <| by
    have hmem : v ∈ Q.radical := ⟨hQv0, LinearMap.ext fun x ↦ by
      obtain ⟨c, hc⟩ := hv_span ⟨f x, LinearMap.mem_range_self f x⟩
      rw [polarBilin_apply_apply, hpolar x c (congrArg Subtype.val hc).symm, hQv0, mul_zero,
        neg_zero, LinearMap.zero_apply]⟩
    rwa [hrad, Submodule.mem_bot] at hmem
  let _ : Invertible (Q v) := invertibleOfNonzero hQv
  refine ⟨v, inferInstance, Subtype.ext <| LinearEquiv.ext fun x ↦ ?_⟩
  obtain ⟨c, hc⟩ := hv_span ⟨f x, LinearMap.mem_range_self f x⟩
  have hfx : f x = c • v := (congrArg Subtype.val hc).symm
  have hgx : (g : V ≃ₗ[K] V) x = x + c • v := eq_add_of_sub_eq' hfx
  rw [coe_reflectionOrthogonal, reflection_apply_eq_sub_div, hpolar x c hfx, neg_div,
    mul_div_cancel_right₀ c hQv, neg_smul, sub_neg_eq_add, hgx]

/-- Core strong-induction engine over any field: if `Q.radical = ⊥` and no `g ∈ O(Q)` can have a
totally isotropic displaced subspace `range (g - 1)` of dimension at least two, then every
`g ∈ O(Q)` is a product of at most `finrank (range (g - 1))` orthogonal reflections. -/
private theorem exists_reflectionOrthogonal_list_prod_le_finrank_range [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hrad : Q.radical = ⊥)
    (hno_ti : ∀ g : orthogonalGroup Q,
      Q.IsTotallyIsotropic
        (LinearMap.range ((g : V ≃ₗ[K] V).toLinearMap - LinearMap.id)) →
      Module.finrank K
        (LinearMap.range ((g : V ≃ₗ[K] V).toLinearMap - LinearMap.id)) ≤ 1)
    (g : orthogonalGroup Q) :
    ∃ l : List (orthogonalGroup Q),
      (∀ r ∈ l, ∃ (v : V) (_ : Invertible (Q v)), reflectionOrthogonal Q v = r) ∧
      l.length ≤ Module.finrank K
        (LinearMap.range ((g : V ≃ₗ[K] V).toLinearMap - LinearMap.id)) ∧
      l.prod = g := by
  set k := Module.finrank K
    (LinearMap.range ((g : V ≃ₗ[K] V).toLinearMap - LinearMap.id)) with hk
  clear_value k
  induction k using Nat.strong_induction_on generalizing g with
  | ind k ih =>
    by_cases hti : Q.IsTotallyIsotropic
        (LinearMap.range ((g : V ≃ₗ[K] V).toLinearMap - LinearMap.id))
    · have hk1 : k ≤ 1 := hk ▸ hno_ti g hti
      interval_cases k
      · exact ⟨[], by simp, Nat.zero_le _,
          (eq_one_of_finrank_range_sub_id_eq_zero g hk.symm).symm⟩
      · obtain ⟨v, hv, hrv⟩ :=
          eq_reflectionOrthogonal_of_finrank_range_sub_id_eq_one Q hrad g hk.symm
        exact ⟨[reflectionOrthogonal Q v], fun r hr ↦ by
          rw [List.mem_singleton] at hr
          exact ⟨v, hv, hr.symm⟩, le_rfl, by simp [hrv]⟩
    · rw [isTotallyIsotropic_iff] at hti
      push Not at hti
      obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hti
      let d := (g : V ≃ₗ[K] V) a - a
      have hd : Q d ≠ 0 := ha
      let _ : Invertible (Q d) := invertibleOfNonzero hd
      have hlt : Module.finrank K
          (LinearMap.range (((reflectionOrthogonal Q d * g : orthogonalGroup Q) :
            V ≃ₗ[K] V).toLinearMap - LinearMap.id)) < k :=
        hk ▸ finrank_range_sub_id_reflectionOrthogonal_mul_lt Q g hd
      obtain ⟨l, hlrefl, hllen, hlprod⟩ :=
        ih _ hlt (reflectionOrthogonal Q d * g) rfl
      refine ⟨reflectionOrthogonal Q d :: l, ?_, by simp only [List.length_cons]; omega, ?_⟩
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨d, inferInstance, rfl⟩
        · exact hlrefl r hr
      · rw [List.prod_cons, hlprod, ← mul_assoc, reflectionOrthogonal_mul_self, one_mul]

/-- **Cartan--Dieudonné for anisotropic forms over an arbitrary field.** Every orthogonal
automorphism of a finite-dimensional anisotropic quadratic space over any field `K` (including
characteristic two) is a product of at most `Module.finrank K V` reflections. -/
theorem exists_reflectionOrthogonal_list_prod_eq_of_anisotropic [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Anisotropic) (g : orthogonalGroup Q) :
    ∃ l : List (orthogonalGroup Q),
      (∀ r ∈ l, ∃ (v : V) (_ : Invertible (Q v)), reflectionOrthogonal Q v = r) ∧
      l.length ≤ Module.finrank K V ∧ l.prod = g := by
  obtain ⟨l, hlrefl, hllen, hlprod⟩ :=
    exists_reflectionOrthogonal_list_prod_le_finrank_range hQ.radical_eq_bot
      (fun g' hti ↦ by
        have hbot : LinearMap.range ((g' : V ≃ₗ[K] V).toLinearMap - LinearMap.id) = ⊥ :=
          (Submodule.eq_bot_iff _).mpr fun x hx ↦ hQ x (hti.apply_eq_zero hx)
        rw [hbot, finrank_bot]
        exact Nat.zero_le 1) g
  exact ⟨l, hlrefl, hllen.trans (Submodule.finrank_le _), hlprod⟩

/-- Reflections generate the full orthogonal group of any finite-dimensional anisotropic quadratic
form over an arbitrary field. -/
theorem reflectionSubgroup_eq_top_of_anisotropic [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Anisotropic) :
    Q.reflectionSubgroup = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨l, hlrefl, _, hlprod⟩ := Q.exists_reflectionOrthogonal_list_prod_eq_of_anisotropic hQ g
  exact (Q.mem_reflectionSubgroup_iff_exists_list_prod).mpr ⟨l, hlrefl, hlprod⟩

/-- **Cartan--Dieudonné in dimensions at most three over an arbitrary field.** For every
nondegenerate quadratic form `Q` on a vector space of dimension at most three over any field `K`
(including characteristic two), every orthogonal automorphism is a product of at most
`Module.finrank K V` reflections. -/
theorem exists_reflectionOrthogonal_list_prod_eq_of_finrank_le_three [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank K V ≤ 3) (g : orthogonalGroup Q) :
    ∃ l : List (orthogonalGroup Q),
      (∀ r ∈ l, ∃ (v : V) (_ : Invertible (Q v)), reflectionOrthogonal Q v = r) ∧
      l.length ≤ Module.finrank K V ∧ l.prod = g := by
  obtain ⟨l, hlrefl, hllen, hlprod⟩ :=
    exists_reflectionOrthogonal_list_prod_le_finrank_range hQ.radical_eq_bot
      (fun g' hti ↦ by
        set W := LinearMap.range ((g' : V ≃ₗ[K] V).toLinearMap - LinearMap.id)
        obtain ⟨U, hUW⟩ := Submodule.exists_isCompl W
        have hle : Module.finrank K W ≤ Module.finrank K U :=
          hti.finrank_le_of_codisjoint hQ hUW.symm.codisjoint
        have hsum : Module.finrank K W + Module.finrank K U = Module.finrank K V := by
          have h := Submodule.finrank_sup_add_finrank_inf_eq W U
          rw [hUW.sup_eq_top, hUW.inf_eq_bot, finrank_top, finrank_bot, add_zero] at h
          exact h.symm
        omega) g
  exact ⟨l, hlrefl, hllen.trans (Submodule.finrank_le _), hlprod⟩

/-- For every nondegenerate quadratic form on a vector space of dimension at most three over an
arbitrary field, reflections generate the full orthogonal group. -/
theorem reflectionSubgroup_eq_top_of_finrank_le_three [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank K V ≤ 3) :
    Q.reflectionSubgroup = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨l, hlrefl, _, hlprod⟩ :=
    Q.exists_reflectionOrthogonal_list_prod_eq_of_finrank_le_three hQ hdim g
  exact (Q.mem_reflectionSubgroup_iff_exists_list_prod).mpr ⟨l, hlrefl, hlprod⟩

end LowDimAndAnisotropic

section ZModTwoAnisotropicProd

/-- For any two anisotropic quadratic forms `Q₁`, `Q₂` over `ZMod 2`, if `Q₁ x₁ + Q₂ x₂` is a
unit, then one of `x₁` and `x₂` vanishes, because `1 + 1 = 0` in `ZMod 2`. -/
theorem eq_zero_or_eq_zero_of_isUnit_add_of_anisotropic_zmod_two {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]
    (Q₁ : QuadraticForm (ZMod 2) V₁) (Q₂ : QuadraticForm (ZMod 2) V₂)
    (hQ₁ : Q₁.Anisotropic) (hQ₂ : Q₂.Anisotropic) {x₁ : V₁} {x₂ : V₂}
    (hunit : IsUnit (Q₁ x₁ + Q₂ x₂)) :
    x₁ = 0 ∨ x₂ = 0 := by
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 (Q₁ x₁) with h₁ | h₁
  · exact .inl (hQ₁ x₁ h₁)
  · rcases h01 (Q₂ x₂) with h₂ | h₂
    · exact .inr (hQ₂ x₂ h₂)
    · rw [h₁, h₂] at hunit
      exact absurd hunit.ne_zero (by decide)

/-- Over `ZMod 2`, the reflection subgroup of the orthogonal sum of two anisotropic forms is the
block-diagonal image of the product of their reflection subgroups. -/
theorem reflectionSubgroup_prod_of_anisotropic_zmod_two {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]
    (Q₁ : QuadraticForm (ZMod 2) V₁) (Q₂ : QuadraticForm (ZMod 2) V₂)
    (hQ₁ : Q₁.Anisotropic) (hQ₂ : Q₂.Anisotropic) :
    (Q₁.prod Q₂).reflectionSubgroup =
      (Q₁.reflectionSubgroup.prod Q₂.reflectionSubgroup).map (orthogonalGroupProd Q₁ Q₂) :=
  reflectionSubgroup_prod_eq_map Q₁ Q₂
    (fun _ _ ↦ eq_zero_or_eq_zero_of_isUnit_add_of_anisotropic_zmod_two Q₁ Q₂ hQ₁ hQ₂)

/-- For any nontrivial finite-dimensional anisotropic quadratic space `(V, Q)` over `ZMod 2`,
`(Q.prod Q).reflectionSubgroup` has index two in `orthogonalGroup (Q.prod Q)`. -/
theorem index_reflectionSubgroup_prod_self_eq_two_of_anisotropic_zmod_two {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : Q.Anisotropic) :
    (Q.prod Q).reflectionSubgroup.index = 2 :=
  Q.index_reflectionSubgroup_prod_self_eq_two
    (fun x hx ↦ isUnit_iff_ne_zero.mpr fun h0 ↦ hx (hQ x h0))
    (fun _ _ ↦ eq_zero_or_eq_zero_of_isUnit_add_of_anisotropic_zmod_two Q Q hQ hQ)
    (Q.reflectionSubgroup_eq_top_of_anisotropic hQ)

end ZModTwoAnisotropicProd

end QuadraticMap

open QuadraticMap TauCeti.QuadraticMap

namespace TauCeti

section CounterexampleDimFour

/-- The involutive orthogonal automorphism of `QuadraticForm.dualProd R (Fin 2 → R)` induced by
swapping the two coordinates of `Fin 2 → R`. -/
def dualProdSwapOrthogonal (R : Type*) [CommSemiring R] :
    orthogonalGroup (QuadraticForm.dualProd R (Fin 2 → R)) :=
  (orthogonalGroupEquivIsometryEquiv (QuadraticForm.dualProd R (Fin 2 → R))).symm
    (QuadraticForm.dualProdIsometry (LinearEquiv.funCongrLeft R R (Equiv.swap (0 : Fin 2) 1)))

/-- `dualProdSwapOrthogonal R` acts on the dual functional by precomposing with `Equiv.swap 0 1`. -/
@[simp]
theorem dualProdSwapOrthogonal_apply_fst_apply (R : Type*) [CommSemiring R]
    (p : Module.Dual R (Fin 2 → R) × (Fin 2 → R)) (z : Fin 2 → R) :
    (((dualProdSwapOrthogonal R :
      (Module.Dual R (Fin 2 → R) × (Fin 2 → R)) ≃ₗ[R]
        Module.Dual R (Fin 2 → R) × (Fin 2 → R)) p).1) z =
      p.1 (z ∘ Equiv.swap (0 : Fin 2) 1) := by
  simp [dualProdSwapOrthogonal]
  rfl

/-- `dualProdSwapOrthogonal R` acts on the vector component by precomposing with
`Equiv.swap 0 1`. -/
@[simp]
theorem dualProdSwapOrthogonal_apply_snd_apply (R : Type*) [CommSemiring R]
    (p : Module.Dual R (Fin 2 → R) × (Fin 2 → R)) (i : Fin 2) :
    (((dualProdSwapOrthogonal R :
      (Module.Dual R (Fin 2 → R) × (Fin 2 → R)) ≃ₗ[R]
        Module.Dual R (Fin 2 → R) × (Fin 2 → R)) p).2) i =
      p.2 (Equiv.swap (0 : Fin 2) 1 i) := by
  simp [dualProdSwapOrthogonal]
  rfl

/-- `dualProdSwapOrthogonal R` has order dividing two in the orthogonal group. -/
@[simp]
theorem dualProdSwapOrthogonal_mul_self (R : Type*) [CommSemiring R] :
    dualProdSwapOrthogonal R * dualProdSwapOrthogonal R = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro p
  refine Prod.ext (LinearMap.ext fun z ↦ ?_) (funext fun i ↦ ?_)
  · simp [Function.comp_def]
  · simp

/-- `dualProdSwapOrthogonal R` is its own inverse in the orthogonal group. -/
@[simp]
theorem dualProdSwapOrthogonal_inv (R : Type*) [CommSemiring R] :
    (dualProdSwapOrthogonal R)⁻¹ = dualProdSwapOrthogonal R :=
  inv_eq_of_mul_eq_one_left (dualProdSwapOrthogonal_mul_self R)

/-- Auxiliary binary norm form `u 0 ^ 2 + u 0 * u 1 + u 1 ^ 2` on `Fin 2 → R`. -/
private def anisotropicPlaneAux (R : Type*) [CommSemiring R] : QuadraticForm R (Fin 2 → R) :=
  (QuadraticMap.sq (R := R)).comp (LinearMap.proj (0 : Fin 2)) +
    QuadraticMap.linMulLin (LinearMap.proj (0 : Fin 2)) (LinearMap.proj (1 : Fin 2)) +
    (QuadraticMap.sq (R := R)).comp (LinearMap.proj (1 : Fin 2))

private theorem anisotropicPlaneAux_apply {R : Type*} [CommSemiring R] (u : Fin 2 → R) :
    anisotropicPlaneAux R u = u 0 * u 0 + u 0 * u 1 + u 1 * u 1 := by
  simp [anisotropicPlaneAux]

private theorem anisotropic_anisotropicPlaneAux_zmod_two :
    (anisotropicPlaneAux (ZMod 2)).Anisotropic := by
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  intro u hu
  rw [anisotropicPlaneAux_apply] at hu
  rcases h01 (u 0) with h0 | h0 <;> rcases h01 (u 1) with h1 | h1
  · ext i
    fin_cases i <;> assumption
  · rw [h0, h1] at hu
    exact absurd hu (by decide)
  · rw [h0, h1] at hu
    exact absurd hu (by decide)
  · rw [h0, h1] at hu
    exact absurd hu (by decide)

/-- Underlying linear equivalence identifying `(Fin 2 → R) × (Fin 2 → R)` with
`Module.Dual R (Fin 2 → R) × (Fin 2 → R)` in characteristic two. -/
private def anisotropicPlaneProdLinearEquivDualProd (R : Type*) [CommRing R] [CharP R 2] :
    ((Fin 2 → R) × (Fin 2 → R)) ≃ₗ[R] Module.Dual R (Fin 2 → R) × (Fin 2 → R) where
  toFun uv :=
    ((uv.1 0 + uv.2 1) • LinearMap.proj (0 : Fin 2) +
        (uv.1 1 + uv.2 0) • LinearMap.proj (1 : Fin 2),
      ![uv.1 0 + uv.1 1 + uv.2 1, uv.1 1 + uv.2 0 + uv.2 1])
  invFun fx :=
    (![fx.1 (Pi.single 0 1) + fx.1 (Pi.single 1 1) + fx.2 1, fx.1 (Pi.single 0 1) + fx.2 0],
      ![fx.1 (Pi.single 0 1) + fx.1 (Pi.single 1 1) + fx.2 0, fx.1 (Pi.single 1 1) + fx.2 1])
  map_add' p q := by
    refine Prod.ext (LinearMap.ext fun z ↦ ?_) (funext fun i ↦ ?_)
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
      ring
    · fin_cases i <;> simp <;> ring
  map_smul' r p := by
    refine Prod.ext (LinearMap.ext fun z ↦ ?_) (funext fun i ↦ ?_)
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · fin_cases i <;> simp <;> ring
  left_inv uv := by
    have h2 (x : R) : 2 * x = 0 := by rw [CharTwo.two_eq_zero, zero_mul]
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
    · fin_cases i <;> simp
      · linear_combination h2 (uv.1 1 + uv.2 0 + uv.2 1)
      · linear_combination h2 (uv.1 0 + uv.2 1)
    · fin_cases i <;> simp
      · linear_combination h2 (uv.1 0 + uv.1 1 + uv.2 1)
      · linear_combination h2 (uv.1 1 + uv.2 0)
  right_inv fx := by
    have h2 (x : R) : 2 * x = 0 := by rw [CharTwo.two_eq_zero, zero_mul]
    refine Prod.ext ?_ (funext fun i ↦ ?_)
    · ext i
      fin_cases i <;> simp
      · linear_combination h2 (fx.1 (Pi.single 1 1) + fx.2 1)
      · linear_combination h2 (fx.1 (Pi.single 0 1) + fx.2 0)
    · fin_cases i <;> simp
      · linear_combination h2 (fx.1 (Pi.single 0 1) + fx.1 (Pi.single 1 1) + fx.2 1)
      · linear_combination h2 (fx.1 (Pi.single 0 1) + fx.1 (Pi.single 1 1) + fx.2 0)

/-- In characteristic two, the orthogonal sum of two copies of `u₀² + u₀ u₁ + u₁²` is isometric to
the four-dimensional hyperbolic space `QuadraticForm.dualProd R (Fin 2 → R)`. -/
private def anisotropicPlaneProdEquivDualProd (R : Type*) [CommRing R] [CharP R 2] :
    ((anisotropicPlaneAux R).prod (anisotropicPlaneAux R)).IsometryEquiv
      (QuadraticForm.dualProd R (Fin 2 → R)) where
  toLinearEquiv := anisotropicPlaneProdLinearEquivDualProd R
  map_app' uv := by
    have h2 : (2 : R) * (uv.1 0 * uv.2 1 + uv.1 1 * uv.2 0 + uv.1 1 * uv.2 1) = 0 := by
      rw [CharTwo.two_eq_zero, zero_mul]
    simp only [anisotropicPlaneProdLinearEquivDualProd, QuadraticForm.dualProd_apply,
      QuadraticMap.prod_apply, anisotropicPlaneAux_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_eq_mul]
    linear_combination h2

private theorem anisotropicPlaneProdEquivDualProd_toLinearEquiv_apply {R : Type*}
    [CommRing R] [CharP R 2] (uv : (Fin 2 → R) × (Fin 2 → R)) :
    (anisotropicPlaneProdEquivDualProd R).toLinearEquiv uv =
      ((uv.1 0 + uv.2 1) • LinearMap.proj (0 : Fin 2) +
          (uv.1 1 + uv.2 0) • LinearMap.proj (1 : Fin 2),
        ![uv.1 0 + uv.1 1 + uv.2 1, uv.1 1 + uv.2 0 + uv.2 1]) :=
  rfl

private theorem anisotropicPlaneProdEquivDualProd_toLinearEquiv_symm_apply {R : Type*}
    [CommRing R] [CharP R 2] (fx : Module.Dual R (Fin 2 → R) × (Fin 2 → R)) :
    (anisotropicPlaneProdEquivDualProd R).toLinearEquiv.symm fx =
      (![fx.1 (Pi.single 0 1) + fx.1 (Pi.single 1 1) + fx.2 1, fx.1 (Pi.single 0 1) + fx.2 0],
        ![fx.1 (Pi.single 0 1) + fx.1 (Pi.single 1 1) + fx.2 0, fx.1 (Pi.single 1 1) + fx.2 1]) :=
  rfl

/-- Under `anisotropicPlaneProdEquivDualProd R`, swapping the two anisotropic binary summands
corresponds to swapping the two hyperbolic planes via `dualProdSwapOrthogonal R`. -/
private theorem orthogonalGroupCongr_anisotropicPlaneProdEquivDualProd_prodCommOrthogonal
    (R : Type*) [CommRing R] [CharP R 2] :
    (anisotropicPlaneProdEquivDualProd R).orthogonalGroupCongr
        (anisotropicPlaneAux R).prodCommOrthogonal =
      dualProdSwapOrthogonal R := by
  have h2 (x : R) : 2 * x = 0 := by rw [CharTwo.two_eq_zero, zero_mul]
  have hswap0 : (Pi.single (0 : Fin 2) (1 : R)) ∘ Equiv.swap (0 : Fin 2) 1 = Pi.single 1 1 := by
    ext j
    fin_cases j <;> simp
  have hswap1 : (Pi.single (1 : Fin 2) (1 : R)) ∘ Equiv.swap (0 : Fin 2) 1 = Pi.single 0 1 := by
    ext j
    fin_cases j <;> simp
  apply Subtype.ext
  apply LinearEquiv.ext
  intro fx
  rw [IsometryEquiv.coe_orthogonalGroupCongr_apply,
    anisotropicPlaneProdEquivDualProd_toLinearEquiv_symm_apply, prodCommOrthogonal_apply,
    anisotropicPlaneProdEquivDualProd_toLinearEquiv_apply]
  refine Prod.ext ?_ (funext fun i ↦ ?_)
  · ext i
    fin_cases i
    · simp [hswap0]
      linear_combination h2 (fx.1 (Pi.single 0 1) + fx.2 0)
    · simp [hswap1]
      linear_combination h2 (fx.1 (Pi.single 1 1) + fx.2 1)
  · fin_cases i
    · simp
      linear_combination h2 (fx.1 (Pi.single 0 1) + fx.1 (Pi.single 1 1) + fx.2 0)
    · simp
      linear_combination h2 (fx.1 (Pi.single 0 1) + fx.1 (Pi.single 1 1) + fx.2 1)

/-- **Dieudonné's index-two theorem in dimension four over `𝔽₂`.** On the four-dimensional
hyperbolic space `QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)`, the subgroup generated by
orthogonal reflections has index two in the orthogonal group. -/
theorem index_reflectionSubgroup_dualProd_fin_two_zmod_two :
    (QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)).reflectionSubgroup.index = 2 := by
  rw [← (anisotropicPlaneProdEquivDualProd (ZMod 2)).index_reflectionSubgroup_eq]
  exact index_reflectionSubgroup_prod_self_eq_two_of_anisotropic_zmod_two
    (anisotropicPlaneAux (ZMod 2)) anisotropic_anisotropicPlaneAux_zmod_two

/-- On `QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)`, orthogonal reflections do not generate
the full orthogonal group. -/
theorem reflectionSubgroup_dualProd_fin_two_zmod_two_ne_top :
    (QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)).reflectionSubgroup ≠ ⊤ := by
  intro htop
  have hidx := index_reflectionSubgroup_dualProd_fin_two_zmod_two
  rw [htop, Subgroup.index_top] at hidx
  omega

/-- **Explicit witness outside the reflection subgroup in dimension four over `𝔽₂`.** Swapping the
two hyperbolic planes via `dualProdSwapOrthogonal (ZMod 2)` gives an orthogonal transformation not
in `(QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)).reflectionSubgroup`. -/
theorem dualProdSwapOrthogonal_notMem_reflectionSubgroup_zmod_two :
    dualProdSwapOrthogonal (ZMod 2) ∉
      (QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)).reflectionSubgroup := by
  rw [← orthogonalGroupCongr_anisotropicPlaneProdEquivDualProd_prodCommOrthogonal (ZMod 2),
    IsometryEquiv.mem_reflectionSubgroup_orthogonalGroupCongr_iff]
  exact (anisotropicPlaneAux (ZMod 2)).prodCommOrthogonal_notMem_reflectionSubgroup fun _ _ ↦
    eq_zero_or_eq_zero_of_isUnit_add_of_anisotropic_zmod_two
      (anisotropicPlaneAux (ZMod 2)) (anisotropicPlaneAux (ZMod 2))
      anisotropic_anisotropicPlaneAux_zmod_two anisotropic_anisotropicPlaneAux_zmod_two

/-- `dualProdSwapOrthogonal (ZMod 2)` cannot be written as the product of any finite list of
orthogonal reflections on `QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)`. -/
theorem not_exists_reflectionOrthogonal_list_prod_eq_dualProdSwapOrthogonal :
    ¬ ∃ l : List (orthogonalGroup (QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2))),
        (∀ r ∈ l, ∃ (v : Module.Dual (ZMod 2) (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
          (_ : Invertible (QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2) v)),
          reflectionOrthogonal (QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2)) v = r) ∧
        l.prod = dualProdSwapOrthogonal (ZMod 2) := by
  rw [← mem_reflectionSubgroup_iff_exists_list_prod]
  exact dualProdSwapOrthogonal_notMem_reflectionSubgroup_zmod_two

/-- **Failure of Cartan--Dieudonné in dimension four over `𝔽₂`.** There exists a four-dimensional
nondegenerate quadratic space over `ZMod 2` and an orthogonal automorphism that is not a product of
reflections, showing that `[NeZero (2 : K)]` cannot be omitted from
`TauCeti.QuadraticMap.exists_reflectionOrthogonal_list_prod_eq` or
`TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem`. -/
theorem exists_nondegenerate_finrank_four_not_exists_reflectionOrthogonal_list_prod_eq :
    ∃ (Q : QuadraticForm (ZMod 2)
        (Module.Dual (ZMod 2) (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))),
      Q.Nondegenerate ∧
      Module.finrank (ZMod 2)
        (Module.Dual (ZMod 2) (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) = 4 ∧
      Q.reflectionSubgroup ≠ ⊤ ∧
      ∃ g : orthogonalGroup Q,
        ¬ ∃ l : List (orthogonalGroup Q),
          (∀ r ∈ l, ∃ (v : Module.Dual (ZMod 2) (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
            (_ : Invertible (Q v)), reflectionOrthogonal Q v = r) ∧
          l.prod = g :=
  ⟨QuadraticForm.dualProd (ZMod 2) (Fin 2 → ZMod 2),
    nondegenerate_dualProd_pi (ZMod 2) (Fin 2),
    by rw [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_fin_fun],
    reflectionSubgroup_dualProd_fin_two_zmod_two_ne_top,
    dualProdSwapOrthogonal (ZMod 2),
    not_exists_reflectionOrthogonal_list_prod_eq_dualProdSwapOrthogonal⟩

end CounterexampleDimFour

end TauCeti
