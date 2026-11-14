/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Hyperbolic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.IsotropicPoints
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Generation of the special unitary group by Siegel transformations

Let `σ` be a nontrivial involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q ^ σ)ᵀ = ε • Q`, and write `B(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` for its sesquilinear form. Assume
the two trace hypotheses of `Matrix.isPretransitive_isotropicPoints` (`t ↦ t + ε σ(t)` is onto
`{s | σ(s) = ε s}` and has a nonzero kernel element) together with surjectivity of the norm
`b ↦ b * σ(b)` onto `{t | σ(t) = t}`. This file proves that the admissible Siegel transformations
`Matrix.siegelTransvection Q σ ε u w c` generate `Matrix.specialIsometryGroup Q σ`
(`Matrix.eq_top_of_siegelTransvection_mem`).

The proof inducts on the dimension of a nondegenerate subspace `U ≤ K^n` whose orthogonal
complement `F` is fixed pointwise by `g ∈ Q.specialIsometryGroup σ`:

* **Dimension `0`:** `U = ⊥`, so `g = 1`.
* **Dimension `1`:** `U = K ∙ w₀` with `B(w₀, w₀) ≠ 0`, and `g *ᵥ w₀ = μ • w₀`. Writing `g` as a
  rank-one perturbation `1 - ((1 - μ) • w₀) (B(w₀, w₀)⁻¹ σ(w₀)ᵀ Q)` and evaluating
  `TauCeti.det_one_sub_vecMulVec` gives `1 = g.det = μ`, so `g = 1`.
* **Dimension `2`:** `U` is a hyperbolic plane `K ∙ u ⊔ K ∙ v` (`B(u, v) = 1`). Unitary
  transvections in `U` move `g *ᵥ u` to `μ • u` and then `g₁ *ᵥ v` to `σ(μ)⁻¹ • v`; a two-factor
  rank-one determinant calculation gives `1 = μ * σ(μ)⁻¹`, so `σ(μ) = μ`, and Whitehead's
  four-transvection hyperbolic scaling `Matrix.exists_unitaryTransvection_hyperbolic_scaling`
  reduces to `1`.
* **Dimension at least `3`:** `U = P ⊔ W` for a hyperbolic plane `P = K ∙ u ⊔ K ∙ v` and its
  orthogonal complement `W` in `U`, which is nondegenerate of positive dimension and therefore
  contains an anisotropic vector `w₀`. Rescaling `w₀` via the norm hypothesis supplies admissible
  Siegel transformations `S(u, α • w₀, c)` for arbitrary `c`, allowing Siegel transformations in
  `U` (which fix `F` pointwise) to send `g *ᵥ u` to `u` and then `g' *ᵥ v` to `v`, reducing to
  `(F ⊔ P, W)`.

`TauCeti/LinearAlgebra/Matrix/SpecialLinearGroup/Isometry/Generation.lean` combines this with the
decomposition of Siegel transformations into unitary transvections to prove that the unitary
transvection subgroups generate `Q.specialIsometryGroup σ`.

## Main results

* `Matrix.eq_top_of_siegelTransvection_mem`: any subgroup of `Q.specialIsometryGroup σ` containing
  all admissible Siegel transformations equals `⊤`.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, 3rd ed., Springer (1971), Chapter II, §4.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

namespace Matrix

section Nondegenerate

variable {n K : Type*} [Fintype n] [Field K] {Q : Matrix n n K} {σ : K →+* K} {ε : K}

private abbrev IsNondegenerateSubmodule (Q : Matrix n n K) (σ : K →+* K)
    (U : Submodule K (n → K)) : Prop :=
  ∀ x ∈ U, (∀ y ∈ U, (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0) → x = 0

private theorem isNondegenerateSubmodule_bot : IsNondegenerateSubmodule Q σ ⊥ :=
  fun _ hx _ ↦ (Submodule.mem_bot K).mp hx

private theorem isNondegenerateSubmodule_sup {F P : Submodule K (n → K)}
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (horth : ∀ f ∈ F, ∀ p ∈ P, (σ ∘ f) ⬝ᵥ (Q *ᵥ p) = 0)
    (hF : IsNondegenerateSubmodule Q σ F) (hP : IsNondegenerateSubmodule Q σ P) :
    IsNondegenerateSubmodule Q σ (F ⊔ P) := by
  intro x hx hx0
  obtain ⟨f, hfF, p, hpP, rfl⟩ := Submodule.mem_sup.mp hx
  have hf0 : f = 0 := hF f hfF fun f' hf'F ↦ by
    have h := hx0 f' (Submodule.mem_sup_left hf'F)
    rw [map_comp_add, add_dotProduct,
      (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f' hf'F p hpP), add_zero] at h
    exact h
  subst hf0
  rw [zero_add] at hx0 ⊢
  exact hP p hpP fun p' hp'P ↦ hx0 p' (Submodule.mem_sup_right hp'P)

end Nondegenerate

section Generation

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-! ### Pointwise fixing on orthogonal decompositions -/

private def FixesOn (F : Submodule K (n → K)) (g : Q.specialIsometryGroup σ) : Prop :=
  ∀ f ∈ F, ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ f = f

private theorem fixesOn_mul {F : Submodule K (n → K)} {g₁ g₂ : Q.specialIsometryGroup σ}
    (h₁ : FixesOn F g₁) (h₂ : FixesOn F g₂) : FixesOn F (g₁ * g₂) := fun f hf ↦ by
  rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, h₂ f hf, h₁ f hf]

private theorem mulVec_mem_of_fixesOn (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    {F U : Submodule K (n → K)} (hFU : F ⊔ U = ⊤)
    (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    (hF : IsNondegenerateSubmodule Q σ F) {g : Q.specialIsometryGroup σ} (hgF : FixesOn F g)
    {u : n → K} (huU : u ∈ U) :
    ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u ∈ U := by
  obtain ⟨f₀, hf₀F, u₀, hu₀U, hsum⟩ :=
    Submodule.mem_sup.mp (hFU ▸ (Submodule.mem_top :
      ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u ∈ ⊤))
  have hf₀ : f₀ = 0 := hF f₀ hf₀F fun f hfF ↦ by
    have hpres := comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2) f u
    rw [hgF f hfF, horth f hfF u huU, ← hsum, mulVec_add, dotProduct_add,
      horth f hfF u₀ hu₀U, add_zero] at hpres
    exact (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hpres
  rw [← hsum, hf₀, zero_add]
  exact hu₀U

private theorem eq_one_of_fixesOn_sup {F U : Submodule K (n → K)} (hFU : F ⊔ U = ⊤)
    {g : Q.specialIsometryGroup σ} (hgF : FixesOn F g) (hgU : FixesOn U g) : g = 1 := by
  refine Subtype.ext (SpecialLinearGroup.ext _ _ (Matrix.ext_iff.mpr ?_))
  rw [Subgroup.coe_one, SpecialLinearGroup.coe_one]
  refine mulVec_injective (funext fun x ↦ ?_)
  obtain ⟨f, hfF, u, huU, rfl⟩ := Submodule.mem_sup.mp (hFU ▸ (Submodule.mem_top : x ∈ ⊤))
  rw [mulVec_add, hgF f hfF, hgU u huU, one_mulVec]

omit [DecidableEq n] in
/-- Two matrices whose action agrees on `F` and on `U` with `F ⊔ U = ⊤` are equal. -/
private theorem matrix_eq_of_mulVec_eq_on_sup {F U : Submodule K (n → K)} (hFU : F ⊔ U = ⊤)
    {M₁ M₂ : Matrix n n K} (hF : ∀ f ∈ F, M₁ *ᵥ f = M₂ *ᵥ f)
    (hU : ∀ u ∈ U, M₁ *ᵥ u = M₂ *ᵥ u) : M₁ = M₂ := by
  refine mulVec_injective (funext fun x ↦ ?_)
  obtain ⟨f, hfF, u, huU, rfl⟩ := Submodule.mem_sup.mp (hFU ▸ (Submodule.mem_top : x ∈ ⊤))
  rw [mulVec_add, mulVec_add, hF f hfF, hU u huU]

/-- Connecting two non-orthogonal isotropic vectors in `U` by an admissible unitary transvection
in `U`, which therefore fixes `F` pointwise. -/
private theorem exists_transvection_fixesOn_and_mulVec_eq_smul
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {F U : Submodule K (n → K)}
    (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH_tr : ∀ {v : n → K} {a : K}, v ∈ U → (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a → g ∈ H)
    {x y : n → K} (hxU : x ∈ U) (hyU : y ∈ U)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ k ∈ H, ∃ c ≠ (0 : K), FixesOn F k ∧
      ((k : SpecialLinearGroup n K) : Matrix n n K) *ᵥ x = c • y := by
  obtain ⟨d, hd, hdε⟩ := hadm
  set b := (σ ∘ y) ⬝ᵥ (Q *ᵥ x) with hb
  have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hyx
  have hσb_eq : σ b = ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) := by
    rw [hb, apply_comp_dotProduct_mulVec hσ hQ]
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul (hσb_eq ▸ hσb)
  set c := d * (σ b)⁻¹
  have hc : c ≠ 0 := mul_ne_zero hd (inv_ne_zero hσb)
  have hcyx : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = σ d := by
    simp [c, TauCeti.map_comp_smul, hσ b, ← hb, hyx]
  have hcy : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ (c • y)) = 0 := by
    rw [comp_smul_dotProduct_mulVec_smul, hy, mul_zero]
  have hxcy : (σ ∘ x) ⬝ᵥ (Q *ᵥ (c • y)) + (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = 0 := by
    refine mul_left_cancel₀ hε0 ?_
    have h1 : c * (ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y))) = d := by
      rw [← hσb_eq]; simp [c, hσb]
    rw [hcyx, mulVec_smul, dotProduct_smul, smul_eq_mul]
    linear_combination h1 + hdε
  obtain ⟨g, hg, hga, hgx⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection_sub_and_mulVec_eq
      hσ hQ hx hcy (hcyx ▸ (map_ne_zero σ).mpr hd) hxcy
  have hwU : c • y - x ∈ U := U.sub_mem (U.smul_mem c hyU) hxU
  have hw_iso : (σ ∘ (c • y - x)) ⬝ᵥ (Q *ᵥ (c • y - x)) = 0 := by
    simp only [map_comp_sub, sub_dotProduct, mulVec_sub, dotProduct_sub, hx, hcy]
    linear_combination -hxcy
  have ha_adm : ((σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x))⁻¹ + ε * σ ((σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x))⁻¹ = 0 := by
    rw [hcyx, map_inv₀, hσ d]
    have hσd_ne : σ d ≠ 0 := (map_ne_zero σ).mpr hd
    have hprod : d * σ d * ((σ d)⁻¹ + ε * d⁻¹) = d * (σ d * (σ d)⁻¹) + ε * σ d * (d * d⁻¹) := by
      ring
    rw [mul_inv_cancel₀ hσd_ne, mul_inv_cancel₀ hd, mul_one, mul_one,
      show d + ε * σ d = 0 from hdε, mul_eq_zero] at hprod
    exact hprod.resolve_left (mul_ne_zero hd hσd_ne)
  let k : Q.specialIsometryGroup σ := ⟨g, hg⟩
  refine ⟨k, hH_tr hwU hw_iso ha_adm k hga, c, hc, fun f hfF ↦ ?_, hgx⟩
  have hyf := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF y hyU)
  have hxf := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF x hxU)
  simp [k, hga, unitaryTransvection_mulVec, map_comp_sub, TauCeti.map_comp_smul, hyf, hxf]

/-- Connecting two isotropic vectors `x, y ∈ U` sharing a nonzero pairing with an isotropic
`u ∈ U`, using an admissible Siegel transformation in `U` (which fixes `F` and `u`). -/
private theorem exists_siegel_fixesOn_and_mulVec_eq
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    {F U : Submodule K (n → K)} (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH : ∀ {u w : n → K} {c : K}, (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 → (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 →
      c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c → g ∈ H)
    {u x y : n → K} (huU : u ∈ U) (hxU : x ∈ U) (hyU : y ∈ U)
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0)
    (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0) (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0)
    (hxy : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = (σ ∘ u) ⬝ᵥ (Q *ᵥ y)) :
    ∃ s ∈ H, FixesOn F s ∧
      ((s : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = u ∧
      ((s : SpecialLinearGroup n K) : Matrix n n K) *ᵥ x = y := by
  set b := (σ ∘ u) ⬝ᵥ (Q *ᵥ x)
  set u' := (σ b)⁻¹ • u
  set c' := ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y))
  set w' := y - x - c' • u'
  have hu'U : u' ∈ U := U.smul_mem _ huU
  have hw'U : w' ∈ U := U.sub_mem (U.sub_mem hyU hxU) (U.smul_mem _ hu'U)
  have hu'pair (z : n → K) : (σ ∘ u') ⬝ᵥ (Q *ᵥ z) = b⁻¹ * ((σ ∘ u) ⬝ᵥ (Q *ᵥ z)) := by
    rw [TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul, map_inv₀, hσ]
  have hu' : (σ ∘ u') ⬝ᵥ (Q *ᵥ u') = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hu, mul_zero]
  have hu'x : (σ ∘ u') ⬝ᵥ (Q *ᵥ x) = 1 := by rw [hu'pair, inv_mul_cancel₀ hux]
  have hu'y : (σ ∘ u') ⬝ᵥ (Q *ᵥ y) = 1 := by rw [hu'pair, ← hxy, inv_mul_cancel₀ hux]
  have hu'w' : (σ ∘ u') ⬝ᵥ (Q *ᵥ w') = 0 := by simp [w', mulVec_sub, mulVec_smul, hu'y, hu'x, hu']
  have hwu' : (σ ∘ w') ⬝ᵥ (Q *ᵥ u') = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hu'w'
  have hσc' : σ c' = (σ ∘ y) ⬝ᵥ (Q *ᵥ x) :=
    (congrArg σ (apply_comp_dotProduct_mulVec hσ hQ y x)).symm.trans (hσ _)
  have hwx : (σ ∘ w') ⬝ᵥ (Q *ᵥ x) = 0 := by
    simp [w', map_comp_sub, TauCeti.map_comp_smul, hx, hu'x, hσc']
  have hxw' : (σ ∘ x) ⬝ᵥ (Q *ᵥ w') = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mpr hwx
  have hc' : c' + ε * σ c' + ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w')) = 0 := by
    have hy_eq : (x + w') + c' • u' = y := by dsimp [w']; abel
    have h0 : (σ ∘ w') ⬝ᵥ (Q *ᵥ w') + c' * ((σ ∘ x) ⬝ᵥ (Q *ᵥ u')) + σ c' = 0 := by
      rw [← hy, ← hy_eq]
      simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct,
        mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul,
        hx, hu', hu'x, hu'w', hwu', hxw', hwx]
      ring
    have hσ0 := congrArg σ h0
    simp only [map_zero, map_add, map_mul, hσ c', apply_comp_dotProduct_mulVec hσ hQ, hu'x,
      mul_one] at hσ0
    linear_combination hσ0
  obtain ⟨g, hg, hS⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ hu' hu'w' hc'
  let s : Q.specialIsometryGroup σ := ⟨g, hg⟩
  have hu_eq : σ b • u' = u := smul_inv_smul₀ ((map_ne_zero σ).mpr hux) u
  refine ⟨s, hH hu' hu'w' hc' s hS, fun f hfF ↦ ?_, ?_, ?_⟩
  · have hu'f : (σ ∘ u') ⬝ᵥ (Q *ᵥ f) = 0 :=
      (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF _ hu'U)
    have hw'f : (σ ∘ w') ⬝ᵥ (Q *ᵥ f) = 0 :=
      (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF _ hw'U)
    simp [s, hS, siegelTransvection_mulVec, hu'f, hw'f]
  · rw [← hu_eq, mulVec_smul, show ((s : SpecialLinearGroup n K) : Matrix n n K) = g from rfl, hS,
      siegelTransvection_mulVec_self hu' hwu']
  · simp only [s, w', hS, siegelTransvection_mulVec, hu'x, hwx, one_smul, mul_zero, zero_smul,
      sub_zero]
    abel

/-! ### Base cases and inductive step -/

/-- **Dimension `1` base case:** a special isometry fixing the orthogonal complement `F` of a
one-dimensional nondegenerate submodule `U` is the identity. -/
private theorem eq_one_of_finrank_eq_one (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hσ_ne : ∃ a : K, σ a ≠ a) {F U : Submodule K (n → K)} (hFU : F ⊔ U = ⊤)
    (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    (hF : IsNondegenerateSubmodule Q σ F) (hU : IsNondegenerateSubmodule Q σ U)
    (hdim : Module.finrank K U = 1) {g : Q.specialIsometryGroup σ} (hgF : FixesOn F g) :
    g = 1 := by
  have hU0 : U ≠ ⊥ := by rintro rfl; simp at hdim
  obtain ⟨w₀, hw₀U, ha₀⟩ := exists_mem_comp_dotProduct_mulVec_self_ne_zero hσ_ne hU hU0
  have hw₀0 : w₀ ≠ 0 := fun h ↦ ha₀ (by simp [h])
  have hspan : K ∙ w₀ = U := Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem w₀ U).mpr hw₀U)
    (by rw [finrank_span_singleton hw₀0, hdim])
  have hgw₀ : ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ w₀ ∈ K ∙ w₀ :=
    hspan.symm ▸ mulVec_mem_of_fixesOn hσ hQ hFU horth hF hgF hw₀U
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hgw₀
  set a₀ := (σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)
  have hM : ((g : SpecialLinearGroup n K) : Matrix n n K) =
      1 - vecMulVec ((1 - μ) • w₀) (a₀⁻¹ • ((σ ∘ w₀) ᵥ* Q)) := by
    refine matrix_eq_of_mulVec_eq_on_sup (hspan ▸ hFU) (fun f hfF ↦ ?_) (fun u hu ↦ ?_)
    · have hwf : (σ ∘ w₀) ⬝ᵥ (Q *ᵥ f) = 0 :=
        (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF w₀ hw₀U)
      rw [hgF f hfF, sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
        ← dotProduct_mulVec, hwf, smul_zero, zero_smul, sub_zero]
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [mulVec_smul, ← hμ, sub_mulVec, one_mulVec, mulVec_smul, vecMulVec_mulVec,
        op_smul_eq_smul, smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ ha₀,
        one_smul]
      module
  have hdet1 : (1 - vecMulVec ((1 - μ) • w₀) (a₀⁻¹ • ((σ ∘ w₀) ᵥ* Q))).det = 1 :=
    hM ▸ (g : SpecialLinearGroup n K).prop
  rw [TauCeti.det_one_sub_vecMulVec, smul_dotProduct, dotProduct_smul, ← dotProduct_mulVec,
    smul_eq_mul, smul_eq_mul] at hdet1
  have hcancel : a₀⁻¹ * ((1 - μ) * a₀) = 1 - μ := by
    calc a₀⁻¹ * ((1 - μ) * a₀) = (1 - μ) * (a₀⁻¹ * a₀) := by ring
      _ = 1 - μ := by rw [inv_mul_cancel₀ ha₀, mul_one]
  rw [hcancel] at hdet1
  have hμ1 : μ = 1 := by linear_combination hdet1
  refine eq_one_of_fixesOn_sup (hspan ▸ hFU) hgF fun u hu ↦ ?_
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [mulVec_smul, ← hμ, hμ1, one_smul]

omit [Fintype n] [DecidableEq n] in
private theorem mem_sup_span_singleton_iff {u v z : n → K} :
    z ∈ (K ∙ u) ⊔ (K ∙ v) ↔ ∃ c₁ c₂ : K, c₁ • u + c₂ • v = z := by
  simp only [Submodule.mem_sup, Submodule.mem_span_singleton]
  exact ⟨fun ⟨_, ⟨c₁, rfl⟩, _, ⟨c₂, rfl⟩, h⟩ ↦ ⟨c₁, c₂, h⟩,
    fun ⟨c₁, c₂, h⟩ ↦ ⟨c₁ • u, ⟨c₁, rfl⟩, c₂ • v, ⟨c₂, rfl⟩, h⟩⟩

/-- Two-factor rank-one determinant calculation: if `g` fixes `F` pointwise and scales a
hyperbolic pair `(u, v)` spanning `U` by `(μ, (σ μ)⁻¹)`, then `σ μ = μ`. -/
private theorem map_eq_self_of_hyperbolic_mulVec (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {F U : Submodule K (n → K)}
    (hFU : F ⊔ U = ⊤) (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    {u v : n → K} (huU : u ∈ U) (hvU : v ∈ U) (hPU_eq : (K ∙ u) ⊔ (K ∙ v) = U)
    (huiso : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hviso : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) {μ : K} (hμ0 : μ ≠ 0)
    {g : Q.specialIsometryGroup σ} (hgF : FixesOn F g)
    (hgu : ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = μ • u)
    (hgv : ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v = (σ μ)⁻¹ • v) : σ μ = μ := by
  have hvu : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε u v, huv, map_one, mul_one]
  have hσμ0 : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ0
  have hM_prod : ((g : SpecialLinearGroup n K) : Matrix n n K) =
      (1 - vecMulVec ((1 - μ) • u) (ε • ((σ ∘ v) ᵥ* Q))) *
        (1 - vecMulVec ((1 - (σ μ)⁻¹) • v) ((σ ∘ u) ᵥ* Q)) := by
    refine matrix_eq_of_mulVec_eq_on_sup (hPU_eq ▸ hFU) (fun f hfF ↦ ?_) (fun z hz ↦ ?_)
    · have huf : (σ ∘ u) ⬝ᵥ (Q *ᵥ f) = 0 :=
        (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF u huU)
      have hvf : (σ ∘ v) ⬝ᵥ (Q *ᵥ f) = 0 :=
        (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF v hvU)
      have hf₂ : (1 - vecMulVec ((1 - (σ μ)⁻¹) • v) ((σ ∘ u) ᵥ* Q)) *ᵥ f = f := by
        rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, ← dotProduct_mulVec, huf,
          zero_smul, sub_zero]
      rw [hgF f hfF, ← mulVec_mulVec, hf₂, sub_mulVec, one_mulVec, vecMulVec_mulVec,
        op_smul_eq_smul, smul_dotProduct, ← dotProduct_mulVec, hvf, smul_zero, zero_smul, sub_zero]
    · obtain ⟨c₁, c₂, rfl⟩ := mem_sup_span_singleton_iff.mp hz
      have hu₂ : (1 - vecMulVec ((1 - (σ μ)⁻¹) • v) ((σ ∘ u) ᵥ* Q)) *ᵥ u = u := by
        rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, ← dotProduct_mulVec, huiso,
          zero_smul, sub_zero]
      have hu_rhs : (1 - vecMulVec ((1 - μ) • u) (ε • ((σ ∘ v) ᵥ* Q))) *ᵥ u = μ • u := by
        rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
          ← dotProduct_mulVec, hvu, smul_eq_mul, hε, one_smul]
        module
      have hv₂ : (1 - vecMulVec ((1 - (σ μ)⁻¹) • v) ((σ ∘ u) ᵥ* Q)) *ᵥ v = (σ μ)⁻¹ • v := by
        rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, ← dotProduct_mulVec, huv,
          one_smul]
        module
      have hv_rhs : (1 - vecMulVec ((1 - μ) • u) (ε • ((σ ∘ v) ᵥ* Q))) *ᵥ ((σ μ)⁻¹ • v) =
          (σ μ)⁻¹ • v := by
        rw [mulVec_smul, sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
          smul_dotProduct, ← dotProduct_mulVec, hviso, smul_zero, zero_smul, sub_zero]
      rw [mulVec_add, mulVec_smul, mulVec_smul, hgu, hgv, mulVec_add, mulVec_smul, mulVec_smul,
        ← mulVec_mulVec, ← mulVec_mulVec, hu₂, hu_rhs, hv₂, hv_rhs]
  have hdet_g : ((1 - vecMulVec ((1 - μ) • u) (ε • ((σ ∘ v) ᵥ* Q))) *
      (1 - vecMulVec ((1 - (σ μ)⁻¹) • v) ((σ ∘ u) ᵥ* Q))).det = 1 :=
    hM_prod ▸ (g : SpecialLinearGroup n K).prop
  rw [det_mul, TauCeti.det_one_sub_vecMulVec, TauCeti.det_one_sub_vecMulVec,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, ← dotProduct_mulVec, ← dotProduct_mulVec,
    hvu, huv, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hdet_g
  have hprod : μ * (σ μ)⁻¹ = 1 := by
    linear_combination hdet_g + (1 - μ) * (1 - (1 - (σ μ)⁻¹) * 1) * hε
  exact (mul_left_cancel₀ (inv_ne_zero hσμ0)
    (by rw [mul_comm, hprod, inv_mul_cancel₀ hσμ0])).symm

/-- Moving an isotropic vector `y ∈ (K ∙ u) ⊔ (K ∙ v)` with `B(u, y) = (σ μ)⁻¹` to `(σ μ)⁻¹ • v`
by an admissible unitary transvection along `u`. -/
private theorem exists_transvection_along_hyperbolic_mulVec_eq
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    {F U : Submodule K (n → K)} (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH_tr : ∀ {v : n → K} {a : K}, v ∈ U → (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a → g ∈ H)
    {u v y : n → K} (huU : u ∈ U) (huiso : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hviso : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1)
    (hy_mem : y ∈ (K ∙ u) ⊔ (K ∙ v)) (hy_iso : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    {μ : K} (hμ0 : μ ≠ 0) (huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = (σ μ)⁻¹) :
    ∃ k₂ ∈ H, FixesOn F k₂ ∧
      ((k₂ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = u ∧
      ((k₂ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ y = (σ μ)⁻¹ • v := by
  have hvu : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε u v, huv, map_one, mul_one]
  have hσμ0 : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ0
  obtain ⟨a, b, hysum⟩ := mem_sup_span_singleton_iff.mp hy_mem
  have hb_eq : b = (σ μ)⁻¹ := by
    simpa [← hysum, mulVec_add, mulVec_smul, huiso, huv] using huy
  have ha_adm : -(a * σ μ) + ε * σ (-(a * σ μ)) = 0 := by
    rw [← hysum, hb_eq] at hy_iso
    simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct,
      mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul,
      huiso, hviso, huv, hvu, map_inv₀, hσ μ] at hy_iso
    rw [map_neg, map_mul, hσ μ]
    have h1 : a * μ⁻¹ * ε + (σ μ)⁻¹ * σ a = 0 := by linear_combination hy_iso
    have h2 : a * (μ * μ⁻¹) * σ μ * (ε * ε) + ε * σ a * μ * (σ μ * (σ μ)⁻¹) = 0 := by
      linear_combination μ * σ μ * ε * h1
    rw [mul_inv_cancel₀ hμ0, mul_inv_cancel₀ hσμ0, hε] at h2
    linear_combination -h2
  obtain ⟨t₂, ht₂_mem, hM₂⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ huiso ha_adm
  let k₂ : Q.specialIsometryGroup σ := ⟨t₂, ht₂_mem⟩
  refine ⟨k₂, hH_tr huU huiso ha_adm k₂ hM₂, fun f hfF ↦ ?_, ?_, ?_⟩
  · have huf : (σ ∘ u) ⬝ᵥ (Q *ᵥ f) = 0 :=
      (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF u huU)
    simp [k₂, hM₂, unitaryTransvection_mulVec, huf]
  · simp [k₂, hM₂, unitaryTransvection_mulVec, huiso]
  · rw [← hysum, hb_eq]
    simp only [k₂, hM₂, mulVec_add, mulVec_smul, unitaryTransvection_mulVec, huiso, huv, mul_zero,
      zero_smul, add_zero, mul_one, smul_add, smul_smul]
    have hcancel : (σ μ)⁻¹ * -(a * σ μ) = -a := by
      calc (σ μ)⁻¹ * -(a * σ μ) = -a * ((σ μ)⁻¹ * σ μ) := by ring
        _ = -a := by rw [inv_mul_cancel₀ hσμ0, mul_one]
    rw [hcancel]
    module

/-- Moving `g *ᵥ u` in a hyperbolic plane `U = (K ∙ u) ⊔ (K ∙ v)` to a nonzero multiple `μ • u`
by an admissible unitary transvection in `U` (or `1`). -/
private theorem exists_transvection_or_one_fixesOn_and_mulVec_eq_smul
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {F U : Submodule K (n → K)}
    (hFU : F ⊔ U = ⊤) (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    (hF : IsNondegenerateSubmodule Q σ F)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH_tr : ∀ {v : n → K} {a : K}, v ∈ U → (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a → g ∈ H)
    {u v : n → K} (huU : u ∈ U) (hPU_eq : (K ∙ u) ⊔ (K ∙ v) = U)
    (huiso : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1)
    {g : Q.specialIsometryGroup σ} (hgF : FixesOn F g) :
    ∃ k₁ ∈ H, ∃ μ ≠ (0 : K), FixesOn F k₁ ∧
      ((k₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ
        (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u) = μ • u := by
  set x := ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u with hx_def
  have hxU : x ∈ U := mulVec_mem_of_fixesOn hσ hQ hFU horth hF hgF huU
  have hx_iso : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), huiso]
  by_cases hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0
  · obtain ⟨a, b, hsum⟩ := mem_sup_span_singleton_iff.mp (hPU_eq.symm ▸ hxU)
    have hb0 : b = 0 := by simpa [← hsum, mulVec_add, mulVec_smul, huiso, huv] using hux
    have ha0 : a ≠ 0 := by
      rintro rfl
      have hx0 : x = 0 := by simp [← hsum, hb0]
      exact one_ne_zero <| by
        rw [← huv, ← comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2),
          ← hx_def, hx0, map_comp_zero, zero_dotProduct]
    exact ⟨1, one_mem H, a, ha0, fun _ _ ↦ by simp, by simp [← hsum, hb0]⟩
  · exact exists_transvection_fixesOn_and_mulVec_eq_smul hσ hQ hadm horth hH_tr hxU huU
      hx_iso huiso hux

/-- Once `g₂` fixes `F` and scales a hyperbolic basis `(u, v)` of `U` by `μ` and `(σ μ)⁻¹`,
Whitehead's hyperbolic scaling shows `g₂ ∈ H`. -/
private theorem mem_of_hyperbolic_mulVec_smul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hσ_eps : σ ε = ε)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {F U : Submodule K (n → K)} (hFU : F ⊔ U = ⊤)
    (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    {u v : n → K} (huU : u ∈ U) (hvU : v ∈ U) (hPU_eq : (K ∙ u) ⊔ (K ∙ v) = U)
    (huiso : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hviso : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) {μ : K} (hμ0 : μ ≠ 0)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH_tr : ∀ {v : n → K} {a : K}, v ∈ U → (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a → g ∈ H)
    {g₂ : Q.specialIsometryGroup σ} (hg₂F : FixesOn F g₂)
    (hg₂u : ((g₂ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = μ • u)
    (hg₂v : ((g₂ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v = (σ μ)⁻¹ • v) : g₂ ∈ H := by
  have hμ_fixed : σ μ = μ := map_eq_self_of_hyperbolic_mulVec hσ hQ hε hFU horth huU hvU hPU_eq
    huiso hviso huv hμ0 hg₂F hg₂u hg₂v
  obtain ⟨d, hd0, hdε⟩ := hadm
  obtain ⟨h, hhH, hhu, hhv, hhw⟩ := exists_unitaryTransvection_hyperbolic_scaling hσ hQ hε hσ_eps
    hd0 hdε huiso hviso huv (inv_ne_zero hμ0) (by rw [map_inv₀, hμ_fixed])
    (fun a ha k hk ↦ hH_tr huU huiso ha k hk) (fun a ha k hk ↦ hH_tr hvU hviso ha k hk)
  have hhF : FixesOn F h := fun f hfF ↦ hhw f
    ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF u huU))
    ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF v hvU))
  have h_eq_one : h * g₂ = 1 := by
    refine eq_one_of_fixesOn_sup (hPU_eq ▸ hFU) (fixesOn_mul hhF hg₂F) fun z hz ↦ ?_
    obtain ⟨c₁, c₂, rfl⟩ := mem_sup_span_singleton_iff.mp hz
    simp [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, mulVec_add, mulVec_smul,
      hg₂u, hg₂v, hhu, hhv, hμ_fixed, smul_smul, mul_inv_cancel₀ hμ0, inv_mul_cancel₀ hμ0]
  rw [show g₂ = h⁻¹ * (h * g₂) by group, h_eq_one, mul_one]
  exact inv_mem hhH

/-- **Dimension `2` base case:** a special isometry fixing the orthogonal complement `F` of a
two-dimensional nondegenerate submodule `U` lies in any subgroup containing admissible unitary
transvections. -/
private theorem mem_of_finrank_eq_two (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hε : ε * ε = 1) (hσ_eps : σ ε = ε)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t) {F U : Submodule K (n → K)} (hFU : F ⊔ U = ⊤)
    (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    (hF : IsNondegenerateSubmodule Q σ F) (hU : IsNondegenerateSubmodule Q σ U)
    (hdim : Module.finrank K U = 2) {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH_tr : ∀ {v : n → K} {a : K}, v ∈ U → (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a → g ∈ H)
    {g : Q.specialIsometryGroup σ} (hgF : FixesOn F g) : g ∈ H := by
  obtain ⟨u, huU, v, hvU, huiso, hviso, huv⟩ :=
    exists_hyperbolic_pair_mem hσ hQ hε htr hnorm hU hdim.ge
  obtain ⟨_, -, hPU, -, hfinP, -, -, -, -, -⟩ :=
    exists_hyperbolic_complement hσ hQ hε hU huU hvU huiso hviso huv
  have hPU_eq : (K ∙ u) ⊔ (K ∙ v) = U :=
    Submodule.eq_of_le_of_finrank_eq hPU (hfinP.trans hdim.symm)
  obtain ⟨k₁, hk₁H, μ, hμ0, hk₁F, hk₁x⟩ :=
    exists_transvection_or_one_fixesOn_and_mulVec_eq_smul hσ hQ hadm hFU horth hF hH_tr huU hPU_eq
      huiso huv hgF
  let g₁ := k₁ * g
  have hg₁F : FixesOn F g₁ := fixesOn_mul hk₁F hgF
  have hg₁u : ((g₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = μ • u := by
    simpa [g₁, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec] using hk₁x
  set y := ((g₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v
  have hy_mem : y ∈ (K ∙ u) ⊔ (K ∙ v) := hPU_eq.symm ▸ mulVec_mem_of_fixesOn hσ hQ hFU horth hF
    hg₁F hvU
  have hy_iso : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₁.2), hviso]
  have huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = (σ μ)⁻¹ := by
    have hσμ0 : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ0
    have h1 := comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₁.2) u v
    rw [huv, hg₁u, TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul] at h1
    exact mul_left_cancel₀ hσμ0 (h1.trans (mul_inv_cancel₀ hσμ0).symm)
  obtain ⟨k₂, hk₂H, hk₂F, hk₂u, hk₂y⟩ := exists_transvection_along_hyperbolic_mulVec_eq
    hσ hQ hε horth hH_tr huU huiso hviso huv hy_mem hy_iso hμ0 huy
  let g₂ := k₂ * g₁
  have hg₂u : ((g₂ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = μ • u := by
    simp [g₂, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁u, mulVec_smul,
      hk₂u]
  have hg₂v : ((g₂ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v = (σ μ)⁻¹ • v := by
    simpa [g₂, y, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec] using hk₂y
  have hg₂_mem := mem_of_hyperbolic_mulVec_smul hσ hQ hε hσ_eps hadm hFU horth huU hvU hPU_eq
    huiso hviso huv hμ0 hH_tr (fixesOn_mul hk₂F hg₁F) hg₂u hg₂v
  rw [show g = k₁⁻¹ * (k₂⁻¹ * g₂) by simp [g₂, g₁]]
  exact mul_mem (inv_mem hk₁H) (mul_mem (inv_mem hk₂H) hg₂_mem)

/-- Step A in dimension `≥ 3`: move `g *ᵥ u` into non-orthogonality with `u` via an admissible
Siegel transformation in `U`. -/
private theorem exists_siegel_fixesOn_and_comp_dotProduct_mulVec_ne_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hσ_eps : σ ε = ε)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {F U W : Submodule K (n → K)} (hFU : F ⊔ U = ⊤)
    (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    (hF : IsNondegenerateSubmodule Q σ F) (hWU : W ≤ U)
    {u v : n → K} (huU : u ∈ U) (hvU : v ∈ U)
    (hmemW : ∀ w, w ∈ W ↔ w ∈ U ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0)
    (hW : IsNondegenerateSubmodule Q σ W)
    (huiso : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hviso : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH : ∀ {u w : n → K} {c : K}, (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 → (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 →
      c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c → g ∈ H)
    (g : Q.specialIsometryGroup σ) (hgF : FixesOn F g) :
    ∃ k₁ ∈ H, FixesOn F k₁ ∧
      (σ ∘ u) ⬝ᵥ (Q *ᵥ (((k₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ
        (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u))) ≠ 0 := by
  set x₀ := ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u with hx₀_def
  have hx₀U : x₀ ∈ U := mulVec_mem_of_fixesOn hσ hQ hFU horth hF hgF huU
  have hx₀_iso : (σ ∘ x₀) ⬝ᵥ (Q *ᵥ x₀) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), huiso]
  by_cases hux₀ : (σ ∘ u) ⬝ᵥ (Q *ᵥ x₀) = 0
  · by_cases hvx₀ : (σ ∘ v) ⬝ᵥ (Q *ᵥ x₀) = 0
    · have hx₀W : x₀ ∈ W := (hmemW x₀).mpr ⟨hx₀U, hux₀, hvx₀⟩
      have hx₀0 : x₀ ≠ 0 := fun h ↦ one_ne_zero <| by
        rw [← huv, ← comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2),
          ← hx₀_def, h, map_comp_zero, zero_dotProduct]
      obtain ⟨w₁, hw₁W, hx₀w₁⟩ : ∃ w₁ ∈ W, (σ ∘ x₀) ⬝ᵥ (Q *ᵥ w₁) ≠ 0 := by
        by_contra! h0
        exact hx₀0 (hW x₀ hx₀W h0)
      have hw₁x₀ : (σ ∘ w₁) ⬝ᵥ (Q *ᵥ x₀) ≠ 0 :=
        (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mp hx₀w₁
      obtain ⟨c₁, hc₁⟩ := htr (-(ε * ((σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₁)))) <| by
        rw [map_neg, map_mul, hσ_eps, apply_comp_dotProduct_mulVec hσ hQ]
        ring
      have hc₁_adm : c₁ + ε * σ c₁ + ε * ((σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₁)) = 0 := by linear_combination hc₁
      have hvw₁ : (σ ∘ v) ⬝ᵥ (Q *ᵥ w₁) = 0 := ((hmemW w₁).mp hw₁W).2.2
      obtain ⟨s₀, hs₀_mem, hS₀⟩ :=
        exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ hviso hvw₁ hc₁_adm
      let k : Q.specialIsometryGroup σ := ⟨s₀, hs₀_mem⟩
      refine ⟨k, hH hviso hvw₁ hc₁_adm k hS₀, fun f hfF ↦ ?_, ?_⟩
      · have hvf := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF v hvU)
        have hw₁f := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF w₁ (hWU hw₁W))
        simp [k, hS₀, siegelTransvection_mulVec, hvf, hw₁f]
      · simp only [k, hS₀, siegelTransvection_mulVec, hvx₀, zero_smul, add_zero, mulVec_sub,
          mulVec_smul, dotProduct_sub, dotProduct_smul, hux₀, huv, smul_eq_mul, mul_one, zero_sub,
          neg_ne_zero]
        exact mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hw₁x₀
    · have hH_tr : ∀ {z : n → K} {a : K}, z ∈ U → (σ ∘ z) ⬝ᵥ (Q *ᵥ z) = 0 → a + ε * σ a = 0 →
          ∀ k : Q.specialIsometryGroup σ,
            ((k : SpecialLinearGroup n K) : Matrix n n K) =
              Q.unitaryTransvection σ z a → k ∈ H := by
        intro z a _ hz ha k hk
        refine hH hz (by rw [mulVec_zero, dotProduct_zero])
          (by rw [mulVec_zero, dotProduct_zero, mul_zero, add_zero]; exact ha) k ?_
        rwa [siegelTransvection_zero_eq_unitaryTransvection]
      obtain ⟨k, hkH, c, hc0, hkF, hkx₀⟩ :=
        exists_transvection_fixesOn_and_mulVec_eq_smul hσ hQ hadm horth hH_tr hx₀U hvU
          hx₀_iso hviso hvx₀
      exact ⟨k, hkH, hkF,
        by rw [hkx₀, mulVec_smul, dotProduct_smul, huv, smul_eq_mul, mul_one]; exact hc0⟩
  · exact ⟨1, one_mem H, fun _ _ ↦ by simp, by simpa using hux₀⟩

/-- Move `g *ᵥ u` to `u` using Siegel transformations in `U` (which fix `F` pointwise). -/
private theorem exists_siegel_fixesOn_and_mulVec_eq_self
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hσ_eps : σ ε = ε)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t) {F U W : Submodule K (n → K)}
    (hFU : F ⊔ U = ⊤) (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    (hF : IsNondegenerateSubmodule Q σ F) (hWU : W ≤ U)
    {u v w₀ : n → K} (huU : u ∈ U) (hvU : v ∈ U) (hw₀W : w₀ ∈ W)
    (hmemW : ∀ w, w ∈ W ↔ w ∈ U ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0)
    (hW : IsNondegenerateSubmodule Q σ W)
    (huiso : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hviso : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) (hw₀_aniso : (σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀) ≠ 0)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH : ∀ {u w : n → K} {c : K}, (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 → (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 →
      c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c → g ∈ H)
    (g : Q.specialIsometryGroup σ) (hgF : FixesOn F g) :
    ∃ s ∈ H, FixesOn F s ∧
      (((s * g : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = u := by
  obtain ⟨k₁, hk₁H, hk₁F, hux₁⟩ := exists_siegel_fixesOn_and_comp_dotProduct_mulVec_ne_zero
    hσ hQ hε hσ_eps htr hadm hFU horth hF hWU huU hvU hmemW hW huiso hviso huv hH g hgF
  set x₁ := ((k₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ
    (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u)
  have hx₁U : x₁ ∈ U :=
    mulVec_mem_of_fixesOn hσ hQ hFU horth hF hk₁F (mulVec_mem_of_fixesOn hσ hQ hFU horth hF hgF huU)
  have hx₁_iso : (σ ∘ x₁) ⬝ᵥ (Q *ᵥ x₁) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp k₁.2),
      comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), huiso]
  set b := (σ ∘ u) ⬝ᵥ (Q *ᵥ x₁)
  obtain ⟨k₂, hk₂H, hk₂F, -, hk₂x₁⟩ := exists_siegel_fixesOn_and_mulVec_eq hσ hQ horth hH huU hx₁U
    (U.smul_mem b hvU) huiso hx₁_iso (by rw [comp_smul_dotProduct_mulVec_smul, hviso, mul_zero])
    hux₁ (by simp [b, mulVec_smul, huv])
  obtain ⟨α, hα⟩ := exists_smul_comp_dotProduct_mulVec_self_eq hσ hQ hε hnorm hw₀_aniso
    (s := -(ε * b⁻¹ + σ b⁻¹)) <| by
      rw [map_neg, map_add, map_mul, hσ_eps, hσ]
      linear_combination b⁻¹ * hε
  have hα_adm : b⁻¹ + ε * σ b⁻¹ + ε * ((σ ∘ (α • w₀)) ⬝ᵥ (Q *ᵥ (α • w₀))) = 0 := by
    rw [hα]; linear_combination -(b⁻¹) * hε
  obtain ⟨-, huw₀, hvw₀⟩ := (hmemW w₀).mp hw₀W
  have huαw₀ : (σ ∘ u) ⬝ᵥ (Q *ᵥ (α • w₀)) = 0 := by simp [mulVec_smul, huw₀]
  obtain ⟨s₃_sl, hs₃_mem, hS₃⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ huiso huαw₀ hα_adm
  let k₃ : Q.specialIsometryGroup σ := ⟨s₃_sl, hs₃_mem⟩
  have hk₃H : k₃ ∈ H := hH huiso huαw₀ hα_adm k₃ hS₃
  have hk₃F : FixesOn F k₃ := fun f hfF ↦ by
    have huf := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF u huU)
    have hw₀f := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth f hfF w₀ (hWU hw₀W))
    simp [k₃, hS₃, siegelTransvection_mulVec, huf, hw₀f]
  set x₂ := ((k₃ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ (b • v)
  have hx₂U : x₂ ∈ U := mulVec_mem_of_fixesOn hσ hQ hFU horth hF hk₃F (U.smul_mem b hvU)
  have hx₂_iso : (σ ∘ x₂) ⬝ᵥ (Q *ᵥ x₂) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp k₃.2),
      comp_smul_dotProduct_mulVec_smul, hviso, mul_zero]
  have hvu : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε u v, huv, map_one, mul_one]
  have hvx₂ : (σ ∘ v) ⬝ᵥ (Q *ᵥ x₂) = (σ ∘ v) ⬝ᵥ (Q *ᵥ u) := by
    have hw₀v : (σ ∘ w₀) ⬝ᵥ (Q *ᵥ v) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hvw₀
    simp [x₂, k₃, hS₃, siegelTransvection_mulVec, huv, hw₀v, mulVec_add, mulVec_smul,
      hviso, hvw₀, ← mul_assoc, mul_inv_cancel₀ hux₁]
  obtain ⟨k₄, hk₄H, hk₄F, -, hk₄x₂⟩ := exists_siegel_fixesOn_and_mulVec_eq hσ hQ horth hH hvU hx₂U
    huU hviso hx₂_iso huiso (hvx₂.symm ▸ hvu ▸ left_ne_zero_of_mul_eq_one hε) hvx₂
  refine ⟨k₄ * k₃ * k₂ * k₁, mul_mem (mul_mem (mul_mem hk₄H hk₃H) hk₂H) hk₁H,
    fixesOn_mul (fixesOn_mul (fixesOn_mul hk₄F hk₃F) hk₂F) hk₁F, ?_⟩
  simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
  have hstep : ((k₃ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ
      (((k₂ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ x₁) = x₂ := by rw [hk₂x₁]
  rw [show (((k₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ
      (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u)) = x₁ from rfl, hstep, hk₄x₂]

/-- Inductive step in dimension `≥ 3`: split off a hyperbolic plane `P ≤ U` and reduce to its
orthogonal complement `W ≤ U` of codimension `2`. -/
private theorem mem_of_finrank_ge_three
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hσ_eps : σ ε = ε)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t) (hσ_ne : ∃ a : K, σ a ≠ a)
    {F U : Submodule K (n → K)} (hFU : F ⊔ U = ⊤)
    (horth : ∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0)
    (hF : IsNondegenerateSubmodule Q σ F) (hU : IsNondegenerateSubmodule Q σ U)
    (hdim3 : 3 ≤ Module.finrank K U) {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH : ∀ {u w : n → K} {c : K}, (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 → (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 →
      c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c → g ∈ H)
    (ih : ∀ (F' W : Submodule K (n → K)), Module.finrank K W < Module.finrank K U →
      F' ⊔ W = ⊤ → (∀ f ∈ F', ∀ w ∈ W, (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0) →
      IsNondegenerateSubmodule Q σ F' → IsNondegenerateSubmodule Q σ W →
      ∀ g' : Q.specialIsometryGroup σ, FixesOn F' g' → g' ∈ H)
    (g : Q.specialIsometryGroup σ) (hgF : FixesOn F g) : g ∈ H := by
  obtain ⟨u, huU, v, hvU, huiso, hviso, huv⟩ :=
    exists_hyperbolic_pair_mem hσ hQ hε htr hnorm hU (by omega)
  obtain ⟨W, hWU, hPU, hPW_sup, -, hfinW, hmemW, horthPW, hP_nondeg, hW_nondeg⟩ :=
    exists_hyperbolic_complement hσ hQ hε hU huU hvU huiso hviso huv
  set P : Submodule K (n → K) := (K ∙ u) ⊔ (K ∙ v)
  have hW_ne : W ≠ ⊥ := fun hW0 ↦ by rw [hW0, finrank_bot] at hfinW; omega
  obtain ⟨w₀, hw₀W, hw₀_aniso⟩ :=
    exists_mem_comp_dotProduct_mulVec_self_ne_zero hσ_ne hW_nondeg hW_ne
  obtain ⟨s₁, hs₁H, hs₁F, hs₁u⟩ := exists_siegel_fixesOn_and_mulVec_eq_self
    hσ hQ hε hσ_eps htr hadm hnorm hFU horth hF hWU huU hvU hw₀W hmemW hW_nondeg
    huiso hviso huv hw₀_aniso hH g hgF
  let g₁ := s₁ * g
  have hg₁F : FixesOn F g₁ := fixesOn_mul hs₁F hgF
  have hg₁u : ((g₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = u := hs₁u
  have hg₁vU : ((g₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v ∈ U :=
    mulVec_mem_of_fixesOn hσ hQ hFU horth hF hg₁F hvU
  have hg₁v_iso : (σ ∘ (((g₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v)) ⬝ᵥ
      (Q *ᵥ (((g₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v)) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₁.2), hviso]
  have hug₁v : (σ ∘ u) ⬝ᵥ (Q *ᵥ (((g₁ : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v)) =
      (σ ∘ u) ⬝ᵥ (Q *ᵥ v) := by
    have h1 := comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₁.2) u v
    rwa [hg₁u] at h1
  obtain ⟨s₂, hs₂H, hs₂F, hs₂u, hs₂v⟩ := exists_siegel_fixesOn_and_mulVec_eq hσ hQ horth hH
    huU hg₁vU hvU huiso hg₁v_iso hviso (hug₁v.symm ▸ huv ▸ one_ne_zero) hug₁v
  let g₂ := s₂ * g₁
  have hg₂FP : FixesOn (F ⊔ P) g₂ := by
    intro x hx
    obtain ⟨f, hfF, p, hpP, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Submodule.mem_sup.mp hpP
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hp₁
    obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.mp hp₂
    rw [mulVec_add, fixesOn_mul hs₂F hg₁F f hfF, mulVec_add, mulVec_smul, mulVec_smul,
      show g₂ = s₂ * g₁ from rfl]
    simp [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁u, hs₂u, hs₂v]
  have horthFP_W : ∀ fp ∈ F ⊔ P, ∀ w ∈ W, (σ ∘ fp) ⬝ᵥ (Q *ᵥ w) = 0 := by
    intro fp hfp w hwW
    obtain ⟨f, hfF, p, hpP, rfl⟩ := Submodule.mem_sup.mp hfp
    rw [map_comp_add, add_dotProduct, horth f hfF w (hWU hwW), horthPW p hpP w hwW, add_zero]
  have hg₂H : g₂ ∈ H := ih (F ⊔ P) W (by omega) (by rw [sup_assoc, hPW_sup, hFU]) horthFP_W
    (isNondegenerateSubmodule_sup hσ hQ (fun f hf p hp ↦ horth f hf p (hPU hp)) hF hP_nondeg)
    hW_nondeg g₂ hg₂FP
  rw [show g = s₁⁻¹ * (s₂⁻¹ * g₂) by simp [g₂, g₁]]
  exact mul_mem (inv_mem hs₁H) (mul_mem (inv_mem hs₂H) hg₂H)

/-- **Generation of the special unitary group by Siegel transformations.** Let `σ` be a nontrivial
involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix, `(Q ^ σ)ᵀ = ε • Q`, and
suppose that the trace `t ↦ t + ε σ(t)` is onto `{s | σ(s) = ε s}` and has a nonzero kernel
element, and that the norm `b ↦ b * σ(b)` is onto `{t | σ(t) = t}`. Then any subgroup `H` of
`Q.specialIsometryGroup σ` containing every admissible Siegel transformation equals `⊤`. -/
theorem eq_top_of_siegelTransvection_mem (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (H : Subgroup (Q.specialIsometryGroup σ))
    (hH : ∀ {u w : n → K} {c : K}, (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 → (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 →
      c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c → g ∈ H) :
    H = ⊤ := by
  rcases isEmpty_or_nonempty n with _ | _
  · refine eq_top_iff.mpr fun g _ ↦ ?_
    have hg1 : g = 1 := Subtype.ext (SpecialLinearGroup.ext _ _ fun i _ ↦ isEmptyElim i)
    exact hg1 ▸ one_mem H
  have hε : ε * ε = 1 := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have hσ_eps : σ ε = ε := map_eq_self_of_mul_self_eq_one_of_det_ne_zero hσ hQ hdet hε
  have hH_tr : ∀ {v : n → K} {a : K}, (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a → g ∈ H := by
    intro v a hv ha g hg
    refine hH hv (by rw [mulVec_zero, dotProduct_zero])
      (by rw [mulVec_zero, dotProduct_zero, mul_zero, add_zero]; exact ha) g ?_
    rwa [siegelTransvection_zero_eq_unitaryTransvection]
  have main_ind : ∀ m : ℕ, ∀ (F U : Submodule K (n → K)),
      Module.finrank K U = m → F ⊔ U = ⊤ →
      (∀ f ∈ F, ∀ u ∈ U, (σ ∘ f) ⬝ᵥ (Q *ᵥ u) = 0) →
      IsNondegenerateSubmodule Q σ F → IsNondegenerateSubmodule Q σ U →
      ∀ g : Q.specialIsometryGroup σ, FixesOn F g → g ∈ H := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro F U hdim hFU horth hF hU g hgF
      rcases m with _ | _ | _ | m'
      · have hU_bot : U = ⊥ := Submodule.finrank_eq_zero.mp hdim
        have hg1 : g = 1 := eq_one_of_fixesOn_sup hFU hgF fun x hx ↦ by
          rw [hU_bot, Submodule.mem_bot] at hx
          rw [hx, mulVec_zero]
        exact hg1 ▸ one_mem H
      · exact (eq_one_of_finrank_eq_one hσ hQ hσ_ne hFU horth hF hU hdim hgF) ▸ one_mem H
      · exact mem_of_finrank_eq_two hσ hQ hε hσ_eps htr hadm hnorm hFU horth hF hU hdim
          (fun _ ↦ hH_tr) hgF
      · exact mem_of_finrank_ge_three hσ hQ hε hσ_eps htr hadm hnorm hσ_ne hFU horth hF hU
          (by omega) hH (fun F' W hlt ↦ ih (Module.finrank K W) (hdim ▸ hlt) F' W rfl) g hgF
  refine eq_top_iff.mpr fun g _ ↦ main_ind (Module.finrank K (⊤ : Submodule K (n → K))) ⊥ ⊤ rfl
    (bot_sup_eq _) (fun f hf _ _ ↦ ?_) isNondegenerateSubmodule_bot
    (fun x _ hx ↦ eq_zero_of_forall_comp_dotProduct_mulVec_eq_zero hdet fun y ↦ hx y trivial)
    g (fun f hf ↦ ?_)
  · rw [Submodule.mem_bot] at hf
    simp [hf]
  · rw [Submodule.mem_bot] at hf
    simp [hf]

end Generation

end Matrix
