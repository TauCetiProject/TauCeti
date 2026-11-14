/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Transvection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Hyperbolic pairs, orthogonal splitting, and Whitehead's hyperbolic scaling

Let `σ` be an involution of a field `K`, let `Q` be an `ε`-Hermitian matrix, `(Q ^ σ)ᵀ = ε • Q`,
with `ε * ε = 1`, and write `B(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` for its coordinate sesquilinear form.
This file collects the submodule geometry of nondegenerate subspaces of `K^n` together with
Whitehead's four-transvection hyperbolic scaling identity in `Q.specialIsometryGroup σ`:

* `Matrix.exists_smul_comp_dotProduct_mulVec_self_eq`: when the norm `b ↦ b * σ(b)` is onto
  `{t | σ(t) = t}`, an anisotropic vector `w₀` rescales so that `B(α • w₀, α • w₀)` takes any value
  `s` with `σ(s) = ε * s`.
* `Matrix.exists_mem_comp_dotProduct_mulVec_self_ne_zero`: when `σ` is nontrivial, any nonzero
  nondegenerate submodule contains an anisotropic vector.
* `Matrix.exists_mem_ne_zero_comp_dotProduct_mulVec_self_eq_zero` and
  `Matrix.exists_hyperbolic_pair_mem`: under norm and trace surjectivity, any nondegenerate
  submodule of dimension at least `2` contains a nonzero isotropic vector and a hyperbolic pair
  `(u, v)` (`B(u, u) = B(v, v) = 0`, `B(u, v) = 1`).
* `Matrix.exists_hyperbolic_complement`: a hyperbolic pair `(u, v)` inside a nondegenerate
  submodule `U` splits `U` orthogonally as `((K ∙ u) ⊔ (K ∙ v)) ⊔ W` with `W` nondegenerate of
  codimension `2`.
* `Matrix.exists_unitaryTransvection_hyperbolic_scaling`: Whitehead's product of four admissible
  unitary transvections along `u` and `v` scaling `u ↦ t • u`, `v ↦ t⁻¹ • v`, and fixing
  `{u, v}^⊥` pointwise for `t ≠ 0` with `σ(t) = t`.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, 3rd ed., Springer (1971), Chapter II, §4.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

namespace Matrix

section Submodules

variable {n K : Type*} [Fintype n] [Field K] {Q : Matrix n n K} {σ : K →+* K} {ε : K}

/-- Using surjectivity of the norm `b ↦ b * σ(b)` onto `{t | σ(t) = t}`, an anisotropic vector `w₀`
can be rescaled so that `B(α • w₀, α • w₀)` equals any given `s` with `σ(s) = ε * s`. -/
theorem exists_smul_comp_dotProduct_mulVec_self_eq (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t) {w₀ : n → K}
    (hw₀ : (σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀) ≠ 0) {s : K} (hs : σ s = ε * s) :
    ∃ α : K, (σ ∘ (α • w₀)) ⬝ᵥ (Q *ᵥ (α • w₀)) = s := by
  set a₀ := (σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul_eq_one hε
  have ha₀ : σ a₀ = ε * a₀ := apply_comp_dotProduct_mulVec hσ hQ w₀ w₀
  obtain ⟨b, hb⟩ := hnorm (s / a₀) <| by
    rw [map_div₀, hs, ha₀, mul_div_mul_left _ _ hε0]
  refine ⟨σ b, ?_⟩
  rw [TauCeti.map_comp_smul, hσ b, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, hb, div_mul_cancel₀ _ hw₀]

/-- For a fixed left argument `x`, the pairing `y ↦ B(x, y)` as a `K`-linear functional. -/
private def pairRight (Q : Matrix n n K) (σ : K →+* K) (x : n → K) : (n → K) →ₗ[K] K where
  toFun y := (σ ∘ x) ⬝ᵥ (Q *ᵥ y)
  map_add' y₁ y₂ := by rw [mulVec_add, dotProduct_add]
  map_smul' c y := by rw [mulVec_smul, dotProduct_smul, RingHom.id_apply]

@[simp]
private theorem pairRight_apply (Q : Matrix n n K) (σ : K →+* K) (x y : n → K) :
    pairRight Q σ x y = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) :=
  (rfl)

/-- When `σ ≠ id`, any nonzero submodule on which `B` is nondegenerate contains an anisotropic
vector. -/
theorem exists_mem_comp_dotProduct_mulVec_self_ne_zero (hσ_ne : ∃ a : K, σ a ≠ a)
    {U : Submodule K (n → K)}
    (hU : ∀ x ∈ U, (∀ y ∈ U, (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0) → x = 0) (hU0 : U ≠ ⊥) :
    ∃ w ∈ U, (σ ∘ w) ⬝ᵥ (Q *ᵥ w) ≠ 0 := by
  by_contra! hall
  obtain ⟨w₁, hw₁U, hw₁0⟩ := U.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨w₂, hw₂U, hb0⟩ : ∃ w₂ ∈ U, (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₂) ≠ 0 := by
    by_contra! h0
    exact hw₁0 (hU w₁ hw₁U h0)
  set b := (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₂)
  have hexp (c : K) : c * b + σ c * ((σ ∘ w₂) ⬝ᵥ (Q *ᵥ w₁)) = 0 := by
    have h := hall (w₁ + c • w₂) (U.add_mem hw₁U (U.smul_mem c hw₂U))
    simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hall w₁ hw₁U, hall w₂ hw₂U] at h
    linear_combination h
  have hswap : (σ ∘ w₂) ⬝ᵥ (Q *ᵥ w₁) = -b := by
    have h1 := hexp 1
    rw [map_one, one_mul, one_mul] at h1
    linear_combination h1
  obtain ⟨a, ha⟩ := hσ_ne
  have ha0 := hexp a
  rw [hswap] at ha0
  exact (mul_ne_zero (sub_ne_zero.mpr ha.symm) hb0) (by linear_combination ha0)

/-- Under surjectivity of the norm `b ↦ b * σ(b)` onto `{t | σ(t) = t}`, any submodule of dimension
at least `2` on which `B` is nondegenerate contains a nonzero isotropic vector. -/
theorem exists_mem_ne_zero_comp_dotProduct_mulVec_self_eq_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t) {U : Submodule K (n → K)}
    (hU : ∀ x ∈ U, (∀ y ∈ U, (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0) → x = 0)
    (hdim : 2 ≤ Module.finrank K U) :
    ∃ u ∈ U, u ≠ 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 := by
  have hU0 : U ≠ ⊥ := by rintro rfl; simp at hdim
  obtain ⟨v₁, hv₁U, hv₁0⟩ := U.exists_mem_ne_zero_of_ne_bot hU0
  by_cases hv₁iso : (σ ∘ v₁) ⬝ᵥ (Q *ᵥ v₁) = 0
  · exact ⟨v₁, hv₁U, hv₁0, hv₁iso⟩
  let f : U →ₗ[K] K := (pairRight Q σ v₁).comp U.subtype
  have hker_ne : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    have hrle : Module.finrank K (LinearMap.range f) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    rw [hbot, finrank_bot, add_zero] at hrk
    omega
  obtain ⟨⟨v₂, hv₂U⟩, hv₂ker, hv₂0'⟩ := (LinearMap.ker f).exists_mem_ne_zero_of_ne_bot hker_ne
  have hv₂0 : v₂ ≠ 0 := fun h ↦ hv₂0' (Subtype.ext h)
  have hv₁₂ : (σ ∘ v₁) ⬝ᵥ (Q *ᵥ v₂) = 0 := hv₂ker
  have hv₂₁ : (σ ∘ v₂) ⬝ᵥ (Q *ᵥ v₁) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hv₁₂
  by_cases hv₂iso : (σ ∘ v₂) ⬝ᵥ (Q *ᵥ v₂) = 0
  · exact ⟨v₂, hv₂U, hv₂0, hv₂iso⟩
  obtain ⟨α, hα⟩ := exists_smul_comp_dotProduct_mulVec_self_eq hσ hQ hε hnorm hv₂iso
    (s := -((σ ∘ v₁) ⬝ᵥ (Q *ᵥ v₁))) <| by
      rw [map_neg, apply_comp_dotProduct_mulVec hσ hQ, mul_neg]
  refine ⟨v₁ + α • v₂, U.add_mem hv₁U (U.smul_mem α hv₂U), ?_, ?_⟩
  · intro hsum
    have h0 : (σ ∘ v₁) ⬝ᵥ (Q *ᵥ (v₁ + α • v₂)) = 0 := by rw [hsum, mulVec_zero, dotProduct_zero]
    rw [mulVec_add, dotProduct_add, mulVec_smul, dotProduct_smul, hv₁₂, smul_zero, add_zero] at h0
    exact hv₁iso h0
  · simp only [map_comp_add, add_dotProduct, mulVec_add, dotProduct_add,
      TauCeti.map_comp_smul, smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul,
      hv₁₂, hv₂₁, mul_zero, add_zero, zero_add] at hα ⊢
    linear_combination hα

/-- Under trace and norm surjectivity, any submodule of dimension at least `2` on which `B` is
nondegenerate contains a hyperbolic pair `(u, v)` (`B(u, u) = B(v, v) = 0`, `B(u, v) = 1`). -/
theorem exists_hyperbolic_pair_mem (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t) {U : Submodule K (n → K)}
    (hU : ∀ x ∈ U, (∀ y ∈ U, (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0) → x = 0)
    (hdim : 2 ≤ Module.finrank K U) :
    ∃ u ∈ U, ∃ v ∈ U,
      (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧ (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1 := by
  obtain ⟨u, huU, hu0, huiso⟩ :=
    exists_mem_ne_zero_comp_dotProduct_mulVec_self_eq_zero hσ hQ hε hnorm hU hdim
  obtain ⟨y, hyU, huy⟩ : ∃ y ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
    by_contra! h0
    exact hu0 (hU u huU h0)
  have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) ≠ 0 := (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mp huy
  obtain ⟨c, hc⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr huiso hyu
  set v₀ := y + c • u
  have hv₀U : v₀ ∈ U := U.add_mem hyU (U.smul_mem c huU)
  have huv₀ : (σ ∘ u) ⬝ᵥ (Q *ᵥ v₀) = (σ ∘ u) ⬝ᵥ (Q *ᵥ y) := by
    simp [v₀, mulVec_add, mulVec_smul, huiso]
  refine ⟨u, huU, ((σ ∘ u) ⬝ᵥ (Q *ᵥ y))⁻¹ • v₀, U.smul_mem _ hv₀U, huiso, ?_, ?_⟩
  · rw [comp_smul_dotProduct_mulVec_smul, hc, mul_zero]
  · rw [mulVec_smul, dotProduct_smul, smul_eq_mul, huv₀, inv_mul_cancel₀ huy]

/-- Coordinate projection onto a hyperbolic pair `(u, v)`. -/
private def hyperbolicProj (Q : Matrix n n K) (σ : K →+* K) (ε : K) (u v : n → K) :
    (n → K) →ₗ[K] K × K :=
  LinearMap.prod (ε • pairRight Q σ v) (pairRight Q σ u)

/-- Linear inclusion `(a, b) ↦ a • u + b • v` of the coordinates of a hyperbolic plane. -/
private def hyperbolicIncl (K : Type*) [Field K] {n : Type*} (u v : n → K) :
    K × K →ₗ[K] (n → K) :=
  (LinearMap.fst K K K).smulRight u + (LinearMap.snd K K K).smulRight v

private theorem hyperbolicProj_hyperbolicIncl (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {u v : n → K}
    (huiso : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hviso : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) (ab : K × K) :
    hyperbolicProj Q σ ε u v (hyperbolicIncl K u v ab) = ab := by
  have hvu : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε u v, huv, map_one, mul_one]
  rcases ab with ⟨a, b⟩
  ext
  · simp only [hyperbolicProj, hyperbolicIncl, LinearMap.prod_apply, Function.prod,
      LinearMap.smul_apply, pairRight_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, mulVec_add, mulVec_smul, dotProduct_add,
      dotProduct_smul, smul_eq_mul, hvu, hviso, mul_zero, add_zero]
    linear_combination a * hε
  · simp [hyperbolicProj, hyperbolicIncl, mulVec_add, mulVec_smul, huiso, huv]

omit [Fintype n] in
private theorem range_hyperbolicIncl (u v : n → K) :
    LinearMap.range (hyperbolicIncl K u v) = (K ∙ u) ⊔ (K ∙ v) := by
  ext x
  simp only [LinearMap.mem_range, Prod.exists, hyperbolicIncl, LinearMap.add_apply,
    LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply, Submodule.mem_sup,
    Submodule.mem_span_singleton]
  exact ⟨fun ⟨a, b, hx⟩ ↦ ⟨a • u, ⟨a, rfl⟩, b • v, ⟨b, rfl⟩, hx⟩,
    fun ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hx⟩ ↦ ⟨a, b, hx⟩⟩

/-- **Orthogonal hyperbolic splitting.** Inside a submodule `U` on which `B` is nondegenerate, any
hyperbolic pair `(u, v)` (`B(u, u) = B(v, v) = 0`, `B(u, v) = 1`) splits `U` orthogonally as
`((K ∙ u) ⊔ (K ∙ v)) ⊔ W`, where `W = {w ∈ U | B(u, w) = 0 ∧ B(v, w) = 0}` is nondegenerate of
codimension `2`. -/
theorem exists_hyperbolic_complement (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hε : ε * ε = 1) {U : Submodule K (n → K)}
    (hU : ∀ x ∈ U, (∀ y ∈ U, (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0) → x = 0)
    {u v : n → K} (huU : u ∈ U) (hvU : v ∈ U)
    (huiso : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hviso : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) :
    let P : Submodule K (n → K) := (K ∙ u) ⊔ (K ∙ v)
    ∃ W : Submodule K (n → K), W ≤ U ∧
      P ≤ U ∧ P ⊔ W = U ∧
      Module.finrank K P = 2 ∧
      Module.finrank K W + 2 = Module.finrank K U ∧
      (∀ w, w ∈ W ↔ w ∈ U ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0) ∧
      (∀ p ∈ P, ∀ w ∈ W, (σ ∘ p) ⬝ᵥ (Q *ᵥ w) = 0) ∧
      (∀ x ∈ P, (∀ y ∈ P, (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0) → x = 0) ∧
      (∀ x ∈ W, (∀ y ∈ W, (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0) → x = 0) := by
  intro P
  let W : Submodule K (n → K) := U ⊓ LinearMap.ker (hyperbolicProj Q σ ε u v)
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul_eq_one hε
  have hleft := hyperbolicProj_hyperbolicIncl hσ hQ hε huiso hviso huv
  have hrange : LinearMap.range (hyperbolicIncl K u v) = P := range_hyperbolicIncl u v
  have hPU : P ≤ U := sup_le ((Submodule.span_singleton_le_iff_mem u U).mpr huU)
    ((Submodule.span_singleton_le_iff_mem v U).mpr hvU)
  have hWU : W ≤ U := inf_le_left
  have hPW_sup : P ⊔ W = U := le_antisymm (sup_le hPU hWU) fun x hxU ↦ by
    let p := hyperbolicIncl K u v (hyperbolicProj Q σ ε u v x)
    have hpP : p ∈ P := hrange ▸ ⟨_, rfl⟩
    have hwW : x - p ∈ W := ⟨U.sub_mem hxU (hPU hpP), by
      simp [p, LinearMap.mem_ker, map_sub, hleft]⟩
    simpa [p] using Submodule.add_mem_sup hpP hwW
  have hPW_inf : P ⊓ W = ⊥ := eq_bot_iff.mpr fun x ⟨hxP, _, hxker⟩ ↦ by
    obtain ⟨ab, rfl⟩ := hrange ▸ hxP
    rw [show ab = 0 by simpa [hleft] using hxker, map_zero]
    exact Submodule.zero_mem ⊥
  have hfinP : Module.finrank K P = 2 := by
    rw [← hrange, LinearMap.finrank_range_of_inj (Function.LeftInverse.injective hleft),
      Module.finrank_prod, Module.finrank_self]
  have hfinW : Module.finrank K W + 2 = Module.finrank K U := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P W
    rw [hPW_sup, hPW_inf, finrank_bot, add_zero, hfinP] at h
    omega
  have hmemW (w : n → K) : w ∈ W ↔ w ∈ U ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 := by
    simp [W, hyperbolicProj, LinearMap.mem_ker, hε0, and_comm]
  have horthPW : ∀ p ∈ P, ∀ w ∈ W, (σ ∘ p) ⬝ᵥ (Q *ᵥ w) = 0 := by
    intro p hpP w hwW
    obtain ⟨ab, rfl⟩ := hrange ▸ hpP
    obtain ⟨-, huw, hvw⟩ := (hmemW w).mp hwW
    simp [hyperbolicIncl, map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct,
      huw, hvw]
  refine ⟨W, hWU, hPU, hPW_sup, hfinP, hfinW, hmemW, horthPW, ?_, ?_⟩
  · intro p hpP hp0
    obtain ⟨⟨a, b⟩, rfl⟩ := hrange ▸ hpP
    have hpu := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp
      (hp0 u (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)))
    have hpv := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp
      (hp0 v (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    rw [show (a, b) = (0 : K × K) by rw [← hleft (a, b)]; ext <;> simp [hyperbolicProj, hpu, hpv],
      map_zero]
  · intro w hwW hw0
    refine hU w (hWU hwW) fun y hyU ↦ ?_
    obtain ⟨p, hpP, w', hw'W, rfl⟩ := Submodule.mem_sup.mp (hPW_sup ▸ hyU)
    rw [mulVec_add, dotProduct_add,
      (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horthPW p hpP w hwW), hw0 w' hw'W, zero_add]

end Submodules

section HyperbolicScaling

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

private theorem hyperbolic_scaling_mulVec_left (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {d : K} (hd0 : d ≠ 0)
    {u v : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) {t : K} (ht0 : t ≠ 0) :
    Q.unitaryTransvection σ u (d * (t - 1)) *ᵥ
      (Q.unitaryTransvection σ v (ε * d⁻¹ * 1) *ᵥ
        (Q.unitaryTransvection σ u (d * (t⁻¹ - 1)) *ᵥ
          (Q.unitaryTransvection σ v (ε * d⁻¹ * (-t)) *ᵥ u))) = t • u := by
  have hvu : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε u v, huv, map_one, mul_one]
  have step4 : Q.unitaryTransvection σ v (ε * d⁻¹ * (-t)) *ᵥ u = u - (d⁻¹ * t) • v := by
    rw [unitaryTransvection_mulVec, hvu,
      show ε * d⁻¹ * -t * ε = -(d⁻¹ * t) by linear_combination -(d⁻¹ * t) * hε,
      neg_smul, sub_eq_add_neg]
  have step3 : Q.unitaryTransvection σ u (d * (t⁻¹ - 1)) *ᵥ (u - (d⁻¹ * t) • v) =
      t • u - (d⁻¹ * t) • v := by
    rw [unitaryTransvection_mulVec, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, hu, huv, mul_one, zero_sub]
    have : d * (t⁻¹ - 1) * -(d⁻¹ * t) = t - 1 := by
      calc d * (t⁻¹ - 1) * -(d⁻¹ * t) = -(d * d⁻¹) * ((t⁻¹ * t) - t) := by ring
        _ = t - 1 := by rw [mul_inv_cancel₀ hd0, inv_mul_cancel₀ ht0]; ring
    rw [this]; module
  have step2 : Q.unitaryTransvection σ v (ε * d⁻¹ * 1) *ᵥ (t • u - (d⁻¹ * t) • v) = t • u := by
    simp only [mulVec_sub, mulVec_smul, unitaryTransvection_mulVec, hvu, hv, mul_zero, zero_smul,
      add_zero]
    rw [show ε * d⁻¹ * 1 * ε = d⁻¹ by linear_combination d⁻¹ * hε, smul_add, smul_smul,
      mul_comm t d⁻¹]
    abel
  rw [step4, step3, step2, unitaryTransvection_mulVec, mulVec_smul, dotProduct_smul, hu, smul_zero,
    mul_zero, zero_smul, add_zero]

private theorem hyperbolic_scaling_mulVec_right (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {d : K} (hd0 : d ≠ 0)
    {u v : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) {t : K} (ht0 : t ≠ 0) :
    Q.unitaryTransvection σ u (d * (t - 1)) *ᵥ
      (Q.unitaryTransvection σ v (ε * d⁻¹ * 1) *ᵥ
        (Q.unitaryTransvection σ u (d * (t⁻¹ - 1)) *ᵥ
          (Q.unitaryTransvection σ v (ε * d⁻¹ * (-t)) *ᵥ v))) = t⁻¹ • v := by
  have hvu : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε u v, huv, map_one, mul_one]
  have step4 : Q.unitaryTransvection σ v (ε * d⁻¹ * (-t)) *ᵥ v = v := by
    rw [unitaryTransvection_mulVec, hv, mul_zero, zero_smul, add_zero]
  have step3 : Q.unitaryTransvection σ u (d * (t⁻¹ - 1)) *ᵥ v = (d * (t⁻¹ - 1)) • u + v := by
    rw [unitaryTransvection_mulVec, huv, mul_one, add_comm]
  have step2 : Q.unitaryTransvection σ v (ε * d⁻¹ * 1) *ᵥ ((d * (t⁻¹ - 1)) • u + v) =
      (d * (t⁻¹ - 1)) • u + t⁻¹ • v := by
    rw [unitaryTransvection_mulVec, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul, hvu, hv, add_zero]
    have : ε * d⁻¹ * 1 * (d * (t⁻¹ - 1) * ε) = t⁻¹ - 1 := by
      calc ε * d⁻¹ * 1 * (d * (t⁻¹ - 1) * ε) = (ε * ε) * (d⁻¹ * d) * (t⁻¹ - 1) := by ring
        _ = t⁻¹ - 1 := by rw [hε, inv_mul_cancel₀ hd0]; ring
    rw [this]; module
  rw [step4, step3, step2]
  simp only [mulVec_add, mulVec_smul, unitaryTransvection_mulVec, hu, huv, mul_zero, zero_smul,
    add_zero, mul_one]
  have hcancel : d * (t⁻¹ - 1) + t⁻¹ * (d * (t - 1)) = 0 := by
    calc d * (t⁻¹ - 1) + t⁻¹ * (d * (t - 1)) = d * (t⁻¹ - 1 + t⁻¹ * t - t⁻¹) := by ring
      _ = 0 := by rw [inv_mul_cancel₀ ht0]; ring
  rw [smul_add, smul_smul, add_left_comm ((d * (t⁻¹ - 1)) • u), ← add_smul, hcancel, zero_smul,
    add_zero]

/-- **Whitehead's hyperbolic scaling identity.** Let `(u, v)` be a hyperbolic pair
(`B(u, u) = B(v, v) = 0`, `B(u, v) = 1`), let `d ≠ 0` satisfy `d + ε σ(d) = 0`, and let `t ≠ 0`
satisfy `σ(t) = t`. Any subgroup `H` of `Q.specialIsometryGroup σ` containing all admissible
unitary transvections along `u` and along `v` contains an element scaling `u ↦ t • u`,
`v ↦ t⁻¹ • v`, and fixing `{u, v}^⊥` pointwise. -/
theorem exists_unitaryTransvection_hyperbolic_scaling (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hσ_eps : σ ε = ε)
    {d : K} (hd0 : d ≠ 0) (hd : d + ε * σ d = 0)
    {u v : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) {t : K} (ht0 : t ≠ 0) (ht : σ t = t)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hHu : ∀ a, a + ε * σ a = 0 → ∀ g : Q.specialIsometryGroup σ,
      ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ u a → g ∈ H)
    (hHv : ∀ a, a + ε * σ a = 0 → ∀ g : Q.specialIsometryGroup σ,
      ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a → g ∈ H) :
    ∃ h ∈ H,
      ((h : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u = t • u ∧
        ((h : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v = t⁻¹ • v ∧
        ∀ w : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 →
          ((h : SpecialLinearGroup n K) : Matrix n n K) *ᵥ w = w := by
  have hσd : σ d = -(ε * d) := by linear_combination ε * hd - σ d * hε
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul_eq_one hε
  have hε_inv : ε⁻¹ = ε := mul_left_cancel₀ hε0 (by rw [mul_inv_cancel₀ hε0, hε])
  have hadm1 (r : K) (hr : σ r = r) : d * r + ε * σ (d * r) = 0 := by
    rw [map_mul, hr]; linear_combination r * hd
  have hadm2 (r : K) (hr : σ r = r) : ε * d⁻¹ * r + ε * σ (ε * d⁻¹ * r) = 0 := by
    rw [map_mul, map_mul, map_inv₀, hσ_eps, hσd, hr, inv_neg, mul_inv, hε_inv]
    linear_combination -(ε * d⁻¹ * r) * hε
  have ha₁ := hadm1 (t - 1) (by rw [map_sub, map_one, ht])
  have ha₂ := hadm2 1 (map_one σ)
  have ha₃ := hadm1 (t⁻¹ - 1) (by rw [map_sub, map_inv₀, map_one, ht])
  have ha₄ := hadm2 (-t) (by rw [map_neg, ht])
  obtain ⟨g₁, hg₁, hM₁⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hu ha₁
  obtain ⟨g₂, hg₂, hM₂⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hv ha₂
  obtain ⟨g₃, hg₃, hM₃⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hu ha₃
  obtain ⟨g₄, hg₄, hM₄⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hv ha₄
  let k₁ : Q.specialIsometryGroup σ := ⟨g₁, hg₁⟩
  let k₂ : Q.specialIsometryGroup σ := ⟨g₂, hg₂⟩
  let k₃ : Q.specialIsometryGroup σ := ⟨g₃, hg₃⟩
  let k₄ : Q.specialIsometryGroup σ := ⟨g₄, hg₄⟩
  refine ⟨k₁ * k₂ * k₃ * k₄,
    mul_mem (mul_mem (mul_mem (hHu _ ha₁ k₁ hM₁) (hHv _ ha₂ k₂ hM₂)) (hHu _ ha₃ k₃ hM₃))
      (hHv _ ha₄ k₄ hM₄), ?_, ?_, ?_⟩
  · simpa only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, k₁, k₂, k₃, k₄,
      hM₁, hM₂, hM₃, hM₄] using hyperbolic_scaling_mulVec_left hσ hQ hε hd0 hu hv huv ht0
  · simpa only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, k₁, k₂, k₃, k₄,
      hM₁, hM₂, hM₃, hM₄] using hyperbolic_scaling_mulVec_right hσ hQ hε hd0 hu hv huv ht0
  · intro w huw hvw
    simp [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, k₁, k₂, k₃, k₄,
      hM₁, hM₂, hM₃, hM₄, unitaryTransvection_mulVec, huw, hvw]

end HyperbolicScaling

end Matrix
