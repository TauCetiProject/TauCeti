/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.InvariantForm.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.RootLattice

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.InvariantForm.Uniqueness

/-!
# The dual invariant form, simple root reflections, and Casimir norm inequality

Given a nondegenerate standard invariant form `B` on a finite-dimensional Cartan realization `R` of
a symmetrizable generalized Cartan matrix `A`, the musical isomorphism
`ν = B.form.toDual hB : H ≃ₗ[K] Module.Dual K H` maps each simple coroot `hᵢ` to `αᵢ / d i` and
transfers `B.form` to a symmetric nondegenerate bilinear form `B.dualForm hB` on `Module.Dual K H`
satisfying `(αᵢ, μ) = d i * μ(hᵢ)` and `(αᵢ, αⱼ) = d i * a i j`.

Although `B.dualForm hB` depends on `B` when both arguments lie outside the root span, its values
whenever at least one argument lies in the root span (or root lattice `R.rootLattice`) are
completely independent of the choice of nondegenerate standard invariant form `B`
(`dualForm_eq_of_mem_rootSpan_left`). Moreover, `B.dualForm hB` is invariant under every simple
reflection `sᵢ(μ) = μ - μ(hᵢ) • αᵢ` (`Module.reflection`), which takes the metric form
`sᵢ(μ) = μ - (2 (μ, αᵢ) / (αᵢ, αᵢ)) • αᵢ`, and `B.form.toDual hB` intertwines the simple
reflections on `H` and `Module.Dual K H`.

Finally, over a strict ordered field (`ℚ` or `ℝ`), for dominant weights `μ, λ` with `R.RootLE μ λ`
and `μ ≠ λ` and any weight `ρ` with `ρ(hᵢ) > 0` for all `i`, one has strict norm separation
`(μ + ρ, μ + ρ) < (λ + ρ, λ + ρ)` (`dualForm_add_lt_of_rootLE`), the eigenvalue inequality
governing Kac's generalized Casimir operator, complete reducibility of integrable modules in
Category `𝒪`, and the Weyl–Kac character formula.

## Main definitions

* `TauCeti.CartanRealization.InvariantForm.dualForm`: the induced symmetric nondegenerate bilinear
  form on `Module.Dual K H`.
* `TauCeti.CartanRealization.InvariantForm.toDualIsometryEquiv`: `B.form.toDual hB` bundled as an
  isometric equivalence `B.form.IsometryEquiv (B.dualForm hB)`.
* `TauCeti.CartanRealization.InvariantForm.dualReflectionIsometryEquiv`: simple reflections on
  `Module.Dual K H` bundled as isometric equivalences of `B.dualForm hB`.

## Main results

* `TauCeti.CartanRealization.InvariantForm.toDual_coroot`,
  `TauCeti.CartanRealization.InvariantForm.toDual_symm_root`: `ν(hᵢ) = αᵢ / d i` and
  `ν⁻¹(αᵢ) = d i • hᵢ`.
* `TauCeti.CartanRealization.InvariantForm.dualForm_root_left`,
  `TauCeti.CartanRealization.InvariantForm.dualForm_root_root`: `(αᵢ, μ) = d i * μ(hᵢ)` and
  `(αᵢ, αⱼ) = d i * a i j`.
* `TauCeti.CartanRealization.InvariantForm.dualForm_eq_of_mem_rootSpan_left`,
  `TauCeti.CartanRealization.InvariantForm.dualForm_eq_of_mem_rootLattice_left`: independence of
  `B.dualForm hB` from `B` whenever an argument lies in the root span or root lattice.
* `TauCeti.CartanRealization.InvariantForm.isOrthogonal_dualForm_reflection`,
  `TauCeti.CartanRealization.InvariantForm.reflection_dual_apply_eq_sub_dualForm`,
  `TauCeti.CartanRealization.InvariantForm.toDual_reflection`: simple-reflection invariance, metric
  reflection formula, and `toDual` equivariance.
* `TauCeti.CartanRealization.InvariantForm.dualForm_add_self_sub_eq_sum`,
  `TauCeti.CartanRealization.InvariantForm.dualForm_add_lt_of_rootLE`: Casimir norm-difference
  identity and strict norm inequality `(μ + ρ, μ + ρ) < (λ + ρ, λ + ρ)`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §2.1 (eqs. (2.1.5)–(2.1.6)), §2.6, §3.9, and §10.4.
-/

public section

open Module
open scoped Matrix

namespace TauCeti.CartanRealization.InvariantForm

section DualForm

section

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  [FiniteDimensional K H] {A : SymmetrizableDatum I}
  {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}
  (B : InvariantForm A R) (hB : B.form.Nondegenerate)

/-- Kac's linear isomorphism `ν = B.form.toDual hB : H ≃ₗ[K] Dual K H` maps the `i`-th simple
coroot `hᵢ` to `αᵢ / d i`. -/
@[simp]
theorem toDual_coroot (i : I) :
    B.form.toDual hB (R.coroot i) = (A.symmetrizer i : K)⁻¹ • R.root i := by
  ext h
  simp [LinearMap.BilinForm.toDual_def, div_eq_inv_mul]

/-- The inverse of `B.form.toDual hB` maps the `i`-th simple root `αᵢ` to `d i • hᵢ`. -/
@[simp]
theorem toDual_symm_root (i : I) :
    (B.form.toDual hB).symm (R.root i) = (A.symmetrizer i : K) • R.coroot i := by
  rw [LinearEquiv.symm_apply_eq, map_smul, B.toDual_coroot hB,
    smul_inv_smul₀ (A.symmetrizer_cast_ne_zero i)]

/-- The symmetric nondegenerate bilinear form on `Module.Dual K H` transported from `B.form` along
`B.form.toDual hB` (Kac, §2.1, eq. (2.1.5)). -/
noncomputable def dualForm : LinearMap.BilinForm K (Dual K H) := B.form.congr (B.form.toDual hB)

theorem dualForm_def : B.dualForm hB = B.form.congr (B.form.toDual hB) := (rfl)

/-- Evaluating `B.dualForm hB` on `φ, ψ : Dual K H` applies `φ` to `(B.form.toDual hB).symm ψ`. -/
theorem dualForm_apply (φ ψ : Dual K H) :
    B.dualForm hB φ ψ = φ ((B.form.toDual hB).symm ψ) := by simp [dualForm]

/-- The dual bilinear form is symmetric. -/
theorem isSymm_dualForm : (B.dualForm hB).IsSymm := ⟨fun _ _ ↦ B.isSymm.eq _ _⟩

/-- The dual bilinear form is nondegenerate. -/
theorem nondegenerate_dualForm : (B.dualForm hB).Nondegenerate := hB.congr (B.form.toDual hB)

/-- `B.form.toDual hB` bundled as an isometric equivalence
`B.form.IsometryEquiv (B.dualForm hB)`. -/
noncomputable def toDualIsometryEquiv : B.form.IsometryEquiv (B.dualForm hB) :=
  { B.form.toDual hB with map_app' := fun x y ↦ by simp [dualForm] }

@[simp]
theorem toDualIsometryEquiv_toLinearEquiv :
    (B.toDualIsometryEquiv hB).toLinearEquiv = B.form.toDual hB := (rfl)

@[simp]
theorem toDualIsometryEquiv_apply (x : H) :
    B.toDualIsometryEquiv hB x = B.form.toDual hB x := (rfl)

/-- Pairing a simple root on the left against any weight `μ : Dual K H` gives `d i * μ(hᵢ)`. -/
@[simp]
theorem dualForm_root_left (i : I) (μ : Dual K H) :
    B.dualForm hB (R.root i) μ = A.symmetrizer i * μ (R.coroot i) := by
  rw [(B.isSymm_dualForm hB).eq, B.dualForm_apply, B.toDual_symm_root, map_smul, smul_eq_mul]

/-- Pairing a simple root on the right against any weight `μ : Dual K H` gives `d i * μ(hᵢ)`. -/
@[simp]
theorem dualForm_root_right (μ : Dual K H) (i : I) :
    B.dualForm hB μ (R.root i) = A.symmetrizer i * μ (R.coroot i) := by
  rw [B.dualForm_apply, B.toDual_symm_root, map_smul, smul_eq_mul]

/-- On the simple roots, `B.dualForm hB` realizes the symmetrized Cartan matrix:
`(αᵢ, αⱼ) = d i * a i j`. -/
theorem dualForm_root_root (i j : I) :
    B.dualForm hB (R.root i) (R.root j) = A.symmetrizedMatrix i j := by
  rw [B.dualForm_root_left, R.root_coroot, Matrix.map_apply]
  exact_mod_cast (A.symmetrizedMatrix_apply i j).symm

/-- The squared norm of the `i`-th simple root is `2 * d i`. -/
theorem dualForm_root_self (i : I) :
    B.dualForm hB (R.root i) (R.root i) = 2 * A.symmetrizer i := by
  simp [A.isGeneralizedCartan.diag, mul_comm]

/-- Every simple root is non-isotropic under `B.dualForm hB`. -/
theorem dualForm_root_self_ne_zero (i : I) :
    B.dualForm hB (R.root i) (R.root i) ≠ 0 := by
  rw [B.dualForm_root_self]
  exact mul_ne_zero two_ne_zero (A.symmetrizer_cast_ne_zero i)

/-- **Canonicality of `dualForm` on the root span**: for any two nondegenerate standard invariant
forms on `R` (including on non-minimal central enlargements), their induced dual forms agree
whenever the left argument lies in `Submodule.span K (Set.range R.root)`. -/
theorem dualForm_eq_of_mem_rootSpan_left {B₁ B₂ : InvariantForm A R}
    (hB₁ : B₁.form.Nondegenerate) (hB₂ : B₂.form.Nondegenerate) {φ : Dual K H}
    (hφ : φ ∈ Submodule.span K (Set.range R.root)) (ψ : Dual K H) :
    B₁.dualForm hB₁ φ ψ = B₂.dualForm hB₂ φ ψ :=
  LinearMap.congr_fun
    (LinearMap.eqOn_span (f := B₁.dualForm hB₁) (g := B₂.dualForm hB₂)
      (by rintro _ ⟨i, rfl⟩; ext μ; rw [B₁.dualForm_root_left, B₂.dualForm_root_left]) hφ)
    ψ

/-- Any two nondegenerate standard invariant forms induce the same pairing whenever the right
argument lies in `Submodule.span K (Set.range R.root)`. -/
theorem dualForm_eq_of_mem_rootSpan_right {B₁ B₂ : InvariantForm A R}
    (hB₁ : B₁.form.Nondegenerate) (hB₂ : B₂.form.Nondegenerate) (φ : Dual K H) {ψ : Dual K H}
    (hψ : ψ ∈ Submodule.span K (Set.range R.root)) :
    B₁.dualForm hB₁ φ ψ = B₂.dualForm hB₂ φ ψ := by
  rw [(B₁.isSymm_dualForm hB₁).eq, (B₂.isSymm_dualForm hB₂).eq]
  exact dualForm_eq_of_mem_rootSpan_left hB₁ hB₂ hψ φ

/-- Any two nondegenerate standard invariant forms induce the same pairing whenever the left
argument lies in `R.rootLattice`. -/
theorem dualForm_eq_of_mem_rootLattice_left {B₁ B₂ : InvariantForm A R}
    (hB₁ : B₁.form.Nondegenerate) (hB₂ : B₂.form.Nondegenerate) {φ : Dual K H}
    (hφ : φ ∈ R.rootLattice) (ψ : Dual K H) :
    B₁.dualForm hB₁ φ ψ = B₂.dualForm hB₂ φ ψ :=
  dualForm_eq_of_mem_rootSpan_left hB₁ hB₂
    (Submodule.span_le_restrictScalars ℤ K (Set.range R.root) (R.rootLattice_def ▸ hφ)) ψ

/-- Any two nondegenerate standard invariant forms induce the same pairing whenever the right
argument lies in `R.rootLattice`. -/
theorem dualForm_eq_of_mem_rootLattice_right {B₁ B₂ : InvariantForm A R}
    (hB₁ : B₁.form.Nondegenerate) (hB₂ : B₂.form.Nondegenerate) (φ : Dual K H) {ψ : Dual K H}
    (hψ : ψ ∈ R.rootLattice) :
    B₁.dualForm hB₁ φ ψ = B₂.dualForm hB₂ φ ψ := by
  rw [(B₁.isSymm_dualForm hB₁).eq, (B₂.isSymm_dualForm hB₂).eq]
  exact dualForm_eq_of_mem_rootLattice_left hB₁ hB₂ hψ φ

/-! ### Invariance under simple reflections on `Dual K H` -/

/-- `B.dualForm hB` is invariant under the simple reflection `μ ↦ μ - μ(hᵢ) • αᵢ`
(`Module.reflection`). -/
theorem isOrthogonal_dualForm_reflection (i : I)
    (h : Dual.eval K H (R.coroot i) (R.root i) = 2 := by simp [A.isGeneralizedCartan.diag]) :
    (B.dualForm hB).IsOrthogonal (Module.reflection h) := by
  intro μ ν
  have h' : R.root i (R.coroot i) = 2 := h
  simp only [Module.reflection_apply, Dual.eval_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, B.dualForm_root_left, B.dualForm_root_right, h']
  ring

/-- The simple reflection on `Dual K H` bundled as an isometric equivalence of `B.dualForm hB`. -/
noncomputable def dualReflectionIsometryEquiv (i : I) :
    (B.dualForm hB).IsometryEquiv (B.dualForm hB) :=
  { Module.reflection (f := Dual.eval K H (R.coroot i)) (x := R.root i)
      (by simp [A.isGeneralizedCartan.diag]) with
    map_app' := B.isOrthogonal_dualForm_reflection hB i }

theorem dualReflectionIsometryEquiv_toLinearEquiv (i : I)
    (h : Dual.eval K H (R.coroot i) (R.root i) = 2 := by simp [A.isGeneralizedCartan.diag]) :
    (B.dualReflectionIsometryEquiv hB i).toLinearEquiv = Module.reflection h :=
  (rfl)

@[simp]
theorem dualReflectionIsometryEquiv_apply (i : I) (μ : Dual K H) :
    B.dualReflectionIsometryEquiv hB i μ = μ - μ (R.coroot i) • R.root i :=
  (rfl)

/-- Metric formula for the simple reflection on `Dual K H`:
`sᵢ(μ) = μ - (2 (μ, αᵢ) / (αᵢ, αᵢ)) • αᵢ`. -/
theorem reflection_dual_apply_eq_sub_dualForm (i : I) (μ : Dual K H)
    (h : Dual.eval K H (R.coroot i) (R.root i) = 2 := by simp [A.isGeneralizedCartan.diag]) :
    Module.reflection h μ =
      μ - (2 * B.dualForm hB μ (R.root i) / B.dualForm hB (R.root i) (R.root i)) • R.root i := by
  have hd : (2 : K) * A.symmetrizer i ≠ 0 :=
    mul_ne_zero two_ne_zero (A.symmetrizer_cast_ne_zero i)
  rw [Module.reflection_apply, Dual.eval_apply, B.dualForm_root_right, B.dualForm_root_self]
  congr 2
  field_simp [hd]

/-- `B.form.toDual hB` intertwines the simple reflection on `H` with the simple reflection on
`Dual K H`. -/
theorem toDual_reflection (i : I) (x : H)
    (h₁ : R.root i (R.coroot i) = 2 := by simp [A.isGeneralizedCartan.diag])
    (h₂ : Dual.eval K H (R.coroot i) (R.root i) = 2 := by simp [A.isGeneralizedCartan.diag]) :
    B.form.toDual hB (Module.reflection h₁ x) =
      Module.reflection h₂ (B.form.toDual hB x) := by
  rw [Module.reflection_apply, Module.reflection_apply, Dual.eval_apply,
    LinearMap.BilinForm.toDual_def, B.form_coroot_right, map_sub, map_smul, B.toDual_coroot,
    smul_smul, div_eq_mul_inv]

/-- **Casimir norm-difference identity**: when `λ - μ = ∑ i, c i • αᵢ`, the difference
`(λ + ρ, λ + ρ) - (μ + ρ, μ + ρ)` equals `∑ i, c i * d i * (λ(hᵢ) + μ(hᵢ) + 2 ρ(hᵢ))` and in
particular does not depend on the choice of nondegenerate standard invariant form `B`. -/
theorem dualForm_add_self_sub_eq_sum [Fintype I] {μ lam : Dual K H} (ρ : Dual K H) {c : I → K}
    (hc : ∑ i, c i • R.root i = lam - μ) :
    B.dualForm hB (lam + ρ) (lam + ρ) - B.dualForm hB (μ + ρ) (μ + ρ) =
      ∑ i, c i * A.symmetrizer i * (lam (R.coroot i) + μ (R.coroot i) + 2 * ρ (R.coroot i)) := by
  have hdiff :
      B.dualForm hB (lam + ρ) (lam + ρ) - B.dualForm hB (μ + ρ) (μ + ρ) =
        B.dualForm hB (lam - μ) (lam + μ + (2 : K) • ρ) := by
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, smul_eq_mul,
      (B.isSymm_dualForm hB).eq μ lam, (B.isSymm_dualForm hB).eq ρ lam,
      (B.isSymm_dualForm hB).eq ρ μ]
    ring
  rw [hdiff, ← hc, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, B.dualForm_root_left, LinearMap.add_apply]
  ring

end

/-- **Casimir / Weyl–Kac strict norm inequality** (Kac, §2.6 and §10.4): over a strict ordered field
(`ℚ` or `ℝ`), if `μ ≤ λ` in the root order (`R.RootLE μ lam`) with `μ ≠ lam`, both `lam` and `μ` are
dominant, and `ρ(hᵢ) > 0` for every `i`, then `(μ + ρ, μ + ρ) < (lam + ρ, lam + ρ)`. -/
theorem dualForm_add_lt_of_rootLE {I K H : Type*} [Finite I] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    {A : SymmetrizableDatum I} {R : CartanRealization (A.cartan.map (Int.cast : ℤ → K)) H}
    (B : InvariantForm A R) (hB : B.form.Nondegenerate) {μ lam ρ : Dual K H}
    (hμlam : R.RootLE μ lam) (hne : μ ≠ lam) (hlam : R.IsDominant lam) (hμ : R.IsDominant μ)
    (hρ : ∀ i, 0 < ρ (R.coroot i)) :
    B.dualForm hB (μ + ρ) (μ + ρ) < B.dualForm hB (lam + ρ) (lam + ρ) := by
  let := Fintype.ofFinite I
  obtain ⟨c, hc⟩ := R.mem_posRootCone_iff.mp (R.rootLE_iff.mp hμlam)
  have hcK : ∑ i, (c i : K) • R.root i = lam - μ := by
    simpa [Nat.cast_smul_eq_nsmul] using hc
  have hne' : ∃ i, 0 < c i := by
    by_contra! h0
    have hc0 : ∀ i, c i = 0 := fun i ↦ Nat.le_zero.mp (h0 i)
    have hsub : lam - μ = 0 := by simp [← hc, hc0]
    exact hne (sub_eq_zero.mp hsub).symm
  obtain ⟨i₀, hi₀⟩ := hne'
  have hlam' := R.isDominant_iff.mp hlam
  have hμ' := R.isDominant_iff.mp hμ
  rw [← sub_pos, B.dualForm_add_self_sub_eq_sum hB ρ hcK]
  refine Finset.sum_pos' (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
  · refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_
    linarith [hlam' i, hμ' i, hρ i]
  · refine mul_pos (mul_pos (Nat.cast_pos.mpr hi₀) (Nat.cast_pos.mpr (A.symmetrizer_pos i₀))) ?_
    linarith [hlam' i₀, hμ' i₀, hρ i₀]

end DualForm

end TauCeti.CartanRealization.InvariantForm

end

/-! ### Worked examples -/

section Examples

open Module Matrix TauCeti TauCeti.CartanRealization

private def a1Datum : SymmetrizableDatum (Fin 1) where
  cartan := !![2]
  isGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp [Fin.forall_fin_one]
      zero_comm := by simp }
  symmetrizer := 1
  symmetrizer_pos := by decide
  symmetrizes := by decide

/-- Minimal realization of `A₁` on `ℚ¹` with `h₀ = e₀` and `α₀ = 2 e₀*`. -/
private noncomputable def a1Minimal :
    CartanRealization (a1Datum.cartan.map (Int.cast : ℤ → ℚ)) (Fin 1 → ℚ) where
  coroot _ := Pi.single 0 1
  root _ := (2 : ℚ) • LinearMap.proj 0
  coroot_linearIndependent := Fintype.linearIndependent_iff.mpr fun c hc i ↦ by
    fin_cases i; simpa using congrFun hc 0
  root_linearIndependent := Fintype.linearIndependent_iff.mpr fun c hc i ↦ by
    fin_cases i; simpa using LinearMap.congr_fun hc (Pi.single 0 1)
  root_coroot i j := by fin_cases i; fin_cases j; simp [a1Datum]

/-- Type `A₁` on its minimal realization `ℚ¹`: the unique standard invariant form satisfies
`(h₀, h₀) = 2` and `(α₀, α₀) = 2`. -/
example :
    ∃! B : InvariantForm a1Datum a1Minimal,
      B.form (a1Minimal.coroot 0) (a1Minimal.coroot 0) = 2 ∧
        ∃ hB : B.form.Nondegenerate,
          B.dualForm hB (a1Minimal.root 0) (a1Minimal.root 0) = 2 := by
  have htop : a1Minimal.corootSpan = ⊤ := eq_top_iff.mpr fun x _ ↦ by
    have hx : x = x 0 • a1Minimal.coroot 0 := by ext i; fin_cases i; simp [a1Minimal]
    exact hx ▸ Submodule.smul_mem _ _ (a1Minimal.coroot_mem_corootSpan 0)
  obtain ⟨B⟩ := InvariantForm.nonempty a1Datum a1Minimal
  have hmin : a1Minimal.IsMinimal := by
    rw [a1Minimal.isMinimal_iff_cartanCenter_le_corootSpan, htop]
    exact le_top
  refine ⟨B, ⟨by simp [a1Datum], B.nondegenerate_of_isMinimal hmin, ?_⟩, fun B' _ ↦
    InvariantForm.eq_of_corootSpan_eq_top htop B' B⟩
  rw [B.dualForm_root_self]; simp [a1Datum]

/-- Non-simply-laced type `B₂` (`A = !![2, -2; -1, 2]`, `d = ![1, 2]`) over `ℚ`: there is a
realization `R` on `Fin N → ℚ` carrying a nondegenerate standard invariant form `B`, which satisfies
`(h₀, h₀) = 2`, `(h₁, h₁) = 1`, `(α₀, α₀) = 2`, `(α₁, α₁) = 4`, and `(α₀, α₁) = -2`. -/
example :
    let A : SymmetrizableDatum (Fin 2) :=
      { cartan := !![2, -2; -1, 2],
        isGeneralizedCartan :=
          { diag := by decide,
            offDiag_nonpos := by simp [Fin.forall_fin_two],
            zero_comm := by simp [Fin.forall_fin_two] },
        symmetrizer := ![1, 2],
        symmetrizer_pos := by simp [Fin.forall_fin_two], symmetrizes := by decide }
    let N := 2 * Fintype.card (Fin 2) - (A.cartan.map (Int.cast : ℤ → ℚ)).rank
    ∃ (R : CartanRealization (A.cartan.map (Int.cast : ℤ → ℚ)) (Fin N → ℚ))
      (B : InvariantForm A R) (hB : B.form.Nondegenerate),
      B.form (R.coroot 0) (R.coroot 0) = 2 ∧ B.form (R.coroot 1) (R.coroot 1) = 1 ∧
        B.dualForm hB (R.root 0) (R.root 0) = 2 ∧ B.dualForm hB (R.root 1) (R.root 1) = 4 ∧
        B.dualForm hB (R.root 0) (R.root 1) = -2 := by
  intro A N
  obtain ⟨R⟩ := Matrix.nonempty_cartanRealization (A.cartan.map (Int.cast : ℤ → ℚ))
  obtain ⟨B, hB⟩ := InvariantForm.exists_nondegenerate A R
  refine ⟨R, B, hB, by simp [A], by simp [A], ?_, ?_, ?_⟩
  · rw [B.dualForm_root_self]; norm_num [A]
  · rw [B.dualForm_root_self]; norm_num [A]
  · rw [B.dualForm_root_root]; norm_num [A]

end Examples
