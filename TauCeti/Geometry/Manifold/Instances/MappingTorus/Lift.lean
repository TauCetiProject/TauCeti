/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus

/-!
# Functions on smooth mapping tori

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a diffeomorphism with smooth mapping torus
`Y_φ = (ℝ × M) / ((t + 1, x) ∼ (t, φ x))` (`TauCeti.SmoothMappingTorus`). A function
`g : ℝ → M → X` with

`g (t + 1) x = g t (φ x)`

is constant on the classes of this relation, so it descends to the function
`[t, x] ↦ g t x` on the mapping torus (`TauCeti.SmoothMappingTorus.lift φ g hg`). For instance a
function `g₀ : M → X` with `g₀ ∘ φ = g₀` gives `[t, x] ↦ g₀ x`, constant along the suspension flow.

Since the quotient map `(t, x) ↦ [t, x]` is a surjective local diffeomorphism, the descended
function is `C^m`, for `m ≤ n`, exactly when `(t, x) ↦ g t x` is `C^m`
(`TauCeti.SmoothMappingTorus.contMDiff_lift_iff`).

## Main definitions

* `TauCeti.SmoothMappingTorus.lift`: the function on the mapping torus induced by a function on
  `ℝ × M` satisfying `g (t + 1) x = g t (φ x)`.

## Main results

* `TauCeti.SmoothMappingTorus.apply_add_intCast_of_apply_add_one`: such a function satisfies
  `g (t + k) x = g t ((φ ^ k) x)` for every integer `k`.
* `TauCeti.SmoothMappingTorus.lift_mk`: the induced function sends `[t, x]` to `g t x`.
* `TauCeti.SmoothMappingTorus.eq_lift_iff`: it is the only function on the mapping torus doing so.
* `TauCeti.SmoothMappingTorus.contMDiff_lift_iff`: it is `C^m` exactly when `g` is, as a function
  of `(t, x)`.
-/

public noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

open Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (φ : M ≃ₘ^n⟮I, I⟯ M) {X : Type*} {g : ℝ → M → X}

/-- A function with `g (t + 1) x = g t (φ x)` satisfies `g (t + k) x = g t ((φ ^ k) x)` for every
integer `k`. -/
theorem apply_add_intCast_of_apply_add_one (hg : ∀ t x, g (t + 1) x = g t (φ x)) (t : ℝ) (k : ℤ)
    (x : M) : g (t + k) x = g t ((φ ^ k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [← add_assoc, hg, ih, zpow_add_one, Diffeomorph.mul_apply]
  | pred k ih =>
    have h := hg (t + (-(k : ℝ) - 1)) (φ.symm x)
    push_cast at ih ⊢
    simpa [zpow_sub_one, Diffeomorph.mul_apply, add_assoc, ih] using h.symm

/-- The function `[t, x] ↦ g t x` on the mapping torus induced by a function `g` on `ℝ × M` with
`g (t + 1) x = g t (φ x)`. -/
def lift (g : ℝ → M → X) (hg : ∀ t x, g (t + 1) x = g t (φ x)) : SmoothMappingTorus φ → X :=
  MulAction.orbitRelQuotientLift (fun z ↦ g ((ofProd φ).symm z).1 ((ofProd φ).symm z).2)
    fun k z ↦ by
      rw [ofProd_symm_smul, apply_add_intCast_of_apply_add_one φ hg, ← Diffeomorph.mul_apply,
        ← zpow_add, add_neg_cancel, zpow_zero, Diffeomorph.one_apply]

variable (hg : ∀ t x, g (t + 1) x = g t (φ x))

/-- The induced function sends `[t, x]` to `g t x`. -/
@[simp]
theorem lift_mk (t : ℝ) (x : M) : lift φ g hg (mk φ t x) = g t x := by
  rw [lift, mk_def φ, MulAction.orbitRelQuotientLift_mk, Equiv.symm_apply_apply]

/-- On `ℝ × M`, the induced function is `g`. -/
theorem lift_comp_uncurry_mk : lift φ g hg ∘ uncurry (mk φ) = uncurry g :=
  funext fun p ↦ lift_mk φ hg p.1 p.2

/-- Two functions on the mapping torus are equal when they agree at every `[t, x]`. -/
theorem funext_mk {f f' : SmoothMappingTorus φ → X} (h : ∀ t x, f (mk φ t x) = f' (mk φ t x)) :
    f = f' :=
  (uncurry_mk_surjective φ).injective_comp_right (funext fun p ↦ h p.1 p.2)

/-- **Uniqueness of the induced function.** A function on the mapping torus is the function
induced by `g` exactly when it sends `[t, x]` to `g t x`. -/
theorem eq_lift_iff {f : SmoothMappingTorus φ → X} :
    f = lift φ g hg ↔ ∀ t x, f (mk φ t x) = g t x := by
  refine ⟨?_, fun h ↦ funext_mk φ fun t x ↦ by rw [h, lift_mk]⟩
  rintro rfl t x
  exact lift_mk φ hg t x

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X] [ChartedSpace H' X]

/-- **Smoothness of an induced function.** For `m ≤ n`, the function `[t, x] ↦ g t x` on the
mapping torus is `C^m` exactly when `(t, x) ↦ g t x` is `C^m` on `ℝ × M`, since the quotient map
is a surjective `C^n` local diffeomorphism. -/
theorem contMDiff_lift_iff {m : ℕ∞ω} (hm : m ≤ n) :
    ContMDiff (𝓘(ℝ).prod I) J m (lift φ g hg) ↔ ContMDiff (𝓘(ℝ).prod I) J m (uncurry g) := by
  rw [← (isLocalDiffeomorph_uncurry_mk φ).contMDiff_comp_iff (uncurry_mk_surjective φ) hm,
    lift_comp_uncurry_mk]

end SmoothMappingTorus

end TauCeti
