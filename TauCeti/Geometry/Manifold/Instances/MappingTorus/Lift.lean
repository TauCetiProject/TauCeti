/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Manifold.Instances.MappingTorus
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.GroupTheory.Perm.Basic

/-!
# Invariant functions on a smooth mapping torus

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a diffeomorphism and `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its
smooth mapping torus (`TauCeti.SmoothMappingTorus`). A map `g : M → β` which is invariant under
`φ`, `g ∘ φ = g`, is invariant under every integer power of `φ`, so the function
`(t, x) ↦ g x` on `ℝ × M` is constant on the classes of the mapping torus and descends to

`G : Y_φ → β`, `G [t, x] = g x`

(`TauCeti.SmoothMappingTorus.lift φ g hg`). Pulled back along the quotient map
`(t, x) ↦ [t, x]` it is `g ∘ Prod.snd` (`TauCeti.SmoothMappingTorus.lift_comp_uncurry_mk`), and it
is invariant under the suspension flow (`TauCeti.SmoothMappingTorus.lift_flow`). Since
the quotient map is a surjective `C^n` local diffeomorphism, `G` is `C^m` at `[t, x]`, for
`m ≤ n`, exactly when `g` is `C^m` at `x`, and `C^m` exactly when `g` is.

## Main definitions

* `TauCeti.SmoothMappingTorus.lift φ g hg`: the map `[t, x] ↦ g x` induced on the mapping torus by
  a `φ`-invariant map `g`.

## Main results

* `TauCeti.SmoothMappingTorus.lift_mk`: `G [t, x] = g x`.
* `TauCeti.SmoothMappingTorus.lift_flow`: `G` is invariant under the suspension flow.
* `TauCeti.SmoothMappingTorus.contMDiffAt_lift_mk_iff`,
  `TauCeti.SmoothMappingTorus.contMDiff_lift_iff`: `G` is `C^m` at `[t, x]`, or everywhere,
  exactly when `g` is `C^m` at `x`, or everywhere.
-/

public noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

open Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (φ : M ≃ₘ^n⟮I, I⟯ M) {β : Type*}

/-- The map `[t, x] ↦ g x` induced on the mapping torus by a map `g` invariant under `φ`. -/
def lift (g : M → β) (hg : ∀ x, g (φ x) = g x) : SmoothMappingTorus φ → β :=
  MulAction.orbitRelQuotientLift (fun z : Cover φ ↦ g ((ofProd φ).symm z).2) fun k z ↦ by
    -- `g` is invariant under `φ`, hence constant on the cycle of `φ` through `x` and `φ ^ (-k) x`.
    rw [ofProd_symm_smul]
    refine (Equiv.Perm.SameCycle.apply_eq_of_apply_eq (σ := φ.toEquiv) ⟨-k.toAdd, ?_⟩ hg).symm
    rw [← Diffeomorph.toPerm_apply, ← map_zpow, Diffeomorph.toPerm_apply, Diffeomorph.coe_toEquiv]

variable {g : M → β} (hg : ∀ x, g (φ x) = g x)

/-- The induced map sends `[t, x]` to `g x`. -/
@[simp]
theorem lift_mk (t : ℝ) (x : M) : lift φ g hg (mk φ t x) = g x := by
  rw [lift, mk_def, MulAction.orbitRelQuotientLift_mk, Equiv.symm_apply_apply]

/-- Pulled back to `ℝ × M`, the induced map is `g ∘ Prod.snd`. -/
theorem lift_comp_uncurry_mk : lift φ g hg ∘ uncurry (mk φ) = g ∘ Prod.snd :=
  funext fun p ↦ lift_mk φ hg p.1 p.2

/-- The induced map is invariant under the suspension flow. -/
@[simp]
theorem lift_flow (s : ℝ) (z : SmoothMappingTorus φ) :
    lift φ g hg (flow φ s z) = lift φ g hg z := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp only [uncurry_apply_pair, flow_mk, lift_mk]

section Manifold

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {g : M → N} (hg : ∀ x, g (φ x) = g x) {m : ℕ∞ω}

/-- For `m ≤ n`, the induced map is `C^m` at `[t, x]` exactly when `g` is `C^m` at `x`. -/
theorem contMDiffAt_lift_mk_iff (hm : m ≤ n) (t : ℝ) (x : M) :
    ContMDiffAt (𝓘(ℝ).prod I) J m (lift φ g hg) (mk φ t x) ↔ ContMDiffAt I J m g x := by
  -- Read `[t, x]` as the quotient map `(t, x) ↦ [t, x]` evaluated at `(t, x)`.
  rw [show mk φ t x = uncurry (mk φ) (t, x) from rfl,
    ← (isLocalDiffeomorph_uncurry_mk φ (t, x)).contMDiffAt_comp_iff hm, lift_comp_uncurry_mk]
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp (t, x) contMDiffAt_snd⟩
  -- `g` is `g ∘ Prod.snd` composed with the inclusion `y ↦ (t, y)`.
  exact h.comp x (contMDiffAt_const.prodMk contMDiffAt_id)

/-- For `m ≤ n`, the induced map is `C^m` exactly when `g` is. -/
theorem contMDiff_lift_iff (hm : m ≤ n) :
    ContMDiff (𝓘(ℝ).prod I) J m (lift φ g hg) ↔ ContMDiff I J m g := by
  refine ⟨fun h x ↦ (contMDiffAt_lift_mk_iff φ hg hm 0 x).1 (h _), fun h z ↦ ?_⟩
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  exact (contMDiffAt_lift_mk_iff φ hg hm t x).2 (h x)

end Manifold

end SmoothMappingTorus

end TauCeti
