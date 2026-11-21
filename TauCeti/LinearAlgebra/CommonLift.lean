/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.LinearAlgebra.Prod

/-!
# Common linear lifts along spans

For a jointly injective span `U ← N → V`, linear maps from a semimodule `E` to
`U` and `V` have a unique common linear lift precisely when their paired values
lie in the range of the span. The lift uses Mathlib's `LinearMap.codLift`, so
pointwise existence suffices without a projectivity assumption on `E`.
Mathlib's `LinearEquiv.ofInjective` already identifies `N` with the joint range.

Adapted from `Mei/LinearAlgebra/CommonLift.lean` in `yuma-mizuno-lean/Mei`, commit
`61509bfe75ce943898bc99cfa509fb40bb78c614`, under the Apache 2.0 license.
-/

public section

namespace LinearMap

variable {R E N U V : Type*} [Semiring R]
  [AddCommMonoid E] [Module R E] [AddCommMonoid N] [Module R N]
  [AddCommMonoid U] [Module R U] [AddCommMonoid V] [Module R V]

/-- Along a jointly injective span `U ← N → V`, two maps `α : E → U` and `β : E → V` have a
common lift to `N` exactly when every pair `(α e, β e)` lies in the joint range of the span; the
common lift is then unique. -/
theorem existsUnique_comp_eq_and_comp_eq_iff {f : N →ₗ[R] U} {g : N →ₗ[R] V}
    (hfg : Function.Injective (f.prod g)) {α : E →ₗ[R] U} {β : E →ₗ[R] V} :
    (∃! ℓ : E →ₗ[R] N, f ∘ₗ ℓ = α ∧ g ∘ₗ ℓ = β) ↔ ∀ e, (α e, β e) ∈ range (f.prod g) := by
  constructor
  · rintro ⟨ℓ, ⟨hf, hg⟩, -⟩ e
    exact ⟨ℓ e, Prod.ext (congr($hf e)) (congr($hg e))⟩
  · intro h
    let ℓ := (α.prod β).codLift (f.prod g) hfg h
    have hℓ : (f.prod g).comp ℓ = α.prod β := comp_codLift ..
    have hf : f.comp ℓ = α := by
      simpa only [← comp_assoc, fst_prod] using congrArg ((fst R U V).comp ·) hℓ
    have hg : g.comp ℓ = β := by
      simpa only [← comp_assoc, snd_prod] using congrArg ((snd R U V).comp ·) hℓ
    refine ⟨ℓ, ⟨hf, hg⟩, fun k hk => ?_⟩
    ext e
    apply hfg
    have hk' : (f.prod g) (k e) = (α e, β e) :=
      Prod.ext (DFunLike.congr_fun hk.1 e) (DFunLike.congr_fun hk.2 e)
    exact hk'.trans (DFunLike.congr_fun hℓ e).symm

end LinearMap
