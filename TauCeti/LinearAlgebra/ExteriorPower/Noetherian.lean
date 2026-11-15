/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Positive exterior powers of a Noetherian module are Noetherian

Let `M` be a Noetherian module over a commutative ring `R` (without assuming `R` itself is a
Noetherian ring; in degree zero `⋀[R]^0 M ≃ R` need not be Noetherian when `M = 0`). Every
positive exterior power `⋀[R]^(n + 1) M` is a Noetherian `R`-module: `⋀[R]^1 M ≃ M`, and if
`s₁, …, sₘ` generate `M` over `R` then `(Fin m → ⋀[R]^(n + 1) M)` surjects onto `⋀[R]^(n + 2) M`
by `(gᵢ) ↦ ∑ᵢ sᵢ ∧ gᵢ`.
-/

public section

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Every positive exterior power of a Noetherian module over a commutative ring is Noetherian,
without assuming the base ring is Noetherian. -/
instance instIsNoetherianSucc [IsNoetherian R M] (n : ℕ) : IsNoetherian R (⋀[R]^(n + 1) M) := by
  induction n with
  | zero => exact isNoetherian_of_linearEquiv (oneEquiv R M).symm
  | succ n ih =>
    obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
    let Φ : (Fin m → ⋀[R]^(n + 1) M) →ₗ[R] ⋀[R]^(n + 2) M :=
      { toFun := fun g ↦ ∑ i, TauCeti.ExteriorAlgebra.wedgeLeft (s i) (n + 1) (g i)
        map_add' := fun g₁ g₂ ↦ by simp [Finset.sum_add_distrib]
        map_smul' := fun r g ↦ by simp [Finset.smul_sum] }
    refine isNoetherian_of_surjective Φ (eq_top_iff.mpr ?_)
    rw [← ιMulti_span R (n + 2) M, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun R).mp (hs ▸ Submodule.mem_top : v 0 ∈ _)
    let η := ιMulti R (n + 1) (Fin.tail v)
    refine ⟨fun i ↦ c i • η, Subtype.ext ?_⟩
    have hv : v = Fin.cons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
    conv_rhs => rw [hv, ← TauCeti.ExteriorAlgebra.wedgeLeft_ιMulti]
    simp only [Φ, η, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
      TauCeti.ExteriorAlgebra.coe_wedgeLeft_apply, SetLike.val_smul, mul_smul_comm,
      ← smul_mul_assoc, ← Finset.sum_mul, ← map_smul, ← map_sum, hc]

end exteriorPower
