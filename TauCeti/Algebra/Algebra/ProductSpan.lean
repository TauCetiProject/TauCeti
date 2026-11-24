/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Products of two large subspaces of a division algebra

Let `D` be a division algebra of finite dimension `n` over a field `k`, and let `V` and `W` be
`k`-subspaces of `D` with `dim V + dim W > n`. Then the products `a * b` with `a ∈ V` and `b ∈ W`
span `D` over `k`, that is, `V * W = ⊤` (`Submodule.mul_eq_top_of_finrank_lt_add`).

The argument uses the pairing `(a, b) ↦ f (a * b)` attached to a nonzero linear form `f` on `D`,
not the trace form, so it needs neither separability nor commutativity. If `V * W` were a proper
subspace, choose `f ≠ 0` vanishing on it. The map `a ↦ (b ↦ f (a * b))` from `D` to its dual is
injective: for `a ≠ 0` and `f c ≠ 0`, the form at `a` takes the value `f c` at `b = a⁻¹ * c`. It
sends `V` into the annihilator of `W`, of dimension `n - dim W`, so `dim V + dim W ≤ n`.

The bound is sharp: in a quadratic extension `K / k`, the subspace `V = W = k` has
`dim V + dim W = 2` while `V * W = k ≠ K`. The division hypothesis cannot be dropped either: in
`k × k × k × k` the subspace `V = W = k × k × k × 0` has `3 + 3 > 4`, while `V * W = V`.

## Main results

* `Submodule.mul_eq_top_of_finrank_lt_add`: if `finrank k D < finrank k V + finrank k W`, then
  `V * W = ⊤`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. (2) **192** (2020), no. 2,
  487–497, §2, the product-span argument before Proposition 1.
-/

public section

open Module

namespace Submodule

variable {k D : Type*} [Field k] [DivisionRing D] [Algebra k D] [FiniteDimensional k D]

/-- **Products of large subspaces span a division algebra.** If `V` and `W` are subspaces of a
finite-dimensional division algebra `D` over a field `k` with `dim V + dim W > dim D`, then the
products of elements of `V` and `W` span `D`: `V * W = ⊤`. -/
theorem mul_eq_top_of_finrank_lt_add {V W : Submodule k D}
    (h : finrank k D < finrank k V + finrank k W) : V * W = ⊤ := by
  by_contra hne
  -- A nonzero linear form `f` vanishes on the proper subspace `V * W`.
  obtain ⟨f, hf0, hf⟩ := exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  have hfVW : ∀ a ∈ V, ∀ b ∈ W, f (a * b) = 0 := fun a ha b hb ↦ by
    rw [← mem_bot k, ← hf]
    exact mem_map_of_mem (mul_mem_mul ha hb)
  -- The map `a ↦ (b ↦ f (a * b))` from `D` to its dual.
  let φ : D →ₗ[k] Dual k D := (LinearMap.mul k D).compr₂ f
  have hφ : ∀ a b, φ a b = f (a * b) := fun _ _ ↦ by simp [φ]
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    rw [mem_bot]
    by_contra ha0
    obtain ⟨c, hc⟩ : ∃ c, f c ≠ 0 := by
      by_contra! hc
      exact hf0 (LinearMap.ext hc)
    apply hc
    have := LinearMap.congr_fun ha (a⁻¹ * c)
    rwa [hφ, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul] at this
  -- It maps `V` injectively into the annihilator of `W`.
  have hmap : V.map φ ≤ W.dualAnnihilator := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_dualAnnihilator]
    exact fun b hb ↦ hfVW a ha b hb
  have hle := finrank_mono hmap
  rw [← (equivMapOfInjective φ hφinj V).finrank_eq] at hle
  have := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

end Submodule
