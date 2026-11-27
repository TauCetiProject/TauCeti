/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi

import Mathlib.Tactic.Ring

/-!
# Splitting the first coordinate of a submodule

The inverse image of a submodule of `Fin N → M` under deletion of coordinate zero
is the product of a copy of `M` and that submodule. For `M = R`, this is the fibrewise
coordinate splitting for adjoining a first trivial line to a plane. The construction
restricts Mathlib's `Fin.consLinearEquiv`.

Over a commutative ring `R`, let `P` be a submodule of `R^(n+1)` which contains `a e_0` and whose
elements all have first coordinate divisible by `a`. Then `P` is determined by its image under
`Fin.tail`: a vector lies in `P` exactly when its first coordinate is divisible by `a` and its tail
lies in that image (`Submodule.mem_iff_dvd_apply_zero_and_funLeft_succ_mem_map`). This is the
inductive step in the diagonalisation of submodules of `R^n` one row and column at a time.
-/

public section

namespace Submodule

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {N : ℕ}

/-- Splitting off coordinate zero identifies the inverse image of a submodule under
`Fin.tail` with a copy of the coordinate module followed by that submodule. -/
def finConsEquiv (V : Submodule R (Fin N → M)) :
    (M × V) ≃ₗ[R] V.comap (LinearMap.funLeft R M Fin.succ) where
  toFun p := ⟨Fin.cons p.1 p.2.val, by
    apply (Submodule.mem_comap).2
    convert p.2.property using 1
    ext i
    simp⟩
  invFun v := (v.val 0, ⟨Fin.tail v.val, v.property⟩)
  left_inv p := by ext <;> simp
  right_inv v := Subtype.ext (Fin.cons_self_tail v.val)
  map_add' p q := by
    apply Subtype.ext
    exact (Fin.consLinearEquiv R (fun _ : Fin (N + 1) ↦ M)).map_add (p.1, p.2.val) (q.1, q.2.val)
  map_smul' a p := by
    apply Subtype.ext
    exact (Fin.consLinearEquiv R (fun _ : Fin (N + 1) ↦ M)).map_smul a (p.1, p.2.val)

@[simp]
theorem coe_finConsEquiv_apply (V : Submodule R (Fin N → M)) (p : M × V) :
    (V.finConsEquiv p).val = Fin.cons p.1 p.2.val := (rfl)

@[simp]
theorem finConsEquiv_symm_apply (V : Submodule R (Fin N → M))
    (v : V.comap (LinearMap.funLeft R M Fin.succ)) :
    V.finConsEquiv.symm v = (v.val 0, ⟨Fin.tail v.val, v.property⟩) := (rfl)

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

/-- **Splitting off the first coordinate.** If `P ≤ R^(n+1)` contains `a e_0` and the first
coordinate of each of its elements is divisible by `a`, then `P` consists of the vectors whose
first coordinate is divisible by `a` and whose tail lies in the image of `P` under `Fin.tail`. -/
theorem mem_iff_dvd_apply_zero_and_funLeft_succ_mem_map {n : ℕ} {P : Submodule R (Fin (n + 1) → R)}
    {a : R} (ha : Pi.single 0 a ∈ P) (hdvd : ∀ k ∈ P, a ∣ k 0) (y : Fin (n + 1) → R) :
    y ∈ P ↔ a ∣ y 0 ∧
      LinearMap.funLeft R R Fin.succ y ∈ P.map (LinearMap.funLeft R R Fin.succ) := by
  refine ⟨fun hy ↦ ⟨hdvd y hy, mem_map_of_mem hy⟩, ?_⟩
  rintro ⟨⟨d, hd⟩, ⟨k, hk, hky⟩⟩
  obtain ⟨e, he⟩ := hdvd k hk
  -- `y = k + (d - e) • a e_0`, comparing coordinates.
  have : y = k + (d - e) • Pi.single 0 a := by
    ext j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp [hd, he]
      ring
    · simpa using congr_fun hky.symm i
  rw [this]
  exact add_mem hk (smul_mem _ _ ha)

end CommRing

end Submodule
