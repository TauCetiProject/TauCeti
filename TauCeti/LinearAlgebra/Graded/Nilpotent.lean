/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Graded.LinearMap
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic.Linarith

/-!
# Nilpotence of homogeneous endomorphisms of nonzero degree

Let `𝒜 : ℤ → Submodule R M` be an exhaustive grading of `M` (its pieces span `M`) with only
finitely many nonzero pieces. An endomorphism of nonzero degree `c` moves each piece `𝒜 p` into
`𝒜 (p + c)`, so a long enough power carries every nonzero piece outside the finite support of the
grading. Hence the endomorphism is nilpotent, with one exponent for the whole module, without any
finiteness assumption on `M` itself. This applies for instance to the raising and lowering
operators of a finite-support integer-graded vector space.

## Main results

* `LinearMap.IsHomogeneous.isNilpotent`: an endomorphism of nonzero degree for an
  exhaustive finite-support `ℤ`-grading is nilpotent.
-/

public section

namespace LinearMap

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {𝒜 : ℤ → Submodule R M}

/-- An endomorphism of nonzero degree for an exhaustive `ℤ`-grading with finitely many nonzero
pieces is nilpotent. -/
theorem IsHomogeneous.isNilpotent (h𝒜 : ⨆ a, 𝒜 a = ⊤) (hfin : {a | 𝒜 a ≠ ⊥}.Finite)
    {f : Module.End R M} {c : ℤ} (hf : IsHomogeneous f 𝒜 𝒜 c) (hc : c ≠ 0) :
    IsNilpotent f := by
  obtain ⟨hi, hhi⟩ := hfin.bddAbove
  obtain ⟨lo, hlo⟩ := hfin.bddBelow
  -- `k` steps of size `|c| ≥ 1` leave the interval `[lo, hi]` containing the support.
  set k := (hi - lo + 1).toNat
  refine ⟨k, LinearMap.ker_eq_top.1 (eq_top_iff.2 (h𝒜 ▸ iSup_le fun p x hx ↦ ?_))⟩
  rw [LinearMap.mem_ker]
  by_cases hp : 𝒜 p = ⊥
  · rw [(Submodule.eq_bot_iff _).1 hp x hx, map_zero]
  have hmem := (hf.pow k).map_mem hx
  suffices hk : 𝒜 (p + k • c) = ⊥ from (Submodule.eq_bot_iff _).1 hk _ hmem
  by_contra hk
  have h₁ := hhi hp
  have h₂ := hlo hp
  have h₃ := hhi hk
  have h₄ := hlo hk
  have hk' : (k : ℤ) = hi - lo + 1 := Int.toNat_of_nonneg (by linarith)
  rw [nsmul_eq_mul] at h₃ h₄
  rcases lt_or_gt_of_ne hc with hc | hc
  · nlinarith
  · nlinarith

end LinearMap
