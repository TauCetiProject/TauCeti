/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Graded.LinearMap
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotence of homogeneous endomorphisms of nonzero degree

Let `𝒜 : ℤ → Submodule R M` be an exhaustive grading of `M` (its pieces span `M`) with only
finitely many nonzero pieces. An endomorphism of nonzero degree `c` moves each piece `𝒜 p` into
`𝒜 (p + c)`, so a long enough power carries every nonzero piece outside the finite support of the
grading. Hence the endomorphism is nilpotent, with one exponent for the whole module, without any
finiteness assumption on `M` itself. This applies for instance to the raising and lowering
operators of a finite-support integer-graded vector space.

More generally, an endomorphism that strictly raises the degree, sending each piece into the sum
of the pieces of higher degree without being homogeneous, is nilpotent for the same reason.

## Main results

* `LinearMap.isNilpotent_of_le_comap_iSup_lt`: an endomorphism that strictly raises the degree of
  an exhaustive finite-support `ℤ`-grading is nilpotent.
* `LinearMap.IsHomogeneous.isNilpotent`: an endomorphism of nonzero degree for an
  exhaustive finite-support `ℤ`-grading is nilpotent.
-/

public section

namespace LinearMap

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {𝒜 : ℤ → Submodule R M}

/-- An endomorphism that strictly raises the degree of an exhaustive `ℤ`-grading with finitely
many nonzero pieces is nilpotent: if it sends each piece `𝒜 p` into the sum of the pieces of degree
greater than `p`, a long enough power carries everything past the top of the support. -/
theorem isNilpotent_of_le_comap_iSup_lt (h𝒜 : ⨆ a, 𝒜 a = ⊤) (hfin : {a | 𝒜 a ≠ ⊥}.Finite)
    {f : Module.End R M} (hf : ∀ p, 𝒜 p ≤ (⨆ (q) (_ : p < q), 𝒜 q).comap f) :
    IsNilpotent f := by
  -- `F n` is the sum of the pieces of degree at least `n`, and `f` maps it into `F (n + 1)`.
  set F : ℤ → Submodule R M := fun n ↦ ⨆ (q) (_ : n ≤ q), 𝒜 q
  have hstep (n : ℤ) : F n ≤ (F (n + 1)).comap f :=
    iSup₂_le fun p hp ↦ (hf p).trans <| Submodule.comap_mono <|
      iSup₂_le fun q hq ↦ le_iSup₂_of_le (f := fun q (_ : n + 1 ≤ q) ↦ 𝒜 q) q (by omega) le_rfl
  have hpow (k : ℕ) (n : ℤ) : F n ≤ (F (n + k)).comap (f ^ k) := by
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      rw [Submodule.mem_comap, pow_succ', mul_apply_eq_comp, Nat.cast_succ, ← add_assoc]
      exact hstep _ (ih hv)
  -- the support lies in `[lo, hi]`, so `F lo = ⊤` and `F (hi + 1) = ⊥`
  obtain ⟨hi, hhi⟩ := hfin.bddAbove
  obtain ⟨lo, hlo⟩ := hfin.bddBelow
  have hbot {p : ℤ} (hp : p ∉ {a | 𝒜 a ≠ ⊥}) : 𝒜 p = ⊥ := by simpa using hp
  have htop : F lo = ⊤ := eq_top_iff.mpr <| h𝒜 ▸ iSup_le fun p ↦ by
    by_cases hp : lo ≤ p
    · exact le_iSup₂_of_le p hp le_rfl
    · exact (hbot fun h ↦ hp (hlo h)).le.trans bot_le
  have hFbot : F (lo + (hi + 1 - lo).toNat) = ⊥ :=
    eq_bot_iff.mpr <| iSup₂_le fun p hp ↦ (hbot fun h ↦ by have := hhi h; omega).le
  refine ⟨(hi + 1 - lo).toNat, LinearMap.ext fun v ↦ ?_⟩
  have hv := hpow (hi + 1 - lo).toNat lo (htop ▸ Submodule.mem_top : v ∈ F lo)
  rw [Submodule.mem_comap, hFbot, Submodule.mem_bot] at hv
  simpa using hv

/-- An endomorphism of nonzero degree for an exhaustive `ℤ`-grading with finitely many nonzero
pieces is nilpotent. -/
theorem IsHomogeneous.isNilpotent (h𝒜 : ⨆ a, 𝒜 a = ⊤) (hfin : {a | 𝒜 a ≠ ⊥}.Finite)
    {f : Module.End R M} {c : ℤ} (hf : IsHomogeneous f 𝒜 𝒜 c) (hc : c ≠ 0) :
    IsNilpotent f := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · -- reverse the grading, so that `f` raises the degree by `-c > 0`
    refine isNilpotent_of_le_comap_iSup_lt (𝒜 := fun a ↦ 𝒜 (-a))
      (by rwa [← (Equiv.neg ℤ).iSup_comp] at h𝒜) (hfin.preimage neg_injective.injOn)
      fun p x hx ↦ ?_
    refine le_iSup₂_of_le (f := fun q (_ : p < q) ↦ 𝒜 (-q)) (p - c) (by omega) le_rfl ?_
    simpa [neg_sub, sub_eq_neg_add] using hf.map_mem hx
  · exact isNilpotent_of_le_comap_iSup_lt h𝒜 hfin fun p x hx ↦
      le_iSup₂_of_le (f := fun q (_ : p < q) ↦ 𝒜 q) (p + c) (by omega) le_rfl (hf.map_mem hx)

end LinearMap
