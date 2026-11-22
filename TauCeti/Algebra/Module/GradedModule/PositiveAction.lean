/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMulAction
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Positive-degree action on internally graded modules

For an internally `ℤ`-graded module `M` over a `ℤ`-graded `k`-algebra `A`, the positive-degree
action `A₊ M := (⨆ i > 0, 𝒜 i) • ⊤` is a homogeneous `k`-submodule stable under degree-zero
scalars `𝒜 0`. Its degree-`p` homogeneous component consists of sums of products `a • y` with
`a ∈ 𝒜 i` (`0 < i`) and `y ∈ M_{p - i}`.

## Main results

* `TauCeti.InternalGrading.decompose_mem_span_of_mem_positive_smul_top`: the degree-`p` component
  of an element of `A₊ M` lies in the `k`-span of products `a • y` with `a ∈ 𝒜 i` (`i > 0`) and
  `y ∈ M_{p - i}`.
* `TauCeti.InternalGrading.isHomogeneous_positive_smul_top`: `A₊ M` is a homogeneous submodule.
* `TauCeti.InternalGrading.smul_mem_positive_smul_top`: degree-zero scalars preserve `A₊ M`.
-/

public section

namespace TauCeti.InternalGrading

open _root_.DirectSum

universe uk uA uM

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
  {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝒜 : ℤ → Submodule k A) {G : InternalGrading k M ℤ} [SetLike.GradedSMul 𝒜 G.piece]

/-- The degree-`p` component of an element of `A₊ M` is a sum of products `a • y` with `a` of
some positive degree `i` and `y` of degree `p - i`. -/
theorem decompose_mem_span_of_mem_positive_smul_top {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) (p : ℤ) :
    (decompose G.piece x p : M) ∈ Submodule.span k
      {z | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ G.piece (p - i), a • y = z} := by
  classical
  set S := Submodule.span k {z | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ G.piece (p - i), a • y = z}
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
  · refine Submodule.iSup_induction _ (motive := fun a =>
      (decompose G.piece (a • y) p : M) ∈ S) ha (fun i a ha => ?_) ?_ ?_
    · refine Submodule.iSup_induction _ (motive := fun a =>
        (decompose G.piece (a • y) p : M) ∈ S) ha (fun hi a ha => ?_) ?_ ?_
      · let f : M →ₗ[k] M := Algebra.lsmul k k M a
        have hf : LinearMap.IsHomogeneous f G.piece G.piece i :=
          LinearMap.isHomogeneous_def.mpr fun q z hz => by
            simpa [f, add_comm] using SetLike.GradedSMul.smul_mem ha hz
        have h := hf.map_decompose (p - i) y
        rw [sub_add_cancel] at h
        simpa only [f, Algebra.lsmul_apply] using h ▸ Submodule.subset_span
          ⟨i, hi, a, ha, _, (decompose G.piece y (p - i)).property, rfl⟩
      · simp
      · intro a b ha hb
        simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
          S.add_mem ha hb
    · simp
    · intro a b ha hb
      simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
        S.add_mem ha hb
  · simpa only [decompose_add, DirectSum.add_apply, Submodule.coe_add] using S.add_mem hx hy

/-- The positive-degree action `A₊ M` is a homogeneous submodule. -/
theorem isHomogeneous_positive_smul_top :
    SetLike.IsHomogeneous G.piece ((⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) := by
  intro p x hx
  refine Submodule.span_le.mpr ?_ (decompose_mem_span_of_mem_positive_smul_top 𝒜 hx p)
  rintro _ ⟨i, hi, a, ha, y, -, rfl⟩
  exact Submodule.smul_mem_smul (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ha))
    Submodule.mem_top

variable {𝒜} in
/-- Degree-zero scalars preserve the positive-degree action `A₊ M`. -/
theorem smul_mem_positive_smul_top [SetLike.GradedMul 𝒜] {a : A} (ha : a ∈ 𝒜 0) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    a • x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  have hmul : ∀ b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i, a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
    intro b hb
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i)
      hb (fun i b hb => ?_) (by simp) (fun b c hb hc => by simpa [mul_add] using add_mem hb hc)
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i)
      hb (fun hi b hb => ?_) (by simp) (fun b c hb hc => by simpa [mul_add] using add_mem hb hc)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi
      (by simpa using SetLike.GradedMul.mul_mem ha hb))
  refine Submodule.smul_induction_on hx (fun b hb y _ => ?_) (fun x y hx hy => ?_)
  · rw [← mul_smul]
    exact Submodule.smul_mem_smul (hmul b hb) Submodule.mem_top
  · simpa only [smul_add] using Submodule.add_mem _ hx hy

end TauCeti.InternalGrading
