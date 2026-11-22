/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Common kernels and dual coannihilators

The dual coannihilator of the span of a family of functionals is their common
kernel. This relates equations defining a submodule to the span of its conormals,
without finiteness assumptions on either the family or the ambient module.
Contracting two functionals at a transverse vector adds its line to their common kernel.

## Attribution

Adapted from `Mei/LinearAlgebra/Dual/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author: Codex; original copyright: Mei contributors.

-/

public section

namespace Submodule

/-- The dual coannihilator of a set's span is the intersection of its kernels. -/
theorem dualCoannihilator_span {R M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set (Module.Dual R M)) :
    (span R s).dualCoannihilator = ⨅ f ∈ s, f.ker := by
  ext v
  rw [← SetLike.mem_coe, coe_dualCoannihilator_span]
  simp only [Set.mem_ofPred_eq, mem_iInf, LinearMap.mem_ker]

/-- The dual coannihilator of a family's span is the intersection of its kernels. -/
@[simp]
theorem dualCoannihilator_span_range {R M : Type*} {ι : Sort*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] (f : ι → Module.Dual R M) :
    (span R (Set.range f)).dualCoannihilator = ⨅ j, (f j).ker := by
  rw [dualCoannihilator_span, iInf_range]

end Submodule

namespace LinearMap

/-- If the two evaluations are coprime, contraction adds the line of the
evaluation vector to the common kernel, over any commutative ring.

Adapted from `Mei/LinearAlgebra/Dual/Kernel.lean`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0; Mei contributors, author Codex). -/
theorem ker_apply_smul_sub_apply_smul_of_isCoprime {R V : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    (f g : V →ₗ[R] R) {v : V} (hv : IsCoprime (f v) (g v)) :
    (f v • g - g v • f).ker = (f.ker ⊓ g.ker) ⊔ R ∙ v := by
  have hmem (x : V) : x ∈ (f v • g - g v • f).ker ↔ f v * g x = g v * f x := by
    simp only [mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero]
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, hab⟩ := hv
    let t := a * f x + b * g x
    have he := (hmem x).mp hx
    have hf : f x = t * f v := by
      dsimp only [t]
      linear_combination -(f x) * hab - b * he
    have hg : g x = t * g v := by
      dsimp only [t]
      linear_combination -(g x) * hab + a * he
    refine Submodule.mem_sup.mpr ⟨x - t • v, ?_, t • v,
      Submodule.mem_span_singleton.mpr ⟨t, rfl⟩, sub_add_cancel ..⟩
    exact Submodule.mem_inf.mpr
      ⟨mem_ker.mpr (by simp only [map_sub, map_smul, smul_eq_mul, hf, sub_self]),
        mem_ker.mpr (by simp only [map_sub, map_smul, smul_eq_mul, hg, sub_self])⟩
  · refine sup_le (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    · obtain ⟨hf, hg⟩ := Submodule.mem_inf.mp hx
      exact (hmem x).mpr (by simp only [mem_ker.mp hf, mem_ker.mp hg, mul_zero])
    · exact (hmem v).mpr (mul_comm _ _)

/-- Over a field, contracting at a vector outside the common kernel adds that
vector's line to the common kernel. -/
theorem ker_apply_smul_sub_apply_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) {v : V} (hv : v ∉ f.ker ⊓ g.ker) :
    (f v • g - g v • f).ker = (f.ker ⊓ g.ker) ⊔ K ∙ v := by
  apply ker_apply_smul_sub_apply_smul_of_isCoprime
  rw [Semifield.isCoprime_iff]
  by_contra! h
  exact hv (Submodule.mem_inf.mpr ⟨mem_ker.mpr h.1, mem_ker.mpr h.2⟩)

/-- Contracting independent functionals at a vector outside their common kernel
is nonzero. The coefficient ring need not be a field or a domain. -/
theorem apply_smul_sub_apply_smul_ne_zero {R V : Type*} [CommRing R]
    [AddCommMonoid V] [Module R V] (f g : V →ₗ[R] R)
    (hind : LinearIndependent R ![f, g]) {v : V} (hv : v ∉ f.ker ⊓ g.ker) :
    f v • g - g v • f ≠ 0 := by
  intro he
  have hz := hind.eq_zero_of_pair' (sub_eq_zero.mp he).symm
  exact hv (Submodule.mem_inf.mpr
    ⟨LinearMap.mem_ker.mpr hz.2, LinearMap.mem_ker.mpr hz.1⟩)

end LinearMap
