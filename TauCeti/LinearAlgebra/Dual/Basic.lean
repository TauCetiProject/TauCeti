/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

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

/-- Contracting two functionals at a vector outside their common kernel adds its line
to that common kernel.

Adapted from `Mei/LinearAlgebra/Dual/Kernel.lean`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0; Mei contributors, author Codex). -/
theorem ker_apply_smul_sub_apply_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) {v : V} (hv : v ∉ f.ker ⊓ g.ker) :
    (f v • g - g v • f).ker = (f.ker ⊓ g.ker) ⊔ K ∙ v := by
  have step (f g : V →ₗ[K] K) (hf : f v ≠ 0) :
      (f v • g - g v • f).ker = (f.ker ⊓ g.ker) ⊔ K ∙ v := by
    have hmem (x : V) : x ∈ (f v • g - g v • f).ker ↔ f v * g x = g v * f x := by
      simp only [mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero]
    have hline : K ∙ v ≤ (f v • g - g v • f).ker :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr ((hmem v).mpr (mul_comm _ _))
    have hinter : f.ker ⊓ (f v • g - g v • f).ker = f.ker ⊓ g.ker := by
      ext x
      constructor
      · intro hx
        obtain ⟨hfx, hx⟩ := Submodule.mem_inf.mp hx
        have hzero : f v * g x = 0 := by
          simpa only [mem_ker.mp hfx, mul_zero] using (hmem x).mp hx
        exact Submodule.mem_inf.mpr ⟨hfx, mem_ker.mpr ((mul_eq_zero.mp hzero).resolve_left hf)⟩
      · intro hx
        obtain ⟨hfx, hgx⟩ := Submodule.mem_inf.mp hx
        exact Submodule.mem_inf.mpr ⟨hfx, (hmem x).mpr (by
          simp only [mem_ker.mp hfx, mem_ker.mp hgx, mul_zero])⟩
    calc
      _ = (K ∙ v ⊔ f.ker) ⊓ (f v • g - g v • f).ker := by
        rw [span_singleton_sup_ker_eq_top f hf, top_inf_eq]
      _ = K ∙ v ⊔ f.ker ⊓ (f v • g - g v • f).ker := sup_inf_assoc_of_le _ hline
      _ = _ := by rw [hinter, sup_comm]
  by_cases hf : f v = 0
  · have hg : g v ≠ 0 := fun hg => hv (Submodule.mem_inf.mpr
      ⟨LinearMap.mem_ker.mpr hf, LinearMap.mem_ker.mpr hg⟩)
    have hswap : g v • f - f v • g = -(f v • g - g v • f) := (neg_sub _ _).symm
    have hs := step g f hg
    rw [hswap, ker_neg, inf_comm] at hs
    exact hs
  · exact step f g hf

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
