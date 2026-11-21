/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Module.GradedModule.Nakayama
import TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# Graded Nakayama isomorphism criterion in `GradedModuleCat`

For a bounded-below graded module `P`, any degree-zero endomorphism `h : P ⟶ P` taking values in
the positive-degree action `A₊ P` is locally nilpotent, so `𝟙 P - h` is an isomorphism in
`GradedModuleCat 𝒜` (`TauCeti.GradedModuleCat.isIso_id_sub_of_mem_positive_smul_top`). Neither a
nonnegative grading on `𝒜` nor finite generation is required.

This categorical criterion depends only on `TauCeti.Algebra.Module.GradedModule.Nakayama` and
locally nilpotent endomorphisms, without importing projective-resolution or Ext machinery. It is
used in `TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution` to prove termwise uniqueness
of minimal graded projective resolutions.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded modules
  and Nakayama-type arguments.
-/

public section

namespace TauCeti

open CategoryTheory

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

namespace GradedModuleCat

private theorem pow_apply_eq_zero_of_mem_positive_smul_top
    {P : GradedModuleCat.{v} 𝒜} (h : P ⟶ P) (b : ℤ)
    (hbelow : ∀ p < b, P.grading.piece p = ⊥)
    (hh : ∀ x : P, h.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)) :
    ∀ (m : ℕ) {p : ℤ}, p < b + m → ∀ x ∈ P.grading.piece p, (h.hom ^ m) x = 0 := by
  classical
  intro m
  induction m with
  | zero =>
    intro p hp x hx
    rw [hbelow p (by omega), Submodule.mem_bot] at hx
    simp [hx]
  | succ m ih =>
    intro p hp x hx
    have hker : h.hom x ∈ LinearMap.ker (h.hom ^ m) := by
      have hmem := InternalGrading.decompose_mem_of_mem_positive_smul_top 𝒜
        (LinearMap.ker (h.hom ^ m)) (p := p)
        (fun q hq y hy => ih (by omega) y hy) (hh x)
      have hhom : h.hom x ∈ P.grading.piece p := by
        simpa only [add_zero] using h.isHomogeneous.map_mem hx
      rwa [DirectSum.decompose_of_mem_same P.grading.piece hhom] at hmem
    simpa only [pow_succ, mul_apply_eq_comp] using LinearMap.mem_ker.mp hker

/-- **Local-nilpotence isomorphism criterion for graded endomorphisms.** If a bounded-below graded
module `P` carries a degree-zero endomorphism `h` taking values in `A₊ P`, then `h` is locally
nilpotent and `𝟙 P - h` is an isomorphism in `GradedModuleCat 𝒜`. Neither a nonnegative grading
on `𝒜` nor finite generation is required. -/
theorem isIso_id_sub_of_mem_positive_smul_top {P : GradedModuleCat.{v} 𝒜}
    (h : P ⟶ P) (b : ℤ) (hbelow : ∀ p < b, P.grading.piece p = ⊥)
    (hh : ∀ x : P, h.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)) :
    IsIso (𝟙 P - h) := by
  classical
  have hpow := pow_apply_eq_zero_of_mem_positive_smul_top h b hbelow hh
  have hnil : ∀ x : P, ∃ m : ℕ, ((-h.hom) ^ m) x = 0 := fun x => by
    obtain ⟨u, hu⟩ := (DirectSum.decompose P.grading.piece x).support.finite_toSet.bddAbove
    refine ⟨(u - b + 1).toNat, (Module.End.neg_pow_apply_eq_zero_iff h.hom _ x).mpr ?_⟩
    rw [← DirectSum.sum_support_decompose P.grading.piece x, map_sum]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpu : p ≤ u := hu hp
    exact hpow _ (by omega) _ (DirectSum.decompose P.grading.piece x p).property
  have hunit : IsUnit (1 + (-h.hom)) :=
    Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero (-h.hom) hnil
  rw [isIso_iff_bijective]
  have hhom : (𝟙 P - h).hom = 1 + (-h.hom) := by
    rw [hom_sub, hom_id, sub_eq_add_neg]
    rfl
  rw [hhom]
  exact (Module.End.isUnit_iff _).mp hunit

end GradedModuleCat

end TauCeti
