/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Nonzero linear maps from modules cyclic at every maximal ideal

Over a domain, a nonzero linear map from a module cyclic at every maximal ideal
to a torsion-free module
is injective. This cyclicity hypothesis permits a denominator outside each maximal ideal
for each element; no global generator, finite generation or freeness is required.
-/

public section

namespace LinearMap

/-- A nonzero map from a module cyclic at every maximal ideal to a torsion-free module
over a domain
is injective. The generator may depend on the maximal ideal, and the denominator may also
depend on the element. -/
theorem injective_of_ne_zero_of_forall_isMaximal_exists_smul_eq_smul {R M N : Type*}
    [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]
    (f : M →ₗ[R] N) (hf : f ≠ 0)
    (hcyc : ∀ q : Ideal R, q.IsMaximal →
      ∃ m : M, ∀ x : M, ∃ s ∉ q, ∃ a : R, s • x = a • m) :
    Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  let I : Ideal R := Submodule.comap (LinearMap.toSpanSingleton R M x) ⊥
  suffices hI : I = ⊤ by
    have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using h1
  by_contra hI
  obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨m, hm⟩ := hcyc q hq
  obtain ⟨s, hs, a, ha⟩ := hm x
  by_cases ha0 : a = 0
  · exact hs (hIq (by simp [I, ha, ha0]))
  have hfm : f m = 0 := by
    have h : a • f m = 0 := by rw [← map_smul, ← ha, map_smul, hx, smul_zero]
    exact (smul_eq_zero.mp h).resolve_left ha0
  apply hf
  ext y
  obtain ⟨s, hs, b, hb⟩ := hm y
  have hs0 : s ≠ 0 := fun h ↦ hs (h ▸ q.zero_mem)
  have h : s • f y = 0 := by rw [← map_smul, hb, map_smul, hfm, smul_zero]
  exact (smul_eq_zero.mp h).resolve_left hs0

end LinearMap
