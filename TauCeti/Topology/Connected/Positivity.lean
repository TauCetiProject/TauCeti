/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Propagation of positivity

On a preconnected space, local positive transfer between any two times propagates a positive
initial seed to every point at the terminal time.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollaries 4.14–4.15.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section
open Set Topology Filter

namespace TauCeti

/-- On a preconnected space, local positive transfer between two times in a slab propagates
one positive initial seed to every point at the terminal time. -/
theorem positive_everywhere_of_local_transfer
    {M : Type u} [TopologicalSpace M] [PreconnectedSpace M]
    {a b : ℝ} (hab : a < b) (f : ℝ → M → ℝ)
    (hlocal : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ s t : ℝ, a ≤ s → s < t → t ≤ b → ∀ y ∈ U, ∀ z ∈ U,
        0 < f s y → 0 < f t z)
    (p : M) (hp : 0 < f a p) : ∀ x : M, 0 < f b x := by
  let S : Set M := {x | ∃ t ∈ Ioo a b, 0 < f t x}
  have hSo : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨U, hU, hxU, htransfer⟩ := hlocal x
    apply mem_of_superset (hU.mem_nhds hxU)
    intro y hy
    refine ⟨(t + b) / 2, ⟨by linarith [ht.1, ht.2], by linarith [ht.2]⟩, ?_⟩
    exact htransfer t ((t + b) / 2) ht.1.le (by linarith [ht.2]) (by linarith [ht.2])
      x hxU y hy htx
  have hSne : S.Nonempty := by
    obtain ⟨U, _, hpU, htransfer⟩ := hlocal p
    refine ⟨p, (a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    exact htransfer a ((a + b) / 2) le_rfl (by linarith) (by linarith) p hpU p hpU hp
  have hSc : IsClosed S := by
    apply isClosed_of_closure_subset
    intro x hx
    obtain ⟨U, hU, hxU, htransfer⟩ := hlocal x
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff_nhds.mp hx U (hU.mem_nhds hxU)
    obtain ⟨t, ht, hty⟩ := hyS
    refine ⟨(t + b) / 2, ⟨by linarith [ht.1, ht.2], by linarith [ht.2]⟩, ?_⟩
    exact htransfer t ((t + b) / 2) ht.1.le (by linarith [ht.2]) (by linarith [ht.2])
      y hyU x hxU hty
  have hSclopen : IsClopen S := ⟨hSc, hSo⟩
  have hSuniv : S = univ := hSclopen.eq_univ hSne
  intro x
  have hxS : x ∈ S := by rw [hSuniv]; exact mem_univ x
  obtain ⟨t, ht, htx⟩ := hxS
  obtain ⟨U, _, hxU, htransfer⟩ := hlocal x
  exact htransfer t b ht.1.le ht.2 le_rfl x hxU x hxU htx

end TauCeti
