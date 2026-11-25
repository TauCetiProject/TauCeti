/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Ideals under pointwise group actions

A group acting on a ring by ring automorphisms permutes its maximal ideals: the translate
`g • I` is the preimage of `I` under the ring automorphism `g⁻¹`. This is the maximal-ideal
companion of Mathlib's `Ideal.IsPrime.smul`. In a commutative semiring, distinct ideals in the
orbit of a maximal ideal are therefore pairwise coprime. For an `A`-linear action on `S`, any
extended ideal `I.map (algebraMap A S)` and any ideal stabilized by `g` map into themselves under
`MulSemiringAction.toAlgHom A S g`.

## Main results

* `Ideal.IsMaximal.smul`: the translate of a maximal ideal is maximal.
* `Ideal.pairwise_isCoprime_orbit_of_isMaximal`: distinct ideals in the orbit of a maximal ideal
  are pairwise coprime.
* `Ideal.map_le_comap_toAlgHom`: an extended ideal from `A` is mapped into itself by any `A`-linear
  action element.
* `Ideal.le_comap_toAlgHom_of_mem_stabilizer`: an element of `MulAction.stabilizer G I` maps `I`
  into itself via `MulSemiringAction.toAlgHom`.
-/

public section

open scoped Pointwise

namespace Ideal

section Semiring

variable {M R : Type*} [Group M] [Semiring R] [MulSemiringAction M R]

/-- **Translates of maximal ideals are maximal.** The translate `g • I` is the preimage of `I`
under a ring automorphism, so it is maximal whenever `I` is. -/
instance IsMaximal.smul {I : Ideal R} [I.IsMaximal] (g : M) : (g • I).IsMaximal := by
  rw [I.pointwise_smul_eq_comap]
  infer_instance

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Distinct ideals in the orbit of a maximal ideal under a group action by ring automorphisms
are pairwise coprime. -/
theorem pairwise_isCoprime_orbit_of_isMaximal (I : Ideal R) [I.IsMaximal] (G : Type*) [Group G]
    [MulSemiringAction G R] :
    (MulAction.orbit G I).Pairwise IsCoprime := by
  rintro P hP Q hQ hne
  obtain ⟨g₁, rfl⟩ := MulAction.mem_orbit_iff.mp hP
  obtain ⟨g₂, rfl⟩ := MulAction.mem_orbit_iff.mp hQ
  exact isCoprime_of_isMaximal hne

end CommSemiring

/-- Extending an ideal of `A` to `S` gives an ideal mapped into itself by any `A`-linear action of
`G`. -/
theorem map_le_comap_toAlgHom {A S G : Type*} [CommSemiring A] [Semiring S] [Algebra A S]
    [Monoid G] [MulSemiringAction G S] [SMulCommClass G A S] (I : Ideal A) (g : G) :
    I.map (algebraMap A S) ≤ (I.map (algebraMap A S)).comap (MulSemiringAction.toAlgHom A S g) :=
  map_le_iff_le_comap.mpr fun a ha ↦
    mem_comap.mpr (mem_comap.mpr
      (((MulSemiringAction.toAlgHom A S g).commutes a).symm ▸
        mem_map_of_mem (algebraMap A S) ha))

/-- An element of `MulAction.stabilizer G I` maps `I` into itself via
`MulSemiringAction.toAlgHom`. -/
theorem le_comap_toAlgHom_of_mem_stabilizer {A S G : Type*} [CommSemiring A] [Semiring S]
    [Algebra A S] [Group G] [MulSemiringAction G S] [SMulCommClass G A S] (I : Ideal S) {g : G}
    (hg : g ∈ MulAction.stabilizer G I) :
    I ≤ I.comap (MulSemiringAction.toAlgHom A S g) := by
  have hg' : g • I = I := MulAction.mem_stabilizer_iff.mp hg
  intro s hs
  rw [mem_comap, MulSemiringAction.toAlgHom_apply, ← hg']
  exact smul_mem_pointwise_smul g s I hs

end Ideal
