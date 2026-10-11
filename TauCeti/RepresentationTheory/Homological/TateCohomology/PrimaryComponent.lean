/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Linear
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.GroupTheory.Torsion

/-!
# Primary components of Tate cohomology

If multiplication by a natural number `p` is bijective on a representation, it is bijective on
its Tate cohomology in every degree. In particular the `p`-primary component of each Tate group
vanishes. This lets a cohomology comparison ignore coefficient groups on which multiplication
by `p` is invertible.
-/

public section

universe u

open CategoryTheory

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- Multiplication by `p` on every Tate cohomology group is bijective when it is bijective on
the coefficient representation. -/
theorem bijective_nsmul_tateCohomology (A : Rep.{u} k G) (p : ℕ)
    (hp : Function.Bijective (fun x : A.V ↦ p • x)) (n : ℤ) :
    Function.Bijective (fun x : tateCohomology A n ↦ p • x) := by
  -- The underlying map of `p • 𝟙 A` is multiplication by `p` on `A.V`.
  have hi : IsIso (p • (𝟙 A)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (by
      change Function.Bijective (fun x : A.V ↦ p • x)
      exact hp)
  have hiH : IsIso (p • (𝟙 (tateCohomology A n))) := by
    simpa [Functor.map_nsmul] using
      (inferInstance : IsIso ((tateCohomologyFunctor n).map (p • (𝟙 A))))
  exact (ConcreteCategory.isIso_iff_bijective _).mp hiH

/-- The `p`-primary component of Tate cohomology vanishes when multiplication by `p` is
bijective on the coefficient representation. This applies in every integer degree. -/
theorem primaryComponent_tateCohomology_eq_bot (A : Rep.{u} k G) (p : ℕ)
    (hp : Function.Bijective (fun x : A.V ↦ p • x)) (n : ℤ) :
    AddCommGroup.primaryComponent (tateCohomology A n) p = ⊥ := by
  have h_inj := (bijective_nsmul_tateCohomology A p hp n).1
  have hpow (j : ℕ) (x : tateCohomology A n) (hx : p ^ j • x = 0) : x = 0 := by
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      apply ih
      apply h_inj
      simpa [pow_succ', mul_smul] using hx
  ext x
  simp only [AddCommGroup.mem_primaryComponent, AddSubgroup.mem_bot]
  constructor
  · rintro ⟨j, hj⟩
    exact hpow j x hj
  · intro hx
    subst x
    exact ⟨0, by simp⟩

end TauCeti.TateCohomology
