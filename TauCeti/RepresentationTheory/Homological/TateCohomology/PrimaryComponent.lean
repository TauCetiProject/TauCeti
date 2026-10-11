/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Linear

/-!
# Primary components of Tate cohomology

The `p`-primary component of Tate cohomology vanishes when multiplication by `p` acts bijectively
on the coefficient representation. Scalar multiplication on the coefficients induces the same
scalar multiplication on Tate cohomology, so an invertible scalar acts injectively on every Tate
group; this excludes nonzero elements killed by a power of `p`.
-/

public section

open CategoryTheory Representation

namespace TauCeti.TateCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- **An invertible scalar contributes no primary Tate cohomology.** If multiplication by a natural
number `p` is bijective on a representation `A`, then the `p`-primary component of `Ĥⁿ(S, A)` is
zero for every subgroup `S` and every integer degree `n`. -/
theorem primaryComponent_tateCohomology_eq_bot (p : ℕ) (A : Rep k G)
    (hA : Function.Bijective fun x : A.V => (p : k) • x) (S : Subgroup G) [Fintype S]
    (n : ℤ) :
    AddCommGroup.primaryComponent (tateCohomology (Rep.res S.subtype A) n) p = ⊥ := by
  let B := Rep.res S.subtype A
  let e : B.V ≃ₗ[k] B.V :=
    LinearEquiv.ofBijective ((p : k) • LinearMap.id) (by
      change Function.Bijective (fun x : A.V => (p : k) • x)
      exact hA)
  let eRep : B.ρ.Equiv B.ρ := Representation.Equiv.mk e fun g ↦ by
    ext x
    simp [e]
  let eB : B ≅ B := Rep.mkIso eRep
  have heB : eB.hom = (p : k) • 𝟙 B := by
    ext x
    simp [eB, eRep, e, Rep.smul_hom]
  let F := tateCohomologyFunctor (R := k) (G := S) n
  let eH := F.mapIso eB
  have heH : eH.hom = (p : k) • 𝟙 (ModuleCat.of k (tateCohomology B n)) := by
    change F.map eB.hom = _
    calc
      F.map eB.hom = F.map ((p : k) • 𝟙 B) := congrArg F.map heB
      _ = (p : k) • F.map (𝟙 B) := F.map_smul _ _
      _ = (p : k) • 𝟙 (F.obj B) := by rw [F.map_id]
  have hpH : Function.Bijective fun x : tateCohomology B n => (p : k) • x := by
    have h := ConcreteCategory.bijective_of_isIso eH.hom
    have hfun : (fun x : F.obj B => (p : k) • x) = eH.hom := by
      funext x
      change (p : k) • x = eH.hom.hom x
      rw [heH]
      rfl
    change Function.Bijective (fun x : F.obj B => (p : k) • x)
    simpa only [← hfun] using h
  have hpH' : Function.Bijective fun x : tateCohomology B n => p • x := by
    simpa only [Nat.cast_smul_eq_nsmul] using hpH
  have hpPow (m : ℕ) : Function.Injective fun x : tateCohomology B n => p ^ m • x := by
    induction m with
    | zero => intro x y hxy; simpa using hxy
    | succ m ih =>
        intro x y hxy
        apply ih
        apply hpH'.1
        simpa only [pow_succ', Nat.cast_pow, Nat.cast_mul, smul_smul,
          Nat.cast_smul_eq_nsmul] using hxy
  rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨m, hm⟩ := AddCommGroup.mem_primaryComponent.mp hx
  exact (hpPow m) (by simpa using hm)

end TauCeti.TateCohomology
