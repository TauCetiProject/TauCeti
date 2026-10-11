/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
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

/-- A scalar acting bijectively on a representation acts bijectively on its Tate cohomology. -/
theorem bijective_smul_tateCohomology [Fintype G] (c : k) (A : Rep k G)
    (hA : Function.Bijective fun x : A.V => c • x) (n : ℤ) :
    Function.Bijective fun x : tateCohomology A n => c • x := by
  let e : A.V ≃ₗ[k] A.V :=
    LinearEquiv.ofBijective (c • LinearMap.id) (by
      -- The underlying function of this scalar multiple of the identity is `c • ·`.
      change Function.Bijective (fun x : A.V => c • x)
      exact hA)
  let eRep : A.ρ.Equiv A.ρ := Representation.Equiv.mk e fun g ↦ by
    ext x
    simp [e]
  let eA : A ≅ A := Rep.mkIso eRep
  have heA : eA.hom = c • 𝟙 A := by
    ext x
    simp [eA, eRep, e, Rep.smul_hom]
  let F := tateCohomologyFunctor (R := k) (G := G) n
  let eH := F.mapIso eA
  have heH : eH.hom = c • 𝟙 (F.obj A) := by
    rw [Functor.mapIso_hom]
    calc
      F.map eA.hom = F.map (c • 𝟙 A) := congrArg F.map heA
      _ = c • F.map (𝟙 A) := F.map_smul _ _
      _ = c • 𝟙 (F.obj A) := by rw [F.map_id]
  have h := ConcreteCategory.bijective_of_isIso eH.hom
  have hfun : (fun x : F.obj A => c • x) = eH.hom := by
    funext x
    simp only [heH, ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_id,
      LinearMap.id_apply]
  simpa only [← hfun] using h

/-- **An invertible scalar contributes no primary Tate cohomology.** If multiplication by a natural
number `p` is bijective on a representation `A`, then the `p`-primary component of `Ĥⁿ(S, A)` is
zero for every finite subgroup `S` and every integer degree `n`. -/
theorem primaryComponent_tateCohomology_eq_bot (p : ℕ) (A : Rep k G)
    (hA : Function.Bijective fun x : A.V => (p : k) • x) (S : Subgroup G) [Fintype S]
    (n : ℤ) :
    AddCommGroup.primaryComponent (tateCohomology (Rep.res S.subtype A) n) p = ⊥ := by
  have hp : Function.Bijective fun x : tateCohomology (Rep.res S.subtype A) n =>
      (p : k) • x :=
    bijective_smul_tateCohomology (p : k) (Rep.res S.subtype A) (by simpa using hA) n
  apply TauCeti.primaryComponent_eq_bot_of_injective_nsmul
  simpa only [Nat.cast_smul_eq_nsmul] using hp.1

end TauCeti.TateCohomology
