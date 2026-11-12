/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Linear
import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees

/-!
# Primary components of Tate cohomology

The `p`-primary component of Tate cohomology vanishes when multiplication by `p` acts bijectively
on the coefficient representation. Scalar multiplication on the coefficients induces the same
scalar multiplication on Tate cohomology, so an invertible scalar acts injectively on every Tate
group; this excludes nonzero elements killed by a power of `p`.

With the long exact sequence, the `p`-primary components of Tate cohomology of a finite group `G`
are therefore unchanged along a short exact sequence `0 → X₁ → X₂ → X₃ → 0` one of whose outer
terms has bijective multiplication by a prime `p`. If `p` is bijective on `X₁`, the map
`H_Tateⁿ(G, X₂) → H_Tateⁿ(G, X₃)` is a bijection of `p`-primary components
(`TauCeti.TateCohomology.bijOn_pPowerTorsion_map_g`); if it is bijective on `X₃`, so is
`H_Tateⁿ(G, X₁) → H_Tateⁿ(G, X₂)` (`TauCeti.TateCohomology.bijOn_pPowerTorsion_map_f`). The torsion
argument is `TauCeti.injOn_pPowerTorsion_of_exact` and `TauCeti.surjOn_pPowerTorsion_of_exact`,
which use that all the groups involved are torsion
(`TauCeti.TateCohomology.isAddTorsion_tateCohomology`), being killed by `|G|`
(`TauCeti.TateCohomology.natCard_nsmul_eq_zero`). Factoring a morphism through its image, it
follows that a morphism whose kernel and cokernel have bijective multiplication by `p` induces
bijections of `p`-primary components (`TauCeti.TateCohomology.bijOn_pPowerTorsion_map`).

## Main statements

* `TauCeti.TateCohomology.pPowerTorsion_tateCohomology_eq_bot`: the `p`-power torsion of
  `H_Tateⁿ(G, A)` is trivial when multiplication by `p` is bijective on `A`.
* `TauCeti.TateCohomology.primaryComponent_tateCohomology_eq_bot`: the `p`-primary component of
  `H_Tateⁿ(S, A)` is trivial when multiplication by `p` is bijective on `A`.
* `TauCeti.TateCohomology.bijOn_pPowerTorsion_map_g`,
  `TauCeti.TateCohomology.bijOn_pPowerTorsion_map_f`: along a short exact sequence whose first,
  respectively last, term has bijective multiplication by a prime `p`, the induced maps are
  bijections of `p`-primary components.
* `TauCeti.TateCohomology.bijOn_pPowerTorsion_map`: a morphism whose kernel and cokernel have
  bijective multiplication by a prime `p` induces bijections of `p`-primary components.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII.
* K. S. Brown, *Cohomology of Groups*, Chapter VI.
-/

public section

open CategoryTheory Limits Representation

namespace TauCeti.TateCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The `p`-power torsion of every Tate cohomology group of a representation of a finite group on
which multiplication by `p` is bijective is trivial. -/
theorem pPowerTorsion_tateCohomology_eq_bot [Fintype G] {A : Rep k G} {p : ℕ}
    (hp : Function.Bijective fun a : A.V ↦ p • a) (n : ℤ) :
    pPowerTorsion p k (tateCohomology A n) = ⊥ := by
  have hinj : Function.Injective fun x : tateCohomology A n ↦ p • x := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      (smul_bijective (p : k) A (by simpa only [Nat.cast_smul_eq_nsmul] using hp) n).1
  have h := TauCeti.primaryComponent_eq_bot_of_injective_nsmul hinj
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  have hx' : x ∈ AddCommGroup.primaryComponent (tateCohomology A n) p :=
    AddCommGroup.mem_primaryComponent.mpr (mem_pPowerTorsion_iff.mp hx)
  rwa [h, AddSubgroup.mem_bot] at hx'

/-- **An invertible scalar contributes no primary Tate cohomology.** If multiplication by a natural
number `p` is bijective on a representation `A`, then the `p`-primary component of
`H_Tateⁿ(S, A)` is zero for every finite subgroup `S` and every integer degree `n`. -/
theorem primaryComponent_tateCohomology_eq_bot (p : ℕ) (A : Rep k G)
    (hA : Function.Bijective fun x : A.V => (p : k) • x) (S : Subgroup G) [Fintype S]
    (n : ℤ) :
    AddCommGroup.primaryComponent (tateCohomology (Rep.res S.subtype A) n) p = ⊥ := by
  have h := pPowerTorsion_tateCohomology_eq_bot (A := Rep.res S.subtype A)
    (by simpa only [Nat.cast_smul_eq_nsmul] using hA) n
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun x hx ↦ ?_
  have hx' : x ∈ pPowerTorsion p k (tateCohomology (Rep.res S.subtype A) n) :=
    mem_pPowerTorsion_iff.mpr (AddCommGroup.mem_primaryComponent.mp hx)
  rwa [h, Submodule.mem_bot] at hx'

section ShortExact

variable [Fintype G]

variable {S : ShortComplex (Rep k G)} (hS : S.ShortExact) {p : ℕ} [Fact p.Prime]
include hS

/-- Along a short exact sequence `0 → X₁ → X₂ → X₃ → 0` on whose first term multiplication by a
prime `p` is bijective, the map `H_Tateⁿ(G, X₂) → H_Tateⁿ(G, X₃)` is a bijection of `p`-primary
components. -/
theorem bijOn_pPowerTorsion_map_g (hp : Function.Bijective fun a : S.X₁.V ↦ p • a) (n : ℤ) :
    Set.BijOn ((tateCohomologyFunctor n).map S.g) (pPowerTorsion p k (tateCohomology S.X₂ n))
      (pPowerTorsion p k (tateCohomology S.X₃ n)) := by
  refine ⟨mapsTo_pPowerTorsion _, ?_, ?_⟩
  · exact injOn_pPowerTorsion_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (_root_.TateCohomology.exact₂ hS n))
      (isAddTorsion_tateCohomology _ _)
      (pPowerTorsion_tateCohomology_eq_bot hp n)
  · exact surjOn_pPowerTorsion_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (_root_.TateCohomology.exact₃ hS n))
      (isAddTorsion_tateCohomology _ _)
      (pPowerTorsion_tateCohomology_eq_bot hp (n + 1))

/-- Along a short exact sequence `0 → X₁ → X₂ → X₃ → 0` on whose last term multiplication by a
prime `p` is bijective, the map `H_Tateⁿ(G, X₁) → H_Tateⁿ(G, X₂)` is a bijection of `p`-primary
components. -/
theorem bijOn_pPowerTorsion_map_f (hp : Function.Bijective fun a : S.X₃.V ↦ p • a) (n : ℤ) :
    Set.BijOn ((tateCohomologyFunctor n).map S.f) (pPowerTorsion p k (tateCohomology S.X₁ n))
      (pPowerTorsion p k (tateCohomology S.X₂ n)) := by
  refine ⟨mapsTo_pPowerTorsion _, ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact injOn_pPowerTorsion_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (_root_.TateCohomology.exact₁ hS m))
      (isAddTorsion_tateCohomology _ _)
      (pPowerTorsion_tateCohomology_eq_bot hp m)
  · exact surjOn_pPowerTorsion_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (_root_.TateCohomology.exact₂ hS n))
      (isAddTorsion_tateCohomology _ _)
      (pPowerTorsion_tateCohomology_eq_bot hp n)

end ShortExact

/-- **Morphisms with uniquely `p`-divisible kernel and cokernel.** If multiplication by a prime `p`
is bijective on the kernel and on the cokernel of a morphism `f : A ⟶ B` of representations of a
finite group `G`, then `H_Tateⁿ(G, A) → H_Tateⁿ(G, B)` is a bijection of `p`-primary
components. -/
theorem bijOn_pPowerTorsion_map [Fintype G] {A B : Rep k G} (f : A ⟶ B) {p : ℕ} [Fact p.Prime]
    (hK : Function.Bijective fun a : (kernel f).V ↦ p • a)
    (hC : Function.Bijective fun a : (cokernel f).V ↦ p • a) (n : ℤ) :
    Set.BijOn ((tateCohomologyFunctor n).map f) (pPowerTorsion p k (tateCohomology A n))
      (pPowerTorsion p k (tateCohomology B n)) := by
  -- `f` factors as `A ↠ coimage f ≅ image f ↪ B`, where the outer maps sit in the short exact
  -- sequences `0 → kernel f → A → coimage f → 0` and `0 → image f → B → cokernel f → 0`.
  have hπ := bijOn_pPowerTorsion_map_g (S := .mk _ _ (cokernel.condition (kernel.ι f)))
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) } hK n
  have hι := bijOn_pPowerTorsion_map_f (S := .mk _ _ (kernel.condition (cokernel.π f)))
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) } hC n
  let e := (tateCohomologyFunctor n).mapIso (Abelian.coimageIsoImage f)
  have hc : Set.BijOn e.hom (pPowerTorsion p k (tateCohomology (Abelian.coimage f) n))
      (pPowerTorsion p k (tateCohomology (Abelian.image f) n)) :=
    Set.InvOn.bijOn ⟨fun x _ ↦ e.hom_inv_id_apply x, fun y _ ↦ e.inv_hom_id_apply y⟩
      (mapsTo_pPowerTorsion _) (mapsTo_pPowerTorsion _)
  rw [← Abelian.coimage_image_factorisation f, Functor.map_comp, Functor.map_comp]
  exact (hι.comp hc).comp hπ

end TauCeti.TateCohomology
