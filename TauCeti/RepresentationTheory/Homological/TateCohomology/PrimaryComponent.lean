/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees

/-!
# The `p`-primary components of Tate cohomology

Let `G` be a finite group and `A` a representation of `G` over a commutative ring `k`.

**`p`-primary Tate cohomology sees only `p`.** If multiplication by a natural number `p` is
bijective on `A`, it induces a bijection of every `Ĥⁿ(G, A)`, by functoriality, so the `p`-primary
component `TauCeti.pPowerTorsion p k (tateCohomology A n)` of every Tate cohomology group of `A` is
trivial (`TauCeti.TateCohomology.pPowerTorsion_tateCohomology_eq_bot`). Applied to the restriction
of `A` to a subgroup `S`, on which multiplication by `p` is the same map, this is the vanishing of
the `p`-primary component of `Ĥⁿ(S, A)` for every subgroup `S` and every `n ∈ ℤ`.

With the long exact sequence, the `p`-primary components of Tate cohomology are therefore
unchanged along a short exact sequence `0 → X₁ → X₂ → X₃ → 0` one of whose outer terms has
bijective multiplication by a prime `p`. If `p` is bijective on `X₁`, the map
`Ĥⁿ(G, X₂) → Ĥⁿ(G, X₃)` is a bijection of `p`-primary components
(`TauCeti.TateCohomology.bijOn_pPowerTorsion_map_g`); if it is bijective on `X₃`, so is
`Ĥⁿ(G, X₁) → Ĥⁿ(G, X₂)` (`TauCeti.TateCohomology.bijOn_pPowerTorsion_map_f`). The torsion
argument is `TauCeti.injOn_pPowerTorsion_of_exact` and `TauCeti.surjOn_pPowerTorsion_of_exact`,
which use that all the groups involved are torsion, being killed by `|G|`
(`TauCeti.TateCohomology.natCard_nsmul_eq_zero`).

## Main statements

* `TauCeti.TateCohomology.nsmul_tateCohomology_bijective`: multiplication by `p` is bijective on
  Tate cohomology when it is bijective on the representation.
* `TauCeti.TateCohomology.pPowerTorsion_tateCohomology_eq_bot`: the `p`-primary component of the
  Tate cohomology of such a representation is trivial.
* `TauCeti.TateCohomology.bijOn_pPowerTorsion_map_g`,
  `TauCeti.TateCohomology.bijOn_pPowerTorsion_map_f`: along a short exact sequence whose first,
  respectively last, term has bijective multiplication by a prime `p`, the induced maps are
  bijections of `p`-primary components.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII.
* K. S. Brown, *Cohomology of Groups*, Chapter VI.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- If multiplication by a natural number `p` is bijective on `A`, then it is bijective on every
Tate cohomology group of `A`. -/
theorem nsmul_tateCohomology_bijective {A : Rep k G} {p : ℕ}
    (hp : Function.Bijective fun a : A.V ↦ p • a) (n : ℤ) :
    Function.Bijective fun x : tateCohomology A n ↦ p • x := by
  -- Multiplication by `p` on `Ĥⁿ(G, A)` is the map induced by the automorphism `p • 𝟙 A`.
  have : IsIso ((forget (Rep k G)).map (p • 𝟙 A)) := (isIso_iff_bijective _).mpr hp
  have : IsIso (p • 𝟙 A) := isIso_of_reflects_iso _ (forget (Rep k G))
  convert ConcreteCategory.bijective_of_isIso ((tateCohomologyFunctor n).map (p • 𝟙 A)) using 1
  ext x
  simp

/-- **`p`-primary Tate cohomology sees only `p`.** If multiplication by a natural number `p` is
bijective on `A`, then the `p`-primary component of every Tate cohomology group of `A` is trivial.
Applied to `Rep.res S.subtype A`, this holds for the Tate cohomology of every subgroup `S`. -/
theorem pPowerTorsion_tateCohomology_eq_bot {A : Rep k G} {p : ℕ}
    (hp : Function.Bijective fun a : A.V ↦ p • a) (n : ℤ) :
    pPowerTorsion p k (tateCohomology A n) = ⊥ := by
  have hinj := (nsmul_tateCohomology_bijective hp n).injective
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  obtain ⟨j, hj⟩ := mem_pPowerTorsion_iff.mp hx
  clear hx
  induction j generalizing x with
  | zero => simpa using hj
  | succ j ih => exact hinj ((ih (p • x) (by rwa [smul_smul, ← pow_succ])).trans (smul_zero p).symm)

variable {S : ShortComplex (Rep k G)} (hS : S.ShortExact) {p : ℕ} [Fact p.Prime]
include hS

/-- Along a short exact sequence `0 → X₁ → X₂ → X₃ → 0` on whose first term multiplication by a
prime `p` is bijective, the map `Ĥⁿ(G, X₂) → Ĥⁿ(G, X₃)` is a bijection of `p`-primary
components. -/
theorem bijOn_pPowerTorsion_map_g (hp : Function.Bijective fun a : S.X₁.V ↦ p • a) (n : ℤ) :
    Set.BijOn ((tateCohomologyFunctor n).map S.g) (pPowerTorsion p k (tateCohomology S.X₂ n))
      (pPowerTorsion p k (tateCohomology S.X₃ n)) := by
  refine ⟨fun x hx ↦ ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := mem_pPowerTorsion_iff.mp hx
    exact mem_pPowerTorsion_iff.mpr ⟨j, by rw [← map_nsmul, hj, map_zero]⟩
  · exact injOn_pPowerTorsion_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (_root_.TateCohomology.exact₂ hS n))
      (ExponentExists.isAddTorsion ⟨_, Nat.card_pos, natCard_nsmul_eq_zero⟩)
      (pPowerTorsion_tateCohomology_eq_bot hp n)
  · exact surjOn_pPowerTorsion_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (_root_.TateCohomology.exact₃ hS n))
      (ExponentExists.isAddTorsion ⟨_, Nat.card_pos, natCard_nsmul_eq_zero⟩)
      (pPowerTorsion_tateCohomology_eq_bot hp (n + 1))

/-- Along a short exact sequence `0 → X₁ → X₂ → X₃ → 0` on whose last term multiplication by a
prime `p` is bijective, the map `Ĥⁿ(G, X₁) → Ĥⁿ(G, X₂)` is a bijection of `p`-primary
components. -/
theorem bijOn_pPowerTorsion_map_f (hp : Function.Bijective fun a : S.X₃.V ↦ p • a) (n : ℤ) :
    Set.BijOn ((tateCohomologyFunctor n).map S.f) (pPowerTorsion p k (tateCohomology S.X₁ n))
      (pPowerTorsion p k (tateCohomology S.X₂ n)) := by
  refine ⟨fun x hx ↦ ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := mem_pPowerTorsion_iff.mp hx
    exact mem_pPowerTorsion_iff.mpr ⟨j, by rw [← map_nsmul, hj, map_zero]⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact injOn_pPowerTorsion_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (_root_.TateCohomology.exact₁ hS m))
      (ExponentExists.isAddTorsion ⟨_, Nat.card_pos, natCard_nsmul_eq_zero⟩)
      (pPowerTorsion_tateCohomology_eq_bot hp m)
  · exact surjOn_pPowerTorsion_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (_root_.TateCohomology.exact₂ hS n))
      (ExponentExists.isAddTorsion ⟨_, Nat.card_pos, natCard_nsmul_eq_zero⟩)
      (pPowerTorsion_tateCohomology_eq_bot hp n)

end TauCeti.TateCohomology
