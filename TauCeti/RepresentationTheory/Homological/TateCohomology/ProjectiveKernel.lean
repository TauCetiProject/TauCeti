/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.IsoCriterion
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Projective

/-!
# Tate cohomology isomorphisms have projective kernels

Let `G` be a finite group and `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` a short exact sequence of representations
of `G` over an integral domain `k` of characteristic zero in which every prime number is a unit or
generates a maximal ideal, such as `ℤ` or `ℤ_[p]`. Suppose that `X₁` is projective over
`k`, and that for every subgroup `S` of `G` of prime-power order the map `X₂ ⟶ X₃` induces on the
Tate cohomology of `S` a surjection in degree `q - 1`, a bijection in degree `q` and an injection in
degree `q + 1`. Then `X₁` is a projective `k[G]`-module.

Indeed, Tate's isomorphism criterion
(`TauCeti.TateCohomology.map_res_bijective_of_forall_isPGroup`) upgrades the hypothesis to
bijectivity in every degree on every subgroup, so the long exact sequence makes `X₁`
cohomologically trivial, and the theorem of Nakayama and Rim in its lattice form
(`Rep.projective_of_isZero_res`) makes it projective. This is a converse of the fact that a
surjection with projective kernel induces isomorphisms in positive degrees
(`TauCeti.groupCohomology.isIso_map_of_surjective_of_projective_ker`). It is how one recognizes
that the kernel of a map between two class modules, such as a relation module and the completed
multiplicative group of a local field, is projective from its effect on degree-two cohomology.

## Main statements

* `TauCeti.TateCohomology.projective_X₁_of_forall_isPGroup`: the kernel of a morphism inducing
  isomorphisms on Tate cohomology in three consecutive degrees on every subgroup of prime-power
  order is projective, provided it is projective over `k`.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §§5–6.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.1.4) and
  the proof of (7.4.2).
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Finite G] [IsDomain k] [CharZero k]

/-- **A Tate cohomology isomorphism has a projective kernel.** Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a
short exact sequence of representations of a finite group `G` over an integral domain `k` of
characteristic zero in which every prime number is a unit or generates a maximal ideal, with `X₁`
projective over `k`. If for every subgroup `S` of prime-power order the map `X₂ ⟶ X₃` induces on
the Tate cohomology of `S` a surjection in degree `q - 1`, a bijection in degree `q` and an
injection in degree `q + 1`, then `X₁` is a projective `k[G]`-module. -/
theorem projective_X₁_of_forall_isPGroup
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    {T : ShortComplex (Rep k G)} (hT : T.ShortExact) [Module.Projective k T.X₁.V] {q : ℤ}
    (hsurj : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Surjective ((tateCohomologyFunctor (q - 1)).map ((resFunctor S.subtype).map T.g)))
    (hbij : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Bijective ((tateCohomologyFunctor q).map ((resFunctor S.subtype).map T.g)))
    (hinj : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Injective ((tateCohomologyFunctor (q + 1)).map ((resFunctor S.subtype).map T.g))) :
    Module.Projective (MonoidAlgebra k G) T.X₁.ρ.asModule :=
  Rep.projective_of_isZero_res hk T.X₁ fun S _ n ↦
    -- On `S`, the map `X₂ ⟶ X₃` is bijective in every degree, so `H-hat^n(S, X₁)` vanishes.
    isZero_X₁_of_surjective_of_injective ((Rep.shortExact_res S.subtype).2 hT) (n - 1) n
      (by omega) (map_res_bijective_of_forall_isPGroup T.g hsurj hbij hinj S (n - 1)).2
      (map_res_bijective_of_forall_isPGroup T.g hsurj hbij hinj S n).1

end TauCeti.TateCohomology
