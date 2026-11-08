/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Torsor

/-!
# Fibres of the adic spectrum of a finite étale torsor

Let `(A, A⁺)` be a Huber pair, `B` a finite étale `G`-torsor over `A`
(`TauCeti.Algebra.IsFiniteEtaleTorsor G A B`) and `φ : (A, A⁺) → (B, B⁺)` a morphism of Huber
pairs whose underlying ring map is `algebraMap A B`. The group `G` acts on `Spv B` by
`(g • y)(b) = y(g⁻¹ • b)`. The fibres of `Spa(B, B⁺) → Spa(A, A⁺)` are exactly the intersections
of `Spa(B, B⁺)` with the `G`-orbits
(`TauCeti.Huber.Pair.Hom.spaComap_eq_spaComap_iff_of_isFiniteEtaleTorsor`). This is the
valuation-theoretic statement
`TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_isFiniteEtaleTorsor`
and needs no completeness, sheafiness or Tate hypothesis.

When `A` is Tate and `(B, B⁺)` is the Huber pair of the finite étale algebra `B` (natural
topology, `B⁺` the integral closure of the image of `A⁺`), the orbits lie in `Spa(B, B⁺)`, since
`A`-algebra automorphisms preserve it (`AlgHom.comap_mem_spa_integralClosure`),
and `Spa(B, B⁺) → Spa(A, A⁺)` is surjective, since a torsor is faithfully flat
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.surjective_spaComap`). So `Spa(B, B⁺) → Spa(A, A⁺)` is a
continuous bijection from the set of `G`-orbits of `Spa(B, B⁺)` onto `Spa(A, A⁺)`.

## References

* P. Scholze, *Étale cohomology of diamonds*, proof of Proposition 15.4.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, Remark 2.4.2, for the Huber pair of a finite étale algebra.
-/

public section

namespace TauCeti.Huber.Pair.Hom

open ValuationSpectrum

variable {G A B : Type*} [Group G] [Finite G] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsHuberRing B] [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsFiniteEtaleTorsor G A B]
  {S : Pair A} {T : Pair B}

/-- **The fibres of the adic spectrum of a finite étale torsor are the `G`-orbits.** For a
finite étale `G`-torsor `B` over `A` and a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` with
underlying map `algebraMap A B`, two points `x` and `y` of `Spa(B, B⁺)` have the same image in
`Spa(A, A⁺)` exactly when `y = g • x` for some `g ∈ G`, where `(g • x)(b) = x(g⁻¹ • b)`. -/
theorem spaComap_eq_spaComap_iff_of_isFiniteEtaleTorsor {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap A B) {x y : spa T.plus} :
    φ.spaComap x = φ.spaComap y ↔
      ∃ g : G, (y : Spv B) = comap (MulSemiringAction.toRingHom G B g⁻¹) x := by
  rw [← comap_algebraMap_eq_comap_algebraMap_iff_of_isFiniteEtaleTorsor (A := A), Subtype.ext_iff,
    spaComap_val, spaComap_val, hφ]

end TauCeti.Huber.Pair.Hom
