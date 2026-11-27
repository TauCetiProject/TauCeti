/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.FiniteAlgebra
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Generalizing
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Action
public import TauCeti.RingTheory.Etale.Torsor.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Invariant

/-!
# The adic spectrum of a finite étale torsor

Let `(A, A⁺)` be a Huber pair, `B` a finite étale `G`-torsor over `A`
(`TauCeti.Algebra.IsFiniteEtaleTorsor G A B`) and `φ : (A, A⁺) → (B, B⁺)` a morphism of Huber
pairs whose underlying ring map is `algebraMap A B`. The group `G` acts on `Spv B` by
`(g • y)(b) = y(g⁻¹ • b)`. The fibres of `Spa(B, B⁺) → Spa(A, A⁺)` are exactly the intersections
of `Spa(B, B⁺)` with the `G`-orbits: a torsor satisfies `Algebra.IsInvariant A B G`
(`TauCeti.Algebra.IsFiniteEtaleTorsor.isInvariant`), so this is
`TauCeti.Huber.Pair.Hom.spaComap_eq_spaComap_iff_of_isInvariant`, which needs no completeness,
sheafiness or Tate hypothesis.

When `A` is Tate and `(B, B⁺)` is the Huber pair of the finite étale algebra `B` (natural
topology, `B⁺` the integral closure of the image of `A⁺`), the orbits lie in `Spa(B, B⁺)`, since
`A`-algebra automorphisms preserve it (`AlgHom.comap_mem_spa_integralClosure`),
and `Spa(B, B⁺) → Spa(A, A⁺)` is surjective, since a torsor is faithfully flat
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.surjective_spaComap`). So `Spa(B, B⁺) → Spa(A, A⁺)` is a
continuous bijection from the set of `G`-orbits of `Spa(B, B⁺)` onto `Spa(A, A⁺)`
(`TauCeti.Huber.Pair.Hom.surjective_spaComap_of_isFiniteEtaleTorsor`).

This bijection is a homeomorphism: `Spa(B, B⁺) → Spa(A, A⁺)` is open
(`TauCeti.Huber.Pair.Hom.isOpenMap_spaComap_of_isFiniteEtaleTorsor`). Every morphism of adic
spectra out of a Tate pair lifts generizations, so a surjective one is a quotient map
(`TauCeti.Huber.Pair.Hom.isQuotientMap_spaComap_of_isTateRing`). The saturation of an open subset
`U` of `Spa(B, B⁺)` is the union of its translates under `G`, and `G` acts by homeomorphisms, so
the image of `U` is open. `TauCeti.Huber.Pair.Hom.spaComap_orbits_of_isFiniteEtaleTorsor` collects
surjectivity, openness and the description of the fibres.

## References

* P. Scholze, *Étale cohomology of diamonds*, proof of Proposition 15.4.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, Remark 2.4.2, for the Huber pair of a finite étale algebra.
-/

public section

namespace TauCeti.Huber.Pair.Hom

open ValuationSpectrum

variable {G A B : Type*} [Group G] [Finite G] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsHuberRing B] [Algebra A B] [IsModuleTopology A B] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsFiniteEtaleTorsor G A B]
  {S : Pair A} {T : Pair B}

include G in
/-- **The adic spectrum of a finite étale torsor surjects onto the base.** If `B` is a finite étale
`G`-torsor over a Tate ring `A`, carries its natural topology and has plus ring the integral
closure of `A⁺`, then `Spa(B, B⁺) → Spa(A, A⁺)` is surjective, since `B` is faithfully flat. -/
theorem surjective_spaComap_of_isFiniteEtaleTorsor {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap A B)
    (hT : T.plus = (integralClosure (S.plus.map (algebraMap A B)) B).toSubring) :
    Function.Surjective φ.spaComap := by
  have := Algebra.IsFiniteEtaleTorsor.finite (G := G) (A := A) (B := B)
  have := Algebra.IsFiniteEtaleTorsor.etale (G := G) (A := A) (B := B)
  have := Algebra.IsFiniteEtaleTorsor.faithfullyFlat (G := G) (A := A) (B := B)
  refine IsFiniteEtale.surjective_spaComap ⟨?_, ?_, ?_, ?_⟩ ?_ <;> rw [hφ]
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact RingHom.etale_algebraMap.mpr inferInstance
  · rw [_root_.toAlgebra_algebraMap]
    infer_instance
  · exact hT
  · exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

include G in
/-- **The adic spectrum of a finite étale torsor maps openly onto the base.** If `B` is a finite
étale `G`-torsor over a Tate ring `A`, carries its natural topology and has plus ring the integral
closure of `A⁺`, then `Spa(B, B⁺) → Spa(A, A⁺)` is open. It is a quotient map
(`TauCeti.Huber.Pair.Hom.isQuotientMap_spaComap_of_isTateRing`), and the saturation of an open
set is the union of its translates under `G`, which act by homeomorphisms. -/
theorem isOpenMap_spaComap_of_isFiniteEtaleTorsor {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap A B)
    (hT : T.plus = (integralClosure (S.plus.map (algebraMap A B)) B).toSubring) :
    IsOpenMap φ.spaComap := by
  have := Algebra.IsFiniteEtaleTorsor.finite (G := G) (A := A) (B := B)
  have hquot := φ.isQuotientMap_spaComap_of_isTateRing
    (surjective_spaComap_of_isFiniteEtaleTorsor (G := G) hφ hT)
  -- `G` acts on `Spa(B, B⁺)` by `σ g : y ↦ comap g y`
  have hmem (g : G) {y : Spv B} (hy : y ∈ spa T.plus) :
      comap (MulSemiringAction.toRingHom G B g) y ∈ spa T.plus := by
    rw [hT] at hy ⊢
    exact (MulSemiringAction.toAlgHom A B g).comap_mem_spa_integralClosure hy
  let σ (g : G) : spa T.plus → spa T.plus := fun y ↦ ⟨_, hmem g y.property⟩
  have hσ (g : G) : Continuous (σ g) :=
    ((continuous_comap _).comp continuous_subtypeVal).subtype_mk _
  have hinv (g : G) (y : Spv B) :
      comap (MulSemiringAction.toRingHom G B g⁻¹) (comap (MulSemiringAction.toRingHom G B g) y) =
        y := by
    -- acting by `g⁻¹` and then by `g` is the identity of `B`
    have hcomp : (MulSemiringAction.toRingHom G B g).comp (MulSemiringAction.toRingHom G B g⁻¹) =
        RingHom.id B :=
      RingHom.ext fun b ↦ smul_inv_smul g b
    rw [comap_comap, hcomp, comap_id, _root_.id]
  intro U hU
  rw [← hquot.isOpen_preimage]
  -- the saturation of `U` is the union of its translates
  convert isOpen_iUnion fun g ↦ hU.preimage (hσ g) using 1
  ext y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨u, hu, huy⟩
    obtain ⟨g, hg⟩ := (spaComap_eq_spaComap_iff_of_isInvariant (G := G) hφ).mp huy
    refine ⟨g, ?_⟩
    convert hu using 1
    exact Subtype.ext <| by simpa [σ, hg, smul_def] using hinv g⁻¹ u.val
  · rintro ⟨g, hg⟩
    refine ⟨σ g y, hg, (spaComap_eq_spaComap_iff_of_isInvariant (G := G) hφ).mpr
      ⟨g, (hinv g y.val).symm⟩⟩

/-- **The base is the `G`-quotient of the adic spectrum of a finite étale torsor.** If `B` is a
finite étale `G`-torsor over a Tate ring `A`, carries its natural topology and has plus ring the
integral closure of `A⁺`, then `Spa(B, B⁺) → Spa(A, A⁺)` is surjective and open, and its fibres
are the `G`-orbits for `(g • y)(b) = y(g⁻¹ • b)`. Hence it identifies `Spa(A, A⁺)` with the
orbit space `Spa(B, B⁺) / G`. -/
theorem spaComap_orbits_of_isFiniteEtaleTorsor {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap A B)
    (hT : T.plus = (integralClosure (S.plus.map (algebraMap A B)) B).toSubring) :
    Function.Surjective φ.spaComap ∧ IsOpenMap φ.spaComap ∧
      ∀ x y : spa T.plus, φ.spaComap x = φ.spaComap y ↔
        ∃ g : G, (y : Spv B) = g • (x : Spv B) :=
  ⟨surjective_spaComap_of_isFiniteEtaleTorsor (G := G) hφ hT,
    isOpenMap_spaComap_of_isFiniteEtaleTorsor (G := G) hφ hT,
    fun _ _ ↦ spaComap_eq_spaComap_iff_of_isInvariant hφ⟩

end TauCeti.Huber.Pair.Hom
