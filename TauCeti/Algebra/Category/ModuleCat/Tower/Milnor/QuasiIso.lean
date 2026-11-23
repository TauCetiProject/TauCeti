/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality

/-!
# Quasi-isomorphisms of towers of complexes

A morphism of towers of modules that is an isomorphism from some index on induces bijections on
both `lim` (`TauCeti.ModuleTower.limMap_bijective_of_isIso_of_le`) and `lim¹`
(`TauCeti.ModuleTower.limOneMap_bijective_of_isIso_of_le`).

For two towers of complexes of arbitrary shape whose termwise shifts are surjective (for example,
towers with degreewise surjective transitions or Mittag-Leffler terms), a morphism of towers `f`
that is eventually a quasi-isomorphism in degree `j` and in every degree `i` with `c.Rel i j`
therefore induces isomorphisms on `lim Hⱼ` and `lim¹ Hᵢ`. By naturality of the Milnor sequence
(`TauCeti.ComplexTower.homologyToLim_naturality`,
`TauCeti.ComplexTower.limOneToHomology_naturality`) and the short five lemma
(`CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃`), `limComplexMap f` is a
quasi-isomorphism at degree `j` (`TauCeti.ComplexTower.quasiIsoAt_limComplexMap`). In particular,
a levelwise quasi-isomorphism between such towers induces a quasi-isomorphism of limit complexes
(`TauCeti.ComplexTower.quasiIso_limComplexMap_of_forall_quasiIso`).

## Main results

* `TauCeti.ComplexTower.quasiIsoAt_limComplexMap`: an eventually levelwise quasi-isomorphism in
  degree `j` and in every predecessor degree induces a quasi-isomorphism on limit complexes at `j`.
* `TauCeti.ComplexTower.quasiIso_limComplexMap` and
  `TauCeti.ComplexTower.quasiIso_limComplexMap_of_forall_quasiIso`: an eventually (or everywhere)
  levelwise quasi-isomorphism of shift-surjective complex towers induces a quasi-isomorphism of
  limit complexes.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* C. A. Weibel, *An introduction to homological algebra*, Theorem 3.5.8.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u w

namespace TauCeti.ComplexTower

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {C D : ComplexTower.{v} R c}

private def milnorShortComplex (E : ComplexTower.{v} R c)
    (hE : ∀ i, Function.Surjective (E.term i).shift) {i j : ι} (hij : c.Rel i j) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom (E.limOneToHomology hE hij))
    (ModuleCat.ofHom (E.homologyToLim j))
    (ModuleCat.hom_ext <| LinearMap.ext fun x ↦
      (exact_limOneToHomology_homologyToLim hE hij _).2 ⟨x, rfl⟩)

private lemma milnorShortComplex_shortExact (E : ComplexTower.{v} R c)
    (hE : ∀ i, Function.Surjective (E.term i).shift) {i j : ι} (hij : c.Rel i j) :
    (milnorShortComplex E hE hij).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (exact_limOneToHomology_homologyToLim hE hij)
    (limOneToHomology_injective hE hij)
    (homologyToLim_surjective hE j)

/-- **Degreewise limit-homology comparison for towers of complexes.** Let `f : C ⟶ D` be a
morphism between towers of complexes whose termwise shifts are surjective. If `f` is eventually a
quasi-isomorphism in degree `j` and in every degree `i` with `c.Rel i j`, then `limComplexMap f`
is a quasi-isomorphism at `j`. -/
theorem quasiIsoAt_limComplexMap (f : C ⟶ D)
    (hC : ∀ i, Function.Surjective (C.term i).shift)
    (hD : ∀ i, Function.Surjective (D.term i).shift) (j : ι)
    (hj : ∃ N, ∀ n, N ≤ n → QuasiIsoAt (f.app (op n)) j)
    (hi : ∀ i, c.Rel i j → ∃ N, ∀ n, N ≤ n → QuasiIsoAt (f.app (op n)) i) :
    QuasiIsoAt (limComplexMap f) j := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨Nj, hNj⟩ := hj
  have hlimj : Function.Bijective (ModuleTower.limMap (Functor.whiskerRight f
      (HomologicalComplex.homologyFunctor _ c j))) :=
    ModuleTower.limMap_bijective_of_isIso_of_le _ Nj fun n hn ↦
      (quasiIsoAt_iff_isIso_homologyMap (f.app (op n)) j).1 (hNj n hn)
  by_cases hrel : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hrel
    obtain ⟨Ni, hNi⟩ := hi i hij
    have hlim1i : Function.Bijective (ModuleTower.limOneMap (Functor.whiskerRight f
        (HomologicalComplex.homologyFunctor _ c i))) :=
      ModuleTower.limOneMap_bijective_of_isIso_of_le _ Ni fun n hn ↦
        (quasiIsoAt_iff_isIso_homologyMap (f.app (op n)) i).1 (hNi n hn)
    let φ : milnorShortComplex C hC hij ⟶ milnorShortComplex D hD hij := ShortComplex.homMk
      (ModuleCat.ofHom (ModuleTower.limOneMap
        (Functor.whiskerRight f (HomologicalComplex.homologyFunctor _ c i))))
      (HomologicalComplex.homologyMap (limComplexMap f) j)
      (ModuleCat.ofHom (ModuleTower.limMap
        (Functor.whiskerRight f (HomologicalComplex.homologyFunctor _ c j))))
      (ModuleCat.hom_ext (limOneToHomology_naturality f hC hD hij).symm)
      (ModuleCat.hom_ext (homologyToLim_naturality f j))
    have : IsIso φ.τ₁ := (ConcreteCategory.isIso_iff_bijective _).2 hlim1i
    have : IsIso φ.τ₃ := (ConcreteCategory.isIso_iff_bijective _).2 hlimj
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
      (milnorShortComplex_shortExact C hC hij) (milnorShortComplex_shortExact D hD hij)
  · rw [ConcreteCategory.isIso_iff_bijective]
    have hCbij : Function.Bijective (C.homologyToLim j) :=
      ⟨C.homologyToLim_injective_of_forall_not_rel fun i hij ↦ hrel ⟨i, hij⟩,
        homologyToLim_surjective hC j⟩
    have hDbij : Function.Bijective (D.homologyToLim j) :=
      ⟨D.homologyToLim_injective_of_forall_not_rel fun i hij ↦ hrel ⟨i, hij⟩,
        homologyToLim_surjective hD j⟩
    have hcomp : Function.Bijective
        (D.homologyToLim j ∘ₗ (HomologicalComplex.homologyMap (limComplexMap f) j).hom) := by
      rw [homologyToLim_naturality f j]
      exact hlimj.comp hCbij
    exact (Function.Bijective.of_comp_iff' hDbij _).1 hcomp

/-- **Limit-homology comparison for eventually quasi-isomorphic towers of complexes.** Let
`f : C ⟶ D` be a morphism between towers of complexes whose termwise shifts are surjective. If in
each degree `j`, `f` is eventually a quasi-isomorphism at `j`, then `limComplexMap f` is a
quasi-isomorphism. -/
theorem quasiIso_limComplexMap (f : C ⟶ D)
    (hC : ∀ i, Function.Surjective (C.term i).shift)
    (hD : ∀ i, Function.Surjective (D.term i).shift)
    (hf : ∀ j, ∃ N, ∀ n, N ≤ n → QuasiIsoAt (f.app (op n)) j) :
    QuasiIso (limComplexMap f) := by
  rw [quasiIso_iff]
  exact fun j ↦ quasiIsoAt_limComplexMap f hC hD j (hf j) fun i _ ↦ hf i

/-- **Levelwise quasi-isomorphisms of shift-surjective towers induce quasi-isomorphisms of limit
complexes.** -/
theorem quasiIso_limComplexMap_of_forall_quasiIso (f : C ⟶ D)
    (hC : ∀ i, Function.Surjective (C.term i).shift)
    (hD : ∀ i, Function.Surjective (D.term i).shift)
    (hf : ∀ n, QuasiIso (f.app (op n))) :
    QuasiIso (limComplexMap f) :=
  quasiIso_limComplexMap f hC hD fun j ↦ ⟨0, fun n _ ↦ by
    have := hf n
    infer_instance⟩

end TauCeti.ComplexTower
