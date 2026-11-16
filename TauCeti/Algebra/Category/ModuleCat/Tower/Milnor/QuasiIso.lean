/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality
import TauCeti.Algebra.Category.ModuleCat.Tower.Subsequence.LimOne
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Quasi-isomorphisms of towers of complexes

A morphism of towers of modules that is an isomorphism from some index on induces bijections on
both `lim` and `lim¹`: shifting along `n ↦ N + n` turns it into an isomorphism of towers, and
cofinal subsequences preserve `lim` (`TauCeti.ModuleTower.limSubsequenceEquiv`) and `lim¹`
(`TauCeti.ModuleTower.limOneSubsequenceEquiv`) naturally.

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

* `TauCeti.ModuleTower.bijective_limMap_of_isIso_of_le` and
  `TauCeti.ModuleTower.bijective_limOneMap_of_isIso_of_le`: an eventually levelwise isomorphism of
  module towers induces bijections on `lim` and `lim¹`.
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

namespace TauCeti.ModuleTower

variable {R : Type u} [Ring R] {F G : ModuleTower.{v} R}

/-- A morphism of module towers that is an isomorphism from some index on induces a bijection on
inverse limits. -/
theorem bijective_limMap_of_isIso_of_le (f : F ⟶ G) (N : ℕ)
    (hf : ∀ n, N ≤ n → IsIso (f.app (op n))) :
    Function.Bijective (limMap f) := by
  let φ : ℕ →o ℕ := ⟨(N + ·), fun _ _ h ↦ Nat.add_le_add_left h N⟩
  have hφ : ∀ n, ∃ m, n ≤ φ m := fun n ↦ ⟨n, Nat.le_add_left n N⟩
  let f' : F.subsequence φ ⟶ G.subsequence φ := Functor.whiskerLeft φ.monotone.functor.op f
  have : ∀ n, IsIso (f'.app n) := fun ⟨n⟩ ↦ hf (N + n) (Nat.le_add_right N n)
  have : IsIso f' := NatIso.isIso_of_isIso_app f'
  have hnat := limSubsequenceEquiv_naturality φ hφ f
  have hbij : Function.Bijective (limMap f' ∘ₗ (F.limSubsequenceEquiv φ hφ).toLinearMap) := by
    have h1 : ⇑(limEquivOfIso (asIso f')) = ⇑(limMap f') := funext (limEquivOfIso_apply _)
    rw [LinearMap.coe_comp, ← h1]
    exact (limEquivOfIso (asIso f')).bijective.comp (F.limSubsequenceEquiv φ hφ).bijective
  rw [← hnat] at hbij
  exact (Function.Bijective.of_comp_iff' (G.limSubsequenceEquiv φ hφ).bijective _).1 hbij

/-- A morphism of module towers that is an isomorphism from some index on induces a bijection on
`lim¹`. -/
theorem bijective_limOneMap_of_isIso_of_le (f : F ⟶ G) (N : ℕ)
    (hf : ∀ n, N ≤ n → IsIso (f.app (op n))) :
    Function.Bijective (limOneMap f) := by
  let φ : ℕ →o ℕ := ⟨(N + ·), fun _ _ h ↦ Nat.add_le_add_left h N⟩
  have hφ : ∀ n, ∃ m, n ≤ φ m := fun n ↦ ⟨n, Nat.le_add_left n N⟩
  let f' : F.subsequence φ ⟶ G.subsequence φ := Functor.whiskerLeft φ.monotone.functor.op f
  have : ∀ n, IsIso (f'.app n) := fun ⟨n⟩ ↦ hf (N + n) (Nat.le_add_right N n)
  have : IsIso f' := NatIso.isIso_of_isIso_app f'
  have hnat := limOneSubsequenceEquiv_naturality φ hφ f
  have hbij :
      Function.Bijective (limOneMap f' ∘ₗ (F.limOneSubsequenceEquiv φ hφ).toLinearMap) := by
    have h1 : ⇑(limOneEquivOfIso (asIso f')) = ⇑(limOneMap f') :=
      funext (limOneEquivOfIso_apply _)
    rw [LinearMap.coe_comp, ← h1]
    exact (limOneEquivOfIso (asIso f')).bijective.comp (F.limOneSubsequenceEquiv φ hφ).bijective
  rw [← hnat] at hbij
  exact (Function.Bijective.of_comp_iff' (G.limOneSubsequenceEquiv φ hφ).bijective _).1 hbij

end TauCeti.ModuleTower

namespace TauCeti.ComplexTower

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {C D : ComplexTower.{v} R c}

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
    ModuleTower.bijective_limMap_of_isIso_of_le _ Nj fun n hn ↦
      (quasiIsoAt_iff_isIso_homologyMap (f.app (op n)) j).1 (hNj n hn)
  by_cases hrel : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hrel
    obtain ⟨Ni, hNi⟩ := hi i hij
    have hlim1i : Function.Bijective (ModuleTower.limOneMap (Functor.whiskerRight f
        (HomologicalComplex.homologyFunctor _ c i))) :=
      ModuleTower.bijective_limOneMap_of_isIso_of_le _ Ni fun n hn ↦
        (quasiIsoAt_iff_isIso_homologyMap (f.app (op n)) i).1 (hNi n hn)
    let SC : ShortComplex (ModuleCat.{v} R) := ShortComplex.mk
      (ModuleCat.ofHom (C.limOneToHomology hC hij))
      (ModuleCat.ofHom (C.homologyToLim j))
      (ModuleCat.hom_ext <| LinearMap.ext fun x ↦
        (exact_limOneToHomology_homologyToLim hC hij _).2 ⟨x, rfl⟩)
    let SD : ShortComplex (ModuleCat.{v} R) := ShortComplex.mk
      (ModuleCat.ofHom (D.limOneToHomology hD hij))
      (ModuleCat.ofHom (D.homologyToLim j))
      (ModuleCat.hom_ext <| LinearMap.ext fun x ↦
        (exact_limOneToHomology_homologyToLim hD hij _).2 ⟨x, rfl⟩)
    have hSC : SC.ShortExact := ModuleCat.shortComplex_shortExact SC
      (exact_limOneToHomology_homologyToLim hC hij)
      (limOneToHomology_injective hC hij)
      (homologyToLim_surjective hC j)
    have hSD : SD.ShortExact := ModuleCat.shortComplex_shortExact SD
      (exact_limOneToHomology_homologyToLim hD hij)
      (limOneToHomology_injective hD hij)
      (homologyToLim_surjective hD j)
    let φ : SC ⟶ SD := ShortComplex.homMk
      (ModuleCat.ofHom (ModuleTower.limOneMap
        (Functor.whiskerRight f (HomologicalComplex.homologyFunctor _ c i))))
      (HomologicalComplex.homologyMap (limComplexMap f) j)
      (ModuleCat.ofHom (ModuleTower.limMap
        (Functor.whiskerRight f (HomologicalComplex.homologyFunctor _ c j))))
      (ModuleCat.hom_ext (limOneToHomology_naturality f hC hD hij).symm)
      (ModuleCat.hom_ext (homologyToLim_naturality f j))
    have : IsIso φ.τ₁ := (ConcreteCategory.isIso_iff_bijective _).2 hlim1i
    have : IsIso φ.τ₃ := (ConcreteCategory.isIso_iff_bijective _).2 hlimj
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hSC hSD
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
