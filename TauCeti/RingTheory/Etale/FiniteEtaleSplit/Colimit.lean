/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.Algebra.Colimit.Ring
public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic
public import TauCeti.RingTheory.Etale.NoetherianDescent

/-!
# Filtered colimits of rings without nonsplit finite étale covers

A ring `R` has no nonsplit finite étale covers (`TauCeti.IsFiniteEtaleSplit`) as soon as every
ring map from a finitely presented ring into `R` factors through some ring without nonsplit
finite étale covers. Indeed, a finite étale `R`-algebra `T` is the base change of a finite étale
algebra `T₀` over a finitely generated subring `R₀ ⊆ R`
(`Algebra.Etale.exists_subalgebra_fg_of_finite`). If `R₀ → R` factors as `R₀ → A → R` with `A`
split, then `A ⊗[R₀] T₀` is totally split over `A`, and so is its base change
`R ⊗[A] (A ⊗[R₀] T₀) ≃ R ⊗[R₀] T₀ ≃ T` over `R`.

The hypothesis says that `R` is a filtered colimit of rings without nonsplit finite étale covers,
and the criterion applies to the two colimits that occur in practice: directed colimits of rings
(`Ring.DirectLimit`) and rings of locally constant functions. The ring `LocallyConstant X A` of
locally constant functions on a topological space `X` with values in a ring `A` is the union of
the subrings of functions factoring through the joint values of a finite family of locally
constant functions, and each of these is a product of copies of `A`. For `X` profinite
and `A` a separably closed field, this is the locally constant case of Scholze's Lemma 15.3.

## Main results

* `TauCeti.IsFiniteEtaleSplit.of_forall_finitePresentation`: if every ring map from a finitely
  presented ring into `R` factors through a ring without nonsplit finite étale covers, then `R`
  has none.
* `Ring.DirectLimit.isFiniteEtaleSplit`: a directed colimit, over a nonempty index set, of rings
  without nonsplit finite étale covers has none.
* `LocallyConstant.isFiniteEtaleSplit`: if `A` has no nonsplit finite étale covers, then neither
  has `LocallyConstant X A`, for any topological space `X`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3.
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Lemma 10.1.6.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Remark 1.2.9.
-/

public section

universe w v u

open TensorProduct

namespace TauCeti

/-- If every ring map from a finitely presented ring into `R` factors through a ring without
nonsplit finite étale covers, then `R` has no nonsplit finite étale covers. The hypothesis holds
when `R` is a filtered colimit of rings without nonsplit finite étale covers. -/
theorem IsFiniteEtaleSplit.of_forall_finitePresentation {R : Type u} [CommRing R]
    (h : ∀ (P : Type u) [CommRing P] [Algebra.FinitePresentation ℤ P] (g : P →+* R),
      ∃ (A : Type w) (_ : CommRing A) (_ : IsFiniteEtaleSplit A) (φ : P →+* A) (ψ : A →+* R),
        ψ.comp φ = g) :
    IsFiniteEtaleSplit R where
  isTotallySplit T _ _ _ _ := by
    -- `T` is the base change of a finite étale algebra `T₀` over a subring `R₀` of finite type.
    obtain ⟨R₀, T₀, _, _, hR₀, _, _, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg_of_finite ℤ R T
    have : Algebra.FinitePresentation ℤ R₀ :=
      Algebra.FinitePresentation.of_finiteType.1 (Subalgebra.fg_iff_finiteType R₀ |>.1 hR₀)
    obtain ⟨A, _, _, φ, ψ, hφψ⟩ := h R₀ (algebraMap R₀ R)
    let : Algebra R₀ A := φ.toAlgebra
    let : Algebra A R := ψ.toAlgebra
    have : IsScalarTower R₀ A R := .of_algebraMap_eq fun x ↦ congr($hφψ x).symm
    -- `A ⊗[R₀] T₀` is totally split over `A`, hence so is its base change to `R`.
    exact ((Algebra.IsTotallySplit.of_isFiniteEtaleSplit (A ⊗[R₀] T₀)).baseChange R).of_algEquiv
      ((Algebra.TensorProduct.cancelBaseChange R₀ A R R T₀).trans e.symm)

end TauCeti

namespace Ring.DirectLimit

variable {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] {G : ι → Type u}
  [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G (f · · ·)]

/-- A directed colimit, over a nonempty index set, of rings without nonsplit finite étale covers
has none. Nonemptiness is what lets maps from finitely presented rings factor through a stage; the
colimit of the empty system is `ℤ`, for which the statement would be Minkowski's theorem. -/
instance isFiniteEtaleSplit [∀ i, TauCeti.IsFiniteEtaleSplit (G i)] :
    TauCeti.IsFiniteEtaleSplit (DirectLimit G (f · · ·)) :=
  .of_forall_finitePresentation fun _ _ _ g ↦
    have ⟨i, g', hg'⟩ := exists_of_comp_eq_of_finitePresentation g
    ⟨G i, _, inferInstance, g', of G (f · · ·) i, hg'⟩

end Ring.DirectLimit

namespace LocallyConstant

/-- If `A` has no nonsplit finite étale covers, then neither has the ring of locally constant
functions on any topological space with values in `A`. For a profinite space and a separably
closed field `A`, this is the locally constant case of Scholze's Lemma 15.3. -/
instance isFiniteEtaleSplit (X : Type*) [TopologicalSpace X] (A : Type*) [CommRing A]
    [TauCeti.IsFiniteEtaleSplit A] : TauCeti.IsFiniteEtaleSplit (LocallyConstant X A) := by
  refine .of_forall_finitePresentation fun P _ _ g ↦ ?_
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := ℤ) (A := P)
  -- The images of the generators assemble to a locally constant map `F` with values in
  -- `t → A`, and each of them factors through the range of `F`.
  let F : LocallyConstant X (t → A) := unflip fun p ↦ g p
  have hF : IsLocallyConstant (Set.rangeFactorization F) :=
    .desc _ Subtype.val F.isLocallyConstant Subtype.val_injective
  let ψ : (Set.range F → A) →+* LocallyConstant X A :=
    { toFun a := ⟨a ∘ Set.rangeFactorization F, hF.comp a⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  -- Evaluate at a chosen point of each fibre of `F`.
  let φ : P →+* (Set.range F → A) := RingHom.pi fun q ↦ (evalRingHom q.2.choose).comp g
  refine ⟨Set.range F → A, _, inferInstance, φ, ψ, RingHom.toIntAlgHom_injective ?_⟩
  -- Both maps are determined by the generators, on which `g p` is constant on the fibres of `F`.
  refine AlgHom.ext_of_adjoin_eq_top ht fun p hp ↦ ext fun x ↦ ?_
  exact congrFun (Set.rangeFactorization F x).2.choose_spec ⟨p, hp⟩

end LocallyConstant
