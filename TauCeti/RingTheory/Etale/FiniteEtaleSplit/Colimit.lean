/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.Algebra.Colimit.FinitePresentation
public import TauCeti.RingTheory.Etale.DirectLimit
public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic

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

The stages of a colimit need not be split themselves. If `B i` is a directed system of finite étale
`A`-algebras and every finite étale `A`-algebra becomes totally split over some `B i`, the colimit
is split. A finite étale algebra `C` over the colimit comes from a finite étale algebra `Cᵢ` over
some `B i`, which is finite étale over `A`; once `B k ⊗[A] Cᵢ` is totally split over `B k`, so is
its étale quotient `B k ⊗[B i] Cᵢ` (`TauCeti.Algebra.IsTotallySplit.of_surjective`), and hence
the base change of the latter, which is `C`. This is the splitting property of the colimit of a
tower of finite étale torsors in which every finite étale `A`-algebra is split at some level.

## Main results

* `TauCeti.IsFiniteEtaleSplit.of_forall_finitePresentation`: if every ring map from a finitely
  presented ring into `R` factors through a ring without nonsplit finite étale covers, then `R`
  has none.
* `Ring.DirectLimit.isFiniteEtaleSplit`: a directed colimit, over a nonempty index set, of rings
  without nonsplit finite étale covers has none.
* `LocallyConstant.isFiniteEtaleSplit`: if `A` has no nonsplit finite étale covers, then neither
  has `LocallyConstant X A`, for any topological space `X`.
* `Ring.DirectLimit.isFiniteEtaleSplit_of_forall_exists_isTotallySplit`: a directed colimit of
  finite étale `A`-algebras over which every finite étale `A`-algebra eventually becomes totally
  split has no nonsplit finite étale covers.

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
    -- Index the possible factorizations by split rings and their maps to `R`.
    let I := Σ (A : Type w) (_ : CommRing A), {_ψ : A →+* R // IsFiniteEtaleSplit A}
    let A (i : I) := i.1
    let (i : I) : CommRing (A i) := i.2.1
    let ψ (i : I) : A i →+* R := i.2.2.val
    have hfactor (P : Type u) [CommRing P] [Algebra.FinitePresentation ℤ P] (g : P →+* R) :
        ∃ i, ∃ φ : P →+* A i, (ψ i).comp φ = g := by
      obtain ⟨A, _, hA, φ, ψ, hφψ⟩ := h P g
      exact ⟨⟨A, inferInstance, ψ, hA⟩, φ, hφψ⟩
    obtain ⟨i, Tᵢ, _, _, _, _, ⟨e⟩⟩ :=
      Algebra.exists_etale_finite_algEquiv_tensorProduct_of_factorization A ψ hfactor T
    let : IsFiniteEtaleSplit (A i) := i.2.2.property
    let := (ψ i).toAlgebra
    exact ((Algebra.IsTotallySplit.of_isFiniteEtaleSplit Tᵢ).baseChange R).of_algEquiv e.symm

end TauCeti

namespace Ring.DirectLimit

section

variable {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] {G : ι → Type u}
  [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G (f · · ·)]

/-- A directed colimit, over a nonempty index set, of rings without nonsplit finite étale covers
has none. Nonemptiness is what lets maps from finitely presented rings factor through a stage; the
colimit of the empty system is `ℤ`, for which the statement would be Minkowski's theorem. -/
instance isFiniteEtaleSplit [∀ i, TauCeti.IsFiniteEtaleSplit (G i)] :
    TauCeti.IsFiniteEtaleSplit (DirectLimit G (f · · ·)) :=
  .of_forall_finitePresentation fun _ _ _ g ↦
    have ⟨i, g', hg'⟩ := g.exists_of_comp_eq_of_finitePresentation
    ⟨G i, _, inferInstance, g', of G (f · · ·) i, hg'⟩

end

section Levelwise

variable {A : Type*} [CommRing A] {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]

/-- **A colimit of finite étale algebras splitting every finite étale algebra is split.** Let
`B i` be a directed system of finite étale `A`-algebras, indexed by a directed preorder. If
every finite étale `A`-algebra `S` becomes totally split over some `B i`, then the colimit has no
nonsplit finite étale covers.

This is how a tower of finite étale torsors over `A`, chosen so that each finite étale
`A`-algebra is split at some level, acquires a colimit without nonsplit finite étale covers. -/
theorem isFiniteEtaleSplit_of_forall_exists_isTotallySplit [∀ i, Algebra.Etale A (B i)]
    [∀ i, Module.Finite A (B i)]
    (h : ∀ (S : Type u) [CommRing S] [Algebra A S] [Algebra.Etale A S] [Module.Finite A S],
      ∃ i, TauCeti.Algebra.IsTotallySplit (B i) (B i ⊗[A] S)) :
    TauCeti.IsFiniteEtaleSplit (DirectLimit B (f · · ·)) where
  isTotallySplit C _ _ _ _ := by
    -- The zero algebra splits at some stage, so the index set is nonempty.
    have : Nonempty ι := have ⟨i, _⟩ := h PUnit; ⟨i⟩
    -- The descent lemma below takes ring homomorphisms as transition maps. Forgetting `f` to
    -- ring homomorphisms does not change the underlying functions, so the directed system and
    -- its colimit are literally the same.
    have : DirectedSystem B fun i j h ↦ (f i j h).toRingHom := ‹DirectedSystem B (f · · ·)›
    let R := DirectLimit B (f · · ·)
    -- `C` is the base change of a finite étale algebra `Cᵢ` over some `B i`.
    obtain ⟨i, Cᵢ, _, _, _, _, ⟨e⟩⟩ :=
      exists_etale_finite_algEquiv_tensorProduct (f := fun i j h ↦ (f i j h).toRingHom) C
    let : Algebra A Cᵢ := ((algebraMap (B i) Cᵢ).comp (algebraMap A (B i))).toAlgebra
    have : IsScalarTower A (B i) Cᵢ := .of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.Etale A Cᵢ := .comp A (B i) Cᵢ
    have : Module.Finite A Cᵢ := .trans (B i) Cᵢ
    -- As a finite étale `A`-algebra, `Cᵢ` splits over some `B j`, hence over a common upper
    -- bound `B k` of `B i` and `B j`.
    obtain ⟨j, hj⟩ := h Cᵢ
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let := (f j k hjk).toAlgebra
    have hk : TauCeti.Algebra.IsTotallySplit (B k) (B k ⊗[A] Cᵢ) :=
      (hj.baseChange (B k)).of_algEquiv
        (Algebra.TensorProduct.cancelBaseChange A (B j) (B k) (B k) Cᵢ)
    -- Its étale quotient `B k ⊗[B i] Cᵢ` is then split over `B k`, and so is the base change
    -- `R ⊗[B i] Cᵢ ≃ C` of the latter to the colimit.
    let := (f i k hik).toAlgebra
    have hk' : TauCeti.Algebra.IsTotallySplit (B k) (B k ⊗[B i] Cᵢ) :=
      hk.of_surjective (Algebra.TensorProduct.mapOfCompatibleSMul (B i) A (B k) (B k) Cᵢ)
        (Algebra.TensorProduct.mapOfCompatibleSMul_surjective _ _ _ _ _)
    let := (of B (f · · ·) i).toAlgebra
    let := (of B (f · · ·) k).toAlgebra
    have : IsScalarTower (B i) (B k) R := .of_algebraMap_eq fun x ↦ (of_f hik x).symm
    exact (hk'.baseChange R).of_algEquiv
      ((Algebra.TensorProduct.cancelBaseChange (B i) (B k) R R Cᵢ).trans e.symm)

end Levelwise

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
  let φ : P →+* (Set.range F → A) := RingHom.pi fun q ↦ (evalRingHom q.property.choose).comp g
  refine ⟨Set.range F → A, _, inferInstance, φ, ψ, RingHom.toIntAlgHom_injective ?_⟩
  -- Both maps are determined by the generators, on which `g p` is constant on the fibres of `F`.
  refine AlgHom.ext_of_adjoin_eq_top ht fun p hp ↦ ext fun x ↦ ?_
  exact congrFun (Set.rangeFactorization F x).property.choose_spec ⟨p, hp⟩

end LocallyConstant
