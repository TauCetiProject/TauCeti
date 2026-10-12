/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.TrivialityCriterion

/-!
# Tate's isomorphism criterion for a morphism of representations

Let `G` be a finite group and `f : A ⟶ B` a morphism of representations of `G`. Suppose that for
every subgroup `S` of `G` of prime-power order the map induced by `f` on the Tate cohomology of
`S` is surjective in degree `q - 1`, bijective in degree `q` and injective in degree `q + 1`.
Then `f` induces isomorphisms `Ĥⁿ(S, A) ≃ Ĥⁿ(S, B)` in every integer degree `n`, for every
subgroup `S` of `G` (`TauCeti.TateCohomology.map_res_bijective_of_forall_isPGroup`), and in
particular for `G` itself (`TauCeti.TateCohomology.map_bijective_of_forall_isPGroup`).

This is the heart of Tate's theorem in the form given by Artin and Tate (*Class Field Theory*,
Preliminaries, §2, Theorem A): once the cohomology class is moved to degree zero by dimension
shifting, their cup-product criterion is the case of this statement in which `f` is the morphism
`ℤ ⟶ A`, `1 ↦ a`, attached to an invariant `a`. The proof is the standard one. Replace `f` by the
monomorphism `A ⟶ B ⊞ Coind_⊥^G A` with components `f` and the coinduction unit; the second
summand has no Tate cohomology on any subgroup, so this changes nothing on cohomology. The long
exact sequence of the cokernel `C` then shows that the Tate cohomology of `C` vanishes in the
two consecutive degrees `q - 1` and `q` on every subgroup of prime-power order, so `C` is
cohomologically trivial by Tate's triviality criterion
(`TauCeti.TateCohomology.isZero_of_forall_isPGroup`), and the long exact sequence gives the
conclusion in every degree.

The other classical route to Tate's theorem, through the splitting module of a degree-two class
(Serre, *Local Fields*, Chapter IX, §8; `ClassFieldTheory/Cohomology/SplittingModule.lean` in
`kbuzzard/ClassFieldTheory`), is not taken here: the criterion below applies to any morphism and
any triple of consecutive degrees, which is what the cup-product formulation of Tate's theorem
consumes.

## Main statements

* `TauCeti.TateCohomology.map_res_bijective_of_forall_isPGroup`: the criterion, with the
  conclusion on every subgroup of `G`.
* `TauCeti.TateCohomology.map_bijective_of_forall_isPGroup`: the criterion, with the conclusion
  on `G` itself.

## References

* E. Artin and J. Tate, *Class Field Theory*, Preliminaries, §2, Theorem A.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §10.
* J.-P. Serre, *Local Fields*, Chapter IX, §8.
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} (f : A ⟶ B)

/-- The morphism `A ⟶ B ⊞ Coind_⊥^G A` with components `f` and the coinduction unit is a
monomorphism, because its second component `coindBotUnit A` is a monomorphism
(`coindBotUnit_mono`). -/
private theorem mono_lift_coindBotUnit : Mono (biprod.lift f (coindBotUnit A)) :=
  mono_of_mono_fac (biprod.lift_snd f (coindBotUnit A))

variable (A B) in
/-- On the Tate cohomology of a finite subgroup, the projection `B ⊞ Coind_⊥^G A ⟶ B` is a
bijection, because the second summand has no Tate cohomology there. -/
private theorem map_res_biprod_fst_bijective (S : Subgroup G) [Fintype S] (n : ℤ) :
    Function.Bijective ((tateCohomologyFunctor n).map
      ((resFunctor S.subtype).map (biprod.fst : B ⊞ coindBot k G A.V ⟶ B))) :=
  haveI := (resFunctor S.subtype ⋙ tateCohomologyFunctor n).isIso_map_biprod_fst_of_isZero
    B (coindBot k G A.V) (isZero_res_coindBot S A.V n)
  ConcreteCategory.bijective_of_isIso
    ((resFunctor S.subtype ⋙ tateCohomologyFunctor n).map (biprod.fst : B ⊞ coindBot k G A.V ⟶ B))

/-- On the Tate cohomology of a finite subgroup, `f` is the morphism `A ⟶ B ⊞ Coind_⊥^G A`
followed by the projection onto `B`. -/
private theorem coe_map_res_eq (S : Subgroup G) [Fintype S] (n : ℤ) :
    ⇑((tateCohomologyFunctor n).map ((resFunctor S.subtype).map f)) =
      ⇑((tateCohomologyFunctor n).map ((resFunctor S.subtype).map
        (biprod.fst : B ⊞ coindBot k G A.V ⟶ B))) ∘
      ⇑((tateCohomologyFunctor n).map ((resFunctor S.subtype).map
        (biprod.lift f (coindBotUnit A)))) := by
  rw [← ConcreteCategory.coe_comp, ← Functor.map_comp, ← Functor.map_comp, biprod.lift_fst]

/-- `f` and the monomorphism `A ⟶ B ⊞ Coind_⊥^G A` are surjective in the same degrees on the Tate
cohomology of a finite subgroup. -/
private theorem map_res_lift_surjective_iff (S : Subgroup G) [Fintype S] (n : ℤ) :
    Function.Surjective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map
        (biprod.lift f (coindBotUnit A)))) ↔
      Function.Surjective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map f)) := by
  rw [coe_map_res_eq f S n, Function.Surjective.of_comp_iff' (map_res_biprod_fst_bijective A B S n)]

/-- `f` and the monomorphism `A ⟶ B ⊞ Coind_⊥^G A` are injective in the same degrees on the Tate
cohomology of a finite subgroup. -/
private theorem map_res_lift_injective_iff (S : Subgroup G) [Fintype S] (n : ℤ) :
    Function.Injective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map
        (biprod.lift f (coindBotUnit A)))) ↔
      Function.Injective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map f)) := by
  rw [coe_map_res_eq f S n,
    Function.Injective.of_comp_iff (map_res_biprod_fst_bijective A B S n).1]

/-- **Tate's isomorphism criterion**, on every subgroup. Let `G` be a finite group and `f : A ⟶ B`
a morphism of representations of `G`. If, for every subgroup `S` of `G` of prime-power order, the
map induced by `f` on the Tate cohomology of `S` is surjective in degree `q - 1`, bijective in
degree `q` and injective in degree `q + 1`, then it is bijective in every degree `n` for every
subgroup `S` of `G`. -/
theorem map_res_bijective_of_forall_isPGroup [Finite G] {q : ℤ}
    (hsurj : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Surjective ((tateCohomologyFunctor (q - 1)).map ((resFunctor S.subtype).map f)))
    (hbij : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Bijective ((tateCohomologyFunctor q).map ((resFunctor S.subtype).map f)))
    (hinj : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Injective ((tateCohomologyFunctor (q + 1)).map ((resFunctor S.subtype).map f)))
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    Function.Bijective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map f)) := by
  -- The short exact sequence `A ⟶ B ⊞ Coind_⊥^G A ⟶ C` and its restrictions to subgroups; the
  -- `Mono` instance makes the cokernel sequence short exact.
  have := mono_lift_coindBotUnit f
  set T := ShortComplex.cokernelSequence (biprod.lift f (coindBotUnit A))
  have hT : ∀ (S : Subgroup G) [Fintype S], (T.map (resFunctor S.subtype)).ShortExact :=
    fun S _ ↦ (shortExact_res S.subtype).2 (TauCeti.cokernelSequence_shortExact _)
  -- The cokernel `C` has no Tate cohomology on any subgroup, by the triviality criterion.
  have hC : ∀ (S : Subgroup G) [Fintype S] (m : ℤ),
      IsZero (tateCohomology (res S.subtype T.X₃) m) := by
    intro S _ m
    refine isZero_of_forall_isPGroup T.X₃ (q := q - 1) (fun p _ P _ hP ↦ ?_)
      (fun p _ P _ hP ↦ ?_) S m
    · exact isZero_X₃_of_surjective_of_injective (hT P) (q - 1) q (sub_add_cancel q 1)
        ((map_res_lift_surjective_iff f P (q - 1)).2 (hsurj p P hP))
        ((map_res_lift_injective_iff f P q).2 (hbij p P hP).1)
    · rw [sub_add_cancel]
      exact isZero_X₃_of_surjective_of_injective (hT P) q (q + 1) rfl
        ((map_res_lift_surjective_iff f P q).2 (hbij p P hP).2)
        ((map_res_lift_injective_iff f P (q + 1)).2 (hinj p P hP))
  rw [coe_map_res_eq f S n]
  exact (map_res_biprod_fst_bijective A B S n).comp
    ⟨map_f_injective_of_isZero_X₃ (hT S) (n - 1) n (sub_add_cancel n 1) (hC S (n - 1)),
      map_f_surjective_of_isZero_X₃ (hT S) n (hC S n)⟩

/-- **Tate's isomorphism criterion.** Let `G` be a finite group and `f : A ⟶ B` a morphism of
representations of `G`. If, for every subgroup `S` of `G` of prime-power order, the map induced by
`f` on the Tate cohomology of `S` is surjective in degree `q - 1`, bijective in degree `q` and
injective in degree `q + 1`, then `f` induces a bijection `Ĥⁿ(G, A) → Ĥⁿ(G, B)` in every
degree `n`. -/
theorem map_bijective_of_forall_isPGroup [Fintype G] {q : ℤ}
    (hsurj : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Surjective ((tateCohomologyFunctor (q - 1)).map ((resFunctor S.subtype).map f)))
    (hbij : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Bijective ((tateCohomologyFunctor q).map ((resFunctor S.subtype).map f)))
    (hinj : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Function.Injective ((tateCohomologyFunctor (q + 1)).map ((resFunctor S.subtype).map f)))
    (n : ℤ) : Function.Bijective ((tateCohomologyFunctor n).map f) := by
  let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  -- Restriction along `⊤ ≃* G` does not change Tate cohomology, naturally in the coefficients, so
  -- the statement on `G` is the statement on the subgroup `⊤`. The monoid homomorphism underlying
  -- `Subgroup.topEquiv` is `(⊤ : Subgroup G).subtype` by definition, which is how the conclusion
  -- of `map_res_bijective_of_forall_isPGroup` at `⊤` matches the restriction in `resIso`.
  have hnat := (resIso (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G) n).hom.naturality f
  have : IsIso ((resFunctor ((Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G) : (⊤ : Subgroup G) →* G) ⋙
      tateCohomologyFunctor n).map f) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (map_res_bijective_of_forall_isPGroup f hsurj hbij hinj ⊤ n)
  rw [(IsIso.eq_inv_comp _).2 hnat.symm]
  exact ConcreteCategory.bijective_of_isIso _

end TauCeti.TateCohomology
