/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Colimit
public import TauCeti.RingTheory.Etale.Torsor.PiTensorProduct
public import TauCeti.RingTheory.Etale.Torsor.Splitting

import TauCeti.Algebra.Group.Pi.Finset
import TauCeti.Algebra.Group.Pi.Lemmas
import TauCeti.RingTheory.Etale.Small

/-!
# Towers of finite étale torsors

A *finite étale torsor tower* over a commutative ring `A` (`TauCeti.FiniteEtaleTorsorTower A`) is
a directed system, over a nonempty directed preorder, of finite étale torsors `A_i` over `A` under
finite groups `G_i`, with surjections `G_j → G_i` and `A`-algebra maps `A_i → A_j` equivariant
along them, whose colimit `A_∞ = colim_i A_i` has no nonsplit finite étale covers
(`TauCeti.IsFiniteEtaleSplit`). Geometrically, `Spec A_∞ → Spec A` is a pro-finite étale Galois
cover, under the profinite group `lim_i G_i`, over which every finite étale cover of `Spec A`
becomes totally split: after pullback it is a finite disjoint union of clopen subschemes of the
base, which need not cover it. Its colimit is the ring-theoretic analogue of a separable closure
of a field, but it need not be a field even when `A` is one. The tower is purely algebraic and no
topology is involved.

Every commutative ring has a finite étale torsor tower
(`TauCeti.FiniteEtaleTorsorTower.nonempty_tower`). Choose, for each finite étale quotient
presentation `S = A[X_1, …, X_n] ⧸ I` (`TauCeti.FiniteEtaleSkeleton A`, a small family in which
isomorphic algebras may repeat), a finite étale torsor `P(S)` under a finite group `G(S)` over
which `S` becomes totally split (`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`).
The levels are indexed by the finite sets `F` of finite étale quotient presentations, ordered by
inclusion: the level at `F` is `⨂_{S ∈ F} P(S)`, a torsor under `∏_{S ∈ F} G(S)`
(`TauCeti.Algebra.IsFiniteEtaleTorsor.piTensorProduct`), and the transition maps are the
inclusions of tensor factors (`PiTensorProduct.finsetInclusion`) and the restrictions of group
elements (`Finset.restrict₂MonoidHom`). Every finite étale `A`-algebra is of finite type, hence
isomorphic to one of the finite étale quotient presentations
(`TauCeti.FiniteEtaleSkeleton.exists_algEquiv`), so it becomes totally split over some level, and
the colimit has no nonsplit finite étale covers
(`Ring.DirectLimit.isFiniteEtaleSplit_of_forall_exists_isTotallySplit`).

For `i ≤ j`, the transition map makes `A_j` a finite étale torsor over `A_i` under the kernel of
`G_j → G_i` (`TauCeti.FiniteEtaleTorsorTower.transition_isFiniteEtaleTorsor`); in particular the
transition maps are injective and faithfully flat.

## Main definitions

* `TauCeti.FiniteEtaleTorsorTower A`: a finite étale torsor tower over `A`.

## Main results

* `TauCeti.FiniteEtaleTorsorTower.nonempty_tower`: every commutative ring has a finite étale torsor
  tower.
* `TauCeti.FiniteEtaleTorsorTower.transition_isFiniteEtaleTorsor`: for `i ≤ j`, `A_j` is a finite
  étale torsor over `A_i` under the kernel of `G_j → G_i`.
* `TauCeti.FiniteEtaleTorsorTower.transition_injective`: the transition maps are injective.
* `TauCeti.FiniteEtaleTorsorTower.π_π`, `TauCeti.FiniteEtaleTorsorTower.transition_transition`
  and their identity and `comp` forms: the functoriality of `π` and `transition`.

## References

* P. Scholze, *Étale cohomology of diamonds*, §15, proof of Lemma 15.3.
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Lecture 10, proof of
  Lemma 10.1.6.
-/

public section

universe u

open TensorProduct PiTensorProduct

namespace TauCeti

/-- A *finite étale torsor tower* over a commutative ring `A`: a directed system, indexed by a
nonempty directed preorder `ι`, of finite étale torsors `level i` over `A` under finite groups
`G i`, with surjective homomorphisms `π h : G j →* G i` and `A`-algebra maps
`transition h : level i →ₐ[A] level j` for `i ≤ j`, the latter equivariant along the former, such
that the colimit `colim_i level i` has no nonsplit finite étale covers.

The groups form an inverse system and the levels a directed system: `π` and `transition` are the
identity at `i ≤ i` and compatible with composition. -/
structure FiniteEtaleTorsorTower (A : Type u) [CommRing A] where
  /-- The index set. -/
  ι : Type u
  /-- The order on the index set. -/
  [preorder : Preorder ι]
  /-- The index set is directed. -/
  [isDirectedOrder : IsDirectedOrder ι]
  /-- The index set is nonempty. -/
  [nonempty : Nonempty ι]
  /-- The finite group at level `i`. -/
  G : ι → Type u
  /-- The group structure at level `i`. -/
  [instGroup : ∀ i, Group (G i)]
  /-- The group at level `i` is finite. -/
  [finite : ∀ i, Finite (G i)]
  /-- The surjection `G j →* G i` for `i ≤ j`. -/
  π : ∀ ⦃i j : ι⦄, i ≤ j → G j →* G i
  /-- The maps `π` are the identity at `i ≤ i` and compatible with composition. -/
  [inverseSystem : InverseSystem (F := G) fun _ _ h ↦ ⇑(π h)]
  /-- The maps `π` are surjective. -/
  π_surjective : ∀ ⦃i j : ι⦄ (h : i ≤ j), Function.Surjective (π h)
  /-- The finite étale torsor at level `i`. -/
  level : ι → Type u
  /-- The ring structure at level `i`. -/
  [commRing : ∀ i, CommRing (level i)]
  /-- The `A`-algebra structure at level `i`. -/
  [algebra : ∀ i, _root_.Algebra A (level i)]
  /-- The action of `G i` on level `i`. -/
  [mulSemiringAction : ∀ i, MulSemiringAction (G i) (level i)]
  /-- The group `G i` acts on level `i` by `A`-algebra automorphisms. -/
  [smulCommClass : ∀ i, SMulCommClass (G i) A (level i)]
  /-- Level `i` is a finite étale `G i`-torsor over `A`. -/
  [isFiniteEtaleTorsor : ∀ i, Algebra.IsFiniteEtaleTorsor (G i) A (level i)]
  /-- The transition map `level i →ₐ[A] level j` for `i ≤ j`. -/
  transition : ∀ ⦃i j : ι⦄, i ≤ j → level i →ₐ[A] level j
  /-- The transition maps are the identity at `i ≤ i` and compatible with composition. -/
  [directedSystem : DirectedSystem level fun _ _ h ↦ ⇑(transition h)]
  /-- The transition maps are equivariant along `π`. -/
  transition_smul : ∀ ⦃i j : ι⦄ (h : i ≤ j) (g : G j) (a : level i),
    transition h (π h g • a) = g • transition h a
  /-- The colimit of the levels has no nonsplit finite étale covers. -/
  isFiniteEtaleSplit : IsFiniteEtaleSplit (Ring.DirectLimit level fun _ _ h ↦ transition h)

namespace FiniteEtaleTorsorTower

attribute [instance] preorder isDirectedOrder nonempty instGroup finite inverseSystem commRing
  algebra mulSemiringAction smulCommClass isFiniteEtaleTorsor directedSystem

section Functoriality

variable {A : Type u} [CommRing A] (T : FiniteEtaleTorsorTower A) {i j k : T.ι}

/-- The group surjection `π` along `i ≤ i` is the identity. -/
@[simp]
theorem π_self (h : i ≤ i) (g : T.G i) : T.π h g = g :=
  InverseSystem.map_self (f := fun _ _ h ↦ ⇑(T.π h)) g

/-- The group surjections `π` compose. -/
@[simp]
theorem π_π (hij : i ≤ j) (hjk : j ≤ k) (g : T.G k) :
    T.π hij (T.π hjk g) = T.π (hij.trans hjk) g :=
  InverseSystem.map_map (f := fun _ _ h ↦ ⇑(T.π h)) hij hjk g

/-- The group surjection `π` along `i ≤ i` is the identity homomorphism. -/
theorem π_self_eq_id (h : i ≤ i) : T.π h = MonoidHom.id (T.G i) :=
  MonoidHom.ext (T.π_self h)

/-- The group surjections `π` compose, as homomorphisms. -/
@[simp]
theorem π_comp_π (hij : i ≤ j) (hjk : j ≤ k) : (T.π hij).comp (T.π hjk) = T.π (hij.trans hjk) :=
  MonoidHom.ext (T.π_π hij hjk)

/-- The transition map along `i ≤ i` is the identity. -/
@[simp]
theorem transition_self (h : i ≤ i) (a : T.level i) : T.transition h a = a :=
  DirectedSystem.map_self (f := fun _ _ h ↦ ⇑(T.transition h)) a

/-- The transition maps compose. -/
@[simp]
theorem transition_transition (hij : i ≤ j) (hjk : j ≤ k) (a : T.level i) :
    T.transition hjk (T.transition hij a) = T.transition (hij.trans hjk) a :=
  DirectedSystem.map_map (f := fun _ _ h ↦ ⇑(T.transition h)) hij hjk a

/-- The transition map along `i ≤ i` is the identity algebra map. -/
theorem transition_self_eq_id (h : i ≤ i) : T.transition h = AlgHom.id A (T.level i) :=
  AlgHom.ext (T.transition_self h)

/-- The transition maps compose, as algebra maps. -/
@[simp]
theorem transition_comp_transition (hij : i ≤ j) (hjk : j ≤ k) :
    (T.transition hjk).comp (T.transition hij) = T.transition (hij.trans hjk) :=
  AlgHom.ext (T.transition_transition hij hjk)

end Functoriality

section Transition

variable {A : Type u} [CommRing A] (T : FiniteEtaleTorsorTower A) {i j : T.ι} (h : i ≤ j)

/-- For `i ≤ j`, the kernel of `π h : G j →* G i` acts on `level j` by `level i`-algebra
automorphisms, for the `level i`-algebra structure given by the transition map. -/
theorem smulCommClass_ker :
    letI := (T.transition h).toAlgebra
    SMulCommClass (T.π h).ker (T.level i) (T.level j) :=
  letI := (T.transition h).toAlgebra
  Algebra.smulCommClass_ker (π := T.π h) fun g a ↦ (T.transition_smul h g a).symm

/-- **Transitions are torsors.** For `i ≤ j`, the transition map makes `level j` a finite étale
torsor over `level i` under the kernel of `π h : G j →* G i`. -/
theorem transition_isFiniteEtaleTorsor :
    letI := (T.transition h).toAlgebra
    haveI := T.smulCommClass_ker h
    Algebra.IsFiniteEtaleTorsor (T.π h).ker (T.level i) (T.level j) := by
  let := (T.transition h).toAlgebra
  have : IsScalarTower A (T.level i) (T.level j) := .of_algHom (T.transition h)
  exact Algebra.IsFiniteEtaleTorsor.of_surjective (A := A) (T.π_surjective h)
    fun g a ↦ (T.transition_smul h g a).symm

/-- The transition maps of a finite étale torsor tower are injective. -/
theorem transition_injective : Function.Injective (T.transition h) := by
  let := (T.transition h).toAlgebra
  have := T.smulCommClass_ker h
  have := (T.transition_isFiniteEtaleTorsor h).faithfullyFlat
  -- The transition map is the algebra map of the induced `level i`-algebra structure.
  have hinj := FaithfulSMul.algebraMap_injective (T.level i) (T.level j)
  rw [RingHom.algebraMap_toAlgebra] at hinj
  exact hinj

end Transition

section OfSplittingFamily

attribute [local instance] piMulSemiringAction

variable {A : Type u} [CommRing A] {τ : Type u} (G : τ → Type u) [∀ t, Group (G t)]
  (P : τ → Type u) [∀ t, CommRing (P t)] [∀ t, _root_.Algebra A (P t)]

/-- If an `A`-algebra `S` becomes totally split over `P t`, then it becomes totally split over the
singleton level `⨂_{s ∈ {t}} P s`. -/
private theorem isTotallySplit_singleton (t : τ) (S : Type u) [CommRing S]
    [_root_.Algebra A S] (hS : Algebra.IsTotallySplit (P t) (P t ⊗[A] S)) :
    Algebra.IsTotallySplit (⨂[A] s : ({t} : Finset τ), P s)
      ((⨂[A] s : ({t} : Finset τ), P s) ⊗[A] S) := by
  classical
  let incl := singleAlgHom (R := A) (A := fun s : ({t} : Finset τ) ↦ P s)
    ⟨t, Finset.mem_singleton_self t⟩
  let := incl.toAlgebra
  have : IsScalarTower A (P t) (⨂[A] s : ({t} : Finset τ), P s) := .of_algHom incl
  exact hS.tensorProduct_of_isScalarTower

open scoped Classical in
variable (A) [∀ t, Finite (G t)] [∀ t, MulSemiringAction (G t) (P t)]
  [∀ t, SMulCommClass (G t) A (P t)] [∀ t, Algebra.IsFiniteEtaleTorsor (G t) A (P t)] in
/-- The finite étale torsor tower of finite tensor products of a family of finite étale torsors
`P t` over `A` under finite groups `G t`, over which every finite étale `A`-algebra becomes totally
split. Its levels are indexed by the finite subsets `F` of the index type: the level at `F` is
`⨂_{t ∈ F} P t`, a torsor under `∏_{t ∈ F} G t`; the transition maps are the inclusions of tensor
factors and the restrictions of group elements. -/
private noncomputable def ofSplittingFamily
    (hsplit : ∀ (S : Type u) [CommRing S] [_root_.Algebra A S] [_root_.Algebra.Etale A S]
      [Module.Finite A S], ∃ t, Algebra.IsTotallySplit (P t) (P t ⊗[A] S)) :
    FiniteEtaleTorsorTower A where
  ι := Finset τ
  G F := ∀ t : F, G t
  π _ _ h := Finset.restrict₂MonoidHom (fun t ↦ G t) h
  inverseSystem :=
    { map_self _ g := DFunLike.congr_fun (Finset.restrict₂MonoidHom_refl (fun t ↦ G t)) g
      map_map _ _ _ h₁ h₂ g :=
        DFunLike.congr_fun (Finset.restrict₂MonoidHom_comp_restrict₂MonoidHom _ h₁ h₂) g }
  π_surjective F F' h := by
    -- Restriction is evaluation at the points of the injective inclusion `F → F'`.
    rw [Finset.coe_restrict₂MonoidHom]
    exact MonoidHom.pi_evalMonoidHom_surjective_of_injective
      (f := fun t : F ↦ (⟨t, h t.property⟩ : F')) fun _ _ hst ↦
        Subtype.ext (Subtype.mk.inj hst)
  level F := ⨂[A] t : F, P t
  transition _ _ h := finsetInclusion A P h
  transition_smul F F' h g x := by
    -- Restriction is `g ↦ fun t ↦ g (f t)` for the inclusion `f`, as `fiberwiseMul` expects.
    rw [Finset.coe_restrict₂MonoidHom, finsetInclusion_def]
    exact fiberwiseMul_piMulSemiringAction_smul (A := fun t : F' ↦ P t)
      (fun t : F ↦ (⟨t, h t.property⟩ : F')) g x
  isFiniteEtaleSplit := by
    have (F : Finset τ) : _root_.Algebra.Etale A (⨂[A] t : F, P t) :=
      Algebra.IsFiniteEtaleTorsor.etale (G := ∀ t : F, G t)
    have (F : Finset τ) : Module.Finite A (⨂[A] t : F, P t) :=
      Algebra.IsFiniteEtaleTorsor.finite (G := ∀ t : F, G t)
    refine Ring.DirectLimit.isFiniteEtaleSplit_of_forall_exists_isTotallySplit fun S _ _ _ _ ↦ ?_
    obtain ⟨t, ht⟩ := hsplit S
    exact ⟨{t}, isTotallySplit_singleton P t S ht⟩

end OfSplittingFamily

section Existence

variable (A : Type u) [CommRing A]

/-- A finite étale torsor over `A`, with group and algebra in the universe of `A`, over which `S`
becomes totally split. -/
private structure SplittingTorsor (S : Type*) [CommRing S] [_root_.Algebra A S] where
  /-- The group. -/
  G : Type u
  /-- The group structure. -/
  [group : Group G]
  /-- The group is finite. -/
  [finite : Finite G]
  /-- The torsor. -/
  P : Type u
  /-- The ring structure of the torsor. -/
  [commRing : CommRing P]
  /-- The `A`-algebra structure of the torsor. -/
  [algebra : _root_.Algebra A P]
  /-- The action of the group on the torsor. -/
  [mulSemiringAction : MulSemiringAction G P]
  /-- The group acts by `A`-algebra automorphisms. -/
  [smulCommClass : SMulCommClass G A P]
  /-- `P` is a finite étale `G`-torsor over `A`. -/
  [isFiniteEtaleTorsor : Algebra.IsFiniteEtaleTorsor G A P]
  /-- `S` becomes totally split over `P`. -/
  isTotallySplit : Algebra.IsTotallySplit P (P ⊗[A] S)

attribute [instance] SplittingTorsor.group SplittingTorsor.finite SplittingTorsor.commRing
  SplittingTorsor.algebra SplittingTorsor.mulSemiringAction SplittingTorsor.smulCommClass
  SplittingTorsor.isFiniteEtaleTorsor

/-- A chosen splitting torsor of each finite étale quotient presentation. -/
private noncomputable def splittingTorsor (t : FiniteEtaleSkeleton A) :
    SplittingTorsor A t.toFGAlgCatSkeleton.eval.obj :=
  Classical.choice <|
    have ⟨G, _, _, P, _, _, _, _, _, hP⟩ := Algebra.exists_isFiniteEtaleTorsor_isTotallySplit A
      t.toFGAlgCatSkeleton.eval.obj
    ⟨⟨G, P, hP⟩⟩

/-- Every finite étale `A`-algebra becomes totally split over the chosen splitting torsor of one
of the finite étale quotient presentations. -/
private theorem exists_isTotallySplit_splittingTorsor (S : Type u) [CommRing S]
    [_root_.Algebra A S] [_root_.Algebra.Etale A S] [Module.Finite A S] :
    ∃ t : FiniteEtaleSkeleton A,
      Algebra.IsTotallySplit (splittingTorsor A t).P ((splittingTorsor A t).P ⊗[A] S) := by
  obtain ⟨t, ⟨e⟩⟩ := FiniteEtaleSkeleton.exists_algEquiv A S
  let P := (splittingTorsor A t).P
  exact ⟨t, (splittingTorsor A t).isTotallySplit.of_algEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) e.symm)⟩

/-- **Every commutative ring has a finite étale torsor tower.** -/
theorem nonempty_tower : Nonempty (FiniteEtaleTorsorTower A) :=
  ⟨ofSplittingFamily A (fun t ↦ (splittingTorsor A t).G) (fun t ↦ (splittingTorsor A t).P)
    (exists_isTotallySplit_splittingTorsor A)⟩

end Existence

end FiniteEtaleTorsorTower

end TauCeti
