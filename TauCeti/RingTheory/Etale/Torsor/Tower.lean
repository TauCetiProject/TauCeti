/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Colimit
public import TauCeti.RingTheory.Etale.Torsor.PiTensorProduct
public import TauCeti.RingTheory.Etale.Torsor.Splitting

import Mathlib.RingTheory.FiniteType
import TauCeti.Algebra.Group.Pi.Lemmas

/-!
# Towers of finite étale torsors

A *finite étale torsor tower* over a commutative ring `A` (`TauCeti.FiniteEtaleTorsorTower A`) is
a directed system, over a nonempty directed preorder, of finite étale torsors `A_i` over `A` under
finite groups `G_i`, with surjections `G_j → G_i` and `A`-algebra maps `A_i → A_j` equivariant
along them, whose colimit `A_∞ = colim_i A_i` has no nonsplit finite étale covers
(`TauCeti.IsFiniteEtaleSplit`). Geometrically, `Spec A_∞ → Spec A` is a pro-finite étale Galois
cover, under the profinite group `lim_i G_i`, which trivialises every finite étale cover of
`Spec A`. Its colimit is the ring-theoretic analogue of a separable closure of a field, but it need
not be a field even when `A` is one. The tower is purely algebraic and no topology is involved.

Every commutative ring has a finite étale torsor tower
(`TauCeti.FiniteEtaleTorsorTower.nonempty_tower`). Choose, for each finite étale `A`-algebra `S`
in a small set of representatives, a finite étale torsor `P(S)` under a finite group `G(S)`
splitting `S` (`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`). The levels are
indexed by the finite sets `F` of representatives, ordered by inclusion: the level at `F` is
`⨂_{S ∈ F} P(S)`, a torsor under `∏_{S ∈ F} G(S)`
(`TauCeti.Algebra.IsFiniteEtaleTorsor.piTensorProduct`), and the transition maps are the
inclusions of tensor factors (`PiTensorProduct.fiberwiseMul`) and the restrictions of group
elements. Every finite étale `A`-algebra becomes totally split over some level, so the colimit
has no nonsplit finite étale covers
(`Ring.DirectLimit.isFiniteEtaleSplit_of_forall_exists_isTotallySplit`). As the representatives
we take the quotients of polynomial rings `A[X_1, …, X_n]` that are finite étale over `A`; every
finite étale `A`-algebra is of finite type, hence isomorphic to one of them.

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
  [group : ∀ i, Group (G i)]
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

attribute [instance] preorder isDirectedOrder nonempty group finite inverseSystem commRing algebra
  mulSemiringAction smulCommClass isFiniteEtaleTorsor directedSystem

section Transition

variable {A : Type u} [CommRing A] (T : FiniteEtaleTorsorTower A) {i j : T.ι} (h : i ≤ j)

/-- **Transitions are torsors.** For `i ≤ j`, the transition map makes `level j` a finite étale
torsor over `level i` under the kernel of `π h : G j →* G i`. -/
theorem transition_isFiniteEtaleTorsor :
    letI := (T.transition h).toAlgebra
    haveI := Algebra.smulCommClass_ker (π := T.π h) fun g a ↦ (T.transition_smul h g a).symm
    Algebra.IsFiniteEtaleTorsor (T.π h).ker (T.level i) (T.level j) := by
  let := (T.transition h).toAlgebra
  have : IsScalarTower A (T.level i) (T.level j) := .of_algHom (T.transition h)
  exact Algebra.IsFiniteEtaleTorsor.of_surjective (A := A) (T.π_surjective h)
    fun g a ↦ (T.transition_smul h g a).symm

/-- The transition maps of a finite étale torsor tower are injective. -/
theorem transition_injective : Function.Injective (T.transition h) :=
  letI := (T.transition h).toAlgebra
  haveI := Algebra.smulCommClass_ker (π := T.π h) fun g a ↦ (T.transition_smul h g a).symm
  haveI := (T.transition_isFiniteEtaleTorsor h).faithfullyFlat
  FaithfulSMul.algebraMap_injective (T.level i) (T.level j)

end Transition

section OfSplittingFamily

attribute [local instance] piMulSemiringAction

variable {A : Type u} [CommRing A] {τ : Type u} (G : τ → Type u) [∀ t, Group (G t)]
  (P : τ → Type u) [∀ t, CommRing (P t)] [∀ t, _root_.Algebra A (P t)]

/-- The restriction `∏_{t ∈ F'} G t →* ∏_{t ∈ F} G t` for finite sets `F ⊆ F'`. -/
private def restrict {F F' : Finset τ} (h : F ≤ F') : (∀ t : F', G t) →* ∀ t : F, G t :=
  MonoidHom.pi fun t ↦ Pi.evalMonoidHom (fun t : F' ↦ G t) ⟨t, h t.property⟩

open scoped Classical in
/-- The inclusion of tensor factors `⨂_{t ∈ F} P t →ₐ[A] ⨂_{t ∈ F'} P t` for finite sets
`F ⊆ F'`. -/
private noncomputable def incl {F F' : Finset τ} (h : F ≤ F') :
    (⨂[A] t : F, P t) →ₐ[A] ⨂[A] t : F', P t :=
  fiberwiseMul (A := fun t : F' ↦ P t) fun t : F ↦ ⟨t, h t.property⟩

private theorem incl_smul [∀ t, MulSemiringAction (G t) (P t)] [∀ t, SMulCommClass (G t) A (P t)]
    {F F' : Finset τ} (h : F ≤ F') (g : ∀ t : F', G t)
    (x : ⨂[A] t : F, P t) : incl P h (restrict G h g • x) = g • incl P h x := by
  classical
  exact fiberwiseMul_piMulSemiringAction_smul (A := fun t : F' ↦ P t)
    (fun t : F ↦ (⟨t, h t.property⟩ : F')) g x

private instance directedSystem_incl :
    DirectedSystem (fun F : Finset τ ↦ ⨂[A] t : F, P t) fun _ _ h ↦ ⇑(incl P h) := by
  classical
  -- The inclusion along `F ⊆ F` is `fiberwiseMul id`, and `fiberwiseMul` is functorial.
  refine ⟨fun F x ↦ DFunLike.congr_fun (fiberwiseMul_id A fun t : F ↦ P t) x,
    fun F₃ F₂ F₁ h₁₂ h₂₃ x ↦ ?_⟩
  exact DFunLike.congr_fun (fiberwiseMul_comp (R := A) (A := fun t : F₃ ↦ P t)
    (fun t : F₂ ↦ (⟨t, h₂₃ t.property⟩ : F₃)) fun t : F₁ ↦ ⟨t, h₁₂ t.property⟩) x

/-- Over the tensor product of a finite family of torsors containing `P t`, every algebra split
by `P t` is split. -/
private theorem isTotallySplit_incl_singleton (t : τ) (S : Type u) [CommRing S]
    [_root_.Algebra A S] (hS : Algebra.IsTotallySplit (P t) (P t ⊗[A] S)) :
    Algebra.IsTotallySplit (⨂[A] s : ({t} : Finset τ), P s)
      ((⨂[A] s : ({t} : Finset τ), P s) ⊗[A] S) := by
  classical
  let L := ⨂[A] s : ({t} : Finset τ), P s
  let := (singleAlgHom (R := A) (A := fun s : ({t} : Finset τ) ↦ P s)
    ⟨t, Finset.mem_singleton_self t⟩).toAlgebra
  have : IsScalarTower A (P t) L := .of_algebraMap_eq' (singleAlgHom _).comp_algebraMap.symm
  exact (hS.baseChange L).of_algEquiv (Algebra.TensorProduct.cancelBaseChange A (P t) L L S)

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
  π _ _ h := restrict G h
  inverseSystem := ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩
  π_surjective _ _ h := MonoidHom.pi_evalMonoidHom_surjective_of_injective
    (Set.inclusion_injective (Finset.coe_subset.mpr h))
  level F := ⨂[A] t : F, P t
  transition _ _ h := incl P h
  transition_smul _ _ h g x := incl_smul G P h g x
  isFiniteEtaleSplit := by
    have (F : Finset τ) : _root_.Algebra.Etale A (⨂[A] t : F, P t) :=
      Algebra.IsFiniteEtaleTorsor.etale (G := ∀ t : F, G t)
    have (F : Finset τ) : Module.Finite A (⨂[A] t : F, P t) :=
      Algebra.IsFiniteEtaleTorsor.finite (G := ∀ t : F, G t)
    refine Ring.DirectLimit.isFiniteEtaleSplit_of_forall_exists_isTotallySplit fun S _ _ _ _ ↦ ?_
    obtain ⟨t, ht⟩ := hsplit S
    exact ⟨{t}, isTotallySplit_incl_singleton P t S ht⟩

end OfSplittingFamily

section Existence

variable (A : Type u) [CommRing A]

/-- The finite étale `A`-algebras of the form `A[X_1, …, X_n] ⧸ I`: every finite étale
`A`-algebra is isomorphic to one of them. -/
private def Presentation : Type u :=
  {t : Σ n : ℕ, Ideal (MvPolynomial (Fin n) A) //
    _root_.Algebra.Etale A (MvPolynomial (Fin t.fst) A ⧸ t.snd) ∧
      Module.Finite A (MvPolynomial (Fin t.fst) A ⧸ t.snd)}

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

/-- A chosen splitting torsor of each presented finite étale algebra. -/
private noncomputable def splittingTorsor (t : Presentation A) :
    SplittingTorsor A (MvPolynomial (Fin t.val.fst) A ⧸ t.val.snd) :=
  have := t.property.1
  have := t.property.2
  Classical.choice <|
    have ⟨G, _, _, P, _, _, _, _, _, hP⟩ := Algebra.exists_isFiniteEtaleTorsor_isTotallySplit A
      (MvPolynomial (Fin t.val.fst) A ⧸ t.val.snd)
    ⟨⟨G, P, hP⟩⟩

/-- Every finite étale `A`-algebra becomes totally split over the chosen splitting torsor of one
of the presented finite étale algebras. -/
private theorem exists_isTotallySplit_splittingTorsor (S : Type u) [CommRing S]
    [_root_.Algebra A S] [_root_.Algebra.Etale A S] [Module.Finite A S] :
    ∃ t : Presentation A,
      Algebra.IsTotallySplit (splittingTorsor A t).P ((splittingTorsor A t).P ⊗[A] S) := by
  obtain ⟨n, f, hf⟩ := _root_.Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : _root_.Algebra.FiniteType A S)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let t : Presentation A :=
    ⟨⟨n, RingHom.ker f⟩, .of_equiv e.symm, .equiv e.symm.toLinearEquiv⟩
  let P := (splittingTorsor A t).P
  exact ⟨t, (splittingTorsor A t).isTotallySplit.of_algEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) e)⟩

/-- **Every commutative ring has a finite étale torsor tower.** The levels are the finite tensor
products of splitting torsors of finite étale `A`-algebras, indexed by the finite sets of finite
étale `A`-algebras, so that every finite étale `A`-algebra is split at some level. -/
theorem nonempty_tower : Nonempty (FiniteEtaleTorsorTower A) :=
  ⟨ofSplittingFamily A (fun t ↦ (splittingTorsor A t).G) (fun t ↦ (splittingTorsor A t).P)
    (exists_isTotallySplit_splittingTorsor A)⟩

end Existence

end FiniteEtaleTorsorTower

end TauCeti
