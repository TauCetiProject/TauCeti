/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import TauCeti.CategoryTheory.Galois.Topology

/-!
# Surjectivity and injectivity of homomorphisms of fundamental groups

Let `C` and `D` be Galois categories, `F : C ⥤ FintypeCat` a fibre functor and `P : D ⥤ C` a
functor such that `P ⋙ F` is again a fibre functor. Precomposition with `P` induces a continuous
homomorphism of fundamental groups `Aut F →* Aut (P ⋙ F)`
(`CategoryTheory.PreGaloisCategory.continuous_mapAut_whiskeringLeft`). This is how a morphism of
schemes `T ⟶ S` acts on étale fundamental groups, with `P` the base change of finite étale covers
along it.
This file characterises surjectivity and injectivity of this homomorphism in terms of `P`:

* it is surjective if and only if `P` carries connected objects to connected objects;
* it is injective if and only if every connected object `A` of `C` is a quotient of a subobject of
  `P.obj Y` for some `Y`, that is, there are a monomorphism `Z ⟶ P.obj Y` and an epimorphism
  `Z ⟶ A`.

Surjectivity uses Mathlib's criterion `toAut_surjective_of_isPretransitive`: a compact group
acting naturally and continuously on the fibres of `P ⋙ F`, transitively on those of Galois
objects, surjects onto `Aut (P ⋙ F)`. Here `Aut F` acts on `(P ⋙ F).obj Y = F.obj (P.obj Y)`,
transitively when `P.obj Y` is connected. Conversely, if `Aut F` acts transitively on the
nonempty fibre of an object, the object is connected
(`CategoryTheory.PreGaloisCategory.FiberFunctor.isConnected_of_isPretransitive`).

For injectivity, a kernel element acts trivially on every fibre of `P ⋙ F`, hence on the fibres of
subobjects and quotients of objects `P.obj Y`, hence on all fibres if these exhaust the connected
objects. Conversely, if the homomorphism is injective, it is a closed embedding because `Aut F`
is compact, so the stabiliser of a point `a` of the fibre of `A` contains the preimage of the
stabiliser of a point `y` of the fibre of some `P.obj Y`. The connected component of
`P.obj Y ⨯ A` through `(y, a)` then maps monomorphically to `P.obj Y` and epimorphically to `A`.

## Main results

* `CategoryTheory.PreGaloisCategory.FiberFunctor.of_iso`: a functor isomorphic to a fibre functor
  is a fibre functor.
* `CategoryTheory.PreGaloisCategory.FiberFunctor.isConnected_of_isPretransitive`: an object whose
  fibre is nonempty, with `Aut F` acting transitively on it, is connected.
* `CategoryTheory.PreGaloisCategory.mapAut_whiskeringLeft_surjective_iff`: the homomorphism
  `Aut F →* Aut (P ⋙ F)` is surjective if and only if `P` preserves connectedness.
* `CategoryTheory.PreGaloisCategory.mapAut_whiskeringLeft_injective_iff`: the homomorphism
  `Aut F →* Aut (P ⋙ F)` is injective if and only if every connected object of `C` is a quotient
  of a subobject of an object in the image of `P`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, Propositions 6.9 and 6.11.
* The Stacks Project, Lemma 0BN6 (Section 58.4, *Functors and homomorphisms*).
-/

public section

universe u₁ u₂ u₃ u₄ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]

/-- A functor naturally isomorphic to a fibre functor is a fibre functor. -/
theorem FiberFunctor.of_iso [PreGaloisCategory C] {F G : C ⥤ FintypeCat.{w}} (e : F ≅ G)
    [FiberFunctor F] : FiberFunctor G where
  preservesTerminalObjects := preservesLimitsOfShape_of_natIso e
  preservesPullbacks := preservesLimitsOfShape_of_natIso e
  preservesFiniteCoproducts := ⟨fun _ ↦ preservesColimitsOfShape_of_natIso e⟩
  preservesEpis := Functor.PreservesEpimorphisms.of_iso e
  preservesQuotientsByFiniteGroups _ _ _ := preservesColimitsOfShape_of_natIso e
  reflectsIsos := reflectsIsomorphisms_of_iso e

/-- An object whose fibre under a fibre functor `F` is nonempty, and on which `Aut F` acts
transitively, is connected. Mathlib's `FiberFunctor.isPretransitive_of_isConnected` is the
converse. -/
theorem FiberFunctor.isConnected_of_isPretransitive [PreGaloisCategory C] (F : C ⥤ FintypeCat.{w})
    [FiberFunctor F] (X : C) [Nonempty (F.obj X)] [MulAction.IsPretransitive (Aut F) (F.obj X)] :
    IsConnected X where
  notInitial h := not_initial_of_inhabited F (Classical.arbitrary (F.obj X)) h
  noTrivialComponent Z i _ hZ := by
    obtain ⟨z⟩ := (not_initial_iff_fiber_nonempty F Z).mp hZ
    have hinj : Function.Injective (F.map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
    have hsurj : Function.Surjective (F.map i) := fun x ↦ by
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) (F.map i z) x
      exact ⟨σ • z, by rw [← mulAction_naturality, hσ]⟩
    have : IsIso (F.map i) :=
      (ConcreteCategory.isIso_iff_bijective (F.map i)).mpr ⟨hinj, hsurj⟩
    exact isIso_of_reflects_iso i F

variable [GaloisCategory C] [GaloisCategory D] (P : D ⥤ C) (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

/-- **Surjectivity criterion.** If `P ⋙ F` is a fibre functor, the homomorphism of fundamental
groups `Aut F →* Aut (P ⋙ F)` induced by `P` is surjective if and only if `P` carries connected
objects to connected objects. -/
theorem mapAut_whiskeringLeft_surjective_iff [FiberFunctor (P ⋙ F)] :
    Function.Surjective (((Functor.whiskeringLeft D C FintypeCat.{w}).obj P).mapAut F) ↔
      PreservesIsConnected P := by
  refine ⟨fun h ↦ ⟨fun {Y} _ ↦ ?_⟩, fun _ ↦ ?_⟩
  · -- `Aut F` acts on the nonempty fibre of `P.obj Y` through `Aut (P ⋙ F)`, transitively.
    have : Nonempty (F.obj (P.obj Y)) := nonempty_fiber_of_isConnected (P ⋙ F) Y
    have : MulAction.IsPretransitive (Aut F) (F.obj (P.obj Y)) := ⟨fun x x' ↦ by
      obtain ⟨τ, hτ⟩ := (FiberFunctor.isPretransitive_of_isConnected (P ⋙ F) Y).exists_smul_eq x x'
      obtain ⟨σ, rfl⟩ := h τ
      exact ⟨σ, hτ⟩⟩
    exact FiberFunctor.isConnected_of_isPretransitive F (P.obj Y)
  · -- `Aut F` acts on the fibres of `P ⋙ F` as on those of `F`; its image is all of
    -- `Aut (P ⋙ F)` by Mathlib's criterion for compact groups acting transitively.
    let (Y : D) : MulAction (Aut F) ((P ⋙ F).obj Y) :=
      inferInstanceAs (MulAction (Aut F) (F.obj (P.obj Y)))
    have : IsNaturalSMul (P ⋙ F) (Aut F) :=
      ⟨fun σ _ _ f x ↦ (mulAction_naturality F σ (P.map f) x).symm⟩
    have (Y : D) : ContinuousSMul (Aut F) ((P ⋙ F).obj Y) := continuousSMul_aut_fiber F (P.obj Y)
    have hsurj := toAut_surjective_of_isPretransitive (P ⋙ F) (Aut F) fun Y _ ↦
      have : IsConnected (P.obj Y) := PreservesIsConnected.preserves
      FiberFunctor.isPretransitive_of_isConnected F (P.obj Y)
    -- Both send `σ` to the automorphism acting on `(P ⋙ F).obj Y = F.obj (P.obj Y)` by `σ`;
    -- the local action instance above is this action by definition.
    have heq : toAut (P ⋙ F) (Aut F) =
        ((Functor.whiskeringLeft D C FintypeCat.{w}).obj P).mapAut F := by
      ext σ Y x
      rfl
    rwa [← heq]

/-- If `Aut F →* Aut (P ⋙ F)` is injective, every connected object `A` of `C` receives an
epimorphism from a subobject of some `P.obj Y`. -/
private theorem exists_mono_epi_of_mapAut_whiskeringLeft_injective [FiberFunctor (P ⋙ F)]
    (h : Function.Injective (((Functor.whiskeringLeft D C FintypeCat.{w}).obj P).mapAut F))
    (A : C) [IsConnected A] :
    ∃ (Y : D) (Z : C) (i : Z ⟶ P.obj Y) (p : Z ⟶ A), Mono i ∧ Epi p := by
  let φ : Aut F →* Aut (P ⋙ F) := ((Functor.whiskeringLeft D C FintypeCat.{w}).obj P).mapAut F
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  -- `φ` is a closed embedding, so the stabiliser of `a` is the preimage of an open set `V`.
  obtain ⟨V, hV, hVa⟩ := ((continuous_mapAut_whiskeringLeft P F).isClosedEmbedding
    h).isInducing.isOpen_iff.mp (stabilizer_isOpen (Aut F) a)
  have hV1 : V ∈ nhds (1 : Aut (P ⋙ F)) := by
    refine hV.mem_nhds ?_
    have : (1 : Aut F) ∈ φ ⁻¹' V := hVa ▸ one_mem (MulAction.stabilizer (Aut F) a)
    rwa [Set.mem_preimage, map_one] at this
  -- `V` contains the stabiliser of a point `y` of the fibre of some `P.obj Y`.
  obtain ⟨⟨Y, y, _⟩, -, hY⟩ := (nhds_one_has_basis_stabilizers (P ⋙ F)).mem_iff.mp hV1
  -- Restating the type of `y` as the fibre of `F` at `P.obj Y`, which `(P ⋙ F).obj Y` is by
  -- definition, lets `Aut F` act on it; `φ σ` acts on `y` as `σ` does, by definition of `φ`.
  set y' : F.obj (P.obj Y) := y
  have hstab (σ : Aut F) (hσ : σ • y' = y') : σ • a = a := by
    have : σ ∈ φ ⁻¹' V := hY hσ
    rwa [hVa] at this
  -- The connected component `W` of `P.obj Y ⨯ A` through `(y, a)`.
  let e := fiberBinaryProductEquiv F (P.obj Y) A
  obtain ⟨W, j, w, hw, _, _⟩ := fiber_in_connected_component F (P.obj Y ⨯ A) (e.symm (y', a))
  have : Nonempty (F.obj W) := ⟨w⟩
  refine ⟨Y, W, j ≫ prod.fst, j ≫ prod.snd, ?_, epi_of_nonempty_of_isConnected F _⟩
  have he (u : F.obj (P.obj Y ⨯ A)) : e u = (F.map prod.fst u, F.map prod.snd u) := by
    obtain ⟨⟨p₁, p₂⟩, rfl⟩ := e.symm.surjective u
    simp [e]
  have hjinj : Function.Injective (F.map j) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map j)
  -- The projection to `P.obj Y` is injective on the fibre of `W`: two points of it with the
  -- same first coordinate differ by some `σ`, which then fixes their second coordinate by
  -- `hstab`, after conjugating the first point back to the base point `w`.
  refine F.mono_of_mono_map ((ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
    fun x₁ x₂ hx ↦ ?_)
  have : MulAction.IsPretransitive (Aut F) (F.obj W) :=
    FiberFunctor.isPretransitive_of_isConnected F W
  obtain ⟨τ, rfl⟩ := MulAction.exists_smul_eq (Aut F) w x₁
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) (τ • w) x₂
  have hwy : F.map (j ≫ prod.fst) w = y' := by simp [hw, e]
  have hwa : F.map (j ≫ prod.snd) w = a := by simp [hw, e]
  simp only [← mulAction_naturality, hwy] at hx
  have hσa : σ • τ • a = τ • a := by
    have := hstab (τ⁻¹ * σ * τ) (by rw [mul_smul, mul_smul, ← hx, inv_smul_smul])
    rwa [mul_smul, mul_smul, inv_smul_eq_iff] at this
  apply hjinj
  apply e.injective
  rw [he, he]
  simp only [← FintypeCat.comp_apply, ← F.map_comp, ← mulAction_naturality, hwy, hwa]
  exact Prod.ext hx hσa.symm

/-- **Injectivity criterion.** If `P ⋙ F` is a fibre functor, the homomorphism of fundamental
groups `Aut F →* Aut (P ⋙ F)` induced by `P` is injective if and only if every connected object
`A` of `C` is a quotient of a subobject of `P.obj Y` for some `Y`: there are a monomorphism
`i : Z ⟶ P.obj Y` and an epimorphism `p : Z ⟶ A`. -/
theorem mapAut_whiskeringLeft_injective_iff [FiberFunctor (P ⋙ F)] :
    Function.Injective (((Functor.whiskeringLeft D C FintypeCat.{w}).obj P).mapAut F) ↔
      ∀ (A : C) [IsConnected A], ∃ (Y : D) (Z : C) (i : Z ⟶ P.obj Y) (p : Z ⟶ A),
        Mono i ∧ Epi p := by
  refine ⟨fun h A _ ↦ exists_mono_epi_of_mapAut_whiskeringLeft_injective P F h A, fun h ↦ ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  -- The component of `φ σ = 1` at `Y` is the action of `σ` on the fibre of `P.obj Y`.
  have hfix (Y : D) (y : F.obj (P.obj Y)) : σ • y = y :=
    congr_arg (fun τ : Aut (P ⋙ F) ↦ τ.asIso.hom.app Y y) (MonoidHom.mem_ker.mp hσ)
  -- `σ` fixes the fibre of every connected object, as a quotient of a subobject of some `P.obj Y`.
  have hconn (A : C) [IsConnected A] (a : F.obj A) : σ • a = a := by
    obtain ⟨Y, Z, i, p, _, _⟩ := h A
    obtain ⟨z, rfl⟩ := surjective_on_fiber_of_epi F p a
    have hz : σ • z = z := ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
      (by rw [← mulAction_naturality, hfix])
    rw [mulAction_naturality, hz]
  ext X x
  obtain ⟨A, i, a, rfl, _, _⟩ := fiber_in_connected_component F X x
  exact (mulAction_naturality F σ i a).trans (congr_arg (F.map i) (hconn A a))

end PreGaloisCategory

end CategoryTheory
