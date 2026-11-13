/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import all TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Word maps and coordinate-group homomorphisms

A map `V_H(S) → V_H(T)` between algebraic sets is a *morphism* if it is given at every point by a
tuple of coefficient words. A tuple of words that maps one algebraic set into another induces a
coefficient-preserving homomorphism in the opposite direction between their coordinate groups,
`CoordGroup.homOfMapsToWordMap`, contravariantly functorially. Conversely, every such
homomorphism is represented by a tuple of words, and two tuples represent the same homomorphism
precisely when their word maps agree at every point of the source algebraic set. This describes
polynomial maps without choosing presentations of coordinate functions.

In the other direction, a coefficient-preserving homomorphism `φ : Γ(T) → Γ(S)` of coordinate
groups induces the map `CoordGroup.comap φ : V_H(S) → V_H(T)`: a solution of `S`, viewed as a
homomorphism `Γ(S) → H`, is precomposed with `φ`. This is again functorial, and the morphisms
`V_H(S) → V_H(T)` correspond bijectively to the homomorphisms `Γ(T) → Γ(S)`. Consequently two
algebraic sets are isomorphic through mutually inverse morphisms exactly when their coordinate
groups are isomorphic by an isomorphism fixing the coefficients.

Everything holds for an arbitrary coefficient homomorphism `ι : G →* H`, including systems
without solutions, whose coordinate groups are trivial.

## Main definitions

* `TauCeti.GroupAlgGeom.IsWordMap`: a map between algebraic sets given by a tuple of words.
* `TauCeti.GroupAlgGeom.CoordGroup.comap`: the map of algebraic sets induced by a
  coordinate-group homomorphism.
* `TauCeti.GroupAlgGeom.CoordGroup.gHomEquivWordMap`: coefficient-preserving homomorphisms
  `Γ(T) → Γ(S)` correspond to morphisms `V_H(S) → V_H(T)`.

## Main results

* `TauCeti.GroupAlgGeom.isWordMap_id`, `TauCeti.GroupAlgGeom.IsWordMap.comp`: morphisms of
  algebraic sets contain the identities and are closed under composition.
* `TauCeti.GroupAlgGeom.CoordGroup.comap_id`, `TauCeti.GroupAlgGeom.CoordGroup.comap_comp`:
  the map of algebraic sets induced by a coordinate-group homomorphism is contravariantly
  functorial.
* `TauCeti.GroupAlgGeom.CoordGroup.exists_wordMap_representation`,
  `TauCeti.GroupAlgGeom.CoordGroup.homOfMapsToWordMap_eq_iff`: every coordinate-group
  homomorphism comes from a word map, unique up to agreement on the algebraic set.
* `TauCeti.GroupAlgGeom.CoordGroup.exists_mulEquiv_iff_exists_equiv_isWordMap`: algebraic sets
  are isomorphic if and only if their coordinate groups are isomorphic over the coefficients.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.3, Definitions 13 and 14, and §3.5, Theorem 4 and
  Corollary 9.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod

variable {G H X Y Z : Type*} [Group G] [Group H]

/-! ### Morphisms of algebraic sets -/

section IsWordMap

variable {ι : G →* H} {S : Set (GX G X)} {T : Set (GX G Y)} {U : Set (GX G Z)}

/-- A map `V_H(S) → V_H(T)` between algebraic sets is a *morphism* if there is a tuple of
coefficient words `w : Y → G[X]` such that `f v = (w_y(v))_y` at every solution `v` of `S`. -/
def IsWordMap (f : V ι S → V ι T) : Prop :=
  ∃ w : Y → GX G X, ∀ v : V ι S, (f v : Y → H) = wordMap ι w v

/-- A map between algebraic sets is a morphism exactly when some tuple of words gives it at every
point. -/
theorem isWordMap_iff {f : V ι S → V ι T} :
    IsWordMap f ↔ ∃ w : Y → GX G X, ∀ v : V ι S, (f v : Y → H) = wordMap ι w v :=
  Iff.rfl

/-- The identity of an algebraic set is a morphism, given by the tuple of variables. -/
theorem isWordMap_id : IsWordMap (id : V ι S → V ι S) :=
  ⟨fun x => inr (FreeGroup.of x), fun v => (wordMap_id (ι := ι) v.1).symm⟩

/-- Morphisms of algebraic sets compose; the composite is given by substituting the first tuple
of words into the second. -/
theorem IsWordMap.comp {g : V ι T → V ι U} {f : V ι S → V ι T} (hg : IsWordMap g)
    (hf : IsWordMap f) : IsWordMap (g ∘ f) := by
  obtain ⟨u, hu⟩ := hg
  obtain ⟨w, hw⟩ := hf
  refine ⟨fun z => eval (inl : G →* GX G X) w (u z), fun v => ?_⟩
  rw [Function.comp_apply, hu, hw, wordMap_wordMap]

end IsWordMap

namespace CoordGroup

variable (ι : G →* H) (S : Set (GX G X)) (T : Set (GX G Y)) (U : Set (GX G Z))

/-! ### Coordinate-group homomorphisms are given by word maps -/

/-- Every coefficient-preserving coordinate-group homomorphism is represented by a tuple of
coefficient words, whose word map carries source solutions to target solutions. -/
theorem exists_wordMap_representation (φ : GHom (coeff ι T) (coeff ι S)) :
    ∃ w : Y → GX G X, ∃ hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T),
      homOfMapsToWordMap ι S T w hw = φ := by
  classical
  have hsurj : ∀ y : Y, ∃ w : GX G X,
      (w : CoordGroup ι S) = φ ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T) := by
    intro y
    exact QuotientGroup.mk_surjective _
  choose w hw using hsurj
  have hmap : Set.MapsTo (wordMap ι w) (V ι S) (V ι T) := by
    intro v hv
    let ψ : GHom (coeff ι T) ι := (evalGHom v hv).comp φ
    have hcoords : wordMap ι w v = (homEquiv ι T ψ : Y → H) := by
      funext y
      simp only [wordMap_apply, homEquiv_apply_coe]
      rw [← evalGHom_mk (ι := ι) (S := S) hv (w y), hw y]
      exact (congrFun (GHom.coe_comp (evalGHom v hv) φ)
        ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T)).symm
    rw [hcoords]
    exact (homEquiv ι T ψ).property
  refine ⟨w, hmap, ?_⟩
  apply gHom_ext
  intro y
  rw [homOfMapsToWordMap_mk, eval_inr_of, hw y]

/-- Two representing tuples induce the same coordinate-group homomorphism exactly when they
give the same function on the source algebraic set. -/
theorem homOfMapsToWordMap_eq_iff (w w' : Y → GX G X)
    (hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T))
    (hw' : Set.MapsTo (wordMap ι w') (V ι S) (V ι T)) :
    homOfMapsToWordMap ι S T w hw = homOfMapsToWordMap ι S T w' hw' ↔
      ∀ v ∈ V ι S, wordMap ι w v = wordMap ι w' v := by
  constructor
  · intro h v hv
    have h' := congrArg (fun f : GHom (coeff ι T) (coeff ι S) =>
      (homEquiv ι T ((evalGHom v hv).comp f) : Y → H)) h
    exact (homEquiv_comp_homOfMapsToWordMap ι S T w hw ⟨v, hv⟩).symm.trans
      (h'.trans (homEquiv_comp_homOfMapsToWordMap ι S T w' hw' ⟨v, hv⟩))
  · intro h
    apply gHom_ext
    intro y
    simp only [homOfMapsToWordMap_mk, eval_inr_of]
    apply QuotientGroup.eq.mpr
    rw [mem_Rad]
    intro v hv
    have := congrFun (h v hv) y
    simpa only [wordMap_apply, map_mul, map_inv, inv_mul_eq_one] using this

/-! ### From coordinate-group homomorphisms to maps of algebraic sets -/

variable {ι S T U}

/-- A coefficient-preserving homomorphism `φ : Γ(T) → Γ(S)` maps solutions of `S` to solutions
of `T`: a solution of `S`, viewed as a homomorphism `Γ(S) → H`, is precomposed with `φ`. -/
def comap (φ : GHom (coeff ι T) (coeff ι S)) (v : V ι S) : V ι T :=
  homEquiv ι T ((evalGHom v.1 v.2).comp φ)

/-- Evaluation at `comap φ v` is evaluation at `v` precomposed with `φ`. -/
@[simp]
theorem evalGHom_comap (φ : GHom (coeff ι T) (coeff ι S)) (v : V ι S) :
    evalGHom (comap φ v : Y → H) (comap φ v).2 = (evalGHom v.1 v.2).comp φ :=
  (homEquiv ι T).symm_apply_apply _

/-- The coordinates of `comap φ v` are the values at `v` of the images of the variables
under `φ`. -/
@[simp]
theorem comap_apply_coe (φ : GHom (coeff ι T) (coeff ι S)) (v : V ι S) (y : Y) :
    (comap φ v : Y → H) y =
      evalGHom v.1 v.2 (φ ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T)) := by
  simp [comap]

/-- The identity of a coordinate group induces the identity of the algebraic set. -/
@[simp]
theorem comap_id : comap (GHom.id (coeff ι S)) = id := by
  ext v x
  simp

/-- Pointwise form of `comap_comp`. -/
theorem comap_comp_apply (φ : GHom (coeff ι T) (coeff ι S)) (ψ : GHom (coeff ι U) (coeff ι T))
    (v : V ι S) : comap (φ.comp ψ) v = comap ψ (comap φ v) := by
  apply (homEquiv ι U).symm.injective
  simp [GHom.comp_assoc]

/-- A composite of coordinate-group homomorphisms induces the composite of the induced maps of
algebraic sets, in the opposite order. -/
@[simp]
theorem comap_comp (φ : GHom (coeff ι T) (coeff ι S)) (ψ : GHom (coeff ι U) (coeff ι T)) :
    comap (φ.comp ψ) = comap ψ ∘ comap φ :=
  funext (comap_comp_apply φ ψ)

/-- On a word map, `comap` of the induced homomorphism is that word map. -/
@[simp]
theorem comap_homOfMapsToWordMap (w : Y → GX G X) (hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T))
    (v : V ι S) :
    (comap (homOfMapsToWordMap ι S T w hw) v : Y → H) = wordMap ι w v :=
  homEquiv_comp_homOfMapsToWordMap ι S T w hw v

/-- The map of algebraic sets induced by a coordinate-group homomorphism is a morphism. -/
theorem isWordMap_comap (φ : GHom (coeff ι T) (coeff ι S)) : IsWordMap (comap φ) := by
  obtain ⟨w, hw, rfl⟩ := exists_wordMap_representation ι S T φ
  exact ⟨w, comap_homOfMapsToWordMap w hw⟩

/-- A coordinate-group homomorphism is determined by the map it induces on algebraic sets. -/
theorem comap_injective :
    Function.Injective (comap : GHom (coeff ι T) (coeff ι S) → V ι S → V ι T) := by
  intro φ ψ h
  obtain ⟨w, hw, rfl⟩ := exists_wordMap_representation ι S T φ
  obtain ⟨w', hw', rfl⟩ := exists_wordMap_representation ι S T ψ
  refine (homOfMapsToWordMap_eq_iff ι S T w w' hw hw').2 fun v hv => ?_
  simpa using congrArg Subtype.val (congrFun h ⟨v, hv⟩)

/-- The morphisms `V_H(S) → V_H(T)` are exactly the maps induced by coefficient-preserving
homomorphisms `Γ(T) → Γ(S)`. -/
theorem isWordMap_iff_exists_comap_eq {f : V ι S → V ι T} :
    IsWordMap f ↔ ∃ φ : GHom (coeff ι T) (coeff ι S), comap φ = f := by
  refine ⟨fun ⟨w, hf⟩ => ?_, fun ⟨φ, hφ⟩ => hφ ▸ isWordMap_comap φ⟩
  have hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T) := fun v hv => by
    rw [← hf ⟨v, hv⟩]
    exact (f ⟨v, hv⟩).2
  exact ⟨homOfMapsToWordMap ι S T w hw, funext fun v =>
    Subtype.ext ((comap_homOfMapsToWordMap w hw v).trans (hf v).symm)⟩

variable (ι S T) in
/-- Coefficient-preserving homomorphisms `Γ(T) → Γ(S)` of coordinate groups correspond to
morphisms `V_H(S) → V_H(T)` of algebraic sets, by `comap`. -/
noncomputable def gHomEquivWordMap :
    GHom (coeff ι T) (coeff ι S) ≃ {f : V ι S → V ι T // IsWordMap f} :=
  Equiv.ofBijective (fun φ => ⟨comap φ, isWordMap_comap φ⟩)
    ⟨fun _ _ h => comap_injective (congrArg Subtype.val h),
      fun f => (isWordMap_iff_exists_comap_eq.1 f.2).imp fun _ hφ => Subtype.ext hφ⟩

/-- The morphism corresponding to a coordinate-group homomorphism is the map it induces. -/
@[simp]
theorem gHomEquivWordMap_apply (φ : GHom (coeff ι T) (coeff ι S)) :
    (gHomEquivWordMap ι S T φ : V ι S → V ι T) = comap φ :=
  (rfl)

/-- The coordinate-group homomorphism corresponding to a morphism induces that morphism. -/
@[simp]
theorem comap_gHomEquivWordMap_symm (f : {g : V ι S → V ι T // IsWordMap g}) :
    comap ((gHomEquivWordMap ι S T).symm f) = f :=
  congrArg Subtype.val ((gHomEquivWordMap ι S T).apply_symm_apply f)

/-- Two algebraic sets are isomorphic through mutually inverse morphisms exactly when their
coordinate groups are isomorphic by an isomorphism fixing the coefficients. -/
theorem exists_mulEquiv_iff_exists_equiv_isWordMap :
    (∃ e : CoordGroup ι T ≃* CoordGroup ι S, ∀ g, e (coeff ι T g) = coeff ι S g) ↔
      ∃ e : V ι S ≃ V ι T, IsWordMap e ∧ IsWordMap e.symm := by
  constructor
  · rintro ⟨e, he⟩
    let φ : GHom (coeff ι T) (coeff ι S) := ⟨e.toMonoidHom, he⟩
    let ψ : GHom (coeff ι S) (coeff ι T) :=
      ⟨e.symm.toMonoidHom, fun g => e.symm_apply_eq.2 (he g).symm⟩
    have h₁ : φ.comp ψ = GHom.id _ := GHom.ext fun x => by simp [φ, ψ]
    have h₂ : ψ.comp φ = GHom.id _ := GHom.ext fun x => by simp [φ, ψ]
    refine ⟨⟨comap φ, comap ψ, fun v => ?_, fun v => ?_⟩, isWordMap_comap φ, isWordMap_comap ψ⟩
    · rw [← comap_comp_apply, h₁, comap_id, id]
    · rw [← comap_comp_apply, h₂, comap_id, id]
  · rintro ⟨e, he, he'⟩
    obtain ⟨φ, hφ⟩ := isWordMap_iff_exists_comap_eq.1 he
    obtain ⟨ψ, hψ⟩ := isWordMap_iff_exists_comap_eq.1 he'
    have h₁ : φ.comp ψ = GHom.id _ := comap_injective (by
      rw [comap_comp, hφ, hψ, comap_id, e.symm_comp_self])
    have h₂ : ψ.comp φ = GHom.id _ := comap_injective (by
      rw [comap_comp, hφ, hψ, comap_id, e.self_comp_symm])
    exact ⟨MonoidHom.toMulEquiv φ ψ
      (MonoidHom.ext fun x => by simpa using DFunLike.congr_fun h₂ x)
      (MonoidHom.ext fun x => by simpa using DFunLike.congr_fun h₁ x), φ.map_coeff⟩

end CoordGroup
end TauCeti.GroupAlgGeom
