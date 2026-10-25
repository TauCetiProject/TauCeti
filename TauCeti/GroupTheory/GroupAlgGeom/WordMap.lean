/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Word maps and homomorphisms of coordinate groups

Let `H` be a group receiving the coefficients `G` through `ι : G →* H`. A tuple of words
`w : Y → G[X]` defines a *word map* `H^X → H^Y`, and it is a morphism of algebraic sets
`V_H(S) → V_H(T)` (for systems `S ⊆ G[X]`, `T ⊆ G[Y]`) when it maps the first set into the
second. This file shows that such morphisms are the same as `G`-homomorphisms between the
coordinate groups, in the opposite direction.

* A word map `V_H(S) → V_H(T)` induces the `G`-homomorphism `CoordGroup.map w hw` from the
  coordinate group of `T` to that of `S`, substituting `w` for the variables.
* Conversely, a `G`-homomorphism `φ` from the coordinate group of `T` to that of `S` induces the
  map `CoordGroup.pointMap φ : V_H(S) → V_H(T)`: a solution of `S`, viewed as a `G`-homomorphism
  out of the coordinate group of `S`, is precomposed with `φ`.

The point map of `CoordGroup.map w hw` is the word map of `w`, and every `G`-homomorphism of
coordinate groups is of this form. Moreover `pointMap` is injective, its range consists exactly of
the word maps, and it reverses composition. Hence algebraic sets over `H` with word maps are
anti-equivalent to their coordinate groups with `G`-homomorphisms. No hypothesis on `ι` or on the
solution sets is needed, so the statements also cover empty algebraic sets, whose coordinate groups
are trivial.

A change of coordinates is a `G`-automorphism `σ` of `G[X]`. It acts on points by the invertible
word map `coordChange ι σ`, which carries `V_H(S)` onto `V_H(σ⁻¹(S))`, and it identifies the
radical of `σ⁻¹(S)` with the preimage of the radical of `S`, so the coordinate groups of `S` and
`σ⁻¹(S)` are isomorphic compatibly with the coefficients (`CoordGroup.congr`).

## Main definitions

* `TauCeti.GroupAlgGeom.CoordGroup.map`: the homomorphism of coordinate groups induced by a word
  map.
* `TauCeti.GroupAlgGeom.CoordGroup.pointMap`: the map of algebraic sets induced by a
  `G`-homomorphism of coordinate groups.
* `TauCeti.GroupAlgGeom.CoordGroup.gHomEquivWordMap`: `G`-homomorphisms of coordinate groups
  correspond to word maps of algebraic sets.
* `TauCeti.GroupAlgGeom.coordChange`: the action of a change of coordinates on points.
* `TauCeti.GroupAlgGeom.CoordGroup.congr`: the isomorphism of coordinate groups induced by a
  change of coordinates.

## Main results

* `TauCeti.GroupAlgGeom.mapsTo_wordMap_V_iff`: a word map sends `V_H(S)` into `V_H(T)` exactly
  when substituting it into `T` lands in the radical of `S`.
* `TauCeti.GroupAlgGeom.CoordGroup.eq_of_forall_evalGHom_eq`: elements of a coordinate group are
  separated by evaluation at the solutions.
* `TauCeti.GroupAlgGeom.CoordGroup.pointMap_injective`,
  `TauCeti.GroupAlgGeom.CoordGroup.range_pointMap`, `TauCeti.GroupAlgGeom.CoordGroup.pointMap_comp`:
  the anti-equivalence of algebraic sets and coordinate groups.
* `TauCeti.GroupAlgGeom.image_coordChange_V`, `TauCeti.GroupAlgGeom.Rad_preimage`: a change of
  coordinates `σ` maps `V_H(S)` onto `V_H(σ⁻¹(S))` and pulls the radical of `S` back to that of
  `σ⁻¹(S)`.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.5 (Theorem 4 and Corollary 9).
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.4.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod Subgroup

variable {G H X Y Z : Type*} [Group G] [Group H] {ι : G →* H}
  {S : Set (GX G X)} {T : Set (GX G Y)} {U : Set (GX G Z)}

/-! ### Word maps between algebraic sets -/

/-- A tuple of words maps `V_H(S)` into `V_H(T)` exactly when substituting it into the equations
of `T` gives equations in the radical of `S`. -/
theorem mapsTo_wordMap_V_iff {w : Y → GX G X} :
    Set.MapsTo (wordMap ι w) (V ι S) (V ι T) ↔
      eval (inl : G →* GX G X) w '' T ⊆ Rad ι S := by
  rw [Set.mapsTo_iff_subset_preimage, preimage_wordMap_V, Rad_def, subset_I_iff]

/-- Substituting a word map `V_H(S) → V_H(T)` into the radical of `T` lands in the radical
of `S`. -/
theorem Rad_le_comap_eval_of_mapsTo {w : Y → GX G X}
    (hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T)) :
    Rad ι T ≤ (Rad ι S).comap (eval (inl : G →* GX G X) w) := fun u hu =>
  mem_Rad.2 fun v hv => by
    rw [← MonoidHom.comp_apply, eval_comp_eval]
    exact mem_Rad.1 hu _ (hw hv)

namespace CoordGroup

/-- Elements of the coordinate group `G_{R(S)}` are separated by evaluation at the solutions of
`S` in `H`. -/
theorem eq_of_forall_evalGHom_eq {q q' : CoordGroup ι S}
    (h : ∀ v (hv : v ∈ V ι S), evalGHom v hv q = evalGHom v hv q') : q = q' := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective q'
  refine QuotientGroup.eq.2 (mem_Rad.2 fun v hv => ?_)
  have huv := h v hv
  simp only [evalGHom_mk] at huv
  simp [huv]

/-- The `G`-homomorphism `G_{R(T)} → G_{R(S)}` induced by a word map `V_H(S) → V_H(T)`: it sends
the class of an equation `u ∈ G[Y]` to the class of `u(w) ∈ G[X]`. -/
def map (w : Y → GX G X) (hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T)) :
    GHom (coeff ι T) (coeff ι S) where
  toMonoidHom := QuotientGroup.map _ _ (eval inl w) (Rad_le_comap_eval_of_mapsTo hw)
  map_coeff' g := by
    simp only [MonoidHom.toOneHom_coe, OneHom.toFun_eq_coe, coeff_apply]
    rw [QuotientGroup.map_mk, eval_inl]

/-- `map w hw` substitutes `w` for the variables. -/
@[simp]
theorem map_mk (w : Y → GX G X) (hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T)) (u : GX G Y) :
    map w hw (u : CoordGroup ι T) = (eval (inl : G →* GX G X) w u : CoordGroup ι S) :=
  QuotientGroup.map_mk _ _ _ (Rad_le_comap_eval_of_mapsTo hw) u

/-- The tuple of variables induces the identity of the coordinate group. -/
theorem map_id (hw : Set.MapsTo (wordMap ι fun x => (inr (FreeGroup.of x) : GX G X)) (V ι S)
    (V ι S)) : map _ hw = GHom.id (coeff ι S) :=
  gHom_ext fun x => by simp

/-- Composing the homomorphisms induced by word maps is induced by the substituted words. -/
theorem map_comp_map {w : Y → GX G X} {u : Z → GX G Y}
    (hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T)) (hu : Set.MapsTo (wordMap ι u) (V ι T) (V ι U))
    (hwu : Set.MapsTo (wordMap ι fun z => eval (inl : G →* GX G X) w (u z)) (V ι S) (V ι U)) :
    (map w hw).comp (map u hu) = map _ hwu :=
  gHom_ext fun z => by simp

/-- The map of algebraic sets `V_H(S) → V_H(T)` induced by a `G`-homomorphism
`φ : G_{R(T)} → G_{R(S)}`: a solution of `S`, viewed as a `G`-homomorphism `G_{R(S)} → H`, is
precomposed with `φ`. -/
def pointMap (φ : GHom (coeff ι T) (coeff ι S)) (v : V ι S) : V ι T :=
  homEquiv ι T (((homEquiv ι S).symm v).comp φ)

/-- The coordinates of `pointMap φ v` are the values at `v` of the images under `φ` of the
variables. -/
@[simp]
theorem pointMap_apply_coe (φ : GHom (coeff ι T) (coeff ι S)) (v : V ι S) (y : Y) :
    (pointMap φ v : Y → H) y =
      evalGHom (v : X → H) v.2 (φ ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T)) := by
  simp [pointMap]

/-- Evaluation at the point `pointMap φ v` is evaluation at `v` precomposed with `φ`. -/
@[simp]
theorem evalGHom_pointMap (φ : GHom (coeff ι T) (coeff ι S)) (v : V ι S) :
    evalGHom (pointMap φ v : Y → H) (pointMap φ v).2 = (evalGHom (v : X → H) v.2).comp φ := by
  rw [← homEquiv_symm_apply, pointMap, Equiv.symm_apply_apply, homEquiv_symm_apply]

/-- The map of algebraic sets induced by `map w hw` is the word map of `w`. -/
@[simp]
theorem pointMap_map (w : Y → GX G X) (hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T))
    (v : V ι S) : (pointMap (map w hw) v : Y → H) = wordMap ι w v := by
  funext y
  simp

/-- The identity of a coordinate group induces the identity of its algebraic set. -/
@[simp]
theorem pointMap_id : pointMap (GHom.id (coeff ι S)) = id := by
  funext v
  ext x
  simp

/-- Taking maps of algebraic sets reverses composition of homomorphisms of coordinate groups. -/
theorem pointMap_comp (ψ : GHom (coeff ι T) (coeff ι S)) (φ : GHom (coeff ι U) (coeff ι T)) :
    pointMap (ψ.comp φ) = pointMap φ ∘ pointMap ψ := by
  funext v
  ext z
  simp

/-- A `G`-homomorphism of coordinate groups is determined by the map of algebraic sets it
induces. -/
theorem pointMap_injective :
    Function.Injective (pointMap : GHom (coeff ι T) (coeff ι S) → V ι S → V ι T) := by
  intro φ ψ h
  refine GHom.ext fun q => eq_of_forall_evalGHom_eq fun v hv => ?_
  have hv' := congrArg (fun f : V ι S → V ι T => evalGHom (f ⟨v, hv⟩ : Y → H) (f ⟨v, hv⟩).2) h
  simp only [evalGHom_pointMap] at hv'
  simpa using DFunLike.congr_fun hv' q

/-- Every `G`-homomorphism of coordinate groups is induced by a word map. -/
theorem exists_map_eq (φ : GHom (coeff ι T) (coeff ι S)) :
    ∃ (w : Y → GX G X) (hw : Set.MapsTo (wordMap ι w) (V ι S) (V ι T)), map w hw = φ := by
  choose w hw using fun y : Y =>
    QuotientGroup.mk_surjective (φ ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T))
  have hpt (v : V ι S) : wordMap ι w v = pointMap φ v := by
    funext y
    simp [← hw y]
  have hmaps : Set.MapsTo (wordMap ι w) (V ι S) (V ι T) := fun v hv => by
    rw [hpt ⟨v, hv⟩]
    exact (pointMap φ ⟨v, hv⟩).2
  refine ⟨w, hmaps, gHom_ext fun y => ?_⟩
  rw [map_mk, ← hw y]
  simp

/-- The maps of algebraic sets induced by `G`-homomorphisms of coordinate groups are exactly the
word maps. -/
theorem range_pointMap :
    Set.range (pointMap : GHom (coeff ι T) (coeff ι S) → V ι S → V ι T) =
      {f | ∃ w : Y → GX G X, ∀ v : V ι S, (f v : Y → H) = wordMap ι w v} := by
  ext f
  constructor
  · rintro ⟨φ, rfl⟩
    obtain ⟨w, hw, rfl⟩ := exists_map_eq φ
    exact ⟨w, pointMap_map w hw⟩
  · rintro ⟨w, hw⟩
    have hmaps : Set.MapsTo (wordMap ι w) (V ι S) (V ι T) := fun v hv => by
      rw [← hw ⟨v, hv⟩]
      exact (f ⟨v, hv⟩).2
    exact ⟨map w hmaps, funext fun v => Subtype.ext ((pointMap_map w hmaps v).trans (hw v).symm)⟩

/-- **Algebraic sets and coordinate groups are anti-equivalent.** `G`-homomorphisms
`G_{R(T)} → G_{R(S)}` correspond to the word maps `V_H(S) → V_H(T)`, by `pointMap`. -/
noncomputable def gHomEquivWordMap :
    GHom (coeff ι T) (coeff ι S) ≃
      {f : V ι S → V ι T // ∃ w : Y → GX G X, ∀ v : V ι S, (f v : Y → H) = wordMap ι w v} :=
  (Equiv.ofInjective _ pointMap_injective).trans (Set.equivOfEq range_pointMap)

/-- `gHomEquivWordMap` sends a `G`-homomorphism to its map of algebraic sets. -/
@[simp]
theorem gHomEquivWordMap_apply_coe (φ : GHom (coeff ι T) (coeff ι S)) :
    (gHomEquivWordMap φ : V ι S → V ι T) = pointMap φ := by
  rw [gHomEquivWordMap, Equiv.trans_apply, Set.equivOfEq_apply, Equiv.ofInjective_apply]

end CoordGroup

/-! ### Changes of coordinates -/

section ChangeOfCoordinates

variable (σ : GX G X ≃* GX G X) (hσ : ∀ g, σ (inl g) = inl g)

include hσ in
/-- A `G`-automorphism of `G[X]` is substitution of its values on the variables. -/
theorem eval_inl_mulEquiv :
    eval (inl : G →* GX G X) (fun x => σ (inr (FreeGroup.of x))) = σ :=
  eval_eq_of_comp_inl (f := (σ : GX G X →* GX G X)) (MonoidHom.ext hσ)

variable (ι) in
/-- The action on points of a change of coordinates `σ`, a `G`-automorphism of `G[X]`: the point
`v` goes to the point `x ↦ σ(x)(v)`, at which evaluation is evaluation at `v` precomposed
with `σ`. -/
def coordChange : (X → H) ≃ (X → H) where
  toFun := wordMap ι fun x => σ (inr (FreeGroup.of x))
  invFun := wordMap ι fun x => σ.symm (inr (FreeGroup.of x))
  left_inv v := by
    have hσ' (g : G) : σ.symm (inl g) = inl g := σ.symm_apply_eq.2 (hσ g).symm
    rw [wordMap_wordMap, eval_inl_mulEquiv σ hσ]
    funext x
    simp
  right_inv v := by
    have hσ' (g : G) : σ.symm (inl g) = inl g := σ.symm_apply_eq.2 (hσ g).symm
    rw [wordMap_wordMap, eval_inl_mulEquiv σ.symm hσ']
    funext x
    simp

/-- A change of coordinates acts on points by the word map of the images of the variables. -/
theorem coe_coordChange :
    ⇑(coordChange ι σ hσ) = wordMap ι fun x => σ (inr (FreeGroup.of x)) :=
  (rfl)

/-- The coordinate `x` of `coordChange ι σ hσ v` is the value of `σ(x)` at `v`. -/
@[simp]
theorem coordChange_apply (v : X → H) (x : X) :
    coordChange ι σ hσ v x = eval ι v (σ (inr (FreeGroup.of x))) := by
  simp [coe_coordChange]

/-- Evaluation at `coordChange ι σ hσ v` is evaluation at `v` precomposed with `σ`. -/
@[simp]
theorem eval_coordChange (v : X → H) (w : GX G X) :
    eval ι (coordChange ι σ hσ v) w = eval ι v (σ w) := by
  have h := DFunLike.congr_fun (eval_comp_eval (ι := ι) (fun x => σ (inr (FreeGroup.of x))) v) w
  rw [MonoidHom.comp_apply, eval_inl_mulEquiv σ hσ] at h
  simpa [coe_coordChange] using h.symm

/-- The inverse of the action of `σ` on points is the action of `σ⁻¹`. -/
theorem coordChange_symm :
    (coordChange ι σ hσ).symm =
      coordChange ι σ.symm fun g => σ.symm_apply_eq.2 (hσ g).symm :=
  (rfl)

/-- The points that a change of coordinates `σ` sends into `V_H(T)` form `V_H(σ(T))`. -/
theorem preimage_coordChange_V (T : Set (GX G X)) :
    coordChange ι σ hσ ⁻¹' V ι T = V ι (σ '' T) := by
  ext v
  simp

/-- A change of coordinates `σ` maps `V_H(S)` bijectively onto `V_H(σ⁻¹(S))`. -/
theorem image_coordChange_V (S : Set (GX G X)) :
    coordChange ι σ hσ '' V ι S = V ι (σ ⁻¹' S) := by
  rw [Equiv.image_eq_preimage_symm, coordChange_symm, preimage_coordChange_V]
  congr 1
  exact σ.toEquiv.image_symm_eq_preimage S

include hσ in
/-- The radical of `σ⁻¹(S)` is the preimage under the change of coordinates `σ` of the radical
of `S`. -/
theorem Rad_preimage (S : Set (GX G X)) : Rad ι (σ ⁻¹' S) = (Rad ι S).comap σ := by
  ext u
  rw [mem_comap, mem_Rad, mem_Rad, ← image_coordChange_V σ hσ, Set.forall_mem_image]
  simp

include hσ in
/-- The isomorphism of coordinate groups `G_{R(σ⁻¹(S))} ≃* G_{R(S)}` induced by a change of
coordinates `σ`; it is compatible with the coefficients by `CoordGroup.congr_coeff`. -/
def CoordGroup.congr (S : Set (GX G X)) : CoordGroup ι (σ ⁻¹' S) ≃* CoordGroup ι S :=
  QuotientGroup.congr _ _ σ <| by
    rw [Rad_preimage σ hσ]
    exact map_comap_eq_self_of_surjective σ.surjective _

/-- `CoordGroup.congr σ hσ S` is induced by `σ` on representatives. -/
@[simp]
theorem CoordGroup.congr_mk (S : Set (GX G X)) (u : GX G X) :
    CoordGroup.congr σ hσ S (u : CoordGroup ι (σ ⁻¹' S)) = (σ u : CoordGroup ι S) :=
  QuotientGroup.congr_mk _ _ _ _ u

/-- `CoordGroup.congr σ hσ S` is compatible with the coefficient maps. -/
theorem CoordGroup.congr_coeff (S : Set (GX G X)) (g : G) :
    CoordGroup.congr σ hσ S (CoordGroup.coeff ι (σ ⁻¹' S) g) = CoordGroup.coeff ι S g := by
  simp [hσ]

end ChangeOfCoordinates

end TauCeti.GroupAlgGeom
