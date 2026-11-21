/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism
public import TauCeti.GroupTheory.GroupAlgGeom.FreeVariables
public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.Separated

/-!
# Compatibility and lifts in terms of coordinate groups

Let `S ⊆ G[X]` and `T ⊆ G[X ⊔ Y]` be systems of equations over `G`, with solutions sought in a
group `H` receiving the coefficients through `ι : G →* H`. The system `S ∪ T` in the variables
`X ⊔ Y` is `jointSystem S T`, the union of `T` with `S` read in the variables `X ⊔ Y`. The
inclusion of the variables `X` induces a `G`-homomorphism of coordinate groups
`coordGroupMap ι S T : G_{R(S)} → G_{R(S ∪ T)}`.

* `T` is compatible with `S` if and only if every `G`-homomorphism `G_{R(S)} → H` extends along
  `coordGroupMap` to `G_{R(S ∪ T)}`; the map `coordGroupMap` is then injective
  ([IFT], Proposition 2).
* `T` admits an `S`-lift if and only if `coordGroupMap` has a left inverse `G`-homomorphism, a
  retraction of `G_{R(S ∪ T)}` onto `G_{R(S)}`; these retractions correspond, by their values on
  the variables `Y`, to the solutions of `T` at the generic point of `S` ([IFT], Lemma 40 and
  Proposition 3).
* Lifts compose: if `T(X, Y)` admits an `S`-lift `Y(X)` and `T'(X, Y, Z)` admits an
  `(S ∪ T)`-lift `Z(X, Y)`, then `(Y(X), Z(X, Y(X)))` is an `S`-lift of `T ∪ T'`, where
  `Z(X, Y(X))` is the image of `Z(X, Y)` under the left inverse of `coordGroupMap` determined by
  `Y(X)`.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.jointSystem S T`: the system `S ∪ T` in the variables `X ⊔ Y`.
* `TauCeti.GroupAlgGeom.Lift.coordGroupMap ι S T`: the canonical map `G_{R(S)} → G_{R(S ∪ T)}`.
* `TauCeti.GroupAlgGeom.Lift.extensionEquiv T hK φ`: for a group `K` separated by `H` over `G` and
  a `G`-homomorphism `φ : G_{R(S)} → K`, the extensions of `φ` along `coordGroupMap` to
  `G_{R(S ∪ T)}` correspond, by their values on `Y`, to the solutions of `T` in `K` at the image
  under `φ` of the generic point of `S`.
* `TauCeti.GroupAlgGeom.Lift.retractionEquiv ι S T`: the left inverses of `coordGroupMap`
  correspond, by their values on `Y`, to the solutions of `T` at the generic point of `S`
  ([IFT], Lemma 40).

## Main results

* `TauCeti.GroupAlgGeom.Lift.isCompatible_iff_forall_exists_gHom`: compatibility as extension of
  homomorphisms.
* `TauCeti.GroupAlgGeom.Lift.IsCompatible.coordGroupMap_injective`: for a compatible system the
  canonical map of coordinate groups is injective. Together with the previous result this is
  [IFT], Proposition 2, which characterises compatibility by the embedding and the extension of
  homomorphisms.
* `TauCeti.GroupAlgGeom.Lift.hasLift_iff_exists_gHom`: lifts as left inverses of `coordGroupMap`
  ([IFT], Proposition 3).
* `TauCeti.GroupAlgGeom.Lift.sumElim_mem_V_image_jointSystem`,
  `TauCeti.GroupAlgGeom.Lift.HasLift.trans`: composition of lifts.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §6, Lemmas 36–40 and Propositions 2–3.
* [LIFT] O. Kharlampovich, A. Myasnikov, *Algebraic geometry over free groups: lifting solutions
  into generic points*, Contemp. Math. 378 (2005), §2, Propositions 2.5 and 2.8.
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

open Monoid.Coprod

variable {G H X Y : Type*} [Group G] [Group H]

section Defs

variable (ι : G →* H) (S : Set (GX G X)) (T : Set (GX G (X ⊕ Y)))

/-- The system `S(X) = 1 ∧ T(X, Y) = 1` in the variables `X ⊔ Y`: the equations of `S`, read in
`G[X ⊔ Y]`, together with those of `T`. -/
def jointSystem : Set (GX G (X ⊕ Y)) :=
  addFreeVars Y S ∪ T

theorem jointSystem_def : jointSystem S T = addFreeVars Y S ∪ T := (rfl)

variable {S T} in
@[simp]
theorem mem_jointSystem {w : GX G (X ⊕ Y)} :
    w ∈ jointSystem S T ↔ w ∈ addFreeVars Y S ∨ w ∈ T := Iff.rfl

@[simp]
theorem jointSystem_empty_left : jointSystem (∅ : Set (GX G X)) T = T := by
  simp [jointSystem_def, addFreeVars_def]

@[simp]
theorem jointSystem_empty_right : jointSystem S (∅ : Set (GX G (X ⊕ Y))) = addFreeVars Y S :=
  Set.union_empty _

variable {ι} in
/-- The solutions of `S ∪ T` are the solutions of `T` whose `X`-coordinates solve `S`. -/
@[simp]
theorem V_jointSystem : V ι (jointSystem S T) = (· ∘ Sum.inl) ⁻¹' V ι S ∩ V ι T := by
  rw [jointSystem_def, V_union, V_addFreeVars]

variable {ι S T} in
/-- A point solves `S ∪ T` exactly when it solves `T` and its `X`-coordinates solve `S`. -/
theorem mem_V_jointSystem {v : X ⊕ Y → H} : v ∈ V ι (jointSystem S T) ↔
    v ∘ Sum.inl ∈ V ι S ∧ v ∈ V ι T := by
  rw [V_jointSystem, Set.mem_inter_iff, Set.mem_preimage]

/-- The canonical `G`-homomorphism `G_{R(S)} → G_{R(S ∪ T)}` of coordinate groups induced by the
inclusion of the variables `X` into `X ⊔ Y`: the embedding of `G_{R(S)}` into the coordinate group
of `S` with the free variables `Y`, followed by the quotient map onto `G_{R(S ∪ T)}`. -/
def coordGroupMap : GHom (CoordGroup.coeff ι S) (CoordGroup.coeff ι (jointSystem S T)) :=
  (CoordGroup.homOfVSubset <| by
    rw [jointSystem_def]
    exact V_antitone ι Set.subset_union_left).comp (CoordGroup.inclFreeVarsHom ι Y S)

end Defs

variable {ι : G →* H} {S : Set (GX G X)} {T : Set (GX G (X ⊕ Y))}

/-- The canonical map of coordinate groups sends the class of a word `w(X)` to the class of the
same word, read in the variables `X ⊔ Y`. -/
@[simp]
theorem coordGroupMap_mk (w : GX G X) : coordGroupMap ι S T (w : CoordGroup ι S) =
    ((inclFreeVars G X Y w : GX G (X ⊕ Y)) : CoordGroup ι (jointSystem S T)) := by
  simp [coordGroupMap]

/-- The canonical map of coordinate groups sends the generic point of `S` to the `X`-coordinates
of the generic point of `S ∪ T`. -/
@[simp]
theorem coordGroupMap_genericPoint (x : X) : coordGroupMap ι S T (CoordGroup.genericPoint ι S x) =
    CoordGroup.genericPoint ι (jointSystem S T) (Sum.inl x) := by
  simp [CoordGroup.genericPoint_apply]

@[simp]
theorem coordGroupMap_comp_genericPoint :
    coordGroupMap ι S T ∘ CoordGroup.genericPoint ι S =
      CoordGroup.genericPoint ι (jointSystem S T) ∘ Sum.inl :=
  funext coordGroupMap_genericPoint

/-- Evaluation at a solution `v` of `S ∪ T` restricts along `coordGroupMap` to evaluation at the
`X`-coordinates of `v`. -/
@[simp]
theorem evalGHom_coordGroupMap {v : X ⊕ Y → H} (hv : v ∈ V ι (jointSystem S T))
    (q : CoordGroup ι S) :
    CoordGroup.evalGHom v hv (coordGroupMap ι S T q) =
      CoordGroup.evalGHom (v ∘ Sum.inl) (mem_V_jointSystem.1 hv).1 q := by
  induction q using QuotientGroup.induction_on
  simp

@[simp]
theorem evalGHom_comp_coordGroupMap {v : X ⊕ Y → H} (hv : v ∈ V ι (jointSystem S T)) :
    (CoordGroup.evalGHom v hv).comp (coordGroupMap ι S T) =
      CoordGroup.evalGHom (v ∘ Sum.inl) (mem_V_jointSystem.1 hv).1 :=
  GHom.ext fun _ => by simp

/-- Evaluation at a solution `p` of `S ∪ T` in a group separated by `H` restricts along
`coordGroupMap` to evaluation at the `X`-coordinates of `p`. -/
@[simp]
theorem evalGHomOfIsSeparatedBy_coordGroupMap {K : Type*} [Group K] {κ : G →* K}
    (hK : IsSeparatedBy κ ι) {p : X ⊕ Y → K} (hp : p ∈ V κ (jointSystem S T))
    (q : CoordGroup ι S) :
    CoordGroup.evalGHomOfIsSeparatedBy hK p hp (coordGroupMap ι S T q) =
      CoordGroup.evalGHomOfIsSeparatedBy hK (p ∘ Sum.inl) (mem_V_jointSystem.1 hp).1 q := by
  induction q using QuotientGroup.induction_on
  simp

@[simp]
theorem evalGHomOfIsSeparatedBy_comp_coordGroupMap {K : Type*} [Group K] {κ : G →* K}
    (hK : IsSeparatedBy κ ι) {p : X ⊕ Y → K} (hp : p ∈ V κ (jointSystem S T)) :
    (CoordGroup.evalGHomOfIsSeparatedBy hK p hp).comp (coordGroupMap ι S T) =
      CoordGroup.evalGHomOfIsSeparatedBy hK (p ∘ Sum.inl) (mem_V_jointSystem.1 hp).1 :=
  GHom.ext fun _ => by simp

/-- Restricting a `G`-homomorphism `G_{R(S ∪ T)} → K` into a group separated by `H` along
`coordGroupMap` restricts the corresponding solution of `S ∪ T` in `K` to its `X`-coordinates. -/
@[simp]
theorem homEquivOfIsSeparatedBy_comp_coordGroupMap {K : Type*} [Group K] {κ : G →* K}
    (hK : IsSeparatedBy κ ι) (φ : GHom (CoordGroup.coeff ι (jointSystem S T)) κ) :
    (CoordGroup.homEquivOfIsSeparatedBy hK S (φ.comp (coordGroupMap ι S T)) : X → K) =
      (CoordGroup.homEquivOfIsSeparatedBy hK (jointSystem S T) φ : X ⊕ Y → K) ∘ Sum.inl := by
  funext x
  simp

/-- Restricting a `G`-homomorphism `G_{R(S ∪ T)} → H` along `coordGroupMap` restricts the
corresponding solution of `S ∪ T` to its `X`-coordinates. -/
@[simp]
theorem homEquiv_comp_coordGroupMap (φ : GHom (CoordGroup.coeff ι (jointSystem S T)) ι) :
    (CoordGroup.homEquiv ι S (φ.comp (coordGroupMap ι S T)) : X → H) =
      (CoordGroup.homEquiv ι (jointSystem S T) φ : X ⊕ Y → H) ∘ Sum.inl := by
  simpa only [CoordGroup.homEquivOfIsSeparatedBy_self] using
    homEquivOfIsSeparatedBy_comp_coordGroupMap (IsDiscriminatedBy.self ι).isSeparatedBy φ

/-! ### Extensions along the canonical map -/

/-- A `G`-homomorphism `ρ` out of the coordinate group of `S ∪ T` restricts along `coordGroupMap`
to a `G`-homomorphism `φ` out of the coordinate group of `S` exactly when `ρ` and `φ` agree on the
`X`-coordinates of the generic points. -/
theorem comp_coordGroupMap_eq_iff {K : Type*} [Group K] {κ : G →* K}
    {ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) κ} {φ : GHom (CoordGroup.coeff ι S) κ} :
    ρ.comp (coordGroupMap ι S T) = φ ↔
      ∀ x, ρ (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inl x)) =
        φ (CoordGroup.genericPoint ι S x) :=
  ⟨fun h x => by simpa using DFunLike.congr_fun h (CoordGroup.genericPoint ι S x),
    fun h => CoordGroup.gHom_ext fun x => by simpa [CoordGroup.genericPoint_apply] using h x⟩

/-- If a `G`-homomorphism `ρ` out of the coordinate group of `S ∪ T` restricts along
`coordGroupMap` to `φ`, then the image under `φ` of the generic point of `S`, together with the
values of `ρ` on the variables `Y`, is a solution of `T`. -/
theorem sumElim_comp_genericPoint_mem_V_of_comp_eq {K : Type*} [Group K] {κ : G →* K}
    {ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) κ} {φ : GHom (CoordGroup.coeff ι S) κ}
    (hρ : ρ.comp (coordGroupMap ι S T) = φ) : Sum.elim (φ ∘ CoordGroup.genericPoint ι S)
      (fun y => ρ (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inr y))) ∈ V κ T := by
  -- The point is the image under `ρ` of the generic point of `S ∪ T`.
  have h : Sum.elim (φ ∘ CoordGroup.genericPoint ι S)
      (fun y => ρ (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inr y))) =
        ρ ∘ CoordGroup.genericPoint ι (jointSystem S T) :=
    funext <| Sum.forall.2 ⟨fun x => (comp_coordGroupMap_eq_iff.1 hρ x).symm, fun _ => rfl⟩
  rw [h]
  exact (mem_V_jointSystem.1 (ρ.comp_mem_V (CoordGroup.genericPoint_mem_V _))).2

section Extension

variable (T) {K : Type*} [Group K] {κ : G →* K} (hK : IsSeparatedBy κ ι)
  (φ : GHom (CoordGroup.coeff ι S) κ)

/-- Let `K` be separated by `H` over `G` and `φ` a `G`-homomorphism from the coordinate group of
`S` to `K`. The extensions of `φ` along `coordGroupMap` to the coordinate group of `S ∪ T`
correspond, by their values on the variables `Y`, to the solutions of `T` in `K` at the image
under `φ` of the generic point of `S`. -/
def extensionEquiv :
    {ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) κ // ρ.comp (coordGroupMap ι S T) = φ} ≃
      {w : Y → K // Sum.elim (φ ∘ CoordGroup.genericPoint ι S) w ∈ V κ T} where
  toFun ρ := ⟨fun y => ρ.val (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inr y)),
    sumElim_comp_genericPoint_mem_V_of_comp_eq ρ.property⟩
  invFun w := ⟨CoordGroup.evalGHomOfIsSeparatedBy hK _
      (mem_V_jointSystem.2 ⟨φ.comp_mem_V (CoordGroup.genericPoint_mem_V S), w.property⟩),
    comp_coordGroupMap_eq_iff.2 fun x => by simp⟩
  left_inv ρ := Subtype.ext <| CoordGroup.gHom_ext <| Sum.forall.2
    ⟨fun x => by simpa [CoordGroup.genericPoint_apply] using
      (comp_coordGroupMap_eq_iff.1 ρ.property x).symm,
      fun y => by simp [CoordGroup.genericPoint_apply]⟩
  right_inv w := Subtype.ext <| funext fun y => by simp

variable {T φ}

@[simp]
theorem extensionEquiv_apply_coe (ρ) (y : Y) :
    (extensionEquiv T hK φ ρ : Y → K) y =
      ρ.val (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inr y)) := (rfl)

@[simp]
theorem extensionEquiv_symm_apply_mk (w) (u : GX G (X ⊕ Y)) :
    ((extensionEquiv T hK φ).symm w).val (u : CoordGroup ι (jointSystem S T)) =
      eval κ (Sum.elim (φ ∘ CoordGroup.genericPoint ι S) w) u :=
  CoordGroup.evalGHomOfIsSeparatedBy_mk hK _ u

@[simp]
theorem extensionEquiv_symm_apply_genericPoint (w) (z : X ⊕ Y) :
    ((extensionEquiv T hK φ).symm w).val (CoordGroup.genericPoint ι (jointSystem S T) z) =
      Sum.elim (φ ∘ CoordGroup.genericPoint ι S) w z := by
  simp [CoordGroup.genericPoint_apply]

@[simp]
theorem extensionEquiv_symm_comp_coordGroupMap (w) :
    ((extensionEquiv T hK φ).symm w).val.comp (coordGroupMap ι S T) = φ :=
  ((extensionEquiv T hK φ).symm w).property

end Extension

/-! ### Compatibility -/

/-- A system `T` is compatible with `S` if and only if every `G`-homomorphism from the coordinate
group of `S` to `H` extends along `coordGroupMap` to the coordinate group of `S ∪ T`. -/
theorem isCompatible_iff_forall_exists_gHom : IsCompatible ι S T ↔
    ∀ α : GHom (CoordGroup.coeff ι S) ι, ∃ α' : GHom (CoordGroup.coeff ι (jointSystem S T)) ι,
      α'.comp (coordGroupMap ι S T) = α := by
  rw [isCompatible_iff]
  refine ⟨fun h α => ?_, fun h v hv => ?_⟩
  · -- Extend the solution `α ∘ μ` of `S` to a solution of `T`, then extend `α` along it.
    obtain ⟨w, hw⟩ := h _ (α.comp_mem_V (CoordGroup.genericPoint_mem_V S))
    exact ⟨_, ((extensionEquiv T (IsDiscriminatedBy.self ι).isSeparatedBy α).symm ⟨w, hw⟩).property⟩
  · -- An extension of evaluation at `v` gives a solution of `T` over `v`.
    obtain ⟨α', hα'⟩ := h (CoordGroup.evalGHom v hv)
    have hT := sumElim_comp_genericPoint_mem_V_of_comp_eq hα'
    rw [CoordGroup.evalGHom_comp_genericPoint] at hT
    exact ⟨_, hT⟩

/-- If `T` is compatible with `S`, the canonical map `coordGroupMap` from the coordinate group of
`S` to the coordinate group of `S ∪ T` is injective. -/
theorem IsCompatible.coordGroupMap_injective (h : IsCompatible ι S T) :
    Function.Injective (coordGroupMap ι S T) := by
  -- A nontrivial element of the kernel would survive some `α`, which extends along the map.
  refine (injective_iff_map_eq_one (coordGroupMap ι S T)).2 fun q hq => by_contra fun hq₁ => ?_
  obtain ⟨α, hα⟩ := (isSeparatedBy_def _ _).1 (CoordGroup.isSeparatedBy_coeff S) q hq₁
  obtain ⟨α', rfl⟩ := isCompatible_iff_forall_exists_gHom.1 h α
  exact hα (by simp [hq])

/-! ### Lifts as retractions -/

/-- A `G`-homomorphism `ρ` from the coordinate group of `S ∪ T` to the coordinate group of `S` is a
left inverse of `coordGroupMap` exactly when it sends the `X`-coordinates of the generic point of
`S ∪ T` to the generic point of `S`. -/
theorem comp_coordGroupMap_eq_id_iff
    {ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) (CoordGroup.coeff ι S)} :
    ρ.comp (coordGroupMap ι S T) = GHom.id _ ↔
      ∀ x, ρ (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inl x)) =
        CoordGroup.genericPoint ι S x := by
  simp [comp_coordGroupMap_eq_iff]

section Retraction

variable (ι S T)

/-- The left inverses of `coordGroupMap`, which retract the coordinate group of `S ∪ T` onto that
of `S`, correspond by their values on the variables `Y` to the solutions of `T` at the generic
point of `S`. -/
def retractionEquiv :
    {ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) (CoordGroup.coeff ι S) //
        ρ.comp (coordGroupMap ι S T) = GHom.id _} ≃
      {w : Y → CoordGroup ι S //
        Sum.elim (CoordGroup.genericPoint ι S) w ∈ V (CoordGroup.coeff ι S) T} :=
  (extensionEquiv T (CoordGroup.isSeparatedBy_coeff S) (GHom.id _)).trans
    (Equiv.subtypeEquivRight fun _ => by simp)

variable {ι S T}

@[simp]
theorem retractionEquiv_apply_coe (ρ) (y : Y) :
    (retractionEquiv ι S T ρ : Y → CoordGroup ι S) y =
      ρ.val (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inr y)) := (rfl)

@[simp]
theorem retractionEquiv_symm_apply_mk (w) (u : GX G (X ⊕ Y)) :
    ((retractionEquiv ι S T).symm w).val (u : CoordGroup ι (jointSystem S T)) =
      eval (CoordGroup.coeff ι S) (Sum.elim (CoordGroup.genericPoint ι S) w) u := by
  simp [retractionEquiv]

@[simp]
theorem retractionEquiv_symm_apply_genericPoint (w) (z : X ⊕ Y) :
    ((retractionEquiv ι S T).symm w).val (CoordGroup.genericPoint ι (jointSystem S T) z) =
      Sum.elim (CoordGroup.genericPoint ι S) w z := by
  simp [CoordGroup.genericPoint_apply]

@[simp]
theorem retractionEquiv_symm_comp_coordGroupMap (w) :
    ((retractionEquiv ι S T).symm w).val.comp (coordGroupMap ι S T) = GHom.id _ :=
  ((retractionEquiv ι S T).symm w).property

end Retraction

/-- A system `T` admits an `S`-lift if and only if the canonical map `coordGroupMap` from the
coordinate group of `S` to the coordinate group of `S ∪ T` has a left inverse `G`-homomorphism. -/
theorem hasLift_iff_exists_gHom : HasLift ι S T ↔
    ∃ ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) (CoordGroup.coeff ι S),
      ρ.comp (coordGroupMap ι S T) = GHom.id _ := by
  rw [hasLift_iff]
  exact ⟨fun ⟨w, hw⟩ => ⟨_, ((retractionEquiv ι S T).symm ⟨w, hw⟩).property⟩,
    fun ⟨ρ, hρ⟩ => ⟨_, (retractionEquiv ι S T ⟨ρ, hρ⟩).property⟩⟩

/-! ### Composition of lifts -/

section Composition

variable {Z : Type*} {T' : Set (GX G ((X ⊕ Y) ⊕ Z))}

/-- The composite of two lifts: let `w = Y(X)` be an `S`-lift of `T(X, Y)` and `z = Z(X, Y)` an
`(S ∪ T)`-lift of `T'(X, Y, Z)`, and let `ρ` be the left inverse of `coordGroupMap ι S T`, a
retraction of `G_{R(S ∪ T)}` onto `G_{R(S)}`, determined by `w` ([IFT], Lemma 40); it substitutes
`Y(X)` for `Y`. Then `(Y(X), Z(X, Y(X)))`, that is `Sum.elim w (ρ ∘ z)`, is an `S`-lift of
`T ∪ T'`. Here `T ∪ T'` is `jointSystem T T'` with its variables renamed from `(X ⊔ Y) ⊔ Z` to
`X ⊔ (Y ⊔ Z)` along `Equiv.sumAssoc`, so that `Y ⊔ Z` are the further variables of the lift. -/
theorem sumElim_mem_V_image_jointSystem {w : Y → CoordGroup ι S}
    (hw : Sum.elim (CoordGroup.genericPoint ι S) w ∈ V (CoordGroup.coeff ι S) T)
    {z : Z → CoordGroup ι (jointSystem S T)}
    (hz : Sum.elim (CoordGroup.genericPoint ι (jointSystem S T)) z ∈
      V (CoordGroup.coeff ι (jointSystem S T)) T') :
    Sum.elim (CoordGroup.genericPoint ι S)
        (Sum.elim w (((retractionEquiv ι S T).symm ⟨w, hw⟩).val ∘ z)) ∈
      V (CoordGroup.coeff ι S) (GX.renameEquiv G (Equiv.sumAssoc X Y Z) '' jointSystem T T') := by
  set ρ := ((retractionEquiv ι S T).symm ⟨w, hw⟩).val
  -- `ρ` carries the solution `z` of `T'` over the generic point of `S ∪ T` to one over `(μ, w)`.
  have hμ : ρ ∘ CoordGroup.genericPoint ι (jointSystem S T) =
      Sum.elim (CoordGroup.genericPoint ι S) w :=
    funext (retractionEquiv_symm_apply_genericPoint _)
  have hT' := ρ.comp_mem_V hz
  rw [Sum.comp_elim, hμ] at hT'
  -- The point is stated explicitly: inferring it from `hw` would be a higher-order unification
  -- problem (`?v ∘ Sum.inl = (μ, w)`).
  have hjoint : Sum.elim (Sum.elim (CoordGroup.genericPoint ι S) w) (ρ ∘ z) ∈
      V (CoordGroup.coeff ι S) (jointSystem T T') := mem_V_jointSystem.2 ⟨hw, hT'⟩
  -- Re-bracketing the point along `Equiv.sumAssoc` gives the point of `hjoint`.
  have hassoc : Sum.elim (CoordGroup.genericPoint ι S) (Sum.elim w (ρ ∘ z)) ∘
      Equiv.sumAssoc X Y Z = Sum.elim (Sum.elim (CoordGroup.genericPoint ι S) w) (ρ ∘ z) := by
    ext ((_ | _) | _) <;> simp
  simpa only [mem_V, Set.forall_mem_image, GX.eval_renameEquiv, hassoc] using hjoint

/-- Lifts compose: if `T(X, Y)` admits an `S`-lift and `T'(X, Y, Z)` admits an `(S ∪ T)`-lift,
then `T ∪ T'`, with its variables renamed as in `sumElim_mem_V_image_jointSystem`, admits an
`S`-lift. By [IFT], §6, Proposition 3 (`hasLift_iff_exists_gHom`), the first hypothesis holds
exactly when the canonical map `coordGroupMap ι S T : G_{R(S)} → G_{R(S ∪ T)}` has a left inverse
`G`-homomorphism, that is a retraction of `G_{R(S ∪ T)}` onto `G_{R(S)}` splitting it, so no
separate retraction hypothesis is needed. -/
theorem HasLift.trans (h : HasLift ι S T) (h' : HasLift ι (jointSystem S T) T') :
    HasLift ι S (GX.renameEquiv G (Equiv.sumAssoc X Y Z) '' jointSystem T T') := by
  obtain ⟨w, hw⟩ := hasLift_iff.1 h
  obtain ⟨z, hz⟩ := hasLift_iff.1 h'
  exact hasLift_iff.2 ⟨_, sumElim_mem_V_image_jointSystem hw hz⟩

end Composition

end TauCeti.GroupAlgGeom.Lift
