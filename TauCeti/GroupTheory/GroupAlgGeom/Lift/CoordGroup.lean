/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.FreeVariables
public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic
import TauCeti.GroupTheory.GroupAlgGeom.Separated

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
  retraction of `G_{R(S ∪ T)}` onto `G_{R(S)}`; the solutions of `T` at the generic point of `S`
  are the values of such retractions on the variables `Y` ([IFT], Lemma 40 and Proposition 3).

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.jointSystem S T`: the system `S ∪ T` in the variables `X ⊔ Y`.
* `TauCeti.GroupAlgGeom.Lift.coordGroupMap ι S T`: the canonical map `G_{R(S)} → G_{R(S ∪ T)}`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.existsUnique_gHom_genericPoint_inr_eq_of_isSeparatedBy`: for a group
  `K` separated by `H` over `G`, a `G`-homomorphism `G_{R(S)} → K` extends uniquely along
  `coordGroupMap` to `G_{R(S ∪ T)}` with prescribed values on `Y`, whenever these values solve `T`
  at the image of the generic point of `S`.
* `TauCeti.GroupAlgGeom.Lift.isCompatible_iff_forall_exists_gHom`: compatibility as extension of
  homomorphisms.
* `TauCeti.GroupAlgGeom.Lift.IsCompatible.coordGroupMap_injective`: for a compatible system the
  canonical map of coordinate groups is injective. Together with the previous result this is
  [IFT], Proposition 2, which characterises compatibility by the embedding and the extension of
  homomorphisms.
* `TauCeti.GroupAlgGeom.Lift.existsUnique_gHom_genericPoint_inr_eq`: a solution of `T` at the
  generic point of `S` is the value on `Y` of a unique left inverse of `coordGroupMap`
  ([IFT], Lemma 40).
* `TauCeti.GroupAlgGeom.Lift.genericPoint_inr_mem_V_of_comp_eq_id`: conversely, the values on `Y`
  of a left inverse of `coordGroupMap` solve `T` at the generic point of `S`.
* `TauCeti.GroupAlgGeom.Lift.hasLift_iff_exists_gHom`: lifts as left inverses of `coordGroupMap`
  ([IFT], Proposition 3).

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

variable {ι S T} in
/-- A point solves `S ∪ T` exactly when it solves `T` and its `X`-coordinates solve `S`. -/
theorem mem_V_jointSystem {v : X ⊕ Y → H} : v ∈ V ι (jointSystem S T) ↔
    v ∘ Sum.inl ∈ V ι S ∧ v ∈ V ι T := by
  simp [jointSystem_def]

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
theorem genericPoint_inr_mem_V_of_comp_eq {K : Type*} [Group K] {κ : G →* K}
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

/-- Let `K` be separated by `H` over `G`. If `φ` is a `G`-homomorphism from the coordinate group of
`S` to `K` and `w` is a solution of `T` in `K` at the image under `φ` of the generic point of `S`,
then there is a unique `G`-homomorphism from the coordinate group of `S ∪ T` to `K` that extends
`φ` along `coordGroupMap` and takes the values `w` on the variables `Y`. -/
theorem existsUnique_gHom_genericPoint_inr_eq_of_isSeparatedBy {K : Type*} [Group K]
    {κ : G →* K} (hK : IsSeparatedBy κ ι) {φ : GHom (CoordGroup.coeff ι S) κ} {w : Y → K}
    (hw : Sum.elim (φ ∘ CoordGroup.genericPoint ι S) w ∈ V κ T) :
    ∃! ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) κ, ρ.comp (coordGroupMap ι S T) = φ ∧
      ∀ y, ρ (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inr y)) = w y := by
  -- The point `(φ ∘ μ, w)` solves `S ∪ T` in `K`, so evaluation at it is defined on `G_{R(S ∪ T)}`.
  have hp : Sum.elim (φ ∘ CoordGroup.genericPoint ι S) w ∈ V κ (jointSystem S T) :=
    mem_V_jointSystem.2 ⟨φ.comp_mem_V (CoordGroup.genericPoint_mem_V S), hw⟩
  refine ⟨CoordGroup.evalGHomOfIsSeparatedBy hK _ hp,
    ⟨comp_coordGroupMap_eq_iff.2 fun x => by simp, fun y => by simp⟩,
    fun ρ ⟨hρ, hρw⟩ => CoordGroup.gHom_ext <| Sum.forall.2 ⟨fun x => ?_, fun y => ?_⟩⟩
  · simpa [CoordGroup.genericPoint_apply] using comp_coordGroupMap_eq_iff.1 hρ x
  · simpa [CoordGroup.genericPoint_apply] using hρw y

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
    exact (existsUnique_gHom_genericPoint_inr_eq_of_isSeparatedBy
      (IsDiscriminatedBy.self ι).isSeparatedBy hw).exists.imp fun _ => And.left
  · -- An extension of evaluation at `v` gives a solution of `T` over `v`.
    obtain ⟨α', hα'⟩ := h (CoordGroup.evalGHom v hv)
    have hT := genericPoint_inr_mem_V_of_comp_eq hα'
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

/-- A solution `w` of `T` at the generic point of `S` is the value on the variables `Y` of a
unique `G`-homomorphism from the coordinate group of `S ∪ T` to the coordinate group of `S` that is
a left inverse of `coordGroupMap`. -/
theorem existsUnique_gHom_genericPoint_inr_eq {w : Y → CoordGroup ι S}
    (hw : Sum.elim (CoordGroup.genericPoint ι S) w ∈ V (CoordGroup.coeff ι S) T) :
    ∃! ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) (CoordGroup.coeff ι S),
      ρ.comp (coordGroupMap ι S T) = GHom.id _ ∧
        ∀ y, ρ (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inr y)) = w y := by
  simpa using existsUnique_gHom_genericPoint_inr_eq_of_isSeparatedBy
    (CoordGroup.isSeparatedBy_coeff S) (φ := GHom.id _) (by simpa using hw)

/-- If a `G`-homomorphism `ρ` from the coordinate group of `S ∪ T` to the coordinate group of `S` is
a left inverse of `coordGroupMap`, its values on the variables `Y` form a solution of `T` at the
generic point of `S`. -/
theorem genericPoint_inr_mem_V_of_comp_eq_id
    {ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) (CoordGroup.coeff ι S)}
    (hρ : ρ.comp (coordGroupMap ι S T) = GHom.id _) : Sum.elim (CoordGroup.genericPoint ι S)
      (fun y => ρ (CoordGroup.genericPoint ι (jointSystem S T) (Sum.inr y))) ∈
        V (CoordGroup.coeff ι S) T := by
  simpa using genericPoint_inr_mem_V_of_comp_eq hρ

/-- A system `T` admits an `S`-lift if and only if the canonical map `coordGroupMap` from the
coordinate group of `S` to the coordinate group of `S ∪ T` has a left inverse `G`-homomorphism. -/
theorem hasLift_iff_exists_gHom : HasLift ι S T ↔
    ∃ ρ : GHom (CoordGroup.coeff ι (jointSystem S T)) (CoordGroup.coeff ι S),
      ρ.comp (coordGroupMap ι S T) = GHom.id _ := by
  rw [hasLift_iff]
  exact ⟨fun ⟨_, hw⟩ => (existsUnique_gHom_genericPoint_inr_eq hw).exists.imp fun _ => And.left,
    fun ⟨_, hρ⟩ => ⟨_, genericPoint_inr_mem_V_of_comp_eq_id hρ⟩⟩

end TauCeti.GroupAlgGeom.Lift
