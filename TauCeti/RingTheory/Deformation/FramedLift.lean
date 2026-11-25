/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Deformation.Lift

/-!
# Framed lifts and framed deformations

Let `ρbar : G →* GL n k` be a residual representation and `T` a type, in practice a finite set of
places of a number field. A *`T`-framed lift* of `ρbar` to an object `A` of the Artinian coefficient
category `C_Λ` is a pair `(ρ, α)` of a lift `ρ` of `ρbar` to `A` and a family of *frames*
`α t ∈ Γ̂ₙ(A)`, one for each `t ∈ T`, in the strict kernel of reduction `GL n A →* GL n k`. The
strict kernel acts on `T`-framed lifts by simultaneous conjugation and translation,
`β • (ρ, α) = (βρβ⁻¹, βα)`, and the orbits are the *`T`-framed deformations* of `ρbar`. Both are
functors `C_Λ ⥤ Type` under pushforward along morphisms of `C_Λ`.

The frames record a basis at each `t` reducing to the standard one. They are what makes the local
restrictions of a global framed deformation into well-defined lifts: if `ι : H →* G` is the
inclusion of a decomposition group at `t`, the matrix-valued representation `(α t)⁻¹ (ρ ∘ ι) (α t)`
is unchanged by the action above, whereas `ρ ∘ ι` itself changes by conjugation. No determinant,
local condition or ramification is imposed here: global deformation problems of a fixed type are
subfunctors of the functor of `T`-framed deformations.

The frame at a single index can always be normalised away. For `t₀ ∈ T`, every `T`-framed
deformation has a unique representative whose frame at `t₀` is the identity, so the `T`-framed
deformations are the `T ∖ {t₀}`-framed lifts (`TauCeti.Deformation.framedStrictClassFunctorIso`).
In particular, for a single frame the framed deformations are just the lifts
(`TauCeti.Deformation.FramedStrictClass.equivLiftOfUnique`). With no frames they are the strict
classes of lifts (`TauCeti.Deformation.FramedStrictClass.forgetFramingEquivOfIsEmpty`). Since a
frame is a point of the strict kernel, which is pro-represented by a power series ring in `n²`
variables, the normalisation is the functor-level source of the `n²(|T| - 1)` extra framing
variables of a ring framed at a nonempty `T` over the ring framed at a single index.

## Main definitions

* `TauCeti.Deformation.FramedLift ρbar T A`: the `T`-framed lifts of `ρbar` to `A`, with the action
  of the strict kernel `Γ̂ₙ(A)` by `β • (ρ, α) = (βρβ⁻¹, βα)`.
* `TauCeti.Deformation.FramedLift.map f`: pushforward of framed lifts along a morphism `f` of `C_Λ`.
* `TauCeti.Deformation.framedLiftFunctor Λ ρbar T`: the functor `C_Λ ⥤ Type` of `T`-framed lifts.
* `TauCeti.Deformation.FramedStrictClass ρbar T A`: the `T`-framed deformations, the orbits of the
  strict kernel on `T`-framed lifts.
* `TauCeti.Deformation.framedStrictClassFunctor Λ ρbar T`: the functor of `T`-framed deformations.
* `TauCeti.Deformation.FramedStrictClass.forgetFraming`: the map to strict classes forgetting the
  frames.
* `TauCeti.Deformation.comapFrame Λ ρbar e`: for `e : T' → T`, the natural transformation keeping
  only the frames indexed by the image of `e`.
* `TauCeti.Deformation.framedStrictClassFunctorIso Λ ρbar t₀`: the natural isomorphism from
  `T`-framed deformations to `T ∖ {t₀}`-framed lifts normalising the frame at `t₀`.

## Main results

* `TauCeti.Deformation.FramedStrictClass.mk_eq_mk_iff`: two framed lifts define the same framed
  deformation exactly when they are related by an element of the strict kernel.
* `TauCeti.Deformation.FramedStrictClass.forgetFraming_surjective`: every strict class carries a
  framing.
* `TauCeti.Deformation.FramedStrictClass.forgetFramingEquivOfIsEmpty`: with no frames, framed
  deformations are strict classes.
* `TauCeti.Deformation.FramedStrictClass.equivLiftOfUnique`: with one frame, framed deformations are
  lifts.
* `TauCeti.Deformation.FramedStrictClass.nonempty_residue_iff` and the `Subsingleton` instance:
  over the residue field there is exactly one framed deformation when `ρbar` is continuous for the
  discrete topology on `k`.

## References

* T. Gee, *Modularity lifting theorems*, Essent. Number Theory 1 (2022), §§3.20–3.21 and
  Exercise 3.9.
* M. Kisin, *Lectures on deformations of Galois representations*, Lecture 1, Remark (1.2.2),
  https://people.math.harvard.edu/~kisin/notes/notes.pdf.
* C. Khare and J.-P. Wintenberger, *Serre's modularity conjecture (II)*, Invent. Math. 178 (2009),
  §4.1.
-/

public section

open CategoryTheory Matrix

universe u v w x y

namespace TauCeti.Deformation

open ArtinLocalAlg

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]
  {n : Type x} [Fintype n] [DecidableEq n] {G : Type w} [Monoid G] [TopologicalSpace G]

/-- A *`T`-framed lift* of the residual representation `ρbar` to an object `A` of `C_Λ`: a lift of
`ρbar` to `A` together with a frame in the strict kernel `Γ̂ₙ(A)` for each index `t ∈ T`. -/
@[ext]
structure FramedLift (ρbar : G →* GL n k) (T : Type y) (A : ArtinLocalAlg Λ k) where
  /-- The underlying lift. -/
  toLift : Lift ρbar A
  /-- The frame at each index, a matrix reducing to the identity. -/
  frame : T → A.strictKernel n

namespace FramedLift

variable {ρbar : G →* GL n k} {T T' T'' : Type y} {A B C : ArtinLocalAlg Λ k}

section Conjugation

/-- The strict kernel acts on framed lifts by conjugating the lift and translating the frames:
`β • (ρ, α) = (βρβ⁻¹, βα)`. -/
instance : SMul (A.strictKernel n) (FramedLift ρbar T A) where
  smul b x := ⟨b • x.toLift, fun t ↦ b * x.frame t⟩

@[simp]
theorem toLift_smul (b : A.strictKernel n) (x : FramedLift ρbar T A) :
    (b • x).toLift = b • x.toLift :=
  (rfl)

@[simp]
theorem frame_smul (b : A.strictKernel n) (x : FramedLift ρbar T A) (t : T) :
    (b • x).frame t = b * x.frame t :=
  (rfl)

instance : MulAction (A.strictKernel n) (FramedLift ρbar T A) where
  one_smul _ := FramedLift.ext (one_smul _ _) (funext fun _ ↦ one_mul _)
  mul_smul _ _ _ := FramedLift.ext (mul_smul _ _ _) (funext fun _ ↦ mul_assoc _ _ _)

end Conjugation

section Map

/-- The pushforward of a framed lift along a morphism `f : A ⟶ B` of `C_Λ`: the lift and each
frame are pushed forward entrywise. -/
def map (f : A ⟶ B) (x : FramedLift ρbar T A) : FramedLift ρbar T B :=
  ⟨Lift.map f x.toLift, fun t ↦ strictKernelMap n f (x.frame t)⟩

@[simp]
theorem toLift_map (f : A ⟶ B) (x : FramedLift ρbar T A) :
    (map f x).toLift = Lift.map f x.toLift :=
  (rfl)

@[simp]
theorem frame_map (f : A ⟶ B) (x : FramedLift ρbar T A) (t : T) :
    (map f x).frame t = strictKernelMap n f (x.frame t) :=
  (rfl)

/-- Pushforward along the identity is the identity. -/
@[simp]
theorem map_id (x : FramedLift ρbar T A) : map (𝟙 A) x = x :=
  FramedLift.ext (Lift.map_id _) (funext fun _ ↦ strictKernelMap_id _)

/-- Pushforward along a composite is the composite of the pushforwards. -/
theorem map_comp (f : A ⟶ B) (f' : B ⟶ C) (x : FramedLift ρbar T A) :
    map (f ≫ f') x = map f' (map f x) :=
  FramedLift.ext (Lift.map_comp _ _ _) (funext fun _ ↦ strictKernelMap_comp _ _ _)

/-- Pushforward is equivariant along the induced map of strict kernels. -/
theorem map_smul (f : A ⟶ B) (b : A.strictKernel n) (x : FramedLift ρbar T A) :
    map f (b • x) = strictKernelMap n f b • map f x :=
  FramedLift.ext (Lift.map_smul f b x.toLift) (funext fun _ ↦ map_mul _ _ _)

end Map

section ComapFrame

/-- Reindexing the frames along `e : T' → T`: the framed lift keeps the frames at the indices
`e t'`. For an inclusion `T' ⊆ T` this forgets the frames outside `T'`. -/
def comapFrame (e : T' → T) (x : FramedLift ρbar T A) : FramedLift ρbar T' A :=
  ⟨x.toLift, x.frame ∘ e⟩

@[simp]
theorem toLift_comapFrame (e : T' → T) (x : FramedLift ρbar T A) :
    (x.comapFrame e).toLift = x.toLift :=
  (rfl)

@[simp]
theorem frame_comapFrame (e : T' → T) (x : FramedLift ρbar T A) (t : T') :
    (x.comapFrame e).frame t = x.frame (e t) :=
  (rfl)

@[simp]
theorem comapFrame_id (x : FramedLift ρbar T A) : x.comapFrame id = x :=
  (rfl)

theorem comapFrame_comp (e : T' → T) (e' : T'' → T') (x : FramedLift ρbar T A) :
    x.comapFrame (e ∘ e') = (x.comapFrame e).comapFrame e' :=
  (rfl)

theorem comapFrame_smul (e : T' → T) (b : A.strictKernel n) (x : FramedLift ρbar T A) :
    (b • x).comapFrame e = b • x.comapFrame e :=
  (rfl)

theorem comapFrame_map (e : T' → T) (f : A ⟶ B) (x : FramedLift ρbar T A) :
    (map f x).comapFrame e = map f (x.comapFrame e) :=
  (rfl)

end ComapFrame

section Normalize

variable (t₀ : T)

/-- The normalisation of a framed lift at `t₀`: translating by the inverse of its frame at `t₀`
makes that frame `1`; the normalisation records the lift and the remaining frames. -/
def normalize (x : FramedLift ρbar T A) : FramedLift ρbar {t // t ≠ t₀} A :=
  ((x.frame t₀)⁻¹ • x).comapFrame Subtype.val

@[simp]
theorem toLift_normalize (x : FramedLift ρbar T A) :
    (normalize t₀ x).toLift = (x.frame t₀)⁻¹ • x.toLift :=
  (rfl)

@[simp]
theorem frame_normalize (x : FramedLift ρbar T A) (t : {t // t ≠ t₀}) :
    (normalize t₀ x).frame t = (x.frame t₀)⁻¹ * x.frame t :=
  (rfl)

/-- The normalisation at `t₀` is invariant under the action of the strict kernel. -/
@[simp]
theorem normalize_smul (b : A.strictKernel n) (x : FramedLift ρbar T A) :
    normalize t₀ (b • x) = normalize t₀ x := by
  rw [normalize, normalize, frame_smul, ← mul_smul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem normalize_map (f : A ⟶ B) (x : FramedLift ρbar T A) :
    normalize t₀ (map f x) = map f (normalize t₀ x) := by
  rw [normalize, normalize, frame_map, ← map_inv, ← map_smul, comapFrame_map]

variable [DecidableEq T]

/-- The framed lift with frame `1` at `t₀` and the frames of `y` at the other indices. -/
def insertFrame (y : FramedLift ρbar {t // t ≠ t₀} A) : FramedLift ρbar T A :=
  ⟨y.toLift, fun t ↦ if h : t = t₀ then 1 else y.frame ⟨t, h⟩⟩

@[simp]
theorem toLift_insertFrame (y : FramedLift ρbar {t // t ≠ t₀} A) :
    (insertFrame t₀ y).toLift = y.toLift :=
  (rfl)

@[simp]
theorem frame_insertFrame_self (y : FramedLift ρbar {t // t ≠ t₀} A) :
    (insertFrame t₀ y).frame t₀ = 1 := by
  simp [insertFrame]

theorem frame_insertFrame_of_ne (y : FramedLift ρbar {t // t ≠ t₀} A) {t : T} (h : t ≠ t₀) :
    (insertFrame t₀ y).frame t = y.frame ⟨t, h⟩ := by
  simp [insertFrame, h]

@[simp]
theorem comapFrame_insertFrame (y : FramedLift ρbar {t // t ≠ t₀} A) :
    (insertFrame t₀ y).comapFrame Subtype.val = y :=
  FramedLift.ext rfl (funext fun t ↦ frame_insertFrame_of_ne t₀ y t.property)

/-- A framed lift whose frame at `t₀` is `1` is recovered from its other frames. -/
theorem insertFrame_comapFrame {x : FramedLift ρbar T A} (hx : x.frame t₀ = 1) :
    insertFrame t₀ (x.comapFrame Subtype.val) = x :=
  FramedLift.ext rfl <| funext fun t ↦ by
    by_cases h : t = t₀
    · subst h
      rw [frame_insertFrame_self, hx]
    · rw [frame_insertFrame_of_ne t₀ _ h, frame_comapFrame]

theorem insertFrame_map (f : A ⟶ B) (y : FramedLift ρbar {t // t ≠ t₀} A) :
    insertFrame t₀ (map f y) = map f (insertFrame t₀ y) :=
  FramedLift.ext rfl <| funext fun t ↦ by
    by_cases h : t = t₀
    · subst h
      simp
    · simp [frame_insertFrame_of_ne t₀ _ h]

theorem insertFrame_normalize (x : FramedLift ρbar T A) :
    insertFrame t₀ (normalize t₀ x) = (x.frame t₀)⁻¹ • x :=
  insertFrame_comapFrame t₀ (inv_mul_cancel _)

@[simp]
theorem normalize_insertFrame (y : FramedLift ρbar {t // t ≠ t₀} A) :
    normalize t₀ (insertFrame t₀ y) = y := by
  rw [normalize, frame_insertFrame_self, inv_one, one_smul, comapFrame_insertFrame]

end Normalize

section Residue

/-- Over the residue field there is at most one framed lift: the lift is the residual
representation and every frame is `1`. -/
instance : Subsingleton (FramedLift ρbar T (residue Λ k)) where
  allEq _ _ := FramedLift.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The residual representation has a framed lift to `k` exactly when it is continuous for the
discrete topology on `k`. -/
theorem nonempty_residue_iff :
    Nonempty (FramedLift ρbar T (residue Λ k)) ↔ IsLocallyConstant ρbar :=
  ⟨fun ⟨x⟩ ↦ x.toLift.isLocallyConstant_residual,
   fun h ↦ (Lift.nonempty_residue_iff.mpr h).map fun ρ ↦ ⟨ρ, fun _ ↦ 1⟩⟩

end Residue

/-- With no frames, a framed lift is just a lift. -/
def equivLiftOfIsEmpty [IsEmpty T] : FramedLift ρbar T A ≃ Lift ρbar A where
  toFun := toLift
  invFun ρ := ⟨ρ, isEmptyElim⟩
  left_inv _ := FramedLift.ext rfl (funext isEmptyElim)
  right_inv _ := rfl

@[simp]
theorem equivLiftOfIsEmpty_apply [IsEmpty T] (x : FramedLift ρbar T A) :
    equivLiftOfIsEmpty x = x.toLift :=
  (rfl)

@[simp]
theorem toLift_equivLiftOfIsEmpty_symm [IsEmpty T] (ρ : Lift ρbar A) :
    (equivLiftOfIsEmpty.symm ρ : FramedLift ρbar T A).toLift = ρ :=
  (rfl)

end FramedLift

variable (ρbar : G →* GL n k)

variable (Λ) in
/-- The functor `C_Λ ⥤ Type` of `T`-framed lifts of `ρbar`, with pushforward of framed lifts. -/
-- Exposed so that `(framedLiftFunctor Λ ρbar T).obj A` unfolds to `FramedLift ρbar T A` in
-- statements.
@[expose] def framedLiftFunctor (T : Type y) : ArtinLocalAlg Λ k ⥤ Type (max w v x y) where
  obj A := FramedLift ρbar T A
  map f := TypeCat.ofHom (FramedLift.map f)
  map_id A := by
    ext x : 3
    exact FramedLift.map_id x
  map_comp f f' := by
    ext x : 3
    exact FramedLift.map_comp f f' x

variable (Λ) in
@[simp]
theorem framedLiftFunctor_obj (T : Type y) (A : ArtinLocalAlg Λ k) :
    (framedLiftFunctor Λ ρbar T).obj A = FramedLift ρbar T A :=
  (rfl)

variable (Λ) in
@[simp]
theorem framedLiftFunctor_map_apply (T : Type y) {A B : ArtinLocalAlg Λ k} (f : A ⟶ B)
    (x : FramedLift ρbar T A) : (framedLiftFunctor Λ ρbar T).map f x = FramedLift.map f x :=
  (rfl)

/-- The *`T`-framed deformations* of `ρbar` over `A`: `T`-framed lifts up to the action
`β • (ρ, α) = (βρβ⁻¹, βα)` of the strict kernel `Γ̂ₙ(A)`. -/
-- Exposed as a quotient type: code generation needs its representation in other modules.
@[expose] def FramedStrictClass (T : Type y) (A : ArtinLocalAlg Λ k) : Type (max w v x y) :=
  MulAction.orbitRel.Quotient (A.strictKernel n) (FramedLift ρbar T A)

namespace FramedStrictClass

variable {ρbar} {T T' T'' : Type y} {A B C : ArtinLocalAlg Λ k}

/-- The framed deformation of a framed lift. -/
def mk (x : FramedLift ρbar T A) : FramedStrictClass ρbar T A :=
  Quotient.mk'' x

/-- Every framed deformation is the class of a framed lift. -/
theorem mk_surjective :
    Function.Surjective (mk : FramedLift ρbar T A → FramedStrictClass ρbar T A) :=
  Quotient.mk''_surjective

/-- Two framed lifts define the same framed deformation exactly when they are related by an element
of the strict kernel. -/
theorem mk_eq_mk_iff {x y : FramedLift ρbar T A} :
    mk x = mk y ↔ ∃ b : A.strictKernel n, b • x = y := by
  refine Quotient.eq''.trans ?_
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm, MulAction.mem_orbit_iff]

@[simp]
theorem mk_smul (b : A.strictKernel n) (x : FramedLift ρbar T A) : mk (b • x) = mk x :=
  (mk_eq_mk_iff.mpr ⟨b, rfl⟩).symm

/-- A function on framed lifts that is invariant under the strict kernel descends to framed
deformations. -/
def lift {β : Sort*} (f : FramedLift ρbar T A → β)
    (hf : ∀ (b : A.strictKernel n) x, f (b • x) = f x) : FramedStrictClass ρbar T A → β :=
  Quotient.lift f fun x y h ↦ by
    obtain ⟨b, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    exact hf b y

@[simp]
theorem lift_mk {β : Sort*} (f : FramedLift ρbar T A → β)
    (hf : ∀ (b : A.strictKernel n) x, f (b • x) = f x) (x : FramedLift ρbar T A) :
    lift f hf (mk x) = f x :=
  (rfl)

/-- The descent of an invariant function to framed deformations is unique. -/
theorem lift_unique {β : Sort*} (f : FramedLift ρbar T A → β)
    (hf : ∀ (b : A.strictKernel n) x, f (b • x) = f x) (g : FramedStrictClass ρbar T A → β)
    (hg : ∀ x, g (mk x) = f x) : g = lift f hf :=
  funext fun c ↦ by
    obtain ⟨x, rfl⟩ := mk_surjective c
    exact hg x

/-- The pushforward of framed deformations along a morphism `f : A ⟶ B` of `C_Λ`. -/
def map (f : A ⟶ B) : FramedStrictClass ρbar T A → FramedStrictClass ρbar T B :=
  lift (fun x ↦ mk (FramedLift.map f x)) fun b x ↦ by rw [FramedLift.map_smul, mk_smul]

@[simp]
theorem map_mk (f : A ⟶ B) (x : FramedLift ρbar T A) : map f (mk x) = mk (FramedLift.map f x) :=
  (rfl)

/-- Pushforward of framed deformations along the identity is the identity. -/
@[simp]
theorem map_id (c : FramedStrictClass ρbar T A) : map (𝟙 A) c = c := by
  obtain ⟨x, rfl⟩ := mk_surjective c
  simp

/-- Pushforward of framed deformations along a composite is the composite of the pushforwards. -/
theorem map_comp (f : A ⟶ B) (f' : B ⟶ C) (c : FramedStrictClass ρbar T A) :
    map (f ≫ f') c = map f' (map f c) := by
  obtain ⟨x, rfl⟩ := mk_surjective c
  simp [FramedLift.map_comp]

section ForgetFraming

/-- The strict class of the underlying lift of a framed deformation. -/
def forgetFraming : FramedStrictClass ρbar T A → StrictClass ρbar A :=
  lift (fun x ↦ StrictClass.mk x.toLift) fun b _ ↦
    (StrictClass.mk_eq_mk_iff.mpr ⟨b, rfl⟩).symm

@[simp]
theorem forgetFraming_mk (x : FramedLift ρbar T A) :
    forgetFraming (mk x) = StrictClass.mk x.toLift :=
  (rfl)

/-- Forgetting the frames commutes with pushforward. -/
theorem forgetFraming_map (f : A ⟶ B) (c : FramedStrictClass ρbar T A) :
    forgetFraming (map f c) = StrictClass.map f (forgetFraming c) := by
  obtain ⟨x, rfl⟩ := mk_surjective c
  rw [map_mk, forgetFraming_mk, forgetFraming_mk, StrictClass.map_mk, FramedLift.toLift_map]

/-- Every strict class is the underlying class of a framed deformation, for instance with every
frame `1`. -/
theorem forgetFraming_surjective :
    Function.Surjective (forgetFraming : FramedStrictClass ρbar T A → StrictClass ρbar A) := by
  intro c
  obtain ⟨ρ, rfl⟩ := StrictClass.mk_surjective c
  exact ⟨mk ⟨ρ, fun _ ↦ 1⟩, rfl⟩

/-- With no frames, framed deformations are strict classes of lifts: the inverse sends the class
of a lift `ρ` to the class of `ρ` with the empty framing. -/
def forgetFramingEquivOfIsEmpty [IsEmpty T] :
    FramedStrictClass ρbar T A ≃ StrictClass ρbar A where
  toFun := forgetFraming
  invFun := StrictClass.lift (fun ρ ↦ mk ⟨ρ, isEmptyElim⟩) fun b ρ ↦
    .trans (congrArg mk (FramedLift.ext rfl (funext isEmptyElim) :
      (⟨b • ρ, isEmptyElim⟩ : FramedLift ρbar T A) = b • ⟨ρ, isEmptyElim⟩)) (mk_smul b _)
  left_inv c := by
    obtain ⟨x, rfl⟩ := mk_surjective c
    rw [forgetFraming_mk, StrictClass.lift_mk]
    exact congrArg mk (FramedLift.ext rfl (funext isEmptyElim))
  right_inv c := by
    obtain ⟨ρ, rfl⟩ := StrictClass.mk_surjective c
    rw [StrictClass.lift_mk, forgetFraming_mk]

@[simp]
theorem forgetFramingEquivOfIsEmpty_apply [IsEmpty T] (c : FramedStrictClass ρbar T A) :
    forgetFramingEquivOfIsEmpty c = forgetFraming c :=
  (rfl)

@[simp]
theorem forgetFramingEquivOfIsEmpty_symm_mk [IsEmpty T] (ρ : Lift ρbar A) :
    (forgetFramingEquivOfIsEmpty.symm (StrictClass.mk ρ) : FramedStrictClass ρbar T A) =
      mk ⟨ρ, isEmptyElim⟩ :=
  StrictClass.lift_mk _ _ ρ

end ForgetFraming

section ComapFrame

/-- Reindexing the frames of framed deformations along `e : T' → T`. -/
def comapFrame (e : T' → T) : FramedStrictClass ρbar T A → FramedStrictClass ρbar T' A :=
  lift (fun x ↦ mk (x.comapFrame e)) fun b x ↦ by rw [FramedLift.comapFrame_smul, mk_smul]

@[simp]
theorem comapFrame_mk (e : T' → T) (x : FramedLift ρbar T A) :
    comapFrame e (mk x) = mk (x.comapFrame e) :=
  (rfl)

@[simp]
theorem comapFrame_id (c : FramedStrictClass ρbar T A) : comapFrame id c = c := by
  obtain ⟨x, rfl⟩ := mk_surjective c
  rfl

theorem comapFrame_comp (e : T' → T) (e' : T'' → T') (c : FramedStrictClass ρbar T A) :
    comapFrame (e ∘ e') c = comapFrame e' (comapFrame e c) := by
  obtain ⟨x, rfl⟩ := mk_surjective c
  rfl

theorem comapFrame_map (e : T' → T) (f : A ⟶ B) (c : FramedStrictClass ρbar T A) :
    comapFrame e (map f c) = map f (comapFrame e c) := by
  obtain ⟨x, rfl⟩ := mk_surjective c
  rfl

/-- Reindexing the frames does not change the underlying strict class. -/
@[simp]
theorem forgetFraming_comapFrame (e : T' → T) (c : FramedStrictClass ρbar T A) :
    forgetFraming (comapFrame e c) = forgetFraming c := by
  obtain ⟨x, rfl⟩ := mk_surjective c
  rfl

end ComapFrame

section Normalize

variable [DecidableEq T] (t₀ : T)

/-- Normalising the frame at `t₀`: a `T`-framed deformation is the same as a
`T ∖ {t₀}`-framed lift. The inverse sends a framed lift to the class obtained by inserting the
frame `1` at `t₀`. -/
def normalizeEquiv : FramedStrictClass ρbar T A ≃ FramedLift ρbar {t // t ≠ t₀} A where
  toFun := lift (FramedLift.normalize t₀) fun b x ↦ FramedLift.normalize_smul t₀ b x
  invFun y := mk (FramedLift.insertFrame t₀ y)
  left_inv c := by
    obtain ⟨x, rfl⟩ := mk_surjective c
    dsimp only
    rw [lift_mk, FramedLift.insertFrame_normalize, mk_smul]
  right_inv y := FramedLift.normalize_insertFrame t₀ y

@[simp]
theorem normalizeEquiv_mk (x : FramedLift ρbar T A) :
    normalizeEquiv t₀ (mk x) = FramedLift.normalize t₀ x :=
  (rfl)

@[simp]
theorem normalizeEquiv_symm_apply (y : FramedLift ρbar {t // t ≠ t₀} A) :
    (normalizeEquiv t₀).symm y = mk (FramedLift.insertFrame t₀ y) :=
  (rfl)

theorem normalizeEquiv_map (f : A ⟶ B) (c : FramedStrictClass ρbar T A) :
    normalizeEquiv t₀ (map f c) = FramedLift.map f (normalizeEquiv t₀ c) := by
  obtain ⟨x, rfl⟩ := mk_surjective c
  exact FramedLift.normalize_map t₀ f x

/-- With a single frame, framed deformations are lifts: normalising the frame to `1` picks out
the unique representative `(α⁻¹ρα, 1)` of the class of `(ρ, α)`. -/
def equivLiftOfUnique [Unique T] : FramedStrictClass ρbar T A ≃ Lift ρbar A :=
  have : IsEmpty {t : T // t ≠ default} := ⟨fun t ↦ t.property (Unique.eq_default t.val)⟩
  (normalizeEquiv default).trans FramedLift.equivLiftOfIsEmpty

@[simp]
theorem equivLiftOfUnique_mk [Unique T] (x : FramedLift ρbar T A) :
    equivLiftOfUnique (mk x) = (x.frame default)⁻¹ • x.toLift :=
  (rfl)

@[simp]
theorem equivLiftOfUnique_symm_apply [Unique T] (ρ : Lift ρbar A) :
    equivLiftOfUnique.symm ρ = mk (⟨ρ, fun _ ↦ 1⟩ : FramedLift ρbar T A) := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [equivLiftOfUnique_mk, inv_one, one_smul]

end Normalize

section Residue

/-- Over the residue field there is at most one framed deformation. -/
instance : Subsingleton (FramedStrictClass ρbar T (residue Λ k)) :=
  Quotient.instSubsingletonQuotient _

/-- There is a framed deformation over the residue field exactly when `ρbar` is continuous for the
discrete topology on `k`. -/
theorem nonempty_residue_iff :
    Nonempty (FramedStrictClass ρbar T (residue Λ k)) ↔ IsLocallyConstant ρbar :=
  ⟨fun ⟨c⟩ ↦ FramedLift.nonempty_residue_iff.mp (mk_surjective c).nonempty,
   fun h ↦ (FramedLift.nonempty_residue_iff.mpr h).map mk⟩

end Residue

end FramedStrictClass

variable (Λ) in
/-- The functor `C_Λ ⥤ Type` of `T`-framed deformations of `ρbar`, with pushforward of framed
deformations. -/
-- Exposed so that `(framedStrictClassFunctor Λ ρbar T).obj A` unfolds to
-- `FramedStrictClass ρbar T A` in statements.
@[expose] def framedStrictClassFunctor (T : Type y) : ArtinLocalAlg Λ k ⥤ Type (max w v x y) where
  obj A := FramedStrictClass ρbar T A
  map f := TypeCat.ofHom (FramedStrictClass.map f)
  map_id A := by
    ext c : 3
    exact FramedStrictClass.map_id c
  map_comp f f' := by
    ext c : 3
    exact FramedStrictClass.map_comp f f' c

variable (Λ) in
@[simp]
theorem framedStrictClassFunctor_obj (T : Type y) (A : ArtinLocalAlg Λ k) :
    (framedStrictClassFunctor Λ ρbar T).obj A = FramedStrictClass ρbar T A :=
  (rfl)

variable (Λ) in
@[simp]
theorem framedStrictClassFunctor_map_apply (T : Type y) {A B : ArtinLocalAlg Λ k} (f : A ⟶ B)
    (c : FramedStrictClass ρbar T A) :
    (framedStrictClassFunctor Λ ρbar T).map f c = FramedStrictClass.map f c :=
  (rfl)

variable (Λ) in
/-- The natural map from framed lifts to framed deformations. -/
def toFramedStrictClass (T : Type y) :
    framedLiftFunctor Λ ρbar T ⟶ framedStrictClassFunctor Λ ρbar T where
  app A := TypeCat.ofHom FramedStrictClass.mk

variable (Λ) in
@[simp]
theorem toFramedStrictClass_app_apply (T : Type y) (A : ArtinLocalAlg Λ k)
    (x : FramedLift ρbar T A) : (toFramedStrictClass Λ ρbar T).app A x = FramedStrictClass.mk x :=
  (rfl)

variable (Λ) in
/-- Reindexing frames along `e : T' → T` as a natural transformation of framed deformation
functors. For an inclusion `T' ⊆ T` it forgets the frames outside `T'`. -/
def comapFrame {T T' : Type y} (e : T' → T) :
    framedStrictClassFunctor Λ ρbar T ⟶ framedStrictClassFunctor Λ ρbar T' where
  app A := TypeCat.ofHom (FramedStrictClass.comapFrame e)
  naturality A B f := by
    ext c : 3
    exact FramedStrictClass.comapFrame_map e f c

variable (Λ) in
@[simp]
theorem comapFrame_app_apply {T T' : Type y} (e : T' → T) (A : ArtinLocalAlg Λ k)
    (c : FramedStrictClass ρbar T A) :
    (comapFrame Λ ρbar e).app A c = FramedStrictClass.comapFrame e c :=
  (rfl)

variable (Λ) in
/-- Normalising the frame at `t₀ ∈ T`: the functor of `T`-framed deformations is isomorphic to the
functor of `T ∖ {t₀}`-framed lifts. -/
def framedStrictClassFunctorIso {T : Type y} [DecidableEq T] (t₀ : T) :
    framedStrictClassFunctor Λ ρbar T ≅ framedLiftFunctor Λ ρbar {t // t ≠ t₀} :=
  NatIso.ofComponents (fun _ ↦ (FramedStrictClass.normalizeEquiv t₀).toIso) fun f ↦ by
    ext c : 3
    exact FramedStrictClass.normalizeEquiv_map t₀ f c

variable (Λ) in
@[simp]
theorem framedStrictClassFunctorIso_hom_app_apply {T : Type y} [DecidableEq T] (t₀ : T)
    (A : ArtinLocalAlg Λ k) (c : FramedStrictClass ρbar T A) :
    (framedStrictClassFunctorIso Λ ρbar t₀).hom.app A c = FramedStrictClass.normalizeEquiv t₀ c :=
  (rfl)

variable (Λ) in
@[simp]
theorem framedStrictClassFunctorIso_inv_app_apply {T : Type y} [DecidableEq T] (t₀ : T)
    (A : ArtinLocalAlg Λ k) (y : FramedLift ρbar {t // t ≠ t₀} A) :
    (framedStrictClassFunctorIso Λ ρbar t₀).inv.app A y =
      (FramedStrictClass.normalizeEquiv t₀).symm y :=
  (rfl)

end TauCeti.Deformation
