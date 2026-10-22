/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Prefunctor
public import TauCeti.Combinatorics.Network.Flow

/-!
# Isomorphisms of bounded networks

An isomorphism of bounded networks consists of an equivalence of vertices and equivalences of
the corresponding arrow types that preserve both bounds.  This file supplies identity, inverse,
and composition, together with transport of assignments, feasibility, excess, circulations,
bounded terminal assignments, ordinary flows, and directed paths.

Arrow identities are retained by transport, so the constructions apply unchanged to networks
with parallel arrows, antiparallel arrows, and loops.  Finiteness is needed only for excess and
flow transport, where excess is defined by finite sums.
-/

public section

namespace TauCeti

universe u u' u'' v v' v'' w w'

namespace Network

variable {K : Type w}
variable {V : Type u} {W : Type u'} {X : Type u''}

section LE

variable [LE K]
variable {N : Network K V} {N' : Network K W} {N'' : Network K X}

/-- The directed paths in the explicit arrow family carried by a network. -/
abbrev Path (N : Network K V) (x y : V) := @Quiver.Path V ⟨N.Hom⟩ x y

/-- An isomorphism of bounded networks: an equivalence of vertices and equivalences of every
corresponding arrow type that preserve the lower and upper bounds. -/
@[ext]
structure Iso (N : Network K V) (N' : Network K W) where
  /-- The equivalence of vertices. -/
  vertexEquiv : V ≃ W
  /-- The equivalence between arrows with corresponding endpoints. -/
  homEquiv : ∀ x y, N.Hom x y ≃ N'.Hom (vertexEquiv x) (vertexEquiv y)
  /-- Lower bounds are preserved. -/
  map_lower : ∀ {x y} (a : N.Hom x y), N'.lower (homEquiv x y a) = N.lower a
  /-- Upper bounds are preserved. -/
  map_upper : ∀ {x y} (a : N.Hom x y), N'.upper (homEquiv x y a) = N.upper a

/-- Notation for an isomorphism of bounded networks. -/
scoped infix:25 " ≃ₙ " => Network.Iso

namespace Iso

/-- The identity isomorphism of a bounded network. -/
@[refl] def refl (N : Network K V) : N ≃ₙ N where
  vertexEquiv := Equiv.refl V
  homEquiv _ _ := Equiv.refl _
  map_lower _ := rfl
  map_upper _ := rfl

/-- The composite of two bounded-network isomorphisms. -/
@[trans] def trans (e : N ≃ₙ N') (f : N' ≃ₙ N'') : N ≃ₙ N'' where
  vertexEquiv := e.vertexEquiv.trans f.vertexEquiv
  homEquiv x y := (e.homEquiv x y).trans (f.homEquiv (e.vertexEquiv x) (e.vertexEquiv y))
  map_lower a := (f.map_lower (e.homEquiv _ _ a)).trans (e.map_lower a)
  map_upper a := (f.map_upper (e.homEquiv _ _ a)).trans (e.map_upper a)

/-- The identity isomorphism uses the identity vertex equivalence. -/
theorem refl_vertexEquiv (N : Network K V) :
    (refl N).vertexEquiv = Equiv.refl V :=
  (rfl)

/-- The identity isomorphism fixes vertices. -/
@[simp]
theorem refl_vertexEquiv_apply (N : Network K V) (x : V) : (refl N).vertexEquiv x = x :=
  (rfl)

/-- The identity isomorphism fixes every arrow, after transporting its endpoints. -/
@[simp]
theorem refl_homEquiv_apply (N : Network K V) (x y : V) (a : N.Hom x y) :
    @Quiver.homOfEq V ⟨N.Hom⟩ _ _ x y ((refl N).homEquiv x y a)
      (refl_vertexEquiv_apply N x) (refl_vertexEquiv_apply N y) = a :=
  (rfl)

/-- Composition uses the composite vertex equivalence. -/
theorem trans_vertexEquiv (e : N ≃ₙ N') (f : N' ≃ₙ N'') :
    (e.trans f).vertexEquiv = e.vertexEquiv.trans f.vertexEquiv :=
  (rfl)

/-- Composition applies the two vertex equivalences in order. -/
@[simp]
theorem trans_vertexEquiv_apply (e : N ≃ₙ N') (f : N' ≃ₙ N'') (x : V) :
    (e.trans f).vertexEquiv x = f.vertexEquiv (e.vertexEquiv x) :=
  (rfl)

/-- Composition applies the two arrow equivalences in order, after transporting endpoints. -/
@[simp]
theorem trans_homEquiv_apply (e : N ≃ₙ N') (f : N' ≃ₙ N'') (x y : V)
    (a : N.Hom x y) :
    @Quiver.homOfEq X ⟨N''.Hom⟩ _ _ _ _ ((e.trans f).homEquiv x y a)
      (trans_vertexEquiv_apply e f x) (trans_vertexEquiv_apply e f y) =
        f.homEquiv _ _ (e.homEquiv x y a) :=
  (rfl)

/-- Arrow transport commutes with transporting the arrow endpoints. -/
theorem homEquiv_homOfEq (e : N ≃ₙ N') {x y x' y' : V} (a : N.Hom x y) (hx : x = x')
    (hy : y = y') :
    e.homEquiv x' y' (@Quiver.homOfEq V ⟨N.Hom⟩ x y x' y' a hx hy) =
      @Quiver.homOfEq W ⟨N'.Hom⟩ _ _ _ _ (e.homEquiv x y a) (congrArg e.vertexEquiv hx)
        (congrArg e.vertexEquiv hy) := by
  subst x' y'
  rfl

/-- The inverse arrow equivalence over arbitrary vertices of the target network. -/
def inverseHomEquiv (e : N ≃ₙ N') (x y : W) :
    N'.Hom x y ≃ N.Hom (e.vertexEquiv.symm x) (e.vertexEquiv.symm y) where
  toFun a := (e.homEquiv _ _).symm
    (@Quiver.homOfEq W ⟨N'.Hom⟩ x y _ _ a (e.vertexEquiv.apply_symm_apply x).symm
      (e.vertexEquiv.apply_symm_apply y).symm)
  invFun a := @Quiver.homOfEq W ⟨N'.Hom⟩ _ _ x y (e.homEquiv _ _ a)
    (e.vertexEquiv.apply_symm_apply x) (e.vertexEquiv.apply_symm_apply y)
  left_inv a := by simp
  right_inv a := by simp

/-- The inverse arrow equivalence transports the arrow endpoints and then inverts the forward
arrow equivalence. -/
theorem inverseHomEquiv_apply (e : N ≃ₙ N') (x y : W) (a : N'.Hom x y) :
    e.inverseHomEquiv x y a = (e.homEquiv _ _).symm
      (@Quiver.homOfEq W ⟨N'.Hom⟩ x y _ _ a (e.vertexEquiv.apply_symm_apply x).symm
        (e.vertexEquiv.apply_symm_apply y).symm) :=
  (rfl)

/-- An assignment pair related by forward arrow transport is also related by inverse arrow
transport. -/
private theorem apply_inverseHomEquiv {R : Type w'} (e : N ≃ₙ N') (g : N.Assignment R)
    (g' : N'.Assignment R) (hg : ∀ {x y} (a : N.Hom x y), g' (e.homEquiv x y a) = g a)
    {x y : W} (a : N'.Hom x y) : g (e.inverseHomEquiv x y a) = g' a := by
  rw [inverseHomEquiv_apply, ← hg]
  simp only [Equiv.apply_symm_apply]
  exact assignment_homOfEq g' a _ _

/-- Reverse a bounded-network isomorphism. -/
@[symm] def symm (e : N ≃ₙ N') : N' ≃ₙ N where
  vertexEquiv := e.vertexEquiv.symm
  homEquiv := e.inverseHomEquiv
  map_lower := e.apply_inverseHomEquiv N.lower N'.lower e.map_lower
  map_upper := e.apply_inverseHomEquiv N.upper N'.upper e.map_upper

/-- The inverse isomorphism uses the inverse vertex equivalence. -/
theorem symm_vertexEquiv (e : N ≃ₙ N') :
    e.symm.vertexEquiv = e.vertexEquiv.symm :=
  (rfl)

/-- The inverse isomorphism applies the inverse vertex equivalence. -/
@[simp]
theorem symm_vertexEquiv_apply (e : N ≃ₙ N') (x : W) :
    e.symm.vertexEquiv x = e.vertexEquiv.symm x :=
  (rfl)

/-- Applying the inverse vertex equivalence after the forward one fixes a vertex. -/
theorem symm_vertexEquiv_apply_vertexEquiv (e : N ≃ₙ N') (x : V) :
    e.symm.vertexEquiv (e.vertexEquiv x) = x := by
  simp

/-- Applying the forward vertex equivalence after the inverse one fixes a vertex. -/
theorem vertexEquiv_apply_symm_vertexEquiv (e : N ≃ₙ N') (x : W) :
    e.vertexEquiv (e.symm.vertexEquiv x) = x := by
  simp

/-- The inverse isomorphism uses the inverse arrow equivalence, after transporting endpoints. -/
@[simp]
theorem symm_homEquiv_apply (e : N ≃ₙ N') (x y : W) (a : N'.Hom x y) :
    @Quiver.homOfEq V ⟨N.Hom⟩ _ _ _ _ (e.symm.homEquiv x y a)
      (symm_vertexEquiv_apply e x) (symm_vertexEquiv_apply e y) =
        e.inverseHomEquiv x y a :=
  (rfl)

/-- Applying inverse arrow transport after forward transport fixes an arrow after transporting
its endpoints along the inverse laws. -/
@[simp]
theorem symm_homEquiv_apply_homEquiv (e : N ≃ₙ N') (x y : V) (a : N.Hom x y) :
    @Quiver.homOfEq V ⟨N.Hom⟩ _ _ x y
      (e.symm.homEquiv (e.vertexEquiv x) (e.vertexEquiv y) (e.homEquiv x y a))
      (symm_vertexEquiv_apply_vertexEquiv e x) (symm_vertexEquiv_apply_vertexEquiv e y) = a := by
  have h := symm_homEquiv_apply e _ _ (e.homEquiv x y a)
  rw [@Quiver.homOfEq_eq_iff V ⟨N.Hom⟩] at h
  simp [h, inverseHomEquiv_apply, ← homEquiv_homOfEq]

/-- Applying forward arrow transport after inverse transport fixes an arrow after transporting
its endpoints along the inverse laws. -/
@[simp]
theorem homEquiv_apply_symm_homEquiv (e : N ≃ₙ N') (x y : W) (a : N'.Hom x y) :
    @Quiver.homOfEq W ⟨N'.Hom⟩ _ _ x y
      (e.homEquiv _ _ (e.symm.homEquiv x y a))
      (vertexEquiv_apply_symm_vertexEquiv e x) (vertexEquiv_apply_symm_vertexEquiv e y) = a := by
  have h := symm_homEquiv_apply e x y a
  rw [@Quiver.homOfEq_eq_iff V ⟨N.Hom⟩] at h
  simp [h, homEquiv_homOfEq, inverseHomEquiv_apply]

/-- Transport assignments along a bounded-network isomorphism. -/
def assignmentEquiv (e : N ≃ₙ N') (R : Type w') : N.Assignment R ≃ N'.Assignment R :=
  e.vertexEquiv.piCongr fun x ↦
    e.vertexEquiv.piCongr fun y ↦ (e.homEquiv x y).arrowCongr (Equiv.refl R)

/-- Transporting an assignment evaluates on a transported arrow as the original assignment. -/
@[simp]
theorem assignmentEquiv_apply (e : N ≃ₙ N') (R : Type w') (f : N.Assignment R)
    {x y : V} (a : N.Hom x y) :
    e.assignmentEquiv R f (e.homEquiv x y a) = f a := by
  simp [assignmentEquiv]

/-- Pulling an assignment back evaluates by applying the forward arrow equivalence. -/
@[simp]
theorem assignmentEquiv_symm_apply (e : N ≃ₙ N') (R : Type w') (f : N'.Assignment R)
    {x y : V} (a : N.Hom x y) :
    (e.assignmentEquiv R).symm f a = f (e.homEquiv x y a) := by
  simp [assignmentEquiv]

/-- Inverse assignment transport is transport along the inverse network isomorphism. -/
theorem assignmentEquiv_symm (e : N ≃ₙ N') (R : Type w') :
    (e.assignmentEquiv R).symm = e.symm.assignmentEquiv R := by
  apply Equiv.ext
  intro f
  ext x y a
  rw [assignmentEquiv_symm_apply]
  symm
  calc
    e.symm.assignmentEquiv R f a =
        e.symm.assignmentEquiv R f
          (@Quiver.homOfEq V ⟨N.Hom⟩ _ _ x y
            (e.symm.homEquiv (e.vertexEquiv x) (e.vertexEquiv y) (e.homEquiv x y a))
            (symm_vertexEquiv_apply_vertexEquiv e x)
            (symm_vertexEquiv_apply_vertexEquiv e y)) := by
      rw [symm_homEquiv_apply_homEquiv]
    _ = e.symm.assignmentEquiv R f
          (e.symm.homEquiv (e.vertexEquiv x) (e.vertexEquiv y) (e.homEquiv x y a)) :=
      assignment_homOfEq _ _ _ _
    _ = f (e.homEquiv x y a) := e.symm.assignmentEquiv_apply R f (e.homEquiv x y a)

/-- Assignment transport carries the zero assignment to zero. -/
@[simp]
theorem assignmentEquiv_zero {R : Type w'} [Zero R] (e : N ≃ₙ N') :
    e.assignmentEquiv R 0 = 0 := by
  apply (e.assignmentEquiv R).symm.injective
  ext x y a
  simp

/-- Transport along the identity network isomorphism is the identity on assignments. -/
@[simp]
theorem assignmentEquiv_refl (N : Network K V) (R : Type w') :
    (refl N).assignmentEquiv R = Equiv.refl (N.Assignment R) := by
  apply Equiv.ext
  intro f
  ext x y a
  exact (refl N).assignmentEquiv_apply R f a

/-- Transport carries the lower-bound assignment to the lower-bound assignment. -/
@[simp]
theorem assignmentEquiv_lower (e : N ≃ₙ N') : e.assignmentEquiv K N.lower = N'.lower := by
  apply (e.assignmentEquiv K).symm.injective
  ext x y a
  simp [e.map_lower]

/-- Transport carries the upper-bound assignment to the upper-bound assignment. -/
@[simp]
theorem assignmentEquiv_upper (e : N ≃ₙ N') : e.assignmentEquiv K N.upper = N'.upper := by
  apply (e.assignmentEquiv K).symm.injective
  ext x y a
  simp [e.map_upper]

/-- Transporting assignments along a composite is the composite of the assignment transports. -/
@[simp]
theorem assignmentEquiv_trans (e : N ≃ₙ N') (f : N' ≃ₙ N'') (R : Type w') :
    (e.trans f).assignmentEquiv R = (e.assignmentEquiv R).trans (f.assignmentEquiv R) := by
  apply Equiv.ext
  intro g
  apply (e.trans f).assignmentEquiv R |>.symm.injective
  ext x y a
  calc
    (e.trans f).assignmentEquiv R g ((e.trans f).homEquiv x y a) = g a :=
      (e.trans f).assignmentEquiv_apply R g a
    _ = e.assignmentEquiv R g (e.homEquiv x y a) := (e.assignmentEquiv_apply R g a).symm
    _ = f.assignmentEquiv R (e.assignmentEquiv R g)
        (f.homEquiv _ _ (e.homEquiv x y a)) :=
      (f.assignmentEquiv_apply R (e.assignmentEquiv R g) (e.homEquiv x y a)).symm
    _ = f.assignmentEquiv R (e.assignmentEquiv R g) ((e.trans f).homEquiv x y a) := rfl

end Iso

end LE


section Preorder

variable [Preorder K]
variable {N : Network K V} {N' : Network K W}

namespace Iso

/-- Assignment transport preserves arbitrary pointwise order intervals. -/
theorem assignmentEquiv_mem_Icc_map_iff (e : N ≃ₙ N') (lo hi f : N.Assignment K) :
    e.assignmentEquiv K f ∈
        Set.Icc (e.assignmentEquiv K lo) (e.assignmentEquiv K hi) ↔ f ∈ Set.Icc lo hi := by
  constructor
  · intro hf
    constructor
    · intro x y a
      simpa using hf.1 (e.vertexEquiv x) (e.vertexEquiv y) (e.homEquiv x y a)
    · intro x y a
      simpa using hf.2 (e.vertexEquiv x) (e.vertexEquiv y) (e.homEquiv x y a)
  · intro hf
    constructor <;> intro x y a
    · obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective x
      obtain ⟨y, rfl⟩ := e.vertexEquiv.surjective y
      obtain ⟨a, rfl⟩ := (e.homEquiv x y).surjective a
      simpa using hf.1 x y a
    · obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective x
      obtain ⟨y, rfl⟩ := e.vertexEquiv.surjective y
      obtain ⟨a, rfl⟩ := (e.homEquiv x y).surjective a
      simpa using hf.2 x y a

/-- Assignment transport preserves pointwise order intervals when the endpoints are transported. -/
theorem assignmentEquiv_mem_Icc_iff (e : N ≃ₙ N') (f : N.Assignment K) :
    e.assignmentEquiv K f ∈ Set.Icc N'.lower N'.upper ↔ f ∈ Set.Icc N.lower N.upper := by
  simpa only [assignmentEquiv_lower, assignmentEquiv_upper] using
    e.assignmentEquiv_mem_Icc_map_iff N.lower N.upper f

end Iso

end Preorder


section LE

variable [LE K]
variable {N : Network K V} {N' : Network K W}

namespace Iso

/-- Excess is preserved by assignment transport. -/
@[simp]
theorem excessAt_assignmentEquiv [Fintype V] [Fintype W]
    [∀ x y, Fintype (N.Hom x y)] [∀ x y, Fintype (N'.Hom x y)]
    {R : Type w'} [AddCommGroup R] (e : N ≃ₙ N') (f : N.Assignment R) (x : V) :
    TauCeti.excessAt (e.assignmentEquiv R f) (e.vertexEquiv x) = TauCeti.excessAt f x := by
  rw [← excessAt_comp_equiv e.vertexEquiv e.homEquiv (e.assignmentEquiv R f) x]
  congr 1
  exact (e.assignmentEquiv R).symm_apply_apply f

/-- Assignment transport preserves the circulation predicate. -/
@[simp]
theorem isCirculation_assignmentEquiv_iff [Fintype V] [Fintype W]
    [∀ x y, Fintype (N.Hom x y)] [∀ x y, Fintype (N'.Hom x y)]
    {R : Type w'} [AddCommGroup R] (e : N ≃ₙ N') (f : N.Assignment R) :
    IsCirculation (e.assignmentEquiv R f) ↔ IsCirculation f := by
  rw [isCirculation_iff, isCirculation_iff]
  constructor
  · intro hf x
    rw [← e.excessAt_assignmentEquiv f x]
    exact hf _
  · intro hf y
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective y
    rw [e.excessAt_assignmentEquiv f x, hf x]

/-- A network isomorphism as a prefunctor between its explicit arrow families. -/
def toPrefunctor (e : N ≃ₙ N') :
    @Prefunctor V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) :=
  @Prefunctor.mk V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.vertexEquiv
    (fun {x y} a ↦ e.homEquiv x y a)

/-- The identity network isomorphism induces the identity prefunctor. -/
@[simp]
theorem toPrefunctor_refl (N : Network K V) :
    (refl N).toPrefunctor = @Prefunctor.id V (Quiver.mk N.Hom) := by
  rfl

/-- Composition of network isomorphisms induces composition of prefunctors. -/
@[simp]
theorem toPrefunctor_trans {N'' : Network K X} (e : N ≃ₙ N') (f : N' ≃ₙ N'') :
    (e.trans f).toPrefunctor =
      @Prefunctor.comp V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) X (Quiver.mk N''.Hom)
        e.toPrefunctor f.toPrefunctor := by
  rfl

/-- Transport a directed path along a network isomorphism. -/
def mapPath (e : N ≃ₙ N') {x y : V} (p : N.Path x y) :
    N'.Path (e.vertexEquiv x) (e.vertexEquiv y) :=
  @Prefunctor.mapPath V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.toPrefunctor x y p

/-- Path transport preserves the empty path. -/
@[simp]
theorem mapPath_nil (e : N ≃ₙ N') (x : V) :
    e.mapPath (@Quiver.Path.nil V ⟨N.Hom⟩ x) = @Quiver.Path.nil W ⟨N'.Hom⟩ _ :=
  @Prefunctor.mapPath_nil V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.toPrefunctor x

/-- Path transport commutes with appending one arrow. -/
@[simp]
theorem mapPath_cons (e : N ≃ₙ N') {x y z : V} (p : N.Path x y) (a : N.Hom y z) :
    e.mapPath (@Quiver.Path.cons V ⟨N.Hom⟩ x y z p a) =
      @Quiver.Path.cons W ⟨N'.Hom⟩ _ _ _ (e.mapPath p) (e.homEquiv y z a) :=
  @Prefunctor.mapPath_cons V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.toPrefunctor
    x y z p a

end Iso

/-- Transporting the endpoints of an empty path gives the empty path. -/
private theorem homOfEq_path_nil {N : Network K V} {x x' : V} (hx : x = x') :
    @Quiver.homOfEq V ⟨fun x y ↦ N.Path x y⟩ x x x' x'
      (@Quiver.Path.nil V ⟨N.Hom⟩ x) hx hx = @Quiver.Path.nil V ⟨N.Hom⟩ x' := by
  subst x'
  rfl

/-- Transporting the endpoints of a path ending in an arrow transports the shorter path and the
arrow separately. -/
private theorem homOfEq_path_cons {N : Network K V} {x y z x' y' z' : V} (q : N.Path x y)
    (a : N.Hom y z) (hx : x = x') (hy : y = y') (hz : z = z') :
    @Quiver.homOfEq V ⟨fun x y ↦ N.Path x y⟩ x z x' z'
        (@Quiver.Path.cons V ⟨N.Hom⟩ x y z q a) hx hz =
      @Quiver.Path.cons V ⟨N.Hom⟩ x' y' z'
        (@Quiver.homOfEq V ⟨fun x y ↦ N.Path x y⟩ x y x' y' q hx hy)
        (@Quiver.homOfEq V ⟨N.Hom⟩ y z y' z' a hy hz) := by
  subst x' y' z'
  rfl

namespace Iso

/-- The identity network isomorphism fixes every path. -/
@[simp]
theorem mapPath_refl (N : Network K V) {x y : V} (p : N.Path x y) :
    @Quiver.homOfEq V ⟨fun x y ↦ N.Path x y⟩ _ _ x y ((refl N).mapPath p)
      (refl_vertexEquiv_apply N x) (refl_vertexEquiv_apply N y) = p :=
  -- The endpoint casts are along `rfl`, and `(refl N).toPrefunctor` is the identity prefunctor
  -- by `toPrefunctor_refl`, so both sides agree definitionally with `Prefunctor.mapPath_id`.
  @Prefunctor.mapPath_id V (Quiver.mk N.Hom) x y p

/-- Transport along a composite isomorphism applies the two path transports in order. -/
@[simp]
theorem mapPath_trans {N'' : Network K X} (e : N ≃ₙ N') (f : N' ≃ₙ N'')
    {x y : V} (p : N.Path x y) :
    @Quiver.homOfEq X ⟨fun x y ↦ N''.Path x y⟩ _ _ _ _ ((e.trans f).mapPath p)
      (trans_vertexEquiv_apply e f x) (trans_vertexEquiv_apply e f y) =
        f.mapPath (e.mapPath p) :=
  -- The endpoint casts are along `rfl`, and `(e.trans f).toPrefunctor` is the composite
  -- prefunctor by `toPrefunctor_trans`, so this is `Prefunctor.mapPath_comp_apply`.
  @Prefunctor.mapPath_comp_apply V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom)
    e.toPrefunctor X (Quiver.mk N''.Hom) f.toPrefunctor x y p

/-- Path transport along a pair of isomorphisms that is inverse on vertices and on arrows fixes
every path. -/
private theorem homOfEq_mapPath_mapPath (e : N ≃ₙ N') (f : N' ≃ₙ N)
    (hv : ∀ x, f.vertexEquiv (e.vertexEquiv x) = x)
    (ha : ∀ x y (a : N.Hom x y),
      @Quiver.homOfEq V ⟨N.Hom⟩ _ _ x y (f.homEquiv _ _ (e.homEquiv x y a)) (hv x) (hv y) = a)
    {x y : V} (p : N.Path x y) :
    @Quiver.homOfEq V ⟨fun x y ↦ N.Path x y⟩ _ _ x y (f.mapPath (e.mapPath p)) (hv x) (hv y) =
      p := by
  induction p with
  | nil =>
      rw [mapPath_nil, mapPath_nil]
      exact homOfEq_path_nil (hv x)
  | @cons y z p a ih =>
      rw [mapPath_cons, mapPath_cons, homOfEq_path_cons _ _ (hv x) (hv y) (hv z), ih, ha]

/-- Mapping a path forward and then along the inverse isomorphism fixes it. -/
@[simp]
theorem mapPath_symm_mapPath (e : N ≃ₙ N') {x y : V} (p : N.Path x y) :
    @Quiver.homOfEq V ⟨fun x y ↦ N.Path x y⟩ _ _ x y (e.symm.mapPath (e.mapPath p))
      (symm_vertexEquiv_apply_vertexEquiv e x) (symm_vertexEquiv_apply_vertexEquiv e y) = p :=
  homOfEq_mapPath_mapPath e e.symm _ e.symm_homEquiv_apply_homEquiv p

/-- Mapping a path along the inverse and then forward fixes it. -/
@[simp]
theorem mapPath_mapPath_symm (e : N ≃ₙ N') {x y : W} (p : N'.Path x y) :
    @Quiver.homOfEq W ⟨fun x y ↦ N'.Path x y⟩ _ _ x y (e.mapPath (e.symm.mapPath p))
      (vertexEquiv_apply_symm_vertexEquiv e x) (vertexEquiv_apply_symm_vertexEquiv e y) = p :=
  homOfEq_mapPath_mapPath e.symm e _ e.homEquiv_apply_symm_homEquiv p

/-- Path transport preserves length. -/
@[simp]
theorem length_mapPath (e : N ≃ₙ N') {x y : V} (p : N.Path x y) :
    @Quiver.Path.length W ⟨N'.Hom⟩ _ _ (e.mapPath p) =
      @Quiver.Path.length V ⟨N.Hom⟩ _ _ p :=
  @Prefunctor.length_mapPath V W (Quiver.mk N.Hom) (Quiver.mk N'.Hom) e.toPrefunctor x y p

/-- Path transport preserves concatenation. -/
@[simp]
theorem mapPath_comp (e : N ≃ₙ N') {x y z : V} (p : N.Path x y) (q : N.Path y z) :
    e.mapPath (@Quiver.Path.comp V ⟨N.Hom⟩ x y z p q) =
      @Quiver.Path.comp W ⟨N'.Hom⟩ _ _ _ (e.mapPath p) (e.mapPath q) :=
  @Prefunctor.mapPath_comp V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.toPrefunctor
    x y p z q

end Iso

end LE


section Flow

variable [AddCommGroup K] [Preorder K]
variable {N : Network K V} {N' : Network K W}
variable [Fintype V] [Fintype W]
variable [∀ x y, Fintype (N.Hom x y)] [∀ x y, Fintype (N'.Hom x y)]

namespace Iso

/-- Transport a bounded terminal assignment, transporting its two bound assignments with it. -/
def mapBoundedFlow (e : N ≃ₙ N') {lo hi : N.Assignment K} {s t : V}
    (f : TauCeti.BoundedFlow lo hi s t) :
    TauCeti.BoundedFlow (e.assignmentEquiv K lo) (e.assignmentEquiv K hi)
      (e.vertexEquiv s) (e.vertexEquiv t) where
  toFun := e.assignmentEquiv K f.toFun
  mem_Icc := (e.assignmentEquiv_mem_Icc_map_iff lo hi f.toFun).2 f.mem_Icc
  conserve y hys hyt := by
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective y
    rw [e.excessAt_assignmentEquiv]
    exact f.conserve x (fun h ↦ hys (congrArg e.vertexEquiv h))
      (fun h ↦ hyt (congrArg e.vertexEquiv h))

/-- The underlying assignment of a transported bounded flow is assignment transport. -/
@[simp]
theorem mapBoundedFlow_toFun (e : N ≃ₙ N') {lo hi : N.Assignment K} {s t : V}
    (f : TauCeti.BoundedFlow lo hi s t) :
    (e.mapBoundedFlow f).toFun = e.assignmentEquiv K f.toFun :=
  (rfl)

/-- Transport preserves the value of a bounded terminal assignment. -/
@[simp]
theorem val_mapBoundedFlow (e : N ≃ₙ N') {lo hi : N.Assignment K} {s t : V}
    (f : TauCeti.BoundedFlow lo hi s t) : (e.mapBoundedFlow f).val = f.val := by
  rw [TauCeti.BoundedFlow.val_def, mapBoundedFlow_toFun, e.excessAt_assignmentEquiv,
    TauCeti.BoundedFlow.val_def]

/-- Transport an ordinary flow, transporting its capacity assignment with it. -/
def mapFlow (e : N ≃ₙ N') {cap : N.Assignment K} {s t : V}
    (f : TauCeti.Flow cap s t) :
    TauCeti.Flow (e.assignmentEquiv K cap) (e.vertexEquiv s) (e.vertexEquiv t) where
  toFun := e.assignmentEquiv K f.toFun
  mem_Icc := by
    simpa only [assignmentEquiv_zero] using
      (e.assignmentEquiv_mem_Icc_map_iff 0 cap f.toFun).2 f.mem_Icc
  conserve y hys hyt := by
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective y
    rw [e.excessAt_assignmentEquiv]
    exact f.conserve x (fun h ↦ hys (congrArg e.vertexEquiv h))
      (fun h ↦ hyt (congrArg e.vertexEquiv h))
  excessAt_sink_nonneg := by
    rw [e.excessAt_assignmentEquiv]
    exact f.excessAt_sink_nonneg

/-- The underlying assignment of a transported flow is assignment transport. -/
@[simp]
theorem mapFlow_toFun (e : N ≃ₙ N') {cap : N.Assignment K} {s t : V}
    (f : TauCeti.Flow cap s t) : (e.mapFlow f).toFun = e.assignmentEquiv K f.toFun :=
  (rfl)

/-- Transport preserves the value of an ordinary flow. -/
@[simp]
theorem val_mapFlow (e : N ≃ₙ N') {cap : N.Assignment K} {s t : V}
    (f : TauCeti.Flow cap s t) : (e.mapFlow f).val = f.val := by
  rw [TauCeti.BoundedFlow.val_def, mapFlow_toFun, e.excessAt_assignmentEquiv,
    TauCeti.BoundedFlow.val_def]

end Iso

end Flow

end Network

end TauCeti
