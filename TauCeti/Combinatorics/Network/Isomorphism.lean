/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Prefunctor
public import TauCeti.Combinatorics.Network.Flow
public import TauCeti.Combinatorics.Network.Walk

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
  exact g'.apply_homOfEq a _ _

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
      Assignment.apply_homOfEq _ _ _ _
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

/-- Assignment transport preserves and reflects the pointwise order. -/
theorem assignmentEquiv_le_assignmentEquiv_iff {R : Type w'} [LE R] (e : N ≃ₙ N')
    (f g : N.Assignment R) : e.assignmentEquiv R f ≤ e.assignmentEquiv R g ↔ f ≤ g := by
  constructor
  · intro h x y a
    simpa using h (e.vertexEquiv x) (e.vertexEquiv y) (e.homEquiv x y a)
  · intro h x y a
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective x
    obtain ⟨y, rfl⟩ := e.vertexEquiv.surjective y
    obtain ⟨a, rfl⟩ := (e.homEquiv x y).surjective a
    simpa using h x y a

end Iso

end LE


section Preorder

variable [Preorder K]
variable {N : Network K V} {N' : Network K W}

namespace Iso

/-- Assignment transport preserves arbitrary pointwise order intervals. -/
theorem assignmentEquiv_mem_Icc_map_iff (e : N ≃ₙ N') (lo hi f : N.Assignment K) :
    e.assignmentEquiv K f ∈
        Set.Icc (e.assignmentEquiv K lo) (e.assignmentEquiv K hi) ↔ f ∈ Set.Icc lo hi :=
  and_congr (e.assignmentEquiv_le_assignmentEquiv_iff lo f)
    (e.assignmentEquiv_le_assignmentEquiv_iff f hi)

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
  funext x y a
  exact e.assignmentEquiv_apply R f a

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
def mapPath (e : N ≃ₙ N') {x y : V} (p : ArrowWalk N.Hom x y) :
    ArrowWalk N'.Hom (e.vertexEquiv x) (e.vertexEquiv y) :=
  @Prefunctor.mapPath V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.toPrefunctor x y p

/-- Path transport preserves the empty path. -/
@[simp]
theorem mapPath_nil (e : N ≃ₙ N') (x : V) :
    e.mapPath (ArrowWalk.nil x) = ArrowWalk.nil (e.vertexEquiv x) :=
  @Prefunctor.mapPath_nil V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.toPrefunctor x

/-- Path transport commutes with appending one arrow. -/
@[simp]
theorem mapPath_cons (e : N ≃ₙ N') {x y z : V} (p : ArrowWalk N.Hom x y) (a : N.Hom y z) :
    e.mapPath (p.cons a) = (e.mapPath p).cons (e.homEquiv y z a) :=
  @Prefunctor.mapPath_cons V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.toPrefunctor
    x y z p a

/-- The identity network isomorphism fixes every path. -/
@[simp]
theorem mapPath_refl (N : Network K V) {x y : V} (p : ArrowWalk N.Hom x y) :
    @Quiver.Path.cast V ⟨N.Hom⟩ _ _ x y (refl_vertexEquiv_apply N x)
      (refl_vertexEquiv_apply N y) ((refl N).mapPath p) = p :=
  -- The endpoint casts are along `rfl`, and `(refl N).toPrefunctor` is the identity prefunctor
  -- by `toPrefunctor_refl`, so both sides agree definitionally with `Prefunctor.mapPath_id`.
  @Prefunctor.mapPath_id V (Quiver.mk N.Hom) x y p

/-- Transport along a composite isomorphism applies the two path transports in order. -/
@[simp]
theorem mapPath_trans {N'' : Network K X} (e : N ≃ₙ N') (f : N' ≃ₙ N'')
    {x y : V} (p : ArrowWalk N.Hom x y) :
    @Quiver.Path.cast X ⟨N''.Hom⟩ _ _ _ _ (trans_vertexEquiv_apply e f x)
      (trans_vertexEquiv_apply e f y) ((e.trans f).mapPath p) =
        f.mapPath (e.mapPath p) :=
  -- The endpoint casts are along `rfl`, and `(e.trans f).toPrefunctor` is the composite
  -- prefunctor by `toPrefunctor_trans`, so this is `Prefunctor.mapPath_comp_apply`.
  @Prefunctor.mapPath_comp_apply V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom)
    e.toPrefunctor X (Quiver.mk N''.Hom) f.toPrefunctor x y p

/-- Mapping a path forward and then along the inverse isomorphism fixes it. -/
@[simp]
theorem mapPath_symm_mapPath (e : N ≃ₙ N') {x y : V} (p : ArrowWalk N.Hom x y) :
    @Quiver.Path.cast V ⟨N.Hom⟩ _ _ x y (symm_vertexEquiv_apply_vertexEquiv e x)
      (symm_vertexEquiv_apply_vertexEquiv e y) (e.symm.mapPath (e.mapPath p)) = p :=
  -- `Quiver.Hom.cast` and `Quiver.homOfEq` are the same endpoint transport by definition, so the
  -- arrow inverse law is the hypothesis of `Prefunctor.cast_mapPath_mapPath`.
  @Prefunctor.cast_mapPath_mapPath V W (Quiver.mk N.Hom) (Quiver.mk N'.Hom) e.toPrefunctor
    e.symm.toPrefunctor _ (e.symm_homEquiv_apply_homEquiv _ _) x y p

/-- Mapping a path along the inverse and then forward fixes it. -/
@[simp]
theorem mapPath_mapPath_symm (e : N ≃ₙ N') {x y : W} (p : ArrowWalk N'.Hom x y) :
    @Quiver.Path.cast W ⟨N'.Hom⟩ _ _ x y (vertexEquiv_apply_symm_vertexEquiv e x)
      (vertexEquiv_apply_symm_vertexEquiv e y) (e.mapPath (e.symm.mapPath p)) = p :=
  -- As in `mapPath_symm_mapPath`, `Quiver.Hom.cast` agrees with `Quiver.homOfEq` by definition.
  @Prefunctor.cast_mapPath_mapPath W V (Quiver.mk N'.Hom) (Quiver.mk N.Hom) e.symm.toPrefunctor
    e.toPrefunctor _ (e.homEquiv_apply_symm_homEquiv _ _) x y p

/-- Path transport preserves length. -/
@[simp]
theorem length_mapPath (e : N ≃ₙ N') {x y : V} (p : ArrowWalk N.Hom x y) :
    (e.mapPath p).length = p.length :=
  @Prefunctor.length_mapPath V W (Quiver.mk N.Hom) (Quiver.mk N'.Hom) e.toPrefunctor x y p

/-- Path transport preserves concatenation. -/
@[simp]
theorem mapPath_comp (e : N ≃ₙ N') {x y z : V} (p : ArrowWalk N.Hom x y)
    (q : ArrowWalk N.Hom y z) :
    e.mapPath (p.comp q) = (e.mapPath p).comp (e.mapPath q) :=
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
  simp [TauCeti.BoundedFlow.val_def]

/-- Transport an ordinary flow, transporting its capacity assignment with it. -/
def mapFlow (e : N ≃ₙ N') {cap : N.Assignment K} {s t : V}
    (f : TauCeti.Flow cap s t) :
    TauCeti.Flow (e.assignmentEquiv K cap) (e.vertexEquiv s) (e.vertexEquiv t) where
  toFun := e.assignmentEquiv K f.toFun
  mem_Icc := by
    simpa only [assignmentEquiv_zero] using
      (e.assignmentEquiv_mem_Icc_map_iff 0 cap f.toFun).2 f.mem_Icc
  conserve := (e.mapBoundedFlow f.toBoundedFlow).conserve
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
  simp [TauCeti.BoundedFlow.val_def]

end Iso

end Flow

end Network

end TauCeti
