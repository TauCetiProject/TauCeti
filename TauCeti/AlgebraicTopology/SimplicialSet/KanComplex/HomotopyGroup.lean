/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.PtSimplex

/-!
# Homotopy groups of Kan complexes

For a simplicial set `X` with a vertex `x`, `SSet.KanComplex.π n X x` is the set of homotopy
classes, relative to `∂Δ[n]`, of morphisms `Δ[n] ⟶ X` sending `∂Δ[n]` to `x`. When `X` is a Kan
complex and `n ≥ 1`, two such morphisms are homotopic exactly when they are related by
`SSet.PtSimplex.RelStruct₀` (`SSet.KanComplex.π.mk_eq_mk_iff`), and `π (n + 1) X x` is a group
(`SSet.KanComplex.π.group`): `mk p * mk q = mk pq` exactly when `p`, `pq` and `q` are faces of an
`(n + 2)`-simplex as in `SSet.PtSimplex.MulStruct` (`SSet.KanComplex.π.mul_mk_eq_iff`).

Functions on `π n X x` are defined by `SSet.KanComplex.π.lift` from functions on pointed simplices
which agree on homotopic ones.
A morphism `f : X ⟶ Y` sending `x` to `y` induces `SSet.KanComplex.π.map f : π n X x → π n Y y`,
functorially, and a group homomorphism `SSet.KanComplex.π.mapHom f` between Kan complexes.

These combinatorial homotopy groups are the ones to compare with the homotopy groups of a
topological space `T` through the Kan complex `TopCat.toSSet.obj T`.

## References

The definition of `π`, of its group structure and of their characterizations follows Joël Riou's
Mathlib pull request [mathlib4#42435](https://github.com/leanprover-community/mathlib4/pull/42435)
(file `Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/HomotopyGroup.lean`), whose names and
shapes are kept for the declarations the two share. There the group structures in the other
directions `i : Fin (n + 1)` are also constructed, and the characterizations cover `n = 0`; here
`π 0 X x` is only a type with a distinguished element. The induced maps are not part of that
pull request.

* J. P. May, *Simplicial Objects in Algebraic Topology*, University of Chicago Press, 1967,
  Chapter I, §3–§4.
-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace KanComplex

/-- The `n`th homotopy group of a simplicial set `X` at a vertex `x`: the homotopy classes,
relative to the boundary `∂Δ[n]`, of morphisms `Δ[n] ⟶ X` sending `∂Δ[n]` to `x`. It is a group
for `n ≥ 1` when `X` is a Kan complex (`SSet.KanComplex.π.group`). -/
def π (n : ℕ) (X : SSet.{u}) (x : X _⦋0⦌) : Type u :=
  RelativeMorphism.HomotopyClass ∂Δ[n] (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

namespace π

variable {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌}

/-- The class in `π n X x` of a pointed simplex. -/
def mk (p : X.PtSimplex n x) : π n X x := p.homotopyClass

lemma mk_surjective : Function.Surjective (mk : X.PtSimplex n x → π n X x) :=
  Quot.mk_surjective

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma rec {motive : π n X x → Prop} (mk : ∀ p : X.PtSimplex n x, motive (mk p))
    (a : π n X x) : motive a := by
  obtain ⟨p, rfl⟩ := mk_surjective a
  exact mk p

instance : One (π n X x) where
  one := mk .const

lemma one_def : (1 : π n X x) = mk .const := rfl

/-- Homotopic pointed simplices have the same class. -/
lemma mk_eq_mk_of_homotopy {p q : X.PtSimplex n x} (h : p.Homotopy q) : mk p = mk q :=
  h.eq

/-- A function on pointed simplices which takes the same value on homotopic pointed simplices
descends to `π n X x`. -/
def lift {α : Sort*} (f : X.PtSimplex n x → α)
    (hf : ∀ p q : X.PtSimplex n x, p.Homotopy q → f p = f q) : π n X x → α :=
  Quot.lift f fun p q ⟨h⟩ => hf p q h

@[simp]
lemma lift_mk {α : Sort*} (f : X.PtSimplex n x → α)
    (hf : ∀ p q : X.PtSimplex n x, p.Homotopy q → f p = f q) (p : X.PtSimplex n x) :
    lift f hf (mk p) = f p :=
  (rfl)

section map

variable {Y Z : SSet.{u}} {y : Y _⦋0⦌} {z : Z _⦋0⦌} (f : X ⟶ Y) (hy : f.app _ x = y)

/-- The map `π n X x → π n Y y` induced by a morphism `f : X ⟶ Y` sending `x` to `y`. -/
def map (a : π n X x) : π n Y y :=
  RelativeMorphism.HomotopyClass.postcomp a (.ofSimplex₀ f x y hy) (by simp)

@[simp]
lemma map_mk (p : X.PtSimplex n x) :
    map f hy (mk p) = mk (p.comp (.ofSimplex₀ f x y hy) (by simp)) := (rfl)

@[simp]
lemma map_one : map f hy (1 : π n X x) = 1 := by
  rw [one_def, map_mk, one_def]
  congr 1
  ext : 1
  simp [hy]

@[simp]
lemma map_id (a : π n X x) : map (𝟙 X) rfl a = a := by
  induction a with | mk p => rfl

lemma map_map (g : Y ⟶ Z) (hz : g.app _ y = z) (a : π n X x) :
    map g hz (map f hy a) = map (f ≫ g) (by simp [hy, hz]) a := by
  induction a with | mk p => rfl

end map

variable [KanComplex X]

/-- In a Kan complex, two pointed simplices of positive dimension have the same class exactly
when they are related by `RelStruct₀`. -/
lemma mk_eq_mk_iff {p q : X.PtSimplex (n + 1) x} :
    mk p = mk q ↔ Nonempty (p.RelStruct₀ q) := by
  refine Quot.eq.trans ⟨fun r ↦ ?_, fun ⟨h⟩ ↦ .rel _ _ ⟨h.symm.homotopy⟩⟩
  induction r with
  | rel p q h => exact ⟨PtSimplex.Homotopy.relStruct₀ h.some⟩
  | refl p => exact ⟨.refl _ _⟩
  | symm _ _ _ h => exact ⟨h.some.symm⟩
  | trans _ _ _ _ _ h₁ h₂ => exact ⟨h₁.some.trans h₂.some⟩

/-- In a Kan complex, two pointed simplices of positive dimension have the same class exactly
when they are homotopic. -/
lemma mk_eq_mk_iff_nonempty_homotopy {p q : X.PtSimplex (n + 1) x} :
    mk p = mk q ↔ Nonempty (p.Homotopy q) :=
  mk_eq_mk_iff.trans ⟨fun ⟨h⟩ ↦ ⟨h.symm.homotopy⟩, fun ⟨h⟩ ↦ ⟨h.relStruct₀⟩⟩

lemma mk_eq_one_iff (p : X.PtSimplex (n + 1) x) :
    mk p = 1 ↔ Nonempty (p.RelStruct₀ .const) :=
  mk_eq_mk_iff

namespace group

/-- A product of `p` and `q`, chosen using the Kan condition. -/
private noncomputable def mul' (p q : X.PtSimplex (n + 1) x) : X.PtSimplex (n + 1) x :=
  (PtSimplex.MulStruct.nonempty p q (Fin.last n)).choose

private noncomputable def mulStruct (p q : X.PtSimplex (n + 1) x) :
    PtSimplex.MulStruct p q (mul' p q) (Fin.last n) :=
  (PtSimplex.MulStruct.nonempty p q (Fin.last n)).choose_spec.some

/-- The multiplication on `π (n + 1) X x`. -/
private noncomputable def mul (a b : π (n + 1) X x) : π (n + 1) X x := by
  refine Quot.lift₂ (fun p q ↦ mk (mul' p q)) ?_ ?_ a b
  · rintro p q q' ⟨h : q.Homotopy q'⟩
    exact mk_eq_mk_iff.2 ⟨(mulStruct p q).unique (mulStruct p q') (.refl _ _) h.relStruct₀⟩
  · rintro p p' q ⟨h : p.Homotopy p'⟩
    exact mk_eq_mk_iff.2 ⟨(mulStruct p q).unique (mulStruct p' q) h.relStruct₀ (.refl _ _)⟩

private lemma mul_eq_of_mulStruct {p q pq : X.PtSimplex (n + 1) x}
    (h : PtSimplex.MulStruct p q pq (Fin.last n)) : mul (mk p) (mk q) = mk pq :=
  mk_eq_mk_iff.2 ⟨(mulStruct p q).unique h (.refl _ _) (.refl _ _)⟩

private lemma mul_assoc (a b c : π (n + 1) X x) : mul (mul a b) c = mul a (mul b c) := by
  induction a with | mk p
  induction b with | mk q
  induction c with | mk r
  exact mul_eq_of_mulStruct
    (PtSimplex.MulStruct.assoc (mulStruct p q) (mulStruct q r) (mulStruct p (mul' q r)))

private lemma one_mul (a : π (n + 1) X x) : mul 1 a = a := by
  induction a with | mk p => exact mul_eq_of_mulStruct (PtSimplex.MulStruct.oneMul p _)

private lemma mul_one (a : π (n + 1) X x) : mul a 1 = a := by
  induction a with | mk p => exact mul_eq_of_mulStruct (PtSimplex.MulStruct.mulOne p _)

private lemma exists_left_inverse (a : π (n + 1) X x) : ∃ b, mul b a = 1 := by
  induction a with | mk p
  obtain ⟨q, ⟨h⟩⟩ := PtSimplex.MulStruct.exists_left_inverse p (Fin.last n)
  exact ⟨_, mul_eq_of_mulStruct h⟩

end group

/-- The group structure on `π (n + 1) X x`, whose multiplication is given by `MulStruct` in the
last direction: `mk p * mk q = mk pq` exactly when there is a `MulStruct p q pq (Fin.last n)`
(`SSet.KanComplex.π.mul_mk_eq_iff`). -/
@[no_expose]
noncomputable instance group : Group (π (n + 1) X x) where
  mul := group.mul
  mul_assoc := group.mul_assoc
  one_mul := group.one_mul
  mul_one := group.mul_one
  inv a := (group.exists_left_inverse a).choose
  inv_mul_cancel a := (group.exists_left_inverse a).choose_spec

/-- The product `mk p * mk q` is `mk pq` exactly when `q`, `pq` and `p` are the faces `n`,
`n + 1` and `n + 2` of an `(n + 2)`-simplex whose other faces are constant. -/
lemma mul_mk_eq_iff {p q pq : X.PtSimplex (n + 1) x} :
    mk p * mk q = mk pq ↔ Nonempty (PtSimplex.MulStruct p q pq (Fin.last n)) :=
  ⟨fun h ↦ ⟨(group.mulStruct p q).unique' (mk_eq_mk_iff.1 h).some⟩,
    fun ⟨h⟩ ↦ group.mul_eq_of_mulStruct h⟩

/-- The inverse of `mk p` is `mk q` exactly when `mk p * mk q = 1` is witnessed by a
`MulStruct`. -/
lemma inv_mk_eq_iff {p q : X.PtSimplex (n + 1) x} :
    (mk p)⁻¹ = mk q ↔ Nonempty (PtSimplex.MulStruct p q .const (Fin.last n)) := by
  rw [inv_eq_iff_mul_eq_one, one_def, mul_mk_eq_iff]

section map

variable {Y : SSet.{u}} [KanComplex Y] {y : Y _⦋0⦌} (f : X ⟶ Y) (hy : f.app _ x = y)

/-- The map induced by a morphism of Kan complexes is multiplicative. -/
lemma map_mul (a b : π (n + 1) X x) : map f hy (a * b) = map f hy a * map f hy b := by
  induction a with | mk p
  induction b with | mk q
  obtain ⟨pq, ⟨h⟩⟩ := PtSimplex.MulStruct.nonempty p q (Fin.last n)
  rw [mul_mk_eq_iff.2 ⟨h⟩, map_mk, map_mk, map_mk, eq_comm, mul_mk_eq_iff]
  exact ⟨h.postcomp f hy⟩

/-- The group homomorphism `π (n + 1) X x →* π (n + 1) Y y` induced by a morphism of Kan
complexes sending `x` to `y`. -/
noncomputable def mapHom : π (n + 1) X x →* π (n + 1) Y y where
  toFun := map f hy
  map_one' := map_one f hy
  map_mul' := map_mul f hy

@[simp]
lemma mapHom_apply (a : π (n + 1) X x) : mapHom f hy a = map f hy a := (rfl)

end map

end π

end KanComplex

open KanComplex in
/-- A `MulStruct` in the last direction computes a product in the homotopy group. -/
lemma PtSimplex.MulStruct.mul_eq {X : SSet.{u}} [KanComplex X] {n : ℕ} {x : X _⦋0⦌}
    {p q pq : X.PtSimplex (n + 1) x} (h : PtSimplex.MulStruct p q pq (Fin.last n)) :
    π.mk p * π.mk q = π.mk pq :=
  π.mul_mk_eq_iff.2 ⟨h⟩

end SSet
