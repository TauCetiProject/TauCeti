/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Option
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Group

/-!
# `G`-groups and the free `G`-group `G[X]`

Algebraic geometry over a group `G` studies equations with coefficients in `G`. An equation in the
variables `X` is an element of the free product `G[X] = G ∗ F(X)` of `G` with the free group on
`X`, and a solution in a group `H` receiving the coefficients through `ι : G →* H` is a point
`v : X → H` at which the evaluation `G[X] →* H` sends the equation to `1`.

A `G`-group is a group `H` with an injective homomorphism `G →* H`, and a `G`-homomorphism is a
homomorphism commuting with the coefficient maps. Quotients of `G[X]` (coordinate groups of
systems of equations) carry a coefficient map which need not be injective, so `G`-homomorphisms
and evaluation are set up here for arbitrary coefficient homomorphisms; the bundled `GGroup` adds
injectivity.

## Main definitions

* `TauCeti.GroupAlgGeom.GGroup`: a group with an embedding of `G`.
* `TauCeti.GroupAlgGeom.GHom ιH ιK`: homomorphisms `H →* K` with `φ ∘ ιH = ιK`.
* `TauCeti.GroupAlgGeom.GX G X`: the free `G`-group `G[X] = Monoid.Coprod G (FreeGroup X)`.
* `TauCeti.GroupAlgGeom.eval ι v`: evaluation `G[X] →* H` at a point `v : X → H`.
* `TauCeti.GroupAlgGeom.homEquiv ι`: `G[X]` is free on `X` among groups under `G`:
  `G`-homomorphisms `G[X] → H` correspond to points `X → H`.

## Main results

* `MonoidHom.comp_eval`, `TauCeti.GroupAlgGeom.map_eval`: homomorphisms and `G`-homomorphisms
  commute with evaluation.
* `TauCeti.GroupAlgGeom.GX.equivOfIsEmpty`, `TauCeti.GroupAlgGeom.GX.equivFreeGroup`: `G[∅] ≅ G`
  and, for trivial `G`, `G[X] ≅ F(X)`, under which evaluation is `FreeGroup.lift`.
* `TauCeti.GroupAlgGeom.GX.not_commute_inl_inr_of`: a nontrivial coefficient does not commute
  with a variable, so the inclusions of `G` and `F(X)` do not commute in `G[X]`.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §§1–2.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.2.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod

universe u v

variable {G H K L : Type*} [Group G] [Group H] [Group K] [Group L]

/-! ### `G`-homomorphisms -/

/-- A `G`-homomorphism between groups receiving `G` through `ιH` and `ιK`: a homomorphism
`φ : H →* K` with `φ ∘ ιH = ιK`. -/
structure GHom (ιH : G →* H) (ιK : G →* K) extends H →* K where
  /-- A `G`-homomorphism fixes the coefficients. -/
  map_coeff' : ∀ g, toFun (ιH g) = ιK g

/-- Reinterpret a `G`-homomorphism as a monoid homomorphism. -/
add_decl_doc GHom.toMonoidHom

namespace GHom

variable {ιH : G →* H} {ιK : G →* K} {ιL : G →* L}

instance : FunLike (GHom ιH ιK) H K where
  coe φ := φ.toFun
  coe_injective φ ψ h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := φ
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := ψ
    congr

instance : MonoidHomClass (GHom ιH ιK) H K where
  map_mul φ := φ.map_mul'
  map_one φ := φ.map_one'

@[simp]
theorem toMonoidHom_eq_coe (φ : GHom ιH ιK) : φ.toMonoidHom = (φ : H →* K) := rfl

@[simp]
theorem coe_mk (φ : H →* K) (h : ∀ g, φ.toFun (ιH g) = ιK g) : ⇑(⟨φ, h⟩ : GHom ιH ιK) = φ :=
  rfl

@[ext]
theorem ext {φ ψ : GHom ιH ιK} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext _ _ h

@[simp]
theorem map_coeff (φ : GHom ιH ιK) (g : G) : φ (ιH g) = ιK g :=
  φ.map_coeff' g

@[simp]
theorem comp_coeff (φ : GHom ιH ιK) : (φ : H →* K).comp ιH = ιK :=
  MonoidHom.ext φ.map_coeff

variable (ιH) in
/-- The identity `G`-homomorphism. -/
protected def id : GHom ιH ιH where
  toMonoidHom := .id H
  map_coeff' _ := rfl

@[simp]
theorem coe_id : ⇑(GHom.id ιH) = id := (rfl)

/-- The composite of two `G`-homomorphisms. -/
def comp (ψ : GHom ιK ιL) (φ : GHom ιH ιK) : GHom ιH ιL where
  toMonoidHom := ψ.toMonoidHom.comp φ.toMonoidHom
  map_coeff' g := by simp

@[simp]
theorem coe_comp (ψ : GHom ιK ιL) (φ : GHom ιH ιK) : ⇑(ψ.comp φ) = ψ ∘ φ := (rfl)

@[simp]
theorem id_comp (φ : GHom ιH ιK) : (GHom.id ιK).comp φ = φ := (rfl)

@[simp]
theorem comp_id (φ : GHom ιH ιK) : φ.comp (GHom.id ιH) = φ := (rfl)

variable {M : Type*} [Group M] {ιM : G →* M} in
theorem comp_assoc (χ : GHom ιL ιM) (ψ : GHom ιK ιL) (φ : GHom ιH ιK) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := (rfl)

/-- The inverse of a bijective coefficient-preserving homomorphism preserves coefficients. -/
noncomputable def symmOfBijective (φ : GHom ιH ιK) (hφ : Function.Bijective φ) :
    GHom ιK ιH where
  toMonoidHom := (MulEquiv.ofBijective φ.toMonoidHom hφ).symm.toMonoidHom
  map_coeff' g := by
    apply hφ.1
    rw [φ.map_coeff g]
    exact MulEquiv.ofBijective_apply_symm_apply φ.toMonoidHom hφ

@[simp]
theorem apply_symmOfBijective (φ : GHom ιH ιK) (hφ : Function.Bijective φ) (x : K) :
    φ (φ.symmOfBijective hφ x) = x := by
  exact MulEquiv.ofBijective_apply_symm_apply φ.toMonoidHom hφ

@[simp]
theorem symmOfBijective_apply (φ : GHom ιH ιK) (hφ : Function.Bijective φ) (x : H) :
    φ.symmOfBijective hφ (φ x) = x := by
  exact (MulEquiv.ofBijective φ.toMonoidHom hφ).symm_apply_apply x

@[simp]
theorem comp_symmOfBijective (φ : GHom ιH ιK) (hφ : Function.Bijective φ) :
    φ.comp (φ.symmOfBijective hφ) = GHom.id ιK := by
  ext x
  exact φ.apply_symmOfBijective hφ x

@[simp]
theorem symmOfBijective_comp (φ : GHom ιH ιK) (hφ : Function.Bijective φ) :
    (φ.symmOfBijective hφ).comp φ = GHom.id ιH := by
  ext x
  exact φ.symmOfBijective_apply hφ x

end GHom

/-! ### `G`-groups -/

/-- A `G`-group: a group together with an injective homomorphism from `G`, its coefficients.
Homomorphisms between `G`-groups `H` and `K` are `GHom H.coeff K.coeff`. -/
structure GGroup (G : Type u) [Group G] where
  /-- The underlying type. -/
  carrier : Type v
  [instGroup : Group carrier]
  /-- The coefficient embedding. -/
  coeff : G →* carrier
  coeff_injective : Function.Injective coeff

namespace GGroup

variable {G : Type u} [Group G]

instance : CoeSort (GGroup.{u, v} G) (Type v) := ⟨carrier⟩

attribute [instance] instGroup

/-- `G` is a `G`-group through the identity. -/
@[expose] def self (G : Type u) [Group G] : GGroup.{u, u} G :=
  ⟨G, .id G, Function.injective_id⟩

@[simp]
theorem coeff_self : (self G).coeff = .id G := rfl

end GGroup

/-! ### The free `G`-group `G[X]` and evaluation -/

variable (G) in
/-- The free `G`-group `G[X] = G ∗ F(X)` on a type of variables `X`; its coefficients are the left
inclusion `Monoid.Coprod.inl`, and the variable `x` is `inr (FreeGroup.of x)`. Its elements are
the equations over `G` in the variables `X`. -/
abbrev GX (X : Type*) : Type _ := Monoid.Coprod G (FreeGroup X)

variable {X : Type*}

variable (G X) in
/-- `G[X]` as a `G`-group. -/
@[expose] def GGroup.free : GGroup G := ⟨GX G X, inl, inl_injective⟩

@[simp]
theorem GGroup.coeff_free : (GGroup.free G X).coeff = inl := rfl

/-- Evaluation `w ↦ w(v)` of `G[X]` at a point `v : X → H`, for a group `H` receiving the
coefficients through `ι`: coefficients go to their images under `ι` and the variable `x` goes
to `v x`. -/
def eval (ι : G →* H) (v : X → H) : GX G X →* H :=
  lift ι (FreeGroup.lift v)

variable (ι : G →* H) (v : X → H)

@[simp]
theorem eval_inl (g : G) : eval ι v (inl g) = ι g :=
  lift_apply_inl _ _ g

@[simp]
theorem eval_inr (w : FreeGroup X) : eval ι v (inr w) = FreeGroup.lift v w :=
  lift_apply_inr _ _ w

theorem eval_inr_of (x : X) : eval ι v (inr (FreeGroup.of x)) = v x := by
  simp

@[simp]
theorem eval_comp_inl : (eval ι v).comp inl = ι :=
  MonoidHom.ext (eval_inl ι v)

@[simp]
theorem eval_comp_inr : (eval ι v).comp inr = FreeGroup.lift v :=
  MonoidHom.ext (eval_inr ι v)

/-- Evaluating at the generic point, the tuple of variables of `G[X]`, is the identity. -/
@[simp]
theorem eval_inl_inr_of : eval (inl : G →* GX G X) (fun x => inr (FreeGroup.of x)) = .id _ :=
  hom_ext (by simp) (FreeGroup.ext_hom _ _ fun _ => by simp)

/-- A homomorphism out of `G[X]` is determined by its restriction to the coefficients and its
values on the variables: it is evaluation at those values. -/
theorem eq_eval (f : GX G X →* H) : f = eval (f.comp inl) (fun x => f (inr (FreeGroup.of x))) :=
  hom_ext (by simp) (FreeGroup.ext_hom _ _ fun _ => by simp)

/-- Evaluation as a `G`-homomorphism from the free `G`-group `G[X]`. -/
def evalGHom : GHom (inl : G →* GX G X) ι where
  toMonoidHom := eval ι v
  map_coeff' := eval_inl ι v

@[simp]
theorem coe_evalGHom : ⇑(evalGHom ι v) = eval ι v := (rfl)

/-- `G[X]` is the free `G`-group on `X`: `G`-homomorphisms `G[X] → H` correspond to points
`X → H`, by restriction to the variables and by evaluation. -/
def homEquiv : GHom (inl : G →* GX G X) ι ≃ (X → H) where
  toFun φ x := φ (inr (FreeGroup.of x))
  invFun v := evalGHom ι v
  left_inv φ := by
    refine GHom.ext fun w => ?_
    simpa using (DFunLike.congr_fun (eq_eval (φ : GX G X →* H)) w).symm
  right_inv v := funext fun x => eval_inr_of ι v x

@[simp]
theorem homEquiv_apply (φ : GHom (inl : G →* GX G X) ι) (x : X) :
    homEquiv ι φ x = φ (inr (FreeGroup.of x)) := (rfl)

@[simp]
theorem homEquiv_symm_apply : (homEquiv ι).symm v = evalGHom ι v := (rfl)

/-- A `G`-homomorphism out of `G[X]` is determined by its values on the variables. -/
@[ext]
theorem GX.gHom_ext {φ ψ : GHom (inl : G →* GX G X) ι}
    (h : ∀ x, φ (inr (FreeGroup.of x)) = ψ (inr (FreeGroup.of x))) : φ = ψ :=
  (homEquiv ι).injective (funext h)

variable {ι v}

/-- A homomorphism out of `G[X]` that restricts to `ι` on the coefficients is evaluation at its
values on the variables. -/
theorem eval_eq_of_comp_inl {f : GX G X →* H} (hf : f.comp inl = ι) :
    eval ι (fun x => f (inr (FreeGroup.of x))) = f :=
  hf ▸ (eq_eval f).symm

/-- Homomorphisms commute with evaluation: `f ∘ eval ι v = eval (f ∘ ι) (f ∘ v)`. -/
theorem _root_.MonoidHom.comp_eval (f : H →* K) {ι : G →* H} {v : X → H} :
    f.comp (eval ι v) = eval (f.comp ι) (f ∘ v) :=
  hom_ext (by simp [MonoidHom.comp_assoc]) (FreeGroup.ext_hom _ _ fun _ => by simp)

/-- Homomorphisms commute with evaluation: `f (w(v)) = w(f ∘ v)`, the coefficients being moved
along `f`. -/
theorem hom_eval {F : Type*} [FunLike F H K] [MonoidHomClass F H K] (f : F) (w : GX G X) :
    f (eval ι v w) = eval ((f : H →* K).comp ι) (f ∘ v) w :=
  DFunLike.congr_fun (f : H →* K).comp_eval w

/-- `G`-homomorphisms commute with evaluation, as homomorphisms out of `G[X]`. -/
theorem comp_eval {ιK : G →* K} (φ : GHom ι ιK) :
    (φ : H →* K).comp (eval ι v) = eval ιK (φ ∘ v) := by
  rw [MonoidHom.comp_eval, φ.comp_coeff, MonoidHom.coe_ofClass]

/-- `G`-homomorphisms commute with evaluation: `φ (w(v)) = w(φ ∘ v)`. -/
@[simp]
theorem map_eval {ιK : G →* K} (φ : GHom ι ιK) (w : GX G X) :
    φ (eval ι v w) = eval ιK (φ ∘ v) w :=
  DFunLike.congr_fun (comp_eval φ) w

/-- Changing the coefficients along `f : K →* G` and renaming the variables along `e : Y → X`
before evaluating at `v` is evaluation at `v ∘ e` with coefficients `ι ∘ f`. -/
theorem eval_comp_map {Y : Type*} (f : K →* G) (e : Y → X) :
    (eval ι v).comp (Monoid.Coprod.map f (FreeGroup.map e)) = eval (ι.comp f) (v ∘ e) :=
  hom_ext (MonoidHom.ext fun _ => by simp) (FreeGroup.ext_hom _ _ fun _ => by simp)

@[simp]
theorem eval_map {Y : Type*} (f : K →* G) (e : Y → X) (w : GX K Y) :
    eval ι v (Monoid.Coprod.map f (FreeGroup.map e) w) = eval (ι.comp f) (v ∘ e) w :=
  DFunLike.congr_fun (eval_comp_map f e) w

/-! ### Degenerate cases and noncommutativity of `G[X]` -/

namespace GX

/-- With no variables, `G[X]` is `G`. -/
def equivOfIsEmpty [IsEmpty X] : GX G X ≃* G :=
  (MulEquiv.coprodCongr (.refl G) (MulEquiv.ofUnique (N := PUnit.{1}))).trans
    (MulEquiv.coprodPUnit G)

@[simp]
theorem equivOfIsEmpty_apply [IsEmpty X] (w : GX G X) : equivOfIsEmpty w = fst w := by
  induction w using induction_on with
  | inl g => simp [equivOfIsEmpty]
  | inr w => simp [Subsingleton.elim w 1]
  | mul x y hx hy => simp [hx, hy]

@[simp]
theorem equivOfIsEmpty_symm_apply [IsEmpty X] (g : G) :
    (equivOfIsEmpty (X := X)).symm g = inl g := by
  simp [MulEquiv.symm_apply_eq]

variable (G X) in
/-- Over trivial coefficients, `G[X]` is the free group `F(X)`. -/
def equivFreeGroup [Subsingleton G] : GX G X ≃* FreeGroup X :=
  letI := uniqueOfSubsingleton (1 : G)
  (MulEquiv.coprodCongr (MulEquiv.ofUnique (N := PUnit.{1})) (.refl _)).trans
    (MulEquiv.punitCoprod (FreeGroup X))

@[simp]
theorem equivFreeGroup_apply [Subsingleton G] (w : GX G X) : equivFreeGroup G X w = snd w := by
  induction w using induction_on with
  | inl g => simp [Subsingleton.elim g 1]
  | inr w => simp [equivFreeGroup]
  | mul x y hx hy => simp [hx, hy]

@[simp]
theorem equivFreeGroup_symm_apply [Subsingleton G] (w : FreeGroup X) :
    (equivFreeGroup G X).symm w = inr w := by
  simp [MulEquiv.symm_apply_eq]

/-- Over trivial coefficients, evaluation is `FreeGroup.lift` through `G[X] ≅ F(X)`. -/
theorem eval_eq_lift_equivFreeGroup [Subsingleton G] (ι : G →* H) (v : X → H) (w : GX G X) :
    eval ι v w = FreeGroup.lift v (equivFreeGroup G X w) := by
  have : eval ι v = (FreeGroup.lift v).comp (equivFreeGroup G X).toMonoidHom :=
    hom_ext (MonoidHom.ext fun g => by simp [Subsingleton.elim g 1])
      (FreeGroup.ext_hom _ _ fun _ => by simp)
  exact DFunLike.congr_fun this w

/-- A nontrivial coefficient does not commute with a variable in `G[X]`; in particular the
inclusions of `G` and `F(X)` do not commute, unlike in the direct product `G × F(X)`. -/
theorem not_commute_inl_inr_of {a : G} (ha : a ≠ 1) (x : X) :
    ¬Commute (inl a : GX G X) (inr (FreeGroup.of x)) := by
  classical
  intro h
  -- Separate the two in the permutations of `Option G`: `G` acts by left multiplication on `G`,
  -- and the variable acts as the transposition of `none` and `some 1`.
  let f : GX G X →* Equiv.Perm (Option G) :=
    eval (MulAction.toPermHom G (Option G)) fun _ => Equiv.swap none (some 1)
  have := congrArg (fun σ : Equiv.Perm (Option G) => σ none) (congrArg f h.eq)
  exact ha (by simpa [f] using this)

end GX

/-! ### Examples -/

section Examples

open FreeGroup

/-- Over `G = F(a, b)` with one variable `x`, the commutator `x a x⁻¹ a⁻¹` vanishes at `x = a²`
but not at `x = b`. -/
theorem eval_commutator :
    let a : FreeGroup (Fin 2) := of 0
    let w : GX (FreeGroup (Fin 2)) Unit := inr (of ()) * inl a * (inr (of ()))⁻¹ * (inl a)⁻¹
    eval (.id _) (fun _ => a ^ 2) w = 1 ∧ eval (.id _) (fun _ => of 1) w ≠ 1 := by
  simp only [_root_.map_mul, _root_.map_inv, eval_inl, eval_inr, lift_apply_of, MonoidHom.id_apply]
  exact ⟨by group, by decide⟩

end Examples

end TauCeti.GroupAlgGeom
