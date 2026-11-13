/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Basic
public import Mathlib.Algebra.Ring.Equiv

/-!
# Homomorphisms of coefficient semifields

A homomorphism of coefficient semifields is a group homomorphism that also preserves the
auxiliary addition. These are the maps along which the coefficients of a cluster algebra are
specialized: a homomorphism `P → Q` carries the coefficient mutation rule over `P` to the one
over `Q`.

## Main declarations

* `TauCeti.CoefficientSemifieldHom`: the bundled homomorphisms, with their `MonoidHomClass` and
  `AddHomClass` instances, identity and composition.
* `TauCeti.CoefficientSemifieldHom.fst`, `TauCeti.CoefficientSemifieldHom.snd` and
  `TauCeti.CoefficientSemifieldHom.prod`: the projections of a binary product and the
  homomorphism into it determined by its two components.
* `TauCeti.CoefficientSemifieldHom.eval` and `TauCeti.CoefficientSemifieldHom.pi`: the same for
  indexed products.
* The `Unique` instance for homomorphisms into the one-element coefficient semifield, which is
  therefore terminal.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  §2.
-/

public section

universe u

namespace TauCeti

/-- A homomorphism of coefficient semifields is a group homomorphism that preserves the
auxiliary addition. -/
structure CoefficientSemifieldHom (P Q : Type*) [CoefficientSemifield P]
    [CoefficientSemifield Q] extends P →* Q, P →ₙ+ Q

/-- Reinterpret a homomorphism of coefficient semifields as a homomorphism for the auxiliary
addition alone. -/
add_decl_doc CoefficientSemifieldHom.toAddHom

namespace CoefficientSemifieldHom

variable {P Q R S : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]
  [CoefficientSemifield R] [CoefficientSemifield S]

instance : FunLike (CoefficientSemifieldHom P Q) P Q where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

instance : MonoidHomClass (CoefficientSemifieldHom P Q) P Q where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

instance : AddHomClass (CoefficientSemifieldHom P Q) P Q where
  map_add f := f.map_add'

@[ext]
theorem ext {f g : CoefficientSemifieldHom P Q} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_mk (f : P →* Q) (h : ∀ x y, f (x + y) = f x + f y) :
    ⇑(CoefficientSemifieldHom.mk f h) = f :=
  (rfl)

@[simp]
theorem coe_toMonoidHom (f : CoefficientSemifieldHom P Q) : ⇑f.toMonoidHom = f :=
  (rfl)

theorem coe_toAddHom (f : CoefficientSemifieldHom P Q) : ⇑f.toAddHom = f :=
  (rfl)

variable (P) in
/-- The identity homomorphism of a coefficient semifield. -/
protected def id : CoefficientSemifieldHom P P :=
  { MonoidHom.id P, AddHom.id P with }

@[simp]
theorem coe_id : ⇑(CoefficientSemifieldHom.id P) = id :=
  (rfl)

theorem id_apply (x : P) : CoefficientSemifieldHom.id P x = x :=
  (rfl)

/-- The composition of two homomorphisms of coefficient semifields. -/
def comp (g : CoefficientSemifieldHom Q R) (f : CoefficientSemifieldHom P Q) :
    CoefficientSemifieldHom P R :=
  { g.toMonoidHom.comp f.toMonoidHom, g.toAddHom.comp f.toAddHom with }

@[simp]
theorem coe_comp (g : CoefficientSemifieldHom Q R) (f : CoefficientSemifieldHom P Q) :
    ⇑(g.comp f) = g ∘ f :=
  (rfl)

theorem comp_apply (g : CoefficientSemifieldHom Q R) (f : CoefficientSemifieldHom P Q) (x : P) :
    g.comp f x = g (f x) :=
  (rfl)

@[simp]
theorem comp_id (f : CoefficientSemifieldHom P Q) : f.comp (CoefficientSemifieldHom.id P) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : CoefficientSemifieldHom P Q) : (CoefficientSemifieldHom.id Q).comp f = f :=
  ext fun _ => rfl

theorem comp_assoc (h : CoefficientSemifieldHom R S) (g : CoefficientSemifieldHom Q R)
    (f : CoefficientSemifieldHom P Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

/-! ### Binary products -/

section Prod

variable (P Q) in
/-- The first projection of a product of coefficient semifields. -/
def fst : CoefficientSemifieldHom (P × Q) P :=
  { MonoidHom.fst P Q with map_add' := fun _ _ => rfl }

variable (P Q) in
/-- The second projection of a product of coefficient semifields. -/
def snd : CoefficientSemifieldHom (P × Q) Q :=
  { MonoidHom.snd P Q with map_add' := fun _ _ => rfl }

@[simp]
theorem coe_fst : ⇑(fst P Q) = Prod.fst :=
  (rfl)

@[simp]
theorem coe_snd : ⇑(snd P Q) = Prod.snd :=
  (rfl)

/-- The homomorphism into a product of coefficient semifields with components `f` and `g`. -/
protected def prod (f : CoefficientSemifieldHom P Q) (g : CoefficientSemifieldHom P R) :
    CoefficientSemifieldHom P (Q × R) :=
  { f.toMonoidHom.prod g.toMonoidHom with
    map_add' := fun x y => Prod.ext (map_add f x y) (map_add g x y) }

@[simp]
theorem prod_apply (f : CoefficientSemifieldHom P Q) (g : CoefficientSemifieldHom P R) (x : P) :
    f.prod g x = (f x, g x) :=
  (rfl)

@[simp]
theorem fst_comp_prod (f : CoefficientSemifieldHom P Q) (g : CoefficientSemifieldHom P R) :
    (fst Q R).comp (f.prod g) = f :=
  ext fun _ => rfl

@[simp]
theorem snd_comp_prod (f : CoefficientSemifieldHom P Q) (g : CoefficientSemifieldHom P R) :
    (snd Q R).comp (f.prod g) = g :=
  ext fun _ => rfl

/-- A homomorphism into a product is determined by its two components. -/
theorem prod_unique (f : CoefficientSemifieldHom P (Q × R)) :
    ((fst Q R).comp f).prod ((snd Q R).comp f) = f :=
  ext fun _ => rfl

end Prod

/-! ### Indexed products -/

section Pi

variable {ι : Type*} {A : ι → Type*} [∀ i, CoefficientSemifield (A i)]

variable (A) in
/-- Evaluation at an index, as a homomorphism from a product of coefficient semifields. -/
def eval (i : ι) : CoefficientSemifieldHom (∀ i, A i) (A i) :=
  { Pi.evalMonoidHom A i with map_add' := fun _ _ => rfl }

@[simp]
theorem eval_apply (i : ι) (x : ∀ i, A i) : eval A i x = x i :=
  (rfl)

/-- The homomorphism into a product of coefficient semifields with components `f i`. -/
protected def pi (f : ∀ i, CoefficientSemifieldHom P (A i)) :
    CoefficientSemifieldHom P (∀ i, A i) :=
  { MonoidHom.pi fun i => (f i).toMonoidHom with
    map_add' := fun x y => funext fun i => map_add (f i) x y }

@[simp]
theorem pi_apply (f : ∀ i, CoefficientSemifieldHom P (A i)) (x : P) (i : ι) :
    CoefficientSemifieldHom.pi f x i = f i x :=
  (rfl)

@[simp]
theorem eval_comp_pi (f : ∀ i, CoefficientSemifieldHom P (A i)) (i : ι) :
    (eval A i).comp (CoefficientSemifieldHom.pi f) = f i :=
  ext fun _ => rfl

/-- A homomorphism into an indexed product is determined by its components. -/
theorem pi_unique (f : CoefficientSemifieldHom P (∀ i, A i)) :
    (CoefficientSemifieldHom.pi fun i => (eval A i).comp f) = f :=
  ext fun _ => rfl

end Pi

/-! ### The terminal object -/

/-- There is exactly one homomorphism into the one-element coefficient semifield. -/
instance : Unique (CoefficientSemifieldHom P PUnit.{u + 1}) where
  default := { (1 : P →* PUnit.{u + 1}) with map_add' := fun _ _ => rfl }
  uniq _ := ext fun _ => rfl

end CoefficientSemifieldHom

end TauCeti

namespace RingEquiv

variable {P Q R : Type*} [TauCeti.CoefficientSemifield P]
  [TauCeti.CoefficientSemifield Q] [TauCeti.CoefficientSemifield R]

/-- An isomorphism preserving multiplication and auxiliary addition is a homomorphism of
coefficient semifields. -/
def toCoefficientSemifieldHom (e : P ≃+* Q) : TauCeti.CoefficientSemifieldHom P Q :=
  { MonoidHom.ofClass e, AddHomClass.toAddHom e with }

@[simp]
theorem coe_toCoefficientSemifieldHom (e : P ≃+* Q) :
    ⇑e.toCoefficientSemifieldHom = e :=
  (rfl)

@[simp]
theorem toCoefficientSemifieldHom_refl :
    (RingEquiv.refl P).toCoefficientSemifieldHom = TauCeti.CoefficientSemifieldHom.id P := by
  ext
  rfl

@[simp]
theorem toCoefficientSemifieldHom_trans (e : P ≃+* Q) (f : Q ≃+* R) :
    (e.trans f).toCoefficientSemifieldHom =
      f.toCoefficientSemifieldHom.comp e.toCoefficientSemifieldHom := by
  ext
  rfl

end RingEquiv
