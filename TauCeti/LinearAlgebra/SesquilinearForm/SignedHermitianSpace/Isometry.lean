/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.SesquilinearForm.IsometryGroup
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Basic

/-!
# Isometries, orthogonal sums and nondegenerate subspaces of signed hermitian spaces

For signed hermitian spaces `(V₁, h₁)` and `(V₂, h₂)` over a commutative ring `K` with an
involution `σ`, of the same sign `ε`, this file defines the isometric equivalences between them,
their orthogonal sum on `V₁ × V₂`, and the signed hermitian space carried by a subspace on which
the form stays nondegenerate. These are the notions in which Witt cancellation
(`TauCeti/LinearAlgebra/SesquilinearForm/SignedHermitianSpace/Witt/Basic.lean`) is stated. The
unitary group `U(V)` of a signed hermitian space is the isometry group
`LinearMap.isometryGroup H.form` of its form; its elements are the isometric equivalences of `H`
with itself (`TauCeti.SignedHermitianSpace.IsometryEquiv.ofMemIsometryGroup`).

## Main definitions

* `TauCeti.SignedHermitianSpace.IsometryEquiv H₁ H₂`: a linear equivalence `V₁ ≃ V₂` carrying
  `h₁` to `h₂`; `TauCeti.SignedHermitianSpace.Equivalent H₁ H₂` says that one exists.
* `TauCeti.SignedHermitianSpace.prod H₁ H₂`: the orthogonal sum `H₁ ⊥ H₂` on `V₁ × V₂`.
* `TauCeti.SignedHermitianSpace.restrict H W hW`: the signed hermitian space carried by a
  submodule `W` on which the restricted form is left-separating.

## Main statements

* `TauCeti.SignedHermitianSpace.separatingLeft_domRestrict_iff`: the form restricted to `W` is
  left-separating exactly when `W` meets its orthogonal only in `0`.
* `TauCeti.SignedHermitianSpace.Equivalent.prod`: orthogonal sums of equivalent spaces are
  equivalent.

## Attribution

`TauCeti.SignedHermitianSpace.IsometryEquiv` and `TauCeti.SignedHermitianSpace.Equivalent`, with
their API (`refl`, `symm`, `trans`, the `EquivLike` instance and `map_app`), are modelled on
Mathlib's `QuadraticMap.IsometryEquiv` and `QuadraticMap.Equivalent`
(`Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv`), here for sesquilinear forms of a fixed sign.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

variable {K V V₁ V₂ V₃ V₄ : Type*} [CommRing K] {σ : K →+* K} {ε : ℤˣ}
  [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃] [AddCommGroup V₄] [Module K V₄]

/-! ### Isometric equivalences -/

/-- An **isometric equivalence** between signed hermitian spaces `(V₁, h₁)` and `(V₂, h₂)` of the
same sign: a linear equivalence `f : V₁ ≃ V₂` with `h₂ (f x) (f y) = h₁ x y`. -/
structure IsometryEquiv (H₁ : SignedHermitianSpace K V₁ σ ε) (H₂ : SignedHermitianSpace K V₂ σ ε)
    extends V₁ ≃ₗ[K] V₂ where
  /-- The equivalence carries the first form to the second. -/
  map_app' : ∀ x y, H₂.form (toFun x) (toFun y) = H₁.form x y

/-- Two signed hermitian spaces are **equivalent** (isometric) if there is an isometric
equivalence between them. -/
def Equivalent (H₁ : SignedHermitianSpace K V₁ σ ε) (H₂ : SignedHermitianSpace K V₂ σ ε) :
    Prop :=
  Nonempty (IsometryEquiv H₁ H₂)

namespace IsometryEquiv

variable {H : SignedHermitianSpace K V σ ε} {H₁ : SignedHermitianSpace K V₁ σ ε}
  {H₂ : SignedHermitianSpace K V₂ σ ε} {H₃ : SignedHermitianSpace K V₃ σ ε}

instance : EquivLike (IsometryEquiv H₁ H₂) V₁ V₂ where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

instance : LinearEquivClass (IsometryEquiv H₁ H₂) K V₁ V₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

@[simp]
theorem coe_toLinearEquiv (f : IsometryEquiv H₁ H₂) : ⇑f.toLinearEquiv = f :=
  (rfl)

@[ext]
theorem ext {f g : IsometryEquiv H₁ H₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- An isometric equivalence carries the first form to the second. -/
@[simp]
theorem map_app (f : IsometryEquiv H₁ H₂) (x y : V₁) : H₂.form (f x) (f y) = H₁.form x y :=
  f.map_app' x y

/-- The identity isometric equivalence of a signed hermitian space. -/
@[refl]
def refl (H : SignedHermitianSpace K V σ ε) : IsometryEquiv H H :=
  { LinearEquiv.refl K V with map_app' := fun _ _ ↦ rfl }

/-- The inverse of an isometric equivalence. -/
@[symm]
def symm (f : IsometryEquiv H₁ H₂) : IsometryEquiv H₂ H₁ :=
  { f.toLinearEquiv.symm with
    map_app' := fun x y ↦ by
      rw [← f.map_app]
      simp only [LinearEquiv.toFun_eq_coe]
      congr 2 <;> exact f.toLinearEquiv.apply_symm_apply _ }

/-- The composition of two isometric equivalences. -/
@[trans]
def trans (f : IsometryEquiv H₁ H₂) (g : IsometryEquiv H₂ H₃) : IsometryEquiv H₁ H₃ :=
  { f.toLinearEquiv.trans g.toLinearEquiv with
    map_app' := fun x y ↦ (g.map_app _ _).trans (f.map_app x y) }

@[simp]
theorem refl_apply (x : V) : refl H x = x :=
  (rfl)

@[simp]
theorem symm_apply_apply (f : IsometryEquiv H₁ H₂) (x : V₁) : f.symm (f x) = x :=
  f.toLinearEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (f : IsometryEquiv H₁ H₂) (x : V₂) : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x

theorem symm_apply_eq (f : IsometryEquiv H₁ H₂) {x : V₂} {y : V₁} : f.symm x = y ↔ x = f y :=
  f.toLinearEquiv.symm_apply_eq

theorem eq_symm_apply (f : IsometryEquiv H₁ H₂) {x : V₂} {y : V₁} : y = f.symm x ↔ f y = x :=
  f.toLinearEquiv.eq_symm_apply

@[simp]
theorem toLinearEquiv_symm (f : IsometryEquiv H₁ H₂) :
    f.symm.toLinearEquiv = f.toLinearEquiv.symm :=
  (rfl)

@[simp]
theorem coe_symm_toLinearEquiv (f : IsometryEquiv H₁ H₂) : ⇑f.toLinearEquiv.symm = f.symm :=
  (rfl)

@[simp]
theorem trans_apply (f : IsometryEquiv H₁ H₂) (g : IsometryEquiv H₂ H₃) (x : V₁) :
    f.trans g x = g (f x) :=
  (rfl)

/-- An element of the unitary group `U(V)`, the isometry group of the form, as an isometric
equivalence of the space with itself. -/
def ofMemIsometryGroup {e : V ≃ₗ[K] V} (he : e ∈ H.form.isometryGroup) : IsometryEquiv H H :=
  { e with map_app' := LinearMap.mem_isometryGroup_iff.1 he }

@[simp]
theorem ofMemIsometryGroup_apply {e : V ≃ₗ[K] V} (he : e ∈ H.form.isometryGroup) (x : V) :
    ofMemIsometryGroup he x = e x :=
  (rfl)

/-- The linear equivalence underlying an isometric equivalence of a space with itself lies in the
unitary group of the space. -/
theorem toLinearEquiv_mem_isometryGroup (f : IsometryEquiv H H) :
    f.toLinearEquiv ∈ H.form.isometryGroup :=
  LinearMap.mem_isometryGroup_iff.2 f.map_app

end IsometryEquiv

section Equivalent

variable {H₁ : SignedHermitianSpace K V₁ σ ε} {H₂ : SignedHermitianSpace K V₂ σ ε}
  {H₃ : SignedHermitianSpace K V₃ σ ε}

/-- Two signed hermitian spaces are equivalent exactly when there is an isometric equivalence
between them. -/
theorem equivalent_iff_nonempty_isometryEquiv :
    Equivalent H₁ H₂ ↔ Nonempty (IsometryEquiv H₁ H₂) :=
  Iff.rfl

/-- An isometric equivalence witnesses that the two spaces are equivalent. -/
theorem IsometryEquiv.equivalent (f : IsometryEquiv H₁ H₂) : Equivalent H₁ H₂ :=
  ⟨f⟩

/-- Choose an isometric equivalence between two equivalent spaces. -/
theorem Equivalent.nonempty (h : Equivalent H₁ H₂) : Nonempty (IsometryEquiv H₁ H₂) :=
  h

end Equivalent

namespace Equivalent

variable {H₁ : SignedHermitianSpace K V₁ σ ε} {H₂ : SignedHermitianSpace K V₂ σ ε}
  {H₃ : SignedHermitianSpace K V₃ σ ε}

@[refl]
theorem refl (H : SignedHermitianSpace K V σ ε) : Equivalent H H :=
  ⟨IsometryEquiv.refl H⟩

@[symm]
theorem symm (h : Equivalent H₁ H₂) : Equivalent H₂ H₁ :=
  h.elim fun f ↦ ⟨f.symm⟩

@[trans]
theorem trans (h : Equivalent H₁ H₂) (h' : Equivalent H₂ H₃) : Equivalent H₁ H₃ :=
  h.elim fun f ↦ h'.elim fun g ↦ ⟨f.trans g⟩

end Equivalent

/-! ### Orthogonal sums -/

/-- The **orthogonal sum** `H₁ ⊥ H₂` of two signed hermitian spaces of the same sign: the module
`V₁ × V₂` with the form `h ((x₁, x₂), (y₁, y₂)) = h₁ x₁ y₁ + h₂ x₂ y₂`. -/
def prod (H₁ : SignedHermitianSpace K V₁ σ ε) (H₂ : SignedHermitianSpace K V₂ σ ε) :
    SignedHermitianSpace K (V₁ × V₂) σ ε where
  form := (H₁.form.comp (LinearMap.fst K V₁ V₂)).compl₂ (LinearMap.fst K V₁ V₂) +
    (H₂.form.comp (LinearMap.snd K V₁ V₂)).compl₂ (LinearMap.snd K V₁ V₂)
  form_swap x y := by simp [H₁.form_swap x.1, H₂.form_swap x.2, smul_add]
  separatingLeft x hx := Prod.ext
    (H₁.separatingLeft x.1 fun y ↦ by simpa using hx (y, 0))
    (H₂.separatingLeft x.2 fun y ↦ by simpa using hx (0, y))

@[simp]
theorem prod_form_apply (H₁ : SignedHermitianSpace K V₁ σ ε)
    (H₂ : SignedHermitianSpace K V₂ σ ε) (x y : V₁ × V₂) :
    (H₁.prod H₂).form x y = H₁.form x.1 y.1 + H₂.form x.2 y.2 :=
  (rfl)

/-- The orthogonal sum of two isometric equivalences. -/
def IsometryEquiv.prod {H₁ : SignedHermitianSpace K V₁ σ ε} {H₂ : SignedHermitianSpace K V₂ σ ε}
    {H₃ : SignedHermitianSpace K V₃ σ ε} {H₄ : SignedHermitianSpace K V₄ σ ε}
    (f : IsometryEquiv H₁ H₃) (g : IsometryEquiv H₂ H₄) :
    IsometryEquiv (H₁.prod H₂) (H₃.prod H₄) :=
  { f.toLinearEquiv.prodCongr g.toLinearEquiv with
    map_app' := fun x y ↦ by simp }

@[simp]
theorem IsometryEquiv.prod_apply {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} {H₃ : SignedHermitianSpace K V₃ σ ε}
    {H₄ : SignedHermitianSpace K V₄ σ ε} (f : IsometryEquiv H₁ H₃) (g : IsometryEquiv H₂ H₄)
    (x : V₁ × V₂) : f.prod g x = (f x.1, g x.2) :=
  (rfl)

/-- Orthogonal sums of equivalent spaces are equivalent. -/
theorem Equivalent.prod {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} {H₃ : SignedHermitianSpace K V₃ σ ε}
    {H₄ : SignedHermitianSpace K V₄ σ ε} (h : Equivalent H₁ H₃) (h' : Equivalent H₂ H₄) :
    Equivalent (H₁.prod H₂) (H₃.prod H₄) :=
  h.elim fun f ↦ h'.elim fun g ↦ ⟨f.prod g⟩

/-- The orthogonal sum is commutative: `H₁ ⊥ H₂ ≅ H₂ ⊥ H₁`. -/
def IsometryEquiv.prodComm (H₁ : SignedHermitianSpace K V₁ σ ε)
    (H₂ : SignedHermitianSpace K V₂ σ ε) : IsometryEquiv (H₁.prod H₂) (H₂.prod H₁) :=
  { LinearEquiv.prodComm K V₁ V₂ with
    map_app' := fun x y ↦ by simp [add_comm] }

@[simp]
theorem IsometryEquiv.prodComm_apply (H₁ : SignedHermitianSpace K V₁ σ ε)
    (H₂ : SignedHermitianSpace K V₂ σ ε) (x : V₁ × V₂) :
    IsometryEquiv.prodComm H₁ H₂ x = x.swap :=
  (rfl)

/-- The orthogonal sum is associative: `(H₁ ⊥ H₂) ⊥ H₃ ≅ H₁ ⊥ (H₂ ⊥ H₃)`. -/
def IsometryEquiv.prodAssoc (H₁ : SignedHermitianSpace K V₁ σ ε)
    (H₂ : SignedHermitianSpace K V₂ σ ε) (H₃ : SignedHermitianSpace K V₃ σ ε) :
    IsometryEquiv ((H₁.prod H₂).prod H₃) (H₁.prod (H₂.prod H₃)) :=
  { LinearEquiv.prodAssoc K V₁ V₂ V₃ with
    map_app' := fun x y ↦ by simp [add_assoc] }

@[simp]
theorem IsometryEquiv.prodAssoc_apply (H₁ : SignedHermitianSpace K V₁ σ ε)
    (H₂ : SignedHermitianSpace K V₂ σ ε) (H₃ : SignedHermitianSpace K V₃ σ ε)
    (x : (V₁ × V₂) × V₃) :
    IsometryEquiv.prodAssoc H₁ H₂ H₃ x = (x.1.1, (x.1.2, x.2)) :=
  (rfl)

/-! ### Isometric maps -/

/-- A linear map carrying the form of a signed hermitian space to the form of another is
injective, because the first form is nondegenerate. -/
theorem injective_of_form_apply_eq {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} {f : V₁ →ₗ[K] V₂}
    (hf : ∀ x y, H₂.form (f x) (f y) = H₁.form x y) : Function.Injective f :=
  (injective_iff_map_eq_zero f).2 fun x hx ↦ H₁.separatingLeft x fun y ↦ by
    rw [← hf, hx, map_zero, LinearMap.zero_apply]

/-! ### Nondegenerate subspaces -/

variable (H : SignedHermitianSpace K V σ ε)

/-- The form of a signed hermitian space restricted to a submodule `W` is left-separating exactly
when `W` meets its orthogonal `{v | ∀ w ∈ W, h w v = 0}` only in `0`. -/
theorem separatingLeft_domRestrict_iff (W : Submodule K V) :
    (H.form.domRestrict₁₂ W W).SeparatingLeft ↔ Disjoint W (W.orthogonalBilin H.form) := by
  rw [Submodule.disjoint_def]
  refine ⟨fun hW x hx hx' ↦ ?_, fun hW x hx ↦ Subtype.ext <| hW x x.property ?_⟩
  · refine congrArg Subtype.val (hW ⟨x, hx⟩ fun y ↦ ?_)
    exact H.isRefl _ _ ((Submodule.mem_orthogonalBilin).1 hx' y y.property)
  · exact (Submodule.mem_orthogonalBilin).2 fun y hy ↦ H.isRefl _ _ (hx ⟨y, hy⟩)

/-- The signed hermitian space carried by a submodule `W` on which the restricted form is
left-separating (equivalently, `W ⊓ Wᗮ = 0`, `separatingLeft_domRestrict_iff`). -/
def restrict (W : Submodule K V) (hW : (H.form.domRestrict₁₂ W W).SeparatingLeft) :
    SignedHermitianSpace K W σ ε where
  form := H.form.domRestrict₁₂ W W
  form_swap x y := H.form_swap x y
  separatingLeft := hW

@[simp]
theorem restrict_form_apply (W : Submodule K V) (hW : (H.form.domRestrict₁₂ W W).SeparatingLeft)
    (x y : W) : (H.restrict W hW).form x y = H.form x y :=
  (rfl)

end SignedHermitianSpace

end TauCeti
