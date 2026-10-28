/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The group structure on the translation orbit space of a submodule

A submodule `p` of a module `M` over a ring acts on `M` by translation, and the orbit space of this
action is the standard carrier `AddAction.orbitRel.Quotient p M` for quotients of `M` by
translations, for instance for a complex torus `E ⧸ Λ` built from a lattice `Λ` in a complex
vector space `E`. Two points lie in one orbit exactly when their difference lies in `p`, which is
also the relation defining the quotient module `M ⧸ p`.

This file transfers the additive group structure of `M ⧸ p` to the orbit space, so that the orbit
projection is additive, and records the resulting additive equivalence between the two quotients.
The orbit space of translation by a product `p.prod q` on `M × M₂` is additively equivalent to
the product of the orbit spaces of `p` and `q`.

For a linear map `f : M → M₂` and a submodule `q` of `M₂`, the image `f⁻¹(q) / p` of `f⁻¹(q)` in
the orbit space contains the image of `ker f`, and the quotient of the former by the latter is
`(q ∩ range f) / (q ∩ f(p))`, which is `(q ∩ range f) / f(p)` when `f(p) ⊆ q`. For lattices
`L ⊆ E`, `L' ⊆ E'` in complex vector spaces and a complex linear map `f` with `f(L) ⊆ L'`, this is
the component group of `f⁻¹(L') / L`, the kernel of the induced homomorphism of complex tori
`E / L → E' / L'`.

## Main declarations

* `Submodule.orbitRelQuotientAddEquiv`: the orbit space of translation by `p` is additively
  equivalent to the quotient module `M ⧸ p`, by an equivalence sending the orbit of `x` to the
  class of `x`.
* `Submodule.orbitRelQuotient_mk_add`, `Submodule.orbitRelQuotient_mk_zero`,
  `Submodule.orbitRelQuotient_mk_neg`, `Submodule.orbitRelQuotient_mk_sub`: the orbit projection
  is additive.
* `Submodule.orbitRelQuotient_mk_eq_zero_iff`: its kernel is `p`.
* `Submodule.orbitRelQuotientMkHom`: the orbit projection as an additive map.
* `Submodule.orbitRelQuotientProdAddEquiv`: the orbit space of translation by `p.prod q` is
  additively equivalent to the product of the orbit spaces of `p` and `q`.
* `Submodule.orbitRelQuotientComapQuotientEquiv`: the quotient of `f⁻¹(q) / p` by the image of
  `ker f` is additively equivalent to `(q ∩ range f) / (q ∩ f(p))`.
-/

public section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)

/-- Two points lie in one orbit of translation by a submodule `p` exactly when their difference
lies in `p`. -/
theorem Submodule.orbitRel_apply_iff_sub_mem {x y : M} :
    AddAction.orbitRel p M x y ↔ x - y ∈ p :=
  (QuotientAddGroup.rightRel_apply (s := p.toAddSubgroup)).trans <| by
    rw [← sub_eq_add_neg]; exact sub_mem_comm_iff

/-- The additive group structure on the orbit space of translation by `p`, transferred from the
quotient module `M ⧸ p`, which is the same quotient of `M`. -/
instance Submodule.instAddCommGroupOrbitRelQuotient :
    AddCommGroup (AddAction.orbitRel.Quotient p M) :=
  Equiv.addCommGroup (β := M ⧸ p) <|
    Quotient.congrRight fun _ _ ↦ p.orbitRel_apply_iff_sub_mem.trans p.quotientRel_def.symm

/-- The orbit space of translation by `p` is additively equivalent to the quotient module
`M ⧸ p`, by an equivalence sending the orbit of `x` to the class of `x`. -/
def Submodule.orbitRelQuotientAddEquiv : AddAction.orbitRel.Quotient p M ≃+ M ⧸ p :=
  Equiv.addEquiv (β := M ⧸ p) <|
    Quotient.congrRight fun _ _ ↦ p.orbitRel_apply_iff_sub_mem.trans p.quotientRel_def.symm

/-- `Submodule.orbitRelQuotientAddEquiv` sends the orbit of `x` to the class of `x`. -/
@[simp]
theorem Submodule.orbitRelQuotientAddEquiv_mk (x : M) :
    p.orbitRelQuotientAddEquiv (_root_.Quotient.mk (AddAction.orbitRel p M) x) =
      Submodule.Quotient.mk x :=
  (rfl)

/-- The inverse of `Submodule.orbitRelQuotientAddEquiv` sends the class of `x` to the orbit of
`x`. -/
@[simp]
theorem Submodule.orbitRelQuotientAddEquiv_symm_mk (x : M) :
    p.orbitRelQuotientAddEquiv.symm (Submodule.Quotient.mk x) =
      _root_.Quotient.mk (AddAction.orbitRel p M) x :=
  (rfl)

/-- The orbit projection for translation by `p` is additive. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_add (x y : M) :
    _root_.Quotient.mk (AddAction.orbitRel p M) (x + y) =
      _root_.Quotient.mk (AddAction.orbitRel p M) x +
        _root_.Quotient.mk (AddAction.orbitRel p M) y :=
  p.orbitRelQuotientAddEquiv.injective <| by simp

/-- The orbit projection for translation by `p` sends `0` to `0`. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_zero :
    _root_.Quotient.mk (AddAction.orbitRel p M) 0 = 0 :=
  p.orbitRelQuotientAddEquiv.injective <| by simp

/-- The orbit projection `M → AddAction.orbitRel.Quotient p M` for translation by `p`, as an
additive map. -/
def Submodule.orbitRelQuotientMkHom : M →+ AddAction.orbitRel.Quotient p M where
  toFun := _root_.Quotient.mk (AddAction.orbitRel p M)
  map_zero' := p.orbitRelQuotient_mk_zero
  map_add' := p.orbitRelQuotient_mk_add

/-- As a function, `Submodule.orbitRelQuotientMkHom` is the orbit projection. -/
@[simp]
theorem Submodule.coe_orbitRelQuotientMkHom :
    ⇑p.orbitRelQuotientMkHom = _root_.Quotient.mk (AddAction.orbitRel p M) :=
  (rfl)

/-- A point of `M` projects to `0` in the orbit space of translation by `p` exactly when it lies
in `p`. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_eq_zero_iff {x : M} :
    _root_.Quotient.mk (AddAction.orbitRel p M) x = 0 ↔ x ∈ p := by
  rw [← orbitRelQuotient_mk_zero, _root_.Quotient.eq, orbitRel_apply_iff_sub_mem, sub_zero]

/-- The kernel of the orbit projection for translation by `p` is `p`. -/
@[simp]
theorem Submodule.ker_orbitRelQuotientMkHom : p.orbitRelQuotientMkHom.ker = p.toAddSubgroup := by
  ext x
  simp

/-- The orbit projection for translation by `p` commutes with negation. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_neg (x : M) :
    _root_.Quotient.mk (AddAction.orbitRel p M) (-x) =
      -_root_.Quotient.mk (AddAction.orbitRel p M) x :=
  p.orbitRelQuotientAddEquiv.injective <| by simp

/-- The orbit projection for translation by `p` commutes with subtraction. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_sub (x y : M) :
    _root_.Quotient.mk (AddAction.orbitRel p M) (x - y) =
      _root_.Quotient.mk (AddAction.orbitRel p M) x -
        _root_.Quotient.mk (AddAction.orbitRel p M) y :=
  p.orbitRelQuotientAddEquiv.injective <| by simp

section Preimage

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] (q : Submodule R M₂) (f : M →ₗ[R] M₂)

/-- For a linear map `f : M → M₂` and submodules `p ≤ M`, `q ≤ M₂`, consider the image `K` of
`f⁻¹(q)` and the image `K₀` of `ker f` in the orbit space of translation by `p`. The quotient
`K / K₀` is additively equivalent to `(q ∩ range f) / (q ∩ f(p))`, by the map sending the class
of the orbit of `x ∈ f⁻¹(q)` to the class of `f x`. Here the denominator `q ∩ f(p)` is the
pullback of `f(p)` to `q ∩ range f`; it is `f(p)` itself when `f(p) ⊆ q`.

For lattices `L ⊆ E`, `L' ⊆ E'` and a complex linear map `f` with `f(L) ⊆ L'`, `K = f⁻¹(L') / L`
is the kernel of the induced homomorphism of complex tori `E / L → E' / L'`, `K₀` is its identity
component, and this is the description of its component group as `(L' ∩ range f) / f(L)`. -/
noncomputable def Submodule.orbitRelQuotientComapQuotientEquiv :
    (q.comap f).toAddSubgroup.map p.orbitRelQuotientMkHom ⧸
        ((LinearMap.ker f).toAddSubgroup.map p.orbitRelQuotientMkHom).addSubgroupOf
          ((q.comap f).toAddSubgroup.map p.orbitRelQuotientMkHom) ≃+
      ↥(q ⊓ LinearMap.range f) ⧸ (p.map f).comap (q ⊓ LinearMap.range f).subtype :=
  let K := (q.comap f).toAddSubgroup.map p.orbitRelQuotientMkHom
  let K₀ := ((LinearMap.ker f).toAddSubgroup.map p.orbitRelQuotientMkHom).addSubgroupOf K
  let N := (p.map f).comap (q ⊓ LinearMap.range f).subtype
  -- Both sides are quotients of `f⁻¹(q)`: by `σ`, through the orbit projection, and by `ρ`,
  -- through `f`. The two maps have the same kernel `(ker f + p) ∩ f⁻¹(q)`.
  let ι : q.comap f →+ K :=
    { toFun x := ⟨_root_.Quotient.mk _ x, x, x.2, rfl⟩
      map_zero' := by ext; simp
      map_add' x y := by ext; simp }
  let θ : q.comap f →+ ↥(q ⊓ LinearMap.range f) :=
    { toFun x := ⟨f x, x.2, x, rfl⟩
      map_zero' := by ext; simp
      map_add' x y := by ext; simp }
  let σ := (QuotientAddGroup.mk' K₀).comp ι
  let ρ := N.mkQ.toAddMonoidHom.comp θ
  have hσ : Function.Surjective σ := by
    refine (QuotientAddGroup.mk'_surjective K₀).comp ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hρ : Function.Surjective ρ := by
    refine N.mkQ_surjective.comp ?_
    rintro ⟨_, hy, x, rfl⟩
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : σ.ker = ρ.ker := by
    ext ⟨x, hx⟩
    suffices (∃ y, f y = 0 ∧ y - x ∈ p) ↔ ∃ z ∈ p, f z = f x by
      simpa [σ, ρ, ι, θ, K₀, N, AddSubgroup.mem_addSubgroupOf, QuotientAddGroup.eq_zero_iff,
        _root_.Quotient.eq, orbitRel_apply_iff_sub_mem] using this
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨x - y, by simpa using p.neg_mem hyx, by simp [hy]⟩
    · rintro ⟨z, hz, hzx⟩
      exact ⟨x - z, by simp [hzx], by simpa using p.neg_mem hz⟩
  (QuotientAddGroup.quotientKerEquivOfSurjective σ hσ).symm.trans <|
    (QuotientAddGroup.quotientAddEquivOfEq hker).trans <|
      QuotientAddGroup.quotientKerEquivOfSurjective ρ hρ

/-- `Submodule.orbitRelQuotientComapQuotientEquiv` sends the class of the orbit of `x ∈ f⁻¹(q)`
to the class of `f x`. -/
@[simp]
theorem Submodule.orbitRelQuotientComapQuotientEquiv_mk {x : M} (hx : x ∈ q.comap f) :
    p.orbitRelQuotientComapQuotientEquiv q f
        (QuotientAddGroup.mk ⟨_root_.Quotient.mk (AddAction.orbitRel p M) x, x, hx,
          congrFun p.coe_orbitRelQuotientMkHom x⟩) =
      Submodule.Quotient.mk ⟨f x, hx, x, rfl⟩ := by
  -- By construction the first factor of the equivalence inverts the map sending `⟨x, hx⟩` to
  -- the class of the orbit of `x`, and the last factor sends `⟨x, hx⟩` to the class of `f x`.
  rw [orbitRelQuotientComapQuotientEquiv, AddEquiv.trans_apply]
  exact congrArg _ (AddEquiv.symm_apply_apply _ (QuotientAddGroup.mk (⟨x, hx⟩ : q.comap f)))

end Preimage

section Prod

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] (q : Submodule R M₂)

/-- The orbit relation of translation by `p.prod q` on `M × M₂` is the product of the orbit
relations of translation by `p` on `M` and by `q` on `M₂`. -/
theorem Submodule.orbitRel_prod :
    AddAction.orbitRel (p.prod q) (M × M₂) =
      (AddAction.orbitRel p M).prod (AddAction.orbitRel q M₂) :=
  Setoid.ext fun x y ↦ by
    rw [orbitRel_apply_iff_sub_mem, Setoid.prod_apply, orbitRel_apply_iff_sub_mem,
      orbitRel_apply_iff_sub_mem]
    exact Submodule.mem_prod

/-- The orbit space of translation by `p.prod q` on `M × M₂` is additively equivalent to the
product of the orbit spaces of translation by `p` on `M` and by `q` on `M₂`, by the equivalence
sending the orbit of `(x, y)` to the pair of orbits of `x` and `y`. For lattices `L ⊆ E` and
`L' ⊆ E'` in complex vector spaces, this identifies the complex torus `(E × E') / (L × L')` with the
product of the complex tori `E / L` and `E' / L'`. -/
def Submodule.orbitRelQuotientProdAddEquiv :
    AddAction.orbitRel.Quotient (p.prod q) (M × M₂) ≃+
      AddAction.orbitRel.Quotient p M × AddAction.orbitRel.Quotient q M₂ where
  toEquiv := (Quotient.congrRight fun x y ↦ by rw [p.orbitRel_prod q]).trans
    (Setoid.prodQuotientEquiv _ _).symm
  map_add' x y := by
    induction x, y using _root_.Quotient.inductionOn₂ with | h x y => ?_
    rw [← (p.prod q).orbitRelQuotient_mk_add]
    exact Prod.ext (p.orbitRelQuotient_mk_add _ _) (q.orbitRelQuotient_mk_add _ _)

/-- `Submodule.orbitRelQuotientProdAddEquiv` sends the orbit of `x` to the pair of orbits of its
components. -/
@[simp]
theorem Submodule.orbitRelQuotientProdAddEquiv_mk (x : M × M₂) :
    p.orbitRelQuotientProdAddEquiv q (_root_.Quotient.mk (AddAction.orbitRel (p.prod q) _) x) =
      (_root_.Quotient.mk (AddAction.orbitRel p M) x.1,
        _root_.Quotient.mk (AddAction.orbitRel q M₂) x.2) :=
  (rfl)

/-- The inverse of `Submodule.orbitRelQuotientProdAddEquiv` sends a pair of orbits of `x` and `y`
to the orbit of `(x, y)`. -/
@[simp]
theorem Submodule.orbitRelQuotientProdAddEquiv_symm_mk (x : M) (y : M₂) :
    (p.orbitRelQuotientProdAddEquiv q).symm
        (_root_.Quotient.mk (AddAction.orbitRel p M) x,
          _root_.Quotient.mk (AddAction.orbitRel q M₂) y) =
      _root_.Quotient.mk (AddAction.orbitRel (p.prod q) (M × M₂)) (x, y) :=
  (rfl)

end Prod
