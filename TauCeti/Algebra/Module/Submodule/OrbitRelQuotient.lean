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
A semilinear map carrying `p` into a submodule `q` then induces an additive map of orbit spaces,
read through these equivalences from `Submodule.mapQ`, and a semilinear equivalence carrying `p`
onto `q` induces an additive equivalence. For lattices `L ⊆ E` and `L' ⊆ E'` in complex vector
spaces, these are the group homomorphisms and isomorphisms of complex tori `E / L → E' / L'`
underlying the holomorphic maps induced by complex linear maps preserving the lattices.

## Main declarations

* `Submodule.orbitRelQuotientAddEquiv`: the orbit space of translation by `p` is additively
  equivalent to the quotient module `M ⧸ p`, by an equivalence sending the orbit of `x` to the
  class of `x`.
* `Submodule.orbitRelQuotient_mk_add`, `Submodule.orbitRelQuotient_mk_zero`,
  `Submodule.orbitRelQuotient_mk_neg`, `Submodule.orbitRelQuotient_mk_sub`: the orbit projection
  is additive.
* `Submodule.orbitRelQuotient_mk_eq_zero_iff`: its kernel is `p`.
* `Submodule.orbitRelQuotientMap`: the additive map of orbit spaces induced by a semilinear map
  `f` carrying `p` into `q`, functorial in `f` (`Submodule.orbitRelQuotientMap_id`,
  `Submodule.orbitRelQuotientMap_comp`).
* `Submodule.orbitRelQuotientMap_injective_iff`: the induced map is injective exactly when
  `f⁻¹(q) ≤ p`.
* `Submodule.orbitRelQuotientCongr`: the additive equivalence of orbit spaces induced by a
  semilinear equivalence `e` with `p.map e = q`.
* `Submodule.orbitRelQuotientMap_bijective_iff`: for a semilinear equivalence `e` carrying `p` into
  `q`, the induced map is bijective exactly when `e` carries `p` onto `q`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.2.
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

/-- A point of `M` projects to `0` in the orbit space of translation by `p` exactly when it lies
in `p`. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_eq_zero_iff {x : M} :
    _root_.Quotient.mk (AddAction.orbitRel p M) x = 0 ↔ x ∈ p := by
  rw [← orbitRelQuotient_mk_zero, _root_.Quotient.eq, orbitRel_apply_iff_sub_mem, sub_zero]

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

section Map

variable {R₂ M₂ : Type*} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] (q : Submodule R₂ M₂)
  {τ₁₂ : R →+* R₂}

/-- A semilinear map `f : M → M₂` carrying `p` into `q` induces an additive map from the orbit
space of translation by `p` to that of translation by `q`, sending the orbit of `x` to the orbit
of `f x`. It is `Submodule.mapQ` read through `Submodule.orbitRelQuotientAddEquiv`. -/
def Submodule.orbitRelQuotientMap (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ q.comap f) :
    AddAction.orbitRel.Quotient p M →+ AddAction.orbitRel.Quotient q M₂ :=
  q.orbitRelQuotientAddEquiv.symm.toAddMonoidHom.comp <|
    (p.mapQ q f h).toAddMonoidHom.comp p.orbitRelQuotientAddEquiv.toAddMonoidHom

/-- `Submodule.orbitRelQuotientMap` sends the orbit of `x` to the orbit of `f x`. -/
@[simp]
theorem Submodule.orbitRelQuotientMap_mk (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ q.comap f) (x : M) :
    p.orbitRelQuotientMap q f h (_root_.Quotient.mk (AddAction.orbitRel p M) x) =
      _root_.Quotient.mk (AddAction.orbitRel q M₂) (f x) :=
  (rfl)

/-- Read through `Submodule.orbitRelQuotientAddEquiv`, the induced map of orbit spaces is
`Submodule.mapQ`. -/
@[simp]
theorem Submodule.orbitRelQuotientAddEquiv_orbitRelQuotientMap (f : M →ₛₗ[τ₁₂] M₂)
    (h : p ≤ q.comap f) (x : AddAction.orbitRel.Quotient p M) :
    q.orbitRelQuotientAddEquiv (p.orbitRelQuotientMap q f h x) =
      p.mapQ q f h (p.orbitRelQuotientAddEquiv x) :=
  q.orbitRelQuotientAddEquiv.apply_symm_apply _

/-- The identity map induces the identity of the orbit space. -/
@[simp]
theorem Submodule.orbitRelQuotientMap_id
    (h : p ≤ p.comap LinearMap.id := (by rw [Submodule.comap_id])) :
    p.orbitRelQuotientMap p LinearMap.id h = AddMonoidHom.id _ := by
  ext x
  induction x using _root_.Quotient.inductionOn
  simp

/-- The map of orbit spaces induced by a composite is the composite of the induced maps. -/
theorem Submodule.orbitRelQuotientMap_comp {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M₃]
    [Module R₃ M₃] (r : Submodule R₃ M₃) {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
    [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃)
    (hf : p ≤ q.comap f) (hg : q ≤ r.comap g) (h := hf.trans (Submodule.comap_mono hg)) :
    p.orbitRelQuotientMap r (g.comp f) h =
      (q.orbitRelQuotientMap r g hg).comp (p.orbitRelQuotientMap q f hf) := by
  ext x
  induction x using _root_.Quotient.inductionOn
  simp

/-- The map of orbit spaces induced by `f` is injective exactly when every point that `f` sends
into `q` already lies in `p`. -/
theorem Submodule.orbitRelQuotientMap_injective_iff (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ q.comap f) :
    Function.Injective (p.orbitRelQuotientMap q f h) ↔ q.comap f ≤ p := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun hinj x hx ↦ ?_, fun hle x hx ↦ ?_⟩
  · simpa using hinj (_root_.Quotient.mk _ x) (by simpa using hx)
  · induction x using _root_.Quotient.inductionOn
    simpa using hle (by simpa using hx)

/-- The map of orbit spaces induced by a surjective map is surjective. -/
theorem Submodule.orbitRelQuotientMap_surjective {f : M →ₛₗ[τ₁₂] M₂}
    (hf : Function.Surjective f) (h : p ≤ q.comap f) :
    Function.Surjective (p.orbitRelQuotientMap q f h) := by
  intro y
  induction y using _root_.Quotient.inductionOn with | h y => ?_
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨_, p.orbitRelQuotientMap_mk q f h x⟩

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- A semilinear equivalence `e : M ≃ M₂` carrying `p` onto `q` induces an additive equivalence
between the orbit spaces of translation by `p` and by `q`, sending the orbit of `x` to the orbit
of `e x`. It is `Submodule.Quotient.equiv` read through `Submodule.orbitRelQuotientAddEquiv`. -/
def Submodule.orbitRelQuotientCongr (e : M ≃ₛₗ[σ₁₂] M₂) (he : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) :
    AddAction.orbitRel.Quotient p M ≃+ AddAction.orbitRel.Quotient q M₂ :=
  p.orbitRelQuotientAddEquiv.trans <|
    (Submodule.Quotient.equiv p q e he).toAddEquiv.trans q.orbitRelQuotientAddEquiv.symm

/-- `Submodule.orbitRelQuotientCongr` sends the orbit of `x` to the orbit of `e x`. -/
@[simp]
theorem Submodule.orbitRelQuotientCongr_mk (e : M ≃ₛₗ[σ₁₂] M₂)
    (he : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) (x : M) :
    p.orbitRelQuotientCongr q e he (_root_.Quotient.mk (AddAction.orbitRel p M) x) =
      _root_.Quotient.mk (AddAction.orbitRel q M₂) (e x) :=
  (rfl)

/-- The inverse of the equivalence induced by `e` is the equivalence induced by `e.symm`. -/
@[simp]
theorem Submodule.orbitRelQuotientCongr_symm (e : M ≃ₛₗ[σ₁₂] M₂)
    (he : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) :
    (p.orbitRelQuotientCongr q e he).symm =
      q.orbitRelQuotientCongr p e.symm ((Submodule.map_symm_eq_iff e).2 he) := by
  ext x
  induction x using _root_.Quotient.inductionOn
  simp [AddEquiv.symm_apply_eq]

/-- As an additive map, the equivalence induced by `e` is the map of orbit spaces induced by
`e`. -/
@[simp]
theorem Submodule.coe_orbitRelQuotientCongr (e : M ≃ₛₗ[σ₁₂] M₂)
    (he : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) :
    (p.orbitRelQuotientCongr q e he :
        AddAction.orbitRel.Quotient p M →+ AddAction.orbitRel.Quotient q M₂) =
      p.orbitRelQuotientMap q (e : M →ₛₗ[σ₁₂] M₂) (Submodule.map_le_iff_le_comap.1 he.le) := by
  ext x
  induction x using _root_.Quotient.inductionOn
  simp

/-- For a semilinear equivalence `e` carrying `p` into `q`, the induced map of orbit spaces is
bijective exactly when `e` carries `p` onto `q`. -/
theorem Submodule.orbitRelQuotientMap_bijective_iff (e : M ≃ₛₗ[σ₁₂] M₂)
    (h : p ≤ q.comap (e : M →ₛₗ[σ₁₂] M₂)) :
    Function.Bijective (p.orbitRelQuotientMap q (e : M →ₛₗ[σ₁₂] M₂) h) ↔
      p.map (e : M →ₛₗ[σ₁₂] M₂) = q := by
  rw [Function.Bijective, and_iff_left (p.orbitRelQuotientMap_surjective q e.surjective h),
    orbitRelQuotientMap_injective_iff, Submodule.comap_equiv_eq_map_symm,
    Submodule.map_le_iff_le_comap, ← Submodule.map_equiv_eq_comap_symm]
  exact ⟨(Submodule.map_le_iff_le_comap.2 h).antisymm, Eq.ge⟩

end Map
