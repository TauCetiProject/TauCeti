/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.OfModule
public import TauCeti.RingTheory.PrimitiveIdempotent

/-!
# Intertwining maps out of the left ideal of a quasi-idempotent

Let `σ` be a representation of a monoid `G` on `V` over a commutative semiring `k`, and let `a` be
an element of the monoid algebra `k[G]` that is **quasi-idempotent**: `a * a = κ • a` for a unit
`κ` of `k`. The left ideal `k[G] a` is a representation of `G` by left multiplication, and this
file identifies the intertwining maps out of it:

`Hom_G(k[G] a, V) ≃ₗ[k] a V`, by `f ↦ f a`,

where `a V` is the image of `a` acting on `V` through `σ`.

This identifies the intertwiner space with a subspace of `V` itself, the image of `a`. In a split
semisimple setting, when `k[G] a` is irreducible, this intertwiner space is its multiplicity space
in `V`. The identification is natural in `V`
(`Representation.spanSingletonHomEquivRange_comp`), so any operator on `V` commuting with `G`
acts compatibly on both sides.

Allowing a scalar `κ` rather than asking for an idempotent is what the applications need: the
Young symmetrizer `c_t` satisfies `c_t * c_t = κ • c_t` with `κ = n! / dim (k[Sₙ] c_t)`, and it is
`c_t` itself, not its normalization, whose image cuts out the Weyl module.

Both directions are elementary. The monoid-algebra linear map corresponding to an intertwining map
commutes with the whole of `k[G]`, so its value on an element `r a` of the ideal is `r` applied to
its value at `a`, which therefore determines it; and that value lies in `a V` because
`a = κ⁻¹ a a`. Conversely a vector `a v` of `a V` defines the intertwining map
`x ↦ κ⁻¹ x (a v)`, which sends `a` to `κ⁻¹ a a v = a v`.

## Main definitions

* `Representation.spanSingletonHomEquivRange`: **the dictionary**
  `Hom_G(k[G] a, V) ≃ₗ[k] a V`, evaluation at the generator `a`.

## Main results

* `Representation.coe_spanSingletonHomEquivRange_apply`: the dictionary evaluates at
  the generator.
* `Representation.spanSingletonHomEquivRange_symm_apply_smul_generator`: its inverse
  sends a vector of `a V` to the intertwining map taking `r a` to `r` applied to that vector.
* `Representation.spanSingletonHomEquivRange_comp`: naturality in the target.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Section I.4, for the idempotent case `Hom_A(Ae, M) ≅ eM`.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, where the
  quasi-idempotent Young symmetrizers are the case that matters.
-/

public section

namespace Representation

open scoped MonoidAlgebra
open TauCeti (spanSingletonGenerator coe_spanSingletonGenerator)

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
variable (σ : Representation k G V) {a : k[G]} {κ : k}

/-- The representation of `G` on the left ideal `k[G] a` by left multiplication. -/
local notation "ρₐ" a =>
  ofModule' (k := k) (G := G) (Ideal.span {a} : Ideal k[G])

/-- An element of the left ideal `k[G] a` is a left multiple of the generator `a`. -/
private theorem exists_smul_spanSingletonGenerator (x : (Ideal.span {a} : Ideal k[G])) :
    ∃ r : k[G], r • spanSingletonGenerator a = x := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp x.2
  exact ⟨r, Subtype.ext (by rwa [Submodule.coe_smul, coe_spanSingletonGenerator, smul_eq_mul])⟩

/-- Under quasi-idempotence, `a` acting on the generator of `k[G] a` scales it by `κ`. -/
private theorem smul_spanSingletonGenerator_self (ha : a * a = κ • a) :
    a • spanSingletonGenerator a = κ • spanSingletonGenerator a :=
  Subtype.ext (by
    rwa [Submodule.coe_smul, Submodule.coe_smul_of_tower, coe_spanSingletonGenerator, smul_eq_mul])

/-- An intertwining map out of `k[G] a` sends `r a` to `r` applied to its value at `a`. -/
private theorem intertwining_apply_smul_generator (f : IntertwiningMap (ρₐ a) σ) (r : k[G]) :
    f (r • spanSingletonGenerator a) = σ.asAlgebraHom r (f (spanSingletonGenerator a)) := by
  rw [← TauCeti.Representation.asAlgebraHom_ofModule'_apply]
  exact (IntertwiningMap.equivLinearMapAsModule _ _ f).map_smul' r _

/-- The value of an intertwining map out of `k[G] a` at the generator lies in the image of `a`. -/
private theorem intertwining_apply_generator_mem_range (hκ : IsUnit κ) (ha : a * a = κ • a)
    (f : IntertwiningMap (ρₐ a) σ) :
    f (spanSingletonGenerator a) ∈ LinearMap.range (σ.asAlgebraHom a) := by
  refine ⟨(↑hκ.unit⁻¹ : k) • f (spanSingletonGenerator a), ?_⟩
  rw [map_smul, ← intertwining_apply_smul_generator, smul_spanSingletonGenerator_self ha, map_smul,
    smul_smul, hκ.val_inv_mul, one_smul]

/-- The intertwining map out of `k[G] a` attached to a vector `v`: it sends `x` to `κ⁻¹ x v`. -/
private noncomputable def intertwiningOfVector (hκ : IsUnit κ) (v : V) :
    IntertwiningMap (ρₐ a) σ where
  toFun x := (↑hκ.unit⁻¹ : k) • σ.asAlgebraHom (x : k[G]) v
  map_add' x y := by simp only [Submodule.coe_add, map_add, LinearMap.add_apply, smul_add]
  map_smul' c x := by
    rw [Submodule.coe_smul_of_tower, map_smul, LinearMap.smul_apply, RingHom.id_apply,
      smul_comm c]
  isIntertwining' g := by
    ext x
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      TauCeti.Representation.ofModule'_apply, Submodule.coe_smul, smul_eq_mul, map_mul,
      Module.End.mul_apply, asAlgebraHom_single_one, map_smul]

private theorem intertwiningOfVector_apply (hκ : IsUnit κ) (v : V)
    (x : (Ideal.span {a} : Ideal k[G])) :
    intertwiningOfVector σ hκ v x = (↑hκ.unit⁻¹ : k) • σ.asAlgebraHom (x : k[G]) v :=
  rfl

/-- **Intertwining maps out of the left ideal of a quasi-idempotent.** If `a * a = κ • a` with `κ`
a unit, evaluation at the generator identifies the intertwining maps from `k[G] a` to `V` with the
image of `a` acting on `V`. -/
noncomputable def spanSingletonHomEquivRange (hκ : IsUnit κ) (ha : a * a = κ • a) :
    IntertwiningMap (ρₐ a) σ ≃ₗ[k] LinearMap.range (σ.asAlgebraHom a) where
  toFun f := ⟨f (spanSingletonGenerator a), intertwining_apply_generator_mem_range σ hκ ha f⟩
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun v := intertwiningOfVector σ hκ v
  left_inv f := by
    refine IntertwiningMap.ext (LinearMap.ext fun x => ?_)
    obtain ⟨r, rfl⟩ := exists_smul_spanSingletonGenerator x
    dsimp only
    rw [IntertwiningMap.toLinearMap_apply, IntertwiningMap.toLinearMap_apply,
      intertwiningOfVector_apply,
      intertwining_apply_smul_generator, Submodule.coe_smul, smul_eq_mul,
      coe_spanSingletonGenerator, map_mul, Module.End.mul_apply]
    -- `a` applied to the value at `a` is the value at `a • a = κ • a`, so `κ⁻¹` cancels
    rw [← intertwining_apply_smul_generator, smul_spanSingletonGenerator_self ha, map_smul,
      map_smul, smul_smul, hκ.val_inv_mul, one_smul]
  right_inv := by
    rintro ⟨_, u, rfl⟩
    refine Subtype.ext ?_
    dsimp only
    rw [intertwiningOfVector_apply, coe_spanSingletonGenerator, ← Module.End.mul_apply,
      ← map_mul, ha, map_smul, LinearMap.smul_apply, smul_smul, hκ.val_inv_mul, one_smul]

/-- The dictionary evaluates an intertwining map at the generator `a`. -/
@[simp]
theorem coe_spanSingletonHomEquivRange_apply (hκ : IsUnit κ) (ha : a * a = κ • a)
    (f : IntertwiningMap (ρₐ a) σ) :
    (spanSingletonHomEquivRange σ hκ ha f : V) = f (spanSingletonGenerator a) :=
  (rfl)

/-- The intertwining map attached to a vector `w` of `a V` sends `r a` to `r w`. -/
theorem spanSingletonHomEquivRange_symm_apply_smul_generator (hκ : IsUnit κ)
    (ha : a * a = κ • a) (w : LinearMap.range (σ.asAlgebraHom a)) (r : k[G]) :
    (spanSingletonHomEquivRange σ hκ ha).symm w (r • spanSingletonGenerator a) =
      σ.asAlgebraHom r w := by
  rw [intertwining_apply_smul_generator, ← coe_spanSingletonHomEquivRange_apply σ hκ ha,
    LinearEquiv.apply_symm_apply]

/-- The intertwining map attached to a vector `w` of `a V` sends the generator `a` to `w`. -/
@[simp]
theorem spanSingletonHomEquivRange_symm_apply_generator (hκ : IsUnit κ) (ha : a * a = κ • a)
    (w : LinearMap.range (σ.asAlgebraHom a)) :
    (spanSingletonHomEquivRange σ hκ ha).symm w (spanSingletonGenerator a) = w := by
  simpa using spanSingletonHomEquivRange_symm_apply_smul_generator σ hκ ha w 1

/-- **Naturality in the target.** Composing with an intertwining map `T : V → W` corresponds, on
the images of `a`, to applying `T`. -/
theorem spanSingletonHomEquivRange_comp {W : Type*} [AddCommMonoid W] [Module k W]
    {τ : Representation k G W} (hκ : IsUnit κ) (ha : a * a = κ • a)
    (T : IntertwiningMap σ τ) (f : IntertwiningMap (ρₐ a) σ) :
    (spanSingletonHomEquivRange τ hκ ha (T.comp f) : W) =
      T (spanSingletonHomEquivRange σ hκ ha f) :=
  (rfl)

end Representation
