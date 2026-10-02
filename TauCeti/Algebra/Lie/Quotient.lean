/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient

/-!
# Homomorphisms from quotients by Lie ideals

Mathlib equips the quotient of a Lie algebra by a Lie ideal with its Lie algebra structure and
provides the quotient map as a morphism of Lie modules. This file records that map as a
homomorphism of Lie algebras and gives its universal property: a homomorphism killing the ideal
factors uniquely through the quotient. For a surjective homomorphism, the induced map from the
quotient by its kernel is an isomorphism, which is the first isomorphism theorem.

These declarations live in the root `LieIdeal` and `LieHom` namespaces, extending Mathlib's API
and supporting receiver notation on the ideal and the homomorphism.

## Main definitions

* `LieIdeal.mkQ`: the quotient map `L →ₗ⁅R⁆ L ⧸ I`.
* `LieIdeal.liftQ`: the homomorphism `L ⧸ I →ₗ⁅R⁆ L'` induced by a homomorphism
  `L →ₗ⁅R⁆ L'` whose kernel contains `I`.
* `LieHom.quotKerEquivOfSurjective`: the first isomorphism theorem, identifying the quotient of
  `L` by the kernel of a surjective homomorphism with its target.

## Main results

* `LieIdeal.mkQ_surjective`: every quotient class has a representative in the original Lie
  algebra.
* `LieIdeal.liftQ_mkQ`: the lifted homomorphism restricts to the original one along the quotient
  map.
* `LieIdeal.coe_liftQ`: the lifted homomorphism is `Submodule.liftQ` of the underlying linear map.
* `LieIdeal.liftQ_injective` and `LieIdeal.liftQ_surjective`: the lifted homomorphism is injective
  when the ideal exhausts the kernel, and surjective when the original homomorphism is.
* `LieIdeal.lieHom_qext`: two homomorphisms from the quotient are equal when they agree after the
  quotient map.
* `LieIdeal.eq_liftQ`: the lifted homomorphism is the unique such factorization.
* `LieIdeal.ker_liftQ_mkQ`: for ideals `J ≤ I`, the kernel of `L ⧸ J → L ⧸ I` is the image of `I`.
* `LieIdeal.mkQ_comp_incl_surjective`: a Lie subalgebra `P` with `I + P = L` maps onto `L ⧸ I`.
* `LieIdeal.ker_mkQ_comp_incl`: the kernel of `P → L ⧸ I` is the ideal `I ∩ P` of `P`.
-/

public section

namespace LieIdeal

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (I : LieIdeal R L)

/-- The quotient map `L → L ⧸ I` as a homomorphism of Lie algebras.

Its underlying function is Mathlib's `LieSubmodule.Quotient.mk`, sending each element to its
quotient class. -/
def mkQ : L →ₗ⁅R⁆ L ⧸ I where
  __ := I.toSubmodule.mkQ
  map_lie' := rfl

/-- The quotient homomorphism sends an element to its class. -/
@[simp]
theorem mkQ_apply (x : L) : I.mkQ x = LieSubmodule.Quotient.mk x := (rfl)

/-- Every element of the quotient has a representative in the original Lie algebra. -/
theorem mkQ_surjective : Function.Surjective I.mkQ := fun y => by
  obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' I y
  exact ⟨x, (I.mkQ_apply x).trans hx⟩

/-- The kernel of the quotient homomorphism is the ideal quotiented by. -/
@[simp]
theorem ker_mkQ : I.mkQ.ker = I := by
  ext x
  simp [LieHom.mem_ker]

/-- The homomorphism `L ⧸ I →ₗ⁅R⁆ L'` induced by a homomorphism `f : L →ₗ⁅R⁆ L'` whose kernel
contains the ideal `I`. -/
def liftQ (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) : L ⧸ I →ₗ⁅R⁆ L' where
  __ := LieSubmodule.toSubmodule I |>.liftQ (f : L →ₗ[R] L') h
  map_lie' {x y} := by
    induction x using Quotient.inductionOn' with | _ x
    induction y using Quotient.inductionOn' with | _ y
    exact f.map_lie x y

/-- The induced homomorphism on the quotient sends the class of `x` to `f x`. -/
@[simp]
theorem liftQ_apply (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) (x : L) :
    I.liftQ f h (LieSubmodule.Quotient.mk x) = f x := (rfl)

/-- The linear map underlying the induced homomorphism on the quotient is `Submodule.liftQ` of
the linear map underlying `f`. -/
theorem coe_liftQ (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) :
    ((I.liftQ f h : L ⧸ I →ₗ⁅R⁆ L') : L ⧸ I →ₗ[R] L') =
      (LieSubmodule.toSubmodule I).liftQ (f : L →ₗ[R] L')
        (((LieSubmodule.toSubmodule_le_toSubmodule I f.ker).mpr h).trans
          (LieHom.ker_toSubmodule f).le) :=
  (rfl)

/-- The homomorphism induced on the quotient is injective as soon as the ideal quotiented by
exhausts the kernel. -/
theorem liftQ_injective (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) (h' : f.ker ≤ I) :
    Function.Injective (I.liftQ f h) := by
  rw [← LieHom.coe_toLinearMap, ← LinearMap.ker_eq_bot, coe_liftQ]
  exact Submodule.ker_liftQ_eq_bot _ (f : L →ₗ[R] L') _ <| by
    rw [← LieHom.ker_toSubmodule, LieSubmodule.toSubmodule_le_toSubmodule]; exact h'

/-- The homomorphism induced on the quotient by a surjective homomorphism is surjective. -/
theorem liftQ_surjective (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) (h' : Function.Surjective f) :
    Function.Surjective (I.liftQ f h) := by
  rw [← LieHom.coe_toLinearMap, ← LinearMap.range_eq_top, coe_liftQ, Submodule.range_liftQ,
    LinearMap.range_eq_top, LieHom.coe_toLinearMap]
  exact h'

/-- The induced homomorphism on the quotient composed with the quotient map is the original
homomorphism. -/
@[simp]
theorem liftQ_mkQ (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) : (I.liftQ f h).comp I.mkQ = f := by
  ext x
  simp

/-- Two homomorphisms out of `L ⧸ I` that agree after composition with the quotient map are
equal. -/
@[ext high]
theorem lieHom_qext {g₁ g₂ : L ⧸ I →ₗ⁅R⁆ L'} (h : ∀ x : L, g₁ (I.mkQ x) = g₂ (I.mkQ x)) :
    g₁ = g₂ := by
  apply LieHom.ext
  exact LinearMap.congr_fun <|
    Submodule.quot_hom_ext I.toSubmodule g₁.toLinearMap g₂.toLinearMap fun x => h x

/-- The factorization of `LieIdeal.liftQ` is the only one: a homomorphism out of `L ⧸ I`
restricting to `f` along the quotient map is `I.liftQ f h`. -/
theorem eq_liftQ {f : L →ₗ⁅R⁆ L'} {h : I ≤ f.ker} {g : L ⧸ I →ₗ⁅R⁆ L'}
    (hg : ∀ x : L, g (I.mkQ x) = f x) : g = I.liftQ f h :=
  I.lieHom_qext fun x => by rw [hg]; simp

/-- For ideals `J ≤ I`, the kernel of the induced map `L ⧸ J → L ⧸ I` is the image of `I` in
`L ⧸ J`. -/
theorem ker_liftQ_mkQ {J : LieIdeal R L} (h : J ≤ I.mkQ.ker) :
    (J.liftQ I.mkQ h).ker = I.map J.mkQ := by
  rw [ker_mkQ] at h
  ext z
  obtain ⟨x, rfl⟩ := J.mkQ_surjective z
  rw [LieHom.mem_ker, ← LieHom.comp_apply, liftQ_mkQ, ← LieHom.mem_ker, ker_mkQ]
  refine ⟨fun hx ↦ mem_map hx, fun hx ↦ ?_⟩
  obtain ⟨⟨y, hy⟩, hyx⟩ := mem_map_of_surjective J.mkQ_surjective hx
  rw [← sub_add_cancel x y]
  refine I.add_mem (h ?_) hy
  rw [← ker_mkQ J, LieHom.mem_ker, map_sub, hyx, sub_self]

section Supplement

variable {P : LieSubalgebra R L}

/-- A Lie subalgebra `P` supplementing an ideal `I`, in the sense that `I + P = L`, maps onto the
quotient `L ⧸ I`. -/
theorem mkQ_comp_incl_surjective (hIP : Codisjoint I.toSubmodule P.toSubmodule) :
    Function.Surjective (I.mkQ.comp P.incl) := by
  intro y
  obtain ⟨x, rfl⟩ := I.mkQ_surjective y
  obtain ⟨i, hi, s, hs, rfl⟩ := Submodule.mem_sup.1 (hIP.eq_top ▸ Submodule.mem_top (x := x))
  refine ⟨⟨s, hs⟩, ?_⟩
  rw [LieHom.comp_apply, LieSubalgebra.coe_incl, ← sub_eq_zero, ← map_sub, ← LieHom.mem_ker,
    ker_mkQ, Subtype.coe_mk, sub_add_cancel_right]
  exact I.neg_mem hi

/-- The kernel of the map `P → L ⧸ I` induced by a Lie subalgebra `P` is the ideal `I ∩ P` of
`P`. -/
@[simp]
theorem ker_mkQ_comp_incl : (I.mkQ.comp P.incl).ker = I.comap P.incl := by
  ext x
  rw [LieHom.mem_ker, mem_comap, LieHom.comp_apply, mkQ_apply, LieSubmodule.Quotient.mk_eq_zero']

end Supplement

end LieIdeal

namespace LieHom

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- **The first isomorphism theorem** for a surjective homomorphism of Lie algebras: the quotient
by its kernel is isomorphic to the target. -/
noncomputable def quotKerEquivOfSurjective (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f) :
    (L ⧸ f.ker) ≃ₗ⁅R⁆ L' :=
  LieEquiv.ofBijective (f.ker.liftQ f le_rfl)
    ⟨f.ker.liftQ_injective f le_rfl le_rfl, f.ker.liftQ_surjective f le_rfl hf⟩

/-- The first isomorphism theorem sends the class of `x` to `f x`. -/
@[simp]
theorem quotKerEquivOfSurjective_apply_mk (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f) (x : L) :
    f.quotKerEquivOfSurjective hf (LieSubmodule.Quotient.mk x) = f x := (rfl)

end LieHom
