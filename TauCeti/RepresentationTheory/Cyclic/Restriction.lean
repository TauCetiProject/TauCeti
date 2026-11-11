/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.RepresentationTheory.Cyclic.Automorphism

/-!
# Restricting cyclic representations of additive automorphisms

A homomorphism `χ : C_n → C_m` sending the selected generator to its `d`-th power
restricts the cyclic representation of `A` to one whose generator acts by `A^d`.
An additive map intertwining `A^d` with `B` therefore gives a morphism from the
restricted representation of `A` to the cyclic representation of `B`.

`AddMonoidHom.cyclicRepResHom` constructs this morphism from the generator equation,
without requiring equivariance to be supplied separately for every group element.
It permits the degree-one partial norms, degree-two classes, and connecting classes
of cyclic representations to be compared under arbitrary homomorphisms of cyclic groups.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter I, §§6–7.
-/

public section

open CategoryTheory Rep

namespace AddMonoidHom

universe u

variable {T M : Type u} [AddCommGroup T] [AddCommGroup M] {m n : ℕ} [NeZero m] [NeZero n]
  {A : T ≃+ T} {B : M ≃+ M} (f : T →+ M)
  (hA : (⇑A)^[m] = _root_.id) (hB : (⇑B)^[n] = _root_.id)
  (χ : Multiplicative (ZMod n) →* Multiplicative (ZMod m)) (d : ℕ)
  (hχ : χ (.ofAdd 1) = (.ofAdd 1) ^ d) (hf : ∀ x, f ((⇑A)^[d] x) = B (f x))

/-- An additive map intertwining `A^d` with `B` is equivariant from the restriction of the
cyclic representation of `A` along `χ` to that of `B`, when `χ` sends the generator to
its `d`-th power. Neither injectivity nor surjectivity of `χ` is required. -/
noncomputable def cyclicRepResHom : res χ (A.cyclicRep hA) ⟶ B.cyclicRep hB :=
  Rep.ofHom <| f.toIntLinearMap.intertwiningMap_of_isIntertwiningMap _ _ fun g x ↦ by
    have hg : (Multiplicative.ofAdd (1 : ZMod n)) ^ g.toAdd.val = g := by
      rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
    rw [← hg, MonoidHom.comp_apply, map_pow χ, hχ, ← pow_mul,
      AddEquiv.cyclicRepresentation_ofAdd_one_pow_apply,
      AddEquiv.cyclicRepresentation_ofAdd_one_pow_apply, Function.iterate_mul]
    exact Function.Semiconj.iterate_right hf g.toAdd.val x

/-- On underlying groups the morphism induced by `f` is `f`. The coercion is stated on
intertwining maps, so simplification also recognizes evaluations with restricted instances. -/
@[simp]
theorem coe_cyclicRepResHom_hom :
    DFunLike.coe (F := Representation.IntertwiningMap ((A.cyclicRepresentation hA).comp χ)
      (B.cyclicRepresentation hB)) (f.cyclicRepResHom hA hB χ d hχ hf).hom = f :=
  (rfl)

end AddMonoidHom
