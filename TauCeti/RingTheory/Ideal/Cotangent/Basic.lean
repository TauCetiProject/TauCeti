/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Basic

/-!
# Cotangent spaces of ideals and augmented algebras

Elements of an ideal `I` of `A` whose images span the cotangent space `I ⧸ I ^ 2` over `A`
generate `I` modulo `I ^ 2`. For an augmentation `f : A →ₐ[R] R`, if the augmentation ideal is
finitely generated over `A`, then its cotangent space is finite over `R`.

## Main declarations

* `Ideal.le_span_sup_sq_of_span_toCotangent_eq_top`: elements whose images span the cotangent
  space generate the ideal modulo its square.
* `TauCeti.AlgHom.finite_cotangent_ker_of_fg`: finite generation of the augmentation ideal gives
  finiteness of its cotangent space over the base.
* `TauCeti.AlgHom.finite_cotangent_ker`: the noetherian specialization.

## References

* Mathlib's `Algebra.Extension.Cotangent.finite` provides the generic cotangent-space finiteness
  result used here.
-/

public section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- Elements of an ideal `I` whose images span the cotangent space `I ⧸ I ^ 2` over `A` generate
`I` modulo `I ^ 2`. -/
theorem le_span_sup_sq_of_span_toCotangent_eq_top (I : Ideal A) {ι : Type*} {f : ι → I}
    (h : Submodule.span A (Set.range (I.toCotangent ∘ f)) = ⊤) :
    I ≤ span (Set.range fun i ↦ (f i : A)) ⊔ I ^ 2 := by
  set J := span (Set.range fun i ↦ (f i : A)) ⊔ I ^ 2
  -- The image of `J ∩ I` in the cotangent space contains every generator, so is everything.
  let P : Submodule A I.Cotangent := (Submodule.comap I.subtype J).map I.toCotangent
  have hP : P = ⊤ := by
    refine eq_top_iff.2 (h ▸ Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, mem_sup_left (subset_span ⟨i, rfl⟩), rfl⟩
  intro y hy
  obtain ⟨z, hzJ, hz⟩ : I.toCotangent ⟨y, hy⟩ ∈ P := hP ▸ Submodule.mem_top
  rw [toCotangent_eq] at hz
  rw [← sub_sub_cancel (z : A) y]
  exact J.sub_mem hzJ (mem_sup_right hz)

end Ideal

namespace TauCeti

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The cotangent space of an augmentation with finitely generated kernel is finite over the
base. -/
theorem finite_cotangent_ker_of_fg (f : A →ₐ[R] R)
    (h : (RingHom.ker f.toRingHom).FG) :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent := by
  let P : Algebra.Extension R R :=
    Algebra.Extension.ofSurjective f (fun r ↦ ⟨algebraMap R A r, f.commutes r⟩)
  have hmap : algebraMap P.Ring R = f.toRingHom := by
    exact RingHom.algebraMap_toAlgebra f.toRingHom
  have hker : P.ker = RingHom.ker f.toRingHom := congrArg RingHom.ker hmap
  have hP : P.ker.FG := by
    rw [hker]
    exact h
  let _ : Module.Finite R P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) hP
  have hfinite : Module.Finite R P.ker.Cotangent :=
    Module.Finite.equiv (P.cotangentEquivCotangentKer.restrictScalars R)
  exact Module.Finite.equiv
    ((Ideal.Cotangent.equivOfEq P.ker (RingHom.ker f.toRingHom) hker).restrictScalars R)

/-- The cotangent space at an augmented point of a noetherian algebra is finite over the base.

The augmentation hypothesis is encoded by the codomain of `f`: because `f` is an `R`-algebra
homomorphism, it is a retraction of `algebraMap R A`. -/
theorem finite_cotangent_ker (f : A →ₐ[R] R) [IsNoetherianRing A] :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent :=
  finite_cotangent_ker_of_fg f (RingHom.ker f.toRingHom).fg_of_isNoetherianRing

end AlgHom

end TauCeti
