/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Basic

/-!
# Cotangent spaces of ideals and kernels

If elements `f₁, f₂, …` generate an ideal `I`, their classes span the conormal module `I ⧸ I²`
over `R ⧸ I`. Conversely, elements of an ideal `I` of `A` whose images span the cotangent space
`I ⧸ I ^ 2` over `A` generate `I` modulo `I ^ 2`. For a surjective `R`-algebra homomorphism
`f : A →ₐ[R] S` onto a module-finite `R`-algebra, if the kernel of `f` is finitely generated over
`A`, then its cotangent space is finite over `R`. The main case is an augmentation
`f : A →ₐ[R] R`, whose kernel is the augmentation ideal.

## Main declarations

* `Ideal.span_range_toCotangent_eq_top`: the classes of generators of `I` span `I ⧸ I²` over
  `R ⧸ I`.
* `Ideal.le_span_sup_sq_of_span_toCotangent_eq_top`: elements whose images span the cotangent
  space generate the ideal modulo its square.
* `AlgHom.finite_cotangent_ker_of_fg`: finite generation of the kernel gives finiteness of its
  cotangent space over the base.
* `AlgHom.finite_cotangent_ker`: the noetherian specialization.

## References

* Mathlib's `Algebra.Extension.Cotangent.finite` provides the generic cotangent-space finiteness
  result used here.
-/

public section

namespace Ideal

section

variable {R : Type*} [CommRing R] {I : Ideal R} {ι : Type*}

/-- If the elements `f i` generate `I`, their classes span the conormal module `I ⧸ I²` over
`R ⧸ I`. -/
theorem span_range_toCotangent_eq_top {f : ι → I}
    (hf : Ideal.span (Set.range fun i ↦ (f i : R)) = I) :
    Submodule.span (R ⧸ I) (Set.range fun i ↦ I.toCotangent (f i)) = ⊤ := by
  have hspan : Submodule.span R (Set.range f) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I fun i ↦ (f i).2).mpr hf
  refine Submodule.span_eq_top_of_span_eq_top (S := R ⧸ I) R _ ?_
  rw [Set.range_comp' I.toCotangent f, ← Submodule.map_span, hspan, Submodule.map_top,
    I.toCotangent_range]

end

section

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

end

end Ideal

namespace AlgHom

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
  [Module.Finite R S]

/-- The cotangent space of the kernel of a surjection onto a module-finite algebra is finite over
the base when the kernel is finitely generated. -/
theorem finite_cotangent_ker_of_fg (f : A →ₐ[R] S) (hf : Function.Surjective f)
    (h : (RingHom.ker f).FG) :
    Module.Finite R (RingHom.ker f).Cotangent := by
  -- The extension `P` has ring `A` and structure map `f`, so `P.ker` is `RingHom.ker f` by
  -- definition of `Algebra.Extension.ofSurjective`.
  let P : Algebra.Extension R S := .ofSurjective f hf
  have : Module.Finite S P.Cotangent := Algebra.Extension.Cotangent.finite h
  have : Module.Finite R P.Cotangent := .trans S _
  exact .equiv (P.cotangentEquivCotangentKer.restrictScalars R)

/-- The cotangent space of the kernel of a surjection from a noetherian algebra onto a
module-finite algebra is finite over the base. -/
theorem finite_cotangent_ker [IsNoetherianRing A] (f : A →ₐ[R] S) (hf : Function.Surjective f) :
    Module.Finite R (RingHom.ker f).Cotangent :=
  finite_cotangent_ker_of_fg f hf (RingHom.ker f).fg_of_isNoetherianRing

end AlgHom
