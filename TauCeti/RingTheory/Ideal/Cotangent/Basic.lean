/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Basic
public import TauCeti.RingTheory.Ideal.Maps
import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# Cotangent spaces of ideals and kernels

If elements `f₁, f₂, …` generate an ideal `I`, their classes span the conormal module `I ⧸ I²`
over `R ⧸ I`. Conversely, elements of an ideal `I` of `A` whose images span the cotangent space
`I ⧸ I ^ 2` over `A` generate `I` modulo `I ^ 2`. For a surjective `R`-algebra homomorphism
`f : A →ₐ[R] S` onto a module-finite `R`-algebra, if the kernel of `f` is finitely generated over
`A`, then its cotangent space is finite over `R`. The main case is an augmentation
`f : A →ₐ[R] R`, whose kernel is the augmentation ideal. A square-zero ideal `I` is isomorphic to
its cotangent space, which makes `I` a module over `R ⧸ I`.

For a ring homomorphism `f : R →+* S` carrying an ideal `I` into `J`, surjectivity on
`R ⧸ I → S ⧸ J` and on the conormal pieces `I ⧸ I ^ 2 → J ⧸ J ^ 2` propagates to every graded piece
`I ^ n ⧸ I ^ (n + 1) → J ^ n ⧸ J ^ (n + 1)` (`RingHom.exists_mem_pow_sub_mem_pow_succ`) and hence
to every infinitesimal quotient `R ⧸ I ^ n → S ⧸ J ^ n` (`RingHom.quotientMap_pow_surjective`).

## Main declarations

* `Ideal.span_range_toCotangent_eq_top`: the classes of generators of `I` span `I ⧸ I²` over
  `R ⧸ I`.
* `Ideal.le_span_sup_sq_of_span_toCotangent_eq_top`: elements whose images span the cotangent
  space generate the ideal modulo its square.
* `Ideal.toCotangentEquivOfSqEqBot`: a square-zero ideal is isomorphic to its cotangent space.
* `RingHom.exists_mem_pow_sub_mem_pow_succ`: surjectivity modulo `J` and on `I ⧸ I ^ 2 → J ⧸ J ^ 2`
  implies surjectivity on every graded piece `I ^ n ⧸ I ^ (n + 1) → J ^ n ⧸ J ^ (n + 1)`.
* `RingHom.quotientMap_pow_surjective`: surjectivity modulo `J` and on `I ⧸ I ^ 2 → J ⧸ J ^ 2`
  implies surjectivity of `Ideal.quotientMap (J ^ n) f _` for every `n`.
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
    (Submodule.span_range_subtype_eq_top_iff I fun i ↦ (f i).property).mpr hf
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

section SqEqBot

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- For a square-zero ideal `I`, the quotient map `I → I ⧸ I²` is an isomorphism of `R`-modules.
Through it a square-zero ideal is a module over `R ⧸ I`. -/
noncomputable def toCotangentEquivOfSqEqBot (hI : I ^ 2 = ⊥) : I ≃ₗ[R] I.Cotangent :=
  .ofBijective I.toCotangent
    ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ by
      simpa [hI] using (I.toCotangent_eq_zero x).mp hx, I.toCotangent_surjective⟩

@[simp]
theorem toCotangentEquivOfSqEqBot_apply (hI : I ^ 2 = ⊥) (x : I) :
    I.toCotangentEquivOfSqEqBot hI x = I.toCotangent x :=
  LinearEquiv.ofBijective_apply _ _

@[simp]
theorem toCotangentEquivOfSqEqBot_symm_apply (hI : I ^ 2 = ⊥) (x : I) :
    (I.toCotangentEquivOfSqEqBot hI).symm (I.toCotangent x) = x :=
  (LinearEquiv.symm_apply_eq _).mpr (by simp)

end SqEqBot

end Ideal

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Surjectivity of a ring homomorphism `f : R →+* S` with `I ≤ J.comap f` on `R ⧸ I → S ⧸ J`
and on `I ⧸ I ^ 2 → J ⧸ J ^ 2` implies surjectivity on every graded piece
`I ^ n ⧸ I ^ (n + 1) → J ^ n ⧸ J ^ (n + 1)`. -/
theorem exists_mem_pow_sub_mem_pow_succ {I : Ideal R} {J : Ideal S} (f : R →+* S)
    (hf : I ≤ J.comap f)
    (hquot : Function.Surjective (Ideal.quotientMap J f hf))
    (hcot : ∀ y ∈ J, ∃ x ∈ I, y - f x ∈ J ^ 2) :
    ∀ n : ℕ, ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, y - f x ∈ J ^ (n + 1)
  | 0, y, _ => by
    obtain ⟨x, hx⟩ := Ideal.exists_sub_mem_of_surjective_quotient_mk_comp
      (hquot.comp Ideal.Quotient.mk_surjective) y
    exact ⟨x, by simp, by simpa using hx⟩
  | 1, y, hy => by
    simpa only [pow_one] using hcot y (by simpa only [pow_one] using hy)
  | n + 2, y, hy => by
    have ih := f.exists_mem_pow_sub_mem_pow_succ hf hquot hcot (n + 1)
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun u v hu hv => ?_)
    · obtain ⟨u, hu, hau⟩ := ih a ha
      obtain ⟨v, hv, hbv⟩ := hcot b hb
      refine ⟨u * v, pow_succ I (n + 1) ▸ Ideal.mul_mem_mul hu hv, ?_⟩
      have hdecomp : a * b - f (u * v) = (a - f u) * b + f u * (b - f v) := by
        rw [map_mul]
        ring
      rw [hdecomp]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hau hb
      · have hfu : f u ∈ J ^ (n + 1) := Ideal.pow_le_comap_pow_of_le_comap f hf (n + 1) hu
        have hpow : J ^ (n + 1) * J ^ 2 = J ^ (n + 3) := by
          rw [← pow_add]
        rw [← hpow]
        exact Ideal.mul_mem_mul hfu hbv
    · obtain ⟨x₁, hx₁, hy₁⟩ := hu
      obtain ⟨x₂, hx₂, hy₂⟩ := hv
      refine ⟨x₁ + x₂, Ideal.add_mem _ hx₁ hx₂, ?_⟩
      have hdecomp : (u + v) - f (x₁ + x₂) = (u - f x₁) + (v - f x₂) := by
        rw [map_add]
        ring
      rw [hdecomp]
      exact Ideal.add_mem _ hy₁ hy₂

/-- A ring homomorphism `f : R →+* S` with `I ≤ J.comap f` that is surjective on `R ⧸ I → S ⧸ J`
and on `I ⧸ I ^ 2 → J ⧸ J ^ 2` is surjective on `R ⧸ I ^ n → S ⧸ J ^ n` for every `n`. -/
theorem quotientMap_pow_surjective {I : Ideal R} {J : Ideal S} (f : R →+* S)
    (hf : I ≤ J.comap f)
    (hquot : Function.Surjective (Ideal.quotientMap J f hf))
    (hcot : ∀ y ∈ J, ∃ x ∈ I, y - f x ∈ J ^ 2) (n : ℕ) :
    Function.Surjective
      (Ideal.quotientMap (J ^ n) f (Ideal.pow_le_comap_pow_of_le_comap f hf n)) := by
  have hstep : ∀ k : ℕ, ∀ y : S, ∃ x : R, y - f x ∈ J ^ k := by
    intro k
    induction k with
    | zero => intro y; exact ⟨0, by simp⟩
    | succ k ih =>
      intro y
      obtain ⟨x₁, hx₁⟩ := ih y
      obtain ⟨x₂, -, hx₂⟩ :=
        f.exists_mem_pow_sub_mem_pow_succ hf hquot hcot k (y - f x₁) hx₁
      refine ⟨x₁ + x₂, ?_⟩
      have hdecomp : y - f (x₁ + x₂) = (y - f x₁) - f x₂ := by
        rw [map_add]
        ring
      rwa [hdecomp]
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, hx⟩ := hstep n y
  refine ⟨Ideal.Quotient.mk (I ^ n) x, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  simpa only [neg_sub] using (J ^ n).neg_mem hx

end RingHom

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
