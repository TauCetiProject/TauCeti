/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective

/-!
# Schanuel's lemma for projective presentations

Schanuel's lemma compares two surjections `π : P → M` and `ρ : Q → M` from projective modules: their
kernels agree after adding `Q` and `P`. This file proves it in the stronger *automorphism form*
that also records the maps: `π ∘ fst` and `ρ ∘ snd` are two maps `P × Q → M` which differ by an
automorphism of `P × Q`. The argument is that of Schanuel's lemma — lift each map through the other
and shear — and it needs no surjectivity, only that the two maps have the same range
(`TauCeti.exists_linearEquiv_comp_fst_eq_comp_snd_comp`).

The second shear follows the shear argument in the proof of `Submodule.minorsIdeal_ker_eq_prod_top`
in `TauCeti/RingTheory/FittingIdeal/Basic.lean`.

Applied twice, once to the surjections `P₀ → M` and `Q₀ → M` and once to the first maps of two
projective presentations `P₁ → P₀ → M → 0` and `Q₁ → Q₀ → M → 0`, it shows that any two
projective presentations of the same module become isomorphic as arrows once each is enlarged by
the identity of the other's middle term and by a zero map out of the remaining projectives
(`TauCeti.exists_linearEquiv_comp_prodMap_comp_fst_eq`). This is what makes a construction from a
projective presentation that is additive in the arrow — the Auslander–Bridger transpose, for
instance — independent of the presentation up to summands built from projectives.

## Main results

* `TauCeti.exists_comp_eq_of_range_le`: a map from a projective module factors through any map
  whose range contains its range.
* `TauCeti.exists_lift_projective_presentation`: module maps lift to commutative squares between
  projective presentations.
* `TauCeti.exists_linearEquiv_comp_fst_eq_comp_snd_comp`: two maps from projective modules with
  equal ranges differ, after stabilisation, by an automorphism.
* `TauCeti.exists_linearEquiv_comp_prodMap_comp_fst_eq`: two projective presentations of the same
  module are stably isomorphic as arrows.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189, Springer (1999),
  (5.1) (Schanuel's lemma).
-/

public section

namespace TauCeti

open LinearMap

variable {R : Type*} [Semiring R]

section EqualRange

variable {A B E : Type*} [AddCommMonoid E] [Module R E]

/-- A map from a projective module factors through any map whose range contains its range. This
is the lifting property of projective modules, applied to the corestriction onto the range. -/
theorem exists_comp_eq_of_range_le [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [Module.Projective R A] {a : A →ₗ[R] E}
    {b : B →ₗ[R] E} (h : range a ≤ range b) : ∃ α : A →ₗ[R] B, b ∘ₗ α = a := by
  obtain ⟨α, hα⟩ := Module.projective_lifting_property b.rangeRestrict
    (a.codRestrict (range b) fun x => h (mem_range_self a x)) b.surjective_rangeRestrict
  refine ⟨α, LinearMap.ext fun x => ?_⟩
  simpa using congrArg Subtype.val (LinearMap.congr_fun hα x)

/-- **Schanuel's lemma in automorphism form.** If `a : A → E` and `b : B → E` are maps from
projective modules with the same range, then `a ∘ fst` and `b ∘ snd`, as maps `A × B → E`, differ by
an automorphism of `A × B`.

For surjective `a` and `b` this is Schanuel's lemma: the automorphism carries
`ker (a ∘ fst) = ker a × B` onto `ker (b ∘ snd) = A × ker b`. -/
theorem exists_linearEquiv_comp_fst_eq_comp_snd_comp [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [Module.Projective R A]
    [Module.Projective R B] {a : A →ₗ[R] E} {b : B →ₗ[R] E} (h : range a = range b) :
    ∃ e : (A × B) ≃ₗ[R] (A × B), a ∘ₗ fst R A B = b ∘ₗ snd R A B ∘ₗ e.toLinearMap := by
  obtain ⟨α, hα⟩ := exists_comp_eq_of_range_le h.le
  obtain ⟨β, hβ⟩ := exists_comp_eq_of_range_le h.ge
  -- The shears `(x, y) ↦ (x, y + α x)` and `(x, y) ↦ (x + β y, y)` both turn the two maps
  -- into `a.coprod b`.
  let θ₁ : (A × B) ≃ₗ[R] (A × B) := (LinearEquiv.refl R A).skewProd (.refl R B) α
  let θ₂ : (A × B) ≃ₗ[R] (A × B) :=
    ((LinearEquiv.prodComm R A B).trans ((LinearEquiv.refl R B).skewProd (.refl R A) β)).trans
      (LinearEquiv.prodComm R B A)
  have h₁ : b ∘ₗ snd R A B ∘ₗ θ₁.toLinearMap = a.coprod b := by
    ext x <;> simp [θ₁, ← hα]
  have h₂ : a ∘ₗ fst R A B ∘ₗ θ₂.toLinearMap = a.coprod b := by
    ext x <;> simp [θ₂, ← hβ]
  refine ⟨θ₂.symm.trans θ₁, LinearMap.ext fun x => ?_⟩
  have := LinearMap.congr_fun (h₂.trans h₁.symm) (θ₂.symm x)
  simpa using this

end EqualRange

section LiftPresentation

variable {M N P₀ P₁ Q₀ Q₁ : Type*}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P₀] [Module R P₀] [AddCommMonoid P₁] [Module R P₁]
  [AddCommMonoid Q₀] [Module R Q₀] [AddCommMonoid Q₁] [Module R Q₁]
  {p : P₁ →ₗ[R] P₀} {q : Q₁ →ₗ[R] Q₀} {π : P₀ →ₗ[R] M} {ρ : Q₀ →ₗ[R] N}

/-- A map to a presented module lifts to a square from any complex with projective terms.
In particular, module maps lift to squares between projective presentations. The source needs
only a zero composite, and the target needs exactness and a surjective augmentation. -/
theorem exists_lift_projective_presentation [Module.Projective R P₀] [Module.Projective R P₁]
    (hp : π ∘ₗ p = 0) (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ)
    (f : M →ₗ[R] N) :
    ∃ (f₀ : P₀ →ₗ[R] Q₀) (f₁ : P₁ →ₗ[R] Q₁),
      ρ ∘ₗ f₀ = f ∘ₗ π ∧ f₀ ∘ₗ p = q ∘ₗ f₁ := by
  obtain ⟨f₀, hf₀⟩ := Module.projective_lifting_property ρ (f ∘ₗ π) hρ
  have hrange : range (f₀ ∘ₗ p) ≤ range q := by
    rw [← LinearMap.exact_iff.mp hq]
    rintro _ ⟨x, rfl⟩
    simp only [mem_ker, comp_apply]
    rw [← comp_apply, hf₀]
    simp only [comp_apply, ← comp_apply π p, hp, zero_apply, map_zero]
  obtain ⟨f₁, hf₁⟩ := exists_comp_eq_of_range_le hrange
  exact ⟨f₀, f₁, hf₀, hf₁.symm⟩

end LiftPresentation

section Presentation

variable {M P₀ P₁ Q₀ Q₁ : Type*} [AddCommMonoid M] [Module R M]
  [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
  [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]
  [Module.Projective R P₀] [Module.Projective R P₁]
  [Module.Projective R Q₀] [Module.Projective R Q₁]

/-- **Two projective presentations are stably isomorphic arrows.** Let `P₁ → P₀ → M → 0` and
`Q₁ → Q₀ → M → 0` be projective presentations of the same module, with first maps `f` and `g`.
Enlarge `f` to `(f ⊕ id_{Q₀}) ∘ fst : (P₁ × Q₀) × (P₀ × Q₁) → P₀ × Q₀` and `g` to
`(id_{P₀} ⊕ g) ∘ snd`, on the same source and target. These two arrows are isomorphic: there are
automorphisms `e₀` of the target and `e₁` of the source with `e₀ ∘ (f ⊕ id) ∘ fst =
(id ⊕ g) ∘ snd ∘ e₁`.

The presentations need not be finite, and the presented module is arbitrary. -/
theorem exists_linearEquiv_comp_prodMap_comp_fst_eq {f : P₁ →ₗ[R] P₀} {π : P₀ →ₗ[R] M}
    {g : Q₁ →ₗ[R] Q₀} {ρ : Q₀ →ₗ[R] M} (hf : Function.Exact f π) (hπ : Function.Surjective π)
    (hg : Function.Exact g ρ) (hρ : Function.Surjective ρ) :
    ∃ (e₀ : (P₀ × Q₀) ≃ₗ[R] (P₀ × Q₀))
      (e₁ : ((P₁ × Q₀) × (P₀ × Q₁)) ≃ₗ[R] ((P₁ × Q₀) × (P₀ × Q₁))),
      e₀.toLinearMap ∘ₗ f.prodMap id ∘ₗ fst R (P₁ × Q₀) (P₀ × Q₁) =
        (id : P₀ →ₗ[R] P₀).prodMap g ∘ₗ snd R (P₁ × Q₀) (P₀ × Q₁) ∘ₗ e₁.toLinearMap := by
  -- Schanuel's lemma on the two surjections onto `M`.
  obtain ⟨e₀, he₀⟩ := exists_linearEquiv_comp_fst_eq_comp_snd_comp
    (a := π) (b := ρ) (by rw [range_eq_top.mpr hπ, range_eq_top.mpr hρ])
  -- It carries `ker (π ∘ fst) = range f × Q₀` onto `ker (ρ ∘ snd) = P₀ × range g`.
  have hker : ∀ x : P₀ × Q₀, x ∈ range (f.prodMap (id : Q₀ →ₗ[R] Q₀)) ↔
      e₀ x ∈ range ((id : P₀ →ₗ[R] P₀).prodMap g) := by
    intro x
    have hx := LinearMap.congr_fun he₀ x
    simp only [coe_comp, Function.comp_apply, coe_fst, coe_snd, LinearEquiv.coe_coe] at hx
    rw [range_prodMap, range_prodMap, range_id, range_id, Submodule.mem_prod,
      Submodule.mem_prod, ← hf.linearMap_ker_eq, ← hg.linearMap_ker_eq, mem_ker, mem_ker, hx]
    simp
  -- Schanuel's lemma again, on the two first maps, which now have the same range.
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_comp_fst_eq_comp_snd_comp
    (a := e₀.toLinearMap ∘ₗ f.prodMap (id : Q₀ →ₗ[R] Q₀))
    (b := (id : P₀ →ₗ[R] P₀).prodMap g) <| by
      ext y
      refine ⟨?_, fun hy => ?_⟩
      · rintro ⟨x, rfl⟩
        exact (hker _).mp (mem_range_self _ x)
      · obtain ⟨x, hx⟩ := (hker (e₀.symm y)).mpr (by simpa using hy)
        exact ⟨x, by simp [hx]⟩
  exact ⟨e₀, e₁, he₁⟩

end Presentation

end TauCeti
