/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Category.ModuleCat.Indecomposable
import TauCeti.RingTheory.Length

/-!
# The Harada–Sai lemma

Let `M₀ → M₁ → ⋯ → Mₙ` be a chain of non-isomorphisms between indecomposable modules, each of
length at most `b`. The **Harada–Sai lemma** says that the composite vanishes as soon as
`n ≥ 2 ^ b - 1`. It is the basic finiteness statement of Auslander–Reiten theory: when the
indecomposable modules over a representation-finite algebra have length at most `b`, it makes the
`(2 ^ b - 1)`-th power of the radical of the module category vanish, and it is the first step
towards Auslander's theorem and the first Brauer–Thrall conjecture.

A chain of morphisms is encoded as a functor `F : ℕ ⥤ ModuleCat A`: the morphism `i ⟶ j` of `ℕ`
is sent to the composite `F.obj i ⟶ F.obj j`, and `F.map (homOfLE (Nat.le_add_right i 1))` is the
`i`-th link. A sequence of morphisms `f i : M i ⟶ M (i + 1)` gives such a functor through
Mathlib's `CategoryTheory.Functor.ofSequence`, whose value on `0 ⟶ n` is the composite of the
first `n` links.

## Main results

* `TauCeti.bijective_of_length_range_le_length_range_comp`: the inductive step. If `g : M → X`,
  `f : X → Y` and `h : Y → Z` are linear, `X` and `Y` are indecomposable, and the image of
  `h ∘ f ∘ g` is nonzero, of finite length, and at least as long as the images of `g` and `h`,
  then `f` is bijective.
* `TauCeti.length_range_map_le`: the length bound. For a chain of non-isomorphisms between
  indecomposable modules of length at most `b`, the composite of at least `2 ^ n - 1` links has
  image of length at most `b - n`.
* `TauCeti.map_eq_zero_of_length_le`: **the Harada–Sai lemma**, the case `n = b` of the bound.
* `TauCeti.ofSequence_map_eq_zero_of_length_le`: the same statement for a sequence of morphisms.

## Implementation notes

The proof is the classical induction on `n` ([ARS, Lemma VI.1.2], [ASS, Lemma IV.5.2]). Write
the composite of `2 ^ (n + 1) - 1` links as `h ∘ f ∘ g`, with `g` and `h` composites of
`2 ^ n - 1` links. The bound for `n` on `g` and `h` and the failure of the bound for `n + 1` force
the three images to have the same length. Then `h ∘ f` maps the image `U` of `g` isomorphically
onto the image of `h`, so the inclusion of `U` into `X` and the map `f` restricted to `U` are both
split injections into indecomposable modules
(`TauCeti.IsIndecomposableModule.bijective_of_bijective_comp`); hence `U = X` and `f` is
bijective.

## References

* M. Harada and Y. Sai, *On categories of indecomposable modules. I*, Osaka J. Math. 7 (1970),
  323–344, Lemma 12, where some composite of such a chain is shown to vanish.
* [ARS] M. Auslander, I. Reiten and S. O. Smalø, *Representation theory of Artin algebras*,
  Lemma VI.1.2 and Corollary VI.1.3.
* [ASS] I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of
  Associative Algebras, Vol. 1*, Lemma IV.5.2.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {A : Type u} [Ring A]

section Step

variable {M X Y Z : Type*} [AddCommGroup M] [Module A M] [AddCommGroup X] [Module A X]
  [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]

/-- **The Harada–Sai step.** Let `g : M →ₗ[A] X`, `f : X →ₗ[A] Y` and `h : Y →ₗ[A] Z` be linear
maps between `A`-modules, with `X` and `Y` indecomposable. If the image of `h ∘ₗ f ∘ₗ g` is
nonzero, has finite length, and is at least as long as the images of `g` and of `h`, then `f` is
bijective. -/
theorem bijective_of_length_range_le_length_range_comp (hX : IsIndecomposableModule A X)
    (hY : IsIndecomposableModule A Y) {g : M →ₗ[A] X} {f : X →ₗ[A] Y} {h : Y →ₗ[A] Z}
    (hne : LinearMap.range (h ∘ₗ f ∘ₗ g) ≠ ⊥)
    (hfin : Module.length A (LinearMap.range (h ∘ₗ f ∘ₗ g)) ≠ ⊤)
    (hg : Module.length A (LinearMap.range g) ≤ Module.length A (LinearMap.range (h ∘ₗ f ∘ₗ g)))
    (hh : Module.length A (LinearMap.range h) ≤ Module.length A (LinearMap.range (h ∘ₗ f ∘ₗ g))) :
    Function.Bijective f := by
  set U := LinearMap.range g
  set V := LinearMap.range (h ∘ₗ f ∘ₗ g)
  -- The image `V` of the composite lies in the image of `h` and is as long, so the two agree.
  have hVh : V ≤ LinearMap.range h := LinearMap.range_comp_le_range _ _
  have hle : Module.length A V ≤ Module.length A (LinearMap.range h) :=
    Module.length_le_of_injective _ (Submodule.inclusion_injective hVh)
  have hVh_len := le_antisymm hle hh
  have hhV : LinearMap.range h ≤ V := (Submodule.eq_of_le_of_length_eq hVh hfin hVh_len).ge
  -- So `h ∘ₗ f` maps `U` onto the image of `h`, and the lengths force this map to be injective.
  let θ := h.rangeRestrict ∘ₗ f ∘ₗ U.subtype
  have hθs : Function.Surjective θ := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := hhV hy
    exact ⟨⟨g m, m, rfl⟩, rfl⟩
  have hθi : Function.Injective θ :=
    injective_of_surjective_of_length_eq hθs (hVh_len ▸ hfin)
      (le_antisymm (hg.trans hle) (Module.length_le_of_surjective _ hθs))
  have : Nontrivial U := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro hU
    rw [LinearMap.range_eq_bot] at hU
    exact hne (by simp [V, hU])
  -- The inclusion of `U` and the restriction of `f` to `U` split, through the inverse of `θ`, so
  -- both are bijective.
  let e := LinearEquiv.ofBijective θ ⟨hθi, hθs⟩
  have he : Function.Bijective (e.symm.toLinearMap ∘ₗ θ) := e.symm.bijective.comp e.bijective
  have hι : Function.Bijective U.subtype :=
    hX.bijective_of_bijective_comp (g := e.symm.toLinearMap ∘ₗ h.rangeRestrict ∘ₗ f) he
  have hfι : Function.Bijective (f ∘ₗ U.subtype) :=
    hY.bijective_of_bijective_comp (g := e.symm.toLinearMap ∘ₗ h.rangeRestrict) he
  exact (Function.Bijective.of_comp_iff f hι).mp hfι

end Step

section Chain

variable {F : ℕ ⥤ ModuleCat.{v} A} {b : ℕ}

/-- **The Harada–Sai bound.** Let `F : ℕ ⥤ ModuleCat A` be a chain of modules whose links
`F.obj i ⟶ F.obj (i + 1)` are not isomorphisms, between indecomposable modules of length at most
`b`. Then the composite `F.obj i ⟶ F.obj j` of at least `2 ^ n - 1` links has image of length at
most `b - n`. -/
theorem length_range_map_le (hF : ∀ i, Indecomposable (F.obj i))
    (hlen : ∀ i, Module.length A (F.obj i) ≤ b)
    (hf : ∀ i, ¬ IsIso (F.map (homOfLE (Nat.le_add_right i 1)))) (n : ℕ) {i j : ℕ} (φ : i ⟶ j)
    (hij : i + (2 ^ n - 1) ≤ j) :
    Module.length A (LinearMap.range (F.map φ).hom) ≤ (b - n : ℕ) := by
  have hrange {i j : ℕ} (φ : i ⟶ j) : Module.length A (LinearMap.range (F.map φ).hom) ≤ b :=
    (Module.length_le_of_injective _ (Submodule.injective_subtype _)).trans (hlen j)
  induction n generalizing i j with
  | zero => simpa using hrange φ
  | succ n ih =>
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ, mul_two]
    have hpos := Nat.one_le_two_pow (n := n)
    by_cases hbn : b ≤ n
    · exact (ih φ (by omega)).trans (Nat.cast_le.mpr (by omega))
    -- Split the composite as `g`, then the link at `a`, then `h`, with `g` and `h` composites of
    -- `2 ^ n - 1` links, and argue by contradiction that the link at `a` is an isomorphism.
    set a := i + (2 ^ n - 1)
    have hφ : (F.map φ).hom = (F.map (homOfLE (by omega : a + 1 ≤ j))).hom ∘ₗ
        (F.map (homOfLE (Nat.le_add_right a 1))).hom ∘ₗ
        (F.map (homOfLE (Nat.le_add_right i _ : i ≤ a))).hom := by
      simp only [← ModuleCat.hom_comp, ← Functor.map_comp]
      congr 2
    by_contra hcon
    have hc : ((b - n : ℕ) : ℕ∞) ≤ Module.length A (LinearMap.range (F.map φ).hom) := by
      rw [show b - n = b - (n + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt (not_le.mp hcon)
    have hg := ih (homOfLE (Nat.le_add_right i (2 ^ n - 1))) le_rfl
    have hh := ih (homOfLE (by omega : a + 1 ≤ j)) (by omega)
    have hfin := (hrange φ).trans_lt (WithTop.coe_lt_top b)
    rw [hφ] at hc hfin
    refine hf a ((ConcreteCategory.isIso_iff_bijective _).mpr ?_)
    refine bijective_of_length_range_le_length_range_comp
      ((indecomposable_iff_isIndecomposableModule _).mp (hF a))
      ((indecomposable_iff_isIndecomposableModule _).mp (hF (a + 1))) ?_ hfin.ne (hg.trans hc)
      (hh.trans hc)
    intro hbot
    rw [hbot, Module.length_bot] at hc
    have : b - n ≤ 0 := by exact_mod_cast hc
    omega

/-- **The Harada–Sai lemma.** Let `F : ℕ ⥤ ModuleCat A` be a chain of modules whose links
`F.obj i ⟶ F.obj (i + 1)` are not isomorphisms, between indecomposable modules of length at most
`b`. Then every composite `F.obj i ⟶ F.obj j` of at least `2 ^ b - 1` links is zero. -/
theorem map_eq_zero_of_length_le (hF : ∀ i, Indecomposable (F.obj i))
    (hlen : ∀ i, Module.length A (F.obj i) ≤ b)
    (hf : ∀ i, ¬ IsIso (F.map (homOfLE (Nat.le_add_right i 1)))) {i j : ℕ} (φ : i ⟶ j)
    (hij : i + (2 ^ b - 1) ≤ j) : F.map φ = 0 := by
  have h := length_range_map_le hF hlen hf b φ hij
  simp only [Nat.sub_self, Nat.cast_zero, nonpos_iff_eq_zero, Module.length_eq_zero_iff,
    Submodule.subsingleton_iff_eq_bot, LinearMap.range_eq_bot] at h
  exact ModuleCat.hom_ext h

/-- **The Harada–Sai lemma**, for a sequence of morphisms `f i : M i ⟶ M (i + 1)` that are not
isomorphisms, between indecomposable modules of length at most `b`: the composite
`M 0 ⟶ M n` of the first `n` of them is zero once `n ≥ 2 ^ b - 1`. -/
theorem ofSequence_map_eq_zero_of_length_le {M : ℕ → ModuleCat.{v} A}
    (f : ∀ i, M i ⟶ M (i + 1)) (hM : ∀ i, Indecomposable (M i))
    (hlen : ∀ i, Module.length A (M i) ≤ b) (hf : ∀ i, ¬ IsIso (f i)) {n : ℕ}
    (hn : 2 ^ b - 1 ≤ n) : (Functor.ofSequence f).map (homOfLE (Nat.zero_le n)) = 0 :=
  map_eq_zero_of_length_le hM hlen
    (fun i ↦ by rw [Functor.ofSequence_map_homOfLE_succ]; exact hf i) _ (by omega)

end Chain

end TauCeti
