/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.Algebra.Module.Projective.Schanuel
public import TauCeti.Algebra.Module.PseudoCoherent.FiniteProjectiveDimension

/-!
# Finite free resolutions

A module `M` over a ring `R` has a *finite free resolution of length at most `n`* when there is an
exact sequence `0 → Fₙ → ⋯ → F₁ → F₀ → M → 0` of finite free `R`-modules. This file defines the
notion recursively, as in Lang's *Algebra*: `M` is finite free when `n = 0`, and for `n = m + 1`
some surjection `Rᵏ → M` has a kernel with a finite free resolution of length at most `m`.

Finite free resolutions are the algebraic input of the Quillen–Suslin type theorems: a finite
projective module with a finite free resolution is stably free, and a finite free resolution
survives a change of rings that is exact enough. This file proves the first fact and the
*two out of three* property for short exact sequences, from which a module built by finitely many
extensions out of pieces with finite free resolutions has one itself.

All modules live in the universe of `R`, as do the kernels of maps out of `Fin k → R`.

## Main definitions

* `TauCeti.Module.HasFiniteFreeResolutionLE R n M`: `M` has a finite free resolution of length at
  most `n`.
* `TauCeti.Module.HasFiniteFreeResolution R M`: `M` has a finite free resolution of some length.

## Main results

* `TauCeti.Module.HasFiniteFreeResolutionLE.mono`: the length can always be increased.
* `TauCeti.Module.HasFiniteFreeResolutionLE.isFPD`: a finite free resolution of length at most
  `n` is a finite projective resolution of length at most `n`; in particular the module is
  finitely presented (`TauCeti.Module.HasFiniteFreeResolution.finitePresentation`).
* `TauCeti.Module.HasFiniteFreeResolutionLE.extension`: an extension of two modules with finite
  free resolutions of length at most `n` has one (the horseshoe lemma).
* `TauCeti.Module.HasFiniteFreeResolutionLE.ker`: Schanuel's lemma for finite free resolutions;
  the kernel of every surjection onto `M` from a finite free module has a finite free resolution.
* `TauCeti.Module.HasFiniteFreeResolution.extension`, `.cokernel`, `.kernel`: two out of three for
  a short exact sequence `0 → M₁ → M → M₂ → 0`.
* `TauCeti.Module.HasFiniteFreeResolution.isStablyFree`: a projective module with a finite free
  resolution is stably free.
* `TauCeti.Module.hasFiniteFreeResolution_iff_isStablyFree`: a finite projective module has a
  finite free resolution if and only if it is stably free, and then it has one of length at most
  one.

## References

* S. Lang, *Algebra*, third edition, Graduate Texts in Mathematics 211, Springer (2002),
  Chapter XXI, §2, Theorem 2.1 and Lemma 2.7.
* K. S. Kedlaya, *Full faithfulness for overconvergent F-isocrystals*, §6, Propositions 6.5
  and 6.6, which apply them.
-/

public section

namespace TauCeti.Module

open LinearMap

universe u

section Definition

variable (R : Type u) [Ring R]

/-- `M` has a finite free resolution of length at most `n`: for `n = 0`, `M` is finite and free;
for `n = m + 1`, some surjection `(Fin k → R) → M` has a kernel with a finite free resolution of
length at most `m`. Unwound, this is an exact sequence `0 → Fₙ → ⋯ → F₀ → M → 0` of finite free
`R`-modules. -/
def HasFiniteFreeResolutionLE : ℕ → (M : Type u) → [AddCommGroup M] → [Module R M] → Prop
  | 0, M, _, _ => Module.Finite R M ∧ Module.Free R M
  | n + 1, M, _, _ => ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] M),
      Function.Surjective f ∧ HasFiniteFreeResolutionLE n (ker f)

/-- `M` has a finite free resolution `0 → Fₙ → ⋯ → F₀ → M → 0` of some length `n`. -/
def HasFiniteFreeResolution (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∃ n, HasFiniteFreeResolutionLE R n M

variable {R} {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}

/-- A finite free resolution of length at most `0` is a finite free module. -/
@[simp]
theorem hasFiniteFreeResolutionLE_zero_iff :
    HasFiniteFreeResolutionLE R 0 M ↔ Module.Finite R M ∧ Module.Free R M :=
  Iff.rfl

/-- A finite free resolution of length at most `n + 1` is a surjection from `Fin k → R` whose kernel
has a finite free resolution of length at most `n`. -/
theorem hasFiniteFreeResolutionLE_succ_iff :
    HasFiniteFreeResolutionLE R (n + 1) M ↔ ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] M),
      Function.Surjective f ∧ HasFiniteFreeResolutionLE R n (ker f) :=
  Iff.rfl

/-- A finite free resolution is a finite free resolution of length at most `n` for some `n`. -/
theorem hasFiniteFreeResolution_iff :
    HasFiniteFreeResolution R M ↔ ∃ n, HasFiniteFreeResolutionLE R n M :=
  Iff.rfl

end Definition

variable {R : Type u} [Ring R] {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {n : ℕ}

/-- A finite free module has a finite free resolution of length zero. -/
theorem hasFiniteFreeResolutionLE_zero [Module.Finite R M] [Module.Free R M] :
    HasFiniteFreeResolutionLE R 0 M :=
  hasFiniteFreeResolutionLE_zero_iff.mpr ⟨‹_›, ‹_›⟩

namespace HasFiniteFreeResolutionLE

/-- Finite free resolutions of bounded length transport along linear equivalences. -/
theorem of_equiv (e : M ≃ₗ[R] N) (h : HasFiniteFreeResolutionLE R n M) :
    HasFiniteFreeResolutionLE R n N := by
  induction n generalizing M N with
  | zero =>
    obtain ⟨_, _⟩ := hasFiniteFreeResolutionLE_zero_iff.mp h
    exact hasFiniteFreeResolutionLE_zero_iff.mpr ⟨.equiv e, .of_equiv e⟩
  | succ n ih =>
    obtain ⟨k, f, hf, hK⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h
    exact hasFiniteFreeResolutionLE_succ_iff.mpr ⟨k, e.toLinearMap ∘ₗ f, e.surjective.comp hf,
      ih (.ofEq _ _ (LinearEquiv.ker_comp e f).symm) hK⟩

/-- A surjection onto `M` from any finite free module, whose kernel has a finite free resolution of
length at most `n`, gives a finite free resolution of `M` of length at most `n + 1`. -/
theorem succ_of_surjective {F : Type u} [AddCommGroup F] [Module R F] [Module.Finite R F]
    [Module.Free R F] {f : F →ₗ[R] M} (hf : Function.Surjective f)
    (h : HasFiniteFreeResolutionLE R n (ker f)) : HasFiniteFreeResolutionLE R (n + 1) M := by
  -- Identify `F` with `Fin k → R` through a finite basis.
  let b := (Module.Free.chooseBasis R F).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex R F))
  let e : (Fin _ → R) ≃ₗ[R] F := b.equivFun.symm
  have hker : (ker (f ∘ₗ e.toLinearMap)).map e.toLinearMap = ker f := by
    rw [ker_comp, Submodule.map_comap_eq_of_surjective e.surjective]
  exact hasFiniteFreeResolutionLE_succ_iff.mpr
    ⟨_, f ∘ₗ e.toLinearMap, hf.comp e.surjective, h.of_equiv (e.ofSubmodules _ _ hker).symm⟩

/-- A finite free resolution of length at most `n` is one of length at most `n + 1`. -/
theorem succ (h : HasFiniteFreeResolutionLE R n M) : HasFiniteFreeResolutionLE R (n + 1) M := by
  induction n generalizing M with
  | zero =>
    obtain ⟨_, _⟩ := hasFiniteFreeResolutionLE_zero_iff.mp h
    -- The identity of `M` has kernel zero.
    have : Subsingleton (ker (LinearMap.id : M →ₗ[R] M)) := by
      rw [ker_id]
      infer_instance
    exact succ_of_surjective (f := LinearMap.id) Function.surjective_id
      (hasFiniteFreeResolutionLE_zero_iff.mpr ⟨Module.Finite.of_finite, inferInstance⟩)
  | succ n ih =>
    obtain ⟨k, f, hf, hK⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h
    exact hasFiniteFreeResolutionLE_succ_iff.mpr ⟨k, f, hf, ih hK⟩

/-- **The length of a finite free resolution can be increased.** -/
theorem mono {m : ℕ} (h : HasFiniteFreeResolutionLE R n M) (hnm : n ≤ m) :
    HasFiniteFreeResolutionLE R m M := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ _ _ ih => exact ih.succ

/-- A finite free resolution of length at most `n` is a resolution of length at most `n` by
finitely generated projective modules. -/
theorem isFPD (h : HasFiniteFreeResolutionLE R n M) : IsFPD R M n := by
  induction n generalizing M with
  | zero =>
    obtain ⟨_, _⟩ := hasFiniteFreeResolutionLE_zero_iff.mp h
    exact .of_projective
  | succ n ih =>
    obtain ⟨k, f, hf, hK⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h
    exact (IsFPD.succ_iff_ker hf).mpr (ih hK)

/-- A module with a finite free resolution is finitely generated. -/
theorem finite (h : HasFiniteFreeResolutionLE R n M) : Module.Finite R M :=
  h.isFPD.isPseudoCoherentOver.finite

/-- **Horseshoe lemma.** In a short exact sequence `0 → M₁ → M → M₂ → 0`, if `M₁` and `M₂` have
finite free resolutions of length at most `n`, so does `M`. -/
theorem extension {M₁ M₂ : Type u} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] {f : M₁ →ₗ[R] M} {g : M →ₗ[R] M₂} (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : HasFiniteFreeResolutionLE R n M₁) (h₂ : HasFiniteFreeResolutionLE R n M₂) :
    HasFiniteFreeResolutionLE R n M := by
  induction n generalizing M₁ M M₂ with
  | zero =>
    obtain ⟨_, _⟩ := hasFiniteFreeResolutionLE_zero_iff.mp h₁
    obtain ⟨_, _⟩ := hasFiniteFreeResolutionLE_zero_iff.mp h₂
    -- The sequence splits because `M₂` is projective.
    obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
    exact hasFiniteFreeResolutionLE_zero.of_equiv
      (hfg.splitSurjectiveEquiv hf ⟨s, hs⟩).1.symm
  | succ n ih =>
    obtain ⟨a, f₁, hf₁, hK₁⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h₁
    obtain ⟨b, f₂, hf₂, hK₂⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h₂
    -- Lift `f₂` through `g` and combine it with `f ∘ f₁` into a surjection `F : Rᵃ × Rᵇ → M`.
    obtain ⟨l, hl⟩ := Module.projective_lifting_property g f₂ hg
    have hl' (y : Fin b → R) : g (l y) = f₂ y := LinearMap.congr_fun hl y
    let F := (f ∘ₗ f₁).coprod l
    have hF : Function.Surjective F := by
      intro m
      obtain ⟨y, hy⟩ := hf₂ (g m)
      obtain ⟨m₁, hm₁⟩ := (hfg (m - l y)).mp (by simp [hl', hy])
      obtain ⟨x, rfl⟩ := hf₁ m₁
      exact ⟨(x, y), by simp [F, hm₁]⟩
    -- The kernels form a short exact sequence `0 → ker f₁ → ker F → ker f₂ → 0`.
    have hi (x : ker f₁) : F (x.1, 0) = 0 := by simp [F, mem_ker.mp x.2]
    have hF0 (z : ker F) : f (f₁ z.1.1) + l z.1.2 = 0 := mem_ker.mp z.2
    have hp (z : ker F) : f₂ z.1.2 = 0 := by
      rw [← hl', eq_neg_of_add_eq_zero_right (hF0 z), map_neg, hfg.apply_apply_eq_zero, neg_zero]
    let i : ker f₁ →ₗ[R] ker F :=
      (inl R _ _ ∘ₗ (ker f₁).subtype).codRestrict (ker F) hi
    let p : ker F →ₗ[R] ker f₂ := (snd R _ _ ∘ₗ (ker F).subtype).codRestrict (ker f₂) hp
    refine succ_of_surjective hF (ih (f := i) (g := p) (fun x y hxy ↦ ?_) (fun y ↦ ?_)
      (fun z ↦ ⟨fun hz ↦ ?_, ?_⟩) hK₁ hK₂)
    · exact Subtype.ext congr(($hxy).1.1)
    · obtain ⟨m₁, hm₁⟩ := (hfg (l y)).mp (by simp [hl', mem_ker.mp y.2])
      obtain ⟨x, rfl⟩ := hf₁ m₁
      exact ⟨⟨(-x, y), by simp [F, hm₁]⟩, rfl⟩
    · have hz2 : z.1.2 = 0 := congr(($hz).1)
      have hz1 : f₁ z.1.1 = 0 := hf (by simpa [hz2] using hF0 z)
      exact ⟨⟨z.1.1, hz1⟩, Subtype.ext (Prod.ext rfl hz2.symm)⟩
    · rintro ⟨x, rfl⟩
      rfl

/-- Resolutions of `M` and `N` of length at most `n` give one of `M × N`. -/
theorem prod (h : HasFiniteFreeResolutionLE R n M) (h' : HasFiniteFreeResolutionLE R n N) :
    HasFiniteFreeResolutionLE R n (M × N) :=
  extension LinearMap.inl_injective LinearMap.snd_surjective Function.Exact.inl_snd h h'

/-- **Removing a finite free summand.** If `M × F` has a finite free resolution of length at most
`n` and `F` is finite free, then `M` has one of length at most `max n 1`. The length can grow from
`0` to `1`: a stably free module that is not free is a summand of a free module. -/
theorem of_prod {F : Type u} [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
    (h : HasFiniteFreeResolutionLE R n (M × F)) : HasFiniteFreeResolutionLE R (max n 1) M := by
  cases n with
  | zero =>
    obtain ⟨_, _⟩ := hasFiniteFreeResolutionLE_zero_iff.mp h
    -- The projection `M × F → M` has kernel `F`.
    exact succ_of_surjective (f := fst R M F) fst_surjective
      (hasFiniteFreeResolutionLE_zero.of_equiv
        ((LinearEquiv.ofInjective (inr R M F) inr_injective).trans
          (.ofEq _ _ (ker_fst (R := R) (M := M) (M₂ := F)).symm)))
  | succ n =>
    obtain ⟨k, φ, hφ, hK⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h
    -- The kernels of `φ` and `fst ∘ φ` differ by `F`.
    have hp (z : ker (fst R M F ∘ₗ φ)) : φ z = (0, (φ z).2) :=
      Prod.ext (mem_ker.mp z.2) rfl
    rw [max_eq_left (by omega)]
    refine hasFiniteFreeResolutionLE_succ_iff.mpr ⟨k, fst R M F ∘ₗ φ,
      (fst_surjective (R := R) (M := M) (M₂ := F)).comp hφ,
      extension (f := Submodule.inclusion (ker_le_ker_comp φ (fst R M F)))
        (g := snd R M F ∘ₗ φ ∘ₗ (ker (fst R M F ∘ₗ φ)).subtype) (Submodule.inclusion_injective _)
        (fun y ↦ ?_) (fun z ↦ ⟨fun hz ↦ ?_, ?_⟩) hK
        (hasFiniteFreeResolutionLE_zero.mono n.zero_le)⟩
    · obtain ⟨x, hx⟩ := hφ (0, y)
      exact ⟨⟨x, by simp [hx]⟩, by simp [hx]⟩
    · have hz' : φ z = 0 := (hp z).trans (Prod.ext rfl hz)
      exact ⟨⟨z, hz'⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      simp [mem_ker.mp x.2]

/-- **Schanuel's lemma for finite free resolutions.** If `M` has a finite free resolution of length
at most `n + 1`, then the kernel of every surjection onto `M` from a finite free module has one of
length at most `max n 1`. -/
theorem ker_of_surjective {P : Type u} [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Free R P] {f : P →ₗ[R] M} (hf : Function.Surjective f)
    (h : HasFiniteFreeResolutionLE R (n + 1) M) :
    HasFiniteFreeResolutionLE R (max n 1) (ker f) := by
  obtain ⟨k, f', hf', hK⟩ := h
  -- The fibre product `X = P ×_M Rᵏ` is an extension of `P` by `ker f'` and of `Rᵏ` by `ker f`.
  let X := ker (f ∘ₗ fst R P (Fin k → R) - f' ∘ₗ snd R P (Fin k → R))
  have hX (z : X) : f z.1.1 = f' z.1.2 := by
    have hz := mem_ker.mp z.2
    rw [LinearMap.sub_apply, sub_eq_zero] at hz
    exact hz
  have hXres : HasFiniteFreeResolutionLE R n X := by
    refine extension (f := ((inr R P _ ∘ₗ (ker f').subtype).codRestrict X fun y ↦ by
        simp [X, mem_ker.mp y.2]))
      (g := fst R P _ ∘ₗ X.subtype) (fun x y hxy ↦ Subtype.ext congr(($hxy).1.2)) (fun x ↦ ?_)
      (fun z ↦ ⟨fun hz ↦ ?_, ?_⟩) hK (hasFiniteFreeResolutionLE_zero.mono n.zero_le)
    · obtain ⟨y, hy⟩ := hf' (f x)
      exact ⟨⟨(x, y), by simp [X, hy]⟩, rfl⟩
    · have hz : z.1.1 = 0 := by simpa using hz
      have hz2 : f' z.1.2 = 0 := by rw [← hX, hz, map_zero]
      exact ⟨⟨z.1.2, hz2⟩, Subtype.ext (Prod.ext hz.symm rfl)⟩
    · rintro ⟨y, rfl⟩
      rfl
  -- Splitting off `Rᵏ`, which is free, leaves `ker f`.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (snd R P (Fin k → R) ∘ₗ X.subtype)
    LinearMap.id fun y ↦ by
      obtain ⟨x, hx⟩ := hf (f' y)
      exact ⟨⟨(x, y), by simp [X, hx]⟩, rfl⟩
  let ι : ker f →ₗ[R] X :=
    (inl R P _ ∘ₗ (ker f).subtype).codRestrict X fun x ↦ by simp [X, mem_ker.mp x.2]
  have hι : Function.Exact ι (snd R P (Fin k → R) ∘ₗ X.subtype) := fun z ↦ by
    refine ⟨fun hz ↦ ?_, ?_⟩
    · have hz : z.1.2 = 0 := by simpa using hz
      have hz1 : f z.1.1 = 0 := by rw [hX, hz, map_zero]
      exact ⟨⟨z.1.1, hz1⟩, Subtype.ext (Prod.ext rfl hz.symm)⟩
    · rintro ⟨x, rfl⟩
      rfl
  exact of_prod (hXres.of_equiv (hι.splitSurjectiveEquiv
    (fun x y hxy ↦ Subtype.ext congr(($hxy).1.1)) ⟨s, hs⟩).1)

/-- For a short exact sequence `0 → M₁ → M → M₂ → 0` and a surjection `F : P → M`, the inclusion
`ker F → ker (g ∘ F)` has cokernel `M₁`: the map `ker (g ∘ F) → M₁` takes `z` to the preimage of
`F z` under `f`. -/
private theorem exists_exact_inclusion_ker_comp {M₁ M₂ P : Type u} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup P] [Module R P] {f : M₁ →ₗ[R] M}
    {g : M →ₗ[R] M₂} (hf : Function.Injective f) (hfg : Function.Exact f g) {F : P →ₗ[R] M}
    (hF : Function.Surjective F) :
    ∃ q : ker (g ∘ₗ F) →ₗ[R] M₁, Function.Surjective q ∧
      Function.Exact (Submodule.inclusion (ker_le_ker_comp F g)) q := by
  let e := LinearEquiv.ofInjective f hf
  let q : ker (g ∘ₗ F) →ₗ[R] M₁ := e.symm.toLinearMap ∘ₗ
    ((F ∘ₗ (ker (g ∘ₗ F)).subtype).codRestrict (range f) fun z ↦ by
      rw [← hfg.linearMap_ker_eq]
      exact z.2)
  have hq (z : ker (g ∘ₗ F)) : f (q z) = F z := by
    rw [← LinearEquiv.ofInjective_apply (h := hf)]
    simp [q, e]
  refine ⟨q, fun x ↦ ?_, fun z ↦ ⟨fun hz ↦ ?_, ?_⟩⟩
  · obtain ⟨y, hy⟩ := hF (f x)
    exact ⟨⟨y, by simp [hy, hfg.apply_apply_eq_zero]⟩, hf (by rw [hq, hy])⟩
  · exact ⟨⟨z, by rw [mem_ker, ← hq, hz, map_zero]⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact hf (by rw [hq, map_zero]; exact mem_ker.mp x.2)

/-- **Cokernels.** In a short exact sequence `0 → M₁ → M → M₂ → 0`, if `M₁` has a finite free
resolution of length at most `n` and `M` one of length at most `n + 1`, then `M₂` has one of length
at most `n + 1`. -/
theorem cokernel {M₁ M₂ : Type u} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] {f : M₁ →ₗ[R] M} {g : M →ₗ[R] M₂} (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : HasFiniteFreeResolutionLE R n M₁) (h : HasFiniteFreeResolutionLE R (n + 1) M) :
    HasFiniteFreeResolutionLE R (n + 1) M₂ := by
  obtain ⟨k, F, hF, hK⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h
  -- `0 → ker F → ker (g ∘ F) → M₁ → 0` is exact, so `ker (g ∘ F)` is an extension.
  obtain ⟨q, hq, hqe⟩ := exists_exact_inclusion_ker_comp hf hfg hF
  exact hasFiniteFreeResolutionLE_succ_iff.mpr
    ⟨k, g ∘ₗ F, hg.comp hF, extension (Submodule.inclusion_injective _) hq hqe hK h₁⟩

/-- **Kernels.** In a short exact sequence `0 → M₁ → M → M₂ → 0`, if `M` has a finite free
resolution of length at most `n + 1` and `M₂` one of length at most `n + 2`, then `M₁` has one of
length at most `n + 1`. -/
theorem kernel {M₁ M₂ : Type u} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] {f : M₁ →ₗ[R] M} {g : M →ₗ[R] M₂} (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h : HasFiniteFreeResolutionLE R (n + 1) M) (h₂ : HasFiniteFreeResolutionLE R (n + 2) M₂) :
    HasFiniteFreeResolutionLE R (n + 1) M₁ := by
  obtain ⟨k, F, hF, hK⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h
  -- `M₁` is the cokernel of the inclusion `ker F → ker (g ∘ F)`, and `ker (g ∘ F)` has a
  -- resolution by Schanuel's lemma.
  obtain ⟨q, hq, hqe⟩ := exists_exact_inclusion_ker_comp hf hfg hF
  exact cokernel (Submodule.inclusion_injective _) hq hqe hK
    ((h₂.ker_of_surjective (f := g ∘ₗ F) (hg.comp hF)).mono (by omega))

/-- **A projective module with a finite free resolution is stably free** (Lang XXI.2.1). -/
theorem isStablyFree [Module.Projective R M] (h : HasFiniteFreeResolutionLE R n M) :
    Module.IsStablyFree R M := by
  induction n generalizing M with
  | zero =>
    obtain ⟨_, _⟩ := hasFiniteFreeResolutionLE_zero_iff.mp h
    infer_instance
  | succ n ih =>
    obtain ⟨k, f, hf, hK⟩ := hasFiniteFreeResolutionLE_succ_iff.mp h
    -- `f` splits, so `Rᵏ ≃ ker f × M`, where `ker f` is projective with a shorter resolution.
    obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
    let e := ((exact_subtype_ker_map f).splitSurjectiveEquiv (ker f).injective_subtype ⟨s, hs⟩).1
    have := f.projective_ker_of_surjective hf
    have := ih hK
    have := hK.finite
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R (ker f)
    -- Then `ker f × N` is a finite free complement of `M`.
    have : Module.Free R (M × (ker f × N)) := .of_equiv <|
      ((e.prodCongr (.refl R N)).trans ((LinearEquiv.prodComm R _ M).prodCongr (.refl R N))).trans
        (LinearEquiv.prodAssoc R M _ N)
    exact .of_free_prod R M (ker f × N)

end HasFiniteFreeResolutionLE

/-- A finite stably free module has a finite free resolution of length at most one: if
`M × N ≃ Rᵐ` with `N` finite free, then `0 → N → Rᵐ → M → 0` is one. -/
theorem hasFiniteFreeResolutionLE_one_of_isStablyFree [Module.Finite R M]
    [Module.IsStablyFree R M] : HasFiniteFreeResolutionLE R 1 M := by
  obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R M
  exact HasFiniteFreeResolutionLE.of_prod (F := N) (n := 0) hasFiniteFreeResolutionLE_zero

/-- A finite free resolution of bounded length is a finite free resolution. -/
theorem HasFiniteFreeResolutionLE.hasFiniteFreeResolution (h : HasFiniteFreeResolutionLE R n M) :
    HasFiniteFreeResolution R M :=
  hasFiniteFreeResolution_iff.mpr ⟨n, h⟩

namespace HasFiniteFreeResolution

/-- Finite free resolutions transport along linear equivalences. -/
theorem of_equiv (e : M ≃ₗ[R] N) (h : HasFiniteFreeResolution R M) :
    HasFiniteFreeResolution R N :=
  let ⟨_, h⟩ := hasFiniteFreeResolution_iff.mp h
  (h.of_equiv e).hasFiniteFreeResolution

/-- A module with a finite free resolution is finitely generated. -/
theorem finite (h : HasFiniteFreeResolution R M) : Module.Finite R M :=
  let ⟨_, h⟩ := hasFiniteFreeResolution_iff.mp h
  h.finite

/-- A module with a finite free resolution is finitely presented. -/
theorem finitePresentation (h : HasFiniteFreeResolution R M) : Module.FinitePresentation R M :=
  let ⟨_, h⟩ := hasFiniteFreeResolution_iff.mp h
  h.isFPD.isPseudoCoherentOver.finitePresentation le_top

/-- Resolutions of `M` and `N` give one of `M × N`. -/
theorem prod (h : HasFiniteFreeResolution R M) (h' : HasFiniteFreeResolution R N) :
    HasFiniteFreeResolution R (M × N) :=
  let ⟨a, h⟩ := hasFiniteFreeResolution_iff.mp h
  let ⟨b, h'⟩ := hasFiniteFreeResolution_iff.mp h'
  ((h.mono (le_max_left a b)).prod (h'.mono (le_max_right a b))).hasFiniteFreeResolution

/-- **Schanuel's lemma.** If `M` has a finite free resolution, so does the kernel of every
surjection onto `M` from a finite free module. -/
theorem ker_of_surjective {P : Type u} [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Free R P] {f : P →ₗ[R] M} (hf : Function.Surjective f)
    (h : HasFiniteFreeResolution R M) : HasFiniteFreeResolution R (ker f) :=
  let ⟨n, h⟩ := hasFiniteFreeResolution_iff.mp h
  ((h.mono n.le_succ).ker_of_surjective hf).hasFiniteFreeResolution

section TwoOutOfThree

variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {f : M₁ →ₗ[R] M} {g : M →ₗ[R] M₂}

/-- **Two out of three, extensions** (Lang XXI.2.7). In a short exact sequence
`0 → M₁ → M → M₂ → 0`, if `M₁` and `M₂` have finite free resolutions, so does `M`. -/
theorem extension (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (h₁ : HasFiniteFreeResolution R M₁)
    (h₂ : HasFiniteFreeResolution R M₂) : HasFiniteFreeResolution R M :=
  let ⟨a, h₁⟩ := hasFiniteFreeResolution_iff.mp h₁
  let ⟨b, h₂⟩ := hasFiniteFreeResolution_iff.mp h₂
  (HasFiniteFreeResolutionLE.extension hf hg hfg (h₁.mono (le_max_left a b))
    (h₂.mono (le_max_right a b))).hasFiniteFreeResolution

/-- **Two out of three, cokernels** (Lang XXI.2.7). In a short exact sequence
`0 → M₁ → M → M₂ → 0`, if `M₁` and `M` have finite free resolutions, so does `M₂`. -/
theorem cokernel (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (h₁ : HasFiniteFreeResolution R M₁)
    (h : HasFiniteFreeResolution R M) : HasFiniteFreeResolution R M₂ :=
  let ⟨a, h₁⟩ := hasFiniteFreeResolution_iff.mp h₁
  let ⟨b, h⟩ := hasFiniteFreeResolution_iff.mp h
  (HasFiniteFreeResolutionLE.cokernel hf hg hfg (h₁.mono (le_max_left a b))
    (h.mono (by omega))).hasFiniteFreeResolution

/-- **Two out of three, kernels** (Lang XXI.2.7). In a short exact sequence
`0 → M₁ → M → M₂ → 0`, if `M` and `M₂` have finite free resolutions, so does `M₁`. -/
theorem kernel (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (h : HasFiniteFreeResolution R M)
    (h₂ : HasFiniteFreeResolution R M₂) : HasFiniteFreeResolution R M₁ :=
  let ⟨a, h⟩ := hasFiniteFreeResolution_iff.mp h
  let ⟨b, h₂⟩ := hasFiniteFreeResolution_iff.mp h₂
  (HasFiniteFreeResolutionLE.kernel (n := max a b) hf hg hfg (h.mono (by omega))
    (h₂.mono (by omega))).hasFiniteFreeResolution

end TwoOutOfThree

/-- **A projective module with a finite free resolution is stably free** (Lang XXI.2.1). -/
theorem isStablyFree [Module.Projective R M] (h : HasFiniteFreeResolution R M) :
    Module.IsStablyFree R M :=
  let ⟨_, h⟩ := hasFiniteFreeResolution_iff.mp h
  h.isStablyFree

end HasFiniteFreeResolution

/-- **A finite projective module has a finite free resolution if and only if it is stably free**
(Lang XXI.2.1). It then has one of length at most one, by
`TauCeti.Module.hasFiniteFreeResolutionLE_one_of_isStablyFree`. -/
theorem hasFiniteFreeResolution_iff_isStablyFree [Module.Finite R M] [Module.Projective R M] :
    HasFiniteFreeResolution R M ↔ Module.IsStablyFree R M :=
  ⟨HasFiniteFreeResolution.isStablyFree,
    fun _ ↦ hasFiniteFreeResolutionLE_one_of_isStablyFree.hasFiniteFreeResolution⟩

end TauCeti.Module
