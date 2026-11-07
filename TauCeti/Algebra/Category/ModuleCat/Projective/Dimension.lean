/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import TauCeti.Algebra.Category.ModuleCat.FiniteLength
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Projective dimension bounds for modules

A common bound on the projective dimensions of simple modules also bounds every
module of finite length. This lets short resolutions of simple modules control higher
Ext groups of arbitrary finite-length modules, without choosing resolutions of their
successive extensions.

For a finitely generated module over a left Noetherian ring, vanishing of one Ext degree
against every finitely generated target detects the corresponding projective-dimension bound.
The proof adapts `ModuleCat.hasProjectiveDimensionLT_of_forall_finite` from
`Mathlib/RingTheory/Regular/ProjectiveDimension.lean` (Nailin Guan), removing commutativity.

Over a principal ideal ring without zero divisors, every module has projective dimension at most
one: a submodule of a projective module is free, and hence projective. This supplies the
hereditary condition in terms of Mathlib's projective-dimension predicate. Over a principal ideal
domain the bound is attained by every torsion cyclic module `R ⧸ (a)` with `a` a nonzero nonunit,
which is not projective because projective modules over a domain are torsion-free.

For a module of projective dimension at most one, the standard free presentation has
projective kernel and hence is a projective resolution of length one. More generally, for a
surjection `f` from a projective module onto `M`, the projective dimension of `M` is at most
`n + 1` exactly when that of `ker f` is at most `n`, and when `M` is not projective its projective
dimension is exactly one more than that of `ker f`. Iterating this along a resolution of `M`
by projective modules, `M` has projective dimension at most `k + 1` exactly when the image of
`F_{k+1} → F_k` is projective, whichever resolution is chosen.

The projective dimensions of the cyclic modules `R ⧸ I` bound those of all modules: by Baer's
criterion they bound every injective dimension, and the vanishing of all `Ext^{n+1}(-, N)` then
bounds every projective dimension (Stacks, Lemma 10.109.12 (065T)). This is how a bound on finite
modules over a Noetherian ring becomes a bound on its global dimension.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A bound on the projective dimension of every simple module bounds every module
of finite length. Neither Artinianity of the ring nor finite generation of the ring
over a field is needed. -/
theorem _root_.ModuleCat.hasProjectiveDimensionLT_of_isFiniteLength
    (X : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ S : ModuleCat.{v} R, IsSimpleModule R S → HasProjectiveDimensionLT S n)
    (hX : IsFiniteLength R X) : HasProjectiveDimensionLT X n := by
  refine X.prop_of_isFiniteLength hX (fun M ↦ HasProjectiveDimensionLT M n) ?_ h
    (fun hS h₁ h₃ ↦ hS.hasProjectiveDimensionLT_X₂ n h₁ h₃)
  intro M hM
  let _ := hM.hasProjectiveDimensionLT_zero
  exact hasProjectiveDimensionLT_of_ge M 0 n (Nat.zero_le n)

/-- Over a left Noetherian ring, vanishing of `Extⁿ(M,L)` for every finite target `L`
detects projective dimension `< n` of a finite source `M`. No commutativity is required.

This generalizes Mathlib's `ModuleCat.hasProjectiveDimensionLT_of_forall_finite`. -/
theorem _root_.ModuleCat.hasProjectiveDimensionLT_of_subsingleton_ext_finite
    [Small.{v} R] [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ)
    (h : ∀ L : ModuleCat.{v} R, Module.Finite R L → Subsingleton (Abelian.Ext M L n)) :
    HasProjectiveDimensionLT M n := by
  induction n generalizing M with
  | zero =>
    have : Subsingleton (M ⟶ M) := Abelian.Ext.homEquiv₀.subsingleton_congr.mp (h M inferInstance)
    exact ((Limits.IsZero.iff_id_eq_zero M).2 (Subsingleton.eq_zero (𝟙 M)))
      |>.hasProjectiveDimensionLT_zero
  | succ n ih =>
    obtain ⟨d, f, hf⟩ := Module.Finite.exists_fin' R M
    -- Shrink the finite free cover into the universe of the module category.
    let e := Shrink.linearEquiv.{v} R (Fin d → R)
    let g := f.comp e.toLinearMap
    have : Module.Finite R (Shrink.{v} (Fin d → R)) := Module.Finite.equiv e.symm
    have : Module.Free R (Shrink.{v} (Fin d → R)) := Module.Free.of_equiv e.symm
    let S := g.shortComplexKer
    have hS : S.ShortExact := g.shortExact_shortComplexKer (hf.comp e.surjective)
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R g.ker)
    have : Projective S.X₂ := ModuleCat.projective_of_categoryTheory_projective _
    cases n with
    | zero =>
      have : Subsingleton (Abelian.Ext M S.X₁ 1) := h S.X₁ inferInstance
      obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₃ M hS
        (Abelian.Ext.mk₀ (𝟙 M)) (zero_add 1) (Subsingleton.eq_zero _)
      obtain ⟨s, rfl⟩ := (Abelian.Ext.mk₀_bijective M S.X₂).2 x
      rw [Abelian.Ext.mk₀_comp_mk₀, (Abelian.Ext.mk₀_bijective _ _).1.eq_iff] at hx
      exact projective_iff_hasProjectiveDimensionLT_one.1 (Retract.mk s S.g hx).projective
    | succ n =>
      apply (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).2
      apply ih S.X₁
      intro L hL
      have : Subsingleton (Abelian.Ext M L (n + 2)) := h L hL
      refine subsingleton_of_forall_eq 0 fun x ↦ ?_
      obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS L x
        (n₁ := n + 2) (by omega) (Subsingleton.eq_zero _)
      simpa [y.eq_zero_of_projective] using hy.symm

/-- **Global dimension is attained on cyclic modules.** If every cyclic module `R ⧸ I` has
projective dimension at most `n`, then every `R`-module has projective dimension at most `n`.
Stacks, Lemma 10.109.12 (065T). -/
theorem _root_.ModuleCat.hasProjectiveDimensionLE_of_quotients [Small.{v} R] (n : ℕ)
    (h : ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ I))) n)
    (M : ModuleCat.{v} R) : HasProjectiveDimensionLE M n := by
  -- By Baer's criterion every module has injective dimension at most `n` ...
  have hinj (N : ModuleCat.{v} R) : HasInjectiveDimensionLE N n :=
    ModuleCat.hasInjectiveDimensionLE_of_quotients N n fun I ↦
      HasProjectiveDimensionLT.subsingleton _ (n + 1) (n + 1) le_rfl N
  -- ... so every `Ext^{n+1}(M, N)` vanishes.
  exact hasProjectiveDimensionLT_of_enoughInjectives M (n + 1) fun N ↦
    HasInjectiveDimensionLT.subsingleton _ (n + 1) (n + 1) le_rfl M

/-- The standard free presentation of a module of projective dimension at most one
has projective kernel, so it is a projective resolution of length one. -/
theorem projective_projectiveShortComplex_X₁ [Small.{v} R] {M : ModuleCat.{v} R}
    (hM : HasProjectiveDimensionLT M 2) : Projective M.projectiveShortComplex.X₁ := by
  have h₂ : Projective M.projectiveShortComplex.X₂ := inferInstance
  have h₁ := (M.shortExact_projectiveShortComplex.hasProjectiveDimensionLT_X₃_iff 0 h₂).mp hM
  exact projective_iff_hasProjectiveDimensionLT_one.mpr h₁

/-- **Dimension shifting along a projective presentation.** For a surjection `f : P → M` from a
projective module, `M` has projective dimension at most `n + 1` exactly when `ker f` has
projective dimension at most `n`. -/
theorem _root_.LinearMap.hasProjectiveDimensionLE_succ_iff_ker [Small.{v} R] {P M : Type v}
    [AddCommGroup P] [Module R P] [Module.Projective R P] [AddCommGroup M] [Module R M]
    {f : P →ₗ[R] M} (hf : Function.Surjective f) (n : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1) ↔
      HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n :=
  (LinearMap.shortExact_shortComplexKer hf).hasProjectiveDimensionLT_X₃_iff n
    ((IsProjective.iff_projective P).mp ‹_›)

/-- For a surjection `f` from a projective module onto a module `M` that is not projective, the
projective dimension of `M` is one more than that of `ker f`. -/
theorem _root_.LinearMap.projectiveDimension_ker_add_one [Small.{v} R] {P M : Type v}
    [AddCommGroup P] [Module R P] [Module.Projective R P] [AddCommGroup M] [Module R M]
    {f : P →ₗ[R] M} (hf : Function.Surjective f) (hM : ¬ Module.Projective R M) :
    projectiveDimension (ModuleCat.of R (LinearMap.ker f)) + 1 =
      projectiveDimension (ModuleCat.of R M) :=
  ((LinearMap.shortExact_shortComplexKer hf).projectiveDimension_X₃_eq_succ_of_not_projective
    ((IsProjective.iff_projective P).mp ‹_›) (mt (IsProjective.iff_projective M).mpr hM)).symm

/-- **Projective dimension along a projective resolution.** Along a resolution
`⋯ → F₁ → F₀ → M → 0` of `M` by projective modules, exact everywhere, the image of
`d k : F_{k+1} → F_k` is projective exactly when `M` has projective dimension at most `k + 1`. In
particular this projectivity does not depend on the resolution. -/
theorem projective_range_iff_hasProjectiveDimensionLE [Small.{v} R] (k : ℕ) {F : ℕ → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module.Projective R (F i)]
    {M : Type v} [AddCommGroup M] [Module R M] {d : ∀ i, F (i + 1) →ₗ[R] F i}
    {ε : F 0 →ₗ[R] M} (hε : Function.Surjective ε) (h₀ : Function.Exact (d 0) ε)
    (hd : ∀ i, Function.Exact (d (i + 1)) (d i)) :
    Module.Projective R (LinearMap.range (d k)) ↔
      HasProjectiveDimensionLE (ModuleCat.of R M) (k + 1) := by
  rw [ε.hasProjectiveDimensionLE_succ_iff_ker hε]
  induction k generalizing M F with
  | zero =>
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective,
      LinearMap.exact_iff.mp h₀]
  | succ k ih =>
    -- Shift the resolution: `d (i + 1)` resolves `ker ε` along the corestriction of `d 0`.
    let ε' : F 1 →ₗ[R] LinearMap.ker ε := (d 0).codRestrict (LinearMap.ker ε)
      h₀.apply_apply_eq_zero
    have hε' : Function.Surjective ε' := by
      rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := (h₀ x).mp hx
      exact ⟨y, rfl⟩
    rw [ih (F := fun i ↦ F (i + 1)) (d := fun i ↦ d (i + 1)) hε'
      (fun x ↦ Subtype.ext_iff.trans (hd 0 x)) (fun i ↦ hd (i + 1)),
      ε'.hasProjectiveDimensionLE_succ_iff_ker hε']

end TauCeti

namespace ModuleCat

open CategoryTheory

universe u v

/-- Every module over a principal ideal ring without zero divisors has projective dimension at
most one. -/
instance hasProjectiveDimensionLE_one_of_isPrincipalIdealRing {R : Type u} [CommRing R]
    [NoZeroDivisors R] [IsPrincipalIdealRing R] [Small.{v} R] (M : ModuleCat.{v} R) :
    HasProjectiveDimensionLE M 1 := by
  apply (forall_hasProjectiveDimensionLE_one_iff_projective_of_mono (ModuleCat.{v} R)).mpr ?_ M
  intro X Y f _ _
  have : Module.Free R X := Module.Free.of_injective_of_projective_of_isPrincipalIdealRing f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
  have : Module.Projective R X := Module.Projective.of_free
  exact ModuleCat.projective_of_categoryTheory_projective X

/-- Over a principal ideal domain, the quotient `R ⧸ (a)` by a nonzero nonunit `a` has projective
dimension exactly one. It is not projective, since projective modules over a domain are
torsion-free while `a` kills the nonzero class of `1`, and every module over a principal ideal
domain has projective dimension at most one. -/
theorem projectiveDimension_quotient_span_singleton_eq_one {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Small.{v} R] {a : R} (ha : a ≠ 0) (ha' : ¬ IsUnit a) :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.span {a}))) = 1 := by
  refine le_antisymm ((projectiveDimension_le_iff _ 1).mpr inferInstance) ?_
  rw [← Nat.cast_one, projectiveDimension_ge_iff, ← projective_iff_hasProjectiveDimensionLT_one,
    ← IsProjective.iff_projective]
  intro hP
  have := Module.Projective.of_equiv (Shrink.linearEquiv R (R ⧸ Ideal.span {a}))
  -- The class of `1` in `R ⧸ (a)` is a nonzero element killed by `a`.
  have h1 : Ideal.Quotient.mk (Ideal.span {a}) 1 ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, ← isUnit_iff_dvd_one]
  refine h1 ((smul_eq_zero_iff_right ha).mp ?_)
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self a

end ModuleCat
