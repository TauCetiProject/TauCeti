/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.Grassmannian.Basic

/-!
# Points of the Grassmannian are Zariski-local

Let `M` be a module over a commutative ring `R`, and `A` a commutative `R`-algebra. This file
proves that the points of the Grassmannian functor `A ↦ G(k, A ⊗[R] M; A)` glue uniquely along
a standard Zariski cover of `Spec A`: for elements `s ⊆ A` generating the unit ideal, a point
`N ∈ G(k, A ⊗[R] M; A)` is determined by its base changes to the localizations `A[1/r]`,
`r ∈ s`, and a family of points over the `A[1/r]` whose base changes to the overlaps
`A[1/r] ⊗[A] A[1/r']` agree comes from a point over `A`. This is the sheaf property of
the Grassmannian functor for standard Zariski covers, the input needed to identify the points of
the glued Grassmannian scheme with the points of the functor.

The tool is a description of base change along a localization. If `B` is the localization of
`A` at a submonoid `S`, then the image of `x ∈ A ⊗[R] M` lies in the base change of `N` to `B`
exactly when `t • x ∈ N` for some `t ∈ S` (`Module.Grassmannian.rTensor_mem_map_iff`). The glued
point is the submodule of the `x` whose images in each `A[1/r] ⊗[R] M` lie in the given point. Its
quotient is finite projective of rank `k` because its base change to each `A[1/r]` is, by the
local–global principles for finite presentation and flatness.

## Main results

* `IsLocalizedModule.mk'_mem_iff`: a fraction `f x / s` lies in a submodule over the localization
  exactly when `f x` does.
* `TensorProduct.AlgebraTensorModule.rTensor_linearMap_apply`: the `A`-linear base change of the
  structure map `A → B` is the base change of the `R`-algebra map `A →ₐ[R] B`.
* `Module.Grassmannian.rTensor_mem_map_iff`: membership in the base change of a point along a
  localization.
* `Module.Grassmannian.eq_of_isLocalized_span`: a point of `G(k, A ⊗[R] M; A)` is determined by
  its base changes to the localizations `A[1/r]` for `r` in a set generating the unit ideal.
* `Module.Grassmannian.exists_map_eq_of_isLocalized_span`: points over the localizations `A[1/r]`
  at a set generating the unit ideal, compatible on the overlaps `A[1/r] ⊗[A] A[1/r']`,
  glue to a point over `A`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open TensorProduct

/-- Let `A` be the localization of `R` at `S`, and `f : M → M'` a localization map at `S` into an
`A`-module. Then `f x / s` lies in an `A`-submodule `L` of `M'` exactly when `f x` does. -/
theorem IsLocalizedModule.mk'_mem_iff {R : Type*} [CommSemiring R] {S : Submonoid R}
    {A : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] [Module A M']
    [IsScalarTower R A M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] {L : Submodule A M'}
    {x : M} {s : S} : IsLocalizedModule.mk' f x s ∈ L ↔ f x ∈ L := by
  rw [← IsLocalization.smul_mem_iff (s := s), IsLocalizedModule.mk'_cancel']

/-- The `A`-linear base change of the structure map `A → B` is, as a function, the base change
of the `R`-algebra map `A →ₐ[R] B`. -/
theorem TensorProduct.AlgebraTensorModule.rTensor_linearMap_apply {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [AddCommMonoid M] [Module R M] (x : A ⊗[R] M) :
    AlgebraTensorModule.rTensor R M (Algebra.linearMap A B) x =
      (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x := by
  rw [AlgebraTensorModule.coe_rTensor]
  exact congrArg (LinearMap.rTensor M · x) (LinearMap.ext fun a ↦ by simp)

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

section BaseChange

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B] (S : Submonoid A) [IsLocalization S B]

/-- Let `B` be the localization of `A` at `S`. The image of `x ∈ A ⊗[R] M` in `B ⊗[R] M` lies in
the kernel of `baseChangeMkQ B N` exactly when `t • x ∈ N` for some `t ∈ S`. -/
theorem rTensor_mem_ker_baseChangeMkQ_iff (N : Submodule A (A ⊗[R] M)) (x : A ⊗[R] M) :
    (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x ∈
        LinearMap.ker (baseChangeMkQ B N) ↔ ∃ t ∈ S, t • x ∈ N := by
  rw [LinearMap.mem_ker, baseChangeMkQ_rTensor,
    ← TensorProduct.mk_apply, IsLocalizedModule.eq_zero_iff S]
  simp [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]

/-- **Base change along a localization.** Let `B` be the localization of `A` at `S` and
`N ∈ G(k, A ⊗[R] M; A)`. The image of `x ∈ A ⊗[R] M` lies in the base change of `N` to `B`
exactly when `t • x ∈ N` for some `t ∈ S`. -/
theorem rTensor_mem_map_iff (N : G(k, A ⊗[R] M; A)) (x : A ⊗[R] M) :
    (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x ∈
        (map (IsScalarTower.toAlgHom R A B) N).toSubmodule ↔ ∃ t ∈ S, t • x ∈ N.toSubmodule := by
  rw [map_toAlgHom_toSubmodule, rTensor_mem_ker_baseChangeMkQ_iff S]

end BaseChange

section Local

variable {A : Type w} [CommRing A] [Algebra R A] (s : Set A) (hs : Ideal.span s = ⊤)
  {B : s → Type w} [∀ r, CommRing (B r)] [∀ r, Algebra R (B r)] [∀ r, Algebra A (B r)]
  [∀ r, IsScalarTower R A (B r)] [∀ r : s, IsLocalization.Away r.1 (B r)]

include hs

/-- **Points of the Grassmannian are determined locally.** Let `s ⊆ A` generate the unit ideal
and let `B r` be the localization `A[1/r]` for `r ∈ s`. Two points of `G(k, A ⊗[R] M; A)` with the
same base change to every `B r` are equal. -/
theorem eq_of_isLocalized_span {N N' : G(k, A ⊗[R] M; A)}
    (h : ∀ r : s, map (IsScalarTower.toAlgHom R A (B r)) N =
      map (IsScalarTower.toAlgHom R A (B r)) N') : N = N' := by
  -- the base changes of `N` determine `N`, so it is enough to prove `N ≤ N'` from `h` alone
  suffices H : ∀ {N N' : G(k, A ⊗[R] M; A)}, (∀ r : s, map (IsScalarTower.toAlgHom R A (B r)) N =
      map (IsScalarTower.toAlgHom R A (B r)) N') → N.toSubmodule ≤ N'.toSubmodule from
    Grassmannian.ext (le_antisymm (H h) (H fun r ↦ (h r).symm))
  intro N N' h x hx
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs x fun r ↦ ?_
  have hx' := rTensor_mem_map (IsScalarTower.toAlgHom R A (B r)) hx
  rw [h r, rTensor_mem_map_iff (.powers r.1)] at hx'
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hx'
  exact ⟨n, hn⟩

end Local

section Glue

/-! Throughout, the image of `x ∈ A ⊗[R] M` in `B r ⊗[R] M` is written as the base change
`(IsScalarTower.toAlgHom R A (B r)).toLinearMap.rTensor M x` of the structure map. As a function
this is the `A`-linear map `AlgebraTensorModule.rTensor R M (Algebra.linearMap A (B r))`
(`TensorProduct.AlgebraTensorModule.rTensor_linearMap_apply`), which is how its `A`-linearity is
used. -/

variable {A : Type w} [CommRing A] [Algebra R A] {s : Set A}
  {B : s → Type w} [∀ r, CommRing (B r)] [∀ r, Algebra R (B r)] [∀ r, Algebra A (B r)]
  [∀ r, IsScalarTower R A (B r)] (N : ∀ r : s, G(k, B r ⊗[R] M; B r))

/-- The vectors of `A ⊗[R] M` whose image in every `B r ⊗[R] M` lies in `N r`. -/
private def glueSubmodule : Submodule A (A ⊗[R] M) :=
  ⨅ r : s, ((N r).toSubmodule.restrictScalars A).comap
    (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (B r)))

private theorem mem_glueSubmodule_iff {x : A ⊗[R] M} :
    x ∈ glueSubmodule N ↔
      ∀ r : s, (IsScalarTower.toAlgHom R A (B r)).toLinearMap.rTensor M x ∈ (N r).toSubmodule := by
  simp only [glueSubmodule, Submodule.mem_iInf, Submodule.mem_comap,
    Submodule.restrictScalars_mem, AlgebraTensorModule.rTensor_linearMap_apply]

/-- The image of `a • x` in `B r ⊗[R] M` is `a •` the image of `x`. -/
private theorem rTensor_smul (r : s) (a : A) (x : A ⊗[R] M) :
    (IsScalarTower.toAlgHom R A (B r)).toLinearMap.rTensor M (a • x) =
      a • (IsScalarTower.toAlgHom R A (B r)).toLinearMap.rTensor M x :=
  (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (B r))).map_smul a x

variable [∀ r : s, IsLocalization.Away r.1 (B r)]

/-- Under the compatibility hypothesis, if the image of `x` in `B r ⊗[R] M` lies in `N r`, then
for every `r'` some power of `r` moves the image of `x` in `B r' ⊗[R] M` into `N r'`. -/
private theorem exists_pow_smul_rTensor_mem
    (hN : ∀ r r' : s, map (Algebra.TensorProduct.includeLeft : B r →ₐ[R] B r ⊗[A] B r') (N r) =
      map ((Algebra.TensorProduct.includeRight : B r' →ₐ[A] B r ⊗[A] B r').restrictScalars R)
        (N r'))
    {r : s} {x : A ⊗[R] M}
    (hx : (IsScalarTower.toAlgHom R A (B r)).toLinearMap.rTensor M x ∈ (N r).toSubmodule)
    (r' : s) : ∃ n : ℕ, (IsScalarTower.toAlgHom R A (B r')).toLinearMap.rTensor M
      (r.1 ^ n • x) ∈ (N r').toSubmodule := by
  have hx' := rTensor_mem_map
    ((Algebra.TensorProduct.includeRight : B r →ₐ[A] B r' ⊗[A] B r).restrictScalars R) hx
  -- on the overlap `B r' ⊗[A] B r`, the two images of `x` agree
  have hover : ((Algebra.TensorProduct.includeRight : B r →ₐ[A] B r' ⊗[A] B r).restrictScalars
        R).toLinearMap.rTensor M ((IsScalarTower.toAlgHom R A (B r)).toLinearMap.rTensor M x) =
      (Algebra.TensorProduct.includeLeft : B r' →ₐ[R] B r' ⊗[A] B r).toLinearMap.rTensor M
        ((IsScalarTower.toAlgHom R A (B r')).toLinearMap.rTensor M x) := by
    rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
    congr 2
    ext a
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  -- `includeLeft` is the structure map of the `B r'`-algebra `B r' ⊗[A] B r`, so the base change
  -- along it is described by `rTensor_mem_map_iff` for the localization of `B r'` at `r`
  have hincl : (Algebra.TensorProduct.includeLeft : B r' →ₐ[R] B r' ⊗[A] B r) =
      IsScalarTower.toAlgHom R (B r') (B r' ⊗[A] B r) :=
    AlgHom.ext fun _ ↦ by simp
  rw [hover, ← hN r' r, hincl,
    rTensor_mem_map_iff (Algebra.algebraMapSubmonoid (B r') (.powers r.1))] at hx'
  obtain ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, hn⟩ := hx'
  refine ⟨n, ?_⟩
  rwa [rTensor_smul, ← algebraMap_smul (B r')]

/-- Under the compatibility hypothesis, the image of `x` in `B r ⊗[R] M` lies in `N r` exactly
when some power of `r` moves `x` into `glueSubmodule N`. -/
private theorem rTensor_mem_iff_exists_pow_smul_mem (hs : Ideal.span s = ⊤)
    (hN : ∀ r r' : s, map (Algebra.TensorProduct.includeLeft : B r →ₐ[R] B r ⊗[A] B r') (N r) =
      map ((Algebra.TensorProduct.includeRight : B r' →ₐ[A] B r ⊗[A] B r').restrictScalars R)
        (N r'))
    (r : s) (x : A ⊗[R] M) :
    (IsScalarTower.toAlgHom R A (B r)).toLinearMap.rTensor M x ∈ (N r).toSubmodule ↔
      ∃ n : ℕ, r.1 ^ n • x ∈ glueSubmodule N := by
  refine ⟨fun hx ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · -- a single power of `r` works for every `r'` in a finite subcover `t ⊆ s`
    obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    choose n hn using fun r' : t ↦ exists_pow_smul_rTensor_mem N hN hx ⟨r'.1, hts r'.2⟩
    obtain ⟨n₀, hn₀⟩ := Finite.exists_le n
    refine ⟨n₀, (mem_glueSubmodule_iff N).mpr fun r'' ↦ ?_⟩
    -- and then for every `r'' ∈ s`, since the `r' ∈ t` generate the unit ideal
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem
      (((N r'').toSubmodule.restrictScalars A).comap
        (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (B r'')))) _ ht _ fun r' ↦ ?_
    refine exists_pow_smul_rTensor_mem N hN (r := ⟨r'.1, hts r'.2⟩) ?_ r''
    rw [← Nat.sub_add_cancel (hn₀ r'), pow_add, mul_smul, rTensor_smul]
    exact Submodule.smul_of_tower_mem _ _ (hn r')
  · have := (mem_glueSubmodule_iff N).mp hn r
    rw [rTensor_smul] at this
    exact (IsLocalization.smul_mem_iff (S := .powers r.1) (s := ⟨r.1 ^ n, n, rfl⟩)).mp this

/-- Under the compatibility hypothesis, the base change of `glueSubmodule N` to `B r` is `N r`. -/
private theorem ker_baseChangeMkQ_glueSubmodule (hs : Ideal.span s = ⊤)
    (hN : ∀ r r' : s, map (Algebra.TensorProduct.includeLeft : B r →ₐ[R] B r ⊗[A] B r') (N r) =
      map ((Algebra.TensorProduct.includeRight : B r' →ₐ[A] B r ⊗[A] B r').restrictScalars R)
        (N r'))
    (r : s) : LinearMap.ker (baseChangeMkQ (B r) (glueSubmodule N)) = (N r).toSubmodule := by
  let g := AlgebraTensorModule.rTensor R M (Algebra.linearMap A (B r))
  ext z
  -- write `z = g x / t`; membership of `z` in a `B r`-submodule is membership of `g x`
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (.powers r.1) g z
  rw [Function.uncurry_apply_pair, IsLocalizedModule.mk'_mem_iff, IsLocalizedModule.mk'_mem_iff,
    AlgebraTensorModule.rTensor_linearMap_apply,
    rTensor_mem_ker_baseChangeMkQ_iff (.powers r.1), rTensor_mem_iff_exists_pow_smul_mem N hs hN]
  simp [Submonoid.mem_powers_iff]

variable (s) in
/-- **Points of the Grassmannian glue along a Zariski cover.** Let `s ⊆ A` generate the unit
ideal, and let `B r` be the localization `A[1/r]` for `r ∈ s`. Given points
`N r ∈ G(k, B r ⊗[R] M; B r)` whose base changes to every overlap `B r ⊗[A] B r'` agree, there is
a point of `G(k, A ⊗[R] M; A)` whose base change to each `B r` is `N r`. By
`Module.Grassmannian.eq_of_isLocalized_span` it is unique. -/
theorem exists_map_eq_of_isLocalized_span (hs : Ideal.span s = ⊤)
    (hN : ∀ r r' : s, map (Algebra.TensorProduct.includeLeft : B r →ₐ[R] B r ⊗[A] B r') (N r) =
      map ((Algebra.TensorProduct.includeRight : B r' →ₐ[A] B r ⊗[A] B r').restrictScalars R)
        (N r')) :
    ∃ N₀ : G(k, A ⊗[R] M; A), ∀ r : s, map (IsScalarTower.toAlgHom R A (B r)) N₀ = N r := by
  let Q := (A ⊗[R] M) ⧸ glueSubmodule N
  -- the base change of the quotient `Q` to `B r` is the quotient of `B r ⊗[R] M` by `N r`
  let e (r : s) : ((B r ⊗[R] M) ⧸ (N r).toSubmodule) ≃ₗ[B r] B r ⊗[A] Q :=
    Submodule.quotEquivOfEq _ _ (ker_baseChangeMkQ_glueSubmodule N hs hN r).symm ≪≫ₗ
      baseChangeMkQEquiv (glueSubmodule N)
  have hfin (r : s) : Module.Finite (B r) (B r ⊗[A] Q) := Module.Finite.equiv (e r)
  have hproj (r : s) : Module.Projective (B r) (B r ⊗[A] Q) := Module.Projective.of_equiv (e r)
  -- so `Q` is finitely presented and flat, hence projective, by the local–global principles
  have : Module.FinitePresentation A Q :=
    Module.FinitePresentation.of_localizationSpan' s hs (Rₚ := B)
      (fun r ↦ TensorProduct.mk A (B r) Q 1) fun r ↦
        have := hfin r
        have := hproj r
        Module.finitePresentation_of_projective _ _
  have : Module.Flat A Q := by
    refine Module.flat_of_isLocalized_span A Q s hs (fun r ↦ B r ⊗[A] Q)
      (fun r ↦ TensorProduct.mk A (B r) Q 1) fun r ↦ ?_
    have := hproj r
    have : Module.Flat A (B r) := IsLocalization.flat (B r) (.powers r.1)
    exact Module.Flat.trans A (B r) (B r ⊗[A] Q)
  refine ⟨{ toSubmodule := glueSubmodule N
            finite_quotient := inferInstance
            projective_quotient := Module.Flat.projective_of_finitePresentation
            rankAtStalk_eq := fun p ↦ ?_ }, fun r ↦ ?_⟩
  · -- the rank of `Q` at `p` is read off a localization `B r` with `r ∉ p`
    obtain ⟨r, hr⟩ : ∃ r : s, r.1 ∉ p.asIdeal := by
      by_contra! h
      exact p.isPrime.ne_top (eq_top_iff.mpr (hs ▸ Ideal.span_le.mpr fun x hx ↦ h ⟨x, hx⟩))
    obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (B r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (B r) r.1]
      exact hr
    rw [← rankAtStalk_baseChange, ← rankAtStalk_eq_of_equiv (e r)]
    exact (N r).rankAtStalk_eq q
  · ext : 1
    rw [map_toAlgHom_toSubmodule]
    exact ker_baseChangeMkQ_glueSubmodule N hs hN r

end Glue

end Module.Grassmannian
