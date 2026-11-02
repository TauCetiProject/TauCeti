/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Defs

import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.TensorProduct.Quotient
import TauCeti.RingTheory.Flat.Extensions
import TauCeti.RingTheory.Spectrum.Prime.Semicontinuity

/-!
# Finite projective models of two-term complexes of flat modules

Let `R` be a Noetherian ring and `d : C₀ → C₁` a map of flat `R`-modules whose kernel and
cokernel are finite. The modules `C₀` and `C₁` themselves need not be finite: for a scheme `X`
over `R` covered by two affine opens `U` and `V` with affine intersection, and a quasi-coherent
sheaf `M` with flat sections, `d` is the difference map `Γ(M, U) × Γ(M, V) → Γ(M, U ∩ V)` of the
Mayer–Vietoris sequence, whose kernel and cokernel are `H⁰(X, M)` and `H¹(X, M)`, and whose
scalar extension along `R → B` computes the cohomology of the base change `X_B`.

This file shows that `d` can be replaced by a two-term complex `δ : K₀ → K₁` of finite projective
modules, compatibly with every scalar extension: there is a map of complexes from `δ` to `d`
inducing isomorphisms `ker (B ⊗ δ) ≅ ker (B ⊗ d)` and `coker (B ⊗ δ) ≅ coker (B ⊗ d)` for every
`R`-algebra `B`. Here `K₁ = Rⁿ` maps onto the cokernel of `d`, and `K₀` is the fibre product
`C₀ ×_{C₁} K₁`; the sequence `0 → K₀ → C₀ × K₁ → C₁ → 0` is exact with flat last term, so it
stays exact after any scalar extension, and its exactness says that the map of complexes is an
isomorphism on kernels and cokernels
(`Function.Exact.bijective_restrict_ker_of_prod_coprod`,
`Function.Exact.bijective_mapQ_range_of_prod_coprod`). The module `K₀` is flat, as the kernel of
a surjection of flat modules, and finite over the Noetherian ring `R`, hence projective.

Consequently the fibrewise Euler characteristic
`p ↦ dim ker (κ(p) ⊗ d) - dim coker (κ(p) ⊗ d)` equals `rank K₀ - rank K₁` near every prime, so
it is locally constant on `Spec R`, and the fibrewise kernel dimension `p ↦ dim ker (κ(p) ⊗ d)`
is upper semicontinuous. For the two-affine cover above these are the local constancy of
`χ(X_p, M_p)` and the semicontinuity of `dim H⁰(X_p, M_p)`.

## Main results

* `Function.Exact.baseChange_prod_coprod`: scalar extension preserves the short exact sequence
  `0 → K₀ → C₀ × K₁ → C₁ → 0` of a map of two-term complexes when `C₁` is flat.
* `LinearMap.exists_finite_projective_prod_coprod`: a two-term complex of flat modules with
  finite kernel and cokernel over a Noetherian ring receives a map from a two-term complex of
  finite projective modules whose cone is short exact.
* `LinearMap.isLocallyConstant_finrank_ker_baseChange_sub_finrank`: the fibrewise Euler
  characteristic of such a complex is locally constant on `Spec R`.
* `LinearMap.upperSemicontinuous_finrank_ker_baseChange`: the fibrewise kernel dimension of such
  a complex is upper semicontinuous on `Spec R`.

## References

* D. Mumford, *Abelian Varieties*, §5, the lemma on complexes of flat modules with finitely
  generated cohomology and its Corollary (a).
* [Stacks, Lemma 0B91](https://stacks.math.columbia.edu/tag/0B91)
* R. Hartshorne, *Algebraic Geometry*, Lemma III.12.3 and Theorem III.12.8.
-/

public section

open TensorProduct Module

namespace LinearMap

section BaseChange

variable {R : Type*} [CommRing R] (B : Type*) [Ring B] [Algebra R B]
  {K₀ K₁ C₀ C₁ : Type*} [AddCommGroup K₀] [Module R K₀] [AddCommGroup K₁] [Module R K₁]
  [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁]
  {α₀ : K₀ →ₗ[R] C₀} {δ : K₀ →ₗ[R] K₁} {d : C₀ →ₗ[R] C₁} {α₁ : K₁ →ₗ[R] C₁}

/-- **Scalar extension preserves a short exact cone with flat last term.** If
`0 → K₀ → C₀ × K₁ → C₁ → 0`, given by `(α₀, δ)` and by `d - α₁`, is short exact and `C₁` is flat,
then so is its scalar extension along any `R`-algebra `B`. Hence the map of two-term complexes
from `B ⊗ δ` to `B ⊗ d` is an isomorphism on kernels and on cokernels. -/
theorem _root_.Function.Exact.baseChange_prod_coprod [Module.Flat R C₁]
    (hinj : Function.Injective (α₀.prod δ)) (h : Function.Exact (α₀.prod δ) (d.coprod (-α₁)))
    (hsurj : Function.Surjective (d.coprod (-α₁))) :
    Function.Injective ((α₀.baseChange B).prod (δ.baseChange B)) ∧
      Function.Exact ((α₀.baseChange B).prod (δ.baseChange B))
        ((d.baseChange B).coprod (-α₁.baseChange B)) ∧
      Function.Surjective ((d.baseChange B).coprod (-α₁.baseChange B)) := by
  let e := TensorProduct.prodRight R B B C₀ K₁
  -- Under `B ⊗ (C₀ × K₁) ≃ (B ⊗ C₀) × (B ⊗ K₁)`, the cone of the scalar extension is the scalar
  -- extension of the cone.
  have h₁ : (α₀.baseChange B).prod (δ.baseChange B) =
      e.toLinearMap ∘ₗ (α₀.prod δ).baseChange B := by
    refine TensorProduct.AlgebraTensorModule.ext fun b x ↦ ?_
    simp [e]
  have h₂ : (d.baseChange B).coprod (-α₁.baseChange B) ∘ₗ e.toLinearMap =
      (d.coprod (-α₁)).baseChange B := by
    refine TensorProduct.AlgebraTensorModule.ext fun b x ↦ ?_
    simp [e, tmul_add, tmul_neg]
  have h₂' : (d.baseChange B).coprod (-α₁.baseChange B) =
      (d.coprod (-α₁)).baseChange B ∘ₗ e.symm.toLinearMap := by
    rw [← h₂, comp_assoc, LinearEquiv.comp_symm, comp_id]
  refine ⟨?_, ?_, ?_⟩
  · rw [h₁, coe_comp, baseChange_eq_lTensor]
    exact e.injective.comp (lTensor_injective_of_exact_of_flat _ hsurj _ hinj h B)
  · rw [h₁, h₂', LinearEquiv.conj_exact_iff_exact]
    exact lTensor_exact B h hsurj
  · rw [h₂', coe_comp, baseChange_eq_lTensor]
    exact (lTensor_surjective B hsurj).comp e.symm.surjective

end BaseChange

section Model

variable {R : Type*} [CommRing R] {C₀ C₁ : Type*} [AddCommGroup C₀] [Module R C₀]
  [AddCommGroup C₁] [Module R C₁] (d : C₀ →ₗ[R] C₁)

/-- **Finite projective models of two-term flat complexes.** Let `d : C₀ → C₁` be a map of flat
modules over a Noetherian ring `R` whose kernel and cokernel are finite. Then there are a finite
projective module `K₀`, a finite free module `K₁ = Rⁿ` and a map of two-term complexes
`(α₀, α₁)` from `δ : K₀ → K₁` to `d` such that `0 → K₀ → C₀ × K₁ → C₁ → 0`, given by `(α₀, δ)`
and by `d - α₁`, is short exact. By `Function.Exact.baseChange_prod_coprod`, the scalar extension
of this map of complexes along every `R`-algebra is an isomorphism on kernels and cokernels.
The module `K₀` is the fibre product `C₀ ×_{C₁} Rⁿ` along a map `Rⁿ → C₁` hitting the cokernel
of `d`. -/
theorem exists_finite_projective_prod_coprod [IsNoetherianRing R] [Module.Flat R C₀]
    [Module.Flat R C₁] [Module.Finite R (ker d)] [Module.Finite R (C₁ ⧸ range d)] :
    ∃ (n : ℕ) (K₀ : Submodule R (C₀ × (Fin n → R))) (α₀ : K₀ →ₗ[R] C₀) (δ : K₀ →ₗ[R] Fin n → R)
      (α₁ : (Fin n → R) →ₗ[R] C₁), Module.Finite R K₀ ∧ Module.Projective R K₀ ∧
      Function.Injective (α₀.prod δ) ∧ Function.Exact (α₀.prod δ) (d.coprod (-α₁)) ∧
      Function.Surjective (d.coprod (-α₁)) := by
  -- Lift a surjection `Rⁿ → coker d` to `φ : Rⁿ → C₁`, so that `d - φ : C₀ × Rⁿ → C₁` is onto.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (C₁ ⧸ range d)
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property (range d).mkQ f (range d).mkQ_surjective
  have hg : Function.Surjective (d.coprod (-φ)) := by
    intro c
    obtain ⟨v, hv⟩ := hf ((range d).mkQ c)
    obtain ⟨c₀, hc₀⟩ :=
      (Submodule.Quotient.eq _).1 (hv.symm.trans (LinearMap.congr_fun hφ v).symm)
    exact ⟨(c₀, -v), by simp [hc₀]⟩
  set K₀ := ker (d.coprod (-φ))
  have hprod : (fst R C₀ (Fin n → R) ∘ₗ K₀.subtype).prod (snd R C₀ (Fin n → R) ∘ₗ K₀.subtype) =
      K₀.subtype := by
    ext <;> rfl
  -- `K₀` is the kernel of a surjection of flat modules, hence flat.
  have : Module.Flat R K₀ := Function.Exact.flat_left_of_injective_of_surjective
    (exact_subtype_ker_map _) K₀.injective_subtype hg
  -- `K₀` is an extension of a submodule of `Rⁿ` by `ker d`, hence finite.
  have : Module.Finite R K₀ := by
    let p : K₀ →ₗ[R] Fin n → R := snd R C₀ (Fin n → R) ∘ₗ K₀.subtype
    let i : ker d →ₗ[R] K₀ := (inl R C₀ (Fin n → R)).restrict fun x hx ↦ by
      simpa [K₀] using mem_ker.1 hx
    refine Module.Finite.of_exact (f := i) (g := p.rangeRestrict) (fun y ↦ ?_)
      p.surjective_rangeRestrict
    obtain ⟨⟨c, v⟩, hy⟩ := y
    refine ⟨fun hv ↦ ?_, ?_⟩
    · obtain rfl : v = 0 := congrArg Subtype.val hv
      exact ⟨⟨c, mem_ker.2 (by simpa [K₀] using mem_ker.1 hy)⟩, rfl⟩
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact Subtype.ext rfl
  have := Module.finitePresentation_of_finite R K₀
  exact ⟨n, K₀, _, _, φ, inferInstance, Module.Flat.projective_of_finitePresentation,
    hprod ▸ K₀.injective_subtype, hprod ▸ exact_subtype_ker_map _, hg⟩

/-- **The fibrewise Euler characteristic of a two-term flat complex is locally constant.** Let
`d : C₀ → C₁` be a map of flat modules over a Noetherian ring `R` whose kernel and cokernel are
finite. Then `p ↦ dim ker (κ(p) ⊗ d) - dim coker (κ(p) ⊗ d)` is a locally constant function on
`Spec R`. -/
theorem isLocallyConstant_finrank_ker_baseChange_sub_finrank [IsNoetherianRing R]
    [Module.Flat R C₀] [Module.Flat R C₁] [Module.Finite R (ker d)]
    [Module.Finite R (C₁ ⧸ range d)] :
    IsLocallyConstant fun p : PrimeSpectrum R ↦
      (finrank p.asIdeal.ResidueField (ker (d.baseChange p.asIdeal.ResidueField)) : ℤ) -
        finrank p.asIdeal.ResidueField
          ((p.asIdeal.ResidueField ⊗[R] C₁) ⧸ range (d.baseChange p.asIdeal.ResidueField)) := by
  obtain ⟨n, K₀, α₀, δ, α₁, _, _, hinj, h, hsurj⟩ := d.exists_finite_projective_prod_coprod
  have := Module.finitePresentation_of_projective R K₀
  -- At each prime, the Euler characteristic of `κ(p) ⊗ d` is that of `κ(p) ⊗ δ`, which is
  -- `rank K₀ - rank Rⁿ` by rank–nullity.
  convert ((isLocallyConstant_rankAtStalk (R := R) (M := K₀)).comp ((↑) : ℕ → ℤ)).sub
    ((isLocallyConstant_rankAtStalk (R := R) (M := Fin n → R)).comp ((↑) : ℕ → ℤ)) using 1
  ext p
  let κ := p.asIdeal.ResidueField
  obtain ⟨hinj', h', hsurj'⟩ := h.baseChange_prod_coprod κ hinj hsurj
  have hker := (LinearEquiv.ofBijective _
    (Function.Exact.bijective_restrict_ker_of_prod_coprod hinj' h')).finrank_eq
  have hcoker := (LinearEquiv.ofBijective _
    (Function.Exact.bijective_mapQ_range_of_prod_coprod h' hsurj')).finrank_eq
  have h₀ := (δ.baseChange κ).finrank_range_add_finrank_ker
  have h₁ := Submodule.finrank_quotient_add_finrank (range (δ.baseChange κ))
  simp only [Pi.sub_apply, Function.comp_apply, rankAtStalk_eq]
  dsimp only [κ, Ideal.Fiber] at *
  omega

/-- **Semicontinuity of the fibrewise kernel of a two-term flat complex.** Let `d : C₀ → C₁` be a
map of flat modules over a Noetherian ring `R` whose kernel and cokernel are finite. Then
`p ↦ dim ker (κ(p) ⊗ d)` is an upper semicontinuous function on `Spec R`. -/
theorem upperSemicontinuous_finrank_ker_baseChange [IsNoetherianRing R] [Module.Flat R C₀]
    [Module.Flat R C₁] [Module.Finite R (ker d)] [Module.Finite R (C₁ ⧸ range d)] :
    UpperSemicontinuous fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField (ker (d.baseChange p.asIdeal.ResidueField)) := by
  -- The cokernel of `κ(p) ⊗ d` is the fibre of `coker d`, whose dimension is upper
  -- semicontinuous, and the difference of the two dimensions is locally constant.
  have hcoker (q : PrimeSpectrum R) :
      finrank q.asIdeal.ResidueField
          ((q.asIdeal.ResidueField ⊗[R] C₁) ⧸ range (d.baseChange q.asIdeal.ResidueField)) =
        finrank q.asIdeal.ResidueField (q.asIdeal.Fiber (C₁ ⧸ range d)) :=
    (d.cokernelBaseChangeEquiv (S := q.asIdeal.ResidueField)).finrank_eq.symm
  intro p y hy
  filter_upwards [(d.isLocallyConstant_finrank_ker_baseChange_sub_finrank).eventually_eq p,
    Module.upperSemicontinuous_finrank_fiber (C₁ ⧸ range d) p _ (Nat.lt_succ_self _)] with q hq hc
  have := hcoker p
  have := hcoker q
  dsimp only at hy hq hc
  omega

end Model

end LinearMap
