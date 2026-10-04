/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Adjoin.PowerBasis
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.NumberTheory.LocalField.Unramified.Factorization
import TauCeti.RingTheory.RootsOfUnity.Adjoin
import TauCeti.RingTheory.RootsOfUnity.Henselian

/-!
# Rigidity of unramified extensions

Let `K` be a nonarchimedean local field, let `L/K` be a finite unramified extension and let `M/K`
be any finite extension. A `K`-embedding `ι : L → M` induces a `𝓀[K]`-embedding of residue fields
`ι.residueFieldHom : 𝓀[L] → 𝓀[M]`. This file proves that reduction is a bijection

`(L →ₐ[K] M) ≃ (𝓀[L] →ₐ[𝓀[K]] 𝓀[M])`.

So a `K`-embedding of an unramified extension is determined by its effect on residue fields, and
every embedding of residue fields lifts. In particular, when `M/K` is unramified as well, a chosen
`𝓀[K]`-isomorphism `𝓀[L] ≃ 𝓀[M]` lifts to a unique `K`-isomorphism `L ≃ M`. Without fixing the
residue isomorphism there is no uniqueness: `L` has `[L : K]` automorphisms over `K`, one above
each automorphism of `𝓀[L]` over `𝓀[K]`.

Write `q = #𝓀[K]` and `f = f(L/K)`. The extension `L` is generated over `K` by a primitive
`(q^f − 1)`-st root of unity `ζ`, and `q^f − 1` is prime to the residue characteristic. Reduction
is therefore injective on the `(q^f − 1)`-st roots of unity of `𝒪[M]`, and by Hensel's lemma every
such root of unity of `𝓀[M]` lifts. An embedding `ι` is determined by `ι ζ`, which is the unique
lift of the residue of `ι ζ`. Conversely, given a residue embedding `φ`, the lift `ξ` of `φ(ζ̄)` is
a root of the minimal polynomial `g` of `ζ` over `𝒪[K]`: its residue is a root of the reduction of
`g`, and not of the reduction of the cofactor `(X^{q^f−1} − 1) / g`, because `X^{q^f−1} − 1` is
separable over `𝓀[M]`. So `ζ ↦ ξ` defines a `K`-embedding lifting `φ`, since `ζ̄` generates `𝓀[L]`.

## Main definitions

* `TauCeti.IsUnramified.residueFieldHomEquiv`: for `L/K` unramified, reduction as an equivalence
  `(L →ₐ[K] M) ≃ (𝓀[L] →ₐ[𝓀[K]] 𝓀[M])`.

## Main results

* `TauCeti.IsUnramified.residueFieldHom_bijective`: reduction of `K`-embeddings of an unramified
  extension is bijective.
* `TauCeti.IsUnramified.existsUnique_algEquiv_residueFieldHom_eq`: for `L/K` and `M/K` unramified,
  every `𝓀[K]`-isomorphism of residue fields lifts to a unique `K`-isomorphism `L ≃ M`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

noncomputable section

open ValuativeRel IsLocalRing Polynomial

namespace TauCeti

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra K M]
  [ValuativeExtension K M] [Module.Finite K M] [IsUnramified K L]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeRel L] [Module.Finite K L]
  [Module.Finite K M] [IsUnramified K L] in
/-- Let `ζ` be an integral `N`-th root of unity over `𝒪[K]`, with `N` invertible in `𝒪[M]`. An
`N`-th root of unity `ξ` of `𝒪[M]` whose residue is a root of the minimal polynomial `g` of `ζ`
over `𝒪[K]` is a root of the minimal polynomial of `ζ` over `K`. Indeed `g` divides
`X ^ N - 1 = g h`, which is separable over `𝓀[M]`, so the residue of `ξ` is not a root of `h`. -/
private theorem aeval_minpoly_eq_zero_of_aeval_residue_eq_zero {N : ℕ} (hNM : IsUnit (N : 𝒪[M]))
    {ζ : L} (hζO : IsIntegral 𝒪[K] ζ) (hζ : ζ ^ N = 1) {ξ : 𝒪[M]} (hξ : ξ ^ N = 1)
    (hres : aeval (residue 𝒪[M] ξ) (minpoly 𝒪[K] ζ) = 0) :
    aeval (ξ : M) (minpoly K ζ) = 0 := by
  have : NeZero N := ⟨by rintro rfl; simp at hNM⟩
  obtain ⟨h, hgh⟩ : minpoly 𝒪[K] ζ ∣ X ^ N - 1 :=
    minpoly.isIntegrallyClosed_dvd hζO (by simp [hζ])
  have hhξ : aeval ξ h ≠ 0 := by
    intro H
    have hhξ₀ : aeval (residue 𝒪[M] ξ) h = 0 := by
      rw [← ResidueField.algebraMap_eq, aeval_algebraMap_apply, H, map_zero]
    -- Otherwise the residue of `ξ` would be a double root of `X ^ N - 1`.
    have hd := congrArg (fun p ↦ aeval (residue 𝒪[M] ξ) (derivative p)) hgh
    simp only [derivative_mul, map_add, map_mul, hres, hhξ₀, mul_zero, zero_mul, add_zero,
      derivative_sub, derivative_X_pow, derivative_one, sub_zero, aeval_X_pow,
      map_natCast] at hd
    have hN : (N : 𝓀[M]) ≠ 0 := by
      simpa only [map_natCast] using (residue_ne_zero_iff_isUnit _).2 hNM
    have hξ0 : residue 𝒪[M] ξ ≠ 0 := fun h0 ↦ by
      simpa [h0, zero_pow (NeZero.ne N)] using congrArg (residue 𝒪[M]) hξ
    exact mul_ne_zero hN (pow_ne_zero _ hξ0) hd
  have hgξ : aeval ξ (minpoly 𝒪[K] ζ) = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_right hhξ
    rw [← map_mul, ← hgh, map_sub, map_pow, aeval_X, map_one, hξ, sub_self]
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hζO, aeval_map_algebraMap,
    ← Algebra.algebraMap_ofSubsemiring_apply, aeval_algebraMap_apply, hgξ, map_zero]

/-- **Embeddings of an unramified extension are determined by their residue maps, and every
residue map lifts.** For `L/K` unramified, reduction is a bijection from the `K`-embeddings
`L → M` to the `𝓀[K]`-embeddings `𝓀[L] → 𝓀[M]`. -/
theorem IsUnramified.residueFieldHom_bijective :
    Function.Bijective (AlgHom.residueFieldHom : (L →ₐ[K] M) → 𝓀[L] →ₐ[𝓀[K]] 𝓀[M]) := by
  -- `L = K(ζ)` for a primitive `N`-th root of unity `ζ`, where `N = q ^ f - 1` is invertible in
  -- the integer rings.
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K L
  set N := Nat.card 𝓀[K] ^ inertiaDegree K L - 1
  have hadj : Algebra.adjoin K {ζ} = ⊤ := Algebra.adjoin_eq_top_of_primitive_element
    (Algebra.IsAlgebraic.isAlgebraic ζ) (by
      rw [← unramifiedExtension_eq_adjoin_simple inertiaDegree_pos.ne' hζ,
        IsUnramified.unramifiedExtension_inertiaDegree_eq_top])
  have hNK : IsUnit (N : 𝒪[K]) := isUnit_natCast_natCard_pow_sub_one K inertiaDegree_pos.ne'
  have hNL : IsUnit (N : 𝒪[L]) := by simpa using hNK.map (algebraMap 𝒪[K] 𝒪[L])
  have hNM : IsUnit (N : 𝒪[M]) := by simpa using hNK.map (algebraMap 𝒪[K] 𝒪[M])
  have : NeZero N := ⟨by rintro h; simp [h] at hNK⟩
  have hζ1 : valuation L ζ ≤ 1 := (pow_le_one_iff_of_nonneg zero_le (NeZero.ne N)).1
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  set z : 𝒪[L] := ⟨ζ, hζ1⟩
  have hz : IsPrimitiveRoot z N := hζ.of_map_of_injective (f := algebraMap 𝒪[L] L)
    Subtype.val_injective
  let pb := PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral ζ) hadj
  have hιz (ι : L →ₐ[K] M) : ι.integerRingHom z ^ N = 1 := by
    rw [← map_pow, hz.pow_eq_one, map_one]
  refine ⟨fun ι₁ ι₂ h ↦ pb.algHom_ext ?_, fun φ ↦ ?_⟩
  · -- Both embeddings send `ζ` to `N`-th roots of unity with the same residue.
    have h' := eq_of_residue_eq_of_pow_eq_one hNM (hιz ι₁) (hιz ι₂)
      (by rw [← AlgHom.residueFieldHom_residue, ← AlgHom.residueFieldHom_residue, h])
    simpa [pb, z] using congrArg Subtype.val h'
  -- Lift `φ ζ̄` to an `N`-th root of unity `ξ` of `𝒪[M]`.
  have hφ : φ (residue 𝒪[L] z) ^ N = 1 := by rw [← map_pow, ← map_pow, hz.pow_eq_one, map_one,
    map_one]
  obtain ⟨u, hu⟩ := rootsOfUnityResidue_surjective hNM (rootsOfUnity.mkOfPowEq _ hφ)
  have hres : residue 𝒪[M] ((u : 𝒪[M]ˣ) : 𝒪[M]) = φ (residue 𝒪[L] z) := by
    simpa using congrArg (fun v : rootsOfUnity N 𝓀[M] ↦ ((v : 𝓀[M]ˣ) : 𝓀[M])) hu
  -- `φ ζ̄` is a root of the reduction of the minimal polynomial `g` of `ζ` over `𝒪[K]`.
  have hζO : IsIntegral 𝒪[K] ζ := (Valuation.Integers.isIntegral_iff_valuation_le_one
    (Valuation.integer.integers (valuation K)) ζ).2 hζ1
  have hgz : aeval z (minpoly 𝒪[K] ζ) = 0 := FaithfulSMul.algebraMap_injective 𝒪[L] L (by
    rw [← aeval_algebraMap_apply, Algebra.algebraMap_ofSubsemiring_apply, map_zero]
    exact minpoly.aeval 𝒪[K] ζ)
  have hgφ : aeval (residue 𝒪[M] ((u : 𝒪[M]ˣ) : 𝒪[M])) (minpoly 𝒪[K] ζ) = 0 := by
    have h1 := aeval_algHom_apply (φ.restrictScalars 𝒪[K]) (residue 𝒪[L] z) (minpoly 𝒪[K] ζ)
    rw [AlgHom.restrictScalars_apply, AlgHom.restrictScalars_apply] at h1
    rw [hres, h1, ← ResidueField.algebraMap_eq, aeval_algebraMap_apply, hgz, map_zero, map_zero]
  -- So `ζ ↦ ξ` defines a `K`-embedding, whose residue map agrees with `φ` on the generator `ζ̄`.
  have hroot : aeval ((u : 𝒪[M]ˣ) : M) (minpoly K pb.gen) = 0 :=
    aeval_minpoly_eq_zero_of_aeval_residue_eq_zero hNM hζO hζ.pow_eq_one
      ((mem_rootsOfUnity' N _).1 u.2) hgφ
  refine ⟨pb.lift _ hroot, AlgHom.ext_of_adjoin_eq_top (s := {residue 𝒪[L] z}) ?_ ?_⟩
  · refine IsPrimitiveRoot.adjoin_eq_top_of_natCard_sub_one ?_
    rw [natCard_residueField K L]
    exact hz.map_residue hNL
  rintro x rfl
  rw [AlgHom.residueFieldHom_residue, ← hres]
  congr 1
  exact Subtype.ext (by rw [AlgHom.coe_integerRingHom_apply]; exact pb.lift_gen _ hroot)

variable (K L M) in
/-- **Reduction of embeddings of an unramified extension.** For `L/K` unramified, passing to
residue fields is an equivalence between the `K`-embeddings `L → M` and the `𝓀[K]`-embeddings
`𝓀[L] → 𝓀[M]`. -/
def IsUnramified.residueFieldHomEquiv : (L →ₐ[K] M) ≃ (𝓀[L] →ₐ[𝓀[K]] 𝓀[M]) :=
  Equiv.ofBijective _ IsUnramified.residueFieldHom_bijective

/-- The equivalence `IsUnramified.residueFieldHomEquiv` sends an embedding to the induced
embedding of residue fields. -/
@[simp]
theorem IsUnramified.residueFieldHomEquiv_apply (ι : L →ₐ[K] M) :
    IsUnramified.residueFieldHomEquiv K L M ι = ι.residueFieldHom :=
  (rfl)

/-- **Rigidity of unramified extensions.** Let `L/K` and `M/K` be finite unramified extensions.
Every `𝓀[K]`-isomorphism `𝓀[L] ≃ 𝓀[M]` of residue fields lifts to a unique `K`-isomorphism
`L ≃ M`. -/
theorem IsUnramified.existsUnique_algEquiv_residueFieldHom_eq [IsUnramified K M]
    (φ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[M]) :
    ∃! e : L ≃ₐ[K] M, e.toAlgHom.residueFieldHom = φ.toAlgHom := by
  obtain ⟨ι, hι⟩ := IsUnramified.residueFieldHom_bijective.2 φ.toAlgHom
  -- `L` and `M` have the same degree over `K`, the degree of their residue fields.
  have hdeg : Module.finrank K L = Module.finrank K M := by
    rw [← IsUnramified.inertiaDegree_eq_finrank, ← IsUnramified.inertiaDegree_eq_finrank,
      inertiaDegree_def, inertiaDegree_def, φ.toLinearEquiv.finrank_eq]
  have hbij : Function.Bijective ι :=
    ⟨ι.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdeg
      (f := ι.toLinearMap)).1 ι.injective⟩
  refine ⟨AlgEquiv.ofBijective ι hbij, hι, fun e he ↦ ?_⟩
  refine AlgEquiv.coe_toAlgHom_injective (IsUnramified.residueFieldHom_bijective.1 ?_)
  rw [he, AlgEquiv.toAlgHom_ofBijective, hι]

end TauCeti
