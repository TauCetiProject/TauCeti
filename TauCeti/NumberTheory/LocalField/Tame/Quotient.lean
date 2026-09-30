/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Tame.Character
public import TauCeti.NumberTheory.LocalField.Unramified.ZHat
import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# The tame quotient of the absolute Galois group

Let `K` be a nonarchimedean local field with residue characteristic `p` and residue field of order
`q`, let `G_K = Gal(K^{alg}/K)`, and let `P_K ≤ I_K ≤ G_K` be the wild inertia and inertia
subgroups. This file studies the **tame quotient**

`G_K^t = G_K / P_K`,

a profinite group, and proves that it sits in a split exact sequence of profinite groups

`1 → ℤ̂^{(p')}(1) → G_K^t → ℤ̂ → 1`

whose conjugation action is the Iwasawa relation `σ τ σ⁻¹ = τ ^ q`:

* the first map `TauCeti.tameInertiaHom K` is the inverse of the tame character
  `I_K / P_K ≃ₜ* ℤ̂^{(p')}(1)` followed by the inclusion `I_K / P_K ↪ G_K / P_K`, so its image is
  the tame inertia group `I_K / P_K`;
* the second map `TauCeti.tameQuotientToZHat K` is restriction to the maximal unramified extension
  followed by `Gal(K^{ur}/K) ≃ₜ* ℤ̂`, whose kernel is therefore the image of `I_K`;
* the image of an arithmetic Frobenius lift `σ` generates the quotient `ℤ̂`, so `ℤ̂ → G_K^t`,
  `1 ↦ σ`, splits the sequence;
* conjugation by `g ∈ G_K` acts on `ℤ̂^{(p')}(1)` through the action of `g` on the roots of unity,
  by the equivariance of the tame character; a Frobenius lift raises every root of unity of order
  prime to `p` to the `q`-th power, so conjugation by `σ` is `x ↦ x ^ q`.

## Main definitions

* `TauCeti.tameQuotient K`: the tame quotient `G_K / P_K`, a profinite group.
* `TauCeti.toTameQuotient K`: the quotient map `G_K →ₜ* G_K^t`.
* `TauCeti.tameInertiaHom K`: the inclusion `ℤ̂^{(p')}(1) →ₜ* G_K^t` of tame inertia.
* `TauCeti.tameQuotientToZHat K`: the surjection `G_K^t →ₜ* ℤ̂`.

## Main results

* `TauCeti.tameInertiaHom_injective`, `TauCeti.ker_tameQuotientToZHat`,
  `TauCeti.tameQuotientToZHat_surjective`: the sequence `1 → ℤ̂^{(p')}(1) → G_K^t → ℤ̂ → 1` is
  exact.
* `TauCeti.range_tameInertiaHom`: the image of `ℤ̂^{(p')}(1)` is the image of inertia.
* `TauCeti.IsArithFrobeniusLift.tameQuotientToZHat_comp_lift`: the continuous homomorphism
  `ℤ̂ → G_K^t` sending `1` to the image of a Frobenius lift splits the sequence.
* `TauCeti.tameInertiaHom_smul`: conjugation in `G_K^t` acts on `ℤ̂^{(p')}(1)` through the
  Galois action on the roots of unity.
* `TauCeti.IsArithFrobeniusLift.smul_eq_pow`: a Frobenius lift acts on `ℤ̂^{(p')}(1)` as
  `x ↦ x ^ q`.
* `TauCeti.IsArithFrobeniusLift.toTameQuotient_mul_tameInertiaHom_mul_inv`,
  `TauCeti.IsArithFrobeniusLift.toTameQuotient_mul_toTameQuotient_mul_inv`: the Iwasawa relation
  `σ τ σ⁻¹ = τ ^ q` in `G_K^t`, for a Frobenius lift `σ` and `τ` in tame inertia.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.5.2) and (7.5.3).
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### The tame quotient -/

/-- **The tame quotient** `G_K^t = G_K / P_K` of the absolute Galois group of `K` by its wild
inertia subgroup. -/
abbrev tameQuotient := Field.absoluteGaloisGroup K ⧸ wildInertiaSubgroup K

/-- The tame quotient is Hausdorff, since wild inertia is closed. -/
instance : T2Space (tameQuotient K) :=
  haveI := isClosed_wildInertiaSubgroup K
  inferInstance

/-- The tame quotient is totally disconnected, since wild inertia is closed; with compactness, it
is a profinite group. -/
instance : TotallyDisconnectedSpace (tameQuotient K) :=
  haveI := isClosed_wildInertiaSubgroup K
  inferInstance

/-- The quotient map `G_K →ₜ* G_K^t` onto the tame quotient. -/
def toTameQuotient : Field.absoluteGaloisGroup K →ₜ* tameQuotient K :=
  ContinuousMonoidHom.quotientMk _

variable {K} in
/-- An element of `G_K` has trivial image in the tame quotient exactly when it is wild. -/
@[simp]
theorem toTameQuotient_eq_one_iff {σ : Field.absoluteGaloisGroup K} :
    toTameQuotient K σ = 1 ↔ σ ∈ wildInertiaSubgroup K :=
  QuotientGroup.eq_one_iff σ

/-- The quotient map onto the tame quotient is surjective. -/
theorem toTameQuotient_surjective : Function.Surjective (toTameQuotient K) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the quotient map onto the tame quotient is wild inertia. -/
theorem ker_toTameQuotient : (toTameQuotient K).toMonoidHom.ker = wildInertiaSubgroup K :=
  QuotientGroup.ker_mk' _

/-! ### Tame inertia inside the tame quotient -/

/-- **The inclusion of tame inertia** `ℤ̂^{(p')}(1) →ₜ* G_K^t`: the inverse of the isomorphism
`I_K / P_K ≃ₜ* ℤ̂^{(p')}(1)` given by the tame character, followed by the map
`I_K / P_K → G_K / P_K` induced by the inclusion of inertia. -/
def tameInertiaHom :
    PrimeToPTateModule (ringChar 𝓀[K]) (AlgebraicClosure K) →ₜ* tameQuotient K :=
  let f : inertiaSubgroup K ⧸ (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) →*
      tameQuotient K :=
    QuotientGroup.map _ _ (inertiaSubgroup K).subtype le_rfl
  have hf : Continuous f :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
      (QuotientGroup.continuous_mk.comp continuous_subtype_val)
  (ContinuousMonoidHom.mk f hf).comp ((quotientWildInertiaSubgroupEquiv K).symm : _ →ₜ* _)

variable {K} in
/-- The inclusion of tame inertia sends the tame character of `τ ∈ I_K` to the image of `τ` in
the tame quotient. -/
@[simp]
theorem tameInertiaHom_inertiaTameCharacter (τ : inertiaSubgroup K) :
    tameInertiaHom K (inertiaTameCharacter K τ) = toTameQuotient K τ := by
  rw [tameInertiaHom, ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_coe,
    quotientWildInertiaSubgroupEquiv_symm_inertiaTameCharacter, ContinuousMonoidHom.coe_mk]
  -- Both sides are the class of `τ` in `G_K / P_K`.
  rfl

/-- **The inclusion of tame inertia is injective**: an element of `I_K` whose image in `G_K / P_K`
is trivial lies in `P_K`, so its tame character is trivial. -/
theorem tameInertiaHom_injective : Function.Injective (tameInertiaHom K) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ?_
  obtain ⟨⟨τ, hτ⟩, rfl⟩ := inertiaTameCharacter_surjective K x
  rw [tameInertiaHom_inertiaTameCharacter, toTameQuotient_eq_one_iff] at hx
  exact (inertiaTameCharacter_eq_one_iff hτ).2 hx

/-- The image of the inclusion of tame inertia is the image `I_K / P_K` of the inertia subgroup in
the tame quotient. -/
theorem range_tameInertiaHom :
    (tameInertiaHom K).toMonoidHom.range =
      (inertiaSubgroup K).map (toTameQuotient K).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨τ, rfl⟩ := inertiaTameCharacter_surjective K y
    exact ⟨τ, τ.2, (tameInertiaHom_inertiaTameCharacter τ).symm⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨inertiaTameCharacter K ⟨τ, hτ⟩, tameInertiaHom_inertiaTameCharacter ⟨τ, hτ⟩⟩

/-! ### The unramified quotient `ℤ̂` -/

/-- **The surjection `G_K^t →ₜ* ℤ̂`**: restriction to the maximal unramified extension, followed by
the identification `Gal(K^{ur}/K) ≃ₜ* ℤ̂` carrying arithmetic Frobenius to `1`. It is well defined
on the tame quotient because wild inertia fixes `K^{ur}`. -/
def tameQuotientToZHat : tameQuotient K →ₜ* zHat.{u} :=
  let f : Field.absoluteGaloisGroup K →ₜ* zHat.{u} :=
    (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K) : _ →ₜ* _).comp
      ⟨restrictMaximalUnramifiedHom K, continuous_restrictMaximalUnramifiedHom K⟩
  ContinuousMonoidHom.quotientLift _ f fun σ hσ ↦ by
    have h := wildInertiaSubgroup_le_inertiaSubgroup K hσ
    rw [← ker_restrictMaximalUnramifiedHom, MonoidHom.mem_ker] at h
    simp [f, MonoidHom.mem_ker, h]

variable {K} in
/-- The image in `ℤ̂` of the class of `σ` is the image of the restriction of `σ` to `K^{ur}`. -/
@[simp]
theorem tameQuotientToZHat_toTameQuotient (σ : Field.absoluteGaloisGroup K) :
    tameQuotientToZHat K (toTameQuotient K σ) =
      maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
        (restrictMaximalUnramifiedHom K σ) :=
  ContinuousMonoidHom.quotientLift_mk _ _ _ σ

/-- **Exactness in the middle**: the kernel of `G_K^t → ℤ̂` is the image of `ℤ̂^{(p')}(1)`, since
both are the image of the inertia subgroup. -/
theorem ker_tameQuotientToZHat :
    (tameQuotientToZHat K).toMonoidHom.ker = (tameInertiaHom K).toMonoidHom.range := by
  have h : (tameQuotientToZHat K).toMonoidHom.ker.comap (toTameQuotient K).toMonoidHom =
      inertiaSubgroup K := by
    ext σ
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, ← ker_restrictMaximalUnramifiedHom,
      MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, ContinuousMonoidHom.coe_toMonoidHom,
      MonoidHom.coe_ofClass, MonoidHom.coe_ofClass, tameQuotientToZHat_toTameQuotient,
      map_eq_one_iff _ (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).injective]
  rw [range_tameInertiaHom, ← h,
    Subgroup.map_comap_eq_self_of_surjective (toTameQuotient_surjective K)]

variable {K} in
/-- The map `G_K^t → ℤ̂` kills tame inertia: the elementwise form of `ker_tameQuotientToZHat`. -/
@[simp]
theorem tameQuotientToZHat_tameInertiaHom
    (x : PrimeToPTateModule (ringChar 𝓀[K]) (AlgebraicClosure K)) :
    tameQuotientToZHat K (tameInertiaHom K x) = 1 :=
  (ker_tameQuotientToZHat K).ge ⟨x, rfl⟩

/-! ### The conjugation action -/

variable {K} in
/-- **Conjugation acts on tame inertia through the roots of unity**: conjugating the image of
`x ∈ ℤ̂^{(p')}(1)` by the image of `g ∈ G_K` gives the image of `g • x`. This is the equivariance of
the tame character, `TauCeti.inertiaTameCharacter_conj`. -/
theorem tameInertiaHom_smul (g : Gal(AlgebraicClosure K/K))
    (x : PrimeToPTateModule (ringChar 𝓀[K]) (AlgebraicClosure K)) :
    tameInertiaHom K (g • x) =
      toTameQuotient K g * tameInertiaHom K x * (toTameQuotient K g)⁻¹ := by
  obtain ⟨⟨τ, hτ⟩, rfl⟩ := inertiaTameCharacter_surjective K x
  rw [← inertiaTameCharacter_conj g hτ, tameInertiaHom_inertiaTameCharacter,
    tameInertiaHom_inertiaTameCharacter]
  -- `g * τ * g⁻¹` is formed in `Gal(K^{alg}/K)`, whose group structure is not reducibly that of
  -- `Field.absoluteGaloisGroup K`, so `map_mul` does not rewrite; both sides are the class of
  -- `g * τ * g⁻¹` in `G_K / P_K`.
  rfl

namespace IsArithFrobeniusLift

variable {K}

/-- **A Frobenius lift acts on `ℤ̂^{(p')}(1)` as `x ↦ x ^ q`**, since it raises every root of unity
of order prime to `p` to the `q`-th power (`TauCeti.IsArithFrobeniusLift.apply_of_pow_eq_one`). -/
theorem smul_eq_pow {σ : Gal(AlgebraicClosure K/K)} (hσ : IsArithFrobeniusLift K σ)
    (x : PrimeToPTateModule (ringChar 𝓀[K]) (AlgebraicClosure K)) :
    σ • x = x ^ Nat.card 𝓀[K] := by
  refine PrimeToPTateModule.ext fun m ↦ Subtype.ext (Units.ext ?_)
  have h : ((PrimeToPTateModule.proj m x : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^
      (m : ℕ) = 1 := by
    simpa using congrArg Units.val ((mem_rootsOfUnity _ _).1 (PrimeToPTateModule.proj m x).2)
  rw [PrimeToPTateModule.coe_proj_smul, AlgEquiv.smul_def, hσ.apply_of_pow_eq_one m.2.2 h]
  simp

variable {σ : Field.absoluteGaloisGroup K}

/-- **The Iwasawa relation on tame inertia**: conjugation by the image of an arithmetic Frobenius
lift `σ` raises the image of every `x ∈ ℤ̂^{(p')}(1)` in the tame quotient to the `q`-th power. -/
theorem toTameQuotient_mul_tameInertiaHom_mul_inv (hσ : IsArithFrobeniusLift K σ)
    (x : PrimeToPTateModule (ringChar 𝓀[K]) (AlgebraicClosure K)) :
    toTameQuotient K σ * tameInertiaHom K x * (toTameQuotient K σ)⁻¹ =
      tameInertiaHom K x ^ Nat.card 𝓀[K] := by
  rw [← map_pow, ← hσ.smul_eq_pow]
  exact (tameInertiaHom_smul σ x).symm

/-- **The Iwasawa relation** `σ τ σ⁻¹ = τ ^ q` in the tame quotient, for an arithmetic Frobenius
lift `σ` and an element `τ` of the inertia subgroup. -/
theorem toTameQuotient_mul_toTameQuotient_mul_inv (hσ : IsArithFrobeniusLift K σ)
    {τ : Field.absoluteGaloisGroup K} (hτ : τ ∈ inertiaSubgroup K) :
    toTameQuotient K σ * toTameQuotient K τ * (toTameQuotient K σ)⁻¹ =
      toTameQuotient K τ ^ Nat.card 𝓀[K] := by
  simpa using hσ.toTameQuotient_mul_tameInertiaHom_mul_inv (inertiaTameCharacter K ⟨τ, hτ⟩)

/-- The image of an arithmetic Frobenius lift in `ℤ̂` is the canonical generator. -/
theorem tameQuotientToZHat_eq_gen (hσ : IsArithFrobeniusLift K σ) :
    tameQuotientToZHat K (toTameQuotient K σ) = zHat.gen := by
  rw [tameQuotientToZHat_toTameQuotient, isArithFrobeniusLift_def.1 hσ,
    maximalUnramifiedGaloisGroupEquivZHat_apply_frobenius]

/-- **The splitting by a Frobenius lift**: the continuous homomorphism `ℤ̂ → G_K^t` sending `1` to
the image of an arithmetic Frobenius lift is a section of `G_K^t → ℤ̂`. -/
theorem tameQuotientToZHat_comp_lift (hσ : IsArithFrobeniusLift K σ) :
    (tameQuotientToZHat K).comp (zHat.lift (toTameQuotient K σ)) =
      ContinuousMonoidHom.id zHat.{u} :=
  zHat.hom_ext (by simp [hσ.tameQuotientToZHat_eq_gen])

end IsArithFrobeniusLift

/-- **The map `G_K^t → ℤ̂` is surjective**, being split by any Frobenius lift. -/
theorem tameQuotientToZHat_surjective : Function.Surjective (tameQuotientToZHat K) := by
  obtain ⟨σ, hσ⟩ := exists_isArithFrobeniusLift K
  exact fun x ↦ ⟨zHat.lift (toTameQuotient K σ) x,
    DFunLike.congr_fun hσ.tameQuotientToZHat_comp_lift x⟩

end TauCeti
