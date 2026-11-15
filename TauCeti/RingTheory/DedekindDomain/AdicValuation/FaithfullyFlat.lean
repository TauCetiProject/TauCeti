/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Localization
public import TauCeti.RingTheory.TensorProduct.CentralBaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.RingTheory.Flat.Tower

/-!
# Completions of a Dedekind domain jointly detect exactness

Let `R` be a Dedekind domain with fraction field `K`, and for a height-one prime `v` of `R` let
`𝒪_v = v.adicCompletionIntegers K` be the ring of integers of the completion `K_v`. The canonical
map `R_v → 𝒪_v` from the localization (`localizationToCompletionIntegers`) is a flat local
homomorphism of local rings, hence faithfully flat. This file records it as an algebra structure
and proves the faithful flatness.

When `R` is not a field, every maximal ideal of `R` is a height-one prime. Since localizations at
all maximal ideals detect exactness, so do the completions `R → 𝒪_v`: for arbitrary `R`-modules
(not necessarily finitely generated), a sequence `M → N → P` is exact if and only if
`𝒪_v ⊗[R] M → 𝒪_v ⊗[R] N → 𝒪_v ⊗[R] P` is exact for every `v`; likewise for injectivity,
surjectivity, the vanishing of a map and the vanishing of a module. This is how lattices over
orders are compared with their completions. As applications, a submodule `p` of an `R`-module `M`
is determined by its completions `p.baseChange 𝒪_v ⊆ 𝒪_v ⊗[R] M`, and projectivity of a finitely
presented module over an `R`-algebra can be checked after every completion.

If `R` is a field there are no height-one primes, so the family detects nothing; this is why the
hypothesis `¬ IsField R` appears.

## Main results

The algebra structure and its instances are in the namespace
`IsDedekindDomain.HeightOneSpectrum`; the detection results are in the namespace `TauCeti`.

* The instance
  `Module.FaithfullyFlat (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K)`:
  `𝒪_v` is faithfully flat over `R_v`.
* `exact_iff_forall_exact_lTensor_adicCompletionIntegers`: the completions jointly detect
  exactness.
* `injective_iff_forall_injective_lTensor_adicCompletionIntegers` and
  `surjective_iff_forall_surjective_lTensor_adicCompletionIntegers`: the same for injectivity
  and surjectivity.
* `subsingleton_iff_forall_subsingleton_adicCompletionIntegers_tensor`: a module vanishes if and
  only if all its completions vanish.
* `eq_zero_iff_forall_lTensor_adicCompletionIntegers_eq_zero`: a map vanishes if and only if all
  its completions vanish.
* `le_iff_forall_baseChange_adicCompletionIntegers_le` and
  `eq_iff_forall_baseChange_adicCompletionIntegers_eq`: containment and equality of submodules
  are detected by their completions.
* `eq_iff_forall_surjective_lTensor_inclusion_adicCompletionIntegers`: submodules `p ≤ q` are
  equal if and only if `𝒪_v ⊗[R] p → 𝒪_v ⊗[R] q` is surjective for every `v`.
* `projective_of_forall_projective_adicCompletionIntegers`:
  projectivity descends from the completions.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
  Lemma 9.4.6, Corollary 9.4.7 and Lemma 10.2.10.
-/

public section

open TensorProduct

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The ring of integers `𝒪_v` of the completion is an algebra over the localization `R_v`,
through `localizationToCompletionIntegers`. -/
noncomputable instance instAlgebraLocalizationAtPrimeAdicCompletionIntegers :
    Algebra (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) :=
  (v.localizationToCompletionIntegers (K := K)).toAlgebra

/-- The algebra map `R_v → 𝒪_v` is `localizationToCompletionIntegers`. -/
@[simp]
theorem algebraMap_localization_adicCompletionIntegers :
    algebraMap (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) =
      v.localizationToCompletionIntegers :=
  (rfl)

/-- The algebra structures `R → R_v → 𝒪_v` and `R → 𝒪_v` are compatible. -/
instance : IsScalarTower R (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) :=
  .of_algebraMap_eq fun x ↦ by
    rw [algebraMap_localization_adicCompletionIntegers, localizationToCompletionIntegers_algebraMap]

/-- The map `R_v → 𝒪_v` is a local homomorphism: it sends the maximal ideal into the maximal
ideal. -/
instance : IsLocalHom (algebraMap (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K)) :=
  ((IsLocalRing.local_hom_tfae _).out 3 1).mp (v.maximalIdeal_map_completion (K := K)).le

/-- `𝒪_v` is flat over `R_v`, since it is torsion-free, hence flat, over the Dedekind domain
`R`. -/
instance : Module.Flat (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) :=
  (Module.flat_iff_of_isLocalization _ v.asIdeal.primeCompl _).mpr inferInstance

/-- `𝒪_v` is faithfully flat over `R_v`, being a flat local algebra over a local ring. -/
instance : Module.FaithfullyFlat (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) :=
  .of_flat_of_isLocalHom

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

variable (K) in
/-- **The completions of a Dedekind domain jointly detect exactness.** If `R` is not a field, a
sequence `M → N → P` of `R`-modules is exact if and only if it is exact after tensoring with the
ring of integers `𝒪_v` of every completion of the fraction field. -/
theorem exact_iff_forall_exact_lTensor_adicCompletionIntegers (hR : ¬IsField R)
    {F : M →ₗ[R] N} {G : N →ₗ[R] P} :
    Function.Exact F G ↔ ∀ v : HeightOneSpectrum R,
      Function.Exact (F.lTensor (v.adicCompletionIntegers K))
        (G.lTensor (v.adicCompletionIntegers K)) := by
  refine ⟨fun h v ↦ Module.Flat.lTensor_exact _ h, fun h ↦ ?_⟩
  -- Exactness is detected by the localizations `R_J ⊗[R] -` at the maximal ideals `J`.
  refine exact_of_isLocalized_maximal
    (fun J _ ↦ Localization.AtPrime J ⊗[R] M) (fun J _ ↦ TensorProduct.mk R _ M 1)
    (fun J _ ↦ Localization.AtPrime J ⊗[R] N) (fun J _ ↦ TensorProduct.mk R _ N 1)
    (fun J _ ↦ Localization.AtPrime J ⊗[R] P) (fun J _ ↦ TensorProduct.mk R _ P 1) F G
    fun J hJ ↦ ?_
  obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum R, v.asIdeal = J :=
    ⟨⟨J, hJ.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hJ hR⟩, rfl⟩
  -- On `R_v ⊗[R] -`, the localized maps are the base changes of `F` and `G`.
  have hF : IsLocalizedModule.map v.asIdeal.primeCompl
      (TensorProduct.mk R (Localization.AtPrime v.asIdeal) M 1) (TensorProduct.mk R _ N 1) F =
        F.lTensor _ :=
    IsLocalizedModule.linearMap_ext v.asIdeal.primeCompl (TensorProduct.mk R _ M 1)
      (TensorProduct.mk R _ N 1) (LinearMap.ext fun x ↦ by
        rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]; simp)
  have hG : IsLocalizedModule.map v.asIdeal.primeCompl
      (TensorProduct.mk R (Localization.AtPrime v.asIdeal) N 1) (TensorProduct.mk R _ P 1) G =
        G.lTensor _ :=
    IsLocalizedModule.linearMap_ext v.asIdeal.primeCompl (TensorProduct.mk R _ N 1)
      (TensorProduct.mk R _ P 1) (LinearMap.ext fun x ↦ by
        rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]; simp)
  rw [hF, hG]
  -- `𝒪_v` is faithfully flat over `R_v`, so exactness over `𝒪_v` descends to `R_v`.
  exact (Module.FaithfullyFlat.lTensor_exact_iff_lTensor_exact (M := v.adicCompletionIntegers K)
    F G).mp (h v)

variable (K) in
/-- If `R` is not a field, a map of `R`-modules is injective if and only if it is injective after
tensoring with the ring of integers `𝒪_v` of every completion. -/
theorem injective_iff_forall_injective_lTensor_adicCompletionIntegers (hR : ¬IsField R)
    {F : M →ₗ[R] N} :
    Function.Injective F ↔ ∀ v : HeightOneSpectrum R,
      Function.Injective (F.lTensor (v.adicCompletionIntegers K)) := by
  simpa using exact_iff_forall_exact_lTensor_adicCompletionIntegers K hR (F := (0 : M →ₗ[R] M))
    (G := F)

variable (K) in
/-- If `R` is not a field, a map of `R`-modules is surjective if and only if it is surjective
after tensoring with the ring of integers `𝒪_v` of every completion. -/
theorem surjective_iff_forall_surjective_lTensor_adicCompletionIntegers (hR : ¬IsField R)
    {F : M →ₗ[R] N} :
    Function.Surjective F ↔ ∀ v : HeightOneSpectrum R,
      Function.Surjective (F.lTensor (v.adicCompletionIntegers K)) := by
  simpa using exact_iff_forall_exact_lTensor_adicCompletionIntegers K hR (F := F)
    (G := (0 : N →ₗ[R] N))

variable (K M) in
/-- If `R` is not a field, an `R`-module vanishes if and only if its tensor product with the ring
of integers `𝒪_v` of every completion vanishes. -/
theorem subsingleton_iff_forall_subsingleton_adicCompletionIntegers_tensor (hR : ¬IsField R) :
    Subsingleton M ↔
      ∀ v : HeightOneSpectrum R, Subsingleton (v.adicCompletionIntegers K ⊗[R] M) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  refine Module.subsingleton_of_localization_maximal (fun J _ ↦ Localization.AtPrime J ⊗[R] M)
    (fun J _ ↦ TensorProduct.mk R _ M 1) fun J hJ ↦ ?_
  obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum R, v.asIdeal = J :=
    ⟨⟨J, hJ.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hJ hR⟩, rfl⟩
  have := h v
  -- `𝒪_v ⊗[R_v] (R_v ⊗[R] M) ≃ 𝒪_v ⊗[R] M` vanishes, and `𝒪_v` is faithfully flat over `R_v`.
  have := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime v.asIdeal)
    (v.adicCompletionIntegers K) (v.adicCompletionIntegers K) M).toEquiv.subsingleton
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _
    (v.adicCompletionIntegers K)).mp this

variable (K) in
/-- If `R` is not a field, a map of `R`-modules vanishes if and only if it vanishes after
tensoring with the ring of integers `𝒪_v` of every completion. -/
theorem eq_zero_iff_forall_lTensor_adicCompletionIntegers_eq_zero (hR : ¬IsField R)
    {F : M →ₗ[R] N} :
    F = 0 ↔ ∀ v : HeightOneSpectrum R, F.lTensor (v.adicCompletionIntegers K) = 0 := by
  have h := exact_iff_forall_exact_lTensor_adicCompletionIntegers K hR (F := F) (G := .id)
  simpa only [LinearMap.exact_iff, LinearMap.lTensor_id, LinearMap.ker_id, eq_comm (a := ⊥),
    LinearMap.range_eq_bot] using h

variable (K) in
/-- **Containment of lattices is detected by completions.** If `R` is not a field, a submodule
`p` of an `R`-module `M` is contained in a submodule `q` if and only if
`𝒪_v ⊗[R] p ⊆ 𝒪_v ⊗[R] q` inside `𝒪_v ⊗[R] M` for the ring of integers `𝒪_v` of every completion.
No finiteness is needed. This is the analogue, for the family of completions, of Mathlib's
`Submodule.baseChange_le_iff` for a single faithfully flat algebra. -/
theorem le_iff_forall_baseChange_adicCompletionIntegers_le (hR : ¬IsField R)
    {p q : Submodule R M} :
    p ≤ q ↔ ∀ v : HeightOneSpectrum R,
      p.baseChange (v.adicCompletionIntegers K) ≤ q.baseChange (v.adicCompletionIntegers K) := by
  refine ⟨fun h v ↦ Submodule.baseChange_mono _ h, fun h ↦ ?_⟩
  -- `p ≤ q` says that `p → M → M ⧸ q` vanishes, and right exactness of `𝒪_v ⊗[R] -` identifies
  -- the kernel of `𝒪_v ⊗[R] M → 𝒪_v ⊗[R] (M ⧸ q)` with `q.baseChange 𝒪_v`. This follows the proof
  -- of Mathlib's `Submodule.baseChange_le_iff`.
  rw [← q.ker_mkQ, LinearMap.le_ker_iff_comp_subtype_eq_zero,
    eq_zero_iff_forall_lTensor_adicCompletionIntegers_eq_zero K hR]
  intro v
  rw [LinearMap.lTensor_comp, ← LinearMap.range_le_ker_iff, lTensor_mkQ,
    ← Submodule.restrictScalars_le R]
  exact h v

variable (K) in
/-- **Lattices are determined by their completions.** If `R` is not a field, two submodules `p`
and `q` of an `R`-module `M` are equal if and only if `𝒪_v ⊗[R] p = 𝒪_v ⊗[R] q` inside
`𝒪_v ⊗[R] M` for the ring of integers `𝒪_v` of every completion. No finiteness is needed. This is
the analogue, for the family of completions, of Mathlib's `Submodule.baseChange_inj`. -/
theorem eq_iff_forall_baseChange_adicCompletionIntegers_eq (hR : ¬IsField R)
    {p q : Submodule R M} :
    p = q ↔ ∀ v : HeightOneSpectrum R,
      p.baseChange (v.adicCompletionIntegers K) = q.baseChange (v.adicCompletionIntegers K) := by
  simp only [le_antisymm_iff, le_iff_forall_baseChange_adicCompletionIntegers_le K hR,
    forall_and]

variable (K) in
/-- **Equality of nested lattices is detected by completions.** If `R` is not a field and `p ≤ q`
are submodules of an `R`-module, then `p = q` if and only if the map
`𝒪_v ⊗[R] p → 𝒪_v ⊗[R] q` is surjective for the ring of integers `𝒪_v` of every completion.
No finiteness is needed. -/
theorem eq_iff_forall_surjective_lTensor_inclusion_adicCompletionIntegers (hR : ¬IsField R)
    {p q : Submodule R M} (h : p ≤ q) :
    p = q ↔ ∀ v : HeightOneSpectrum R,
      Function.Surjective ((Submodule.inclusion h).lTensor (v.adicCompletionIntegers K)) := by
  rw [← surjective_iff_forall_surjective_lTensor_adicCompletionIntegers K hR]
  refine ⟨fun hpq x ↦ ⟨⟨x, hpq ▸ x.2⟩, rfl⟩, fun hs ↦ le_antisymm h fun x hx ↦ ?_⟩
  obtain ⟨⟨y, hy⟩, hyx⟩ := hs ⟨x, hx⟩
  simp only [Subtype.ext_iff, Submodule.coe_inclusion] at hyx
  exact hyx ▸ hy

attribute [local instance low] TauCeti.CentralBaseChange.module in
variable (K) in
/-- **Projectivity descends from the completions.** Let `R` be a Dedekind domain that is not a
field and `Λ` an `R`-algebra. A finitely presented `Λ`-module `M` is projective if, for every
height-one prime `v`, the module `𝒪_v ⊗[R] M` is projective over `𝒪_v ⊗[R] Λ`, with the module
structure `TauCeti.CentralBaseChange.module`. -/
theorem projective_of_forall_projective_adicCompletionIntegers (hR : ¬IsField R)
    {Λ : Type*} [Ring Λ] [Algebra R Λ] [Module Λ M] [IsScalarTower R Λ M]
    [Module.FinitePresentation Λ M]
    [∀ v : HeightOneSpectrum R, Module.Projective (v.adicCompletionIntegers K ⊗[R] Λ)
      (v.adicCompletionIntegers K ⊗[R] M)] :
    Module.Projective Λ M :=
  CentralBaseChange.projective_of_forall_projective_of_forall_subsingleton
    (fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers K)
    fun C _ _ ↦ (subsingleton_iff_forall_subsingleton_adicCompletionIntegers_tensor K C hR).mpr

end TauCeti
