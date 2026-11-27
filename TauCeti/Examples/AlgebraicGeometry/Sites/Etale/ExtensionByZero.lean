/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.Constructible.ExtensionByZero

/-!
# Extension by zero from `𝔾_m` to `𝔸¹`

Let `k` be a field and `j : 𝔾_m ⟶ 𝔸¹` the inclusion, `Spec k[X, X⁻¹] ⟶ Spec k[X]`. For a ring
`Λ`, the extension by zero `j_! Λ` of the constant sheaf `Λ` is constructible
(`TauCeti.Examples.ExtensionByZeroAffineLine.constructibleSheaf_extensionByZero`), its stalks at
geometric points over the origin vanish (`isZero_etaleStalk_extensionByZero_of_origin`) and its
stalks at geometric points of `𝔾_m` are `Λ` (`etaleStalkExtensionByZeroIso`). For `Λ ≠ 0` it is
not locally constant, whatever the allowed values (`not_isLocallyConstantIn_extensionByZero`): the
origin lies in the closure of `𝔾_m`.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme Polynomial

namespace TauCeti.Examples.ExtensionByZeroAffineLine

open TauCeti.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (Λ : Type u) [Ring Λ]

/-- The inclusion `𝔾_m ⟶ 𝔸¹` over `k`, as `Spec k[X, X⁻¹] ⟶ Spec k[X]`. -/
noncomputable abbrev j : Spec (.of (Localization.Away (X : k[X]))) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X]))))

/-- The origin of `𝔸¹`, the prime ideal `(X)` of `k[X]`. -/
noncomputable def origin : Spec (.of k[X]) :=
  ⟨Ideal.span {X}, (Ideal.span_singleton_prime X_ne_zero).mpr prime_X⟩

/-- The extension by zero `j_! Λ` of the constant sheaf `Λ` on `𝔾_m`. -/
noncomputable abbrev extensionByZero : Sheaf (smallEtaleTopology (Spec (.of k[X])))
    (ModuleCat.{u} Λ) :=
  ((j k).smallEtaleExtensionByZero (ModuleCat.{u} Λ)).obj
    ((constantSheaf (smallEtaleTopology _) (ModuleCat.{u} Λ)).obj (.of Λ Λ))

/-- The image of `𝔾_m` in `𝔸¹` is the basic open `D(X)`. -/
lemma range_j : Set.range (j k) = (PrimeSpectrum.basicOpen (X : k[X]) : Set (PrimeSpectrum k[X])) :=
  PrimeSpectrum.localization_away_comap_range _ _

lemma origin_notMem_range_j : origin k ∉ Set.range (j k) := by
  rw [range_j]
  exact fun h ↦ h (Ideal.subset_span rfl)

/-- The origin lies in the closure of `𝔾_m`, which is dense in the irreducible `𝔸¹`. -/
lemma origin_mem_closure_range_j : origin k ∈ closure (Set.range (j k)) := by
  rw [range_j]
  refine ((PrimeSpectrum.basicOpen (X : k[X])).isOpen.dense ?_).closure_eq ▸ Set.mem_univ _
  exact ⟨⟨⊥, Ideal.isPrime_bot⟩, fun h ↦ X_ne_zero ((Submodule.mem_bot _).mp h)⟩

/-- `j_! Λ` is constructible, through the stratification `𝔾_m ⊔ {0}`. -/
theorem constructibleSheaf_extensionByZero :
    (Spec (.of k[X])).constructibleSheaf Λ (extensionByZero k Λ) :=
  constructibleSheaf_smallEtaleExtensionByZero (j k) (constructibleSheaf_constantSheaf _)

/-- The stalk of `j_! Λ` at a geometric point over the origin is zero. -/
theorem isZero_etaleStalk_extensionByZero_of_origin {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of k[X])) (hs : ∀ z, s z = origin k) :
    IsZero ((etaleStalk Λ s).obj (extensionByZero k Λ)) :=
  (j k).isZero_sheafFiber_smallEtaleExtensionByZero_obj_of_notMem_range _
    ((hs default).symm ▸ origin_notMem_range_j k) _

/-- The stalk of `j_! Λ` at a geometric point of `𝔾_m` is `Λ`. -/
noncomputable def etaleStalkExtensionByZeroIso {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of (Localization.Away (X : k[X])))) :
    (etaleStalk Λ (t ≫ j k)).obj (extensionByZero k Λ) ≅ .of Λ Λ :=
  ((j k).smallEtaleExtensionByZeroCompSheafFiberIso (ModuleCat.{u} Λ) t).app _ ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso _

/-- For `Λ ≠ 0`, `j_! Λ` is not locally constant, with values in any property `P` of modules. -/
theorem not_isLocallyConstantIn_extensionByZero [Nontrivial Λ] (P : ObjectProperty (ModuleCat Λ)) :
    ¬ (extensionByZero k Λ).IsLocallyConstantIn (smallEtaleTopology _) P :=
  haveI : Nontrivial (ModuleCat.of Λ Λ) := ‹Nontrivial Λ›
  not_isLocallyConstantIn_smallEtaleExtensionByZero_constantSheaf (j k)
    (origin_mem_closure_range_j k) (origin_notMem_range_j k) _ P

end TauCeti.Examples.ExtensionByZeroAffineLine
