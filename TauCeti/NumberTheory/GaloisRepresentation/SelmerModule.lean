/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Inertia.Above
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle.SelmerModule

/-!
# Selmer modules of Galois cocycles unramified outside a set of places

Let `E` be a field (a number field in the case of interest) inside a field `Ω`, and
`G_E = Gal(Ω/E)`, the group `Ω ≃ₐ[E] Ω` with the Krull topology. For a set `T` of finite places of
`E`, `I_T ⊆ G_E` (`TauCeti.GaloisRep.inertiaAbove E Ω T`, in
`TauCeti/NumberTheory/NumberField/AbsoluteGaloisGroup/Inertia/Above.lean`) is the union of the
inertia groups at the places of `Ω` above the places of `T`.

For a map `ρ : G_E → Mₙ(O)`, an `O`-module `B`, a set `S` of finite places of `E` and a set `L` of
relations (finitely supported functions `G_E → Mₙ(O)`), the **Selmer module** of the locally
constant `ρ`-cocycles `c : G_E → Bⁿ` unramified outside `S` and obeying `L` is
`TauCeti.cocycleSelmerModule O (n → B) ρ (inertiaAbove E Ω Sᶜ) L`, with `Mₙ(O)` acting on `Bⁿ`
through the scoped instance `Matrix.Module.matrixModule`: its members are the locally
constant `c` with `c(gh) = c(g) + ρ(g) c(h)` that vanish on the inertia groups at the places of
`Ω` over the places outside `S` and satisfy `∑_g R(g) c(g) = 0` for every `R ∈ L`. The general
theory of these modules, including functoriality in `B` and the comparison of the coefficients
`O/a` and `K/O`, is in
`TauCeti/RepresentationTheory/Homological/GroupCohomology/Cocycle/SelmerModule.lean`; this file
records the consequences of the properties of `I_T` for the dependence on `S`.

## Main results

* `TauCeti.GaloisRep.apply_eq_zero_of_mem_cocycleSelmerModule_inertiaAbove_compl`: a member of
  the Selmer module unramified outside `S` vanishes on the inertia group of every place of `Ω`
  over a finite place outside `S`.
* `TauCeti.GaloisRep.cocycleSelmerModule_inertiaAbove_compl_mono`: enlarging `S` and dropping
  relations enlarges the Selmer module.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GaloisRep

variable {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {O Λ V : Type*} [CommSemiring O]
  [Semiring Λ] [Algebra O Λ] [AddCommMonoid V] [Module Λ V] [Module O V] [IsScalarTower O Λ V]
  {ρ : (Ω ≃ₐ[E] Ω) → Λ} {S : Set (HeightOneSpectrum (𝓞 E))} {L : Set ((Ω ≃ₐ[E] Ω) →₀ Λ)}

/-- **A cocycle unramified outside `S` vanishes on inertia outside `S`**: a member of the Selmer
module unramified outside `S` vanishes on the inertia group of every place of `Ω` above a finite
place `v ∉ S`. -/
theorem apply_eq_zero_of_mem_cocycleSelmerModule_inertiaAbove_compl {c : (Ω ≃ₐ[E] Ω) → V}
    (hc : c ∈ cocycleSelmerModule O V ρ (inertiaAbove E Ω Sᶜ) L) {v : HeightOneSpectrum (𝓞 E)}
    (hv : v ∉ S) {A : ValuationSubring Ω} (hA : A.IsCenteredAt v.asIdeal)
    {σ : A.decompositionSubgroup E} (hσ : σ ∈ A.inertiaSubgroup E) : c σ = 0 :=
  apply_eq_zero_of_mem_cocycleSelmerModule hc
    (map_inertiaSubgroup_subset_inertiaAbove (T := Sᶜ) hv hA ⟨σ, hσ, rfl⟩)

/-- **Monotonicity in `S` and `L`**: allowing ramification at more places and dropping relations
enlarges the Selmer module. -/
theorem cocycleSelmerModule_inertiaAbove_compl_mono {S' : Set (HeightOneSpectrum (𝓞 E))}
    (hS : S ⊆ S') {L' : Set ((Ω ≃ₐ[E] Ω) →₀ Λ)} (hL : L' ⊆ L) :
    cocycleSelmerModule O V ρ (inertiaAbove E Ω Sᶜ) L ≤
      cocycleSelmerModule O V ρ (inertiaAbove E Ω S'ᶜ) L' :=
  cocycleSelmerModule_anti (inertiaAbove_mono (Set.compl_subset_compl.mpr hS)) hL

end TauCeti.GaloisRep
