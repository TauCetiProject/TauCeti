/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Envelope.Basic
import TauCeti.Algebra.Module.Injective.SelfInjective
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Existence of injective envelopes

Every module has an injective envelope (Eckmann–Schopf). More precisely, every embedding
`i : M →ₗ[R] Q` into an injective module restricts to an injective envelope of `M` inside `Q`
(`TauCeti.exists_isInjectiveEnvelope_submodule`), and since every module embeds into an injective
module, every module has an injective envelope in its own universe
(`TauCeti.exists_isInjectiveEnvelope`). By `TauCeti.IsInjectiveEnvelope.exists_linearEquiv` this
envelope is unique up to isomorphism. In particular this provides the injective hull `E(k)` of the
residue field of a local ring, the dualizing module of Matlis duality.

The envelope is a maximal essential extension `E` of the image of `M` inside `Q`, which exists by
Zorn's lemma: a union of a chain of essential extensions is an essential extension
(`TauCeti.isEssential_comap_subtype_sSup`). To see that `E` is injective, choose by Zorn's lemma a
submodule `K` of `Q` maximal among those disjoint from `E`. Then `E` embeds in `Q ⧸ K` with
essential image (`TauCeti.isEssential_range_mkQ_comp_subtype`), the inclusion of `E` into `Q`
extends along this embedding to a map `φ : Q ⧸ K →ₗ[R] Q`, and the essential image forces `φ` to
be injective. The range of `φ` is then
an essential extension of `M` containing `E`, hence equals `E`, so `Q → Q ⧸ K → E` retracts `Q`
onto `E` and `E` is injective as a retract of an injective module.

## Main results

* `TauCeti.exists_isInjectiveEnvelope_submodule`: an embedding into an injective module restricts
  to an injective envelope inside that module.
* `TauCeti.exists_isInjectiveEnvelope`: every module has an injective envelope.

## References

* B. Eckmann, A. Schopf, *Über injektive Moduln*, Arch. Math. 4 (1953), 75–78.
* T. Y. Lam, *Lectures on Modules and Rings*, §3D.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {Q : Type w} [AddCommGroup Q] [Module R Q]

variable (R) in
/-- **Injective envelopes inside an injective module.** Every embedding into an injective module
restricts to an injective envelope inside that module: some submodule `P` of `Q` containing the
image is injective, with the image essential in `P`. -/
theorem exists_isInjectiveEnvelope_submodule [Small.{w} R] [Module.Injective R Q]
    (i : M →ₗ[R] Q) (hi : Function.Injective i) :
    ∃ (P : Submodule R Q) (hP : LinearMap.range i ≤ P),
      IsInjectiveEnvelope (i.codRestrict P (fun x => hP ⟨x, rfl⟩)) := by
  set N := LinearMap.range i
  -- The essential extensions of `N` inside `Q`.
  let S : Set (Submodule R Q) := {P | N ≤ P ∧ IsEssential (N.comap P.subtype)}
  -- Zorn's lemma gives a maximal essential extension `E` of `N`.
  obtain ⟨E, -, hE⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy =>
      ⟨sSup c, ⟨(hcS hy).1.trans (le_sSup hy),
        isEssential_comap_subtype_sSup hc.directedOn fun P hP => (hcS hP).2⟩,
        fun z hz => le_sSup hz⟩)
    N ⟨le_rfl, by rw [Submodule.comap_subtype_self]; exact isEssential_top⟩
  -- Zorn's lemma again gives `K` maximal among the submodules disjoint from `E`.
  obtain ⟨K, -, hK⟩ := zorn_le_nonempty₀ {K : Submodule R Q | Disjoint E K}
    (fun c hcS hc y hy =>
      ⟨sSup c, hc.directedOn.disjoint_sSup_right.mpr fun _ hL => hcS hL, fun z hz => le_sSup hz⟩)
    ⊥ disjoint_bot_right
  -- `E` embeds into `Q ⧸ K`, with essential image by the maximality of `K`.
  let j : E →ₗ[R] Q ⧸ K := K.mkQ ∘ₗ E.subtype
  have hj : Function.Injective j := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ,
      ← Submodule.disjoint_iff_comap_eq_bot]
    exact hK.prop
  have hjess : IsEssential (LinearMap.range j) := isEssential_range_mkQ_comp_subtype hK
  -- Extend the inclusion of `E` along `j`; the extension is injective since `j` is essential.
  obtain ⟨φ, hφ⟩ := Module.Injective.extension_property R Q E (Q ⧸ K) j hj E.subtype
  have hφj (e : E) : φ (j e) = e := LinearMap.congr_fun hφ e
  have hφ_inj : Function.Injective φ :=
    hjess.injective_of_injective_comp (by rw [hφ]; exact E.injective_subtype)
  -- The range of `φ` is an essential extension of `N` containing `E`, so it is `E`: transport
  -- the essential trace of `N` on `E` along `j` and then along `φ`.
  have hEφ : E ≤ LinearMap.range φ := fun x hx => ⟨j ⟨x, hx⟩, hφj ⟨x, hx⟩⟩
  have hφS : LinearMap.range φ ∈ S := by
    refine ⟨hE.prop.1.trans hEφ, ((isEssential_map_equiv_iff
      (LinearEquiv.ofInjective φ hφ_inj)).mpr (hE.prop.2.map hj hjess)).mono ?_⟩
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    simpa [LinearEquiv.ofInjective_apply, hφj] using he
  have hφE : LinearMap.range φ = E := (hE.eq_of_le hφS hEφ).symm
  -- So `Q → Q ⧸ K → E` retracts `Q` onto `E`, and `E` is injective.
  let ρ : Q →ₗ[R] E := (φ ∘ₗ K.mkQ).codRestrict E fun q => hφE ▸ ⟨K.mkQ q, rfl⟩
  have hEinj : Module.Injective R E := Module.Baer.injective
    ((Module.Baer.of_injective ‹_›).of_leftInverse E.subtype ρ fun e => Subtype.ext (hφj e))
  refine ⟨E, hE.prop.1, hEinj, fun a b hab => hi (congrArg Subtype.val hab), ?_⟩
  rw [LinearMap.range_codRestrict]
  exact hE.prop.2

variable (R M) in
/-- **Existence of injective envelopes.** Every module has an injective envelope, in its own
universe. -/
theorem exists_isInjectiveEnvelope [Small.{v} R] :
    ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q) (i : M →ₗ[R] Q),
      IsInjectiveEnvelope i := by
  let I : ModuleCat.{v} R := CategoryTheory.Injective.under (ModuleCat.of R M)
  let ι : ModuleCat.of R M ⟶ I := CategoryTheory.Injective.ι (ModuleCat.of R M)
  have : Module.Injective R I := Module.injective_module_of_injective_object R I
    (inj := CategoryTheory.Injective.injective_under (ModuleCat.of R M))
  obtain ⟨P, _, hP⟩ := exists_isInjectiveEnvelope_submodule R ι.hom
    ((ModuleCat.mono_iff_injective ι).mp inferInstance)
  exact ⟨P, _, _, _, hP⟩

end TauCeti
