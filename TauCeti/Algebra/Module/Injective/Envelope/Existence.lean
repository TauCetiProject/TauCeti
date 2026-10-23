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
envelope is unique up to isomorphism. Injective envelopes are the injective hulls `E(k)` of residue
fields on which Matlis duality is built.

The envelope is a maximal essential extension `E` of the image of `M` inside `Q`, which exists by
Zorn's lemma: a union of a chain of essential extensions is an essential extension, by the
pointwise criterion `TauCeti.isEssential_iff_forall_exists_smul`. To see that `E` is injective,
choose by Zorn's lemma a submodule `K` of `Q` maximal for `E ⊓ K = ⊥`. Then `E` embeds in `Q ⧸ K`
with essential image, the inclusion of `E` into `Q` extends along this embedding to a map
`φ : Q ⧸ K →ₗ[R] Q`, and the essential image forces `φ` to be injective. The range of `φ` is then
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
  -- The essential extensions of `N` inside `Q`, in pointwise form.
  let S : Set (Submodule R Q) :=
    {P | N ≤ P ∧ ∀ x ∈ P, x ≠ 0 → ∃ r : R, r • x ∈ N ∧ r • x ≠ 0}
  -- Zorn's lemma gives a maximal essential extension `E` of `N`.
  obtain ⟨E, -, hE⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
      refine ⟨sSup c, ⟨(hcS hy).1.trans (le_sSup hy), fun x hx hx0 => ?_⟩,
        fun z hz => le_sSup hz⟩
      obtain ⟨P, hPc, hxP⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).mp hx
      exact (hcS hPc).2 x hxP hx0)
    N ⟨le_rfl, fun x hx hx0 => ⟨1, by rwa [one_smul], by rwa [one_smul]⟩⟩
  -- Zorn's lemma again gives `K` maximal among the submodules meeting `E` trivially.
  obtain ⟨K, -, hK⟩ := zorn_le_nonempty₀ {K : Submodule R Q | E ⊓ K = ⊥}
    (fun c hcS hc y hy => by
      refine ⟨sSup c, (Submodule.eq_bot_iff _).mpr fun x ⟨hxE, hx⟩ => ?_,
        fun z hz => le_sSup hz⟩
      obtain ⟨L, hLc, hxL⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).mp hx
      exact (Submodule.eq_bot_iff _).mp (hcS hLc) x ⟨hxE, hxL⟩)
    ⊥ (inf_bot_eq E)
  have hEK : ∀ x ∈ E, x ∈ K → x = 0 := fun x hxE hxK =>
    (Submodule.eq_bot_iff _).mp hK.prop x ⟨hxE, hxK⟩
  -- `E` embeds into `Q ⧸ K`, with essential image by the maximality of `K`.
  let j : E →ₗ[R] Q ⧸ K := K.mkQ ∘ₗ E.subtype
  have hj : Function.Injective j := fun a b hab => Subtype.ext (sub_eq_zero.mp
    (hEK _ (sub_mem a.2 b.2) ((Submodule.Quotient.eq K).mp hab)))
  have hjess : IsEssential (LinearMap.range j) := by
    refine isEssential_iff.mpr fun L hL => ?_
    have hLK : K = L.comap K.mkQ := by
      refine hK.eq_of_le ((Submodule.eq_bot_iff _).mpr fun x ⟨hxE, hxL⟩ => hEK x hxE ?_)
        fun x hx => by
          rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).mpr hx]
          exact L.zero_mem
      have hx : K.mkQ x ∈ LinearMap.range j ⊓ L := ⟨⟨⟨x, hxE⟩, rfl⟩, hxL⟩
      rwa [hL, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective L, ← hLK, Submodule.mkQ_map_self]
  -- Extend the inclusion of `E` along `j`; the extension is injective since `j` is essential.
  obtain ⟨φ, hφ⟩ := Module.Injective.extension_property R Q E (Q ⧸ K) j hj E.subtype
  have hφj (e : E) : φ (j e) = e := LinearMap.congr_fun hφ e
  have hφ_inj : Function.Injective φ :=
    hjess.injective_of_injective_comp (by rw [hφ]; exact E.injective_subtype)
  -- The range of `φ` is an essential extension of `N` containing `E`, so it is `E`.
  have hEφ : E ≤ LinearMap.range φ := fun x hx => ⟨j ⟨x, hx⟩, hφj ⟨x, hx⟩⟩
  have hφS : LinearMap.range φ ∈ S := by
    refine ⟨hE.prop.1.trans hEφ, ?_⟩
    rintro _ ⟨z, rfl⟩ hz0
    obtain ⟨r, ⟨e, he⟩, hr0⟩ := isEssential_iff_forall_exists_smul.mp hjess z
      (by rintro rfl; exact hz0 (map_zero φ))
    have hre : r • φ z = e := by rw [← map_smul, ← he, hφj]
    have he0 : (e : Q) ≠ 0 := by
      rw [← hre, ← map_smul]
      exact fun h0 => hr0 (hφ_inj (h0.trans (map_zero φ).symm))
    obtain ⟨s, hsN, hs0⟩ := hE.prop.2 e e.2 he0
    exact ⟨s * r, by rwa [mul_smul, hre], by rwa [mul_smul, hre]⟩
  have hφE : LinearMap.range φ = E := (hE.eq_of_le hφS hEφ).symm
  -- So `Q → Q ⧸ K → E` retracts `Q` onto `E`, and `E` is injective.
  let ρ : Q →ₗ[R] E := (φ ∘ₗ K.mkQ).codRestrict E fun q => hφE ▸ ⟨K.mkQ q, rfl⟩
  have hEinj : Module.Injective R E := Module.Baer.injective
    ((Module.Baer.of_injective ‹_›).of_leftInverse E.subtype ρ fun e => Subtype.ext (hφj e))
  refine ⟨E, hE.prop.1, hEinj, fun a b hab => hi (congrArg Subtype.val hab), ?_⟩
  -- The image is essential in `E`, by the pointwise criterion transported along `E.subtype`.
  rw [LinearMap.range_codRestrict, isEssential_iff_forall_exists_smul]
  intro x hx0
  obtain ⟨r, hrN, hr0⟩ := hE.prop.2 x x.2 fun h0 => hx0 (Subtype.ext h0)
  exact ⟨r, hrN, fun h0 => hr0 (congrArg Subtype.val h0)⟩

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
