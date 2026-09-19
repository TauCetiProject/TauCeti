/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import TauCeti.Algebra.Module.Injective.Envelope
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.Zorn

/-!
# Existence of injective envelopes

Every module over a ring has an injective envelope. Embed it in an injective module, choose
by Zorn's lemma a maximal essential extension of its image, and prove that extension injective.
The resulting envelope uses the existing `TauCeti.IsInjectiveEnvelope` interface.

## Main results

* `TauCeti.exists_isInjectiveEnvelope`: every module admits an injective envelope.
* `TauCeti.injectiveEnvelope`: a chosen injective envelope.
* `TauCeti.injectiveEnvelopeInclusion`: its essential inclusion.
* `TauCeti.isInjectiveEnvelope_inclusion`: the inclusion is an injective envelope.

The construction keeps the ring, the original module, and the envelope in the same universe.
No finiteness or commutativity assumption on the ring or module is needed.

## References

This supplies existence and the chosen envelope for Layer 3, "projective covers and injective
envelopes", of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
See T. Y. Lam, *Lectures on Modules and Rings*, §3.
-/

public section

namespace TauCeti

universe u

section Construction

variable {R M N : Type u} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- `A` meets every nonzero submodule of `B`. -/
private def EssentialIn (A B : Submodule R M) : Prop :=
  A ≤ B ∧ ∀ N : Submodule R M, N ≤ B → Disjoint A N → N = ⊥

private theorem essentialIn_refl (A : Submodule R M) : EssentialIn A A := by
  refine ⟨le_rfl, fun N hN hd => ?_⟩
  exact disjoint_self.mp (hd.mono_left hN)

private theorem EssentialIn.trans {A B C : Submodule R M}
    (hAB : EssentialIn A B) (hBC : EssentialIn B C) : EssentialIn A C := by
  refine ⟨hAB.1.trans hBC.1, fun N hN hd => hBC.2 N hN ?_⟩
  rw [disjoint_iff]
  exact hAB.2 (B ⊓ N) inf_le_left (hd.mono_right inf_le_right)

/-- A maximal essential extension exists inside any fixed ambient module. -/
private theorem exists_maximal_essential (A : Submodule R M) :
    ∃ B, Maximal (EssentialIn A) B := by
  apply zorn_le₀ {B | EssentialIn A B}
  intro c hc hchain
  by_cases hne : c.Nonempty
  · refine ⟨sSup c, ⟨?_, ?_⟩, fun B hB => le_sSup hB⟩
    · obtain ⟨B, hB⟩ := hne
      exact (hc hB).1.trans (le_sSup hB)
    · intro N hN hd
      apply le_antisymm _ bot_le
      intro x hx
      obtain ⟨B, hB, hxB⟩ :=
        (Submodule.mem_sSup_of_directed hne hchain.directedOn).mp (hN hx)
      have hz : B ⊓ N = ⊥ := (hc hB).2 _ inf_le_left (hd.mono_right inf_le_right)
      have : x ∈ B ⊓ N := ⟨hxB, hx⟩
      simpa [hz] using this
  · refine ⟨A, essentialIn_refl A, ?_⟩
    intro B hB
    exact (hne ⟨B, hB⟩).elim

/-- Maximal submodules disjoint from a given submodule exist, without finiteness assumptions. -/
private theorem exists_maximal_disjoint (A : Submodule R M) :
    ∃ K, Maximal (fun K => Disjoint A K) K := by
  apply zorn_le₀ {K | Disjoint A K}
  intro c hc hchain
  refine ⟨sSup c, ?_, fun K hK => le_sSup hK⟩
  by_cases hne : c.Nonempty
  · apply Submodule.disjoint_def.mpr
    intro x hxA hxc
    obtain ⟨K, hK, hxK⟩ :=
      (Submodule.mem_sSup_of_directed hne hchain.directedOn).mp hxc
    exact Submodule.disjoint_def.mp (hc hK) x hxA hxK
  · have : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [this]

/-- Dividing out a maximal disjoint submodule makes the given submodule essential. -/
private theorem essential_quotient_of_maximal_disjoint (A K : Submodule R M)
    (hK : Maximal (fun K => Disjoint A K) K) :
    EssentialIn (A.map K.mkQ) ⊤ := by
  refine ⟨le_top, fun N _ hd => ?_⟩
  have hdis : Disjoint A (N.comap K.mkQ) := by
    apply Submodule.disjoint_def.mpr
    intro x hxA hxN
    have hz : K.mkQ x = 0 := Submodule.disjoint_def.mp hd (K.mkQ x)
      (Submodule.mem_map.mpr ⟨x, hxA, rfl⟩) hxN
    exact Submodule.disjoint_def.mp hK.1 x hxA ((Submodule.Quotient.mk_eq_zero K).mp hz)
  have hle : K ≤ N.comap K.mkQ := by
    intro x hx
    change K.mkQ x ∈ N
    have hz : K.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hx
    rw [hz]
    exact N.zero_mem
  have heq : N.comap K.mkQ = K := le_antisymm (hK.2 hdis hle) hle
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨x, rfl⟩ := K.mkQ_surjective y
  have hx : x ∈ K := by
    rw [← heq]
    exact hy
  exact (Submodule.Quotient.mk_eq_zero K).mpr hx

/-- Essentiality passes through a map injective on the containing submodule. -/
private theorem EssentialIn.map {A B : Submodule R M} (hAB : EssentialIn A B)
    (f : M →ₗ[R] N) (hf : ∀ x ∈ B, f x = 0 → x = 0) :
    EssentialIn (A.map f) (B.map f) := by
  refine ⟨Submodule.map_mono hAB.1, fun L hL hd => ?_⟩
  have hz : B ⊓ L.comap f = ⊥ := by
    apply hAB.2 _ inf_le_left
    apply Submodule.disjoint_def.mpr
    intro x hxA hx
    apply hf x (hAB.1 hxA)
    exact Submodule.disjoint_def.mp hd (f x)
      (Submodule.mem_map.mpr ⟨x, hxA, rfl⟩) hx.2
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨x, hxB, rfl⟩ := Submodule.mem_map.mp (hL hy)
  have hx : x ∈ B ⊓ L.comap f := ⟨hxB, hy⟩
  have hx0 : x = 0 := by simpa [hz] using hx
  simp [hx0]

/-- Injectivity on an essential submodule forces injectivity everywhere. -/
private theorem injective_of_essential {A : Submodule R M} (hA : EssentialIn A ⊤)
    (f : M →ₗ[R] N) (hf : ∀ x ∈ A, f x = 0 → x = 0) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply hA.2 _ le_top
  exact Submodule.disjoint_def.mpr (fun x hxA hx => hf x hxA hx)

/-- A maximal essential extension inside an injective module is injective. -/
private theorem injective_of_maximal_essential [Module.Injective R M]
    (A B : Submodule R M) (hB : Maximal (EssentialIn A) B) :
    Module.Injective R B := by
  obtain ⟨K, hK⟩ := exists_maximal_disjoint B
  let i : B →ₗ[R] M ⧸ K := K.mkQ.comp B.subtype
  have hi : Function.Injective i := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hK.1 x x.property
      ((Submodule.Quotient.mk_eq_zero K).mp hx)
  obtain ⟨g, hg⟩ := Module.Injective.out i hi B.subtype
  have hquot := essential_quotient_of_maximal_disjoint B K hK
  have hg_inj : Function.Injective g := by
    apply injective_of_essential hquot g
    intro x hx hx0
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hx
    have heq := hg ⟨b, hb⟩
    change g (K.mkQ b) = b at heq
    have hb0 : b = 0 := heq.symm.trans hx0
    simp [hb0]
  have hAquot : EssentialIn (A.map K.mkQ) (B.map K.mkQ) := by
    apply hB.1.map K.mkQ
    intro x hx hx0
    exact Submodule.disjoint_def.mp hK.1 x hx
      ((Submodule.Quotient.mk_eq_zero K).mp hx0)
  have hAg := (hAquot.trans hquot).map g (fun x _ hx => hg_inj (by simpa using hx))
  have hmapA : (A.map K.mkQ).map g = A := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy
      have heq := hg ⟨a, hB.1.1 ha⟩
      change g (K.mkQ a) = a at heq
      change g (K.mkQ a) ∈ A
      rw [heq]
      exact ha
    · intro a ha
      refine Submodule.mem_map.mpr ⟨K.mkQ a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      exact hg ⟨a, hB.1.1 ha⟩
  have hABg : EssentialIn A (LinearMap.range g) := by
    simpa only [hmapA, Submodule.map_top] using hAg
  have hBrange : B ≤ LinearMap.range g := by
    intro b hb
    exact ⟨i ⟨b, hb⟩, hg ⟨b, hb⟩⟩
  have hrange : LinearMap.range g = B :=
    le_antisymm (hB.2 hABg hBrange) hBrange
  let r : M →ₗ[R] B := (g.comp K.mkQ).codRestrict B (by
    intro x
    rw [← hrange]
    exact ⟨K.mkQ x, rfl⟩)
  have hr : ∀ b : B, r b = b := by
    intro b
    apply Subtype.ext
    exact hg b
  constructor
  intro X Y _ _ _ _ f hf a
  obtain ⟨b, hb⟩ := Module.Injective.out f hf (B.subtype.comp a)
  refine ⟨r.comp b, fun x => ?_⟩
  change r (b (f x)) = a x
  rw [hb]
  exact hr (a x)

/-- Essentiality in a containing submodule, now regarded as the ambient module. -/
private theorem EssentialIn.restrict {A B : Submodule R M} (hAB : EssentialIn A B) :
    EssentialIn (A.comap B.subtype) ⊤ := by
  refine ⟨le_top, fun L _ hd => ?_⟩
  have hzero : L.map B.subtype = ⊥ := by
    apply hAB.2
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact y.property
    · apply Submodule.disjoint_def.mpr
      intro x hxA hxL
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hxL
      have hy0 := Submodule.disjoint_def.mp hd y hxA hy
      exact congrArg Subtype.val hy0
  apply le_antisymm _ bot_le
  intro y hy
  have : (y : M) ∈ L.map B.subtype := Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  have hy0 : (y : M) = 0 := by simpa [hzero] using this
  exact Subtype.ext hy0

/-- Every module admits an injective essential extension, with actual linear maps. -/
private theorem exists_injective_essential_extension (R M : Type u) [Ring R]
    [AddCommGroup M] [Module R M] :
    ∃ (E : ModuleCat.{u} R) (ι : M →ₗ[R] E),
      Module.Injective R E ∧ Function.Injective ι ∧ EssentialIn (LinearMap.range ι) ⊤ := by
  let I := CategoryTheory.Injective.under (ModuleCat.of R M)
  let ι : M →ₗ[R] I := (CategoryTheory.Injective.ι (ModuleCat.of R M)).hom
  have hι : Function.Injective ι := (ModuleCat.mono_iff_injective _).mp inferInstance
  let : CategoryTheory.Injective (ModuleCat.of R I) := by
    change CategoryTheory.Injective I
    dsimp [I]
    infer_instance
  let : Module.Injective R I := Module.injective_module_of_injective_object R I
  obtain ⟨B, hB⟩ := exists_maximal_essential (LinearMap.range ι)
  let j : M →ₗ[R] B := ι.codRestrict B (fun x => hB.1.1 ⟨x, rfl⟩)
  have hj : Function.Injective j := by
    intro x y h
    exact hι (congrArg Subtype.val h)
  have hrange : LinearMap.range j = (LinearMap.range ι).comap B.subtype := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  refine ⟨ModuleCat.of R B, j, injective_of_maximal_essential _ _ hB, hj, ?_⟩
  rw [hrange]
  exact hB.1.restrict

end Construction

/-- Every module over a ring admits an injective envelope in the same universe. -/
theorem exists_isInjectiveEnvelope (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] :
    ∃ (E : ModuleCat.{u} R) (i : M →ₗ[R] E), IsInjectiveEnvelope i := by
  obtain ⟨E, i, hE, hi, hess⟩ := exists_injective_essential_extension R M
  refine ⟨E, i, hE, hi, ?_⟩
  apply isEssential_iff.mpr
  intro N hN
  exact hess.2 N le_top (disjoint_iff.mpr hN)

/-- A chosen injective envelope of a module. -/
noncomputable def injectiveEnvelope (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] :
    ModuleCat.{u} R :=
  (exists_isInjectiveEnvelope R M).choose

/-- The essential inclusion of a module into its chosen injective envelope. -/
noncomputable def injectiveEnvelopeInclusion (R M : Type u) [Ring R]
    [AddCommGroup M] [Module R M] : M →ₗ[R] injectiveEnvelope R M :=
  (exists_isInjectiveEnvelope R M).choose_spec.choose

/-- The chosen inclusion exhibits an injective envelope. -/
theorem isInjectiveEnvelope_inclusion (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] :
    IsInjectiveEnvelope (injectiveEnvelopeInclusion R M) :=
  (exists_isInjectiveEnvelope R M).choose_spec.choose_spec

noncomputable instance (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] :
    Module.Injective R (injectiveEnvelope R M) :=
  (isInjectiveEnvelope_inclusion R M).moduleInjective

noncomputable instance (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] :
    CategoryTheory.Injective (injectiveEnvelope R M) :=
  Module.injective_object_of_injective_module R (injectiveEnvelope R M)

/-- The inclusion into the chosen injective envelope is injective. -/
theorem injective_injectiveEnvelopeInclusion (R M : Type u) [Ring R]
    [AddCommGroup M] [Module R M] : Function.Injective (injectiveEnvelopeInclusion R M) :=
  (isInjectiveEnvelope_inclusion R M).injective

/-- The inclusion into the chosen injective envelope has essential range. -/
theorem isEssential_range_injectiveEnvelopeInclusion (R M : Type u) [Ring R]
    [AddCommGroup M] [Module R M] :
    IsEssential (LinearMap.range (injectiveEnvelopeInclusion R M)) :=
  (isInjectiveEnvelope_inclusion R M).isEssential_range

end TauCeti
