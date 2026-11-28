/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Colimit.FinitePresentation
import TauCeti.Algebra.Colimit.Ring.Cofinal

/-!
# Descending sections to later stages of a directed colimit

`RingHom.exists_of_comp_eq_of_finitePresentation_of_comp_algebraMap` descends a map from a
finitely presented algebra over a fixed stage to a later stage, compatibly with the base ring.
It uses `Ring.DirectLimit.ringEquivOfIsCofinal` and
`TauCeti.DirectLimit.Algebra.exists_eq_comp_of_finitePresentation`.

For finite étale algebras this gives section descent in Kedlaya and Liu, *Relative p-adic Hodge
theory: foundations*, Astérisque 371 (2015), Remark 1.2.9.
-/

public section

namespace RingHom

open Ring.DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {G : ι → Type*}
  [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G (f · · ·)]
  {i : ι} {S : Type*} [CommRing S] [Algebra (G i) S] [Algebra.FinitePresentation (G i) S]

/-- A map from a finitely presented algebra over stage `i` to the direct limit that extends
the canonical map from stage `i` factors through a later stage `j`, extending the transition
map from `i` to `j`. By the tensor product universal property, this descends sections of the
base-changed algebra. -/
theorem exists_of_comp_eq_of_finitePresentation_of_comp_algebraMap
    (g : S →+* Ring.DirectLimit G (f · · ·))
    (hg : g.comp (algebraMap (G i) S) = of G (f · · ·) i) :
    ∃ j, ∃ hij : i ≤ j, ∃ g' : S →+* G j,
      (of G (f · · ·) j).comp g' = g ∧ g'.comp (algebraMap (G i) S) = f i j hij := by
  -- Above the chosen stage, all transitions are maps of `G i`-algebras.
  let s := Set.Ici i
  have hs : IsCofinal s := fun j ↦
    let ⟨k, hik, hjk⟩ := exists_ge_ge i j
    ⟨k, hik, hjk⟩
  have : Nonempty s := ⟨⟨i, le_rfl⟩⟩
  have : IsDirectedOrder s := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let stageAlgebra (j : s) : Algebra (G i) (G j) := (f i j j.property).toAlgebra
  have halg (j : s) : algebraMap (G i) (G j) = f i j j.property :=
    RingHom.algebraMap_toAlgebra _
  let F (j k : s) (hjk : j ≤ k) : G j →ₐ[G i] G k :=
    ⟨f j k hjk, fun a ↦ by
      rw [halg, halg]
      exact DirectedSystem.map_map' f j.property hjk a⟩
  have hF (j k : s) (hjk : j ≤ k) (x : G j) : F j k hjk x = f j k hjk x := rfl
  have : DirectedSystem (fun j : s ↦ G j) (F · · ·) := ⟨
    fun j x ↦ (hF j j _ x).trans (DirectedSystem.map_self' f _),
    fun j k l hjk hkl x ↦ by
      simp only [hF, DirectedSystem.map_map' f]⟩
  let e := (ringEquivOfIsCofinal (f := f) hs).symm.trans
    (TauCeti.Ring.DirectLimit.ringEquivOfEq hF)
  have he (j : s) (x : G j) :
      e (of G (f · · ·) j x) = _root_.DirectLimit.Algebra.of _ F j x := by
    have h := (ringEquivOfIsCofinal (f := f) hs).symm_apply_apply (of _ _ j x)
    simp only [ringEquivOfIsCofinal_apply_of] at h
    rw [RingEquiv.trans_apply, h, TauCeti.Ring.DirectLimit.ringEquivOfEq_of]
    simp only [_root_.DirectLimit.Ring.of_apply, _root_.DirectLimit.Algebra.of_apply]
  let g₀ : S →ₐ[G i] _ :=
    ⟨e.toRingHom.comp g, fun a ↦ by
      have h := congr($hg a)
      rw [RingHom.comp_apply] at h
      suffices e (g (algebraMap (G i) S a)) = algebraMap (G i) _ a from this
      rw [h, he ⟨i, le_rfl⟩]
      rw [← (_root_.DirectLimit.Algebra.of _ F ⟨i, le_rfl⟩).commutes]
      apply congrArg (_root_.DirectLimit.Algebra.of _ F ⟨i, le_rfl⟩)
      rw [halg]
      exact (DirectedSystem.map_self' f a).symm⟩
  obtain ⟨j, g', h⟩ := TauCeti.DirectLimit.Algebra.exists_eq_comp_of_finitePresentation g₀
  refine ⟨j, j.property, g'.toRingHom, RingHom.ext fun x ↦ e.injective ?_, ?_⟩
  · rw [RingHom.comp_apply, he]
    exact (congr($h x)).symm
  · exact RingHom.ext fun x ↦ (g'.commutes x).trans (DFunLike.congr_fun (halg j) x)

end RingHom
