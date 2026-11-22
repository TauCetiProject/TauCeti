/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# Base change of closed rational points and closed fibres

Over an algebraically closed field `k`, every closed point of a locally-finite-type `k`-scheme has
a unique preimage in the base change along any field extension `L / k`
(`AlgebraicGeometry.Scheme.Hom.existsUnique_preimage_of_isPullback_of_isAlgClosed`). Consequently,
in a pullback square of `k`-schemes along `Spec L ⟶ Spec k`, the projection identifies the fibre
over a base-changed closed point `y'` with the fibre over `gY y'` whenever that fibre consists of
closed points (`AlgebraicGeometry.Scheme.Hom.fiberEquivOfIsAlgClosed`), in particular when the
morphism is locally quasi-finite
(`AlgebraicGeometry.Scheme.Hom.fiberEquivOfIsAlgClosedOfLocallyQuasiFinite`).
-/

public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

section SinglePullback

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X X' : Scheme.{u}}
  [X.Over (Spec (.of k))] [X'.Over (Spec (.of L))] {gX : X' ⟶ X}
  (HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))))

include HX in
/-- Over an algebraically closed field `k`, every closed point of a locally-finite-type `k`-scheme
has a unique preimage in the base change along any field extension `L / k`. -/
theorem existsUnique_preimage_of_isPullback_of_isAlgClosed [IsAlgClosed k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] {x : X} (hx : IsClosed {x}) :
    ∃! x' : X', gX x' = x := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let s : Spec (.of k) ⟶ X := pointOfClosedPoint (X ↘ Spec (.of k)) x hx
  have hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 _ := pointOfClosedPoint_comp (X ↘ Spec (.of k)) x hx
  have hw : (b ≫ s) ≫ (X ↘ Spec (.of k)) = 𝟙 _ ≫ b := by simp [hs]
  have hpre := TauCeti.AlgebraicGeometry.preimage_singleton_section_closedPoint_of_isPullback HX
    hs (HX.lift_snd (b ≫ s) (𝟙 _) hw) (HX.lift_fst (b ≫ s) (𝟙 _) hw)
  have hsx : s (closedPoint k) = x := pointOfClosedPoint_apply (X ↘ Spec (.of k)) x hx _
  rw [hsx] at hpre
  exact ⟨HX.lift (b ≫ s) (𝟙 _) hw (closedPoint L),
    Set.mem_preimage.mp (hpre.symm ▸ Set.mem_singleton _),
    fun _ hz ↦ Set.mem_singleton_iff.mp (hpre ▸ Set.mem_preimage.mpr hz)⟩

end SinglePullback

section PullbackSquare

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
  {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
  [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
  (Hf : IsPullback gX f' f gY)
  (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]

include Hf HY

/-- **Closed-fibre bijection under field extension from an algebraically closed field** along
`gX`, for any `y'` over a closed point `gY y'` whose fibre in `X` consists of closed points. -/
noncomputable def fiberEquivOfIsAlgClosed (y' : Y') (hy : IsClosed {gY y'})
    (hfib : ∀ x : X, f x = gY y' → IsClosed {x}) :
    {x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'} := by
  have HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    simpa only [comp_over] using Hf.paste_vert HY
  refine Equiv.ofBijective (fun x' ↦ ⟨gX x'.val, by
      rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, x'.property]⟩) ⟨?_, ?_⟩
  · rintro ⟨x'₁, hx'₁⟩ ⟨x'₂, hx'₂⟩ h
    have hxcl : IsClosed {gX x'₁} :=
      hfib (gX x'₁) (by rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, hx'₁])
    obtain ⟨_, -, hunique⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HX hxcl
    exact Subtype.ext ((hunique x'₁ rfl).trans (hunique x'₂ (congrArg Subtype.val h).symm).symm)
  · rintro ⟨x, hx⟩
    obtain ⟨x', hx', -⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HX (hfib x hx)
    obtain ⟨_, -, hyunique⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HY hy
    have hgy : gY (f' x') = gY y' := by
      rw [← Scheme.Hom.comp_apply, ← Hf.w, Scheme.Hom.comp_apply, hx', hx]
    exact ⟨⟨x', (hyunique (f' x') hgy).trans (hyunique y' rfl).symm⟩, Subtype.ext hx'⟩

/-- `fiberEquivOfIsAlgClosed` acts on underlying points via the projection `gX`. -/
@[simp]
theorem fiberEquivOfIsAlgClosed_coe (y' : Y') (hy : IsClosed {gY y'})
    (hfib : ∀ x : X, f x = gY y' → IsClosed {x}) (x' : {x' : X' // f' x' = y'}) :
    (fiberEquivOfIsAlgClosed Hf HY y' hy hfib x').val = gX x'.val :=
  (rfl)

/-- Specialization of `fiberEquivOfIsAlgClosed` to locally quasi-finite morphisms. -/
noncomputable def fiberEquivOfIsAlgClosedOfLocallyQuasiFinite [LocallyQuasiFinite f]
    (y' : Y') (hy : IsClosed {gY y'}) :
    {x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'} :=
  fiberEquivOfIsAlgClosed Hf HY y' hy fun _ hx ↦
    isClosed_singleton_of_locallyQuasiFinite_of_isClosed f (hx ▸ hy)

/-- `fiberEquivOfIsAlgClosedOfLocallyQuasiFinite` acts on underlying points via the projection
`gX`. -/
@[simp]
theorem fiberEquivOfIsAlgClosedOfLocallyQuasiFinite_coe [LocallyQuasiFinite f] (y' : Y')
    (hy : IsClosed {gY y'}) (x' : {x' : X' // f' x' = y'}) :
    (fiberEquivOfIsAlgClosedOfLocallyQuasiFinite Hf HY y' hy x').val = gX x'.val :=
  fiberEquivOfIsAlgClosed_coe Hf HY y' hy _ x'

end PullbackSquare

end AlgebraicGeometry.Scheme.Hom
