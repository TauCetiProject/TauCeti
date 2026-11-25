/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
public import TauCeti.RingTheory.Norm.FullSetOfSections.Projective
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Full sets of sections of a finite locally free scheme

Let `g : Z ⟶ S` be finite locally free and let `s₁, …, s_r` be sections of `g`. Following
Katz–Mazur §1.8, they form a **full set of sections** when, after every base change `T ⟶ S`, the
norm of every function `f` on `Z_T` is the product of its values at the base-changed sections:

  `Norm_{Z_T/T}(f) = ∏ i, s_{i,T}^*(f)`.

Over an affine open `U` of `S`, the sections `Γ(Z, g⁻¹ U)` form a finite projective
`Γ(S, U)`-algebra, and the sections `sᵢ` give `Γ(S, U)`-algebra maps
`sᵢ^* : Γ(Z, g⁻¹ U) → Γ(S, U)` (`sectionAlgHom`). The definition `IsFullSetOfSections` asks that
these form a full set of sections of the algebra in the sense of `TauCeti.IsFullSetOfSections`,
which quantifies over all base changes `Γ(S, U) → R`; since every scheme over `S` is covered by
affine schemes over affine opens of `S`, this is the condition after every base change, and
`IsFullSetOfSections.pullback` proves that it holds after base change along any `T ⟶ S`.

The **full-set locus** (Katz–Mazur 1.9.1) is the closed subscheme of `S` cut out by the norm
identities: the ideal sheaf `fullSetLocus g s hs`, whose ideal over an affine open `U` is the
ideal `TauCeti.fullSetLocusIdeal` of the coefficients of the norm identity for a generic function
on `Z` over `U`. A morphism `T ⟶ S` factors through it exactly when the base-changed sections are a
full set of sections of `Z_T` over `T` (`fullSetLocus_le_ker_iff`).

## Main definitions

* `TauCeti.AlgebraicGeometry.IsFullSetOfSections g s hs`: the sections `s` of `g` form a full set
  of sections.
* `TauCeti.AlgebraicGeometry.fullSetLocus g s hs`: the ideal sheaf on `S` of the full-set locus.

## Main results

* `TauCeti.AlgebraicGeometry.fullSetLocus_le_ker_iff`: **the universal property of the full-set
  locus**. A morphism `t : T ⟶ S` factors through the closed subscheme of `fullSetLocus g s hs`
  if and only if the base change of `s` along `t` is a full set of sections of `T ×_S Z ⟶ T`.
* `TauCeti.AlgebraicGeometry.isFullSetOfSections_iff_fullSetLocus_eq_bot`: `s` is a full set of
  sections exactly when its full-set locus is all of `S`.
* `TauCeti.AlgebraicGeometry.fullSetLocus_le_ker_iff_of_isPullback`: the same, for a base change
  given by any pullback square.
* `TauCeti.AlgebraicGeometry.IsFullSetOfSections.pullback`: a full set of sections remains one
  after any base change.
* `TauCeti.AlgebraicGeometry.IsFullSetOfSections.of_pullback`: full sets of sections descend
  along morphisms with trivial kernel.
* `TauCeti.AlgebraicGeometry.fullSetLocus_pullback`: the full-set locus commutes with base
  change.
* `TauCeti.AlgebraicGeometry.isFullSetOfSections_pullback_subschemeι_fullSetLocus`: over the
  full-set locus, the base-changed sections are a full set of sections.
* `TauCeti.AlgebraicGeometry.isFullSetOfSections_iff_of_isAffine`: over an affine base, a full set
  of sections of an affine morphism is detected on global sections alone.
* `TauCeti.AlgebraicGeometry.isFullSetOfSections_iff_of_iso`,
  `TauCeti.AlgebraicGeometry.isFullSetOfSections_subschemeι_comp_iff_of_eq`,
  `TauCeti.AlgebraicGeometry.fullSetLocus_eq_of_iso`,
  `TauCeti.AlgebraicGeometry.isFullSetOfSections_iff_of_equiv`, and
  `TauCeti.AlgebraicGeometry.fullSetLocus_eq_of_equiv`: invariance of full sets of sections and of
  their locus under isomorphisms over `S`, equalities of ideal sheaves, and reindexing.
* `TauCeti.AlgebraicGeometry.IsFullSetOfSections.finrank_eq_card`: if a finite flat morphism `g`
  admits a full set of sections indexed by `ι`, its rank at every point of `S` is `Fintype.card ι`.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §§1.8–1.9.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.IdealSheafData

variable {Z S : Scheme.{u}} (g : Z ⟶ S)

variable {ι : Type*} (s : ι → (S ⟶ Z)) (hs : ∀ i, s i ≫ g = 𝟙 S)

variable {T : Scheme.{u}} (t : T ⟶ S)

variable [Fintype ι]

/-- The sections `s` of `g : Z ⟶ S` form a **full set of sections** (Katz–Mazur §1.8): over every
affine open `U` of `S`, the algebra maps `sᵢ^* : Γ(Z, g⁻¹ U) → Γ(S, U)` are a full set of sections
of the finite `Γ(S, U)`-algebra `Γ(Z, g⁻¹ U)`. The latter condition asks that after every base
change `Γ(S, U) → R`, the norm of every function on `Z_R` be the product of its values at the
sections, so this is the norm identity after every base change `T ⟶ S`
(`IsFullSetOfSections.pullback`). -/
def IsFullSetOfSections : Prop :=
  ∀ U : S.affineOpens, letI := (g.app U).hom.toAlgebra
    TauCeti.IsFullSetOfSections (fun i ↦ sectionAlgHom g (hs i) U)

/-- Unfolding `IsFullSetOfSections`: over every affine open `U` of `S`, the algebra maps
`sᵢ^* : Γ(Z, g⁻¹ U) → Γ(S, U)` are a full set of sections. -/
theorem isFullSetOfSections_iff : IsFullSetOfSections g s hs ↔
    ∀ U : S.affineOpens, letI := (g.app U).hom.toAlgebra
      TauCeti.IsFullSetOfSections (fun i ↦ sectionAlgHom g (hs i) U) :=
  Iff.rfl

variable [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]

/-- The ideal sheaf on `S` of the **full-set locus** of the sections `s` of the finite locally free
morphism `g` (Katz–Mazur 1.9.1). Over an affine open `U` of `S`, its ideal is
`TauCeti.fullSetLocusIdeal` of the algebra maps `sᵢ^* : Γ(Z, g⁻¹ U) → Γ(S, U)`: the ideal of
coefficients of the norm identity for a generic function on `Z` over `U`. A morphism `T ⟶ S`
factors through its closed subscheme exactly when the base change of `s` is a full set of sections
(`fullSetLocus_le_ker_iff`). -/
noncomputable def fullSetLocus : S.IdealSheafData where
  ideal U := letI := (g.app U).hom.toAlgebra
    haveI : Module.Finite Γ(S, U) Γ(Z, g ⁻¹ᵁ U) := g.finite_app U U.property
    haveI := g.projective_app U
    fullSetLocusIdeal (fun i ↦ sectionAlgHom g (hs i) U)
  map_ideal_basicOpen U f := by
    have hle : g ⁻¹ᵁ S.basicOpen f ≤ g ⁻¹ᵁ U.val := g.preimage_mono (S.basicOpen_le f)
    -- `Γ(Z, g⁻¹ D(f))` is the pushout of `Γ(S, D(f))` and `Γ(Z, g⁻¹ U)` over `Γ(S, U)`
    have hpush := (isIso_pushoutSection_iff (IsPullback.of_horiz_isIso ⟨by simp⟩ :
      IsPullback (𝟙 Z) g g (𝟙 S)) (S.basicOpen_le f) le_rfl (UY := g ⁻¹ᵁ S.basicOpen f)
      (by simpa using hle)).1 (isIso_pushoutSection_of_isAffineOpen _ _ _ _ U.property
        (S.affineBasicOpen f).property (U.property.preimage g))
    simp only [Scheme.Hom.appLE_eq_app] at hpush
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at hpush
    algebraize [(g.app U).hom, (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom,
      (g.app (S.basicOpen f)).hom, (Z.presheaf.map (homOfLE hle).op).hom,
      (Z.presheaf.map (homOfLE hle).op).hom.comp (g.app U).hom]
    have : IsScalarTower Γ(S, U) Γ(S, S.basicOpen f) Γ(Z, g ⁻¹ᵁ S.basicOpen f) :=
      .of_algebraMap_eq' congr($(g.naturality (homOfLE (S.basicOpen_le f)).op).hom).symm
    have : Algebra.IsPushout Γ(S, U) Γ(S, S.basicOpen f) Γ(Z, g ⁻¹ᵁ U)
        Γ(Z, g ⁻¹ᵁ S.basicOpen f) :=
      ((CommRingCat.isPushout_iff_isPushout).1 hpush).symm
    have : Module.Finite Γ(S, U) Γ(Z, g ⁻¹ᵁ U) := g.finite_app U U.property
    have := g.projective_app U
    have : Module.Finite Γ(S, S.basicOpen f) Γ(Z, g ⁻¹ᵁ S.basicOpen f) :=
      g.finite_app _ (S.affineBasicOpen f).property
    have : Module.Projective Γ(S, S.basicOpen f) Γ(Z, g ⁻¹ᵁ S.basicOpen f) :=
      g.projective_app (S.affineBasicOpen f)
    refine map_fullSetLocusIdeal_of_isPushout (A' := Γ(S, S.basicOpen f))
      (B' := Γ(Z, g ⁻¹ᵁ S.basicOpen f)) _ _ fun i b ↦ ?_
    -- `sectionAlgHom` evaluates `appLE`; write both sides as composites to use its naturality
    refine (sectionAlgHom_apply g (hs i) (S.basicOpen f) _).trans ?_
    rw [sectionAlgHom_apply]
    change (Z.presheaf.map (homOfLE hle).op ≫ (s i).appLE _ (S.basicOpen f)
      (preimage_preimage_of_comp_eq_id g (hs i) _).ge) b =
      ((s i).appLE _ U.val (preimage_preimage_of_comp_eq_id g (hs i) _).ge ≫
        S.presheaf.map (homOfLE (S.basicOpen_le f)).op) b
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- Over an affine open `U`, the ideal of the full-set locus is the ideal
`TauCeti.fullSetLocusIdeal` of the algebra maps `sᵢ^* : Γ(Z, g⁻¹ U) → Γ(S, U)`. -/
theorem fullSetLocus_ideal (U : S.affineOpens) :
    (fullSetLocus g s hs).ideal U = letI := (g.app U).hom.toAlgebra
      haveI : Module.Finite Γ(S, U) Γ(Z, g ⁻¹ᵁ U) := g.finite_app U U.property
      haveI := g.projective_app U
      fullSetLocusIdeal (fun i ↦ sectionAlgHom g (hs i) U) :=
  (rfl)

/-- The sections `s` form a full set of sections exactly when their full-set locus is all of
`S`. -/
theorem isFullSetOfSections_iff_fullSetLocus_eq_bot :
    IsFullSetOfSections g s hs ↔ fullSetLocus g s hs = ⊥ := by
  have key (U : S.affineOpens) : (fullSetLocus g s hs).ideal U = ⊥ ↔
      letI := (g.app U).hom.toAlgebra
      TauCeti.IsFullSetOfSections (fun i ↦ sectionAlgHom g (hs i) U) := by
    let := (g.app U).hom.toAlgebra
    have : Module.Finite Γ(S, U) Γ(Z, g ⁻¹ᵁ U) := g.finite_app U U.property
    have := g.projective_app U
    exact fullSetLocusIdeal_eq_bot_iff _
  refine ⟨fun h ↦ Scheme.IdealSheafData.ext (funext fun U ↦ (key U).2 (h U)), fun h U ↦ ?_⟩
  exact (key U).1 (by rw [h, ideal_bot]; rfl)

section IsPullback

variable {t} {Z' : Scheme.{u}} {g' : Z' ⟶ T} {gZ : Z' ⟶ Z} (H : IsPullback gZ g' g t)
  [IsFinite g'] [Flat g'] [LocallyOfFinitePresentation g'] {s' : ι → (T ⟶ Z')}
  (hs' : ∀ i, s' i ≫ g' = 𝟙 T) (hss' : ∀ i, s' i ≫ gZ = t ≫ s i)

omit [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
  [IsFinite g'] [Flat g'] [LocallyOfFinitePresentation g'] in
include H hss' in
private theorem isFullSetOfSections_sectionAlgHom_iff_of_isPullback [IsAffineHom g]
    (U : S.affineOpens) (V : T.affineOpens) (hV : V.val ≤ t ⁻¹ᵁ U) :
    (letI := (g'.app V).hom.toAlgebra
     TauCeti.IsFullSetOfSections (fun i ↦ sectionAlgHom g' (hs' i) V)) ↔
      (letI := (g.app U).hom.toAlgebra; letI := (t.appLE U V hV).hom.toAlgebra
       TauCeti.IsFullSetOfSections
         (fun i ↦ (sectionAlgHom g (hs i) U).sectionBaseChange Γ(T, V))) := by
  have hUY : g' ⁻¹ᵁ V.val = gZ ⁻¹ᵁ g ⁻¹ᵁ U ⊓ g' ⁻¹ᵁ V :=
    (inf_eq_right.2 fun x hx ↦ by
      -- membership in a preimage is membership of the image
      change g (gZ x) ∈ U.val
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      exact hV hx).symm
  -- the sections of `Z'` over `V` are the pushout of `Γ(T, V)` and `Γ(Z, g⁻¹ U)`
  have hpush := (isIso_pushoutSection_iff H hV le_rfl hUY).1
    (isIso_pushoutSection_of_isAffineOpen _ _ _ _ U.property V.property (U.property.preimage g))
  simp only [Scheme.Hom.appLE_eq_app] at hpush
  have hle : g' ⁻¹ᵁ V.val ≤ gZ ⁻¹ᵁ g ⁻¹ᵁ U := hUY.le.trans inf_le_left
  algebraize [(g.app U).hom, (t.appLE U V hV).hom, (gZ.appLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ V.val) hle).hom,
    (g'.app V).hom, (g'.app V).hom.comp (t.appLE U V hV).hom]
  have : IsScalarTower Γ(S, U) Γ(Z, g ⁻¹ᵁ U) Γ(Z', g' ⁻¹ᵁ V.val) :=
    .of_algebraMap_eq' congr($(hpush.w).hom).symm
  have : Algebra.IsPushout Γ(S, U) Γ(T, V) Γ(Z, g ⁻¹ᵁ U) Γ(Z', g' ⁻¹ᵁ V.val) :=
    ((CommRingCat.isPushout_iff_isPushout).1 hpush).symm
  refine (isFullSetOfSections_iff_of_isPushout fun i b ↦ ?_)
  -- both sides are the restriction of `b` along `t ≫ sᵢ`
  have key : ∀ (φ ψ : T ⟶ Z) (_ : φ = ψ) (e : V.val ≤ φ ⁻¹ᵁ g ⁻¹ᵁ U) (e' : V.val ≤ ψ ⁻¹ᵁ g ⁻¹ᵁ U),
      φ.appLE (g ⁻¹ᵁ U) V e = ψ.appLE (g ⁻¹ᵁ U) V e' := by
    rintro _ _ rfl _ _
    rfl
  -- `sectionAlgHom` evaluates `appLE`; write both sides as composites of `appLE`s
  simp only [sectionAlgHom_apply]
  change (gZ.appLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ V.val) hle ≫
      (s' i).appLE _ V (preimage_preimage_of_comp_eq_id _ (hs' i) _).ge) b =
    ((s i).appLE (g ⁻¹ᵁ U) U (preimage_preimage_of_comp_eq_id g (hs i) _).ge ≫
      t.appLE U V hV) b
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, key _ _ (hss' i)]

omit [IsFinite g'] [Flat g'] [LocallyOfFinitePresentation g'] in
include H hss' in
/-- The universal property over a pair of affine opens: for affine opens `U ⊆ S` and `V ⊆ T`
with `t(V) ⊆ U`, the restriction `Γ(S, U) → Γ(T, V)` kills the ideal of the full-set locus over
`U` exactly when the base-changed sections form a full set of sections over `V`. -/
private theorem fullSetLocus_ideal_le_ker_iff (U : S.affineOpens) (V : T.affineOpens)
    (hV : V.val ≤ t ⁻¹ᵁ U) :
    (fullSetLocus g s hs).ideal U ≤ RingHom.ker (t.appLE U V hV).hom ↔
      letI := (g'.app V).hom.toAlgebra
      TauCeti.IsFullSetOfSections (fun i ↦ sectionAlgHom g' (hs' i) V) := by
  let := (g.app U).hom.toAlgebra; let := (t.appLE U V hV).hom.toAlgebra
  have : Module.Finite Γ(S, U) Γ(Z, g ⁻¹ᵁ U) := g.finite_app U U.property
  have := g.projective_app U
  rw [fullSetLocus_ideal, ← RingHom.algebraMap_toAlgebra (t.appLE U V hV).hom]
  exact (fullSetLocusIdeal_le_ker_iff (fun i ↦ sectionAlgHom g (hs i) U) Γ(T, V)).trans
    (isFullSetOfSections_sectionAlgHom_iff_of_isPullback g s hs H hs' hss' U V hV).symm

include H hss' in
/-- **The universal property of the full-set locus** (Katz–Mazur 1.9.1), for a base change given
by any pullback square: `t : T ⟶ S` factors through the closed subscheme of `fullSetLocus g s hs`
exactly when the sections `s'` of the base change `g' : Z' ⟶ T` of `g` lying over `t ≫ sᵢ` are a
full set of sections. -/
theorem fullSetLocus_le_ker_iff_of_isPullback :
    fullSetLocus g s hs ≤ t.ker ↔ IsFullSetOfSections g' s' hs' := by
  constructor
  · intro h V
    let := (g'.app V).hom.toAlgebra
    have : Module.Finite Γ(T, V) Γ(Z', g' ⁻¹ᵁ V.val) := g'.finite_app V V.property
    have := g'.projective_app V
    refine (fullSetLocusIdeal_eq_bot_iff _).1 (eq_bot_iff.2 fun a ha ↦
      (Submodule.mem_bot _).2 (T.IsSheaf.section_ext fun p hp ↦ ?_))
    -- near `p`, choose affine opens `US ⊆ S` and `V' ⊆ V ∩ t⁻¹ US`
    obtain ⟨_, ⟨US, hUS, rfl⟩, hpUS, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (t p)) isOpen_univ
    obtain ⟨_, ⟨V', hV', rfl⟩, hpV', hV'le⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ V.val ⊓ t ⁻¹ᵁ US from ⟨hp, hpUS⟩) (V.val ⊓ t ⁻¹ᵁ US).is_open'
    have hV'V : (⟨V', hV'⟩ : T.affineOpens) ≤ V := fun y hy ↦ (hV'le hy).1
    refine ⟨V', hV'V, hpV', ?_⟩
    -- over `V'`, the sections `s'` are a full set, so the ideal of their locus vanishes
    have hfull := (fullSetLocus_ideal_le_ker_iff g s hs H hs' hss' ⟨US, hUS⟩ ⟨V', hV'⟩
      fun y hy ↦ (hV'le hy).2).1
      ((fullSetLocus g s hs).ideal_le_ker_appLE h ⟨US, hUS⟩ _)
    have hbot : (fullSetLocus g' s' hs').ideal ⟨V', hV'⟩ = ⊥ := by
      let := (g'.app V').hom.toAlgebra
      have : Module.Finite Γ(T, V') Γ(Z', g' ⁻¹ᵁ V') := g'.finite_app V' hV'
      have := g'.projective_app ⟨V', hV'⟩
      exact (fullSetLocusIdeal_eq_bot_iff _).2 hfull
    have hmem := (fullSetLocus g' s' hs').ideal_le_comap_ideal hV'V ha
    rw [Ideal.mem_comap, hbot, Ideal.mem_bot] at hmem
    rw [map_zero]
    exact hmem
  · intro h
    refine (fullSetLocus g s hs).le_ker_iff t |>.2 fun U V hVU ↦ fun a ha ↦ ?_
    exact (fullSetLocus_ideal_le_ker_iff g s hs H hs' hss' U V hVU).2 (h _) ha

end IsPullback

/-- **The universal property of the full-set locus** (Katz–Mazur 1.9.1). Let `g : Z ⟶ S` be
finite locally free with sections `s`. A morphism `t : T ⟶ S` factors through the closed
subscheme of `fullSetLocus g s hs` exactly when the base change of `s` along `t` is a full set of
sections of `T ×_S Z ⟶ T`. -/
theorem fullSetLocus_le_ker_iff :
    fullSetLocus g s hs ≤ t.ker ↔ IsFullSetOfSections (pullback.fst t g)
      (fun i ↦ baseChangeSection g (s i) (hs i) (Over.mk t))
      (fun i ↦ baseChangeSection_fst g (s i) (hs i) (Over.mk t)) :=
  fullSetLocus_le_ker_iff_of_isPullback g s hs (IsPullback.of_hasPullback t g).flip _
    fun i ↦ baseChangeSection_snd g (s i) (hs i) (Over.mk t)

/-- **Full sets of sections are stable under base change**: if the sections `s` of `g` are a full
set of sections, then so are their base changes along any `t : T ⟶ S`. -/
theorem IsFullSetOfSections.pullback (h : IsFullSetOfSections g s hs) :
    IsFullSetOfSections (pullback.fst t g) (fun i ↦ baseChangeSection g (s i) (hs i) (Over.mk t))
      (fun i ↦ baseChangeSection_fst g (s i) (hs i) (Over.mk t)) :=
  (fullSetLocus_le_ker_iff g s hs t).1
    (((isFullSetOfSections_iff_fullSetLocus_eq_bot g s hs).1 h).symm ▸ bot_le)

/-- **Descent of full sets of sections.** If `t : T ⟶ S` has trivial kernel, that is, `T` is
scheme-theoretically dense over `S`, and the base change of `s` along `t` is a full set of
sections, then `s` is a full set of sections. -/
theorem IsFullSetOfSections.of_pullback (ht : t.ker = ⊥)
    (h : IsFullSetOfSections (pullback.fst t g)
      (fun i ↦ baseChangeSection g (s i) (hs i) (Over.mk t))
      (fun i ↦ baseChangeSection_fst g (s i) (hs i) (Over.mk t))) :
    IsFullSetOfSections g s hs :=
  (isFullSetOfSections_iff_fullSetLocus_eq_bot g s hs).2
    (le_bot_iff.1 (ht ▸ (fullSetLocus_le_ker_iff g s hs t).2 h))

/-- Over the full-set locus, the base-changed sections are a full set of sections: the universal
family of the full-set locus. -/
theorem isFullSetOfSections_pullback_subschemeι_fullSetLocus :
    IsFullSetOfSections (pullback.fst (fullSetLocus g s hs).subschemeι g)
      (fun i ↦ baseChangeSection g (s i) (hs i) (Over.mk _))
      (fun i ↦ baseChangeSection_fst g (s i) (hs i) (Over.mk _)) :=
  (fullSetLocus_le_ker_iff g s hs _).1 (ker_subschemeι _).ge

/-- **The full-set locus commutes with base change.** For `t : T ⟶ S`, the full-set locus of the
base-changed sections of `T ×_S Z ⟶ T` is the inverse image of the full-set locus of `s`. -/
theorem fullSetLocus_pullback :
    fullSetLocus (pullback.fst t g) (fun i ↦ baseChangeSection g (s i) (hs i) (Over.mk t))
        (fun i ↦ baseChangeSection_fst g (s i) (hs i) (Over.mk t)) =
      (fullSetLocus g s hs).comap t := by
  -- both sides have the same morphisms factoring through their closed subschemes
  have key {T' : Scheme.{u}} (r : T' ⟶ T) :
      fullSetLocus (pullback.fst t g) (fun i ↦ baseChangeSection g (s i) (hs i) (Over.mk t))
          (fun i ↦ baseChangeSection_fst g (s i) (hs i) (Over.mk t)) ≤ r.ker ↔
        (fullSetLocus g s hs).comap t ≤ r.ker := by
    rw [fullSetLocus_le_ker_iff, ← le_map_iff_comap_le, map_ker,
      fullSetLocus_le_ker_iff_of_isPullback g s hs
        ((IsPullback.of_hasPullback r (pullback.fst t g)).flip.paste_horiz
          (IsPullback.of_hasPullback t g).flip)
        (fun i ↦ baseChangeSection_fst (pullback.fst t g) _
          (baseChangeSection_fst g (s i) (hs i) (Over.mk t)) (Over.mk r))
        fun i ↦ (baseChangeSection_snd_assoc _ _ _ (Over.mk r) _).trans
          (congrArg (r ≫ ·) (baseChangeSection_snd g (s i) (hs i) (Over.mk t)))]
  exact le_antisymm
    (((key ((fullSetLocus g s hs).comap t).subschemeι).2 (ker_subschemeι _).ge).trans
      (ker_subschemeι _).le)
    (((key (fullSetLocus (pullback.fst t g)
      (fun i ↦ baseChangeSection g (s i) (hs i) (Over.mk t))
      (fun i ↦ baseChangeSection_fst g (s i) (hs i) (Over.mk t))).subschemeι).1
        (ker_subschemeι _).ge).trans (ker_subschemeι _).le)

omit [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] in
/-- **Over an affine base, a full set of sections of an affine morphism is detected on global
sections alone.** -/
theorem isFullSetOfSections_iff_of_isAffine [IsAffine S] [IsAffineHom g] :
    IsFullSetOfSections g s hs ↔
      letI := (g.app ⊤).hom.toAlgebra
      TauCeti.IsFullSetOfSections (fun i ↦ sectionAlgHom g (hs i) ⊤) := by
  let U : S.affineOpens := ⟨⊤, isAffineOpen_top S⟩
  refine ⟨fun h ↦ h U, fun h V ↦ ?_⟩
  let := (g.app U).hom.toAlgebra; let := ((𝟙 S : S ⟶ S).appLE U V le_top).hom.toAlgebra
  exact (isFullSetOfSections_sectionAlgHom_iff_of_isPullback g s hs
    (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 Z) g g (𝟙 S)) hs (fun i ↦ by simp) U V
    le_top).2 (h.baseChange_of_univ Γ(S, V))

/-- **The full-set locus is invariant under isomorphisms over `S`.** -/
theorem fullSetLocus_eq_of_iso {Z' : Scheme.{u}} {g' : Z' ⟶ S} [IsFinite g'] [Flat g']
    [LocallyOfFinitePresentation g'] (e : Z' ≅ Z) (heg : e.hom ≫ g = g') {s' : ι → (S ⟶ Z')}
    (hs' : ∀ i, s' i ≫ g' = 𝟙 S) (hse : ∀ i, s' i ≫ e.hom = s i) :
    fullSetLocus g' s' hs' = fullSetLocus g s hs := by
  have H : IsPullback e.hom g' g (𝟙 S) := .of_horiz_isIso ⟨by simp [heg]⟩
  refine eq_of_forall_le_ker_iff fun r ↦ ?_
  have H' : IsPullback (Limits.pullback.snd r g' ≫ e.hom) (Limits.pullback.fst r g') g r := by
    simpa using (IsPullback.of_hasPullback r g').flip.paste_horiz H
  rw [fullSetLocus_le_ker_iff, ← fullSetLocus_le_ker_iff_of_isPullback g s hs H'
    (fun i ↦ baseChangeSection_fst g' (s' i) (hs' i) (Over.mk r)) fun i ↦
    (baseChangeSection_snd_assoc g' (s' i) (hs' i) (Over.mk r) e.hom).trans
      (congrArg (r ≫ ·) (hse i))]

omit [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] in
/-- **Full sets of sections are invariant under isomorphisms over `S`.** -/
theorem isFullSetOfSections_iff_of_iso {Z' : Scheme.{u}} {g' : Z' ⟶ S} (e : Z' ≅ Z)
    (heg : e.hom ≫ g = g') {s' : ι → (S ⟶ Z')} (hs' : ∀ i, s' i ≫ g' = 𝟙 S)
    (hse : ∀ i, s' i ≫ e.hom = s i) :
    IsFullSetOfSections g' s' hs' ↔ IsFullSetOfSections g s hs := by
  refine forall_congr' fun U ↦ ?_
  let := (g.app U).hom.toAlgebra; let := (g'.app U).hom.toAlgebra
  have heinv : e.inv ≫ g' = g := by rw [← heg, Iso.inv_hom_id_assoc]
  have hle₁ : g' ⁻¹ᵁ U.val ≤ e.hom ⁻¹ᵁ g ⁻¹ᵁ U.val := by rw [← heg, Scheme.Hom.comp_preimage]
  have hle₂ : g ⁻¹ᵁ U.val ≤ e.inv ⁻¹ᵁ g' ⁻¹ᵁ U.val := by rw [← heinv, Scheme.Hom.comp_preimage]
  let eIso : Γ(Z, g ⁻¹ᵁ U) ≅ Γ(Z', g' ⁻¹ᵁ U) :=
    { hom := e.hom.appLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ U) hle₁
      inv := e.inv.appLE (g' ⁻¹ᵁ U) (g ⁻¹ᵁ U) hle₂
      hom_inv_id := (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans <|
        ((e.inv ≫ e.hom).congr_appLE e.inv_hom_id _ _ _ le_rfl).trans
          (Scheme.Hom.appLE_eq_app (𝟙 Z))
      inv_hom_id := (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans <|
        ((e.hom ≫ e.inv).congr_appLE e.hom_inv_id _ _ _ le_rfl).trans
          (Scheme.Hom.appLE_eq_app (𝟙 Z')) }
  let eAlg : Γ(Z, g ⁻¹ᵁ U) ≃ₐ[Γ(S, U)] Γ(Z', g' ⁻¹ᵁ U) :=
    AlgEquiv.ofRingEquiv (f := eIso.commRingCatIsoToRingEquiv) fun r ↦ by
      have hcomp : g.app U ≫ e.hom.appLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ U) hle₁ = g'.app U :=
        g.app_eq_appLE.symm ▸ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
          (((e.hom ≫ g).congr_appLE heg _ _ _ le_rfl).trans g'.app_eq_appLE.symm)
      exact congr($(hcomp).hom r)
  refine (TauCeti.isFullSetOfSections_comp_algEquiv_iff eAlg).symm.trans
    (Iff.of_eq (congrArg TauCeti.IsFullSetOfSections (funext fun i ↦ AlgHom.ext fun b ↦ ?_)))
  have hcomp : e.hom.appLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ U) hle₁ ≫
      (s' i).appLE (g' ⁻¹ᵁ U) U (preimage_preimage_of_comp_eq_id g' (hs' i) U).ge =
    (s i).appLE (g ⁻¹ᵁ U) U (preimage_preimage_of_comp_eq_id g (hs i) U).ge :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      ((s' i ≫ e.hom).congr_appLE (hse i) _ _ _ _)
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.ofRingEquiv_apply,
    sectionAlgHom_apply, eAlg]
  exact congr($(hcomp).hom b)

omit [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] in
/-- **Transporting a full set of sections across an equality of ideal sheaves.** -/
theorem isFullSetOfSections_subschemeι_comp_iff_of_eq {X : Scheme.{u}} {f : X ⟶ S}
    {I J : X.IdealSheafData} (hIJ : I = J) {sI : ι → (S ⟶ I.subscheme)}
    (hsI : ∀ i, sI i ≫ (I.subschemeι ≫ f) = 𝟙 S) {sJ : ι → (S ⟶ J.subscheme)}
    (hsJ : ∀ i, sJ i ≫ (J.subschemeι ≫ f) = 𝟙 S)
    (hsec : ∀ i, sI i ≫ I.subschemeι = sJ i ≫ J.subschemeι) :
    IsFullSetOfSections (I.subschemeι ≫ f) sI hsI ↔
      IsFullSetOfSections (J.subschemeι ≫ f) sJ hsJ := by
  subst hIJ; obtain rfl : sI = sJ := funext fun i ↦ (cancel_mono I.subschemeι).1 (hsec i); rfl

omit [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] in
/-- **Full sets of sections are invariant under reindexing by an equivalence.** -/
theorem isFullSetOfSections_iff_of_equiv {ι' : Type*} [Fintype ι'] {s' : ι' → (S ⟶ Z)}
    (hs' : ∀ j, s' j ≫ g = 𝟙 S) (e : ι' ≃ ι) (hse : ∀ j, s' j = s (e j)) :
    IsFullSetOfSections g s' hs' ↔ IsFullSetOfSections g s hs := by
  refine forall_congr' fun U ↦ ?_; let := (g.app U).hom.toAlgebra
  have heq : (fun j ↦ sectionAlgHom g (hs' j) U) = (fun i ↦ sectionAlgHom g (hs i) U) ∘ e :=
    funext fun j ↦ AlgHom.ext fun b ↦ by
      simpa [sectionAlgHom_apply] using congr($((s' j).congr_appLE (hse j) _ _ _ _).hom b)
  rw [heq, TauCeti.isFullSetOfSections_comp_equiv_iff]

/-- **The full-set locus is invariant under reindexing sections by an equivalence.** -/
theorem fullSetLocus_eq_of_equiv {ι' : Type*} [Fintype ι'] {s' : ι' → (S ⟶ Z)}
    (hs' : ∀ j, s' j ≫ g = 𝟙 S) (e : ι' ≃ ι) (hse : ∀ j, s' j = s (e j)) :
    fullSetLocus g s' hs' = fullSetLocus g s hs := by
  refine eq_of_forall_le_ker_iff fun r ↦ ?_
  rw [fullSetLocus_le_ker_iff, fullSetLocus_le_ker_iff]
  exact isFullSetOfSections_iff_of_equiv (pullback.fst r g) _ _ _ e fun j ↦ by
    apply pullback.hom_ext <;> simp [hse j]

omit [LocallyOfFinitePresentation g] in
variable {g s hs} in
/-- **A finite flat morphism with a full set of sections has constant rank equal to `card ι`.** -/
theorem IsFullSetOfSections.finrank_eq_card (h : IsFullSetOfSections g s hs) (p : S) :
    g.finrank p = Fintype.card ι := by
  let r := S.fromSpecResidueField p; let g_p := Limits.pullback.fst r g
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ p) isOpen_univ
  have hle : (⊤ : (Spec (S.residueField p)).Opens) ≤ r ⁻¹ᵁ U := fun q _ ↦ by simpa [r] using hpU
  let : Algebra Γ(Spec (S.residueField p), ⊤) Γ(Limits.pullback r g, ⊤) := g_p.appTop.hom.toAlgebra
  let σ_p (i : ι) : Γ(Limits.pullback r g, ⊤) →ₐ[Γ(Spec (S.residueField p), ⊤)]
      Γ(Spec (S.residueField p), ⊤) :=
    sectionAlgHom g_p (baseChangeSection_fst g (s i) (hs i) (Over.mk r)) ⊤
  have htop : TauCeti.IsFullSetOfSections σ_p := by
    let := (g.app U).hom.toAlgebra; let := (r.appLE U ⊤ hle).hom.toAlgebra
    exact (isFullSetOfSections_sectionAlgHom_iff_of_isPullback g s hs
      (IsPullback.of_hasPullback r g).flip _
      (fun i ↦ baseChangeSection_snd g (s i) (hs i) (Over.mk r)) ⟨U, hU⟩ ⟨⊤, isAffineOpen_top _⟩
      hle).2 ((h ⟨U, hU⟩).baseChange_of_univ _)
  let eA := (Scheme.ΓSpecIso (S.residueField p)).commRingCatIsoToRingEquiv
  have := eA.toEquiv.nontrivial; have := eA.symm.isLocalRing
  have := g_p.finite_appTop; have := g_p.free_appTop
  let : Algebra (S.residueField p) Γ(Limits.pullback r g, ⊤) :=
    ((Scheme.ΓSpecIso (S.residueField p)).inv ≫ g_p.appTop).hom.toAlgebra
  have hfinrank := Algebra.finrank_eq_of_equiv_equiv eA (.refl _) (RingHom.ext fun x ↦
    congr($(Iso.hom_inv_id_assoc (Scheme.ΓSpecIso (S.residueField p)) g_p.appTop).hom x))
  rw [g.finrank_eq_finrank_pullback_fromSpecResidueField p rfl, ← hfinrank, htop.card_eq_finrank]

end TauCeti.AlgebraicGeometry
