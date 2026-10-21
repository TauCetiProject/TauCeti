/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Topology.JacobsonSpace
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.Modules.Skyscraper

/-!
# Global generation of line bundles

A line bundle is globally generated if every point has a global section which generates its
stalk. Equivalently, the nonvanishing loci of its global sections cover the scheme. A morphism
to the residue skyscraper detects a generating section whenever its image is nonzero. This
criterion turns surjectivity of restriction to a point into generation of the line bundle there.
Global generation supplies Mathlib's `SheafOfModules.GeneratingSections`, including the
epimorphism from a free sheaf onto the line bundle.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 7.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]

/-- A section of an invertible sheaf generates at `x` if some morphism to the residue
skyscraper at `x` sends it to a nonzero element. -/
theorem mem_nonvanishingLocus_of_skyscraperResidueFieldHom_ne_zero {U : X.Opens}
    {x : X} (hx : x ∈ U) (φ : M ⟶ Scheme.skyscraperResidueField x)
    (s : Γ(M, U)) (hs : φ.app U s ≠ 0) : x ∈ M.nonvanishingLocus s := by
  obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
  let i : U ⊓ V ⟶ U := homOfLE inf_le_left
  let j : U ⊓ V ⟶ V := homOfLE inf_le_right
  let r := trivializationCoordinate M t j (M.presheaf.map i.op s)
  have hxUV : x ∈ U ⊓ V := ⟨hx, hxV⟩
  have hnat : φ.app (U ⊓ V) (M.presheaf.map i.op s) =
      (Scheme.skyscraperResidueField x).presheaf.map i.op
        (φ.app U s) := φ.mapPresheaf.naturality_apply i.op s
  have hne : φ.app (U ⊓ V) (M.presheaf.map i.op s) ≠ 0 := by
    intro h
    apply hs
    apply (Scheme.skyscraperResidueFieldEquiv x hx).injective
    simpa only [Scheme.skyscraperResidueFieldEquiv_map, map_zero]
      using congrArg (Scheme.skyscraperResidueFieldEquiv x hxUV)
        (hnat.symm.trans h)
  have hr : IsUnit (X.presheaf.germ (U ⊓ V) x hxUV r) := by
    by_contra h
    have hz : X.evaluation (U ⊓ V) x hxUV r = 0 := by
      rw [← X.germ_residue, ConcreteCategory.comp_apply]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr h
    apply hne
    apply (Scheme.skyscraperResidueFieldEquiv x hxUV).injective
    conv_lhs => rw [eq_trivializationCoordinate_smul_map_trivializationGenerator M t j
      (M.presheaf.map i.op s)]
    rw [Hom.app_smul, Scheme.skyscraperResidueFieldEquiv_smul,
      hz, zero_mul, map_zero]
  have hmem : x ∈ M.nonvanishingLocus (M.presheaf.map i.op s) := by
    rw [nonvanishingLocus_eq_basicOpen t j]
    exact (X.mem_basicOpen _ _ hxUV).mpr hr
  rw [nonvanishingLocus_map] at hmem
  exact hmem.2

end TauCeti.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}}

/-- A line bundle is globally generated if, at each point, some global section generates the
stalk. -/
def IsGloballyGenerated (L : InvertibleSheaf X) : Prop :=
  ∀ x : X, ∃ s : Γ(L.obj, ⊤), x ∈ L.obj.nonvanishingLocus s

/-- Global generation means that a generating global section exists at each point. -/
theorem isGloballyGenerated_iff {L : InvertibleSheaf X} :
    L.IsGloballyGenerated ↔ ∀ x : X, ∃ s : Γ(L.obj, ⊤), x ∈ L.obj.nonvanishingLocus s :=
  Iff.rfl

/-- Global generation is equivalent to the nonvanishing loci of global sections covering `X`. -/
theorem isGloballyGenerated_iff_iSup_nonvanishingLocus_eq_top {L : InvertibleSheaf X} :
    L.IsGloballyGenerated ↔ (⨆ s : Γ(L.obj, ⊤), L.obj.nonvanishingLocus s) = ⊤ := by
  constructor
  · intro h
    exact top_unique fun x _ ↦ Opens.mem_iSup.mpr (h x)
  · intro h x
    exact Opens.mem_iSup.mp (h.symm ▸ Opens.mem_top x)

/-- Global generation is invariant under isomorphism of line bundles. -/
theorem isGloballyGenerated_iff_of_iso {L N : InvertibleSheaf X} (e : L.obj ≅ N.obj) :
    L.IsGloballyGenerated ↔ N.IsGloballyGenerated := by
  have transfer {L N : InvertibleSheaf X} (e : L.obj ≅ N.obj)
      (h : L.IsGloballyGenerated) : N.IsGloballyGenerated := by
    intro x
    obtain ⟨s, hs⟩ := h x
    exact ⟨e.hom.app ⊤ s, by rwa [Scheme.Modules.nonvanishingLocus_hom_app]⟩
  exact ⟨transfer e, transfer e.symm⟩

/-- On a Jacobson scheme, global generation can be checked at closed points. -/
theorem isGloballyGenerated_iff_forall_isClosed [JacobsonSpace X] {L : InvertibleSheaf X} :
    L.IsGloballyGenerated ↔
      ∀ x : X, IsClosed ({x} : Set X) → ∃ s : Γ(L.obj, ⊤), x ∈ L.obj.nonvanishingLocus s := by
  refine ⟨fun h x _ ↦ h x, fun h ↦ ?_⟩
  rw [isGloballyGenerated_iff_iSup_nonvanishingLocus_eq_top]
  let U : X.Opens := ⨆ s : Γ(L.obj, ⊤), L.obj.nonvanishingLocus s
  by_contra hU
  have hne : (U : Set X)ᶜ.Nonempty := by
    by_contra hn
    apply hU
    apply top_unique
    intro x _
    exact Classical.byContradiction fun hx ↦ hn ⟨x, hx⟩
  obtain ⟨x, hxU, hxclosed⟩ :=
    nonempty_inter_closedPoints hne U.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨s, hs⟩ := h x hxclosed
  exact hxU (Opens.mem_iSup.mpr ⟨s, hs⟩)

/-- A globally generated line bundle admits Mathlib's generating-section data. The associated
morphism from the free sheaf is an epimorphism. -/
theorem IsGloballyGenerated.nonempty_generatingSections {L : InvertibleSheaf X}
    (hL : L.IsGloballyGenerated) : Nonempty L.obj.GeneratingSections := by
  let σ : Γ(L.obj, ⊤) → L.obj.sections := fun s ↦
    PresheafOfModules.sectionsMk (fun U ↦ L.obj.presheaf.map U.unop.leTop.op s)
      (fun {U _} f ↦
        (ConcreteCategory.congr_hom (L.obj.presheaf.map_comp U.unop.leTop.op f) s).symm)
  let π : (SheafOfModules.free Γ(L.obj, ⊤) : X.Modules) ⟶ L.obj := L.obj.freeHomEquiv.symm σ
  have hcancel (N : X.Modules) (f g : L.obj ⟶ N) (hfg : π ≫ f = π ≫ g) : f = g := by
    have hσ (s : Γ(L.obj, ⊤)) :
        SheafOfModules.sectionsMap f (σ s) = SheafOfModules.sectionsMap g (σ s) := by
      have hp (p : L.obj ⟶ N) :
          SheafOfModules.sectionsMap (π ≫ p) (SheafOfModules.freeSection s) =
            SheafOfModules.sectionsMap p (σ s) :=
        (SheafOfModules.sectionsMap_comp _ _ _).trans
          (congrArg (SheafOfModules.sectionsMap p)
            (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection σ s))
      exact (hp f).symm.trans ((congrArg
        (fun p ↦ SheafOfModules.sectionsMap p (SheafOfModules.freeSection s)) hfg).trans (hp g))
    have htop (s : Γ(L.obj, ⊤)) : f.app ⊤ s = g.app ⊤ s := by
      have h := congrArg (fun t : N.sections ↦ t.val (op ⊤)) (hσ s)
      -- Native compatible sections evaluate through the same module-section carriers.
      change f.app ⊤ (L.obj.presheaf.map (𝟙 (op ⊤)) s) =
        g.app ⊤ (L.obj.presheaf.map (𝟙 (op ⊤)) s) at h
      rw [L.obj.presheaf.map_id] at h
      exact h
    have hnat (p : L.obj ⟶ N) {U V : X.Opens} (i : V ⟶ U) (s : Γ(L.obj, U)) :
        p.app V (L.obj.presheaf.map i.op s) = N.presheaf.map i.op (p.app U s) :=
      p.mapPresheaf.naturality_apply i.op s
    ext U m
    apply TopCat.Presheaf.section_ext (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    intro x hx
    obtain ⟨s, hs⟩ := hL x
    let V := U ⊓ L.obj.nonvanishingLocus s
    let i : V ⟶ U := homOfLE inf_le_left
    let j : V ⟶ ⊤ := V.leTop
    have hV : V ≤ L.obj.nonvanishingLocus (L.obj.presheaf.map j.op s) := by
      rw [Scheme.Modules.nonvanishingLocus_map]
      exact le_inf le_rfl inf_le_right
    obtain ⟨r, hr⟩ := Scheme.Modules.surjective_smul_of_le_nonvanishingLocus hV
      (L.obj.presheaf.map i.op m)
    have heq : N.presheaf.map i.op (f.app U m) = N.presheaf.map i.op (g.app U m) := by
      rw [← hnat, ← hnat, ← hr, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
        hnat, hnat, htop]
    have hxV : x ∈ V := ⟨hx, hs⟩
    rw [← TopCat.Presheaf.germ_res_apply N.presheaf i x hxV,
      ← TopCat.Presheaf.germ_res_apply N.presheaf i x hxV]
    exact congrArg _ heq
  exact ⟨{ I := Γ(L.obj, ⊤), s := σ, epi := ⟨fun {N} ↦ hcancel N⟩ }⟩

end TauCeti.AlgebraicGeometry.InvertibleSheaf
