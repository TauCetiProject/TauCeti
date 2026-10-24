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
Global generation is equivalent to the existence of Mathlib's
`SheafOfModules.GeneratingSections`, including the epimorphism from a free sheaf onto the
line bundle.

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

/-- An invertible sheaf has a nonzero morphism to the residue skyscraper at every point. -/
theorem exists_skyscraperResidueFieldHom_ne_zero (x : X) :
    ∃ φ : M ⟶ Scheme.skyscraperResidueField x, φ ≠ 0 := by
  classical
  obtain ⟨e⟩ := nonempty_linearEquiv_stalk_of_isInvertible M x
  let ρ (U : X.Opens) (hx : x ∈ U) : Γ(M, U) →+ X.residueField x :=
    ((X.residue x).hom.toAddMonoidHom.comp e.symm.toAddMonoidHom).comp
      (M.presheaf.germ U x hx).hom
  let f (U : X.Opens) : Γ(M, U) →+ Γ(Scheme.skyscraperResidueField x, U) :=
    if hx : x ∈ U then
      (Scheme.skyscraperResidueFieldEquiv x hx).symm.toAddMonoidHom.comp (ρ U hx)
    else 0
  have hf {U : X.Opens} (hx : x ∈ U) (s : Γ(M, U)) :
      Scheme.skyscraperResidueFieldEquiv x hx (f U s) =
        X.residue x (e.symm (M.presheaf.germ U x hx s)) := by
    simp [f, ρ, hx]
  have hnat {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
      f V (M.presheaf.map i.op s) =
        (Scheme.skyscraperResidueField x).presheaf.map i.op (f U s) := by
    by_cases hx : x ∈ V
    · apply (Scheme.skyscraperResidueFieldEquiv x hx).injective
      rw [hf hx, Scheme.skyscraperResidueFieldEquiv_map, hf (i.le hx),
        TopCat.Presheaf.germ_res_apply]
    · have := Scheme.subsingleton_skyscraperResidueField x hx
      exact Subsingleton.elim _ _
  have hsmul (U : X.Opens) (r : Γ(X, U)) (s : Γ(M, U)) :
      f U (r • s) = r • f U s := by
    by_cases hx : x ∈ U
    · apply (Scheme.skyscraperResidueFieldEquiv x hx).injective
      rw [hf hx, Scheme.skyscraperResidueFieldEquiv_smul, hf hx, germ_smul,
        e.symm.map_smul, smul_eq_mul, map_mul]
      exact congrArg (· * X.residue x (e.symm (M.presheaf.germ U x hx s)))
        (ConcreteCategory.congr_hom (X.germ_residue x hx) r)
    · have := Scheme.subsingleton_skyscraperResidueField x hx
      exact Subsingleton.elim _ _
  -- Send a germ to its coordinate in the local ring, then to its residue.
  let φ : M ⟶ Scheme.skyscraperResidueField x :=
    ⟨PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (f U.unop)
        naturality {U V} i := by
          ext s
          exact hnat i.unop s }
      (fun U r s ↦ hsmul U.unop r s)⟩
  -- A local section representing the basis germ has residue one.
  obtain ⟨U, hx, s, hs⟩ := M.presheaf.exists_germ_eq (e 1)
  refine ⟨φ, fun hφ ↦ ?_⟩
  have hz : f U s = 0 := congrArg (fun q : M ⟶ Scheme.skyscraperResidueField x ↦ q.app U s) hφ
  have := congrArg (Scheme.skyscraperResidueFieldEquiv x hx) hz
  rw [hf hx, hs, e.symm_apply_apply, map_one, map_zero] at this
  exact one_ne_zero this

/-- A section of an invertible sheaf generates at `x` if some morphism to the residue
skyscraper at `x` sends it to a nonzero element. -/
theorem mem_nonvanishingLocus_of_app_ne_zero {U : X.Opens}
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

/-- The compatible family obtained by restricting a global section of a line bundle. -/
noncomputable def compatibleSection (L : InvertibleSheaf X) (s : Γ(L.obj, ⊤)) : L.obj.sections :=
  PresheafOfModules.sectionsMk (fun U ↦ L.obj.presheaf.map U.unop.leTop.op s)
    (fun {U _} f ↦
      (ConcreteCategory.congr_hom (L.obj.presheaf.map_comp U.unop.leTop.op f) s).symm)

/-- The compatible family associated to a global section evaluates by restriction. -/
@[simp]
theorem compatibleSection_val (L : InvertibleSheaf X) (s : Γ(L.obj, ⊤)) (U : X.Opens) :
    (compatibleSection L s).val (op U) = L.obj.presheaf.map U.leTop.op s :=
  (rfl)

/-- Morphisms out of a globally generated line bundle are determined by global sections. -/
theorem IsGloballyGenerated.hom_ext {L : InvertibleSheaf X} (hL : L.IsGloballyGenerated)
    {N : X.Modules} (f g : L.obj ⟶ N) (htop : ∀ s : Γ(L.obj, ⊤), f.app ⊤ s = g.app ⊤ s) :
    f = g := by
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

/-- A globally generated line bundle admits Mathlib's generating-section data. The associated
morphism from the free sheaf is an epimorphism. -/
theorem IsGloballyGenerated.nonempty_generatingSections {L : InvertibleSheaf X}
    (hL : L.IsGloballyGenerated) : Nonempty L.obj.GeneratingSections := by
  refine ⟨{ I := Γ(L.obj, ⊤), s := compatibleSection L, epi := ?_ }⟩
  -- Keep the scheme-module category explicit when introducing the epimorphism test object.
  refine ⟨fun {N : X.Modules} f g hfg ↦ hL.hom_ext f g fun s ↦ ?_⟩
  have h := congrArg
    (fun p ↦ SheafOfModules.sectionsMap p (SheafOfModules.freeSection s)) hfg
  simp only [SheafOfModules.sectionsMap_comp,
    SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection] at h
  have htop := congrArg (fun t ↦ t.val (op ⊤)) h
  simpa only [SheafOfModules.sectionsMap, PresheafOfModules.sectionsMap_coe,
    compatibleSection_val, L.obj.presheaf.map_id] using htop

/-- Global generation of a line bundle is equivalent to the existence of Mathlib's
family of generating global sections. -/
theorem isGloballyGenerated_iff_nonempty_generatingSections {L : InvertibleSheaf X} :
    L.IsGloballyGenerated ↔ Nonempty L.obj.GeneratingSections := by
  refine ⟨IsGloballyGenerated.nonempty_generatingSections, fun ⟨σ⟩ x ↦ ?_⟩
  classical
  obtain ⟨φ, hφ⟩ := exists_skyscraperResidueFieldHom_ne_zero (M := L.obj) x
  by_contra hx
  have htop (s : Γ(L.obj, ⊤)) : φ.app ⊤ s = 0 := by
    by_contra hs
    exact hx ⟨s, mem_nonvanishingLocus_of_app_ne_zero
      (Opens.mem_top x) φ s hs⟩
  -- Vanishing on the generating family forces the entire residue morphism to vanish.
  apply hφ
  have : Epi σ.π := σ.epi
  apply (cancel_epi σ.π).mp
  apply (Scheme.skyscraperResidueField x).freeHomEquiv.injective
  funext i
  have hp (p : L.obj ⟶ Scheme.skyscraperResidueField x) :
      (Scheme.skyscraperResidueField x).freeHomEquiv (σ.π ≫ p) i =
        SheafOfModules.sectionsMap p (σ.s i) :=
    (SheafOfModules.freeHomEquiv_comp_apply σ.π p i).trans
      (congrArg (SheafOfModules.sectionsMap p)
        (congrFun ((SheafOfModules.freeHomEquiv L.obj).apply_symm_apply σ.s) i))
  have heq : SheafOfModules.sectionsMap φ (σ.s i) =
      SheafOfModules.sectionsMap (0 : L.obj ⟶ Scheme.skyscraperResidueField x) (σ.s i) := by
    apply PresheafOfModules.sections_ext
    intro U
    have hnat : φ.app U.unop (L.obj.presheaf.map U.unop.leTop.op ((σ.s i).val (op ⊤))) =
        (Scheme.skyscraperResidueField x).presheaf.map U.unop.leTop.op
          (φ.app ⊤ ((σ.s i).val (op ⊤))) :=
      φ.mapPresheaf.naturality_apply U.unop.leTop.op ((σ.s i).val (op ⊤))
    have hsection : L.obj.presheaf.map U.unop.leTop.op ((σ.s i).val (op ⊤)) = (σ.s i).val U :=
      PresheafOfModules.sections_property (σ.s i) U.unop.leTop.op
    have hz : φ.app U.unop ((σ.s i).val U) = 0 := by
      rw [← hsection, hnat, htop ((σ.s i).val (op ⊤)), map_zero]
    exact hz
  exact (hp φ).trans (heq.trans (hp 0).symm)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
