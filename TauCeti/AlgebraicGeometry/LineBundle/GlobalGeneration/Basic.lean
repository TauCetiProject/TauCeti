/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Topology.JacobsonSpace
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.AlgebraicGeometry.Modules.Skyscraper

/-!
# Global generation of line bundles

A line bundle is globally generated if every point has a global section which generates its
stalk. Equivalently, the nonvanishing loci of its global sections cover the scheme. A morphism
to the residue skyscraper detects a generating section whenever its image is nonzero. This
criterion turns surjectivity of restriction to a point into generation of the line bundle there.
Global generation is equivalent to the existence of Mathlib's
`SheafOfModules.GeneratingSections`, including the epimorphism from a free sheaf onto the
line bundle; more generally, any indexed family of global sections whose nonvanishing loci cover
`X` determines morphisms out of the invertible sheaf and induces an epimorphism from the free
sheaf (`TauCeti.AlgebraicGeometry.hom_ext_of_iSup_nonvanishingLocus_eq_top`,
`TauCeti.AlgebraicGeometry.epi_freeHomEquiv_symm_of_iSup_nonvanishingLocus_eq_top`). The trivial
line bundle is globally generated
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.isGloballyGenerated_trivial`), and so is every line
bundle on an affine scheme
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.isGloballyGenerated_of_isAffine`).

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
  exact hmem.right

/-- Morphisms out of an invertible sheaf are determined by their values on a family of global
sections whose nonvanishing loci cover `X`. -/
theorem hom_ext_of_iSup_nonvanishingLocus_eq_top {ι : Type*} {f : ι → Γ(M, ⊤)}
    (hcover : (⨆ i, M.nonvanishingLocus (f i)) = ⊤) {N : X.Modules} (p q : M ⟶ N)
    (htop : ∀ i, p.app ⊤ (f i) = q.app ⊤ (f i)) : p = q := by
  have hnat (r : M ⟶ N) {U V : X.Opens} (k : V ⟶ U) (s : Γ(M, U)) :
      r.app V (M.presheaf.map k.op s) = N.presheaf.map k.op (r.app U s) :=
    r.mapPresheaf.naturality_apply k.op s
  ext U m
  apply TopCat.Presheaf.section_ext (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top x)
  let V := U ⊓ M.nonvanishingLocus (f i)
  let k : V ⟶ U := homOfLE inf_le_left
  let j : V ⟶ ⊤ := V.leTop
  have hV : V ≤ M.nonvanishingLocus (M.presheaf.map j.op (f i)) := by
    rw [Scheme.Modules.nonvanishingLocus_map]
    exact le_inf le_rfl inf_le_right
  obtain ⟨a, ha⟩ := Scheme.Modules.surjective_smul_of_le_nonvanishingLocus hV
    (M.presheaf.map k.op m)
  have heq : N.presheaf.map k.op (p.app U m) = N.presheaf.map k.op (q.app U m) := by
    rw [← hnat, ← hnat, ← ha, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
      hnat, hnat, htop i]
  have hxV : x ∈ V := ⟨hx, hi⟩
  rw [← TopCat.Presheaf.germ_res_apply N.presheaf k x hxV,
    ← TopCat.Presheaf.germ_res_apply N.presheaf k x hxV]
  exact congrArg _ heq

/-- A family of global sections of an invertible sheaf whose nonvanishing loci cover `X` induces an
epimorphism from the free sheaf onto `M`. -/
theorem epi_freeHomEquiv_symm_of_iSup_nonvanishingLocus_eq_top {ι : Type u} (f : ι → Γ(M, ⊤))
    (hcover : (⨆ i, M.nonvanishingLocus (f i)) = ⊤) :
    Epi (M.freeHomEquiv.symm (fun i ↦ M.sectionsEquivTop.symm (f i))) := by
  -- Select the scheme-module category before introducing cancellation morphisms.
  change @Epi X.Modules _ _ _ _
  refine ⟨fun {N : X.Modules} p q hpq ↦
    hom_ext_of_iSup_nonvanishingLocus_eq_top hcover p q fun i ↦ ?_⟩
  have hcomp (r : M ⟶ N) :
      (M.freeHomEquiv.symm fun i ↦ M.sectionsEquivTop.symm (f i)) ≫ r =
        N.freeHomEquiv.symm fun i ↦
          SheafOfModules.sectionsMap r (M.sectionsEquivTop.symm (f i)) :=
    SheafOfModules.freeHomEquiv_symm_comp _ r
  have h := congrFun (N.freeHomEquiv.symm.injective ((hcomp p).symm.trans (hpq.trans (hcomp q)))) i
  simpa only [sectionsEquivTop_sectionsMap, M.sectionsEquivTop.apply_symm_apply] using
    congrArg N.sectionsEquivTop h

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

/-- Morphisms out of a globally generated line bundle are determined by global sections. -/
theorem IsGloballyGenerated.hom_ext {L : InvertibleSheaf X} (hL : L.IsGloballyGenerated)
    {N : X.Modules} (f g : L.obj ⟶ N) (htop : ∀ s : Γ(L.obj, ⊤), f.app ⊤ s = g.app ⊤ s) :
    f = g :=
  hom_ext_of_iSup_nonvanishingLocus_eq_top
    (isGloballyGenerated_iff_iSup_nonvanishingLocus_eq_top.mp hL) f g htop

/-- A globally generated line bundle admits Mathlib's generating-section data. The associated
morphism from the free sheaf is an epimorphism. -/
theorem IsGloballyGenerated.nonempty_generatingSections {L : InvertibleSheaf X}
    (hL : L.IsGloballyGenerated) : Nonempty L.obj.GeneratingSections :=
  ⟨{ I := Γ(L.obj, ⊤), s := L.obj.sectionsEquivTop.symm,
     epi := epi_freeHomEquiv_symm_of_iSup_nonvanishingLocus_eq_top id
       (isGloballyGenerated_iff_iSup_nonvanishingLocus_eq_top.mp hL) }⟩

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
  refine (cancel_epi σ.π).mp ?_
  have hcomp (r : L.obj ⟶ Scheme.skyscraperResidueField x) :
      σ.π ≫ r = (Scheme.skyscraperResidueField x).freeHomEquiv.symm
        fun i ↦ SheafOfModules.sectionsMap r (σ.s i) :=
    SheafOfModules.freeHomEquiv_symm_comp σ.s r
  rw [hcomp φ, hcomp 0]
  congr 2
  funext i
  apply (Scheme.skyscraperResidueField x).sectionsEquivTop.injective
  rw [Scheme.Modules.sectionsEquivTop_sectionsMap, Scheme.Modules.sectionsEquivTop_sectionsMap,
    htop]
  rfl

/-- The trivial line bundle on a scheme is globally generated. -/
@[simp]
theorem isGloballyGenerated_trivial (X : Scheme.{u}) : (trivial X).IsGloballyGenerated :=
  isGloballyGenerated_iff_nonempty_generatingSections.mpr
    ⟨(trivial_obj X).symm ▸ SheafOfModules.free.generatingSections PUnit⟩

/-- Every line bundle on an affine scheme is globally generated. -/
theorem isGloballyGenerated_of_isAffine [IsAffine X] (L : InvertibleSheaf X) :
    L.IsGloballyGenerated := fun x ↦
  Scheme.Modules.exists_mem_nonvanishingLocus_of_isAffineOpen L.obj (isAffineOpen_top X)
    (Opens.mem_top x)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
