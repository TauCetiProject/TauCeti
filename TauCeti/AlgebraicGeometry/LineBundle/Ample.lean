/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.LineBundle.TwistedSections
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Separation.Basic

/-!
# Ample line bundles

An invertible sheaf `L` on a scheme `X` is *ample* if `X` is quasi-compact and every point `x` of
`X` lies in the nonvanishing locus `X_s` of a global section `s` of some positive tensor power
`L^⊗n` such that `X_s` is affine. This is the positivity notion through which projective
morphisms, relative `Proj` and the stability of curves are expressed: a stable curve is one whose
(log-)dualizing sheaf is ample on every fibre.

Ampleness depends only on the isomorphism class of `L`, and tensor powers are available on
isomorphism classes, where they are powers in the Picard group. So ampleness is defined here as a
predicate `LineBundleClass.IsAmple` on line-bundle classes; for a line bundle `L` it reads
`(LineBundleClass.mk L).IsAmple`. The nonvanishing loci of the global sections of a line bundle
depend only on its isomorphism class (`Scheme.Modules.range_nonvanishingLocus_eq_of_iso`), so in the
definition any representative of the class of `L^⊗n` may be used
(`LineBundleClass.IsAmple.exists_pos_forall_mk_eq`).

For the trivial class the definition recovers quasi-affineness: the global sections of `𝒪_X` are
the regular functions `r` on `X`, whose nonvanishing loci are the basic open sets `X_r`, so `𝒪_X` is
ample exactly when `X` is quasi-compact and covered by affine basic open sets of global functions,
that is, when `X` is quasi-affine (`LineBundleClass.isAmple_one_iff`). In particular `𝒪_X` is ample
on every affine scheme, and so is every torsion class there
(`LineBundleClass.isAmple_of_pow_eq_one`). More generally, every line-bundle class on an affine
scheme is ample (`LineBundleClass.isAmple_of_isAffine`): the global sections of a line bundle
generate its stalks, and their nonvanishing loci are affine.

A scheme carrying an ample line bundle is quasi-separated
(`LineBundleClass.IsAmple.quasiSeparatedSpace`): it is covered by affine nonvanishing loci `X_s`,
and `X_s ∩ X_t` is the nonvanishing locus of the restriction of `t` to the affine scheme `X_s`,
hence affine.

On a quasi-compact scheme, the affine nonvanishing neighbourhoods need only be
constructed at closed points (`LineBundleClass.isAmple_iff_forall_isClosed_singleton`).
No common tensor
power is required. Every ample class also admits a finite affine cover by such nonvanishing
loci (`LineBundleClass.IsAmple.exists_finset_isAffineOpen_nonvanishingLocus`).

Ampleness is invariant under positive powers (`isAmple_pow_iff`), pulls back along affine morphisms
(`IsAmple.pullback_of_isAffineHom`), and descends from basic open covers
(`IsAmple.of_forall_exists_basicOpen`) and open covers of a quasi-affine base
(`IsAmple.of_forall_exists_opens_of_isQuasiAffine`).

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple a`: the line-bundle class `a` is ample.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_pos_forall_mk_eq`: the defining
  sections can be taken in any line bundle representing the relevant power.
* `IsAmple.of_pow`, `IsAmple.pow`, `isAmple_pow_iff`: `aⁿ` is ample iff `a` is ample (`n > 0`).
* `IsAmple.pullback_of_isAffineHom`, `isAmple_pullback_iff_of_isIso`: pullback along affine
  morphisms and invariance under scheme isomorphisms.
* `IsAmple.of_forall_exists_basicOpen`, `IsAmple.of_forall_exists_opens_of_isQuasiAffine`: descent
  from basic open covers and from open covers of a quasi-affine base.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_one_iff`: the structure sheaf is ample
  exactly when `X` is quasi-affine.
* `LineBundleClass.isAmple_iff_forall_isClosed_singleton`: on a quasi-compact
  scheme, the defining affine nonvanishing neighbourhoods need only cover the closed points.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_finset_isAffineOpen_nonvanishingLocus`:
  finitely many such nonvanishing loci cover a scheme carrying an ample class.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_of_isAffine`: on an affine scheme every
  line-bundle class is ample.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.quasiSeparatedSpace`: a scheme with an ample
  line-bundle class is quasi-separated.

## References

* [The Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS) (ample invertible
  sheaves), [Tag 01VG](https://stacks.math.columbia.edu/tag/01VG) (the locus of ampleness on the
  base), and [Tag 0D32](https://stacks.math.columbia.edu/tag/0D32).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 7.
-/

public section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {X : Scheme.{u}}

/-- A line-bundle class `a` on `X` is **ample** if `X` is quasi-compact and every point `x` lies in
the nonvanishing locus `X_s` of a global section `s` of a line bundle of class `aⁿ`, for some
`n > 0`, such that `X_s` is affine. For a line bundle `L`, this says that `L` is ample, with
`L^⊗n` represented by any line bundle of class `(mk L)ⁿ`. -/
structure IsAmple (a : LineBundleClass X) : Prop where
  /-- A scheme carrying an ample line bundle is quasi-compact. -/
  compactSpace : CompactSpace X
  /-- Every point lies in an affine nonvanishing locus of a global section of a positive power. -/
  exists_isAffineOpen_nonvanishingLocus (x : X) :
    ∃ n : ℕ, 0 < n ∧ ∃ (L : InvertibleSheaf X) (_ : mk L = a ^ n) (s : Γ(L.obj, ⊤)),
      x ∈ L.obj.nonvanishingLocus s ∧ IsAffineOpen (L.obj.nonvanishingLocus s)

/-- The sections defining ampleness can be found in every line bundle of the relevant class: if `a`
is ample, then each point `x` has some `n > 0` such that every line bundle `L` of class `aⁿ` has a
global section `s` with `x ∈ X_s` and `X_s` affine. -/
theorem IsAmple.exists_pos_forall_mk_eq {a : LineBundleClass X} (h : a.IsAmple) (x : X) :
    ∃ n : ℕ, 0 < n ∧ ∀ L : InvertibleSheaf X, LineBundleClass.mk L = a ^ n →
      ∃ s : Γ(L.obj, ⊤),
        x ∈ L.obj.nonvanishingLocus s ∧ IsAffineOpen (L.obj.nonvanishingLocus s) := by
  obtain ⟨n, hn, L₀, hL₀, s₀, hx, hs₀⟩ := h.exists_isAffineOpen_nonvanishingLocus x
  refine ⟨n, hn, fun L hL ↦ ?_⟩
  obtain ⟨e⟩ := mk_eq_mk_iff.mp (hL₀.trans hL.symm)
  obtain ⟨s, hs⟩ : L₀.obj.nonvanishingLocus s₀ ∈
      Set.range (L.obj.nonvanishingLocus (U := ⊤)) := by
    rw [← Scheme.Modules.range_nonvanishingLocus_eq_of_iso e ⊤]
    exact ⟨s₀, rfl⟩
  exact ⟨s, hs ▸ hx, hs ▸ hs₀⟩

/-- If a positive power `aⁿ` of a line-bundle class is ample, then so is `a`. -/
theorem IsAmple.of_pow {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) (h : (a ^ n).IsAmple) :
    a.IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨m, hm, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    exact ⟨n * m, Nat.mul_pos hn hm, L, hL.trans (pow_mul a n m).symm, s, hx, hs⟩

/-- The structure sheaf `𝒪_X` is ample exactly when `X` is quasi-affine: the nonvanishing loci of
global sections of a line bundle isomorphic to `𝒪_X` are the basic open sets of global regular
functions. -/
@[simp]
theorem isAmple_one_iff : (1 : LineBundleClass X).IsAmple ↔ X.IsQuasiAffine := by
  let O : InvertibleSheaf X := ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩
  -- The tensor unit `𝟙_ X.Modules` is by definition the structure sheaf `SheafOfModules.unit`.
  have hO : mk O = 1 := mk_eq_one_iff.mpr ⟨Iso.refl _⟩
  -- The nonvanishing loci of global sections of a line bundle of trivial class are exactly the
  -- basic open sets of global regular functions.
  have hrange (L : InvertibleSheaf X) (hL : mk L = 1) :
      Set.range (L.obj.nonvanishingLocus (U := ⊤)) =
        Set.range (X.basicOpen (U := ⊤)) := by
    obtain ⟨e⟩ := mk_eq_mk_iff.mp (hL.trans hO.symm)
    rw [Scheme.Modules.range_nonvanishingLocus_eq_of_iso e ⊤]
    exact congrArg Set.range (funext Scheme.Modules.nonvanishingLocus_unit)
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨inferInstance, fun x ↦ ?_⟩⟩
  · have := h.compactSpace
    refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x ↦ ?_
    obtain ⟨n, -, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    obtain ⟨r, hr⟩ : L.obj.nonvanishingLocus s ∈ Set.range (X.basicOpen (U := ⊤)) := by
      rw [← hrange L (hL.trans (one_pow n))]
      exact ⟨s, rfl⟩
    exact ⟨r, hr ▸ hs, hr ▸ hx⟩
  · obtain ⟨_, ⟨r, hr, rfl⟩, hx, -⟩ :=
      Opens.isBasis_iff_nbhd.mp (Scheme.IsQuasiAffine.isBasis_basicOpen X) (Opens.mem_top x)
    obtain ⟨s, hs⟩ :
        X.basicOpen r ∈ Set.range (O.obj.nonvanishingLocus (U := ⊤)) := by
      rw [hrange O hO]
      exact ⟨r, rfl⟩
    exact ⟨1, Nat.one_pos, O, hO.trans (one_pow 1).symm, s, hs ▸ hx, hs ▸ hr⟩

/-- On a quasi-affine scheme, in particular on an affine scheme, the structure sheaf is ample. -/
theorem isAmple_one [X.IsQuasiAffine] : (1 : LineBundleClass X).IsAmple :=
  isAmple_one_iff.mpr inferInstance

/-- On a quasi-affine scheme, in particular on an affine scheme, every torsion line-bundle class is
ample. -/
theorem isAmple_of_pow_eq_one [X.IsQuasiAffine] {a : LineBundleClass X} {n : ℕ} (hn : 0 < n)
    (h : a ^ n = 1) : a.IsAmple :=
  IsAmple.of_pow hn (h ▸ isAmple_one)

/-- On a quasi-compact scheme, a line-bundle class is ample exactly when every closed
point has an affine nonvanishing neighbourhood from a section of a positive tensor power. -/
theorem isAmple_iff_forall_isClosed_singleton [CompactSpace X]
    (a : LineBundleClass X) :
    a.IsAmple ↔ ∀ x : X, IsClosed {x} →
      ∃ n : ℕ, 0 < n ∧ ∃ (L : InvertibleSheaf X) (_ : mk L = a ^ n) (s : Γ(L.obj, ⊤)),
        x ∈ L.obj.nonvanishingLocus s ∧ IsAffineOpen (L.obj.nonvanishingLocus s) := by
  classical
  refine ⟨fun h x _ ↦ h.exists_isAffineOpen_nonvanishingLocus x, fun h ↦ ?_⟩
  choose n hn L hL s hx hs using fun x : {x : X // IsClosed {x}} ↦ h x x.property
  let U : X.Opens := ⨆ x : {x : X // IsClosed {x}}, (L x).obj.nonvanishingLocus (s x)
  have hU : U = ⊤ := by
    apply top_unique
    intro x _
    by_contra hxU
    obtain ⟨y, hy, hyc⟩ := U.isOpen.isClosed_compl.exists_closed_singleton ⟨x, hxU⟩
    exact hy (Opens.mem_iSup.mpr ⟨⟨y, hyc⟩, hx ⟨y, hyc⟩⟩)
  refine ⟨inferInstance, fun x ↦ ?_⟩
  have hxU : x ∈ U := by rw [hU]; exact Opens.mem_top x
  obtain ⟨y, hy⟩ := Opens.mem_iSup.mp hxU
  exact ⟨n y, hn y, L y, hL y, s y, hy, hs y⟩

/-- An ample class admits a finite affine open cover by nonvanishing loci of sections of
positive tensor powers. The exponent and representative may vary between members of the cover. -/
theorem IsAmple.exists_finset_isAffineOpen_nonvanishingLocus {a : LineBundleClass X}
    (ha : a.IsAmple) :
    ∃ S : Finset X.Opens, sSup (S : Set X.Opens) = ⊤ ∧ ∀ U ∈ S,
      IsAffineOpen U ∧ ∃ n : ℕ, 0 < n ∧
        ∃ (L : InvertibleSheaf X) (_ : LineBundleClass.mk L = a ^ n) (s : Γ(L.obj, ⊤)),
          L.obj.nonvanishingLocus s = U := by
  classical
  have : CompactSpace X := ha.compactSpace
  choose n hn L hL s hx hs using ha.exists_isAffineOpen_nonvanishingLocus
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ ((L x).obj.nonvanishingLocus (s x) : Set X))
    (fun x ↦ ((L x).obj.nonvanishingLocus (s x)).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨T.image (fun x ↦ (L x).obj.nonvanishingLocus (s x)), ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
    exact Opens.mem_sSup.mpr ⟨_, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hxy⟩
  · intro U hU
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨hs x, n x, hn x, L x, hL x, s x, rfl⟩

/-- **Every line bundle on an affine scheme is ample.** The global sections of a line bundle `L` on
an affine scheme generate every stalk, and their nonvanishing loci are affine. -/
theorem isAmple_of_isAffine [IsAffine X] (a : LineBundleClass X) : a.IsAmple where
  compactSpace := inferInstance
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨L, rfl⟩ := mk_surjective a
    obtain ⟨s, hs⟩ := Scheme.Modules.exists_mem_nonvanishingLocus_of_isAffineOpen L.obj
      (isAffineOpen_top X) (Opens.mem_top x)
    exact ⟨1, Nat.one_pos, L, (pow_one _).symm, s, hs, (isAffineOpen_top X).nonvanishingLocus s⟩

/-- **A scheme carrying an ample line bundle is quasi-separated.** It is covered by the affine
nonvanishing loci `X_s` of global sections of line bundles, and `X_s ∩ X_t` is the nonvanishing
locus of the restriction of `t` to the affine open `X_s`, which is affine. -/
theorem IsAmple.quasiSeparatedSpace {a : LineBundleClass X} (h : a.IsAmple) :
    QuasiSeparatedSpace X := by
  let I := Σ L : InvertibleSheaf X,
    {s : Γ(L.obj, ⊤) // IsAffineOpen (L.obj.nonvanishingLocus s)}
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun i : I ↦ i.1.obj.nonvanishingLocus i.2.val)
    (IsOpenCover.mk (top_unique fun x _ ↦ ?_)) (fun i ↦ i.2.property) fun i j ↦ ?_
  · obtain ⟨-, -, L, -, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    exact Opens.mem_iSup.mpr ⟨⟨L, s, hs⟩, hx⟩
  · let k : i.1.obj.nonvanishingLocus i.2.val ⟶ ⊤ := homOfLE le_top
    rw [← Opens.coe_inf, ← Scheme.Modules.nonvanishingLocus_map k]
    exact (i.2.property.nonvanishingLocus _).isCompact

/-- Every positive power of an ample line-bundle class is ample. -/
theorem IsAmple.pow {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) (h : a.IsAmple) :
    (a ^ n).IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨m, hm, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    have hsn := Scheme.Modules.nonvanishingLocus_tensorPowSection s hn
    exact ⟨m, hm, ⟨TauCeti.tensorPow L.obj n, inferInstance⟩,
      by rw [mk_tensorPowObj, hL, ← pow_mul, mul_comm, pow_mul],
      Scheme.Modules.tensorPowSection s n, hsn.symm ▸ hx, hsn.symm ▸ hs⟩

/-- For `n > 0`, the power `aⁿ` is ample if and only if `a` is ample. -/
theorem isAmple_pow_iff {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) :
    (a ^ n).IsAmple ↔ a.IsAmple := ⟨IsAmple.of_pow hn, IsAmple.pow hn⟩

/-- **Ampleness pulls back along affine morphisms.** If `f : X ⟶ Y` is an affine morphism and `a`
is an ample line-bundle class on `Y`, then `pullback f a` is ample on `X`. -/
theorem IsAmple.pullback_of_isAffineHom {Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {a : LineBundleClass Y} (h : a.IsAmple) : (pullback f a).IsAmple where
  compactSpace := have := h.compactSpace; QuasiCompact.compactSpace_of_compactSpace f
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hfx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus (f.base x)
    have hloc := (Scheme.Modules.nonvanishingLocus_pullbackSectionsLE f (M := L.obj) ⊤
      f.preimage_top.symm.le s).trans (top_inf_eq _)
    exact ⟨n, hn, (InvertibleSheaf.pullback f).obj L, by rw [← pullback_mk, hL, pullback_pow],
      f.pullbackSectionsLE L.obj ⊤ ⊤ f.preimage_top.symm.le s,
      hloc.symm ▸ hfx, hloc.symm ▸ hs.preimage f⟩

/-- Ampleness pulls back along isomorphisms of schemes. -/
theorem IsAmple.pullback_of_isIso {Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {a : LineBundleClass Y} (h : a.IsAmple) : (pullback f a).IsAmple :=
  h.pullback_of_isAffineHom f

/-- Along an isomorphism of schemes, `pullback f a` is ample if and only if `a` is ample. -/
@[simp]
theorem isAmple_pullback_iff_of_isIso {Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {a : LineBundleClass Y} : (pullback f a).IsAmple ↔ a.IsAmple :=
  ⟨fun h ↦ by simpa only [pullback_comp, IsIso.inv_hom_id, pullback_id] using
    h.pullback_of_isIso (inv f), fun h ↦ h.pullback_of_isIso f⟩

/-- **Ampleness is local on basic open covers of a quasi-compact scheme** (Stacks, Tag 01VG). Let
`X` be a quasi-compact scheme and `a` a line-bundle class on `X`. If every point `x` lies in
`X.basicOpen f` for some global regular function `f` such that `a|_{X.basicOpen f}` is ample, then
`a` is ample. -/
theorem IsAmple.of_forall_exists_basicOpen [CompactSpace X] {a : LineBundleClass X}
    (h : ∀ x : X, ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ (pullback (X.basicOpen f).ι a).IsAmple) :
    a.IsAmple := by
  have : QuasiSeparatedSpace X := by
    choose f hxf hf using h
    exact .of_isOpenCover (U := fun x ↦ X.basicOpen (f x))
      (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxf x⟩)
      (fun x ↦ isRetrocompact_basicOpen (f x))
      (fun x ↦ (isQuasiSeparated_iff_quasiSeparatedSpace _ (X.basicOpen (f x)).isOpen).mpr
        (hf x).quasiSeparatedSpace)
  refine ⟨inferInstance, fun x ↦ ?_⟩
  obtain ⟨L, rfl⟩ := mk_surjective a; obtain ⟨f, hxf, hf⟩ := h x
  let V : X.Opens := X.basicOpen f
  obtain ⟨n, hn, hsec⟩ := hf.exists_pos_forall_mk_eq ⟨x, hxf⟩
  obtain ⟨s', hxs', hs'⟩ := hsec ((InvertibleSheaf.pullback V.ι).obj (L.tensorPow n))
    (by rw [← pullback_mk, mk_tensorPow, pullback_pow])
  let M : X.Modules := (L.tensorPow n).obj
  obtain ⟨t, rfl⟩ := (Scheme.Modules.bijective_pullbackSectionsLE_ι M V ⊤ rfl).2 s'
  have hloc : ((InvertibleSheaf.pullback V.ι).obj (L.tensorPow n)).obj.nonvanishingLocus
      (V.ι.pullbackSectionsLE M V ⊤ (by simp) t) = V.ι ⁻¹ᵁ M.nonvanishingLocus t :=
    (Scheme.Modules.nonvanishingLocus_pullbackSectionsLE V.ι ⊤ _ t).trans (top_inf_eq _)
  have himg : V.ι ''ᵁ V.ι ⁻¹ᵁ M.nonvanishingLocus t = M.nonvanishingLocus t := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (M.nonvanishingLocus_le t)
  have htaff : IsAffineOpen (M.nonvanishingLocus t) :=
    himg ▸ (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion V.ι).mpr (hloc ▸ hs')
  obtain ⟨⟨t₀, ⟨_, m, rfl⟩⟩, ht₀⟩ :=
    (M.isLocalizedModule_basicOpenRestrict_of_qcqs isCompact_univ isQuasiSeparated_univ f).surj t
  dsimp only at ht₀
  have hsn : M.nonvanishingLocus (f • t₀) = M.nonvanishingLocus t := by
    let i : V ⟶ ⊤ := homOfLE (X.basicOpen_le f)
    have hres : M.presheaf.map i.op t₀ = (X.presheaf.map i.op f) ^ m • t := by
      rw [← M.basicOpenRestrict_apply f t₀, ← ht₀, Submonoid.smul_def, M.basicOpen_smul_def,
        map_pow]
    have hbf : V ≤ X.basicOpen ((X.presheaf.map i.op f) ^ m) := by
      rcases m.eq_zero_or_pos with rfl | hm
      · rw [pow_zero, X.basicOpen_one]
      · rw [X.basicOpen_pow _ hm, X.basicOpen_res]; exact le_inf le_rfl le_rfl
    rw [Scheme.Modules.nonvanishingLocus_smul, ← Scheme.Modules.nonvanishingLocus_map i, hres,
      Scheme.Modules.nonvanishingLocus_smul,
      inf_eq_right.mpr ((M.nonvanishingLocus_le t).trans hbf)]
  exact ⟨n, hn, L.tensorPow n, mk_tensorPow L n, f • t₀,
    hsn.symm ▸ (show x ∈ M.nonvanishingLocus t from by rwa [hloc] at hxs'), hsn.symm ▸ htaff⟩

/-- **Ampleness over a quasi-affine base is Zariski-local on the base** (Stacks, Tag 0D32). Let
`π : X ⟶ S` be a morphism into a quasi-affine scheme `S`, and `a` a line-bundle class on `X`. If
every point `s : S` lies in an open `U` over which `a|_{π⁻¹ U}` is ample, then `a` is ample on
`X`. -/
theorem IsAmple.of_forall_exists_opens_of_isQuasiAffine {S : Scheme.{u}} (π : X ⟶ S)
    [S.IsQuasiAffine] {a : LineBundleClass X}
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ (pullback (π ⁻¹ᵁ U).ι a).IsAmple) : a.IsAmple := by
  have hbase (s : S) : ∃ r : Γ(S, ⊤), s ∈ S.basicOpen r ∧
      (pullback (X.basicOpen (π.appTop r)).ι a).IsAmple := by
    obtain ⟨U, hsU, hU⟩ := h s
    obtain ⟨_, ⟨r, _, rfl⟩, hsr, hrU⟩ :=
      Opens.isBasis_iff_nbhd.mp (Scheme.IsQuasiAffine.isBasis_basicOpen S) hsU
    have hVU : X.basicOpen (π.appTop r) ≤ π ⁻¹ᵁ U :=
      (Scheme.preimage_basicOpen_top π r).symm.le.trans (Set.preimage_mono hrU)
    have : IsAffineHom (X.homOfLE hVU ≫ (π ⁻¹ᵁ U).ι) := by rw [X.homOfLE_ι]; infer_instance
    have : IsAffineHom (X.homOfLE hVU) := .of_comp _ (π ⁻¹ᵁ U).ι
    refine ⟨r, hsr, ?_⟩
    rw [← X.homOfLE_ι hVU, ← pullback_comp]; exact hU.pullback_of_isAffineHom (X.homOfLE hVU)
  choose r hsr hamp using hbase
  have : CompactSpace X := by
    obtain ⟨t, ht⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
      (fun s : S ↦ (S.basicOpen (r s) : Set S)) (fun s ↦ (S.basicOpen (r s)).isOpen)
      fun s _ ↦ Set.mem_iUnion.mpr ⟨s, hsr s⟩
    refine ⟨(show (Set.univ : Set X) = ⋃ s ∈ t, (X.basicOpen (π.appTop (r s)) : Set X) by
      ext x; simp only [Set.mem_univ, true_iff, Set.mem_iUnion, exists_prop]
      obtain ⟨s, hst, hsx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (π.base x)))
      exact ⟨s, hst, (Scheme.preimage_basicOpen_top π (r s)).le hsx⟩) ▸
      t.isCompact_biUnion fun s _ ↦ isCompact_iff_compactSpace.mpr (hamp s).compactSpace⟩
  exact IsAmple.of_forall_exists_basicOpen fun x ↦
    ⟨π.appTop (r (π.base x)), (Scheme.preimage_basicOpen_top π (r (π.base x))).le (hsr _),
      hamp (π.base x)⟩

end TauCeti.AlgebraicGeometry.LineBundleClass
