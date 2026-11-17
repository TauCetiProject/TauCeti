/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.LineBundle.TwistedSections

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
(`LineBundleClass.isAmple_of_pow_eq_one`).

Ampleness implies quasi-separatedness (`LineBundleClass.IsAmple.quasiSeparatedSpace`), is invariant
under positive powers (`LineBundleClass.isAmple_pow_iff`), pulls back along affine morphisms
(`LineBundleClass.IsAmple.pullback_of_isAffineHom`), and is local on basic open covers of
quasi-compact schemes (`LineBundleClass.IsAmple.of_forall_exists_basicOpen`); in particular, over a
quasi-affine base, ampleness may be checked Zariski-locally on the base without hypotheses on the
structure morphism (`LineBundleClass.IsAmple.of_forall_exists_opens_of_isQuasiAffine`).

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple a`: the line-bundle class `a` is ample.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_pos_forall_mk_eq`: the defining
  sections can be taken in any line bundle representing the relevant power.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.quasiSeparatedSpace`: a scheme carrying an
  ample line bundle is quasi-separated.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.of_pow`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.pow`, and
  `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_pow_iff`: for `n > 0`, `aⁿ` is ample if and
  only if `a` is ample.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.pullback_of_isAffineHom` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_pullback_iff_of_isIso`: ampleness pulls back
  along affine morphisms and is invariant under scheme isomorphisms.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.of_forall_exists_basicOpen` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.of_forall_exists_opens_of_isQuasiAffine`:
  descent of ampleness from basic open covers and from open covers of a quasi-affine base.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_one_iff`: the structure sheaf is ample
  exactly when `X` is quasi-affine.

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

/-- A scheme carrying an ample line bundle is quasi-separated: it is covered by affine nonvanishing
loci of global sections, each of which is retrocompact and quasi-separated. -/
theorem IsAmple.quasiSeparatedSpace {a : LineBundleClass X} (h : a.IsAmple) :
    QuasiSeparatedSpace X := by
  choose n _ L _ s hxs hs using h.exists_isAffineOpen_nonvanishingLocus
  exact .of_isOpenCover (U := fun x ↦ (L x).obj.nonvanishingLocus (s x))
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxs x⟩)
    (fun x ↦ (L x).obj.isRetrocompact_nonvanishingLocus (s x))
    (fun x ↦ (hs x).isQuasiSeparated)

/-- If a positive power `aⁿ` of a line-bundle class is ample, then so is `a`. -/
theorem IsAmple.of_pow {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) (h : (a ^ n).IsAmple) :
    a.IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨m, hm, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    exact ⟨n * m, Nat.mul_pos hn hm, L, hL.trans (pow_mul a n m).symm, s, hx, hs⟩

/-- Every positive power of an ample line-bundle class is ample. -/
theorem IsAmple.pow {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) (h : a.IsAmple) :
    (a ^ n).IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨m, hm, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    have hpow : LineBundleClass.mk ⟨TauCeti.tensorPow L.obj n, inferInstance⟩ = (a ^ n) ^ m := by
      rw [mk_tensorPowObj, hL, ← pow_mul, mul_comm, pow_mul]
    have hsn := Scheme.Modules.nonvanishingLocus_tensorPowSection s hn
    exact ⟨m, hm, ⟨TauCeti.tensorPow L.obj n, inferInstance⟩, hpow,
      Scheme.Modules.tensorPowSection s n, hsn.symm ▸ hx, hsn.symm ▸ hs⟩

/-- For `n > 0`, the power `aⁿ` is ample if and only if `a` is ample. -/
theorem isAmple_pow_iff {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) :
    (a ^ n).IsAmple ↔ a.IsAmple :=
  ⟨IsAmple.of_pow hn, IsAmple.pow hn⟩

/-- **Ampleness pulls back along affine morphisms.** If `f : X ⟶ Y` is an affine morphism and `a`
is an ample line-bundle class on `Y`, then `pullback f a` is ample on `X`. -/
theorem IsAmple.pullback_of_isAffineHom {Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {a : LineBundleClass Y} (h : a.IsAmple) : (pullback f a).IsAmple where
  compactSpace := by
    have := h.compactSpace
    exact QuasiCompact.compactSpace_of_compactSpace f
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hfx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus (f.base x)
    let fs : Γ(((InvertibleSheaf.pullback f).obj L).obj, ⊤) :=
      f.pullbackSectionsLE L.obj ⊤ ⊤ f.preimage_top.symm.le s
    have hloc : ((InvertibleSheaf.pullback f).obj L).obj.nonvanishingLocus fs =
        f ⁻¹ᵁ L.obj.nonvanishingLocus s :=
      (Scheme.Modules.nonvanishingLocus_pullbackSectionsLE f ⊤ f.preimage_top.symm.le s).trans
        (top_inf_eq _)
    refine ⟨n, hn, (InvertibleSheaf.pullback f).obj L, ?_, fs, hloc.symm ▸ hfx,
      hloc.symm ▸ hs.preimage f⟩
    rw [← pullback_mk, hL, pullback_pow]

/-- Ampleness pulls back along isomorphisms of schemes. -/
theorem IsAmple.pullback_of_isIso {Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {a : LineBundleClass Y} (h : a.IsAmple) : (pullback f a).IsAmple :=
  h.pullback_of_isAffineHom f

/-- Along an isomorphism of schemes, `pullback f a` is ample if and only if `a` is ample. -/
@[simp]
theorem isAmple_pullback_iff_of_isIso {Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {a : LineBundleClass Y} : (pullback f a).IsAmple ↔ a.IsAmple := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pullback_of_isIso f⟩
  have h' := h.pullback_of_isIso (inv f)
  rwa [pullback_comp, IsIso.inv_hom_id, pullback_id] at h'

/-- **Ampleness is local on basic open covers of a quasi-compact scheme** (Stacks, Tag 01VG). Let
`X` be a quasi-compact scheme and `a` a line-bundle class on `X`. If every point `x` lies in
`X.basicOpen f` for some global regular function `f` such that `a|_{X.basicOpen f}` is ample, then
`a` is ample. -/
theorem IsAmple.of_forall_exists_basicOpen [CompactSpace X]
    {a : LineBundleClass X}
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
  obtain ⟨L, rfl⟩ := mk_surjective a
  obtain ⟨f, hxf, hf⟩ := h x
  let V : X.Opens := X.basicOpen f
  obtain ⟨n, hn, hsec⟩ := hf.exists_pos_forall_mk_eq ⟨x, hxf⟩
  obtain ⟨s', hxs', hs'⟩ := hsec ((InvertibleSheaf.pullback V.ι).obj (L.tensorPow n))
    (by rw [← pullback_mk, mk_tensorPow, pullback_pow])
  let M : X.Modules := (L.tensorPow n).obj
  -- Lift `s'` from `V` to a section `t ∈ Γ(M, V)` with the same affine nonvanishing locus.
  obtain ⟨t, rfl⟩ := (Scheme.Modules.bijective_pullbackSectionsLE_ι M V ⊤ rfl).2 s'
  have hloc : ((InvertibleSheaf.pullback V.ι).obj (L.tensorPow n)).obj.nonvanishingLocus
      (V.ι.pullbackSectionsLE M V ⊤ (by simp) t) = V.ι ⁻¹ᵁ M.nonvanishingLocus t :=
    (Scheme.Modules.nonvanishingLocus_pullbackSectionsLE V.ι ⊤ _ t).trans (top_inf_eq _)
  have himg : V.ι ''ᵁ V.ι ⁻¹ᵁ M.nonvanishingLocus t = M.nonvanishingLocus t := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (M.nonvanishingLocus_le t)
  have hxt : x ∈ M.nonvanishingLocus t := by
    rw [hloc] at hxs'
    exact hxs'
  have htaff : IsAffineOpen (M.nonvanishingLocus t) := by
    rw [← himg]
    exact (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion V.ι).mpr (hloc ▸ hs')
  -- By the qcqs lemma for `M`, some `f^m • t` extends to a global section `t₀` of `M`, and then
  -- `f • t₀` has nonvanishing locus `V ∩ X_{t₀} = X_t`.
  have hlocMod := M.isLocalizedModule_basicOpenRestrict_of_qcqs
    isCompact_univ isQuasiSeparated_univ f
  obtain ⟨⟨t₀, ⟨_, m, rfl⟩⟩, ht₀⟩ := hlocMod.surj t
  dsimp only at ht₀
  have hsn : M.nonvanishingLocus (f • t₀) = M.nonvanishingLocus t := by
    let i : V ⟶ ⊤ := homOfLE (X.basicOpen_le f)
    have hres : M.presheaf.map i.op t₀ = (X.presheaf.map i.op f) ^ m • t := by
      rw [← M.basicOpenRestrict_apply f t₀, ← ht₀, Submonoid.smul_def,
        M.basicOpen_smul_def, map_pow]
    have hbf : V ≤ X.basicOpen ((X.presheaf.map i.op f) ^ m) := by
      rcases m.eq_zero_or_pos with rfl | hm
      · rw [pow_zero, X.basicOpen_one]
      · rw [X.basicOpen_pow _ hm, X.basicOpen_res]
        exact le_inf le_rfl le_rfl
    rw [Scheme.Modules.nonvanishingLocus_smul, ← Scheme.Modules.nonvanishingLocus_map i, hres,
      Scheme.Modules.nonvanishingLocus_smul,
      inf_eq_right.mpr ((M.nonvanishingLocus_le t).trans hbf)]
  exact ⟨n, hn, L.tensorPow n, mk_tensorPow L n, f • t₀, hsn.symm ▸ hxt, hsn.symm ▸ htaff⟩

/-- **Ampleness over a quasi-affine base is Zariski-local on the base** (Stacks, Tag 0D32). Let
`π : X ⟶ S` be a morphism into a quasi-affine scheme `S`, and `a` a line-bundle class on `X`. If
every point `s : S` lies in an open `U` over which `a|_{π⁻¹ U}` is ample, then `a` is ample on
`X`. -/
theorem IsAmple.of_forall_exists_opens_of_isQuasiAffine {S : Scheme.{u}} (π : X ⟶ S)
    [S.IsQuasiAffine] {a : LineBundleClass X}
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ (pullback (π ⁻¹ᵁ U).ι a).IsAmple) :
    a.IsAmple := by
  have hbase (s : S) : ∃ r : Γ(S, ⊤), s ∈ S.basicOpen r ∧
      (pullback (X.basicOpen (π.appTop r)).ι a).IsAmple := by
    obtain ⟨U, hsU, hU⟩ := h s
    obtain ⟨_, ⟨r, _, rfl⟩, hsr, hrU⟩ :=
      Opens.isBasis_iff_nbhd.mp (Scheme.IsQuasiAffine.isBasis_basicOpen S) hsU
    have hf : X.basicOpen (π.appTop r) = π ⁻¹ᵁ S.basicOpen r :=
      (Scheme.preimage_basicOpen_top π r).symm
    have hVU : X.basicOpen (π.appTop r) ≤ π ⁻¹ᵁ U := hf.le.trans (Set.preimage_mono hrU)
    have : IsAffineHom (X.homOfLE hVU ≫ (π ⁻¹ᵁ U).ι) := by
      rw [X.homOfLE_ι]
      infer_instance
    have : IsAffineHom (X.homOfLE hVU) := .of_comp _ (π ⁻¹ᵁ U).ι
    refine ⟨r, hsr, ?_⟩
    rw [← X.homOfLE_ι hVU, ← pullback_comp]
    exact hU.pullback_of_isAffineHom (X.homOfLE hVU)
  choose r hsr hamp using hbase
  have : CompactSpace X := by
    obtain ⟨t, ht⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
      (fun s : S ↦ (S.basicOpen (r s) : Set S)) (fun s ↦ (S.basicOpen (r s)).isOpen)
      fun s _ ↦ Set.mem_iUnion.mpr ⟨s, hsr s⟩
    refine ⟨?_⟩
    have hcov : (Set.univ : Set X) = ⋃ s ∈ t, (X.basicOpen (π.appTop (r s)) : Set X) := by
      ext x
      simp only [Set.mem_univ, true_iff, Set.mem_iUnion, exists_prop]
      obtain ⟨s, hst, hsx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (π.base x)))
      exact ⟨s, hst, (Scheme.preimage_basicOpen_top π (r s)).le hsx⟩
    rw [hcov]
    exact t.isCompact_biUnion fun s _ ↦
      isCompact_iff_compactSpace.mpr (hamp s).compactSpace
  exact IsAmple.of_forall_exists_basicOpen fun x ↦
    ⟨π.appTop (r (π.base x)), (Scheme.preimage_basicOpen_top π (r (π.base x))).le (hsr _),
      hamp (π.base x)⟩

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

end TauCeti.AlgebraicGeometry.LineBundleClass
