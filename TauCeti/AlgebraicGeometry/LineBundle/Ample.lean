/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.TensorProduct
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
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

Ampleness is preserved by positive tensor powers, tensoring with a globally generated line
bundle, products of ample classes, and pullback along affine morphisms. In particular it is
invariant under isomorphisms of schemes. These closure properties are the inputs to transporting
relative ampleness over affine opens of the base.

These closure properties are ported from `roed-math/TauCeti-w2-fresh`, branch
`lookahead/StableReduction/relative-ampleness`, commit `efa6fc8f3735`.

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple a`: the line-bundle class `a` is ample.

## Main results

* `LineBundleClass.isAmple_pow_iff`: a positive power is ample exactly when the class is.
* `LineBundleClass.IsAmple.mul_mk_of_isGloballyGenerated` and `LineBundleClass.IsAmple.mul`:
  tensoring with a globally generated line bundle, or another ample class, preserves ampleness.
* `LineBundleClass.IsAmple.pullback` and `LineBundleClass.isAmple_pullback_iff_of_isIso`:
  affine pullback preserves ampleness, and isomorphic schemes have corresponding ample classes.

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_pos_forall_mk_eq`: the defining
  sections can be taken in any line bundle representing the relevant power.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.of_pow`: if a positive power `aⁿ` is ample,
  then so is `a`.
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

* [The Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS), the definition of an
  ample invertible sheaf, and the section of the same chapter on affine and quasi-affine schemes,
  where quasi-affineness is characterized by ampleness of `𝒪_X`.
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

/-- **Positive powers of an ample class are ample.** If `a` is ample and `k > 0`, then `aᵏ` is
ample: for a global section `s` of a line bundle `L` of class `aⁿ`, the `k`-fold tensor product
`s ⊗ ⋯ ⊗ s` is a global section of a line bundle of class `(aᵏ)ⁿ` with the same nonvanishing locus
`X_s`. -/
theorem IsAmple.pow {a : LineBundleClass X} (h : a.IsAmple) {k : ℕ} (hk : 0 < k) :
    (a ^ k).IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    obtain ⟨L', hL'⟩ := mk_surjective ((a ^ k) ^ n)
    obtain ⟨s', hs'⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow hk
      (by rw [hL', hL, ← pow_mul, ← pow_mul, mul_comm]) s
    exact ⟨n, hn, L', hL', s', hs' ▸ hx, hs' ▸ hs⟩

/-- For `k > 0`, the power `aᵏ` of a line-bundle class is ample exactly when `a` is. -/
@[simp]
theorem isAmple_pow_iff {a : LineBundleClass X} {k : ℕ} (hk : 0 < k) :
    (a ^ k).IsAmple ↔ a.IsAmple :=
  ⟨IsAmple.of_pow hk, fun h ↦ h.pow hk⟩

/-- **An ample class times a globally generated line bundle is ample.** If `a` is ample and `K` is
globally generated, then `a · [K]` is ample: if `s` is a global section of a line bundle of class
`aⁿ` with `X_s` affine and `t` is a global section of `K^{⊗n}` with `x ∈ X_t`, then `s ⊗ t` vanishes
nowhere exactly on `X_s ∩ X_t`, the nonvanishing locus of the restriction of `t` to the affine open
`X_s`, which is affine. -/
theorem IsAmple.mul_mk_of_isGloballyGenerated {a : LineBundleClass X} (h : a.IsAmple)
    {K : InvertibleSheaf X} (hK : K.IsGloballyGenerated) : (a * LineBundleClass.mk K).IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hxs, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    obtain ⟨t, hxt⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp (hK.tensorPow n) x
    let u := Scheme.Modules.tmulRight L.obj t s
    have hu : (L ⊗ K.tensorPow n).obj.nonvanishingLocus u =
        L.obj.nonvanishingLocus s ⊓ (K.tensorPow n).obj.nonvanishingLocus t :=
      Scheme.Modules.nonvanishingLocus_tmulRight s t
    refine ⟨n, hn, L ⊗ K.tensorPow n, ?_, u, hu ▸ ⟨hxs, hxt⟩, ?_⟩
    · rw [mk_tensorObj, hL, mk_tensorPow, mul_pow]
    · -- `X_s ∩ X_t` is the nonvanishing locus of `t` restricted to `X_s`.
      rw [hu, ← Scheme.Modules.nonvanishingLocus_map
        (homOfLE (le_top : L.obj.nonvanishingLocus s ≤ ⊤)) t]
      exact hs.nonvanishingLocus _

/-- **Products of ample classes are ample.** If `a` and `b` are ample, then so is `a * b`. For a
point `x`, take global sections `s` and `t` of line bundles of classes `aⁿ` and `bᵐ` that do not
vanish at `x`, with `X_s` affine. Moved to the common power `n * m`, their tensor product vanishes
nowhere exactly on `X_s ∩ X_t`, the nonvanishing locus of `t` restricted to the affine open `X_s`,
which is affine. -/
theorem IsAmple.mul {a b : LineBundleClass X} (ha : a.IsAmple) (hb : b.IsAmple) :
    (a * b).IsAmple where
  compactSpace := ha.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hxs, hs⟩ := ha.exists_isAffineOpen_nonvanishingLocus x
    obtain ⟨m, hm, M, hM, t, hxt, -⟩ := hb.exists_isAffineOpen_nonvanishingLocus x
    -- Move both sections to the common power `n * m`.
    obtain ⟨L', hL'⟩ := mk_surjective (a ^ (n * m))
    obtain ⟨s', hs'⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow hm
      (by rw [hL', hL, ← pow_mul]) s
    obtain ⟨M', hM'⟩ := mk_surjective (b ^ (n * m))
    obtain ⟨t', ht'⟩ := InvertibleSheaf.exists_nonvanishingLocus_eq_of_mk_eq_pow hn
      (by rw [hM', hM, ← pow_mul, mul_comm m]) t
    let u := Scheme.Modules.tmulRight L'.obj t' s'
    have hu : (L' ⊗ M').obj.nonvanishingLocus u =
        L.obj.nonvanishingLocus s ⊓ M.obj.nonvanishingLocus t := by
      exact (Scheme.Modules.nonvanishingLocus_tmulRight s' t').trans (by rw [hs', ht'])
    refine ⟨n * m, Nat.mul_pos hn hm, L' ⊗ M', ?_, u, hu ▸ ⟨hxs, hxt⟩, ?_⟩
    · rw [mk_tensorObj, hL', hM', mul_pow]
    · -- `X_s ∩ X_t` is the nonvanishing locus of `t` restricted to `X_s`.
      rw [hu, ← Scheme.Modules.nonvanishingLocus_map
        (homOfLE (le_top : L.obj.nonvanishingLocus s ≤ ⊤)) t]
      exact hs.nonvanishingLocus _

/-- **Ampleness is preserved by pullback along an affine morphism.** If `a` is ample on `Y` and
`e : X ⟶ Y` is an affine morphism, for instance a closed immersion or an isomorphism, then the
pullback of `a` to `X` is ample: the nonvanishing locus of a pulled-back global section is the
preimage of the original one (`Scheme.Modules.nonvanishingLocus_pullbackSections`), which is
affine when the original one is. -/
theorem IsAmple.pullback {Y : Scheme.{u}} {a : LineBundleClass Y} (h : a.IsAmple) (e : X ⟶ Y)
    [IsAffineHom e] : (pullback e a).IsAmple where
  compactSpace := by
    have := h.compactSpace
    exact QuasiCompact.compactSpace_of_compactSpace e
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨n, hn, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus (e x)
    let s' : Γ(((InvertibleSheaf.pullback e).obj L).obj, ⊤) := e.pullbackSections L.obj ⊤ s
    have hs' : ((InvertibleSheaf.pullback e).obj L).obj.nonvanishingLocus s' =
        e ⁻¹ᵁ L.obj.nonvanishingLocus s :=
      Scheme.Modules.nonvanishingLocus_pullbackSections e s
    refine ⟨n, hn, (InvertibleSheaf.pullback e).obj L, ?_, s', hs' ▸ hx, hs' ▸ hs.preimage e⟩
    rw [← pullback_mk, hL, pullback_pow]

/-- **Ampleness is invariant under isomorphisms of schemes**: for an isomorphism `e : X ⟶ Y`, the
pullback of `a` to `X` is ample exactly when `a` is ample. -/
theorem isAmple_pullback_iff_of_isIso {Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (a : LineBundleClass Y) : (pullback e a).IsAmple ↔ a.IsAmple := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pullback e⟩
  simpa using h.pullback (inv e)

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

end TauCeti.AlgebraicGeometry.LineBundleClass
