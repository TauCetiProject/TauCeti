/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
public import TauCeti.RingTheory.Smooth.KrullDimension
public import TauCeti.Topology.KrullDimension.Irreducible

/-!
# The relative dimension of smooth morphisms

A morphism `f : X ⟶ Spec k` to the spectrum of a field is smooth of relative dimension `n` exactly
when it is smooth and the local ring of `X` at every closed point has Krull dimension `n`. In
particular a smooth irreducible `k`-scheme of dimension `n` is smooth of relative dimension `n`,
and a smooth curve, an integral smooth `k`-scheme whose function field is an algebraic function
field of one variable over `k`, is smooth of relative dimension one. This turns the dimension
hypothesis on a smooth curve into the relative-dimension hypothesis under which its sheaf of
relative differentials `Ω_{X/k}` is invertible
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.relativeDifferentials`). Over an arbitrary base,
a morphism smooth of relative dimension `n` has fibres of dimension at most `n`; the bound
also includes empty fibres. When a smooth morphism has irreducible fibres, its fibre dimension is a
finite, locally constant function on the base; a constant fibre dimension `n` upgrades smoothness
to `SmoothOfRelativeDimension n`, and in fibre dimension zero any section is an isomorphism.

Around every point a smooth morphism has affine charts whose rings are standard smooth over `k`
of some relative dimension. By `TauCeti.height_eq_of_isStandardSmoothOfRelativeDimension` that
relative dimension is the height of every maximal ideal of the chart, which is the dimension of
the local ring of `X` at every closed point of `X` lying in the chart. Charts are nonempty open
subsets of a Jacobson scheme, so they contain closed points.

## Main declarations

* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq`:
  `f : X ⟶ Spec k` is smooth of relative dimension `n` if and only if it is smooth and the local
  rings at closed points have dimension `n`;
* `TauCeti.AlgebraicGeometry.coheight_eq_of_isClosed_of_smoothOfRelativeDimension`: a closed
  point of a `k`-scheme smooth of relative dimension `n` has codimension `n`;
* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_of_topologicalKrullDim_eq`: a smooth
  irreducible `k`-scheme of dimension `n` is smooth of relative dimension `n`;
* `TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension`: conversely,
  a nonempty scheme smooth of relative dimension `n` over `k` has dimension `n`;
* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_one_of_isFunctionField`: a smooth curve is
  smooth of relative dimension one;
* `TauCeti.AlgebraicGeometry.relativeDimensionLE_of_smoothOfRelativeDimension`: over any base,
  a morphism smooth of relative dimension `n` has fibres of dimension at most `n`;
* `TauCeti.AlgebraicGeometry.exists_smoothOfRelativeDimension_open_of_smooth`,
  `TauCeti.AlgebraicGeometry.exists_topologicalKrullDim_fiber_eq_nat`,
  `TauCeti.AlgebraicGeometry.isLocallyConstant_topologicalKrullDim_fiber`, and
  `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_of_forall_topologicalKrullDim_fiber_eq`:
  for a smooth morphism with irreducible fibres, the fibre dimension is finite and locally
  constant on the base, and constant fibre dimension `n` gives `SmoothOfRelativeDimension n`;
* `TauCeti.AlgebraicGeometry.isIso_of_comp_eq_id_of_topologicalKrullDim_fiber_eq_zero`: a section
  of a smooth morphism with zero-dimensional irreducible fibres is an isomorphism.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Section 10.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order RingHom

namespace TauCeti.AlgebraicGeometry

universe u

/-- A standard smooth ring homomorphism is standard smooth of some relative dimension. -/
private lemma exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth
    {R S : Type u} [CommRing R] [CommRing S] {g : R →+* S} (hg : g.IsStandardSmooth) :
    ∃ m : ℕ, g.IsStandardSmoothOfRelativeDimension m := by
  let := g.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hg
  exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- If the ring of an affine open `W` is standard smooth of relative dimension `m` over the ring
of global sections of `Spec k`, then the local ring of `X` at every closed point of `X` in `W` has
dimension `m`. -/
private lemma ringKrullDim_stalk_eq_of_isStandardSmoothOfRelativeDimension {W : X.Opens}
    (hW : IsAffineOpen W) {m : ℕ}
    (h : (f.appLE ⊤ W le_top).hom.IsStandardSmoothOfRelativeDimension m)
    {x : X} (hxW : x ∈ W) (hx : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = m := by
  -- View `Γ(X, W)` as a standard smooth `k`-algebra through `k ≅ Γ(Spec k, ⊤)`.
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ W le_top
  have hφ : φ.hom.IsStandardSmoothOfRelativeDimension m := by
    rw [CommRingCat.hom_comp]
    exact (isStandardSmoothOfRelativeDimension_respectsIso (n := m)).right _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv h
  let := φ.hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension m k Γ(X, W) := hφ.toAlgebra
  have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  -- `x` is the image of a closed point `y` of the chart `Spec Γ(X, W)`, a maximal ideal.
  obtain ⟨y, rfl⟩ : x ∈ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  have hy : IsClosed ({y} : Set (Spec Γ(X, W))) :=
    preimage_closedPoints_subset hW.fromSpec.isOpenEmbedding.injective
      hW.fromSpec.continuous (Set.mem_preimage.mpr hx)
  have : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
  exact_mod_cast height_eq_of_isStandardSmoothOfRelativeDimension k m y.asIdeal

/-- A morphism `f : X ⟶ Spec k` is smooth of relative dimension `n` if and only if it is smooth
and the local ring of `X` at every closed point has Krull dimension `n`. -/
theorem smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (n : ℕ) :
    SmoothOfRelativeDimension n f ↔
      Smooth f ∧ ∀ x : X, IsClosed {x} → ringKrullDim (X.presheaf.stalk x) = n := by
  refine ⟨fun _ ↦ ⟨SmoothOfRelativeDimension.smooth n f, fun x hx ↦ ?_⟩, fun ⟨_, hdim⟩ ↦ ⟨?_⟩⟩
  · obtain ⟨W, hxW, h⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top f n x
    exact ringKrullDim_stalk_eq_of_isStandardSmoothOfRelativeDimension f W.property h hxW hx
  · intro x
    obtain ⟨U, hU, V, hV, hxV, e, hst⟩ := (Smooth.iff_forall_exists_isStandardSmooth f).mp ‹_› x
    -- The only nonempty open of `Spec k` is `⊤`.
    obtain rfl : U = ⊤ := eq_top_iff.mpr fun z _ ↦ Subsingleton.elim (f x) z ▸ e hxV
    -- The chart is standard smooth of some relative dimension `m`.
    obtain ⟨m, hm⟩ := exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth hst
    -- Comparing with a closed point of `X` in the chart shows `m = n`.
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
    obtain ⟨y, hyV, hy⟩ := nonempty_inter_closedPoints ⟨x, hxV⟩ V.isOpen.isLocallyClosed
    have hmn : m = n := by
      exact_mod_cast (ringKrullDim_stalk_eq_of_isStandardSmoothOfRelativeDimension f hV hm hyV
        hy).symm.trans (hdim y hy)
    exact ⟨⊤, hU, V, hV, hxV, e, hmn ▸ hm⟩

/-- A closed point of a scheme smooth of relative dimension `n` over a field has codimension `n`.
For instance, a rational point of a smooth curve is a point of codimension one. -/
theorem coheight_eq_of_isClosed_of_smoothOfRelativeDimension {n : ℕ}
    [SmoothOfRelativeDimension n f] {x : X} (hx : IsClosed {x}) : coheight x = n := by
  exact_mod_cast (ringKrullDim_stalk_eq_coheight x).symm.trans
    (((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f n).mp inferInstance).2 x hx)

/-- A smooth irreducible scheme of dimension `n` over a field is smooth of relative
dimension `n`. -/
theorem smoothOfRelativeDimension_of_topologicalKrullDim_eq [Smooth f] [IrreducibleSpace X]
    {n : ℕ} (h : topologicalKrullDim X = n) : SmoothOfRelativeDimension n f :=
  (smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f n).mpr
    ⟨‹_›, fun _ hx ↦ (ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed f hx).trans h⟩

/-- A nonempty scheme smooth of relative dimension `n` over a field has dimension `n`. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension [Nonempty X]
    {n : ℕ} [SmoothOfRelativeDimension n f] : topologicalKrullDim X = n := by
  have := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f n).mp inferInstance).2
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDim_eq_iSup_coheight]
    refine iSup_le fun x ↦ ?_
    -- Every point specializes to a closed point, whose local ring has dimension `n`.
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
      (Set.singleton_nonempty x).closure isClosed_closure.isLocallyClosed
    have hxy : y ≤ x := specializes_iff_mem_closure.mpr hy
    calc
      (coheight x : WithBot ℕ∞) ≤ coheight y := by exact_mod_cast coheight_anti hxy
      _ = n := (ringKrullDim_stalk_eq_coheight y).symm.trans (hdim y hyc)
  · obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
      (Set.univ_nonempty : (Set.univ : Set X).Nonempty) isOpen_univ.isLocallyClosed
    rw [← hdim x hx, ringKrullDim_stalk_eq_coheight]
    exact coheight_le_topologicalKrullDim x

/-- A smooth curve over a field, an integral smooth scheme whose function field is an algebraic
function field of one variable, is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_isFunctionField [X.Over (Spec (.of k))] [IsIntegral X]
    [Smooth (X ↘ Spec (.of k))] (hF : IsFunctionField k X.functionField) :
    SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) :=
  smoothOfRelativeDimension_of_topologicalKrullDim_eq _ <| by
    exact_mod_cast (isFunctionField_functionField_iff k).mp hF

end Field

/-- A morphism smooth of relative dimension `n` has fibres of dimension at most `n`.
Empty fibres are allowed. -/
instance relativeDimensionLE_of_smoothOfRelativeDimension {X Y : Scheme.{u}}
    (n : ℕ) (f : X ⟶ Y) [SmoothOfRelativeDimension n f] : RelativeDimensionLE n f where
  topologicalKrullDim_fiber_le y := by
    let F := pullback f (Y.fromSpecResidueField y)
    let hSmooth : SmoothOfRelativeDimension n (pullback.snd f (Y.fromSpecResidueField y)) :=
      inferInstance
    rcases isEmpty_or_nonempty F with h | h
    · let hEmpty := h
      exact (topologicalKrullDim_zero_of_discreteTopology F).trans (by exact_mod_cast Nat.zero_le n)
    · exact (@topologicalKrullDim_eq_of_smoothOfRelativeDimension
        (Y.residueField y) inferInstance F (pullback.snd f (Y.fromSpecResidueField y))
        h n hSmooth).le

section IrreducibleFibers

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On an affine open `V` mapping into an affine open `U` such that the induced ring map is
standard smooth of relative dimension `m`, `V.ι ≫ f` is smooth of relative dimension `m`. -/
private lemma smoothOfRelativeDimension_open_of_isStandardSmoothOfRelativeDimension
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) {m : ℕ}
    (hm : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m) :
    SmoothOfRelativeDimension m (V.ι ≫ f) := by
  have : SmoothOfRelativeDimension m (Spec.map (f.appLE U V e)) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension m)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hm
  have hcomp : SmoothOfRelativeDimension m (Spec.map (f.appLE U V e) ≫ hU.fromSpec) :=
    inferInstanceAs (SmoothOfRelativeDimension (m + 0) _)
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV] at hcomp
  have hVι : V.ι ≫ f = hV.isoSpec.hom ≫ hV.fromSpec ≫ f := by
    rw [← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
  rw [hVι, ← Nat.zero_add m]
  exact inferInstance

/-- Around any point of the source of a smooth morphism, there is an open neighbourhood on which
the morphism is smooth of some relative dimension `m`. -/
theorem exists_smoothOfRelativeDimension_open_of_smooth [Smooth f] (x : X) :
    ∃ (V : X.Opens) (m : ℕ), x ∈ V ∧ SmoothOfRelativeDimension m (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hxV, e, hst⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨m, hm⟩ := exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth hst
  exact ⟨V, m, hxV,
    smoothOfRelativeDimension_open_of_isStandardSmoothOfRelativeDimension f hU hV e hm⟩

/-- If an open subset `V` of `X` meets an irreducible fibre `f.fiber y` and `f` is smooth of
relative dimension `m` on `V`, then `f.fiber y` has Krull dimension `m`. -/
private lemma topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_open [Smooth f]
    {V : X.Opens} {m : ℕ} [SmoothOfRelativeDimension m (V.ι ≫ f)] {y : Y}
    [IrreducibleSpace (f.fiber y)] {x : X} (hxV : x ∈ V) (hfx : f x = y) :
    topologicalKrullDim (f.fiber y) = m := by
  have hmem : (⟨x, hxV⟩ : V) ∈ (V.ι ≫ f) ⁻¹' {y} := by
    -- Unfold membership in the preimage of `{y}` along `V.ι ≫ f` on the open subscheme `V`.
    change f (V.ι ⟨x, hxV⟩) = y
    simpa using hfx
  have hne : Nonempty ((V.ι ≫ f).fiber y) := ⟨((V.ι ≫ f).fiberHomeo y).symm ⟨⟨x, hxV⟩, hmem⟩⟩
  have hsm : SmoothOfRelativeDimension m ((V.ι ≫ f).fiberToSpecResidueField y) :=
    inferInstanceAs
      (SmoothOfRelativeDimension m (pullback.snd (V.ι ≫ f) (Y.fromSpecResidueField y)))
  have hdimV : topologicalKrullDim ((V.ι ≫ f).fiber y) = m :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (k := Y.residueField y)
      ((V.ι ≫ f).fiberToSpecResidueField y)
  have hloc : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y)))
  have hemb : Topology.IsOpenEmbedding
      (((f.fiberHomeo y).symm ∘ (f ⁻¹' {y}).restrictPreimage V.ι) ∘ ((V.ι ≫ f).fiberHomeo y)) :=
    (isOpenEmbedding_fiber V.ι f y).comp ((V.ι ≫ f).fiberHomeo y).isOpenEmbedding
  have hEq := topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
    (K := Y.residueField y) (f.fiberToSpecResidueField y) hemb
  exact hEq.symm.trans hdimV

/-- Every irreducible fibre of a smooth morphism has finite natural-number Krull dimension. -/
theorem exists_topologicalKrullDim_fiber_eq_nat [Smooth f] (y : Y)
    [IrreducibleSpace (f.fiber y)] :
    ∃ m : ℕ, topologicalKrullDim (f.fiber y) = m := by
  obtain ⟨z⟩ : Nonempty (f.fiber y) := inferInstance
  let x : f ⁻¹' {y} := f.fiberHomeo y z
  obtain ⟨V, m, hxV, _⟩ := exists_smoothOfRelativeDimension_open_of_smooth f x.val
  exact ⟨m, topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_open f (m := m) hxV
    x.property⟩

/-- The fibre dimension of a smooth morphism with irreducible fibres is a locally constant
function on the base. -/
theorem isLocallyConstant_topologicalKrullDim_fiber [Smooth f]
    [∀ y : Y, IrreducibleSpace (f.fiber y)] :
    IsLocallyConstant fun y : Y ↦ topologicalKrullDim (f.fiber y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  obtain ⟨z⟩ : Nonempty (f.fiber y) := inferInstance
  let x : f ⁻¹' {y} := f.fiberHomeo y z
  obtain ⟨V, m, hxV, _⟩ := exists_smoothOfRelativeDimension_open_of_smooth f x.val
  have hyW : y ∈ f '' (V : Set X) := ⟨x.val, hxV, x.property⟩
  have hW : IsOpen (f '' (V : Set X)) := f.isOpenMap _ V.isOpen
  refine Filter.eventually_of_mem (hW.mem_nhds hyW) fun t ⟨w, hwV, hwt⟩ ↦ ?_
  rw [topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_open f (m := m) hwV hwt,
    topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_open f (m := m) hxV x.property]

/-- A smooth morphism with irreducible fibres all of Krull dimension `n` is smooth of relative
dimension `n`. -/
theorem smoothOfRelativeDimension_of_forall_topologicalKrullDim_fiber_eq [Smooth f]
    [∀ y : Y, IrreducibleSpace (f.fiber y)] {n : ℕ}
    (h : ∀ y : Y, topologicalKrullDim (f.fiber y) = n) :
    SmoothOfRelativeDimension n f where
  exists_isStandardSmoothOfRelativeDimension x := by
    obtain ⟨U, hU, V, hV, hxV, e, hst⟩ := Smooth.exists_isStandardSmooth f x
    obtain ⟨m, hm⟩ := exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth hst
    have : SmoothOfRelativeDimension m (V.ι ≫ f) :=
      smoothOfRelativeDimension_open_of_isStandardSmoothOfRelativeDimension f hU hV e hm
    have hmn : m = n := by
      exact_mod_cast (topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension_open f (m := m) hxV
        rfl).symm.trans (h (f x))
    exact ⟨U, hU, V, hV, hxV, e, hmn ▸ hm⟩

/-- A section of a smooth morphism whose fibres are irreducible of Krull dimension zero is an
isomorphism. -/
theorem isIso_of_comp_eq_id_of_topologicalKrullDim_fiber_eq_zero [Smooth f]
    [∀ y : Y, IrreducibleSpace (f.fiber y)] {e : Y ⟶ X} (he : e ≫ f = 𝟙 Y)
    (h0 : ∀ y : Y, topologicalKrullDim (f.fiber y) = 0) : IsIso e := by
  have : SmoothOfRelativeDimension 0 f :=
    smoothOfRelativeDimension_of_forall_topologicalKrullDim_fiber_eq f h0
  have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
  have : Etale (e ≫ f) := he ▸ inferInstance
  have : Etale e := Etale.of_comp e f
  have : Mono e := (SplitMono.mk f he).mono
  have : IsOpenImmersion e := IsOpenImmersion.of_flat_of_mono e
  refine (isIso_iff_isOpenImmersion_and_surjective e).2 ⟨inferInstance, ⟨fun x ↦ ?_⟩⟩
  have hsub : Subsingleton (f.fiber (f x)) :=
    (topologicalKrullDim_eq_zero_iff_subsingleton (X := f.fiber (f x))).mp (h0 (f x))
  have hpre : Subsingleton (f ⁻¹' {f x}) := (f.fiberHomeo (f x)).symm.injective.subsingleton
  refine ⟨f x, ?_⟩
  have hfe : f (e (f x)) = f x := by
    simpa [Scheme.Hom.comp_apply] using congrArg (fun g : Y ⟶ Y ↦ g (f x)) he
  exact congrArg Subtype.val (@Subsingleton.elim _ hpre ⟨e (f x), hfe⟩ ⟨x, rfl⟩)

end IrreducibleFibers

end TauCeti.AlgebraicGeometry
