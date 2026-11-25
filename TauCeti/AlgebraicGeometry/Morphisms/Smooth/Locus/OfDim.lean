/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.LocalDimension

/-!
# The smooth locus of dimension `d`

For a scheme `X` locally of finite presentation over `Spec R`, the sheaf of relative
differentials `Ω_{X/R}` is finite locally free on the smooth locus `X_sm` of `X ⟶ Spec R`, so its
rank is a locally constant function there. The smooth locus of dimension `d`, `X_sm^{(d)}`, is
the open subscheme of points of `X_sm` at which this rank is `d`.

On `X_sm^{(d)}` the structure morphism is smooth of relative dimension `d`, and the loci for
different `d` are disjoint and cover `X_sm`. They are compatible with passing to an open
subscheme. Over a field `k`, the rank of `Ω_{X/k}` at a smooth point `x` is the local dimension
`dim_x X`, so `X_sm^{(d)} = X_sm` when `X` is pure of dimension `d`.

## Main declarations

* `TauCeti.AlgebraicGeometry.smoothLocusOfDim`: the smooth locus of dimension `d`.
* `TauCeti.AlgebraicGeometry.smoothLocusOfDim_eq_top_iff`: `X_sm^{(d)}` is all of `X` exactly
  when `X` is smooth of relative dimension `d` over `Spec R`.
* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_smoothLocusOfDim` and
  `TauCeti.AlgebraicGeometry.rank_relativeDifferentials_smoothLocusOfDim`: `X_sm^{(d)}` is smooth
  of relative dimension `d` over `Spec R`, and its sheaf of differentials has rank `d`.
* `TauCeti.AlgebraicGeometry.iSup_smoothLocusOfDim_eq_smoothLocus` and
  `TauCeti.AlgebraicGeometry.disjoint_smoothLocusOfDim`: the loci partition `X_sm`.
* `TauCeti.AlgebraicGeometry.preimage_smoothLocusOfDim_eq`: compatibility with open immersions.
* `TauCeti.AlgebraicGeometry.rank_relativeDifferentials_smoothLocus_eq_topologicalKrullDimAt`:
  over a field, the rank at a smooth point is the local dimension.
* `TauCeti.AlgebraicGeometry.smoothLocusOfDim_eq_smoothLocus` and
  `TauCeti.AlgebraicGeometry.rank_relativeDifferentials_smoothLocus_of_isPureDimensional`: for `X`
  pure of dimension `d`, `X_sm^{(d)} = X_sm`, and `Ω_{X/k}` has rank `d` on `X_sm`.

## References

* The Stacks Project, *Commutative Algebra*, Lemma 10.140.3 (Tag 00TT).
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R]

variable (X : Scheme.{u}) [X.Over (Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]

/-- The **smooth locus of dimension `d`** of a scheme `X` locally of finite presentation over
`Spec R`: the open subscheme of points of the smooth locus of `X ⟶ Spec R` at which the finite
locally free sheaf of relative differentials of the smooth locus has rank `d`. -/
def smoothLocusOfDim (d : ℕ) : X.Opens :=
  (X ↘ Spec (.of R)).smoothLocus.ι ''ᵁ
    ((FiniteLocallyFreeSheaf.relativeDifferentials R
      (X ↘ Spec (.of R)).smoothLocus).rankLocus d).toOpens

variable {R X}

/-- A point lies in the smooth locus of dimension `d` exactly when it is a smooth point at which
the sheaf of relative differentials of the smooth locus has rank `d`. -/
theorem mem_smoothLocusOfDim_iff {d : ℕ} {x : X} :
    x ∈ smoothLocusOfDim R X d ↔ ∃ hx : x ∈ (X ↘ Spec (.of R)).smoothLocus,
      (FiniteLocallyFreeSheaf.relativeDifferentials R
        (X ↘ Spec (.of R)).smoothLocus).rank ⟨x, hx⟩ = d := by
  refine ⟨?_, fun ⟨hx, h⟩ ↦ ⟨⟨x, hx⟩, FiniteLocallyFreeSheaf.mem_rankLocus.mpr h, rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact ⟨y.property, FiniteLocallyFreeSheaf.mem_rankLocus.mp hy⟩

/-- On a scheme smooth over `Spec R`, a point lies in the smooth locus of dimension `d` exactly
when the sheaf of relative differentials has rank `d` there. -/
theorem mem_smoothLocusOfDim_iff_of_smooth [Smooth (X ↘ Spec (.of R))] {d : ℕ} {x : X} :
    x ∈ smoothLocusOfDim R X d ↔ (FiniteLocallyFreeSheaf.relativeDifferentials R X).rank x = d := by
  have hx : x ∈ (X ↘ Spec (.of R)).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rw [mem_smoothLocusOfDim_iff, exists_prop_of_true hx]
  -- The inclusion of the smooth locus sends `⟨x, hx⟩` to `x` by definition.
  exact Eq.congr_left (FiniteLocallyFreeSheaf.rank_relativeDifferentials_of_isOpenImmersion R
    (X ↘ Spec (.of R)).smoothLocus.ι ⟨x, hx⟩)

/-- The smooth locus of dimension `d` is all of `X` exactly when `X` is smooth of relative
dimension `d` over `Spec R`. -/
theorem smoothLocusOfDim_eq_top_iff {d : ℕ} :
    smoothLocusOfDim R X d = ⊤ ↔ SmoothOfRelativeDimension d (X ↘ Spec (.of R)) := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
  · have : Smooth (X ↘ Spec (.of R)) := by
      refine Scheme.Hom.smoothLocus_eq_top_iff.mp (eq_top_iff.mpr fun x _ ↦ ?_)
      refine (mem_smoothLocusOfDim_iff (R := R) (d := d).mp ?_).1
      rw [h]
      trivial
    refine smoothOfRelativeDimension_of_forall_rank_relativeDifferentials_eq R fun x ↦ ?_
    rw [← mem_smoothLocusOfDim_iff_of_smooth, h]
    trivial
  · have := SmoothOfRelativeDimension.smooth d (X ↘ Spec (.of R))
    exact eq_top_iff.mpr fun x _ ↦ mem_smoothLocusOfDim_iff_of_smooth.mpr
      (FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R d x)

/-- On a scheme smooth of relative dimension `d` over `Spec R`, the smooth locus of dimension `d`
is everything. -/
@[simp]
theorem smoothLocusOfDim_eq_top {d : ℕ} [SmoothOfRelativeDimension d (X ↘ Spec (.of R))] :
    smoothLocusOfDim R X d = ⊤ :=
  smoothLocusOfDim_eq_top_iff.mpr ‹_›

variable (R X)

/-- The smooth locus of dimension `d` lies in the smooth locus. -/
theorem smoothLocusOfDim_le_smoothLocus (d : ℕ) :
    smoothLocusOfDim R X d ≤ (X ↘ Spec (.of R)).smoothLocus :=
  fun _ hx ↦ (mem_smoothLocusOfDim_iff.mp hx).1

/-- The smooth loci of the various dimensions cover the smooth locus. -/
theorem iSup_smoothLocusOfDim_eq_smoothLocus :
    ⨆ d, smoothLocusOfDim R X d = (X ↘ Spec (.of R)).smoothLocus := by
  refine le_antisymm (iSup_le (smoothLocusOfDim_le_smoothLocus R X)) fun x hx ↦ ?_
  exact Opens.mem_iSup.mpr ⟨_, mem_smoothLocusOfDim_iff.mpr ⟨hx, rfl⟩⟩

/-- The smooth loci of different dimensions are disjoint. -/
theorem disjoint_smoothLocusOfDim {d e : ℕ} (h : d ≠ e) :
    Disjoint (smoothLocusOfDim R X d) (smoothLocusOfDim R X e) := by
  refine disjoint_iff_inf_le.mpr fun x hx ↦ ?_
  obtain ⟨hxd, hxe⟩ := Opens.mem_inf.mp hx
  obtain ⟨_, hd⟩ := mem_smoothLocusOfDim_iff.mp hxd
  obtain ⟨_, he⟩ := mem_smoothLocusOfDim_iff.mp hxe
  exact absurd (hd.symm.trans he) h

/-- The smooth locus of dimension `d` is smooth of relative dimension `d` over `Spec R`. -/
instance smoothOfRelativeDimension_smoothLocusOfDim (d : ℕ) :
    SmoothOfRelativeDimension d ((smoothLocusOfDim R X d).toScheme ↘ Spec (.of R)) := by
  set V := smoothLocusOfDim R X d
  set W := (X ↘ Spec (.of R)).smoothLocus
  have hVW : V ≤ W := smoothLocusOfDim_le_smoothLocus R X d
  have : (X.homOfLE hVW).IsOver (Spec (.of R)) := ⟨by
    rw [← Scheme.Opens.ι_comp_over, ← Scheme.Opens.ι_comp_over, X.homOfLE_ι_assoc]⟩
  have : Smooth (V.toScheme ↘ Spec (.of R)) := by
    rw [← HomIsOver.comp_over (f := X.homOfLE hVW) (S := Spec (.of R))]
    infer_instance
  refine smoothOfRelativeDimension_of_forall_rank_relativeDifferentials_eq R fun v ↦ ?_
  rw [FiniteLocallyFreeSheaf.rank_relativeDifferentials_of_isOpenImmersion R (X.homOfLE hVW)]
  obtain ⟨hv, hd⟩ := mem_smoothLocusOfDim_iff.mp v.property
  -- `homOfLE_apply'` describes the image of `v.1` as a point of `W` built from `v.1` and its
  -- membership proof; the type ascription states this for `v` itself, which is that point up to
  -- eta, so that `rw` finds it.
  rwa [show X.homOfLE hVW v = ⟨v.val, hv⟩ from X.homOfLE_apply' hVW v.val v.property]

/-- The smooth locus of dimension `d` is smooth over `Spec R`. -/
instance smooth_smoothLocusOfDim (d : ℕ) :
    Smooth ((smoothLocusOfDim R X d).toScheme ↘ Spec (.of R)) :=
  SmoothOfRelativeDimension.smooth d _

/-- The sheaf of relative differentials of the smooth locus of dimension `d` has rank `d` at every
point. -/
@[simp]
theorem rank_relativeDifferentials_smoothLocusOfDim (d : ℕ) (x : smoothLocusOfDim R X d) :
    (FiniteLocallyFreeSheaf.relativeDifferentials R (smoothLocusOfDim R X d)).rank x = d :=
  FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply (X := smoothLocusOfDim R X d) R d x

/-- For an open immersion `f : U ⟶ X` over `Spec R`, the smooth locus of dimension `d` of `U` is
the preimage of that of `X`. -/
@[simp]
theorem preimage_smoothLocusOfDim_eq {U : Scheme.{u}} [U.Over (Spec (.of R))]
    [LocallyOfFinitePresentation (U ↘ Spec (.of R))] (f : U ⟶ X) [IsOpenImmersion f]
    [f.IsOver (Spec (.of R))] (d : ℕ) :
    f ⁻¹ᵁ smoothLocusOfDim R X d = smoothLocusOfDim R U d := by
  have hsm : f ⁻¹ᵁ (X ↘ Spec (.of R)).smoothLocus = (U ↘ Spec (.of R)).smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    simp only [HomIsOver.comp_over]
  -- The restriction `g : U_sm ⟶ X_sm` of `f` is an open immersion over `Spec R`.
  let g := f.resLE (X ↘ Spec (.of R)).smoothLocus (U ↘ Spec (.of R)).smoothLocus hsm.ge
  have : IsOpenImmersion g := by
    dsimp only [g]
    delta Scheme.Hom.resLE
    infer_instance
  have : g.IsOver (Spec (.of R)) := ⟨by
    rw [← Scheme.Opens.ι_comp_over, ← Scheme.Opens.ι_comp_over, f.resLE_comp_ι_assoc,
      HomIsOver.comp_over]⟩
  ext u
  simp only [Scheme.Hom.mem_preimage, SetLike.mem_coe, mem_smoothLocusOfDim_iff]
  have hrk (p : (U ↘ Spec (.of R)).smoothLocus.toScheme)
      (hp : f p.val ∈ (X ↘ Spec (.of R)).smoothLocus) :
      (FiniteLocallyFreeSheaf.relativeDifferentials R (U ↘ Spec (.of R)).smoothLocus).rank p =
        (FiniteLocallyFreeSheaf.relativeDifferentials R
          (X ↘ Spec (.of R)).smoothLocus).rank ⟨f p.val, hp⟩ := by
    rw [FiniteLocallyFreeSheaf.rank_relativeDifferentials_of_isOpenImmersion R g]
    exact congrArg _ (Subtype.ext (f.coe_resLE_apply hsm.ge p))
  refine ⟨fun ⟨hx, h⟩ ↦ ?_, fun ⟨hu, h⟩ ↦ ?_⟩
  · have hu : u ∈ (U ↘ Spec (.of R)).smoothLocus := hsm ▸ hx
    exact ⟨hu, (hrk ⟨u, hu⟩ hx).trans h⟩
  · have hx : f u ∈ (X ↘ Spec (.of R)).smoothLocus := (hsm.symm ▸ hu :)
    exact ⟨hx, (hrk ⟨u, hu⟩ hx).symm.trans h⟩

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- Over a field `k`, the rank of `Ω_{X/k}` at a smooth point `x` is the local dimension
`dim_x X`. -/
theorem rank_relativeDifferentials_smoothLocus_eq_topologicalKrullDimAt
    (x : (X ↘ Spec (.of k)).smoothLocus.toScheme) :
    ((FiniteLocallyFreeSheaf.relativeDifferentials k
      (X ↘ Spec (.of k)).smoothLocus).rank x : WithBot ℕ∞) =
      topologicalKrullDimAt X ((X ↘ Spec (.of k)).smoothLocus.ι x) := by
  obtain ⟨n, hn⟩ : ∃ n,
      (FiniteLocallyFreeSheaf.relativeDifferentials k (X ↘ Spec (.of k)).smoothLocus).rank x = n :=
    ⟨_, rfl⟩
  set V := smoothLocusOfDim k X n
  have hx : x.val ∈ V := mem_smoothLocusOfDim_iff.mpr ⟨x.property, hn⟩
  -- `V` is smooth of relative dimension `n` over `k`, hence pure of dimension `n`.
  have hV := ((pureRelativeDimension_iff_of_field (d := n) (V.toScheme ↘ Spec (.of k))).mp
    inferInstance).2
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X ↘ Spec (.of k)))
  rw [hn]
  exact (topologicalKrullDimAt_eq_of_isPureDimensional k hV ⟨_, hx⟩).symm.trans
    (V.ι.isOpenEmbedding.topologicalKrullDimAt_eq _)

/-- Over a field, for `X` pure of dimension `d`, the sheaf of differentials of the smooth locus
has rank `d` at every point. -/
theorem rank_relativeDifferentials_smoothLocus_of_isPureDimensional {d : ℕ}
    (h : IsPureDimensional d X) (x : (X ↘ Spec (.of k)).smoothLocus.toScheme) :
    (FiniteLocallyFreeSheaf.relativeDifferentials k (X ↘ Spec (.of k)).smoothLocus).rank x = d := by
  have := rank_relativeDifferentials_smoothLocus_eq_topologicalKrullDimAt x
  rw [topologicalKrullDimAt_eq_of_isPureDimensional k h] at this
  exact_mod_cast this

/-- Over a field, for `X` pure of dimension `d`, the smooth locus of dimension `d` is the whole
smooth locus. -/
theorem smoothLocusOfDim_eq_smoothLocus {d : ℕ} (h : IsPureDimensional d X) :
    smoothLocusOfDim k X d = (X ↘ Spec (.of k)).smoothLocus :=
  le_antisymm (smoothLocusOfDim_le_smoothLocus k X d) fun x hx ↦
    mem_smoothLocusOfDim_iff.mpr
      ⟨hx, rank_relativeDifferentials_smoothLocus_of_isPureDimensional h ⟨x, hx⟩⟩

end Field

end

end TauCeti.AlgebraicGeometry
