/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Prestable
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension

/-!
# Pointed prestable families of curves

An `n`-pointed prestable family over a scheme `S` is a prestable family `π : X ⟶ S` together with
`n` ordered sections `s₁, …, sₙ` of `π`, the markings, whose images are pairwise disjoint and lie
in the smooth locus of `π`. No genus bound, stability condition, projectivity hypothesis, or
choice of polarization is part of the data.

Since `π` is proper, each marking is a closed immersion. Since `π` is nodal, it has pure relative
dimension one, so it is smooth of relative dimension one on its smooth locus; hence each marking
is a relative effective Cartier divisor on `X`, and so is the divisor `s₁ + ⋯ + sₙ`. This is the
divisor in the log-canonical sheaf `ω_{X/S}(s₁ + ⋯ + sₙ)` that governs pointed stability.

Pointed prestable families pull back along arbitrary morphisms `T ⟶ S`: the base change of the
markings stays pairwise disjoint and in the smooth locus. Markings can be reindexed along an
injection `Fin m ↪ Fin n`, which covers both reordering and forgetting markings. A smooth proper
relative curve with geometrically connected fibres and pairwise disjoint sections is a pointed
prestable family.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily S n`: an `n`-pointed prestable family of
  curves over `S`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.pullback`: base change along `T ⟶ S`.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.reindex`: reindexing the markings.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.ofSmooth`: a smooth proper relative curve with
  geometrically connected fibres and pairwise disjoint sections.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.isRelativeEffectiveCartier_ker_marking`: each
  marking is a relative effective Cartier divisor.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.isRelativeEffectiveCartier_prod_ker_marking`:
  the divisor `s₁ + ⋯ + sₙ` is a relative effective Cartier divisor.

## References

* [The Stacks Project, Section 109.20, Prestable curves](https://stacks.math.columbia.edu/tag/0E6S)
* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, Definition 1.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- An **`n`-pointed prestable family** of curves over `S`: a prestable family
`toBase : total ⟶ S` with `n` ordered sections, the markings, whose images are pairwise disjoint
and contained in the smooth locus of `toBase`. -/
structure PointedPrestableFamily (S : Scheme.{u}) (n : ℕ) where
  /-- The total space of the family. -/
  total : Scheme.{u}
  /-- The structure morphism of the family. -/
  toBase : total ⟶ S
  /-- The structure morphism is a prestable family. -/
  [prestableFamily : PrestableFamily toBase]
  /-- The markings of the family. -/
  marking : Fin n → (S ⟶ total)
  /-- Each marking is a section of the structure morphism. -/
  marking_comp_toBase (i : Fin n) : marking i ≫ toBase = 𝟙 S
  /-- Distinct markings have disjoint images. -/
  pairwise_disjoint_range :
    Pairwise fun i j ↦ Disjoint (Set.range (marking i)) (Set.range (marking j))
  /-- Each marking lies in the smooth locus of the structure morphism. -/
  range_marking_subset_smoothLocus (i : Fin n) : Set.range (marking i) ⊆ toBase.smoothLocus

attribute [instance] PointedPrestableFamily.prestableFamily

attribute [reassoc (attr := simp)] PointedPrestableFamily.marking_comp_toBase

namespace PointedPrestableFamily

variable {S T : Scheme.{u}} {m n : ℕ} (P : PointedPrestableFamily S n)

/-- Distinct markings take distinct values at every point of the base. -/
theorem marking_apply_ne {i j : Fin n} (hij : i ≠ j) (s : S) : P.marking i s ≠ P.marking j s :=
  fun h ↦ Set.disjoint_left.mp (P.pairwise_disjoint_range hij) ⟨s, rfl⟩ ⟨s, h.symm⟩

/-- Each marking is a closed immersion, being a section of a separated morphism. -/
instance isClosedImmersion_marking (i : Fin n) : IsClosedImmersion (P.marking i) :=
  (P.marking i).isClosedImmersion_of_comp_eq_id (P.marking_comp_toBase i)

/-- Each marking is a relative effective Cartier divisor on the total space. -/
theorem isRelativeEffectiveCartier_ker_marking (i : Fin n) :
    (P.marking i).ker.IsRelativeEffectiveCartier P.toBase :=
  Scheme.Hom.isRelativeEffectiveCartier_ker_of_comp_eq_id (P.marking i) (P.marking_comp_toBase i)
    _ (P.range_marking_subset_smoothLocus i)

/-- The divisor `s₁ + ⋯ + sₙ` of the markings is a relative effective Cartier divisor on the
total space. -/
theorem isRelativeEffectiveCartier_prod_ker_marking :
    (∏ i, (P.marking i).ker).IsRelativeEffectiveCartier P.toBase :=
  isRelativeEffectiveCartier_prod fun i _ ↦ P.isRelativeEffectiveCartier_ker_marking i

/-- The base change of a pointed prestable family along `g : T ⟶ S`. Its total space is the
pullback of the structure morphism along `g`, and its `i`th marking is the base change of the
`i`th marking: the section of `X ×_S T ⟶ T` with first component `g ≫ sᵢ`. -/
@[expose, simps total toBase]
def pullback (g : T ⟶ S) : PointedPrestableFamily T n where
  total := Limits.pullback P.toBase g
  toBase := Limits.pullback.snd P.toBase g
  marking i := Limits.pullback.lift (g ≫ P.marking i) (𝟙 T) (by simp)
  marking_comp_toBase i := Limits.pullback.lift_snd _ _ _
  pairwise_disjoint_range i j hij := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨t, rfl⟩ ⟨t', ht⟩
    -- The second projection identifies `t'` with `t`, and the first projection then makes the
    -- `i`th and `j`th markings of `P` agree at `g t`.
    obtain rfl : t' = t := by
      simpa [← Scheme.Hom.comp_apply] using congr(Limits.pullback.snd P.toBase g $ht)
    have hfst := congr(Limits.pullback.fst P.toBase g $ht)
    simp only [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst] at hfst
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hfst
    exact P.marking_apply_ne hij (g t') hfst.symm
  range_marking_subset_smoothLocus i := by
    rintro _ ⟨t, rfl⟩
    refine Scheme.Hom.preimage_smoothLocus_le_smoothLocus_pullback_snd P.toBase g ?_
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, Limits.pullback.lift_fst]
    exact P.range_marking_subset_smoothLocus i ⟨g t, rfl⟩

/-- The first projection carries the base-changed `i`th marking to `g` followed by the `i`th
marking. -/
@[simp, reassoc]
theorem pullback_marking_fst (g : T ⟶ S) (i : Fin n) :
    (P.pullback g).marking i ≫ Limits.pullback.fst P.toBase g = g ≫ P.marking i :=
  Limits.pullback.lift_fst _ _ _

/-- The base-changed markings are sections of the second projection `X ×_S T ⟶ T`. -/
@[simp, reassoc]
theorem pullback_marking_snd (g : T ⟶ S) (i : Fin n) :
    (P.pullback g).marking i ≫ Limits.pullback.snd P.toBase g = 𝟙 T :=
  (P.pullback g).marking_comp_toBase i

/-- The base-changed markings and the original markings form pullback squares with the first
projection `X ×_S T ⟶ X`. -/
theorem isPullback_pullback_marking (g : T ⟶ S) (i : Fin n) :
    IsPullback ((P.pullback g).marking i) g (Limits.pullback.fst P.toBase g) (P.marking i) :=
  -- Paste with the pullback square of `P.toBase` and `g`; both horizontal composites are
  -- identities.
  .of_right (by simpa only [pullback_marking_snd, marking_comp_toBase] using IsPullback.id_horiz g)
    (P.pullback_marking_fst g i) (IsPullback.of_hasPullback P.toBase g).flip

/-- Reindex the markings of a pointed prestable family along an injection `e : Fin m ↪ Fin n`:
the `i`th marking of the result is the `e i`th marking of `P`. Reindexing along an equivalence
reorders the markings, and reindexing along `Fin.castSuccEmb` forgets the last marking. -/
@[expose, simps]
def reindex (e : Fin m ↪ Fin n) : PointedPrestableFamily S m where
  total := P.total
  toBase := P.toBase
  marking i := P.marking (e i)
  marking_comp_toBase i := P.marking_comp_toBase (e i)
  pairwise_disjoint_range _ _ hij := P.pairwise_disjoint_range (e.injective.ne hij)
  range_marking_subset_smoothLocus i := P.range_marking_subset_smoothLocus (e i)

/-- Reindexing the markings commutes with base change. -/
theorem reindex_pullback (e : Fin m ↪ Fin n) (g : T ⟶ S) :
    (P.reindex e).pullback g = (P.pullback g).reindex e :=
  rfl

/-- A smooth proper relative curve with geometrically connected fibres, equipped with `n`
sections with pairwise disjoint images, is an `n`-pointed prestable family. -/
@[expose, simps]
def ofSmooth {X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] (s : Fin n → (S ⟶ X)) (hs : ∀ i, s i ≫ f = 𝟙 S)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j))) :
    PointedPrestableFamily S n where
  total := X
  toBase := f
  prestableFamily := .of_smooth f
  marking := s
  marking_comp_toBase := hs
  pairwise_disjoint_range := hdisj
  range_marking_subset_smoothLocus _ := by
    have := SmoothOfRelativeDimension.smooth 1 f
    simp [Scheme.Hom.smoothLocus_eq_top]

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry
