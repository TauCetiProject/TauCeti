/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Carrier
public import TauCeti.RingTheory.AdicRing.CompletedAway

/-!
# Completed localisations at an open prime

Let `A` be an adic ring of finite ideal type with ideal of definition `I`, and let `p` be an open
prime of `A`, a point of the formal spectrum `Spf A`. The basic open sets `D(f)` of `Spf A`
containing `p` are indexed by the elements `f ∉ p`, and over `D(f)` the structure sheaf has
sections the completed localisation `A_{f}`. The filtered colimit `colim_{f ∉ p} A_{f}` along the
restriction maps `A_{f} → A_{g}` for `D(g) ⊆ D(f)` is the algebraic model of the stalk of `Spf A`
at `p` (EGA I, Ch. 0, 7.6.17; Ch. I, 10.1.6).

This file shows that this colimit is a local ring with residue field `Frac(A ⧸ p)`. The residue map
sends the class of `x ∈ A_{f}` to its value in `Frac(A ⧸ p)`, the unique continuous extension of
`A → A ⧸ p → Frac(A ⧸ p)` (for the discrete topology on the field). An element of `A_{f}` with
nonzero value at `p` becomes a unit in `A_{g}` for some `f ∉ p` with `D(g) ⊆ D(f)`: modulo
`I A_{f}` it is a fraction `a / fⁿ` with `a ∉ p`, which is a unit in `A_{fa}`, and `I A_{fa}` lies
in the Jacobson radical of the `I`-adically complete ring `A_{fa}`. Hence the residue map is a
local homomorphism onto a field.

## Main definitions

* `TauCeti.FormalScheme.Spf.BasicNeighbourhood p`: the elements `f ∉ p`, preordered by reverse
  inclusion of the basic open sets `D(f)`.
* `TauCeti.FormalScheme.Spf.completedNeighbourhoodDiagram p`: the diagram `f ↦ A_{f}` of
  completed localisations with the restriction maps.
* `TauCeti.FormalScheme.Spf.stalkResidueIso p`: the residue field of the colimit is
  `Frac(A ⧸ p)`.

## Main results

* `TauCeti.FormalScheme.Spf.completedNeighbourhoodColimit_isLocalRing`: the colimit
  `colim_{f ∉ p} A_{f}` is a local ring.
* `TauCeti.FormalScheme.Spf.stalkResidueIso_coeff`: the residue isomorphism sends the class of
  `a ∈ A` to the image of `a` in `Frac(A ⧸ p)`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.17, and
  Ch. I, 10.1.6.
-/

public section

open CategoryTheory Limits Topology

namespace TauCeti.FormalScheme.Spf

open AdicRing

universe u

section BasicNeighbourhood

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The basic open neighbourhoods of a point `p` of `Spf A`: the elements `f ∉ p`, indexing the
basic open sets `D(f)` containing `p`. They are preordered by reverse inclusion, so that `f ≤ g`
when `D(g) ⊆ D(f)`; this preorder is directed, with `fg` above `f` and `g`. -/
structure BasicNeighbourhood (p : carrier A) : Type u where
  /-- The element `f` defining the basic open set `D(f)`. -/
  elem : A
  notMem : elem ∉ (p : PrimeSpectrum A).asIdeal

namespace BasicNeighbourhood

variable {p : carrier A}

instance : Preorder (BasicNeighbourhood p) :=
  Preorder.lift fun f : BasicNeighbourhood p ↦ OrderDual.toDual (basicOpen f.elem)

theorem le_def {f g : BasicNeighbourhood p} : f ≤ g ↔ basicOpen g.elem ≤ basicOpen f.elem :=
  Iff.rfl

/-- The product `fg` of two basic neighbourhoods `f` and `g` of `p`, with `D(fg) = D(f) ∩ D(g)`. -/
instance : Mul (BasicNeighbourhood p) :=
  ⟨fun f g ↦ ⟨f.elem * g.elem, (p : PrimeSpectrum A).isPrime.mul_notMem f.notMem g.notMem⟩⟩

@[simp]
theorem elem_mul (f g : BasicNeighbourhood p) : (f * g).elem = f.elem * g.elem :=
  (rfl)

theorem le_mul_right (f g : BasicNeighbourhood p) : f ≤ f * g := by
  simp [le_def, basicOpen_mul]

theorem le_mul_left (f g : BasicNeighbourhood p) : g ≤ f * g := by
  simp [le_def, basicOpen_mul]

instance : IsDirectedOrder (BasicNeighbourhood p) :=
  ⟨fun f g ↦ ⟨f * g, le_mul_right f g, le_mul_left f g⟩⟩

instance : Nonempty (BasicNeighbourhood p) :=
  ⟨⟨1, (p : PrimeSpectrum A).asIdeal.one_notMem⟩⟩

/-- For an ideal of definition `I`, `f ≤ g` holds exactly when `g` lies in the radical of
`f A + I`, the condition for the restriction map `A_{f} → A_{g}`. -/
theorem le_iff_mem_radical {I : Ideal A} (hI : IsAdic I) {f g : BasicNeighbourhood p} :
    f ≤ g ↔ g.elem ∈ (Ideal.span {f.elem} ⊔ I).radical :=
  basicOpen_le_basicOpen_iff hI

end BasicNeighbourhood

end BasicNeighbourhood

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-- The diagram of completed localisations `A_{f}` over the basic open neighbourhoods `D(f)` of a
point `p` of `Spf A`, with the restriction maps `A_{f} → A_{g}` for `D(g) ⊆ D(f)`. Its colimit is
the algebraic model of the stalk of `Spf A` at `p`.

The body is exposed so that the objects of the diagram are definitionally the rings `A_{f}`, which
lets elements of `A_{f}` be fed to the colimit inclusions. -/
@[expose] noncomputable def completedNeighbourhoodDiagram :
    BasicNeighbourhood p ⥤ CommRingCat.{u} where
  obj f := CommRingCat.of (CompletedAway A f.elem)
  map {f g} h := CommRingCat.ofHom <| CompletedAway.restrict
    ((BasicNeighbourhood.le_iff_mem_radical (IsAdicRing.ideal_spec A).2.1).mp h.le) |>.toRingHom
  map_id f := by
    ext x
    simp
  map_comp h₁ h₂ := by
    ext x
    exact (CompletedAway.restrict_restrict _ _ _ x).symm

@[simp]
theorem completedNeighbourhoodDiagram_obj (f : BasicNeighbourhood p) :
    (completedNeighbourhoodDiagram p).obj f = CommRingCat.of (CompletedAway A f.elem) :=
  (rfl)

@[simp]
theorem completedNeighbourhoodDiagram_map_apply {f g : BasicNeighbourhood p} (h : f ⟶ g)
    (x : CompletedAway A f.elem) :
    (completedNeighbourhoodDiagram p).map h x = CompletedAway.restrict
      ((BasicNeighbourhood.le_iff_mem_radical (IsAdicRing.ideal_spec A).2.1).mp h.le) x :=
  (rfl)

/-! ### The value at `p` -/

section Residue

/-- The map `A → A ⧸ p → Frac(A ⧸ p)`. -/
private noncomputable def toResidue :
    A →+* FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  (algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal) _).comp (Ideal.Quotient.mk _)

omit [IsTopologicalRing A] [IsAdicRing A] in
private theorem toResidue_apply (a : A) :
    toResidue p a = algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal) _ (Ideal.Quotient.mk _ a) :=
  (rfl)

omit [IsTopologicalRing A] [IsAdicRing A] in
private theorem toResidue_eq_zero_iff {a : A} :
    toResidue p a = 0 ↔ a ∈ (p : PrimeSpectrum A).asIdeal := by
  rw [toResidue_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The discrete uniform structure on `Frac(A ⧸ p)`, used to extend maps out of `A` to the
completed localisations. -/
private noncomputable abbrev residueUniformSpace :
    UniformSpace (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) :=
  ⊥

attribute [local instance] residueUniformSpace

omit [IsAdicRing A] in
/-- Since `p` is open, the map `A → Frac(A ⧸ p)` is continuous for the discrete topology. -/
private theorem continuous_toResidue : Continuous (toResidue p) := by
  refine continuous_of_continuousAt_zero (toResidue p).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, nhds_discrete (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)),
    Filter.tendsto_pure]
  filter_upwards [(mem_carrier.mp p.2).mem_nhds (zero_mem _)] with a ha
  exact (toResidue_eq_zero_iff p).mpr ha

omit [IsTopologicalRing A] [IsAdicRing A] in
private theorem isUnit_toResidue (f : BasicNeighbourhood p) : IsUnit (toResidue p f.elem) :=
  Ne.isUnit fun h ↦ f.notMem ((toResidue_eq_zero_iff p).mp h)

/-- The value at `p` of an element of `A_{f}`, for `f ∉ p`: the continuous extension of
`A → Frac(A ⧸ p)`, for the discrete topology on `Frac(A ⧸ p)`. -/
private noncomputable def residueAway (f : BasicNeighbourhood p) :
    CompletedAway A f.elem →+* FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  CompletedAway.lift (toResidue p) (continuous_toResidue p) (isUnit_toResidue p f)

private theorem residueAway_algebraMap (f : BasicNeighbourhood p) (a : A) :
    residueAway p f (algebraMap A (CompletedAway A f.elem) a) = toResidue p a :=
  CompletedAway.lift_algebraMap _ _ _ a

private theorem residueAway_restrict {f g : BasicNeighbourhood p}
    (h : g.elem ∈ (Ideal.span {f.elem} ⊔ IsAdicRing.ideal A).radical) (x : CompletedAway A f.elem) :
    residueAway p g (CompletedAway.restrict h x) = residueAway p f x := by
  -- both sides are continuous ring homomorphisms out of `A_{f}` agreeing on `A`
  refine congr($(CompletedAway.ringHom_ext A f.elem
    (g₁ := (residueAway p g).comp (CompletedAway.restrict h).toRingHom)
    ((CompletedAway.continuous_lift _ _ _).comp (CompletedAway.continuous_restrict h))
    (CompletedAway.continuous_lift _ _ _) (RingHom.ext fun a ↦ ?_)) x)
  simp [residueAway_algebraMap]

/-- The values at `p` vanish on the ideal of definition. -/
private theorem residueAway_eq_zero_of_mem (f : BasicNeighbourhood p) {x : CompletedAway A f.elem}
    (hx : x ∈ (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f.elem))) :
    residueAway p f x = 0 := by
  refine (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_ : _ ≤ RingHom.ker (residueAway p f)) hx
  rw [Ideal.mem_comap, RingHom.mem_ker, residueAway_algebraMap, toResidue_eq_zero_iff]
  exact (mem_carrier_iff_le (IsAdicRing.ideal_spec A).2.1).mp p.2 ha

/-- An element of `A_{f}` with nonzero value at `p` becomes a unit in `A_{g}` for some basic
neighbourhood `D(g) ⊆ D(f)` of `p`. -/
private theorem exists_isUnit_restrict {f : BasicNeighbourhood p} {x : CompletedAway A f.elem}
    (hx : residueAway p f x ≠ 0) :
    ∃ (g : BasicNeighbourhood p) (h : f ≤ g), IsUnit (CompletedAway.restrict
      ((BasicNeighbourhood.le_iff_mem_radical (IsAdicRing.ideal_spec A).2.1).mp h) x) := by
  -- modulo `I A_{f}`, `x` is a fraction `a / fⁿ`
  obtain ⟨y, hy⟩ := CompletedAway.exists_sub_mem_map A f.elem x
  obtain ⟨n, a, hya⟩ := IsLocalization.Away.surj f.elem y
  have hya' : algebraMap _ (CompletedAway A f.elem) y * algebraMap A _ f.elem ^ n =
      algebraMap A (CompletedAway A f.elem) a := by
    rw [IsScalarTower.algebraMap_apply A (Localization.Away f.elem), ← map_pow, ← map_mul, hya,
      ← IsScalarTower.algebraMap_apply]
  -- the numerator `a` does not lie in `p`
  have ha : a ∉ (p : PrimeSpectrum A).asIdeal := by
    rw [← toResidue_eq_zero_iff, ← residueAway_algebraMap p f, ← hya', map_mul, map_pow,
      residueAway_algebraMap]
    refine mul_ne_zero (fun h ↦ hx ?_) (pow_ne_zero _ (isUnit_toResidue p f).ne_zero)
    rw [← sub_add_cancel x (algebraMap _ _ y), map_add, residueAway_eq_zero_of_mem p f hy, h,
      add_zero]
  -- so `x` becomes a unit in `A_{fa}`
  let g : BasicNeighbourhood p := f * ⟨a, ha⟩
  refine ⟨g, BasicNeighbourhood.le_mul_right _ _, ?_⟩
  set r := CompletedAway.restrict
    ((BasicNeighbourhood.le_iff_mem_radical (IsAdicRing.ideal_spec A).2.1).mp
      (BasicNeighbourhood.le_mul_right f ⟨a, ha⟩))
  have hunit : IsUnit (r (algebraMap _ _ y)) := by
    refine isUnit_of_mul_isUnit_left (y := algebraMap A (CompletedAway A g.elem) f.elem ^ n) ?_
    rw [← AlgHom.commutes r, ← map_pow, ← map_mul, hya', AlgHom.commutes]
    exact CompletedAway.isUnit_algebraMap_of_mem_radical
      (Ideal.le_radical (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_left a f.elem))))
  -- the error term lies in `I A_{fa}`, hence in the Jacobson radical
  have hmem : r (x - algebraMap _ _ y) ∈
      (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A g.elem)) := by
    rw [← r.comp_algebraMap, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hy
  have := (CompletedAway.isAdic A g.elem).isAdicComplete
  have hjac := IsAdicComplete.le_jacobson_bot _ hmem
  obtain ⟨v, hv⟩ := hunit
  have := Ideal.mem_jacobson_bot.mp hjac ↑v⁻¹
  rw [← sub_add_cancel x (algebraMap _ _ y), map_add, ← hv]
  convert v.isUnit.mul this using 1
  rw [mul_add, mul_one, mul_comm, mul_assoc, v.inv_mul, mul_one, add_comm]

/-- The cocone of values at `p` on the diagram of completed localisations. -/
private noncomputable def residueCocone : Cocone (completedNeighbourhoodDiagram p) where
  pt := CommRingCat.of (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal))
  ι.app f := CommRingCat.ofHom (residueAway p f)
  ι.naturality {f g} h := by
    ext x
    exact residueAway_restrict p _ x

/-- The residue map of the colimit: the value at `p`. -/
private noncomputable def residue :
    (colimit (completedNeighbourhoodDiagram p) : CommRingCat) →+*
      FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  (colimit.desc _ (residueCocone p)).hom

private theorem residue_ι (f : BasicNeighbourhood p)
    (x : ToType ((completedNeighbourhoodDiagram p).obj f)) :
    residue p (colimit.ι (completedNeighbourhoodDiagram p) f x) = residueAway p f x :=
  colimit.ι_desc_apply (residueCocone p) f x

private theorem residue_surjective : Function.Surjective (residue p) := by
  intro z
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (A := A ⧸ (p : PrimeSpectrum A).asIdeal) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : b ∉ (p : PrimeSpectrum A).asIdeal := fun h ↦
    nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  obtain ⟨v, hv⟩ := CompletedAway.isUnit_algebraMap_self A b
  have hbv : residueAway p ⟨b, hb'⟩ ↑v⁻¹ * toResidue p b = 1 := by
    rw [← residueAway_algebraMap p ⟨b, hb'⟩, ← hv, ← map_mul, v.inv_mul, map_one]
  have hy : residueAway p ⟨b, hb'⟩ (algebraMap A (CompletedAway A b) a * ↑v⁻¹) =
      toResidue p a / toResidue p b := by
    rw [map_mul, residueAway_algebraMap, eq_div_iff (isUnit_toResidue p ⟨b, hb'⟩).ne_zero,
      mul_assoc, hbv, mul_one]
  exact ⟨colimit.ι (completedNeighbourhoodDiagram p) ⟨b, hb'⟩ _, (residue_ι p _ _).trans hy⟩

private instance isLocalHom_residue : IsLocalHom (residue p) := by
  refine ⟨fun c hc ↦ ?_⟩
  obtain ⟨f, x, rfl⟩ := Concrete.colimit_exists_rep _ c
  rw [residue_ι] at hc
  obtain ⟨g, h, hunit⟩ := exists_isUnit_restrict p hc.ne_zero
  rw [← colimit.w_apply (completedNeighbourhoodDiagram p) (homOfLE h)]
  exact hunit.map _

/-- The colimit `colim_{f ∉ p} A_{f}` of the completed localisations of `A` over the basic open
neighbourhoods of an open prime `p` is a local ring (EGA I, Ch. 0, 7.6.17). -/
instance completedNeighbourhoodColimit_isLocalRing :
    IsLocalRing (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
  (residue p).domain_isLocalRing

/-- The residue map descends to a bijection from the residue field of the colimit. -/
private theorem bijective_lift_residue :
    Function.Bijective (IsLocalRing.ResidueField.lift (residue p)) :=
  ⟨RingHom.injective _, fun z ↦ (residue_surjective p z).elim fun c hc ↦
    ⟨IsLocalRing.residue _ c, (IsLocalRing.ResidueField.lift_residue_apply _ c).trans hc⟩⟩

end Residue

/-- The residue field of the colimit `colim_{f ∉ p} A_{f}` is the fraction field of `A ⧸ p`
(EGA I, Ch. 0, 7.6.17). -/
noncomputable def stalkResidueIso :
    IsLocalRing.ResidueField (colimit (completedNeighbourhoodDiagram p) : CommRingCat) ≃+*
      FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.lift (residue p)) (bijective_lift_residue p)

/-- The residue isomorphism sends the class of `a ∈ A`, through any of the completed
localisations `A_{f}`, to the image of `a` in `Frac(A ⧸ p)`. -/
@[simp]
theorem stalkResidueIso_coeff (f : BasicNeighbourhood p) (a : A) :
    stalkResidueIso p (IsLocalRing.residue _ (colimit.ι (completedNeighbourhoodDiagram p) f
      (algebraMap A (CompletedAway A f.elem) a))) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal) _ (Ideal.Quotient.mk _ a) := by
  rw [stalkResidueIso, RingEquiv.ofBijective_apply, IsLocalRing.ResidueField.lift_residue_apply]
  exact (residue_ι p f _).trans (residueAway_algebraMap p f a)

end TauCeti.FormalScheme.Spf
