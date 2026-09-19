/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Scheme.ClosedPoint
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Picard
public import TauCeti.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite-dimensionality of Riemann–Roch spaces on a proper curve

For a Weil divisor `D` on an integral scheme whose codimension-one local rings are discrete
valuation rings, the global sections of the sheaf `𝒪_X(D)` form the Riemann–Roch space

`L(D) = {f ∈ K(X) | f = 0 or ord_y f ≥ -D(y) for every codimension-one point y}`.

This file proves that `L(D)` is finite-dimensional over `k` when `X` is a proper curve over a
field `k`, and deduces that `H⁰(X, L)` is finite-dimensional for every line bundle `L` on such a
curve. This is the degree-zero half of the finiteness needed to read `dim H⁰ - dim H¹` as the
Euler characteristic of a line bundle on a proper curve.

The argument is the classical one. Adding a codimension-one point `y` to `D` enlarges `L(D)` by at
most a copy of the residue field `κ(y)`: if `g` has order `D(y) + 1` at `y`, then `f ↦ g f`
sends `L(D + y)` into the local ring at `y`, and composing with the residue map gives a linear
map `L(D + y) ⟶ κ(y)` whose kernel is exactly `L(D)`. Starting from `L(0) = Γ(X, 𝒪_X)`, every
`L(D)` is reached by adding and removing points one at a time.

## Main declarations

* `SchemeWeilDivisor.fg_sections_add_ofPoint`: if `L(D)` is finitely generated over `Γ(X, ⊤)` and
  `κ(y)` is finite over `Γ(X, ⊤)`, then `L(D + y)` is finitely generated;
* `SchemeWeilDivisor.fg_sections_of_le`: over a Noetherian ring of global functions, `L(D)` is
  finitely generated as soon as `L(E)` is for some `E ≥ D`;
* `SchemeWeilDivisor.fg_sections_top`: on a curve whose ring of global functions is Noetherian and
  whose residue fields at codimension-one points are finite over it, every `L(D)` is finitely
  generated;
* `SchemeWeilDivisor.finiteDimensional_globalSections_sheaf` and
  `SchemeWeilDivisor.finiteDimensional_cohomology_zero_sheaf`: on a proper curve over a field `k`,
  `Γ(X, 𝒪_X(D)) = H⁰(X, 𝒪_X(D))` is finite-dimensional over `k`;
* `InvertibleSheaf.finiteDimensional_cohomology_zero`: on a proper curve over `k`, `H⁰(X, L)` is
  finite-dimensional for every line bundle `L`.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma IV.1.2 and Theorem III.5.2(a).
* W. Fulton, *Algebraic Curves*, Chapter 8, Proposition 2.
-/

public section

open CategoryTheory Order AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

noncomputable section

/-- The whole of the integral scheme `X` is a nonempty open subset, so global sections of `𝒦_X`
are rational functions. -/
local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

section Step

variable {D : SchemeWeilDivisor X} {y : CodimensionOnePoint X}

/-- If `g` has order `D(y) + 1` at `y`, then `g` times a global section of `𝒪_X(D + y)` is regular
at `y`. -/
private lemma exists_algebraMap_eq_mul {g : X.functionField} (hg0 : g ≠ 0)
    (hg : X.ord g y = WeilDivisor.coeff D y + 1) {s : Γ(Scheme.rationalFunctions X, ⊤)}
    (hs : s ∈ sections (D + WeilDivisor.ofPoint y) ⊤) :
    ∃ r : X.presheaf.stalk (y : X), algebraMap _ X.functionField r =
      g * Scheme.rationalFunctionsEquiv ⊤ s := by
  refine Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg y.property ?_
  rcases eq_or_ne (Scheme.rationalFunctionsEquiv ⊤ s) 0 with hf | hf
  · simp [hf]
  · have h := (mem_sections.mp hs y trivial).resolve_left hf
    rw [Scheme.ord_mul hg0 hf, hg]
    simp only [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_self] at h
    omega

/-- A global section `s` of `𝒪_X(D + y)` is a section of `𝒪_X(D)` exactly when the regular
function `g s` at `y` vanishes at `y`, where `g` has order `D(y) + 1` at `y`. -/
private lemma mem_sections_iff_mem_maximalIdeal {g : X.functionField} (hg0 : g ≠ 0)
    (hg : X.ord g y = WeilDivisor.coeff D y + 1) {s : Γ(Scheme.rationalFunctions X, ⊤)}
    (hs : s ∈ sections (D + WeilDivisor.ofPoint y) ⊤) {r : X.presheaf.stalk (y : X)}
    (hr : algebraMap _ X.functionField r = g * Scheme.rationalFunctionsEquiv ⊤ s) :
    s ∈ sections D ⊤ ↔ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (y : X)) := by
  rw [mem_sections_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (Scheme.rationalFunctionsEquiv ⊤ s) 0 with hf | hf
  · have : r = 0 :=
      IsFractionRing.injective _ X.functionField (by rw [hr, hf, mul_zero, map_zero])
    simp [hf, this]
  have hr0 : algebraMap _ X.functionField r ≠ 0 := by
    rw [hr]
    exact mul_ne_zero hg0 hf
  -- In a discrete valuation ring the units are the elements of order zero.
  have hunit : IsUnit r ↔ X.ord (algebraMap _ X.functionField r) y = 0 := by
    rw [Scheme.ord_eq_iff y.property hr0, ofAdd_zero]
    exact Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing
  rw [hunit, hr, Scheme.ord_mul hg0 hf, hg]
  have hy := (mem_sections.mp hs y trivial).resolve_left hf
  simp only [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_self] at hy
  simp only [hf, false_or]
  refine ⟨fun h ↦ by have := h y trivial; omega, fun h z _ ↦ ?_⟩
  by_cases hz : z = y
  · subst hz
    omega
  · simpa [WeilDivisor.coeff_ofPoint_of_ne hz] using
      (mem_sections.mp hs z trivial).resolve_left hf

variable (D y) in
/-- The residue at `y` of `g s`, for a global section `s` of `𝒪_X(D + y)` and a rational function
`g` of order `D(y) + 1` at `y`, as a `Γ(X, ⊤)`-linear map to `κ(y)`. -/
private def residueMap {g : X.functionField} (hg0 : g ≠ 0)
    (hg : X.ord g y = WeilDivisor.coeff D y + 1) :
    letI := (X.Γevaluation y).hom.toAlgebra
    sections (D + WeilDivisor.ofPoint y) ⊤ →ₗ[Γ(X, ⊤)] X.residueField y :=
  letI := (X.Γevaluation y).hom.toAlgebra
  { toFun s := X.residue y (exists_algebraMap_eq_mul hg0 hg s.2).choose
    map_add' s t := by
      rw [← map_add]
      congr 1
      refine IsFractionRing.injective _ X.functionField ?_
      rw [map_add, (exists_algebraMap_eq_mul hg0 hg s.2).choose_spec,
        (exists_algebraMap_eq_mul hg0 hg t.2).choose_spec,
        (exists_algebraMap_eq_mul hg0 hg (s + t).2).choose_spec, Submodule.coe_add, map_add,
        mul_add]
    map_smul' a s := by
      have key : (exists_algebraMap_eq_mul hg0 hg (a • s).2).choose =
          X.presheaf.germ ⊤ y trivial a * (exists_algebraMap_eq_mul hg0 hg s.2).choose := by
        refine IsFractionRing.injective _ X.functionField ?_
        rw [(exists_algebraMap_eq_mul hg0 hg (a • s).2).choose_spec, map_mul,
          (exists_algebraMap_eq_mul hg0 hg s.2).choose_spec,
          Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := ⊤) (x := (y : X))
            trivial a,
          Submodule.coe_smul, map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        ring
      simp only [RingHom.id_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rw [key, map_mul]
      -- `X.Γevaluation y` is by definition the germ at `y` followed by the residue map.
      rfl }

private lemma residueMap_eq_zero_iff {g : X.functionField} (hg0 : g ≠ 0)
    (hg : X.ord g y = WeilDivisor.coeff D y + 1) (s : sections (D + WeilDivisor.ofPoint y) ⊤) :
    residueMap D y hg0 hg s = 0 ↔ (s : Γ(Scheme.rationalFunctions X, ⊤)) ∈ sections D ⊤ := by
  rw [mem_sections_iff_mem_maximalIdeal hg0 hg s.2
    (exists_algebraMap_eq_mul hg0 hg s.2).choose_spec]
  exact IsLocalRing.residue_eq_zero_iff _

/-- **Adding a point to a divisor preserves finite generation of global sections.** If the global
sections of `𝒪_X(D)` are finitely generated over a Noetherian ring `Γ(X, ⊤)`, and the residue
field at `y` is a finite `Γ(X, ⊤)`-algebra, then the global sections of `𝒪_X(D + y)` are finitely
generated: they are an extension of a submodule of `κ(y)` by those of `𝒪_X(D)`. -/
theorem fg_sections_add_ofPoint [IsNoetherianRing Γ(X, ⊤)] (hy : (X.Γevaluation y).hom.Finite)
    (hD : (sections D ⊤).FG) : (sections (D + WeilDivisor.ofPoint y) ⊤).FG := by
  let := (X.Γevaluation y).hom.toAlgebra
  have : Module.Finite Γ(X, ⊤) (X.residueField y) := hy
  obtain ⟨g, hg⟩ := exists_orderAt_eq y (WeilDivisor.coeff D y + 1)
  rw [orderAt_apply] at hg
  let φ := residueMap D y (Units.ne_zero _) hg
  have hker : LinearMap.ker φ = (sections D ⊤).comap (sections _ ⊤).subtype := by
    ext s
    exact residueMap_eq_zero_iff (Units.ne_zero _) hg s
  rw [← Submodule.fg_top]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker φ (IsNoetherian.noetherian _) ?_
  rw [top_inf_eq, hker]
  refine Submodule.fg_of_fg_map_injective (sections _ ⊤).subtype Subtype.val_injective ?_
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr (sections_mono (le_add_of_nonneg_right
    ((WeilDivisor.isEffective_iff _).mp (WeilDivisor.isEffective_ofPoint y))) ⊤)]

end Step

/-- On a scheme of dimension at most one, the global sections of `𝒪_X(0)` are the multiples of the
constant function `1` by global regular functions. -/
private lemma sections_zero_top_eq_span (hX : ∀ y : X, coheight y ≤ 1) :
    sections (0 : SchemeWeilDivisor X) ⊤ =
      Submodule.span Γ(X, ⊤) {(Scheme.rationalFunctionsEquiv ⊤).symm 1} := by
  refine le_antisymm (fun s hs ↦ ?_) ?_
  · obtain ⟨a, rfl⟩ := (mem_sections_zero_iff (fun y _ ↦ hX y) s).mp hs
    refine Submodule.mem_span_singleton.mpr ⟨a, (Scheme.rationalFunctionsEquiv ⊤).injective ?_⟩
    rw [map_smul, LinearEquiv.apply_symm_apply, Algebra.smul_def, mul_one,
      Scheme.rationalFunctionsEquiv_toRationalFunctions_app, RingHom.algebraMap_toAlgebra]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact rationalFunctionsEquiv_symm_mem_sections fun y _ ↦ by simp

/-- Over a Noetherian ring of global functions, the global sections of `𝒪_X(D)` are finitely
generated as soon as those of `𝒪_X(E)` are for some `E ≥ D`. -/
theorem fg_sections_of_le [IsNoetherianRing Γ(X, ⊤)] {D E : SchemeWeilDivisor X} (h : D ≤ E)
    (hE : (sections E ⊤).FG) : (sections D ⊤).FG := by
  have : Module.Finite Γ(X, ⊤) (sections E ⊤) := Module.Finite.iff_fg.mpr hE
  exact isNoetherian_submodule.mp inferInstance _ (sections_mono h ⊤)

/-- **Global sections of `𝒪_X(D)` are finitely generated.** On a locally Noetherian integral scheme
of dimension at most one whose codimension-one local rings are discrete valuation rings, whose ring
`Γ(X, ⊤)` of global functions is Noetherian, and whose residue fields at codimension-one points
are finite `Γ(X, ⊤)`-algebras, the global sections of `𝒪_X(D)` are a finitely generated
`Γ(X, ⊤)`-module for every Weil divisor `D`. -/
theorem fg_sections_top [IsNoetherianRing Γ(X, ⊤)] (hX : ∀ y : X, coheight y ≤ 1)
    (hfin : ∀ y : CodimensionOnePoint X, (X.Γevaluation y).hom.Finite)
    (D : SchemeWeilDivisor X) : (sections D ⊤).FG := by
  -- Adding any integer multiple of a point preserves finite generation: nonnegative multiples by
  -- `fg_sections_add_ofPoint`, negative ones by passing to a smaller divisor.
  have step (y : CodimensionOnePoint X) (n : ℤ) (E : SchemeWeilDivisor X)
      (hE : (sections E ⊤).FG) : (sections (E + n • WeilDivisor.ofPoint y) ⊤).FG := by
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      induction n with
      | zero => simpa using hE
      | succ n ih =>
        have := fg_sections_add_ofPoint (D := E + (n : ℤ) • WeilDivisor.ofPoint y) (hfin y) ih
        rwa [add_assoc, ← add_one_zsmul] at this
    · refine fg_sections_of_le (add_le_of_nonpos_right fun z ↦ ?_) hE
      simp only [Finsupp.coe_smul, Pi.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul]
      exact mul_nonpos_of_nonpos_of_nonneg hn.le
        ((WeilDivisor.isEffective_iff _).mp (WeilDivisor.isEffective_ofPoint y) z)
  induction D using Finsupp.induction with
  | zero => rw [sections_zero_top_eq_span hX]; exact Submodule.fg_span_singleton _
  | single_add a b f _ _ ih =>
    rw [add_comm, WeilDivisor.single_eq_zsmul_ofPoint]
    exact step a b f ih

section Field

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **Riemann–Roch spaces are finite-dimensional.** On a proper integral curve over a field `k`
whose codimension-one local rings are discrete valuation rings, the space `Γ(X, 𝒪_X(D))` of global
sections of the sheaf of a Weil divisor `D` is finite-dimensional over `k`. -/
theorem finiteDimensional_globalSections_sheaf (hX : ∀ y : X, coheight y ≤ 1)
    (D : SchemeWeilDivisor X) : FiniteDimensional k Γ(sheaf D, ⊤) := by
  let := (Scheme.Modules.baseRingToGlobalSections k X).toAlgebra
  -- `Γ(X, ⊤)` is a finite field extension of `k`, since `X` is proper and integral over `k`.
  let := (isField_of_universallyClosed k (X ↘ Spec (.of k))).toField
  have hbase : Scheme.Modules.baseRingToGlobalSections k X =
      (X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom :=
    RingHom.ext (Scheme.Modules.baseRingToGlobalSections_apply k X)
  have : (Scheme.Modules.baseRingToGlobalSections k X).Finite := by
    rw [hbase]
    exact (finite_appTop_of_universallyClosed k (X ↘ Spec (.of k))).comp
      (RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Module.Finite k Γ(X, ⊤) := this
  -- Codimension-one points of a curve are closed, so their residue fields are finite over `k`.
  have hfin (y : CodimensionOnePoint X) : (X.Γevaluation y).hom.Finite :=
    Scheme.finite_Γevaluation_of_isClosed (X ↘ Spec (.of k))
      (isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hX y.property)
  -- The inclusion `𝒪_X(D) ⟶ 𝒦_X` identifies global sections of `𝒪_X(D)` with `sections D ⊤`.
  let ι : Γ(sheaf D, ⊤) →ₗ[Γ(X, ⊤)] Γ(Scheme.rationalFunctions X, ⊤) :=
    { toFun := (sheafι D).app ⊤
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hrange : LinearMap.range ι = sections D ⊤ :=
    SetLike.coe_injective (by rw [LinearMap.coe_range]; exact range_sheafι_app D ⊤)
  have : Module.Finite Γ(X, ⊤) (LinearMap.range ι) :=
    Module.Finite.iff_fg.mpr (hrange ▸ fg_sections_top hX hfin D)
  have : Module.Finite Γ(X, ⊤) Γ(sheaf D, ⊤) :=
    Module.Finite.equiv (LinearEquiv.ofInjective ι (sheafι_app_injective D ⊤)).symm
  have : IsScalarTower k Γ(X, ⊤) Γ(sheaf D, ⊤) := .of_algebraMap_smul fun r x ↦
    (Scheme.Modules.base_smul_globalSections k X (sheaf D) r x).symm
  exact Module.Finite.trans Γ(X, ⊤) _

/-- On a proper integral curve over a field `k` whose codimension-one local rings are discrete
valuation rings, `H⁰(X, 𝒪_X(D))` is finite-dimensional over `k` for every Weil divisor `D`. -/
theorem finiteDimensional_cohomology_zero_sheaf (hX : ∀ y : X, coheight y ≤ 1)
    (D : SchemeWeilDivisor X) : FiniteDimensional k (Scheme.Modules.Cohomology (sheaf D) 0) :=
  have := finiteDimensional_globalSections_sheaf k hX D
  Module.Finite.equiv (Scheme.Modules.cohomologyZeroBaseLinearEquiv k X (sheaf D)).symm

end Field

end

end SchemeWeilDivisor

namespace InvertibleSheaf

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

open Scheme.Modules in
/-- **`H⁰` of a line bundle on a proper curve is finite-dimensional.** On a proper integral curve
over a field `k` whose codimension-one local rings are discrete valuation rings, `H⁰(X, L)` is
finite-dimensional over `k` for every line bundle `L`: `L` is isomorphic to the sheaf `𝒪_X(D)` of a
Weil divisor. -/
theorem finiteDimensional_cohomology_zero (hX : ∀ y : X, coheight y ≤ 1) (L : InvertibleSheaf X) :
    FiniteDimensional k (Cohomology L.obj 0) := by
  -- `X` is Noetherian, being proper over a field.
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  have : IsNoetherian X := {}
  obtain ⟨D, ⟨e⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hX L
  have := SchemeWeilDivisor.finiteDimensional_cohomology_zero_sheaf k hX D
  refine Module.Finite.of_surjective (cohomologyMapBaseLinear k X e.inv 0) fun x ↦
    ⟨cohomologyMapBaseLinear k X e.hom 0 x, ?_⟩
  rw [← LinearMap.comp_apply, ← cohomologyMapBaseLinear_comp, e.hom_inv_id,
    cohomologyMapBaseLinear_id, LinearMap.id_apply]

end InvertibleSheaf

end AlgebraicGeometry

end TauCeti
