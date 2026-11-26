/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialCharacter.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.Grp.Injective

/-!
# The curvature exact sequence of differential characters

Let `M` be a boundaryless smooth manifold. Cheeger and Simons' first exact sequence for the
differential characters of degree `k` (integral differential cohomology of degree `k + 1`) is

`0 → Hᵏ(M; ℝ/ℤ) → Hᵏ_diff(M) → Ω^{k+1}_ℤ(M) → 0`,

where `Hᵏ_diff(M)` is the group `TauCeti.differentialCharacters I M k`, the second map is the
curvature and `Ω^{k+1}_ℤ(M)` is the group of smooth `(k + 1)`-forms with integral periods
(`TauCeti.integralPeriodForms`). This file proves it.

* **The flat characters.** A homomorphism `f : H_k(M; ℤ) → ℝ/ℤ` from the smooth singular homology
  composed with the class map from cycles is a character vanishing on boundaries
  (`TauCeti.differentialCharacters.ofHomology`). This is injective
  (`TauCeti.differentialCharacters.ofHomology_injective`), and its image is the kernel of the
  curvature (`TauCeti.differentialCharacters.exact_ofHomology_curvature`): a character of curvature
  zero vanishes on boundaries, so it factors through homology.
* **The image of the curvature.** A smooth `(k + 1)`-form `φ` is a curvature exactly when it has
  integral periods (`TauCeti.differentialCharacters.range_curvature`). Given `φ` with integral
  periods, `c ↦ ∫_c φ mod ℤ` on `(k + 1)`-chains vanishes on cycles, so it defines a homomorphism
  on the boundaries of `M`. Since `ℝ/ℤ` is divisible, hence an injective abelian group, it extends
  from the boundaries to all `k`-cycles, and the extension is a character of curvature `φ`.
* **Singular cohomology.** When `M` is moreover finite-dimensional, Hausdorff and `σ`-compact, the
  kernel is identified with the singular cohomology `Hᵏ(M; ℝ/ℤ)`
  (`TauCeti.singularCohomologyUnitAddCircleAddEquiv`,
  `TauCeti.differentialCharacters.ofSingularCohomology`,
  `TauCeti.differentialCharacters.exact_ofSingularCohomology_curvature`): singular cohomology is
  the cohomology of smooth singular cochains by the smoothing theorem
  (`TauCeti.smoothSingularCohomologyIso`), and as `ℝ/ℤ` is injective, the Kronecker pairing
  identifies the cohomology of `Hom(C_*^∞(M; ℤ), ℝ/ℤ)` with `Hom(H_k(M; ℤ), ℝ/ℤ)`
  (`TauCeti.ChainComplex.kroneckerEquiv`), the universal coefficient theorem for divisible
  coefficients.

## References

* J. Cheeger and J. Simons, *Differential characters and geometric invariants*, Geometry and
  Topology (College Park, 1983/84), Lecture Notes in Math. 1167, Springer, 1985, §1, Theorem 1.1.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

namespace differentialCharacters

section OfHomology

variable [IsManifold I 1 M]

/-- The **flat differential character** of a homomorphism `f : H_k(M; ℤ) → ℝ/ℤ` out of the smooth
singular homology of `M`: the composite of `f` with the class map from `k`-cycles to homology. It
vanishes on boundaries, so the zero form is a curvature for it. -/
def ofHomology :
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k →+
      UnitAddCircle) →+ differentialCharacters I M k where
  toFun f := ⟨f.comp (((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).homologyπ k).hom.toAddMonoidHom,
    mem_differentialCharacters_iff.2 ⟨0, fun c ↦ by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ZeroMemClass.coe_zero,
        integrationCochain_zero]
      rw [← ModuleCat.comp_apply, toCycles_comp_homologyπ]
      simp⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The flat character of `f` evaluates a cycle by applying `f` to its homology class. -/
@[simp]
theorem ofHomology_apply
    (f : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k →+
      UnitAddCircle)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k) :
    (ofHomology f : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).cycles k →+ UnitAddCircle) z =
      f (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ k z) :=
  (rfl)

/-- A homomorphism out of homology is determined by its flat character, since every homology class
is the class of a cycle. -/
theorem ofHomology_injective :
    Function.Injective (ofHomology (I := I) (M := M) (k := k)) := by
  intro f g hfg
  refine moduleCat_addMonoidHom_ext_homologyπ fun z ↦ ?_
  rw [← ofHomology_apply, ← ofHomology_apply, hfg]

end OfHomology

section Exact

variable [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- Flat characters have curvature zero. -/
@[simp]
theorem curvature_ofHomology
    (f : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k →+
      UnitAddCircle) :
    curvature (ofHomology f) = 0 :=
  curvature_eq_of_forall fun c ↦ by
    rw [ofHomology_apply, ← ModuleCat.comp_apply, toCycles_comp_homologyπ]
    simp

/-- **Exactness at the characters.** The characters of curvature zero are exactly the flat
characters of homomorphisms out of homology. -/
theorem exact_ofHomology_curvature :
    Function.Exact (ofHomology (I := I) (M := M) (k := k)) curvature := by
  intro χ
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- A character of curvature zero vanishes on boundaries, the kernel of the class map, so it
    -- descends to homology.
    let π := (((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).homologyπ k).hom.toAddMonoidHom
    have hπ : Function.Surjective π := moduleCat_homologyπ_surjective _ k
    have hker : π.ker ≤ (χ : ((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).cycles k →+ UnitAddCircle).ker := fun z hz ↦ by
      obtain ⟨c, rfl⟩ := (moduleCat_homologyπ_eq_zero_iff _ (ChainComplex.prev ℕ k) z).1 hz
      exact curvature_eq_zero_iff.1 h c
    refine ⟨π.liftOfSurjective hπ ⟨_, hker⟩, ?_⟩
    ext z
    exact AddMonoidHom.liftOfRightInverse_comp_apply π _ (Function.rightInverse_surjInv hπ) _
      z
  · rintro ⟨f, rfl⟩
    exact curvature_ofHomology f

/-- **The image of the curvature.** On a boundaryless manifold, the curvatures of the differential
characters of degree `k` are exactly the smooth `(k + 1)`-forms with integral periods. -/
theorem range_curvature :
    (curvature (I := I) (M := M) (k := k)).range = integralPeriodForms I M (k + 1) := by
  refine le_antisymm ?_ fun φ hφ ↦ ?_
  · rintro _ ⟨χ, rfl⟩
    exact curvature_mem_integralPeriodForms χ
  -- The homomorphism `c ↦ ∫_c φ mod ℤ` on `(k + 1)`-chains vanishes on cycles, so it descends to
  -- the boundaries `T c` of chains, and extends to all `k`-cycles since `ℝ/ℤ` is divisible.
  let T := (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).toCycles
    (k + 1) k).hom.toAddMonoidHom
  let ψ : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1) →+
      UnitAddCircle :=
    (QuotientAddGroup.mk' _).comp (integrationCochain φ.val).hom.toAddMonoidHom
  have hker : T.rangeRestrict.ker ≤ ψ.ker := fun c hc ↦ by
    rw [AddMonoidHom.ker_rangeRestrict] at hc
    have hd : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k
        c = 0 := by
      rw [← moduleCat_iCycles_toCycles_apply]
      exact (congrArg _ hc).trans (map_zero _)
    obtain ⟨n, hn⟩ := mem_integralPeriodForms_iff.1 hφ
      (moduleCatCyclesMk _ c k (ChainComplex.next_nat_succ k) hd)
    rw [iCycles_moduleCatCyclesMk] at hn
    simp [ψ, hn]
  obtain ⟨χ, hχ⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    T.range.subtype Subtype.val_injective
    (T.rangeRestrict.liftOfSurjective T.rangeRestrict_surjective ⟨ψ, hker⟩)
  have hχT : ∀ c, χ (T c) = ψ c := fun c ↦
    (DFunLike.congr_fun hχ (T.rangeRestrict c)).trans
      (AddMonoidHom.liftOfRightInverse_comp_apply T.rangeRestrict _
        (Function.rightInverse_surjInv T.rangeRestrict_surjective) _ c)
  exact ⟨⟨χ, mem_differentialCharacters_iff.2 ⟨φ, hχT⟩⟩, curvature_eq_of_forall hχT⟩

end Exact

end differentialCharacters

section SingularCohomology

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

namespace differentialCharacters

variable (I) in
/-- The **flat differential character of a singular cohomology class** `x ∈ Hᵏ(M; ℝ/ℤ)`: the flat
character of the homomorphism `H_k(M; ℤ) → ℝ/ℤ` that `x` defines by the universal coefficient
theorem (`TauCeti.singularCohomologyUnitAddCircleAddEquiv`). -/
def ofSingularCohomology :
    (TopCat.of M).singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ UnitAddCircle) k →+
      differentialCharacters I M k :=
  ofHomology.comp (singularCohomologyUnitAddCircleAddEquiv I M k).toAddMonoidHom

/-- The flat character of a singular cohomology class evaluates a cycle on its homology class
through the universal coefficient equivalence. -/
@[simp]
theorem ofSingularCohomology_apply
    (x : (TopCat.of M).singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ UnitAddCircle) k)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k) :
    (ofSingularCohomology I x : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).cycles k →+ UnitAddCircle) z =
      singularCohomologyUnitAddCircleAddEquiv I M k x
        (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ k z) :=
  (rfl)

/-- Flat characters of singular cohomology classes have curvature zero. -/
@[simp]
theorem curvature_ofSingularCohomology [BoundarylessManifold I M]
    (x : (TopCat.of M).singularCohomology (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ UnitAddCircle) k) :
    curvature (ofSingularCohomology I x) = 0 :=
  curvature_ofHomology _

/-- **Exactness at `Hᵏ(M; ℝ/ℤ)`.** The flat character map from singular cohomology with
coefficients in `ℝ/ℤ` is injective. -/
theorem ofSingularCohomology_injective :
    Function.Injective (ofSingularCohomology I (M := M) (k := k)) :=
  ofHomology_injective.comp (singularCohomologyUnitAddCircleAddEquiv I M k).injective

/-- **Exactness at the characters, singular form.** On a finite-dimensional Hausdorff `σ`-compact
boundaryless manifold, the characters of curvature zero are exactly the flat characters of the
singular cohomology classes in `Hᵏ(M; ℝ/ℤ)`. -/
theorem exact_ofSingularCohomology_curvature [BoundarylessManifold I M] :
    Function.Exact (ofSingularCohomology I (M := M) (k := k)) curvature := fun χ ↦ by
  rw [exact_ofHomology_curvature χ, ofSingularCohomology, AddMonoidHom.coe_comp]
  exact Iff.of_eq (congrArg (χ ∈ ·)
    ((singularCohomologyUnitAddCircleAddEquiv I M k).surjective.range_comp _).symm)

end differentialCharacters

end SingularCohomology

end TauCeti
