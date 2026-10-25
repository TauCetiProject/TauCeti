/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ResidueSequence.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import TauCeti.FieldTheory.FunctionField.Consequences.PointSeparation

/-!
# The point-residue connecting map in positive genus

Let `X` be a proper regular integral curve over a field `k`, with `k` algebraically closed
in its function field, and let `p` be a closed point of residue degree one. In positive genus,
the inclusion `𝒪_X ⟶ 𝒪_X(p)` induces a bijection on global sections: a rational function
with at most a single simple pole at `p` is constant. Hence the connecting map

`H⁰(X, κ(p)_p) ⟶ H¹(X, 𝒪_X)`

of the point-residue sequence is injective. In genus one it is bijective. The source is
one-dimensional over `k`; choosing a local parameter identifies it with the space of simple
principal parts at `p`. This is the cohomological input to tangent separation for the
Abel–Jacobi map. No identification with a differential of a represented Picard functor is
asserted here.

The residue sequence and its connecting map are the existing `residueShortComplex` and
`Scheme.Modules.cohomologyδ`; the dimension calculation uses
`Divisor.dim_ofPoint_eq_one_of_genus_pos` through the scheme/function-field comparison.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1 and Theorem 4.17.
* J. S. Milne, *Jacobian Varieties*, Section 2 (the tangent map of the canonical map).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

universe u

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [hX : Fact (∀ y : X, coheight y ≤ 1)] [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  (hk : IsIntegrallyClosedIn k X.functionField)
  {p : CodimensionOnePoint X} (hp : (X ↘ Spec (.of k)).residueDegree p = 1)

include hk hp

/-- On a positive-genus proper regular curve with exact constants, allowing a simple pole
at a rational closed point still gives only a one-dimensional space of global sections. -/
theorem finrank_cohomology_zero_sheaf_ofPoint_eq_one_of_genus_pos (hg : 0 < X.genus k) :
    finrank k (Scheme.Modules.Cohomology (sheaf (WeilDivisor.ofPoint p)) 0) = 1 := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex := (UniversallyClosed.eq_valuativeCriterion.le _ _
    (X ↘ Spec (.of k)) inferInstance).1
  have hF := isFunctionField_functionField_of_forall_coheight_le_one_of_coheight_eq_one
    k hX.out p.2
  have hgF : 0 < genus k X.functionField := by
    rwa [← genus_eq_genus_functionField hex hX.out hF hk]
  rw [finrank_cohomology_zero_sheaf_eq_dim hex hX.out,
    equivFunctionFieldDivisor_ofPoint]
  exact Divisor.dim_ofPoint_eq_one_of_genus_pos hF hk hgF
    (by rw [X.toPlace_degree_eq_residueDegree, hp])

/-- The inclusion `𝒪_X ⟶ 𝒪_X(p)` is a bijection on zeroth cohomology when `p` is rational
and the curve has positive genus. -/
theorem cohomologyMap_sheafHomOfLE_zero_add_ofPoint_bijective_of_genus_pos
    (hg : 0 < X.genus k) :
    Function.Bijective (Scheme.Modules.cohomologyMap
      (sheafHomOfLE (WeilDivisor.le_add_ofPoint (0 : SchemeWeilDivisor X) p)) 0) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex := (UniversallyClosed.eq_valuativeCriterion.le _ _
    (X ↘ Spec (.of k)) inferInstance).1
  have hF := isFunctionField_functionField_of_forall_coheight_le_one_of_coheight_eq_one
    k hX.out p.2
  have := finiteDimensional_cohomology_zero_sheaf (k := k) hX.out
    (D := (0 : SchemeWeilDivisor X))
  have := finiteDimensional_cohomology_zero_sheaf (k := k) hX.out
    (D := (0 : SchemeWeilDivisor X) + WeilDivisor.ofPoint p)
  let i := sheafHomOfLE (WeilDivisor.le_add_ofPoint (0 : SchemeWeilDivisor X) p)
  have : Mono i := by
    have : Mono (i ≫ sheafι _) := by
      rw [sheafHomOfLE_ι]
      infer_instance
    exact mono_of_mono i (sheafι _)
  have hi := Scheme.Modules.cohomologyMap_injective i
  have hdim : finrank k (Scheme.Modules.Cohomology (sheaf (0 : SchemeWeilDivisor X)) 0) =
      finrank k (Scheme.Modules.Cohomology (sheaf (0 + WeilDivisor.ofPoint p)) 0) := by
    rw [zero_add, finrank_cohomology_zero_sheaf_zero_eq_one hex hX.out hF hk,
      finrank_cohomology_zero_sheaf_ofPoint_eq_one_of_genus_pos k hk hp hg]
  have hcoe : ⇑(Scheme.Modules.cohomologyMapBaseLinear k X i 0) =
      ⇑(Scheme.Modules.cohomologyMap i 0) := by
    funext x
    rw [Scheme.Modules.cohomologyMapBaseLinear_apply, Scheme.Modules.cohomologyFunctor_map]
    rfl
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := Scheme.Modules.cohomologyMapBaseLinear k X i 0)).mp (by
      rwa [hcoe])
  exact ⟨hi, by rwa [hcoe] at hsurj⟩

variable {g : X.functionFieldˣ}
  (hg : X.ord (g : X.functionField) p = WeilDivisor.coeff (0 : SchemeWeilDivisor X) p + 1)

/-- The point-residue connecting map is injective at a rational closed point of a
positive-genus proper regular curve with exact constants. Any choice of local parameter
in the residue sequence gives this injectivity. -/
theorem cohomologyδ_residueShortComplex_zero_injective_of_genus_pos (hgenus : 0 < X.genus k) :
    Function.Injective (Scheme.Modules.cohomologyδ
      (residueShortComplex_shortExact
        (isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hX.out p.2) hg)
      0 1 rfl) := by
  let S := residueShortComplex g hg
  have hS : S.ShortExact :=
    residueShortComplex_shortExact
      (isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hX.out p.2) hg
  have hi : Function.Surjective (Scheme.Modules.cohomologyMap S.f 0) := by
    -- Transport the whole short complex, including the dependent cohomology carriers.
    exact (congrArg (fun C : ShortComplex X.Modules ↦
      Function.Surjective (Scheme.Modules.cohomologyMap C.f 0))
        (residueShortComplex_def hg)).mpr
      (cohomologyMap_sheafHomOfLE_zero_add_ofPoint_bijective_of_genus_pos k hk hp hgenus).2
  apply (injective_iff_map_eq_zero (Scheme.Modules.cohomologyδ hS 0 1 rfl)).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := (Scheme.Modules.exact_cohomologyMap_cohomologyδ hS 0 1 rfl x).mp hx
  obtain ⟨z, rfl⟩ := hi y
  exact (Scheme.Modules.exact_cohomologyMap_cohomologyMap hS 0 _).mpr ⟨z, rfl⟩

/-- In genus one the point-residue connecting map at a rational closed point is bijective:
it identifies the one-dimensional space of simple principal parts with `H¹(X, 𝒪_X)`. -/
theorem cohomologyδ_residueShortComplex_zero_bijective_of_genus_eq_one
    (hgenus : X.genus k = 1) :
    Function.Bijective (Scheme.Modules.cohomologyδ
      (residueShortComplex_shortExact
        (isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hX.out p.2) hg)
      0 1 rfl) := by
  let S := residueShortComplex g hg
  have hS : S.ShortExact :=
    residueShortComplex_shortExact
      (isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hX.out p.2) hg
  have : FiniteDimensional k (Scheme.Modules.Cohomology S.X₃ 0) := by
    dsimp only [S]
    rw [residueShortComplex_X₃]
    exact Scheme.finiteDimensional_cohomology_skyscraperResidueField k (by omega) 0
  have : FiniteDimensional k (Scheme.Modules.Cohomology S.X₁ 1) := by
    dsimp only [S]
    rw [residueShortComplex_X₁]
    exact (Scheme.Modules.finiteDimensional_cohomology_congr k (sheafZeroIsoTrivial hX.out) 1).mpr
      inferInstance
  have hdim : finrank k (Scheme.Modules.Cohomology S.X₃ 0) =
      finrank k (Scheme.Modules.Cohomology S.X₁ 1) := by
    dsimp only [S]
    rw [residueShortComplex_X₃, residueShortComplex_X₁,
      Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections,
      Scheme.finrank_cohomology_zero_skyscraperResidueField, hp,
      Scheme.Modules.finrank_cohomology_congr k (sheafZeroIsoTrivial hX.out) 1,
      ← Scheme.genus_def, hgenus]
  have hi := cohomologyδ_residueShortComplex_zero_injective_of_genus_pos k hk hp hg (by omega)
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := Scheme.Modules.cohomologyδBaseLinear k X hS 0 1 rfl)).mp (by
      simpa only [Function.Injective, Scheme.Modules.cohomologyδBaseLinear_apply] using hi)
  exact ⟨hi, by
    simpa only [Function.Surjective, Scheme.Modules.cohomologyδBaseLinear_apply] using hsurj⟩

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
