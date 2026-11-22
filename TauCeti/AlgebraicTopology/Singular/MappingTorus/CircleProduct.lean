/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.AddCircle
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.BaseCircle
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FirstCohomology
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.SecondCohomology
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# The first and second cohomology of `(ℝ / pℤ) × Y_φ`

Let `F` be a closed connected oriented surface and `φ : F ≃ₜ F` an orientation-preserving
homeomorphism with `det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, so that the mapping torus `Y_φ` has
`b₁(Y_φ) = 1`. The symplectic suspension of an area-preserving `φ` is `X = (ℝ / ℤ)_s × Y_φ`, and
Taubes's line labels on `X` are written in two classes: the pullback `pr₂^* v` of a class
`v ∈ H²(Y_φ; ℤ)` pairing to one with the fibre class, and the class `t = [ds] ⌣ pr₂^* a`, where
`[ds]` is the angular class of the circle factor and `a` generates `H¹(Y_φ; ℤ) ≅ ℤ`; when `a` is
the class `[dt]` of the base circle of `Y_φ`, `t = [ds ∧ dt]`. This file proves that these two
classes are a basis of `H²(X; ℤ)` modulo torsion, keeping every torsion label:

* every class of `H²((ℝ / pℤ) × Y_φ; ℤ)` differs from `m • pr₂^* v + c • t` by an element of finite
  order, for some integers `m` and `c`
  (`TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`);
* `m • pr₂^* v + c • t` has finite order only for `m = c = 0`
  (`TauCeti.MappingTorus.isOfFinAddOrder_smul_add_smul_addCircleProd_iff`), so `m` and `c` are
  unique;
* as for every space `Y`, the classes of finite order of `H²((ℝ / pℤ) × Y_φ; ℤ)` are exactly the
  pullbacks of the classes of finite order of `H²(Y_φ; ℤ)`
  (`TopCat.isOfFinAddOrder_iff_exists_singularCohomologyMap_snd_addCircle` with `n = 1`, since
  `H¹(Y_φ; ℤ)` is torsion-free by `TopCat.isAddTorsionFree_singularCohomology_one`).

The first statement is the spanning hypothesis `hspan` of the intersection-form results for the
pair `v, t` in `TauCeti.LinearAlgebra.BilinearForm.HyperbolicPair` and
`TauCeti.Geometry.Symplectic.Manifold.Suspension.Chamber`, such as
`LinearMap.BilinForm.even_apply_self_of_isOfFinAddOrder_span` and
`LinearMap.BilinForm.sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span`, applied to
`H = H²(X; ℤ)` with its `ℤ`-module structure `AddCommGroup.toIntModule`.

The proof combines three computations. The cohomology of a product with a circle splits as
`H²((ℝ / pℤ) × Y; ℤ) ≅ H²(Y; ℤ) × H¹(Y; ℤ)` by slant products
(`TopCat.singularCohomologyAddCircleProdSlantEquiv`), so a basis modulo torsion of each factor
gives one of the product (`TopCat.exists_isOfFinAddOrder_sub_smul_add_smul_addCircle`,
`TopCat.isOfFinAddOrder_smul_add_smul_addCircle_iff`). The factor `H¹(Y_φ; ℤ)` is `ℤ`
(`TauCeti.MappingTorus.cohomologyOneEquiv`) and torsion-free
(`TopCat.isAddTorsionFree_singularCohomology_one`), so a generator has infinite order. The factor
`H²(Y_φ; ℤ)` is `ℤ` modulo torsion, detected by evaluation on the fibre class
(`TauCeti.MappingTorus.isOfFinAddOrder_sub_evalFundamentalClass_smul`). The fibre class is built
from singular chains with coefficients in `ULift ℤ`, so the class `v` is read there through the
change of chain coefficients `TopCat.singularCohomologyChainCoefficientMap` along
`TauCeti.uliftIntIso`, an isomorphism
(`TauCeti.MappingTorus.isOfFinAddOrder_sub_evalFundamentalClass_chainCoefficientMap_smul`).

For the generator `a` one may take the base class `[dt] = proj^* θ_1` of the mapping torus
(`TauCeti.MappingTorus.baseClass`), which generates `H¹(Y_φ; ℤ)` by
`TauCeti.MappingTorus.exists_eq_zsmul_baseClass`; then `t = pr₁^* θ_p ⌣ pr₂^* [dt]`.

**The first cohomology.** The same slant decomposition in degree one,
`H¹((ℝ / pℤ) × Y; ℤ) ≃ H¹(Y; ℤ) × H⁰(Y; ℤ)`, together with `H⁰(Y; ℤ) ≅ ℤ` for a path-connected `Y`
(`TauCeti.singularCohomologyZeroEvalEquiv`) and `H¹(Y_φ; ℤ) = ℤ [dt]`, shows that the angular class
`pr₁^* θ_p` of the circle factor and the base class `pr₂^* [dt]` form a basis of
`H¹((ℝ / pℤ) × Y_φ; ℤ)` (`TauCeti.MappingTorus.basisAddCircleProd`). This only needs a
path-connected fibre with `H₁(F; ℤ)` free of finite rank and `det (1 - φ_*) ≠ 0`. For `p = 1` the
basis is `([ds], [dt])`, in the order of the product homology orientation `e₀ ∧ i[ds] ∧ i[dt] ∧ e₊`,
and its coordinates are the coordinates `νₛ, νₜ` in which the Seiberg–Witten wall class of the
suspension is `q νₛ νₜ`
(`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_eq_smul_det`). That theorem is
stated in the model `TopCat.integralCohomology` of integral cohomology, with chains in `ULift ℤ`;
reading the basis there, through the change of chain coefficients along
`TauCeti.integralCoeffIso`, is not done here.

The intersection numbers `v · v = t · t = 0` and `v · t = 1` of the two classes are not proved
here.

## Main results

* `TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`: `pr₂^* v` and
  `t` span `H²((ℝ / pℤ) × Y_φ; ℤ)` modulo torsion.
* `TauCeti.MappingTorus.isOfFinAddOrder_smul_add_smul_addCircleProd_iff`: they are independent
  modulo torsion.
* `TauCeti.MappingTorus.basisAddCircleProd`: the basis `(pr₁^* θ_p, pr₂^* [dt])` of
  `H¹((ℝ / pℤ) × Y_φ; ℤ)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 (the Künneth formula) and Example 2.48 (the Wang sequence of a mapping torus).
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Module

attribute [local instance 1100] ModuleCat.instLinear

namespace TauCeti.MappingTorus

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)

/-! ### The first cohomology of `(ℝ / pℤ) × Y_φ` -/

section FirstCohomology

variable (p : ℝ) [Fact (0 < p)]

variable [PathConnectedSpace F]
  [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
  [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]

/-- **`[ds]` and `[dt]` are independent in `H¹((ℝ / pℤ) × Y_φ; ℤ)`.** If `F` is path-connected,
`H₁(F; ℤ)` is free of finite rank and `det (1 - φ_*) ≠ 0` on it, the classes `pr₁^* θ_p` and
`pr₂^* [dt]` are linearly independent. -/
theorem linearIndependent_addCircleProd_baseClass
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    LinearIndependent ℤ ![TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst
        (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p),
      TopCat.singularCohomologyMap (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd
        (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (baseClass φ)] := by
  have h₀ := TopCat.singularCohomologyAddCircleProdSlantEquiv_symm_zero_singularCohomologyZeroOne
    (TopCat.of (MappingTorus φ)) (0 : AddCircle p)
  have h₁ : (TopCat.singularCohomologyAddCircleProdSlantEquiv (𝟙_ (ModuleCat.{0} ℤ))
      (TopCat.of (MappingTorus φ)) (0 : AddCircle p) 0).symm (baseClass φ, 0) =
        TopCat.singularCohomologyMap (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd
          (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (baseClass φ) :=
    TopCat.singularCohomologyAddCircleProdSlantEquiv_symm_mk_zero _ _ _ 0 _
  rw [LinearIndependent.pair_iff]
  intro a b hab
  rw [← h₀, ← h₁, ← Int.cast_id (n := a), ← Int.cast_id (n := b), Int.cast_smul_eq_zsmul ℤ,
    Int.cast_smul_eq_zsmul ℤ, ← map_zsmul, ← map_zsmul, ← map_add, AddEquivClass.map_eq_zero_iff,
    Prod.ext_iff] at hab
  obtain ⟨hb, ha⟩ := hab
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, zsmul_zero, zero_add,
    add_zero, Prod.fst_zero, Prod.snd_zero] at hb ha
  refine ⟨?_, ?_⟩
  · -- Evaluate the degree-zero class `a • 1` at a point.
    obtain ⟨x₀⟩ := (inferInstance : Nonempty (MappingTorus φ))
    simpa using congrArg (singularCohomologyZeroEval x₀) ha
  · -- `H¹(Y_φ; ℤ) ≅ ℤ` sends `[dt]` to a unit.
    have h := congrArg (cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet) hb
    rw [map_zsmul, map_zero, smul_eq_mul] at h
    rcases cohomologyOneEquiv_baseClass φ hdet with h' | h' <;> simpa [h'] using h

/-- **`[ds]` and `[dt]` span `H¹((ℝ / pℤ) × Y_φ; ℤ)`.** Under the hypotheses of
`TauCeti.MappingTorus.linearIndependent_addCircleProd_baseClass`, every class of
`H¹((ℝ / pℤ) × Y_φ; ℤ)` is an integer combination of `pr₁^* θ_p` and `pr₂^* [dt]`. -/
theorem top_le_span_addCircleProd_baseClass
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    ⊤ ≤ Submodule.span ℤ (Set.range ![TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst
        (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p),
      TopCat.singularCohomologyMap (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd
        (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (baseClass φ)]) := by
  have h₀ := TopCat.singularCohomologyAddCircleProdSlantEquiv_symm_zero_singularCohomologyZeroOne
    (TopCat.of (MappingTorus φ)) (0 : AddCircle p)
  have h₁ : (TopCat.singularCohomologyAddCircleProdSlantEquiv (𝟙_ (ModuleCat.{0} ℤ))
      (TopCat.of (MappingTorus φ)) (0 : AddCircle p) 0).symm (baseClass φ, 0) =
        TopCat.singularCohomologyMap (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd
          (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (baseClass φ) :=
    TopCat.singularCohomologyAddCircleProdSlantEquiv_symm_mk_zero _ _ _ 0 _
  set e := TopCat.singularCohomologyAddCircleProdSlantEquiv (𝟙_ (ModuleCat.{0} ℤ))
    (TopCat.of (MappingTorus φ)) (0 : AddCircle p) 0
  intro x _
  -- The two slant products of `x` are `m • [dt]` and `c • 1`.
  obtain ⟨m, hm⟩ := exists_eq_zsmul_baseClass φ hdet (e x).1
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (MappingTorus φ))
  set c := singularCohomologyZeroEval x₀ (e x).2
  have hc : (e x).2 = c • (TopCat.of (MappingTorus φ)).singularCohomologyZeroOne := by
    rw [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id]
    exact eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne
      (X := TopCat.of (MappingTorus φ)) x₀ _
  have hx : x = c • e.symm (0, (TopCat.of (MappingTorus φ)).singularCohomologyZeroOne) +
      m • e.symm (baseClass φ, 0) := by
    rw [← map_zsmul, ← map_zsmul, ← map_add, e.eq_symm_apply]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, hm]
      rw [zsmul_zero]
      exact (zero_add _).symm
    · simp only [Prod.snd_add, Prod.smul_snd, hc]
      rw [zsmul_zero]
      exact (add_zero _).symm
  rw [hx, h₀, h₁]
  exact add_mem (zsmul_mem (Submodule.subset_span (Set.mem_range_self 0)) c)
    (zsmul_mem (Submodule.subset_span (Set.mem_range_self 1)) m)

/-- **The basis `([ds], [dt])` of `H¹((ℝ / pℤ) × Y_φ; ℤ)`.** If `F` is path-connected, `H₁(F; ℤ)`
is free of finite rank and `det (1 - φ_*) ≠ 0` on it, the angular class `pr₁^* θ_p` of the circle
factor and the base class `pr₂^* [dt]` of the mapping torus form a basis, in this order. For
`p = 1` these are the classes `[ds]` and `[dt]` of the symplectic suspension `(ℝ / ℤ)_s × Y_φ`, and
the coordinates of the basis are the coordinates `νₛ, νₜ` of the Seiberg–Witten wall class. -/
def basisAddCircleProd
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    Module.Basis (Fin 2) ℤ
      ((TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCohomology
        (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 1) :=
  .mk (linearIndependent_addCircleProd_baseClass φ p hdet)
    (top_le_span_addCircleProd_baseClass φ p hdet)

/-- The first vector of `basisAddCircleProd` is the angular class `[ds] = pr₁^* θ_p`. -/
@[simp]
lemma basisAddCircleProd_zero
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    basisAddCircleProd φ p hdet 0 = TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst
      (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p) := by
  simp [basisAddCircleProd]

/-- The second vector of `basisAddCircleProd` is the base class `[dt] = pr₂^* [dt]`. -/
@[simp]
lemma basisAddCircleProd_one
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    basisAddCircleProd φ p hdet 1 = TopCat.singularCohomologyMap (M := 𝟙_ (ModuleCat.{0} ℤ))
      (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1
      (baseClass φ) := by
  simp [basisAddCircleProd]

end FirstCohomology

variable [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
  [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]

variable {E : Type} [T2Space F] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E F] [CompactSpace F] [ConnectedSpace F]
  (o : HomologicalOrientation F E 2) (hn : finrank ℝ E = 2)

/-! ### The second cohomology of `(ℝ / pℤ) × Y_φ` modulo torsion -/

variable {p : ℝ} [Fact (0 < p)]

/-- **`H²((ℝ / pℤ) × Y_φ; ℤ)` is spanned modulo torsion by `pr₂^* v` and `θ_p ⌣ pr₂^* a`.** Let `φ`
be an orientation-preserving homeomorphism of a closed connected oriented surface `F` with
`det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, let `v ∈ H²(Y_φ; ℤ)` pair to one with the fibre class and let
`a` generate `H¹(Y_φ; ℤ)`. Then every class `x ∈ H²((ℝ / pℤ) × Y_φ; ℤ)` differs from
`m • pr₂^* v + c • (pr₁^* θ_p ⌣ pr₂^* a)` by an element of finite order, for some integers `m`
and `c`, where `θ_p` is the angular class of the circle. For `p = 1`, `θ_1 = [ds]`, and when `a`
is the class `[dt]` of the base circle of `Y_φ` the second class is `t = [ds ∧ dt]`. -/
theorem exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ)
      ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientMap ℤ (ModuleCat.of ℤ ℤ)
        uliftIntIso.hom 2 v) = 1)
    {a : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 1} (ha : ∀ c, ∃ m : ℤ, c = m • a)
    (x : (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (ModuleCat.of ℤ ℤ) 2) :
    ∃ m c : ℤ, IsOfFinAddOrder (x -
      (m • TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
          (TopCat.of (MappingTorus φ))) 2 v +
        c • (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCup ℤ
          (λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv (λ_ (ModuleCat.of ℤ ℤ)).hom 1 1 2 rfl
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst (TopCat.of (AddCircle p))
            (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p))
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
            (TopCat.of (MappingTorus φ))) 1 a))) :=
  TopCat.exists_isOfFinAddOrder_sub_smul_add_smul_addCircle (n := 1) _ _
    (fun b ↦ ⟨_, isOfFinAddOrder_sub_evalFundamentalClass_chainCoefficientMap_smul φ o hn hφ hdet
      hv b⟩)
    (fun c ↦ (ha c).imp fun m hm ↦ by rw [hm, sub_self]; exact IsOfFinAddOrder.zero) x

/-- **`pr₂^* v` and `θ_p ⌣ pr₂^* a` are independent modulo torsion.** Under the hypotheses of
`TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`, the class
`m • pr₂^* v + c • (pr₁^* θ_p ⌣ pr₂^* a)` of `H²((ℝ / pℤ) × Y_φ; ℤ)` has finite order only for
`m = c = 0`. So the two classes form a basis of `H²((ℝ / pℤ) × Y_φ; ℤ)` modulo torsion, and the
integers `m` and `c` of the decomposition are unique. -/
theorem isOfFinAddOrder_smul_add_smul_addCircleProd_iff
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ)
      ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientMap ℤ (ModuleCat.of ℤ ℤ)
        uliftIntIso.hom 2 v) = 1)
    {a : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 1} (ha : ∀ c, ∃ m : ℤ, c = m • a) (m c : ℤ) :
    IsOfFinAddOrder
      (m • TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
          (TopCat.of (MappingTorus φ))) 2 v +
        c • (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCup ℤ
          (λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv (λ_ (ModuleCat.of ℤ ℤ)).hom 1 1 2 rfl
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst (TopCat.of (AddCircle p))
            (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p))
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
            (TopCat.of (MappingTorus φ))) 1 a)) ↔
      m = 0 ∧ c = 0 := by
  have := ChartedSpace.locallyPathConnectedSpace E F
  have : PathConnectedSpace F := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  -- The generator `a` of `H¹(Y_φ; ℤ) ≅ ℤ` is nonzero, and `H¹(Y_φ; ℤ)` is torsion-free.
  obtain ⟨k, hk⟩ := ha ((cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).symm 1)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact one_ne_zero ((cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).symm.map_eq_zero_iff.1
      (hk.trans (zsmul_zero k)))
  have ha' : ∀ m : ℤ, IsOfFinAddOrder (m • a) → m = 0 := fun _ hm ↦
    (IsAddTorsionFree.zsmul_eq_zero_iff_left ha0).1 ((isOfFinAddOrder_iff_eq_zero _).1 hm)
  exact TopCat.isOfFinAddOrder_smul_add_smul_addCircle_iff (n := 1) _ _
    (fun _ hm ↦ eq_zero_of_isOfFinAddOrder_smul_of_evalFundamentalClass_eq_one φ o hn hφ hdet hv hm)
    ha' m c

end TauCeti.MappingTorus
