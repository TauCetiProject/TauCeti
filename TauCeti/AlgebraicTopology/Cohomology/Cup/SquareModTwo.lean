/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Data.ZMod.Four

/-!
# The cup square of a degree-one class mod two

For a space `X` and a class `w ∈ H¹(X; 𝔽₂)`, the cup square `w ⌣ w ∈ H²(X; 𝔽₂)` is the
Bockstein of `w` for the coefficient sequence `0 ⟶ ℤ/2 ⟶ ℤ/4 ⟶ ℤ/2 ⟶ 0`, that is, the first
Steenrod square `Sq¹ w`. On cochains this is a computation on one singular `2`-simplex `σ`: lift a
mod-two cocycle `x` to the `ℤ/4`-valued cochain `x'` with values in `{0, 1}`; if `x` takes the
values `a`, `b`, `c` on the edges `δ 0 σ`, `δ 1 σ`, `δ 2 σ`, then `a + c = b` in `𝔽₂`, and
`x'(δ 0 σ) - x'(δ 1 σ) + x'(δ 2 σ)` is `2` exactly when `a = c = 1` and `0` otherwise, which is
twice the value `c a = (x ⌣ x)(σ)` of the cup square. So if `x ⌣ x` is the coboundary of a mod-two
cochain `y`, the cochain `x' + 2 y'` is a `ℤ/4`-valued cocycle reducing to `x`: a degree-one class
with vanishing cup square lifts to `H¹(X; ℤ/4)`.

When `H₁(X; ℤ)` is killed by `2` no class of `H¹(X; 𝔽₂)` other than `0` lifts. By the universal
coefficient theorem in degree one, where `H₀(X; ℤ)` is free, `H¹(X; M)` is
`Hom(H₁(X; ℤ), M)` for every abelian group `M`, compatibly with changing `M`. A homomorphism from a
group killed by `2` to `ℤ/4` takes values in `{0, 2}`, so its reduction mod two vanishes. Hence on
such a space the cup square `H¹(X; 𝔽₂) → H²(X; 𝔽₂)` vanishes only at `0`
(`TopCat.singularCup_self_eq_zero_iff_of_two_smul_eq_zero`). This is the computation behind the
mod-two cup length of the real projective plane, where `H₁(ℝP²; ℤ) = ℤ/2`.

The cohomology `H*(X; 𝔽₂)` here is that of singular chains with coefficients in `𝔽₂`, with the
cup product along the unitors of `ModuleCat 𝔽₂`, as in the cup length
`TauCeti.lsCupLength X (ZMod 2)`; the `ℤ/4` cohomology is that of integral chains.

## Main results

* `TopCat.singularCup_self_eq_zero_iff_of_two_smul_eq_zero`: if `H₁(X; ℤ)` is killed by `2`, a
  class `w ∈ H¹(X; 𝔽₂)` has `w ⌣ w = 0` only when `w = 0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.E (Bockstein homomorphisms) and Section 4.L (`Sq¹` is the Bockstein, and
  `Sq¹ w = w ⌣ w` in degree one).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace TopCat

variable (X : TopCat.{0})

/-- The lifting step: let `x` be a mod-two `1`-cocycle of `X`, given by its values on singular
`1`-simplices, whose cup square is the coboundary of the mod-two `1`-cochain with values `y`. If
`H₁(X; ℤ)` is killed by `2`, then `x` is the coboundary of a mod-two `0`-cochain. The cochain
`x' + 2 y'` is an integral `ℤ/4`-valued cocycle reducing to `x`; its class reduces to `0` by the
universal coefficient theorem in degree one. -/
private lemma exists_sub_eq_of_two_smul_eq_zero
    (h2 : ∀ c : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj X, (2 : ℤ) • c = 0)
    (x y : (toSSet.obj X) _⦋1⦌ → ZMod 2)
    (hx : ∀ σ, x ((toSSet.obj X).δ 0 σ) - x ((toSSet.obj X).δ 1 σ) + x ((toSSet.obj X).δ 2 σ) = 0)
    (hy : ∀ σ, y ((toSSet.obj X).δ 0 σ) - y ((toSSet.obj X).δ 1 σ) + y ((toSSet.obj X).δ 2 σ) =
      x ((toSSet.obj X).δ 2 σ) * x ((toSSet.obj X).δ 0 σ)) :
    ∃ u : (toSSet.obj X) _⦋0⦌ → ZMod 2,
      ∀ τ, u ((toSSet.obj X).δ 0 τ) - u ((toSSet.obj X).δ 1 τ) = x τ := by
  -- The universal coefficient theorem below uses the `ℤ`-linear structure of `ModuleCat ℤ` as a
  -- module category; instance search would choose the one of a preadditive category instead.
  let : Linear ℤ (ModuleCat.{0} ℤ) := ModuleCat.instLinear
  -- The integral `ℤ/4`-valued cochain `x' + 2 y'` is a cocycle.
  obtain ⟨z, hz⟩ : ∃ z : (X.singularCochainComplex (ModuleCat.of ℤ ℤ) ℤ
      (ModuleCat.of ℤ (ZMod 4))).X 1, ∀ τ,
      TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) (toSSet.obj X) 1 z τ =
        ZMod.cast (x τ) + 2 * ZMod.cast (y τ) :=
    ⟨(TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) (toSSet.obj X) 1).symm
      fun τ ↦ ZMod.cast (x τ) + 2 * ZMod.cast (y τ), fun τ ↦ by rw [LinearEquiv.apply_symm_apply]⟩
  have hdz : (X.singularCochainComplex (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ (ZMod 4))).d 1 2 z =
      0 := by
    refine (TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) (toSSet.obj X) 2).injective
      (funext fun σ ↦ (TauCeti.cochainValuesEquiv_d_two_one ℤ _ (toSSet.obj X) _ σ).trans ?_)
    rw [hz, hz, hz]
    exact (ZMod.cast_add_two_mul_cast_sub_add_eq_zero (hx σ) (hy σ)).trans (congrFun (map_zero
      (TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) (toSSet.obj X) 2)) σ).symm
  let ρ : ModuleCat.of ℤ (ZMod 4) ⟶ ModuleCat.of ℤ (ZMod 2) :=
    ModuleCat.ofHom (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toIntLinearMap
  let zc := (X.singularCochainComplex (ModuleCat.of ℤ ℤ) ℤ
    (ModuleCat.of ℤ (ZMod 4))).moduleCatCyclesMk z 2 (CochainComplex.next ℕ 1) hdz
  -- Its class reduces to `0` mod two: the Kronecker map is injective in degree one, and the
  -- reduction of a homomorphism `H₁(X; ℤ) ⟶ ℤ/4` vanishes, since `H₁(X; ℤ)` is killed by `2`.
  have hρ : HomologicalComplex.homologyMap
      (((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObjMap ℤ ρ) 1
      ((X.singularCochainComplex (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ (ZMod 4))).homologyπ 1 zc) =
      0 := by
    refine (X.singularKronecker_bijective_of_projective_homology_lt (ModuleCat.of ℤ (ZMod 2)) 1
      fun j hj ↦ ?_).1 ?_
    · obtain rfl : j = 0 := by omega
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ _)
    refine ((singularKronecker_coefficient_naturality X ℤ ρ 1 _).trans ?_).trans
      (map_zero (X.singularKronecker ℤ 1)).symm
    ext c
    refine ZMod.castHom_eq_zero_of_two_smul_eq_zero ?_
    rw [← map_zsmul, h2 c, map_zero]
  -- So the reduction `x` of `x' + 2 y'` is the coboundary of an integral mod-two cochain `u`.
  rw [ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply] at hρ
  obtain ⟨u, hu⟩ := (HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _
    (CochainComplex.prev_nat_succ 0) _).1 hρ
  refine ⟨TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 2)) (toSSet.obj X) 0 u, fun τ ↦ ?_⟩
  have hu' := congrArg (fun φ ↦ TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 2))
    (toSSet.obj X) 1 (((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ
      (ModuleCat.of ℤ (ZMod 2)) |>.iCycles 1 φ) τ) hu
  simp only [TauCeti.ChainComplex.linearYonedaObj_iCycles_toCycles_apply,
    ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply] at hu'
  refine (TauCeti.cochainValuesEquiv_d_one_zero ℤ _ (toSSet.obj X) _ τ).symm.trans
    (hu'.trans ((TauCeti.cochainValuesEquiv_comp ℤ _ _ 1 _ ρ τ).trans ?_))
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, hz]
  exact ZMod.cast_cast_add_two_mul_cast _ _

/-- **The cup square of a degree-one class mod two.** If `H₁(X; ℤ)` is killed by `2`, as for the
real projective plane, a class `w ∈ H¹(X; 𝔽₂)` has `w ⌣ w = 0` only when `w = 0`. -/
theorem singularCup_self_eq_zero_iff_of_two_smul_eq_zero
    (h2 : ∀ c : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj X, (2 : ℤ) • c = 0)
    {w : X.singularCohomology (𝟙_ (ModuleCat.{0} (ZMod 2))) (ZMod 2)
      (𝟙_ (ModuleCat.{0} (ZMod 2))) 1} :
    X.singularCup (ZMod 2) (λ_ _).inv (λ_ _).hom 1 1 2 rfl w w = 0 ↔ w = 0 := by
  refine ⟨fun hw ↦ ?_, fun hw ↦ by simp [hw]⟩
  -- Write `w` as the class of a cocycle `a` and its cup square as the coboundary of `y`.
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ 1 w
  rw [singularCup_homologyπ] at hw
  obtain ⟨y, hy⟩ := (HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _
    (CochainComplex.prev_nat_succ 1) _).1 hw
  -- The values of cochains with coefficients in the unit `𝟙_ (ModuleCat 𝔽₂)` are read through
  -- `cochainValuesEquiv` at `ModuleCat.of 𝔽₂ 𝔽₂`, which is that unit by definition in Mathlib's
  -- monoidal structure on `ModuleCat 𝔽₂`.
  let e := TauCeti.cochainValuesEquiv (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) (toSSet.obj X)
  let x := (X.singularCochainComplex (𝟙_ (ModuleCat.{0} (ZMod 2))) (ZMod 2)
    (𝟙_ (ModuleCat.{0} (ZMod 2)))).iCycles 1 a
  -- Read the cocycle condition of `x` and `x ⌣ x = d y` on values, and apply the lifting step.
  have hx (σ : (toSSet.obj X) _⦋2⦌) : e 1 x ((toSSet.obj X).δ 0 σ) -
      e 1 x ((toSSet.obj X).δ 1 σ) + e 1 x ((toSSet.obj X).δ 2 σ) = 0 := by
    refine (TauCeti.cochainValuesEquiv_d_two_one (ZMod 2) _ (toSSet.obj X) _ σ).symm.trans ?_
    exact (congrArg (fun φ ↦ e 2 φ σ)
      (TauCeti.ChainComplex.d_comp_linearYonedaObj_iCycles 1 2 a)).trans
      (congrFun (map_zero (e 2)) σ)
  -- `d y = x ⌣ x` as cochains.
  have hdy := (TauCeti.ChainComplex.linearYonedaObj_iCycles_toCycles_apply 1 2 y).symm.trans
    ((congrArg _ hy).trans (TauCeti.ChainComplex.iCycles_cupCycles _ _ 1 1 2 rfl a a))
  have hy' (σ : (toSSet.obj X) _⦋2⦌) : e 1 y ((toSSet.obj X).δ 0 σ) -
      e 1 y ((toSSet.obj X).δ 1 σ) + e 1 y ((toSSet.obj X).δ 2 σ) =
        e 1 x ((toSSet.obj X).δ 2 σ) * e 1 x ((toSSet.obj X).δ 0 σ) := by
    refine (TauCeti.cochainValuesEquiv_d_two_one (ZMod 2) _ (toSSet.obj X) _ σ).symm.trans ?_
    exact (congrArg (fun φ ↦ e 2 φ σ) hdy).trans
      (cochainValuesEquiv_cupCochain_one_one X (ZMod 2) _ _ σ)
  obtain ⟨u, hu⟩ := exists_sub_eq_of_two_smul_eq_zero X h2 (e 1 x) (e 1 y) hx hy'
  -- So `x` is the coboundary of the mod-two `0`-cochain with values `u`, and `w = 0`.
  refine (HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _ (CochainComplex.prev_nat_succ 0)
    _).2 ⟨(e 0).symm u, HomologicalComplex.moduleCat_iCycles_injective _ 1 ?_⟩
  refine (TauCeti.ChainComplex.linearYonedaObj_iCycles_toCycles_apply 0 1 _).trans
    ((e 1).injective (funext fun τ ↦
      (TauCeti.cochainValuesEquiv_d_one_zero (ZMod 2) _ (toSSet.obj X) _ τ).trans ?_))
  rw [LinearEquiv.apply_symm_apply]
  exact hu τ

end TopCat
