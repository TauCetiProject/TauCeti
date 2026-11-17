/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# The cup square of a degree-one class mod two

For a space `X` and a class `w ∈ H¹(X; 𝔽₂)`, the cup square `w ⌣ w ∈ H²(X; 𝔽₂)` is the
Bockstein of `w` for the coefficient sequence `0 ⟶ ℤ/2 ⟶ ℤ/4 ⟶ ℤ/2 ⟶ 0`, that is, the first
Steenrod square `Sq¹ w`. On cochains this is a computation on one singular `2`-simplex `σ`: lift a
mod-two cocycle `x` to the `ℤ/4`-valued cochain `x'` with values in `{0, 1}`; if `x` takes the
values `a`, `b`, `c` on the edges `δ 0 σ`, `δ 1 σ`, `δ 2 σ`, then `a + c = b` in `𝔽₂`, and
`x'(δ 0 σ) - x'(δ 1 σ) + x'(δ 2 σ)` is `2` exactly when `a = c = 1` and `0` otherwise, which is
twice the value `c a = (x ⌣ x)(σ)` of the cup square. So if `x ⌣ x` is the coboundary of a mod-two
cochain `y`, the cochain `x' - 2 y'` is a `ℤ/4`-valued cocycle reducing to `x`: a degree-one class
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

section Values

variable {k : Type} [CommRing k] {M : ModuleCat.{0} k} {K : SSet.{0}}

/-- The value of the coboundary of a `1`-cochain on a `2`-simplex. -/
private lemma cochainValuesEquiv_d_comp_one (φ : (K.chainComplex (ModuleCat.of k k)).X 1 ⟶ M)
    (σ : K _⦋2⦌) :
    TauCeti.cochainValuesEquiv k M K 2 ((K.chainComplex (ModuleCat.of k k)).d 2 1 ≫ φ) σ =
      TauCeti.cochainValuesEquiv k M K 1 φ (K.δ 0 σ) -
        TauCeti.cochainValuesEquiv k M K 1 φ (K.δ 1 σ) +
        TauCeti.cochainValuesEquiv k M K 1 φ (K.δ 2 σ) := by
  refine (TauCeti.cochainValuesEquiv_d k M K 1 φ σ).trans ?_
  simp [Fin.sum_univ_three, sub_eq_add_neg]

/-- The value of the coboundary of a `0`-cochain on a `1`-simplex. -/
private lemma cochainValuesEquiv_d_comp_zero (φ : (K.chainComplex (ModuleCat.of k k)).X 0 ⟶ M)
    (σ : K _⦋1⦌) :
    TauCeti.cochainValuesEquiv k M K 1 ((K.chainComplex (ModuleCat.of k k)).d 1 0 ≫ φ) σ =
      TauCeti.cochainValuesEquiv k M K 0 φ (K.δ 0 σ) -
        TauCeti.cochainValuesEquiv k M K 0 φ (K.δ 1 σ) := by
  refine (TauCeti.cochainValuesEquiv_d k M K 0 φ σ).trans ?_
  simp [Fin.sum_univ_two, sub_eq_add_neg]

end Values

/-! ### Arithmetic in `ℤ/4` -/

/-- The value `a' - 2 b'` in `ℤ/4`, where `a'` and `b'` are the lifts of `a b : 𝔽₂` with values in
`{0, 1}`. -/
private def liftModFour (a b : ZMod 2) : ZMod 4 := (a.val : ZMod 4) - 2 * b.val

/-- The arithmetic on one `2`-simplex: if `a - b + c = 0` and `p - q + r = c a` in `𝔽₂`, the lifts
`a' - 2 p'`, `b' - 2 q'`, `c' - 2 r'` have alternating sum `0` in `ℤ/4`. -/
private lemma liftModFour_sub_add_eq_zero :
    ∀ a b c p q r : ZMod 2, a - b + c = 0 → p - q + r = c * a →
      liftModFour a p - liftModFour b q + liftModFour c r = 0 := by
  unfold liftModFour; decide

private lemma castHom_liftModFour :
    ∀ a b : ZMod 2, ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (liftModFour a b) = a := by
  unfold liftModFour; decide

/-- An element of `ℤ/4` killed by `2` reduces to `0` mod two. -/
private lemma castHom_eq_zero_of_two_smul_eq_zero :
    ∀ m : ZMod 4, (2 : ℤ) • m = 0 → ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) m = 0 := by
  decide

variable (X : TopCat.{0})

/-- The cup product of two degree-one cochains with coefficients in `𝔽₂` evaluates a singular
`2`-simplex `σ` to the product of the value of the first on the front edge `δ 2 σ` and that of the
second on the back edge `δ 0 σ`. -/
private lemma cochainValuesEquiv_cupCochain_one_one
    (φ ψ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} (ZMod 2)))).X 1 ⟶
      𝟙_ (ModuleCat.{0} (ZMod 2))) (σ : (toSSet.obj X) _⦋2⦌) :
    TauCeti.cochainValuesEquiv (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) (toSSet.obj X) 2
        (TauCeti.ChainComplex.cupCochain (ZMod 2) (X.alexanderWhitneyDiagonal (λ_ _).inv)
          (λ_ _).hom 1 1 2 rfl φ ψ) σ =
      TauCeti.cochainValuesEquiv (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) (toSSet.obj X) 1 φ
          ((toSSet.obj X).δ 2 σ) *
        TauCeti.cochainValuesEquiv (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) (toSSet.obj X) 1 ψ
          ((toSSet.obj X).δ 0 σ) := by
  have h₀ : SimplexCategory.subinterval (n := 2) 0 1 (by omega) = SimplexCategory.δ 2 := by
    ext i; fin_cases i <;> rfl
  have h₁ : SimplexCategory.subinterval (n := 2) 1 1 (by omega) = SimplexCategory.δ 0 := by
    ext i; fin_cases i <;> rfl
  simp only [TauCeti.cochainValuesEquiv_apply, SimplicialObject.δ_def]
  -- `simp` does not apply `ModuleCat.comp_apply` here, where the coefficient object is both the
  -- monoidal unit and `ModuleCat.of (ZMod 2) (ZMod 2)`, so the formula is unfolded by `rw`.
  rw [← ModuleCat.comp_apply, ιChainComplex_cupCochain_alexanderWhitneyDiagonal, h₀, h₁,
    ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
    smul_eq_mul, ModuleCat.comp_apply, ModuleCat.comp_apply]

/-- The lifting step: let `x` be a mod-two `1`-cocycle of `X`, given by its values on singular
`1`-simplices, whose cup square is the coboundary of the mod-two `1`-cochain with values `y`. If
`H₁(X; ℤ)` is killed by `2`, then `x` is the coboundary of a mod-two `0`-cochain. The cochain
`x' - 2 y'` is an integral `ℤ/4`-valued cocycle reducing to `x`; its class reduces to `0` by the
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
  -- The integral `ℤ/4`-valued cochain `x' - 2 y'` is a cocycle.
  obtain ⟨z, hz⟩ : ∃ z : (X.singularCochainComplex (ModuleCat.of ℤ ℤ) ℤ
      (ModuleCat.of ℤ (ZMod 4))).X 1, ∀ τ,
      TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) (toSSet.obj X) 1 z τ =
        liftModFour (x τ) (y τ) :=
    ⟨(TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) (toSSet.obj X) 1).symm
      fun τ ↦ liftModFour (x τ) (y τ), fun τ ↦ by rw [LinearEquiv.apply_symm_apply]⟩
  have hdz : (X.singularCochainComplex (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ (ZMod 4))).d 1 2 z =
      0 := by
    refine (TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 4)) (toSSet.obj X) 2).injective
      (funext fun σ ↦ (cochainValuesEquiv_d_comp_one _ σ).trans ?_)
    rw [hz, hz, hz]
    exact (liftModFour_sub_add_eq_zero _ _ _ _ _ _ (hx σ) (hy σ)).trans (congrFun (map_zero
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
    refine castHom_eq_zero_of_two_smul_eq_zero _ ?_
    rw [← map_zsmul, h2 c, map_zero]
  -- So the reduction `x` of `x' - 2 y'` is the coboundary of an integral mod-two cochain `u`.
  rw [ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply] at hρ
  obtain ⟨u, hu⟩ := (HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _
    (CochainComplex.prev_nat_succ 0) _).1 hρ
  refine ⟨TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 2)) (toSSet.obj X) 0 u, fun τ ↦ ?_⟩
  have hu' := congrArg (fun φ ↦ TauCeti.cochainValuesEquiv ℤ (ModuleCat.of ℤ (ZMod 2))
    (toSSet.obj X) 1 (((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ
      (ModuleCat.of ℤ (ZMod 2)) |>.iCycles 1 φ) τ) hu
  simp only [TauCeti.ChainComplex.linearYonedaObj_iCycles_toCycles_apply,
    ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply] at hu'
  refine (cochainValuesEquiv_d_comp_zero _ τ).symm.trans
    (hu'.trans ((TauCeti.cochainValuesEquiv_comp ℤ _ _ 1 _ ρ τ).trans ?_))
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, hz]
  exact castHom_liftModFour _ _

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
  let e := TauCeti.cochainValuesEquiv (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) (toSSet.obj X)
  let x := (X.singularCochainComplex (𝟙_ (ModuleCat.{0} (ZMod 2))) (ZMod 2)
    (𝟙_ (ModuleCat.{0} (ZMod 2)))).iCycles 1 a
  -- Read the cocycle condition of `x` and `x ⌣ x = d y` on values, and apply the lifting step.
  obtain ⟨u, hu⟩ := exists_sub_eq_of_two_smul_eq_zero X h2 (e 1 x) (e 1 y)
    (fun σ ↦ (cochainValuesEquiv_d_comp_one _ σ).symm.trans
      ((congrArg (fun φ ↦ e 2 φ σ)
        (TauCeti.ChainComplex.d_comp_linearYonedaObj_iCycles 1 2 a)).trans
        (congrFun (map_zero (e 2)) σ)))
    (fun σ ↦ (cochainValuesEquiv_d_comp_one _ σ).symm.trans
      ((congrArg (fun φ ↦ e 2 φ σ) ((TauCeti.ChainComplex.linearYonedaObj_iCycles_toCycles_apply
        1 2 y).symm.trans (congrArg _ hy))).trans
        ((congrArg (fun φ ↦ e 2 φ σ)
          (TauCeti.ChainComplex.iCycles_cupCycles _ _ 1 1 2 rfl a a)).trans
          (cochainValuesEquiv_cupCochain_one_one X _ _ σ))))
  -- So `x` is the coboundary of the mod-two `0`-cochain with values `u`, and `w = 0`.
  refine (HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _ (CochainComplex.prev_nat_succ 0)
    _).2 ⟨(e 0).symm u, HomologicalComplex.moduleCat_iCycles_injective _ 1 ?_⟩
  refine (TauCeti.ChainComplex.linearYonedaObj_iCycles_toCycles_apply 0 1 _).trans
    ((e 1).injective (funext fun τ ↦ (cochainValuesEquiv_d_comp_zero _ τ).trans ?_))
  rw [LinearEquiv.apply_symm_apply]
  exact hu τ

end TopCat
