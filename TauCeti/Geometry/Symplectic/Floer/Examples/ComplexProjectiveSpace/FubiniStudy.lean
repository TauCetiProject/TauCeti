/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere.Hurewicz
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Chern
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Line
public import TauCeti.Geometry.Symplectic.Floer.Cap.Action
public import TauCeti.Geometry.Symplectic.Floer.Examples.ComplexProjectiveSpace.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern.Hurewicz

/-!
# The period group of complex projective space with its Fubini–Study form

Capped Hamiltonian Floer theory on a symplectic manifold `(M, σ)` takes its coefficients over the
period group `Γ = TauCeti.Floer.SphericalPeriodGroup ω c` of homomorphisms `ω` and `c` on
`H₂(M; ℤ)`, the symplectic area and the first Chern number.
`TauCeti.Geometry.Symplectic.Floer.Examples.ComplexProjectiveSpace.Basic` computes `Γ` for
complex projective space and arbitrary homomorphisms `ω` and `c`. This file takes the actual
ones on `CPᵐ = CPⁿ⁺¹`, `m ≥ 1`, with its Fubini–Study form `ω_FS`
(`TauCeti.ComplexProjectiveSpace.fubiniStudyForm`): the area is the integral of `ω_FS`
(`TauCeti.homologySphereIntegralHom`), and the first Chern number is the clutching number of the
tangent bundle with an almost complex structure tamed by `ω_FS`
(`TauCeti.SmoothTwoForm.IsNondegenerate.homologyFirstChernHom`).

* **The periods of a line.** On the Hurewicz class of the coordinate line
  `TauCeti.ComplexProjectiveSpace.lineSquare n` of `CPⁿ⁺¹` the area is `1`
  (`ComplexProjectiveSpace.homologySphereIntegralHom_fubiniStudyForm_hurewiczIntHom_lineSquare`,
  from `TauCeti.ComplexProjectiveSpace.sphereIntegral_fubiniStudyForm_lineSquare`) and the first
  Chern number is `m + 1 = n + 2`
  (`TauCeti.ComplexProjectiveSpace.homologyFirstChernHom_fubiniStudyForm_hurewiczIntHom_lineSquare`,
  from `TauCeti.ComplexProjectiveSpace.firstChernHom_fubiniStudyForm_apply_mk_lineSquare`).
* **Monotonicity.** Since the class of a line generates `H₂(CPᵐ; ℤ)`, the area of every class is
  its first Chern number divided by `m + 1`
  (`TauCeti.ComplexProjectiveSpace.homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul`): `CPᵐ`
  with `ω_FS` is spherically monotone with monotonicity constant `1 / (m + 1)`.
* **The period group.** The generator `ℓ` of `Γ`, the class of the generator of `π₂(CPᵐ)`, which
  is the class of the coordinate line
  (`TauCeti.Floer.SphericalPeriodGroup.projectiveSpaceGenerator_eq_ofHomotopyGroup_lineSquare`),
  has area `1` and first Chern number `m + 1`
  (`TauCeti.Floer.SphericalPeriodGroup.area_projectiveSpaceGenerator_fubiniStudyForm`,
  `TauCeti.Floer.SphericalPeriodGroup.chern_projectiveSpaceGenerator_fubiniStudyForm`), hence
  degree `2 (m + 1)`. Area and first Chern number are injective on `Γ`
  (`TauCeti.Floer.SphericalPeriodGroup.area_injective_projectiveSpace_fubiniStudyForm`,
  `TauCeti.Floer.SphericalPeriodGroup.chern_injective_projectiveSpace_fubiniStudyForm`), and `ℓ`
  is the positive Chern generator
  (`TauCeti.Floer.SphericalPeriodGroup.chernEquivInt_projectiveSpaceGenerator_fubiniStudyForm`):
  `Γ = ℤ ℓ` with `c₁(ℓ) = m + 1`, the minimal Chern number of `CPᵐ`. Since both periods of `ℓ`
  are nonzero, the results of
  `TauCeti.Geometry.Symplectic.Floer.Examples.ComplexProjectiveSpace.Basic` for nonvanishing
  periods apply: the class map `H₂(CPᵐ; ℤ) → Γ` and the coefficient comparison are bijective, and
  any two cap classes of a loop differ by a unique multiple of `ℓ`.
* **Laurent coefficients.** The Floer Novikov ring is the ring of formal Laurent series in the
  variable `X = e^(-ℓ)`
  (`NovikovRing.toLaurentSeries_single_neg_zsmul_projectiveSpaceGenerator_fubiniStudyForm`),
  of raw degree `-2 (m + 1)` and valuation `ω_FS(ℓ) = 1`.
* **The coefficient comparison `q^A ↦ e^(-A)`.** The comparison from the Novikov ring indexed by
  the class group `H₂(CPᵐ; ℤ)` of genus-zero Gromov–Witten theory to the Floer Novikov ring sends
  `q^(k L)`, for `L` the class of the coordinate line, to `X^k`
  (`TauCeti.Floer.NovikovRing.toLaurentSeries_coefficientComparison_lineSquare_single`). For
  `k = 1` this is `q^L ↦ X`, the coefficient of the quantum relation `x^(m+1) = q^L` of `CPᵐ`.
* **Recapping at a line.** Recapping a cap class of a loop in `CPᵐ` by `k • ℓ` lowers its capped
  action for `ω_FS` by exactly `k`
  (`TauCeti.Floer.SphericalCapClass.action_zsmul_projectiveSpaceGenerator_fubiniStudyForm_vadd`);
  in particular a cap class is determined by its capped action
  (`TauCeti.Floer.SphericalCapClass.action_injective_projectiveSpace_fubiniStudyForm`).

For `m = 1` these are the data of `TauCeti.Geometry.Symplectic.Floer.Examples.RiemannSphere`,
there for the Riemann sphere `OnePoint ℂ` and its own Fubini–Study form.

## Main results

* `TauCeti.ComplexProjectiveSpace.homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul`: on
  `H₂(CPⁿ⁺¹; ℤ)` the Fubini–Study area is the first Chern number divided by `n + 2`.
* `TauCeti.Floer.SphericalPeriodGroup.chernEquivInt_projectiveSpaceGenerator_fubiniStudyForm`:
  the period group of `CPⁿ⁺¹` is `ℤ`, generated by the class of a line, of Chern number `n + 2`.
* `TauCeti.Floer.NovikovRing.toLaurentSeries_coefficientComparison_lineSquare_single`: the
  comparison `q^A ↦ e^(-A)` sends `q^(k L)` to the Laurent monomial `X^k`.
* `TauCeti.Floer.SphericalCapClass.action_zsmul_projectiveSpaceGenerator_fubiniStudyForm_vadd`:
  recapping by `k` lines lowers the capped action by `k`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 11.1 (the Novikov ring and the quantum cohomology of `CPⁿ`).
-/

public section

noncomputable section

open AlgebraicTopology HomotopyGroup Metric
open scoped Manifold Topology Topology.Homotopy

namespace TauCeti

variable {n : ℕ}

/-- The integral of the Fubini–Study form on `H₂(CPⁿ⁺¹; ℤ)`. -/
local notation "ω_FS" =>
  homologySphereIntegralHom (ComplexProjectiveSpace.isSmoothForm_fubiniStudyForm (n + 1))
    (ComplexProjectiveSpace.mextDeriv_fubiniStudyForm (n + 1))

/-- The first Chern number of the Fubini–Study form on `H₂(CPⁿ⁺¹; ℤ)`. -/
local notation "c₁_FS" =>
  SmoothTwoForm.IsNondegenerate.homologyFirstChernHom
    (SmoothTwoForm.IsSymplectic.isNondegenerate
      (ComplexProjectiveSpace.isSymplectic_fubiniStudyForm (n := n + 1)))

/-- The Hurewicz class in `H₂(CPⁿ⁺¹; ℤ)` of the coordinate line. -/
local notation "lineH₂" =>
  hurewiczIntHom (ComplexProjectiveSpace (n + 1)) (ComplexProjectiveSpace.affineParam 1 0) 1
    (Additive.ofMul (⟦ComplexProjectiveSpace.lineSquare n⟧ :
      π_ 2 (ComplexProjectiveSpace (n + 1)) (ComplexProjectiveSpace.affineParam 1 0)))

/-- The class of the generator of `π₂(CPⁿ⁺¹)` in the period group of the Fubini–Study form. -/
local notation "ℓ" =>
  Floer.SphericalPeriodGroup.projectiveSpaceGenerator ω_FS c₁_FS
    (ComplexProjectiveSpace.affineUnitVector 1 0) (Nat.add_one_ne_zero n)

namespace ComplexProjectiveSpace

/-- **A line has Fubini–Study area `1`** on `H₂(CPⁿ⁺¹; ℤ)`. -/
theorem homologySphereIntegralHom_fubiniStudyForm_hurewiczIntHom_lineSquare :
    ω_FS lineH₂ = 1 := by
  rw [homologySphereIntegralHom_hurewiczIntHom, sphereIntegralHom_apply]
  exact sphereIntegral_fubiniStudyForm_lineSquare

/-- **A line of `CPⁿ⁺¹` has first Chern number `n + 2`** on `H₂(CPⁿ⁺¹; ℤ)`. -/
theorem homologyFirstChernHom_fubiniStudyForm_hurewiczIntHom_lineSquare :
    c₁_FS lineH₂ = n + 2 := by
  rw [SmoothTwoForm.IsNondegenerate.homologyFirstChernHom_hurewiczIntHom,
    firstChernHom_fubiniStudyForm_apply_mk_lineSquare]

end ComplexProjectiveSpace

namespace Floer

open NovikovSeries PeriodGroup ComplexProjectiveSpace

namespace SphericalPeriodGroup

/-- **The generator of the period group of `CPⁿ⁺¹` has Fubini–Study area `1`.** Not a simp lemma:
simp already rewrites its left-hand side by `SphericalPeriodGroup.area_projectiveSpaceGenerator`,
and then evaluates it by
`ComplexProjectiveSpace.sphereIntegral_fubiniStudyForm_pi2MulEquivInt_symm_ofAdd_one`. -/
theorem area_projectiveSpaceGenerator_fubiniStudyForm : PeriodGroup.area _ _ ℓ = 1 := by
  rw [projectiveSpaceGenerator_eq_ofHomotopyGroup_lineSquare, area_ofHomotopyGroup]
  exact homologySphereIntegralHom_fubiniStudyForm_hurewiczIntHom_lineSquare

/-- **The generator of the period group of `CPⁿ⁺¹` has first Chern number `n + 2`.** Not a simp
lemma: simp already rewrites its left-hand side by
`SphericalPeriodGroup.chern_projectiveSpaceGenerator`, and then evaluates it by
`ComplexProjectiveSpace.firstChernHom_fubiniStudyForm_apply_pi2MulEquivInt_symm_ofAdd_one`. -/
theorem chern_projectiveSpaceGenerator_fubiniStudyForm : PeriodGroup.chern _ _ ℓ = n + 2 := by
  rw [projectiveSpaceGenerator_eq_ofHomotopyGroup_lineSquare, chern_ofHomotopyGroup]
  exact homologyFirstChernHom_fubiniStudyForm_hurewiczIntHom_lineSquare

/-- **The generator of the period group of `CPⁿ⁺¹` has degree `2 (n + 2)`**, twice its first
Chern number: the Laurent variable `e^(-ℓ)` has raw degree `-2 (n + 2)`. -/
theorem degree_projectiveSpaceGenerator_fubiniStudyForm :
    PeriodGroup.degree _ _ ℓ = 2 * (n + 2) := by
  rw [degree_apply, chern_projectiveSpaceGenerator_fubiniStudyForm]

/-- The generator of the period group of `CPⁿ⁺¹` has positive first Chern number. -/
theorem chern_projectiveSpaceGenerator_fubiniStudyForm_pos : 0 < PeriodGroup.chern _ _ ℓ := by
  rw [chern_projectiveSpaceGenerator_fubiniStudyForm]
  positivity

end SphericalPeriodGroup

end Floer

namespace ComplexProjectiveSpace

open Floer Floer.SphericalPeriodGroup

/-- **`CPⁿ⁺¹` is spherically monotone with constant `1 / (n + 2)`.** For the Fubini–Study form,
the symplectic area of every class of `H₂(CPⁿ⁺¹; ℤ)` is its first Chern number divided by
`n + 2`. -/
theorem homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul
    (A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (ComplexProjectiveSpace (n + 1)))) :
    ω_FS A = (n + 2 : ℝ)⁻¹ * c₁_FS A := by
  have h := area_eq_mul_chern_projectiveSpace (affineUnitVector 1 0) (Nat.add_one_ne_zero n)
    chern_projectiveSpaceGenerator_fubiniStudyForm_pos.ne' ⟨A, by simp⟩
  rw [area_projectiveSpaceGenerator_fubiniStudyForm, chern_projectiveSpaceGenerator_fubiniStudyForm]
    at h
  simpa using h

end ComplexProjectiveSpace

namespace Floer

open NovikovSeries PeriodGroup ComplexProjectiveSpace

namespace SphericalPeriodGroup

/-- **On the period group of `CPⁿ⁺¹`, area is the first Chern number divided by `n + 2`**, for the
Fubini–Study form and its first Chern number. -/
theorem area_eq_inv_mul_chern_projectiveSpace_fubiniStudyForm
    (γ : SphericalPeriodGroup ω_FS c₁_FS) :
    PeriodGroup.area _ _ γ = (n + 2 : ℝ)⁻¹ * PeriodGroup.chern _ _ γ :=
  PeriodGroup.area_eq_mul_chern (ω := AddMonoidHom.comp ω_FS (sphericalClasses _ 1).subtype)
    (c := AddMonoidHom.comp c₁_FS (sphericalClasses _ 1).subtype)
    (fun s ↦ homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul (n := n) s) γ

/-- **On the period group of `CPⁿ⁺¹`, the first Chern number is injective**, for the Fubini–Study
form: a class of the period group is determined by its first Chern number. -/
theorem chern_injective_projectiveSpace_fubiniStudyForm :
    Function.Injective (PeriodGroup.chern _ _ : SphericalPeriodGroup ω_FS c₁_FS →+ ℤ) :=
  PeriodGroup.chern_injective_of_area_eq_mul_chern
    fun s ↦ homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul (n := n) s

/-- **On the period group of `CPⁿ⁺¹`, area is injective**, for the Fubini–Study form: a class of
the period group is determined by its area. -/
theorem area_injective_projectiveSpace_fubiniStudyForm :
    Function.Injective (PeriodGroup.area _ _ : SphericalPeriodGroup ω_FS c₁_FS →+ ℝ) :=
  PeriodGroup.area_injective_of_area_eq_mul_chern
    (fun s ↦ homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul (n := n) s) (by positivity)

/-- **The class of a line in the period group.** The Hurewicz class of the coordinate line of
`CPⁿ⁺¹` is sent to the generator `ℓ`. Not a simp lemma: simp already rewrites its left-hand side
by `SphericalPeriodGroup.ofSingularHomology_hurewiczIntHom`. -/
theorem ofSingularHomology_hurewiczIntHom_lineSquare :
    ofSingularHomology ω_FS c₁_FS (sphericalClasses_eq_top_of_simplyConnectedSpace _) lineH₂ =
      ℓ := by
  rw [ofSingularHomology_hurewiczIntHom, projectiveSpaceGenerator_eq_ofHomotopyGroup_lineSquare]

/-- On `CPⁿ⁺¹`, every spherical class of vanishing first Chern number has vanishing Fubini–Study
area, the hypothesis of the integer coordinates `TauCeti.Floer.PeriodGroup.chernEquivInt`. -/
theorem ker_chern_le_ker_area_projectiveSpace_fubiniStudyForm :
    (AddMonoidHom.comp c₁_FS (sphericalClasses (ComplexProjectiveSpace (n + 1)) 1).subtype).ker ≤
      (AddMonoidHom.comp ω_FS (sphericalClasses (ComplexProjectiveSpace (n + 1)) 1).subtype).ker :=
  ker_le_ker_of_area_eq_mul_chern
    fun s ↦ homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul (n := n) s

/-- On `CPⁿ⁺¹` the first Chern number does not vanish on spherical classes. -/
theorem chern_ne_zero_projectiveSpace_fubiniStudyForm :
    AddMonoidHom.comp c₁_FS (sphericalClasses (ComplexProjectiveSpace (n + 1)) 1).subtype ≠ 0 :=
  fun h ↦ chern_projectiveSpaceGenerator_fubiniStudyForm_pos.ne' <| by
    rw [projectiveSpaceGenerator_eq_ofHomotopyGroup_lineSquare, chern_ofHomotopyGroup]
    exact DFunLike.congr_fun h ⟨_, hurewiczIntHom_mem_sphericalClasses _ _⟩

/-- **The class of a line is the positive Chern generator** of the period group of `CPⁿ⁺¹`: its
integer coordinate is `1`, so `Γ = ℤ ℓ` and the minimal Chern number is `n + 2`. -/
theorem chernEquivInt_projectiveSpaceGenerator_fubiniStudyForm :
    chernEquivInt ker_chern_le_ker_area_projectiveSpace_fubiniStudyForm
      chern_ne_zero_projectiveSpace_fubiniStudyForm ℓ = 1 :=
  chernEquivInt_projectiveSpaceGenerator _ _ _ _
    chern_projectiveSpaceGenerator_fubiniStudyForm_pos

end SphericalPeriodGroup

open SphericalPeriodGroup

namespace NovikovRing

/-- **Laurent coefficients of `CPⁿ⁺¹`.** The Laurent coordinates of the Floer Novikov ring of
`CPⁿ⁺¹` with its Fubini–Study form, for the monotonicity constant `1 / (n + 2)`, send the monomial
`e^(-k ℓ)` to `X^k`: the Laurent variable `X` is `e^(-ℓ)`, of raw degree `-2 (n + 2)` and
valuation `1`. -/
theorem toLaurentSeries_single_neg_zsmul_projectiveSpaceGenerator_fubiniStudyForm {R : Type*}
    [Semiring R] (k : ℤ) (r : R) :
    NovikovRing.toLaurentSeries (ω := AddMonoidHom.comp ω_FS (sphericalClasses _ 1).subtype)
        (c := AddMonoidHom.comp c₁_FS (sphericalClasses _ 1).subtype)
        (fun s ↦ homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul (n := n) s)
        chern_ne_zero_projectiveSpace_fubiniStudyForm (by positivity) (single (-(k • ℓ)) r) =
      HahnSeries.single k r :=
  NovikovRing.toLaurentSeries_single_neg_zsmul_projectiveSpaceGenerator _ _ _ _ _
    chern_projectiveSpaceGenerator_fubiniStudyForm_pos k r

/-- **The comparison `q^A ↦ e^(-A)` in Laurent coordinates on `CPⁿ⁺¹`.** The comparison out of
the Novikov ring indexed by `H₂(CPⁿ⁺¹; ℤ)` sends the monomial `q^(k L)` of the class `L` of the
coordinate line to the Laurent monomial `X^k`. For `k = 1` this is `q^L ↦ X`, the coefficient of
the quantum relation `x^(n+2) = q^L` of `CPⁿ⁺¹`. -/
theorem toLaurentSeries_coefficientComparison_lineSquare_single {R : Type*}
    [Semiring R] (k : ℤ) (r : R) :
    NovikovRing.toLaurentSeries (ω := AddMonoidHom.comp ω_FS (sphericalClasses _ 1).subtype)
        (c := AddMonoidHom.comp c₁_FS (sphericalClasses _ 1).subtype)
        (fun s ↦ homologySphereIntegralHom_fubiniStudyForm_eq_inv_mul (n := n) s)
        chern_ne_zero_projectiveSpace_fubiniStudyForm (by positivity)
        (coefficientComparison
          (ofSingularHomology ω_FS c₁_FS (sphericalClasses_eq_top_of_simplyConnectedSpace _))
          (area_ofSingularHomology (sphericalClasses_eq_top_of_simplyConnectedSpace _))
          (single (k • lineH₂) r)) =
      HahnSeries.single k r := by
  rw [coefficientComparison_single, map_zsmul, ofSingularHomology_hurewiczIntHom_lineSquare]
  exact toLaurentSeries_single_neg_zsmul_projectiveSpaceGenerator_fubiniStudyForm k r

end NovikovRing

namespace SphericalCapClass

variable {x : ComplexProjectiveSpace (n + 1)} {γ : Ω (ComplexProjectiveSpace (n + 1)) x}

/-- **On `CPⁿ⁺¹` a cap class is determined by its action.** For the Fubini–Study form, its first
Chern number and any time-dependent Hamiltonian, the capped action is injective on the cap classes
of a loop with a smooth based cap. -/
theorem action_injective_projectiveSpace_fubiniStudyForm
    (Ham : ℝ → ComplexProjectiveSpace (n + 1) → ℝ)
    (h : ∃ u, IsSmoothBasedCap 𝓘(ℝ, Fin (n + 1) → ℂ) γ u) :
    Function.Injective (action (c := c₁_FS) (isSmoothForm_fubiniStudyForm (n + 1))
      (mextDeriv_fubiniStudyForm (n + 1)) (homologySphereIntegralHom_hurewiczIntHom _ _ x) Ham
      h) :=
  action_injective _ Ham h area_injective_projectiveSpace_fubiniStudyForm

/-- **The action of recapping at a line.** For every time-dependent Hamiltonian, recapping a cap
class of a loop in `CPⁿ⁺¹` by `k` lines lowers its capped action for the Fubini–Study form by
exactly `k`. -/
theorem action_zsmul_projectiveSpaceGenerator_fubiniStudyForm_vadd
    (Ham : ℝ → ComplexProjectiveSpace (n + 1) → ℝ)
    (h : ∃ u, IsSmoothBasedCap 𝓘(ℝ, Fin (n + 1) → ℂ) γ u) (k : ℤ)
    (q : SphericalCapClass ω_FS c₁_FS γ) :
    action _ _ (homologySphereIntegralHom_hurewiczIntHom _ _ x) Ham h (k • ℓ +ᵥ q) =
      -k + action _ _ (homologySphereIntegralHom_hurewiczIntHom _ _ x) Ham h q := by
  rw [action_vadd, map_zsmul, area_projectiveSpaceGenerator_fubiniStudyForm, zsmul_eq_mul,
    mul_one]

end SphericalCapClass

end Floer

end TauCeti
