/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Constraint
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Evaluation
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey
public import TauCeti.LinearAlgebra.Determinant.Augmentation
import TauCeti.LinearAlgebra.Complex.Finrank
import TauCeti.LinearAlgebra.Prod
import TauCeti.Topology.VectorBundle.FiniteDimensional

/-!
# Point constraints on a real Cauchy–Riemann operator

Let `D` be a smooth real Cauchy–Riemann operator on a complex vector bundle `V` of complex rank `n`
over a closed Riemann surface `M`, realized as `D_p : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`. For
`p > 2` the elements of `W^{1,p}(M, V)` are continuous sections, so they can be evaluated at
points. Asking that a section take prescribed values at finitely many points `x : ι → M` is the
linearization of asking that a pseudoholomorphic curve pass through these points, when `V` is its
normal bundle. The linearized problem with these point constraints is the **incidence operator**

`D_p^x = (D_p, ev_x) : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V) × Π i, V (x i)`,
`w ↦ (D_p w, (w (x i))ᵢ)`

(`TauCeti.IsRealCauchyRiemannOperator.sobolevLIncidence`). This file develops it from the general
theory of operators extended by finitely many constraints
(`TauCeti.Analysis.Fredholm.Constraint`):

* **Fredholm theory.** `D_p^x` is Fredholm for `2 < p < ∞`
  (`TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevLIncidence`), and each point lowers the
  index by `2 n`, the real dimension of a fibre
  (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevLIncidence`).
* **Regularity.** On the kernel of `D_p` the evaluation `ev_x` is the evaluation of smooth
  sections `TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval`
  (`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval_eq_domRestrict`). So `D_p^x` is onto
  exactly when `D_p` is onto and every family of values at the points is taken by a smooth
  solution of `D ξ = 0` (`TauCeti.IsRealCauchyRiemannOperator.surjective_sobolevLIncidence_iff`),
  and it is injective exactly when no nonzero smooth solution vanishes at all the points
  (`TauCeti.IsRealCauchyRiemannOperator.injective_sobolevLIncidence_iff`). Surjectivity of `D_p^x`
  is the linearized transversality of the point constraints, which these criteria reduce to the
  values of the smooth solutions of `D ξ = 0` at the points.
* **Line bundles.** For a line bundle `L` of degree `d = c₁(L)[M] ≥ -1` with
  `2 (d + 1) ≤ ind D_p`, the index given by the Riemann–Roch theorem on the sphere, the incidence
  operator at `k ≤ d + 1` distinct points is onto
  (`TauCeti.IsRealCauchyRiemannOperator.surjective_sobolevLIncidence_of_le_index`), and its kernel
  has real dimension `2 (d + 1 - k)`
  (`TauCeti.IsRealCauchyRiemannOperator.finrank_ker_sobolevLIncidence_of_le_index`): each point
  constraint removes two real dimensions. At exactly `d + 1` distinct points it is bijective
  (`TauCeti.IsRealCauchyRiemannOperator.bijective_sobolevLIncidence_of_le_index`).
* **The incidence orientation map.** When `D_p^x` is bijective, the determinant line of `D_p` is
  identified with the determinant line of `Π i, V (x i)`
  (`TauCeti.IsRealCauchyRiemannOperator.sobolevLDetLineEquivPi`), by sending an exterior product
  of kernel elements to the exterior product of their values at the points
  (`TauCeti.IsRealCauchyRiemannOperator.coe_sobolevLDetLineEquivPi_tmul`). Comparing an
  orientation of `det D_p` with the complex orientation of the fibres through it is the sign with
  which a curve through the points is counted.

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.sobolevLIncidence`: the incidence operator `(D_p, ev_x)`.
* `TauCeti.IsRealCauchyRiemannOperator.sobolevLDetLineEquivPi`: for a bijective incidence
  operator, the isomorphism `det D_p ≃ det (Π i, V (x i))`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevLIncidence`:
  `ind D_p^x = ind D_p - 2 n · #ι`.
* `TauCeti.IsRealCauchyRiemannOperator.surjective_sobolevLIncidence_iff`: regularity of the
  constrained problem through the evaluation of smooth kernel elements.
* `TauCeti.IsRealCauchyRiemannOperator.bijective_sobolevLIncidence_of_le_index`: on a line bundle
  of degree `d` with `2 (d + 1) ≤ ind D_p`, the incidence operator at `d + 1` distinct points is
  bijective.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications 52 (2012), Section 3.4 (evaluation maps) and Appendix A.2
  (determinant lines).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (curves through fixed points and their signs).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set Function
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

namespace IsRealCauchyRiemannOperator

section Incidence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannIncidence : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The incidence operator.** When the elements of `W^{1,p}(M, V)` have continuous
representatives, as they do for `p > 2`
(`TauCeti.SobolevSection.HasContinuousRepresentatives.of_two_lt_mul`), this is the realization
`W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` of `D` extended by the evaluation of the continuous
representative at points `x : ι → M`: `w ↦ (D_p w, (w (x i))ᵢ)`. It is the linearization of the
Cauchy–Riemann equation with the constraint of passing through the points. -/
def sobolevLIncidence (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) {ι : Type*}
    (x : ι → M) :
    SobolevSection A volume p 1 →L[ℝ] zeroOneSobolevSections A volume p 0 × Π i, V (x i) :=
  (hD.sobolevL A hDs volume p).prod (ContinuousLinearMap.pi fun i ↦ SobolevSection.evalL hc (x i))

@[simp]
theorem sobolevLIncidence_apply (hc : SobolevSection.HasContinuousRepresentatives A volume p 1)
    {ι : Type*} (x : ι → M) (w : SobolevSection A volume p 1) :
    sobolevLIncidence A hD hDs hc x w =
      (hD.sobolevL A hDs volume p w, fun i ↦ SobolevSection.toSection w (x i)) := by
  simp [sobolevLIncidence]

/-- The evaluation of a kernel element at the points is the evaluation of its continuous
representative. -/
theorem kerSobolevLEval_apply_eq_toSection (hp : 1 < p) {ι : Type*} (x : ι → M)
    (w : (hD.sobolevL A hDs volume p).ker) (i : ι) :
    kerSobolevLEval A hD hDs hp x w i =
      SobolevSection.toSection (w : SobolevSection A volume p 1) (x i) := by
  set t := (kerSobolevLEquivComap A hD hDs hp).symm w
  have hw : (w : SobolevSection A volume p 1) =
      SobolevSection.ofContMDiffSection A volume p 1
        (t : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); F, V⟯) := by
    rw [← coe_kerSobolevLEquivComap_apply A hD hDs hp, LinearEquiv.apply_symm_apply]
  rw [kerSobolevLEval_apply_eq_kerSobolevLEquivComap_symm, hw,
    SobolevSection.toSection_ofContMDiffSection]

/-- **The constraint map on the kernel is the evaluation of smooth kernel elements.** The
restriction of the point evaluation of `W^{1,p}(M, V)` to the kernel of `D_p` is
`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEval`. -/
theorem kerSobolevLEval_eq_domRestrict (hp : 1 < p)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) {ι : Type*} (x : ι → M) :
    kerSobolevLEval A hD hDs hp x =
      ((ContinuousLinearMap.pi fun i ↦ SobolevSection.evalL hc (x i)) :
          SobolevSection A volume p 1 →ₗ[ℝ] Π i, V (x i)).domRestrict
        (hD.sobolevL A hDs volume p).ker := by
  ext w i
  simp [kerSobolevLEval_apply_eq_toSection]

/-- **Regularity of the constrained problem.** The incidence operator is onto exactly when `D_p` is
onto and every family of values at the points is the family of values of a smooth solution of
`D ξ = 0`. -/
theorem surjective_sobolevLIncidence_iff (hp : 1 < p)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) {ι : Type*} (x : ι → M) :
    Surjective (sobolevLIncidence A hD hDs hc x) ↔
      Surjective (hD.sobolevL A hDs volume p) ∧ Surjective (kerSobolevLEval A hD hDs hp x) := by
  rw [sobolevLIncidence, ContinuousLinearMap.surjective_prod_iff,
    kerSobolevLEval_eq_domRestrict A hD hDs hp hc]
  rfl

/-- The incidence operator is injective exactly when no nonzero element of the kernel of `D_p`, a
smooth solution of `D ξ = 0`, vanishes at all the points. -/
theorem injective_sobolevLIncidence_iff (hp : 1 < p)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) {ι : Type*} (x : ι → M) :
    Injective (sobolevLIncidence A hD hDs hc x) ↔ Injective (kerSobolevLEval A hD hDs hp x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [kerSobolevLEval_eq_domRestrict A hD hDs hp hc]
    exact LinearMap.injective_domRestrict_of_injective_prod h
  · rw [← ContinuousLinearMap.coe_coe, injective_iff_map_eq_zero]
    intro w hw
    have hDw : w ∈ (hD.sobolevL A hDs volume p).ker := by
      simpa using congrArg Prod.fst hw
    -- A kernel element vanishing at all the points is zero.
    have hev : kerSobolevLEval A hD hDs hp x ⟨w, hDw⟩ = 0 := funext fun i ↦ by
      rw [kerSobolevLEval_apply_eq_toSection]
      simpa using congrFun (congrArg Prod.snd hw) i
    exact congrArg Subtype.val (h (hev.trans (map_zero _).symm))

/-- **The incidence operator is Fredholm.** For `1 < p < ∞` and finitely many points, the
incidence operator differs from `D_p` by the finite-rank evaluation, so it is Fredholm. -/
theorem isFredholm_sobolevLIncidence (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) {ι : Type*} [Finite ι]
    (x : ι → M) :
    (sobolevLIncidence A hD hDs hc x).IsFredholm := by
  have := VectorBundle.finiteDimensional_pi ℝ F V x
  have (i : ι) : T2Space (V (x i)) := FiberBundle.t2Space F V (x i)
  exact ContinuousLinearMap.isFredholm_prod_iff.2 (isFredholm_sobolevL A hD hDs hp hp_top)

/-- **Each point constraint lowers the index by the real rank.** For `1 < p < ∞` and finitely many
points, the index of the incidence operator is `ind D_p - 2 n · #ι`, where `n` is the complex rank
of `V`. -/
theorem index_sobolevLIncidence (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) {ι : Type*} [Finite ι]
    (x : ι → M) :
    (sobolevLIncidence A hD hDs hc x).index =
      (hD.sobolevL A hDs volume p).index - 2 * finrank ℂ F * Nat.card ι := by
  have := VectorBundle.finiteDimensional_pi ℝ F V x
  have := finiteDimensional_ker_sobolevL A hD hDs hp hp_top
  have := finiteDimensional_quotient_range_sobolevL A hD hDs hp hp_top
  have hfin : ((Nat.card ι * finrank ℝ F : ℕ) : ℤ) = 2 * finrank ℂ F * Nat.card ι := by
    rw [finrank_real_eq_two_mul_finrank_complex]
    push_cast
    ring
  rw [sobolevLIncidence, ContinuousLinearMap.index_prod, VectorBundle.finrank_pi ℝ F V, hfin]

end Incidence

section LineBundle

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {L : M → Type} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, ContinuousSMul ℂ (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealCauchyRiemannIncidenceLine : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

variable [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M ℂ L)
  {D : (Π x : M, L x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] L x}
  (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn ℂ ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable [CompactSpace M] [ConnectedSpace M] {d : ℤ}
  (hd : ((complexHomologicalOrientation M).evalFundamentalClass Complex.finrank_real_complex
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
    (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down = d)

include hd in
/-- On a compact connected Riemann surface, the incidence operator of a smooth real
Cauchy–Riemann operator on a complex line bundle `L` of degree `d = c₁(L)[M]`, at more than `d`
distinct points, is injective: a smooth solution of `D ξ = 0` vanishing at more than `d` points is
zero. -/
theorem injective_sobolevLIncidence (hp : 1 < p)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) {ι : Type*} {x : ι → M}
    (hx : Injective x) (hlt : d < Nat.card ι) :
    Injective (sobolevLIncidence A hD hDs hc x) :=
  (injective_sobolevLIncidence_iff A hD hDs hp hc x).2
    (kerSobolevLEval_injective A hD hDs hp hx (by rwa [hd]))

include hd in
/-- **Automatic regularity of point constraints.** On a compact connected Riemann surface, let `D`
be a smooth real Cauchy–Riemann operator on a complex line bundle `L` of degree
`d = c₁(L)[M] ≥ -1`, whose realization `W^{1,p}(M, L) → Lᵖ(M, Λ^{0,1} ⊗ L)`, `1 < p < ∞`, has
index at least `2 (d + 1)`. Then the incidence operator at at most `d + 1` distinct points is
onto. -/
theorem surjective_sobolevLIncidence_of_le_index (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) (hd₁ : -1 ≤ d)
    {ι : Type*} [Finite ι] {x : ι → M} (hx : Injective x) (hcard : Nat.card ι ≤ d + 1)
    (hind : 2 * (d + 1) ≤ (hD.sobolevL A hDs volume p).index) :
    Surjective (sobolevLIncidence A hD hDs hc x) :=
  (surjective_sobolevLIncidence_iff A hD hDs hp hc x).2
    ⟨sobolevL_surjective_of_le_index A hD hDs hd hp hp_top hd₁ hind,
      kerSobolevLEval_surjective_of_le_index A hD hDs hd hp hx hcard hind⟩

include hd in
/-- **Each point constraint removes two real dimensions.** Under the hypotheses of
`TauCeti.IsRealCauchyRiemannOperator.surjective_sobolevLIncidence_of_le_index`, the kernel of the
incidence operator at `k ≤ d + 1` distinct points, the space of smooth solutions of `D ξ = 0`
vanishing at the points, has real dimension `2 (d + 1 - k)`. -/
theorem finrank_ker_sobolevLIncidence_of_le_index (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) (hd₁ : -1 ≤ d)
    {ι : Type*} [Finite ι] {x : ι → M} (hx : Injective x) (hcard : Nat.card ι ≤ d + 1)
    (hind : 2 * (d + 1) ≤ (hD.sobolevL A hDs volume p).index) :
    (finrank ℝ (sobolevLIncidence A hD hDs hc x).ker : ℤ) = 2 * (d + 1 - Nat.card ι) := by
  have hsurj :=
    surjective_sobolevLIncidence_of_le_index A hD hDs hd hp hp_top hc hd₁ hx hcard hind
  have := (isFredholm_sobolevLIncidence A hD hDs hp hp_top hc x).finite_ker
  have hindex := index_sobolevLIncidence A hD hDs hp hp_top hc x
  have hle := index_sobolevL_le A hD hDs hd hp
  -- The cokernel of the onto incidence operator is zero, so its index is the kernel dimension.
  rw [ContinuousLinearMap.index_eq_finrank_sub,
    LinearMap.finrank_quotient_range_eq_zero_of_surjective hsurj, finrank_self] at hindex
  omega

include hd in
/-- **The incidence operator at `d + 1` points is an isomorphism.** Under the hypotheses of
`TauCeti.IsRealCauchyRiemannOperator.surjective_sobolevLIncidence_of_le_index`, the incidence
operator at exactly `d + 1` distinct points is bijective. -/
theorem bijective_sobolevLIncidence_of_le_index (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) (hd₁ : -1 ≤ d)
    {ι : Type*} [Finite ι] {x : ι → M} (hx : Injective x) (hcard : Nat.card ι = d + 1)
    (hind : 2 * (d + 1) ≤ (hD.sobolevL A hDs volume p).index) :
    Bijective (sobolevLIncidence A hD hDs hc x) :=
  ⟨injective_sobolevLIncidence A hD hDs hd hp hc hx (by omega),
    surjective_sobolevLIncidence_of_le_index A hD hDs hd hp hp_top hc hd₁ hx hcard.le hind⟩

end LineBundle

section DetLine

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannIncidenceDetLine : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The incidence orientation map.** For finitely many points at which the incidence
operator is bijective, the isomorphism `det D_p ≃ det (Π i, V (x i))` between the determinant line
of the realization of `D` and the determinant line of the fibres at the points
(`LinearMap.detLineEquivOfBijectiveProd`). It sends an exterior product of kernel elements to the
exterior product of their values at the points
(`TauCeti.IsRealCauchyRiemannOperator.coe_sobolevLDetLineEquivPi_tmul`). -/
def sobolevLDetLineEquivPi (hc : SobolevSection.HasContinuousRepresentatives A volume p 1)
    {ι : Type*} [Finite ι] (x : ι → M) (h : Bijective (sobolevLIncidence A hD hDs hc x)) :
    (hD.sobolevL A hDs volume p :
        SobolevSection A volume p 1 →ₗ[ℝ] zeroOneSobolevSections A volume p 0).detLine ≃ₗ[ℝ]
      TauCeti.detLine ℝ (Π i, V (x i)) :=
  have := VectorBundle.finiteDimensional_pi ℝ F V x
  LinearMap.detLineEquivOfBijectiveProd _ _ h

/-- **The value of the incidence orientation map.** For a family `u` of `dim (ker D_p)` kernel
elements, the exterior product of `u` tensored with `φ` goes to the exterior product of the values
`kerSobolevLEval x ∘ u` of the smooth kernel sections at the points, multiplied by the value of `φ`
on the empty exterior product `e` of the zero cokernel. So an orientation of `det D_p` agrees with
an orientation of `Π i, V (x i)` exactly when, for a basis `u` of the kernel positive for the
first, the values of `u` at the points are positive for the second. -/
theorem coe_sobolevLDetLineEquivPi_tmul (hp : 1 < p)
    (hc : SobolevSection.HasContinuousRepresentatives A volume p 1) {ι : Type*} [Finite ι]
    (x : ι → M) (h : Bijective (sobolevLIncidence A hD hDs hc x))
    (u : Fin (finrank ℝ (hD.sobolevL A hDs volume p).ker) → (hD.sobolevL A hDs volume p).ker)
    (φ : Dual ℝ (TauCeti.detLine ℝ (zeroOneSobolevSections A volume p 0 ⧸
      LinearMap.range (hD.sobolevL A hDs volume p :
        SobolevSection A volume p 1 →ₗ[ℝ] zeroOneSobolevSections A volume p 0))))
    (e : Fin (finrank ℝ (zeroOneSobolevSections A volume p 0 ⧸
      LinearMap.range (hD.sobolevL A hDs volume p :
        SobolevSection A volume p 1 →ₗ[ℝ] zeroOneSobolevSections A volume p 0))) →
      zeroOneSobolevSections A volume p 0 ⧸
        LinearMap.range (hD.sobolevL A hDs volume p :
          SobolevSection A volume p 1 →ₗ[ℝ] zeroOneSobolevSections A volume p 0)) :
    (sobolevLDetLineEquivPi A hD hDs hc x h (exteriorPower.ιMulti ℝ _ u ⊗ₜ φ) :
        ExteriorAlgebra ℝ (Π i, V (x i))) =
      φ (exteriorPower.ιMulti ℝ _ e) •
        ExteriorAlgebra.ιMulti ℝ _ (kerSobolevLEval A hD hDs hp x ∘ u) := by
  have := VectorBundle.finiteDimensional_pi ℝ F V x
  rw [kerSobolevLEval_eq_domRestrict A hD hDs hp hc]
  exact LinearMap.coe_detLineEquivOfBijectiveProd_tmul _ _ h u φ e

end DetLine

end IsRealCauchyRiemannOperator

end TauCeti
