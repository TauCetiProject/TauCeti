/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import TauCeti.Geometry.Manifold.SmoothSingular.Mass.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating

/-!
# Mass of smooth singular chains and comass bounds

The **mass of a smooth singular `p`-chain** `c : SmoothSimplex I M p →₀ R` with coefficients in
any seminormed abelian group `R` (such as `ℝ` or `ℤ`) is `∑ σ ∈ c.support, ‖c σ‖ * σ.mass`. We
establish its seminorm properties, Lipschitz pushforward and Riemannian isometry invariance,
`ℤ → ℝ` coefficient-change preservation (`chainMass_mapRange_intCast`,
`chainMass_intToRealSmoothChains`), barycentric subdivision non-increase
(`chainMass_subcomplexSubdivisionX_le`) and equality on injective simplices, and comass and
calibration bounds for both finitely supported chains and canonical simplicial chains with real or
integer coefficients.

## References

* H. Federer, *Geometric Measure Theory*, Springer, 1969, §4.1.7.
* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §II.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18.
-/

public section

noncomputable section

open Bundle
open CategoryTheory Convexity Set Simplicial Opposite
open scoped BigOperators ContDiff InnerProductSpace Manifold

universe u

namespace TauCeti

section Chains

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M] {p : ℕ}

/-! ### Mass of finitely supported smooth singular chains -/

section ChainMass
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {R : Type*} [SeminormedAddCommGroup R]

/-- The **mass of a smooth singular `p`-chain**: `∑ σ ∈ c.support, ‖c σ‖ * σ.mass`. -/
def chainMass (c : SmoothSimplex I M p →₀ R) : ℝ := c.sum fun σ a ↦ ‖a‖ * σ.mass

/-- Unfolding `chainMass` as a finite sum over the support. -/
theorem chainMass_eq_sum (c : SmoothSimplex I M p →₀ R) :
    chainMass c = c.sum fun σ a ↦ ‖a‖ * σ.mass := (rfl)

/-- `chainMass` may be summed over any finite set containing the support of `c`. -/
theorem chainMass_eq_sum_of_support_subset (c : SmoothSimplex I M p →₀ R)
    {s : Finset (SmoothSimplex I M p)} (hs : c.support ⊆ s) :
    chainMass c = ∑ σ ∈ s, ‖c σ‖ * σ.mass :=
  Finsupp.sum_of_support_subset c hs _ fun _ _ ↦ by simp

/-- The zero chain has mass `0`. -/
@[simp]
theorem chainMass_zero : chainMass (0 : SmoothSimplex I M p →₀ R) = 0 := by simp [chainMass]

/-- The mass of a single-simplex chain `a • σ` is `‖a‖ * σ.mass`. -/
@[simp]
theorem chainMass_single (σ : SmoothSimplex I M p) (a : R) :
    chainMass (Finsupp.single σ a) = ‖a‖ * σ.mass := Finsupp.sum_single_index (by simp)

/-- Chain mass is nonnegative. -/
theorem chainMass_nonneg (c : SmoothSimplex I M p →₀ R) : 0 ≤ chainMass c :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (SmoothSimplex.mass_nonneg _)

/-- Reversing all coefficients preserves chain mass. -/
@[simp]
theorem chainMass_neg (c : SmoothSimplex I M p →₀ R) : chainMass (-c) = chainMass c := by
  rw [chainMass_eq_sum, Finsupp.sum_neg_index (fun _ ↦ by simp)]; simp [chainMass_eq_sum]

/-- **Triangle inequality** for chain mass. -/
theorem chainMass_add_le (c d : SmoothSimplex I M p →₀ R) :
    chainMass (c + d) ≤ chainMass c + chainMass d := by
  classical
  rw [chainMass_eq_sum_of_support_subset (c + d) Finsupp.support_add,
    chainMass_eq_sum_of_support_subset c Finset.subset_union_left,
    chainMass_eq_sum_of_support_subset d Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  rw [Finsupp.add_apply, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le (c σ) (d σ)) σ.mass_nonneg

/-- Triangle inequality for the difference of two smooth chains. -/
theorem chainMass_sub_le (c d : SmoothSimplex I M p →₀ R) :
    chainMass (c - d) ≤ chainMass c + chainMass d := by
  rw [sub_eq_add_neg, ← chainMass_neg d]; exact chainMass_add_le c (-d)

/-- Triangle inequality for a finite sum of smooth chains. -/
theorem chainMass_sum_le {ι : Type*} (s : Finset ι) (c : ι → SmoothSimplex I M p →₀ R) :
    chainMass (∑ i ∈ s, c i) ≤ ∑ i ∈ s, chainMass (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (chainMass_add_le _ _).trans (add_le_add le_rfl ih)

/-- Scaling a smooth chain by `r` under a norm-multiplicative action scales mass by `‖r‖`. -/
@[simp]
theorem chainMass_smul {S : Type*} [Norm S] [SMulZeroClass S R] [NormSMulClass S R]
    (r : S) (c : SmoothSimplex I M p →₀ R) : chainMass (r • c) = ‖r‖ * chainMass c := by
  rw [chainMass_eq_sum_of_support_subset (r • c) Finsupp.support_smul, chainMass_eq_sum,
    Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ ↦ by
    simp only [Finsupp.coe_smul, Pi.smul_apply, norm_smul, mul_assoc]

/-- Scaling a smooth chain by `k : ℤ` multiplies its mass by at most `‖k‖`. -/
theorem chainMass_zsmul_le (k : ℤ) (c : SmoothSimplex I M p →₀ R) :
    chainMass (k • c) ≤ ‖k‖ * chainMass c := by
  rw [chainMass_eq_sum_of_support_subset (k • c) Finsupp.support_smul, chainMass_eq_sum,
    Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  rw [Finsupp.coe_smul, Pi.smul_apply, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_zsmul_le k (c σ)) σ.mass_nonneg

/-- Viewing an integral smooth chain as a real smooth chain preserves its mass. -/
@[simp]
theorem chainMass_mapRange_intCast (c : SmoothSimplex I M p →₀ ℤ) :
    chainMass (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero c) = chainMass c := by
  rw [chainMass_eq_sum, Finsupp.sum_mapRange_index (fun _ ↦ by simp), chainMass_eq_sum]
  exact Finset.sum_congr rfl fun σ _ ↦ by simp only [Real.norm_eq_abs, Int.norm_eq_abs]

section ChainPushforward
variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- Pushing a `p`-chain along a smooth map with `‖mfderiv f‖ ≤ C` scales mass by `≤ C ^ p`. -/
theorem chainMass_mapDomain_le [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [IsManifold J 1 N]
    [IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace J y)] {f : M → N}
    (hf : ContMDiff I J ∞ f) {C : ℝ}
    (hLip : ∀ x (v : TangentSpace I x), ‖mfderiv I J f x v‖ ≤ C * ‖v‖)
    (c : SmoothSimplex I M p →₀ R) :
    chainMass (Finsupp.mapDomain ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌)) c) ≤
      C ^ p * chainMass c := by
  rw [Finsupp.mapDomain, Finsupp.sum]
  refine (chainMass_sum_le _ _).trans ?_
  rw [chainMass_eq_sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  rw [chainMass_single, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (SmoothSimplex.mass_smoothSingularSubcomplexMap_app_le hf hLip σ) (norm_nonneg (c σ))

/-- Pushing a smooth chain forward along a smooth Riemannian isometry preserves its mass. -/
theorem chainMass_mapDomain_riemannianIsometry (Φ : RiemannianIsometry I J M N)
    (c : SmoothSimplex I M p →₀ R) :
    chainMass (Finsupp.mapDomain
        ((smoothSingularSubcomplexMap Φ Φ.toDiffeomorph.contMDiff).app (op ⦋p⦌)) c) =
      chainMass c := by
  have hinj : Function.Injective
      ((smoothSingularSubcomplexMap Φ Φ.toDiffeomorph.contMDiff).app (op ⦋p⦌)) := fun σ₁ σ₂ h ↦ by
    ext x
    have hx := congrArg (fun τ : SmoothSimplex J N p ↦ τ.toContinuousMap x) h
    simp only [SmoothSimplex.toContinuousMap_smoothSingularSubcomplexMap_app] at hx
    exact Φ.injective hx
  rw [chainMass_eq_sum, Finsupp.sum_mapDomain_index_inj hinj, chainMass_eq_sum]
  exact Finset.sum_congr rfl fun σ _ ↦ by
    dsimp only; rw [SmoothSimplex.mass_smoothSingularSubcomplexMap_riemannianIsometry]

end ChainPushforward

section ChainComass
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Comass bound for smooth chains:** `‖φ‖ ≤ C` gives `‖chainIntegral c φ‖ ≤ C * chainMass c`
for any bounded scalar action of `S` on `F`. -/
theorem norm_chainIntegral_le_mul_chainMass {S : Type*} [SeminormedRing S] [Module S F]
    [IsBoundedSMul S F] (c : SmoothSimplex I M p →₀ S) (φ : RoughForm I M F p) {C : ℝ}
    (hφ : ∀ x : M, ‖φ x‖ ≤ C) : ‖chainIntegral c φ‖ ≤ C * chainMass c := by
  rw [chainIntegral_eq_sum, chainMass_eq_sum, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ ↦ ?_)
  refine (norm_smul_le (c σ) (σ.integral φ)).trans ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (σ.norm_integral_le_mul_mass φ fun x ↦ hφ (σ.toContinuousMap x)) (norm_nonneg (c σ))

/-- **Comass bound for integral smooth chains** with values in any real normed space `F`. -/
theorem norm_chainIntegral_int_le_mul_chainMass (c : SmoothSimplex I M p →₀ ℤ)
    (φ : RoughForm I M F p) {C : ℝ} (hφ : ∀ x : M, ‖φ x‖ ≤ C) :
    ‖chainIntegral c φ‖ ≤ C * chainMass c := by
  have : IsBoundedSMul ℤ F := .of_norm_smul_le norm_zsmul_le
  exact norm_chainIntegral_le_mul_chainMass c φ hφ

/-- **Calibration bound for smooth chains:** unit comass gives
`|chainIntegral c φ| ≤ chainMass c` (including both `S = ℝ` and `S = ℤ`). -/
theorem abs_chainIntegral_le_chainMass {S : Type*} [SeminormedRing S] [Module S ℝ]
    [IsBoundedSMul S ℝ] (c : SmoothSimplex I M p →₀ S) (φ : RoughForm I M ℝ p)
    (hφ : ∀ x : M, ∀ v : Fin p → TangentSpace I x, Orthonormal ℝ v → |φ x v| ≤ 1) :
    |chainIntegral c φ| ≤ chainMass c := by
  simpa only [Real.norm_eq_abs, one_mul] using norm_chainIntegral_le_mul_chainMass c φ (C := 1)
    fun x ↦ (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one).mpr (hφ x)

end ChainComass

end ChainMass

end Chains

/-! ### Canonical simplicial chains: subdivision mass, `ℤ → ℝ` mass, and comass bounds -/

section CanonicalChains
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

section SubdivisionMass
variable {R : Type} [SeminormedRing R] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Barycentric subdivision does not increase chain mass** for any seminormed ring `R`. -/
theorem chainMass_subcomplexSubdivisionX_le
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R)).X p) :
    chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp R p
        ((subcomplexSubdivisionX (ModuleCat.of R R) (smoothSingularSubcomplex I M) p).hom c)) ≤
      chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp R p c) := by
  let e := (smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp (k := R) R p
  set f := e c
  have hc : c = ∑ σ ∈ f.support,
      ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of R R) σ).hom (f σ) :=
    e.injective <| by
      rw [map_sum, Finset.sum_congr rfl fun σ _ ↦
        _root_.SSet.chainsLinearEquivFinsupp_ιChainComplex _ σ (f σ)]
      exact (Finsupp.sum_single f).symm
  conv_lhs => rw [hc]
  rw [map_sum, map_sum]
  refine (chainMass_sum_le _ _).trans ?_
  rw [chainMass_eq_sum, Finsupp.sum]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  rw [chainsLinearEquivFinsupp_subcomplexSubdivisionX_ιChainComplex]
  refine (chainMass_sum_le _ _).trans ?_
  simp_rw [chainMass_single, norm_units_zsmul, ← Finset.mul_sum,
    SmoothSimplex.sum_mass_compAffineMapMk_vertex]
  exact le_rfl

/-- Barycentric subdivision preserves chain mass with exact equality on an injective simplex. -/
theorem chainMass_subcomplexSubdivisionX_ιChainComplex_of_injective {σ : SmoothSimplex I M p}
    (hσ : Function.Injective σ.toContinuousMap) (a : R) :
    chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp R p
        ((subcomplexSubdivisionX (ModuleCat.of R R) (smoothSingularSubcomplex I M) p).hom
          (((smoothSingularSubcomplex I M : SSet).ιChainComplex
            (R := ModuleCat.of R R) σ).hom a))) = ‖a‖ * σ.mass := by
  classical
  rw [chainsLinearEquivFinsupp_subcomplexSubdivisionX_ιChainComplex]
  let g (μ : Equiv.Perm (Fin (p + 1))) := σ.compAffineMapMk (BarycentricSubdivision.vertex μ)
  have hinj : Function.Injective g := σ.compAffineMapMk_vertex_injective hσ
  set c : SmoothSimplex I M p →₀ R :=
    ∑ μ : Equiv.Perm (Fin (p + 1)), Finsupp.single (g μ) (μ.sign • a) with hc_def
  have hsupp : c.support ⊆ Finset.univ.image g := fun τ hτ ↦ by
    obtain ⟨μ, _, hμ⟩ := Finsupp.mem_support_finsetSum τ hτ
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hμ)]
    exact Finset.mem_image_of_mem g (Finset.mem_univ μ)
  rw [chainMass_eq_sum_of_support_subset c hsupp, Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
  have hval (μ : Equiv.Perm (Fin (p + 1))) : c (g μ) = μ.sign • a := by
    rw [hc_def, Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply, hinj.eq_iff]; simp
  rw [Finset.sum_congr rfl fun μ _ ↦ by rw [hval μ, norm_units_zsmul], ← Finset.mul_sum]
  exact congrArg (‖a‖ * ·) σ.sum_mass_compAffineMapMk_vertex

end SubdivisionMass

/-- The `ℤ → ℝ` coefficient change `intToRealSmoothChains` preserves chain mass. -/
theorem chainMass_intToRealSmoothChains [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℝ p
        (((intToRealSmoothChains I M).f p).hom c)) =
      chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℤ p c) := by
  rw [chainsLinearEquivFinsupp_intToRealSmoothChains_f, chainMass_mapRange_intCast]

section CanonicalComass

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Comass bound for canonical smooth chains** over any bounded-smul coefficient ring `R`. -/
theorem norm_integrationCochain_le_mul_chainMass {R : Type} [SeminormedRing R] [Module R F]
    [IsBoundedSMul R F] (φ : RoughForm I M F p) {C : ℝ} (hφ : ∀ x : M, ‖φ x‖ ≤ C)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R)).X p) :
    ‖(integrationCochain φ).hom c‖ ≤
      C * chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp R p c) := by
  rw [integrationCochain_apply (I := I)]; exact norm_chainIntegral_le_mul_chainMass _ φ hφ

/-- **Comass bound for canonical integral smooth chains** with values in any real normed space
`F`. -/
theorem norm_integrationCochain_int_le_mul_chainMass (φ : RoughForm I M F p) {C : ℝ}
    (hφ : ∀ x : M, ‖φ x‖ ≤ C)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    ‖(integrationCochain φ).hom c‖ ≤
      C * chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℤ p c) := by
  rw [integrationCochain_apply (I := I)]; exact norm_chainIntegral_int_le_mul_chainMass _ φ hφ

/-- **Calibration bound for canonical smooth chains** (including both `R = ℝ` and `R = ℤ`). -/
theorem abs_integrationCochain_le_chainMass {R : Type} [SeminormedRing R] [Module R ℝ]
    [IsBoundedSMul R ℝ] (φ : RoughForm I M ℝ p)
    (hφ : ∀ x : M, ∀ v : Fin p → TangentSpace I x, Orthonormal ℝ v → |φ x v| ≤ 1)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R)).X p) :
    |(integrationCochain φ).hom c| ≤
      chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp R p c) := by
  rw [integrationCochain_apply (I := I)]; exact abs_chainIntegral_le_chainMass _ φ hφ

end CanonicalComass

end CanonicalChains

end TauCeti
