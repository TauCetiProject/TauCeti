/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import TauCeti.Geometry.Manifold.SmoothSingular.Mass.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Stokes
import TauCeti.AlgebraicTopology.Singular.Subdivision.FullSimplex
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating

/-!
# Mass of smooth singular chains and integral smooth chains

The **mass of a smooth singular `p`-chain** `c : SmoothSimplex I M p →₀ R` with coefficients in
any seminormed abelian group `R` (e.g. `ℝ` or `ℤ`) is `∑ σ ∈ c.support, ‖c σ‖ * σ.mass`. We
establish its seminorm, Lipschitz pushforward, Riemannian isometry, barycentric subdivision, and
comass/calibration properties, together with the integral pairing `intChainIntegral`,
`intIntegrationCochain`, `intToRealSmoothChains` (`ℤ → ℝ`), Stokes' theorem
(`d_comp_intIntegrationCochain`), and barycentric subdivision invariance
(`subcomplexSubdivisionX_comp_intIntegrationCochain`).

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
    (hf : ContMDiff I J ∞ f) {C : ℝ} (hC : 0 ≤ C)
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
    (SmoothSimplex.mass_smoothSingularSubcomplexMap_app_le hf hC hLip σ) (norm_nonneg (c σ))

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

/-- **Comass bound for real chains:** `‖φ‖ ≤ C` gives `‖chainIntegral c φ‖ ≤ C * chainMass c`. -/
theorem norm_chainIntegral_le_mul_chainMass (c : SmoothSimplex I M p →₀ ℝ) (φ : RoughForm I M F p)
    {C : ℝ} (hφ : ∀ x : M, ‖φ x‖ ≤ C) : ‖chainIntegral c φ‖ ≤ C * chainMass c := by
  rw [chainIntegral_eq_sum, chainMass_eq_sum, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ ↦ ?_)
  rw [norm_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (σ.norm_integral_le_mul_mass φ fun x ↦ hφ (σ.toContinuousMap x)) (norm_nonneg (c σ))

/-- **Calibration bound for real chains:** unit comass gives `|chainIntegral c φ| ≤ chainMass c`. -/
theorem abs_chainIntegral_le_chainMass (c : SmoothSimplex I M p →₀ ℝ) (φ : RoughForm I M ℝ p)
    (hφ : ∀ x : M, ∀ v : Fin p → TangentSpace I x, Orthonormal ℝ v → |φ x v| ≤ 1) :
    |chainIntegral c φ| ≤ chainMass c := by
  simpa only [Real.norm_eq_abs, one_mul] using norm_chainIntegral_le_mul_chainMass c φ (C := 1)
    fun x ↦ (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one).mpr (hφ x)

end ChainComass

end ChainMass

/-! ### Integration over integral smooth singular chains -/

section IntChains
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integration of a form over an integral smooth singular `p`-chain `SmoothSimplex I M p →₀ ℤ`. -/
def intChainIntegral (c : SmoothSimplex I M p →₀ ℤ) (φ : RoughForm I M F p) : F :=
  Finsupp.linearCombination ℤ (fun σ ↦ σ.integral φ) c

/-- The integral over an integral chain is the `ℤ`-linear combination of simplex integrals. -/
theorem intChainIntegral_eq_sum (c : SmoothSimplex I M p →₀ ℤ) (φ : RoughForm I M F p) :
    intChainIntegral c φ = c.sum fun σ a ↦ a • σ.integral φ := Finsupp.linearCombination_apply ℤ _

/-- Integration over a single-simplex integral chain. -/
@[simp]
theorem intChainIntegral_single (σ : SmoothSimplex I M p) (a : ℤ) (φ : RoughForm I M F p) :
    intChainIntegral (Finsupp.single σ a) φ = a • σ.integral φ :=
  Finsupp.linearCombination_single ℤ _ _

/-- Integration over the zero integral chain vanishes. -/
@[simp]
theorem intChainIntegral_zero (φ : RoughForm I M F p) : intChainIntegral 0 φ = 0 :=
  map_zero (Finsupp.linearCombination ℤ _)

/-- Integration is additive in the integral chain. -/
@[simp]
theorem intChainIntegral_add (c d : SmoothSimplex I M p →₀ ℤ) (φ : RoughForm I M F p) :
    intChainIntegral (c + d) φ = intChainIntegral c φ + intChainIntegral d φ :=
  map_add (Finsupp.linearCombination ℤ _) c d

/-- Negating an integral chain negates the integral. -/
@[simp]
theorem intChainIntegral_neg (c : SmoothSimplex I M p →₀ ℤ) (φ : RoughForm I M F p) :
    intChainIntegral (-c) φ = -intChainIntegral c φ := map_neg (Finsupp.linearCombination ℤ _) c

/-- Integration respects subtraction of integral chains. -/
@[simp]
theorem intChainIntegral_sub (c d : SmoothSimplex I M p →₀ ℤ) (φ : RoughForm I M F p) :
    intChainIntegral (c - d) φ = intChainIntegral c φ - intChainIntegral d φ :=
  map_sub (Finsupp.linearCombination ℤ _) c d

/-- Integration is `ℤ`-homogeneous in the integral chain. -/
@[simp]
theorem intChainIntegral_zsmul (a : ℤ) (c : SmoothSimplex I M p →₀ ℤ) (φ : RoughForm I M F p) :
    intChainIntegral (a • c) φ = a • intChainIntegral c φ :=
  map_smul (Finsupp.linearCombination ℤ _) a c

/-- Integrating over an integral chain agrees with its image under `ℤ → ℝ`. -/
theorem intChainIntegral_eq_chainIntegral_mapRange (c : SmoothSimplex I M p →₀ ℤ)
    (φ : RoughForm I M F p) :
    intChainIntegral c φ =
      chainIntegral (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero c) φ := by
  rw [intChainIntegral_eq_sum, chainIntegral_eq_sum, Finsupp.sum_mapRange_index (by simp)]
  exact Finset.sum_congr rfl fun σ _ ↦ by dsimp only; rw [Int.cast_smul_eq_zsmul ℝ]

/-- Integrating over the pushforward of an integral smooth chain integrates the pulled-back form. -/
theorem intChainIntegral_mapDomain {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N]
    [ChartedSpace H' N] {f : M → N} (hf : ContMDiff I J ∞ f)
    (c : SmoothSimplex I M p →₀ ℤ) (ψ : RoughForm J N F p) :
    intChainIntegral
        (Finsupp.mapDomain ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌)) c) ψ =
      intChainIntegral c (mpullback I J f ψ) := by
  simp only [intChainIntegral, Finsupp.linearCombination_mapDomain, Function.comp_def,
    SmoothSimplex.integral_smoothSingularSubcomplexMap_app hf]

section IntChainComass
variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Comass bound for integration over an integral smooth chain.** -/
theorem norm_intChainIntegral_le_mul_chainMass (c : SmoothSimplex I M p →₀ ℤ)
    (φ : RoughForm I M F p) {C : ℝ} (hφ : ∀ x : M, ‖φ x‖ ≤ C) :
    ‖intChainIntegral c φ‖ ≤ C * chainMass c := by
  rw [intChainIntegral_eq_chainIntegral_mapRange, ← chainMass_mapRange_intCast c]
  exact norm_chainIntegral_le_mul_chainMass _ φ hφ

/-- **Calibration bound for an integral smooth chain.** -/
theorem abs_intChainIntegral_le_chainMass (c : SmoothSimplex I M p →₀ ℤ) (φ : RoughForm I M ℝ p)
    (hφ : ∀ x : M, ∀ v : Fin p → TangentSpace I x, Orthonormal ℝ v → |φ x v| ≤ 1) :
    |intChainIntegral c φ| ≤ chainMass c := by
  rw [intChainIntegral_eq_chainIntegral_mapRange, ← chainMass_mapRange_intCast c]
  exact abs_chainIntegral_le_chainMass _ φ hφ

end IntChainComass

end IntChains

end Chains

/-! ### Canonical simplicial chains: subdivision mass, integral cochains, and `ℤ → ℝ` -/

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
  have hnorm (μ : Equiv.Perm (Fin (p + 1))) : ‖μ.sign • f σ‖ = ‖f σ‖ := by
    rcases Int.units_eq_one_or μ.sign with h | h <;> simp [h]
  simp_rw [chainMass_single, hnorm, ← Finset.mul_sum, SmoothSimplex.sum_mass_compAffineMapMk_vertex]
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
  have hinj : Function.Injective g := fun μ₁ μ₂ h ↦
    BarycentricSubdivision.vertex_injective <| funext fun k ↦ by
      let x : fullSimplex p := (fullSimplexEquivStdSimplex p).symm (StdSimplex.single k)
      have hx := congrArg (fun τ : SmoothSimplex I M p ↦ τ.toContinuousMap x) h
      simp only [g, SmoothSimplex.toContinuousMap_compAffineMapMk_apply] at hx
      have hval := congrArg Subtype.val (hσ hx); dsimp only at hval
      rw [affineMapAmbient_coe, affineMapAmbient_coe] at hval
      simpa only [x, Homeomorph.apply_symm_apply, StdSimplex.affineMapMk_single] using
        (fullSimplexEquivStdSimplex p).symm.injective (Subtype.ext hval)
  let c : SmoothSimplex I M p →₀ R :=
    ∑ μ : Equiv.Perm (Fin (p + 1)), Finsupp.single (g μ) (μ.sign • a)
  -- Express the subdivision sum via `c` so the support and pointwise rewrites share one term.
  change chainMass c = _
  have hsupp : c.support ⊆ Finset.univ.image g := fun τ hτ ↦ by
    obtain ⟨μ, _, hμ⟩ := Finsupp.mem_support_finsetSum τ hτ
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hμ)]
    exact Finset.mem_image_of_mem g (Finset.mem_univ μ)
  rw [chainMass_eq_sum_of_support_subset c hsupp, Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
  have hval (μ : Equiv.Perm (Fin (p + 1))) : c (g μ) = μ.sign • a := by
    rw [show c = ∑ τ : Equiv.Perm (Fin (p + 1)), Finsupp.single (g τ) (τ.sign • a) from rfl,
      Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply, hinj.eq_iff]; simp
  have hnorm (μ : Equiv.Perm (Fin (p + 1))) : ‖μ.sign • a‖ = ‖a‖ := by
    rcases Int.units_eq_one_or μ.sign with h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun μ _ ↦ by rw [hval μ, hnorm μ], ← Finset.mul_sum]
  exact congrArg (‖a‖ * ·) σ.sum_mass_compAffineMapMk_vertex

end SubdivisionMass

/-- The `ℤ`-linear integration cochain on integral smooth singular chains. -/
def intIntegrationCochain (φ : RoughForm I M F p) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p ⟶
      ModuleCat.of ℤ F :=
  ModuleCat.ofHom ((Finsupp.linearCombination ℤ (fun σ : SmoothSimplex I M p ↦ σ.integral φ)).comp
    (SSet.chainsLinearEquivFinsupp _ ℤ p).toLinearMap)

/-- On canonical integral smooth chains, `intIntegrationCochain` evaluates `intChainIntegral`. -/
theorem intIntegrationCochain_apply (φ : RoughForm I M F p)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    (intIntegrationCochain φ).hom c =
      intChainIntegral ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℤ p c) φ :=
  (rfl)

/-- `intIntegrationCochain` sends a simplex with integer multiplicity `a` to `a • σ.integral φ`. -/
@[simp]
theorem intIntegrationCochain_ιChainComplex (φ : RoughForm I M F p) (σ : SmoothSimplex I M p)
    (a : ℤ) :
    (intIntegrationCochain φ).hom (((smoothSingularSubcomplex I M : SSet).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) σ).hom a) = a • σ.integral φ := by
  rw [intIntegrationCochain_apply (I := I),
    _root_.SSet.chainsLinearEquivFinsupp_ιChainComplex (smoothSingularSubcomplex I M : SSet) σ a]
  exact intChainIntegral_single σ a φ

/-- The canonical `ℤ → ℝ` change-of-coefficients chain map on smooth singular chains. -/
def intToRealSmoothChains (I : ModelWithCorners ℝ E H) (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] :
    (smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ) ⟶
      (smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℝ) :=
  ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
    (ModuleCat.ofHom (Int.castAddHom ℝ).toIntLinearMap)).app (smoothSingularSubcomplex I M : SSet)

/-- On a single smooth simplex, `intToRealSmoothChains` casts the integer coefficient to `ℝ`. -/
@[simp]
theorem intToRealSmoothChains_f_ιChainComplex (σ : SmoothSimplex I M p) (a : ℤ) :
    ((intToRealSmoothChains I M).f p).hom (((smoothSingularSubcomplex I M : SSet).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) σ).hom a) =
      ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℝ) σ).hom (a : ℝ) :=
  ConcreteCategory.congr_hom (SSet.ιChainComplex_chainComplexFunctor_map_app_f
    (X := (smoothSingularSubcomplex I M : SSet))
    (ModuleCat.ofHom (Int.castAddHom ℝ).toIntLinearMap) σ) a

/-- In the finitely supported representation, `intToRealSmoothChains` casts coefficients to `ℝ`. -/
theorem chainsLinearEquivFinsupp_intToRealSmoothChains_f
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    (smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℝ p
        (((intToRealSmoothChains I M).f p).hom c) =
      Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
        ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℤ p c) := by
  simpa [intToRealSmoothChains] using SSet.chainsLinearEquivFinsupp_chainComplexFunctor_map
    (X := (smoothSingularSubcomplex I M : SSet)) (ψ := (Int.castAddHom ℝ).toIntLinearMap) c

/-- Integration on integral chains agrees with `chainIntegral` after `intToRealSmoothChains`. -/
theorem intIntegrationCochain_eq_chainIntegral_intToRealSmoothChains (φ : RoughForm I M F p)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    (intIntegrationCochain φ).hom c =
      chainIntegral ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℝ p
        (((intToRealSmoothChains I M).f p).hom c)) φ := by
  rw [intIntegrationCochain_apply (I := I), chainsLinearEquivFinsupp_intToRealSmoothChains_f,
    intChainIntegral_eq_chainIntegral_mapRange]

/-- The `ℤ → ℝ` coefficient change `intToRealSmoothChains` preserves chain mass. -/
theorem chainMass_intToRealSmoothChains [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℝ p
        (((intToRealSmoothChains I M).f p).hom c)) =
      chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℤ p c) := by
  rw [chainsLinearEquivFinsupp_intToRealSmoothChains_f, chainMass_mapRange_intCast]

/-- `intIntegrationCochain` is natural with respect to smooth maps of manifolds. -/
@[reassoc]
theorem intIntegrationCochain_naturality {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type}
    [TopologicalSpace N] [ChartedSpace H' N] {f : M → N} (hf : ContMDiff I J ∞ f)
    (ψ : RoughForm J N F p) :
    (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)).f p ≫
      intIntegrationCochain ψ = intIntegrationCochain (mpullback I J f ψ) := by
  apply ModuleCat.hom_ext; ext c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, intIntegrationCochain_apply (I := I),
    intIntegrationCochain_apply (I := J), SSet.chainsLinearEquivFinsupp_chainComplexMap_f,
    intChainIntegral_mapDomain hf]

/-- **Stokes' theorem for integral smooth singular chains.** -/
@[reassoc]
theorem d_comp_intIntegrationCochain [IsManifold I 2 M] {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d (p + 1) p ≫
      intIntegrationCochain φ = intIntegrationCochain (mextDeriv φ) := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp only [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
    ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [intIntegrationCochain_ιChainComplex, one_smul, SmoothSimplex.integral_mextDeriv σ hφ]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [intIntegrationCochain_ιChainComplex, one_smul, ← Int.cast_smul_eq_zsmul ℝ]; simp

/-- **Barycentric subdivision preserves integration of continuous forms on integral chains.** -/
@[reassoc]
theorem subcomplexSubdivisionX_comp_intIntegrationCochain [IsManifold I 1 M]
    {φ : RoughForm I M F p} (hφ : IsSmoothForm I 0 φ) :
    subcomplexSubdivisionX (ModuleCat.of ℤ ℤ) (smoothSingularSubcomplex I M) p ≫
      intIntegrationCochain φ = intIntegrationCochain φ := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, intIntegrationCochain_ιChainComplex (I := I),
    one_smul]
  rw [intIntegrationCochain_apply (I := I),
    chainsLinearEquivFinsupp_subcomplexSubdivisionX_ιChainComplex]
  let Iφ : (SmoothSimplex I M p →₀ ℤ) →+ F :=
    AddMonoidHom.mk' (fun c ↦ intChainIntegral c φ) (fun c d ↦ intChainIntegral_add c d φ)
  refine (map_sum Iφ _ _).trans <| (Finset.sum_congr rfl fun μ _ ↦ ?_).trans
    (SmoothSimplex.sum_sign_integral_compAffineMapMk_vertex σ hφ)
  have h := intChainIntegral_single (SmoothSimplex.compAffineMapMk σ
    (BarycentricSubdivision.vertex μ)) (μ.sign • (1 : ℤ)) φ
  rcases Int.units_eq_one_or μ.sign with hs | hs <;> simpa [Iφ, hs] using h

section CanonicalComass

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Comass bound for canonical real smooth chains.** -/
theorem norm_integrationCochain_le_mul_chainMass (φ : RoughForm I M F p) {C : ℝ}
    (hφ : ∀ x : M, ‖φ x‖ ≤ C)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).X p) :
    ‖(integrationCochain φ).hom c‖ ≤
      C * chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℝ p c) := by
  rw [integrationCochain_apply (I := I)]; exact norm_chainIntegral_le_mul_chainMass _ φ hφ

/-- **Calibration bound for canonical real smooth chains.** -/
theorem abs_integrationCochain_le_chainMass (φ : RoughForm I M ℝ p)
    (hφ : ∀ x : M, ∀ v : Fin p → TangentSpace I x, Orthonormal ℝ v → |φ x v| ≤ 1)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).X p) :
    |(integrationCochain φ).hom c| ≤
      chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℝ p c) := by
  rw [integrationCochain_apply (I := I)]; exact abs_chainIntegral_le_chainMass _ φ hφ

/-- **Comass bound for canonical integral smooth chains.** -/
theorem norm_intIntegrationCochain_le_mul_chainMass (φ : RoughForm I M F p) {C : ℝ}
    (hφ : ∀ x : M, ‖φ x‖ ≤ C)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    ‖(intIntegrationCochain φ).hom c‖ ≤
      C * chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℤ p c) := by
  rw [intIntegrationCochain_apply (I := I)]; exact norm_intChainIntegral_le_mul_chainMass _ φ hφ

/-- **Calibration bound for canonical integral smooth chains.** -/
theorem abs_intIntegrationCochain_le_chainMass (φ : RoughForm I M ℝ p)
    (hφ : ∀ x : M, ∀ v : Fin p → TangentSpace I x, Orthonormal ℝ v → |φ x v| ≤ 1)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    |(intIntegrationCochain φ).hom c| ≤
      chainMass ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℤ p c) := by
  rw [intIntegrationCochain_apply (I := I)]; exact abs_intChainIntegral_le_chainMass _ φ hφ

end CanonicalComass

end CanonicalChains

end TauCeti
