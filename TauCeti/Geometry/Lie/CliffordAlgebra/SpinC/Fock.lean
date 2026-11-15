/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.HalfSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.HalfSpinor
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Intertwiner
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.MetricSpace.IsometricSMul
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.HalfSpin
import TauCeti.RepresentationTheory.Spin.Polarization.Chirality

/-!
# Smooth isometric Spinᶜ fiber actions and the four-dimensional Hermitian Fock model

`TauCeti.Geometry.Manifold.VectorBundle.Associated.Basic` and `.Metric` construct smooth
associated vector bundles and invariant Hermitian bundle metrics from a smooth principal `G`-bundle
together with `[DistribMulAction G F]`, `[SMulCommClass G ℂ F]`, `[SMulCommClass G ℝ F]`,
`[ContinuousSMul G F]`, `[ContMDiffSMul IG 𝓘(ℝ, F) ∞ G F]`, and `[IsIsometricSMul G F]`.

This file supplies those fiber actions for compact `Spinᶜ` together with their frame-change
equivariance and concrete four-dimensional Fock realization:

* `CliffordAlgebra.spinCGroup.realDetDistribMulAction` equips `ℂ` with the smooth isometric
  weight-two determinant action of `Spinᶜ(n)`, commuting with scalar multiplications that commute
  with `ℂ` (in particular both `ℂ` and `ℝ`).
* `Orientation.realSpinCHalfSpinDistribMulAction` equips any chirality eigenspace `W^ε` of a
  four-dimensional normed Clifford module with the smooth linear `Spinᶜ(4)` action in an
  orthonormal frame `b`, which is isometric when Clifford generators are skew-adjoint.
* `Orientation.halfSpinLinearIsometryEquiv_realSpinCHalfSpinSmoothHom_apply` and
  `Orientation.exists_realSpinCHalfSpinSmoothHom_eq_conj` establish equivariance under oriented
  linear isometries and unitary Clifford intertwiners, and inner-automorphism conjugation under
  change between equally oriented orthonormal frames.
* `Orientation.exists_almostComplexStructure_orthonormalBasis` constructs an orientation-compatible
  orthogonal complex structure and adapted orthonormal frame on every oriented four-dimensional
  Euclidean space `(V, o)`, yielding a concrete Hermitian Fock `Spinᶜ(4)` model on
  `AlmostComplexStructure.FockSpinors` of half-spin rank two whose smooth chirality representations
  are intertwined across polarizations by unitary equivalences
  (`Orientation.exists_unitary_intertwiner_fock_realSpinCHalfSpinSmoothHom`) and have determinant
  equal to `spinCGroup.det` (`Orientation.det_fock_realSpinCHalfSpinSmoothHom`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Manifold Module Module.End TauCeti TauCeti.CliffordAlgebra
open scoped Manifold ContDiff InnerProductSpace

/-! ### Smooth isometric determinant line action of compact `Spinᶜ(n)` -/

namespace CliffordAlgebra.spinCGroup

variable (n : ℕ) (hQ : realCliffordForm n 0 ≠ 0)

/-- The weight-two determinant action of compact `Spinᶜ(n)` on `ℂ`, defined as a named `abbrev` so
callers can install it locally alongside other `Spinᶜ(n)` actions on `ℂ`. -/
abbrev realDetDistribMulAction :
    DistribMulAction (spinCGroup (realCliffordForm n 0) hQ) ℂ :=
  DistribMulAction.compHom ℂ (det (realCliffordForm n 0) hQ)

/-- Under `realDetDistribMulAction`, `g : Spinᶜ(n)` multiplies `w : ℂ` by `det g`. -/
theorem realDet_smul (g : spinCGroup (realCliffordForm n 0) hQ) (w : ℂ) :
    letI := realDetDistribMulAction n hQ
    g • w = (det (realCliffordForm n 0) hQ g : ℂ) * w := by
  let := realDetDistribMulAction n hQ
  exact Circle.smul_def (det (realCliffordForm n 0) hQ g) w

/-- `realDetDistribMulAction` commutes with any scalar action on `ℂ` commuting with complex
multiplication (in particular `ℂ` and `ℝ`). -/
theorem realDetSMulCommClass {𝕜 : Type*} [SMul 𝕜 ℂ] [SMulCommClass 𝕜 ℂ ℂ] :
    letI := realDetDistribMulAction n hQ
    SMulCommClass (spinCGroup (realCliffordForm n 0) hQ) 𝕜 ℂ := by
  let := realDetDistribMulAction n hQ
  refine ⟨fun g c w ↦ ?_⟩
  rw [realDet_smul, realDet_smul, mul_smul_comm]

/-- `realDetDistribMulAction` is smooth over `ℝ` on `Spinᶜ(n) × ℂ`. -/
theorem realDetContMDiffSMul :
    letI := realDetDistribMulAction n hQ
    ContMDiffSMul (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (spinCGroup (realCliffordForm n 0) hQ) ℂ := by
  let := realDetDistribMulAction n hQ
  let := finrank_real_complex_fact'
  have hdet : ContMDiff (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun g ↦ (det (realCliffordForm n 0) hQ g : ℂ)) :=
    contMDiff_coe_sphere.comp (contMDiff_realDet n hQ)
  have hmul : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2) := by
    rw [contMDiff_iff]
    exact ⟨continuous_mul, fun _ _ ↦ contDiff_mul.contDiffOn⟩
  refine ⟨?_⟩
  have hcomp := hmul.comp ((hdet.comp contMDiff_fst).prodMk contMDiff_snd)
  exact hcomp.congr fun p ↦ realDet_smul n hQ p.1 p.2

/-- `realDetDistribMulAction` is jointly continuous on `Spinᶜ(n) × ℂ`. -/
theorem realDetContinuousSMul :
    letI := realDetDistribMulAction n hQ
    ContinuousSMul (spinCGroup (realCliffordForm n 0) hQ) ℂ := by
  let := realDetDistribMulAction n hQ
  exact ⟨(realDetContMDiffSMul n hQ).contMDiff_smul.continuous⟩

/-- `realDetDistribMulAction` acts by isometries on `ℂ`. -/
theorem realDetIsIsometricSMul :
    letI := realDetDistribMulAction n hQ
    IsIsometricSMul (spinCGroup (realCliffordForm n 0) hQ) ℂ := by
  let := realDetDistribMulAction n hQ
  refine ⟨fun g ↦ Isometry.of_dist_eq fun w₁ w₂ ↦ ?_⟩
  simp [realDet_smul, dist_eq_norm, ← mul_sub]

end CliffordAlgebra.spinCGroup

/-! ### Smooth isometric half-spin fiber action, frame equivariance, and Fock realization -/

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "hQ₀" => b.ne_zero_of_neg_norm_sq hQ
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos
local notation "IG" => ModelWithCorners.prod 𝓘(ℝ, realSpinLieModel 4) (𝓡 1)

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

/-- The weight-one half-spin action of compact `Spinᶜ(4)` on the `ε`-chirality eigenspace in the
frame `b`, packaged as a named `DistribMulAction` for local installation. -/
abbrev realSpinCHalfSpinDistribMulAction : DistribMulAction SpinC S :=
  DistribMulAction.compHom S ((spinCGroupHalfSpinRep o ρ ε hQ₀).comp
    (b.realSpinCGroupHom hQ hpos hQ₀))

/-- Under `realSpinCHalfSpinDistribMulAction`, `g : Spinᶜ(4)` acts by
`realSpinCHalfSpinSmoothHom`. -/
theorem realSpinCHalfSpin_smul (g : SpinC) (ψ : S) :
    letI := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
    g • ψ = realSpinCHalfSpinSmoothHom o hQ b ρ ε g ψ := by
  let := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀ g]
  rfl

/-- `realSpinCHalfSpinDistribMulAction` commutes with any scalar action forming a tower with `ℂ`
(in particular both `ℂ` and `ℝ`). -/
theorem realSpinCHalfSpinSMulCommClass {𝕜 : Type*} [SMul 𝕜 ℂ] [SMul 𝕜 S]
    [IsScalarTower 𝕜 ℂ S] :
    letI := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
    SMulCommClass SpinC 𝕜 S := by
  let := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
  refine ⟨fun g c ψ ↦ ?_⟩
  calc g • (c • ψ) = g • ((c • (1 : ℂ)) • ψ) := by rw [smul_one_smul]
    _ = (c • (1 : ℂ)) • (g • ψ) := by
      rw [realSpinCHalfSpin_smul, realSpinCHalfSpin_smul]
      exact (realSpinCHalfSpinSmoothHom o hQ b ρ ε g).map_smul (c • (1 : ℂ)) ψ
    _ = c • (g • ψ) := smul_one_smul ℂ c (g • ψ)

/-- `realSpinCHalfSpinDistribMulAction` is smooth jointly on `Spinᶜ(4) × S`. -/
theorem realSpinCHalfSpinContMDiffSMul :
    letI := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
    ContMDiffSMul IG 𝓘(ℝ, S) ∞ SpinC S := by
  let := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
  exact ⟨(contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε).congr fun p ↦
    realSpinCHalfSpin_smul o hQ b ρ ε p.1 p.2⟩

/-- `realSpinCHalfSpinDistribMulAction` is jointly continuous on `Spinᶜ(4) × S`. -/
theorem realSpinCHalfSpinContinuousSMul :
    letI := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
    ContinuousSMul SpinC S := by
  let := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
  exact ⟨(realSpinCHalfSpinContMDiffSMul o hQ b ρ ε).contMDiff_smul.continuous⟩

/-- Changing between two equally oriented orthonormal frames `b` and `b'` conjugates
`realSpinCHalfSpinSmoothHom` by the image of a compact Spin element in `Spinᶜ(4)`. -/
theorem exists_realSpinCHalfSpinSmoothHom_eq_conj {b' : OrthonormalBasis (Fin 4) ℝ V}
    (hb : b.toBasis.orientation = b'.toBasis.orientation) :
    ∃ s₀ : spinGroup (realCliffordForm 4 0), ∀ (x : SpinC) (ψ : S),
      realSpinCHalfSpinSmoothHom o hQ b' ρ ε x ψ =
        realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofSpin (realCliffordForm 4 0) hpos s₀)
          (realSpinCHalfSpinSmoothHom o hQ b ρ ε x
            (realSpinCHalfSpinSmoothHom o hQ b ρ ε
              (spinCGroup.ofSpin (realCliffordForm 4 0) hpos s₀)⁻¹ ψ)) := by
  have hconj := b.exists_realSpinCGroupHom_eq_conj b' hQ hb hpos hQ₀
  refine ⟨hconj.choose, fun x ψ ↦ ?_⟩
  simp only [realSpinCHalfSpinSmoothHom_apply o hQ b' ρ ε hQ₀,
    realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀, hconj.choose_spec x, map_mul]
  rfl

end Normed

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

/-- When Clifford generators are skew-adjoint, `realSpinCHalfSpinDistribMulAction` acts by
isometries on `S`. -/
theorem realSpinCHalfSpinIsIsometricSMul
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    letI := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
    IsIsometricSMul SpinC S := by
  let := realSpinCHalfSpinDistribMulAction o hQ b ρ ε
  refine ⟨fun g ↦ Isometry.of_dist_eq fun ψ₁ ψ₂ ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, realSpinCHalfSpin_smul, realSpinCHalfSpin_smul, ← map_sub,
    norm_eq_sqrt_re_inner (𝕜 := ℂ),
    inner_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hρ g (ψ₁ - ψ₂) (ψ₁ - ψ₂),
    ← norm_eq_sqrt_re_inner (𝕜 := ℂ)]

/-- **Equivariance of `realSpinCHalfSpinSmoothHom` along an oriented isometry and unitary Clifford
intertwiner**: `halfSpinLinearIsometryEquiv` intertwines the smooth `Spinᶜ(4)` action in `b` with
the smooth `Spinᶜ(4)` action in `b.map f`. -/
theorem halfSpinLinearIsometryEquiv_realSpinCHalfSpinSmoothHom_apply
    {V' W' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    [Fact (finrank ℝ V' = 4)] {Q' : QuadraticForm ℝ V'} (o' : Orientation ℝ V' (Fin 4))
    (hQ' : ∀ v, Q' v = -‖v‖ ^ 2)
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
    {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ W'}
    {f : V ≃ₗᵢ[ℝ] V'} (ho : o.map (Fin 4) f.toLinearEquiv = o')
    {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap)
    (x : SpinC) (ψ : S) :
    halfSpinLinearIsometryEquiv o' ho hU ε (realSpinCHalfSpinSmoothHom o hQ b ρ ε x ψ) =
      realSpinCHalfSpinSmoothHom o' hQ' (b.map f) ρ' ε x
        (halfSpinLinearIsometryEquiv o' ho hU ε ψ) := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    realSpinCHalfSpinSmoothHom_apply o' hQ' (b.map f) ρ' ε ((b.map f).ne_zero_of_neg_norm_sq hQ'),
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective (realCliffordForm 4 0) hpos x
  let e : Q →qᵢ Q' :=
    { toLinearMap := f.toLinearMap
      map_app' v := by change Q' (f v) = Q v; rw [hQ', f.norm_map, hQ] }
  have he_comp : ((b.map f).negRealCliffordFormIsometryEquiv hQ').toIsometry =
      e.comp (b.negRealCliffordFormIsometryEquiv hQ).toIsometry := by
    ext c
    simp [e, OrthonormalBasis.negRealCliffordFormIsometryEquiv_apply, map_sum, map_smul]
    rfl
  have heven : (⟨CliffordAlgebra.map e
      (b.realEvenCliffordEquiv hQ (spinGroupToEven _ s)),
      map_mem_even e (b.realEvenCliffordEquiv hQ (spinGroupToEven _ s)).2⟩ : even Q') =
      (b.map f).realEvenCliffordEquiv hQ' (spinGroupToEven _ s) := by
    apply Subtype.ext
    dsimp only
    rw [b.coe_realEvenCliffordEquiv_apply hQ, (b.map f).coe_realEvenCliffordEquiv_apply hQ',
      ← AlgHom.comp_apply, CliffordAlgebra.map_comp_map, ← he_comp]
  have hstep := LinearMap.congr_fun
    (halfSpinLinearIsometryEquiv_comp_evenHalfSpinAction o' ho hU e (fun _ ↦ rfl) ε
      (b.realEvenCliffordEquiv hQ (spinGroupToEven _ s))) ψ
  rw [OrthonormalBasis.realSpinCGroupHom_mk, OrthonormalBasis.realSpinCGroupHom_mk,
    spinCGroupHalfSpinRep_mk, spinCGroupHalfSpinRep_mk,
    spinCHalfSpinRep_apply, spinCHalfSpinRep_apply]
  dsimp only
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, halfSpinRep_apply, halfSpinRep_apply,
    b.spinGroupToEven_realSpinGroupEquiv hQ, (b.map f).spinGroupToEven_realSpinGroupEquiv hQ',
    ← heven]
  exact congrArg ((z : ℂ) • ·) hstep

/-- Specialization of `halfSpinLinearIsometryEquiv_realSpinCHalfSpinSmoothHom_apply` to a unitary
Clifford intertwiner between two representations `ρ` and `ρ'` on the same oriented four-space in a
fixed frame `b`. -/
theorem realSpinCHalfSpinSmoothHom_intertwine_apply
    {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
    {ρ' : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W'}
    {U : W ≃ₗᵢ[ℂ] W'}
    (hU : ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ ρ (ι Q v) =
      ρ' (ι Q v) ∘ₗ U.toLinearEquiv.toLinearMap)
    (x : SpinC) (ψ : S) :
    halfSpinLinearIsometryEquiv o (f := .refl ℝ V) (by simp) hU ε
        (realSpinCHalfSpinSmoothHom o hQ b ρ ε x ψ) =
      realSpinCHalfSpinSmoothHom o hQ b ρ' ε x
        (halfSpinLinearIsometryEquiv o (f := .refl ℝ V) (by simp) hU ε ψ) := by
  have hb_refl : b.map (.refl ℝ V) = b := by
    cases b
    congr
  simpa [hb_refl] using
    halfSpinLinearIsometryEquiv_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε o hQ
      (f := .refl ℝ V) (by simp) hU x ψ

end Hermitian

/-! ### Concrete four-dimensional Hermitian Fock `Spinᶜ(4)` realization -/

section Fock

/-- Every oriented four-dimensional real inner product space `(V, o)` admits an orthogonal almost
complex structure `J` together with a positively oriented orthonormal basis `b` satisfying
`J (b 0) = b 1` and `J (b 2) = b 3`. -/
theorem exists_almostComplexStructure_orthonormalBasis :
    ∃ (J : AlmostComplexStructure V) (b : OrthonormalBasis (Fin 4) ℝ V),
      b.toBasis.orientation = o ∧ J (b 0) = b 1 ∧ J (b 2) = b 3 ∧
        ∀ v w, ⟪J v, J w⟫_ℝ = ⟪v, w⟫_ℝ := by
  let b₀ := o.finOrthonormalBasis (by omega) Fact.out
  obtain ⟨J, hb₀, hb₂⟩ := b₀.exists_almostComplexStructure_finFour
  exact ⟨J, b₀, o.finOrthonormalBasis_orientation (by omega) Fact.out, hb₀, hb₂,
    J.inner_apply_apply_of_orthonormalBasis hb₀ hb₂⟩

/-- Four-dimensionality gives `FiniteDimensional ℝ V`. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- **Polarization independence of the smooth Fock `Spinᶜ(4)` half-spin representation**: for any
two `Q`-orthogonal complex structures `J₁` and `J₂` on `(V, o)`, any orthonormal frame `b`, and
any chirality eigenvalue `ε : ℂ`, there exists a unitary equivalence between the `ε`-chirality
half-spinor spaces of `J₁.FockSpinors` and `J₂.FockSpinors` intertwining their smooth `Spinᶜ(4)`
representations. -/
theorem exists_unitary_intertwiner_fock_realSpinCHalfSpinSmoothHom
    (J₁ J₂ : AlmostComplexStructure V)
    (hQJ₁ : ∀ v, Q (J₁ v) = Q v) (hQJ₂ : ∀ v, Q (J₂ v) = Q v)
    (hQnd : Q.Nondegenerate) (ε : ℂ) :
    letI := J₁.fockSpinorsNormedAddCommGroup hQJ₁ hQnd hQ
    letI := J₁.fockSpinorsInnerProductSpace hQJ₁ hQnd hQ
    letI := J₂.fockSpinorsNormedAddCommGroup hQJ₂ hQnd hQ
    letI := J₂.fockSpinorsInnerProductSpace hQJ₂ hQnd hQ
    ∃ Uhalf : eigenspace (J₁.fockSpinorAction hQJ₁ hQnd (chirality Q o)) ε ≃ₗᵢ[ℂ]
        eigenspace (J₂.fockSpinorAction hQJ₂ hQnd (chirality Q o)) ε,
      ∀ (x : SpinC) (ψ : eigenspace (J₁.fockSpinorAction hQJ₁ hQnd (chirality Q o)) ε),
        Uhalf (realSpinCHalfSpinSmoothHom o hQ b (J₁.fockSpinorAction hQJ₁ hQnd) ε x ψ) =
          realSpinCHalfSpinSmoothHom o hQ b (J₂.fockSpinorAction hQJ₂ hQnd) ε x (Uhalf ψ) := by
  let := J₁.fockSpinorsNormedAddCommGroup hQJ₁ hQnd hQ
  let := J₁.fockSpinorsInnerProductSpace hQJ₁ hQnd hQ
  let := J₂.fockSpinorsNormedAddCommGroup hQJ₂ hQnd hQ
  let := J₂.fockSpinorsInnerProductSpace hQJ₂ hQnd hQ
  have hU := J₁.exists_unitary_intertwiner_fockSpinorAction J₂ hQJ₁ hQnd hQ hQJ₂ hQnd hQ
    (.refl ℝ V)
  exact ⟨halfSpinLinearIsometryEquiv o (f := .refl ℝ V) (by simp) hU.choose_spec ε, fun x ψ ↦
    realSpinCHalfSpinSmoothHom_intertwine_apply o hQ b
      (J₁.fockSpinorAction hQJ₁ hQnd) ε hU.choose_spec x ψ⟩

/-- On an orientation-compatible `Q`-orthogonal complex structure `J` on `(V, o)`, both chirality
representations (`ε = 1` and `ε = -1`) of `realSpinCHalfSpinSmoothHom` on `J.FockSpinors` have
determinant equal to the weight-two character `spinCGroup.det`. -/
theorem det_fock_realSpinCHalfSpinSmoothHom
    (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)
    {b₀ : OrthonormalBasis (Fin 4) ℝ V} (hb₀ : b₀.toBasis.orientation = o)
    (hb₁ : b₀ 1 = J (b₀ 0)) (hb₃ : b₀ 3 = J (b₀ 2))
    {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (x : SpinC) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    LinearMap.det
        (realSpinCHalfSpinSmoothHom o hQ b (J.fockSpinorAction hQJ hQnd) ε x).toLinearMap =
      (spinCGroup.det (realCliffordForm 4 0) hpos x : ℂ) := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  let e := J.fockSpinorsLinearEquiv hQJ hQnd
  have he : eigenspace (J.fockSpinorAction hQJ hQnd (chirality Q o)) ε =
      (eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) ε).comap e.toLinearMap := by
    ext y
    rw [Submodule.mem_comap, mem_eigenspace_iff, mem_eigenspace_iff, ← e.injective.eq_iff,
      map_smul]
    dsimp only [e, LinearEquiv.coe_coe]
    rw [J.fockSpinorsLinearEquiv_fockSpinorAction_apply]
  have h₂' : finrank ℂ (eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) ε) = 2 := by
    rcases hε with rfl | rfl
    · rw [← positiveHalfSpinors_eq_eigenspace]
      exact J.finrank_positiveHalfSpinors_realFockAction hQJ hQnd hQ b₀ hb₀ hb₁ hb₃
    · exact J.finrank_eigenspace_realFockAction_chirality_neg_one hQJ hQnd hQ b₀ hb₀ hb₁ hb₃
  have h₂ : finrank ℂ (eigenspace (J.fockSpinorAction hQJ hQnd (chirality Q o)) ε) = 2 := by
    have hmap : (eigenspace (J.fockSpinorAction hQJ hQnd (chirality Q o)) ε).map
        e.toLinearMap = eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) ε := by
      rw [he, Submodule.map_comap_eq_of_surjective e.surjective]
    exact (e.ofSubmodules _ _ hmap).finrank_eq.trans h₂'
  exact det_realSpinCHalfSpinSmoothHom o hQ b (J.fockSpinorAction hQJ hQnd) ε h₂ x

end Fock

end Orientation
