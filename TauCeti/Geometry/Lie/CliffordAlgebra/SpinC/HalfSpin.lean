/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Projection
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Lie.Exponential.Units.Functor
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Smooth half-spin representations of the Spinᶜ quotient and their differentials

An orthonormal frame compares compact coordinate Spin with the negative-metric geometric
Clifford model. The weight-one half-spin action is already smooth on the covering group.
Here it descends smoothly through the actual diagonal central quotient, acting on the actual
chirality eigenspaces rather than on separately chosen matrix spaces.

The descended actions preserve the Hermitian inner product when Clifford generators are
skew-adjoint. In complex rank two their determinant is the weight-two character `[s,z] ↦ z²`.
Lifting the descended action to the Lie group `(S →L[ℂ] S)ˣ` of invertible continuous endomorphisms
yields its Lie-algebra differential on the whole `Spinᶜ(4)` Lie algebra:

* on the Spin summand `ofSpin_* X`, it agrees with the framed even Clifford action on the
  quadratic Clifford coordinate of `X`;
* on the central determinant lift `realDetLieLift 4 hpos a`, it acts as `(i a / 2) Id`;
* in Spin–determinant, quadratic Clifford–determinant, and `𝔰𝔬(4) × ℝ` coordinates, it acts as the
  sum of the lifted Spin/Clifford action and `(i a / 2) Id`.

No choice of orientation of the frame is needed to descend the action on a fixed eigenspace;
identifying the two coordinate SU(2) factors with positive and negative chirality requires a
positively oriented frame separately.

The type synonym `Orientation.SpinCHalfSpinor` of a chirality eigenspace carries the descended
action as a smooth `Spinᶜ(4)`-action. In complex rank two every alternating two-form on it, with
values in the determinant representation `CliffordAlgebra.spinCGroup.DetFiber`, is equivariant
(`Orientation.SpinCHalfSpinor.alternatingMap_apply_smul`). When the Clifford generators act
skew-adjointly the action is isometric (`Orientation.SpinCHalfSpinor.isIsometricSMul`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

namespace Orientation

open Module Module.End Manifold TauCeti TauCeti.CliffordAlgebra CliffordAlgebra
open scoped Manifold ContDiff InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "hQ₀" => b.ne_zero_of_neg_norm_sq hQ
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos
local notation "IC" => ModelWithCorners.prod 𝓘(ℝ, realSpinLieModel 4) (𝓡 1)

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

/-- The smooth weight-one half-spin representation of compact Spinᶜ(4), after comparison
with the negative-metric Clifford model in the frame `b`. -/
def realSpinCHalfSpinSmoothHom : ContMDiffMonoidMorphism IC 𝓘(ℝ, S →L[ℂ] S) ∞
    SpinC (S →L[ℂ] S) where
  toMonoidHom := (Module.End.toContinuousLinearMap S).toMonoidHom.comp
    ((spinCGroupHalfSpinRep o ρ ε hQ₀).comp (b.realSpinCGroupHom hQ hpos hQ₀))
  contMDiff_toFun := by
    apply (spinCGroup.contMDiff_iff_contMDiff_comp_mk 4 hpos _).mpr
    have h := (contMDiff_realSpinCHalfSpinRep o hQ b ρ ε).comp
      (((realSpinDiffeomorphUnitsRange 4).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
    convert h using 1
    funext p
    apply ContinuousLinearMap.ext
    intro ψ
    simp only [Function.comp_apply, realSpinDiffeomorphUnitsRange_apply,
      ContinuousMulEquiv.symm_apply_apply]
    simp only [MulEquiv.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_comp, MonoidHom.coe_ofClass, MulEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, Function.comp_apply, OrthonormalBasis.realSpinCGroupHom_mk,
      spinCGroupHalfSpinRep_mk, Module.End.toContinuousLinearMap_apply,
      LinearMap.coe_toContinuousLinearMap']

/-- The smooth action is the algebraic quotient action after the Spinᶜ frame comparison. -/
theorem realSpinCHalfSpinSmoothHom_apply (hQ₀' : Q ≠ 0) (x : SpinC) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε x =
      (spinCGroupHalfSpinRep o ρ ε hQ₀'
        (b.realSpinCGroupHom hQ hpos hQ₀' x)).toContinuousLinearMap :=
  (rfl)

/-- On representatives the descended representation is `z ρ_spin(s)` in the selected frame. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_mk (s : spinGroup (realCliffordForm 4 0)) (z : Circle) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.mk _ hpos (s, z)) =
      (spinCHalfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s, z)).toContinuousLinearMap := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    OrthonormalBasis.realSpinCGroupHom_mk, spinCGroupHalfSpinRep_mk]

/-- The central circle acts with weight one on spinors. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_ofCircle (z : Circle) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofCircle _ hpos z) =
      (z : ℂ) • (1 : S →L[ℂ] S) := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    OrthonormalBasis.realSpinCGroupHom_ofCircle, spinCGroupHalfSpinRep_ofCircle]
  exact map_smul (Module.End.toContinuousLinearMap S) (z : ℂ) 1

/-- Restriction to Spin is the half-spin action in the selected frame. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_ofSpin (s : spinGroup (realCliffordForm 4 0)) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofSpin _ hpos s) =
      (halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s)).toContinuousLinearMap := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    OrthonormalBasis.realSpinCGroupHom_ofSpin, spinCGroupHalfSpinRep_ofSpin]

section DeterminantDerivative

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] finrank_real_complex_fact'

-- Match the normed-algebra parent structures used by the framed smooth representation.
/-- Operator-norm ring structure on half-spin endomorphisms. -/
local instance : NormedRing (S →L[ℂ] S) := ContinuousLinearMap.toNormedRing
/-- Complex normed-space structure on half-spin endomorphisms. -/
local instance : NormedSpace ℂ (S →L[ℂ] S) := ContinuousLinearMap.toNormedSpace
/-- The underlying real normed algebra of half-spin endomorphisms. -/
local instance : NormedAlgebra ℝ (S →L[ℂ] S) := NormedAlgebra.complexToReal
/-- The real scalar action selected by the normed-algebra structure. -/
local instance : NormedSpace ℝ (S →L[ℂ] S) :=
  NormedAlgebra.toNormedSpace (𝕜 := ℝ) (S →L[ℂ] S)

local instance : CompleteSpace S := FiniteDimensional.completeSpace ℂ S
local instance : CompleteSpace (S →L[ℂ] S) := FiniteDimensional.completeSpace ℂ _

/-- Along a determinant parameter with velocity `a`, the half-spin action has operator-norm
derivative `(ia/2) Id` times the phase at time `t`. Differentiation is over `ℝ`. -/
theorem hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift (a t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε
      (lieExp (s • spinCGroup.realDetLieLift 4 hpos a)))
      ((Complex.I * (a / 2) * (Circle.exp (t * a / 2) : ℂ)) • (1 : S →L[ℂ] S)) t := by
  simp only [spinCGroup.lieExp_smul_realDetLieLift, realSpinCHalfSpinSmoothHom_ofCircle,
    Circle.coe_exp]
  have harg : HasDerivAt (fun s : ℝ ↦ ((s * a / 2 : ℝ) : ℂ) * Complex.I)
      (((a / 2 : ℝ) : ℂ) * Complex.I) t := by
    simpa only [one_mul, id_eq] using
      ((((hasDerivAt_id t).mul_const a).div_const 2).ofReal_comp).mul_const Complex.I
  convert ((Complex.hasDerivAt_exp _).comp t harg).smul_const (1 : S →L[ℂ] S) using 1
  · funext s
    simp only [Function.comp_apply]
  · congr 1
    push_cast
    ring

/-- At the identity the determinant ray acts infinitesimally by `(ia/2) Id`. -/
theorem hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift_zero (a : ℝ) :
    HasDerivAt (fun s : ℝ ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε
      (lieExp (s • spinCGroup.realDetLieLift 4 hpos a)))
      ((Complex.I * (a / 2)) • (1 : S →L[ℂ] S)) 0 := by
  simpa using
    hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift o hQ b ρ ε a 0

/-- The smooth weight-one half-spin representation of compact `Spinᶜ(4)` lifted to the Lie group
`(S →L[ℂ] S)ˣ` of invertible continuous endomorphisms. -/
def realSpinCHalfSpinUnitsSmoothHom :
    ContMDiffMonoidMorphism IC 𝓘(ℝ, S →L[ℂ] S) ∞ SpinC (S →L[ℂ] S)ˣ :=
  (realSpinCHalfSpinSmoothHom o hQ b ρ ε).toHomUnits

/-- Coercing `realSpinCHalfSpinUnitsSmoothHom` back to `S →L[ℂ] S` recovers
`realSpinCHalfSpinSmoothHom`. -/
@[simp]
theorem coe_realSpinCHalfSpinUnitsSmoothHom_apply (x : SpinC) :
    (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε x : S →L[ℂ] S) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε x :=
  (realSpinCHalfSpinSmoothHom o hQ b ρ ε).coe_toHomUnits x

/-- Along any Lie-algebra ray `s ↦ exp(s • Z)` in `Spinᶜ(4)`, the smooth half-spin action has
initial velocity equal to its Lie differential in canonical endomorphism coordinates. -/
theorem hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_zero
    (Z : LeftInvariantDerivation IC SpinC) :
    HasDerivAt (fun s : ℝ ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε (lieExp (s • Z)))
      (unitsLieAlgebraEquiv (lieMap (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε) Z)) 0 := by
  let _ : T2Space SpinC := ModelWithCorners.t2Space_of_lieGroup IC ∞
  exact ((realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε).hasDerivAt_lieExp_smul_val_zero
    Z).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s ↦
        (coe_realSpinCHalfSpinUnitsSmoothHom_apply o hQ b ρ ε (lieExp (s • Z))).symm)

/-- On the central determinant lift `realDetLieLift 4 hpos a`, the differentiated half-spin
representation acts by `(ia/2) Id`, reflecting weight `1` of the spinor action versus weight `2` of
the determinant character. -/
@[simp↓ high]
theorem unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realDetLieLift (a : ℝ) :
    unitsLieAlgebraEquiv
        (lieMap (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε)
          (spinCGroup.realDetLieLift 4 hpos a)) =
      (Complex.I * (a / 2)) • (1 : S →L[ℂ] S) := by
  let _ : T2Space SpinC := ModelWithCorners.t2Space_of_lieGroup IC ∞
  refine (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε).unitsLieAlgebraEquiv_lieMap_eq_of_hasDerivAt
    (spinCGroup.realDetLieLift 4 hpos a) ?_
  exact (hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift_zero
    o hQ b ρ ε a).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s ↦
      coe_realSpinCHalfSpinUnitsSmoothHom_apply o hQ b ρ ε _)

/-- Restricting the smooth `Spinᶜ(4)` half-spin units homomorphism to `Spin(4)` along `ofSpin`
agrees with `realHalfSpinSmoothHom` transported via
`realCliffordSpinContinuousMulEquivUnitsRange`. -/
theorem realSpinCHalfSpinUnitsSmoothHom_comp_ofSpin :
    (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε).comp
        ((spinCGroup.ofSpinContinuousMonoidHom _ hpos).toContMDiffMonoidMorphism
          𝓘(ℝ, realSpinLieModel 4) IC) =
      (realHalfSpinSmoothHom o hQ b ρ ε).comp
        ((realCliffordSpinContinuousMulEquivUnitsRange 4 :
          spinGroup (realCliffordForm 4 0) →ₜ*
            MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm 4 0)))
          |>.toContMDiffMonoidMorphism
            𝓘(ℝ, realSpinLieModel 4) 𝓘(ℝ, realSpinLieModel 4)) := by
  apply DFunLike.coe_injective
  funext s
  apply Units.ext
  simp [realSpinCHalfSpinSmoothHom_ofSpin, realHalfSpinSmoothHom_apply]

/-- On the Spin summand `ofSpin_* X`, the differentiated `Spinᶜ(4)` half-spin representation agrees
with the framed even Clifford action evaluated on the quadratic Clifford coordinate of `X`. -/
@[simp↓ high]
theorem unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_ofSpin
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel 4) (spinGroup (realCliffordForm 4 0))) :
    unitsLieAlgebraEquiv
        (lieMap (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε)
          (ContinuousMonoidHom.lieMap (I := 𝓘(ℝ, realSpinLieModel 4)) (I' := IC)
            (spinCGroup.ofSpinContinuousMonoidHom _ hpos) X)) =
      LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
        (realQuadraticLieSubalgebraEvenIncl 4 (realSpinLieEquivQuadratic 4 X)))) := by
  let IS := 𝓘(ℝ, realSpinLieModel 4)
  let φ := realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε
  let ψ := realHalfSpinSmoothHom o hQ b ρ ε
  let f := spinCGroup.ofSpinContinuousMonoidHom (realCliffordForm 4 0) hpos
  -- Factor through the restricted smooth representation `φ ∘ ofSpin` on `Spin(4)`, which agrees
  -- with `ψ` transported along `realCliffordSpinContinuousMulEquivUnitsRange`.
  have hlie :
      lieMap φ (ContinuousMonoidHom.lieMap (I := IS) (I' := IC) f X) =
        lieMap ψ (realSpinLieEquivUnitsRange 4 X) := by
    calc
      lieMap φ (ContinuousMonoidHom.lieMap (I := IS) (I' := IC) f X)
        = lieMap (φ.comp (f.toContMDiffMonoidMorphism IS IC)) X := by
          rw [ContinuousMonoidHom.lieMap_def, ← LieHom.comp_apply, ← lieMap_comp]
      _ = lieMap (ψ.comp ((realCliffordSpinContinuousMulEquivUnitsRange 4 :
            spinGroup (realCliffordForm 4 0) →ₜ*
              MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm 4 0)))
            |>.toContMDiffMonoidMorphism IS IS)) X := by
          rw [realSpinCHalfSpinUnitsSmoothHom_comp_ofSpin]
      _ = lieMap ψ (realSpinLieEquivUnitsRange 4 X) := by
          symm
          simp only [IS, realSpinLieEquivUnitsRange_apply, ContinuousMonoidHom.lieMap_def,
            lieMap_comp, LieHom.comp_apply]
  rw [hlie, ← TauCeti.Lie.unitsLieAlgebraLieEquiv_apply (R := S →L[ℂ] S),
    unitsLieAlgebraLieEquiv_lieMap_realHalfSpinSmoothHom]
  simp only [realSpinLieEquivQuadratic_apply, realQuadraticLieSubalgebraEvenIncl_apply]

/-- In Spin–determinant coordinates `(X, a)`, the differentiated `Spinᶜ(4)` half-spin
representation acts by the sum of the framed even Clifford action of `X` and `(ia/2) Id`. -/
@[simp↓ high]
theorem unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realSpinProdDetLinearEquiv
    (p : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel 4) (spinGroup (realCliffordForm 4 0)) × ℝ) :
    unitsLieAlgebraEquiv
        (lieMap (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε)
          (spinCGroup.realSpinProdDetLinearEquiv 4 hpos p)) =
      LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
        (realQuadraticLieSubalgebraEvenIncl 4 (realSpinLieEquivQuadratic 4 p.1)))) +
        (Complex.I * (p.2 / 2)) • (1 : S →L[ℂ] S) := by
  rw [spinCGroup.realSpinProdDetLinearEquiv_apply]
  simp only [map_add,
    unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_ofSpin,
    unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realDetLieLift]

/-- In quadratic Clifford–determinant coordinates `(q, a)`, the differentiated `Spinᶜ(4)` half-spin
representation acts by the framed even Clifford action of `q` plus `(ia/2) Id`. -/
@[simp↓ high]
theorem unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realQuadraticProdDetLinearEquiv
    (p : quadraticLieSubalgebra (realCliffordForm 4 0) × ℝ) :
    unitsLieAlgebraEquiv
        (lieMap (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε)
          (spinCGroup.realQuadraticProdDetLinearEquiv 4 hpos p)) =
      LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
        (realQuadraticLieSubalgebraEvenIncl 4 p.1))) +
        (Complex.I * (p.2 / 2)) • (1 : S →L[ℂ] S) := by
  rw [spinCGroup.realQuadraticProdDetLinearEquiv_apply,
    unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realSpinProdDetLinearEquiv,
    (realSpinLieEquivQuadratic 4).apply_symm_apply p.1]

/-- In `𝔰𝔬(4) × ℝ` coordinates, the differentiated `Spinᶜ(4)` half-spin representation acts by the
framed even Clifford action of the lifted quadratic Clifford coordinate of `A ∈ 𝔰𝔬(4)` plus
`(ia/2) Id`. -/
@[simp↓ high]
theorem unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realSoProdDetLinearEquiv
    (p : LieAlgebra.Orthogonal.so (Fin 4) ℝ × ℝ) :
    let q := (realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv 4).symm p.1
    unitsLieAlgebraEquiv
        (lieMap (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε)
          (spinCGroup.realSoProdDetLinearEquiv 4 hpos p)) =
      LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
        (realQuadraticLieSubalgebraEvenIncl 4 q))) +
        (Complex.I * (p.2 / 2)) • (1 : S →L[ℂ] S) := by
  rw [spinCGroup.realSoProdDetLinearEquiv_eq_realQuadraticProdDetLinearEquiv,
    unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realQuadraticProdDetLinearEquiv]

/-- **Differentiated `Spinᶜ(4)` half-spin action in `𝔰𝔬(4) × ℝ` coordinates**: a skew-symmetric
matrix `A ∈ 𝔰𝔬(4)` and real determinant parameter `a ∈ ℝ` act on half-spinors as the framed even
Clifford action of the normalized bivector of `A` plus `(ia/2) Id`. -/
theorem
    unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realSoProdDetLinearEquiv_bivector
    (p : LieAlgebra.Orthogonal.so (Fin 4) ℝ × ℝ) :
    let Q₀ := QuadraticMap.weightedSumSquares ℝ (1 : Fin 4 → ℝ)
    letI := bivectorLieRing Q₀
    letI := bivectorLieAlgebra Q₀
    unitsLieAlgebraEquiv
        (lieMap (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε)
          (spinCGroup.realSoProdDetLinearEquiv 4 hpos p)) =
      LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
        (realQuadraticLieSubalgebraEvenIncl 4
          (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm 4 0)
            ((bivectorEquivSo 4 ℝ).symm p.1))))) +
        (Complex.I * (p.2 / 2)) • (1 : S →L[ℂ] S) := by
  let Q₀ := QuadraticMap.weightedSumSquares ℝ (1 : Fin 4 → ℝ)
  let _ := bivectorLieRing Q₀
  let _ := bivectorLieAlgebra Q₀
  rw [unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realSoProdDetLinearEquiv,
    realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv_symm_eq_bivector]

end DeterminantDerivative

/-- The half-spin action is smooth jointly in the Spinᶜ element and spinor. -/
theorem contMDiff_realSpinCHalfSpinSmoothHom_apply :
    ContMDiff (ModelWithCorners.prod IC 𝓘(ℝ, S)) 𝓘(ℝ, S) ∞
      (fun p : SpinC × S ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε p.1 p.2) :=
  (((ContinuousLinearMap.restrictScalarsL ℂ S S ℝ ℝ).contDiff.contMDiff.comp
    (realSpinCHalfSpinSmoothHom o hQ b ρ ε).contMDiff_toFun).comp
      contMDiff_fst).clm_apply contMDiff_snd

/-- Odd Clifford multiplication intertwines the two descended half-spin actions, with
vectors rotated by the actual Spinᶜ frame projection and then compared through `b`. -/
theorem realSpinCHalfSpinSmoothHom_comp_halfSpinCliffordMul
    (x : SpinC) (v : Fin (4 + 0) → ℝ) :
    (realSpinCHalfSpinSmoothHom o hQ b ρ (-ε) x).toLinearMap ∘ₗ
        halfSpinCliffordMul o ρ ε (b.negRealCliffordFormIsometryEquiv hQ v) =
      halfSpinCliffordMul o ρ ε (b.negRealCliffordFormIsometryEquiv hQ
        ((spinCGroup.toSpecialOrthogonal _ hpos x :
          (Fin (4 + 0) → ℝ) ≃ₗ[ℝ] (Fin (4 + 0) → ℝ)) v)) ∘ₗ
        (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).toLinearMap := by
  simp only [realSpinCHalfSpinSmoothHom_apply o hQ b _ _ hQ₀,
    LinearMap.coe_toContinuousLinearMap]
  rw [spinCGroupHalfSpinRep_comp_halfSpinCliffordMul,
    OrthonormalBasis.toSpecialOrthogonal_realSpinCGroupHom_apply]

/-- In complex rank two the determinant of the descended half-spin action is the
weight-two character, not the weight-one spinor character. -/
@[simp]
theorem det_realSpinCHalfSpinSmoothHom (h₂ : finrank ℂ S = 2) (x : SpinC) :
    LinearMap.det (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).toLinearMap =
      (spinCGroup.det _ hpos x : ℂ) := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    LinearMap.coe_toContinuousLinearMap, det_spinCGroupHalfSpinRep o ρ ε hQ₀ hQ h₂,
    OrthonormalBasis.det_realSpinCGroupHom]

/-! ### The half-spinor representation spaces -/

/-- The `ε`-eigenspace of the chirality element on the Clifford module `W`, on which `Spinᶜ(4)`
acts by the weight-one half-spin representation `[s, z] ↦ z ρ(s)`
(`Orientation.realSpinCHalfSpinSmoothHom`), compared with the geometric Clifford model through
the orthonormal frame `b`. It is the model fiber of the spinor bundle `W^ε`. -/
def SpinCHalfSpinor (_o : Orientation ℝ V (Fin 4)) (_hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (_b : OrthonormalBasis (Fin 4) ℝ V) (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ) :
    Type _ :=
  eigenspace (ρ (chirality Q _o)) ε

namespace SpinCHalfSpinor

instance : NormedAddCommGroup (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (NormedAddCommGroup S)

instance : NormedSpace ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (NormedSpace ℂ S)

instance : FiniteDimensional ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (FiniteDimensional ℂ S)

/-- The half-spinor model is the `ε`-eigenspace of the chirality element. -/
def linearEquiv : SpinCHalfSpinor o hQ b ρ ε ≃ₗ[ℂ] S :=
  LinearEquiv.refl ℂ _

omit [FiniteDimensional ℂ W] in
/-- The identification of the half-spinor model with the chirality eigenspace of `W` preserves
norms. -/
@[simp]
theorem norm_linearEquiv (ψ : SpinCHalfSpinor o hQ b ρ ε) :
    ‖(linearEquiv o hQ b ρ ε ψ : W)‖ = ‖ψ‖ :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- The half-spinor model has the dimension of the chirality eigenspace. -/
theorem finrank_eq : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = finrank ℂ S :=
  (linearEquiv o hQ b ρ ε).finrank_eq

/-- `Spinᶜ(4)` acts on the half-spinor model by the half-spin representation. -/
instance : DistribMulAction SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  letI : DistribMulAction SpinC S :=
    DistribMulAction.compHom S (realSpinCHalfSpinSmoothHom o hQ b ρ ε).toMonoidHom
  inferInstanceAs (DistribMulAction SpinC S)

/-- Under the identification with the chirality eigenspace, `Spinᶜ(4)` acts on the half-spinor
model by the half-spin representation. -/
@[simp]
theorem linearEquiv_smul (x : SpinC) (ψ : SpinCHalfSpinor o hQ b ρ ε) :
    linearEquiv o hQ b ρ ε (x • ψ) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε x (linearEquiv o hQ b ρ ε ψ) := (rfl)

/-- The action of `Spinᶜ(4)` on the half-spinor model, transported from the chirality
eigenspace. -/
theorem smul_def (x : SpinC) (ψ : SpinCHalfSpinor o hQ b ρ ε) :
    x • ψ = (linearEquiv o hQ b ρ ε).symm
      (realSpinCHalfSpinSmoothHom o hQ b ρ ε x (linearEquiv o hQ b ρ ε ψ)) := by
  rw [LinearEquiv.eq_symm_apply, linearEquiv_smul]

instance : SMulCommClass SpinC ℂ (SpinCHalfSpinor o hQ b ρ ε) where
  smul_comm x c ψ := (linearEquiv o hQ b ρ ε).injective <| by
    simp only [linearEquiv_smul, map_smul]

instance : SMulCommClass SpinC ℝ (SpinCHalfSpinor o hQ b ρ ε) where
  smul_comm x c ψ := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_comm]

/-- The half-spin action is smooth. -/
instance : ContMDiffSMul IC 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε) ∞ SpinC
    (SpinCHalfSpinor o hQ b ρ ε) where
  contMDiff_smul := by
    let e : SpinCHalfSpinor o hQ b ρ ε ≃L[ℝ] S :=
      ((linearEquiv o hQ b ρ ε).toContinuousLinearEquiv).restrictScalars ℝ
    have he : ContMDiff (ModelWithCorners.prod IC 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε))
        (ModelWithCorners.prod IC 𝓘(ℝ, S)) ∞
        (fun p : SpinC × SpinCHalfSpinor o hQ b ρ ε ↦ (p.1, e p.2)) :=
      contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)
    simp only [smul_def]
    exact e.symm.contDiff.contMDiff.comp
      ((contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε).comp he)

instance : ContinuousSMul SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  ContMDiffSMul.continuousSMul («I» := IC) (I' := 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε)) ∞

/-- The action of `g` on the half-spinor model, as a linear map, has the determinant of the
half-spin representation at `g`. -/
theorem det_toLinearMap (g : SpinC) :
    LinearMap.det (DistribSMul.toLinearMap ℂ (SpinCHalfSpinor o hQ b ρ ε) g) =
      LinearMap.det (realSpinCHalfSpinSmoothHom o hQ b ρ ε g).toLinearMap :=
  LinearMap.det_eq_of_comp_eq (linearEquiv o hQ b ρ ε)
    (LinearMap.ext fun ψ ↦ linearEquiv_smul o hQ b ρ ε g ψ)

/-- If the half-spinor model is two-dimensional, every alternating two-form on it with values
in the model determinant fiber is `Spinᶜ(4)`-equivariant: the half-spin action has determinant
`[s, z] ↦ z²`, the determinant character. -/
theorem alternatingMap_apply_smul (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) (g : SpinC)
    (v : Fin 2 → SpinCHalfSpinor o hQ b ρ ε) :
    η (fun i ↦ g • v i) = g • η v := by
  have h := congrArg (fun η' ↦ η' v) (AlternatingMap.compLinearMap_eq_det_smul
    (Module.finBasisOfFinrankEq ℂ (SpinCHalfSpinor o hQ b ρ ε) h₂) η
    (DistribSMul.toLinearMap ℂ _ g))
  simp only [AlternatingMap.compLinearMap_apply, DistribSMul.toLinearMap_apply,
    smul_apply, det_toLinearMap,
    det_realSpinCHalfSpinSmoothHom o hQ b ρ ε ((finrank_eq o hQ b ρ ε).symm.trans h₂)] at h
  rw [h, spinCGroup.DetFiber.smul_def]

end SpinCHalfSpinor

end Normed

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

/-- The descended action is unitary when the Clifford generators are skew-adjoint. -/
theorem inner_realSpinCHalfSpinSmoothHom_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (x : SpinC) (ψ χ : S) :
    ⟪realSpinCHalfSpinSmoothHom o hQ b ρ ε x ψ,
      realSpinCHalfSpinSmoothHom o hQ b ρ ε x χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  simp only [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    LinearMap.coe_toContinuousLinearMap']
  exact inner_spinCGroupHalfSpinRep_apply_spinCGroupHalfSpinRep_apply o ε hρ hQ₀ _ ψ χ

/-- The half-spinor model of a Hermitian Clifford module is a complex inner product space. -/
instance : InnerProductSpace ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (InnerProductSpace ℂ S)

omit [FiniteDimensional ℂ W] in
/-- The identification of the half-spinor model with the chirality eigenspace of `W` preserves
inner products. -/
@[simp]
theorem SpinCHalfSpinor.inner_linearEquiv_linearEquiv (ψ χ : SpinCHalfSpinor o hQ b ρ ε) :
    ⟪(SpinCHalfSpinor.linearEquiv o hQ b ρ ε ψ : W),
      (SpinCHalfSpinor.linearEquiv o hQ b ρ ε χ : W)⟫_ℂ = ⟪ψ, χ⟫_ℂ :=
  (rfl)

/-- If the Clifford generators act skew-adjointly on `W`, `Spinᶜ(4)` acts unitarily on the
half-spinor model. -/
theorem SpinCHalfSpinor.inner_smul_smul (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (g : SpinC) (ψ χ : SpinCHalfSpinor o hQ b ρ ε) : ⟪g • ψ, g • χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  rw [← SpinCHalfSpinor.inner_linearEquiv_linearEquiv, SpinCHalfSpinor.linearEquiv_smul,
    SpinCHalfSpinor.linearEquiv_smul, ← Submodule.coe_inner,
    inner_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hρ, Submodule.coe_inner,
    SpinCHalfSpinor.inner_linearEquiv_linearEquiv]

/-- If the Clifford generators act skew-adjointly on `W`, `Spinᶜ(4)` acts isometrically on the
half-spinor model. -/
theorem SpinCHalfSpinor.isIsometricSMul (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    IsIsometricSMul SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  ⟨fun g ↦ AddMonoidHomClass.isometry_of_norm (DistribSMul.toAddMonoidHom _ g) fun ψ ↦ by
    rw [DistribSMul.toAddMonoidHom_apply, @norm_eq_sqrt_re_inner ℂ,
      @norm_eq_sqrt_re_inner ℂ, SpinCHalfSpinor.inner_smul_smul o hQ b ρ ε hρ]⟩

end Orientation
