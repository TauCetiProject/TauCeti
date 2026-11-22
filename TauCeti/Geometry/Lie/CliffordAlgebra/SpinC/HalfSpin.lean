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
  let Z := spinCGroup.realDetLieLift 4 hpos a
  exact (hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_zero o hQ b ρ ε Z).unique
    (hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift_zero o hQ b ρ ε a)

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
  let g : spinGroup (realCliffordForm 4 0) →ₜ*
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm 4 0)) :=
    realCliffordSpinContinuousMulEquivUnitsRange 4
  have hlieHom :
      (lieMap φ).comp (ContinuousMonoidHom.lieMap (I := IS) (I' := IC) f) =
        (lieMap ψ).comp (ContinuousMonoidHom.lieMap (I := IS) (I' := IS) g) := by
    simpa only [lieMap_comp, ← ContinuousMonoidHom.lieMap_def] using
      congrArg lieMap (realSpinCHalfSpinUnitsSmoothHom_comp_ofSpin o hQ b ρ ε)
  have hlie :
      lieMap φ (ContinuousMonoidHom.lieMap (I := IS) (I' := IC) f X) =
        lieMap ψ (realSpinLieEquivUnitsRange 4 X) := by
    simpa only [LieHom.comp_apply, realSpinLieEquivUnitsRange_apply] using
      LieHom.congr_fun hlieHom X
  calc
    unitsLieAlgebraEquiv (lieMap φ (ContinuousMonoidHom.lieMap (I := IS) (I' := IC) f X))
        = unitsLieAlgebraEquiv (lieMap ψ (realSpinLieEquivUnitsRange 4 X)) :=
          congrArg unitsLieAlgebraEquiv hlie
    _ = TauCeti.Lie.unitsLieAlgebraLieEquiv (R := S →L[ℂ] S)
          (lieMap ψ (realSpinLieEquivUnitsRange 4 X)) :=
          (TauCeti.Lie.unitsLieAlgebraLieEquiv_apply (R := S →L[ℂ] S) _).symm
    _ = LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
          ⟨realCliffordSpinLieEquivQuadratic 4 (realSpinLieEquivUnitsRange 4 X),
            quadraticLieSubalgebra_le_even _
              (realCliffordSpinLieEquivQuadratic 4
                (realSpinLieEquivUnitsRange 4 X)).property⟩)) :=
          unitsLieAlgebraLieEquiv_lieMap_realHalfSpinSmoothHom o hQ b ρ ε
            (realSpinLieEquivUnitsRange 4 X)
    _ = LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
          (realQuadraticLieSubalgebraEvenIncl 4 (realSpinLieEquivQuadratic 4 X)))) := by
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
        (Complex.I * (p.2 / 2)) • (1 : S →L[ℂ] S) :=
  let φ := realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε
  (congrArg (fun Z ↦ unitsLieAlgebraEquiv (lieMap φ Z))
      (spinCGroup.realSpinProdDetLinearEquiv_apply 4 hpos p)).trans <|
    (congrArg unitsLieAlgebraEquiv ((lieMap φ).map_add _ _)).trans <|
    (unitsLieAlgebraEquiv.map_add _ _).trans <|
    congrArg₂ (· + ·)
      (unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_ofSpin o hQ b ρ ε p.1)
      (unitsLieAlgebraEquiv_lieMap_realSpinCHalfSpinUnitsSmoothHom_realDetLieLift o hQ b ρ ε p.2)

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

end Orientation
