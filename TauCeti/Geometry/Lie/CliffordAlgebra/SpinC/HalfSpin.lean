/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Determinant
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.HalfSpinor
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Frame
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Smooth half-spin representations of the Spinᶜ quotient

An orthonormal frame compares compact coordinate Spin with the negative-metric geometric
Clifford model. The weight-one half-spin action is already smooth on the covering group.
Here it descends smoothly through the actual diagonal central quotient, acting on the actual
chirality eigenspaces rather than on separately chosen matrix spaces.

The descended actions preserve the Hermitian inner product when Clifford generators are
skew-adjoint. In complex rank two their determinant is the weight-two character `[s,z] ↦ z²`.
The central determinant half-parameter path has operator-norm derivative `(ia/2) Id` at the
identity. No choice of orientation of the frame is needed to descend the action on a fixed
eigenspace; identifying the two coordinate SU(2) factors with positive and negative chirality
requires a positively oriented frame separately. Changing between equally oriented orthonormal
frames conjugates `Orientation.realSpinCHalfSpinSmoothHom` by a compact Spin element
(`Orientation.exists_realSpinCHalfSpinSmoothHom_eq_conj`), and unitary Clifford intertwiners
along oriented linear isometries intertwine the descended actions
(`Orientation.halfSpinLinearIsometryEquiv_realSpinCHalfSpinSmoothHom_apply`,
`Orientation.realSpinCHalfSpinSmoothHom_intertwine_apply`).

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
local notation "I" => ModelWithCorners.prod 𝓘(ℝ, realSpinLieModel 4) (𝓡 1)

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

/-- The smooth weight-one half-spin representation of compact Spinᶜ(4), after comparison
with the negative-metric Clifford model in the frame `b`. -/
def realSpinCHalfSpinSmoothHom : ContMDiffMonoidMorphism I 𝓘(ℝ, S →L[ℂ] S) ∞
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

section DeterminantDerivative

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

end DeterminantDerivative

/-- Restriction to Spin is the half-spin action in the selected frame. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_ofSpin (s : spinGroup (realCliffordForm 4 0)) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofSpin _ hpos s) =
      (halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s)).toContinuousLinearMap := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    OrthonormalBasis.realSpinCGroupHom_ofSpin, spinCGroupHalfSpinRep_ofSpin]

/-- The half-spin action is smooth jointly in the Spinᶜ element and spinor. -/
theorem contMDiff_realSpinCHalfSpinSmoothHom_apply :
    ContMDiff (ModelWithCorners.prod I 𝓘(ℝ, S)) 𝓘(ℝ, S) ∞
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

/-- Changing between two equally oriented orthonormal frames `b` and `b'` conjugates
`realSpinCHalfSpinSmoothHom` by the image of a compact Spin element in `Spinᶜ(4)`. -/
theorem exists_realSpinCHalfSpinSmoothHom_eq_conj {b' : OrthonormalBasis (Fin 4) ℝ V}
    (hb : b.toBasis.orientation = b'.toBasis.orientation) :
    ∃ s₀ : spinGroup (realCliffordForm 4 0),
      ∀ (x : SpinC) (ψ : S),
        realSpinCHalfSpinSmoothHom o hQ b' ρ ε x ψ =
          realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofSpin (realCliffordForm 4 0) hpos s₀)
            (realSpinCHalfSpinSmoothHom o hQ b ρ ε x
              (realSpinCHalfSpinSmoothHom o hQ b ρ ε
                (spinCGroup.ofSpin (realCliffordForm 4 0) hpos s₀)⁻¹ ψ)) := by
  have hconj := b.exists_realSpinCGroupHom_eq_conj b' hQ hb hpos hQ₀
  refine ⟨hconj.choose, fun x ψ ↦ ?_⟩
  simp only [realSpinCHalfSpinSmoothHom_apply o hQ b' ρ ε hQ₀,
    realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀, hconj.choose_spec x, map_mul,
    LinearMap.coe_toContinuousLinearMap', mul_apply_eq_comp]

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
instance : ContMDiffSMul I 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε) ∞ SpinC
    (SpinCHalfSpinor o hQ b ρ ε) where
  contMDiff_smul := by
    let e : SpinCHalfSpinor o hQ b ρ ε ≃L[ℝ] S :=
      ((linearEquiv o hQ b ρ ε).toContinuousLinearEquiv).restrictScalars ℝ
    have he : ContMDiff (ModelWithCorners.prod I 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε))
        (ModelWithCorners.prod I 𝓘(ℝ, S)) ∞
        (fun p : SpinC × SpinCHalfSpinor o hQ b ρ ε ↦ (p.1, e p.2)) :=
      contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)
    simp only [smul_def]
    exact e.symm.contDiff.contMDiff.comp
      ((contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε).comp he)

instance : ContinuousSMul SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  ContMDiffSMul.continuousSMul («I» := I) (I' := 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε)) ∞

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
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective (realCliffordForm 4 0) hpos x
  let e : Q →qᵢ Q' :=
    { toLinearMap := f.toLinearMap
      map_app' v := by simp [hQ', hQ] }
  simp [spinCHalfSpinRep_apply, halfSpinRep_apply,
    b.realEvenCliffordEquiv_map hQ hQ' f e (fun _ ↦ rfl)]
  simpa using LinearMap.congr_fun
    (halfSpinLinearIsometryEquiv_comp_evenHalfSpinAction o' ho hU e (fun _ ↦ rfl) ε
      (b.realEvenCliffordEquiv hQ (spinGroupToEven _ s))) ψ

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
  have hb_refl : b.map (.refl ℝ V) = b := DFunLike.ext _ _ fun _ ↦ by simp
  simpa [hb_refl] using
    halfSpinLinearIsometryEquiv_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε o hQ
      (f := .refl ℝ V) (by simp) hU x ψ

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
