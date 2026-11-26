/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.HalfSpin
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.LinearAlgebra.Determinant.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic
public import TauCeti.Topology.VectorBundle.Associated.Bilinear
public import TauCeti.Topology.VectorBundle.Associated.Metric
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

/-!
# Spinor bundles and the determinant line of a `Spinᶜ` structure

Let `s` be a `Spinᶜ` structure on a real vector bundle `E → X` with fibre inner products
(`TauCeti.SpinCStructure`), with principal `Spinᶜ(n)`-bundle `P`. This file constructs the
complex vector bundles associated to `P` on which Seiberg–Witten theory is set up.

**The determinant line.** For every rank `n ≥ 1`, `Spinᶜ(n)` acts on `ℂ` through its determinant
character `[s, z] ↦ z²` (`CliffordAlgebra.spinCGroup.det`). The associated bundle
`L = P ×_{z²} ℂ` is the determinant line of `s` (`TauCeti.SpinCStructure.determinantLine`), a
Hermitian line bundle on which the central circle `[1, z]` acts with weight two.

**The half-spinor bundles.** In rank four, fix a model Hermitian Clifford module: an oriented
real inner product space `V` of dimension four with `Q v = -‖v‖²`, an orthonormal basis `b` of
`V`, and a complex inner product space `W` with a Clifford action `ρ` by skew-adjoint generators.
The half-spin representation `[s, z] ↦ z ρ(s)` of `Spinᶜ(4)` on the `ε`-eigenspace `S^ε` of the
chirality operator, compared with the coordinate group through `b`
(`Orientation.realSpinCHalfSpinSmoothHom`), is continuous and unitary, so the associated bundle
`W^ε = P ×_{Spinᶜ(4)} S^ε` (`TauCeti.SpinCStructure.halfSpinorBundle`) is a Hermitian vector bundle.
When `b` is positively oriented for `o` (`b.toBasis.orientation = o`), the bundles for `ε = 1` and
`ε = -1` are the positive and negative half-spinor bundles `W⁺` and `W⁻` for the orientation of `E`
chosen by `s`; when `b` is negatively oriented for `o`, the two labels are exchanged.
The central circle acts on them with weight one. Each point `p` of `P` over `x` is a unitary frame
`S^ε ≃ W^ε_x`, and changing `p` acts by the half-spin representation.

**Clifford multiplication.** A point `p` of `P` over `x` also gives an orthonormal frame of
`E x` (`TauCeti.OrthonormalFrameLift.frameAt`), hence a linear isometry `κ_p : E x ≃ V` through
`b` (`TauCeti.SpinCStructure.vectorFrame`). Clifford multiplication `c(v) : W^ε_x → W^{ε'}_x`
by `v ∈ E x`, for `ε' = -ε` (`TauCeti.SpinCStructure.cliffordMul`), is `c(κ_p v)` in the frame
`p`. It does not depend on `p`,
because the half-spin representations intertwine Clifford multiplication with the rotation action
of `Spinᶜ(4)` on vectors, and the frames of `E` are equivariant along the same rotation. It
satisfies the Clifford relation `c(v) c(v) = -‖v‖²` and `c(v)* = -c(v)`.

**The determinant of the half-spinor bundles.** When `S^ε` has complex dimension two, a nonzero
alternating form `ω` on `S^ε` transforms under `[s, z]` by the determinant `z²` of the half-spin
representation, so the model pairing `(ψ₁, ψ₂) ↦ ω(ψ₁, ψ₂)` with values in the determinant model
(`TauCeti.SpinCStructure.halfSpinorDetPairing`) is equivariant. It descends
(`TauCeti.AssociatedBundle.bilinearMap`) to an alternating map `W^ε_x × W^ε_x → L_x`, given by `ω`
in every frame `p` (`TauCeti.SpinCStructure.halfSpinorDetAlternatingMap`), which induces a linear
isomorphism `⋀² W^ε_x ≃ L_x` (`TauCeti.SpinCStructure.exteriorPowerHalfSpinorEquiv`). Thus, for `b`
positively oriented for `o`, `det W⁺ ≃ L ≃ det W⁻` on every fibre, the determinant line of the
half-spinors being the square of the twisting circle.

## Main definitions

* `Orientation.HalfSpinModel o hQ b ρ hρ ε`: the eigenspace `S^ε` with its action of `Spinᶜ(4)`.
* `TauCeti.SpinCStructure.DeterminantModel n`: `ℂ` with `Spinᶜ(n)` acting by `z²`.
* `TauCeti.SpinCStructure.determinantLine`: the determinant line `L` of a `Spinᶜ` structure.
* `TauCeti.SpinCStructure.halfSpinorBundle`: the half-spinor bundle `W^ε` of a `Spinᶜ` structure
  of rank four.
* `TauCeti.SpinCStructure.vectorFrame`: the linear isometry `κ_p : E x ≃ V` of a frame `p`.
* `TauCeti.SpinCStructure.cliffordMul`: Clifford multiplication `E x → Hom(W^ε_x, W^{ε'}_x)`.
* `TauCeti.SpinCStructure.halfSpinorDetPairing`: an alternating form on `S^ε` as a bilinear map to
  the determinant model.
* `TauCeti.SpinCStructure.halfSpinorDetAlternatingMap`,
  `TauCeti.SpinCStructure.exteriorPowerHalfSpinorEquiv`: the isomorphism `⋀² W^ε_x ≃ L_x`.

## Main results

* `Orientation.HalfSpinModel.smul_cliffordMul`: model Clifford multiplication is equivariant.
* `TauCeti.SpinCStructure.finrank_determinantLine`: `L` is a line bundle.
* `TauCeti.SpinCStructure.mk_ofCircle_smul_determinantLine`,
  `TauCeti.SpinCStructure.mk_ofCircle_smul_halfSpinorBundle`: the central circle acts with weight
  two on `L` and weight one on `W^ε`.
* `TauCeti.SpinCStructure.cliffordMul_mk`: Clifford multiplication in every frame.
* `TauCeti.SpinCStructure.cliffordMul_cliffordMul`: the Clifford relation `c(v) c(v) = -‖v‖²`.
* `TauCeti.SpinCStructure.inner_cliffordMul_left`: `c(v)` is skew-adjoint.
* `TauCeti.SpinCStructure.norm_cliffordMul`: `‖c(v) ψ‖ = ‖v‖ ‖ψ‖`.
* `TauCeti.SpinCStructure.exteriorPowerHalfSpinorEquiv_ιMulti`: the isomorphism `⋀² W^ε_x ≃ L_x`
  on decomposable elements.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1–3.2.
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §3 and Appendix D.
-/

public section

noncomputable section

open Bundle MulOpposite Module Module.End TauCeti CliffordAlgebra TauCeti.CliffordAlgebra
open scoped InnerProductSpace

universe w

/-! ### The model half-spinors -/

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ)

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-- The **model half-spinors** `S^ε`: the `ε`-eigenspace of the chirality operator of a Hermitian
Clifford module `W`, as a type on which `Spinᶜ(4)` acts by the half-spin representation
`[s, z] ↦ z ρ(s)`, compared with the coordinate group through the orthonormal basis `b`
(`Orientation.realSpinCHalfSpinSmoothHom`). The form `Q v = -‖v‖²` and the skew-adjointness of the
generators are recorded so that the action is defined and unitary. -/
@[expose] def HalfSpinModel (_hQ : ∀ v, Q v = -‖v‖ ^ 2) (_b : OrthonormalBasis (Fin 4) ℝ V)
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (_hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ) : Type _ :=
  eigenspace (ρ (chirality Q o)) ε

namespace HalfSpinModel

instance instNormedAddCommGroup : NormedAddCommGroup (HalfSpinModel o hQ b ρ hρ ε) :=
  inferInstanceAs (NormedAddCommGroup (eigenspace (ρ (chirality Q o)) ε))

instance instInnerProductSpace : InnerProductSpace ℂ (HalfSpinModel o hQ b ρ hρ ε) :=
  inferInstanceAs (InnerProductSpace ℂ (eigenspace (ρ (chirality Q o)) ε))

instance instFiniteDimensional : FiniteDimensional ℂ (HalfSpinModel o hQ b ρ hρ ε) :=
  inferInstanceAs (FiniteDimensional ℂ (eigenspace (ρ (chirality Q o)) ε))

/-- `Spinᶜ(4)` acts on the model half-spinors through the half-spin representation. -/
instance instDistribMulAction : DistribMulAction SpinC (HalfSpinModel o hQ b ρ hρ ε) :=
  DistribMulAction.compHom (eigenspace (ρ (chirality Q o)) ε)
    (realSpinCHalfSpinSmoothHom o hQ b ρ ε).toMonoidHom

variable {o hQ b ρ hρ ε}

/-- The model half-spinors as elements of the `ε`-eigenspace of the chirality operator. -/
def toEigenspace : HalfSpinModel o hQ b ρ hρ ε ≃ₗᵢ[ℂ] eigenspace (ρ (chirality Q o)) ε :=
  LinearIsometryEquiv.refl ℂ _

/-- `[s, z]` acts on `S^ε` by the half-spin representation `z ρ(s)`. -/
@[simp]
theorem toEigenspace_smul (x : SpinC) (ψ : HalfSpinModel o hQ b ρ hρ ε) :
    toEigenspace (x • ψ) = realSpinCHalfSpinSmoothHom o hQ b ρ ε x (toEigenspace ψ) :=
  (rfl)

/-- The central circle acts on the model half-spinors with weight one. -/
@[simp]
theorem ofCircle_smul (z : Circle) (ψ : HalfSpinModel o hQ b ρ hρ ε) :
    spinCGroup.ofCircle _ hpos z • ψ = (z : ℂ) • ψ :=
  toEigenspace.injective (by
    rw [toEigenspace_smul, realSpinCHalfSpinSmoothHom_ofCircle, smul_apply,
      one_apply_eq_self, map_smul])

instance instSMulCommClass : SMulCommClass SpinC ℂ (HalfSpinModel o hQ b ρ hρ ε) where
  smul_comm x c ψ := (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).map_smul c (toEigenspace ψ)

instance instContinuousSMul : ContinuousSMul SpinC (HalfSpinModel o hQ b ρ hρ ε) :=
  ⟨(contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε).continuous⟩

/-- `Spinᶜ(4)` acts unitarily on the model half-spinors. -/
theorem inner_smul_smul (x : SpinC) (ψ φ : HalfSpinModel o hQ b ρ hρ ε) :
    ⟪x • ψ, x • φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
  inner_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hρ x (toEigenspace ψ) (toEigenspace φ)

instance instIsIsometricSMul : IsIsometricSMul SpinC (HalfSpinModel o hQ b ρ hρ ε) where
  isometry_smul x := AddMonoidHomClass.isometry_of_norm (DistribSMul.toAddMonoidHom _ x)
    fun ψ ↦ by
      rw [DistribSMul.toAddMonoidHom_apply, @norm_eq_sqrt_re_inner ℂ,
        @norm_eq_sqrt_re_inner ℂ, inner_smul_smul]

/-- **Clifford multiplication between the model half-spinors** `c(v) : S^ε → S^{ε'}` by `v ∈ V`, for
`ε' = -ε`: the restriction of the Clifford action, `TauCeti.CliffordAlgebra.halfSpinCliffordMul`
read in the `ε'`-eigenspace. -/
def cliffordMul {ε' : ℂ} (hε : ε' = -ε) :
    V →ₗ[ℝ] HalfSpinModel o hQ b ρ hρ ε →ₗ[ℂ] HalfSpinModel o hQ b ρ hρ ε' :=
  LinearMap.compRight ℝ (LinearEquiv.ofEq _ _ (by rw [hε])).toLinearMap ∘ₗ
    halfSpinCliffordMul o ρ ε

/-- Model Clifford multiplication is `TauCeti.CliffordAlgebra.halfSpinCliffordMul`, read in the
`ε'`-eigenspace. -/
theorem toEigenspace_cliffordMul {ε' : ℂ} (hε : ε' = -ε) (v : V)
    (ψ : HalfSpinModel o hQ b ρ hρ ε) :
    toEigenspace (cliffordMul hε v ψ) =
      LinearEquiv.ofEq _ _ (by rw [hε]) (halfSpinCliffordMul o ρ ε v (toEigenspace ψ)) :=
  (rfl)

/-- Model Clifford multiplication is the Clifford action on the underlying vectors of `W`. -/
@[simp]
theorem coe_toEigenspace_cliffordMul {ε' : ℂ} (hε : ε' = -ε) (v : V)
    (ψ : HalfSpinModel o hQ b ρ hρ ε) :
    (toEigenspace (cliffordMul hε v ψ) : W) = ρ (ι Q v) (toEigenspace ψ : W) := by
  rw [toEigenspace_cliffordMul, LinearEquiv.coe_ofEq_apply, coe_halfSpinCliffordMul_apply_apply]

/-- **Clifford equivariance of the model half-spinors**: Clifford multiplication intertwines the
actions of `Spinᶜ(4)` when it acts on vectors through its rotation, compared with `V` through `b`:
`x • c(v) ψ = c(π(x) v) (x • ψ)`. -/
theorem smul_cliffordMul {ε' : ℂ} (hε : ε' = -ε) (x : SpinC) (v : Fin (4 + 0) → ℝ)
    (ψ : HalfSpinModel o hQ b ρ hρ ε) :
    x • cliffordMul hε (b.negRealCliffordFormIsometryEquiv hQ v) ψ =
      cliffordMul hε (b.negRealCliffordFormIsometryEquiv hQ
        ((spinCGroup.toSpecialOrthogonal _ hpos x :
          (Fin (4 + 0) → ℝ) ≃ₗ[ℝ] (Fin (4 + 0) → ℝ)) v)) (x • ψ) := by
  subst hε
  apply toEigenspace.injective
  simpa [toEigenspace_cliffordMul] using LinearMap.congr_fun
    (realSpinCHalfSpinSmoothHom_comp_halfSpinCliffordMul o hQ b ρ ε x v) (toEigenspace ψ)

/-- **The Clifford relation** on the model half-spinors: `c(v) c(v) = -‖v‖²`. -/
theorem cliffordMul_cliffordMul {ε' : ℂ} (hε : ε' = -ε) (v : V)
    (ψ : HalfSpinModel o hQ b ρ hρ ε) :
    cliffordMul (neg_eq_iff_eq_neg.mp hε.symm) v (cliffordMul hε v ψ) =
      ((-‖v‖ ^ 2 : ℝ) : ℂ) • ψ := by
  apply (toEigenspace (o := o) (hQ := hQ) (b := b) (ρ := ρ) (hρ := hρ) (ε := ε)).injective
  apply Subtype.ext
  rw [coe_toEigenspace_cliffordMul, coe_toEigenspace_cliffordMul, map_ι_apply_map_ι_apply, hQ,
    map_smul, Submodule.coe_smul]

/-- **Model Clifford multiplication is skew-adjoint**: `⟪c(v) ψ, φ⟫ = -⟪ψ, c(v) φ⟫`. -/
theorem inner_cliffordMul_left {ε' : ℂ} (hε : ε' = -ε) (v : V)
    (ψ : HalfSpinModel o hQ b ρ hρ ε) (φ : HalfSpinModel o hQ b ρ hρ ε') :
    ⟪cliffordMul hε v ψ, φ⟫_ℂ = -⟪ψ, cliffordMul (neg_eq_iff_eq_neg.mp hε.symm) v φ⟫_ℂ := by
  rw [← LinearIsometryEquiv.inner_map_map toEigenspace (cliffordMul hε v ψ),
    ← LinearIsometryEquiv.inner_map_map toEigenspace ψ, Submodule.coe_inner, Submodule.coe_inner,
    coe_toEigenspace_cliffordMul, coe_toEigenspace_cliffordMul, ← LinearMap.adjoint_inner_right,
    hρ, LinearMap.neg_apply, inner_neg_right]

/-- Model Clifford multiplication scales norms by `‖v‖`: `‖c(v) ψ‖ = ‖v‖ ‖ψ‖`. -/
theorem norm_cliffordMul {ε' : ℂ} (hε : ε' = -ε) (v : V) (ψ : HalfSpinModel o hQ b ρ hρ ε) :
    ‖cliffordMul hε v ψ‖ = ‖v‖ * ‖ψ‖ := by
  rw [← LinearIsometryEquiv.norm_map toEigenspace (cliffordMul hε v ψ),
    ← LinearIsometryEquiv.norm_map toEigenspace ψ, ← Submodule.norm_coe, ← Submodule.norm_coe,
    coe_toEigenspace_cliffordMul, norm_map_ι_apply hQ hρ]

/-- **`Spinᶜ(4)` scales top-degree alternating forms by its determinant character**: in complex
dimension two, `ω(x • ψ₁, x • ψ₂) = z² ω(ψ₁, ψ₂)` for `x = [s, z]`, since the half-spin
representation has determinant `z²`. -/
theorem alternatingMap_smul {N : Type*} [AddCommGroup N] [Module ℂ N]
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (ω : HalfSpinModel o hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] N) (x : SpinC)
    (ψ : Fin 2 → HalfSpinModel o hQ b ρ hρ ε) :
    ω (fun i ↦ x • ψ i) = (spinCGroup.det _ hpos x : ℂ) • ω ψ := by
  let e := Module.finBasisOfFinrankEq ℂ (HalfSpinModel o hQ b ρ hρ ε)
    ((toEigenspace (o := o) (hQ := hQ) (b := b) (ρ := ρ) (hρ := hρ)).toLinearEquiv.finrank_eq.trans
      h₂)
  -- Through `toEigenspace`, the action of `x` is `realSpinCHalfSpinSmoothHom x`.
  have hconj : (toEigenspace.toLinearEquiv : HalfSpinModel o hQ b ρ hρ ε ≃ₗ[ℂ] _).toLinearMap ∘ₗ
      DistribSMul.toLinearMap ℂ (HalfSpinModel o hQ b ρ hρ ε) x ∘ₗ
        toEigenspace.toLinearEquiv.symm.toLinearMap =
      (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).toLinearMap :=
    LinearMap.ext fun ψ ↦ by simp
  have hdet : LinearMap.det (DistribSMul.toLinearMap ℂ (HalfSpinModel o hQ b ρ hρ ε) x) =
      (spinCGroup.det _ hpos x : ℂ) := by
    rw [← det_realSpinCHalfSpinSmoothHom o hQ b ρ ε h₂ x, ← hconj, LinearMap.det_conj]
  simpa [hdet] using
    congrArg (· ψ) (AlternatingMap.compLinearMap_eq_det_smul e ω
      (DistribSMul.toLinearMap ℂ _ x))

end HalfSpinModel

end Orientation

namespace TauCeti

namespace SpinCStructure

/-! ### The determinant line -/

section DeterminantLine

variable (n : ℕ) [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQn" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)
local notation "SpinCn" => spinCGroup (realCliffordForm n 0) hQn

/-- The **determinant model** `ℂ`, on which `Spinᶜ(n)` acts through its determinant character
`[s, z] ↦ z²` (`CliffordAlgebra.spinCGroup.det`). -/
@[expose] def DeterminantModel (_n : ℕ) : Type := ℂ

namespace DeterminantModel

instance instNormedAddCommGroup : NormedAddCommGroup (DeterminantModel n) :=
  inferInstanceAs (NormedAddCommGroup ℂ)

instance instInnerProductSpace : InnerProductSpace ℂ (DeterminantModel n) :=
  inferInstanceAs (InnerProductSpace ℂ ℂ)

instance instFiniteDimensional : FiniteDimensional ℂ (DeterminantModel n) :=
  inferInstanceAs (FiniteDimensional ℂ ℂ)

/-- `Spinᶜ(n)` acts on the determinant model by multiplication by its determinant character. -/
instance instDistribMulAction :
    DistribMulAction (spinCGroup (realCliffordForm n 0) hQn) (DeterminantModel n) :=
  DistribMulAction.compHom ℂ (Circle.coeHom.comp (spinCGroup.det _ hQn))

variable {n}

/-- The determinant model as `ℂ`. -/
def toComplex : DeterminantModel n ≃ₗᵢ[ℂ] ℂ := LinearIsometryEquiv.refl ℂ ℂ

variable (n) in
omit [NeZero n] in
/-- The determinant model has complex dimension one. -/
theorem finrank_eq_one : finrank ℂ (DeterminantModel n) = 1 :=
  (toComplex (n := n)).finrank_eq.trans (finrank_self ℂ)

/-- `x` acts on the determinant model by multiplication by `det x`. -/
@[simp]
theorem toComplex_smul (x : spinCGroup (realCliffordForm n 0) hQn) (w : DeterminantModel n) :
    toComplex (x • w) = (spinCGroup.det _ hQn x : ℂ) * toComplex w :=
  (rfl)

/-- `x` acts on `c : ℂ` by multiplication by `det x`. -/
theorem smul_toComplex_symm (x : spinCGroup (realCliffordForm n 0) hQn) (c : ℂ) :
    x • (toComplex.symm c : DeterminantModel n) =
      toComplex.symm ((spinCGroup.det _ hQn x : ℂ) * c) :=
  toComplex.injective (by rw [toComplex_smul, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply])

/-- The central circle acts on the determinant model with weight two. -/
@[simp]
theorem ofCircle_smul (z : Circle) (w : DeterminantModel n) :
    spinCGroup.ofCircle _ hQn z • w = ((z : ℂ) ^ 2) • w :=
  toComplex.injective (by
    rw [toComplex_smul, spinCGroup.det_ofCircle, Circle.coe_pow, map_smul, smul_eq_mul])

instance instSMulCommClass :
    SMulCommClass (spinCGroup (realCliffordForm n 0) hQn) ℂ (DeterminantModel n) where
  -- Both actions are multiplications in `ℂ`.
  smul_comm x c w := mul_left_comm (spinCGroup.det _ hQn x : ℂ) c (toComplex w)

instance instContinuousSMul :
    ContinuousSMul (spinCGroup (realCliffordForm n 0) hQn) (DeterminantModel n) :=
  ⟨(continuous_subtypeVal.comp ((spinCGroup.continuous_det _ hQn).comp continuous_fst)).mul
    continuous_snd⟩

instance instIsIsometricSMul :
    IsIsometricSMul (spinCGroup (realCliffordForm n 0) hQn) (DeterminantModel n) where
  isometry_smul x := AddMonoidHomClass.isometry_of_norm (DistribSMul.toAddMonoidHom _ x)
    fun w ↦ by
      rw [DistribSMul.toAddMonoidHom_apply, ← toComplex.norm_map, toComplex_smul, norm_mul,
        Circle.norm_coe, one_mul, toComplex.norm_map]

end DeterminantModel

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n}

/-- The **determinant line** `L = P ×_{z²} ℂ` of a `Spinᶜ` structure: the Hermitian line bundle
associated to its principal `Spinᶜ(n)`-bundle by the determinant character `[s, z] ↦ z²`. -/
abbrev determinantLine (s : SpinCStructure F E n) : X → Type _ :=
  AssociatedBundle (spinCGroup (realCliffordForm n 0) hQn) s.P (DeterminantModel n)

/-- The determinant line has complex rank one. -/
theorem finrank_determinantLine (s : SpinCStructure F E n) (x : X) :
    finrank ℂ (s.determinantLine x) = 1 := by
  rw [AssociatedBundle.finrank_eq ℂ SpinCn, DeterminantModel.finrank_eq_one]

/-- **The central circle acts with weight two on the determinant line**: `[p • [1, z], w]` is
`[p, z² w]`. -/
theorem mk_ofCircle_smul_determinantLine (s : SpinCStructure F E n) {x : X} (p : s.P x)
    (z : Circle) (w : DeterminantModel n) :
    AssociatedBundle.mk _ (op (spinCGroup.ofCircle _ hQn z) • p) w =
      ((z : ℂ) ^ 2) • (AssociatedBundle.mk _ p w : s.determinantLine x) := by
  rw [AssociatedBundle.mk_smul, DeterminantModel.ofCircle_smul, AssociatedBundle.mk_smul_scalar]

end DeterminantLine

/-! ### The half-spinor bundles -/

section HalfSpinor

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (ε : ℂ)

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-- The **half-spinor bundle** `W^ε = P ×_{Spinᶜ(4)} S^ε` of a `Spinᶜ` structure of rank four: the
Hermitian vector bundle associated to its principal `Spinᶜ(4)`-bundle by the half-spin
representation on the `ε`-eigenspace `S^ε` of the chirality operator of a model Hermitian Clifford
module (`Orientation.HalfSpinModel`). For `ε = 1` and `ε = -1` these are `W⁺` and `W⁻` when `b` is
positively oriented for `o` (`b.toBasis.orientation = o`), and `W⁻` and `W⁺` otherwise. -/
abbrev halfSpinorBundle (s : SpinCStructure F E 4) : X → Type _ :=
  AssociatedBundle SpinC s.P (o.HalfSpinModel hQ b ρ hρ ε)

/-- Each fibre of the half-spinor bundle has the complex dimension of the model eigenspace. -/
theorem finrank_halfSpinorBundle (s : SpinCStructure F E 4) (x : X) :
    finrank ℂ (s.halfSpinorBundle o hQ b ρ hρ ε x) =
      finrank ℂ (eigenspace (ρ (chirality Q o)) ε) := by
  rw [AssociatedBundle.finrank_eq ℂ SpinC, Orientation.HalfSpinModel.toEigenspace.finrank_eq]

/-- **The central circle acts with weight one on the half-spinors**: `[p • [1, z], ψ]` is
`[p, z ψ]`. -/
theorem mk_ofCircle_smul_halfSpinorBundle (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (z : Circle) (ψ : o.HalfSpinModel hQ b ρ hρ ε) :
    AssociatedBundle.mk _ (op (spinCGroup.ofCircle _ hpos z) • p) ψ =
      (z : ℂ) • (AssociatedBundle.mk _ p ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) := by
  rw [AssociatedBundle.mk_smul, Orientation.HalfSpinModel.ofCircle_smul,
    AssociatedBundle.mk_smul_scalar]

/-! ### Clifford multiplication -/

variable {o hQ b ρ hρ ε}

/-- The linear isometry `κ_p : E x ≃ V` given by a point `p` of the principal bundle over `x`:
the inverse of the frame of `E x` at `p` (`TauCeti.OrthonormalFrameLift.frameAt`), followed by the
coordinates of the orthonormal basis `b`. -/
def vectorFrame (s : SpinCStructure F E 4) (b : OrthonormalBasis (Fin 4) ℝ V) {x : X}
    (p : s.P x) : E x ≃ₗᵢ[ℝ] V :=
  (s.frameAt p).symm.trans b.repr.symm

omit [Fact (finrank ℝ V = 4)] in
/-- `κ_p` is `b` applied to the coordinates of `v` in the frame `p`. -/
theorem vectorFrame_apply (s : SpinCStructure F E 4) (b : OrthonormalBasis (Fin 4) ℝ V)
    {x : X} (p : s.P x) (v : E x) :
    s.vectorFrame b p v = b.negRealCliffordFormIsometryEquiv hQ ((s.frameAt p).symm v).ofLp := by
  rw [OrthonormalBasis.negRealCliffordFormIsometryEquiv_apply, vectorFrame,
    LinearIsometryEquiv.trans_apply, ← b.sum_repr_symm]

omit [Fact (finrank ℝ V = 4)] in
/-- **The vector frames are equivariant**: `κ_{p • g} = π(g)⁻¹ κ_p`, read through `b`. -/
theorem vectorFrame_smul (s : SpinCStructure F E 4) {x : X} (p : s.P x) (g : SpinC) (v : E x) :
    b.negRealCliffordFormIsometryEquiv hQ
        ((spinCGroup.toSpecialOrthogonal _ hpos g : (Fin (4 + 0) → ℝ) ≃ₗ[ℝ] (Fin (4 + 0) → ℝ))
          ((s.frameAt (op g • p)).symm v).ofLp) =
      s.vectorFrame b p v := by
  rw [vectorFrame_apply (hQ := hQ)]
  congr 2
  set u := ((s.frameAt (op g • p)).symm v).ofLp
  -- The frame of `p • g` is the frame of `p` precomposed with the rotation of `g`, so the
  -- coordinates of `v` in the frame `p` are the rotated coordinates `u` in the frame `p • g`.
  have h := s.frameAt_smul p g u
  rw [WithLp.toLp_ofLp, LinearIsometryEquiv.apply_symm_apply] at h
  rw [h, LinearIsometryEquiv.symm_apply_apply, WithLp.ofLp_toLp, MonoidHom.comp_apply,
    Subgroup.coe_subtype]

omit [Fact (finrank ℝ V = 4)] in
/-- **Changing the frame rotates the vector frame**: `κ_p = π(g) κ_{p • g}`, where `π(g)` is the
rotation of `V` by `g`, read through `b`. -/
theorem vectorFrame_eq_toSpecialOrthogonal_vectorFrame_smul (s : SpinCStructure F E 4) {x : X}
    (p : s.P x) (g : SpinC) (v : E x) :
    s.vectorFrame b p v =
      (spinCGroup.toSpecialOrthogonal Q (b.ne_zero_of_neg_norm_sq hQ)
        (b.realSpinCGroupHom hQ hpos (b.ne_zero_of_neg_norm_sq hQ) g) : V ≃ₗ[ℝ] V)
        (s.vectorFrame b (op g • p) v) := by
  rw [vectorFrame_apply (hQ := hQ) s b (op g • p),
    OrthonormalBasis.toSpecialOrthogonal_realSpinCGroupHom_apply, vectorFrame_smul]

/-- **Clifford multiplication** `c(v) : W^ε_x → W^{ε'}_x` on the half-spinor bundles of a `Spinᶜ`
structure of rank four, for `v ∈ E x` and `ε' = -ε`: in a frame `p` it is model Clifford
multiplication by `κ_p v` (`TauCeti.SpinCStructure.cliffordMul_mk`), which does not depend on `p`.
It is defined in a chosen frame. -/
def cliffordMul (s : SpinCStructure F E 4) (o : Orientation ℝ V (Fin 4))
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (b : OrthonormalBasis (Fin 4) ℝ V)
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ε' : ℂ} (hε : ε' = -ε) (x : X) :
    E x →ₗ[ℝ] s.halfSpinorBundle o hQ b ρ hρ ε x →ₗ[ℂ] s.halfSpinorBundle o hQ b ρ hρ ε' x :=
  let p : s.P x := Classical.arbitrary _
  ((LinearEquiv.arrowCongr (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p).toLinearEquiv
      (AssociatedBundle.mkLinearIsometryEquiv ℂ SpinC p).toLinearEquiv).toLinearMap.restrictScalars
      ℝ) ∘ₗ Orientation.HalfSpinModel.cliffordMul hε ∘ₗ
    (s.vectorFrame b p).toLinearEquiv.toLinearMap

/-- **Clifford multiplication in a frame**: `c(v) [p, ψ] = [p, c(κ_p v) ψ]` for every point `p` of
the principal bundle over `x`. -/
@[simp]
theorem cliffordMul_mk (s : SpinCStructure F E 4) {ε' : ℂ} (hε : ε' = -ε) {x : X} (p : s.P x)
    (v : E x) (ψ : o.HalfSpinModel hQ b ρ hρ ε) :
    s.cliffordMul o hQ b ρ hρ hε x v (AssociatedBundle.mk SpinC p ψ) =
      AssociatedBundle.mk SpinC p
        (Orientation.HalfSpinModel.cliffordMul hε (s.vectorFrame b p v) ψ) := by
  simp only [cliffordMul, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearEquiv.arrowCongr_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    AssociatedBundle.mkLinearIsometryEquiv_apply]
  -- Compare the chosen frame `p₀` with `p = p₀ • g`.
  generalize (Classical.arbitrary (s.P x)) = p₀
  set g := PrincipalBundle.division SpinC p₀ p
  have hp : op g • p₀ = p := PrincipalBundle.smul_division p₀ p
  conv_rhs => rw [← hp, AssociatedBundle.mk_smul, vectorFrame_apply (hQ := hQ),
    Orientation.HalfSpinModel.smul_cliffordMul, vectorFrame_smul]
  exact congrArg _ (congrArg _ (AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk p₀ p ψ))

/-- **The Clifford relation** `c(v) c(v) = -‖v‖²` on the half-spinor bundles. -/
theorem cliffordMul_cliffordMul (s : SpinCStructure F E 4) {ε' : ℂ} (hε : ε' = -ε) {x : X}
    (v : E x) (ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) :
    s.cliffordMul o hQ b ρ hρ (neg_eq_iff_eq_neg.mp hε.symm) x v
      (s.cliffordMul o hQ b ρ hρ hε x v ψ) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • ψ := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [cliffordMul_mk, cliffordMul_mk, Orientation.HalfSpinModel.cliffordMul_cliffordMul,
    LinearIsometryEquiv.norm_map, AssociatedBundle.mk_smul_scalar]

/-- **Clifford multiplication is skew-adjoint**: `⟪c(v) ψ, φ⟫ = -⟪ψ, c(v) φ⟫` for `ψ ∈ W^ε_x` and
`φ ∈ W^{ε'}_x`. -/
theorem inner_cliffordMul_left (s : SpinCStructure F E 4) {ε' : ℂ} (hε : ε' = -ε) {x : X}
    (v : E x) (ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) (φ : s.halfSpinorBundle o hQ b ρ hρ ε' x) :
    ⟪s.cliffordMul o hQ b ρ hρ hε x v ψ, φ⟫_ℂ =
      -⟪ψ, s.cliffordMul o hQ b ρ hρ (neg_eq_iff_eq_neg.mp hε.symm) x v φ⟫_ℂ := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  obtain ⟨φ, rfl⟩ := (AssociatedBundle.mk_bijective (G := SpinC)
    (F := o.HalfSpinModel hQ b ρ hρ ε') p).2 φ
  rw [cliffordMul_mk, cliffordMul_mk, AssociatedBundle.inner_mk, AssociatedBundle.inner_mk,
    Orientation.HalfSpinModel.inner_cliffordMul_left]

/-- Clifford multiplication scales norms by `‖v‖`: `‖c(v) ψ‖ = ‖v‖ ‖ψ‖`. -/
theorem norm_cliffordMul (s : SpinCStructure F E 4) {ε' : ℂ} (hε : ε' = -ε) {x : X} (v : E x)
    (ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) :
    ‖s.cliffordMul o hQ b ρ hρ hε x v ψ‖ = ‖v‖ * ‖ψ‖ := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [cliffordMul_mk, AssociatedBundle.norm_mk, AssociatedBundle.norm_mk,
    Orientation.HalfSpinModel.norm_cliffordMul, LinearIsometryEquiv.norm_map]

/-! ### The determinant of the half-spinors -/

/-- The **model determinant pairing** of an alternating form `ω` on the model half-spinors: the
continuous bilinear map `(ψ₁, ψ₂) ↦ ω(ψ₁, ψ₂)` with values in the determinant model. -/
def halfSpinorDetPairing (ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ) :
    o.HalfSpinModel hQ b ρ hρ ε →L[ℂ] o.HalfSpinModel hQ b ρ hρ ε →L[ℂ] DeterminantModel 4 :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    (DeterminantModel.toComplex.symm.toLinearEquiv.toLinearMap.compAlternatingMap
      ω).toMultilinearMap.toBilinMap)

/-- The model determinant pairing is `ω` read in the determinant model. -/
@[simp]
theorem halfSpinorDetPairing_apply (ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ)
    (ψ₁ ψ₂ : o.HalfSpinModel hQ b ρ hρ ε) :
    halfSpinorDetPairing ω ψ₁ ψ₂ = DeterminantModel.toComplex.symm (ω ![ψ₁, ψ₂]) := by
  simp [halfSpinorDetPairing]

/-- **The model determinant pairing is equivariant** when `S^ε` has complex dimension two, since
`Spinᶜ(4)` scales `ω` by its determinant character. -/
theorem halfSpinorDetPairing_smul_smul
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ) (g : SpinC)
    (ψ₁ ψ₂ : o.HalfSpinModel hQ b ρ hρ ε) :
    halfSpinorDetPairing ω (g • ψ₁) (g • ψ₂) = g • halfSpinorDetPairing ω ψ₁ ψ₂ := by
  have h := Orientation.HalfSpinModel.alternatingMap_smul h₂ ω g ![ψ₁, ψ₂]
  rw [halfSpinorDetPairing_apply, halfSpinorDetPairing_apply,
    DeterminantModel.smul_toComplex_symm, ← smul_eq_mul, ← h]
  congr 2
  ext i
  fin_cases i <;> simp

/-- The fibrewise descent of the model determinant pairing (`TauCeti.AssociatedBundle.bilinearMap`)
is alternating, since `ω` is. -/
theorem isAlt_bilinearMap_halfSpinorDetPairing
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (s : SpinCStructure F E 4)
    (ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ) (x : X) :
    (AssociatedBundle.bilinearMap (P := s.P) (halfSpinorDetPairing ω)
      (halfSpinorDetPairing_smul_smul h₂ ω) x).toLinearMap₁₂.IsAlt := by
  intro ψ
  obtain ⟨p, φ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, AssociatedBundle.bilinearMap_mk,
    halfSpinorDetPairing_apply, ω.map_eq_zero_of_eq ![φ, φ] (i := 0) (j := 1) rfl zero_ne_one,
    map_zero, AssociatedBundle.mk_zero]

/-- The alternating map `W^ε_x × W^ε_x → L_x` induced by an alternating form `ω` on the model
half-spinors of complex dimension two: the fibrewise descent of the model determinant pairing
(`TauCeti.AssociatedBundle.bilinearMap`), sending `([p, ψ₁], [p, ψ₂])` to `[p, ω(ψ₁, ψ₂)]` in every
frame `p` (`TauCeti.SpinCStructure.halfSpinorDetAlternatingMap_mk`). -/
def halfSpinorDetAlternatingMap (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : SpinCStructure F E 4) (ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ) (x : X) :
    s.halfSpinorBundle o hQ b ρ hρ ε x [⋀^Fin 2]→ₗ[ℂ] s.determinantLine x :=
  (isAlt_bilinearMap_halfSpinorDetPairing h₂ s ω x).toAlternatingMap

/-- **The determinant pairing in a frame**: `([p, ψ₁], [p, ψ₂]) ↦ [p, ω(ψ₁, ψ₂)]` for every point
`p` of the principal bundle over `x`. -/
@[simp]
theorem halfSpinorDetAlternatingMap_mk (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : SpinCStructure F E 4) (ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ) {x : X}
    (p : s.P x) (ψ : Fin 2 → o.HalfSpinModel hQ b ρ hρ ε) :
    s.halfSpinorDetAlternatingMap h₂ ω x (fun i ↦ AssociatedBundle.mk SpinC p (ψ i)) =
      AssociatedBundle.mk SpinC p (DeterminantModel.toComplex.symm (ω ψ)) := by
  rw [halfSpinorDetAlternatingMap, LinearMap.IsAlt.toAlternatingMap_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, AssociatedBundle.bilinearMap_mk,
    halfSpinorDetPairing_apply]
  congr 3
  ext i
  fin_cases i <;> simp

/-- For a nonzero `ω` and `S^ε` of complex dimension two, the linear map `⋀² W^ε_x → L_x` induced
by the determinant pairing is bijective: it is onto the line `L_x`, and both sides are lines. -/
theorem bijective_alternatingMapLinearEquiv_halfSpinorDetAlternatingMap
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (s : SpinCStructure F E 4)
    {ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ} (hω : ω ≠ 0) (x : X) :
    Function.Bijective
      (exteriorPower.alternatingMapLinearEquiv (s.halfSpinorDetAlternatingMap h₂ ω x)) := by
  obtain ⟨p⟩ := s.nonempty_P x
  have : FiniteDimensional ℂ (s.halfSpinorBundle o hQ b ρ hρ ε x) :=
    AssociatedBundle.finiteDimensional ℂ SpinC p
  have : FiniteDimensional ℂ (s.determinantLine x) := AssociatedBundle.finiteDimensional ℂ SpinC p
  -- Every `[p, w]` is a multiple of the image of `[p, ψ₁] ∧ [p, ψ₂]`, for `ω(ψ₁, ψ₂) ≠ 0`.
  have hsurj : Function.Surjective
      (exteriorPower.alternatingMapLinearEquiv (s.halfSpinorDetAlternatingMap h₂ ω x)) := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ, ω ψ ≠ 0 := by
      by_contra! h
      exact hω (AlternatingMap.ext h)
    intro y
    obtain ⟨w, rfl⟩ := (AssociatedBundle.mk_bijective (G := SpinC) (F := DeterminantModel 4) p).2 y
    refine ⟨(DeterminantModel.toComplex w / ω ψ) •
      exteriorPower.ιMulti ℂ 2 (fun i ↦ AssociatedBundle.mk SpinC p (ψ i)), ?_⟩
    rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      halfSpinorDetAlternatingMap_mk h₂, ← AssociatedBundle.mk_smul_scalar]
    congr 1
    apply DeterminantModel.toComplex.injective
    rw [map_smul, LinearIsometryEquiv.apply_symm_apply, smul_eq_mul, div_mul_cancel₀ _ hψ]
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj, hsurj⟩
  rw [exteriorPower.finrank_eq, finrank_halfSpinorBundle, h₂, finrank_determinantLine]
  rfl

/-- **The determinant of the half-spinors is the determinant line**: for a nonzero alternating form
`ω` on the model half-spinors of complex dimension two, the linear isomorphism
`⋀² W^ε_x ≃ L_x` sending `[p, ψ₁] ∧ [p, ψ₂]` to `[p, ω(ψ₁, ψ₂)]`. For `ε = ±1` and `b` positively
oriented for `o` this identifies `det W⁺ ≃ L ≃ det W⁻` on every fibre. -/
def exteriorPowerHalfSpinorEquiv (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : SpinCStructure F E 4) {ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ} (hω : ω ≠ 0)
    (x : X) : ⋀[ℂ]^2 (s.halfSpinorBundle o hQ b ρ hρ ε x) ≃ₗ[ℂ] s.determinantLine x :=
  LinearEquiv.ofBijective _
    (bijective_alternatingMapLinearEquiv_halfSpinorDetAlternatingMap h₂ s hω x)

/-- `⋀² W^ε_x ≃ L_x` sends `ψ₁ ∧ ψ₂` to the determinant pairing of `ψ₁` and `ψ₂`. -/
@[simp]
theorem exteriorPowerHalfSpinorEquiv_ιMulti
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (s : SpinCStructure F E 4)
    {ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ} (hω : ω ≠ 0) {x : X}
    (ψ : Fin 2 → s.halfSpinorBundle o hQ b ρ hρ ε x) :
    s.exteriorPowerHalfSpinorEquiv h₂ hω x (exteriorPower.ιMulti ℂ 2 ψ) =
      s.halfSpinorDetAlternatingMap h₂ ω x ψ :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ ψ

end HalfSpinor

end SpinCStructure

end TauCeti
