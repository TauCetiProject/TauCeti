/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.HalfSpin
public import TauCeti.Geometry.Manifold.VectorBundle.Associated
public import TauCeti.LinearAlgebra.Determinant.Basic
public import TauCeti.LinearAlgebra.Determinant.Line

/-!
# Spinor bundles and the determinant line of a principal Spinᶜ(4)-bundle

A `Spinᶜ` structure on an oriented Riemannian four-manifold `X` is a principal
`Spinᶜ(4)`-bundle `P` lifting the oriented orthonormal frame bundle along
`Spinᶜ(4) → SO(4)`. Its spinor bundles `W^±` and its determinant line `L` are the vector bundles
associated with `P` through the half-spin representations `[s, z] ↦ z ρ^±(s)` and through the
determinant character `[s, z] ↦ z²`. This file constructs them for an arbitrary principal
`Spinᶜ(4)`-bundle `P`, as instances of the associated-bundle construction
`TauCeti.AssociatedBundle`, and equips their fibres with the determinant and Hermitian structure
of the model representations.

The model fibres are type synonyms carrying the actions:

* `Orientation.SpinCHalfSpinor o hQ b ρ ε`, the `ε`-eigenspace of the chirality element on a
  Clifford module `W`, with the smooth half-spin action `Orientation.realSpinCHalfSpinSmoothHom`;
* `CliffordAlgebra.spinCGroup.DetFibre n hQ`, the line `ℂ` with `Spinᶜ(n)` acting through the
  determinant character `CliffordAlgebra.spinCGroup.det`.

The associated bundles are `Orientation.spinorBundle o hQ b ρ ε P`, the spinor bundle
`W^ε = P ×_{Spinᶜ(4)} W^ε`, and `CliffordAlgebra.spinCGroup.detLineBundle n hQ P`, the
determinant line `L = P ×_{Spinᶜ(n)} ℂ`. They are complex vector bundles, and smooth vector bundles
when `P` is a smooth principal bundle.

A point `p` of `P` over `x` identifies the model with the fibre over `x` by `v ↦ [p, v]`, and
changing `p` acts on the model by the representation. Structure on the model that is invariant
under the representation therefore descends to the fibres:

* `Spinᶜ(4)` acts on a two-dimensional `W^ε` with determinant `z²`
  (`Orientation.det_realSpinCHalfSpinSmoothHom`), so an alternating two-form `η` on the model
  descends to the **determinant pairing** `Orientation.spinorDetPairing` of `W^ε_x` with values in
  `L_x`, which reads `[p, v 0], [p, v 1] ↦ [p, η v]` in every frame
  (`Orientation.spinorDetPairing_mk`). For `η ≠ 0` it induces an isomorphism
  `⋀² W^ε_x ≃ L_x` (`Orientation.spinorDetEquiv`): the determinant line of each spinor bundle is
  the determinant line of the `Spinᶜ` structure.
* When the Clifford generators act skew-adjointly, `Spinᶜ(4)` acts unitarily on `W^ε`
  (`Orientation.inner_realSpinCHalfSpinSmoothHom_apply`), and the inner product of the model
  descends to the Hermitian form `Orientation.spinorInner` of the fibres
  (`Orientation.spinorInner_mk`).

The identification of `P ×_{Spinᶜ(4)} ℝ⁴` with the tangent bundle for a lift of the frame bundle,
Clifford multiplication as a bundle map, and `Spinᶜ` connections are not constructed here.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1–§3.2.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §10.7.
-/

public section

noncomputable section

open Bundle Module Module.End Manifold MulOpposite TauCeti TauCeti.CliffordAlgebra CliffordAlgebra
open scoped Manifold ContDiff InnerProductSpace

local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos
local notation "I" => ModelWithCorners.prod 𝓘(ℝ, realSpinLieModel 4) (𝓡 1)

/-! ### The determinant line -/

namespace CliffordAlgebra.spinCGroup

variable (n : ℕ) (hQ : realCliffordForm n 0 ≠ 0)

/-- The model fibre `ℂ` of the determinant line of a `Spinᶜ(n)`-bundle, on which `Spinᶜ(n)`
acts through its determinant character `[s, z] ↦ z²` (`CliffordAlgebra.spinCGroup.det`). -/
@[expose]
def DetFibre (_n : ℕ) (_hQ : realCliffordForm _n 0 ≠ 0) : Type := ℂ

namespace DetFibre

instance : NormedAddCommGroup (DetFibre n hQ) := inferInstanceAs (NormedAddCommGroup ℂ)

instance : NormedSpace ℂ (DetFibre n hQ) := inferInstanceAs (NormedSpace ℂ ℂ)

instance : FiniteDimensional ℂ (DetFibre n hQ) := inferInstanceAs (FiniteDimensional ℂ ℂ)

/-- `Spinᶜ(n)` acts on the model determinant fibre through its determinant character. -/
instance : DistribMulAction (spinCGroup (realCliffordForm n 0) hQ) (DetFibre n hQ) :=
  DistribMulAction.compHom ℂ (Circle.coeHom.comp (det (realCliffordForm n 0) hQ))

/-- `Spinᶜ(n)` acts on the model determinant fibre by its determinant character. -/
theorem smul_def (x : spinCGroup (realCliffordForm n 0) hQ) (w : DetFibre n hQ) :
    x • w = (det (realCliffordForm n 0) hQ x : ℂ) • w := (rfl)

instance : SMulCommClass (spinCGroup (realCliffordForm n 0) hQ) ℂ (DetFibre n hQ) where
  smul_comm x c w := by simp only [smul_def, smul_comm (det _ hQ x : ℂ) c w]

instance : SMulCommClass (spinCGroup (realCliffordForm n 0) hQ) ℝ (DetFibre n hQ) where
  smul_comm x c w := by simp only [smul_def, smul_comm (det _ hQ x : ℂ) c w]

/-- The determinant character, viewed in `ℂ`, multiplies smoothly. -/
private theorem contMDiff_det_mul :
    ContMDiff ((𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : spinCGroup (realCliffordForm n 0) hQ × ℂ ↦
        (det (realCliffordForm n 0) hQ p.1 : ℂ) * p.2) := by
  have := finrank_real_complex_fact'
  exact contDiff_mul.contMDiff.comp
    (((contMDiff_coe_sphere.comp (contMDiff_realDet n hQ)).comp contMDiff_fst).prodMk_space
      contMDiff_snd)

/-- The determinant action is smooth. -/
instance : ContMDiffSMul (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) 𝓘(ℝ, DetFibre n hQ) ∞
    (spinCGroup (realCliffordForm n 0) hQ) (DetFibre n hQ) where
  contMDiff_smul := by
    simp only [smul_def]
    exact contMDiff_det_mul n hQ

instance : ContinuousSMul (spinCGroup (realCliffordForm n 0) hQ) (DetFibre n hQ) where
  continuous_smul := by
    simp only [smul_def]
    exact (contMDiff_det_mul n hQ).continuous

end DetFibre

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (P : B → Type*) [TopologicalSpace (TotalSpace (spinCGroup (realCliffordForm n 0) hQ) P)]
  [∀ x, TopologicalSpace (P x)] [FiberBundle (spinCGroup (realCliffordForm n 0) hQ) P]
  [∀ x, MulAction (spinCGroup (realCliffordForm n 0) hQ)ᵐᵒᵖ (P x)]
  [PrincipalBundle (spinCGroup (realCliffordForm n 0) hQ) P]

/-- The determinant line `L = P ×_{Spinᶜ(n)} ℂ` of a principal `Spinᶜ(n)`-bundle `P`, associated
with the determinant character `[s, z] ↦ z²`. -/
abbrev detLineBundle : B → Type _ :=
  AssociatedBundle (spinCGroup (realCliffordForm n 0) hQ) P (DetFibre n hQ)

/-- The determinant line of a smooth principal `Spinᶜ(n)`-bundle is a smooth line bundle. -/
instance [ContMDiffFiberBundle ∞ (spinCGroup (realCliffordForm n 0) hQ) P IB
      (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))] :
    ContMDiffVectorBundle ∞ (DetFibre n hQ) (detLineBundle n hQ P) IB :=
  AssociatedBundle.contMDiffVectorBundle (𝕜 := ℝ) (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))

end CliffordAlgebra.spinCGroup

namespace Orientation

/-! ### The half-spinor model fibres -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-- The model fibre of the spinor bundle `W^ε`: the `ε`-eigenspace of the chirality element
on the Clifford module `W`, on which `Spinᶜ(4)` acts by the weight-one half-spin representation
`[s, z] ↦ z ρ(s)` (`Orientation.realSpinCHalfSpinSmoothHom`), compared with the geometric
Clifford model through the orthonormal frame `b`. -/
@[expose]
def SpinCHalfSpinor (_o : Orientation ℝ V (Fin 4)) (_hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (_b : OrthonormalBasis (Fin 4) ℝ V) (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ) :
    Type _ :=
  eigenspace (ρ (chirality Q _o)) ε

namespace SpinCHalfSpinor

instance : NormedAddCommGroup (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (NormedAddCommGroup (eigenspace (ρ (chirality Q o)) ε))

instance : NormedSpace ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (NormedSpace ℂ (eigenspace (ρ (chirality Q o)) ε))

instance : FiniteDimensional ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (FiniteDimensional ℂ (eigenspace (ρ (chirality Q o)) ε))

/-- `Spinᶜ(4)` acts on the half-spinor model by the half-spin representation. -/
instance : DistribMulAction SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  DistribMulAction.compHom (eigenspace (ρ (chirality Q o)) ε)
    (realSpinCHalfSpinSmoothHom o hQ b ρ ε).toMonoidHom

/-- The action of `Spinᶜ(4)` on the half-spinor model is evaluation of the half-spin
representation. -/
theorem smul_def (x : SpinC) (ψ : SpinCHalfSpinor o hQ b ρ ε) :
    x • ψ = realSpinCHalfSpinSmoothHom o hQ b ρ ε x ψ := (rfl)

instance : SMulCommClass SpinC ℂ (SpinCHalfSpinor o hQ b ρ ε) where
  smul_comm x c ψ := by
    simp only [smul_def]
    exact (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).map_smul c ψ

instance : SMulCommClass SpinC ℝ (SpinCHalfSpinor o hQ b ρ ε) where
  smul_comm x c ψ := by
    simp only [smul_def]
    exact (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).map_smul_of_tower c ψ

/-- The half-spin action is smooth. -/
instance : ContMDiffSMul I 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε) ∞ SpinC
    (SpinCHalfSpinor o hQ b ρ ε) where
  contMDiff_smul := by
    simp only [smul_def]
    exact contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε

instance : ContinuousSMul SpinC (SpinCHalfSpinor o hQ b ρ ε) where
  continuous_smul := by
    simp only [smul_def]
    exact (contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε).continuous

end SpinCHalfSpinor

/-! ### The spinor bundles and the determinant line -/

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (P : B → Type*) [TopologicalSpace (TotalSpace SpinC P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle SpinC P] [∀ x, MulAction SpinCᵐᵒᵖ (P x)] [PrincipalBundle SpinC P]

/-- The spinor bundle `W^ε = P ×_{Spinᶜ(4)} W^ε` of a principal `Spinᶜ(4)`-bundle `P`. -/
abbrev spinorBundle : B → Type _ :=
  AssociatedBundle SpinC P (SpinCHalfSpinor o hQ b ρ ε)

/-- The spinor bundle of a smooth principal `Spinᶜ(4)`-bundle is a smooth vector bundle. -/
instance [ContMDiffFiberBundle ∞ SpinC P IB I] :
    ContMDiffVectorBundle ∞ (SpinCHalfSpinor o hQ b ρ ε) (o.spinorBundle hQ b ρ ε P) IB :=
  AssociatedBundle.contMDiffVectorBundle (𝕜 := ℝ) I

/-! ### The determinant pairing -/

/-- A point of the fibre of a principal bundle, used to define the fibrewise maps below. Under
the hypotheses of `Orientation.spinorDetPairing_mk` and `Orientation.spinorInner_mk` they do not
depend on this choice. -/
private def basePoint (x : B) : P x := (FiberBundle.homeomorphAt SpinC P x).symm 1

/-- The determinant pairing `W^ε_x × W^ε_x → L_x` of the spinor bundle with values in the
determinant line, induced by an alternating form `η` on the model half-spinors. In every
frame `p` of `P` it is `η` itself (`Orientation.spinorDetPairing_mk`); when `W^ε` has complex
dimension two this does not depend on the frame, because `Spinᶜ(4)` acts on `W^ε` with
determinant `[s, z] ↦ z²`. -/
def spinorDetPairing
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFibre 4 hpos) (x : B) :
    o.spinorBundle hQ b ρ ε P x [⋀^Fin 2]→ₗ[ℂ] spinCGroup.detLineBundle 4 hpos P x :=
  ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (F := spinCGroup.DetFibre 4 hpos)
      (basePoint P x)).toLinearEquiv : _ →ₗ[ℂ] _).compAlternatingMap
    (η.compLinearMap ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC
      (F := SpinCHalfSpinor o hQ b ρ ε) (basePoint P x)).symm.toLinearEquiv : _ →ₗ[ℂ] _))

/-- **The determinant pairing in a frame.** If `W^ε` has complex dimension two, then for every
frame `p` of `P` over `x` the determinant pairing of the classes `[p, v i]` is the class
`[p, η v]`. -/
@[simp]
theorem spinorDetPairing_mk (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFibre 4 hpos) {x : B} (p : P x)
    (v : Fin 2 → SpinCHalfSpinor o hQ b ρ ε) :
    o.spinorDetPairing hQ b ρ ε P η x (fun i ↦ AssociatedBundle.mk SpinC p (v i)) =
      AssociatedBundle.mk SpinC p (η v) := by
  set g := PrincipalBundle.division SpinC (basePoint P x) p
  -- In the base frame the classes `[p, v i]` have coordinates `g • v i`.
  have hg : (fun i ↦ (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (basePoint P x)).symm
      (AssociatedBundle.mk SpinC p (v i))) = fun i ↦ g • v i :=
    funext fun i ↦ AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk _ _ _
  -- `g` scales the top-degree form `η` by its determinant `det g`.
  have hη : η (fun i ↦ g • v i) = g • η v := by
    have h := congrArg (fun η' ↦ η' v) (AlternatingMap.compLinearMap_eq_det_smul
      (Module.finBasisOfFinrankEq ℂ (SpinCHalfSpinor o hQ b ρ ε) h₂) η
      (DistribSMul.toLinearMap ℂ _ g))
    simp only [AlternatingMap.compLinearMap_apply, smul_apply] at h
    rw [spinCGroup.DetFibre.smul_def, ← det_realSpinCHalfSpinSmoothHom o hQ b ρ ε h₂ g]
    exact h
  simp only [spinorDetPairing, LinearMap.compAlternatingMap_apply,
    AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, hg, hη,
    AssociatedBundle.mkContinuousLinearEquiv_apply]
  rw [← AssociatedBundle.mk_smul, PrincipalBundle.smul_division]

/-- A nonzero alternating form on the model half-spinors induces a nonzero determinant
pairing on every fibre. -/
theorem spinorDetPairing_ne_zero (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    {η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFibre 4 hpos} (hη : η ≠ 0)
    (x : B) : o.spinorDetPairing hQ b ρ ε P η x ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v, η v ≠ 0 := by
    by_contra! h
    exact hη (AlternatingMap.ext h)
  intro h0
  have h := o.spinorDetPairing_mk hQ b ρ ε P h₂ η (basePoint P x) v
  rw [h0, zero_apply, ← AssociatedBundle.mk_zero (basePoint P x)] at h
  exact hv ((AssociatedBundle.mk_bijective (G := SpinC) (basePoint P x)).1 h).symm

/-- **The determinant line of the spinor bundle.** If `W^ε` has complex dimension two, a nonzero
alternating form `η` on the model half-spinors identifies the determinant line `⋀² W^ε_x` of
every fibre with the fibre `L_x` of the determinant line bundle, sending `[p, v 0] ∧ [p, v 1]` to
`[p, η v]` in every frame `p` (`Orientation.spinorDetEquiv_ιMulti_mk`). -/
def spinorDetEquiv (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFibre 4 hpos) (hη : η ≠ 0)
    (x : B) :
    ⋀[ℂ]^2 (o.spinorBundle hQ b ρ ε P x) ≃ₗ[ℂ] spinCGroup.detLineBundle 4 hpos P x := by
  refine LinearEquiv.ofBijective
    (exteriorPower.alternatingMapLinearEquiv (o.spinorDetPairing hQ b ρ ε P η x)) ?_
  set f := exteriorPower.alternatingMapLinearEquiv (o.spinorDetPairing hQ b ρ ε P η x)
  -- A frame identifies the fibre with the model half-spinors.
  let e := (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (F := SpinCHalfSpinor o hQ b ρ ε)
    (basePoint P x)).toLinearEquiv
  have : FiniteDimensional ℂ (o.spinorBundle hQ b ρ ε P x) := e.finiteDimensional
  -- Both sides are lines, and `f` is nonzero since it restricts to the determinant pairing.
  have hdom : finrank ℂ (⋀[ℂ]^2 (o.spinorBundle hQ b ρ ε P x)) = 1 := by
    have h : finrank ℂ (⋀[ℂ]^(finrank ℂ (o.spinorBundle hQ b ρ ε P x))
        (o.spinorBundle hQ b ρ ε P x)) = 1 :=
      TauCeti.finrank_detLine ℂ (o.spinorBundle hQ b ρ ε P x)
    -- The model is a type synonym of the eigenspace, so `h₂` is its dimension.
    have h₂' : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2 := h₂
    rwa [← e.finrank_eq, h₂'] at h
  have : FiniteDimensional ℂ (⋀[ℂ]^2 (o.spinorBundle hQ b ρ ε P x)) :=
    Module.finite_of_finrank_eq_succ hdom
  have hcod : finrank ℂ (spinCGroup.detLineBundle 4 hpos P x) = 1 :=
    ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (F := spinCGroup.DetFibre 4 hpos)
      (basePoint P x)).toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self ℂ))
  have : FiniteDimensional ℂ (spinCGroup.detLineBundle 4 hpos P x) :=
    Module.finite_of_finrank_eq_succ hcod
  have hf : f ≠ 0 := by
    intro h0
    apply o.spinorDetPairing_ne_zero hQ b ρ ε P h₂ hη x
    ext v
    simpa [f] using congrArg (fun g ↦ g (exteriorPower.ιMulti ℂ 2 v)) h0
  have hsurj : Function.Surjective f := surjective_of_ne_zero_of_finrank_eq_one hcod hf
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hdom.trans hcod.symm)).2 hsurj, hsurj⟩

/-- **The determinant line isomorphism in a frame.** In every frame `p` of `P` over `x`,
`spinorDetEquiv` sends `[p, v 0] ∧ [p, v 1]` to `[p, η v]`. -/
@[simp]
theorem spinorDetEquiv_ιMulti_mk (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFibre 4 hpos) (hη : η ≠ 0)
    {x : B} (p : P x) (v : Fin 2 → SpinCHalfSpinor o hQ b ρ ε) :
    o.spinorDetEquiv hQ b ρ ε P h₂ η hη x
        (exteriorPower.ιMulti ℂ 2 fun i ↦ AssociatedBundle.mk SpinC p (v i)) =
      AssociatedBundle.mk SpinC p (η v) := by
  simp only [spinorDetEquiv, LinearEquiv.ofBijective_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact o.spinorDetPairing_mk hQ b ρ ε P h₂ η p v

end Normed

/-! ### The Hermitian metric -/

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-- The half-spinor model of a Hermitian Clifford module is a complex inner product space. -/
instance : InnerProductSpace ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (InnerProductSpace ℂ (eigenspace (ρ (chirality Q o)) ε))

variable {B : Type*} [TopologicalSpace B]
  (P : B → Type*) [TopologicalSpace (TotalSpace SpinC P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle SpinC P] [∀ x, MulAction SpinCᵐᵒᵖ (P x)] [PrincipalBundle SpinC P]

/-- The Hermitian form on the fibres of the spinor bundle `W^ε`, conjugate-linear in the first
argument. In every frame `p` of `P` it is the inner product of the model half-spinors
(`Orientation.spinorInner_mk`); this does not depend on the frame when the Clifford generators
act skew-adjointly, because `Spinᶜ(4)` then acts unitarily on `W^ε`. -/
def spinorInner (x : B) :
    o.spinorBundle hQ b ρ ε P x →ₗ⋆[ℂ] o.spinorBundle hQ b ρ ε P x →ₗ[ℂ] ℂ :=
  ((innerₛₗ ℂ).comp (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC
      (F := SpinCHalfSpinor o hQ b ρ ε) (basePoint P x)).symm.toLinearEquiv.toLinearMap).compl₂
    (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC
      (F := SpinCHalfSpinor o hQ b ρ ε) (basePoint P x)).symm.toLinearEquiv.toLinearMap

/-- **The Hermitian form in a frame.** If the Clifford generators act skew-adjointly on `W`,
then for every frame `p` of `P` over `x` the Hermitian form of the classes `[p, ψ]` and `[p, χ]`
is the inner product `⟪ψ, χ⟫`. -/
@[simp]
theorem spinorInner_mk (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {x : B}
    (p : P x) (ψ χ : SpinCHalfSpinor o hQ b ρ ε) :
    o.spinorInner hQ b ρ ε P x (AssociatedBundle.mk SpinC p ψ) (AssociatedBundle.mk SpinC p χ) =
      ⟪ψ, χ⟫_ℂ := by
  simp only [spinorInner, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk,
    SpinCHalfSpinor.smul_def]
  exact inner_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hρ _ ψ χ

end Hermitian

end Orientation
