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
`TauCeti.AssociatedBundle`, and equips their fibers with the determinant and Hermitian structure
of the model representations.

The model fibers are type synonyms carrying the actions:

* `Orientation.SpinCHalfSpinor o hQ b ρ ε`, the `ε`-eigenspace of the chirality element on a
  Clifford module `W`, with the smooth half-spin action `Orientation.realSpinCHalfSpinSmoothHom`;
* `CliffordAlgebra.spinCGroup.DetFiber n hQ`, the line `ℂ` with `Spinᶜ(n)` acting through the
  determinant character `CliffordAlgebra.spinCGroup.det`.

The associated bundles are `Orientation.spinorBundle o hQ b ρ ε P`, the spinor bundle
`W^ε = P ×_{Spinᶜ(4)} W^ε`, and `CliffordAlgebra.spinCGroup.detLineBundle n hQ P`, the
determinant line `L = P ×_{Spinᶜ(n)} ℂ`. They are complex vector bundles, and smooth vector bundles
when `P` is a smooth principal bundle.

A point `p` of `P` over `x` identifies the model with the fiber over `x` by `v ↦ [p, v]`, and
changing `p` acts on the model by the representation. Structure on the model that is compatible
with the representation therefore descends to the fibers (`TauCeti.AssociatedBundle.alternatingMap`,
`TauCeti.AssociatedBundle.sesqForm`):

* `Spinᶜ(4)` acts on a two-dimensional `W^ε` with determinant `z²`
  (`Orientation.det_realSpinCHalfSpinSmoothHom`), so every alternating two-form `η` on the model,
  with values in the model of `L`, is equivariant
  (`Orientation.SpinCHalfSpinor.alternatingMap_apply_smul`) and descends to a pairing of `W^ε_x`
  with values in `L_x`, which reads `[p, v 0], [p, v 1] ↦ [p, η v]` in every frame
  (`Orientation.alternatingMap_spinorBundle_mk`).
  For `η ≠ 0` it induces, for each `x`, a linear isomorphism `⋀² W^ε_x ≃ L_x` of fibers
  (`Orientation.spinorDetEquiv`). That these isomorphisms form a continuous or smooth bundle
  isomorphism is not established here.
* When the Clifford generators act skew-adjointly, `Spinᶜ(4)` acts unitarily on `W^ε`
  (`Orientation.inner_realSpinCHalfSpinSmoothHom_apply`), and the inner product of the model
  descends to the Hermitian form `Orientation.spinorInner` of the fibers
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

/-- The model fiber `ℂ` of the determinant line of a `Spinᶜ(n)`-bundle, on which `Spinᶜ(n)`
acts through its determinant character `[s, z] ↦ z²` (`CliffordAlgebra.spinCGroup.det`). -/
@[expose]
def DetFiber (_n : ℕ) (_hQ : realCliffordForm _n 0 ≠ 0) : Type := ℂ

namespace DetFiber

instance : NormedAddCommGroup (DetFiber n hQ) := inferInstanceAs (NormedAddCommGroup ℂ)

instance : NormedSpace ℂ (DetFiber n hQ) := inferInstanceAs (NormedSpace ℂ ℂ)

/-- The model determinant fiber is the line `ℂ`. -/
def linearEquiv : DetFiber n hQ ≃ₗ[ℂ] ℂ := LinearEquiv.refl ℂ ℂ

/-- The model determinant fiber is a line. -/
@[simp]
theorem finrank_eq : finrank ℂ (DetFiber n hQ) = 1 :=
  (linearEquiv n hQ).finrank_eq.trans (Module.finrank_self ℂ)

instance : FiniteDimensional ℂ (DetFiber n hQ) := inferInstanceAs (FiniteDimensional ℂ ℂ)

/-- `Spinᶜ(n)` acts on the model determinant fiber through its determinant character. -/
instance : DistribMulAction (spinCGroup (realCliffordForm n 0) hQ) (DetFiber n hQ) :=
  DistribMulAction.compHom ℂ (Circle.coeHom.comp (det (realCliffordForm n 0) hQ))

/-- `Spinᶜ(n)` acts on the model determinant fiber by its determinant character. -/
theorem smul_def (x : spinCGroup (realCliffordForm n 0) hQ) (w : DetFiber n hQ) :
    x • w = (det (realCliffordForm n 0) hQ x : ℂ) • w := (rfl)

instance : SMulCommClass (spinCGroup (realCliffordForm n 0) hQ) ℂ (DetFiber n hQ) where
  smul_comm x c w := by simp only [smul_def, smul_comm (det _ hQ x : ℂ) c w]

instance : SMulCommClass (spinCGroup (realCliffordForm n 0) hQ) ℝ (DetFiber n hQ) where
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
instance : ContMDiffSMul (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1)) 𝓘(ℝ, DetFiber n hQ) ∞
    (spinCGroup (realCliffordForm n 0) hQ) (DetFiber n hQ) where
  contMDiff_smul := by
    simp only [smul_def]
    exact contMDiff_det_mul n hQ

instance : ContinuousSMul (spinCGroup (realCliffordForm n 0) hQ) (DetFiber n hQ) where
  continuous_smul := by
    simp only [smul_def]
    exact (contMDiff_det_mul n hQ).continuous

end DetFiber

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
  AssociatedBundle (spinCGroup (realCliffordForm n 0) hQ) P (DetFiber n hQ)

/-- The determinant line of a smooth principal `Spinᶜ(n)`-bundle is a smooth line bundle. -/
instance [ContMDiffFiberBundle ∞ (spinCGroup (realCliffordForm n 0) hQ) P IB
      (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))] :
    ContMDiffVectorBundle ∞ (DetFiber n hQ) (detLineBundle n hQ P) IB :=
  AssociatedBundle.contMDiffVectorBundle (𝕜 := ℝ) (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))

/-- The fibers of the determinant line are lines. -/
@[simp]
theorem finrank_detLineBundle (x : B) : finrank ℂ (detLineBundle n hQ P x) = 1 :=
  (AssociatedBundle.finrank_eq ℂ _ (DetFiber n hQ) P x).trans (DetFiber.finrank_eq n hQ)

end CliffordAlgebra.spinCGroup

namespace Orientation

/-! ### The half-spinor model fibers -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-- The model fiber of the spinor bundle `W^ε`: the `ε`-eigenspace of the chirality element
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

/-- The half-spinor model is the `ε`-eigenspace of the chirality element. -/
def linearEquiv : SpinCHalfSpinor o hQ b ρ ε ≃ₗ[ℂ] eigenspace (ρ (chirality Q o)) ε :=
  LinearEquiv.refl ℂ _

omit [FiniteDimensional ℂ W] in
/-- The half-spinor model has the dimension of the chirality eigenspace. -/
theorem finrank_eq :
    finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = finrank ℂ (eigenspace (ρ (chirality Q o)) ε) :=
  (linearEquiv o hQ b ρ ε).finrank_eq

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
  simp only [AlternatingMap.compLinearMap_apply, smul_apply] at h
  rw [spinCGroup.DetFiber.smul_def,
    ← det_realSpinCHalfSpinSmoothHom o hQ b ρ ε ((finrank_eq o hQ b ρ ε).symm.trans h₂) g]
  exact h

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

/-! ### The determinant line of the spinor bundles -/

/-- **The determinant pairing in a frame.** If `W^ε` has complex dimension two, an alternating
form `η` on the model half-spinors induces a pairing of the fiber `W^ε_x` with values in `L_x`
that, in every frame `p` of `P` over `x`, sends the classes `[p, v i]` to `[p, η v]`. -/
@[simp]
theorem alternatingMap_spinorBundle_mk (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) {x : B} (p : P x)
    (v : Fin 2 → SpinCHalfSpinor o hQ b ρ ε) :
    AssociatedBundle.alternatingMap SpinC P η x (fun i ↦ AssociatedBundle.mk SpinC p (v i)) =
      AssociatedBundle.mk SpinC p (η v) :=
  AssociatedBundle.alternatingMap_mk (SpinCHalfSpinor.alternatingMap_apply_smul o hQ b ρ ε h₂ η) p v

/-- If `W^ε` has complex dimension two, so has every fiber of the spinor bundle, and its second
exterior power is a line. -/
theorem finrank_exteriorPower_two_spinorBundle (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (x : B) : finrank ℂ (⋀[ℂ]^2 (o.spinorBundle hQ b ρ ε P x)) = 1 := by
  have h : finrank ℂ (⋀[ℂ]^(finrank ℂ (o.spinorBundle hQ b ρ ε P x))
      (o.spinorBundle hQ b ρ ε P x)) = 1 :=
    TauCeti.finrank_detLine ℂ (o.spinorBundle hQ b ρ ε P x)
  rwa [AssociatedBundle.finrank_eq, h₂] at h

/-- If `W^ε` has complex dimension two, a nonzero alternating form `η` on the model half-spinors
induces a bijection from `⋀² W^ε_x` onto `L_x`. -/
theorem alternatingMapLinearEquiv_spinorBundle_bijective
    (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    {η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos} (hη : η ≠ 0)
    (x : B) :
    Function.Bijective (exteriorPower.alternatingMapLinearEquiv
      (AssociatedBundle.alternatingMap SpinC P η x)) := by
  set f := exteriorPower.alternatingMapLinearEquiv (AssociatedBundle.alternatingMap SpinC P η x)
  have hdom := o.finrank_exteriorPower_two_spinorBundle hQ b ρ ε P h₂ x
  have hcod := spinCGroup.finrank_detLineBundle 4 hpos P x
  have : FiniteDimensional ℂ (⋀[ℂ]^2 (o.spinorBundle hQ b ρ ε P x)) :=
    Module.finite_of_finrank_eq_succ hdom
  -- `f` is nonzero, since it restricts to the induced alternating map on decomposable vectors.
  have hf : f ≠ 0 := by
    intro h0
    apply (AssociatedBundle.alternatingMap_eq_zero_iff (G := SpinC) (P := P) x).not.2 hη
    ext v
    simpa [f] using congrArg (fun g ↦ g (exteriorPower.ιMulti ℂ 2 v)) h0
  have hsurj : Function.Surjective f := surjective_of_ne_zero_of_finrank_eq_one hcod hf
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hdom.trans hcod.symm)).2 hsurj, hsurj⟩

/-- **The determinant line of the spinor bundle.** If `W^ε` has complex dimension two, a nonzero
alternating form `η` on the model half-spinors induces, for each `x`, a linear isomorphism from
`⋀² W^ε_x` onto the fiber `L_x` of the determinant line bundle, sending `[p, v 0] ∧ [p, v 1]` to
`[p, η v]` in every frame `p` (`Orientation.spinorDetEquiv_ιMulti_mk`). -/
def spinorDetEquiv (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) (hη : η ≠ 0)
    (x : B) :
    ⋀[ℂ]^2 (o.spinorBundle hQ b ρ ε P x) ≃ₗ[ℂ] spinCGroup.detLineBundle 4 hpos P x :=
  LinearEquiv.ofBijective _ (o.alternatingMapLinearEquiv_spinorBundle_bijective hQ b ρ ε P h₂ hη x)

/-- **The determinant line isomorphism in a frame.** In every frame `p` of `P` over `x`,
`spinorDetEquiv` sends `[p, v 0] ∧ [p, v 1]` to `[p, η v]`. -/
@[simp]
theorem spinorDetEquiv_ιMulti_mk (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) (hη : η ≠ 0)
    {x : B} (p : P x) (v : Fin 2 → SpinCHalfSpinor o hQ b ρ ε) :
    o.spinorDetEquiv hQ b ρ ε P h₂ η hη x
        (exteriorPower.ιMulti ℂ 2 fun i ↦ AssociatedBundle.mk SpinC p (v i)) =
      AssociatedBundle.mk SpinC p (η v) := by
  simp only [spinorDetEquiv, LinearEquiv.ofBijective_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact o.alternatingMap_spinorBundle_mk hQ b ρ ε P h₂ η p v

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

/-- The Hermitian form on the fibers of the spinor bundle `W^ε`, conjugate-linear in the first
argument, induced by the inner product of the model half-spinors. It is the model inner product
read in a fixed reference point of `P x`. When the Clifford generators act skew-adjointly it is
the model inner product in every frame (`Orientation.spinorInner_mk`), so it does not depend on
that choice. -/
def spinorInner (x : B) :
    o.spinorBundle hQ b ρ ε P x →ₗ⋆[ℂ] o.spinorBundle hQ b ρ ε P x →ₗ[ℂ] ℂ :=
  AssociatedBundle.sesqForm SpinC P (innerₛₗ ℂ) x

/-- **The Hermitian form in a frame.** If the Clifford generators act skew-adjointly on `W`,
then for every frame `p` of `P` over `x` the Hermitian form of the classes `[p, ψ]` and `[p, χ]`
is the inner product `⟪ψ, χ⟫`. -/
@[simp]
theorem spinorInner_mk (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {x : B}
    (p : P x) (ψ χ : SpinCHalfSpinor o hQ b ρ ε) :
    o.spinorInner hQ b ρ ε P x (AssociatedBundle.mk SpinC p ψ) (AssociatedBundle.mk SpinC p χ) =
      ⟪ψ, χ⟫_ℂ :=
  AssociatedBundle.sesqForm_mk
    (fun g ψ χ ↦ by
      rw [SpinCHalfSpinor.smul_def, SpinCHalfSpinor.smul_def]
      exact inner_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hρ g ψ χ) p ψ χ

/-- Two vectors of a fiber of the spinor bundle are classes in a common frame. -/
private theorem exists_mk_mk {x : B} (w w' : o.spinorBundle hQ b ρ ε P x) :
    ∃ (p : P x) (ψ χ : SpinCHalfSpinor o hQ b ρ ε),
      AssociatedBundle.mk SpinC p ψ = w ∧ AssociatedBundle.mk SpinC p χ = w' := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk w
  obtain ⟨χ, rfl⟩ := (AssociatedBundle.mk_bijective (G := SpinC) p).2 w'
  exact ⟨p, ψ, χ, rfl, rfl⟩

/-- The Hermitian form of the spinor bundle is conjugate-symmetric. -/
theorem spinorInner_conj_symm (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {x : B}
    (w w' : o.spinorBundle hQ b ρ ε P x) :
    starRingEnd ℂ (o.spinorInner hQ b ρ ε P x w' w) = o.spinorInner hQ b ρ ε P x w w' := by
  obtain ⟨p, ψ, χ, rfl, rfl⟩ := o.exists_mk_mk hQ b ρ ε P w w'
  simp only [o.spinorInner_mk hQ b ρ ε P hρ, inner_conj_symm]

/-- The Hermitian form of the spinor bundle is positive semidefinite. -/
theorem re_spinorInner_self_nonneg (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {x : B} (w : o.spinorBundle hQ b ρ ε P x) :
    0 ≤ (o.spinorInner hQ b ρ ε P x w w).re := by
  obtain ⟨p, ψ, -, rfl, -⟩ := o.exists_mk_mk hQ b ρ ε P w w
  rw [o.spinorInner_mk hQ b ρ ε P hρ]
  exact inner_self_nonneg (𝕜 := ℂ) (x := ψ)

/-- The Hermitian form of the spinor bundle is definite. -/
@[simp]
theorem spinorInner_self_eq_zero (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {x : B} {w : o.spinorBundle hQ b ρ ε P x} :
    o.spinorInner hQ b ρ ε P x w w = 0 ↔ w = 0 := by
  obtain ⟨p, ψ, -, rfl, -⟩ := o.exists_mk_mk hQ b ρ ε P w w
  rw [o.spinorInner_mk hQ b ρ ε P hρ, inner_self_eq_zero, ← AssociatedBundle.mk_zero (G := SpinC) p,
    (AssociatedBundle.mk_bijective (G := SpinC) p).1.eq_iff]

end Hermitian

end Orientation
