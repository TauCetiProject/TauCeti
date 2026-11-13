/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.HalfSpin
public import TauCeti.Geometry.Manifold.VectorBundle.Associated
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basic

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

The model fibers are the representation spaces

* `Orientation.SpinCHalfSpinor o hQ b ρ ε`, the `ε`-eigenspace of the chirality element on a
  Clifford module `W`, with the smooth half-spin action `Orientation.realSpinCHalfSpinSmoothHom`;
* `CliffordAlgebra.spinCGroup.DetFiber n hQ`, the line `ℂ` with `Spinᶜ(n)` acting through the
  determinant character `CliffordAlgebra.spinCGroup.det`.

The associated bundles are `Orientation.spinorBundle o hQ b ρ ε P`, the spinor bundle
`W^ε = P ×_{Spinᶜ(4)} W^ε`, and `CliffordAlgebra.spinCGroup.detLineBundle n hQ P`, the
determinant line `L = P ×_{Spinᶜ(n)} ℂ`. They are complex vector bundles, and `C^k` vector bundles
when `P` is a `C^k` principal bundle.

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
* The inner product of the model descends to the Hermitian form `Orientation.spinorInner` of the
  fibers. When the Clifford generators act skew-adjointly, `Spinᶜ(4)` acts unitarily on `W^ε`
  (`Orientation.inner_realSpinCHalfSpinSmoothHom_apply`), and the Hermitian form is the model
  inner product in every frame (`Orientation.spinorInner_mk`).

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
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
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

/-- The determinant line of a `C^k` principal `Spinᶜ(n)`-bundle is a `C^k` line bundle. -/
instance {k : ℕ∞ω} [ENat.LEInfty k] [ContMDiffFiberBundle k (spinCGroup (realCliffordForm n 0) hQ)
      P IB (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))] :
    ContMDiffVectorBundle k (DetFiber n hQ) (detLineBundle n hQ P) IB :=
  AssociatedBundle.contMDiffVectorBundle (𝕜 := ℝ) (𝓘(ℝ, realSpinLieModel n).prod (𝓡 1))

/-- The fibers of the determinant line are lines. -/
theorem finrank_detLineBundle (x : B) : finrank ℂ (detLineBundle n hQ P x) = 1 :=
  (AssociatedBundle.finrank_eq ℂ _ (DetFiber n hQ) P x).trans (DetFiber.finrank_eq n hQ)

end CliffordAlgebra.spinCGroup

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-! ### The spinor bundles -/

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (P : B → Type*) [TopologicalSpace (TotalSpace SpinC P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle SpinC P] [∀ x, MulAction SpinCᵐᵒᵖ (P x)] [PrincipalBundle SpinC P]

/-- The spinor bundle `W^ε = P ×_{Spinᶜ(4)} W^ε` of a principal `Spinᶜ(4)`-bundle `P`. -/
abbrev spinorBundle : B → Type _ :=
  AssociatedBundle SpinC P (SpinCHalfSpinor o hQ b ρ ε)

/-- The spinor bundle of a `C^k` principal `Spinᶜ(4)`-bundle is a `C^k` vector bundle. -/
instance {k : ℕ∞ω} [ENat.LEInfty k] [ContMDiffFiberBundle k SpinC P IB I] :
    ContMDiffVectorBundle k (SpinCHalfSpinor o hQ b ρ ε) (o.spinorBundle hQ b ρ ε P) IB :=
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

/-- **The determinant line of the spinor bundle.** If `W^ε` has complex dimension two, a nonzero
alternating form `η` on the model half-spinors induces, for each `x`, a linear isomorphism from
`⋀² W^ε_x` onto the fiber `L_x` of the determinant line bundle, sending `[p, v 0] ∧ [p, v 1]` to
`[p, η v]` in every frame `p` (`Orientation.spinorDetEquiv_ιMulti_mk`). It is the linear map
induced on `⋀² W^ε_x` by the descended pairing `TauCeti.AssociatedBundle.alternatingMap`
(`Orientation.spinorDetEquiv_apply`), bijective by
`TauCeti.exteriorPower.alternatingMapLinearEquiv_bijective`. -/
def spinorDetEquiv (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) (hη : η ≠ 0)
    (x : B) :
    ⋀[ℂ]^2 (o.spinorBundle hQ b ρ ε P x) ≃ₗ[ℂ] spinCGroup.detLineBundle 4 hpos P x :=
  LinearEquiv.ofBijective
    (exteriorPower.alternatingMapLinearEquiv (AssociatedBundle.alternatingMap SpinC P η x))
    (TauCeti.exteriorPower.alternatingMapLinearEquiv_bijective
      ((AssociatedBundle.finrank_eq ℂ SpinC _ P x).trans h₂)
      (spinCGroup.finrank_detLineBundle 4 hpos P x)
      ((AssociatedBundle.alternatingMap_eq_zero_iff x).not.2 hη))

/-- `spinorDetEquiv` is the linear map induced on `⋀² W^ε_x` by the descended pairing. -/
theorem spinorDetEquiv_apply (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) (hη : η ≠ 0)
    (x : B) (w : ⋀[ℂ]^2 (o.spinorBundle hQ b ρ ε P x)) :
    o.spinorDetEquiv hQ b ρ ε P h₂ η hη x w =
      exteriorPower.alternatingMapLinearEquiv (AssociatedBundle.alternatingMap SpinC P η x) w :=
  (rfl)

/-- **The determinant line isomorphism in a frame.** In every frame `p` of `P` over `x`,
`spinorDetEquiv` sends `[p, v 0] ∧ [p, v 1]` to `[p, η v]`. -/
@[simp]
theorem spinorDetEquiv_ιMulti_mk (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) (hη : η ≠ 0)
    {x : B} (p : P x) (v : Fin 2 → SpinCHalfSpinor o hQ b ρ ε) :
    o.spinorDetEquiv hQ b ρ ε P h₂ η hη x
        (exteriorPower.ιMulti ℂ 2 fun i ↦ AssociatedBundle.mk SpinC p (v i)) =
      AssociatedBundle.mk SpinC p (η v) := by
  rw [spinorDetEquiv_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    alternatingMap_spinorBundle_mk o hQ b ρ ε P h₂ η p v]

/-- **The inverse determinant line isomorphism in a frame.** In every frame `p` of `P` over `x`,
the inverse of `spinorDetEquiv` sends `[p, η v]` to `[p, v 0] ∧ [p, v 1]`. -/
@[simp]
theorem spinorDetEquiv_symm_mk (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) (hη : η ≠ 0)
    {x : B} (p : P x) (v : Fin 2 → SpinCHalfSpinor o hQ b ρ ε) :
    (o.spinorDetEquiv hQ b ρ ε P h₂ η hη x).symm (AssociatedBundle.mk SpinC p (η v)) =
      exteriorPower.ιMulti ℂ 2 fun i ↦ AssociatedBundle.mk SpinC p (v i) := by
  rw [LinearEquiv.symm_apply_eq, spinorDetEquiv_ιMulti_mk]

end Normed

/-! ### The Hermitian metric -/

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)
  {B : Type*} [TopologicalSpace B]
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

/-- `spinorInner` is the form induced by the model inner product through
`TauCeti.AssociatedBundle.sesqForm`. -/
theorem spinorInner_def (x : B) :
    o.spinorInner hQ b ρ ε P x = AssociatedBundle.sesqForm SpinC P (innerₛₗ ℂ) x :=
  (rfl)

/-- **The Hermitian form in a frame.** If the Clifford generators act skew-adjointly on `W`,
then for every frame `p` of `P` over `x` the Hermitian form of the classes `[p, ψ]` and `[p, χ]`
is the inner product `⟪ψ, χ⟫`. -/
@[simp]
theorem spinorInner_mk (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {x : B}
    (p : P x) (ψ χ : SpinCHalfSpinor o hQ b ρ ε) :
    o.spinorInner hQ b ρ ε P x (AssociatedBundle.mk SpinC p ψ) (AssociatedBundle.mk SpinC p χ) =
      ⟪ψ, χ⟫_ℂ :=
  AssociatedBundle.sesqForm_mk (SpinCHalfSpinor.inner_smul_smul o hQ b ρ ε hρ) p ψ χ

/-- The Hermitian form of the spinor bundle is conjugate-symmetric. -/
theorem spinorInner_conj_symm {x : B} (w w' : o.spinorBundle hQ b ρ ε P x) :
    starRingEnd ℂ (o.spinorInner hQ b ρ ε P x w' w) = o.spinorInner hQ b ρ ε P x w w' :=
  (AssociatedBundle.isSymm_sesqForm ⟨fun ψ χ ↦ inner_conj_symm χ ψ⟩ x).eq w' w

/-- The diagonal values of the Hermitian form of the spinor bundle have nonnegative real part. -/
theorem re_spinorInner_self_nonneg {x : B} (w : o.spinorBundle hQ b ρ ε P x) :
    0 ≤ (o.spinorInner hQ b ρ ε P x w w).re :=
  AssociatedBundle.re_sesqForm_self_nonneg (f := innerₛₗ ℂ) (fun ψ ↦ inner_self_nonneg (x := ψ)) w

/-- The Hermitian form of the spinor bundle vanishes on the diagonal only at zero. -/
@[simp]
theorem spinorInner_self_eq_zero {x : B} {w : o.spinorBundle hQ b ρ ε P x} :
    o.spinorInner hQ b ρ ε P x w w = 0 ↔ w = 0 :=
  AssociatedBundle.sesqForm_self_eq_zero (fun ψ ↦ (inner_self_eq_zero (𝕜 := ℂ) (x := ψ)).1)

end Hermitian

end Orientation
