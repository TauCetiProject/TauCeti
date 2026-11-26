/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Bundle.QuadraticTwoForm
public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
public import TauCeti.Analysis.PDE.SeibergWitten.UnitaryLift
public import TauCeti.Topology.VectorBundle.SpinStructure.AlmostComplex.Anticanonical
public import TauCeti.Topology.VectorBundle.SpinStructure.HalfSpinorSplitting

/-!
# The canonical spinor of the canonical `Spinᶜ` structure

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, such as the tangent bundle of an almost Hermitian four-manifold,
and let `𝔰` be its canonical `Spinᶜ` structure
(`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`), induced from the unitary frames by the
lift `σ : U(ℝ⁴, J₀) → Spinᶜ(4)` (`TauCeti.unitarySpinCLift`) for a unitary frame `e` of a model
complex structure `J₀`. Its positive half-spinor bundle `W⁺ = 𝔰.halfSpinorBundle o hQ b ρ hρ 1`
is built from a model Hermitian Clifford module, compared with `Spinᶜ(4)` through an orthonormal
basis `b` of the model four-space `V`. In Taubes's analysis of the Seiberg–Witten equations on a
symplectic four-manifold, a positive spinor is written `α u₀ + β`, where `u₀` is a unit section of
the trivial summand of `W⁺ = 1 ⊕ K⁻¹`, the `-2i`-eigenline of `c₂(ω)`. This file constructs `u₀`
and the fibrewise splitting `W⁺_x ≃ ℂ × K⁻¹_x`, with continuous components.

**The model.** Let `JV` be the complex structure of `V` corresponding to `J₀` under `b`. Read on `V`
through `b`, the lift `σ g` is the quaternionic lift `OrthonormalBasis.spinCUnitary` of the frame
`e` carried to `V`, applied to the unitary matrix of `g`
(`TauCeti.realSpinCGroupHom_unitarySpinCLift`). Both are homomorphisms from `U(2)`
lifting the rotation with the complex determinant, and such a lift is unique
(`OrthonormalBasis.eq_spinCUnitary`). The quaternionic lift fixes the `-2i`-eigenspace of
`c₂(ω_JV)` in the positive half-spinors (`TauCeti.SeibergWitten.canonicalLineFixingSubgroup`), so
`σ g` fixes Taubes's canonical line of the model
(`TauCeti.SeibergWitten.realSpinCGroupHom_unitarySpinCLift_mem_canonicalLineFixingSubgroup`).

**The section.** For a model spinor `u` on the canonical line, `P_α u = u`, the class
`u₀(x) = [[p, 1], u]` does not depend on the unitary frame `p` over `x`
(`TauCeti.OrthonormalFrameBundle.canonicalSpinor_eq_mk`): changing `p` to `p • g` changes
`[p, 1]` to `[p, 1] • σ(g)`, and `σ(g)` fixes `u`. This is the canonical spinor
`TauCeti.OrthonormalFrameBundle.canonicalSpinor`, a section of `W⁺` built from `J` alone. It has
the norm of `u` (`TauCeti.OrthonormalFrameBundle.norm_canonicalSpinor`), so it is a unit section
for a unit `u`, and it is continuous (`TauCeti.OrthonormalFrameBundle.continuous_canonicalSpinor`).
Since a unitary frame carries `J₀` to `J`, the vector frame of `[p, 1]` carries the Kähler
two-vector `ω` of `J` to that of `JV`
(`TauCeti.OrthonormalFrameBundle.map_vectorFrame_canonicalSpinCStructureInl_kahlerForm`), so on
every fibre the pointwise identities of the canonical line hold:
`C(iω) u₀ = 2 u₀`, that is `c₂(ω) u₀ = -2i u₀`
(`TauCeti.OrthonormalFrameBundle.cliffordRestriction_kahlerForm_canonicalSpinor`), and
`q(u₀) = (‖u‖² / 4) ω` (`TauCeti.OrthonormalFrameBundle.quadraticTwoForm_canonicalSpinor`), which
is Taubes's `q(u₀) = iω/4` for a unit spinor.

**The fibrewise splitting.** For a nonzero model spinor `u` on the canonical line, the canonical
spinor vanishes nowhere (`TauCeti.OrthonormalFrameBundle.canonicalSpinor_ne_zero`), so it splits
each fibre `W⁺_x` into the line spanned by `u₀(x)` and a complement isomorphic to the fibre of the
determinant line `L` (`TauCeti.SpinCStructure.halfSpinorEquivProd`), and `L` is the anticanonical
line
`K⁻¹ = Λ²_ℂ (E, J)` (`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle`).
For a nonzero alternating form `ω` on the model positive half-spinors, of complex dimension two,
the composite is the complex linear isomorphism `W⁺_x ≃ ℂ × K⁻¹_x`,
`ψ ↦ (⟪u₀(x), ψ⟫, ω(u₀(x), ψ))` (`TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd`).
In a unitary frame `p` it sends `[[p, 1], φ]` to `(⟪u, φ⟫, ω(u, φ) (p e₀ ∧ p e₂))`
(`TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd_mk`), it sends `u₀` to `(‖u‖², 0)`
(`TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd_canonicalSpinor`), and its two
components are continuous on total spaces
(`TauCeti.OrthonormalFrameBundle.continuous_fst_canonicalHalfSpinorEquivProd`,
`TauCeti.OrthonormalFrameBundle.continuous_snd_canonicalHalfSpinorEquivProd`). Its inverse sends
`(a, 0)` to `(a / ‖u‖²) u₀(x)`
(`TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd_symm_mk_zero`), which gives the
decomposition `ψ = α u₀(x) + β` of a positive spinor with `α = ⟪u₀(x), ψ⟫ / ‖u‖²` and `β` in the
complement of `u₀(x)` identified with `K⁻¹_x`
(`TauCeti.OrthonormalFrameBundle.smul_canonicalSpinor_add_canonicalHalfSpinorEquivProd_symm_zero`).

Only the forward components of the fibrewise splitting are shown continuous: the bundle
isomorphism `W⁺ ≃ 1 ⊕ K⁻¹` (continuity of the inverse) and the subbundle `K⁻¹ ⊂ W⁺` are not
constructed here, nor are the canonical connection `A₀` and the identity `D_{A₀} u₀ = 0` on a
manifold.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.canonicalSpinor`: the canonical spinor `u₀ = [[p, 1], u]`.
* `TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd`: the fibrewise splitting
  `W⁺_x ≃ ℂ × K⁻¹_x`, `ψ ↦ (⟪u₀(x), ψ⟫, ω(u₀(x), ψ))`.

## Main results

* `TauCeti.OrthonormalFrameBundle.map_vectorFrame_canonicalSpinCStructureInl_kahlerForm`: the
  vector frame of `[p, 1]` carries the Kähler two-vector of `J` to that of the model.
* `TauCeti.OrthonormalFrameBundle.canonicalSpinor_eq_mk`: `u₀(x) = [[p, 1], u]` for every unitary
  frame `p` over `x`.
* `TauCeti.OrthonormalFrameBundle.norm_canonicalSpinor`,
  `TauCeti.OrthonormalFrameBundle.continuous_canonicalSpinor`: `u₀` has the norm of `u` and is
  continuous.
* `TauCeti.OrthonormalFrameBundle.cliffordRestriction_kahlerForm_canonicalSpinor`,
  `TauCeti.OrthonormalFrameBundle.quadraticTwoForm_canonicalSpinor`: `C(iω) u₀ = 2 u₀` and
  `q(u₀) = (‖u‖² / 4) ω`.
* `TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd_mk`,
  `TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd_canonicalSpinor`: the splitting in a
  unitary frame, and its value `(‖u‖², 0)` on `u₀`.
* `TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd_symm_mk_zero`,
  `TauCeti.OrthonormalFrameBundle.smul_canonicalSpinor_add_canonicalHalfSpinorEquivProd_symm_zero`:
  the inverse on the trivial summand, and the decomposition `ψ = α u₀ + β`.
* `TauCeti.OrthonormalFrameBundle.continuous_fst_canonicalHalfSpinorEquivProd`,
  `TauCeti.OrthonormalFrameBundle.continuous_snd_canonicalHalfSpinorEquivProd`: continuity of its
  components on total spaces.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, §1(c)–(d).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Appendix D.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants and the Van de Ven conjecture*, 1995, §5
  (the splitting `W⁺ = 1 ⊕ K⁻¹` of the canonical `Spinᶜ` structure).
-/

public section

noncomputable section

open Bundle MulOpposite Module Module.End TauCeti CliffordAlgebra TauCeti.CliffordAlgebra

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)

/-! ### The canonical spinor -/

namespace TauCeti.OrthonormalFrameBundle

open Orientation.HalfSpinModel SeibergWitten

local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
  (hJ₂ : ∀ x v, J x (J x v) = -v)
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (hF : finrank ℝ F = 4) (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance finiteDimensionalCanonicalSpinorModel : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

/-- The dimension of `V`, in the form taken by the Hodge star of two-forms. -/
local notation "hkl" => (Eq.symm (Fact.out : finrank ℝ V = 4) : 2 + 2 = finrank ℝ V)

variable {JV : AlmostComplexStructure V}
  (hJV : ∀ w, JV (b.repr.symm w) =
    b.repr.symm ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) w))
  {u : o.HalfSpinModel hQ b ρ hρ 1}
  (hu : cliffordProjection o ρ JV.kahlerForm (toPositiveHalfSpinors o hQ b ρ hρ u) =
    toPositiveHalfSpinors o hQ b ρ hρ u)

variable (u) in
/-- **The canonical spinor** `u₀` of the canonical `Spinᶜ` structure of a rank-four bundle with an
orthogonal complex structure `J`: the section `x ↦ [[p, 1], u]` of the positive half-spinor bundle,
for a unitary frame `p` over `x` and a fixed model spinor `u`. When `u` lies on Taubes's canonical
line, `P_α u = u` for the complex structure `JV` of the model corresponding to `J₀`, the class does
not depend on the unitary frame `p`
(`TauCeti.OrthonormalFrameBundle.canonicalSpinor_eq_mk`); it is defined in a chosen frame. -/
def canonicalSpinor (x : X) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorBundle o hQ b ρ hρ 1 x :=
  AssociatedBundle.mk SpinC
    (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ (Classical.arbitrary _)) u

include hJV hu in
/-- **The canonical spinor in every unitary frame**: `u₀(x) = [[p, 1], u]` for every unitary frame
`p` over `x`, when `u` lies on the canonical line of the model. -/
theorem canonicalSpinor_eq_mk {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x =
      AssociatedBundle.mk SpinC (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) u := by
  rw [canonicalSpinor]
  generalize (Classical.arbitrary ((unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)) = q
  rw [← PrincipalBundle.smul_division (G := Subgroup.centralizer {J₀}) q p,
    canonicalSpinCStructureInl_smul, AssociatedBundle.mk_smul]
  congr 1
  refine toEigenspace.injective ?_
  rw [toEigenspace_smul, Orientation.realSpinCHalfSpinSmoothHom_apply o hQ b ρ 1
    (b.ne_zero_of_neg_norm_sq hQ), LinearMap.coe_toContinuousLinearMap']
  refine (mem_canonicalLineFixingSubgroup_iff.1
    (realSpinCGroupHom_unitarySpinCLift_mem_canonicalLineFixingSubgroup (o := o) (ρ := ρ) hJ₀ e h₀
      h₂ hQ b hJV (b.ne_zero_of_neg_norm_sq hQ) _) _ ?_).symm
  have h := bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu
  rwa [coe_toPositiveHalfSpinors] at h

/-- **The canonical spinor has the norm of the model spinor**: `‖u₀(x)‖ = ‖u‖` at every point. -/
@[simp]
theorem norm_canonicalSpinor (x : X) :
    ‖canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x‖ = ‖u‖ := by
  rw [canonicalSpinor, ← AssociatedBundle.mkLinearIsometryEquiv_apply (𝕜 := ℂ),
    LinearIsometryEquiv.norm_map]

/-- **The canonical spinor vanishes nowhere** when the model spinor is nonzero. -/
theorem canonicalSpinor_ne_zero (hu₀ : u ≠ 0) (x : X) :
    canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_canonicalSpinor]
  exact norm_ne_zero_iff.2 hu₀

include hJV hu in
/-- **The canonical spinor is a continuous section** of the positive half-spinor bundle, when `u`
lies on the canonical line of the model. -/
theorem continuous_canonicalSpinor :
    Continuous fun x ↦
      TotalSpace.mk' (o.HalfSpinModel hQ b ρ hρ 1) x
        (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  -- `Trivialization.symm` takes a `Zero` instance on the fibres for its value off the base set; the
  -- unitary frames have none, and the value off `t.baseSet` is never used below.
  let : ∀ y, Zero ((unitaryFrameLift hJ hJ₂ hJ₀ hF).P y) := fun _ ↦ ⟨Classical.arbitrary _⟩
  set t := trivializationAt (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x₀
  have hσ : ContinuousOn
      (fun y ↦ TotalSpace.mk' (Subgroup.centralizer {J₀}) y (t.symm y 1)) t.baseSet :=
    t.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
      fun _ hy ↦ ⟨hy, Set.mem_univ _⟩
  have hinl : ContinuousOn (fun y ↦ TotalSpace.mk' SpinC y
      (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ (t.symm y 1))) t.baseSet :=
    (continuous_canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂).comp_continuousOn hσ
  refine ((hinl.totalSpaceMk_associatedBundleMk (v := fun _ ↦ u) continuousOn_const).congr
    fun y _ ↦ ?_).continuousAt (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀))
  rw [canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu (t.symm y 1)]

include hJV in
/-- **The frame comparison of Kähler forms**: the vector frame `κ_p : E x ≃ V` of the point
`[p, 1]` of the canonical `Spinᶜ` structure carries the Kähler two-vector of `J x` to that of the
model complex structure `JV`, for every unitary frame `p` over `x`. -/
theorem map_vectorFrame_canonicalSpinCStructureInl_kahlerForm {x : X} [FiniteDimensional ℝ (E x)]
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) {Jx : AlmostComplexStructure (E x)}
    (hJx : ∀ v, Jx v = J x v) :
    exteriorPower.map 2 ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).vectorFrame b
      (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)).toLinearMap Jx.kahlerForm =
        JV.kahlerForm := by
  set κ := (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).vectorFrame b
    (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
  have hκ : ∀ w, κ w = b.repr.symm (p.val.frame.symm w) := fun w ↦ by
    rw [SpinCStructure.vectorFrame_apply_eq_repr_symm, frameAt_canonicalSpinCStructureInl]
  refine AlmostComplexStructure.map_kahlerForm_of_isComplexLinearMap
    (fun v w ↦ by rw [hJx, hJx, LinearIsometryEquiv.inner_map_map])
    ((isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ ?_)
  have hp := mem_unitaryFrames_iff.1 p.property (p.val.frame.symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at hp
  simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [hJx, hκ, hκ, hJV, ← hp, LinearIsometryEquiv.symm_apply_apply]

include hJV hu in
/-- **The canonical spinor lies on the canonical line**: `C(iω) u₀ = 2 u₀`, that is,
`c₂(ω) u₀ = -2i u₀`, for the Kähler two-vector `ω` of `J`, on every fibre. -/
theorem cliffordRestriction_kahlerForm_canonicalSpinor (x : X) [FiniteDimensional ℝ (E x)]
    {Jx : AlmostComplexStructure (E x)} (hJx : ∀ v, Jx v = J x v) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordRestriction o hQ b ρ hρ x
        Jx.kahlerForm (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x) =
      (2 : ℂ) • canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x := by
  have p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x := Classical.arbitrary _
  rw [canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu p,
    SpinCStructure.cliffordRestriction_mk,
    map_vectorFrame_canonicalSpinCStructureInl_kahlerForm hJ hJ₂ hJ₀ hF e h₀ h₂ b hJV p hJx,
    (cliffordProjection_apply_eq_self_iff o ρ).1 hu, _root_.map_smul,
    LinearIsometryEquiv.symm_apply_apply,
    AssociatedBundle.mk_smul_scalar]

include hJV hu in
/-- **The quadratic two-form of the canonical spinor**: `q(u₀) = (‖u‖² / 4) ω` for the Kähler
two-vector `ω` of `J`, on every fibre, when the Kähler two-vector of the model is self-dual and
the positive half-spinors have rank two. For a unit model spinor this is Taubes's `q(u₀) = ω / 4`,
written `iω / 4` when two-forms are read as imaginary forms. -/
theorem quadraticTwoForm_canonicalSpinor (hω : o.hodgeStar hkl JV.kahlerForm = JV.kahlerForm)
    (hrank : finrank ℂ (positiveHalfSpinors o ρ) = 2) (x : X) [FiniteDimensional ℝ (E x)]
    {Jx : AlmostComplexStructure (E x)} (hJx : ∀ v, Jx v = J x v) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).quadraticTwoForm o hQ b ρ hρ x
        (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x) =
      (‖u‖ ^ 2 / 4) • Jx.kahlerForm := by
  have p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x := Classical.arbitrary _
  rw [canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu p,
    SpinCStructure.quadraticTwoForm_mk,
    coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω hrank hρ hu,
    LinearIsometryEquiv.norm_map, _root_.map_smul,
    ← map_vectorFrame_canonicalSpinCStructureInl_kahlerForm hJ hJ₂ hJ₀ hF e h₀ h₂ b hJV p hJx,
    ← LinearMap.comp_apply,
    ← exteriorPower.map_comp]
  simp

end TauCeti.OrthonormalFrameBundle

/-! ### The fibrewise splitting `W⁺_x ≃ ℂ × K⁻¹_x` -/

namespace TauCeti.OrthonormalFrameBundle

open Orientation.HalfSpinModel SeibergWitten
open scoped InnerProductSpace

local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  {hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E)}
  {hJ₂ : ∀ x v, J x (J x v) = -v}
  {hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v}
  {hF : finrank ℝ F = 4} {e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4))}
  {h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1}
  {h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3}
  {Jc : Bundle.ContinuousComplexStructure F E} (hJc : ∀ x v, Jc x v = J x v)
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [Fact (finrank ℝ F = 2 * finrank ℂ G)]
  [FiniteDimensional ℂ G] [FiniteDimensional ℝ F]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)} {hQ : ∀ v, Q v = -‖v‖ ^ 2}
  {b : OrthonormalBasis (Fin 4) ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)}
  (hrank : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
  {ω : o.HalfSpinModel hQ b ρ hρ 1 [⋀^Fin 2]→ₗ[ℂ] ℂ} (hω : ω ≠ 0)
  {u : o.HalfSpinModel hQ b ρ hρ 1} (hu₀ : u ≠ 0)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance finiteDimensionalCanonicalSplittingModel : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

variable {JV : AlmostComplexStructure V}
  (hJV : ∀ w, JV (b.repr.symm w) =
    b.repr.symm ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) w))
  (hu : cliffordProjection o ρ JV.kahlerForm (toPositiveHalfSpinors o hQ b ρ hρ u) =
    toPositiveHalfSpinors o hQ b ρ hρ u)

variable (hJ hJ₂ hJ₀ hF e h₀ h₂) in
/-- **The fibrewise splitting `W⁺_x ≃ ℂ × K⁻¹_x` of the positive half-spinors** of the canonical
`Spinᶜ` structure of a rank-four bundle with an orthogonal complex structure `J`: the complex linear
isomorphism `W⁺_x ≃ ℂ × Λ²_ℂ (E x, J x)` sending `ψ` to `(⟪u₀(x), ψ⟫, ω(u₀(x), ψ))`, the
inner product with the canonical spinor `u₀` (`TauCeti.OrthonormalFrameBundle.canonicalSpinor`),
which is `‖u‖²` times the coefficient of `ψ` along `u₀(x)`, and the determinant pairing with
`u₀` read in the anticanonical line `K⁻¹ = Λ²_ℂ (E, J)` through
`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle`. It sends `u₀` to the
generator `(‖u‖², 0)` of the trivial summand
(`TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd_canonicalSpinor`), so a positive
spinor is `α u₀(x) + β` with `β` in the complement of `u₀(x)` identified with `K⁻¹_x`
(`TauCeti.OrthonormalFrameBundle.smul_canonicalSpinor_add_canonicalHalfSpinorEquivProd_symm_zero`).
When `u` lies on the canonical line, `u₀` does not depend on the unitary frame used to define it
and the components of the splitting are continuous on total spaces
(`TauCeti.OrthonormalFrameBundle.continuous_fst_canonicalHalfSpinorEquivProd`,
`TauCeti.OrthonormalFrameBundle.continuous_snd_canonicalHalfSpinorEquivProd`); for any other `u`
the section `u₀` is read in a chosen frame. Only these forward components are shown continuous; no
bundle isomorphism `W⁺ ≃ 1 ⊕ K⁻¹` is constructed. -/
def canonicalHalfSpinorEquivProd (x : X) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorBundle o hQ b ρ hρ 1 x ≃L[ℂ]
      ℂ × DetBundle ℂ G Jc.Fiber x :=
  ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorEquivProd hrank hω
      (canonicalSpinor_ne_zero hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hu₀ x)).trans
    ((ContinuousLinearEquiv.refl ℂ ℂ).prodCongr
      (canonicalDeterminantLineEquivDetBundle hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x))

/-- The fibrewise splitting `W⁺_x ≃ ℂ × K⁻¹_x` sends `ψ` to the inner product `⟪u₀(x), ψ⟫` and the
determinant pairing `ω(u₀(x), ψ)` read in `K⁻¹_x`. -/
@[simp]
theorem canonicalHalfSpinorEquivProd_apply {x : X}
    (ψ : (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorBundle o hQ b ρ hρ 1 x) :
    canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x ψ =
      (⟪canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x, ψ⟫_ℂ,
        canonicalDeterminantLineEquivDetBundle (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x
          ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorDetAlternatingMap hrank ω x
            ![canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x, ψ])) := by
  simp [canonicalHalfSpinorEquivProd]

/-- **The canonical spinor spans the trivial summand**: the fibrewise splitting
`W⁺_x ≃ ℂ × K⁻¹_x` sends `u₀(x)` to `(‖u‖², 0)`. -/
theorem canonicalHalfSpinorEquivProd_canonicalSpinor (x : X) :
    canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x
        (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x) = ((‖u‖ : ℂ) ^ 2, 0) := by
  rw [canonicalHalfSpinorEquivProd, ContinuousLinearEquiv.trans_apply,
    SpinCStructure.halfSpinorEquivProd_self, norm_canonicalSpinor]
  simp

/-- **The inverse of the fibrewise splitting on the trivial summand**: `W⁺_x ≃ ℂ × K⁻¹_x` sends
`(a / ‖u‖²) • u₀(x)` to `(a, 0)`. -/
@[simp]
theorem canonicalHalfSpinorEquivProd_symm_mk_zero (x : X) (a : ℂ) :
    (canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x).symm (a, 0) =
      (a / (‖u‖ : ℂ) ^ 2) • canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x := by
  simp [canonicalHalfSpinorEquivProd, norm_canonicalSpinor]

/-- **The decomposition `ψ = α u₀ + β`** of a positive spinor: `α = ⟪u₀(x), ψ⟫ / ‖u‖²` and `β` is
the vector of the complement of `u₀(x)` whose component in `K⁻¹_x` is `ω(u₀(x), ψ)`
(`TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd_apply`). -/
theorem smul_canonicalSpinor_add_canonicalHalfSpinorEquivProd_symm_zero {x : X}
    (ψ : (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorBundle o hQ b ρ hρ 1 x) :
    ((canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x ψ).1 /
          (‖u‖ : ℂ) ^ 2) • canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x +
        (canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x).symm
          (0, (canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x
            ψ).2) = ψ := by
  apply (canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x).injective
  rw [← canonicalHalfSpinorEquivProd_symm_mk_zero (G := G) hJc hrank hω hu₀ x,
    ContinuousLinearEquiv.map_add, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, Prod.mk_add_mk, add_zero, zero_add]

/-- **The inverse of the fibrewise splitting, trivial component**: the preimage of `z` under
`W⁺_x ≃ ℂ × K⁻¹_x` has inner product `z.1` with `u₀(x)`; in particular the complementary summand
`symm (0, l)` is orthogonal to `u₀(x)`. -/
@[simp]
theorem inner_canonicalSpinor_canonicalHalfSpinorEquivProd_symm (x : X)
    (z : ℂ × DetBundle ℂ G Jc.Fiber x) :
    ⟪canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x,
        (canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x).symm z⟫_ℂ =
      z.1 := by
  simpa using congrArg Prod.fst (canonicalHalfSpinorEquivProd_apply (G := G) hJc hrank hω hu₀
    ((canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x).symm z)).symm

/-- **The inverse of the fibrewise splitting, anticanonical component**: the determinant pairing of
`u₀(x)` with `(canonicalHalfSpinorEquivProd … x).symm z`, read in `K⁻¹_x`, is `z.2`. -/
@[simp]
theorem canonicalDeterminantLineEquivDetBundle_canonicalHalfSpinorEquivProd_symm (x : X)
    (z : ℂ × DetBundle ℂ G Jc.Fiber x) :
    canonicalDeterminantLineEquivDetBundle (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x
        ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorDetAlternatingMap hrank ω x
          ![canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x,
            (canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x).symm
              z]) = z.2 := by
  simpa using congrArg Prod.snd (canonicalHalfSpinorEquivProd_apply (G := G) hJc hrank hω hu₀
    ((canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x).symm z)).symm

include hJV hu in
/-- **The fibrewise splitting `W⁺_x ≃ ℂ × K⁻¹_x` in a unitary frame.** When the model spinor `u`
lies on the canonical line, the splitting sends the class `[[p, 1], φ]` of a model half-spinor `φ`
in a unitary frame `p` to `(⟪u, φ⟫, ω(u, φ) (p e₀ ∧ p e₂))`. -/
theorem canonicalHalfSpinorEquivProd_mk {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (φ : o.HalfSpinModel hQ b ρ hρ 1) :
    canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ x
        (AssociatedBundle.mk SpinC (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) φ) =
      (⟪u, φ⟫_ℂ, ω ![u, φ] • unitaryFrameWedge (G := G) h₀ h₂ hJc p) := by
  rw [canonicalHalfSpinorEquivProd_apply,
    canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu p, AssociatedBundle.inner_mk,
    SpinCStructure.halfSpinorDetAlternatingMap_mk_mk,
    canonicalDeterminantLineEquivDetBundle_mk_inl, LinearIsometryEquiv.apply_symm_apply]

include hJV hu in
/-- **The trivial component of the fibrewise splitting `W⁺_x ≃ ℂ × K⁻¹_x` is continuous** on the
total space of `W⁺`, when the model spinor lies on the canonical line. -/
theorem continuous_fst_canonicalHalfSpinorEquivProd :
    Continuous fun z : TotalSpace (o.HalfSpinModel hQ b ρ hρ 1)
        ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorBundle o hQ b ρ hρ 1) ↦
      (canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ z.proj
        z.snd).1 :=
  SpinCStructure.continuous_fst_halfSpinorEquivProd hω
    (canonicalSpinor_ne_zero hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hu₀)
    (continuous_canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu)

include hJV hu in
/-- **The anticanonical component of the fibrewise splitting `W⁺_x ≃ ℂ × K⁻¹_x` is continuous**
from the total space of `W⁺` to that of `K⁻¹ = Λ²_ℂ (E, J)`, when the model spinor lies on the
canonical line. -/
theorem continuous_snd_canonicalHalfSpinorEquivProd :
    Continuous fun z : TotalSpace (o.HalfSpinModel hQ b ρ hρ 1)
        ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorBundle o hQ b ρ hρ 1) ↦
      TotalSpace.mk' ℂ z.proj
        (canonicalHalfSpinorEquivProd (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc hrank hω hu₀ z.proj
          z.snd).2 :=
  (continuous_canonicalDeterminantLineEquivDetBundle (G := G) h₀ h₂ hJc).comp
    (SpinCStructure.continuous_snd_halfSpinorEquivProd hω
      (canonicalSpinor_ne_zero hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hu₀)
      (continuous_canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu))

end TauCeti.OrthonormalFrameBundle
