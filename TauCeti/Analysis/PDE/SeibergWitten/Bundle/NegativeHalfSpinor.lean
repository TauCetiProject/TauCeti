/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Bundle.CanonicalSpinor
public import TauCeti.Analysis.PDE.SeibergWitten.Canonical.Line
public import TauCeti.Topology.VectorBundle.Complex.Structure

/-!
# The negative half-spinors of the canonical `Spinᶜ` structure

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, such as the tangent bundle of an almost Hermitian four-manifold,
and let `𝔰` be its canonical `Spinᶜ` structure
(`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`), with canonical spinor `u₀`
(`TauCeti.OrthonormalFrameBundle.canonicalSpinor`), a section of the positive half-spinor bundle
`W⁺` on the `-2i`-eigenline of `c₂(ω)`. This file identifies the negative half-spinor bundle
`W⁻ = 𝔰.halfSpinorBundle o hQ b ρ hρ (-1)` with `E`, regarded as a complex vector bundle through
`J`, by Clifford multiplication on `u₀`:

`(E, J) ≃ W⁻`,  `v ↦ c(v) u₀`.

This is the Clifford intertwiner of the identification `W⁻ = Λ^(0,1)` of the canonical `Spinᶜ`
structure of an almost Hermitian four-manifold, `(E, J)` being isomorphic to its `(0,1)`-covectors
through the metric; that last isomorphism is not constructed here. In Taubes's analysis of the
Seiberg–Witten equations on a symplectic four-manifold it is the identification through which the
Dirac operator on `α u₀ + β` is read as `√2 ∂bar_a α` plus a term in `β`.

**Complex linearity.** A unitary frame `p` carries `J` to the model complex structure `JV`
(`TauCeti.OrthonormalFrameBundle.vectorFrame_canonicalSpinCStructureInl_apply_apply`), and on the
canonical line of the model, Clifford multiplication turns `JV` into `i`
(`TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self`). Hence
`c(J v) u₀ = i c(v) u₀` on every fibre
(`TauCeti.OrthonormalFrameBundle.cliffordMul_apply_apply_canonicalSpinor`), so `v ↦ c(v) u₀` is
complex linear for the complex structure `J` of `E`. It is moreover Hermitian up to the factor
`‖u‖²`: `⟪c(v) u₀, c(w) u₀⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖u‖²`
(`TauCeti.OrthonormalFrameBundle.inner_cliffordMul_canonicalSpinor`).

**The isomorphism.** When the model positive half-spinors have complex dimension two and `u ≠ 0`,
Clifford multiplication by the model spinor `u` is a real isomorphism from the model four-space
onto the model negative half-spinors (`CliffordAlgebra.cliffordMulEquiv`). Read in a unitary
frame, `v ↦ c(v) u₀` is therefore bijective on every fibre, and it is a complex linear isomorphism
`(E x, J x) ≃ W⁻_x` (`TauCeti.OrthonormalFrameBundle.canonicalNegativeHalfSpinorEquiv`). In a
local unitary frame its coordinates are those of `v` in the frame, so it is continuous on total
spaces (`TauCeti.OrthonormalFrameBundle.continuous_cliffordMul_canonicalSpinor`,
`TauCeti.OrthonormalFrameBundle.continuous_canonicalNegativeHalfSpinorEquiv`).

## Main definitions

* `TauCeti.OrthonormalFrameBundle.canonicalNegativeHalfSpinorEquiv`: the complex linear
  isomorphism `(E x, J x) ≃ W⁻_x`, `v ↦ c(v) u₀(x)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.vectorFrame_canonicalSpinCStructureInl_apply_apply`: the vector
  frame of `[p, 1]` carries `J` to the model complex structure.
* `TauCeti.OrthonormalFrameBundle.cliffordMul_apply_apply_canonicalSpinor`:
  `c(J v) u₀ = i c(v) u₀`.
* `TauCeti.OrthonormalFrameBundle.inner_cliffordMul_canonicalSpinor`:
  `⟪c(v) u₀, c(w) u₀⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖u‖²`.
* `TauCeti.OrthonormalFrameBundle.continuous_cliffordMul_canonicalSpinor`,
  `TauCeti.OrthonormalFrameBundle.continuous_canonicalNegativeHalfSpinorEquiv`: continuity on total
  spaces.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Appendix D.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants and the Van de Ven conjecture*, 1995, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, §1(c)–(d).
-/

public section

noncomputable section

open Bundle MulOpposite Module Module.End TauCeti CliffordAlgebra TauCeti.CliffordAlgebra
open scoped InnerProductSpace RealInnerProductSpace

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)

namespace TauCeti.OrthonormalFrameBundle

open Orientation.HalfSpinModel SeibergWitten

local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
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
local instance finiteDimensionalNegativeHalfSpinorModel : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

variable {JV : AlmostComplexStructure V}
  (hJV : ∀ w, JV (b.repr.symm w) =
    b.repr.symm ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) w))
  {u : o.HalfSpinModel hQ b ρ hρ 1}
  (hu : cliffordProjection o ρ JV.kahlerForm (toPositiveHalfSpinors o hQ b ρ hρ u) =
    toPositiveHalfSpinors o hQ b ρ hρ u)

omit [Fact (finrank ℝ V = 4)] in
include hJV in
/-- The model complex structure `JV` is orthogonal, since it corresponds under `b` to the unitary
`J₀`. -/
private theorem inner_apply_apply_of_repr_symm (v w : V) : ⟪JV v, JV w⟫ = ⟪v, w⟫ := by
  rw [← b.repr.symm_apply_apply v, ← b.repr.symm_apply_apply w, hJV, hJV,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map, Unitary.inner_map_map]

omit [Fact (finrank ℝ V = 4)] in
include hJV in
/-- **The vector frame of `[p, 1]` carries `J` to the model complex structure**: for a unitary
frame `p` over `x`, `κ_p (J v) = JV (κ_p v)`. -/
theorem vectorFrame_canonicalSpinCStructureInl_apply_apply {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (v : E x) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).vectorFrame b
        (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) (J x v) =
      JV ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).vectorFrame b
        (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) v) := by
  rw [SpinCStructure.vectorFrame_apply_eq_repr_symm, SpinCStructure.vectorFrame_apply_eq_repr_symm,
    frameAt_canonicalSpinCStructureInl, hJV]
  congr 1
  have hp := mem_unitaryFrames_iff.1 p.property (p.val.frame.symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at hp
  rw [← hp, LinearIsometryEquiv.symm_apply_apply]

include hJV hu in
/-- On the canonical line of the model, Clifford multiplication turns `JV` into `i`. -/
private theorem cliffordMul_apply_of_cliffordProjection (w : V) :
    Orientation.HalfSpinModel.cliffordMul (ε' := -1) rfl (JV w) u =
      Complex.I • Orientation.HalfSpinModel.cliffordMul (ε' := -1) rfl w u := by
  apply toEigenspace.injective
  apply Subtype.ext
  have h := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ
    (inner_apply_apply_of_repr_symm b hJV) hu w
  simp only [coe_toPositiveHalfSpinors] at h
  rw [coe_toEigenspace_cliffordMul, h, _root_.map_smul, Submodule.coe_smul,
    coe_toEigenspace_cliffordMul]

include hJV hu in
/-- **Clifford multiplication turns `J` into `i` on the canonical spinor**: `c(J v) u₀ = i c(v) u₀`
on every fibre. Equivalently, `v ↦ c(v) u₀` is complex linear from `(E x, J x)` to `W⁻_x`. -/
theorem cliffordMul_apply_apply_canonicalSpinor {x : X} (v : E x) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordMul o hQ b ρ hρ (ε' := -1) rfl x
        (J x v) (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x) =
      Complex.I • (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordMul o hQ b ρ hρ
        (ε' := -1) rfl x v (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x) := by
  have p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x := Classical.arbitrary _
  rw [canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu p,
    SpinCStructure.cliffordMul_mk, SpinCStructure.cliffordMul_mk,
    vectorFrame_canonicalSpinCStructureInl_apply_apply hJ hJ₂ hJ₀ hF e h₀ h₂ b hJV p,
    cliffordMul_apply_of_cliffordProjection o hQ b ρ hρ hJV hu, AssociatedBundle.mk_smul_scalar]

include hJV hu in
/-- **`v ↦ c(v) u₀` is Hermitian up to the factor `‖u‖²`**:
`⟪c(v) u₀, c(w) u₀⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖u‖²`. Its real part is `⟪v, w⟫ ‖u‖²`, and the
Hermitian form `⟪v, w⟫ - i ⟪v, J w⟫` is the one of `(E x, J x)` for which `J` is
multiplication by `i`. -/
theorem inner_cliffordMul_canonicalSpinor {x : X} (v w : E x) :
    ⟪(canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordMul o hQ b ρ hρ (ε' := -1) rfl x v
        (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x),
      (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordMul o hQ b ρ hρ (ε' := -1) rfl x w
        (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x)⟫_ℂ =
      ((⟪v, w⟫ : ℂ) - ⟪v, J x w⟫ * Complex.I) * ‖u‖ ^ 2 := by
  have p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x := Classical.arbitrary _
  set κ := (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).vectorFrame b
    (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
  rw [canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu p,
    SpinCStructure.cliffordMul_mk, SpinCStructure.cliffordMul_mk, AssociatedBundle.inner_mk,
    ← LinearIsometryEquiv.inner_map_map toEigenspace, Submodule.coe_inner,
    coe_toEigenspace_cliffordMul, coe_toEigenspace_cliffordMul, ← coe_toPositiveHalfSpinors,
    inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ
      (inner_apply_apply_of_repr_symm b hJV) hρ hu, coe_toPositiveHalfSpinors,
    Submodule.norm_coe, LinearIsometryEquiv.norm_map,
    ← vectorFrame_canonicalSpinCStructureInl_apply_apply hJ hJ₂ hJ₀ hF e h₀ h₂ b hJV p,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

include hJV hu in
/-- **Clifford multiplication on the canonical spinor is continuous** on total spaces: the map
`v ↦ c(v) u₀` from the total space of `E` to that of `W⁻`. -/
theorem continuous_cliffordMul_canonicalSpinor :
    Continuous fun v : TotalSpace F E ↦
      TotalSpace.mk' (o.HalfSpinModel hQ b ρ hρ (-1)) v.proj
        ((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordMul o hQ b ρ hρ (ε' := -1) rfl
          v.proj v.snd (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u v.proj)) := by
  refine continuous_iff_continuousAt.2 fun v₀ ↦ ?_
  -- `Trivialization.symm` takes a `Zero` instance on the fibres for its value off the base set; the
  -- unitary frames have none, and the value off `t.baseSet` is never used below.
  let : ∀ y, Zero ((unitaryFrameLift hJ hJ₂ hJ₀ hF).P y) := fun _ ↦ ⟨Classical.arbitrary _⟩
  set t := trivializationAt (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P v₀.proj
  set s : Set (TotalSpace F E) := TotalSpace.proj ⁻¹' t.baseSet
  have hs : s ∈ nhds v₀ := (FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
    (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ v₀.proj))
  -- The local unitary frame `σ y = t.symm y 1`, read at the base point of `v`.
  have hσ : ContinuousOn (fun v : TotalSpace F E ↦
      TotalSpace.mk' (Subgroup.centralizer {J₀}) v.proj (t.symm v.proj 1)) s :=
    (t.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
      fun _ hy ↦ ⟨hy, Set.mem_univ _⟩).comp (FiberBundle.continuous_proj F E).continuousOn
      fun _ hv ↦ hv
  have hinl : ContinuousOn (fun v : TotalSpace F E ↦ TotalSpace.mk' SpinC v.proj
      (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ (t.symm v.proj 1))) s :=
    (continuous_canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂).comp_continuousOn hσ
  -- The coordinates `(σ y)⁻¹ v` of `v` in the local frame are inner products with the frame.
  have hframe :
      ContinuousOn (fun v : TotalSpace F E ↦ (t.symm v.proj 1).val.frame.symm v.snd) s := by
    have h (i : Fin 4) : ContinuousOn (fun v : TotalSpace F E ↦
        ⟪(t.symm v.proj 1).val.frame (e i), v.snd⟫ • e i) s := by
      have hfr : Continuous fun p : TotalSpace (Subgroup.centralizer {J₀})
          (unitaryFrameLift hJ hJ₂ hJ₀ hF).P ↦ TotalSpace.mk' F p.proj (p.snd.val.frame (e i)) :=
        continuous_totalSpaceMk_frame_apply.comp
          ((unitaryFrameLift hJ hJ₂ hJ₀ hF).continuous_toFrame.prodMk continuous_const)
      exact ((hfr.comp_continuousOn hσ).inner_bundle_of_continuousFiberNorm (𝕜 := ℝ)
        (continuous_id (X := TotalSpace F E)).continuousOn).smul continuousOn_const
    refine (continuousOn_finsetSum Finset.univ fun i _ ↦ h i).congr fun v _ ↦ ?_
    rw [← e.sum_repr' ((t.symm v.proj 1).val.frame.symm v.snd)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← LinearIsometryEquiv.inner_map_map (t.symm v.proj 1).val.frame,
      LinearIsometryEquiv.apply_symm_apply]
  -- Model Clifford multiplication on `u` is a linear map out of the finite-dimensional `V`.
  let L : V →ₗ[ℝ] o.HalfSpinModel hQ b ρ hρ (-1) :=
    { toFun w := Orientation.HalfSpinModel.cliffordMul (ε' := -1) rfl w u
      map_add' w w' := by simp
      map_smul' r w := by simp }
  have hmodel : ContinuousOn (fun v : TotalSpace F E ↦ L (b.repr.symm
      ((t.symm v.proj 1).val.frame.symm v.snd))) s :=
    L.continuous_of_finiteDimensional.comp_continuousOn
      (b.repr.symm.continuous.comp_continuousOn hframe)
  refine ((hinl.totalSpaceMk_associatedBundleMk hmodel).congr fun v _ ↦ ?_).continuousAt hs
  rw [canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu (t.symm v.proj 1),
    SpinCStructure.cliffordMul_mk, SpinCStructure.vectorFrame_apply_eq_repr_symm,
    frameAt_canonicalSpinCStructureInl]
  -- `L w` is `c(w) u` by definition.
  rfl

variable {Jc : Bundle.ContinuousComplexStructure F E} (hJc : ∀ x v, Jc x v = J x v)

include hJV hu hJc in
/-- Clifford multiplication on the canonical spinor, as a complex linear map from `E x` with the
complex structure `J x`: `v ↦ c(v) u₀`. -/
private def cliffordMulCanonicalSpinorLinearMap (x : X) :
    Jc.Fiber x →ₗ[ℂ] (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorBundle o hQ b ρ hρ
      (-1) x where
  toFun v := (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordMul o hQ b ρ hρ
    (ε' := -1) rfl x (Jc.fiberEquiv x v) (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x)
  map_add' v w := by simp
  map_smul' z v := by
    rw [Bundle.ContinuousComplexStructure.fiberEquiv_smul, map_add, _root_.map_smul,
      _root_.map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hJc,
      cliffordMul_apply_apply_canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu,
      RingHom.id_apply]
    conv_rhs => rw [← Complex.re_add_im z]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    -- The two sides differ only in how the real scalar action on `W⁻_x` is presented: restricted
    -- from `ℂ` on the left, through `Complex.coe_smul` on the right.
    rfl

include hJV hu hJc in
private theorem cliffordMulCanonicalSpinorLinearMap_apply {x : X} (v : Jc.Fiber x) :
    cliffordMulCanonicalSpinorLinearMap hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hJc x v =
      (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordMul o hQ b ρ hρ (ε' := -1) rfl x
        (Jc.fiberEquiv x v) (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x) :=
  (rfl)

include hJV hu hJc in
/-- Clifford multiplication on the canonical spinor is bijective from `E x` onto `W⁻_x`, when the
model positive half-spinors have complex dimension two and `u ≠ 0`. -/
private theorem bijective_cliffordMulCanonicalSpinorLinearMap
    (hrank : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hu₀ : u ≠ 0) (x : X) :
    Function.Bijective
      (cliffordMulCanonicalSpinorLinearMap hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hJc x) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun v hv ↦ ?_, fun φ ↦ ?_⟩
  · -- `‖c(v) u₀‖ = ‖v‖ ‖u‖`, and `u ≠ 0`.
    have h := congrArg norm hv
    rw [norm_zero, cliffordMulCanonicalSpinorLinearMap_apply, SpinCStructure.norm_cliffordMul,
      norm_canonicalSpinor, mul_eq_zero, norm_eq_zero, norm_eq_zero] at h
    exact (Jc.fiberEquiv x).injective ((h.resolve_right hu₀).trans (map_zero _).symm)
  · -- In a unitary frame `p`, Clifford multiplication by the model spinor `u` is onto the model
    -- negative half-spinors.
    have p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x := Classical.arbitrary _
    set q := canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p
    obtain ⟨φ, rfl⟩ := (AssociatedBundle.mk_bijective (G := SpinC)
      (F := o.HalfSpinModel hQ b ρ hρ (-1)) q).2 φ
    have hψ₀ : (toEigenspace u : W) ≠ 0 := fun h ↦
      hu₀ (toEigenspace.map_eq_zero_iff.1 (Subtype.ext h))
    have h₂' : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2 := by
      rwa [← positiveHalfSpinors_eq_eigenspace]
    set f := cliffordMulEquiv o hQ (toEigenspace u).property hψ₀ h₂'
    refine ⟨(Jc.fiberEquiv x).symm
      (((canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).vectorFrame b q).symm
        (f.symm (toEigenspace φ))), ?_⟩
    rw [cliffordMulCanonicalSpinorLinearMap_apply, ContinuousLinearEquiv.apply_symm_apply,
      canonicalSpinor_eq_mk hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu p,
      SpinCStructure.cliffordMul_mk, LinearIsometryEquiv.apply_symm_apply]
    congr 1
    apply toEigenspace.injective
    apply Subtype.ext
    rw [coe_toEigenspace_cliffordMul, ← coe_cliffordMulEquiv_apply o hQ (toEigenspace u).property
      hψ₀ h₂', LinearEquiv.apply_symm_apply]

/-- **The negative half-spinors of the canonical `Spinᶜ` structure are `(E, J)`**: Clifford
multiplication on the canonical spinor, `v ↦ c(v) u₀(x)`, is a complex linear isomorphism from `E x`
with the complex structure `J x` onto `W⁻_x`, when the model positive half-spinors have complex
dimension two and the model spinor `u` is nonzero. It is Hermitian up to the factor `‖u‖²`
(`TauCeti.OrthonormalFrameBundle.inner_cliffordMul_canonicalSpinor`), and it is continuous on
total spaces
(`TauCeti.OrthonormalFrameBundle.continuous_canonicalNegativeHalfSpinorEquiv`). -/
def canonicalNegativeHalfSpinorEquiv (hrank : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hu₀ : u ≠ 0) (x : X) :
    Jc.Fiber x ≃ₗ[ℂ] (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).halfSpinorBundle o hQ b ρ hρ
      (-1) x :=
  LinearEquiv.ofBijective _
    (bijective_cliffordMulCanonicalSpinorLinearMap hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hJc
      hrank hu₀ x)

/-- The isomorphism `(E x, J x) ≃ W⁻_x` is Clifford multiplication on the canonical spinor:
`v ↦ c(v) u₀(x)`. -/
@[simp]
theorem canonicalNegativeHalfSpinorEquiv_apply (hrank : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hu₀ : u ≠ 0) {x : X} (v : Jc.Fiber x) :
    canonicalNegativeHalfSpinorEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hJc hrank hu₀ x v =
      (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).cliffordMul o hQ b ρ hρ (ε' := -1) rfl x
        (Jc.fiberEquiv x v) (canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ u x) :=
  (rfl)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)] [FiniteDimensional ℝ F]

/-- **The isomorphism `(E, J) ≃ W⁻` is continuous** on total spaces. -/
theorem continuous_canonicalNegativeHalfSpinorEquiv
    (hrank : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hu₀ : u ≠ 0) :
    Continuous fun v : TotalSpace G Jc.Fiber ↦
      TotalSpace.mk' (o.HalfSpinModel hQ b ρ hρ (-1)) v.proj
        (canonicalNegativeHalfSpinorEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu hJc hrank hu₀
          v.proj v.snd) :=
  ((continuous_cliffordMul_canonicalSpinor hJ hJ₂ hJ₀ hF e h₀ h₂ o hQ b ρ hρ hJV hu).comp
    (Jc.totalSpaceHomeomorph G).continuous).congr fun _ ↦ by
      rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply,
        canonicalNegativeHalfSpinorEquiv_apply]

end TauCeti.OrthonormalFrameBundle
