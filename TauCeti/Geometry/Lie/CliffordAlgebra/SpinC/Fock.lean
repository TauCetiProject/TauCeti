/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.HalfSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.HalfSpinor
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Intertwiner
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Frame

/-!
# Frame equivariance and the four-dimensional Hermitian Fock realization of Spinᶜ(4)

`Orientation.realSpinCHalfSpinSmoothHom` descends the weight-one half-spin representation of
compact `Spinᶜ(4)` smoothly to the `ε`-chirality eigenspace `W^ε` of any Clifford module `(W, ρ)`
in an orthonormal frame `b`. This file establishes how that smooth action varies with the frame and
Clifford module, and realizes it concretely on the diamond-free Fock carrier
`TauCeti.AlmostComplexStructure.FockSpinors`:

* `Orientation.exists_realSpinCHalfSpinSmoothHom_eq_conj`: changing between equally oriented
  orthonormal frames `b` and `b'` conjugates `realSpinCHalfSpinSmoothHom` by the image of a
  compact Spin element in `Spinᶜ(4)`.
* `Orientation.halfSpinLinearIsometryEquiv_realSpinCHalfSpinSmoothHom_apply` and
  `Orientation.realSpinCHalfSpinSmoothHom_intertwine_apply`: equivariance of
  `realSpinCHalfSpinSmoothHom` along an oriented linear isometry and unitary Clifford intertwiner.
* `Orientation.exists_unitary_intertwiner_fock_realSpinCHalfSpinSmoothHom` and
  `Orientation.det_fock_realSpinCHalfSpinSmoothHom`: for every `Q`-orthogonal complex structure `J`
  on `(V, o)`, the chirality eigenspaces (`ε = ±1`) of `J.FockSpinors` carry smooth isometric
  `Spinᶜ(4)` representations intertwined unitarily across polarizations, with determinant equal to
  `spinCGroup.det`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Module Module.End TauCeti TauCeti.CliffordAlgebra
open scoped InnerProductSpace

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "hQ₀" => b.ne_zero_of_neg_norm_sq hQ
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-! ### Frame conjugation and unitary intertwiner equivariance -/

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-- Changing between two equally oriented orthonormal frames `b` and `b'` conjugates
`realSpinCHalfSpinSmoothHom` by the image of a compact Spin element in `Spinᶜ(4)`. -/
theorem exists_realSpinCHalfSpinSmoothHom_eq_conj {b' : OrthonormalBasis (Fin 4) ℝ V}
    (hb : b.toBasis.orientation = b'.toBasis.orientation) :
    ∃ s₀ : spinGroup (realCliffordForm 4 0),
      ∀ (x : SpinC) (ψ : eigenspace (ρ (chirality Q o)) ε),
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

end Normed

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

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
    (x : SpinC) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    halfSpinLinearIsometryEquiv o' ho hU ε (realSpinCHalfSpinSmoothHom o hQ b ρ ε x ψ) =
      realSpinCHalfSpinSmoothHom o' hQ' (b.map f) ρ' ε x
        (halfSpinLinearIsometryEquiv o' ho hU ε ψ) := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    realSpinCHalfSpinSmoothHom_apply o' hQ' (b.map f) ρ' ε ((b.map f).ne_zero_of_neg_norm_sq hQ'),
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective (realCliffordForm 4 0) hpos x
  let e : Q →qᵢ Q' :=
    { toLinearMap := f.toLinearMap
      map_app' v := by simp [hQ', hQ] }
  have he (v : V) : e v = f v := by simp [← QuadraticMap.Isometry.coe_toLinearMap, e]
  have he_comp : ((b.map f).negRealCliffordFormIsometryEquiv hQ').toIsometry =
      e.comp (b.negRealCliffordFormIsometryEquiv hQ).toIsometry := by
    ext c
    simp [QuadraticMap.Isometry.comp_apply, OrthonormalBasis.negRealCliffordFormIsometryEquiv_apply,
      map_sum, map_smul, OrthonormalBasis.map_apply, he]
  have heven : (⟨CliffordAlgebra.map e
      (b.realEvenCliffordEquiv hQ (spinGroupToEven _ s)),
      map_mem_even e (b.realEvenCliffordEquiv hQ (spinGroupToEven _ s)).property⟩ : even Q') =
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
    (x : SpinC) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    halfSpinLinearIsometryEquiv o (f := .refl ℝ V) (by simp) hU ε
        (realSpinCHalfSpinSmoothHom o hQ b ρ ε x ψ) =
      realSpinCHalfSpinSmoothHom o hQ b ρ' ε x
        (halfSpinLinearIsometryEquiv o (f := .refl ℝ V) (by simp) hU ε ψ) := by
  have hb_refl : b.map (.refl ℝ V) = b := DFunLike.ext _ _ fun _ ↦ by simp
  simpa [hb_refl] using
    halfSpinLinearIsometryEquiv_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε o hQ
      (f := .refl ℝ V) (by simp) hU x ψ

end Hermitian

/-! ### Concrete four-dimensional Hermitian Fock `Spinᶜ(4)` realization -/

section Fock

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

/-- For any `Q`-orthogonal complex structure `J` on `(V, o)`, both chirality representations
(`ε = 1` and `ε = -1`) of `realSpinCHalfSpinSmoothHom` on `J.FockSpinors` have determinant equal to
the weight-two character `spinCGroup.det`. -/
theorem det_fock_realSpinCHalfSpinSmoothHom
    (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)
    {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (x : SpinC) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    LinearMap.det
        (realSpinCHalfSpinSmoothHom o hQ b (J.fockSpinorAction hQJ hQnd) ε x).toLinearMap =
      (spinCGroup.det (realCliffordForm 4 0) hpos x : ℂ) := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  exact det_realSpinCHalfSpinSmoothHom o hQ b (J.fockSpinorAction hQJ hQnd) ε
    (finrank_eigenspace_fockSpinorAction_chirality o hQ J hQJ hQnd hε) x

end Fock

end Orientation

end
