/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.HalfSpin
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Intertwiner
import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Chirality

/-!
# The four-dimensional Hermitian Fock realization of Spinᶜ(4)

`Orientation.realSpinCHalfSpinSmoothHom` descends the weight-one half-spin representation of
compact `Spinᶜ(4)` smoothly to the `ε`-chirality eigenspace `W^ε` of any Clifford module `(W, ρ)`
in an orthonormal frame `b`. This file realizes that smooth action concretely on the diamond-free
Fock carrier `TauCeti.AlmostComplexStructure.FockSpinors`:

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
open scoped TauCeti.FactFinrank

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

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

end Orientation

end
