/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift

/-!
# Spinᶜ structures on real vector bundles with fibre inner products

Let `E → X` be a real vector bundle with model fibre `F` and fibre inner products, and let
`n ≥ 1`. The compact group `Spinᶜ(n)` (`CliffordAlgebra.realCliffordSpinCGroupZero n`) is the
quotient `(Spin(n) × U(1)) / {1, (-1, -1)}` of `CliffordAlgebra.spinCGroup`, for the positive
definite form of `ℝⁿ`, with its quotient topology. It maps to `SO(n)` by the rotation homomorphism
`[s, z] ↦ (v ↦ s v s⁻¹)` (`CliffordAlgebra.spinCGroup.toSpecialOrthogonal`) and to `U(1)` by the
determinant character `[s, z] ↦ z²` (`CliffordAlgebra.spinCGroup.det`).

A *Spinᶜ structure* of rank `n` on `E` (`TauCeti.SpinCStructure`) is a principal
`Spinᶜ(n)`-bundle `P → X` together with a continuous map `P → Fr(E)` to the orthonormal frame
bundle of `E` modelled on `ℝⁿ`, covering the identity of `X` and equivariant along the rotation
homomorphism: the frame of `p • g` sends `v` to the frame of `p` applied to the rotation of `g`
applied to `v`. It is the lift `TauCeti.OrthonormalFrameLift` of the orthonormal frame bundle
along the rotation homomorphism, as Spin structures (`TauCeti.SpinStructure`) are along the vector
action of `Spin(n)`, and it inherits the equivalences (`TauCeti.OrthonormalFrameLift.Equiv`) and
pullbacks (`TauCeti.OrthonormalFrameLift.pullback`) of lifts. The frame map is part of the data
and lands in the full orthonormal frame bundle, its image in each fibre being one `SO(n)`-orbit, so
a Spinᶜ structure chooses an orientation of `E`. The central circle `z ↦ [1, z]` acts trivially on
frames (`TauCeti.SpinCStructure.toFrame_smul_ofCircle`).

## Main definitions

* `TauCeti.SpinCStructure`: a Spinᶜ structure of rank `n ≥ 1` on a real vector bundle with fibre
  inner products.

## Main results

* `TauCeti.SpinCStructure.toFrame_smul_mk`: the class `[s, z]` moves frames by the vector action
  of `s`.
* `TauCeti.SpinCStructure.toFrame_smul_ofCircle`: the central circle acts trivially on frames.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

open Bundle MulOpposite CliffordAlgebra

universe w

namespace TauCeti

/-- A **Spinᶜ structure** of rank `n ≥ 1` on a real vector bundle `E` with model fibre `F` and
fibre inner products: a principal `Spinᶜ(n)`-bundle `P` over the base, where `Spinᶜ(n)` is the
compact group `realCliffordSpinCGroupZero n` with its quotient topology, together with a continuous
map to the orthonormal frame bundle of `E` over the identity, equivariant along the rotation
homomorphism `Spinᶜ(n) → SO(n)`, `[s, z] ↦ (v ↦ s v s⁻¹)`: the frame of `p • g` sends `v` to the
frame of `p` applied to the rotation of `g` applied to `v`. It is the lift of the orthonormal frame
bundle along the rotation homomorphism. Each fibre of `P` is a `Spinᶜ(n)`-torsor, so its image is
one `SO(n)`-orbit of frames, and the orientation of `E` is the one for which these frames are
positive. Positive rank is required: `spinCGroup` is defined for nonzero forms, and the native
`Spin(0)` is trivial. -/
abbrev SpinCStructure {X : Type*} [TopologicalSpace X] (F : Type*) (E : X → Type w)
    [TopologicalSpace (TotalSpace F E)]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] (n : ℕ) [NeZero n] :=
  OrthonormalFrameLift F E n (realCliffordSpinCGroupZero n)
    (spinCGroup.toSpecialOrthogonal _ _)

namespace SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ} [NeZero n]

/-- The class `[s, z]` moves frames by the vector action of `s`. -/
theorem toFrame_smul_mk (s : SpinCStructure F E n) (x : X) (p : s.P x)
    (q : realCliffordSpinGroupZero n × Circle) (v : Fin n → ℝ) :
    TotalSpace.mk' F
        (s.toFrame ⟨x, op (spinCGroup.mk _ _ q : realCliffordSpinCGroupZero n) • p⟩).proj
        ((s.toFrame ⟨x, op (spinCGroup.mk _ _ q : realCliffordSpinCGroupZero n) • p⟩).frame
          (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
        ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (spinVectorAction _ q.1 v))) := by
  rw [s.toFrame_smul, spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply]

/-- The central circle `z ↦ [1, z]` of `Spinᶜ(n)` acts trivially on frames. -/
@[simp]
theorem toFrame_smul_ofCircle (s : SpinCStructure F E n) (x : X) (p : s.P x) (z : Circle) :
    s.toFrame ⟨x, op (spinCGroup.ofCircle _ _ z : realCliffordSpinCGroupZero n) • p⟩ =
      s.toFrame ⟨x, p⟩ := by
  have h (v : Fin n → ℝ) :=
    s.toFrame_smul x p (spinCGroup.ofCircle _ _ z : realCliffordSpinCGroupZero n) v
  simp only [spinCGroup.toSpecialOrthogonal_ofCircle, OneMemClass.coe_one,
    FunLike.coe_one_eq_id, id_eq] at h
  have hproj : (s.toFrame ⟨x, p⟩).proj =
      (s.toFrame ⟨x, op (spinCGroup.ofCircle _ _ z : realCliffordSpinCGroupZero n) • p⟩).proj := by
    simp
  obtain ⟨g, hg⟩ := OrthonormalFrameBundle.exists_smul_eq_iff.2 hproj
  generalize s.toFrame ⟨x, op (spinCGroup.ofCircle _ _ z : realCliffordSpinCGroupZero n) • p⟩ =
    a at hg h ⊢
  subst hg
  suffices g = 1 by rw [this, op_one, one_smul]
  ext w : 2
  exact (s.toFrame ⟨x, p⟩).frame.injective (TotalSpace.mk_inj.1 (h (WithLp.ofLp w)))

end SpinCStructure

end TauCeti
