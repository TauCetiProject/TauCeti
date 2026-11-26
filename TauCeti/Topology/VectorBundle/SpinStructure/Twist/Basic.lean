/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Twist
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

/-!
# Twisting a `Spinᶜ` structure by a principal `U(1)`-bundle

Let `s` be a `Spinᶜ` structure of rank `n ≥ 1` on a real vector bundle `V` with fibre inner
products, with principal `Spinᶜ(n)`-bundle `P`, and let `L` be a principal `U(1)`-bundle over the
same base. The **twist** `s.twist L` (`TauCeti.SpinCStructure.twist`) is the `Spinᶜ` structure
with principal bundle

`P ⊗ L = (P ×_X L) ×_μ Spinᶜ(n)`,

the twist of lifts of the orthonormal frame bundle (`TauCeti.OrthonormalFrameLift.twist`) along
the multiplication by the central circle `μ : Spinᶜ(n) × U(1) → Spinᶜ(n)`, `([s, z], w) ↦ [s, z w]`
(`CliffordAlgebra.spinCGroup.mulCircle`): the extension of structure group of the fibre product
`P ×_X L` along `μ`. Since the central circle acts trivially on frames, the frame of `[(p, l), a]`
is the frame of `p` composed with the rotation of `a`
(`TauCeti.OrthonormalFrameLift.toFrame_twist_mk`). Equivalently, `P ⊗ L` is the quotient of
`P ×_X L` by the circle acting by `(p, l) • w = (p • [1, w], l • w⁻¹)`.

The general twist provides the rest of the API: twisting is functorial in `s` and in `L`
(`TauCeti.OrthonormalFrameLift.twistEquiv`), so the equivalence class of `s.twist L` depends only on
the equivalence class of `s` and the isomorphism class of `L`, and it commutes with pullback
(`TauCeti.OrthonormalFrameLift.twistPullbackEquiv`). Twisting by the trivial bundle changes nothing
(`TauCeti.SpinCStructure.twistTrivialEquiv`): `[(p, w), a] ↦ p • [1, w] a`.

This is the action of the isomorphism classes of complex line bundles on the equivalence classes
of `Spinᶜ` structures. Twisting preserves the orientation induced by `s`; on the classes of
`Spinᶜ` structures inducing a fixed orientation the action is free and transitive. The
isomorphism classes of complex line bundles are identified with Čech `H²(X; ℤ)` for paracompact
Hausdorff bases, and with singular `H²(X; ℤ)` for CW complexes. None of these statements is
proved here. Writing `E` for the Hermitian line associated to `L`, the determinant line of
`s.twist L` is that of `s` tensored with `E ⊗ E`, and each half-spinor bundle is that of `s`
tensored with `E` (`TauCeti.SpinCStructure.determinantLineTwistEquiv`,
`TauCeti.SpinCStructure.halfSpinorBundleTwistEquiv`, in
`TauCeti.Topology.VectorBundle.SpinStructure.Twist.Spinor`).

## Main definitions

* `TauCeti.SpinCStructure.twist`: the twist of a `Spinᶜ` structure by a principal `U(1)`-bundle.
* `TauCeti.SpinCStructure.twistTrivialEquiv`: the twist by the trivial bundle is equivalent to
  the `Spinᶜ` structure.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
* D. A. Salamon, *Spin Geometry and Seiberg–Witten Invariants*, 1999, §5.2.
-/

public section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

namespace SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} {V : X → Type}
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V] {n : ℕ} [NeZero n]
  (L : X → Type) [TopologicalSpace (TotalSpace Circle L)] [∀ x, TopologicalSpace (L x)]
  [FiberBundle Circle L] [∀ x, MulAction Circleᵐᵒᵖ (L x)] [PrincipalBundle Circle L]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- The **twist of a `Spinᶜ` structure by a principal `U(1)`-bundle** `L`: the `Spinᶜ`
structure with principal bundle `(P ×_X L) ×_μ Spinᶜ(n)`, the twist of lifts
(`TauCeti.OrthonormalFrameLift.twist`) along multiplication by the central circle
`μ : ([s, z], w) ↦ [s, z w]`. The frame of `[(p, l), a]` is the frame of `p` composed with the
rotation of `a` (`TauCeti.OrthonormalFrameLift.toFrame_twist_mk`). It is reducible, so that the
general API of `TauCeti.OrthonormalFrameLift.twist` applies to it. -/
noncomputable abbrev twist (s : SpinCStructure F V n) : SpinCStructure F V n :=
  OrthonormalFrameLift.twist s L (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
    (spinCGroup.subtype_comp_toSpecialOrthogonal_comp_mulCircle _ _)
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply

variable {L} (s : SpinCStructure F V n)

/-- **Twisting by the trivial bundle changes nothing**: the twist of a `Spinᶜ` structure `s` by
the trivial principal `U(1)`-bundle is equivalent to `s`, by `[(p, w), a] ↦ p • [1, w] a`
(`TauCeti.OrthonormalFrameLift.twistTrivialEquiv_toEquiv_mk`). -/
noncomputable abbrev twistTrivialEquiv : (s.twist (Bundle.Trivial X Circle)).Equiv s :=
  OrthonormalFrameLift.twistTrivialEquiv s (spinCGroup.mulCircle _ hQ)
    (spinCGroup.continuous_mulCircle _ _)
    (spinCGroup.subtype_comp_toSpecialOrthogonal_comp_mulCircle _ _)
    spinCGroup.norm_toLp_toSpecialOrthogonal_apply spinCGroup.continuous_toSpecialOrthogonal_apply
    (spinCGroup.mulCircle_comp_inl _ _)

end SpinCStructure

end TauCeti
