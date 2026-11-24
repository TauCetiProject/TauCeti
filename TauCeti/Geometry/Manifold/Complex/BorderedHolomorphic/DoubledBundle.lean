/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.DoubleAlong

/-!
# The doubled bundle over the Schottky double

Let `M` be a Riemann surface with boundary and `C` a complex point-indexed core over `M` whose
transitions are real at the boundary points (`TauCeti.FiniteRankBundleCore.IsRealAlong`). The real
coordinate subspaces over the boundary form a maximal totally real subbundle `F`, and the pair
`(C, F)` is a bundle pair in the sense of McDuff and Salamon.

`TauCeti.SchottkyDouble.doubledBundleCore C hC` is the doubled bundle `E_F` over the Schottky double
`TauCeti.SchottkyDouble M`: the core `C` on the first copy of `M` glued along the boundary to its
conjugate on the second copy, through the antilinear involution of `C` over the boundary with
fixed set `F`. It is `TauCeti.FiniteRankBundleCore.doubleAlong` along the boundary
(`doubledBundleCore_eq`), and `TauCeti.SchottkyDouble M` is a reducible abbreviation of the double
along the boundary, so after rewriting with `doubledBundleCore_eq` the general API applies:

* `TauCeti.FiniteRankBundleCore.doubleAlongInlIso` and
  `TauCeti.FiniteRankBundleCore.doubleAlongInrIso`: the doubled bundle is `C` on the first copy and
  its conjugate on the second copy.
* `TauCeti.FiniteRankBundleCore.doubleAlongSwap`: the lift of the antiholomorphic involution
  `TauCeti.DoubleAlong.swap` of the Schottky double to a conjugate-linear involution of the
  doubled bundle (`proj_doubleAlongSwap`, `doubleAlongSwap_doubleAlongSwap`).
* `TauCeti.FiniteRankBundleCore.doubleAlongSwap_mk_inl_eq_self_iff`: over a boundary point the
  fixed vectors of the lift are exactly the vectors of `F`.

Only the topological doubled bundle is constructed. Its smooth structure through collars, and
independence of the choices up to isomorphism, are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.3.
-/

public section

namespace TauCeti.SchottkyDouble

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]

/-- The doubled bundle `E_F` over the Schottky double of a Riemann surface with boundary `M`, for a
complex core `C` over `M` whose transitions are real at the boundary: `C` on the first copy of `M`
and its conjugate on the second copy, glued along the boundary. -/
noncomputable def doubledBundleCore (C : FiniteRankBundleCore ℂ M)
    (hC : C.IsRealAlong (borderedInterior M : Set M)ᶜ) :
    FiniteRankBundleCore ℂ (SchottkyDouble M) :=
  C.doubleAlong hC

theorem doubledBundleCore_eq (C : FiniteRankBundleCore ℂ M)
    (hC : C.IsRealAlong (borderedInterior M : Set M)ᶜ) :
    doubledBundleCore C hC = C.doubleAlong hC := (rfl)

@[simp] theorem rank_doubledBundleCore (C : FiniteRankBundleCore ℂ M)
    (hC : C.IsRealAlong (borderedInterior M : Set M)ᶜ) :
    (doubledBundleCore C hC).rank = C.rank := (rfl)

end TauCeti.SchottkyDouble
