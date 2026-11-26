/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
import TauCeti.GroupTheory.GroupAlgGeom.FreeDiscrimination
import TauCeti.GroupTheory.GroupAlgGeom.FreeProduct

/-!
# Free products with a fully residually free group

Let `H` be a nonabelian CSA group with the big powers property, for instance a nonabelian fully
residually free group, and let `K` be a fully residually free group. Then the free product `H ∗ K`
is discriminated by `H` over `H`: finitely many nonidentity elements of `H ∗ K` survive under one
retraction `H ∗ K →* H` of the inclusion of `H`.

Since `K` is discriminated by the free group `F₂`, the free product `H ∗ K` is discriminated by
`H ∗ F₂ = H[Fin 2]` over `H` (`TauCeti.GroupAlgGeom.IsDiscriminatedBy.coprod_inl`), and the free
`H`-group `H[Fin 2]` is discriminated by `H` over `H` (`TauCeti.GroupAlgGeom.GX.isDiscriminatedBy`).

## Main results

* `TauCeti.LimitGroup.isDiscriminatedBy_inl_coprod`: for a nonabelian CSA group `H` with the big
  powers property and a fully residually free group `K`, the free product `H ∗ K` is
  discriminated by `H` over `H`.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.coprod`: the free product of a nonabelian fully
  residually free group and a fully residually free group is fully residually free.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group II: Systems in
  triangular quasi-quadratic form and description of residually free groups*, J. Algebra 200
  (1998), proof of Theorem 4 (where this discrimination is used, for `H` free).
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5 (`H[X]` is discriminated by `H` over `H`).
-/

public section

open Group Monoid.Coprod TauCeti.GroupAlgGeom

namespace TauCeti.LimitGroup

/-- **Free products are discriminated by a nonabelian CSA factor with big powers.** For a
nonabelian CSA group `H` with the big powers property and a fully residually free group `K`, the
free product `H ∗ K` is discriminated by `H` over `H`: finitely many nonidentity elements of
`H ∗ K` survive under one retraction `H ∗ K →* H` of the inclusion of `H`. -/
theorem isDiscriminatedBy_inl_coprod {H K : Type*} [Group H] [Group K] (hBP : IsBP H)
    (hCSA : IsCSA H) (hH : ¬IsMulCommutative H) (hK : IsFullyResiduallyFree K) :
    IsDiscriminatedBy (inl : H →* H ∗ K) (MonoidHom.id H) :=
  ((isFullyResiduallyFree_iff_isDiscriminatedBy.1 hK).coprod_inl H).trans
    (GX.isDiscriminatedBy hBP hCSA hH)

/-- **Free products of fully residually free groups.** The free product `H ∗ K` of a nonabelian
fully residually free group `H` and a fully residually free group `K` is fully residually free,
being discriminated by `H`. -/
theorem IsFullyResiduallyFree.coprod {H K : Type*} [Group H] [Group K]
    (hH : IsFullyResiduallyFree H) (hHc : ¬IsMulCommutative H) (hK : IsFullyResiduallyFree K) :
    IsFullyResiduallyFree (H ∗ K) :=
  hH.of_isDiscriminatedBy (isDiscriminatedBy_inl_coprod hH.isBP hH.isCSA hHc hK)

end TauCeti.LimitGroup
