/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Borel.Reduction
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

/-!
# Reducing Borel conjugacy to smooth connected affine groups

A closed subgroup containing every Borel candidate transfers a Borel-conjugacy theorem to
the ambient group. The conjugating point is mapped along the closed immersion; no lifting
of rational points along a quotient of groups is involved.

Over an algebraically closed field, every Borel candidate lies in the identity component
of the reduction. This subgroup is smooth and geometrically connected even when the ambient
group is neither reduced nor connected. Consequently, to prove conjugacy of Borel subgroups
of all finite-type affine groups, it suffices to prove it for smooth connected groups.
The smooth connected conjugacy theorem is a hypothesis here, not a conclusion.

The construction uses `HopfIdeal.identityComponent_le_of_le` and
`HopfIdeal.reduction_le_of_isReduced_quotient`; transfer uses
`HopfIdeal.exists_conjugate_eq_comapOfSurjective`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.1.
* J. S. Milne, *Algebraic Groups* (2017), §17.a.
-/

public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Two ambient Borel subgroups contained in a closed subgroup are conjugate in the ambient
group whenever Borel subgroups of that closed subgroup are conjugate. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed_of_quotient
    (P : HopfIdeal k H)
    (hconj : ∀ I J : HopfIdeal k (FiniteTypeCommHopfAlgCat.quotient H P),
      IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.quotient H P) I →
      IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.quotient H P) J →
      ∃ g : WithConv (FiniteTypeCommHopfAlgCat.quotient H P →ₐ[k] k), I.conjugate g = J)
    {I J : HopfIdeal k H}
    (hI : IsBorelOverAlgClosed k H I) (hJ : IsBorelOverAlgClosed k H J)
    (hPI : P ≤ I) (hPJ : P ≤ J) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g = J := by
  have h := exists_conjugate_eq_comapOfSurjective _ _
    (Bialgebra.Quotient.mkBialgHom P.toIdeal)
    (Bialgebra.Quotient.mkBialgHom_surjective _) (hconj _ _
      (hI.map_of_le hPI) (hJ.map_of_le hPJ))
  simpa only [comapOfSurjective_map_mkBialgHom hPI,
    comapOfSurjective_map_mkBialgHom hPJ] using h

variable [IsAlgClosed k]

/-- **Borel conjugacy reduces to smooth connected affine groups.** Over an algebraically
closed field, a conjugacy theorem for all smooth geometrically connected finite-type affine
groups implies conjugacy for every finite-type affine group, including nonreduced and
disconnected ones. The conjugating point comes from the reduced identity component. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed_of_smooth_connected
    (hconj : ∀ (K : FiniteTypeCommHopfAlgCat.{u, u} k),
      Algebra.Smooth k K → geometricallyConnectedCommHopfAlgProperty k K.obj →
      ∀ I J : HopfIdeal k K, IsBorelOverAlgClosed k K I → IsBorelOverAlgClosed k K J →
      ∃ g : WithConv (K →ₐ[k] k), I.conjugate g = J)
    {I J : HopfIdeal k H}
    (hI : IsBorelOverAlgClosed k H I) (hJ : IsBorelOverAlgClosed k H J) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g = J := by
  let N := reduction k H
  let P := N.identityComponent
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H N) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _)
  have hP : ∀ B : HopfIdeal k H, IsBorelCandidate k H B → P ≤ B := by
    intro B hB
    let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H B) :=
      (smoothCommHopfAlgProperty_iff _).mp hB.smooth
    let _ : IsReduced (H ⧸ B.toIdeal) := isReduced_of_smooth k _
    exact identityComponent_le_of_le (reduction_le_of_isReduced_quotient k H B)
      hB.geometricallyConnected
  exact exists_conjugate_eq_of_isBorelOverAlgClosed_of_quotient P
    (hconj _ N.smooth_identityComponent N.geometricallyConnected_identityComponent)
    hI hJ (hP I ((isBorelOverAlgClosed_iff _ _ _).mp hI).2.prop)
    (hP J ((isBorelOverAlgClosed_iff _ _ _).mp hJ).2.prop)

end TauCeti.HopfIdeal
