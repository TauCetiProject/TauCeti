/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Map

/-!
# Central subgroups and Lie algebra centralizers

Every central closed subgroup scheme of `G = Spec H` acts trivially in the adjoint representation
and therefore lies scheme-theoretically inside `C_G(x)` for every Lie algebra element `x ∈ 𝔤`.
In Hopf coordinates, `centralizerHopfIdeal H x ≤ I` for every central Hopf ideal `I`, and in
particular `centralizerHopfIdeal H x ≤ CommHopfAlgCat.centerDefiningIdeal H`.

Consequently, when a homomorphism `f : H ⟶ K` has central kernel, the scheme-theoretic kernel of
the induced centralizer morphism `C_K(x) → C_H(df(x))` is canonically isomorphic to `ker(f)`.

## Main declarations

* `TauCeti.centralizerHopfIdeal_le_of_isCentral`: every central Hopf ideal contains
  `centralizerHopfIdeal H x`.
* `CommHopfAlgCat.centralizerHopfIdeal_le_centerDefiningIdeal`: the center `Z(G)` lies in
  `C_G(x)`.
-/

public section

open CategoryTheory Derivation WithConv

namespace TauCeti

universe u

variable {k : Type u} [Field k]

/-- Every central closed subgroup scheme of `Spec H` is contained scheme-theoretically in the
centralizer of every Lie algebra element. In Hopf coordinates, `centralizerHopfIdeal H x ≤ I`. -/
theorem centralizerHopfIdeal_le_of_isCentral {H : Type u} [CommRing H] [HopfAlgebra k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    {I : HopfIdeal k H} (hI : I.IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    centralizerHopfIdeal H x ≤ I := by
  apply (HopfIdeal.le_iff_forall_quotientPointsSubgroup_le
    (H := _root_.CommHopfAlgCat.of k H) _ _).mpr
  intro A g hg
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  have hpt : Derivation.pointInCounitAlgebra A g =
      AlgHom.mapValue (Bialgebra.CounitAlgebra.algEquivSelf k H A).symm.toAlgHom g :=
    (Derivation.pointInCounitAlgebra_eq_pointsMulEquiv_symm A g).trans
      (Bialgebra.CounitAlgebra.pointsMulEquiv_symm_eq_mapValue k H A g)
  have hcent : HopfAlgebra.IsCentralPoint (Derivation.pointInCounitAlgebra A g) :=
    hpt ▸ (CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k H) I hI A hg).mapValue
      (Bialgebra.CounitAlgebra.algEquivSelf k H A).symm.toAlgHom
  have hle : (centralizerHopfIdeal H x).toIdeal ≤ RingHom.ker g.ofConv :=
    (centralizerHopfIdeal_le_ker_iff x g).mpr
      (Derivation.adDerivation_eq_self_of_isCentralPoint _ hcent)
  intro y hy
  exact hle (HopfIdeal.mem_toIdeal.mpr hy)

end TauCeti

namespace CommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- The scheme-theoretic center `Z(G)` lies in the centralizer of every Lie algebra element. -/
theorem centralizerHopfIdeal_le_centerDefiningIdeal (H : CommHopfAlgCat.{u} k)
    [Module.Finite k (TauCeti.Bialgebra.CotangentSpace k H)]
    (x : Module.Dual k (TauCeti.Bialgebra.CotangentSpace k H)) :
    TauCeti.centralizerHopfIdeal H x ≤ TauCeti.CommHopfAlgCat.centerDefiningIdeal H :=
  TauCeti.centralizerHopfIdeal_le_of_isCentral
    (TauCeti.CommHopfAlgCat.isCentral_centerDefiningIdeal H) x

end CommHopfAlgCat
