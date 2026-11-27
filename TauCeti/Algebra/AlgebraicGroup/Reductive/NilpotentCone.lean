/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Lie
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone

/-!
# The nilpotent cone of a reductive group

Let `G = Spec H` be a reductive affine group over an algebraically closed field `k` of
characteristic zero, with Lie algebra `𝔤`. Then `𝔤` is reductive, `𝔤 = Z(𝔤) ⊕ ⁅𝔤, 𝔤⁆`, and the
invariant polynomial functions on `𝔤` include the linear functions vanishing on `⁅𝔤, 𝔤⁆`. So the
nilpotent cone, the zero fibre of the adjoint quotient (`TauCeti.nilpotentConeIdeal`), has zero
central coordinate: its `k`-points are the `ad`-nilpotent elements of the derived ideal.

This is smaller than the set of `ad`-nilpotent elements of `𝔤` as soon as the center of `𝔤` is
nonzero: every central element is `ad`-nilpotent, and the `ad`-nilpotent elements are the sums of a
central element and a point of the cone. When the Killing form of `𝔤` is nondegenerate the two sets
agree (`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff`).

## Main results

* `nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad`, in the namespace
  `TauCeti.reductiveCommHopfAlgProperty`: the `k`-points of the nilpotent cone of a reductive group
  are the `ad`-nilpotent elements of `⁅𝔤, 𝔤⁆`.
* `nilpotentConeIdeal_le_ker_lift_eval_add_iff`: for `z` central and `y ∈ ⁅𝔤, 𝔤⁆`, the point
  `z + y` lies on the cone exactly when `z = 0` and `ad y` is nilpotent.
* `isNilpotent_ad_iff_exists_mem_center_add_nilpotentConeIdeal_le_ker_lift_eval`: the
  `ad`-nilpotent elements of `𝔤` are the sums of a central element and a point of the cone.
* `mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad` and
  `centerProdNilpotentConeOrbitsEquiv`: the rational orbits in the nilpotent cone are the orbits of
  `ad`-nilpotent elements of `⁅𝔤, 𝔤⁆`, giving
  `Z(𝔤) × nilpotentConeOrbits k H ≃ {O // O.IsNilpotentAd}`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §1.3.
* B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. 85 (1963),
  327–404.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **The rational points of the nilpotent cone of a reductive group.** For a reductive affine
group over an algebraically closed field of characteristic zero, an element `x` of the Lie algebra
`𝔤` lies on the nilpotent cone, that is evaluation at `x` kills its ideal, exactly when `x` lies in
the derived ideal `⁅𝔤, 𝔤⁆` and `ad x` is nilpotent. In particular a nonzero central element of `𝔤`
does not lie on the cone. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad
    (hH : reductiveCommHopfAlgProperty k H) {x : 𝔤} :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) ↔
      x ∈ LieAlgebra.derivedSeries k 𝔤 1 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 x) :=
  have := hH.geometricallyConnected.connectedSpace
  have := hH.hasCentralRadical_dual_cotangentSpace
  TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad

/-- **The nilpotent cone of a reductive group has zero central coordinate.** For a reductive affine
group over an algebraically closed field of characteristic zero, let `z` be a central element of
the Lie algebra `𝔤` and `y ∈ ⁅𝔤, 𝔤⁆`. Then `z + y` lies on the nilpotent cone exactly when the
central coordinate `z` is zero and `ad y` is nilpotent. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_add_iff (hH : reductiveCommHopfAlgProperty k H)
    {z y : 𝔤} (hz : z ∈ LieAlgebra.center k 𝔤) (hy : y ∈ LieAlgebra.derivedSeries k 𝔤 1) :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (z + y))) ↔
      z = 0 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 y) :=
  have := hH.geometricallyConnected.connectedSpace
  have := hH.hasCentralRadical_dual_cotangentSpace
  TauCeti.nilpotentConeIdeal_le_ker_lift_eval_add_iff hz hy

/-- **The `ad`-nilpotent elements of the Lie algebra of a reductive group.** For a reductive affine
group over an algebraically closed field of characteristic zero, `ad x` is nilpotent exactly when
`x = z + y` with `z` central and `y` on the nilpotent cone. -/
theorem isNilpotent_ad_iff_exists_mem_center_add_nilpotentConeIdeal_le_ker_lift_eval
    (hH : reductiveCommHopfAlgProperty k H) {x : 𝔤} :
    IsNilpotent (LieAlgebra.ad k 𝔤 x) ↔
      ∃ z ∈ LieAlgebra.center k 𝔤, ∃ y : 𝔤,
        nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 y)) ∧
          z + y = x :=
  have := hH.geometricallyConnected.connectedSpace
  have := hH.hasCentralRadical_dual_cotangentSpace
  TauCeti.isNilpotent_ad_iff_exists_mem_center_add_nilpotentConeIdeal_le_ker_lift_eval

attribute [local instance] Derivation.adjointComodule in
/-- **Reductive nilpotent-cone orbit criterion.** For a reductive affine group over an
algebraically closed field of characteristic zero, the rational adjoint orbit of `x ∈ 𝔤` lies in
`TauCeti.nilpotentConeOrbits` iff `x ∈ ⁅𝔤, 𝔤⁆` and `ad x` is nilpotent. -/
theorem mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad
    (hH : reductiveCommHopfAlgProperty k H) {x : 𝔤} :
    (Comodule.VectorOrbit.mk x : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentConeOrbits k H ↔
      x ∈ LieAlgebra.derivedSeries k 𝔤 1 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 x) :=
  have := hH.geometricallyConnected.connectedSpace
  have := hH.hasCentralRadical_dual_cotangentSpace
  TauCeti.mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad

attribute [local instance] Derivation.adjointComodule in
/-- **Decomposition of `ad`-nilpotent orbits of a reductive group.** Adding a central element to an
orbit in the nilpotent cone gives `Z(𝔤) × nilpotentConeOrbits k H ≃ {O // O.IsNilpotentAd}`. -/
noncomputable def centerProdNilpotentConeOrbitsEquiv (hH : reductiveCommHopfAlgProperty k H) :
    LieAlgebra.center k 𝔤 × nilpotentConeOrbits k H ≃
      {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd} :=
  have := hH.geometricallyConnected.connectedSpace
  have := hH.hasCentralRadical_dual_cotangentSpace
  TauCeti.centerProdNilpotentConeOrbitsEquiv

attribute [local instance] Derivation.adjointComodule in
/-- `hH.centerProdNilpotentConeOrbitsEquiv` unfolds to
`TauCeti.centerProdNilpotentConeOrbitsEquiv`. -/
theorem centerProdNilpotentConeOrbitsEquiv_def (hH : reductiveCommHopfAlgProperty k H) :
    have := hH.geometricallyConnected.connectedSpace
    have := hH.hasCentralRadical_dual_cotangentSpace
    hH.centerProdNilpotentConeOrbitsEquiv =
      TauCeti.centerProdNilpotentConeOrbitsEquiv (k := k) (H := H) :=
  (rfl)

attribute [local instance] Derivation.adjointComodule in
/-- On `(z, mk y)`, `hH.centerProdNilpotentConeOrbitsEquiv` sends the pair to `mk (z + y)`. -/
@[simp]
theorem coe_centerProdNilpotentConeOrbitsEquiv_mk (hH : reductiveCommHopfAlgProperty k H)
    (z : LieAlgebra.center k 𝔤) {y : 𝔤}
    (hy : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentConeOrbits k H) :
    (hH.centerProdNilpotentConeOrbitsEquiv (z, ⟨Comodule.VectorOrbit.mk y, hy⟩) :
        Comodule.VectorOrbit k H 𝔤) =
      Comodule.VectorOrbit.mk ((z : 𝔤) + y) := by
  have := hH.geometricallyConnected.connectedSpace
  have := hH.hasCentralRadical_dual_cotangentSpace
  exact TauCeti.coe_centerProdNilpotentConeOrbitsEquiv_mk z hy

attribute [local instance] Derivation.adjointComodule in
/-- The inverse of `hH.centerProdNilpotentConeOrbitsEquiv` splits `mk (z + y)` into `(z, mk y)`. -/
@[simp]
theorem centerProdNilpotentConeOrbitsEquiv_symm_mk_add (hH : reductiveCommHopfAlgProperty k H)
    (z : LieAlgebra.center k 𝔤) {y : 𝔤}
    (hy : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ∈ nilpotentConeOrbits k H)
    (h : (Comodule.VectorOrbit.mk ((z : 𝔤) + y) : Comodule.VectorOrbit k H 𝔤).IsNilpotentAd) :
    hH.centerProdNilpotentConeOrbitsEquiv.symm
        ⟨Comodule.VectorOrbit.mk ((z : 𝔤) + y), h⟩ =
      (z, ⟨Comodule.VectorOrbit.mk y, hy⟩) := by
  have := hH.geometricallyConnected.connectedSpace
  have := hH.hasCentralRadical_dual_cotangentSpace
  exact TauCeti.centerProdNilpotentConeOrbitsEquiv_symm_mk_add z hy h

end TauCeti.reductiveCommHopfAlgProperty
