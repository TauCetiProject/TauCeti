/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Containment
public import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent
import TauCeti.RingTheory.Derivation.Idempotent

/-!
# Smooth closed subgroups with the full Lie algebra

Let `G` be a smooth connected affine group of finite type over an algebraically closed field,
and `H ≤ G` a smooth closed subgroup with `Lie(H) = Lie(G)`. Then `H = G`.

The subgroup `H` need not be connected, so the comparison of smooth connected closed subgroups
by their Lie algebras does not apply to it directly. Its identity component `H°` is smooth and
connected, and has the same Lie algebra as `H`: a tangent vector at the identity kills every
idempotent, in particular the one cutting out `H°`. The coordinate map `O(G) → O(H°)` is then
surjective with surjective differential, so it is injective.

## Main declarations

* `TauCeti.HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top`: the identity component
  has the same Lie algebra as the group.
* `TauCeti.HopfIdeal.eq_bot_of_lieSubalgebra_eq_top`: a smooth closed subgroup of a smooth
  connected group with the full Lie algebra is the whole group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section


namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The identity component of a finite-type affine group over an algebraically closed field has
the same Lie algebra as the group. -/
theorem lieSubalgebra_identityComponentHopfIdeal_eq_top :
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).lieSubalgebra (B := k) = ⊤ := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let e : H := PrimeSpectrum.connectedComponentIdempotent (R := H)
    (Bialgebra.augmentationPoint k H)
  have hspan : (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal =
      Ideal.span {1 - e} := by
    rw [HopfAlgebra.identityComponentHopfIdeal_toIdeal]
    ext x
    exact PrimeSpectrum.mem_connectedComponentIdeal_iff.trans Ideal.mem_span_singleton'.symm
  rw [eq_top_iff]
  intro d _
  rw [mem_lieSubalgebra_iff_of_toIdeal_eq_span _ hspan]
  rintro x rfl
  have he : IsIdempotentElem e := PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent _
  rw [map_sub, d.map_one_eq_zero, d.apply_eq_zero_of_isIdempotentElem he, sub_zero]

/-- A smooth closed subgroup of a smooth connected affine group over an algebraically closed
field is the whole group as soon as its Lie algebra is the whole Lie algebra.

The order on Hopf ideals reverses inclusion of closed subgroups, so `I = ⊥` says that the closed
subgroup cut out by `I` is everything. -/
theorem eq_bot_of_lieSubalgebra_eq_top [Algebra.Smooth k H] [ConnectedSpace (PrimeSpectrum H)]
    (I : HopfIdeal k H) [Algebra.Smooth k (H ⧸ I.toIdeal)]
    (hI : I.lieSubalgebra (B := k) = ⊤) : I = ⊥ := by
  let Q := FiniteTypeCommHopfAlgCat.quotient H I
  let J := HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Q)
  let _ : Algebra.Smooth k Q := ‹Algebra.Smooth k (H ⧸ I.toIdeal)›
  -- The coordinate map of the inclusion of the identity component of the subgroup.
  let f : H →ₐc[k] Q ⧸ J.toIdeal :=
    (Bialgebra.Quotient.mkBialgHom J.toIdeal).comp (Bialgebra.Quotient.mkBialgHom I.toIdeal)
  have hf : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hdf : Function.Surjective (derivationCompLieHom (B := k) f) := by
    rw [derivationCompLieHom_comp, LieHom.coe_comp]
    -- A closed subgroup with the full Lie algebra has surjective differential.
    have hsurj (K : Type u) [CommRing K] [HopfAlgebra k K] (L : HopfIdeal k K)
        (hL : L.lieSubalgebra (B := k) = ⊤) :
        Function.Surjective
          (derivationCompLieHom (B := k) (Bialgebra.Quotient.mkBialgHom L.toIdeal)) :=
      fun d ↦ ⟨(quotientLieEquiv L).symm ⟨d, hL ▸ LieSubalgebra.mem_top d⟩, by
        rw [derivationCompLieHom_apply, ← quotientLieHom_apply, ← quotientLieEquiv_apply_coe,
          LieEquiv.apply_symm_apply]⟩
    exact (hsurj H I hI).comp (hsurj Q J lieSubalgebra_identityComponentHopfIdeal_eq_top)
  have hker := ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot f hf
    ((smoothCommHopfAlgProperty_iff _).mpr inferInstance) inferInstance
    ((smoothCommHopfAlgProperty_iff _).mpr
      (FiniteTypeCommHopfAlgCat.smooth_identityComponent Q))
    (FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent Q)
    (conormalSubspace_ker_eq_bot_of_surjective_of_derivationCompLieHom_surjective f hf hdf)
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  rw [← hker, mem_ker]
  have hx0 : Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal x = 0 := by
    rw [Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  simp only [f, BialgHom.comp_apply, hx0, map_zero]

end TauCeti.HopfIdeal
