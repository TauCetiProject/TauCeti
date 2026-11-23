/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.Descent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Comap
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Connected
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric connectedness of Mumford–Tate groups

Let `G` be an affine group over `ℚ` and `h : S → G_ℝ` a homomorphism from the Deligne torus. Its
Mumford–Tate group `MT(h)` (`TauCeti.DeligneTorus.mumfordTateHopfIdeal`) is the smallest closed
`ℚ`-subgroup of `G` through whose real extension `h` factors. This file proves that `MT(h)` is
geometrically connected; no polarization is assumed. For `G = GL(V)` this is the connectedness of
the Mumford–Tate group of a rational Hodge structure.

The proof follows the identity component of `MT(h)`. Over `ℚ^alg = AlgebraicClosure ℚ` the
identity component of `MT(h)_{ℚ^alg}` is cut out by
`TauCeti.HopfAlgebra.identityComponentHopfIdeal`. It is stable under the Galois group of
`ℚ^alg / ℚ` (`TauCeti.CommHopfAlgCat.map_mem_identityComponentHopfIdeal_baseChange_iff`), so Galois
descent (`TauCeti.CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff`) defines the identity
component over `ℚ`. Since `S` is geometrically connected, `h` kills it
(`TauCeti.CommHopfAlgCat.apply_one_tmul_eq_zero_of_mem_identityComponentHopfIdeal`), and
minimality of `MT(h)` then forces the identity component to be all of `MT(h)`.

## Main declarations

* `TauCeti.DeligneTorus.geometricallyConnected_quotient_mumfordTateHopfIdeal`: the Mumford–Tate
  group is geometrically connected.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16).
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), §3, pp. 24–25.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 (the identity component) and
  Appendix A (Galois descent).
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat
open scoped TensorProduct

namespace TauCeti.DeligneTorus

/-- **The Mumford–Tate group is geometrically connected.** For an affine group `G` over `ℚ` and a
homomorphism `h : S → G_ℝ` from the Deligne torus whose Mumford–Tate group `MT(h)` is of finite
type, `MT(h)` is geometrically connected. No polarization is needed. -/
theorem geometricallyConnected_quotient_mumfordTateHopfIdeal
    {H : _root_.CommHopfAlgCat.{0} ℚ} (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S)
    [Algebra.FiniteType ℚ (quotient H (mumfordTateHopfIdeal h))] :
    geometricallyConnectedCommHopfAlgProperty ℚ (quotient H (mumfordTateHopfIdeal h)) := by
  set J := mumfordTateHopfIdeal h
  let L := AlgebraicClosure ℚ
  let E : HopfIdeal L (baseChange (K := L) (quotient H J)) :=
    HopfAlgebra.identityComponentHopfIdeal
  obtain ⟨I, hI, -⟩ := (existsUnique_baseChangeHopfIdeal_eq_iff E).mpr
    fun σ _ hx ↦ (map_mem_identityComponentHopfIdeal_baseChange_iff σ).mpr hx
  let I' := I.comapOfSurjective (mkQuotient H J).hom (mkQuotient_surjective H J)
  have hI'J : I' ≤ J := by
    rw [le_mumfordTateHopfIdeal_iff, baseChangeHopfIdeal_toIdeal, Ideal.map_le_iff_le_comap]
    intro y hy
    have hy' : (mkQuotient H J).hom y ∈ I := HopfIdeal.mem_comapOfSurjective.mp hy
    have hmem : (1 : L) ⊗ₜ[ℚ] (mkQuotient H J).hom y ∈ E :=
      hI ▸ one_tmul_mem_baseChangeHopfIdeal hy'
    have hcomp := congrArg (fun f ↦ f.hom ((1 : ℝ) ⊗ₜ[ℚ] y))
      (baseChangeMap_mkQuotient_comp_mumfordTateLift h)
    simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at hcomp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa [← hcomp] using
      apply_one_tmul_eq_zero_of_mem_identityComponentHopfIdeal
        (Algebra.WeilRestriction.geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup
          (k := ℝ) (B := ℂ)) (mumfordTateLift h) hmem
  have hE : E = ⊥ := by rw [← hI, eq_bot_of_comapOfSurjective_le I hI'J, baseChangeHopfIdeal_bot]
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange ℚ L]
  exact HopfAlgebra.identityComponentHopfIdeal_eq_bot_iff_connectedSpace.mp hE

end TauCeti.DeligneTorus
