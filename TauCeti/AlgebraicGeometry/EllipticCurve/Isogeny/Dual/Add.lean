/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.WeilPairing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
-- Proof-only: a morphism acts additively on points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring

/-!
# The dual isogeny is additive

Let `f, g : W₁ → W₂` be morphisms of elliptic curves over a field `F`, with the dual extended to
morphisms by `0̂ = 0` (`TauCeti.Isogeny.Hom.dual`). Then the dual of the sum is the sum of the
duals: `(f + g)^ = f̂ + ĝ` (Silverman III.6.2(b)). So the dual is an additive equivalence
`Hom W₁ W₂ ≃+ Hom W₂ W₁`, its own inverse up to swapping the curves.

Over a separably closed field the proof goes through the Weil pairing. For `N` invertible in the
field, the dual of every isogeny is adjoint to it
(`TauCeti.Isogeny.weilPairing_eq_weilPairing_dual`), and trivially so for the zero map, so for
`S ∈ W₁[N]` and `T ∈ W₂[N]`

    e_N(S, (f + g)^ T) = e_N((f + g) S, T) = e_N(f S, T) · e_N(g S, T) = e_N(S, f̂ T) · e_N(S, ĝ T)
                       = e_N(S, f̂ T + ĝ T).

Nondegeneracy of the pairing gives `(f + g)^ T = f̂ T + ĝ T` on `W₂[N]`, and two morphisms agreeing
on the `ℓ`-torsion for every prime `ℓ` other than the characteristic are equal
(`TauCeti.Isogeny.Hom.ext_pointMap_of_prime_zsmul_eq_zero`). Over an arbitrary field, both sides
are compared after base change to a separable closure, which is faithful on morphisms and commutes
with sums and with duals.

Additivity of the dual is what makes the degree a quadratic form on the morphisms
(`TauCeti.Isogeny.Hom.degreeForm`). Silverman proves it by the Picard-group description of the dual;
the argument here replaces it with the Weil pairing, whose compatibility with the dual
(Silverman III.8.2) is already available.

## Main definitions

* `TauCeti.Isogeny.Hom.dualAddEquiv`: the dual as an additive equivalence.

## Main results

* `TauCeti.Isogeny.Hom.dual_map`: the dual of a morphism commutes with base change.
* `TauCeti.Isogeny.Hom.dual_add`: `(f + g)^ = f̂ + ĝ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.2(b) and III.8.2.
-/

public section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The dual commutes with base change** along any homomorphism of fields. -/
@[simp]
theorem dual_map {K : Type*} [Field K] (f : Hom W₁ W₂) (σ : F →+* K) :
    f.dual.map σ = (f.map σ).dual := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

section IsSepClosed

variable [IsSepClosed F]

/-- The dual of a morphism is adjoint to it for the Weil pairing: `e_N(f S, T) = e_N(S, f̂ T)`. For
the zero map both sides vanish. -/
private theorem weilPairing_eq_weilPairing_dual [DecidableEq F] (f : Hom W₁ W₂) (N : ℕ) [NeZero N]
    (hN : (N : F) ≠ 0) {S : Submodule.torsionBy ℤ W₁.Point (N : ℤ)}
    {T : Submodule.torsionBy ℤ W₂.Point (N : ℤ)} {S' : Submodule.torsionBy ℤ W₂.Point (N : ℤ)}
    {T' : Submodule.torsionBy ℤ W₁.Point (N : ℤ)} (hS : f.pointMap S = S')
    (hT : f.dual.pointMap T = T') :
    weilPairing W₂ N hN S' T = weilPairing W₁ N hN S T' := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · obtain rfl : S' = 0 := Subtype.ext (by rw [← hS, zero_pointMap, ZeroMemClass.coe_zero])
    obtain rfl : T' = 0 := Subtype.ext (by rw [← hT, dual_zero, zero_pointMap,
      ZeroMemClass.coe_zero])
    simp
  · rw [dual_ofIsogeny] at hT
    exact φ.weilPairing_eq_weilPairing_dual N hN hS hT

/-- The dual of a sum is the sum of the duals, over a separably closed field. -/
private theorem dual_add_of_isSepClosed (f g : Hom W₁ W₂) : (f + g).dual = f.dual + g.dual := by
  classical
  refine ext_pointMap_of_prime_zsmul_eq_zero fun N hp hN T hT ↦ ?_
  have : NeZero N := ⟨hp.ne_zero⟩
  let T' : Submodule.torsionBy ℤ W₂.Point (N : ℤ) := ⟨T, (Submodule.mem_torsionBy_iff _ _).mpr hT⟩
  -- the images of `T` under the duals, as `N`-torsion points of `W₁`
  let d (h : Hom W₁ W₂) := torsionByMap (N : ℤ) h.dual.pointMapHom.toIntLinearMap T'
  suffices h : d (f + g) = d f + d g by simpa [d, T'] using congrArg Subtype.val h
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_weilPairing_eq_zero W₁ N hN fun S ↦ ?_
  -- the images of `S` under `f` and `g`, as `N`-torsion points of `W₂`
  let i (h : Hom W₁ W₂) := torsionByMap (N : ℤ) h.pointMapHom.toIntLinearMap S
  -- adjointness moves each dual across the pairing, where `(f + g) S = f S + g S`
  have e (h : Hom W₁ W₂) {S' : Submodule.torsionBy ℤ W₂.Point (N : ℤ)}
      (hS' : h.pointMap S = S') : weilPairing W₁ N hN S (d h) = weilPairing W₂ N hN S' T' :=
    (h.weilPairing_eq_weilPairing_dual N hN hS' (by simp [d, T'])).symm
  -- and the pairing is additive in each variable
  rw [_root_.map_sub, _root_.map_add, e (f + g) (S' := i f + i g) (by simp [i]),
    e f (S' := i f) (by simp [i]), e g (S' := i g) (by simp [i]), _root_.map_add,
    AddMonoidHom.add_apply, sub_self]

end IsSepClosed

/-- **The dual is additive** (Silverman III.6.2(b)): `(f + g)^ = f̂ + ĝ`, over any field. -/
@[simp]
theorem dual_add (f g : Hom W₁ W₂) : (f + g).dual = f.dual + g.dual := by
  classical
  -- compare both sides over a separable closure, where the Weil pairing is available
  refine map_injective (algebraMap F (SeparableClosure F)) ?_
  simp only [dual_map, map_add]
  exact dual_add_of_isSepClosed _ _

variable (W₁ W₂) in
/-- **The dual as an additive equivalence** `Hom W₁ W₂ ≃+ Hom W₂ W₁`, its own inverse up to
swapping the curves. -/
noncomputable def dualAddEquiv : Hom W₁ W₂ ≃+ Hom W₂ W₁ where
  toFun := dual
  invFun := dual
  left_inv := dual_dual
  right_inv := dual_dual
  map_add' := dual_add

@[simp]
theorem dualAddEquiv_apply (f : Hom W₁ W₂) : dualAddEquiv W₁ W₂ f = f.dual :=
  (rfl)

@[simp]
theorem dualAddEquiv_symm : (dualAddEquiv W₁ W₂).symm = dualAddEquiv W₂ W₁ :=
  (rfl)

@[simp]
theorem dual_neg (f : Hom W₁ W₂) : (-f).dual = -f.dual :=
  _root_.map_neg (dualAddEquiv W₁ W₂) f

@[simp]
theorem dual_sub (f g : Hom W₁ W₂) : (f - g).dual = f.dual - g.dual :=
  _root_.map_sub (dualAddEquiv W₁ W₂) f g

@[simp]
theorem dual_nsmul (n : ℕ) (f : Hom W₁ W₂) : (n • f).dual = n • f.dual :=
  _root_.map_nsmul (dualAddEquiv W₁ W₂) n f

@[simp]
theorem dual_zsmul (n : ℤ) (f : Hom W₁ W₂) : (n • f).dual = n • f.dual :=
  _root_.map_zsmul (dualAddEquiv W₁ W₂) n f

end TauCeti.Isogeny.Hom

end
