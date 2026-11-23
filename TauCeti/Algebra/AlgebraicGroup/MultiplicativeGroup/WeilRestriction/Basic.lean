/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.HopfAlgebra.WeilRestriction
public import TauCeti.Algebra.Polynomial.Laurent.Smooth
public import TauCeti.RingTheory.WeilRestriction.Smooth
import TauCeti.Algebra.Bialgebra.BaseChange
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# The Weil restriction of the multiplicative group

Let `B` be a commutative `A`-algebra that is finitely generated and projective as an `A`-module.
The Weil restriction `Res_{B/A} 𝔾ₘ` of the multiplicative group of `B` is the affine group over
`A` with coordinate Hopf algebra `WeilRestriction A B B[T;T⁻¹]`. Its points over a commutative
`A`-algebra `T` are the units of `B ⊗[A] T`
(`TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints`), naturally in `T`. The unit
attached to a point is the value at `T` of the point of `𝔾ₘ` over `B ⊗[A] T` that it classifies.
When `U` is a commutative `A`-bialgebra, the unit of `B ⊗[A] U` classifying a bialgebra map
`WeilRestriction A B B[T;T⁻¹] →ₐc[A] U` is group-like over `B`
(`TauCeti.Algebra.WeilRestriction.isGroupLikeElem_multiplicativeGroupPoints_toConv`).

The group `Res_{B/A} 𝔾ₘ` is commutative, and it is smooth over `A`: the corresponding instances
`TauCeti.Algebra.WeilRestriction.instIsCocomm` and `TauCeti.Algebra.WeilRestriction.instSmooth`
apply because `B[T;T⁻¹]` is cocommutative and smooth over `B`
(`LaurentPolynomial.instSmooth`).

For a nontrivial finite purely inseparable field extension `K/k`, the group `Res_{K/k} 𝔾ₘ` is
the standard example of a commutative pseudo-reductive group which is not reductive; neither of
these two properties is proved in this file.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints`: the group isomorphism
  `(Res_{B/A} 𝔾ₘ)(T) ≃* (B ⊗[A] T)ˣ`.
* `TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints_apply` and
  `TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints_symm_apply`: the unit attached to a
  point is the value of the classified point of `𝔾ₘ` at the coordinate `T`, and the point attached
  to a unit classifies evaluation at that unit.
* `TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints_naturality`: the isomorphism is
  natural in `T`.
* `TauCeti.Algebra.WeilRestriction.isGroupLikeElem_multiplicativeGroupPoints_toConv`: the unit of
  `B ⊗[A] U` classifying a bialgebra map `WeilRestriction A B B[T;T⁻¹] →ₐc[A] U` is group-like
  over `B`.
* `TauCeti.Algebra.WeilRestriction.sum_tmul_universalCoefficient_T`: in a finite basis `b` of `B`,
  the universal point is `∑ᵢ bᵢ ⊗ cᵢ`, where the `cᵢ` are the universal coefficients of `T`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  §1.5.
* J. S. Milne, *Algebraic Groups* (2017), §2.i.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1.
-/

public section

open WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (T : Type*) [CommRing T] [Algebra A T]

/-- **The points of the Weil restriction of `𝔾ₘ` are units.** For every commutative `A`-algebra
`T`, the points of `Res_{B/A} 𝔾ₘ` over `T` form a group isomorphic to the unit group of
`B ⊗[A] T`. -/
noncomputable def multiplicativeGroupPoints :
    WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T) ≃* (B ⊗[A] T)ˣ :=
  (pointsMulEquiv A B B[T;T⁻¹] T).trans MultiplicativeGroup.pointsMulEquiv

variable {A B T}

/-- The unit attached to a point of `Res_{B/A} 𝔾ₘ` is the value at the coordinate `T` of the
point of `𝔾ₘ` over `B ⊗[A] T` that it classifies. -/
@[simp]
theorem multiplicativeGroupPoints_apply (f : WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T)) :
    (multiplicativeGroupPoints A B T f : B ⊗[A] T) =
      homEquiv A B B[T;T⁻¹] T f.ofConv (LaurentPolynomial.T 1) := by
  simp [multiplicativeGroupPoints]

variable (A B) in
/-- **The coordinates of the universal point.** The universal point of `Res_{B/A} 𝔾ₘ`, a unit of
`B ⊗[A] Res_{B/A} 𝔾ₘ`, is `∑ᵢ bᵢ ⊗ cᵢ` for a finite basis `b` of `B`, where `cᵢ` is the universal
coefficient of the coordinate `T` of `𝔾ₘ` extracted by the `i`-th coordinate functional of `b`. -/
theorem sum_tmul_universalCoefficient_T {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) :
    ∑ i, b i ⊗ₜ[A] universalCoefficient (b.coord i) (LaurentPolynomial.T 1 : B[T;T⁻¹]) =
      (multiplicativeGroupPoints A B _ (toConv (AlgHom.id A (WeilRestriction A B B[T;T⁻¹]))) :
        B ⊗[A] WeilRestriction A B B[T;T⁻¹]) := by
  rw [b.sum_tmul_universalCoefficient, multiplicativeGroupPoints_apply, ofConv_toConv,
    homEquiv_apply, AlgHom.comp_apply]
  simp

/-- The point of `Res_{B/A} 𝔾ₘ` attached to a unit `u` of `B ⊗[A] T` is the one classifying
evaluation of Laurent polynomials at `u`. -/
@[simp]
theorem multiplicativeGroupPoints_symm_apply (u : (B ⊗[A] T)ˣ) :
    ((multiplicativeGroupPoints A B T).symm u).ofConv =
      (homEquiv A B B[T;T⁻¹] T).symm (laurentEval u) := by
  simp [multiplicativeGroupPoints]

/-- Naturality of `WeilRestriction.multiplicativeGroupPoints` in the `A`-algebra `T`:
post-composing with `h : T →ₐ[A] T'` corresponds to applying `B ⊗[A] h` to units. -/
theorem multiplicativeGroupPoints_naturality {T' : Type*} [CommRing T'] [Algebra A T']
    (h : T →ₐ[A] T') (f : WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T)) :
    multiplicativeGroupPoints A B T' (toConv (h.comp f.ofConv)) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B h : B ⊗[A] T →* B ⊗[A] T')
        (multiplicativeGroupPoints A B T f) := by
  simp only [multiplicativeGroupPoints, MulEquiv.trans_apply, pointsMulEquiv_naturality,
    ← MultiplicativeGroup.pointsMulEquiv_mapValue, AlgHom.mapValue_apply]

/-- The unit of `B ⊗[A] U` classifying a bialgebra map `WeilRestriction A B B[T;T⁻¹] →ₐc[A] U`
is group-like over `B`. -/
theorem isGroupLikeElem_multiplicativeGroupPoints_toConv
    {U : Type*} [CommRing U] [Bialgebra A U] (φ : WeilRestriction A B B[T;T⁻¹] →ₐc[A] U) :
    IsGroupLikeElem B
      (multiplicativeGroupPoints A B U (toConv (φ : WeilRestriction A B B[T;T⁻¹] →ₐ[A] U)) :
        B ⊗[A] U) := by
  let v := multiplicativeGroupPoints A B U (toConv (φ : WeilRestriction A B B[T;T⁻¹] →ₐ[A] U))
  refine ⟨?_, ?_⟩
  · -- Compatibility with the counit gives `(B ⊗ ε)(v) = 1` in `B ⊗[A] A ≃ B`.
    have hc := congrArg (fun w : (B ⊗[A] A)ˣ ↦ Algebra.TensorProduct.rid A B B (w : B ⊗[A] A))
      (multiplicativeGroupPoints_naturality (Bialgebra.counitAlgHom A U)
        (toConv (φ : WeilRestriction A B B[T;T⁻¹] →ₐ[A] U)))
    rw [ofConv_toConv, BialgHom.counitAlgHom_comp φ,
      ← TauCeti.Bialgebra.ofConv_one_eq_counitAlgHom, toConv_ofConv, map_one, Units.val_one,
      map_one, Units.coe_map, MonoidHom.coe_ofClass] at hc
    have hrid (z : B ⊗[A] U) :
        Algebra.TensorProduct.rid A B B
            (Algebra.TensorProduct.lTensor (S := B) B (Bialgebra.counitAlgHom A U) z) =
          Coalgebra.counit (R := B) z := by
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b u => simp [Algebra.smul_def, mul_comm]
    exact (hrid v).symm.trans hc.symm
  · -- Compatibility with comultiplication splits `(B ⊗ Δ)(v)` into the two tensor inclusions.
    let e := TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv A B U U
    have hd := multiplicativeGroupPoints_naturality (Bialgebra.comulAlgHom A U)
      (toConv (φ : WeilRestriction A B B[T;T⁻¹] →ₐ[A] U))
    have hmul :
        toConv ((Bialgebra.comulAlgHom A U).comp (φ : WeilRestriction A B B[T;T⁻¹] →ₐ[A] U)) =
          toConv ((Algebra.TensorProduct.includeLeft : U →ₐ[A] U ⊗[A] U).comp φ) *
            toConv ((Algebra.TensorProduct.includeRight : U →ₐ[A] U ⊗[A] U).comp φ) := by
      simpa only [← TauCeti.Bialgebra.comulPoint_eq_include_mul, BialgHom.mapDomain_apply,
        ofConv_toConv] using
        map_mul (BialgHom.mapDomain (A := U ⊗[A] U) φ)
          (toConv (Algebra.TensorProduct.includeLeft : U →ₐ[A] U ⊗[A] U))
          (toConv (Algebra.TensorProduct.includeRight : U →ₐ[A] U ⊗[A] U))
    rw [ofConv_toConv, hmul, map_mul, multiplicativeGroupPoints_naturality,
      multiplicativeGroupPoints_naturality] at hd
    have hde := congrArg (fun w : (B ⊗[A] (U ⊗[A] U))ˣ ↦ e (w : B ⊗[A] (U ⊗[A] U))) hd.symm
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul, map_mul] at hde
    have hleft (z : B ⊗[A] U) :
        e (Algebra.TensorProduct.lTensor (S := B) B
            (Algebra.TensorProduct.includeLeft : U →ₐ[A] U ⊗[A] U) z) = z ⊗ₜ[B] 1 := by
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
      | tmul b u => simp [e, Algebra.TensorProduct.one_def]
    have hright (z : B ⊗[A] U) :
        e (Algebra.TensorProduct.lTensor (S := B) B
            (Algebra.TensorProduct.includeRight : U →ₐ[A] U ⊗[A] U) z) = 1 ⊗ₜ[B] z := by
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
      | tmul b u =>
        apply e.symm.injective
        simp [e, Algebra.TensorProduct.one_def]
    have hlTensor (z : B ⊗[A] U) :
        TensorProduct.AlgebraTensorModule.distribBaseChange A B U U
            (Algebra.TensorProduct.map (AlgHom.id A B) (Bialgebra.comulAlgHom A U) z) =
          e (Algebra.TensorProduct.lTensor (S := B) B (Bialgebra.comulAlgHom A U) z) := by
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b u =>
        simp [e, ← AlgEquiv.coe_toLinearEquiv,
          TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv_toLinearEquiv]
    rw [← Bialgebra.comulAlgHom_apply, TensorProduct.comulAlgHom_baseChange, hlTensor, hde,
      hleft, hright, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end TauCeti.Algebra.WeilRestriction
