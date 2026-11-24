/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Convolution groups over products of coefficient algebras

For a `k`-bialgebra `H` and commutative topological `k`-algebras,
`TauCeti.PointTopology.prodContinuousMulEquiv` and `TauCeti.PointTopology.piContinuousMulEquiv`
show that the algebraic convolution equivalences `AlgHom.prodPointsMulEquiv` and
`AlgHom.piValueMulEquiv` are multiplicative homeomorphisms (`≃ₜ*`) for the point topology, with
coordinates given by post-composition with the coefficient projections (and isomorphisms of
topological monoids, or of topological groups when `H` is a Hopf algebra, whenever the coefficient
algebras are topological semirings).

## Main declarations

* `TauCeti.PointTopology.prodContinuousMulEquiv`: multiplicative homeomorphism between points with
  values in `R₁ × R₂` and pairs of points (an isomorphism of topological monoids, or topological
  groups when `H` is a Hopf algebra, if `R₁` and `R₂` are topological semirings).
* `TauCeti.PointTopology.piContinuousMulEquiv`: multiplicative homeomorphism between convolution
  points valued in `∀ i, R i` and `∀ i, WithConv (H →ₐ[k] R i)` (an isomorphism of topological
  monoids, or topological groups when `H` is a Hopf algebra, if each `R i` is a topological
  semiring).

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, §3, and the map (3.6.2) in the proof of Thm. 3.6.
-/

public section

open Topology WithConv

namespace TauCeti.PointTopology

section BialgebraProd

variable {k H R₁ R₂ : Type*} [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁]
  [CommSemiring R₂] [Algebra k R₂] [TopologicalSpace R₂]

variable (k H R₁ R₂) in
/-- Multiplicative homeomorphism identifying points valued in `R₁ × R₂` with pairs of points via
the two projections, and sending `(x, y)` to `h ↦ (x h, y h)`. When `R₁` and `R₂` are topological
semirings, this is an isomorphism of topological monoids (and of topological groups when `H` is a
Hopf algebra). -/
noncomputable def prodContinuousMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toMulEquiv := AlgHom.prodPointsMulEquiv
  continuous_toFun :=
    ((AlgHom.continuous_mapValue continuous_fst).prodMk
      (AlgHom.continuous_mapValue continuous_snd)).congr fun x ↦
      Prod.ext (AlgHom.prodPointsMulEquiv_apply_fst x).symm
        (AlgHom.prodPointsMulEquiv_apply_snd x).symm
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    (((continuous_eval_ofConv h).comp continuous_fst).prodMk
      ((continuous_eval_ofConv h).comp continuous_snd)).congr fun p ↦ by
        simp only [Function.comp_apply, MulEquiv.invFun_eq_symm,
          AlgHom.prodPointsMulEquiv_symm_apply_ofConv]

@[simp]
theorem prodContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] R₁ × R₂)) :
    prodContinuousMulEquiv k H R₁ R₂ x =
      (AlgHom.mapValue (AlgHom.fst k R₁ R₂) x, AlgHom.mapValue (AlgHom.snd k R₁ R₂) x) :=
  Prod.ext (AlgHom.prodPointsMulEquiv_apply_fst x) (AlgHom.prodPointsMulEquiv_apply_snd x)

/-- The point paired from `(x, y)` takes the value `(x h, y h)` at `h`. -/
@[simp]
theorem prodContinuousMulEquiv_symm_apply_apply
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) (h : H) :
    (prodContinuousMulEquiv k H R₁ R₂).symm p h = (p.1 h, p.2 h) :=
  AlgHom.prodPointsMulEquiv_symm_apply_ofConv p h

end BialgebraProd

section BialgebraPi

variable (k H : Type*) {ι : Type*} (R : ι → Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)] [∀ i, TopologicalSpace (R i)]

/-- Multiplicative homeomorphism identifying convolution points of a bialgebra `H` valued in
`∀ i, R i`, with the point topology, with `∀ i, WithConv (H →ₐ[k] R i)`. When each `R i` is a
topological semiring, this is an isomorphism of topological monoids (and of topological groups when
`H` is a Hopf algebra). -/
noncomputable def piContinuousMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃ₜ* ∀ i, WithConv (H →ₐ[k] R i) where
  toMulEquiv := AlgHom.piValueMulEquiv
  continuous_toFun := continuous_pi fun i ↦
    (AlgHom.continuous_mapValue (ψ := Pi.evalAlgHom k R i) (continuous_apply i)).congr
      fun x ↦ WithConv.ofConv_injective <| AlgHom.ext fun h ↦ by
        simp [AlgHom.mapValue_apply]
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    (continuous_pi fun i ↦ (continuous_eval_ofConv h).comp (continuous_apply i)).congr fun f ↦ by
      funext i
      simp only [Function.comp_apply, MulEquiv.invFun_eq_symm, AlgHom.piValueMulEquiv_symm_apply]

variable {k H R}

/-- Evaluating `piContinuousMulEquiv k H R x` at `i` applies `AlgHom.mapValue`. -/
@[simp]
theorem piContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) :
    piContinuousMulEquiv k H R x i = AlgHom.mapValue (Pi.evalAlgHom k R i) x :=
  WithConv.ofConv_injective <| AlgHom.ext fun h ↦ by
    have hcoe : (piContinuousMulEquiv k H R x i).ofConv h =
        (AlgHom.piValueMulEquiv x i).ofConv h := rfl
    rw [hcoe, AlgHom.piValueMulEquiv_apply]
    simp

/-- Evaluating `(piContinuousMulEquiv k H R).symm f` on `h : H` at `i` gives `(f i).ofConv h`. -/
@[simp]
theorem piContinuousMulEquiv_symm_apply_ofConv
    (f : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piContinuousMulEquiv k H R).symm f).ofConv h i = (f i).ofConv h :=
  AlgHom.piValueMulEquiv_symm_apply f h i

end BialgebraPi

end TauCeti.PointTopology
