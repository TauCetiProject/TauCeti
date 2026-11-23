/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.Algebra.Pi
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Point spaces and convolution groups over products of coefficient algebras

For a `k`-algebra `A` and topological `k`-algebras, the point topology on `A →ₐ[k] R × S` and
`A →ₐ[k] ∀ i, R i` agrees with the product topology (`prodHomeomorph` and `piHomeomorph`).
For a `k`-bialgebra `H`, `TauCeti.PointTopology.prodContinuousMulEquiv` and
`TauCeti.PointTopology.piPointsContinuousMulEquiv` upgrade the factor identifications to
topological multiplicative equivalences for the convolution product and the point topology.

## Main declarations

* `TauCeti.PointTopology.prodHomeomorph`, `TauCeti.PointTopology.piHomeomorph`
* `TauCeti.PointTopology.prodContinuousMulEquiv`: points with values in `R₁ × R₂` are pairs of
  points, as topological monoids.
* `TauCeti.PointTopology.piPointsContinuousMulEquiv`: convolution points valued in `∀ i, R i`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, pp. 2–3, §3, p. 4, and the map (3.6.2) in the proof of Thm. 3.6, p. 7.
-/

public section

open Topology WithConv

namespace TauCeti.PointTopology

section Semiring

variable (k A R S : Type*) [CommSemiring k] [Semiring A] [Algebra k A]
  [Semiring R] [Algebra k R] [TopologicalSpace R] [Semiring S] [Algebra k S] [TopologicalSpace S]

/-- Points of `A` valued in `R × S` are homeomorphic to `(A →ₐ[k] R) × (A →ₐ[k] S)`. -/
def prodHomeomorph : (A →ₐ[k] R × S) ≃ₜ (A →ₐ[k] R) × (A →ₐ[k] S) where
  toEquiv := AlgHom.prodEquiv.symm
  continuous_toFun := (continuous_map_codomain (AlgHom.fst k R S) continuous_fst).prodMk
    (continuous_map_codomain (AlgHom.snd k R S) continuous_snd)
  continuous_invFun := continuous_iff.2 fun a ↦
    ((continuous_eval a).comp continuous_fst).prodMk ((continuous_eval a).comp continuous_snd)

variable {k A R S}

/-- The first coordinate of `prodHomeomorph` postcomposes with `AlgHom.fst`. -/
@[simp]
theorem prodHomeomorph_apply_fst (x : A →ₐ[k] R × S) :
    (prodHomeomorph k A R S x).1 = (AlgHom.fst k R S).comp x := (rfl)

/-- The second coordinate of `prodHomeomorph` postcomposes with `AlgHom.snd`. -/
@[simp]
theorem prodHomeomorph_apply_snd (x : A →ₐ[k] R × S) :
    (prodHomeomorph k A R S x).2 = (AlgHom.snd k R S).comp x := (rfl)

/-- The inverse of `prodHomeomorph` pairs two factor homomorphisms with `AlgHom.prod`. -/
@[simp]
theorem prodHomeomorph_symm_apply (p : (A →ₐ[k] R) × (A →ₐ[k] S)) :
    (prodHomeomorph k A R S).symm p = p.1.prod p.2 := (rfl)

end Semiring

section Pi

variable (k A : Type*) {ι : Type*} (R : ι → Type*) [CommSemiring k] [Semiring A] [Algebra k A]
  [∀ i, Semiring (R i)] [∀ i, Algebra k (R i)] [∀ i, TopologicalSpace (R i)]

/-- Points of `A` valued in `∀ i, R i` are homeomorphic to `∀ i, A →ₐ[k] R i`. -/
def piHomeomorph : (A →ₐ[k] ∀ i, R i) ≃ₜ ∀ i, A →ₐ[k] R i where
  toEquiv := AlgHom.piEquiv
  continuous_toFun := continuous_pi fun i ↦
    (continuous_map_codomain (Pi.evalAlgHom k R i) (continuous_apply i)).congr fun _ ↦ by simp
  continuous_invFun := continuous_iff.2 fun a ↦
    continuous_pi fun i ↦ ((continuous_eval a).comp (continuous_apply i)).congr fun _ ↦ by simp

variable {k A R}

/-- Evaluating `piHomeomorph` at `i` postcomposes with `Pi.evalAlgHom k R i`. -/
@[simp]
theorem piHomeomorph_apply (x : A →ₐ[k] ∀ i, R i) (i : ι) :
    piHomeomorph k A R x i = (Pi.evalAlgHom k R i).comp x :=
  AlgHom.piEquiv_apply x i

/-- The inverse of `piHomeomorph` is `AlgHom.pi`. -/
@[simp]
theorem piHomeomorph_symm_apply (f : ∀ i, A →ₐ[k] R i) :
    (piHomeomorph k A R).symm f = AlgHom.pi f :=
  AlgHom.piEquiv_symm_apply f

end Pi

section BialgebraProd

variable {k H R₁ R₂ : Type*} [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁]
  [CommSemiring R₂] [Algebra k R₂] [TopologicalSpace R₂]

variable (k H R₁ R₂) in
/-- Points with values in a product `R₁ × R₂` of coefficient algebras are pairs of points, as
topological monoids for the convolution product and the point topology: a point is sent to its
images under the two projections, and a pair of points `(x, y)` to the point `h ↦ (x h, y h)`.
For a Hopf algebra `H` this is the isomorphism of topological groups `G(R₁ × R₂) ≃ G(R₁) × G(R₂)`.
-/
noncomputable def prodContinuousMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toFun x := (AlgHom.mapValue (AlgHom.fst k R₁ R₂) x, AlgHom.mapValue (AlgHom.snd k R₁ R₂) x)
  invFun p := toConv (p.1.ofConv.prod p.2.ofConv)
  left_inv x := by
    simp only [AlgHom.mapValue_apply, ofConv_toConv, ← AlgHom.prod_comp, AlgHom.prod_fst_snd,
      AlgHom.id_comp, toConv_ofConv]
  right_inv p := by
    simp only [AlgHom.mapValue_apply, AlgHom.fst_prod, AlgHom.snd_prod, toConv_ofConv]
  map_mul' x y := by
    simp only [map_mul, Prod.mk_mul_mk]
  continuous_toFun :=
    (AlgHom.continuous_mapValue continuous_fst).prodMk (AlgHom.continuous_mapValue continuous_snd)
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    ((continuous_eval_ofConv h).comp continuous_fst).prodMk
      ((continuous_eval_ofConv h).comp continuous_snd)

@[simp]
theorem prodContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] R₁ × R₂)) :
    prodContinuousMulEquiv k H R₁ R₂ x =
      (AlgHom.mapValue (AlgHom.fst k R₁ R₂) x, AlgHom.mapValue (AlgHom.snd k R₁ R₂) x) :=
  (rfl)

/-- The point paired from `(x, y)` takes the value `(x h, y h)` at `h`. -/
@[simp]
theorem prodContinuousMulEquiv_symm_apply_apply
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) (h : H) :
    (prodContinuousMulEquiv k H R₁ R₂).symm p h = (p.1 h, p.2 h) :=
  (rfl)

end BialgebraProd

section BialgebraPi

variable (k H : Type*) {ι : Type*} (R : ι → Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)] [∀ i, TopologicalSpace (R i)]

/-- Convolution points of a bialgebra `H` valued in `∀ i, R i`, with the point topology, are
isomorphic as topological monoids (and topological groups when `H` is a Hopf algebra) to
`∀ i, WithConv (H →ₐ[k] R i)`. -/
noncomputable def piPointsContinuousMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃ₜ* ∀ i, WithConv (H →ₐ[k] R i) where
  toMulEquiv := AlgHom.piValueMulEquiv
  continuous_toFun := continuous_pi fun i ↦
    (AlgHom.continuous_mapValue (ψ := Pi.evalAlgHom k R i) (continuous_apply i)).congr fun x ↦
      WithConv.ofConv_injective <| AlgHom.ext fun h ↦ by simp
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    (continuous_pi fun i ↦ (continuous_eval_ofConv h).comp (continuous_apply i)).congr fun f ↦
      funext fun i ↦ (AlgHom.piValueMulEquiv_symm_apply f h i).symm

variable {k H R}

/-- Evaluating `piPointsContinuousMulEquiv k H R x` at `i` applies `AlgHom.mapValue`. -/
@[simp]
theorem piPointsContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) :
    piPointsContinuousMulEquiv k H R x i = AlgHom.mapValue (Pi.evalAlgHom k R i) x :=
  WithConv.ofConv_injective <| AlgHom.ext fun h ↦ by simp [piPointsContinuousMulEquiv]

/-- Evaluating `(piPointsContinuousMulEquiv k H R).symm f` on `h : H` at `i` gives
`(f i).ofConv h`. -/
@[simp]
theorem piPointsContinuousMulEquiv_symm_apply_ofConv
    (f : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piPointsContinuousMulEquiv k H R).symm f).ofConv h i = (f i).ofConv h := by
  have hs : (piPointsContinuousMulEquiv k H R).symm f = AlgHom.piValueMulEquiv.symm f := rfl
  rw [hs, AlgHom.piValueMulEquiv_symm_apply]

end BialgebraPi

end TauCeti.PointTopology
