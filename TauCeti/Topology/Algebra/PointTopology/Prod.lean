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
For a `k`-bialgebra `H`, conjugating by `WithConv.ofConv` upgrades `AlgHom.prodPointsMulEquiv` and
`AlgHom.piPointsMulEquiv` to topological multiplicative equivalences
`prodPointsContinuousMulEquiv` and `piPointsContinuousMulEquiv`.

## Main declarations

* `TauCeti.PointTopology.prodHomeomorph`, `TauCeti.PointTopology.piHomeomorph`
* `TauCeti.PointTopology.prodPointsContinuousMulEquiv`,
  `TauCeti.PointTopology.piPointsContinuousMulEquiv`

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, pp. 2–3, and §3, p. 4.
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

variable (k H R S : Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R] [Algebra k R] [TopologicalSpace R]
  [CommSemiring S] [Algebra k S] [TopologicalSpace S]

/-- Convolution points of a bialgebra `H` valued in `R × S`, with the point topology, are isomorphic
as topological monoids (and topological groups when `H` is a Hopf algebra) to the product of factor
convolution point spaces. -/
noncomputable def prodPointsContinuousMulEquiv :
    WithConv (H →ₐ[k] R × S) ≃ₜ* WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] S) where
  toMulEquiv := AlgHom.prodPointsMulEquiv
  continuous_toFun :=
    ((AlgHom.continuous_mapValue (ψ := AlgHom.fst k R S) continuous_fst).prodMk
      (AlgHom.continuous_mapValue (ψ := AlgHom.snd k R S) continuous_snd)).congr fun _ ↦
        Prod.ext (AlgHom.prodPointsMulEquiv_apply_fst _).symm
          (AlgHom.prodPointsMulEquiv_apply_snd _).symm
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    (((continuous_eval_ofConv h).comp continuous_fst).prodMk
      ((continuous_eval_ofConv h).comp continuous_snd)).congr fun p ↦
        (AlgHom.prodPointsMulEquiv_symm_apply_ofConv p h).symm

variable {k H R S}

/-- The underlying `MulEquiv` of `prodPointsContinuousMulEquiv` is `AlgHom.prodPointsMulEquiv`. -/
@[simp]
theorem coe_prodPointsContinuousMulEquiv :
    (prodPointsContinuousMulEquiv k H R S :
      WithConv (H →ₐ[k] R × S) ≃* WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] S)) =
      AlgHom.prodPointsMulEquiv := (rfl)

/-- The forward map of `prodPointsContinuousMulEquiv` is `AlgHom.prodPointsMulEquiv`. -/
@[simp]
theorem prodPointsContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] R × S)) :
    prodPointsContinuousMulEquiv k H R S x = AlgHom.prodPointsMulEquiv x := (rfl)

/-- The inverse of `prodPointsContinuousMulEquiv` is `AlgHom.prodPointsMulEquiv.symm`. -/
@[simp]
theorem prodPointsContinuousMulEquiv_symm_apply
    (p : WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] S)) :
    (prodPointsContinuousMulEquiv k H R S).symm p = AlgHom.prodPointsMulEquiv.symm p := (rfl)

end BialgebraProd

section BialgebraPi

variable (k H : Type*) {ι : Type*} (R : ι → Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)] [∀ i, TopologicalSpace (R i)]

/-- Convolution points of a bialgebra `H` valued in `∀ i, R i`, with the point topology, are
isomorphic as topological monoids (and topological groups when `H` is a Hopf algebra) to
`∀ i, WithConv (H →ₐ[k] R i)`. -/
noncomputable def piPointsContinuousMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃ₜ* ∀ i, WithConv (H →ₐ[k] R i) where
  toMulEquiv := AlgHom.piPointsMulEquiv
  continuous_toFun := continuous_pi fun i ↦
    (AlgHom.continuous_mapValue (ψ := Pi.evalAlgHom k R i) (continuous_apply i)).congr
      fun x ↦ (AlgHom.piPointsMulEquiv_apply x i).symm
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    (continuous_pi fun i ↦ (continuous_eval_ofConv h).comp (continuous_apply i)).congr fun f ↦
      funext fun i ↦ (AlgHom.piPointsMulEquiv_symm_apply_ofConv f h i).symm

variable {k H R}

/-- Evaluating `piPointsContinuousMulEquiv k H R x` at `i` applies `AlgHom.mapValue`. -/
@[simp]
theorem piPointsContinuousMulEquiv_apply (x : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) :
    piPointsContinuousMulEquiv k H R x i = AlgHom.mapValue (Pi.evalAlgHom k R i) x :=
  AlgHom.piPointsMulEquiv_apply x i

/-- Evaluating `(piPointsContinuousMulEquiv k H R).symm f` on `h : H` at `i` gives
`(f i).ofConv h`. -/
@[simp]
theorem piPointsContinuousMulEquiv_symm_apply_ofConv
    (f : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piPointsContinuousMulEquiv k H R).symm f).ofConv h i = (f i).ofConv h :=
  AlgHom.piPointsMulEquiv_symm_apply_ofConv f h i

end BialgebraPi

end TauCeti.PointTopology
