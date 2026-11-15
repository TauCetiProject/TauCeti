/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Point spaces and convolution groups over products of coefficient algebras

For a `k`-algebra `A`, algebra homomorphisms into `R × S` or `∀ i, R i` correspond to families of
homomorphisms into the factors, and for topological factors the point topology agrees with the
product of the factor point topologies. When the source is a bialgebra `H` over `k` and the factors
are commutative `k`-algebras, this identification respects convolution and upgrades to topological
multiplicative equivalences `TauCeti.PointTopology.prodPointsContinuousMulEquiv` and
`TauCeti.PointTopology.piPointsContinuousMulEquiv` (topological group isomorphisms when `H` is a
Hopf algebra). Applied to `AdeleRing R K = InfiniteAdeleRing K × FiniteAdeleRing R K`, this splits
the adelic points of an affine group into its infinite and finite adelic factors.

## Main declarations

* `AlgHom.piEquiv`: algebra homomorphisms into `∀ i, R i` as families of factor homomorphisms.
* `TauCeti.PointTopology.prodHomeomorph`, `TauCeti.PointTopology.piHomeomorph`: homeomorphisms of
  point spaces over binary and indexed products.
* `AlgHom.prodPointsMulEquiv`, `AlgHom.piPointsMulEquiv`, and their topological upgrades
  `TauCeti.PointTopology.prodPointsContinuousMulEquiv`,
  `TauCeti.PointTopology.piPointsContinuousMulEquiv`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, pp. 2–3, and §3, p. 4.
-/

public section

open Topology WithConv

section AlgHomPi

variable {k A ι : Type*} {R : ι → Type*} [CommSemiring k] [Semiring A] [Algebra k A]
  [∀ i, Semiring (R i)] [∀ i, Algebra k (R i)]

/-- Algebra homomorphisms from `A` into `∀ i, R i` correspond to factor homomorphisms. -/
def AlgHom.piEquiv : (A →ₐ[k] ∀ i, R i) ≃ ∀ i, A →ₐ[k] R i where
  toFun x i := (Pi.evalAlgHom k R i).comp x
  invFun := AlgHom.pi
  left_inv x := by ext a i; rfl
  right_inv f := by ext i a; rfl

/-- Evaluating `AlgHom.piEquiv` at index `i` postcomposes with the `i`-th projection. -/
@[simp]
theorem AlgHom.piEquiv_apply (x : A →ₐ[k] ∀ i, R i) (i : ι) :
    AlgHom.piEquiv x i = (Pi.evalAlgHom k R i).comp x := (rfl)

/-- Evaluating `AlgHom.piEquiv x i` on `a : A` reads off the `i`-th coordinate of `x a`. -/
theorem AlgHom.piEquiv_apply_apply (x : A →ₐ[k] ∀ i, R i) (i : ι) (a : A) :
    AlgHom.piEquiv x i a = x a i := (rfl)

/-- The inverse of `AlgHom.piEquiv` is `AlgHom.pi`. -/
@[simp]
theorem AlgHom.piEquiv_symm_apply (f : ∀ i, A →ₐ[k] R i) :
    AlgHom.piEquiv.symm f = AlgHom.pi f := (rfl)

end AlgHomPi

namespace AlgHom

section BialgebraProd

variable {k H R S T : Type*} [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R] [Algebra k R] [CommSemiring S] [Algebra k S] [CommSemiring T] [Algebra k T]

/-- Convolution points of a bialgebra `H` valued in `R × S` split multiplicatively into `R`-valued
and `S`-valued points via the coordinate projections. -/
noncomputable def prodPointsMulEquiv :
    WithConv (H →ₐ[k] R × S) ≃* WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] S) where
  toFun x := (mapValue (AlgHom.fst k R S) x, mapValue (AlgHom.snd k R S) x)
  invFun p := toConv (p.1.ofConv.prod p.2.ofConv)
  left_inv x := WithConv.ext <| by ext h <;> simp
  right_inv p := by ext h <;> simp
  map_mul' := ((mapValue (H := H) (AlgHom.fst k R S)).prod
    (mapValue (H := H) (AlgHom.snd k R S))).map_mul

/-- The first component of `prodPointsMulEquiv` is induced by `AlgHom.fst`. -/
@[simp]
theorem prodPointsMulEquiv_apply_fst (x : WithConv (H →ₐ[k] R × S)) :
    (prodPointsMulEquiv x).1 = mapValue (AlgHom.fst k R S) x := by delta prodPointsMulEquiv; rfl

/-- The second component of `prodPointsMulEquiv` is induced by `AlgHom.snd`. -/
@[simp]
theorem prodPointsMulEquiv_apply_snd (x : WithConv (H →ₐ[k] R × S)) :
    (prodPointsMulEquiv x).2 = mapValue (AlgHom.snd k R S) x := by delta prodPointsMulEquiv; rfl

/-- The inverse of `prodPointsMulEquiv` assembles two factor points via `AlgHom.prod`. -/
@[simp]
theorem ofConv_prodPointsMulEquiv_symm (p : WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] S)) :
    ((prodPointsMulEquiv (k := k) (H := H) (R := R) (S := S)).symm p).ofConv =
      p.1.ofConv.prod p.2.ofConv := by delta prodPointsMulEquiv; rfl

/-- Evaluating `prodPointsMulEquiv.symm p` at `h : H` pairs the two factor evaluations. -/
theorem prodPointsMulEquiv_symm_apply_ofConv
    (p : WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] S)) (h : H) :
    ((prodPointsMulEquiv (k := k) (H := H) (R := R) (S := S)).symm p).ofConv h =
      (p.1.ofConv h, p.2.ofConv h) := by delta prodPointsMulEquiv; rfl

/-- Projecting `prodPointsMulEquiv.symm p` onto the first factor recovers `p.1`. -/
theorem mapValue_fst_prodPointsMulEquiv_symm (p : WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] S)) :
    mapValue (AlgHom.fst k R S) (prodPointsMulEquiv.symm p) = p.1 := by
  simpa only [prodPointsMulEquiv_apply_fst] using
    congrArg Prod.fst (prodPointsMulEquiv.apply_symm_apply p)

/-- Projecting `prodPointsMulEquiv.symm p` onto the second factor recovers `p.2`. -/
theorem mapValue_snd_prodPointsMulEquiv_symm (p : WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] S)) :
    mapValue (AlgHom.snd k R S) (prodPointsMulEquiv.symm p) = p.2 := by
  simpa only [prodPointsMulEquiv_apply_snd] using
    congrArg Prod.snd (prodPointsMulEquiv.apply_symm_apply p)

/-- `prodPointsMulEquiv` sends `mapValue (φ.prod ψ) x` to `(mapValue φ x, mapValue ψ x)`. -/
theorem prodPointsMulEquiv_mapValue_prod (φ : T →ₐ[k] R) (ψ : T →ₐ[k] S)
    (x : WithConv (H →ₐ[k] T)) :
    prodPointsMulEquiv (mapValue (φ.prod ψ) x) = (mapValue φ x, mapValue ψ x) := by ext <;> simp

/-- `prodPointsMulEquiv` commutes with precomposition along a bialgebra homomorphism. -/
theorem prodPointsMulEquiv_mapDomain {H' : Type*} [Semiring H'] [Bialgebra k H']
    (φ : H →ₐc[k] H') (x : WithConv (H' →ₐ[k] R × S)) :
    prodPointsMulEquiv (BialgHom.mapDomain φ x) =
      (BialgHom.mapDomain φ (prodPointsMulEquiv x).1,
        BialgHom.mapDomain φ (prodPointsMulEquiv x).2) := by ext <;> simp

end BialgebraProd

section BialgebraPi

variable {k H ι : Type*} {R : ι → Type*} [CommSemiring k] [Semiring H] [Bialgebra k H]
  [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)]

/-- Convolution points of a bialgebra `H` valued in `∀ i, R i` split multiplicatively into families
of `R i`-valued convolution points via `Pi.evalAlgHom`. -/
noncomputable def piPointsMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃* ∀ i, WithConv (H →ₐ[k] R i) where
  toFun x i := mapValue (Pi.evalAlgHom k R i) x
  invFun f := toConv (AlgHom.pi fun i ↦ (f i).ofConv)
  left_inv x := WithConv.ext <| by ext h i; simp
  right_inv f := by ext i h; simp
  map_mul' x y := funext fun i ↦ (mapValue (Pi.evalAlgHom k R i)).map_mul x y

/-- At index `i`, `piPointsMulEquiv` applies `AlgHom.mapValue (Pi.evalAlgHom k R i)`. -/
@[simp]
theorem piPointsMulEquiv_apply (x : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) :
    piPointsMulEquiv x i = mapValue (Pi.evalAlgHom k R i) x := by delta piPointsMulEquiv; rfl

/-- Evaluating `piPointsMulEquiv.symm f` at `h : H` and `i : ι` gives `(f i).ofConv h`. -/
@[simp]
theorem piPointsMulEquiv_symm_apply_ofConv (f : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piPointsMulEquiv (k := k) (H := H) (R := R)).symm f).ofConv h i = (f i).ofConv h := by
  delta piPointsMulEquiv; rfl

end BialgebraPi

end AlgHom

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
    continuous_map_codomain (Pi.evalAlgHom k R i) (continuous_apply i)
  continuous_invFun := continuous_iff.2 fun a ↦
    continuous_pi fun i ↦ (continuous_eval a).comp (continuous_apply i)

variable {k A R}

/-- Evaluating `piHomeomorph` at `i` postcomposes with `Pi.evalAlgHom k R i`. -/
@[simp]
theorem piHomeomorph_apply (x : A →ₐ[k] ∀ i, R i) (i : ι) :
    piHomeomorph k A R x i = (Pi.evalAlgHom k R i).comp x := (rfl)

/-- The inverse of `piHomeomorph` is `AlgHom.pi`. -/
@[simp]
theorem piHomeomorph_symm_apply (f : ∀ i, A →ₐ[k] R i) :
    (piHomeomorph k A R).symm f = AlgHom.pi f := (rfl)

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
  continuous_toFun := ((AlgHom.continuous_mapValue continuous_fst).prodMk
    (AlgHom.continuous_mapValue continuous_snd)).congr fun x ↦ by
      rw [MulEquiv.toFun_eq_coe]
      exact Prod.ext (AlgHom.prodPointsMulEquiv_apply_fst x).symm
        (AlgHom.prodPointsMulEquiv_apply_snd x).symm
  continuous_invFun := continuous_withConv_iff.2 fun h ↦ by
    simpa only [MulEquiv.invFun_eq_symm, AlgHom.prodPointsMulEquiv_symm_apply_ofConv,
      Function.comp_apply] using ((continuous_eval_ofConv h).comp continuous_fst).prodMk
        ((continuous_eval_ofConv h).comp continuous_snd)

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
  continuous_toFun :=
    (continuous_pi fun i ↦ AlgHom.continuous_mapValue (continuous_apply i)).congr fun x ↦ by
      rw [MulEquiv.toFun_eq_coe]
      exact funext fun i ↦ (AlgHom.piPointsMulEquiv_apply x i).symm
  continuous_invFun := continuous_withConv_iff.2 fun h ↦
    continuous_pi fun i ↦
      ((continuous_eval_ofConv h).comp (continuous_apply i)).congr fun f ↦
        (AlgHom.piPointsMulEquiv_symm_apply_ofConv f h i).symm

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
