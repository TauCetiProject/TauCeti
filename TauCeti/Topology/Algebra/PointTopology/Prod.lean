/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.Algebra.Pi.Basic
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Point spaces and convolution groups over products of coefficient algebras

For a `k`-algebra `A` and topological `k`-algebras, the point topology on `A →ₐ[k] R × S` and
`A →ₐ[k] ∀ i, R i` agrees with the product topology (`prodHomeomorph` and `piHomeomorph`), with
coordinates given by post-composition with the coefficient projections.
For a `k`-bialgebra `H`, `TauCeti.PointTopology.prodContinuousMulEquiv` and
`TauCeti.PointTopology.piPointsContinuousMulEquiv` show that the algebraic convolution
equivalences `AlgHom.prodPointsMulEquiv` and `AlgHom.piValueMulEquiv` are homeomorphisms for
the point topology, hence multiplicative homeomorphisms (`≃ₜ*`) with coordinates given by the
coefficient projections (and isomorphisms of topological monoids, or of topological groups when `H`
is a Hopf algebra, whenever the coefficient algebras are topological semirings).

## Main declarations

* `TauCeti.PointTopology.prodHomeomorph`, `TauCeti.PointTopology.piHomeomorph`
* `TauCeti.PointTopology.prodContinuousMulEquiv`: multiplicative homeomorphism between points with
  values in `R₁ × R₂` and pairs of points (an isomorphism of topological monoids, or topological
  groups when `H` is a Hopf algebra, if `R₁` and `R₂` are topological semirings).
* `TauCeti.PointTopology.piPointsContinuousMulEquiv`: multiplicative homeomorphism between
  convolution points valued in `∀ i, R i` and `∀ i, WithConv (H →ₐ[k] R i)` (an isomorphism of
  topological monoids, or topological groups when `H` is a Hopf algebra, if each `R i` is a
  topological semiring).

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, §3, and the map (3.6.2) in the proof of Thm. 3.6.
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
  toEquiv := AlgHom.piEquiv.symm
  continuous_toFun := continuous_pi fun i ↦
    (continuous_map_codomain (Pi.evalAlgHom k R i) (continuous_apply i)).congr fun _ ↦ by simp
  continuous_invFun := continuous_iff.2 fun a ↦
    continuous_pi fun i ↦ ((continuous_eval a).comp (continuous_apply i)).congr fun _ ↦ by simp

variable {k A R}

/-- Evaluating `piHomeomorph` at `i` postcomposes with `Pi.evalAlgHom k R i`. -/
@[simp]
theorem piHomeomorph_apply (x : A →ₐ[k] ∀ i, R i) (i : ι) :
    piHomeomorph k A R x i = (Pi.evalAlgHom k R i).comp x :=
  AlgHom.piEquiv_symm_apply x i

/-- The inverse of `piHomeomorph` is `AlgHom.pi`. -/
@[simp]
theorem piHomeomorph_symm_apply (f : ∀ i, A →ₐ[k] R i) :
    (piHomeomorph k A R).symm f = AlgHom.pi f :=
  AlgHom.piEquiv_apply f

end Pi

section BialgebraProd

variable {k H R₁ R₂ : Type*} [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁]
  [CommSemiring R₂] [Algebra k R₂] [TopologicalSpace R₂]

private theorem homeomorph_ofConv_symm_eq_toConv {A R : Type*} [Semiring A] [Algebra k A]
    [Semiring R] [Algebra k R] [TopologicalSpace R] (x : A →ₐ[k] R) :
    (isHomeomorph_ofConv (k := k) (A := A) (R := R)).homeomorph.symm x = toConv x :=
  WithConv.ofConv_injective <| by
    simpa [IsHomeomorph.homeomorph_apply] using
      (isHomeomorph_ofConv (k := k) (A := A) (R := R)).homeomorph.apply_symm_apply x

private noncomputable def prodConvHomeomorph {k H R₁ R₂ : Type*} [CommSemiring k] [Semiring H]
    [Bialgebra k H] [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁] [CommSemiring R₂]
    [Algebra k R₂] [TopologicalSpace R₂] :
    WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) :=
  (isHomeomorph_ofConv.homeomorph).trans ((prodHomeomorph k H R₁ R₂).trans
    ((isHomeomorph_ofConv.homeomorph).symm.prodCongr (isHomeomorph_ofConv.homeomorph).symm))

private theorem prodConvHomeomorph_eq {k H R₁ R₂ : Type*} [CommSemiring k] [Semiring H]
    [Bialgebra k H] [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁] [CommSemiring R₂]
    [Algebra k R₂] [TopologicalSpace R₂] (x : WithConv (H →ₐ[k] R₁ × R₂)) :
    prodConvHomeomorph x = AlgHom.prodPointsMulEquiv x := by
  refine Prod.ext (WithConv.ofConv_injective <| AlgHom.ext fun h ↦ ?_)
    (WithConv.ofConv_injective <| AlgHom.ext fun h ↦ ?_)
  · simp only [prodConvHomeomorph, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
      IsHomeomorph.homeomorph_apply, Prod.map_fst, prodHomeomorph_apply_fst]
    rw [homeomorph_ofConv_symm_eq_toConv]
    simp
  · simp only [prodConvHomeomorph, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
      IsHomeomorph.homeomorph_apply, Prod.map_snd, prodHomeomorph_apply_snd]
    rw [homeomorph_ofConv_symm_eq_toConv]
    simp

variable (k H R₁ R₂) in
/-- Multiplicative homeomorphism identifying points valued in `R₁ × R₂` with pairs of points via
the two projections, and sending `(x, y)` to `h ↦ (x h, y h)`. When `R₁` and `R₂` are topological
semirings, this is an isomorphism of topological monoids (and of topological groups when `H` is a
Hopf algebra). -/
noncomputable def prodContinuousMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toMulEquiv := AlgHom.prodPointsMulEquiv
  continuous_toFun := prodConvHomeomorph.continuous.congr prodConvHomeomorph_eq
  continuous_invFun := prodConvHomeomorph.symm.continuous.congr fun p ↦ by
    rw [MulEquiv.invFun_eq_symm, Homeomorph.symm_apply_eq, prodConvHomeomorph_eq,
      AlgHom.prodPointsMulEquiv.apply_symm_apply]

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

private noncomputable def piConvHomeomorph :
    WithConv (H →ₐ[k] ∀ i, R i) ≃ₜ ∀ i, WithConv (H →ₐ[k] R i) :=
  (isHomeomorph_ofConv.homeomorph).trans ((piHomeomorph k H R).trans
    (Homeomorph.piCongrRight fun _ ↦ (isHomeomorph_ofConv.homeomorph).symm))

private theorem piConvHomeomorph_eq (x : WithConv (H →ₐ[k] ∀ i, R i)) :
    piConvHomeomorph k H R x = AlgHom.piValueMulEquiv x := by
  ext i h
  simp only [piConvHomeomorph, Homeomorph.trans_apply, Homeomorph.piCongrRight_apply,
    IsHomeomorph.homeomorph_apply, piHomeomorph_apply]
  rw [homeomorph_ofConv_symm_eq_toConv]
  simp

/-- Multiplicative homeomorphism identifying convolution points of a bialgebra `H` valued in
`∀ i, R i`, with the point topology, with `∀ i, WithConv (H →ₐ[k] R i)`. When each `R i` is a
topological semiring, this is an isomorphism of topological monoids (and of topological groups when
`H` is a Hopf algebra). -/
noncomputable def piPointsContinuousMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃ₜ* ∀ i, WithConv (H →ₐ[k] R i) where
  toMulEquiv := AlgHom.piValueMulEquiv
  continuous_toFun := (piConvHomeomorph k H R).continuous.congr (piConvHomeomorph_eq k H R)
  continuous_invFun := (piConvHomeomorph k H R).symm.continuous.congr fun f ↦ by
    rw [MulEquiv.invFun_eq_symm, Homeomorph.symm_apply_eq, piConvHomeomorph_eq,
      AlgHom.piValueMulEquiv.apply_symm_apply]

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
    ((piPointsContinuousMulEquiv k H R).symm f).ofConv h i = (f i).ofConv h :=
  AlgHom.piValueMulEquiv_symm_apply f h i

end BialgebraPi

end TauCeti.PointTopology
