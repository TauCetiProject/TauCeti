/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.AlgebraicGroup.NormTorus.Basic
public import TauCeti.RingTheory.Norm.CharP
public import TauCeti.RingTheory.Norm.NonZeroDivisors

/-!
# Coordinates on the Weil restriction of the multiplicative group

Let `B` be a commutative `A`-algebra with a finite basis `b`. A point of `Res_{B/A} 𝔾ₘ` over a
commutative `A`-algebra `R` is a unit `∑ᵢ bᵢ ⊗ xᵢ` of `B ⊗[A] R`
(`TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints`). An element of `B ⊗[A] R` is a unit
exactly when its norm over `R` is (`Algebra.isUnit_norm_iff`), and this norm is the norm form
`N = Norm(∑ᵢ Xᵢ ⊗ bᵢ) ∈ A[X]` of `B` evaluated at the coordinates `x`. Hence `Res_{B/A} 𝔾ₘ` is the
open complement of the hypersurface `N = 0` in the affine space of `B`:

```text
Res_{B/A} 𝔾ₘ ≅ Spec A[X][1 / N],
```

where `A[X]` is the polynomial ring on the coordinates `Xᵢ`. The isomorphism sends the `i`-th
coefficient of the universal point to `Xᵢ`, and the norm morphism `Res_{B/A} 𝔾ₘ → 𝔾ₘ` becomes `N`
in these coordinates.

Let `k` be a field of characteristic `p` and `B` an algebra with power basis
`1, α, …, α ^ (p - 1)` such that `α ^ p = a ∈ k`, for instance the purely inseparable extension
`K = k(a ^ (1 / p))` when `a` is not a `p`-th power. Then the norm form is the diagonal form
`N = ∑ᵢ aⁱ Xᵢ ^ p` (`PowerBasis.norm_sum_X_tmul_gen_pow`), so

```text
Res_{K/k} 𝔾ₘ ≅ Spec k[X₀, …, X_{p-1}][1 / ∑ᵢ aⁱ Xᵢ ^ p],
```

and the points over `R` are the tuples `x` for which `∑ᵢ aⁱ xᵢ ^ p` is a unit of `R`. Moreover the
`p`-th power of every point is the image of its norm under the diagonal `𝔾ₘ → Res_{K/k} 𝔾ₘ`: the
`p`-th power endomorphism of `Res_{K/k} 𝔾ₘ` factors through the norm to `𝔾ₘ`. The statements
allow any exponential characteristic `p`; in characteristic zero they concern only `B = k`.

## Main declarations

In the namespace `TauCeti.Algebra.WeilRestriction`:

* `isUnit_sum_tmul_iff`: `∑ᵢ bᵢ ⊗ xᵢ` is a unit exactly when `N(x)` is.
* `multiplicativeGroupAlgEquiv`: **`Res_{B/A} 𝔾ₘ ≅ Spec A[X][1 / N]`**, for every localization of
  `A[X]` away from the norm form `N`.
* `multiplicativeGroupPoints_comp_multiplicativeGroupAlgEquiv`: the point attached to a
  homomorphism `g` out of `A[X][1 / N]` is the unit `∑ᵢ bᵢ ⊗ g(Xᵢ)`.
* `multiplicativeGroupAlgEquiv_universalCoefficient`: the `i`-th coefficient of the universal point
  is sent to `Xᵢ`.
* `multiplicativeGroupAlgEquiv_normHom`: the norm morphism `Res_{B/A} 𝔾ₘ → 𝔾ₘ` is the norm form in
  these coordinates.
* `isUnit_sum_gen_pow_tmul_iff`: for `α ^ p = a` in characteristic `p`, `∑ᵢ αⁱ ⊗ xᵢ` is a unit
  exactly when `∑ᵢ aⁱ xᵢ ^ p` is.
* `multiplicativeGroupAlgEquivOfPowerBasis`: **`Res_{K/k} 𝔾ₘ ≅ Spec k[X][1 / ∑ᵢ aⁱ Xᵢ ^ p]`**
  for `K = k(a ^ (1 / p))`.

In the namespace `TauCeti.NormTorus`:

* `pow_char_eq_unitsMap_norm`: in this situation the `p`-th power of a point is the diagonal
  image of its norm.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1 and §A.5.
* J. S. Milne, *Algebraic Groups* (2017), §2.i.
-/

public section

open MvPolynomial WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.Algebra.WeilRestriction

section Coordinates

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
  [Module.Finite A B] {ι : Type*} [Fintype ι] (b : Module.Basis ι A B)

/-- **The coordinates of the universal point.** The universal point of `Res_{B/A} 𝔾ₘ`, a unit of
`B ⊗[A] Res_{B/A} 𝔾ₘ`, is `∑ᵢ bᵢ ⊗ cᵢ`, where `cᵢ` is the universal coefficient of the coordinate
`T` of `𝔾ₘ` extracted by the `i`-th coordinate functional of `b`. -/
theorem sum_tmul_universalCoefficient_T :
    ∑ i, b i ⊗ₜ[A] universalCoefficient (b.coord i) (LaurentPolynomial.T 1 : B[T;T⁻¹]) =
      (multiplicativeGroupPoints A B _ (toConv (AlgHom.id A (WeilRestriction A B B[T;T⁻¹]))) :
        B ⊗[A] WeilRestriction A B B[T;T⁻¹]) := by
  rw [sum_tmul_universalCoefficient, multiplicativeGroupPoints_apply, ofConv_toConv,
    homEquiv_apply, AlgHom.comp_apply]
  simp

variable {A B}

omit [Module.Free A B] [Module.Finite A B] in
/-- The coordinates of `∑ⱼ bⱼ ⊗ xⱼ` are the `xⱼ`. -/
private theorem tensorComponent_comm_sum_tmul {R : Type*} [CommRing R] [Algebra A R]
    (x : ι → R) (i : ι) :
    LinearMap.tensorComponent (b.coord i) (TensorProduct.comm A B R (∑ j, b j ⊗ₜ[A] x j)) =
      x i := by
  classical
  simp [Finsupp.single_apply]

variable (A B) in
/-- **The points of `Res_{B/A} 𝔾ₘ` in coordinates.** For a commutative `A`-algebra `R`, the element
`∑ⱼ bⱼ ⊗ xⱼ` of `B ⊗[A] R` is a unit exactly when the norm form `N = Norm(∑ᵢ Xᵢ ⊗ bᵢ)` of `B` in the
basis `b` takes a unit value `N(x)` of `R`. -/
theorem isUnit_sum_tmul_iff {R : Type*} [CommRing R] [Algebra A R] (x : ι → R) :
    IsUnit (∑ j, b j ⊗ₜ[A] x j) ↔ IsUnit (aeval x
      (Algebra.norm (MvPolynomial ι A) (∑ i, (X i : MvPolynomial ι A) ⊗ₜ[A] b i))) := by
  rw [← TauCeti.Algebra.norm_sum_tmul_eq_aeval, Algebra.isUnit_norm_iff]
  exact ⟨fun h ↦ by simpa using h.map (Algebra.TensorProduct.comm A B R),
    fun h ↦ by simpa using h.map (Algebra.TensorProduct.comm A R B)⟩

variable (L : Type*) [CommRing L] [Algebra A L] [Algebra (MvPolynomial ι A) L]
  [IsScalarTower A (MvPolynomial ι A) L]
  [IsLocalization.Away
    (Algebra.norm (MvPolynomial ι A) (∑ i, (X i : MvPolynomial ι A) ⊗ₜ[A] b i)) L]

/-- The point of `Res_{B/A} 𝔾ₘ` over `A[X][1 / N]` whose coordinates are the variables. -/
private noncomputable def localizationPoint : (B ⊗[A] L)ˣ :=
  ((isUnit_sum_tmul_iff A B b fun i ↦ algebraMap (MvPolynomial ι A) L (X i)).2 <| by
    have : (aeval fun i ↦ algebraMap (MvPolynomial ι A) L (X i)) =
        IsScalarTower.toAlgHom A (MvPolynomial ι A) L := MvPolynomial.algHom_ext fun i ↦ by simp
    rw [this, IsScalarTower.coe_toAlgHom']
    exact IsLocalization.Away.algebraMap_isUnit _).unit

private theorem coe_localizationPoint :
    (localizationPoint (A := A) (B := B) b L : B ⊗[A] L) =
      ∑ i, b i ⊗ₜ[A] algebraMap (MvPolynomial ι A) L (X i) :=
  rfl

/-- The coordinates of the universal point have invertible norm form. -/
private theorem isUnit_aeval_universalCoefficient :
    IsUnit (aeval (fun i ↦ universalCoefficient (b.coord i) (LaurentPolynomial.T 1 : B[T;T⁻¹]))
      (Algebra.norm (MvPolynomial ι A) (∑ i, (X i : MvPolynomial ι A) ⊗ₜ[A] b i))) := by
  refine (isUnit_sum_tmul_iff A B b _).1 ?_
  rw [sum_tmul_universalCoefficient_T]
  exact Units.isUnit _

/-- The homomorphism `Res_{B/A} 𝔾ₘ → A[X][1 / N]` classifying `localizationPoint`. -/
private noncomputable def toLocalization : WeilRestriction A B B[T;T⁻¹] →ₐ[A] L :=
  ((multiplicativeGroupPoints A B L).symm (localizationPoint b L)).ofConv

private theorem multiplicativeGroupPoints_toLocalization :
    multiplicativeGroupPoints A B L (toConv (toLocalization b L)) = localizationPoint b L := by
  rw [toLocalization, toConv_ofConv, MulEquiv.apply_symm_apply]

/-- The homomorphism `A[X][1 / N] → Res_{B/A} 𝔾ₘ` sending `Xᵢ` to the universal coefficients. -/
private noncomputable def ofLocalization : L →ₐ[A] WeilRestriction A B B[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom _ (isUnit_aeval_universalCoefficient b)

private theorem ofLocalization_algebraMap_X (i : ι) :
    ofLocalization b L (algebraMap (MvPolynomial ι A) L (X i)) =
      universalCoefficient (b.coord i) (LaurentPolynomial.T 1 : B[T;T⁻¹]) := by
  rw [ofLocalization, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact aeval_X _ i

private theorem toLocalization_comp_ofLocalization :
    (toLocalization b L).comp (ofLocalization b L) = AlgHom.id A L := by
  -- both sides fix the variables `Xᵢ`, the coordinates of `localizationPoint`
  refine IsLocalization.algHom_ext (Submonoid.powers
    (Algebra.norm (MvPolynomial ι A) (∑ i, (X i : MvPolynomial ι A) ⊗ₜ[A] b i))) ?_
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  have key : toLocalization b L (ofLocalization b L (algebraMap (MvPolynomial ι A) L (X i))) =
      algebraMap (MvPolynomial ι A) L (X i) := by
    rw [ofLocalization_algebraMap_X, map_universalCoefficient, ← multiplicativeGroupPoints_apply,
      multiplicativeGroupPoints_toLocalization, coe_localizationPoint,
      tensorComponent_comm_sum_tmul]
  exact key

private theorem ofLocalization_comp_toLocalization :
    (ofLocalization b L).comp (toLocalization b L) = AlgHom.id A _ := by
  -- both sides classify the universal point
  refine toConv_injective ((multiplicativeGroupPoints A B _).injective (Units.ext ?_))
  rw [toLocalization, multiplicativeGroupPoints_naturality, MulEquiv.apply_symm_apply,
    Units.coe_map, MonoidHom.coe_ofClass, coe_localizationPoint,
    ← sum_tmul_universalCoefficient_T A B b]
  simp [ofLocalization_algebraMap_X]

variable (A B)

/-- **The Weil restriction of `𝔾ₘ` in coordinates.** For a commutative `A`-algebra `B` with a finite
basis `b`, `Res_{B/A} 𝔾ₘ` is the open subscheme `Spec A[X][1 / N]` of the affine space of `B`, where
`N = Norm(∑ᵢ Xᵢ ⊗ bᵢ)` is the norm form of `B` in the basis `b`. Here `L` is any localization of
`A[X]` away from `N`. The isomorphism sends the `i`-th universal coefficient of the universal point
to `Xᵢ` (`multiplicativeGroupAlgEquiv_universalCoefficient`). -/
noncomputable def multiplicativeGroupAlgEquiv : WeilRestriction A B B[T;T⁻¹] ≃ₐ[A] L :=
  AlgEquiv.ofAlgHom (toLocalization b L) (ofLocalization b L)
    (toLocalization_comp_ofLocalization b L) (ofLocalization_comp_toLocalization b L)

/-- The point of `Res_{B/A} 𝔾ₘ` over `A[X][1 / N]` classified by `multiplicativeGroupAlgEquiv` is
the unit `∑ᵢ bᵢ ⊗ Xᵢ`. -/
theorem multiplicativeGroupPoints_multiplicativeGroupAlgEquiv :
    (multiplicativeGroupPoints A B L (toConv (multiplicativeGroupAlgEquiv A B b L).toAlgHom) :
      B ⊗[A] L) = ∑ i, b i ⊗ₜ[A] algebraMap (MvPolynomial ι A) L (X i) := by
  rw [multiplicativeGroupAlgEquiv, AlgEquiv.toAlgHom_ofAlgHom,
    multiplicativeGroupPoints_toLocalization, coe_localizationPoint]

/-- The point of `Res_{B/A} 𝔾ₘ` attached to an `A`-algebra map `g : A[X][1 / N] →ₐ[A] R` is the unit
`∑ᵢ bᵢ ⊗ g(Xᵢ)` of `B ⊗[A] R`. -/
theorem multiplicativeGroupPoints_comp_multiplicativeGroupAlgEquiv {R : Type*} [CommRing R]
    [Algebra A R] (g : L →ₐ[A] R) :
    (multiplicativeGroupPoints A B R
        (toConv (g.comp (multiplicativeGroupAlgEquiv A B b L).toAlgHom)) : B ⊗[A] R) =
      ∑ i, b i ⊗ₜ[A] g (algebraMap (MvPolynomial ι A) L (X i)) := by
  have h := multiplicativeGroupPoints_naturality g
    (toConv (multiplicativeGroupAlgEquiv A B b L).toAlgHom)
  rw [ofConv_toConv] at h
  rw [h, Units.coe_map, MonoidHom.coe_ofClass,
    multiplicativeGroupPoints_multiplicativeGroupAlgEquiv]
  simp

/-- The inverse of `multiplicativeGroupAlgEquiv` sends the variable `Xᵢ` to the `i`-th universal
coefficient of the universal point. -/
@[simp]
theorem multiplicativeGroupAlgEquiv_symm_algebraMap_X (i : ι) :
    (multiplicativeGroupAlgEquiv A B b L).symm (algebraMap (MvPolynomial ι A) L (X i)) =
      universalCoefficient (b.coord i) (LaurentPolynomial.T 1 : B[T;T⁻¹]) :=
  ofLocalization_algebraMap_X b L i

/-- `multiplicativeGroupAlgEquiv` sends the `i`-th universal coefficient of the universal point to
the variable `Xᵢ`. -/
@[simp]
theorem multiplicativeGroupAlgEquiv_universalCoefficient (i : ι) :
    multiplicativeGroupAlgEquiv A B b L
        (universalCoefficient (b.coord i) (LaurentPolynomial.T 1 : B[T;T⁻¹])) =
      algebraMap (MvPolynomial ι A) L (X i) := by
  rw [← multiplicativeGroupAlgEquiv_symm_algebraMap_X A B b L, AlgEquiv.apply_symm_apply]

/-- **The norm morphism in coordinates.** Under `multiplicativeGroupAlgEquiv`, the norm morphism
`Res_{B/A} 𝔾ₘ → 𝔾ₘ` sends the coordinate `T` of `𝔾ₘ` to the norm form
`N = Norm(∑ᵢ Xᵢ ⊗ bᵢ)`. -/
theorem multiplicativeGroupAlgEquiv_normHom :
    multiplicativeGroupAlgEquiv A B b L (NormTorus.normHom A B (LaurentPolynomial.T 1)) =
      algebraMap (MvPolynomial ι A) L
        (Algebra.norm (MvPolynomial ι A) (∑ i, (X i : MvPolynomial ι A) ⊗ₜ[A] b i)) := by
  -- on points, the norm morphism composed with the coordinate isomorphism is the norm of
  -- `∑ᵢ bᵢ ⊗ Xᵢ`, which is the norm form evaluated at the variables
  have h := congrArg Units.val (NormTorus.pointsMulEquiv_comp_normHom (R := L)
    (toConv (multiplicativeGroupAlgEquiv A B b L).toAlgHom))
  rw [NormTorus.coe_norm, multiplicativeGroupPoints_multiplicativeGroupAlgEquiv, map_sum] at h
  simp only [MultiplicativeGroup.pointsMulEquiv_apply, laurentEvalEquiv_symm_apply,
    AlgHom.comp_apply, Algebra.TensorProduct.comm_tmul] at h
  refine h.trans ?_
  rw [TauCeti.Algebra.norm_sum_tmul_eq_aeval]
  have : (aeval fun i ↦ algebraMap (MvPolynomial ι A) L (X i)) =
      IsScalarTower.toAlgHom A (MvPolynomial ι A) L := MvPolynomial.algHom_ext fun i ↦ by simp
  rw [this, IsScalarTower.coe_toAlgHom']

end Coordinates

section PowerBasis

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B] (pb : PowerBasis k B)
  {p : ℕ} [ExpChar k p] {a : k}

/-- **The points of `Res_{K/k} 𝔾ₘ` for `K = k(a ^ (1 / p))`.** If `α ^ p = a` for the generator `α`
of a power basis of rank `p` over a field of exponential characteristic `p`, then over every
commutative `k`-algebra `R` the element `∑ᵢ αⁱ ⊗ xᵢ` of `B ⊗[k] R` is a unit exactly when
`∑ᵢ aⁱ xᵢ ^ p` is a unit of `R`. -/
theorem isUnit_sum_gen_pow_tmul_iff (hdim : pb.dim = p) (hgen : pb.gen ^ p = algebraMap k B a)
    {R : Type*} [CommRing R] [Algebra k R] (x : Fin pb.dim → R) :
    IsUnit (∑ i : Fin pb.dim, (pb.gen ^ (i : ℕ)) ⊗ₜ[k] x i) ↔
      IsUnit (∑ i : Fin pb.dim, a ^ (i : ℕ) • x i ^ p) := by
  have : Module.Free k B := .of_basis pb.basis
  have : Module.Finite k B := .of_basis pb.basis
  have h := isUnit_sum_tmul_iff k B pb.basis x
  simp only [pb.coe_basis] at h
  rw [h, pb.norm_sum_X_tmul_gen_pow hdim hgen]
  simp

variable (k B)

/-- **`Res_{K/k} 𝔾ₘ` in coordinates for `K = k(a ^ (1 / p))`.** If `α ^ p = a` for the generator `α`
of a power basis of rank `p` over a field `k` of exponential characteristic `p`, then
`Res_{B/k} 𝔾ₘ ≅ Spec k[X₀, …, X_{p-1}][1 / ∑ᵢ aⁱ Xᵢ ^ p]`. Here `L` is any localization of the
polynomial ring away from `∑ᵢ aⁱ Xᵢ ^ p`; the variable `Xᵢ` is the coordinate of `αⁱ`. -/
noncomputable def multiplicativeGroupAlgEquivOfPowerBasis [Module.Finite k B] (hdim : pb.dim = p)
    (hgen : pb.gen ^ p = algebraMap k B a)
    (L : Type*) [CommRing L] [Algebra k L] [Algebra (MvPolynomial (Fin pb.dim) k) L]
    [IsScalarTower k (MvPolynomial (Fin pb.dim) k) L]
    [IsLocalization.Away (∑ i : Fin pb.dim, a ^ (i : ℕ) • (X i : MvPolynomial (Fin pb.dim) k) ^ p)
      L] :
    WeilRestriction k B B[T;T⁻¹] ≃ₐ[k] L :=
  have : Module.Free k B := .of_basis pb.basis
  have : IsLocalization.Away (Algebra.norm (MvPolynomial (Fin pb.dim) k)
      (∑ i, (X i : MvPolynomial (Fin pb.dim) k) ⊗ₜ[k] pb.basis i)) L := by
    simp only [pb.coe_basis]
    rwa [pb.norm_sum_X_tmul_gen_pow hdim hgen]
  multiplicativeGroupAlgEquiv k B pb.basis L

end PowerBasis

end TauCeti.Algebra.WeilRestriction

namespace TauCeti.NormTorus

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B] (pb : PowerBasis k B)
  {p : ℕ} [ExpChar k p] {a : k}

/-- **The `p`-th power factors through the norm.** If `α ^ p = a` for the generator `α` of a power
basis of rank `p` over a field of exponential characteristic `p`, then the `p`-th power of every
point `u` of `Res_{B/k} 𝔾ₘ` over a commutative `k`-algebra `R` is the image `1 ⊗ Nm(u)` of its
norm under the diagonal `𝔾ₘ → Res_{B/k} 𝔾ₘ`. -/
theorem pow_char_eq_unitsMap_norm (hdim : pb.dim = p) (hgen : pb.gen ^ p = algebraMap k B a)
    {R : Type*} [CommRing R] [Algebra k R] (u : (B ⊗[k] R)ˣ) :
    u ^ p = Units.map (Algebra.TensorProduct.includeRight : R →ₐ[k] B ⊗[k] R) (norm k B R u) := by
  have : Module.Free k B := .of_basis pb.basis
  have : Module.Finite k B := .of_basis pb.basis
  ext
  apply (Algebra.TensorProduct.comm k B R).injective
  rw [Units.val_pow_eq_pow_val, map_pow, pb.pow_char_eq_algebraMap_norm hdim hgen, Units.coe_map,
    MonoidHom.coe_ofClass, coe_norm, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

end TauCeti.NormTorus
