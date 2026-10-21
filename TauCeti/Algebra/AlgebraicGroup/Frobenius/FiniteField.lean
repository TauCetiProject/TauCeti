/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Frobenius.Points
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.CharP.Frobenius.Bialgebra
public import TauCeti.FieldTheory.Finite.FrobeniusFixed
public import TauCeti.GroupTheory.FixedSubgroup
public import TauCeti.RingTheory.FiniteType.AlgHom

/-!
# The `q`-Frobenius of an affine group over a finite field

Let `K` be a finite field with `q` elements and let `H` be a commutative Hopf algebra over `K`,
the coordinate ring of an affine group `G₀` over `K`. Nothing here asks `G₀` to be split, or to
come from a model over `ℤ`: `H` is an arbitrary `K`-form.

On points with values in a commutative `K`-algebra `A`, the `q`-Frobenius raises every coordinate
to its `q`-th power. It is post-composition with the Frobenius `K`-algebra endomorphism of `A`
(`frobeniusPoints`), and also pre-composition with the Frobenius bialgebra endomorphism of `H`;
these agree because a `K`-algebra map commutes with `q`-th powers. It is natural in the value
algebra and in the coordinate bialgebra.

For a commutative `K`-algebra `k`, the *geometric Frobenius* of the base change
`G = G₀ ×_K k` is the `k`-bialgebra endomorphism `id ⊗ Frob` of `k ⊗[K] H`
(`geometricFrobeniusBialgHom`), the scalar extension of the `q`-power map on `H`. It is not the
`q`-power map of `k ⊗[K] H`, which is not `k`-linear. Under the base-change identification
`G(R) ≃ Hom_K(H, R)` it becomes `frobeniusPoints`.

When the value algebra `L` is a domain, the points of `G₀` fixed by the `q`-Frobenius are exactly
the `K`-rational points. So for `k` an algebraic closure of `K`, `G^F ≃ G₀(K)`, and this group is
finite when `H` is of finite type. Closed subgroups of `G₀` are automatically stable under the
Frobenius, and their fixed points are their points inside `G^F`.

## Main declarations

* `TauCeti.Bialgebra.frobeniusPoints`: the `q`-Frobenius on `A`-valued points.
* `TauCeti.Bialgebra.mapDomain_frobeniusBialgHom`: it is pre-composition with the Frobenius
  bialgebra endomorphism of the coordinate algebra.
* `TauCeti.Bialgebra.mapValue_comp_frobeniusPoints` and
  `TauCeti.Bialgebra.mapDomain_comp_frobeniusPoints`: naturality in both arguments.
* `TauCeti.Bialgebra.geometricFrobeniusBialgHom`: the geometric Frobenius of a base change.
* `TauCeti.Bialgebra.baseChangePointsMulEquiv_symm_comp_mapDomain_geometricFrobeniusBialgHom`:
  base change identifies the geometric Frobenius with `frobeniusPoints`.
* `TauCeti.Bialgebra.fixedSubgroup_frobeniusPoints_eq_range`: over a domain, the Frobenius-fixed
  points are the rational points.
* `TauCeti.Bialgebra.rationalPointsMulEquivFixedSubgroup` and
  `TauCeti.Bialgebra.rationalPointsMulEquivFixedSubgroupGeometricFrobenius`: `G₀(K) ≃ G^F`.
* `TauCeti.Bialgebra.mapDomain_rationalPointsMulEquivFixedSubgroupGeometricFrobenius`: that
  isomorphism is natural in the coordinate Hopf algebra.
* `TauCeti.Bialgebra.finite_fixedSubgroup_frobeniusPoints` and
  `TauCeti.Bialgebra.finite_fixedSubgroup_geometricFrobenius`: `G^F` is finite.
* `TauCeti.Bialgebra.map_fixedSubgroup_frobeniusPoints_of_surjective`: the fixed points of a closed
  subgroup are its points that are fixed in the ambient group.
* `TauCeti.Bialgebra.baseChangePointsMulEquiv_symm_frobeniusPoints`: for a model over `ℤ`, the
  `q`-Frobenius is the iterated prime-power Frobenius `iterateFrobeniusPoints`.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* F. Digne and J. Michel, *Representations of Finite Groups of Lie Type*, 2nd ed., §4.1.
-/

public section

open WithConv TensorProduct

namespace TauCeti

namespace Bialgebra

variable (K : Type*) [Field K] [Fintype K]

/-! ### The `q`-Frobenius on points -/

section Points

variable {H : Type*} [Semiring H] [_root_.Bialgebra K H]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- The `q`-Frobenius on the monoid of `A`-valued points of a bialgebra `H` over a finite field
`K` with `q` elements: it raises every value of a point to its `q`-th power. -/
noncomputable def frobeniusPoints : WithConv (H →ₐ[K] A) →* WithConv (H →ₐ[K] A) :=
  AlgHom.mapValue (FiniteField.frobeniusAlgHom K A)

/-- Pointwise, the `q`-Frobenius raises the value of a point to its `q`-th power. -/
@[simp]
theorem frobeniusPoints_apply_apply (f : WithConv (H →ₐ[K] A)) (h : H) :
    (frobeniusPoints K f).ofConv h = f.ofConv h ^ Fintype.card K := by
  rw [frobeniusPoints, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    FiniteField.coe_frobeniusAlgHom]

variable {B : Type*} [CommRing B] [Algebra K B]

/-- The `q`-Frobenius is natural in the value algebra. -/
theorem mapValue_comp_frobeniusPoints (φ : A →ₐ[K] B) :
    (AlgHom.mapValue (H := H) φ).comp (frobeniusPoints K (H := H) (A := A)) =
      (frobeniusPoints K (H := H) (A := B)).comp (AlgHom.mapValue (H := H) φ) := by
  ext f h
  simp

variable {H' : Type*} [Semiring H'] [_root_.Bialgebra K H']

/-- The `q`-Frobenius is natural in the coordinate bialgebra: it commutes with the map on points
induced by any bialgebra morphism. -/
theorem mapDomain_comp_frobeniusPoints (ψ : H →ₐc[K] H') :
    (BialgHom.mapDomain (A := A) ψ).comp (frobeniusPoints K (H := H') (A := A)) =
      (frobeniusPoints K (H := H) (A := A)).comp (BialgHom.mapDomain (A := A) ψ) := by
  ext f h
  simp

end Points

section Commutative

variable {H : Type*} [CommSemiring H] [_root_.Bialgebra K H]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- The `q`-Frobenius on points is pre-composition with the Frobenius bialgebra endomorphism
`x ↦ x ^ q` of the coordinate algebra. -/
theorem mapDomain_frobeniusBialgHom :
    BialgHom.mapDomain (A := A) (frobeniusBialgHom K H) = frobeniusPoints K := by
  ext f h
  simp

end Commutative

/-! ### The geometric Frobenius of a base change -/

section Geometric

variable (k : Type*) [CommSemiring k] [Algebra K k]
variable (H : Type*) [CommSemiring H] [_root_.Bialgebra K H]

/-- The geometric Frobenius of the base change `Spec (k ⊗[K] H)` of an affine monoid over a finite
field `K`: the scalar extension `id ⊗ Frob` of the `q`-power bialgebra endomorphism of `H`. -/
noncomputable def geometricFrobeniusBialgHom : k ⊗[K] H →ₐc[k] k ⊗[K] H :=
  _root_.Bialgebra.TensorProduct.map (BialgHom.id k k) (frobeniusBialgHom K H)

/-- On pure tensors, the geometric Frobenius raises the second factor to its `q`-th power. -/
@[simp]
theorem geometricFrobeniusBialgHom_tmul (s : k) (h : H) :
    geometricFrobeniusBialgHom K k H (s ⊗ₜ h) = s ⊗ₜ (h ^ Fintype.card K) := by
  simp [geometricFrobeniusBialgHom]

variable {k H}
variable {R : Type*} [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower K k R]

/-- **Base change identifies the geometric Frobenius with the `q`-Frobenius on points.** Under
`G(R) ≃ Hom_K(H, R)`, the map on points induced by the geometric Frobenius of `k ⊗[K] H` is
`frobeniusPoints`. -/
theorem baseChangePointsMulEquiv_symm_comp_mapDomain_geometricFrobeniusBialgHom :
    ((AlgHom.baseChangePointsMulEquiv (k := K) (K := k) (A := H) (R := R)).symm :
        WithConv (k ⊗[K] H →ₐ[k] R) →* WithConv (H →ₐ[K] R)).comp
      (BialgHom.mapDomain (A := R) (geometricFrobeniusBialgHom K k H)) =
    (frobeniusPoints K).comp
      ((AlgHom.baseChangePointsMulEquiv (k := K) (K := k) (A := H) (R := R)).symm :
        WithConv (k ⊗[K] H →ₐ[k] R) →* WithConv (H →ₐ[K] R)) := by
  ext f : 1
  exact (BialgHom.baseChangePointsMulEquiv_symm_mapDomain (frobeniusBialgHom K H) f).trans
    (DFunLike.congr_fun (mapDomain_frobeniusBialgHom K) _)

end Geometric

/-! ### Closed subgroups -/

section ClosedSubgroup

variable {H H' : Type*} [Semiring H] [HopfAlgebra K H] [Semiring H'] [HopfAlgebra K H']
variable {A : Type*} [CommRing A] [Algebra K A]

/-- **Frobenius-fixed points of a closed subgroup.** For a surjective bialgebra morphism
`ψ : H → H'`, cutting out a closed subgroup of `Spec H`, the points of that subgroup fixed by its
own `q`-Frobenius are exactly its points that are fixed in the ambient group. -/
theorem map_fixedSubgroup_frobeniusPoints_of_surjective (ψ : H →ₐc[K] H')
    (hψ : Function.Surjective ψ) :
    (fixedSubgroup (frobeniusPoints K (H := H') (A := A))).map (BialgHom.mapDomain ψ) =
      (BialgHom.mapDomain (A := A) ψ).range ⊓ fixedSubgroup (frobeniusPoints K) :=
  (BialgHom.mapDomain ψ).map_fixedSubgroup_of_injective (mapDomain_comp_frobeniusPoints K ψ)
    (BialgHom.mapDomain_injective_of_surjective ψ hψ)

end ClosedSubgroup

/-! ### Frobenius-fixed points are rational points -/

section Fixed

variable {H : Type*} [Semiring H] [HopfAlgebra K H]
variable (L : Type*) [CommRing L] [IsDomain L] [Algebra K L]

/-- **Over a domain, the points fixed by the `q`-Frobenius are exactly the `K`-rational points**,
viewed as `L`-valued points along `K → L`. -/
theorem fixedSubgroup_frobeniusPoints_eq_range :
    fixedSubgroup (frobeniusPoints K (H := H) (A := L)) =
      (AlgHom.mapValue (H := H) (Algebra.ofId K L)).range := by
  ext f
  rw [mem_fixedSubgroup, MonoidHom.mem_range]
  constructor
  · intro hf
    have hmem (h : H) : f.ofConv h ∈ (⊥ : Subalgebra K L) := by
      rw [Algebra.mem_bot, ← FiniteField.pow_card_eq_self_iff_mem_range_algebraMap,
        ← frobeniusPoints_apply_apply, hf]
    refine ⟨toConv ((Algebra.botEquiv K L).toAlgHom.comp (f.ofConv.codRestrict ⊥ hmem)), ?_⟩
    ext h
    have hy := (Algebra.botEquiv K L).symm_apply_apply (f.ofConv.codRestrict ⊥ hmem h)
    rw [Algebra.botEquiv_symm_apply] at hy
    simpa using congrArg Subtype.val hy
  · rintro ⟨g, rfl⟩
    ext h
    simp [AlgHom.mapValue_apply]

/-- The `K`-rational points of `H` are isomorphic to the points fixed by the `q`-Frobenius over any
domain `L`. -/
noncomputable def rationalPointsMulEquivFixedSubgroup :
    WithConv (H →ₐ[K] K) ≃* fixedSubgroup (frobeniusPoints K (H := H) (A := L)) :=
  (MonoidHom.ofInjective (AlgHom.mapValue_injective (H := H)
    (algebraMap K L).injective)).trans
    (MulEquiv.subgroupCongr (fixedSubgroup_frobeniusPoints_eq_range K L).symm)

/-- The isomorphism `rationalPointsMulEquivFixedSubgroup` reads a rational point as an `L`-valued
point along `K → L`. -/
@[simp]
theorem coe_rationalPointsMulEquivFixedSubgroup_apply (g : WithConv (H →ₐ[K] K)) :
    (rationalPointsMulEquivFixedSubgroup K L g : WithConv (H →ₐ[K] L)) =
      AlgHom.mapValue (Algebra.ofId K L) g := by
  ext h
  simp [rationalPointsMulEquivFixedSubgroup, MonoidHom.ofInjective_apply]

/-- **The Frobenius-fixed points over a domain form a finite group** when the coordinate algebra
is of finite type. -/
theorem finite_fixedSubgroup_frobeniusPoints [Algebra.FiniteType K H] :
    Finite (fixedSubgroup (frobeniusPoints K (H := H) (A := L))) :=
  have : Finite (WithConv (H →ₐ[K] K)) := .of_equiv _ (WithConv.equiv _).symm
  .of_equiv _ (rationalPointsMulEquivFixedSubgroup K L).toEquiv

end Fixed

section GeometricFixed

variable (k : Type*) [CommRing k] [IsDomain k] [Algebra K k]
variable (H : Type*) [CommSemiring H] [HopfAlgebra K H]

/-- **`G₀(K) ≃ G^F`.** The `K`-rational points of `H` are isomorphic to the points of the base
change `k ⊗[K] H` over a domain `k` fixed by the geometric Frobenius. The isomorphism sends a
rational point `g` to `s ⊗ h ↦ s * g h`. -/
noncomputable def rationalPointsMulEquivFixedSubgroupGeometricFrobenius :
    WithConv (H →ₐ[K] K) ≃*
      fixedSubgroup (BialgHom.mapDomain (A := k) (geometricFrobeniusBialgHom K k H)) :=
  (rationalPointsMulEquivFixedSubgroup K k).trans
    (fixedSubgroupCongr (AlgHom.baseChangePointsMulEquiv (k := K) (K := k) (A := H) (R := k)).symm
      (baseChangePointsMulEquiv_symm_comp_mapDomain_geometricFrobeniusBialgHom K)).symm

/-- The isomorphism `rationalPointsMulEquivFixedSubgroupGeometricFrobenius` is the base change of
rational points. -/
@[simp]
theorem coe_rationalPointsMulEquivFixedSubgroupGeometricFrobenius_apply
    (g : WithConv (H →ₐ[K] K)) :
    (rationalPointsMulEquivFixedSubgroupGeometricFrobenius K k H g :
        WithConv (k ⊗[K] H →ₐ[k] k)) = AlgHom.pointsBaseChange k g := by
  apply ofConv_injective
  ext h
  simp [rationalPointsMulEquivFixedSubgroupGeometricFrobenius]

variable {H} {H' : Type*} [CommSemiring H'] [HopfAlgebra K H'] in
/-- The isomorphism `G₀(K) ≃ G^F` is natural in the coordinate Hopf algebra: for a morphism
`ψ : H → H'`, the induced map on rational points corresponds to the map on Frobenius-fixed points
induced by the scalar extension of `ψ`. -/
theorem mapDomain_rationalPointsMulEquivFixedSubgroupGeometricFrobenius (ψ : H →ₐc[K] H')
    (g : WithConv (H' →ₐ[K] K)) :
    BialgHom.mapDomain (A := k) (_root_.Bialgebra.TensorProduct.map (BialgHom.id k k) ψ)
        (rationalPointsMulEquivFixedSubgroupGeometricFrobenius K k H' g) =
      rationalPointsMulEquivFixedSubgroupGeometricFrobenius K k H (BialgHom.mapDomain ψ g) := by
  rw [coe_rationalPointsMulEquivFixedSubgroupGeometricFrobenius_apply,
    coe_rationalPointsMulEquivFixedSubgroupGeometricFrobenius_apply,
    BialgHom.mapDomain_pointsBaseChange]

/-- **The fixed points of the geometric Frobenius form a finite group** when the coordinate algebra
is of finite type. -/
theorem finite_fixedSubgroup_geometricFrobenius [Algebra.FiniteType K H] :
    Finite (fixedSubgroup (BialgHom.mapDomain (A := k) (geometricFrobeniusBialgHom K k H))) :=
  have : Finite (WithConv (H →ₐ[K] K)) := .of_equiv _ (WithConv.equiv _).symm
  .of_equiv _ (rationalPointsMulEquivFixedSubgroupGeometricFrobenius K k H).toEquiv

end GeometricFixed

/-! ### Comparison with a model over `ℤ` -/

section Integral

variable {K} {p n : ℕ}
variable {H : Type*} [Semiring H] [_root_.Bialgebra ℤ H]
variable {A : Type*} [CommRing A] [Algebra K A] [ExpChar A p]

/-- **For a model over `ℤ`, the `q`-Frobenius is the iterated prime-power Frobenius.** If
`q = p ^ n`, then under `(K ⊗ H)(A) ≃ Hom_ℤ(H, A)` the `q`-Frobenius of the base change `K ⊗[ℤ] H`
is `iterateFrobeniusPoints p n`. -/
theorem baseChangePointsMulEquiv_symm_frobeniusPoints (hq : Fintype.card K = p ^ n)
    (f : WithConv (K ⊗[ℤ] H →ₐ[K] A)) :
    (AlgHom.baseChangePointsMulEquiv (k := ℤ) (K := K) (A := H) (R := A)).symm
        (frobeniusPoints K f) =
      iterateFrobeniusPoints p n
        ((AlgHom.baseChangePointsMulEquiv (k := ℤ) (K := K) (A := H) (R := A)).symm f) := by
  ext h
  simp [hq]

end Integral

end Bialgebra

end TauCeti
