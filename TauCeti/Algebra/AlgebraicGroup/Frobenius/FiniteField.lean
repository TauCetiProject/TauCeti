/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.CharP.Frobenius.Bialgebra
public import TauCeti.FieldTheory.Finite.Frobenius
public import TauCeti.FieldTheory.Finite.FrobeniusFixed
public import TauCeti.GroupTheory.FixedSubgroup
public import TauCeti.RingTheory.FiniteType.AlgHom

/-!
# The `q`-Frobenius on the points of a group scheme over `𝔽_q`

Let `K` be a finite field with `q` elements and let `H` be a Hopf algebra over `K`, the
coordinate algebra of an affine group scheme `G₀` over `K`. No splitting, `ℤ`-model or
reductivity is assumed: `H` is an arbitrary `K`-form. For a commutative `K`-algebra `A`, the
`q ^ n`-Frobenius acts on the convolution group of `A`-valued points `WithConv (H →ₐ[K] A)` by
post-composition with the `K`-algebra endomorphism `x ↦ x ^ q ^ n` of `A`
(`TauCeti.FiniteField.frobeniusPoints`).

When `H` is commutative, the `q`-power map on the functions of `G₀` is the bialgebra
endomorphism `TauCeti.frobeniusBialgHom K H`, the Frobenius endomorphism of `G₀` defined by its
`𝔽_q`-structure, and the `q`-Frobenius on points is pre-composition with it. For `A = k` an
algebraic closure of `𝔽_q`, reading the `k`-points of `G = G₀ ×_{𝔽_q} k` as the `k`-valued points
of `H`, this is the geometric Frobenius `F` of `G`.

The fixed points of the Frobenius are the points valued in the Frobenius-fixed subalgebra of `A`
(`TauCeti.FiniteField.frobeniusFixedPointsMulEquiv`). When `A` is a domain, for instance a field
extension of `K`, the points fixed by the `q`-Frobenius are exactly the `K`-rational points:
`G^F ≃ G₀(K)` (`TauCeti.FiniteField.rationalPointsMulEquiv`). If moreover `H` is of finite type,
the points fixed by every positive iterate `F ^ n` form a finite group
(`TauCeti.FiniteField.finite_fixedSubgroup_frobeniusPoints`). All of this is natural in the
coordinate algebra, so it applies to every morphism of group schemes over `K` and in particular
to the inclusion of a closed subgroup scheme, whose coordinate algebra is again of finite type.

## Main definitions

* `TauCeti.FiniteField.frobeniusPoints`: the `q ^ n`-Frobenius on `A`-valued points.
* `TauCeti.FiniteField.frobeniusFixedPointsMulEquiv`: the Frobenius-fixed points are the points
  valued in the Frobenius-fixed subalgebra.
* `TauCeti.FiniteField.rationalPointsMulEquiv`: over a domain, the `q`-Frobenius-fixed points are
  the `K`-points.

## Main results

* `TauCeti.FiniteField.frobeniusPoints_apply_apply`: the Frobenius raises every value of a point
  to the `q ^ n`-th power.
* `TauCeti.FiniteField.mapDomain_frobeniusBialgHom`: for commutative `H`, the `q`-Frobenius on
  points is pre-composition with the Frobenius endomorphism `TauCeti.frobeniusBialgHom K H`.
* `TauCeti.FiniteField.mapDomain_comp_frobeniusPoints`: the Frobenius on points commutes with
  every morphism of group schemes over `K`.
* `TauCeti.FiniteField.coe_rationalPointsMulEquiv_mapDomain`: the identification of the fixed
  points with the `K`-points is natural in the group scheme.
* `TauCeti.FiniteField.finite_fixedSubgroup_frobeniusPoints`: for `H` of finite type and `A` a
  domain, the points fixed by a positive iterate of the Frobenius form a finite group.

## References

R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17;
O. Dudas and J. Michel, *Lectures on finite reductive groups and their representations*, §7.
-/

public section

open WithConv

namespace TauCeti.FiniteField

variable (K : Type*) [Field K] [Fintype K]

section Bialgebra

variable {H : Type*} [Semiring H] [_root_.Bialgebra K H]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- The `q ^ n`-Frobenius on the convolution monoid of `A`-valued points of a bialgebra `H` over a
finite field `K` with `q` elements. It post-composes a point with the `K`-algebra endomorphism
`x ↦ x ^ q ^ n` of `A`. -/
noncomputable def frobeniusPoints (n : ℕ) : WithConv (H →ₐ[K] A) →* WithConv (H →ₐ[K] A) :=
  AlgHom.mapValue (_root_.FiniteField.frobeniusAlgHom K A ^ n)

variable {K}

/-- The `q ^ n`-Frobenius raises every value of a point to the `q ^ n`-th power. -/
@[simp]
theorem frobeniusPoints_apply_apply (n : ℕ) (f : WithConv (H →ₐ[K] A)) (h : H) :
    (frobeniusPoints K n f).ofConv h = f.ofConv h ^ Nat.card K ^ n := by
  rw [frobeniusPoints, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    frobeniusAlgHom_pow_apply]

/-- A point is fixed by the `q ^ n`-Frobenius exactly when each of its values is. -/
@[simp]
theorem frobeniusPoints_eq_self_iff {n : ℕ} {f : WithConv (H →ₐ[K] A)} :
    frobeniusPoints K n f = f ↔ ∀ h : H, f.ofConv h ^ Nat.card K ^ n = f.ofConv h := by
  refine ⟨fun hf h => by rw [← frobeniusPoints_apply_apply, hf], fun hf => ?_⟩
  exact ofConv_injective (AlgHom.ext fun h => by rw [frobeniusPoints_apply_apply, hf h])

variable (K) in
/-- The zeroth iterate of the Frobenius is the identity on points. -/
@[simp]
theorem frobeniusPoints_zero : frobeniusPoints K 0 (H := H) (A := A) = MonoidHom.id _ :=
  MonoidHom.ext fun f => ofConv_injective (AlgHom.ext fun h => by simp)

variable (K) in
/-- Iterates of the Frobenius on points compose by adding exponents. -/
theorem frobeniusPoints_add (m n : ℕ) :
    frobeniusPoints K (m + n) (H := H) (A := A) =
      (frobeniusPoints K m).comp (frobeniusPoints K n) :=
  MonoidHom.ext fun f => ofConv_injective (AlgHom.ext fun h => by
    simp only [frobeniusPoints_apply_apply, MonoidHom.comp_apply, ← pow_mul, ← pow_add,
      add_comm m n])

/-- The Frobenius on points is natural in the coordinate bialgebra: it commutes with the map on
points induced by any bialgebra morphism, that is, with every morphism of group schemes over
`K`. -/
theorem mapDomain_comp_frobeniusPoints {H₁ : Type*} [Semiring H₁] [_root_.Bialgebra K H₁]
    (φ : H₁ →ₐc[K] H) (n : ℕ) :
    (BialgHom.mapDomain φ).comp (frobeniusPoints K n (H := H) (A := A)) =
      (frobeniusPoints K n).comp (BialgHom.mapDomain φ) :=
  BialgHom.mapValue_mapDomain φ _

/-- The Frobenius on points is natural in the value algebra. -/
theorem mapValue_comp_frobeniusPoints {B : Type*} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B)
    (n : ℕ) :
    (AlgHom.mapValue (H := H) φ).comp (frobeniusPoints K n) =
      (frobeniusPoints K n).comp (AlgHom.mapValue φ) :=
  MonoidHom.ext fun f => ofConv_injective (AlgHom.ext fun h => by
    simp only [MonoidHom.comp_apply, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      frobeniusPoints_apply_apply, map_pow])

end Bialgebra

/-! ### The Frobenius endomorphism of a commutative bialgebra -/

section Commutative

variable {K}
variable {H : Type*} [CommSemiring H] [_root_.Bialgebra K H]

/-- **The Frobenius on points is the map induced by the Frobenius endomorphism**: for a
commutative bialgebra `H` over `K`, raising the values of a point to the `q`-th power is the
same as pre-composing it with the `q`-power map `TauCeti.frobeniusBialgHom K H` of `H`, the
Frobenius endomorphism of `Spec H` defined by its `K`-structure. -/
theorem mapDomain_frobeniusBialgHom {A : Type*} [CommRing A] [Algebra K A] :
    BialgHom.mapDomain (A := A) (frobeniusBialgHom K H) = frobeniusPoints K 1 :=
  MonoidHom.ext fun f => ofConv_injective (AlgHom.ext fun h => by
    rw [BialgHom.mapDomain_apply_apply, frobeniusBialgHom_apply, frobeniusPoints_apply_apply,
      map_pow, pow_one, Nat.card_eq_fintype_card])

end Commutative

/-! ### Frobenius-fixed points -/

section HopfAlgebra

variable {K}
variable {H : Type*} [Semiring H] [_root_.HopfAlgebra K H]
variable {A : Type*} [CommRing A] [Algebra K A]

variable (K H A) in
/-- The points valued in the Frobenius-fixed subalgebra of `A` are exactly the Frobenius-fixed
points. -/
theorem range_mapValue_val_frobeniusFixedSubalgebra (n : ℕ) :
    (AlgHom.mapValue (H := H) (frobeniusFixedSubalgebra K A n).val).range =
      fixedSubgroup (frobeniusPoints K n) := by
  ext f
  rw [MonoidHom.mem_range, ← MonoidHom.mem_mrange,
    AlgHom.mem_mrange_mapValue_iff Subtype.val_injective, mem_fixedSubgroup,
    frobeniusPoints_eq_self_iff, Subalgebra.range_val]
  exact forall_congr' fun h => mem_frobeniusFixedSubalgebra

variable (K H A) in
/-- **The Frobenius-fixed points are the points over the Frobenius-fixed subalgebra.** For
`A` an algebraic closure of `𝔽_q` and `0 < n` the subalgebra is `𝔽_{q ^ n}`, so the points fixed
by `F ^ n` are the `𝔽_{q ^ n}`-points. -/
noncomputable def frobeniusFixedPointsMulEquiv (n : ℕ) :
    WithConv (H →ₐ[K] frobeniusFixedSubalgebra K A n) ≃*
      fixedSubgroup (frobeniusPoints K n (H := H) (A := A)) :=
  (MonoidHom.ofInjective (AlgHom.mapValue_injective Subtype.val_injective)).trans
    (MulEquiv.subgroupCongr (range_mapValue_val_frobeniusFixedSubalgebra K H A n))

/-- The isomorphism onto the Frobenius-fixed points reads a point over the fixed subalgebra as an
`A`-valued point. -/
@[simp]
theorem coe_frobeniusFixedPointsMulEquiv {n : ℕ}
    (f : WithConv (H →ₐ[K] frobeniusFixedSubalgebra K A n)) :
    (frobeniusFixedPointsMulEquiv K H A n f : WithConv (H →ₐ[K] A)) =
      AlgHom.mapValue (frobeniusFixedSubalgebra K A n).val f := by
  rw [frobeniusFixedPointsMulEquiv, MulEquiv.coe_trans, Function.comp_apply,
    MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

/-- The inverse isomorphism keeps the values of a Frobenius-fixed point. -/
@[simp]
theorem coe_frobeniusFixedPointsMulEquiv_symm_apply_apply {n : ℕ}
    (g : fixedSubgroup (frobeniusPoints K n (H := H) (A := A))) (h : H) :
    (((frobeniusFixedPointsMulEquiv K H A n).symm g).ofConv h : A) =
      (g : WithConv (H →ₐ[K] A)).ofConv h := by
  conv_rhs => rw [← (frobeniusFixedPointsMulEquiv K H A n).apply_symm_apply g]
  rw [coe_frobeniusFixedPointsMulEquiv, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    Subalgebra.coe_val]

section Domain

variable (L : Type*) [CommRing L] [IsDomain L] [Algebra K L]

variable (K H) in
/-- Over a domain, the points fixed by the `q`-Frobenius are exactly those coming from
`K`-points. -/
theorem range_mapValue_ofId :
    (AlgHom.mapValue (H := H) (Algebra.ofId K L)).range = fixedSubgroup (frobeniusPoints K 1) := by
  ext f
  rw [MonoidHom.mem_range, ← MonoidHom.mem_mrange,
    AlgHom.mem_mrange_mapValue_iff (algebraMap K L).injective, mem_fixedSubgroup,
    frobeniusPoints_eq_self_iff]
  simp only [pow_one, pow_natCard_eq_self_iff_mem_range_algebraMap, AlgHom.mem_range,
    Algebra.ofId_apply, Set.mem_range]

variable (K H) in
/-- **The `q`-Frobenius-fixed points are the `K`-rational points.** For a Hopf algebra `H` over
the finite field `K = 𝔽_q`, the coordinate algebra of an arbitrary `𝔽_q`-form `G₀`, and a domain
`L` over `K` such as an algebraic closure of `𝔽_q`, the points fixed by the Frobenius `F` are the
image of the `K`-points: `G^F ≃ G₀(𝔽_q)`. -/
noncomputable def rationalPointsMulEquiv :
    WithConv (H →ₐ[K] K) ≃* fixedSubgroup (frobeniusPoints K 1 (H := H) (A := L)) :=
  (MonoidHom.ofInjective (AlgHom.mapValue_injective (algebraMap K L).injective)).trans
    (MulEquiv.subgroupCongr (range_mapValue_ofId K H L))

/-- The identification of the `K`-points with the Frobenius-fixed points composes a `K`-point
with the structure map `K → L`. -/
@[simp]
theorem coe_rationalPointsMulEquiv (f : WithConv (H →ₐ[K] K)) :
    (rationalPointsMulEquiv K H L f : WithConv (H →ₐ[K] L)) =
      AlgHom.mapValue (Algebra.ofId K L) f := by
  rw [rationalPointsMulEquiv, MulEquiv.coe_trans, Function.comp_apply,
    MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

/-- The inverse identification sends a Frobenius-fixed point to the `K`-point whose values map to
its values under the structure map `K → L`. -/
@[simp]
theorem algebraMap_rationalPointsMulEquiv_symm_apply_apply
    (g : fixedSubgroup (frobeniusPoints K 1 (H := H) (A := L))) (h : H) :
    algebraMap K L (((rationalPointsMulEquiv K H L).symm g).ofConv h) =
      (g : WithConv (H →ₐ[K] L)).ofConv h := by
  conv_rhs => rw [← (rationalPointsMulEquiv K H L).apply_symm_apply g]
  rw [coe_rationalPointsMulEquiv, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    Algebra.ofId_apply]

/-- **The identification of the Frobenius-fixed points with the `K`-points is natural in the
group scheme**: a morphism `φ` of group schemes over `K` acts compatibly on `K`-points and on
Frobenius-fixed `L`-points. -/
theorem coe_rationalPointsMulEquiv_mapDomain {H₁ : Type*} [Semiring H₁] [_root_.HopfAlgebra K H₁]
    (φ : H₁ →ₐc[K] H) (f : WithConv (H →ₐ[K] K)) :
    (rationalPointsMulEquiv K H₁ L (BialgHom.mapDomain φ f) : WithConv (H₁ →ₐ[K] L)) =
      BialgHom.mapDomain φ (rationalPointsMulEquiv K H L f : WithConv (H →ₐ[K] L)) := by
  rw [coe_rationalPointsMulEquiv, coe_rationalPointsMulEquiv]
  exact DFunLike.congr_fun (BialgHom.mapValue_mapDomain φ (Algebra.ofId K L)).symm f

end Domain

/-- **A morphism of group schemes over `K` carries Frobenius-fixed points to Frobenius-fixed
points.** -/
theorem map_fixedSubgroup_frobeniusPoints_le {H₁ : Type*} [Semiring H₁] [_root_.HopfAlgebra K H₁]
    (φ : H₁ →ₐc[K] H) (n : ℕ) :
    (fixedSubgroup (frobeniusPoints K n (H := H) (A := A))).map (BialgHom.mapDomain φ) ≤
      fixedSubgroup (frobeniusPoints K n) :=
  map_fixedSubgroup_le _ (mapDomain_comp_frobeniusPoints φ n)

/-- **Finiteness of the Frobenius-fixed points.** For a Hopf algebra `H` of finite type over `K`
and a domain `A` over `K`, the points fixed by a positive iterate of the Frobenius form a finite
group: they are the points over the finite Frobenius-fixed subalgebra. In particular `G^F` is
finite for every affine group scheme `G₀` of finite type over `𝔽_q`, and so is the group of
rational points of each of its closed subgroup schemes. -/
theorem finite_fixedSubgroup_frobeniusPoints [Algebra.FiniteType K H] [IsDomain A] {n : ℕ}
    (hn : n ≠ 0) : Finite (fixedSubgroup (frobeniusPoints K n (H := H) (A := A))) := by
  have := finite_frobeniusFixedSubalgebra (K := K) (A := A) hn
  have : Finite (WithConv (H →ₐ[K] frobeniusFixedSubalgebra K A n)) :=
    Finite.of_injective ofConv ofConv_injective
  exact Finite.of_equiv _ (frobeniusFixedPointsMulEquiv K H A n).toEquiv

end HopfAlgebra

end TauCeti.FiniteField
