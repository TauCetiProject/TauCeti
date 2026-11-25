/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import TauCeti.AlgebraicGeometry.RationalPoint.Frobenius
import Mathlib.Algebra.MvPolynomial.Funext
import TauCeti.RingTheory.MvPolynomial.OrderAt

/-!
# The points of affine space

For a commutative ring `k` and a field `L` over `k`, the `L`-valued points of the affine space
`𝔸(n; Spec k)` over `Spec k` are the `n`-tuples of elements of `L`
(`AlgebraicGeometry.AffineSpace.homOverEquiv`). So for a finite index type `n` the affine
`n`-space has `|L| ^ |n|` points with values in `L`
(`AlgebraicGeometry.AffineSpace.numberOfRationalPoints_eq`), with the convention of `Nat.card`
that an infinite field `L` gives `0` unless `n` is empty.

Over a finite field `k` with `q` elements, let `L` be an algebraic closure of `k`, or more
generally a separably closed algebraic extension. Points with values in the degree-`r` extension
of `k` are the `L`-valued points fixed by the `r`-th power of the arithmetic Frobenius
(`AlgEquiv.numberOfRationalPoints_fixedField_eq_natCard`), and that extension has `q ^ r`
elements. Hence the `r`-th power of Frobenius has `(q ^ r) ^ |n|` fixed points on the
`L`-valued points of affine `n`-space
(`AlgebraicGeometry.AffineSpace.natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow`). For the
affine line this is the count `q ^ r`, the basic instance of counting points over finite fields
by fixed points of Frobenius. In terms of the point count over the extension of degree `r`,
affine `n`-space has `AlgebraicGeometry.Scheme.Hom.pointCount` equal to `(q ^ r) ^ |n|` for
`r ≠ 0` (`AlgebraicGeometry.AffineSpace.pointCount_eq`).

Over any commutative ring `R`, a translation of `Spec R[X_σ]` over `Spec R` moves a given
`R`-point to the origin (`AlgebraicGeometry.exists_isIso_comp_eq_SpecMap_constantCoeff`). This
centres étale coordinates at a rational point.

## Main results

* `AlgebraicGeometry.AffineSpace.numberOfRationalPoints_eq`: for finite `n`, `𝔸(n; Spec k)` has
  `|L| ^ |n|` points with values in a field `L` over `k`.
* `AlgebraicGeometry.AffineSpace.natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow`: the
  `r`-th power of Frobenius has `(q ^ r) ^ |n|` fixed points on affine `n`-space.
* `AlgebraicGeometry.AffineSpace.pointCount_eq`: affine `n`-space has `(q ^ r) ^ |n|` points over
  the extension of degree `r ≠ 0` of a finite field with `q` elements.
* `AlgebraicGeometry.exists_isIso_comp_eq_SpecMap_constantCoeff`: an automorphism of
  `Spec R[X_σ]` over `Spec R` moves a given `R`-point to the origin.

## References

* P. Deligne, *Cohomologie étale (SGA 4½)*, Rapport, §1, for rational points over finite fields
  as fixed points of Frobenius.
-/

public section

open CategoryTheory IntermediateField

universe u v

namespace AlgebraicGeometry.AffineSpace

/-- Every nonempty open subset of affine space over an infinite field contains a rational
point, with no finiteness assumption on the set of coordinates. -/
theorem exists_rationalPoint_mem_open {k : Type u} [Field k] [Infinite k] (n : Type u)
    (U : Set 𝔸(n; Spec (.of k))) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ s : Spec (.of k) ⟶ 𝔸(n; Spec (.of k)),
      s ≫ 𝔸(n; Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ ∧
        s (IsLocalRing.closedPoint k) ∈ U := by
  let e := SpecIso n (.of k)
  let V := e.inv ⁻¹' U
  obtain ⟨x, hx⟩ := hne.preimage e.inv.surjective
  obtain ⟨_, ⟨p, rfl⟩, hxp, hpV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx
      (hU.preimage e.inv.continuous)
  have hp : p ≠ 0 := by
    rintro rfl
    exact hxp (zero_mem _)
  obtain ⟨v, hv⟩ : ∃ v : n → k, MvPolynomial.aeval (R := k) v p ≠ 0 := by
    by_contra! h
    exact hp (MvPolynomial.funext fun v ↦ by simpa [MvPolynomial.aeval_def] using h v)
  let s := Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) v).toRingHom)
  have hC : CommRingCat.ofHom MvPolynomial.C ≫
      CommRingCat.ofHom (MvPolynomial.aeval (R := k) v).toRingHom = 𝟙 _ :=
    CommRingCat.hom_ext (MvPolynomial.aeval (R := k) v).comp_algebraMap
  have hsV : s (IsLocalRing.closedPoint k) ∈ V := hpV (by
    intro hmem
    have hker : p ∈ Ideal.comap (MvPolynomial.aeval (R := k) v).toRingHom ⊥ := by
      convert hmem using 2
      exact congrArg (Ideal.comap _) (Ideal.eq_bot_of_prime (K := k) _).symm
    exact hv (by simpa using hker))
  refine ⟨s ≫ e.inv, ?_, ?_⟩
  · rw [Category.assoc, SpecIso_inv_over, ← Spec.map_comp, hC, Spec.map_id]
  · exact (Scheme.Hom.comp_apply s e.inv (IsLocalRing.closedPoint k)).symm ▸ hsV

/-- **The points of affine space.** For a field `L` over a commutative ring `k` and a finite index
type `n`, the affine space `𝔸(n; Spec k)` has `|L| ^ |n|` points with values in `L` over
`Spec k`. -/
@[simp]
theorem numberOfRationalPoints_eq {k : Type u} [CommRing k] (L : Type u) [Field L] [Algebra k L]
    (n : Type u) [Finite n] :
    (𝔸(n; Spec (.of k)) ↘ Spec (.of k)).numberOfRationalPoints L = Nat.card L ^ Nat.card n := by
  let _ : (Spec (.of L)).Over (Spec (.of k)) := ⟨Spec.map (CommRingCat.ofHom (algebraMap k L))⟩
  rw [Scheme.Hom.numberOfRationalPoints_def, ← Nat.card_fun]
  -- a point over `Spec k` is a morphism over `Spec k`, that is an `n`-tuple of global sections
  exact Nat.card_congr <| (Equiv.subtypeEquivRight fun _ ↦ (Scheme.Hom.isOver_iff _).symm).trans <|
    (homOverEquiv (Spec (.of k))).trans <|
      Equiv.arrowCongr (.refl n) (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv.toEquiv

/-- **Frobenius fixed points on affine space.** Let `k` be a finite field with `q` elements and
`L` a separably closed algebraic extension of `k`, for instance an algebraic closure. For
`r ≠ 0`, the `r`-th power of the arithmetic Frobenius `x ↦ x ^ q` of `L` fixes exactly
`(q ^ r) ^ |n|` of the `L`-valued points of the affine space `𝔸(n; Spec k)`. -/
@[simp]
theorem natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow (k L : Type u) [Field k] [Fintype k]
    [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [IsSepClosed L] (n : Type u) [Finite n]
    {r : ℕ} (hr : r ≠ 0) :
    Nat.card {x : Spec (.of L) ⟶ 𝔸(n; Spec (.of k)) //
        x ≫ (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) =
          Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        Spec.map (CommRingCat.ofHom
          ((FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ r : L ≃ₐ[k] L) : L →+* L)) ≫ x = x} =
      (Fintype.card k ^ r) ^ Nat.card n := by
  rw [← AlgEquiv.numberOfRationalPoints_fixedField_eq_natCard, numberOfRationalPoints_eq,
    TauCeti.natCard_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L hr]

/-- **The point counts of affine space.** Over a finite field `k` with `q` elements, the affine
space `𝔸(n; Spec k)` has `(q ^ r) ^ |n|` points over the extension of degree `r ≠ 0` of `k`. At
`r = 0` the count is that of `k`-valued points, `q ^ |n|`, which is not `(q ^ 0) ^ |n|` in
general. -/
theorem pointCount_eq {k : Type u} [Field k] [Finite k] (n : Type u) [Finite n] {r : ℕ}
    (hr : r ≠ 0) :
    (𝔸(n; Spec (.of k)) ↘ Spec (.of k)).pointCount r = (Nat.card k ^ r) ^ Nat.card n := by
  have := Fintype.ofFinite k
  rw [Scheme.Hom.pointCount_eq_natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow
      (AlgebraicClosure k) _ hr,
    natCard_fixedPoints_frobeniusAlgEquivOfAlgebraic_pow k (AlgebraicClosure k) n hr,
    Fintype.card_eq_nat_card]

end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry

/-- **Moving a point to the origin.** Every `R`-point `p` of `Spec R[X_σ]`, that is a section of
the structure morphism `Spec R[X_σ] ⟶ Spec R`, is sent to the origin by an automorphism of
`Spec R[X_σ]` over `Spec R`: the translation by `-a`, with comorphism `X_i ↦ X_i - a_i`, where
`a_i` is the value of `X_i` at `p`. -/
theorem exists_isIso_comp_eq_SpecMap_constantCoeff {R : Type max u v} {σ : Type v} [CommRing R]
    (p : Spec (.of R) ⟶ Spec (.of (MvPolynomial σ R)))
    (hp : p ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = 𝟙 _) :
    ∃ τ : Spec (.of (MvPolynomial σ R)) ⟶ Spec (.of (MvPolynomial σ R)), IsIso τ ∧
      τ ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        Spec.map (CommRingCat.ofHom MvPolynomial.C) ∧
      p ≫ τ = Spec.map (CommRingCat.ofHom MvPolynomial.constantCoeff) := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective p
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hp
  have hψ (r : R) : ψ (MvPolynomial.C r) = r := congr($hp r)
  let a : σ → R := fun i ↦ ψ (MvPolynomial.X i)
  refine ⟨Spec.map (MvPolynomial.taylorEquiv (-a)).toRingEquiv.toCommRingCatIso.hom,
    inferInstance, ?_, ?_⟩
  · rw [← Spec.map_comp]
    exact congrArg Spec.map
      (CommRingCat.hom_ext (RingHom.ext (MvPolynomial.taylorEquiv (-a)).commutes))
  · rw [← Spec.map_comp]
    refine congrArg Spec.map
      (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_))
    · simp [hψ]
    · simp [a, hψ]

end AlgebraicGeometry
