/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Five
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Symplectic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import TauCeti.Algebra.CentralSimple.SeparablyClosed
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Even
import TauCeti.LinearAlgebra.Matrix.Involution
import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Spin in dimension five as a symplectic group

For a nondegenerate quadratic form `Q` on a five-dimensional space over a field of characteristic
not two, the even Clifford algebra `C₀` is central simple of degree four
(`TauCeti.CliffordAlgebra.deg_even_of_finrank_eq_five`), and `Spin(Q)` is its group `U(C₀, σ)` of
reverse-unitary elements (`CliffordAlgebra.range_spinGroup_toUnits_eq_evenUnitaryGroup`). The
canonical involution is `σ = reverse`. When `C₀` splits, `C₀ ≃ M₄(K)`, this file shows that `σ`
is **symplectic**: the isomorphism can be chosen to carry `σ` to the standard symplectic adjoint
`X ↦ J⁻¹ Xᵀ J = -(J Xᵀ J)`, and hence `Spin(Q) ≅ Sp₄(K)`.

Without a splitting hypothesis, `σ` is still symplectic in the sense of involutions of central
simple algebras: over any separably closed extension `L / K` the even Clifford algebra of the
extended form splits, `C₀ ⊗ L ≃ M₄(L)`, because it is central simple of degree four, and the split
case then carries the extended reversal to the symplectic adjoint. Consequently `Spin(Q)` embeds in
`Sp₄(L)`, and its image is exactly the set of symplectic matrices whose preimage in `C₀ ⊗ L`
comes from `C₀`: `Spin(Q)` is the group `Sp(C₀, σ)` of `K`-points of a twisted form of `Sp₄`.

The argument transports `σ` to an involutive anti-automorphism of `M₄(K)`, which is the adjoint
involution `X ↦ C⁻¹ Xᵀ C` of an invertible `C` with `Cᵀ = ±C`
(`Matrix.exists_forall_eq_inv_mul_transpose_mul`). The sign is read off from the skew elements:
the Clifford bivectors form a ten-dimensional space of even elements on which `σ` is `-1`, while an
orthogonal involution of `M₄(K)` has at most six independent skew elements
(`Matrix.finrank_skewAdjointMatricesSubmodule_le_choose_two`). So `C` is skew-symmetric, and a
symplectic basis for it conjugates `σ` to the standard symplectic adjoint
(`Matrix.exists_algEquiv_inv_mul_transpose_mul_eq_neg_J_mul_transpose_mul_J`).

## Main definitions

* `CliffordAlgebra.spinGroupEquivSymplecticGroup`: an algebra isomorphism from `C₀` to a matrix
  algebra carrying `σ` to the symplectic adjoint identifies `Spin(Q)` with the symplectic group, in
  dimensions one to five, via `CliffordAlgebra.evenUnitaryGroupEquivSymplecticGroup`.

## Main results

* `CliffordAlgebra.exists_algEquiv_reverseEven_eq_neg_J_mul_transpose_mul_J`: in dimension five, a
  splitting `C₀ ≃ M₄(K)` can be replaced by one carrying `σ` to the symplectic adjoint.
* `CliffordAlgebra.exists_algEquiv_reverseEven_eq_neg_J_mul_transpose_mul_J_iff`: such a
  reversal-compatible symplectic matrix model exists exactly when `C₀` splits.
* `CliffordAlgebra.exists_spinGroupEquivSymplecticGroup_of_finrank_eq_five`: if `C₀` splits in
  dimension five, then `Spin(Q) ≅ Sp₄(K)`.
* `CliffordAlgebra.exists_algEquiv_reverseEven_baseChange_eq_neg_J_mul_transpose_mul_J`: in
  dimension five, over every separably closed extension `L`, reversal on `C₀ ⊗ L` is the
  symplectic adjoint for a suitable splitting `C₀ ⊗ L ≃ M₄(L)`.
* `CliffordAlgebra.exists_injective_spinGroup_symplecticGroup_of_finrank_eq_five`: in dimension
  five, `Spin(Q)` is the subgroup of `Sp₄(L)` of matrices whose preimage under such a splitting is
  defined over `K`.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §8.D and
  §15.C.
-/

public section

open Matrix Module

open scoped TensorProduct

namespace CliffordAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]
  {l : Type*} [Fintype l] [DecidableEq l]

/-- In dimensions one to five, an algebra isomorphism from the even Clifford algebra to a matrix
algebra of even size which carries reversal to the symplectic adjoint `X ↦ -(J Xᵀ J)` identifies
`Spin(Q)` with the symplectic group. In dimension five this is `Spin₅ ≅ Sp₄` for split `C₀`
(`CliffordAlgebra.exists_spinGroupEquivSymplecticGroup_of_finrank_eq_five`). -/
noncomputable def spinGroupEquivSymplecticGroup (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV0 : 0 < finrank K V) (hV : finrank K V ≤ 5)
    (e : even Q ≃ₐ[K] Matrix (l ⊕ l) (l ⊕ l) K)
    (he : ∀ x, e (reverseEven Q x) = -(J l K * (e x)ᵀ * J l K)) :
    spinGroup Q ≃* symplecticGroup l K :=
  MulEquiv.ofBijective
    ((evenUnitaryGroupEquivSymplecticGroup Q e he).toMonoidHom.comp (spinGroupToEvenUnitary Q))
    ⟨(evenUnitaryGroupEquivSymplecticGroup Q e he).injective.comp
      (spinGroupToEvenUnitary_injective Q), fun g => by
      have hx : ((evenUnitaryGroupEquivSymplecticGroup Q e he).symm g : (CliffordAlgebra Q)ˣ) ∈
          (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range := by
        rw [range_spinGroup_toUnits_eq_evenUnitaryGroup Q hQ hV0 hV]
        exact ((evenUnitaryGroupEquivSymplecticGroup Q e he).symm g).2
      obtain ⟨s, hs⟩ := hx
      refine ⟨s, ?_⟩
      have hs' : spinGroupToEvenUnitary Q s =
          (evenUnitaryGroupEquivSymplecticGroup Q e he).symm g :=
        Subtype.ext (by rw [coe_spinGroupToEvenUnitary_apply, hs])
      simp [hs']⟩

/-- The Spin-to-symplectic identification applies the algebra isomorphism to the underlying even
Clifford element. -/
@[simp]
theorem coe_spinGroupEquivSymplecticGroup_apply (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV0 : 0 < finrank K V) (hV : finrank K V ≤ 5)
    (e : even Q ≃ₐ[K] Matrix (l ⊕ l) (l ⊕ l) K)
    (he : ∀ x, e (reverseEven Q x) = -(J l K * (e x)ᵀ * J l K)) (s : spinGroup Q) :
    (spinGroupEquivSymplecticGroup Q hQ hV0 hV e he s : Matrix (l ⊕ l) (l ⊕ l) K) =
      e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) := by
  simp [spinGroupEquivSymplecticGroup]

/-- The inverse Spin-to-symplectic identification applies the inverse algebra isomorphism. -/
@[simp]
theorem coe_spinGroupEquivSymplecticGroup_symm_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V) (hV : finrank K V ≤ 5)
    (e : even Q ≃ₐ[K] Matrix (l ⊕ l) (l ⊕ l) K)
    (he : ∀ x, e (reverseEven Q x) = -(J l K * (e x)ᵀ * J l K)) (g : symplecticGroup l K) :
    ((spinGroupEquivSymplecticGroup Q hQ hV0 hV e he).symm g : CliffordAlgebra Q) =
      (e.symm g : CliffordAlgebra Q) := by
  have h := coe_spinGroupEquivSymplecticGroup_apply Q hQ hV0 hV e he
    ((spinGroupEquivSymplecticGroup Q hQ hV0 hV e he).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  simp [h]

/-- **Reversal is a symplectic involution in dimension five.** For a quadratic form on a
five-dimensional space whose even Clifford algebra splits, `C₀ ≃ M₄(K)`, there is an algebra
isomorphism `C₀ ≃ M₄(K)` carrying reversal to the standard symplectic adjoint
`X ↦ J⁻¹ Xᵀ J = -(J Xᵀ J)`. -/
theorem exists_algEquiv_reverseEven_eq_neg_J_mul_transpose_mul_J (Q : QuadraticForm K V)
    (hV : finrank K V = 5) (e : even Q ≃ₐ[K] Matrix (Fin 4) (Fin 4) K) :
    ∃ e' : even Q ≃ₐ[K] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      ∀ x, e' (reverseEven Q x) = -(J (Fin 2) K * (e' x)ᵀ * J (Fin 2) K) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  -- Reversal transported to `M₄(K)` is an involutive anti-automorphism.
  let φ : Matrix (Fin 4) (Fin 4) K →ₗ[K] Matrix (Fin 4) (Fin 4) K :=
    e.toLinearMap ∘ₗ reverseEven Q ∘ₗ e.symm.toLinearMap
  have hφe : ∀ x, φ (e x) = e (reverseEven Q x) := fun x => by simp [φ]
  have hφ : Function.Involutive φ := fun X => by simp [φ]
  obtain ⟨C, hC | hC, hφC⟩ := exists_forall_eq_inv_mul_transpose_mul φ
    (fun X Y => by simp [φ]) hφ
  · -- An orthogonal involution would have at most six independent skew elements, but the
    -- Clifford bivectors give ten.
    exfalso
    let biv : ⋀[K]^2 V →ₗ[K] even Q :=
      { toFun z := ⟨bivectorExterior Q z, bivectorExterior_range_le_of_bivector_mem Q
          (Subalgebra.toSubmodule (even Q))
          (fun a b => by rw [even_toSubmodule]; exact bivector_mem_evenOdd_zero Q a b)
          (LinearMap.mem_range_self _ z)⟩
        map_add' _ _ := Subtype.ext (map_add _ _ _)
        map_smul' _ _ := Subtype.ext (map_smul _ _ _) }
    have hW : LinearMap.range (e.toLinearMap ∘ₗ biv) ≤
        skewAdjointMatricesSubmodule (C : Matrix (Fin 4) (Fin 4) K) := by
      rintro _ ⟨z, rfl⟩
      have hz : φ (e (biv z)) = -e (biv z) := by
        rw [hφe, ← map_neg]
        exact congrArg e (Subtype.ext (by simp [biv, reverse_bivectorExterior]))
      rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, IsAdjointPair,
        LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, ← hz, hφC, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    have hinj : Function.Injective (e.toLinearMap ∘ₗ biv) :=
      e.injective.comp fun z w h => bivectorExterior_injective Q (congrArg Subtype.val h)
    have h10 := (Submodule.finrank_mono hW).trans
      (finrank_skewAdjointMatricesSubmodule_le_choose_two hC C.isUnit)
    rw [LinearMap.finrank_range_of_inj hinj, exteriorPower.finrank_eq, hV,
      Fintype.card_fin] at h10
    exact absurd h10 (by decide)
  · obtain ⟨m, ψ, hm, hψ⟩ := exists_algEquiv_inv_mul_transpose_mul_eq_neg_J_mul_transpose_mul_J hC
    obtain rfl : m = 2 := by rw [Fintype.card_fin] at hm; omega
    exact ⟨e.trans ψ, fun x => by rw [AlgEquiv.trans_apply, ← hφe, hφC, hψ, AlgEquiv.trans_apply]⟩

/-- **The dimension-five symplectic model is split exactly when the even Clifford algebra is.**
For a five-dimensional quadratic space, there is a matrix model carrying Clifford reversal to
the standard symplectic adjoint if and only if the even Clifford algebra splits, `C₀ ≃ M₄(K)`. -/
theorem exists_algEquiv_reverseEven_eq_neg_J_mul_transpose_mul_J_iff
    (Q : QuadraticForm K V) (hV : finrank K V = 5) :
    (∃ e : even Q ≃ₐ[K] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      ∀ x, e (reverseEven Q x) = -(J (Fin 2) K * (e x)ᵀ * J (Fin 2) K)) ↔
      Nonempty (even Q ≃ₐ[K] Matrix (Fin 4) (Fin 4) K) :=
  ⟨fun ⟨e, _⟩ => ⟨e.trans (Matrix.reindexAlgEquiv K K finSumFinEquiv)⟩,
    fun ⟨e⟩ => exists_algEquiv_reverseEven_eq_neg_J_mul_transpose_mul_J Q hV e⟩

/-- **Split `Spin₅` is `Sp₄`.** For a nondegenerate quadratic form on a five-dimensional space
whose even Clifford algebra splits, `C₀ ≃ M₄(K)`, the group `Spin(Q)` is isomorphic to the
symplectic group `Sp₄(K)`. -/
theorem exists_spinGroupEquivSymplecticGroup_of_finrank_eq_five (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 5)
    (hsplit : Nonempty (even Q ≃ₐ[K] Matrix (Fin 4) (Fin 4) K)) :
    Nonempty (spinGroup Q ≃* symplecticGroup (Fin 2) K) := by
  obtain ⟨e⟩ := hsplit
  obtain ⟨e', he'⟩ := exists_algEquiv_reverseEven_eq_neg_J_mul_transpose_mul_J Q hV e
  exact ⟨spinGroupEquivSymplecticGroup Q hQ (by omega) hV.le e' he'⟩

section BaseChange

variable (L : Type*) [Field L] [Algebra K L] [IsSepClosed L]

/-- **Reversal is a symplectic involution in dimension five**, with no splitting hypothesis. For
a nondegenerate quadratic form on a five-dimensional space and any separably closed extension
`L / K`, the even Clifford algebra of the extended form is isomorphic to `M₄(L)` by an isomorphism
carrying reversal to the standard symplectic adjoint `X ↦ J⁻¹ Xᵀ J = -(J Xᵀ J)`. -/
theorem exists_algEquiv_reverseEven_baseChange_eq_neg_J_mul_transpose_mul_J
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 5) :
    ∃ e : even (Q.baseChange L) ≃ₐ[L] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) L,
      ∀ x, e (reverseEven (Q.baseChange L) x) =
        -(J (Fin 2) L * (e x)ᵀ * J (Fin 2) L) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : L) := (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  have : NeZero (2 : L) := ⟨Invertible.ne_zero 2⟩
  have hVL : finrank L (L ⊗[K] V) = 5 := by rw [Module.finrank_baseChange, hV]
  have hodd : Odd (finrank L (L ⊗[K] V)) := by rw [hVL]; decide
  have hQL : (Q.baseChange L).Nondegenerate := QuadraticForm.Nondegenerate.baseChange (L := L) hQ
  -- The even Clifford algebra of the extended form is central simple of degree four, so it
  -- splits over the separably closed field `L`.
  have := TauCeti.CliffordAlgebra.isCentral_even_of_odd_finrank hQL hodd
  have := TauCeti.CliffordAlgebra.isSimpleRing_even_of_odd_finrank hQL hodd
  obtain ⟨n, -, hn, ⟨e⟩⟩ := TauCeti.IsSimpleRing.exists_algEquiv_matrix_of_isSepClosed L
    (even (Q.baseChange L))
  obtain rfl : n = 4 := by
    rw [← TauCeti.Algebra.deg_eq_of_finrank_eq_sq hn,
      TauCeti.CliffordAlgebra.deg_even_of_finrank_eq_five hVL]
  exact exists_algEquiv_reverseEven_eq_neg_J_mul_transpose_mul_J (Q.baseChange L) hVL e

/-- **`Spin₅` is a twisted form of `Sp₄`.** For a nondegenerate quadratic form on a
five-dimensional space and any separably closed extension `L / K`, there are a splitting
`e : C₀ ⊗ L ≃ M₄(L)` carrying reversal to the symplectic adjoint and an injective homomorphism
`f : Spin(Q) → Sp₄(L)` with `e⁻¹ (f s)` the scalar extension of `s`. Its image consists of exactly
those symplectic matrices `g` for which `e⁻¹ g` comes from `C₀`, so `Spin(Q)` is the group
`Sp(C₀, σ)` of `K`-rational points of `Sp₄(L)` for the `K`-structure `C₀ ⊆ C₀ ⊗ L`. -/
theorem exists_injective_spinGroup_symplecticGroup_of_finrank_eq_five
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 5) :
    ∃ (e : even (Q.baseChange L) ≃ₐ[L] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) L)
      (f : spinGroup Q →* symplecticGroup (Fin 2) L), Function.Injective f ∧
      (∀ s : spinGroup Q,
        (e.symm (f s) : CliffordAlgebra (Q.baseChange L)) = ofBaseChangeAux L Q s) ∧
      ∀ g, g ∈ f.range ↔
        ∃ y ∈ even Q, ofBaseChangeAux L Q y = (e.symm g : CliffordAlgebra (Q.baseChange L)) := by
  obtain ⟨e, he⟩ := exists_algEquiv_reverseEven_baseChange_eq_neg_J_mul_transpose_mul_J L Q hQ hV
  let φ := evenUnitaryGroupToSymplecticGroup Q e he
  refine ⟨e, φ.comp (spinGroupToEvenUnitary Q),
    (evenUnitaryGroupToSymplecticGroup_injective Q e he).comp (spinGroupToEvenUnitary_injective Q),
    fun s => by simp [φ], fun g => ?_⟩
  rw [← mem_range_evenUnitaryGroupToSymplecticGroup_iff Q e he, MonoidHom.range_comp]
  -- In dimension five every even unitary element is a Spin element.
  have hsurj : (spinGroupToEvenUnitary Q).range = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨s, hs⟩ : (x : (CliffordAlgebra Q)ˣ) ∈
        (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range := by
      rw [range_spinGroup_toUnits_eq_evenUnitaryGroup Q hQ (by omega) hV.le]
      exact x.2
    exact ⟨s, Subtype.ext (Units.ext (by rw [coe_spinGroupToEvenUnitary_apply, ← hs]))⟩
  rw [hsurj, ← MonoidHom.range_eq_map]

end BaseChange

end CliffordAlgebra
