/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic
public import TauCeti.RingTheory.TotallySplit

/-!
# Totally split algebras over a totally split algebra

Let `K` be a field and `A → B` a map of totally split `K`-algebras (`Algebra.IsFiniteSplit`), with
`B` flat over `A`. Geometrically, `Spec B → Spec A` is a finite flat morphism between finite
disjoint unions of copies of `Spec K`. Above every `K`-point `χ` of `A` there are exactly as many
`K`-points of `B` as the rank of `B` at the prime `ker χ`: the fibre `K ⊗[A] B` is a quotient of
`B`, hence totally split, so its points are counted by its dimension.

When this rank is a constant `d`, the points of `B` are labelled by pairs of a point of `A` and an
index in `Fin d`, compatibly with the projection to the points of `A`, and `B` is the trivial
cover `Fin d → A` of `A`. This splits a finite flat cover of constant rank of a finite étale
scheme over a field once both schemes are split over the base field, for instance the branches
of a nodal curve over its nodes.

## Main results

* `Algebra.IsFiniteSplit.card_algHom_comp_eq_rankAtStalk`: the number of points of `B` above a
  point `χ` of `A` is the rank of `B` at `ker χ`.
* `Algebra.IsFiniteSplit.nonempty_algEquiv_fun_of_rankAtStalk_eq`: if `B` has constant rank `d`
  over `A`, then `B ≃ₐ[A] (Fin d → A)`.
-/

public section

open TensorProduct

namespace Algebra.IsFiniteSplit

variable {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  [Algebra A B] [IsScalarTower K A B]

/-- **The points of a totally split algebra above a point of its base number its rank there.**
If `B` is a totally split `K`-algebra, flat over the `K`-algebra `A`, then the
`K`-points of `B` restricting to a `K`-point `χ` of `A` are as many as the rank of `B` at the prime
`ker χ` of `A`. -/
theorem card_algHom_comp_eq_rankAtStalk [IsFiniteSplit K B] [Module.Flat A B] (χ : A →ₐ[K] K) :
    Nat.card {ψ : B →ₐ[K] K // ψ.comp (IsScalarTower.toAlgHom K A B) = χ} =
      Module.rankAtStalk (R := A) B ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ := by
  have : Module.Finite A B := .of_restrictScalars_finite K A B
  -- View `K` as an `A`-algebra through `χ`, and let `K ⊗[A] B` be the fibre of `B` at `χ`.
  let : Algebra A K := χ.toAlgebra
  have : IsScalarTower K A K := .of_algebraMap_eq fun k ↦ (χ.commutes k).symm
  have hχ : Function.Surjective (algebraMap A K) := fun k ↦ ⟨algebraMap K A k, χ.commutes k⟩
  -- The fibre is a quotient of `B`, hence totally split, so it has as many points as its rank.
  have : IsFiniteSplit K (K ⊗[A] B) :=
    of_surjective ((Algebra.TensorProduct.includeRight (R := A) (A := K)).restrictScalars K)
      (Algebra.TensorProduct.includeRight_surjective B hχ)
  have hrank : Module.finrank K (K ⊗[A] B) =
      Module.rankAtStalk (R := A) B ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ := by
    have := congr_fun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := K ⊗[A] B)) ⊥
    rw [Pi.natCast_apply, Nat.cast_id] at this
    -- The prime of `A` below the zero ideal of `K` is `ker χ`.
    rw [← this, Module.rankAtStalk_baseChange]
    rfl
  -- The points of the fibre are the points of `B` above `χ`.
  let e : {ψ : B →ₐ[K] K // ψ.comp (IsScalarTower.toAlgHom K A B) = χ} ≃ (B →ₐ[A] K) :=
    { toFun ψ := { ψ.1.toRingHom with
        commutes' a := by simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun ψ.2 a }
      invFun f := ⟨f.restrictScalars K, by ext a; simp [RingHom.algebraMap_toAlgebra]⟩
      left_inv ψ := rfl
      right_inv f := rfl }
  rw [Nat.card_congr (e.trans (Algebra.TensorProduct.liftEquivRight A K B K)),
    card_algHom_eq_finrank, hrank]

/-- **A totally split algebra of constant rank over a totally split algebra is a trivial cover.**
Let `A` and `B` be totally split algebras over a field `K`, with `B` a flat `A`-algebra of constant
rank `d`. Then `B` is `A`-isomorphic to `Fin d → A`: the `K`-points of `B` are labelled by pairs
of a `K`-point of `A` below them and an index in `Fin d`. -/
theorem nonempty_algEquiv_fun_of_rankAtStalk_eq [IsFiniteSplit K A] [IsFiniteSplit K B]
    [Module.Flat A B] {d : ℕ} (hd : ∀ p, Module.rankAtStalk (R := A) B p = d) :
    Nonempty (B ≃ₐ[A] (Fin d → A)) := by
  have := Finite.algHom K A K
  have := Finite.algHom K B K
  -- Each point `χ` of `A` has exactly `d` points of `B` above it, so the points of `B` are
  -- labelled by pairs `(χ, i)` with `i : Fin d`.
  let r : (B →ₐ[K] K) → (A →ₐ[K] K) := fun ψ ↦ ψ.comp (IsScalarTower.toAlgHom K A B)
  let σ : (A →ₐ[K] K) × Fin d ≃ (B →ₐ[K] K) :=
    (Equiv.sigmaEquivProd _ _).symm.trans <|
      (Equiv.sigmaCongrRight fun χ ↦ (Finite.equivFinOfCardEq
        ((card_algHom_comp_eq_rankAtStalk χ).trans (hd _))).symm).trans (Equiv.sigmaFiberEquiv r)
  have hσ (χ : A →ₐ[K] K) (i : Fin d) : r (σ (χ, i)) = χ :=
    ((Finite.equivFinOfCardEq ((card_algHom_comp_eq_rankAtStalk χ).trans (hd _))).symm i).2
  -- Both algebras are the algebras of functions on their points.
  let eA : A ≃ₐ[K] ((A →ₐ[K] K) → K) := .ofBijective _ pi_id_bijective
  let eB : B ≃ₐ[K] ((B →ₐ[K] K) → K) := .ofBijective _ pi_id_bijective
  let Φ : B →ₐ[K] (Fin d → A) :=
    AlgHom.pi fun i ↦ eA.symm.toAlgHom.comp (AlgHom.pi fun χ ↦ σ (χ, i))
  have hΦ (a : A) : Φ (algebraMap A B a) = algebraMap A (Fin d → A) a := by
    funext i
    refine eA.injective ?_
    funext χ
    simpa [Φ, r, eA] using DFunLike.congr_fun (hσ χ i) a
  -- `Φ` is `eB` followed by relabelling the points by `σ`, currying, and `eA.symm`.
  have hbij : Function.Bijective Φ := by
    let T : ((B →ₐ[K] K) → K) ≃ (Fin d → A) :=
      (Equiv.piCongrLeft' _ σ.symm).trans <| (Equiv.curry _ _ _).trans <|
        (Equiv.piComm _).trans (Equiv.piCongrRight fun _ ↦ eA.symm.toEquiv)
    -- Both sides evaluate `b` at `σ (χ, i)` and then apply `eA.symm`.
    have : ⇑Φ = T ∘ eB := funext fun _ ↦ rfl
    rw [this]
    exact T.bijective.comp eB.bijective
  exact ⟨AlgEquiv.ofBijective { Φ.toRingHom with commutes' := hΦ } hbij⟩

end Algebra.IsFiniteSplit
