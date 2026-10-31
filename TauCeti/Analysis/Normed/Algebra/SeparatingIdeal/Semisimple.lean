/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.SeparatingIdeal.Idempotent
public import TauCeti.Analysis.Normed.Algebra.SeparatingIdeal.Radical
public import TauCeti.RingTheory.Jacobson.NonUnital
import TauCeti.RingTheory.Idempotents.Algebraic

/-!
# Automatic continuity of surjective homomorphisms onto semisimple Banach algebras

Johnson's theorem: a surjective homomorphism `θ : A → B` of complex Banach algebras, not assumed
continuous, is continuous whenever `B` is unital and semisimple, meaning that its Jacobson radical
is zero. The algebra `A` need not be unital.

The separating space of `θ` is a separating ideal of `B`, hence finite-dimensional because `B` is
semisimple. A nonzero finite-dimensional ideal of a semisimple algebra contains a nonzero
idempotent, and the separating space of `θ` contains no nonzero idempotent from the range of
`θ`. Since `θ` is surjective, the separating space is zero, and `θ` is continuous.

For a nonunital `B` with zero Jacobson radical, `θ` extends to a surjective homomorphism of the
ℓ¹ unitizations, whose target is again semisimple, and continuity of the extension restricts to
`θ`. Surjectivity cannot be dropped when `B` is noncommutative.

## Main results

* `NonUnitalAlgHom.continuous_of_surjective_of_jacobson_eq_bot`: Johnson's theorem.
* `NonUnitalAlgHom.continuous_of_surjective_of_nonUnitalJacobson_eq_bot`: Johnson's theorem for
  a nonunital semisimple target.
* `AlgEquiv.isHomeomorph_of_jacobson_eq_bot`: an algebra isomorphism from a complex Banach
  algebra onto a semisimple unital complex Banach algebra is a homeomorphism.

## References

* B. E. Johnson, *The uniqueness of the (complete) norm topology*, Bull. Amer. Math. Soc. 73
  (1967), 537–539.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2, in particular the structure of
  separating ideals in semisimple Banach algebras and Johnson's uniqueness-of-norm theorem.
-/

public section

namespace NonUnitalAlgHom

variable {A B : Type*}
  [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [CompleteSpace A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- **Johnson's theorem.** A surjective homomorphism `θ : A → B` of complex Banach algebras, not
assumed continuous, is continuous when `B` is unital with zero Jacobson radical. -/
theorem continuous_of_surjective_of_jacobson_eq_bot (θ : A →ₙₐ[ℂ] B)
    (hθ : Function.Surjective θ) (hB : Ring.jacobson B = ⊥) : Continuous θ := by
  let S := (θ : A →ₗ[ℂ] B).separatingSpace
  have hS := θ.isSeparatingIdeal_separatingSpace hθ
  have : FiniteDimensional ℂ S := hS.finiteDimensional_of_jacobson_eq_bot hB
  -- A nonzero `S` would contain a nonzero idempotent, which lies in the range of `θ`.
  have hS0 : S = ⊥ := by
    by_contra hS0
    obtain ⟨e, heS, he, he0⟩ :=
      S.exists_isIdempotentElem_ne_zero_mem_of_jacobson_eq_bot hS.mul_mem_left hB hS0
    exact he0 (θ.eq_zero_of_isIdempotentElem_of_mem_separatingSpace he (hθ e) heS)
  exact ((θ : A →ₗ[ℂ] B).continuous_iff_separatingSpace_eq_bot.2 hS0 :)

/-- **Johnson's theorem, nonunital form.** A surjective homomorphism `θ : A → B` of complex Banach
algebras, not assumed continuous, is continuous when `B` has zero Jacobson radical. Neither
algebra need be unital. -/
theorem continuous_of_surjective_of_nonUnitalJacobson_eq_bot {B : Type*}
    [NonUnitalNormedRing B] [NormedSpace ℂ B] [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    [CompleteSpace B] (θ : A →ₙₐ[ℂ] B) (hθ : Function.Surjective θ)
    (hB : TauCeti.nonUnitalJacobson ℂ B = ⊥) : Continuous θ := by
  -- Extend `θ` to the ℓ¹ unitizations, where the unital form applies.
  let eA := WithLp.unitizationAlgEquiv (𝕜 := ℂ) (A := A) ℂ
  let eB := WithLp.unitizationAlgEquiv (𝕜 := ℂ) (A := B) ℂ
  let Θ : WithLp 1 (Unitization ℂ A) →ₐ[ℂ] WithLp 1 (Unitization ℂ B) :=
    (eB.symm : Unitization ℂ B →ₐ[ℂ] _).comp
      ((Unitization.lift ((Unitization.inrNonUnitalAlgHom ℂ B).comp θ)).comp eA)
  have hΘ (a : A) :
      Θ (WithLp.toLp 1 (a : Unitization ℂ A)) = WithLp.toLp 1 (θ a : Unitization ℂ B) := by
    simp [Θ, eA, eB]
  have hΘs : Function.Surjective Θ := by
    intro y
    obtain ⟨a, ha⟩ := hθ (WithLp.ofLp y).snd
    refine ⟨algebraMap ℂ _ (WithLp.ofLp y).fst + WithLp.toLp 1 (a : Unitization ℂ A), ?_⟩
    rw [map_add, AlgHom.commutes, hΘ, ha]
    apply WithLp.ofLp_injective
    simpa [WithLp.unitization_algebraMap, Unitization.algebraMap_eq_inl] using
      Unitization.inl_fst_add_inr_snd_eq (WithLp.ofLp y)
  have : RingHomSurjective eB.toRingHom := ⟨eB.surjective⟩
  have hrad : Ring.jacobson (WithLp 1 (Unitization ℂ B)) = ⊥ :=
    Module.jacobson_eq_bot_of_injective eB.toRingHom.toSemilinearMap eB.injective
      ((TauCeti.jacobson_unitization_eq_bot_iff (IsSemisimpleRing.jacobson_eq_bot ℂ)).2 hB)
  have hc := Θ.toNonUnitalAlgHom.continuous_of_surjective_of_jacobson_eq_bot hΘs hrad
  refine (WithLp.unitization_isometry_inr (𝕜 := ℂ) (A := B)).comp_continuous_iff.1 ?_
  exact (hc.comp (WithLp.unitization_isometry_inr (𝕜 := ℂ) (A := A)).continuous).congr hΘ

end NonUnitalAlgHom

namespace AlgEquiv

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- An algebra isomorphism from a complex Banach algebra onto a unital complex Banach algebra with
zero Jacobson radical, not assumed continuous, is a homeomorphism. The inverse is continuous by
the open mapping theorem. -/
theorem isHomeomorph_of_jacobson_eq_bot (e : A ≃ₐ[ℂ] B) (hB : Ring.jacobson B = ⊥) :
    IsHomeomorph e := by
  have hc : Continuous e :=
    (e : A →ₐ[ℂ] B).toNonUnitalAlgHom.continuous_of_surjective_of_jacobson_eq_bot e.surjective hB
  let f : A ≃L[ℂ] B := .ofBijective ⟨e.toLinearMap, hc⟩
    (LinearMap.ker_eq_bot.2 e.injective) (LinearMap.range_eq_top.2 e.surjective)
  exact f.toHomeomorph.isHomeomorph

end AlgEquiv
