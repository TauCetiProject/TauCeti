/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Restricted
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal

/-!
# Contractive renorming of affinoid homomorphisms

Let `φ : A → B` be a homomorphism of affinoid algebras over a complete nonarchimedean field `K`.
This file shows that every residue norm on `A` can be matched by a residue norm on `B` for which
`φ` is contractive.

The construction extends a presentation of `A` to one of `B`. If `A` carries a complete
ultrametric algebra norm, then `φ` factors as `A → A⟨X₁, …, Xₘ⟩ → B` with the second map
surjective: send the variables to the images in `B` of the variables of a Tate presentation
`K⟨X₁, …, Xₘ⟩ → B`. These images are power-bounded for the residue norm of that presentation,
and the resulting map `A⟨X⟩ → B` restricts on `K⟨X⟩` to the presentation itself, by the
uniqueness part of the universal property of restricted series. In Huber's language `φ` is
topologically of finite type (`TauCeti.Huber.IsTopologicallyFiniteType.of_comp`); the statement
here is an algebraic surjection from the Gauss-normed algebra `A⟨X⟩`, the carrier on which the
residue norms below are defined.

For a residue norm on `A = K⟨Y⟩ ⧸ I` this produces a presentation
`K⟨X, Y⟩ ≅ K⟨Y⟩⟨X⟩ → B` which restricts to `φ` on `K⟨Y⟩`. The inclusion
`K⟨Y⟩ → K⟨Y⟩⟨X⟩` and the iteration isomorphism preserve Gauss norms, so `φ` does not increase
the residue norms.

## Main results

* `TauCeti.IsAffinoidAlgebra.exists_surjective_algHom_isRestricted_subring`: a `K`-algebra map
  `φ : A → B` from an affinoid algebra with a complete ultrametric algebra norm to an affinoid
  algebra extends to a surjection `A⟨X₁, …, Xₘ⟩ → B`.
* `TauCeti.IsAffinoidAlgebra.exists_surjective_norm_quotientKerAlgEquivOfSurjective_symm_le`:
  **contractive renorming**. For `φ : K⟨Y⟩ ⧸ I → B` into an affinoid algebra there is a Tate
  presentation `β : K⟨X, Y⟩ → B` whose residue norm on `B` satisfies `‖φ x‖ ≤ ‖x‖`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.3.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type*} [CommRing B] [Algebra K B]

/-- **Affinoid homomorphisms extend to presentations by restricted series.** Let `A` be an
affinoid algebra with a complete ultrametric algebra norm and let `B` be an affinoid algebra.
Every `K`-algebra map `φ : A → B` extends to a surjective `K`-algebra map
`A⟨X₁, …, Xₘ⟩ → B`. No norm on `B` is involved. -/
theorem exists_surjective_algHom_isRestricted_subring {A : Type*} [NormedCommRing A]
    [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A] (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : A →ₐ[K] B) :
    ∃ (m : ℕ) (β : IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) →ₐ[K] B),
      Function.Surjective β ∧ ∀ a, β (algebraMap A _ a) = φ a := by
  obtain ⟨m, π, hπ⟩ := (isAffinoidAlgebra_iff K B).mp hB
  -- give `B` the residue norm of the presentation `π`
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  have hB' : IsAffinoidAlgebra K (IsRestricted.subring (R := K) (fun _ : Fin m ↦ 1) ⧸
      RingHom.ker π) := isAffinoidAlgebra_tate.quotient _
  let b (i : Fin m) : IsRestricted.subring (R := K) (fun _ : Fin m ↦ 1) ⧸ RingHom.ker π :=
    Ideal.Quotient.mk _ ⟨X i, isRestricted_X _ i⟩
  let β := restrictedLift hA hB' (e.symm.toAlgHom.comp φ) (b := b) fun i ↦
    .of_norm_le_one <| (Submodule.Quotient.norm_mk_le _ _).trans (norm_X (R := K) i).le
  -- the Tate algebra in the new variables maps to `A⟨X⟩` by applying `K → A` to coefficients
  have hK (r : K) : ‖algebraMap K A r‖ ≤ ‖(1 : A)‖ * ‖r‖ := by
    rw [norm_algebraMap, mul_comm]
  let j : IsRestricted.subring (R := K) (fun _ : Fin m ↦ 1) →ₐ[K]
      IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) :=
    { restrictedMap (algebraMap K A) hK with
      commutes' r := by
        rw [RingHom.toFun_eq_coe, restrictedMap_algebraMap,
          ← IsScalarTower.algebraMap_apply] }
  -- on `K⟨X⟩`, the extension `β` is the residue map of the presentation `π`
  have hj : β.comp j = Ideal.Quotient.mkₐ K _ :=
    algHom_ext_isRestricted_subring isAffinoidAlgebra_self hB' (fun r ↦ by simp)
      fun i ↦ by
        have : j ⟨X i, isRestricted_X _ i⟩ = ⟨X i, isRestricted_X _ i⟩ :=
          Subtype.ext (by simp [j, coe_restrictedMap])
        simp [this, β, b]
  refine ⟨m, e.toAlgHom.comp β, e.surjective.comp fun y ↦ ?_, fun a ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨j f, congr($hj f)⟩
  · simp [β]

/-- **Contractive renorming.** Let `φ : K⟨Y₁, …, Yₙ⟩ ⧸ I → B` be a `K`-algebra map into an
affinoid algebra, where the source carries its residue Gauss norm. Then `B` has a Tate
presentation `β : K⟨X₁, …, Xₘ, Y₁, …, Yₙ⟩ → B` whose residue norm makes `φ` contractive: reading
`B` as `K⟨X, Y⟩ ⧸ ker β`, the image of every `x` has norm at most `‖x‖`. -/
theorem exists_surjective_norm_quotientKerAlgEquivOfSurjective_symm_le {σ : Type*} [Finite σ]
    (hB : IsAffinoidAlgebra K B) (I : Ideal (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))
    (φ : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) ⧸ I →ₐ[K] B) :
    ∃ (m : ℕ) (β : IsRestricted.subring (R := K) (fun _ : Fin m ⊕ σ ↦ 1) →ₐ[K] B)
      (hβ : Function.Surjective β),
      ∀ x, ‖(Ideal.quotientKerAlgEquivOfSurjective hβ).symm (φ x)‖ ≤ ‖x‖ := by
  obtain ⟨m, β, hβ, hβφ⟩ := exists_surjective_algHom_isRestricted_subring isAffinoidAlgebra_tate
    hB (φ.comp (Ideal.Quotient.mkₐ K I))
  -- the iteration isomorphism `K⟨X, Y⟩ ≅ K⟨Y⟩⟨X⟩`, with the radii written as `Sum.elim`
  let e := restrictedSumAlgEquiv (S := K) (R := K) (c := fun _ : Fin m ↦ (1 : ℝ))
    (d := fun _ : σ ↦ 1)
  -- transport from the radii `Sum.elim 1 1` to the constant radius `1`
  suffices key : ∀ (c : Fin m ⊕ σ → ℝ) [∀ i, Fact (0 < c i)],
      c = Sum.elim (fun _ ↦ 1) (fun _ ↦ 1) →
      ∃ (β' : IsRestricted.subring (R := K) c →ₐ[K] B) (hβ' : Function.Surjective β'),
        ∀ x, ‖(Ideal.quotientKerAlgEquivOfSurjective hβ').symm (φ x)‖ ≤ ‖x‖ from
    ⟨m, key _ (funext (Sum.rec (fun _ ↦ rfl) fun _ ↦ rfl))⟩
  intro c _ hc
  subst hc
  have he : Function.Surjective (β.comp e.toAlgHom) := fun y ↦ by
    obtain ⟨g, rfl⟩ := hβ y
    exact ⟨e.symm g, by simp⟩
  refine ⟨β.comp e.toAlgHom, he, fun x ↦ le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_⟩
  obtain ⟨f, hfx, hf⟩ := QuotientAddGroup.norm_lt_iff.mp hr
  -- the residue norm is the quotient group norm, whose class map is `Ideal.Quotient.mk I`
  obtain rfl : Ideal.Quotient.mk I f = x := hfx
  -- `f` lifts to `K⟨X, Y⟩` with the same Gauss norm
  have hlift : (Ideal.quotientKerAlgEquivOfSurjective he).symm (φ (Ideal.Quotient.mk I f)) =
      Ideal.Quotient.mk _ (e.symm (algebraMap _ _ f)) := by
    rw [← Ideal.quotientKerAlgEquivOfSurjective_symm_apply he]
    simp [hβφ]
  rw [hlift]
  refine (Submodule.Quotient.norm_mk_le _ _).trans (le_of_eq_of_le ?_ hf.le)
  rw [← norm_restrictedSumEquiv, ← coe_restrictedSumAlgEquiv (S := K)]
  simp [e, norm_algebraMap_isRestrictedSubring]

end TauCeti.IsAffinoidAlgebra
