/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Kunneth
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Topology.PiCurry

/-!
# The singular homology of tori

Over a principal ideal domain `k`, the torus `Tⁿ = (S¹)ⁿ` has free homology with
`rank H_m(Tⁿ; M) = (n choose m) · rank M` for a free coefficient module `M` of finite rank.
Splitting off one circle at a time, `Tⁿ⁺¹ ≅ S¹ × Tⁿ`, and the homology of a product of spaces with
free homology is free with ranks given by the Künneth formula
(`TopCat.free_singularHomology_tensor`, `TopCat.finrank_singularHomology_tensor`), from the
homology of the circle (`ModuleCat.finrank_singularHomology_sphere`) and of a point
(`ModuleCat.finrank_singularHomology_of_contractibleSpace`).  In particular, with these freeness
instances, `TopCat.isIso_singularHomologyKunneth_of_projective` shows that the Künneth map
`H(S¹) ⊗ H(Tⁿ) ⟶ H(S¹ × Tⁿ)` is an isomorphism for every `n`, as an iterated Künneth description
of the homology of a torus requires.

The torus is modelled as `ι → TopCat.sphere 1` for a finite index type `ι`, the circle being
Mathlib's `TopCat.sphere 1`.

## Main results

* `ModuleCat.free_singularHomology_torus` and `ModuleCat.finrank_singularHomology_torus`: the
  homology of a torus is free, with `rank H_m(Tⁿ; M) = (n choose m) · rank M`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe w

namespace TauCeti

/-- The torus `S¹ × T^α` obtained by adding one circle factor to `T^α` is homeomorphic to
`T^{Option α}`. -/
private def torusOptionIso (α : Type w) :
    TopCat.of (Option α → TopCat.sphere.{w} 1) ≅
      TopCat.sphere.{w} 1 ⊗ TopCat.of (α → TopCat.sphere.{w} 1) :=
  TopCat.isoOfHomeo (piOptionEquivProdHomeomorph _)

/-- Reindexing the circle factors of a torus is a homeomorphism. -/
private def torusCongrIso {α β : Type w} (e : α ≃ β) :
    TopCat.of (α → TopCat.sphere.{w} 1) ≅ TopCat.of (β → TopCat.sphere.{w} 1) :=
  TopCat.isoOfHomeo (Homeomorph.piCongrLeft (Y := fun _ ↦ TopCat.sphere.{w} 1) e)

end TauCeti

namespace ModuleCat

open TauCeti

section Torus

variable {k : Type w} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k] (M : ModuleCat.{w} k)
  [Module.Free k M]

/-- Splitting off one circle factor, the homology of `T^{Option α}` with coefficients in `M` is
that of `S¹ × T^α` with coefficients in `k ⊗ M`. -/
private def singularHomologyTorusOptionLinearEquiv (α : Type w) (m : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
        (TopCat.of (Option α → TopCat.sphere.{w} 1)) ≃ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{w} k) m).obj (𝟙_ _ ⊗ M)).obj
        (TopCat.sphere.{w} 1 ⊗ TopCat.of (α → TopCat.sphere.{w} 1)) :=
  (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).mapIso (torusOptionIso α) ≪≫
    ((singularHomologyFunctor (ModuleCat.{w} k) m).mapIso (λ_ M).symm).app _).toLinearEquiv

/-- **The homology of a torus is free**: over a principal ideal domain, the singular homology of
`Tⁿ = (S¹)ⁿ` with coefficients in a free module is free. -/
instance free_singularHomology_torus (ι : Type w) [Finite ι] (m : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
      (TopCat.of (ι → TopCat.sphere.{w} 1))) := by
  -- Induction on `ι`, splitting off one circle at a time.
  have := Fintype.ofFinite ι
  revert m
  refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ m : ℕ,
    Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
      (TopCat.of (ι → TopCat.sphere.{w} 1)))) ?_ ?_ ?_ ι
  · intro α β _ e ih m
    exact .of_equiv
      (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).mapIso (torusCongrIso e)).toLinearEquiv
  · intro m
    infer_instance
  · intro α _ ih m
    -- The unit `𝟙_ (ModuleCat k)` is `k` itself.
    have : Module.Free k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Free k k)
    exact .of_equiv (singularHomologyTorusOptionLinearEquiv M α m).symm

variable [Module.Finite k M]

/-- The induction behind `ModuleCat.finite_singularHomology_torus` and
`ModuleCat.finrank_singularHomology_torus`, splitting off one circle at a time. -/
private lemma finite_singularHomology_torus_aux (ι : Type w) [Fintype ι] (m : ℕ) :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
        (TopCat.of (ι → TopCat.sphere.{w} 1))) ∧
      Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
        (TopCat.of (ι → TopCat.sphere.{w} 1))) =
        (Fintype.card ι).choose m * Module.finrank k M := by
  revert m
  refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ m : ℕ,
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
        (TopCat.of (ι → TopCat.sphere.{w} 1))) ∧
      Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
        (TopCat.of (ι → TopCat.sphere.{w} 1))) =
        (Fintype.card ι).choose m * Module.finrank k M) ?_ ?_ ?_ ι
  · intro α β _ e ih m
    let : Fintype α := .ofEquiv β e.symm
    have := (ih m).1
    let f :=
      (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).mapIso (torusCongrIso e)).toLinearEquiv
    refine ⟨.equiv f, ?_⟩
    rw [← f.finrank_eq, (ih m).2, Fintype.card_congr e]
  · intro m
    refine ⟨inferInstance, ?_⟩
    rw [finrank_singularHomology_of_contractibleSpace]
    cases m <;> simp
  · intro α _ ih m
    -- The unit `𝟙_ (ModuleCat k)` is `k` itself, free of rank one.
    have : Module.Free k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Free k k)
    have : Module.Finite k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Finite k k)
    have hk : Module.finrank k (𝟙_ (ModuleCat.{w} k)) = 1 := Module.finrank_self k
    have : ∀ q, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj
        (TopCat.of (α → TopCat.sphere.{w} 1))) :=
      fun q ↦ (ih q).1
    let f := singularHomologyTorusOptionLinearEquiv M α m
    refine ⟨.equiv f.symm, ?_⟩
    have hS (q : ℕ) :
        Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ _)).obj
          (TopCat.sphere.{w} 1)) = (if q = 1 then 1 else 0) + if q = 0 then 1 else 0 := by
      rw [finrank_singularHomology_sphere, hk]
    have hT (q : ℕ) :
        Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj
          (TopCat.of (α → TopCat.sphere.{w} 1))) =
          (Fintype.card α).choose q * Module.finrank k M :=
      (ih q).2
    rw [f.finrank_eq, TopCat.finrank_singularHomology_tensor]
    simp only [hS, hT, Fintype.card_option]
    -- Only the summands `H₀(S¹) ⊗ Hₘ(T^α)` and `H₁(S¹) ⊗ Hₘ₋₁(T^α)` contribute, and Pascal's rule
    -- gives the binomial coefficient.
    cases m with
    | zero => simp
    | succ j =>
      rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [Nat.choose_succ_succ', add_mul, add_comm]

variable (ι : Type w) [Finite ι]

/-- Over a principal ideal domain, the singular homology of a torus with coefficients in a free
module of finite rank has finite rank. -/
instance finite_singularHomology_torus (m : ℕ) :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
      (TopCat.of (ι → TopCat.sphere.{w} 1))) :=
  have := Fintype.ofFinite ι
  (finite_singularHomology_torus_aux M ι m).1

/-- **The ranks of the homology of a torus**: over a principal ideal domain, with coefficients in a
free module `M` of finite rank, `rank H_m(Tⁿ; M) = (n choose m) · rank M`, where `Tⁿ` is the
product of `n` circles. -/
@[simp]
theorem finrank_singularHomology_torus (m : ℕ) :
    Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
      (TopCat.of (ι → TopCat.sphere.{w} 1))) = (Nat.card ι).choose m * Module.finrank k M := by
  have := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card]
  exact (finite_singularHomology_torus_aux M ι m).2

end Torus

end ModuleCat
