/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Homology.PrincipalIdealRing
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Kunneth
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Topology.PiCurry

/-!
# Free singular homology and the homology of tori

This file records when singular homology with coefficients in a free module of finite rank is
again free of finite rank, and computes its rank.

* **Reduced homology.**  A point of a nonempty space `X` splits `H₀(X; M)` as the product of the
  reduced zeroth homology and `M`, and in positive degrees reduced and ordinary homology agree.  So
  `H_q(X; M)` is free of finite rank when the reduced homology is and `M` is, and its rank is that
  of the reduced homology, plus the rank of `M` in degree zero.
* **Contractible spaces and spheres.**  The reduced homology of a contractible space vanishes, and
  that of the sphere `Sᵈ` is one copy of `M` in degree `d` and vanishes elsewhere.  Hence
  `H_q(Sᵈ; M)` is free of rank `rank M` for `q = 0` and for `q = d` (of rank `2 rank M` when
  `d = q = 0`), and vanishes otherwise.
* **Products.**  Over a principal ideal domain `k`, with projective coefficient modules `M` and
  `N`, the Künneth map `⨁_{p + q = n} Hₚ(X; M) ⊗ H_q(Y; N) ⟶ Hₙ(X × Y; M ⊗ N)` is an isomorphism
  whenever the homology modules of `X` and `Y` are free
  (`TopCat.isIso_singularHomologyKunneth_of_projective`).  So `Hₙ(X × Y; M ⊗ N)` is free, of
  finite rank `∑_{p + q = n} rank Hₚ(X; M) · rank H_q(Y; N)` when the factors have finite rank.
* **Tori.**  Splitting off one circle at a time, the torus `Tⁿ = (S¹)ⁿ` has free homology with
  `rank H_m(Tⁿ; M) = (n choose m) · rank M` over a principal ideal domain.  In particular, with
  these freeness instances, `TopCat.isIso_singularHomologyKunneth_of_projective` shows that the
  Künneth map `H(S¹) ⊗ H(Tⁿ) ⟶ H(S¹ × Tⁿ)` is an isomorphism for every `n`, as an iterated Künneth
  description of the homology of a torus requires.

The torus is modelled as `ι → TopCat.sphere 1` for a finite index type `ι`, the circle being
Mathlib's `TopCat.sphere 1`.

## Main results

* `TauCeti.free_singularHomology_of_free_reducedSingularHomology`,
  `TauCeti.finite_singularHomology_of_finite_reducedSingularHomology` and
  `TauCeti.finrank_singularHomology_eq_finrank_reducedSingularHomology_add`: from reduced to
  ordinary homology.
* `TauCeti.finrank_singularHomology_of_contractibleSpace`: the homology of a contractible space.
* `TauCeti.finrank_singularHomology_sphere`: the homology of a sphere.
* `TopCat.free_singularHomology_tensor` and `TopCat.finrank_singularHomology_tensor`: the
  homology of a product of spaces with free homology, over a principal ideal domain.
* `TauCeti.free_singularHomology_torus` and `TauCeti.finrank_singularHomology_torus`: the
  homology of a torus is free, with `rank H_m(Tⁿ; M) = (n choose m) · rank M`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Corollary 2.14 (the homology of spheres), and Section 3.B, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe w

namespace TauCeti

section Reduced

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k) {X : TopCat.{w}}

/-- A point of `X` splits the zeroth singular homology with coefficients in a module as the
product of the reduced zeroth homology and the coefficient module. -/
private def singularHomology₀LinearEquiv (x : X) :
    ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj M).obj X ≃ₗ[k]
      (reducedSingularHomologyFunctor M 0).obj X × M :=
  (singularHomology₀SplitIso M x ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv

variable [Nonempty X]

/-- The singular homology of a nonempty space with coefficients in a free module is free when its
reduced homology is. -/
theorem free_singularHomology_of_free_reducedSingularHomology
    [∀ q, Module.Free k ((reducedSingularHomologyFunctor M q).obj X)] [Module.Free k M] (q : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj X) := by
  cases q with
  | zero => exact .of_equiv (singularHomology₀LinearEquiv M (Classical.arbitrary X)).symm
  | succ q => exact .of_equiv ((reducedSingularHomologySuccIso M q).app X).toLinearEquiv

/-- The singular homology of a nonempty space with coefficients in a finitely generated module is
finitely generated when its reduced homology is. -/
theorem finite_singularHomology_of_finite_reducedSingularHomology
    [∀ q, Module.Finite k ((reducedSingularHomologyFunctor M q).obj X)] [Module.Finite k M]
    (q : ℕ) : Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj X) := by
  cases q with
  | zero => exact .equiv (singularHomology₀LinearEquiv M (Classical.arbitrary X)).symm
  | succ q => exact .equiv ((reducedSingularHomologySuccIso M q).app X).toLinearEquiv

/-- The rank of the singular homology of a nonempty space is the rank of its reduced homology,
plus the rank of the coefficient module in degree zero. -/
theorem finrank_singularHomology_eq_finrank_reducedSingularHomology_add [StrongRankCondition k]
    [Module.Free k ((reducedSingularHomologyFunctor M 0).obj X)]
    [Module.Finite k ((reducedSingularHomologyFunctor M 0).obj X)]
    [Module.Free k M] [Module.Finite k M] (q : ℕ) :
    Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj X) =
      Module.finrank k ((reducedSingularHomologyFunctor M q).obj X) +
        if q = 0 then Module.finrank k M else 0 := by
  cases q with
  | zero =>
    rw [(singularHomology₀LinearEquiv M (Classical.arbitrary X)).finrank_eq,
      Module.finrank_prod, ite_eq_left rfl]
  | succ q =>
    rw [ite_eq_right q.succ_ne_zero, add_zero]
    exact ((reducedSingularHomologySuccIso M q).app X).toLinearEquiv.finrank_eq.symm

end Reduced

section Contractible

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k) (X : TopCat.{w}) [ContractibleSpace X]

/-- The reduced singular homology of a contractible space is trivial. -/
instance subsingleton_reducedSingularHomology_of_contractibleSpace (q : ℕ) :
    Subsingleton ((reducedSingularHomologyFunctor M q).obj X) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace M X q)

/-- The singular homology of a contractible space with coefficients in a free module is free. -/
instance free_singularHomology_of_contractibleSpace [Module.Free k M] (q : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj X) :=
  free_singularHomology_of_free_reducedSingularHomology M q

/-- The singular homology of a contractible space with coefficients in a finitely generated module
is finitely generated. -/
instance finite_singularHomology_of_contractibleSpace [Module.Finite k M] (q : ℕ) :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj X) :=
  finite_singularHomology_of_finite_reducedSingularHomology M q

/-- **The homology of a contractible space** with coefficients in a free module of finite rank
has the rank of the coefficients in degree zero and vanishes in positive degrees. -/
@[simp]
theorem finrank_singularHomology_of_contractibleSpace [StrongRankCondition k] [Module.Free k M]
    [Module.Finite k M] (q : ℕ) :
    Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj X) =
      if q = 0 then Module.finrank k M else 0 := by
  have := nontrivial_of_invariantBasisNumber k
  rw [finrank_singularHomology_eq_finrank_reducedSingularHomology_add,
    Module.finrank_zero_of_subsingleton, zero_add]

end Contractible

section Sphere

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k)

/-- The reduced singular homology of a sphere with coefficients in a free module is free. -/
instance free_reducedSingularHomology_sphere [Module.Free k M] (d q : ℕ) :
    Module.Free k ((reducedSingularHomologyFunctor M q).obj (TopCat.sphere.{w} d)) := by
  by_cases h : q = d
  · subst h
    exact .of_equiv (reducedSingularHomologyTopCatSphereIso M q).symm.toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne M (n := d) h)
    infer_instance

/-- The reduced singular homology of a sphere with coefficients in a finitely generated module is
finitely generated. -/
instance finite_reducedSingularHomology_sphere [Module.Finite k M] (d q : ℕ) :
    Module.Finite k ((reducedSingularHomologyFunctor M q).obj (TopCat.sphere.{w} d)) := by
  by_cases h : q = d
  · subst h
    exact .equiv (reducedSingularHomologyTopCatSphereIso M q).symm.toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne M (n := d) h)
    infer_instance

/-- The reduced homology of the sphere `Sᵈ` has the rank of the coefficients in degree `d` and
vanishes in every other degree. -/
@[simp]
theorem finrank_reducedSingularHomology_sphere [StrongRankCondition k] (d q : ℕ) :
    Module.finrank k ((reducedSingularHomologyFunctor M q).obj (TopCat.sphere.{w} d)) =
      if q = d then Module.finrank k M else 0 := by
  split_ifs with h
  · subst h
    exact (reducedSingularHomologyTopCatSphereIso M q).toLinearEquiv.finrank_eq
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne M (n := d) h)
    have := nontrivial_of_invariantBasisNumber k
    exact Module.finrank_zero_of_subsingleton

/-- The singular homology of a sphere with coefficients in a free module is free. -/
instance free_singularHomology_sphere [Module.Free k M] (d q : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj
      (TopCat.sphere.{w} d)) :=
  free_singularHomology_of_free_reducedSingularHomology M q

/-- The singular homology of a sphere with coefficients in a finitely generated module is finitely
generated. -/
instance finite_singularHomology_sphere [Module.Finite k M] (d q : ℕ) :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj
      (TopCat.sphere.{w} d)) :=
  finite_singularHomology_of_finite_reducedSingularHomology M q

/-- **The homology of a sphere.**  With coefficients in a free module `M` of finite rank,
`H_q(Sᵈ; M)` has rank `rank M` in degree `d`, plus `rank M` in degree zero; so it has rank
`rank M` in degrees `0` and `d` for `d > 0`, rank `2 rank M` in degree `0` for `d = 0`, and
vanishes in every other degree. -/
@[simp]
theorem finrank_singularHomology_sphere [StrongRankCondition k] [Module.Free k M]
    [Module.Finite k M] (d q : ℕ) :
    Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj
      (TopCat.sphere.{w} d)) =
      (if q = d then Module.finrank k M else 0) + if q = 0 then Module.finrank k M else 0 := by
  rw [finrank_singularHomology_eq_finrank_reducedSingularHomology_add,
    finrank_reducedSingularHomology_sphere]

end Sphere

end TauCeti

namespace TopCat

section Tensor

variable {k : Type w} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
  (X Y : TopCat.{w}) (M N : ModuleCat.{w} k) [Module.Projective k M] [Module.Projective k N]
  [∀ p, Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj M).obj X)]
  [∀ q, Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj N).obj Y)]

/-- Over a principal ideal domain, when the homology of `X` and `Y` is free, the Künneth map
identifies `Hₙ(X × Y; M ⊗ N)` with the direct sum of the `Hₚ(X; M) ⊗ H_q(Y; N)` with
`p + q = n`. -/
private def singularHomologyKunnethDirectSumIso (n : ℕ) :
    ModuleCat.of k (DirectSum ((fun x : ℕ × ℕ ↦ x.1 + x.2) ⁻¹' {n}) fun i ↦
      TensorProduct k (((singularHomologyFunctor (ModuleCat.{w} k) i.1.1).obj M).obj X)
        (((singularHomologyFunctor (ModuleCat.{w} k) i.1.2).obj N).obj Y)) ≅
      ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (M ⊗ N)).obj (X ⊗ Y) :=
  -- The source of the Künneth map is by definition the coproduct of the summands.
  (ModuleCat.coprodIsoDirectSum fun i : ((fun x : ℕ × ℕ ↦ x.1 + x.2) ⁻¹' {n}) ↦
    ((singularHomologyFunctor (ModuleCat.{w} k) i.1.1).obj M).obj X ⊗
      ((singularHomologyFunctor (ModuleCat.{w} k) i.1.2).obj N).obj Y).symm ≪≫
    -- `TopCat.isIso_singularHomologyKunneth_of_projective` is a theorem rather than an instance,
    -- so it is supplied to `asIso` explicitly.
    @asIso _ _ _ _ (singularHomologyKunneth X Y M N n)
      (isIso_singularHomologyKunneth_of_projective X Y M N n)

/-- Over a principal ideal domain, with projective coefficients, the singular homology of a
product of spaces with free homology is free. -/
instance free_singularHomology_tensor (n : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (M ⊗ N)).obj (X ⊗ Y)) :=
  .of_equiv (singularHomologyKunnethDirectSumIso X Y M N n).toLinearEquiv

variable [∀ p, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj M).obj X)]
  [∀ q, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj N).obj Y)]

/-- Over a principal ideal domain, with projective coefficients, the singular homology of a
product of spaces with free homology of finite rank has finite rank. -/
instance finite_singularHomology_tensor (n : ℕ) :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (M ⊗ N)).obj (X ⊗ Y)) :=
  have : Finite ((fun x : ℕ × ℕ ↦ x.1 + x.2) ⁻¹' {n}) :=
    (Finset.antidiagonal n).finite_toSet.subset fun x hx ↦ by simpa using hx
  .equiv (singularHomologyKunnethDirectSumIso X Y M N n).toLinearEquiv

/-- **The ranks of the homology of a product.**  Over a principal ideal domain, with projective
coefficients, if `X` and `Y` have free homology of finite rank, then
`rank Hₙ(X × Y; M ⊗ N) = ∑_{p + q = n} rank Hₚ(X; M) · rank H_q(Y; N)`, by the Künneth theorem. -/
theorem finrank_singularHomology_tensor (n : ℕ) :
    Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (M ⊗ N)).obj (X ⊗ Y)) =
      ∑ x ∈ Finset.antidiagonal n,
        Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) x.1).obj M).obj X) *
          Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) x.2).obj N).obj Y) := by
  let e : ((fun x : ℕ × ℕ ↦ x.1 + x.2) ⁻¹' {n}) ≃ Finset.antidiagonal n :=
    Equiv.subtypeEquivRight fun x ↦ by simp
  have := Fintype.ofEquiv _ e.symm
  rw [← (singularHomologyKunnethDirectSumIso X Y M N n).toLinearEquiv.finrank_eq,
    Module.finrank_directSum, ← Finset.sum_coe_sort (Finset.antidiagonal n)]
  exact Fintype.sum_equiv e _ _ fun x ↦ Module.finrank_tensorProduct

end Tensor

end TopCat

namespace TauCeti

section Torus

variable {k : Type w} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k] (M : ModuleCat.{w} k)
  [Module.Free k M]

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

/-- The induction behind `TauCeti.finite_singularHomology_torus` and
`TauCeti.finrank_singularHomology_torus`, splitting off one circle at a time. -/
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

end TauCeti
