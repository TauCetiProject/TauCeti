/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Kunneth.Sequence
public import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.AlgebraicTopology.Singular.Contractible
import TauCeti.CategoryTheory.GradedObject

/-!
# The homology of a product with a sphere

Let `S` be the unit sphere of a real inner product space of dimension `d + 2`, a sphere of
positive dimension `d + 1`, and let `F` be any space. With coefficients in a principal ideal
domain `k`, the homology of `S` is free, so the Künneth map of `S × F` is an isomorphism in
positive degrees (`TopCat.isIso_singularHomologyKunneth_of_flat`), and the only summands of
`Hₘ₊₁(S × F; k)` that can be nonzero are `H₀(S) ⊗ Hₘ₊₁(F)` and `H_{d+1}(S) ⊗ Hₘ₋d(F)`. So:

* `Hₘ₊₁(S × F; k)` vanishes when `Hₘ₊₁(F; k)` and `Hₘ₋d(F; k)` do
  (`TauCeti.isZero_singularHomology_sphere_prod`);
* the inclusion `F → S × F`, `y ↦ (x₀, y)`, at any point `x₀` of the sphere is an isomorphism on
  `Hₘ₊₁` when `Hₘ₋d(F; k)` vanishes (`TauCeti.isIso_singularHomologyMap_prodMk_const_sphere`).

Here a degree `m - d` that would be negative imposes no condition. These are the forms in which the
homology of a space weakly equivalent to `S × F` is read off from that of `F`, as for the loop
space `ΩHPⁿ ≃ S³ × ΩS⁴ⁿ⁺³` of a quaternionic projective space. For the circle the same statements
hold with any coefficients, through the Wang sequence of the mapping torus of the identity
(`TauCeti.isIso_singularHomologyMap_prodMk_const_one_succ_iff`,
`TauCeti.isZero_singularHomology_circle_prod_succ_iff`).

The inclusion at `x₀` is compared with the inclusion of a point through the naturality of the
Künneth map: both Künneth maps are isomorphisms, both identify the relevant homology with the
summand of degree `(0, m + 1)`, and `x₀ : pt → S` is an isomorphism on `H₀` since the sphere is path
connected.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, Theorem 3B.6, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Metric Module

universe w

namespace TauCeti

variable {k : Type w} [CommRing k] {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} (hE : finrank ℝ E = d + 2) (F : Type w) [TopologicalSpace F]

include hE in
/-- The summand `Hₚ(S; k) ⊗ H_q(F; k)`, `p + q = m + 1`, of the Künneth decomposition of
`Hₘ₊₁(S × F; k)` vanishes for `p ≠ 0` as soon as `Hₘ₋d(F; k)` does: either `p` is not the
dimension `d + 1` of the sphere and `Hₚ(S; k)` vanishes, or `q = m - d`. -/
private lemma isZero_singularHomology_sphere_tensor {m p q : ℕ} (hpq : p + q = m + 1)
    (hp : p ≠ 0)
    (h : ∀ q, q + (d + 1) = m + 1 →
      IsZero (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (ModuleCat.of k k)).obj
        (TopCat.of F))) :
    IsZero ((((singularHomologyFunctor (ModuleCat.{w} k) p).obj (ModuleCat.of k k)).obj
        (TopCat.of (sphere (0 : E) 1))) ⊗
      (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (ModuleCat.of k k)).obj
        (TopCat.of F))) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  by_cases hpd : p + 1 = d + 1
  · exact (tensorLeft _).map_isZero (h q (by omega))
  · -- The sphere has no homology in positive degrees other than its dimension.
    exact (tensorRight _).map_isZero
      ((isZero_reducedSingularHomologyFunctor_sphere_of_ne (ModuleCat.of k k) hE hpd).of_iso
        ((reducedSingularHomologySuccIso (ModuleCat.of k k) p).app _).symm)

include hE in
/-- The summand `H₀(S; k) ⊗ Hₘ₊₁(F; k)` is all of the degree `m + 1` part of the tensor product of
the homologies of `S` and `F` when `Hₘ₋d(F; k)` vanishes. -/
private lemma isIso_ιTensorObj_sphere {m : ℕ}
    (h : ∀ q, q + (d + 1) = m + 1 →
      IsZero (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (ModuleCat.of k k)).obj
        (TopCat.of F))) :
    IsIso (GradedObject.Monoidal.ιTensorObj
      (fun p ↦ ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (ModuleCat.of k k)).obj
        (TopCat.of (sphere (0 : E) 1)))
      (fun q ↦ ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (ModuleCat.of k k)).obj
        (TopCat.of F)) 0 (m + 1) (m + 1) (zero_add _)) :=
  GradedObject.isIso_ιMapObj_of_isZero _ _ fun ⟨p, q⟩ hpq hp ↦
    isZero_singularHomology_sphere_tensor hE F hpq (fun h0 ↦ hp (by
      subst h0
      simp only [zero_add] at hpq
      rw [hpq])) h

variable [IsDomain k] [IsPrincipalIdealRing k]

include hE in
/-- The Künneth map of `S × F` is an isomorphism in positive degrees, since the homology of the
sphere is free. -/
private lemma isIso_singularHomologyKunneth_sphere (m : ℕ) :
    IsIso (TopCat.singularHomologyKunneth (TopCat.of (sphere (0 : E) 1)) (TopCat.of F)
      (ModuleCat.of k k) (ModuleCat.of k k) (m + 1)) := by
  have (q : ℕ) : Module.Free k ((reducedSingularHomologyFunctor (ModuleCat.of k k) q).obj
      (TopCat.of (sphere (0 : E) 1))) := by
    by_cases hq : q = d + 1
    · subst hq
      have : FiniteDimensional ℝ E := .of_finrank_eq_succ hE
      exact .of_equiv (reducedSingularHomologySphereIso (ModuleCat.of k k)
        ((stdOrthonormalBasis ℝ E).reindex (finCongr hE))).symm.toLinearEquiv
    · have := ModuleCat.isZero_iff_subsingleton.mp
        (isZero_reducedSingularHomologyFunctor_sphere_of_ne (ModuleCat.of k k) hE hq)
      infer_instance
  have (q : ℕ) := ModuleCat.free_singularHomology_of_free_reducedSingularHomology
    (ModuleCat.of k k) (X := TopCat.of (sphere (0 : E) 1)) q
  exact TopCat.isIso_singularHomologyKunneth_of_flat _ _ _ _ m

include hE in
/-- **The homology of a product with a sphere vanishes with that of the other factor.** Let `S`
be the unit sphere of a real inner product space of dimension `d + 2`. With coefficients in a
principal ideal domain `k`, if `Hₘ₊₁(F; k)` vanishes and so does `Hₘ₋d(F; k)` (no condition when
`m < d`), then `Hₘ₊₁(S × F; k)` vanishes. -/
theorem isZero_singularHomology_sphere_prod {m : ℕ}
    (h₀ : IsZero (((singularHomologyFunctor (ModuleCat.{w} k) (m + 1)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)))
    (h : ∀ q, q + (d + 1) = m + 1 →
      IsZero (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (ModuleCat.of k k)).obj
        (TopCat.of F))) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} k) (m + 1)).obj (ModuleCat.of k k)).obj
      (TopCat.of (sphere (0 : E) 1 × F))) := by
  have := isIso_singularHomologyKunneth_sphere hE F (k := k) m
  have hT : IsZero (((singularHomologyFunctor (ModuleCat.{w} k) (m + 1)).obj
      (ModuleCat.of k k ⊗ ModuleCat.of k k)).obj
      (TopCat.of (sphere (0 : E) 1) ⊗ TopCat.of F)) := by
    refine IsZero.of_iso ?_
      (asIso (TopCat.singularHomologyKunneth (TopCat.of (sphere (0 : E) 1)) (TopCat.of F)
        (ModuleCat.of k k) (ModuleCat.of k k) (m + 1))).symm
    rw [IsZero.iff_id_eq_zero]
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q hpq ↦ IsZero.eq_of_src ?_ _ _
    rcases eq_or_ne p 0 with rfl | hp
    · obtain rfl : q = m + 1 := by omega
      exact (tensorLeft _).map_isZero h₀
    · exact isZero_singularHomology_sphere_tensor hE F hpq hp h
  -- The coefficients `k ⊗ k` of the Künneth map are identified with `k` by the unitor.
  exact hT.of_iso (((singularHomologyFunctor _ (m + 1)).mapIso
    (λ_ (ModuleCat.of k k))).app (TopCat.of (sphere (0 : E) 1) ⊗ TopCat.of F)).symm

include hE in
/-- **The inclusion of a slice of a product with a sphere is an isomorphism on homology** in the
degrees where the other factor has no homology in the complementary degree. Let `S` be the unit
sphere of a real inner product space of dimension `d + 2` and `x₀ ∈ S`. With coefficients in a
principal ideal domain `k`, if `Hₘ₋d(F; k)` vanishes (no condition when `m < d`), then the
inclusion `F → S × F`, `y ↦ (x₀, y)`, is an isomorphism on `Hₘ₊₁(-; k)`. -/
theorem isIso_singularHomologyMap_prodMk_const_sphere {m : ℕ} (x₀ : sphere (0 : E) 1)
    (h : ∀ q, q + (d + 1) = m + 1 →
      IsZero (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (ModuleCat.of k k)).obj
        (TopCat.of F))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{w} k) (m + 1)).obj (ModuleCat.of k k)).map
      (TopCat.ofHom ((ContinuousMap.const F x₀).prodMk (ContinuousMap.id F)))) := by
  let R := ModuleCat.of k k
  let S := TopCat.of (sphere (0 : E) 1)
  let pt : TopCat.{w} := 𝟙_ TopCat.{w}
  let c : pt ⟶ S := TopCat.ofHom (ContinuousMap.const _ x₀)
  let H (n : ℕ) (M : ModuleCat.{w} k) := (singularHomologyFunctor (ModuleCat.{w} k) n).obj M
  -- Pass to the coefficients `k ⊗ k` of the Künneth map, through the unitor.
  rw [← NatIso.isIso_map_iff ((singularHomologyFunctor _ (m + 1)).mapIso (λ_ R))]
  -- `y ↦ (x₀, y)` is the unitor `F ≅ pt × F` followed by `c × 𝟙`. This holds definitionally,
  -- `TopCat.of (S × F)` being the cartesian monoidal product `S ⊗ F`, so `exact` closes the goal.
  suffices IsIso ((H (m + 1) (R ⊗ R)).map (c ⊗ₘ 𝟙 (TopCat.of F))) by
    have : IsIso ((H (m + 1) (R ⊗ R)).map
        ((λ_ (TopCat.of F)).inv ≫ (c ⊗ₘ 𝟙 (TopCat.of F)))) := by
      rw [Functor.map_comp]
      infer_instance
    exact this
  have := isIso_singularHomologyKunneth_sphere hE F (k := k) m
  have : ContractibleSpace pt := inferInstanceAs (ContractibleSpace PUnit)
  have (p : ℕ) : Module.Flat k ((H p R).obj pt) :=
    have := ModuleCat.free_singularHomology_of_contractibleSpace R pt p
    inferInstance
  have : IsIso (TopCat.singularHomologyKunneth pt (TopCat.of F) R R (m + 1)) :=
    TopCat.isIso_singularHomologyKunneth_of_flat _ _ _ _ m
  -- On both sides, the summand of degree `(0, m + 1)` is all of the source of the Künneth map.
  have := isIso_ιTensorObj_sphere hE F (k := k) h
  have : IsIso (GradedObject.Monoidal.ιTensorObj (fun p ↦ (H p R).obj pt)
      (fun q ↦ (H q R).obj (TopCat.of F)) 0 (m + 1) (m + 1) (zero_add _)) :=
    GradedObject.isIso_ιMapObj_of_isZero _ _ fun ⟨p, q⟩ hpq hp ↦ (tensorRight _).map_isZero
      (isZero_singularHomologyFunctor_of_contractibleSpace R pt fun h0 ↦ hp (by
        subst h0
        simp only [zero_add] at hpq
        rw [hpq]))
  -- `c` is an isomorphism on `H₀`, the sphere being path connected.
  have : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by omega)) 0 zero_le_one)
  have := isIso_singularHomologyMap_zero_of_pathConnectedSpace R c
  -- The Künneth maps intertwine `c × 𝟙` with `c_* ⊗ 𝟙` on the summand of degree `(0, m + 1)`.
  have key := (GradedObject.Monoidal.ι_tensorHom_assoc (fun p ↦ (H p R).map c)
      (fun q ↦ (H q R).map (𝟙 (TopCat.of F))) 0 (m + 1) (m + 1) (zero_add _)
      (TopCat.singularHomologyKunneth S (TopCat.of F) R R (m + 1))).symm.trans
    (congrArg (GradedObject.Monoidal.ιTensorObj _ _ 0 (m + 1) (m + 1) (zero_add _) ≫ ·)
      (TopCat.singularHomologyKunneth_naturality c (𝟙 (TopCat.of F)) R R (m + 1)))
  have : IsIso ((GradedObject.Monoidal.ιTensorObj (fun p ↦ (H p R).obj pt)
      (fun q ↦ (H q R).obj (TopCat.of F)) 0 (m + 1) (m + 1) (zero_add _) ≫
        TopCat.singularHomologyKunneth pt (TopCat.of F) R R (m + 1)) ≫
      (H (m + 1) (R ⊗ R)).map (c ⊗ₘ 𝟙 (TopCat.of F))) := by
    rw [Category.assoc, ← key]
    infer_instance
  exact IsIso.of_isIso_comp_left (GradedObject.Monoidal.ιTensorObj (fun p ↦ (H p R).obj pt)
      (fun q ↦ (H q R).obj (TopCat.of F)) 0 (m + 1) (m + 1) (zero_add _) ≫
        TopCat.singularHomologyKunneth pt (TopCat.of F) R R (m + 1)) _

end TauCeti
