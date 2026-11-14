/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head
public import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Direct-sum decomposition of finite graded projectives without finite-dimensionality

Let `A` be a nonnegatively graded `k`-algebra over a field `k` whose degree-zero piece `𝒜 0` is
spanned by a complete family of orthogonal idempotents `eᵢ` with homogeneous left ideals `A eᵢ`.
No finite-dimensionality of `A` over `k` is assumed: this covers polynomial rings `k[X]`, path
algebras of finite quivers (not necessarily acyclic), and finite-dimensional split algebras alike.

For any finitely generated graded `A`-module `M`, the quotient `M / A₊ M` is finite-dimensional
over `k`, and its homogeneous pieces decompose into `k`-subspaces governed by the `eᵢ`. Lifting a
homogeneous `k`-basis gives a minimal graded surjection `⨁ᵣ (A e_{idx r}){d r} ↠ M` from a finite
direct sum of shifted idempotent ideals. When `M` is projective, splitting this surjection and
applying Graded Nakayama to its kernel turns it into an isomorphism in `GradedModuleCat 𝒜`.

Consequently:
* when the `eᵢ` are nonzero, the classes `[A eᵢ]` form a `ℤ[q,q⁻¹]`-basis
  `TauCeti.gradedSplitProjectiveBasis` of `K₀^gr(proj A)` without `[Module.Finite k A]`;
* in any basis `bP` with `bP i = [A eᵢ]`, the `qᵖ`-coefficient of the `i`th coordinate of `[P]`
  counts the summands `(A eᵢ){p}` in a decomposition of `P`, and `P` is generated in degree `d`
  if and only if all off-degree `q`-coefficients of its `bP`-coordinates vanish.

## Main definitions

* `TauCeti.gradedSplitProjectiveBasis`: the `ℤ[q,q⁻¹]`-basis `[A eᵢ]` of `K₀^gr(proj A)` for any
  nonnegatively graded algebra with split degree-zero part.

## Main results

* `TauCeti.laurentK0_projective_of_directSumObj_fin` and
  `TauCeti.laurentK0_projective_of_retract_sum`: the class of a finite `directSumObj` or retract
  sum in `K₀^gr(proj A)` is the sum of the summand classes.
* `TauCeti.exists_iso_directSum_ofIdeal_span_singleton`: every finite graded projective is
  isomorphic to a finite direct sum `⨁ᵣ (A e_{idx r}){d r}`.
* `TauCeti.isGeneratedInDegree_iff_coeff_repr_eq_zero`: a finite graded projective is generated
  in degree `d` if and only if its coordinates in `[A eᵢ]` vanish outside `qᵈ`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter I, Section 5.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits _root_.DirectSum LaurentPolynomial
open scoped Pointwise

universe uk uA uI uJ

/-! ### Finite direct sums in `K₀^gr(proj A)` -/

section DirectSumClass

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

private theorem hom_sum_apply {J : Type*} {M N : GradedModuleCat.{uA} 𝒜}
    (s : Finset J) (φ : J → (M ⟶ N)) (x : M) :
    (∑ j ∈ s, φ j).hom x = ∑ j ∈ s, (φ j).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private def directSumProj {n : ℕ} (M : Fin n → GradedModuleCat.{uA} 𝒜) (r : Fin n) :
    GradedModuleCat.directSumObj M ⟶ M r :=
  GradedModuleCat.ofHom (DirectSum.component A (Fin n) (fun s => M s) r) <|
    LinearMap.isHomogeneous_def.mpr fun p x hx => by
      rw [add_zero]
      exact (GradedModuleCat.mem_coproductCofan_pt_piece_iff M).mp hx r

private abbrev directSumInj {n : ℕ} (M : Fin n → GradedModuleCat.{uA} 𝒜) (r : Fin n) :
    M r ⟶ GradedModuleCat.directSumObj M :=
  (GradedModuleCat.coproductCofan M).inj r

private theorem directSumInj_comp_proj_self {n : ℕ} (M : Fin n → GradedModuleCat.{uA} 𝒜)
    (r : Fin n) : directSumInj M r ≫ directSumProj M r = 𝟙 (M r) :=
  GradedModuleCat.hom_ext <| LinearMap.ext fun x => by simp [directSumProj]

private theorem directSumInj_comp_proj_of_ne {n : ℕ} (M : Fin n → GradedModuleCat.{uA} 𝒜)
    {r s : Fin n} (hrs : r ≠ s) : directSumInj M r ≫ directSumProj M s = 0 :=
  GradedModuleCat.hom_ext <| LinearMap.ext fun x => by
    simp [directSumProj, DirectSum.component.of, hrs]

private theorem sum_directSumProj_comp_inj {n : ℕ} (M : Fin n → GradedModuleCat.{uA} 𝒜) :
    ∑ r : Fin n, directSumProj M r ≫ directSumInj M r = 𝟙 (GradedModuleCat.directSumObj M) :=
  GradedModuleCat.hom_ext <| LinearMap.ext fun x => by
    rw [hom_sum_apply]
    refine (Finset.sum_congr rfl fun r _ => ?_).trans (DirectSum.sum_univ_of x)
    simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply, directSumProj,
      GradedModuleCat.hom_coproductCofan_inj, DirectSum.lof_eq_of]
    rfl

private theorem laurentK0_projective_biprod
    (Y Z : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (Y ⊞ Z) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) Y +
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) Z :=
  LaurentK0.of_conflation.{uA} _
    (ExactStructure.conflation_biprodShortComplex
      (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure Y Z)

/-- A finite `directSumObj` of finite graded projectives is a finite graded projective. -/
theorem gradedFiniteProjectiveModules_directSumObj_fin {n : ℕ}
    (P : Fin n → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedFiniteProjectiveModules 𝒜 (GradedModuleCat.directSumObj fun r => (P r).obj) := by
  let _ : ∀ r, Module.Finite A (P r).obj :=
    fun r => (gradedFiniteProjectiveModules_iff.mp (P r).property).1
  let _ : ∀ r, Module.Projective A (P r).obj :=
    fun r => (gradedFiniteProjectiveModules_iff.mp (P r).property).2
  exact gradedFiniteProjectiveModules_iff.mpr
    ⟨inferInstance, Module.Projective.directSum_iff.mpr inferInstance⟩

private def directSumObjFinSuccIso {m : ℕ}
    (P : Fin (m + 1) → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    (⟨GradedModuleCat.directSumObj (fun r => (P r).obj),
        gradedFiniteProjectiveModules_directSumObj_fin P⟩ :
        (gradedFiniteProjectiveModules 𝒜).FullSubcategory) ≅
      P 0 ⊞ ⟨GradedModuleCat.directSumObj (fun r : Fin m => (P r.succ).obj),
        gradedFiniteProjectiveModules_directSumObj_fin (fun r => P r.succ)⟩ := by
  let M := fun r : Fin (m + 1) => (P r).obj
  let Mt := fun r : Fin m => (P r.succ).obj
  let πt : GradedModuleCat.directSumObj M ⟶ GradedModuleCat.directSumObj Mt :=
    ∑ r : Fin m, directSumProj M r.succ ≫ directSumInj Mt r
  let ιt : GradedModuleCat.directSumObj Mt ⟶ GradedModuleCat.directSumObj M :=
    ∑ r : Fin m, directSumProj Mt r ≫ directSumInj M r.succ
  have h0t : directSumInj M 0 ≫ πt = 0 := by
    simp only [πt, Preadditive.comp_sum, ← Category.assoc]
    exact Finset.sum_eq_zero fun r _ => by
      rw [directSumInj_comp_proj_of_ne M (Fin.succ_ne_zero r).symm, zero_comp]
  have ht0 : ιt ≫ directSumProj M 0 = 0 := by
    simp only [ιt, Preadditive.sum_comp, Category.assoc]
    exact Finset.sum_eq_zero fun r _ => by
      rw [directSumInj_comp_proj_of_ne M (Fin.succ_ne_zero r), comp_zero]
  have htt : ιt ≫ πt = 𝟙 (GradedModuleCat.directSumObj Mt) := by
    dsimp only [ιt, πt]; rw [Preadditive.sum_comp]
    simp only [Preadditive.comp_sum, Category.assoc]
    rw [← sum_directSumProj_comp_inj Mt]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single r (fun s _ hsr => by
        rw [← Category.assoc (directSumInj M r.succ),
          directSumInj_comp_proj_of_ne M (Fin.succ_injective _ |>.ne hsr.symm), zero_comp,
          comp_zero])
      (fun hr => absurd (Finset.mem_univ r) hr),
      ← Category.assoc (directSumInj M r.succ), directSumInj_comp_proj_self M r.succ,
      Category.id_comp]
  have htot : directSumProj M 0 ≫ directSumInj M 0 + πt ≫ ιt =
      𝟙 (GradedModuleCat.directSumObj M) := by
    rw [← sum_directSumProj_comp_inj M, Fin.sum_univ_succ]; congr 1
    dsimp only [πt, ιt]; rw [Preadditive.sum_comp]
    simp only [Preadditive.comp_sum, Category.assoc]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single r (fun s _ hsr => by
        rw [← Category.assoc (directSumInj Mt r), directSumInj_comp_proj_of_ne Mt hsr.symm,
          zero_comp, comp_zero])
      (fun hr => absurd (Finset.mem_univ r) hr),
      ← Category.assoc (directSumInj Mt r), directSumInj_comp_proj_self Mt r, Category.id_comp]
  refine
    { hom := biprod.lift (ObjectProperty.homMk (directSumProj M 0)) (ObjectProperty.homMk πt)
      inv := biprod.desc (ObjectProperty.homMk (directSumInj M 0)) (ObjectProperty.homMk ιt)
      hom_inv_id := by
        rw [biprod.lift_desc]
        apply ObjectProperty.hom_ext
        dsimp only [M] at htot ⊢
        exact htot
      inv_hom_id := biprod.hom_ext' _ _
        (biprod.hom_ext _ _
          (ObjectProperty.hom_ext _ (by simpa using directSumInj_comp_proj_self M 0))
          (ObjectProperty.hom_ext _ (by simpa using h0t)))
        (biprod.hom_ext _ _
          (ObjectProperty.hom_ext _ (by simpa using ht0))
          (ObjectProperty.hom_ext _ (by simpa using htt))) }

/-- The class of a `Fin n`-indexed `directSumObj` of finite graded projectives in `K₀^gr(proj A)`
is the sum of the classes of its summands. -/
theorem laurentK0_projective_of_directSumObj_fin {n : ℕ}
    (P : Fin n → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ⟨GradedModuleCat.directSumObj (fun r => (P r).obj),
          gradedFiniteProjectiveModules_directSumObj_fin P⟩ =
      ∑ r : Fin n, LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P r) := by
  induction n with
  | zero =>
      have hz : IsZero (⟨GradedModuleCat.directSumObj (fun r : Fin 0 => (P r).obj),
          gradedFiniteProjectiveModules_directSumObj_fin P⟩ :
          (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :=
        (IsZero.iff_id_eq_zero _).mpr <| ObjectProperty.hom_ext _ <| GradedModuleCat.hom_ext <|
          DirectSum.linearMap_ext _ fun r => Fin.elim0 r
      rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hz, map_zero]
      simp
  | succ m ih =>
      rw [LaurentK0.of_congr.{uA} _ (directSumObjFinSuccIso P), laurentK0_projective_biprod,
        ih (fun r => P r.succ), Fin.sum_univ_succ]

private def retractSumIsoDirectSumFin {n : ℕ}
    (N : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (P : Fin n → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (ι : ∀ r, (P r).obj ⟶ N.obj) (π : ∀ r, N.obj ⟶ (P r).obj)
    (hdiag : ∀ r, ι r ≫ π r = 𝟙 (P r).obj)
    (hoff : ∀ r s, r ≠ s → ι r ≫ π s = 0)
    (hsum : ∑ r : Fin n, π r ≫ ι r = 𝟙 N.obj) :
    N ≅ ⟨GradedModuleCat.directSumObj (fun r => (P r).obj),
      gradedFiniteProjectiveModules_directSumObj_fin P⟩ := by
  let M := fun r : Fin n => (P r).obj
  let f : N.obj ⟶ GradedModuleCat.directSumObj M := ∑ r : Fin n, π r ≫ directSumInj M r
  let g : GradedModuleCat.directSumObj M ⟶ N.obj := ∑ r : Fin n, directSumProj M r ≫ ι r
  refine ObjectProperty.isoMk _
    { hom := f
      inv := g
      hom_inv_id := by
        dsimp only [f, g]; rw [Preadditive.sum_comp]
        simp only [Preadditive.comp_sum, Category.assoc]
        rw [← hsum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_eq_single r
          (fun s _ hsr => by
            rw [← Category.assoc (directSumInj M r), directSumInj_comp_proj_of_ne M hsr.symm,
              zero_comp, comp_zero])
          (fun hr => absurd (Finset.mem_univ r) hr)]
        rw [← Category.assoc (directSumInj M r), directSumInj_comp_proj_self M r, Category.id_comp]
      inv_hom_id := by
        dsimp only [f, g]; rw [Preadditive.sum_comp]
        simp only [Preadditive.comp_sum, Category.assoc]
        rw [← sum_directSumProj_comp_inj M]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_eq_single r
          (fun s _ hsr => by
            rw [← Category.assoc (ι r), hoff r s hsr.symm, zero_comp, comp_zero])
          (fun hr => absurd (Finset.mem_univ r) hr)]
        rw [← Category.assoc (ι r), hdiag r, Category.id_comp] }

/-- In `K₀^gr(proj A)`, any object equipped with finite biproduct injections and projections from
a family `P : J → (gradedFiniteProjectiveModules 𝒜).FullSubcategory` has class equal to the sum
of `[P j]`. The index type `J` may live in any universe. -/
theorem laurentK0_projective_of_retract_sum {J : Type uJ} [Fintype J]
    (N : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (P : J → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (ι : ∀ j, (P j).obj ⟶ N.obj) (π : ∀ j, N.obj ⟶ (P j).obj)
    (hdiag : ∀ j, ι j ≫ π j = 𝟙 (P j).obj)
    (hoff : ∀ i j, i ≠ j → ι i ≫ π j = 0)
    (hsum : ∑ j : J, π j ≫ ι j = 𝟙 N.obj) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) N =
      ∑ j : J, LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P j) := by
  let eqv : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hiso := retractSumIsoDirectSumFin N (fun r => P (eqv r))
    (fun r => ι (eqv r)) (fun r => π (eqv r))
    (fun r => hdiag (eqv r))
    (fun r s hrs => hoff _ _ (eqv.injective.ne hrs))
    ((Equiv.sum_comp eqv (fun j => π j ≫ ι j)).trans hsum)
  rw [LaurentK0.of_congr.{uA} _ hiso, laurentK0_projective_of_directSumObj_fin]
  exact Equiv.sum_comp eqv fun j =>
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P j)

end DirectSumClass

/-! ### Decomposing finite graded projectives -/

section Decomposition

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {I : Type uI} [Fintype I] {e : I → A}
  (he : CompleteOrthogonalIdempotents e)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hneg : ∀ p < 0, 𝒜 p = ⊥)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))

private abbrev posSubmodule (M : GradedModuleCat.{uA} 𝒜) : Submodule k M :=
  (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)

include he hI hneg hspan in
private theorem smul_mem_posSubmodule_sup_span (M : GradedModuleCat.{uA} 𝒜) [DecidableEq M]
    (s : Finset M) (a : A) {u : M}
    (hu : u ∈ posSubmodule M ⊔ Submodule.span k
      ((Finset.univ.biUnion fun i : I => s.image fun g => e i • g : Finset M) : Set M)) :
    a • u ∈ posSubmodule M ⊔ Submodule.span k
      ((Finset.univ.biUnion fun i : I => s.image fun g => e i • g : Finset M) : Set M) := by
  classical
  have he₀ := he.mem_zero_of_isHomogeneous_span 𝒜 hI
  let T : Finset M := Finset.univ.biUnion fun i : I => s.image fun g => e i • g
  let U : Submodule k M := posSubmodule M ⊔ Submodule.span k (T : Set M)
  rw [← sum_support_decompose 𝒜 a, Finset.sum_smul]
  refine U.sum_mem fun r _ => ?_
  rcases lt_trichotomy r 0 with hr0 | rfl | hrpos
  · have ha0 : (decompose 𝒜 a r : A) = 0 :=
      (Submodule.eq_bot_iff _).mp (hneg r hr0) _ (decompose 𝒜 a r).2
    simp [ha0]
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (hspan (decompose 𝒜 a 0).2)
    rw [← hc, Finset.sum_smul]
    refine U.sum_mem fun j _ => ?_
    rw [smul_assoc]
    refine U.smul_mem (c j) ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
    rw [smul_add]
    refine U.add_mem (Submodule.mem_sup_left
      (InternalGrading.smul_mem_positive_smul_top (he₀ j) hy)) ?_
    refine Submodule.mem_sup_right <| Submodule.span_induction (fun w hw => ?_) (by simp)
      (fun _ _ _ _ hw₁ hw₂ => by simpa [smul_add] using add_mem hw₁ hw₂)
      (fun b w _ hw => by rw [smul_comm]; exact Submodule.smul_mem _ b hw) hz
    obtain ⟨i, -, hw'⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hw)
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw'
    by_cases hji : j = i
    · subst hji
      rw [← mul_smul, (he.idem j).eq]
      exact Submodule.subset_span (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ j, Finset.mem_image_of_mem _ hg⟩)
    · rw [← mul_smul, he.ortho hji, zero_smul]
      exact zero_mem _
  · exact Submodule.mem_sup_left <| Submodule.smul_mem_smul
      (Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hrpos (decompose 𝒜 a r).2))
      Submodule.mem_top

include he hI hneg hspan in
private theorem finite_quotient_posSubmodule (M : GradedModuleCat.{uA} 𝒜) [Module.Finite A M] :
    Module.Finite k (M ⧸ posSubmodule M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  let T : Finset M := Finset.univ.biUnion fun i : I => s.image fun g => e i • g
  let U : Submodule k M := posSubmodule M ⊔ Submodule.span k (T : Set M)
  have htop : U = ⊤ := top_unique fun x _ => by
    have hx : x ∈ Submodule.span A (s : Set M) := hs.symm ▸ Submodule.mem_top
    refine Submodule.span_induction (fun g hg => ?_) U.zero_mem
      (fun _ _ _ _ => U.add_mem)
      (fun a _ _ hu => smul_mem_posSubmodule_sup_span he hI hneg hspan M s a hu) hx
    have h1 : g = ∑ i : I, e i • g := by rw [← Finset.sum_smul, he.complete, one_smul]
    rw [h1]
    exact Submodule.mem_sup_right <| Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hg⟩)
  refine Module.Finite.of_fg_top ⟨T.image (posSubmodule M).mkQ, top_unique fun y _ => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : x ∈ U)
  have hu0 : (posSubmodule M).mkQ u = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hu
  rw [← Submodule.mkQ_apply, map_add, hu0, zero_add, Finset.coe_image, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem hz

include he hI in
private theorem iSupIndep_quotientPiece (M : GradedModuleCat.{uA} 𝒜) :
    iSupIndep fun ip : I × ℤ =>
      Submodule.map (posSubmodule M).mkQ (e ip.1 • M.grading.piece ip.2) := by
  classical
  have he₀ := he.mem_zero_of_isHomogeneous_span 𝒜 hI
  refine iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _ |>.mpr fun t f hf hsum ip₀ hip₀ => ?_
  have hchoose : ∀ ip ∈ t, ∃ x ∈ M.grading.piece ip.2,
      (posSubmodule M).mkQ (e ip.1 • x) = f ip := fun ip hip => by
    obtain ⟨w, hw, hfw⟩ := Submodule.mem_map.mp (hf ip hip)
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hw
    exact ⟨x, hx, hfw⟩
  choose x hx hfx using fun ip : {ip // ip ∈ t} => hchoose ip.1 ip.2
  have hz : ∑ ip : {ip // ip ∈ t}, e ip.1.1 • x ip ∈ posSubmodule M := by
    apply (Submodule.Quotient.mk_eq_zero (posSubmodule M)).mp
    -- Express quotient vanishing via the quotient map `mkQ`.
    change (posSubmodule M).mkQ (∑ ip : {ip // ip ∈ t}, e ip.1.1 • x ip) = 0
    rw [map_sum]
    simpa [hfx] using (Finset.sum_attach t f).trans hsum
  have hhom : ∀ ip : {ip // ip ∈ t}, e ip.1.1 • x ip ∈ M.grading.piece ip.1.2 := fun ip => by
    simpa using SetLike.GradedSMul.smul_mem (he₀ ip.1.1) (hx ip)
  have hact := InternalGrading.smul_mem_positive_smul_top (he₀ ip₀.1)
    (M.grading.isHomogeneous_positive_smul_top 𝒜 ip₀.2 hz)
  rw [decompose_sum, DirectSum.sum_apply, Submodule.coe_sum, Finset.smul_sum] at hact
  have hsingle : ∑ ip : {ip // ip ∈ t},
      e ip₀.1 • (decompose M.grading.piece (e ip.1.1 • x ip) ip₀.2 : M) =
        e ip₀.1 • (decompose M.grading.piece (e ip₀.1 • x ⟨ip₀, hip₀⟩) ip₀.2 : M) := by
    refine Finset.sum_eq_single (⟨ip₀, hip₀⟩ : {ip // ip ∈ t}) (fun ip _ hip => ?_)
      (fun h => absurd (Finset.mem_univ _) h)
    by_cases hp : ip.1.2 = ip₀.2
    · have hi : ip₀.1 ≠ ip.1.1 := fun h1 => hip (Subtype.ext (Prod.ext h1.symm hp))
      rw [← hp, decompose_of_mem_same _ (hhom ip), ← mul_smul, he.ortho hi, zero_smul]
    · rw [decompose_of_mem_ne _ (hhom ip) hp, smul_zero]
  rw [hsingle, decompose_of_mem_same _ (hhom ⟨ip₀, hip₀⟩), ← mul_smul, (he.idem ip₀.1).eq] at hact
  rw [← hfx ⟨ip₀, hip₀⟩]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hact

private theorem linearIndependent_sigma_of_iSupIndep {V₀ : Type*} [AddCommGroup V₀] [Module k V₀]
    {α : Type*} (W : α → Submodule k V₀) (hW : iSupIndep W)
    {β : α → Type*} (b : ∀ a, β a → W a) (hb : ∀ a, LinearIndependent k (b a)) :
    LinearIndependent k (fun j : Σ a, β a => (b j.1 j.2 : V₀)) := by
  classical
  refine linearIndependent_iff'.mpr fun s g hg j₀ hj₀ => ?_
  have hfib : ∑ a ∈ s.image Sigma.fst,
      (∑ j ∈ s.filter (fun j => j.1 = a), g j • (b j.1 j.2 : V₀)) = 0 :=
    (Finset.sum_fiberwise_of_maps_to
      (fun _ hj => Finset.mem_image_of_mem Sigma.fst hj) _).trans hg
  have hfmem : ∀ a ∈ s.image Sigma.fst,
      (∑ j ∈ s.filter (fun j => j.1 = a), g j • (b j.1 j.2 : V₀)) ∈ W a := fun a _ =>
    Submodule.sum_mem _ fun j hj => by
      rcases j with ⟨a', y⟩
      obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hj
      exact Submodule.smul_mem _ _ (b a' y).2
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero W).mp hW _ _ hfmem hfib j₀.1
    (Finset.mem_image_of_mem _ hj₀)
  let t : Finset (β j₀.1) := s.biUnion fun j => if h : j.1 = j₀.1 then {h ▸ j.2} else ∅
  have ht : ∑ y ∈ t, g ⟨j₀.1, y⟩ • b j₀.1 y = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, ZeroMemClass.coe_zero, ← hz]
    refine Finset.sum_bij (fun y _ => ⟨j₀.1, y⟩)
      (fun y hy => ?_) (fun _ _ _ _ h => (Sigma.mk.inj_iff.mp h).2 |> eq_of_heq)
      (fun j hj => ?_) (fun _ _ => rfl)
    · obtain ⟨⟨a, y'⟩, hj, hy'⟩ := Finset.mem_biUnion.mp hy
      by_cases h : a = j₀.1
      · subst h
        rcases Finset.mem_singleton.mp (by simpa using hy') with rfl
        exact Finset.mem_filter.mpr ⟨hj, rfl⟩
      · simp [h] at hy'
    · rcases j with ⟨a, y⟩
      obtain ⟨hjs, rfl⟩ := Finset.mem_filter.mp hj
      exact ⟨y, Finset.mem_biUnion.mpr ⟨⟨j₀.1, y⟩, hjs, by simp⟩, rfl⟩
  exact linearIndependent_iff'.mp (hb j₀.1) t (fun y => g ⟨j₀.1, y⟩) ht j₀.2
    (Finset.mem_biUnion.mpr ⟨j₀, hj₀, by simp⟩)

include he hI hneg hspan in
private theorem exists_coeff_sub_sum_lof_mem_posSubmodule {n : ℕ} (idx : Fin n → I)
    (d : Fin n → ℤ)
    (y : GradedModuleCat.directSumObj fun r : Fin n =>
      (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r)) :
    ∃ c : Fin n → k,
      y - ∑ r : Fin n, c r • DirectSum.lof A (Fin n)
        (fun t => (Ideal.span {e (idx t)} : Ideal A)) r (spanSingletonGenerator (e (idx r))) ∈
        posSubmodule (GradedModuleCat.directSumObj fun r : Fin n =>
          (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r)) := by
  classical
  let Pobj := GradedModuleCat.directSumObj fun r : Fin n =>
    (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r)
  let gen (r : Fin n) : Pobj := DirectSum.lof A (Fin n)
    (fun t => (Ideal.span {e (idx t)} : Ideal A)) r (spanSingletonGenerator (e (idx r)))
  have hcoord : ∀ r : Fin n, ∃ cr : k,
      DirectSum.lof A (Fin n) (fun t => (Ideal.span {e (idx t)} : Ideal A)) r (y r) -
        cr • gen r ∈ posSubmodule Pobj := fun r => by
    obtain ⟨cr, hcr⟩ := exists_eq_smul_of_mem_zero he.toOrthogonalIdempotents hspan
      (decompose 𝒜 (y r : A) 0).2 (hI (idx r) 0 (y r).2)
    have hval : (y r : A) - cr • e (idx r) =
        ∑ q ∈ (decompose 𝒜 (y r : A)).support.erase 0, (decompose 𝒜 (y r : A) q : A) := by
      have hsum := sum_support_decompose 𝒜 (y r : A)
      by_cases h0 : 0 ∈ (decompose 𝒜 (y r : A)).support
      · rw [← Finset.add_sum_erase _ _ h0, hcr] at hsum; exact sub_eq_of_eq_add' hsum.symm
      · have hz0 : (decompose 𝒜 (y r : A) 0 : A) = 0 := by
          simpa [DFinsupp.mem_support_toFun] using h0
        rw [hz0] at hcr; rw [← hcr, sub_zero, Finset.erase_eq_of_notMem h0]; exact hsum.symm
    have hegen : e (idx r) • gen r = gen r := by
      rw [← map_smul]; congr 1
      exact Subtype.ext (by simpa [coe_spanSingletonGenerator] using (he.idem (idx r)).eq)
    have hlof : DirectSum.lof A (Fin n) (fun t => (Ideal.span {e (idx t)} : Ideal A)) r (y r) -
        cr • gen r = ((y r : A) - cr • e (idx r)) • gen r := by
      rw [sub_smul]; congr 1
      · rw [← map_smul]; congr 1; exact Subtype.ext <| by
          simpa [coe_spanSingletonGenerator] using
            ((mem_span_singleton_iff_mul_eq_self (he.idem (idx r))).mp (y r).2).symm
      · rw [smul_assoc, hegen]
    refine ⟨cr, ?_⟩; rw [hlof, hval, Finset.sum_smul]
    refine Submodule.sum_mem _ fun q hq => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hq) with hlt | hgt
    · simp [(Submodule.eq_bot_iff _).mp (hneg q hlt) _ (decompose 𝒜 (y r : A) q).2]
    · exact Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hgt (decompose 𝒜 (y r : A) q).2))
        Submodule.mem_top
  choose c hc using hcoord
  refine ⟨c, ?_⟩
  have hysum : y - ∑ r : Fin n, c r • gen r =
      ∑ r : Fin n, (DirectSum.lof A (Fin n) (fun t => (Ideal.span {e (idx t)} : Ideal A)) r (y r) -
        c r • gen r) := by
    conv_lhs => rw [← DirectSum.sum_univ_of y]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by rw [DirectSum.lof_eq_of]
  rw [hysum]; exact Submodule.sum_mem _ fun r _ => hc r

private def minimalCoverHom (M : GradedModuleCat.{uA} 𝒜)
    {n : ℕ} (idx : Fin n → I) {d : Fin n → ℤ} {m : Fin n → M}
    (hm : ∀ r, m r ∈ M.grading.piece (d r)) :
    (GradedModuleCat.directSumObj fun r : Fin n =>
      (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r)) ⟶ M :=
  GradedModuleCat.ofHom
    (DirectSum.toModule A (Fin n) M fun r =>
      (LinearMap.toSpanSingleton A M (m r)).comp (Ideal.span {e (idx r)}).subtype)
    (LinearMap.isHomogeneous_def.mpr fun p y hy => by
      rw [add_zero, ← DirectSum.sum_univ_of y, map_sum]
      refine Submodule.sum_mem _ fun r _ => ?_
      have hyr := (GradedModuleCat.mem_coproductCofan_pt_piece_iff _).mp hy r
      have hz' := ((GradedModuleCat.mem_shiftObj_piece_iff _ _ _ _).trans
        (GradedModuleCat.mem_ofIdeal_piece_iff (hI (idx r)))).mp hyr
      rw [← DirectSum.lof_eq_of A, DirectSum.toModule_lof, LinearMap.comp_apply,
        Submodule.coe_subtype, LinearMap.toSpanSingleton_apply]
      simpa using SetLike.GradedSMul.smul_mem hz' (hm r))

include he hI hneg in
private theorem minimalCoverHom_surjective (M : GradedModuleCat.{uA} 𝒜) [Module.Finite A M]
    {n : ℕ} (idx : Fin n → I) {d : Fin n → ℤ} {m : Fin n → M}
    (hm : ∀ r, m r ∈ M.grading.piece (d r))
    (hme : ∀ r, e (idx r) • m r = m r)
    (hspanV : ∀ (i : I) (p : ℤ) (x : M), x ∈ M.grading.piece p →
      ∃ c : Fin n → k, (posSubmodule M).mkQ (e i • x) =
        ∑ r : Fin n, c r • (posSubmodule M).mkQ (m r)) :
    Function.Surjective (minimalCoverHom hI M idx hm).hom := by
  let π := minimalCoverHom hI M idx hm
  rw [← LinearMap.range_eq_top]
  obtain ⟨b, hb⟩ := M.grading.exists_piece_eq_bot_of_lt 𝒜 hneg
  refine M.grading.eq_top_of_piece_le_sup_positive_smul_top 𝒜 (LinearMap.range π.hom)
    (LinearMap.IsHomogeneous.isHomogeneous_range π.isHomogeneous) b hb fun p x hx => ?_
  have hxsum : x = ∑ i : I, e i • x := by rw [← Finset.sum_smul, he.complete, one_smul]
  rw [hxsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := hspanV i p x hx
  let z : M := ∑ r : Fin n, c r • m r
  have hzrange : z ∈ (LinearMap.range π.hom).restrictScalars k := by
    refine Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ (c r) ?_
    refine ⟨DirectSum.lof A (Fin n)
      (fun t => (Ideal.span {e (idx t)} : Ideal A)) r (spanSingletonGenerator (e (idx r))), ?_⟩
    dsimp only [π, minimalCoverHom, GradedModuleCat.hom_ofHom]
    rw [DirectSum.toModule_lof, LinearMap.comp_apply, Submodule.coe_subtype,
      LinearMap.toSpanSingleton_apply, coe_spanSingletonGenerator, hme r]
  have hdiff : e i • x - z ∈ posSubmodule M := by
    apply (Submodule.Quotient.mk_eq_zero (posSubmodule M)).mp
    -- Compare images in `M ⧸ posSubmodule M` via `mkQ`.
    change (posSubmodule M).mkQ (e i • x - z) = 0
    simpa [z, map_sub, map_sum, map_smul, sub_eq_zero] using hc
  exact Submodule.mem_sup.mpr ⟨z, hzrange, e i • x - z, hdiff, by abel⟩

include he hI hneg hspan in
private theorem exists_minimal_idempotent_cover (M : GradedModuleCat.{uA} 𝒜) [Module.Finite A M] :
    ∃ (n : ℕ) (idx : Fin n → I) (d : Fin n → ℤ)
      (π : GradedModuleCat.directSumObj
        (fun r : Fin n => (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)})
          (hI (idx r))).shiftObj (d r)) ⟶ M),
      Function.Surjective π.hom ∧
      ∀ y, π.hom y = 0 → y ∈ posSubmodule _ := by
  classical
  have he₀ := he.mem_zero_of_isHomogeneous_span 𝒜 hI
  let _ : Module.Finite k (M ⧸ posSubmodule M) := finite_quotient_posSubmodule he hI hneg hspan M
  let V (ip : I × ℤ) : Submodule k (M ⧸ posSubmodule M) :=
    Submodule.map (posSubmodule M).mkQ (e ip.1 • M.grading.piece ip.2)
  let B (ip : I × ℤ) := Module.Basis.ofVectorSpace k (V ip)
  let J := Σ ip : I × ℤ, Module.Basis.ofVectorSpaceIndex k (V ip)
  have hliV : LinearIndependent k (fun j : J => (B j.1 j.2 : M ⧸ posSubmodule M)) :=
    linearIndependent_sigma_of_iSupIndep V (iSupIndep_quotientPiece he hI M)
      (fun ip => B ip) (fun ip => (B ip).linearIndependent)
  have : Finite J := hliV.finite_of_isNoetherian
  let _ : Fintype J := Fintype.ofFinite J
  let eqv : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let idx (r : Fin (Fintype.card J)) : I := (eqv r).1.1
  let d (r : Fin (Fintype.card J)) : ℤ := (eqv r).1.2
  have hlift : ∀ r : Fin (Fintype.card J), ∃ m ∈ M.grading.piece (d r),
      e (idx r) • m = m ∧ (posSubmodule M).mkQ m = B (eqv r).1 (eqv r).2 := fun r => by
    obtain ⟨w, hw, hbw⟩ := Submodule.mem_map.mp (B (eqv r).1 (eqv r).2).2
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hw
    refine ⟨e (idx r) • x, by simpa [idx, d] using SetLike.GradedSMul.smul_mem (he₀ _) hx,
      by rw [← mul_smul, (he.idem _).eq], hbw⟩
  choose m hm hme hmk using hlift
  let π := minimalCoverHom hI M idx hm
  refine ⟨Fintype.card J, idx, d, π, minimalCoverHom_surjective he hI hneg M idx hm hme
    fun i p x hx => ?_, fun y hy => ?_⟩
  · let v : V (i, p) := ⟨(posSubmodule M).mkQ (e i • x),
      Submodule.mem_map_of_mem (Submodule.smul_mem_pointwise_smul x _ _ hx)⟩
    refine ⟨fun r => ∑ s ∈ ((B (i, p)).repr v).support,
      if r = eqv.symm ⟨(i, p), s⟩ then (B (i, p)).repr v s else 0, ?_⟩
    have hv_eq := congrArg Subtype.val ((B (i, p)).linearCombination_repr v)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum] at hv_eq
    simp only [Finset.sum_smul, ite_smul, zero_smul]; rw [Finset.sum_comm]
    refine hv_eq.symm.trans (Finset.sum_congr rfl fun s _ => ?_)
    rw [Submodule.coe_smul_of_tower, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), hmk,
      eqv.apply_symm_apply]
  · obtain ⟨c, hc⟩ := exists_coeff_sub_sum_lof_mem_posSubmodule he hI hneg hspan idx d y
    have hmap := InternalGrading.map_mem_positive_smul_top 𝒜 π.hom hc
    rw [map_sub, hy, zero_sub, neg_mem_iff, map_sum] at hmap
    have hπgen : ∀ r, π.hom (DirectSum.lof A (Fin (Fintype.card J))
        (fun t => (Ideal.span {e (idx t)} : Ideal A)) r (spanSingletonGenerator (e (idx r)))) =
          m r := fun r => by
      dsimp only [π, minimalCoverHom, GradedModuleCat.hom_ofHom]
      rw [DirectSum.toModule_lof, LinearMap.comp_apply, Submodule.coe_subtype,
        LinearMap.toSpanSingleton_apply, coe_spanSingletonGenerator, hme r]
    have hrel : ∑ r : Fin (Fintype.card J),
        c r • (B (eqv r).1 (eqv r).2 : M ⧸ posSubmodule M) = 0 := by
      have hq := (Submodule.Quotient.mk_eq_zero (posSubmodule M)).mpr hmap
      -- Express quotient vanishing via `mkQ` and evaluate `π` on each generator.
      change (posSubmodule M).mkQ (∑ r, π.hom (c r • _)) = 0 at hq
      simpa [LinearMap.map_smul_of_tower, hπgen, map_sum, map_smul, hmk] using hq
    have hc0 : ∀ r, c r = 0 := fun r =>
      linearIndependent_iff'.mp (hliV.comp eqv eqv.injective) Finset.univ c hrel r
        (Finset.mem_univ r)
    simpa [hc0] using hc

include he hI hneg hspan in
/-- **Every finite graded projective decomposes into shifted idempotent ideals.** Over a
nonnegatively graded algebra whose degree-zero piece is spanned over a field `k` by complete
orthogonal idempotents `eᵢ` with homogeneous left ideals `A eᵢ`, any finite graded projective `P`
is isomorphic in `GradedModuleCat 𝒜` to a finite direct sum `⨁ᵣ (A e_{idx r}){d r}`. No
finite-dimensionality of `A` over `k` is required. -/
theorem exists_iso_directSum_ofIdeal_span_singleton
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    ∃ (n : ℕ) (idx : Fin n → I) (d : Fin n → ℤ),
      Nonempty (P.obj ≅ GradedModuleCat.directSumObj fun r : Fin n =>
        (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r)) := by
  let _ : Module.Finite A P.obj := (gradedFiniteProjectiveModules_iff.mp P.property).1
  let _ : Module.Projective A P.obj := (gradedFiniteProjectiveModules_iff.mp P.property).2
  obtain ⟨n, idx, d, π, hsurj, hmin⟩ := exists_minimal_idempotent_cover he hI hneg hspan P.obj
  have : Epi π := (GradedModuleCat.epi_iff_surjective π).mpr hsurj
  let σ := Projective.factorThru (𝟙 P.obj) π
  have hσ : σ ≫ π = 𝟙 P.obj := Projective.factorThru_comp _ _
  let K := GradedModuleCat.kernelObj π
  let _ : SetLike.GradedSMul 𝒜 K.grading.piece := K.gradedSMul
  let ρ : _ ⟶ _ := 𝟙 _ - π ≫ σ
  have hρπ : ρ ≫ π = 0 := by simp [ρ, Category.assoc, hσ]
  let rK : _ ⟶ K := GradedModuleCat.ofHom
    (ρ.hom.codRestrict (LinearMap.ker π.hom) fun x => by
      simpa using congrArg (fun φ => φ.hom x) hρπ)
    (LinearMap.isHomogeneous_def.mpr fun p x hx => by
      rw [add_zero, InternalGrading.mem_ker_piece, LinearMap.codRestrict_apply]
      exact GradedModuleCat.map_mem ρ hx)
  have htop : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k K) = ⊤ :=
    top_unique fun x _ => by
      have hxK : rK.hom x.1 = x := Subtype.ext <| by
        have hx0 : π.hom x.1 = 0 := x.2
        -- Unfold `rK.hom` to its `codRestrict` action `ρ.hom x.1` in the ambient module.
        change ρ.hom x.1 = x.1
        simp [ρ, hx0]
      rw [← hxK]
      exact InternalGrading.map_mem_positive_smul_top 𝒜 rK.hom (hmin x.1 x.2)
  let _ : ∀ r : Fin n, Module.Finite A
      ((GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r)) :=
    fun r => (gradedFiniteProjectiveModules_iff.mp
      (gradedFiniteProjectiveModules_shiftObj
        (gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem (idx r)) (hI (idx r)))
        (d r))).1
  let Qobj := GradedModuleCat.directSumObj fun r : Fin n =>
    (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r)
  let _ : SetLike.GradedSMul 𝒜 Qobj.grading.piece := Qobj.gradedSMul
  obtain ⟨b, hb⟩ := Qobj.grading.exists_piece_eq_bot_of_lt 𝒜 hneg
  have hbK : ∀ p < b, K.grading.piece p = ⊥ := fun p hp =>
    (Submodule.eq_bot_iff _).mpr fun x hx => Subtype.ext <|
      (Submodule.eq_bot_iff _).mp (hb p hp) x.1 ((InternalGrading.mem_ker_piece _ _).mp hx)
  have : Subsingleton K := K.grading.subsingleton_of_positive_smul_top_eq_top 𝒜 b hbK htop
  have hinj : Function.Injective π.hom :=
    (LinearMap.ker_eq_bot).mp ((Submodule.eq_bot_iff _).mpr fun x hx =>
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : K) 0))
  have : IsIso π := (GradedModuleCat.isIso_iff_bijective π).mpr ⟨hinj, hsurj⟩
  exact ⟨n, idx, d, ⟨(asIso π).symm⟩⟩

/-! ### The projective basis without `[Module.Finite k A]` -/

section Basis

variable (hne : ∀ i, e i ≠ 0)

omit [GradedAlgebra 𝒜] in
private def shiftObjHomLinearEquiv (M N : GradedModuleCat.{uA} 𝒜) (m : ℤ) :
    (M.shiftObj m ⟶ N) ≃ₗ[k] (M ⟶ N.shiftObj (-m)) where
  toFun f := GradedModuleCat.ofHom f.hom <| LinearMap.isHomogeneous_def.mpr fun p x hx => by
    rw [add_zero, GradedModuleCat.mem_shiftObj_piece_iff, sub_neg_eq_add]
    exact GradedModuleCat.map_mem f <| by
      rwa [GradedModuleCat.mem_shiftObj_piece_iff, add_sub_cancel_right]
  invFun g := GradedModuleCat.ofHom g.hom <| LinearMap.isHomogeneous_def.mpr fun p x hx => by
    rw [add_zero]; rw [GradedModuleCat.mem_shiftObj_piece_iff] at hx
    have hg := GradedModuleCat.map_mem g hx
    rwa [GradedModuleCat.mem_shiftObj_piece_iff, sub_neg_eq_add, sub_add_cancel] at hg
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [GradedAlgebra 𝒜] in
private def shiftZeroHomLinearEquiv (M N : GradedModuleCat.{uA} 𝒜) :
    (M ⟶ N) ≃ₗ[k] (M ⟶ N.shiftObj 0) where
  toFun f := GradedModuleCat.ofHom f.hom <| LinearMap.isHomogeneous_def.mpr fun p x hx => by
    rw [add_zero, GradedModuleCat.mem_shiftObj_piece_iff, sub_zero]
    exact GradedModuleCat.map_mem f hx
  invFun g := GradedModuleCat.ofHom g.hom <| LinearMap.isHomogeneous_def.mpr fun p x hx => by
    rw [add_zero]
    have hg := GradedModuleCat.map_mem g hx
    rwa [GradedModuleCat.mem_shiftObj_piece_iff, sub_zero] at hg
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include he hI hneg hspan hne in
private theorem finrank_hom_head_shiftObj [DecidableEq I] (i j : I) (m : ℤ) :
    Module.finrank k
      ((GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i)).shiftObj m ⟶
        gradedPositiveMulQuotient 𝒜 (he.mem_zero_of_isHomogeneous_span 𝒜 hI j)) =
      if i = j ∧ m = 0 then 1 else 0 := by
  have he₀ := he.mem_zero_of_isHomogeneous_span 𝒜 hI
  let S := gradedPositiveMulQuotient 𝒜 (he₀ j)
  rw [(shiftObjHomLinearEquiv (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i)) S m).finrank_eq,
    (GradedModuleCat.ofIdealSpanSingletonHomEquiv (he.idem i) (he₀ i) (hI i) _).finrank_eq]
  -- Unfold `(S.shiftObj (-m)).grading` back to `S.shiftObj (-m)` so `hpiece`/`hebot` rewrite.
  change Module.finrank k ↥(e i • (S.shiftObj (-m)).grading.piece 0) = _
  by_cases hm : m = 0
  · subst hm
    have hpiece : (S.shiftObj (-0)).grading.piece 0 = ⊤ := top_unique fun y _ => by
      rw [GradedModuleCat.mem_shiftObj_piece_iff, neg_zero, sub_zero,
        gradedPositiveMulQuotient_piece_zero_eq_top hneg (he.idem j) (he₀ j)]; trivial
    let _ : Module.Finite k S := Module.finite_of_finrank_eq_succ
      (finrank_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan j (hne j))
    let g : S := gradedPositiveMulQuotientMk (he₀ j) (spanSingletonGenerator (e j))
    have hg : g ≠ 0 :=
      gradedPositiveMulQuotientMk_spanSingletonGenerator_ne_zero hneg (he₀ j) (hne j)
    have hspanS : Submodule.span k {g} = (⊤ : Submodule k S) :=
      Submodule.eq_top_of_finrank_eq <| (finrank_span_singleton hg).trans
        (finrank_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan j (hne j)).symm
    rw [hpiece, ← hspanS, Submodule.smul_span, Set.smul_set_singleton]
    by_cases hij : i = j
    · subst hij
      have heg : e i • g = g := by
        rw [← map_smul]; congr 1
        exact Subtype.ext (by simpa [coe_spanSingletonGenerator] using (he.idem i).eq)
      rw [heg, finrank_span_singleton hg]; simp
    · have heg : e i • g = 0 := by
        rw [← map_smul, show e i • spanSingletonGenerator (e j) = 0 from
          Subtype.ext (by simpa [coe_spanSingletonGenerator] using he.ortho hij), map_zero]
      simp [hij, heg]
  · have hebot : e i • (S.shiftObj (-m)).grading.piece 0 = ⊥ :=
      (Submodule.eq_bot_iff _).mpr fun z hz => by
        obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
        rw [GradedModuleCat.mem_shiftObj_piece_iff, sub_neg_eq_add, zero_add] at hy
        simp [(Submodule.eq_bot_iff _).mp
          (gradedPositiveMulQuotient_piece_eq_bot hneg (he.idem j) (he₀ j) hm) y hy]
    rw [hebot, finrank_bot]; simp [hm]

omit [GradedAlgebra 𝒜] in
private def splitShortComplexHomLinearEquiv
    {S : ShortComplex (gradedFiniteProjectiveModules 𝒜).FullSubcategory}
    (σ : S.Splitting) (N : GradedModuleCat.{uA} 𝒜) :
    (S.X₂.obj ⟶ N) ≃ₗ[k] (S.X₁.obj ⟶ N) × (S.X₃.obj ⟶ N) :=
  let F := (gradedFiniteProjectiveModules 𝒜).ι
  let α : F.obj S.X₂ ⟶ F.obj (S.X₁ ⊞ S.X₃) := F.map σ.isoBinaryBiproduct.hom
  let β : F.obj (S.X₁ ⊞ S.X₃) ⟶ F.obj S.X₂ := F.map σ.isoBinaryBiproduct.inv
  let i₁ : F.obj S.X₁ ⟶ F.obj (S.X₁ ⊞ S.X₃) := F.map biprod.inl
  let i₂ : F.obj S.X₃ ⟶ F.obj (S.X₁ ⊞ S.X₃) := F.map biprod.inr
  let p₁ : F.obj (S.X₁ ⊞ S.X₃) ⟶ F.obj S.X₁ := F.map biprod.fst
  let p₂ : F.obj (S.X₁ ⊞ S.X₃) ⟶ F.obj S.X₃ := F.map biprod.snd
  { toFun f := (i₁ ≫ β ≫ f, i₂ ≫ β ≫ f)
    invFun fg := α ≫ (p₁ ≫ fg.1 + p₂ ≫ fg.2)
    left_inv f := by
      have htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 (F.obj (S.X₁ ⊞ S.X₃)) := by
        rw [← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
      have hαβ : α ≫ β = 𝟙 (F.obj S.X₂) := by
        rw [← F.map_comp, σ.isoBinaryBiproduct.hom_inv_id, F.map_id]
      calc
        α ≫ (p₁ ≫ (i₁ ≫ β ≫ f) + p₂ ≫ (i₂ ≫ β ≫ f)) =
            α ≫ ((p₁ ≫ i₁ + p₂ ≫ i₂) ≫ β ≫ f) := by simp [Preadditive.add_comp, Category.assoc]
        _ = f := by rw [htot, Category.id_comp, ← Category.assoc, hαβ, Category.id_comp]
    right_inv fg := by
      have hβα : β ≫ α = 𝟙 (F.obj (S.X₁ ⊞ S.X₃)) := by
        rw [← F.map_comp, σ.isoBinaryBiproduct.inv_hom_id, F.map_id]
      have h11 : i₁ ≫ p₁ = 𝟙 (F.obj S.X₁) := by rw [← F.map_comp, biprod.inl_fst, F.map_id]
      have h12 : i₁ ≫ p₂ = 0 := by rw [← F.map_comp, biprod.inl_snd, F.map_zero]
      have h21 : i₂ ≫ p₁ = 0 := by rw [← F.map_comp, biprod.inr_fst, F.map_zero]
      have h22 : i₂ ≫ p₂ = 𝟙 (F.obj S.X₃) := by rw [← F.map_comp, biprod.inr_snd, F.map_id]
      refine Prod.ext ?_ ?_
      · dsimp only
        rw [← Category.assoc β, hβα, Category.id_comp, Preadditive.comp_add, ← Category.assoc,
          h11, ← Category.assoc, h12, zero_comp, add_zero]
        exact Category.id_comp fg.1
      · dsimp only
        rw [← Category.assoc β, hβα, Category.id_comp, Preadditive.comp_add, ← Category.assoc,
          h21, zero_comp, zero_add, ← Category.assoc, h22]
        exact Category.id_comp fg.2
    map_add' _ _ := by ext <;> simp
    map_smul' _ _ := by ext <;> simp }

include he hI hneg hspan hne in
private def homHeadInvariant (j : I) :
    ExactK0.AdditiveInvariant (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure ℤ
    where
  obj X := Module.finrank k
    (X.obj ⟶ gradedPositiveMulQuotient 𝒜 (he.mem_zero_of_isHomogeneous_span 𝒜 hI j))
  map_conflation S hS := by
    have he₀ := he.mem_zero_of_isHomogeneous_span 𝒜 hI
    let Sj := gradedPositiveMulQuotient 𝒜 (he₀ j)
    let _ : Module.Finite k Sj := Module.finite_of_finrank_eq_succ
      (finrank_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan j (hne j))
    have hfin : ∀ P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory,
        Module.Finite k (P.obj ⟶ Sj) := fun P => by
      let _ : Module.Finite A P.obj := (gradedFiniteProjectiveModules_iff.mp P.property).1
      let _ : Module.Finite k (P.obj ⟶ Sj.shiftObj 0) :=
        (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj P.obj Sj).finiteDimensional 0
      exact Module.Finite.equiv (shiftZeroHomLinearEquiv P.obj Sj).symm
    let _ := hfin S.X₁
    let _ := hfin S.X₃
    rw [gradedFiniteProjectiveModulesExactStructure_eq_split, ExactStructure.split_conflation] at hS
    obtain ⟨σ⟩ := hS
    rw [(splitShortComplexHomLinearEquiv σ Sj).finrank_eq, Module.finrank_prod, Nat.cast_add]

include he hI hneg hspan hne in
private def homHeadCoord (j : I) :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) →+ ℤ :=
  (ExactK0.lift (homHeadInvariant he hI hneg hspan hne j) :
      ExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure →+ ℤ).comp
    (LaurentK0.ofExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)).symm.toAddMonoidHom

include he hI hneg hspan hne in
private theorem homHeadCoord_smul_idempotent [DecidableEq I] (j i : I)
    (c : LaurentPolynomial ℤ) :
    homHeadCoord he hI hneg hspan hne j
        (c • LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
            gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩) =
      if i = j then c.coeff 0 else 0 := by
  induction c using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [add_smul, map_add, hp, hq]
      split_ifs <;> simp
  | C_mul_T m a =>
      have hiP := gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)
      rw [mul_smul, ← laurentK0_projective_of_shiftObj, ← LaurentPolynomial.single_eq_C_mul_T,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply, LaurentPolynomial.C_eq_algebraMap,
        algebraMap_smul, map_zsmul]
      have hval : homHeadCoord he hI hneg hspan hne j
          (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
            ⟨(GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i)).shiftObj m,
              gradedFiniteProjectiveModules_shiftObj hiP m⟩) =
          if i = j ∧ m = 0 then 1 else 0 := by
        rw [homHeadCoord, AddMonoidHom.comp_apply, ← LaurentK0.ofExactK0_exactK0_of,
          AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply, ExactK0.lift_of]
        dsimp [homHeadInvariant]
        exact_mod_cast finrank_hom_head_shiftObj he hI hneg hspan hne i j m
      rw [hval]
      by_cases hij : i = j <;> by_cases hm : m = 0 <;> simp [hij, hm]

include he hI in
private theorem laurentK0_projective_of_iso_directSum_ofIdeal
    {P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory}
    {n : ℕ} {idx : Fin n → I} {d : Fin n → ℤ}
    (iso : P.obj ≅ GradedModuleCat.directSumObj fun r : Fin n =>
      (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r)) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P =
      ∑ r : Fin n, (T (d r) : LaurentPolynomial ℤ) •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r)),
            gradedFiniteProjectiveModules_ofIdeal_span_singleton
              (he.idem (idx r)) (hI (idx r))⟩ := by
  let Q : Fin n → (gradedFiniteProjectiveModules 𝒜).FullSubcategory := fun r =>
    ⟨(GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj (d r),
      gradedFiniteProjectiveModules_shiftObj
        (gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem (idx r)) (hI (idx r)))
        (d r)⟩
  let Qsum : (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
    ⟨GradedModuleCat.directSumObj (fun r => (Q r).obj),
      gradedFiniteProjectiveModules_directSumObj_fin Q⟩
  rw [LaurentK0.of_congr.{uA} _ (ObjectProperty.isoMk (gradedFiniteProjectiveModules 𝒜)
      (X := P) (Y := Qsum) iso),
    laurentK0_projective_of_directSumObj_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact laurentK0_projective_of_shiftObj
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r)),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem (idx r)) (hI (idx r))⟩
    (d r)

include he hI hneg hspan hne in
/-- **The graded projectives `A eᵢ` form a `ℤ[q,q⁻¹]`-basis of `K₀^gr(proj A)` without
finite-dimensionality.** Let `A` be a nonnegatively graded `k`-algebra over a field `k` whose
degree-zero piece `𝒜 0` is spanned by complete orthogonal nonzero idempotents `eᵢ` with
homogeneous left ideals `A eᵢ`. Then the classes `[A eᵢ]` form a `ℤ[q,q⁻¹]`-basis of
`K₀^gr(proj A)`, even when `A` is infinite-dimensional over `k` (such as `k[X]` or path algebras
with oriented cycles). -/
def gradedSplitProjectiveBasis :
    Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :=
  Module.Basis.mk
    (v := fun i => LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
        gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩)
    (by
      classical
      refine linearIndependent_iff'.mpr fun s g hg j hj =>
        AddMonoidAlgebra.ext (Finsupp.ext fun p => ?_)
      have h := congrArg (fun x => homHeadCoord he hI hneg hspan hne j
        ((T (-p) : LaurentPolynomial ℤ) • x)) hg
      rw [Finset.smul_sum, map_sum, smul_zero, map_zero] at h
      have hsum : (∑ i ∈ s, homHeadCoord he hI hneg hspan hne j
          ((T (-p) : LaurentPolynomial ℤ) • (g i •
            LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
              ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
                gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩))) =
          (T (-p) * g j).coeff 0 := by
        rw [Finset.sum_eq_single j (fun i _ hij => ?_) (fun h' => absurd hj h')]
        · simp [smul_smul, homHeadCoord_smul_idempotent he hI hneg hspan hne]
        · simp [smul_smul, homHeadCoord_smul_idempotent he hI hneg hspan hne, hij]
      rw [hsum, T, AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff p (fun _ _ => by omega),
        one_mul] at h
      exact h)
    (fun x _ => by
      have hmem : ∀ x₀ :
          ExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure,
          LaurentK0.ofExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) x₀ ∈
            Submodule.span (LaurentPolynomial ℤ) (Set.range fun i =>
              LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
                ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
                  gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩) := by
        intro x₀
        induction x₀ using ExactK0.induction_on with
        | zero => simp
        | of P =>
            obtain ⟨n, idx, d, ⟨iso⟩⟩ :=
              exists_iso_directSum_ofIdeal_span_singleton he hI hneg hspan P
            rw [LaurentK0.ofExactK0_exactK0_of.{uA},
              laurentK0_projective_of_iso_directSum_ofIdeal he hI iso]
            exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
              (Submodule.subset_span ⟨idx r, rfl⟩)
        | add _ _ hx₁ hx₂ => simpa only [map_add] using add_mem hx₁ hx₂
        | neg _ hx₁ => simpa only [map_neg] using neg_mem hx₁
      obtain ⟨x₀, rfl⟩ :=
        (LaurentK0.ofExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)).surjective x
      exact hmem x₀)

/-- The basis vector of `TauCeti.gradedSplitProjectiveBasis` at `i` is the class `[A eᵢ]`. -/
@[simp]
theorem gradedSplitProjectiveBasis_apply (i : I) :
    gradedSplitProjectiveBasis he hI hneg hspan hne i =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
          gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩ := by
  unfold gradedSplitProjectiveBasis
  exact Module.Basis.mk_apply _ _ i

/-! ### Degree-generation and coordinate support -/

omit [GradedAlgebra 𝒜] in
private theorem isGeneratedInDegree_of_surjective {M N : GradedModuleCat.{uA} 𝒜}
    (f : M ⟶ N) (hf : Function.Surjective f.hom) {d₀ : ℤ}
    (hM : M.grading.IsGeneratedInDegree A d₀) :
    N.grading.IsGeneratedInDegree A d₀ :=
  (N.grading.isGeneratedInDegree_iff d₀).mpr fun y => by
    obtain ⟨x, rfl⟩ := hf y
    have hx := (M.grading.isGeneratedInDegree_iff d₀).mp hM x
    exact Submodule.span_induction
      (fun z hz => Submodule.subset_span <| by simpa using GradedModuleCat.map_mem f hz)
      (by simp) (fun _ _ _ _ hw₁ hw₂ => by simpa [map_add] using add_mem hw₁ hw₂)
      (fun a _ _ hw => by simpa [map_smul] using Submodule.smul_mem _ a hw) hx

include he hI hneg hne in
private theorem isGeneratedInDegree_ofIdeal_shiftObj_iff (i : I) (m d₀ : ℤ) :
    ((GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i)).shiftObj m).grading.IsGeneratedInDegree
        A d₀ ↔ m = d₀ := by
  have he₀ := he.mem_zero_of_isHomogeneous_span 𝒜 hI
  let Q := (GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i)).shiftObj m
  let _ : SetLike.GradedSMul 𝒜 Q.grading.piece := Q.gradedSMul
  let g : Q := spanSingletonGenerator (e i)
  have hg_ne : g ≠ 0 := fun h => hne i <| by
    simpa [g, coe_spanSingletonGenerator] using congrArg Subtype.val h
  have hg_mem : g ∈ Q.grading.piece m := by
    rw [GradedModuleCat.mem_shiftObj_piece_iff, sub_self, GradedModuleCat.mem_ofIdeal_piece_iff]
    simpa [g, coe_spanSingletonGenerator] using he₀ i
  refine ⟨fun hgen => ?_, fun hm => ?_⟩
  · rcases lt_trichotomy m d₀ with hlt | rfl | hgt
    · exact absurd ((Submodule.eq_bot_iff _).mp
        (hgen.piece_eq_bot_of_lt 𝒜 hneg hlt) g hg_mem) hg_ne
    · rfl
    · have hbot : Q.grading.piece d₀ = ⊥ := (Submodule.eq_bot_iff _).mpr fun z hz => by
        rw [GradedModuleCat.mem_shiftObj_piece_iff, GradedModuleCat.mem_ofIdeal_piece_iff] at hz
        exact Subtype.ext <| (Submodule.eq_bot_iff _).mp (hneg (d₀ - m) (by omega)) _ hz
      have hspan0 : Submodule.span A (Q.grading.piece d₀ : Set Q) = ⊥ := by simp [hbot]
      have hg_top := (Q.grading.isGeneratedInDegree_iff d₀).mp hgen g
      exact absurd ((Submodule.eq_bot_iff _).mp hspan0 g hg_top) hg_ne
  · subst hm
    refine (Q.grading.isGeneratedInDegree_iff m).mpr fun x => ?_
    have hx : x = (x : A) • g := by
      -- Compare underlying elements of `A` inside `Ideal.span {e i}`.
      apply Subtype.ext
      change (x : A) = ((x : A) • g : A)
      simpa [g, coe_spanSingletonGenerator] using
        ((mem_span_singleton_iff_mul_eq_self (he.idem i)).mp x.2).symm
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hg_mem)

include he hI hneg hspan hne in
/-- **A finite graded projective is generated in degree `d₀` if and only if its coordinates in
`[A eᵢ]` are supported in `q^{d₀}`.** This holds in any basis `bP` whose `i`th vector is `[A eᵢ]`
(in particular `gradedSplitProjectiveBasis`, `gradedIdempotentProjectiveBasis`, and quiver
vertex-projective bases), with no finite-dimensionality hypothesis on `A`. -/
theorem isGeneratedInDegree_iff_coeff_repr_eq_zero
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hbP : ∀ i, bP i = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
        gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩)
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) (d₀ : ℤ) :
    P.obj.grading.IsGeneratedInDegree A d₀ ↔
      ∀ (i : I) (p : ℤ), p ≠ d₀ →
        (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P) i).coeff p =
          0 := by
  classical
  obtain ⟨n, idx, d, ⟨iso⟩⟩ := exists_iso_directSum_ofIdeal_span_singleton he hI hneg hspan P
  have hcls : LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P =
      ∑ r : Fin n, (T (d r) : LaurentPolynomial ℤ) • bP (idx r) := by
    rw [laurentK0_projective_of_iso_directSum_ofIdeal he hI iso]
    exact Finset.sum_congr rfl fun r _ => by rw [hbP (idx r)]
  have hcoeff : ∀ (i : I) (p : ℤ),
      (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P) i).coeff p =
        ((Finset.univ.filter fun r : Fin n => idx r = i ∧ d r = p).card : ℤ) := fun i p => by
    have hsum : bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P) i =
        ∑ r : Fin n, if idx r = i then (T (d r) : LaurentPolynomial ℤ) else 0 := by
      rw [hcls, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    rw [hsum, AddMonoidAlgebra.coeff_sum]
    have hboole : ∀ r : Fin n,
        (if idx r = i then (T (d r) : LaurentPolynomial ℤ) else 0).coeff p =
          if idx r = i ∧ d r = p then 1 else 0 := fun r => by
      by_cases hi : idx r = i
      · rw [ite_eq_left hi, T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        by_cases hd : d r = p <;> simp [hi, hd]
      · simp [hi]
    simp [hboole, Finset.sum_boole]
  have hsurj_hom : Function.Surjective iso.hom.hom :=
    ((GradedModuleCat.isIso_iff_bijective iso.hom).mp inferInstance).2
  have hsurj_inv : Function.Surjective iso.inv.hom :=
    ((GradedModuleCat.isIso_iff_bijective iso.inv).mp inferInstance).2
  let Gfam : ∀ r : Fin n, InternalGrading k
      (((GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)})
        (hI (idx r))).shiftObj (d r)).carrier) ℤ :=
    fun r => ((GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e (idx r)}) (hI (idx r))).shiftObj
      (d r)).grading
  have hgen_iff : P.obj.grading.IsGeneratedInDegree A d₀ ↔ ∀ r : Fin n, d r = d₀ := by
    refine ⟨fun h r => ?_, fun hd => ?_⟩
    · have hds := isGeneratedInDegree_of_surjective iso.hom hsurj_hom h
      exact (isGeneratedInDegree_ofIdeal_shiftObj_iff he hI hneg hne (idx r) (d r) d₀).mp
        ((InternalGrading.isGeneratedInDegree_directSum_iff Gfam d₀).mp hds r)
    · refine isGeneratedInDegree_of_surjective iso.inv hsurj_inv
        ((InternalGrading.isGeneratedInDegree_directSum_iff Gfam d₀).mpr fun r => ?_)
      exact (isGeneratedInDegree_ofIdeal_shiftObj_iff he hI hneg hne (idx r) (d r) d₀).mpr (hd r)
  rw [hgen_iff]
  refine ⟨fun hd i p hp => ?_, fun hzero r => ?_⟩
  · rw [hcoeff, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun r _ hr => hp (hr.2.symm.trans (hd r))
  · by_contra hdr
    have h0 := hzero (idx r) (d r) hdr
    rw [hcoeff, Nat.cast_eq_zero, Finset.card_eq_zero] at h0
    exact Finset.notMem_empty r (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl, rfl⟩)

end Basis

end Decomposition

end TauCeti
