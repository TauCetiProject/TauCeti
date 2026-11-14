/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution
public import TauCeti.Algebra.Polynomial.Laurent.Coeff
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The regular projective basis and Betti Poincaré series over connected graded algebras

Let `A` be a nontrivial nonnegatively graded `k`-algebra over a field `k` whose degree-zero piece
is spanned by `1`. No finite-dimensionality of `A` over `k` and no finite-dimensionality of the
positive graded pieces `𝒜 p` are assumed, so polynomial algebras, exterior algebras, and local
finite-dimensional examples such as the dual numbers are covered uniformly.

Every finitely generated graded projective `A`-module `P` is isomorphic to a finite graded free
module `⨁_{j : J} A{d j}`: a `k`-basis of homogeneous generators of `P / A₊ P` lifts to a graded
surjection `⨁_{j : J} A{d j} ↠ P`, which splits by projectivity and has kernel inside the
positive-degree submodule, making the splitting an isomorphism by graded Nakayama.

Meanwhile, the graded residue module `k = A / A₊` is one-dimensional over `k` and concentrated in
degree zero. For any finitely generated graded projective `P`, the graded Hom spaces
`Hom(P, k{d})` have finite Laurent support, and their graded dimension
`∑_d dim_k Hom(P, k{d}) q^d` is additive on split conflations, commutes with the shift `{1}`, and
takes the value `1` on the regular module `A`. Consequently the class `[A]` forms a singleton
`ℤ[q,q⁻¹]`-basis `TauCeti.connectedRegularProjectiveBasis` of `K₀^gr(proj A)` whose unique
coordinate reads off the graded free summand multiplicities `∑_j q^{d j}` without requiring `A` to
be finite-dimensional over `k`.

In this basis, a graded projective resolution with finitely generated terms is linear if and only
if its Betti Poincaré series is supported on the diagonal `d = n`: each term `P_n` is isomorphic
to a finite graded free module whose summands contribute positive Laurent monomials `q^{d j}`, so
off-diagonal vanishing allows no sign cancellation even before assuming minimality.

## Main definitions

* `TauCeti.gradedRegularProjective`: the regular graded module `A` in
  `gradedFiniteProjectiveModules 𝒜`.
* `TauCeti.gradedConnectedResidue`: the graded residue module `A / A₊`.
* `TauCeti.connectedRegularProjectiveBasis`: the `Unit`-indexed `ℤ[q,q⁻¹]`-basis `[A]` of
  `K₀^gr(proj A)` for a connected nonnegatively graded algebra.

## Main results

* `TauCeti.laurentK0_projective_of_directSumObj`: the class in `K₀^gr(proj A)` of a finite
  degreewise direct sum of finite graded projectives is the sum of their classes.
* `TauCeti.GradedModuleCat.exists_free_iso_of_projective`: every finitely generated graded
  projective over a connected nonnegatively graded algebra over a field is graded free of finite
  rank.
* `TauCeti.coeff_connectedRegularProjectiveBasis_repr_of`: the `q^d`-coefficient of `[P]` in the
  regular basis is `dim_k Hom(P, (A / A₊){d})`.
* `TauCeti.connectedRegularProjectiveBasis_repr_of_free`: the coordinate of `[⨁_j A{d j}]` is
  `∑_j q^{d j}`.
* `TauCeti.GradedProjectiveResolution.isLinear_iff_diagonal_bettiPoincarePowerSeries_connected`:
  a resolution with finitely generated terms is linear iff its Betti Poincaré series in the
  regular basis vanishes off `d = n`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded free and
  projective modules over connected graded rings.
* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for graded Betti numbers over positively graded algebras.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial
open scoped _root_.DirectSum

universe uk uA uJ

/-! ### Finite direct sums in `K₀^gr(proj A)` and the regular projective -/

section CommRing

variable {k : Type uk} [CommRing k]

section DirectSumClass

variable {A : Type (max uJ uA)} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

/-- A finite degreewise direct sum of finite graded projectives is a finite graded projective. -/
theorem gradedFiniteProjectiveModules_directSumObj {J : Type uJ} [Finite J]
    (M : J → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedFiniteProjectiveModules 𝒜 (GradedModuleCat.directSumObj fun j ↦ (M j).obj) := by
  cases nonempty_fintype J
  exact gradedFiniteProjectiveModules_iff.2
    ⟨inferInstanceAs (Module.Finite A (⨁ j : J, (M j).obj)),
      inferInstanceAs (Module.Projective A (⨁ j : J, (M j).obj))⟩

/-- **The class in `K₀^gr(proj A)` of a finite degreewise direct sum of finite graded projectives
is the sum of the classes of its summands.** -/
theorem laurentK0_projective_of_directSumObj {J : Type uJ} [Fintype J]
    (M : J → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    LaurentK0.of.{max uJ uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ⟨GradedModuleCat.directSumObj fun j ↦ (M j).obj,
          gradedFiniteProjectiveModules_directSumObj M⟩ =
      ∑ j : J, LaurentK0.of.{max uJ uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (M j) := by
  let _ : HasFiniteProducts (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
    hasFiniteProducts_of_has_binary_and_terminal
  let _ : HasFiniteBiproducts (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let g : Fin (Fintype.card J) → (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
    fun i ↦ M (e.symm i)
  let _ := HasBiproduct.of_hasCoproduct fun j : J ↦ (M j).obj
  let _ := HasBiproduct.of_hasCoproduct fun i : Fin (Fintype.card J) ↦ (M (e.symm i)).obj
  have hcolim := GradedModuleCat.coproductCofanIsColimit fun j : J ↦ (M j).obj
  let isoAmbient : GradedModuleCat.directSumObj (fun j : J ↦ (M j).obj) ≅
      (gradedFiniteProjectiveModules 𝒜).ι.obj (⨁ g) :=
    hcolim.coconePointUniqueUpToIso (biproduct.isColimit fun j : J ↦ (M j).obj) ≪≫
      (biproduct.whiskerEquiv e.symm fun _ ↦ Iso.refl _).symm ≪≫
      ((gradedFiniteProjectiveModules 𝒜).ι.mapBiproduct g).symm
  let isoSub :
      (⟨GradedModuleCat.directSumObj fun j : J ↦ (M j).obj,
          gradedFiniteProjectiveModules_directSumObj M⟩ :
        (gradedFiniteProjectiveModules 𝒜).FullSubcategory) ≅ ⨁ g :=
    (gradedFiniteProjectiveModules 𝒜).isoMk isoAmbient
  rw [LaurentK0.of_congr.{max uJ uA} _ isoSub, ← LaurentK0.ofExactK0_exactK0_of.{max uJ uA},
    ← ExactK0.fromSplit_of, SplitK0.of_biproduct, map_sum, map_sum]
  simp only [ExactK0.fromSplit_of, LaurentK0.ofExactK0_exactK0_of]
  exact e.symm.sum_comp fun j ↦
    LaurentK0.of.{max uJ uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (M j)

end DirectSumClass

section Regular

variable {A : Type uA} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- **The regular graded module `A`** bundled as an object of `gradedFiniteProjectiveModules 𝒜`. -/
abbrev gradedRegularProjective : (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
  ⟨GradedModuleCat.regular (𝒜 := 𝒜),
    gradedFiniteProjectiveModules_iff.2
      ⟨inferInstanceAs (Module.Finite A A), inferInstanceAs (Module.Projective A A)⟩⟩

@[simp]
theorem gradedRegularProjective_obj :
    (gradedRegularProjective 𝒜).obj = GradedModuleCat.regular (𝒜 := 𝒜) :=
  (rfl)

/-- A finite graded free module `⨁_{j : J} A{d j}` is a finite graded projective. -/
theorem gradedFiniteProjectiveModules_free {J : Type uA} [Finite J] (d : J → ℤ) :
    gradedFiniteProjectiveModules 𝒜 (GradedModuleCat.free 𝒜 d) :=
  gradedFiniteProjectiveModules_directSumObj fun j ↦
    ⟨(gradedRegularProjective 𝒜).obj.shiftObj (d j),
      gradedFiniteProjectiveModules_shiftObj (gradedRegularProjective 𝒜).property (d j)⟩

/-- The class of a finite graded free module `⨁_{j : J} A{d j}` in `K₀^gr(proj A)` is
`(∑_j q^{d j}) [A]`. -/
theorem laurentK0_projective_of_free {J : Type uA} [Fintype J] (d : J → ℤ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ⟨GradedModuleCat.free 𝒜 d, gradedFiniteProjectiveModules_free 𝒜 d⟩ =
      (∑ j : J, (T (d j) : LaurentPolynomial ℤ)) •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (gradedRegularProjective 𝒜) := by
  have h := laurentK0_projective_of_directSumObj fun j : J ↦
    (⟨(gradedRegularProjective 𝒜).obj.shiftObj (d j),
      gradedFiniteProjectiveModules_shiftObj (gradedRegularProjective 𝒜).property (d j)⟩ :
      (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
  rw [h, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact laurentK0_projective_of_shiftObj (gradedRegularProjective 𝒜) (d j)

/-- **The graded residue module `A / A₊`** of a graded algebra: the quotient of `A = A · 1` by the
left ideal generated by homogeneous elements of positive degree. -/
abbrev gradedConnectedResidue : GradedModuleCat.{uA} 𝒜 :=
  gradedPositiveMulQuotient 𝒜 (SetLike.one_mem_graded 𝒜)

end Regular

end CommRing

/-! ### Graded freeness of projectives over connected algebras -/

section Field

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Every element of a connected nonnegatively graded algebra is a `k`-multiple of `1` plus an
element of the positive-degree submodule `A₊`. -/
private theorem exists_eq_smul_one_add_mem_positive (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hspan : 𝒜 0 ≤ Submodule.span k {(1 : A)}) (r : A) :
    ∃ c : k, ∃ r' ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i, r = c • (1 : A) + r' := by
  classical
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hspan (DirectSum.decompose 𝒜 r 0).2)
  refine ⟨c, r - c • (1 : A), ?_, (add_sub_cancel _ _).symm⟩
  have hsum : r - c • (1 : A) =
      ∑ p ∈ (DirectSum.decompose 𝒜 r).support.erase 0, (DirectSum.decompose 𝒜 r p : A) := by
    by_cases h0 : (0 : ℤ) ∈ (DirectSum.decompose 𝒜 r).support
    · have hdecomp := (DirectSum.sum_support_decompose 𝒜 r).symm
      rw [← Finset.add_sum_erase _ _ h0, ← hc] at hdecomp
      exact sub_eq_of_eq_add' hdecomp
    · have hz : (DirectSum.decompose 𝒜 r 0 : A) = 0 := by
        simpa using DFinsupp.notMem_support_iff.1 h0
      rw [hc, hz, sub_zero, Finset.erase_eq_of_notMem h0]
      exact (DirectSum.sum_support_decompose 𝒜 r).symm
  rw [hsum]
  refine Submodule.sum_mem _ fun p hp ↦ ?_
  have hp0 : p ≠ 0 := (Finset.mem_erase.1 hp).1
  rcases lt_or_gt_of_ne hp0 with hlt | hgt
  · have hmem : (DirectSum.decompose 𝒜 r p : A) ∈ (⊥ : Submodule k A) :=
      hneg p hlt ▸ (DirectSum.decompose 𝒜 r p).2
    rw [(Submodule.mem_bot k).1 hmem]
    exact zero_mem _
  · exact Submodule.mem_iSup_of_mem p
      (Submodule.mem_iSup_of_mem hgt (DirectSum.decompose 𝒜 r p).2)

namespace GradedModuleCat

/-- **Every finitely generated graded projective module over a connected nonnegatively graded
algebra over a field is isomorphic to a finite graded free module.** No finite-dimensionality of
`A` or of its homogeneous pieces over `k` is needed. -/
theorem exists_free_iso_of_projective (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hspan : 𝒜 0 ≤ Submodule.span k {(1 : A)})
    (P : GradedModuleCat.{uA} 𝒜) [Module.Finite A P] [Module.Projective A P] :
    ∃ (J : Type uA) (_ : Fintype J) (d : J → ℤ), Nonempty (free 𝒜 d ≅ P) := by
  classical
  obtain ⟨I, hI, d₀, f₀, hf₀⟩ := exists_finite_free_surjection P
  let x₀ : ∀ i : I, P.grading.piece (d₀ i) := freeHomEquiv P f₀
  have hx₀_eq : freeLift x₀ = f₀ :=
    (freeHomEquiv_symm_apply P x₀).symm.trans ((freeHomEquiv P).symm_apply_apply f₀)
  have hspanA : Submodule.span A (Set.range fun i : I ↦ (x₀ i : P)) = ⊤ :=
    (freeLift_surjective_iff x₀).1 (hx₀_eq.symm ▸ hf₀)
  let N : Submodule k P := (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)
  -- Modulo `A₊ P`, `A`-span collapses to `k`-span because `𝒜 0 ≤ k · 1` and `𝒜_{<0} = 0`.
  have hspan_quot : Submodule.span k (Set.range fun i : I ↦ N.mkQ (x₀ i : P)) = ⊤ := by
    refine top_unique fun y _ ↦ ?_
    clear ‹y ∈ ⊤›
    obtain ⟨z, rfl⟩ := N.mkQ_surjective y
    have hz : z ∈ Submodule.span A (Set.range fun i : I ↦ (x₀ i : P)) :=
      hspanA.symm ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact Submodule.subset_span (Set.mem_range_self i)
    | zero => simp
    | add u v _ _ hu hv => simpa only [map_add] using add_mem hu hv
    | smul r u _ hu =>
      obtain ⟨c, r', hr', rfl⟩ := exists_eq_smul_one_add_mem_positive hneg hspan r
      have hr'N : r' • u ∈ N := Submodule.smul_mem_smul hr' Submodule.mem_top
      have hmk0 : N.mkQ (r' • u) = 0 := (Submodule.Quotient.mk_eq_zero N).2 hr'N
      rw [add_smul, smul_assoc, one_smul, map_add, map_smul, hmk0, add_zero]
      exact Submodule.smul_mem _ c hu
  -- Extract a `k`-basis of `P / A₊ P` from the homogeneous generators `x₀`.
  obtain ⟨J, a, ha, hspanJ, hliJ⟩ :=
    exists_linearIndependent' (K := k) fun i : I ↦ N.mkQ (x₀ i : P)
  let _ : Finite J := Finite.of_injective a ha
  let _ : Fintype J := Fintype.ofFinite J
  let d : J → ℤ := fun j ↦ d₀ (a j)
  let x : ∀ j : J, P.grading.piece (d j) := fun j ↦ x₀ (a j)
  let π : free 𝒜 d ⟶ P := freeLift x
  have hspanJ_top : Submodule.span k (Set.range fun j : J ↦ N.mkQ (x j : P)) = ⊤ :=
    hspanJ.trans hspan_quot
  -- `π` is surjective by graded Nakayama: its image is homogeneous and covers `P` modulo `A₊ P`.
  obtain ⟨bP, hbP⟩ := P.grading.exists_piece_eq_bot_of_lt 𝒜 hneg
  have hrange_top : LinearMap.range π.hom = ⊤ := by
    refine P.grading.eq_top_of_piece_le_sup_positive_smul_top 𝒜
      (LinearMap.range π.hom) π.isHomogeneous.isHomogeneous_range bP hbP fun p z _ ↦ ?_
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1
      (hspanJ_top.symm ▸ Submodule.mem_top : N.mkQ z ∈ _)
    let u : free 𝒜 d := ∑ j : J, c j • freeGenerator (𝒜 := 𝒜) (d := d) j
    have hπu : π.hom u = ∑ j : J, c j • (x j : P) := by
      simp only [u, π, map_sum, LinearMap.map_smul_of_tower, freeLift_generator]
    have hzu : z - π.hom u ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero N]
      change N.mkQ (z - π.hom u) = 0
      rw [map_sub, hπu, map_sum]
      simp only [map_smul]
      exact sub_eq_zero.2 hc.symm
    rw [show z = π.hom u + (z - π.hom u) from (add_sub_cancel _ _).symm]
    exact Submodule.add_mem_sup ⟨u, rfl⟩ hzu
  have : Epi π := (epi_iff_surjective π).2 (LinearMap.range_eq_top.1 hrange_top)
  have : Projective P := projective_of_module_projective P
  let σ : P ⟶ free 𝒜 d := Projective.factorThru (𝟙 P) π
  have hσπ : σ ≫ π = 𝟙 P := Projective.factorThru_comp (𝟙 P) π
  -- Any element of `ker π` has coordinates in `A₊`, because `x` is `k`-linearly independent
  -- modulo `A₊ P`.
  have hker : ∀ y : free 𝒜 d, π.hom y = 0 →
      y ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 d)) := by
    intro y hy0
    have hy_sum : y = ∑ j : J, y j • freeGenerator (𝒜 := 𝒜) (d := d) j := by
      ext j'
      simp only [DirectSum.sum_apply, DirectSum.smul_apply, freeGenerator_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    choose c r' hr' hyc using fun j : J ↦
      exists_eq_smul_one_add_mem_positive hneg hspan (y j)
    have hrel : ∑ j : J, c j • N.mkQ (x j : P) = 0 := by
      have hπy : π.hom y =
          ∑ j : J, c j • (x j : P) + ∑ j : J, r' j • (x j : P) := by
        conv_lhs => rw [hy_sum]
        rw [map_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hyc j, add_smul, smul_assoc, one_smul, map_add, LinearMap.map_smul_of_tower,
          map_smul, freeLift_generator]
      have hmk := congrArg N.mkQ (hy0.symm.trans hπy)
      rw [map_zero, map_add, map_sum, map_sum] at hmk
      have hr'0 : ∑ j : J, N.mkQ (r' j • (x j : P)) = 0 :=
        Finset.sum_eq_zero fun j _ ↦
          (Submodule.Quotient.mk_eq_zero N).2 (Submodule.smul_mem_smul (hr' j) Submodule.mem_top)
      rw [hr'0, add_zero] at hmk
      simpa only [map_smul] using hmk.symm
    have hc0 : ∀ j : J, c j = 0 := Fintype.linearIndependent_iff.1 hliJ c hrel
    rw [hy_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [hyc j, hc0 j, zero_smul, zero_add]
    exact Submodule.smul_mem_smul (hr' j) Submodule.mem_top
  -- Hence `1 - π ≫ σ` takes values in `A₊ (free 𝒜 d)`, so `π ≫ σ` is an isomorphism.
  let _ : SetLike.GradedSMul 𝒜 (free 𝒜 d).grading.piece := (free 𝒜 d).gradedSMul
  obtain ⟨bF, hbF⟩ := (free 𝒜 d).grading.exists_piece_eq_bot_of_lt 𝒜 hneg
  have : IsIso (π ≫ σ) := isIso_of_sub_mem_positive_smul_top bF hbF (π ≫ σ) fun y ↦ hker _ <| by
    have hcomp : (π ≫ σ) ≫ π = π := by rw [Category.assoc, hσπ, Category.comp_id]
    have happ := LinearMap.congr_fun (congrArg Hom.hom hcomp) y
    simp only [hom_comp, LinearMap.comp_apply] at happ
    rw [map_sub, hom_comp, LinearMap.comp_apply, happ, sub_self]
  have hret : π ≫ (σ ≫ inv (π ≫ σ)) = 𝟙 _ := by rw [← Category.assoc, IsIso.hom_inv_id]
  have : Mono π := ⟨fun g₁ g₂ hg ↦ by
    simpa only [Category.assoc, hret, Category.comp_id] using hg =≫ (σ ≫ inv (π ≫ σ))⟩
  have : IsIso π := isIso_of_mono_of_epi π
  exact ⟨J, inferInstance, d, ⟨asIso π⟩⟩

end GradedModuleCat

/-! ### The graded residue module and the regular projective basis -/

section ConnectedBasis

/-- In a nonnegatively graded algebra, the graded residue module `A / A₊` vanishes outside
degree zero. -/
theorem gradedConnectedResidue_piece_eq_bot (hneg : ∀ p < 0, 𝒜 p = ⊥) {p : ℤ} (hp : p ≠ 0) :
    (gradedConnectedResidue 𝒜).grading.piece p = ⊥ :=
  gradedPositiveMulQuotient_piece_eq_bot hneg IsIdempotentElem.one (SetLike.one_mem_graded 𝒜) hp

/-- In a nonnegatively graded algebra, the graded residue module `A / A₊` is concentrated in
degree zero. -/
theorem gradedConnectedResidue_piece_zero_eq_top (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    (gradedConnectedResidue 𝒜).grading.piece 0 = ⊤ :=
  gradedPositiveMulQuotient_piece_zero_eq_top hneg IsIdempotentElem.one
    (SetLike.one_mem_graded 𝒜)

section Nontrivial

variable [Nontrivial A] (hneg : ∀ p < 0, 𝒜 p = ⊥) (hspan : 𝒜 0 ≤ Submodule.span k {(1 : A)})
include hneg hspan

/-- Over a nontrivial connected nonnegatively graded algebra, the graded residue module `A / A₊`
is one-dimensional over `k`. -/
theorem finrank_gradedConnectedResidue :
    Module.finrank k (gradedConnectedResidue 𝒜) = 1 :=
  finrank_gradedIdempotentHead (I := Unit) (e := fun _ ↦ (1 : A)) hneg
    (CompleteOrthogonalIdempotents.unique_iff.2 rfl).toOrthogonalIdempotents
    (fun _ ↦ SetLike.one_mem_graded 𝒜) (by rwa [Set.range_const]) () one_ne_zero

/-- The graded residue module `A / A₊` of a nontrivial connected nonnegatively graded algebra is
finite-dimensional over `k`, without any finite-dimensionality hypothesis on `A`. -/
theorem moduleFinite_gradedConnectedResidue :
    Module.Finite k (gradedConnectedResidue 𝒜) :=
  Module.finite_of_finrank_pos <| by
    rw [finrank_gradedConnectedResidue hneg hspan]
    exact zero_lt_one

/-- The graded residue module `A / A₊` of a nontrivial connected nonnegatively graded algebra is
a simple graded module. -/
theorem simple_gradedConnectedResidue : Simple (gradedConnectedResidue 𝒜) :=
  simple_gradedIdempotentHead (I := Unit) (e := fun _ ↦ (1 : A)) hneg
    (CompleteOrthogonalIdempotents.unique_iff.2 rfl).toOrthogonalIdempotents
    (fun _ ↦ SetLike.one_mem_graded 𝒜) (by rwa [Set.range_const]) () one_ne_zero

/-- The piece dimensions of `A / A₊`: `1` in degree zero and `0` elsewhere. -/
theorem finrank_gradedConnectedResidue_piece (p : ℤ) :
    Module.finrank k ((gradedConnectedResidue 𝒜).grading.piece p) = if p = 0 then 1 else 0 := by
  by_cases hp : p = 0
  · subst hp
    rw [gradedConnectedResidue_piece_zero_eq_top hneg, finrank_top,
      finrank_gradedConnectedResidue hneg hspan]
    simp
  · rw [gradedConnectedResidue_piece_eq_bot hneg hp, finrank_bot]
    simp [hp]

private theorem hasFiniteLaurentSupport_hom_gradedConnectedResidue
    (P : GradedModuleCat.{uA} 𝒜) [Module.Finite A P] :
    HasFiniteLaurentSupport k fun d : ℤ ↦ P ⟶ (gradedConnectedResidue 𝒜).shiftObj d := by
  let _ := moduleFinite_gradedConnectedResidue hneg hspan
  exact GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj P (gradedConnectedResidue 𝒜)

private def homShiftOneEquiv (M N : GradedModuleCat.{uA} 𝒜) (d : ℤ) :
    (M.shiftObj 1 ⟶ N.shiftObj d) ≃ₗ[k] (M ⟶ N.shiftObj (d - 1)) where
  toFun f := GradedModuleCat.ofHom f.hom <|
    LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      have hx' : x ∈ (M.shiftObj 1).grading.piece (p + 1) := by
        rw [GradedModuleCat.mem_shiftObj_piece_iff, add_sub_cancel_right]
        exact hx
      have hf := GradedModuleCat.map_mem f hx'
      rw [GradedModuleCat.mem_shiftObj_piece_iff] at hf ⊢
      have hdeg : p + 0 - (d - 1) = p + 1 - d := by omega
      rwa [hdeg]
  invFun g := GradedModuleCat.ofHom g.hom <|
    LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      rw [GradedModuleCat.mem_shiftObj_piece_iff] at hx
      have hg := GradedModuleCat.map_mem g hx
      rw [GradedModuleCat.mem_shiftObj_piece_iff] at hg ⊢
      have hdeg : p + 0 - d = p - 1 - (d - 1) := by omega
      rwa [hdeg]
  left_inv _ := GradedModuleCat.hom_ext rfl
  right_inv _ := GradedModuleCat.hom_ext rfl
  map_add' _ _ := GradedModuleCat.hom_ext rfl
  map_smul' _ _ := GradedModuleCat.hom_ext rfl

private def homBiprodEquiv (X Y W : GradedModuleCat.{uA} 𝒜) :
    (X ⊞ Y ⟶ W) ≃ₗ[k] (X ⟶ W) × (Y ⟶ W) where
  toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
  invFun fg := biprod.desc fg.1 fg.2
  left_inv f := biprod.hom_ext' _ _ (by simp) (by simp)
  right_inv fg := Prod.ext (by simp) (by simp)
  map_add' _ _ := Prod.ext (by simp) (by simp)
  map_smul' _ _ := Prod.ext (by simp) (by simp)

private def connectedHomDimensionInvariant :
    GradedExactStructure.ShiftInvariant (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (laurentTAut ℤ (LaurentPolynomial ℤ)) where
  obj P := gradedDimension k (fun d : ℤ ↦ P.obj ⟶ (gradedConnectedResidue 𝒜).shiftObj d)
    (hasFiniteLaurentSupport_hom_gradedConnectedResidue hneg hspan P.obj)
  map_conflation S hS := by
    rw [gradedFiniteProjectiveModulesExactStructure_eq_split, ExactStructure.split_conflation]
      at hS
    obtain ⟨σ⟩ := hS
    let F := (gradedFiniteProjectiveModules 𝒜).ι
    let _ : PreservesBinaryBiproduct S.X₁ S.X₃ F :=
      preservesBinaryBiproduct_of_preservesBinaryCoproduct F
    let e : S.X₂.obj ≅ S.X₁.obj ⊞ S.X₃.obj :=
      F.mapIso σ.isoBinaryBiproduct ≪≫ F.mapBiprod S.X₁ S.X₃
    ext d
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_gradedDimension]
    let _ :=
      (hasFiniteLaurentSupport_hom_gradedConnectedResidue hneg hspan S.X₁.obj).finiteDimensional d
    let _ :=
      (hasFiniteLaurentSupport_hom_gradedConnectedResidue hneg hspan S.X₃.obj).finiteDimensional d
    have hfin := ((Linear.homCongr k e (Iso.refl _)).trans
      (homBiprodEquiv S.X₁.obj S.X₃.obj ((gradedConnectedResidue 𝒜).shiftObj d))).finrank_eq.trans
      Module.finrank_prod
    exact_mod_cast hfin
  map_shift P := by
    let e := (gradedFiniteProjectiveModulesExactStructureShiftFunctorCompιIso (𝒜 := 𝒜)).app P
    ext d
    rw [laurentTAut_apply, smul_eq_mul, coeff_T_mul, coeff_gradedDimension, coeff_gradedDimension]
    have hfin := ((Linear.homCongr k e (Iso.refl _)).trans
      (homShiftOneEquiv P.obj (gradedConnectedResidue 𝒜) d)).finrank_eq
    exact_mod_cast hfin

private def connectedProjectiveCoord :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentPolynomial ℤ :=
  LaurentK0.lift _ (connectedHomDimensionInvariant hneg hspan)

private theorem connectedProjectiveCoord_regular :
    connectedProjectiveCoord hneg hspan
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (gradedRegularProjective 𝒜)) = 1 := by
  rw [connectedProjectiveCoord, LaurentK0.lift_of]
  ext d
  change (gradedDimension k _ _).coeff d = (1 : LaurentPolynomial ℤ).coeff d
  rw [coeff_gradedDimension, coeff_one]
  let e₀ := (GradedModuleCat.shiftFunctorZeroIso 𝒜).app (GradedModuleCat.regular (𝒜 := 𝒜))
  let eHom : (GradedModuleCat.regular (𝒜 := 𝒜) ⟶ (gradedConnectedResidue 𝒜).shiftObj d) ≃ₗ[k]
      (gradedConnectedResidue 𝒜).grading.piece (-d) :=
    (Linear.homCongr k e₀.symm (Iso.refl _)).trans
      ((GradedModuleCat.regularShiftHomEquiv ((gradedConnectedResidue 𝒜).shiftObj d) 0).trans
        (LinearEquiv.ofEq _ _ (by ext; simp)))
  rw [eHom.finrank_eq, finrank_gradedConnectedResidue_piece hneg hspan (-d)]
  simp [neg_eq_zero]

/-- **The regular projective basis of `K₀^gr(proj A)`** over `ℤ[q,q⁻¹]` for a nontrivial
connected nonnegatively graded algebra `A` over a field `k`: the `Unit`-indexed basis whose sole
vector is the class `[A]` of the regular module. No finite-dimensionality of `A` over `k` is
assumed. -/
def connectedRegularProjectiveBasis :
    Module.Basis Unit (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) := by
  let v : Unit → LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) :=
    fun _ ↦ LaurentK0.of.{uA} _ (gradedRegularProjective 𝒜)
  have hli : LinearIndependent (LaurentPolynomial ℤ) v := by
    refine Fintype.linearIndependent_iff.2 fun g hg u ↦ ?_
    cases u
    rw [Finset.univ_unique, Finset.sum_singleton] at hg
    have happ := congrArg (connectedProjectiveCoord hneg hspan) hg
    simpa [v, connectedProjectiveCoord_regular hneg hspan] using happ
  have htop : Submodule.span (LaurentPolynomial ℤ) (Set.range v) = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    clear ‹x ∈ ⊤›
    obtain ⟨x, rfl⟩ :=
      (LaurentK0.ofExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)).surjective x
    induction x using ExactK0.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | of P =>
      obtain ⟨J, _, d, ⟨e⟩⟩ := GradedModuleCat.exists_free_iso_of_projective hneg hspan P.obj
      let eSub : (⟨GradedModuleCat.free 𝒜 d, gradedFiniteProjectiveModules_free 𝒜 d⟩ :
          (gradedFiniteProjectiveModules 𝒜).FullSubcategory) ≅ P :=
        (gradedFiniteProjectiveModules 𝒜).isoMk e
      rw [LaurentK0.ofExactK0_exactK0_of, ← LaurentK0.of_congr.{uA} _ eSub,
        laurentK0_projective_of_free]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self ()))
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | neg x hx => rw [map_neg]; exact neg_mem hx
  exact Module.Basis.mk hli htop.ge

/-- The sole vector of `TauCeti.connectedRegularProjectiveBasis` is the class `[A]` of the
regular graded module. -/
@[simp]
theorem connectedRegularProjectiveBasis_apply (u : Unit) :
    connectedRegularProjectiveBasis hneg hspan u =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (gradedRegularProjective 𝒜) := by
  rw [connectedRegularProjectiveBasis, Module.Basis.mk_apply]

/-- The unique coordinate in `TauCeti.connectedRegularProjectiveBasis` is the Hom-dimension
functional into shifts of `A / A₊`. -/
private theorem connectedRegularProjectiveBasis_repr_eq_coord
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) (u : Unit) :
    (connectedRegularProjectiveBasis hneg hspan).repr x u =
      connectedProjectiveCoord hneg hspan x := by
  cases u
  conv_rhs => rw [← (connectedRegularProjectiveBasis hneg hspan).sum_repr x]
  rw [Finset.univ_unique, Finset.sum_singleton,
    LinearMap.map_smul (connectedProjectiveCoord hneg hspan),
    connectedRegularProjectiveBasis_apply, connectedProjectiveCoord_regular hneg hspan,
    smul_eq_mul, mul_one]

/-- **The `q^d`-coefficient of `[P]` in the regular basis is `dim_k Hom(P, (A / A₊){d})`.** -/
@[simp]
theorem coeff_connectedRegularProjectiveBasis_repr_of
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) (u : Unit) (d : ℤ) :
    ((connectedRegularProjectiveBasis hneg hspan).repr
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P) u).coeff d =
      Module.finrank k (P.obj ⟶ (gradedConnectedResidue 𝒜).shiftObj d) := by
  rw [connectedRegularProjectiveBasis_repr_eq_coord, connectedProjectiveCoord, LaurentK0.lift_of]
  exact coeff_gradedDimension _ d

/-- The coordinate of a shifted regular module `A{d}` in the regular basis is `q^d`. -/
@[simp]
theorem connectedRegularProjectiveBasis_repr_of_shiftObj (d : ℤ) (u : Unit) :
    (connectedRegularProjectiveBasis hneg hspan).repr
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ⟨(GradedModuleCat.regular (𝒜 := 𝒜)).shiftObj d,
            gradedFiniteProjectiveModules_shiftObj
              (gradedRegularProjective 𝒜).property d⟩) u = T d := by
  cases u
  rw [laurentK0_projective_of_shiftObj (gradedRegularProjective 𝒜) d,
    LinearEquiv.map_smul, Finsupp.smul_apply,
    ← connectedRegularProjectiveBasis_apply hneg hspan (), Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-- The coordinate of a finite graded free module `⨁_{j : J} A{d j}` in the regular basis is
`∑_j q^{d j}`. -/
@[simp]
theorem connectedRegularProjectiveBasis_repr_of_free {J : Type uA} [Fintype J] (d : J → ℤ)
    (u : Unit) :
    (connectedRegularProjectiveBasis hneg hspan).repr
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ⟨GradedModuleCat.free 𝒜 d, gradedFiniteProjectiveModules_free 𝒜 d⟩) u =
      ∑ j : J, T (d j) := by
  cases u
  rw [laurentK0_projective_of_free, LinearEquiv.map_smul, Finsupp.smul_apply,
    ← connectedRegularProjectiveBasis_apply hneg hspan (), Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)

/-- In the regular basis of a connected nonnegatively graded algebra, the `(n, d)` Betti
coefficient of `r` is `dim_k Hom(P_n, (A / A₊){d})`. -/
theorem coeff_coeff_bettiPoincarePowerSeries_connected [∀ n, Module.Finite A (r.X n)]
    (u : Unit) (n : ℕ) (d : ℤ) :
    (PowerSeries.coeff n
        (r.bettiPoincarePowerSeries (connectedRegularProjectiveBasis hneg hspan) u)).coeff d =
      Module.finrank k (r.termObj n ⟶ (gradedConnectedResidue 𝒜).shiftObj d) := by
  rw [coeff_coeff_bettiPoincarePowerSeries, coeff_connectedRegularProjectiveBasis_repr_of,
    r.finiteProjectiveTerm_obj]

/-- **Linearity criterion over a connected nonnegatively graded algebra.** A graded projective
resolution with finitely generated terms is linear if and only if its Betti Poincaré series in the
regular basis vanishes off the diagonal `d = n`. Neither minimality of `r` nor
finite-dimensionality of `A` over `k` is required: each projective term splits as a finite graded
free module whose summands contribute positive Laurent monomials. -/
theorem isLinear_iff_diagonal_bettiPoincarePowerSeries_connected [∀ n, Module.Finite A (r.X n)] :
    r.IsLinear ↔
      ∀ (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n
          (r.bettiPoincarePowerSeries
            (connectedRegularProjectiveBasis hneg hspan) ())).coeff d = 0 := by
  rw [isLinear_iff]
  refine forall_congr' fun n ↦ ⟨fun hgen d hnd ↦ ?_, fun hdiag ↦ ?_⟩
  · rw [coeff_coeff_bettiPoincarePowerSeries_connected]
    have hpiece : ((gradedConnectedResidue 𝒜).shiftObj d).grading.piece n = ⊥ := by
      simpa [sub_eq_add_neg] using
        gradedConnectedResidue_piece_eq_bot hneg (p := (n : ℤ) - d) (sub_ne_zero.2 hnd)
    let _ : Subsingleton (r.termObj n ⟶ (gradedConnectedResidue 𝒜).shiftObj d) :=
      subsingleton_of_forall_eq 0 fun f ↦ GradedModuleCat.hom_ext <| by
        rw [GradedModuleCat.hom_zero]
        exact (r.grading n).linearMap_eq_zero_of_isGeneratedInDegree hgen f.isHomogeneous hpiece
    exact_mod_cast Module.finrank_zero_of_subsingleton (R := k)
      (M := r.termObj n ⟶ (gradedConnectedResidue 𝒜).shiftObj d)
  · classical
    let _ : Module.Projective A (r.termObj n) := r.projective n
    obtain ⟨J, _, d, ⟨e⟩⟩ :=
      GradedModuleCat.exists_free_iso_of_projective hneg hspan (r.termObj n)
    let eSub : (⟨GradedModuleCat.free 𝒜 d, gradedFiniteProjectiveModules_free 𝒜 d⟩ :
        (gradedFiniteProjectiveModules 𝒜).FullSubcategory) ≅ r.finiteProjectiveTerm n :=
      (gradedFiniteProjectiveModules 𝒜).isoMk
        (e ≪≫ eqToIso (r.finiteProjectiveTerm_obj n).symm)
    have hdeg : ∀ j : J, d j = (n : ℤ) := by
      intro j
      by_contra hne
      have hz := hdiag (d j) (Ne.symm hne)
      rw [coeff_coeff_bettiPoincarePowerSeries, ← LaurentK0.of_congr.{uA} _ eSub,
        connectedRegularProjectiveBasis_repr_of_free, AddMonoidAlgebra.coeff_sum,
        Finsupp.finsetSum_apply] at hz
      have hnonneg : ∀ j' ∈ Finset.univ,
          0 ≤ (T (R := ℤ) (d j')).coeff (d j) := fun j' _ ↦ by
        simp only [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        split_ifs <;> omega
      have hj0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hz j (Finset.mem_univ j)
      rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hj0
      exact one_ne_zero hj0
    -- Every basis vector of `free 𝒜 d` has degree `n`, so `free 𝒜 d` and `r.termObj n` are
    -- generated in degree `n`.
    have hspan_free : Submodule.span A
        ((GradedModuleCat.free 𝒜 d).grading.piece n : Set (GradedModuleCat.free 𝒜 d)) = ⊤ := by
      refine top_unique fun y _ ↦ ?_
      have hy_sum : y = ∑ j : J, y j • GradedModuleCat.freeGenerator (𝒜 := 𝒜) (d := d) j := by
        ext j'
        simp only [DirectSum.sum_apply, DirectSum.smul_apply, GradedModuleCat.freeGenerator_apply,
          smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [hy_sum]
      refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact SetLike.mem_coe.2 (hdeg j ▸
        GradedModuleCat.freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := d) j)
    refine ((r.grading n).isGeneratedInDegree_iff n).2 fun z ↦ ?_
    obtain ⟨y, rfl⟩ : ∃ y, e.hom.hom y = z := ⟨e.inv.hom z, by
      have h := LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom e.inv_hom_id) z
      rwa [GradedModuleCat.hom_comp, LinearMap.comp_apply, GradedModuleCat.hom_id,
        LinearMap.id_apply] at h⟩
    have hy : y ∈ Submodule.span A
        ((GradedModuleCat.free 𝒜 d).grading.piece n : Set (GradedModuleCat.free 𝒜 d)) :=
      hspan_free.symm ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem w hw =>
      refine Submodule.subset_span (SetLike.mem_coe.2 ?_)
      rw [← add_zero (n : ℤ)]
      exact GradedModuleCat.map_mem e.hom (SetLike.mem_coe.1 hw)
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | smul a u _ hu => rw [map_smul]; exact Submodule.smul_mem _ a hu

end GradedProjectiveResolution

end Nontrivial

end ConnectedBasis

end Field

end TauCeti
