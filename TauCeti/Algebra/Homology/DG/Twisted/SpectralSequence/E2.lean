/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Action
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.FirstDifferential

/-!
# The second page of the index spectral sequence

Let `m` be a twisting cocycle over the generators `P` with values in a DG algebra `A`, and let
`ℳ` be a DG right `A`-module. The entries `m x y` between generators whose indices differ by one
are cycles of degree zero (`TauCeti.TwistingCocycle.m_mem_zero_of_eq_add_one`,
`TauCeti.TwistingCocycle.d_m_eq_zero_of_eq_add_one`), so they act on the cohomology of `ℳ`. The
**classical complex** in coefficient degree `k` has in degree `q` the product over the generators
of index `q` of the cohomology `H^k(ℳ)`, and as differential the matrix of these actions, twisted
by the Koszul sign. It squares to zero by the twisting equation at index difference two
(`TauCeti.TwistingCocycle.sum_subtype_m_mul_m_of_eq_add_two`) and the Leibniz rule.

Under the splitting of the first page of the index spectral sequence into the cohomology of `ℳ`
(`TauCeti.indexGradedPieceHomologyIso`), the first differential is the classical differential
(`TauCeti.TwistingCocycle.indexSpectralSequenceFirstPageXIsoOfEq_comp_indexClassicalD`), so the
second page is the cohomology of the classical complex, the `E²` term of BDHO (Ch. 3, §4.2).

## Main definitions

* `TauCeti.TwistingCocycle.indexClassicalEntry`: the action of `m x y` on cohomology.
* `TauCeti.TwistingCocycle.indexClassicalD`: the matrix of the entries.
* `TauCeti.TwistingCocycle.indexClassicalComplex`: the classical complex in coefficient degree `k`.

## Main results

* `TauCeti.TwistingCocycle.indexSpectralSequenceSecondPageXIso`: the second page of the index
  spectral sequence at `(a, b)` is the homology in degree `b + 1` of the classical complex in
  coefficient degree `a + 2 * b + 1`.

## Implementation notes

The pages are numbered as in Mathlib's `CochainComplex.spectralSequence`: the first page `E₁` is
`page 2` and the second page `E₂` is `page 3`. The object at `(a, b)` of `page 2` is the
cohomology in total degree `a + b` of the graded piece of index `b + 1`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM) (k : ℤ)

/-- The entry of the classical complex in coefficient degree `k` between a generator `x` of index
`q + 1` and a generator `y` of index `q`: the action of the cycle `m x y` of degree zero on the
cohomology of `ℳ` in degree `k`, twisted by the Koszul sign. -/
noncomputable def indexClassicalEntry (q : ℤ) (x : {x : P // ind x = q + 1})
    (y : {y : P // ind y = q}) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1)) ⟶
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) :=
  shiftedModuleComplexActHomology hM
    (m.m_mem_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2]))
    (m.d_m_eq_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2])) q (k - (q + 1)) (k - q)
    (by ring)

/-- The differential of the classical complex in coefficient degree `k`, from the generators of
index `q + 1` to those of index `q`: the matrix of the entries `indexClassicalEntry`. -/
noncomputable def indexClassicalD (q : ℤ) :
    (∏ᶜ fun _ : {x : P // ind x = q + 1} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1))) ⟶
      ∏ᶜ fun _ : {y : P // ind y = q} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) :=
  Pi.lift fun y ↦ ∑ x, Pi.π _ x ≫ m.indexClassicalEntry hM k q x y

/-- **The classical differential squares to zero, entrywise**: for generators `x` of index
`q + 2` and `z` of index `q`, the sum over the generators `y` of index `q + 1` of the composites of
the entries vanishes. On a class `[α]`, the sum is the class of `op (∑ y, m x y * m y z) • α`,
which is `-op (d (m x z)) • α` by the twisting equation, a coboundary by the Leibniz rule. -/
theorem sum_indexClassicalEntry_comp (q : ℤ) (x : {x : P // ind x = q + 1 + 1})
    (z : {z : P // ind z = q}) :
    ∑ y, m.indexClassicalEntry hM k (q + 1) x y ≫ m.indexClassicalEntry hM k q y z = 0 := by
  have hx := x.2
  have hz := z.2
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  obtain ⟨α, hα, rfl⟩ := (shiftedModuleComplex.{uR, uA, uM, uP} hM
    (q + 1 + 1)).exists_homologyπ_moduleCatCyclesMk_eq (k - (q + 1 + 1) + 1) (by simp) c
  have h1 := fun y : {y : P // ind y = q + 1} ↦ exists_shiftedModuleComplexActHomology_homologyπ hM
    (m.m_mem_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2]))
    (m.d_m_eq_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2])) (q + 1)
    (k - (q + 1 + 1)) (k - (q + 1)) (by ring) α hα
  choose β hβ' hβ hβπ using h1
  have h2 := fun y : {y : P // ind y = q + 1} ↦ exists_shiftedModuleComplexActHomology_homologyπ hM
    (m.m_mem_zero_of_eq_add_one (x := y.1) (y := z.1) (by rw [y.2, z.2]))
    (m.d_m_eq_zero_of_eq_add_one (x := y.1) (y := z.1) (by rw [y.2, z.2])) q
    (k - (q + 1)) (k - q) (by ring) (β y) (hβ' y)
  choose γ hγ' hγ hγπ using h2
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply, indexClassicalEntry, hβπ,
    hγπ]
  rw [← map_sum, HomologicalComplex.sum_moduleCatCyclesMk]
  -- Reduction to representatives is done; `α₀` is the underlying cycle of `ℳ` of degree `k`.
  set α₀ := (shiftedModuleComplexXEquiv hM (q + 1 + 1) _ α : M)
  have hα₀ : α₀ ∈ ℳ k := shiftedModuleComplexXEquiv_mem hM (by ring) α
  have hdα₀ : dM α₀ = 0 := (shiftedModuleComplexXEquiv_d_eq_zero_iff hM _ _ α).1 hα
  have hb : -((k.negOnePow : ℤ) • (op (m.m x z) • α₀)) ∈ ℳ (k - q - 1 + q) := by
    have hdeg : k - q - 1 + q = k + -1 := by ring
    rw [hdeg]
    exact neg_mem (zsmul_mem (op_smul_mem_of_mem_graded (m.m_mem_neg_one_of_eq_add_two
      (by rw [hx, hz]; ring)) hα₀) _)
  -- The sum of the composites is a boundary: it is `dM` of the element `hb`-membership provides.
  refine shiftedModuleComplex_homologyπ_eq_zero hM q (k - q) _ _
    ((shiftedModuleComplexXEquiv hM q _).symm ⟨_, hb⟩) ?_
  rw [LinearEquiv.apply_symm_apply, map_sum, Submodule.coe_sum]
  simp only [hγ, hβ]
  -- The twisting equation at index difference two: the double action is by `∑ y, m x y * m y z`.
  rw [Finset.sum_congr rfl fun y _ ↦ op_smul_koszulTwist_op_smul_koszulTwist
      (m.m_mem_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2])) hα₀,
    ← Finset.sum_smul, ← Finset.op_sum, m.sum_subtype_m_mul_m_of_eq_add_two q x.2 z.2]
  -- The Leibniz rule for the cycle `α₀` and the entry `m x z` of degree `-1`.
  have hl := hM.leibniz hα₀ (m.m x z)
  rw [hdα₀, smul_zero, zero_add] at hl
  simp [hl, ← Units.smul_def, smul_smul]

/-- **The classical differential squares to zero**, by `sum_indexClassicalEntry_comp`. -/
theorem indexClassicalD_comp (q : ℤ) :
    m.indexClassicalD hM k (q + 1) ≫ m.indexClassicalD hM k q = 0 := by
  refine Pi.hom_ext _ _ fun z ↦ ?_
  simp only [indexClassicalD, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sum,
    Pi.lift_comp_π_assoc, Preadditive.sum_comp, zero_comp]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  rw [← Preadditive.comp_sum, m.sum_indexClassicalEntry_comp hM k q x z, comp_zero]

/-- **The classical complex** in coefficient degree `k`: in degree `q`, the product over the
generators of index `q` of the cohomology of `ℳ` in degree `k` (as the cohomology of
`shiftedModuleComplex hM q` in degree `k - q`), with the differential `indexClassicalD`, the matrix
of the actions of the entries `m x y` between generators whose indices differ by one. -/
noncomputable def indexClassicalComplex : ChainComplex (ModuleCat.{max uM uP} R) ℤ :=
  ChainComplex.of
    (fun q ↦ ∏ᶜ fun _ : {x : P // ind x = q} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q))
    (m.indexClassicalD hM k) (m.indexClassicalD_comp hM k)

/-- The degree-`q` term of the classical complex is the product over the generators of index `q`
of the cohomology of `ℳ` in degree `k`. -/
noncomputable def indexClassicalComplexXIso (q : ℤ) :
    (m.indexClassicalComplex hM k).X q ≅ ∏ᶜ fun _ : {x : P // ind x = q} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) :=
  -- The terms of `ChainComplex.of` are the given family of objects.
  Iso.refl _

private theorem indexClassicalComplex_d_eq (q : ℤ) :
    (m.indexClassicalComplex hM k).d (q + 1) q = m.indexClassicalD hM k q := by
  unfold indexClassicalComplex
  exact ChainComplex.of_d (fun q ↦ ∏ᶜ fun _ : {x : P // ind x = q} ↦
    (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) (m.indexClassicalD hM k) q

/-- **The differential of the classical complex is `indexClassicalD`**, under the identification
`indexClassicalComplexXIso` of its terms with products of cohomology.  (A plain equation
`d = indexClassicalD` is not available as a public statement, since the complex is not exposed and
its terms are only propositionally the products.) -/
theorem indexClassicalComplexXIso_inv_comp_d_comp_hom (q : ℤ) :
    (m.indexClassicalComplexXIso hM k (q + 1)).inv ≫ (m.indexClassicalComplex hM k).d (q + 1) q ≫
      (m.indexClassicalComplexXIso hM k q).hom = m.indexClassicalD hM k q := by
  rw [indexClassicalComplex_d_eq]
  -- Both identifications are the identity, by definition of `indexClassicalComplexXIso`.
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The components of the classical differential are the entries `indexClassicalEntry`. -/
@[reassoc (attr := simp)]
theorem indexClassicalD_π (q : ℤ) (y : {y : P // ind y = q}) :
    m.indexClassicalD hM k q ≫ Pi.π _ y = ∑ x, Pi.π _ x ≫ m.indexClassicalEntry hM k q x y :=
  Pi.lift_comp_π _ _

/-- **The entries of the classical differential, on classes**: the entry between generators `x` of
index `q + 1` and `y` of index `q` sends the class of a cycle `α` of `ℳ` to the class of
`op (m x y) • ε α`, with `ε` the Koszul sign. -/
theorem indexClassicalEntry_homologyπ (q : ℤ) (x : {x : P // ind x = q + 1})
    (y : {y : P // ind y = q})
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).X (k - (q + 1)))
    (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).d _ (k - (q + 1) + 1)).hom α = 0)
    (β : (shiftedModuleComplex.{uR, uA, uM, uP} hM q).X (k - q))
    (hβ : (shiftedModuleComplexXEquiv hM q (k - q) β : M) =
      op (m.m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
        (shiftedModuleComplexXEquiv hM (q + 1) _ α : M))
    (hβ' : ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).d (k - q) (k - q + 1)).hom β = 0) :
    (m.indexClassicalEntry hM k q x y).hom
        (((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homologyπ _).hom
          ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).moduleCatCyclesMk α _
            (by simp) hα)) =
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).homologyπ _).hom
        ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).moduleCatCyclesMk β _ (by simp) hβ') :=
  shiftedModuleComplexActHomology_homologyπ hM _ _ q _ _ _ α hα β hβ hβ'


section Page

variable [DecidableEq P]

/-- **The entries of the first differential of the index spectral sequence, on cohomology.** Under
the identification of the first page with the cohomology of the graded pieces, the entry of the
differential from `pq` to `pq'` between a generator `x` of index `q + 1` and a generator `y` of
index `q` is the action of `m x y` on the cohomology of `ℳ`. The indices are given with equations,
as in `indexSpectralSequenceFirstPageXIsoOfEq`. -/
theorem homologyMap_single_comp_page_two_d_comp_eval (pq pq' : ℤ × ℤ)
    (hpq' : pq' = (pq.1 + 2, pq.2 - 1)) (q i₁ n n' : ℤ) (hq : q = pq.2) (hi₁ : i₁ = pq'.2)
    (hq' : q = pq'.2 + 1) (hn : n = pq.1 + pq.2) (hn' : n' = pq'.1 + pq'.2)
    (x : {x : P // ind x = q + 1}) (y : {y : P // ind y = q}) :
    HomologicalComplex.homologyMap (indexGradedPieceSingle hM ind x) n ≫
        (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq q (q + 1) hq (by rw [hq]) n hn).inv ≫
        ((m.indexSpectralSequence dM hM).page 2).d pq pq' ≫
        (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq' i₁ q hi₁ hq' n' hn').hom ≫
        HomologicalComplex.homologyMap (indexGradedPieceEval hM ind y) n' =
      shiftedModuleComplexActHomology hM
        (m.m_mem_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2]))
        (m.d_m_eq_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2])) q n n'
        (by rw [hn, hn', hpq']; dsimp only; ring) := by
  obtain ⟨a, b⟩ := pq
  subst hpq'
  dsimp only at hq hi₁ hq' hn hn'
  subst hq hi₁ hn
  obtain rfl : n' = a + q + 1 := by rw [hn']; ring
  ext c : 2
  obtain ⟨α, hα, rfl⟩ := (shiftedModuleComplex.{uR, uA, uM, uP} hM
    (q + 1)).exists_homologyπ_moduleCatCyclesMk_eq (a + q + 1) (by simp) c
  obtain ⟨β, hβ', hβ, hβπ⟩ := exists_shiftedModuleComplexActHomology_homologyπ hM
    (m.m_mem_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2]))
    (m.d_m_eq_zero_of_eq_add_one (x := x.1) (y := y.1) (by rw [x.2, y.2])) q (a + q) (a + q + 1)
    (by ring) α hα
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hβπ, m.homologyMap_indexGradedPieceEval_page_two_d hM x y a α hα]
  congr 1
  refine (shiftedModuleComplex.{uR, uA, uM, uP} hM q).moduleCat_iCycles_injective _ ?_
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, HomologicalComplex.iCycles_moduleCatCyclesMk]
  refine (shiftedModuleComplexXEquiv hM q _).injective (Subtype.ext ?_)
  rw [hβ, shiftedModuleComplexXEquiv_indexGradedPieceEval_D1X_single]

/-- **The first differential of the index spectral sequence is the classical differential**: under
the identifications of the first page with the products of the cohomology of `ℳ`
(`indexSpectralSequenceFirstPageXIsoOfEq` followed by `indexGradedPieceHomologyIso`), the
differential from `pq` to `pq'` is `indexClassicalD`. -/
theorem indexSpectralSequenceFirstPageXIsoOfEq_comp_indexClassicalD (pq pq' : ℤ × ℤ)
    (hpq' : pq' = (pq.1 + 2, pq.2 - 1)) (q i₁ : ℤ) (hq : q = pq.2) (hi₁ : i₁ = pq'.2)
    (hq' : q = pq'.2 + 1) (hn : k - (q + 1) = pq.1 + pq.2) (hn' : k - q = pq'.1 + pq'.2) :
    (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq q (q + 1) hq (by rw [hq]) _ hn).hom ≫
        (indexGradedPieceHomologyIso hM ind _).hom ≫ m.indexClassicalD hM k q =
      ((m.indexSpectralSequence dM hM).page 2).d pq pq' ≫
        (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq' i₁ q hi₁ hq' _ hn').hom ≫
        (indexGradedPieceHomologyIso hM ind _).hom := by
  refine (cancel_epi ((indexGradedPieceHomologyIso hM ind _).inv ≫
    (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq q (q + 1) hq (by rw [hq]) _ hn).inv)).1 ?_
  refine Pi.hom_ext _ _ fun y ↦ ?_
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [indexGradedPieceHomologyIso_inv]
  simp only [Preadditive.sum_comp, Category.assoc, indexGradedPieceHomologyIso_hom_π,
    indexClassicalD_π]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [m.homologyMap_single_comp_page_two_d_comp_eval hM pq pq' hpq' q i₁ _ _ hq hi₁ hq' hn hn' x y]
  rw [indexClassicalEntry]

/-- The first-page differential is the differential of the classical complex, under the
identifications of the first page with the terms of the classical complex. -/
private theorem secondPage_square (pq pq' : ℤ × ℤ) (hpq' : pq' = (pq.1 + 2, pq.2 - 1))
    (q i₁ : ℤ) (hq : q = pq.2) (hi₁ : i₁ = pq'.2) (hq' : q = pq'.2 + 1)
    (hn : k - (q + 1) = pq.1 + pq.2) (hn' : k - q = pq'.1 + pq'.2) :
    (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq q (q + 1) hq (by rw [hq]) _ hn ≪≫
        indexGradedPieceHomologyIso hM ind _).hom ≫ (m.indexClassicalComplex hM k).d (q + 1) q =
      ((m.indexSpectralSequence dM hM).page 2).d pq pq' ≫
        (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq' i₁ q hi₁ hq' _ hn' ≪≫
          indexGradedPieceHomologyIso hM ind _).hom := by
  rw [indexClassicalComplex_d_eq]
  exact (Category.assoc _ _ _).trans
    (m.indexSpectralSequenceFirstPageXIsoOfEq_comp_indexClassicalD hM k pq pq' hpq' q i₁ hq hi₁
      hq' hn hn')

/-- The short complex of the first page around `(a, b)` is isomorphic to the short complex of the
classical complex around degree `b + 1`: the isomorphism is the identification of each first-page
term with a product of cohomology groups, which intertwines the differentials
(`secondPage_square`). -/
noncomputable def indexSecondPageShortComplexIso (a b : ℤ) :
    ((m.indexSpectralSequence dM hM).page 2).sc' (a - 2, b + 1) (a, b) (a + 2, b - 1) ≅
      (m.indexClassicalComplex hM (a + 2 * b + 1)).sc' (b + 1 + 1) (b + 1) b :=
  ShortComplex.isoMk
    (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a - 2, b + 1) (b + 1) (b + 1 + 1) rfl rfl
      (a + 2 * b + 1 - (b + 1 + 1)) (by dsimp only; ring) ≪≫ indexGradedPieceHomologyIso hM ind _)
    (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a, b) b (b + 1) rfl rfl
      (a + 2 * b + 1 - (b + 1)) (by dsimp only; ring) ≪≫ indexGradedPieceHomologyIso hM ind _)
    (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a + 2, b - 1) (b - 1) b rfl
      (by dsimp only; ring) (a + 2 * b + 1 - b) (by dsimp only; ring) ≪≫
        indexGradedPieceHomologyIso hM ind _)
    (m.secondPage_square hM _ (a - 2, b + 1) (a, b)
      (Prod.ext (by dsimp only; ring) (by dsimp only; ring)) (b + 1) b rfl rfl
      (by dsimp only) (by dsimp only; ring) (by dsimp only; ring))
    (m.secondPage_square hM _ (a, b) (a + 2, b - 1) rfl b (b - 1) rfl rfl
      (by dsimp only; ring) (by dsimp only; ring) (by dsimp only; ring))

/-- The first component of `indexSecondPageShortComplexIso`: the first-page term at
`(a - 2, b + 1)` is identified with the product of cohomology groups of `ℳ` (the term of the
classical complex being identified by `indexClassicalComplexXIso`). -/
@[reassoc]
theorem indexSecondPageShortComplexIso_hom_τ₁ (a b : ℤ) :
    (m.indexSecondPageShortComplexIso hM a b).hom.τ₁ ≫
        (m.indexClassicalComplexXIso hM (a + 2 * b + 1) (b + 1 + 1)).hom =
      (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a - 2, b + 1) (b + 1) (b + 1 + 1) rfl rfl
        (a + 2 * b + 1 - (b + 1 + 1)) (by dsimp only; ring) ≪≫
          indexGradedPieceHomologyIso hM ind _).hom := by
  -- `indexClassicalComplexXIso` is the identity, and the component of `isoMk` is the given one.
  exact Category.comp_id _

/-- The second component of `indexSecondPageShortComplexIso`: the first-page term at `(a, b)` is
identified with the product of cohomology groups of `ℳ` (the term of the classical complex being
identified by `indexClassicalComplexXIso`). -/
@[reassoc]
theorem indexSecondPageShortComplexIso_hom_τ₂ (a b : ℤ) :
    (m.indexSecondPageShortComplexIso hM a b).hom.τ₂ ≫
        (m.indexClassicalComplexXIso hM (a + 2 * b + 1) (b + 1)).hom =
      (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a, b) b (b + 1) rfl rfl
        (a + 2 * b + 1 - (b + 1)) (by dsimp only; ring) ≪≫
          indexGradedPieceHomologyIso hM ind _).hom := by
  -- `indexClassicalComplexXIso` is the identity, and the component of `isoMk` is the given one.
  exact Category.comp_id _

/-- The third component of `indexSecondPageShortComplexIso`: the first-page term at
`(a + 2, b - 1)` is identified with the product of cohomology groups of `ℳ` (the term of the
classical complex being identified by `indexClassicalComplexXIso`). -/
@[reassoc]
theorem indexSecondPageShortComplexIso_hom_τ₃ (a b : ℤ) :
    (m.indexSecondPageShortComplexIso hM a b).hom.τ₃ ≫
        (m.indexClassicalComplexXIso hM (a + 2 * b + 1) b).hom =
      (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a + 2, b - 1) (b - 1) b rfl
        (by dsimp only; ring) (a + 2 * b + 1 - b) (by dsimp only; ring) ≪≫
          indexGradedPieceHomologyIso hM ind _).hom := by
  -- `indexClassicalComplexXIso` is the identity, and the component of `isoMk` is the given one.
  exact Category.comp_id _

/-- **The second page of the index spectral sequence is the cohomology of the classical complex**
(BDHO, Definition 3.38 and Ch. 3 §4.2): the object at `(a, b)` of the page `3` of the index
spectral sequence (the classical `E₂` page, in Mathlib's numbering of pages) is the homology in
degree `b + 1` of the classical complex in coefficient degree `a + 2 * b + 1`. It is the
homology of the first page at `(a, b)`, identified with the homology of the classical complex by
`indexSecondPageShortComplexIso` (see `indexSpectralSequenceSecondPageXIso_eq`). -/
noncomputable def indexSpectralSequenceSecondPageXIso (a b : ℤ) :
    ((m.indexSpectralSequence dM hM).page 3).X (a, b) ≅
      (m.indexClassicalComplex hM (a + 2 * b + 1)).homology (b + 1) :=
  ((m.indexSpectralSequence dM hM).iso 2 3 (a, b)).symm ≪≫
    ((m.indexSpectralSequence dM hM).page 2).homologyIsoSc' (a - 2, b + 1) (a, b) (a + 2, b - 1)
      ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
      ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega))) ≪≫
    ShortComplex.homologyMapIso (m.indexSecondPageShortComplexIso hM a b) ≪≫
    ((m.indexClassicalComplex hM (a + 2 * b + 1)).homologyIsoSc' (b + 1 + 1) (b + 1) b
      (by simp) (by simp)).symm

/-- The second-page isomorphism is the inverse of the identification of the second page with the
homology of the first page, followed by the homology isomorphism of
`indexSecondPageShortComplexIso`. -/
theorem indexSpectralSequenceSecondPageXIso_eq (a b : ℤ) :
    m.indexSpectralSequenceSecondPageXIso hM a b =
      ((m.indexSpectralSequence dM hM).iso 2 3 (a, b)).symm ≪≫
        ((m.indexSpectralSequence dM hM).page 2).homologyIsoSc' (a - 2, b + 1) (a, b)
          (a + 2, b - 1)
          ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
          ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega))) ≪≫
        ShortComplex.homologyMapIso (m.indexSecondPageShortComplexIso hM a b) ≪≫
        ((m.indexClassicalComplex hM (a + 2 * b + 1)).homologyIsoSc' (b + 1 + 1) (b + 1) b
          (by simp) (by simp)).symm :=
  (rfl)

end Page

end TwistingCocycle

end TauCeti
