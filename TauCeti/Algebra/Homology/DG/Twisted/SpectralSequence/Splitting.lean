/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# The cohomology of a graded piece of the index filtration

The `p`-th graded piece `⊕_{ind x = p} ℳ ⊗ ⟨x⟩` of the index filtration of a twisted complex is
the twisted complex of the zero cocycle on the generators of index `p`
(`TauCeti.indexGradedPieceComplex`). It carries the differential `dM` on every component, so its
cohomology splits as a product over the generators of index `p` of the cohomology of `ℳ`, shifted
by `p`: in total degree `n`, the component of a generator `x` lies in `ℳ (n + p)`.

The shifted complex is `TauCeti.shiftedModuleComplex hM p`, whose degree-`n` term is `ℳ (n + p)`,
lifted to the universe of the twisted complex.  The splitting is assembled from the chain maps
evaluating a family at a generator (`TauCeti.indexGradedPieceEval`) and inserting an element at a
generator (`TauCeti.indexGradedPieceSingle`), which are inverse to each other up to the sum over
the generators.

## Main definitions

* `TauCeti.shiftedModuleComplex hM p`: the complex `ℳ`, reindexed so that its degree-`n` term is
  `ℳ (n + p)`.
* `TauCeti.indexGradedPieceComplex hM ind p`: the twisted complex of the zero cocycle on the
  generators of index `p`.
* `TauCeti.indexGradedPieceHomologyIso`: the cohomology of the `p`-th graded piece is the product
  over the generators of index `p` of the cohomology of `shiftedModuleComplex hM p`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe uR uA uM uP

section Complex

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (hM : IsDGRightModule h ℳ dM)

/-- The complex of a differential graded right module, reindexed so that its degree-`n` term is
`ℳ (n + p)`, and lifted to a universe containing `uP`. -/
noncomputable def shiftedModuleComplex (p : ℤ) : CochainComplex (ModuleCat.{max uM uP} R) ℤ :=
  gradedCochainComplexLift.{uR, uM, uP} (fun n ↦ ℳ (n + p)) dM
    (hM.isHomogeneous.reindex p) fun _ x ↦ hM.sq_zero x

/-- The degree-`n` term of `shiftedModuleComplex hM p` is `ℳ (n + p)`. -/
noncomputable def shiftedModuleComplexXEquiv (p n : ℤ) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n ≃ₗ[R] ℳ (n + p) :=
  (eqToIso (gradedCochainComplexLift_X n)).toLinearEquiv.trans ULift.moduleEquiv

omit [SMulCommClass R Aᵐᵒᵖ M] in
/-- The differential of `shiftedModuleComplex hM p` is `dM`. -/
theorem shiftedModuleComplexXEquiv_d (p n : ℤ)
    (x : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n) :
    (shiftedModuleComplexXEquiv hM p (n + 1)
        (((shiftedModuleComplex.{uR, uA, uM, uP} hM p).d n (n + 1)).hom x) : M) =
      dM (shiftedModuleComplexXEquiv hM p n x) := by
  have key := gradedCochainComplexLift_d_apply.{uR, uM, uP} (ℳ := fun n ↦ ℳ (n + p))
    (hdeg := hM.isHomogeneous.reindex p) (hsq := fun _ x ↦ hM.sq_zero x) n
    (shiftedModuleComplexXEquiv hM p n x)
  -- `shiftedModuleComplexXEquiv` is the `eqToHom` of `gradedCochainComplexLift_X` followed by
  -- `ULift.down`, which the inverse transport in `key` cancels.
  rw [show (eqToHom (gradedCochainComplexLift_X n).symm)
      (ULift.up (shiftedModuleComplexXEquiv hM p n x)) = x from
    (eqToIso (gradedCochainComplexLift_X.{uR, uM, uP} (hdeg := hM.isHomogeneous.reindex p)
      (hsq := fun _ x ↦ hM.sq_zero x) n)).hom_inv_id_apply x] at key
  exact key

omit [SMulCommClass R Aᵐᵒᵖ M] in
/-- The value of an element of degree `n` of `shiftedModuleComplex hM p` lies in `ℳ j` for every
`j = n + p`. -/
theorem shiftedModuleComplexXEquiv_mem {p n j : ℤ} (hj : j = n + p)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n) :
    (shiftedModuleComplexXEquiv hM p n α : M) ∈ ℳ j :=
  hj ▸ (shiftedModuleComplexXEquiv hM p n α).2

omit [SMulCommClass R Aᵐᵒᵖ M] in
/-- Transport along an equality of degrees does not change the underlying element of `ℳ`. -/
theorem shiftedModuleComplexXEquiv_XIsoOfEq_hom (p i j : ℤ) (hij : i = j)
    (z : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X i) :
    (shiftedModuleComplexXEquiv hM p j
        (((shiftedModuleComplex.{uR, uA, uM, uP} hM p).XIsoOfEq hij).hom.hom z) : M) =
      shiftedModuleComplexXEquiv hM p i z := by
  subst hij
  rfl

omit [SMulCommClass R Aᵐᵒᵖ M] in
/-- A cycle of `shiftedModuleComplex hM p` is a cycle of `ℳ`. -/
theorem shiftedModuleComplexXEquiv_d_eq_zero_iff (p n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n) :
    ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).d n (n + 1)).hom α = 0 ↔
      dM (shiftedModuleComplexXEquiv hM p n α) = 0 := by
  rw [← shiftedModuleComplexXEquiv_d, ← ZeroMemClass.coe_zero (ℳ (n + 1 + p)),
    ← map_zero (shiftedModuleComplexXEquiv hM p (n + 1)), Subtype.coe_inj,
    (shiftedModuleComplexXEquiv hM p (n + 1)).injective.eq_iff]

omit [SMulCommClass R Aᵐᵒᵖ M] in
/-- The class of an element of `shiftedModuleComplex hM p` whose value is `dM` of a value of the
previous degree vanishes. -/
theorem shiftedModuleComplex_homologyπ_eq_zero (p n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n)
    (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).d n (n + 1)).hom α = 0)
    (b : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X (n - 1))
    (hb : (shiftedModuleComplexXEquiv hM p n α : M) = dM (shiftedModuleComplexXEquiv hM p _ b)) :
    ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).homologyπ n).hom
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCatCyclesMk α (n + 1) (by simp) hα) =
      0 := by
  refine ((shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCat_homologyπ_eq_zero_iff (n := n)
    (m := n - 1) (by simp) _).2 ⟨b, ?_⟩
  refine (shiftedModuleComplex.{uR, uA, uM, uP} hM p).moduleCat_iCycles_injective n ?_
  rw [← ModuleCat.comp_apply, HomologicalComplex.toCycles_i,
    HomologicalComplex.iCycles_moduleCatCyclesMk]
  refine (shiftedModuleComplexXEquiv hM p n).injective (Subtype.ext ?_)
  have hd := shiftedModuleComplexXEquiv_d hM p (n - 1) b
  rw [sub_add_cancel] at hd
  rw [hd, hb]

variable (ind : P → ℤ) (p : ℤ)

/-- The twisted complex of the zero cocycle on the generators of index `p`, that is
`⊕_{ind x = p} ℳ ⊗ ⟨x⟩` with the differential `dM` applied to every component. It is the graded
piece `F_p / F_{p-1}` of the index filtration. -/
noncomputable abbrev indexGradedPieceComplex : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  (0 : TwistingCocycle 𝒜 d {x : P // ind x = p} fun x ↦ ind x).twistedCochainComplex dM hM

/-- The degree-`n` term of `indexGradedPieceComplex hM ind p` is the module of families of total
degree `n` indexed by the generators of index `p`. -/
noncomputable abbrev indexGradedPieceComplexXEquiv (n : ℤ) :
    (indexGradedPieceComplex hM ind p).X n ≃ₗ[R]
      twistedTotalGrading ℳ (fun x : {x : P // ind x = p} ↦ ind x) n :=
  twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM n

/-- The differential of `indexGradedPieceComplex hM ind p` is `dM`, applied to every component. -/
theorem indexGradedPieceComplexXEquiv_d (n : ℤ) (f : (indexGradedPieceComplex hM ind p).X n)
    (x : {x : P // ind x = p}) :
    (indexGradedPieceComplexXEquiv hM ind p (n + 1)
        (((indexGradedPieceComplex hM ind p).d n (n + 1)).hom f) : {x : P // ind x = p} → M) x =
      dM ((indexGradedPieceComplexXEquiv hM ind p n f : {x : P // ind x = p} → M) x) := by
  rw [twistedCochainComplexXEquiv_d]
  simp

variable {p}

/-- The evaluation at a generator `x` of index `p`, from the degree-`n` term of the `p`-th graded
piece to `ℳ (n + p)`. -/
noncomputable def indexGradedPieceEvalX (x : {x : P // ind x = p}) (n : ℤ) :
    (indexGradedPieceComplex hM ind p).X n →ₗ[R]
      (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n :=
  (shiftedModuleComplexXEquiv hM p n).symm.toLinearMap ∘ₗ
    ((LinearMap.proj x ∘ₗ
        (twistedTotalGrading ℳ (fun x : {x : P // ind x = p} ↦ ind x) n).subtype).codRestrict
        (ℳ (n + p)) fun f ↦ by
      have hf := mem_twistedTotalGrading_iff.1 f.2 x
      rwa [x.2] at hf) ∘ₗ
    (indexGradedPieceComplexXEquiv hM ind p n).toLinearMap

/-- `indexGradedPieceEvalX` evaluates the underlying family at `x`. -/
@[simp]
theorem shiftedModuleComplexXEquiv_indexGradedPieceEvalX (x : {x : P // ind x = p}) (n : ℤ)
    (f : (indexGradedPieceComplex hM ind p).X n) :
    (shiftedModuleComplexXEquiv hM p n (indexGradedPieceEvalX hM ind x n f) : M) =
      (indexGradedPieceComplexXEquiv hM ind p n f : {x : P // ind x = p} → M) x := by
  simp only [indexGradedPieceEvalX, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  -- The remaining equation holds by unfolding the corestriction of the codomain.
  rfl

/-- **The evaluation at a generator** `x` of index `p`, as a morphism of complexes from the `p`-th
graded piece to `shiftedModuleComplex hM p`. -/
noncomputable def indexGradedPieceEval (x : {x : P // ind x = p}) :
    indexGradedPieceComplex hM ind p ⟶ shiftedModuleComplex.{uR, uA, uM, uP} hM p where
  f n := ModuleCat.ofHom (indexGradedPieceEvalX hM ind x n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (shiftedModuleComplexXEquiv hM p (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [shiftedModuleComplexXEquiv_d, shiftedModuleComplexXEquiv_indexGradedPieceEvalX,
      shiftedModuleComplexXEquiv_indexGradedPieceEvalX, indexGradedPieceComplexXEquiv_d]

/-- `indexGradedPieceEval` evaluates the underlying family at `x`. -/
@[simp]
theorem shiftedModuleComplexXEquiv_indexGradedPieceEval_f (x : {x : P // ind x = p}) (n : ℤ)
    (f : (indexGradedPieceComplex hM ind p).X n) :
    (shiftedModuleComplexXEquiv hM p n (((indexGradedPieceEval hM ind x).f n).hom f) : M) =
      (indexGradedPieceComplexXEquiv hM ind p n f : {x : P // ind x = p} → M) x :=
  shiftedModuleComplexXEquiv_indexGradedPieceEvalX hM ind x n f

variable [DecidableEq P]

/-- The insertion at a generator `x` of index `p`, from `ℳ (n + p)` to the degree-`n` term of the
`p`-th graded piece. -/
noncomputable def indexGradedPieceSingleX (x : {x : P // ind x = p}) (n : ℤ) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n →ₗ[R]
      (indexGradedPieceComplex hM ind p).X n :=
  (indexGradedPieceComplexXEquiv hM ind p n).symm.toLinearMap ∘ₗ
    ((LinearMap.single R (fun _ : {x : P // ind x = p} ↦ M) x ∘ₗ (ℳ (n + p)).subtype).codRestrict
        _ fun α ↦ mem_twistedTotalGrading_iff.2 fun y ↦ by
      by_cases hy : y = x
      · subst hy
        simp [y.2]
      · simp [hy]) ∘ₗ
    (shiftedModuleComplexXEquiv hM p n).toLinearMap

/-- `indexGradedPieceSingleX` inserts an element at `x`. -/
@[simp]
theorem indexGradedPieceComplexXEquiv_indexGradedPieceSingleX (x : {x : P // ind x = p}) (n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n) :
    (indexGradedPieceComplexXEquiv hM ind p n (indexGradedPieceSingleX hM ind x n α) :
        {x : P // ind x = p} → M) = Pi.single x (shiftedModuleComplexXEquiv hM p n α : M) := by
  simp only [indexGradedPieceSingleX, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  -- The remaining equation holds by unfolding the corestriction of the codomain.
  rfl

/-- **The insertion at a generator** `x` of index `p`, as a morphism of complexes from
`shiftedModuleComplex hM p` to the `p`-th graded piece. -/
noncomputable def indexGradedPieceSingle (x : {x : P // ind x = p}) :
    shiftedModuleComplex.{uR, uA, uM, uP} hM p ⟶ indexGradedPieceComplex hM ind p where
  f n := ModuleCat.ofHom (indexGradedPieceSingleX hM ind x n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun α ↦
      (indexGradedPieceComplexXEquiv hM ind p (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    funext y
    rw [indexGradedPieceComplexXEquiv_d, indexGradedPieceComplexXEquiv_indexGradedPieceSingleX,
      indexGradedPieceComplexXEquiv_indexGradedPieceSingleX, shiftedModuleComplexXEquiv_d]
    by_cases hy : y = x
    · subst hy
      simp
    · simp [hy]

/-- `indexGradedPieceSingle` inserts an element at `x`. -/
@[simp]
theorem indexGradedPieceComplexXEquiv_indexGradedPieceSingle_f (x : {x : P // ind x = p})
    (n : ℤ) (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n) :
    (indexGradedPieceComplexXEquiv hM ind p n
        (((indexGradedPieceSingle hM ind x).f n).hom α) : {x : P // ind x = p} → M) =
      Pi.single x (shiftedModuleComplexXEquiv hM p n α : M) :=
  indexGradedPieceComplexXEquiv_indexGradedPieceSingleX hM ind x n α

/-- Inserting at `x` and evaluating at `y` is the identity when `x = y` and zero otherwise. -/
@[reassoc (attr := simp)]
theorem indexGradedPieceSingle_comp_eval (x y : {x : P // ind x = p}) :
    indexGradedPieceSingle hM ind x ≫ indexGradedPieceEval hM ind y =
      if x = y then 𝟙 _ else 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun α ↦
    (shiftedModuleComplexXEquiv hM p n).injective (Subtype.ext ?_))
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    shiftedModuleComplexXEquiv_indexGradedPieceEval_f,
    indexGradedPieceComplexXEquiv_indexGradedPieceSingle_f]
  split_ifs with hxy
  · subst hxy
    simp
  · simp [Ne.symm hxy]

/-- The sum over the generators of index `p` of evaluating and inserting is the identity of the
`p`-th graded piece. -/
@[simp]
theorem sum_indexGradedPieceEval_comp_single :
    ∑ x : {x : P // ind x = p}, indexGradedPieceEval hM ind x ≫ indexGradedPieceSingle hM ind x =
      𝟙 (indexGradedPieceComplex hM ind p) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (indexGradedPieceComplexXEquiv hM ind p n).injective (Subtype.ext ?_))
  rw [← HomologicalComplex.Hom.fAddMonoidHom_apply, map_sum, ModuleCat.hom_sum,
    LinearMap.sum_apply, map_sum, Submodule.coe_sum, HomologicalComplex.id_f, ModuleCat.id_apply]
  funext y
  rw [Finset.sum_apply]
  simp only [HomologicalComplex.Hom.fAddMonoidHom_apply, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply,
    indexGradedPieceComplexXEquiv_indexGradedPieceSingle_f,
    shiftedModuleComplexXEquiv_indexGradedPieceEval_f, Pi.single_apply]
  rw [Finset.sum_eq_single y (fun x _ hx ↦ ite_eq_right fun h : y = x ↦ absurd h.symm hx)
    (fun h ↦ absurd (Finset.mem_univ _) h), ite_eq_left rfl]

/-- **The cohomology of a graded piece of the index filtration**: the cohomology of
`⊕_{ind x = p} ℳ ⊗ ⟨x⟩` in total degree `n` is the product over the generators `x` of index `p`
of the cohomology of `shiftedModuleComplex hM p` in degree `n`, that is of `ℳ` in degree
`n + p`, through the evaluations and insertions at the generators. -/
noncomputable def indexGradedPieceHomologyIso (n : ℤ) :
    (indexGradedPieceComplex hM ind p).homology n ≅
      ∏ᶜ fun _ : {x : P // ind x = p} ↦ (shiftedModuleComplex.{uR, uA, uM, uP} hM p).homology n
    where
  hom := Pi.lift fun x ↦ HomologicalComplex.homologyMap (indexGradedPieceEval hM ind x) n
  inv := ∑ x : {x : P // ind x = p},
    Pi.π _ x ≫ HomologicalComplex.homologyMap (indexGradedPieceSingle hM ind x) n
  hom_inv_id := by
    rw [Preadditive.comp_sum]
    simp only [limit.lift_π_assoc, Fan.mk_π_app, ← HomologicalComplex.homologyMap_comp]
    have key := (HomologicalComplex.homologyFunctor (ModuleCat.{max uP uM} R) (ComplexShape.up ℤ)
      n).map_sum (fun x : {x : P // ind x = p} ↦
        indexGradedPieceEval hM ind x ≫ indexGradedPieceSingle hM ind x) Finset.univ
    rw [sum_indexGradedPieceEval_comp_single, CategoryTheory.Functor.map_id] at key
    exact key.symm
  inv_hom_id := by
    refine Pi.hom_ext _ _ fun y ↦ ?_
    rw [Category.assoc, limit.lift_π, Fan.mk_π_app, Preadditive.sum_comp, Category.id_comp]
    simp only [Category.assoc, ← HomologicalComplex.homologyMap_comp,
      indexGradedPieceSingle_comp_eval]
    rw [Finset.sum_eq_single y (fun x _ hx ↦ ?_) (fun h ↦ absurd (Finset.mem_univ _) h),
      ite_eq_left rfl, HomologicalComplex.homologyMap_id, Category.comp_id]
    rw [ite_eq_right hx, HomologicalComplex.homologyMap_zero, comp_zero]

/-- The component at a generator `x` of `indexGradedPieceHomologyIso` is the map in cohomology of
the evaluation at `x`. -/
@[reassoc (attr := simp)]
theorem indexGradedPieceHomologyIso_hom_π (n : ℤ) (x : {x : P // ind x = p}) :
    (indexGradedPieceHomologyIso hM ind n).hom ≫ Pi.π _ x =
      HomologicalComplex.homologyMap (indexGradedPieceEval hM ind x) n :=
  limit.lift_π _ _

/-- The inverse of `indexGradedPieceHomologyIso` is the sum of the maps in cohomology of the
insertions at the generators. -/
theorem indexGradedPieceHomologyIso_inv (n : ℤ) :
    (indexGradedPieceHomologyIso hM ind (p := p) n).inv = ∑ x : {x : P // ind x = p},
      Pi.π _ x ≫ HomologicalComplex.homologyMap (indexGradedPieceSingle hM ind x) n :=
  -- The inverse is given by this sum in the definition of the isomorphism.
  (rfl)

end Complex

end TauCeti
