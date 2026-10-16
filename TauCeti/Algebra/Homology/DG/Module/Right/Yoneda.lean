/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GradedCochainComplex
public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Right.DGCategory
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Complex
public import TauCeti.CategoryTheory.DG.Functor
public import TauCeti.CategoryTheory.DG.QuasiEquivalence
public import TauCeti.CategoryTheory.DG.SingleObj

/-!
# The free rank-one right module, the differential graded Yoneda lemma and embedding

A differential graded algebra `A` is a differential graded right module over itself — this is
`TauCeti.IsDGAlgebra.isDGRightModule`, the **free rank-one** right module, the module represented
by the unique object of the one-object differential graded category attached to `A`.

The Yoneda lemma identifies the cochains out of it with the module itself.  A right-module map
`A ⟶ M` is determined by the image of `1`; an element `x` of degree `p` produces the map
`a ↦ x * a`; and the two constructions are mutually inverse and linear over the ground ring.
Evaluation at `1` moreover commutes with the differentials on the nose, because `d 1 = 0` kills
the second term of the graded commutator `d_M ∘ f - (-1)^p f ∘ d_A`.  So the Hom complex out of
the free rank-one module *is* the underlying cochain complex of `M`, and in particular a morphism
of differential graded right modules `A ⟶ M` is the same thing as a degree-zero cycle of `M`.

Taking `M = A`, the inverse of evaluation at `1` sends `a` to left multiplication by `a`, and
these maps assemble into the **differential graded Yoneda embedding** of the one-object
differential graded category `TauCeti.DGSingleObj h` into the differential graded category of
right modules: its unique object goes to the free rank-one module, and a morphism `a` goes to
the right-module cochain `x ↦ a * x`.  Left multiplication commutes with the differentials by
the Leibniz rule, and it preserves composition because both categories put the same Koszul sign
`(-1) ^ (p * q)` between Mathlib's enriched factor order and Keller's composition order.  The
embedding is an isomorphism on every Hom complex, so in particular it is quasi-fully faithful.

## Main definitions

* `TauCeti.dgYonedaCochainEquiv`: evaluation at `1`, as a linear equivalence between the
  degree-`p` right-module cochains out of the free rank-one module and the degree-`p` part of
  `M`.
* `TauCeti.dgYonedaHomEquiv`: morphisms of differential graded right modules out of the free
  rank-one module are the degree-zero cycles of `M`.
* `TauCeti.dgYonedaIso`: the degreewise identification as an isomorphism of cochain complexes.
* `TauCeti.dgYonedaEmbedding`: the differential graded Yoneda embedding of the one-object
  differential graded category of `A` into differential graded right modules.
* `TauCeti.dgYonedaEmbeddingHomEquiv`: its action on morphisms of a fixed degree, a linear
  equivalence.

## Main results

* `TauCeti.dgYonedaEmbeddingHomEquiv_apply`: a morphism `a` acts on the free rank-one module by
  left multiplication.
* `TauCeti.isIso_map_dgYonedaEmbedding`: the Yoneda embedding is an isomorphism on Hom complexes.
* `TauCeti.isQuasiFullyFaithful_dgYonedaEmbedding`: the Yoneda embedding is quasi-fully faithful.

## Implementation notes

The Hom complex out of the free rank-one module has its terms in the universe of
`A →ₗ[Aᵐᵒᵖ] M`, while the underlying complex of `M` has its terms in the universe of `M`; an
isomorphism between them therefore needs the universe of `A` to be at most that of `M`.  This is
what `M : Type (max uA uM)` expresses in `TauCeti.dgYonedaIso`, and it is the widest hypothesis
under which the two complexes are objects of a single category without inserting `ULift`.  The
degreewise statements carry no universe constraint at all.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 4.1.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe u uR uA uM

section Degreewise

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}

/-- **The differential graded Yoneda lemma**, degreewise: evaluation at `1` identifies the
right-module cochains of degree `p` out of the free rank-one module with the degree-`p` part of
`M`.  The inverse sends `x` to right multiplication `a ↦ x * a`. -/
def dgYonedaCochainEquiv (p : ℤ) :
    dgRightModuleCochains (R := R) (A := A) (ℳ := 𝒜) (ℳN := ℳ) p ≃ₗ[R] ℳ p where
  toFun f := ⟨f.1 1, by
    simpa using dgRightModuleCochains.map_mem f (SetLike.one_mem_graded 𝒜)⟩
  invFun x :=
    ⟨{ toFun := fun a ↦ op a • (x : M)
       map_add' := fun a b ↦ by rw [MulOpposite.op_add, add_smul]
       map_smul' := fun c a ↦ by
         simp only [RingHom.id_apply]
         rw [← op_unop c, op_smul_eq_mul, op_mul, op_unop, mul_smul] }, by
      rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
      intro q a ha
      exact SetLike.GradedSMul.smul_mem
        ((InternalGrading.op_mem_opposite_piece_iff _ _ _).mpr
          (by rwa [InternalGrading.ofDecomposition_piece 𝒜])) x.2⟩
  left_inv f := by
    refine Subtype.ext (LinearMap.ext fun a ↦ ?_)
    simpa [op_smul_eq_mul] using (f.1.map_smul (op a) 1).symm
  right_inv x := Subtype.ext (by simp)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

omit [DirectSum.Decomposition ℳ] in
@[simp]
theorem dgYonedaCochainEquiv_apply (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := 𝒜) (ℳN := ℳ) p) :
    (dgYonedaCochainEquiv (ℳ := ℳ) p f : M) = f.1 1 :=
  (rfl)

omit [DirectSum.Decomposition ℳ] in
@[simp]
theorem dgYonedaCochainEquiv_symm_apply (p : ℤ) (x : ℳ p) (a : A) :
    ((dgYonedaCochainEquiv (𝒜 := 𝒜) (ℳ := ℳ) p).symm x).1 a = op a • (x : M) :=
  (rfl)

/-- **The differential graded Yoneda lemma** in degree zero: a morphism of differential graded
right modules out of the free rank-one module is the same thing as a degree-zero cycle of `M`. -/
def dgYonedaHomEquiv (hM : IsDGRightModule h ℳ dM) :
    DGRightModuleHom h.isDGRightModule hM ≃ₗ[R] hM.cyclesDeg 0 where
  toFun f :=
    ⟨⟨f 1, by rw [IsDGRightModule.mem_cycles, f.map_d, h.map_one_eq_zero, map_zero]⟩, by
      simpa using Graded.map_mem f (SetLike.one_mem_graded 𝒜)⟩
  invFun z :=
    { toLinearMap :=
        ((dgYonedaCochainEquiv (𝒜 := 𝒜) (ℳ := ℳ) 0).symm ⟨(z : M), hM.mem_cyclesDeg.mp z.2⟩).1
      map_mem' := fun {_ _} ha ↦ by
        simpa using dgRightModuleCochains.map_mem
          ((dgYonedaCochainEquiv (𝒜 := 𝒜) (ℳ := ℳ) 0).symm
            ⟨(z : M), hM.mem_cyclesDeg.mp z.2⟩) ha
      map_d' := fun a ↦ by
        have key := hM.leibniz (hM.mem_cyclesDeg.mp z.2) a
        rw [hM.mem_cycles.mp (z : hM.cycles).2, smul_zero, zero_add, Int.negOnePow_zero,
          one_smul] at key
        exact key }
  left_inv f := by
    -- The two morphisms are compared at `a`, where the left-hand side is `op a • f 1`, and the
    -- right-module linearity of `f` rewrites that as `f (1 * a)`.
    refine DGRightModuleHom.ext fun a ↦ ?_
    have key := (f.toLinearMap.map_smul (op a) 1).symm
    rwa [op_smul_eq_mul, one_mul] at key
  right_inv z := by
    -- The composite evaluates right multiplication by `z` at `1`.
    refine Subtype.ext (Subtype.ext ?_)
    exact one_smul Aᵐᵒᵖ ((z : hM.cycles) : M)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem dgYonedaHomEquiv_apply (hM : IsDGRightModule h ℳ dM)
    (f : DGRightModuleHom h.isDGRightModule hM) :
    ((dgYonedaHomEquiv hM f : hM.cycles) : M) = f 1 :=
  (rfl)

@[simp]
theorem dgYonedaHomEquiv_symm_apply (hM : IsDGRightModule h ℳ dM) (z : hM.cyclesDeg 0) (a : A) :
    (dgYonedaHomEquiv hM).symm z a = op a • ((z : hM.cycles) : M) :=
  (rfl)

end Degreewise

section Complex

variable {R : Type uR} {A : Type uA} {M : Type (max uA uM)}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}

/-- **The differential graded Yoneda lemma**: the Hom complex out of the free rank-one right
module is the underlying cochain complex of `M`. -/
def dgYonedaIso (hM : IsDGRightModule h ℳ dM) :
    dgRightModuleHomComplex h.isDGRightModule hM ≅
      gradedCochainComplex ℳ dM hM.isHomogeneous (fun _ x ↦ hM.sq_zero x) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (dgYonedaCochainEquiv (𝒜 := 𝒜) (ℳ := ℳ) p).toModuleIso ≪≫
      (eqToIso (gradedCochainComplex_X (hdeg := hM.isHomogeneous)
        (hsq := fun _ x ↦ hM.sq_zero x) p)).symm) <| by
      rintro i j (rfl : i + 1 = j)
      simp only [dgRightModuleHomComplex_X, Iso.trans_hom, LinearEquiv.toModuleIso_hom,
        Iso.symm_hom, eqToIso.inv, dgRightModuleHomComplex_d, Category.assoc]
      apply (cancel_mono (eqToHom (gradedCochainComplex_X (hdeg := hM.isHomogeneous)
        (hsq := fun _ x ↦ hM.sq_zero x) (i + 1)))).1
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ Subtype.ext ?_)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [gradedCochainComplex_d_apply]
      -- Both composites evaluate the cochain at `1`.  The Hom-complex differential is opaque, so
      -- the goal is first written in the form its public application lemma rewrites; the extra
      -- term it produces carries `d 1`, which vanishes.
      change dM (f.1 1) =
        ((dgRightModuleCochains.differential (hM := h.isDGRightModule) (hN := hM) i f).1 :
          A →ₗ[Aᵐᵒᵖ] M) 1
      rw [dgRightModuleCochains.differential_apply, h.map_one_eq_zero, map_zero, smul_zero,
        sub_zero]

@[simp]
theorem dgYonedaIso_hom_f (hM : IsDGRightModule h ℳ dM) (p : ℤ) :
    (dgYonedaIso hM).hom.f p =
      (dgYonedaCochainEquiv (𝒜 := 𝒜) (ℳ := ℳ) p).toModuleIso.hom ≫
        eqToHom (gradedCochainComplex_X (hdeg := hM.isHomogeneous)
          (hsq := fun _ x ↦ hM.sq_zero x) p).symm :=
  (rfl)

@[simp]
theorem dgYonedaIso_inv_f (hM : IsDGRightModule h ℳ dM) (p : ℤ) :
    (dgYonedaIso hM).inv.f p =
      eqToHom (gradedCochainComplex_X (hdeg := hM.isHomogeneous)
        (hsq := fun _ x ↦ hM.sq_zero x) p) ≫
          (dgYonedaCochainEquiv (𝒜 := 𝒜) (ℳ := ℳ) p).toModuleIso.inv :=
  (rfl)

end Complex

section Embedding

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} (h : IsDGAlgebra 𝒜 d)

/-- The action of the differential graded Yoneda embedding on morphisms of degree `n`: a
morphism of the one-object category, an element `a` of degree `n` of the algebra, goes to the
degree-`n` endomorphism `x ↦ a * x` of the free rank-one right module.  It is the inverse of the
degreewise Yoneda lemma `TauCeti.dgYonedaCochainEquiv` for the free rank-one module. -/
noncomputable def dgYonedaEmbeddingHomEquiv (X Y : DGSingleObj h) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R]
      DGHom R n (DGRightModuleCat.of h.isDGRightModule) (DGRightModuleCat.of h.isDGRightModule) :=
  (DGSingleObj.dgHomEquiv X Y n).trans ((dgYonedaCochainEquiv (𝒜 := 𝒜) (ℳ := 𝒜) n).symm.trans
    (DGRightModuleCat.dgHomLinearEquivCochains (DGRightModuleCat.of h.isDGRightModule)
      (DGRightModuleCat.of h.isDGRightModule) n).symm)

variable {h}

/-- The Yoneda embedding sends a morphism `a` of the one-object category to left multiplication
by `a`. -/
-- Not tagged `simp`: its key would contain the projections of the reducible bundling
-- `DGRightModuleCat.of`, which `simp` reduces in the goal, so the lemma could never fire.
theorem dgYonedaEmbeddingHomEquiv_apply {X Y : DGSingleObj h} {n : ℤ} (f : DGHom R n X Y)
    (x : A) :
    (DGRightModuleCat.dgHomLinearEquivCochains _ _ n (dgYonedaEmbeddingHomEquiv h X Y n f)).1 x =
      (DGSingleObj.dgHomEquiv X Y n f : A) * x := by
  simp [dgYonedaEmbeddingHomEquiv]

variable (h)

/-- **The differential graded Yoneda embedding** of a differential graded algebra: the DG functor
from the one-object differential graded category of `A` to differential graded right modules over
`A` which sends the unique object to the free rank-one module and a morphism `a` to left
multiplication by `a`. -/
-- The body is exposed so that the objects `(dgYonedaEmbedding h).obj X` are definitionally the
-- free rank-one module, which the statement of `dgMap_dgYonedaEmbedding` needs to typecheck.
@[expose]
noncomputable def dgYonedaEmbedding :
    EnrichedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (DGSingleObj h)
      (DGRightModuleCat.{u, u, u} h) :=
  EnrichedFunctor.ofDGMap (fun _ ↦ DGRightModuleCat.of h.isDGRightModule)
    (fun {X Y} n ↦ (dgYonedaEmbeddingHomEquiv h X Y n).toLinearMap)
    (fun {X Y} n f ↦ by
      -- Left multiplication by `d a` is the graded commutator of `d` with left multiplication by
      -- `a`: this is the Leibniz rule.
      apply (DGRightModuleCat.dgHomLinearEquivCochains _ _ (n + 1)).injective
      rw [DGRightModuleCat.dgDifferential_eq]
      refine Subtype.ext (LinearMap.ext fun x ↦ ?_)
      rw [dgRightModuleCochains.differential_apply]
      simp only [LinearEquiv.coe_coe]
      rw [dgYonedaEmbeddingHomEquiv_apply, dgYonedaEmbeddingHomEquiv_apply,
        dgYonedaEmbeddingHomEquiv_apply, DGSingleObj.dgHomEquiv_dgDifferential,
        h.leibniz (DGSingleObj.dgHomEquiv X Y n f).2 x, add_sub_cancel_right])
    (fun X ↦ by
      apply (DGRightModuleCat.dgHomLinearEquivCochains _ _ 0).injective
      rw [DGRightModuleCat.dgId_eq]
      refine Subtype.ext (LinearMap.ext fun x ↦ ?_)
      simp only [LinearEquiv.coe_coe]
      rw [dgYonedaEmbeddingHomEquiv_apply, DGSingleObj.dgHomEquiv_dgId, one_mul,
        dgRightModuleCochains.id_apply])
    (fun {X Y Z p q n} f g hpq ↦ by
      -- Both compositions carry the Koszul sign `(-1) ^ (p * q)`; what remains is associativity.
      apply (DGRightModuleCat.dgHomLinearEquivCochains _ _ n).injective
      rw [DGRightModuleCat.dgComp_eq]
      refine Subtype.ext (LinearMap.ext fun x ↦ ?_)
      simp only [LinearEquiv.coe_coe]
      rw [dgYonedaEmbeddingHomEquiv_apply, DGSingleObj.dgHomEquiv_dgComp, Units.smul_def,
        Units.smul_def, Submodule.coe_smul_of_tower, LinearMap.smul_apply,
        dgRightModuleCochains.comp_apply, dgYonedaEmbeddingHomEquiv_apply,
        dgYonedaEmbeddingHomEquiv_apply, smul_mul_assoc, mul_assoc])

/-- The Yoneda embedding sends the unique object to the free rank-one right module. -/
@[simp]
theorem dgYonedaEmbedding_obj (X : DGSingleObj h) :
    (dgYonedaEmbedding h).obj X = DGRightModuleCat.of h.isDGRightModule :=
  (rfl)

variable {h} in
/-- The Yoneda embedding acts on morphisms of degree `n` by `TauCeti.dgYonedaEmbeddingHomEquiv`,
that is, by left multiplication. -/
@[simp]
theorem dgMap_dgYonedaEmbedding {X Y : DGSingleObj h} {n : ℤ} (f : DGHom R n X Y) :
    (dgYonedaEmbedding h).dgMap n f = dgYonedaEmbeddingHomEquiv h X Y n f :=
  EnrichedFunctor.dgMap_ofDGMap _ _ _ _ _ n f

/-- **The differential graded Yoneda embedding is fully faithful**: its map on each Hom complex is
an isomorphism of cochain complexes. -/
theorem isIso_map_dgYonedaEmbedding (X Y : DGSingleObj h) :
    IsIso ((dgYonedaEmbedding h).map X Y) :=
  have (n : ℤ) : IsIso (((dgYonedaEmbedding h).map X Y).f n) :=
    (dgYonedaEmbeddingHomEquiv h X Y n).toModuleIso.isIso_hom
  HomologicalComplex.Hom.isIso_of_components _

/-- The differential graded Yoneda embedding is quasi-fully faithful. -/
theorem isQuasiFullyFaithful_dgYonedaEmbedding : (dgYonedaEmbedding h).IsQuasiFullyFaithful :=
  EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map (isIso_map_dgYonedaEmbedding h)

end Embedding

end TauCeti
