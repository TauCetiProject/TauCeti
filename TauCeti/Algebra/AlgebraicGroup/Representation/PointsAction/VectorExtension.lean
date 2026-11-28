/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.TensorPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Exact
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.Coalgebra.Comodule.Cohomology.Points
public import TauCeti.GroupTheory.GroupExtension.Gauge
public import TauCeti.RepresentationTheory.ToMultiplicative

/-!
# Regular factor sets of vector extensions

For an extension of affine groups with vector kernel and a regular section, its factor
set is a regular two-cochain. The group-extension cocycle identity identifies this cochain
as closed for the given linear quotient action. A regular primitive corrects the section
to a group-scheme section, by multiplication on the left with the negative primitive.

The vector kernel is presented as `Spec (Sym P)`, for a finite projective module `P`.
Its coefficient module is `P*`, and all calculations take place on points over arbitrary
commutative algebras. No diagonalizability hypothesis is needed for this calculation;
such a hypothesis can supply a primitive by averaging in applications.

The factor-set and gauge calculations reuse `TauCeti.GroupExtension.factorSetFun` and
`TauCeti.GroupExtension.isMulCocycle₂_factorSetFun`, and
`GroupExtension.Section.factorSetFun_gauge` gives the correction law.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§15.9–15.10 and Proposition 15.31.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat.IsShortExact

universe u

variable {R : Type u} [CommRing R] {D E : _root_.CommHopfAlgCat.{u} R}
  {P : Type u} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  {p : D ⟶ E} {i : E ⟶ _root_.CommHopfAlgCat.of R (SymmetricAlgebra R P)}
  (h : IsShortExact p i) (s : E →ₐ[R] D)
  (hs : s.comp p.hom.toAlgHom = AlgHom.id R D)

/-- An affine vector extension with a regular section gives an extension of point groups
whose kernel is in tensor coordinates. -/
noncomputable def vectorPointsExtension (A : CommAlgCat.{u} R) :
    GroupExtension (Multiplicative (A ⊗[R] Module.Dual R P))
      (WithConv (E →ₐ[R] A)) (WithConv (D →ₐ[R] A)) where
  inl := (BialgHom.mapDomain i.hom).comp (AdditiveGroup.tensorPointsMulEquiv P A).toMonoidHom
  rightHom := BialgHom.mapDomain p.hom
  inl_injective := (BialgHom.mapDomain_injective_of_surjective i.hom h.surjective).comp
    (AdditiveGroup.tensorPointsMulEquiv P A).injective
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (AdditiveGroup.tensorPointsMulEquiv P A).surjective,
      Subgroup.map_top]
    exact (h.ker_mapPointsFunctor_app_eq_range A).symm
  rightHom_surjective g := by
    refine ⟨toConv (g.ofConv.comp s), ?_⟩
    apply WithConv.ofConv_injective
    simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_assoc, hs, AlgHom.comp_id]

/-- The given regular section as a section of the extension of point groups. -/
noncomputable def vectorPointsSection (A : CommAlgCat.{u} R) :
    (h.vectorPointsExtension s hs A).Section where
  toFun g := toConv (g.ofConv.comp s)
  rightInverse_rightHom g := by
    apply WithConv.ofConv_injective
    simp [vectorPointsExtension, AlgHom.comp_assoc, hs]

@[simp]
theorem vectorPointsSection_apply (A : CommAlgCat.{u} R) (g : WithConv (D →ₐ[R] A)) :
    h.vectorPointsSection s hs A g = toConv (g.ofConv.comp s) := (rfl)

/-- The kernel inclusion in tensor coordinates is the original closed inclusion composed
with the vector-group points equivalence. -/
@[simp]
theorem vectorPointsExtension_inl (A : CommAlgCat.{u} R)
    (x : Multiplicative (A ⊗[R] Module.Dual R P)) :
    (h.vectorPointsExtension s hs A).inl x =
      BialgHom.mapDomain i.hom (AdditiveGroup.tensorPointsMulEquiv P A x) := (rfl)

/-- The projection of the extension of points is induced by the original quotient. -/
@[simp]
theorem vectorPointsExtension_rightHom (A : CommAlgCat.{u} R) :
    (h.vectorPointsExtension s hs A).rightHom = BialgHom.mapDomain p.hom := (rfl)

/-- Tensor coordinates for the kernel inclusion are natural in the value algebra. -/
theorem mapValue_vectorPointsExtension_inl {A B : CommAlgCat.{u} R} (φ : A ⟶ B)
    (x : A ⊗[R] Module.Dual R P) :
    AlgHom.mapValue φ.hom ((h.vectorPointsExtension s hs A).inl (Multiplicative.ofAdd x)) =
      (h.vectorPointsExtension s hs B).inl
        (Multiplicative.ofAdd (LinearMap.rTensor (Module.Dual R P) φ.hom.toLinearMap x)) := by
  simp only [vectorPointsExtension_inl]
  rw [← MonoidHom.comp_apply, ← BialgHom.mapValue_mapDomain,
    MonoidHom.comp_apply, AdditiveGroup.mapValue_tensorPointsMulEquiv]

/-- The point sections induced by a scheme section are natural in the value algebra. -/
theorem mapValue_vectorPointsSection {A B : CommAlgCat.{u} R} (φ : A ⟶ B)
    (g : WithConv (D →ₐ[R] A)) :
    AlgHom.mapValue φ.hom (h.vectorPointsSection s hs A g) =
      h.vectorPointsSection s hs B (AlgHom.mapValue φ.hom g) := by
  simp [AlgHom.comp_assoc]

/-- The factor set of a regular section is natural in the value algebra, in tensor
coordinates on the kernel. -/
theorem rTensor_vectorPointsSection_factorSet {A B : CommAlgCat.{u} R} (φ : A ⟶ B)
    (g j : WithConv (D →ₐ[R] A)) :
    LinearMap.rTensor (Module.Dual R P) φ.hom.toLinearMap
        (GroupExtension.factorSetFun (h.vectorPointsSection s hs A) (g, j)).toAdd =
      (GroupExtension.factorSetFun (h.vectorPointsSection s hs B)
        (AlgHom.mapValue φ.hom g, AlgHom.mapValue φ.hom j)).toAdd := by
  apply Multiplicative.ofAdd.injective
  apply (h.vectorPointsExtension s hs B).inl_injective
  rw [← mapValue_vectorPointsExtension_inl]
  simp only [ofAdd_toAdd, GroupExtension.inl_factorSetFun,
    map_mul, map_inv, mapValue_vectorPointsSection]

/-- The regular two-cochain of the factor set of a section, read off at the universal pair.
The convention is `s(g)s(j) = i(c(g,j))s(gj)`. -/
noncomputable def vectorFactorSet :
    (Module.Dual R P ⊗[R] D) ⊗[R] D :=
  (TensorProduct.assoc R (Module.Dual R P) D D).symm
    (TensorProduct.comm R (D ⊗[R] D) (Module.Dual R P)
      (GroupExtension.factorSetFun
        (h.vectorPointsSection s hs (CommAlgCat.of R (D ⊗[R] D)))
        (toConv (Algebra.TensorProduct.includeLeft (S := R)),
          toConv Algebra.TensorProduct.includeRight)).toAdd)

/-- Evaluation of the regular factor set agrees with the group-extension factor set on
every pair of algebra-valued points. -/
@[simp]
theorem pointTwoCochain_vectorFactorSet (A : CommAlgCat.{u} R)
    (g j : WithConv (D →ₐ[R] A)) :
    Comodule.pointTwoCochain (Module.Dual R P) g.ofConv j.ofConv (h.vectorFactorSet s hs) =
      (GroupExtension.factorSetFun (h.vectorPointsSection s hs A) (g, j)).toAdd := by
  rw [vectorFactorSet, Comodule.pointTwoCochain_assoc_symm_comm]
  have hn := h.rTensor_vectorPointsSection_factorSet s hs
    (CommAlgCat.ofHom (Algebra.TensorProduct.lift g.ofConv j.ofConv
      (fun _ _ ↦ Commute.all _ _)) : CommAlgCat.of R (D ⊗[R] D) ⟶ A)
    (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := D) (B := D)))
    (toConv (Algebra.TensorProduct.includeRight (R := R) (A := D) (B := D)))
  simpa using hn

/-- A section preserving the scheme identity preserves the identity on every point group. -/
theorem vectorPointsSection_one
    (hunit : (Bialgebra.counitAlgHom R D).comp s = Bialgebra.counitAlgHom R E)
    (A : CommAlgCat.{u} R) : h.vectorPointsSection s hs A 1 = 1 := by
  apply WithConv.ofConv_injective
  simp only [vectorPointsSection_apply, ofConv_toConv, AlgHom.convOne_def,
    AlgHom.comp_assoc, hunit]

/-- A normalized section has factor zero when the first argument is the identity. -/
theorem pointTwoCochain_vectorFactorSet_one_left
    (hunit : (Bialgebra.counitAlgHom R D).comp s = Bialgebra.counitAlgHom R E)
    (A : CommAlgCat.{u} R) (g : WithConv (D →ₐ[R] A)) :
    Comodule.pointTwoCochain (Module.Dual R P) (1 : WithConv (D →ₐ[R] A)).ofConv g.ofConv
      (h.vectorFactorSet s hs) = 0 := by
  rw [h.pointTwoCochain_vectorFactorSet s hs A 1 g,
    GroupExtension.Section.factorSetFun_one_left _ (h.vectorPointsSection_one s hs hunit A)]
  rfl

/-- A normalized section has factor zero when the second argument is the identity. -/
theorem pointTwoCochain_vectorFactorSet_one_right
    (hunit : (Bialgebra.counitAlgHom R D).comp s = Bialgebra.counitAlgHom R E)
    (A : CommAlgCat.{u} R) (g : WithConv (D →ₐ[R] A)) :
    Comodule.pointTwoCochain (Module.Dual R P) g.ofConv (1 : WithConv (D →ₐ[R] A)).ofConv
      (h.vectorFactorSet s hs) = 0 := by
  rw [h.pointTwoCochain_vectorFactorSet s hs A g 1,
    GroupExtension.Section.factorSetFun_one_right _ (h.vectorPointsSection_one s hs hunit A)]
  rfl

section LinearAction

variable [Comodule R D (Module.Dual R P)]
  (hact : ∀ (A : CommAlgCat.{u} R) (e : WithConv (E →ₐ[R] A))
    (x : A ⊗[R] Module.Dual R P),
    (h.vectorPointsExtension s hs A).conjAct e (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd
        (Comodule.endOfPoint (Module.Dual R P)
          ((h.vectorPointsExtension s hs A).rightHom e).ofConv x))

include hact

/-- Associativity makes the regular factor set a closed algebraic two-cochain for the
specified linear quotient action. -/
theorem d_vectorFactorSet :
    Comodule.Cohomology.d R D (Module.Dual R P) 2 (h.vectorFactorSet s hs) = 0 := by
  apply (Comodule.d_two_eq_zero_iff (Module.Dual R P) _).mpr
  intro A _ _ g j k
  let := MulDistribMulAction.compHom (Multiplicative (A ⊗[R] Module.Dual R P))
    (Comodule.pointsRepresentation (R := R) (H := D) (A := A) (Module.Dual R P)).toMulAut
  have hsmul (g : WithConv (D →ₐ[R] A)) (x : Multiplicative (A ⊗[R] Module.Dual R P)) :
      g • x = Multiplicative.ofAdd (Comodule.endOfPoint (Module.Dual R P) g.ofConv x.toAdd) := by
    exact (Representation.toMulAut_apply _ g x).trans
      (congrArg (fun f ↦ Multiplicative.ofAdd (f x.toAdd))
        (Comodule.pointsRepresentation_apply (Module.Dual R P) g))
  have ha : (h.vectorPointsExtension s hs (CommAlgCat.of R A)).InducesAction := by
    apply GroupExtension.inducesAction_iff.mpr
    intro e x
    rw [hsmul]
    simpa only [ofAdd_toAdd] using hact (CommAlgCat.of R A) e x.toAdd
  have hc := GroupExtension.isMulCocycle₂_factorSetFun
    (h.vectorPointsSection s hs (CommAlgCat.of R A)) ha g j k
  have hadd := congrArg Multiplicative.toAdd hc
  simp only [toAdd_mul] at hadd
  simp only [h.pointTwoCochain_vectorFactorSet s hs (CommAlgCat.of R A)]
  simp only [hsmul, toAdd_ofAdd] at hadd
  linear_combination (norm := module) -hadd

/-- Changing a regular section by a regular one-cochain changes its factor set by `db`.
The gauge multiplies on the left, fixing the sign of the subsequent correction. -/
theorem factorSetFun_gauge_pointCochain (b : Module.Dual R P ⊗[R] D)
    (A : CommAlgCat.{u} R) (g j : WithConv (D →ₐ[R] A)) :
    (GroupExtension.factorSetFun
      ((h.vectorPointsSection s hs A).gauge
        (fun g ↦ Multiplicative.ofAdd (Comodule.pointCochain (Module.Dual R P) g.ofConv b)))
      (g, j)).toAdd =
        Comodule.pointTwoCochain (Module.Dual R P) g.ofConv j.ofConv
          (h.vectorFactorSet s hs + Comodule.Cohomology.d R D (Module.Dual R P) 1 b) := by
  rw [GroupExtension.Section.factorSetFun_gauge]
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, map_add,
    Comodule.pointTwoCochain_d_one (Module.Dual R P) g j,
    pointTwoCochain_vectorFactorSet]
  rw [hact, (h.vectorPointsSection s hs A).rightHom_section g]
  simp only [toAdd_ofAdd]
  abel

/-- A regular primitive of the factor set corrects the section to a splitting on points. -/
noncomputable def correctedVectorPointsSplitting (b : Module.Dual R P ⊗[R] D)
    (hb : Comodule.Cohomology.d R D (Module.Dual R P) 1 b = h.vectorFactorSet s hs)
    (A : CommAlgCat.{u} R) : (h.vectorPointsExtension s hs A).Splitting :=
  GroupExtension.Section.splittingOfFactorSetEqOne
    ((h.vectorPointsSection s hs A).gauge
      (fun g ↦ Multiplicative.ofAdd (Comodule.pointCochain (Module.Dual R P) g.ofConv (-b))))
      fun g j ↦ by
        apply Multiplicative.toAdd.injective
        rw [h.factorSetFun_gauge_pointCochain s hs hact]
        simp [hb]

/-- The corrected splitting multiplies the original section on the left by the kernel
point of the negative value of the primitive. -/
@[simp]
theorem correctedVectorPointsSplitting_apply (b : Module.Dual R P ⊗[R] D)
    (hb : Comodule.Cohomology.d R D (Module.Dual R P) 1 b = h.vectorFactorSet s hs)
    (A : CommAlgCat.{u} R) (g : WithConv (D →ₐ[R] A)) :
    h.correctedVectorPointsSplitting s hs hact b hb A g =
      (h.vectorPointsExtension s hs A).inl
        (Multiplicative.ofAdd (-Comodule.pointCochain (Module.Dual R P) g.ofConv b)) *
          h.vectorPointsSection s hs A g := by
  rw [correctedVectorPointsSplitting, GroupExtension.Section.splittingOfFactorSetEqOne_apply,
    GroupExtension.Section.gauge_apply,
    map_neg (Comodule.pointCochain (Module.Dual R P) g.ofConv) b]

/-- The corrected splitting is natural in the value algebra. -/
theorem mapValue_correctedVectorPointsSplitting (b : Module.Dual R P ⊗[R] D)
    (hb : Comodule.Cohomology.d R D (Module.Dual R P) 1 b = h.vectorFactorSet s hs)
    {A B : CommAlgCat.{u} R} (φ : A ⟶ B) (g : WithConv (D →ₐ[R] A)) :
    AlgHom.mapValue φ.hom (h.correctedVectorPointsSplitting s hs hact b hb A g) =
      h.correctedVectorPointsSplitting s hs hact b hb B (AlgHom.mapValue φ.hom g) := by
  simp only [correctedVectorPointsSplitting_apply, map_mul,
    h.mapValue_vectorPointsExtension_inl s hs φ, map_neg, Comodule.rTensor_pointCochain,
    h.mapValue_vectorPointsSection s hs φ]
  simp only [AlgHom.mapValue_apply, ofConv_toConv]

/-- The corrected splittings form a natural homomorphism of group-valued point functors. -/
noncomputable def correctedVectorPointsMap (b : Module.Dual R P ⊗[R] D)
    (hb : Comodule.Cohomology.d R D (Module.Dual R P) 1 b = h.vectorFactorSet s hs) :
    HopfAlgebra.pointsFunctor (R := R) (H := D) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := E) where
  app A := GrpCat.ofHom (h.correctedVectorPointsSplitting s hs hact b hb A).toMonoidHom
  naturality {A B} φ := by
    ext g
    exact (h.mapValue_correctedVectorPointsSplitting s hs hact b hb φ g).symm

/-- The corrected natural transformation acts by the corrected point-group splitting. -/
@[simp]
theorem correctedVectorPointsMap_app_apply (b : Module.Dual R P ⊗[R] D)
    (hb : Comodule.Cohomology.d R D (Module.Dual R P) 1 b = h.vectorFactorSet s hs)
    (A : CommAlgCat.{u} R) (g : WithConv (D →ₐ[R] A)) :
    (h.correctedVectorPointsMap s hs hact b hb).app A g =
      h.correctedVectorPointsSplitting s hs hact b hb A g := (rfl)

/-- The group-scheme section obtained from the corrected points by full faithfulness,
expressed contravariantly as a coordinate Hopf-algebra morphism. -/
noncomputable def correctedVectorSection (b : Module.Dual R P ⊗[R] D)
    (hb : Comodule.Cohomology.d R D (Module.Dual R P) 1 b = h.vectorFactorSet s hs) : E ⟶ D :=
  homOfPointsMap (h.correctedVectorPointsMap s hs hact b hb)

/-- The group-scheme section induces the corrected splitting on every value algebra. -/
theorem mapPointsFunctor_correctedVectorSection (b : Module.Dual R P ⊗[R] D)
    (hb : Comodule.Cohomology.d R D (Module.Dual R P) 1 b = h.vectorFactorSet s hs) :
    _root_.CommHopfAlgCat.Hom.mapPointsFunctor (h.correctedVectorSection s hs hact b hb) =
      h.correctedVectorPointsMap s hs hact b hb :=
  mapPointsFunctor_homOfPointsMap _

/-- The corrected group-scheme morphism is a section of the quotient morphism. -/
@[reassoc (attr := simp)]
theorem comp_correctedVectorSection (b : Module.Dual R P ⊗[R] D)
    (hb : Comodule.Cohomology.d R D (Module.Dual R P) 1 b = h.vectorFactorSet s hs) :
    p ≫ h.correctedVectorSection s hs hact b hb = 𝟙 D := by
  apply Quiver.Hom.op_inj
  apply (pointsFunctor (R := R)).map_injective
  have heq :
      _root_.CommHopfAlgCat.Hom.mapPointsFunctor (p ≫ h.correctedVectorSection s hs hact b hb) =
        _root_.CommHopfAlgCat.Hom.mapPointsFunctor (𝟙 D) := by
    rw [_root_.CommHopfAlgCat.Hom.mapPointsFunctor_comp,
      h.mapPointsFunctor_correctedVectorSection s hs hact b hb,
      _root_.CommHopfAlgCat.Hom.mapPointsFunctor_id]
    ext A g
    exact (h.correctedVectorPointsSplitting s hs hact b hb A).rightHom_splitting g
  exact heq

end LinearAction

end TauCeti.CommHopfAlgCat.IsShortExact
