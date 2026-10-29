/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded
public import TauCeti.Algebra.Category.GradedModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Small products of curved differential graded right modules

The product is formed degreewise in the category of graded right modules. Its elements are
families with common finite degree support. The differential and right action are componentwise,
so the right Leibniz rule and the common-curvature identity hold in every component. This is the
graded product rather than the unrestricted product of the underlying total modules.

Closed maps into this product have the expected universal property. The homotopy quotient
preserves it: a family of odd homotopies into the factors has a common degree of minus one, so
the finite degree support of a source element also controls the family of its homotopy images.
Consequently the component homotopies lift into the graded product and prove uniqueness in the
quotient. Existence uses fullness of the closed-to-homotopy quotient functor.

No centrality or zero-curvature hypothesis is imposed.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `Curved.Module.Right.Coproduct`: the quotient universal-property
  proof is dualized, using homogeneous product lifts in place of direct-sum descent.
-/

public section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {J : Type u}
  (M : J → CurvedDGRightModuleCat.{u, u, u} h)

local instance : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- The componentwise differential on the underlying degreewise graded product. -/
noncomputable def productDifferential :
    GradedModuleCat.product (fun j ↦ toGradedModuleCat (M j)) →ₗ[R]
      GradedModuleCat.product (fun j ↦ toGradedModuleCat (M j)) :=
  InternalGrading.productLiftLinear (fun j ↦ (toGradedModuleCat (M j)).grading)
    (GradedModuleCat.product (fun j ↦ toGradedModuleCat (M j))).grading 1
    (fun j ↦ (M j).differential.comp
      (InternalGrading.productEval (fun j ↦ (toGradedModuleCat (M j)).grading) j))
    (fun j ↦ by
      rw [LinearMap.isHomogeneous_def]
      intro p x hx
      have hxj : x.1 j ∈ (M j).grading p := by
        simpa only [toGradedModuleCat_piece] using
          (GradedModuleCat.mem_product_piece_iff _ p x).mp hx j
      rw [toGradedModuleCat_piece, LinearMap.comp_apply, InternalGrading.productEval_apply]
      exact (M j).isCurvedDGRightModule.isHomogeneous.map_mem hxj)

/-- The differential of the graded product is computed in each factor. -/
@[simp]
theorem productDifferential_apply
    (x : GradedModuleCat.product (fun j ↦ toGradedModuleCat (M j))) (j : J) :
    (productDifferential M x).1 j = (M j).differential (x.1 j) := by
  dsimp only [productDifferential]
  rw [InternalGrading.productLiftLinear_apply, LinearMap.comp_apply,
    InternalGrading.productEval_apply]

/-- The degreewise product with componentwise curved differential. -/
@[expose, implicit_reducible]
noncomputable def product : CurvedDGRightModuleCat.{u, u, u} h := by
  let P := GradedModuleCat.product (fun j ↦ toGradedModuleCat (M j))
  refine
    { carrier := P
      grading := P.grading.piece
      differential := productDifferential M
      isCurvedDGRightModule := ⟨?_, ?_, ?_⟩ }
  · rw [LinearMap.isHomogeneous_def]
    intro p x hx
    apply (GradedModuleCat.mem_product_piece_iff _ (p + 1) _).mpr
    intro j
    have hxj : x.1 j ∈ (M j).grading p := by
      simpa only [toGradedModuleCat_piece] using
        (GradedModuleCat.mem_product_piece_iff _ p x).mp hx j
    rw [toGradedModuleCat_piece, productDifferential_apply]
    exact (M j).isCurvedDGRightModule.isHomogeneous.map_mem hxj
  · intro p x hx a
    apply Subtype.ext
    funext j
    -- The sum and scalar actions are still typed at the bundled `P.carrier`; the raw
    -- `Submodule.coe_add`/`coe_smul` rules do not match their function-valued coercions.
    -- Align only this carrier arithmetic at `j`, retaining the public differential API.
    change (productDifferential M (op a • x)).1 j =
      op a • (productDifferential M x).1 j + p.negOnePow • (op (d a) • x.1 j)
    rw [productDifferential_apply, productDifferential_apply]
    apply (M j).isCurvedDGRightModule.leibniz
    simpa only [toGradedModuleCat_piece] using
      (GradedModuleCat.mem_product_piece_iff _ p x).mp hx j
  · intro x
    apply Subtype.ext
    funext j
    rw [productDifferential_apply, productDifferential_apply]
    exact (M j).isCurvedDGRightModule.sq_eq (x.1 j)

/-- Product homogeneity is componentwise homogeneity of the family. -/
@[simp]
theorem mem_product_grading_iff (p : ℤ) (x : product M) :
    x ∈ (product M).grading p ↔ ∀ j, x.1 j ∈ (M j).grading p := by
  dsimp only [product]
  simpa only [toGradedModuleCat_piece] using
    (GradedModuleCat.mem_product_piece_iff (fun j ↦ toGradedModuleCat (M j)) p x)

/-- The product differential is the differential in each factor. -/
@[simp]
theorem product_differential_apply (x : product M) (j : J) :
    ((product M).differential x).1 j = (M j).differential (x.1 j) := by
  dsimp only [product]
  exact productDifferential_apply M x j

/-- Forgetting the product differential gives the degreewise graded product. -/
noncomputable def forgetDifferentialProductIso :
    (forgetDifferential (h := h)).obj
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (product M)) ≅
      GradedModuleCat.product (fun j ↦ toGradedModuleCat (M j)) :=
  GradedModuleCat.isoMk (LinearEquiv.refl Aᵐᵒᵖ _) fun p x ↦ by
    -- `isoMk` fixes `x` in the forgetful object’s dependent carrier, so rewriting
    -- `forgetDifferential_obj_of` would also have to transport `x` and cannot match here.
    -- Align only the grading fields and reflexive equivalence, then use the public formulas.
    change x ∈ (toGradedModuleCat (product M)).grading.piece p ↔
      x ∈ (GradedModuleCat.product (fun j ↦ toGradedModuleCat (M j))).grading.piece p
    rw [toGradedModuleCat_piece]
    exact (mem_product_grading_iff M p x).trans
      (by simpa only [toGradedModuleCat_piece] using
        (GradedModuleCat.mem_product_piece_iff
          (fun j ↦ toGradedModuleCat (M j)) p x).symm)

/-- The comparison with the graded product is the identity on underlying families. -/
@[simp]
theorem forgetDifferentialProductIso_hom_hom :
    (forgetDifferentialProductIso M).hom.hom = LinearMap.id := by
  rw [forgetDifferentialProductIso, GradedModuleCat.isoMk_hom_hom]
  rfl

/-- The inverse comparison is also the identity on underlying families. -/
@[simp]
theorem forgetDifferentialProductIso_inv_hom :
    (forgetDifferentialProductIso M).inv.hom = LinearMap.id := by
  rw [forgetDifferentialProductIso, GradedModuleCat.isoMk_inv_hom]
  rfl

/-- The closed projection to one factor of the product. -/
noncomputable def closedProductπ (j : J) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (product M) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j) :=
  closedHomOf (GradedModuleCat.productπ (fun j ↦ toGradedModuleCat (M j)) j).hom
    (by
      intro p x hx
      rw [GradedModuleCat.productπ_apply]
      exact (mem_product_grading_iff M p x).mp hx j)
    (by
      intro x
      rw [GradedModuleCat.productπ_apply, GradedModuleCat.productπ_apply,
        product_differential_apply])

/-- On elements the closed projection is coordinate evaluation. -/
@[simp]
theorem closedHom_closedProductπ_apply (j : J) (x : product M) :
    closedHom (closedProductπ M j) x = x.1 j := by
  rw [closedProductπ, closedHom_closedHomOf]
  exact GradedModuleCat.productπ_apply _ _ _

/-- A family of closed maps lifts into the degreewise product. -/
noncomputable def closedProductLift {N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ∀ j, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j)) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (product M) :=
  closedHomOf (GradedModuleCat.productLift (fun j ↦ toGradedModuleCat (M j))
    (fun j ↦ (forgetDifferential (h := h)).map (f j))).hom
    (by
      intro p x hx
      apply (mem_product_grading_iff M p _).mpr
      intro j
      rw [GradedModuleCat.productLift_apply, forgetDifferential_map_hom]
      exact closedHom_mem (f j) hx)
    (by
      intro x
      apply Subtype.ext
      funext j
      rw [product_differential_apply, GradedModuleCat.productLift_apply,
        GradedModuleCat.productLift_apply, forgetDifferential_map_hom]
      exact differential_closedHom (f j) x)

/-- The lifted closed map has the prescribed components. -/
@[simp]
theorem closedHom_closedProductLift_apply {N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ∀ j, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j)) (x : N) (j : J) :
    (closedHom (closedProductLift M f) x).1 j = closedHom (f j) x := by
  rw [closedProductLift, closedHom_closedHomOf, GradedModuleCat.productLift_apply,
    forgetDifferential_map_hom]

/-- The lifted closed map followed by a projection is the prescribed component. -/
@[reassoc (attr := simp)]
theorem closedProductLift_π {N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ∀ j, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j)) (j : J) :
    closedProductLift M f ≫ closedProductπ M j = f j := by
  apply closedHom_ext
  intro x
  simp only [closedHom_comp, LinearMap.comp_apply, closedHom_closedProductπ_apply,
    closedHom_closedProductLift_apply]

/-- Closed maps into the product are determined by their projections. -/
theorem closedProduct_hom_ext {N : CurvedDGRightModuleCat.{u, u, u} h}
    {f g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (product M)}
    (hfg : ∀ j, f ≫ closedProductπ M j = g ≫ closedProductπ M j) : f = g := by
  apply closedHom_ext
  intro x
  apply Subtype.ext
  funext j
  simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_closedProductπ_apply] using
    congrArg (fun t ↦ closedHom t x) (hfg j)

/-- The fan of closed projections from the degreewise product. -/
noncomputable abbrev closedProductFan :
    Fan fun j ↦ ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j) :=
  Fan.mk (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (product M))
    (closedProductπ M)

/-- The degreewise product is a product in the closed degree-zero category. -/
noncomputable def closedProductFanIsLimit : IsLimit (closedProductFan M) :=
  Fan.IsLimit.mk _ (fun s ↦ closedProductLift M s.proj)
    (fun s j ↦ closedProductLift_π M s.proj j)
    (fun s _ hm ↦ closedProduct_hom_ext M fun j ↦
      (hm j).trans (closedProductLift_π M s.proj j).symm)

noncomputable instance
    (X : J → ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)) : HasProduct X :=
  HasLimit.mk
    { cone := closedProductFan fun j ↦ ForgetEnrichment.to _ (X j)
      isLimit := closedProductFanIsLimit _ }

instance : HasProducts.{u}
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  fun _ ↦ ⟨fun _ ↦ hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

/-- Componentwise homotopies glue to a homotopy into the product. Their common degree of minus
one gives a uniform finite degree support on each source element. -/
theorem dgClosedToHomotopy_map_product_ext {N : CurvedDGRightModuleCat.{u, u, u} h}
    {f g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (product M)}
    (hfg : ∀ j, (dgClosedToHomotopy R).map (f ≫ closedProductπ M j) =
      (dgClosedToHomotopy R).map (g ≫ closedProductπ M j)) :
    (dgClosedToHomotopy R).map f = (dgClosedToHomotopy R).map g := by
  classical
  have hcomponents := fun j ↦ (quotient_map_eq_iff_exists_homotopy _ _).mp (hfg j)
  choose k hk using hcomponents
  have hhom (j : J) : LinearMap.IsHomogeneous ((k j).1.restrictScalars R)
      (InternalGrading.ofDecomposition N.grading).piece
      (toGradedModuleCat (M j)).grading.piece (-1) := by
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    rw [toGradedModuleCat_piece]
    exact (dgRightModuleCochains.mem_iff.mp (k j).2).map_mem
      (by simpa only [InternalGrading.ofDecomposition_piece] using hx)
  let K := InternalGrading.productLift
    (fun j ↦ (toGradedModuleCat (M j)).grading)
    (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition N.grading) (-1) (fun j ↦ (k j).1)
    hhom
  apply (quotient_map_eq_iff_exists_homotopy f g).mpr
  refine ⟨⟨K, ?_⟩, fun x ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p x hx
    apply (mem_product_grading_iff M (p + -1) _).mpr
    intro j
    dsimp only [K, LinearMap.restrictScalars_apply]
    rw [InternalGrading.productLift_apply]
    exact (dgRightModuleCochains.mem_iff.mp (k j).2).map_mem hx
  · apply Subtype.ext
    funext j
    -- The closed maps land in the bundled product, while `K` lands in its scalar-submodule
    -- presentation. The raw `Submodule.coe_sub`/`coe_add` rules do not match these dependent
    -- function-valued coercions. Align just their pointwise arithmetic; keep the named maps.
    change (closedHom f x).1 j - (closedHom g x).1 j =
      ((product M).differential (K x)).1 j + (K (N.differential x)).1 j
    rw [product_differential_apply]
    dsimp only [K]
    rw [InternalGrading.productLift_apply, InternalGrading.productLift_apply]
    simpa only [closedHom_comp, LinearMap.comp_apply,
      closedHom_closedProductπ_apply] using hk j x

/-- The fan of homotopy classes of the product projections. -/
noncomputable abbrev homotopyProductFan : Fan fun j ↦ DGHomotopyCategory.of R (M j) :=
  Fan.mk (DGHomotopyCategory.of R (product M))
    fun j ↦ (dgClosedToHomotopy R).map (closedProductπ M j)

/-- The degreewise product is a product in the curved homotopy category. -/
noncomputable def homotopyProductFanIsLimit : IsLimit (homotopyProductFan M) :=
  Fan.IsLimit.mk _
    (fun s ↦ (dgClosedToHomotopy R).map (closedProductLift M fun j ↦
      (dgClosedToHomotopy R).preimage
        (X := ForgetEnrichment.of _ (DGHomotopyCategory.underlying R s.pt))
        (Y := ForgetEnrichment.of _ (M j)) (s.proj j)))
    (fun s j ↦ by
      simp only [fan_mk_proj, ← Functor.map_comp, closedProductLift_π,
        Functor.map_preimage])
    (fun s m hm ↦ by
      obtain ⟨m, rfl⟩ := (dgClosedToHomotopy R).map_surjective
        (X := ForgetEnrichment.of _ (DGHomotopyCategory.underlying R s.pt))
        (Y := ForgetEnrichment.of _ (product M)) m
      refine dgClosedToHomotopy_map_product_ext M fun j ↦ ?_
      rw [closedProductLift_π, Functor.map_preimage, Functor.map_comp]
      exact hm j)

/-- The quotient functor preserves the degreewise products. -/
instance : PreservesLimit
    (Discrete.functor fun j ↦ ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j))
    (dgClosedToHomotopy R) :=
  preservesLimit_of_preserves_limit_cone (closedProductFanIsLimit M)
    ((isLimitMapConeFanMkEquiv _ _ _).symm (homotopyProductFanIsLimit M))

/-- The quotient functor preserves all products indexed by `J`. -/
instance : PreservesLimitsOfShape (Discrete J)
    (dgClosedToHomotopy R (C := CurvedDGRightModuleCat.{u, u, u} h)) :=
  ⟨fun {F} ↦ preservesLimit_of_iso_diagram (K₁ := Discrete.functor fun j ↦
    ForgetEnrichment.of _ (ForgetEnrichment.to (CochainComplex (ModuleCat R) ℤ) (F.obj ⟨j⟩)))
    _ (Discrete.natIsoFunctor (F := F)).symm⟩

noncomputable instance (X : J → DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    HasProduct X :=
  HasLimit.mk
    { cone := homotopyProductFan fun j ↦ DGHomotopyCategory.underlying R (X j)
      isLimit := homotopyProductFanIsLimit _ }

instance : HasProducts.{u} (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  fun _ ↦ ⟨fun _ ↦ hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

end TauCeti.CurvedDGRightModuleCat
