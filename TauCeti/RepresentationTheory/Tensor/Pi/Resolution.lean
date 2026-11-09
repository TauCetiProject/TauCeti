/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum
public import TauCeti.RepresentationTheory.Tensor.Pi.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded.Contraction
import TauCeti.Algebra.Ring.Commute

/-!
# Contracted resolutions of finite dependent tensor products

The tensor product of a finite family of smooth discrete graded representations carries the
sum of their differentials in characteristic two. If the factors are contracted onto their
coefficients, the tensor product is contracted onto the tensor product of those coefficients.
The retraction is factorwise; for a chosen order on the factors the homotopy applies the
retraction followed by augmentation before its slot, the factor homotopy at the slot, and the
identity afterwards.

The factors may have different carriers and different gradings. In the double-coset formula for
Evens' norm each factor is the tensor-induced resolution attached to one orbit, whose coset
space and coefficient representation vary with the orbit. The construction supplies the outer
contracted complex used for products of orbitwise cohomology classes.

The contraction data are supplied on the factors' total modules, as for
`TopRep.ResolutionContraction.ofGraded`. Its conjugate-continuity conditions hold because the
representations are smooth discrete. The index type's `Fintype` and order are parameters,
including for the empty family, whose tensor product is the scalar ring. The total contraction
identity is the dependent tensor trick `TauCeti.PiTensorProduct.slotSum_comp_slotHomotopy_add`.

The characteristic augmentation, retraction and homotopy equations are named rewrites. Their
native tensor carriers and the bundled representation carriers have different presentations of
the same module instances, so these equations are not reliable simplifier normal forms.

## Main definitions

* `TauCeti.smoothPiTensorProductDifferential`: the slot differential on that carrier.
* `TauCeti.smoothPiTensorProductContraction`: the contraction onto tensor-product coefficients.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. **108** (1963), §§2–6, for tensor products of contracted resolutions.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {I : Type x} [Fintype I]

variable (M : I → DiscreteRep.{u, v, max v w} R G)
  (d : ∀ i, M i ⟶ M i)

/-- The sum of the factor differentials, applied in one tensor slot at a time. -/
noncomputable def smoothPiTensorProductDifferential :
    ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)) ⟶
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)) := by
  classical
  have := (((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M))).property.discreteTopology
  exact ObjectProperty.homMk <| TopRep.ofHom
    { toContinuousLinearMap :=
        ⟨PiTensorProduct.slotSum I (fun i ↦ (d i).toLinearMap),
          continuous_of_discreteTopology⟩
      isIntertwining' g := by
        ext z
        exact (congrArg (PiTensorProduct.slotSum I (fun i ↦ (d i).toLinearMap))
          ((DiscreteRep.piTensorProduct_ρ_apply M g z).trans
            (LinearMap.congr_fun (Representation.piTensorProduct_apply _ g) z))).trans <|
          (LinearMap.congr_fun (PiTensorProduct.slotSum_comp_map
          (g := fun i ↦ (M i).ρ g)
          (f := fun i ↦ (d i).toLinearMap)
          (f' := fun i ↦ (d i).toLinearMap)
          (fun i ↦ LinearMap.ext fun z ↦ (d i).isIntertwining _ _ g z)) z).trans
            ((DiscreteRep.piTensorProduct_ρ_apply M g _).trans
              (LinearMap.congr_fun (Representation.piTensorProduct_apply _ g) _)).symm }

omit [IsTopologicalGroup G] in
/-- The differential is the slot sum on the native tensor carrier. -/
theorem smoothPiTensorProductDifferential_apply [DecidableEq I]
    (z : ⨂[R] i, (M i).V) :
    (smoothPiTensorProductDifferential M d).hom.hom z =
      PiTensorProduct.slotSum I (fun i ↦ (d i).toLinearMap) z := by
  obtain rfl : ‹DecidableEq I› = Classical.decEq _ := Subsingleton.elim _ _
  rfl

section Grading

variable (ℳ : ∀ i, ℤ → Submodule R (M i).V)
  (hρ : ∀ i n g v, v ∈ ℳ i n → (M i).ρ g v ∈ ℳ i n)
  (hd : ∀ i, LinearMap.IsHomogeneous (d i).toLinearMap (ℳ i) (ℳ i) 1)

omit [IsTopologicalGroup G] in
include hρ in
/-- The factorwise action preserves total degree. -/
theorem piTensorProduct_totalDegreePiece_ρ_mem (n : ℤ) (g : G)
    (z : ⨂[R] i, (M i).V) (hz : z ∈ PiTensorProduct.totalDegreePiece I ℳ n) :
    (((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)).obj.ρ g) z ∈
      PiTensorProduct.totalDegreePiece I ℳ n := by
  have he : (((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)).obj.ρ g) z =
      PiTensorProduct.map (fun i ↦ (M i).ρ g) z :=
    (DiscreteRep.piTensorProduct_ρ_apply M g z).trans
      (LinearMap.congr_fun (Representation.piTensorProduct_apply _ g) z)
  have hf : ∀ i, LinearMap.IsHomogeneous ((M i).ρ g) (ℳ i) (ℳ i) 0 :=
    fun i ↦ LinearMap.isHomogeneous_def.2 fun p v hv ↦ by
      rw [add_zero]
      exact hρ i p g v hv
  have hz' := (PiTensorProduct.isHomogeneous_map hf).map_mem hz
  rw [Finset.sum_const_zero, add_zero] at hz'
  exact he.symm ▸ hz'

omit [IsTopologicalGroup G] in
include hd in
/-- The slot differential raises total degree by one. -/
theorem isHomogeneous_smoothPiTensorProductDifferential :
    LinearMap.IsHomogeneous (smoothPiTensorProductDifferential M d).hom.hom.toLinearMap
      (PiTensorProduct.totalDegreePiece I ℳ) (PiTensorProduct.totalDegreePiece I ℳ) 1 := by
  classical
  exact LinearMap.isHomogeneous_def.2 fun n z hz ↦
    (smoothPiTensorProductDifferential_apply M d z).symm ▸
      (PiTensorProduct.isHomogeneous_slotSum hd).map_mem hz

end Grading

variable (hM : ∀ i (v : (M i).V), v + v = 0)
  (hdd : ∀ i, (d i).toLinearMap ∘ₗ (d i).toLinearMap = 0)

omit [IsTopologicalGroup G] in
include hM hdd in
/-- The tensor differential squares to zero when the factor differentials do, in characteristic
 two on the factors. The empty family needs no characteristic assumption on the scalar ring. -/
theorem smoothPiTensorProductDifferential_sq :
    (smoothPiTensorProductDifferential M d).hom ≫
      (smoothPiTensorProductDifferential M d).hom = 0 := by
  classical
  ext z
  exact (smoothPiTensorProductDifferential_apply M d _).trans
    ((congrArg (PiTensorProduct.slotSum I (fun i ↦ (d i).toLinearMap))
      (smoothPiTensorProductDifferential_apply M d z)).trans
        (LinearMap.congr_fun (PiTensorProduct.slotSum_comp_slotSum hM hdd) z))

section Contraction

variable (X : I → DiscreteRep.{u, v, max v w} R G)
  (ℳ : ∀ i, ℤ → Submodule R (M i).V)
  (hρ : ∀ i n g v, v ∈ ℳ i n → (M i).ρ g v ∈ ℳ i n)
  (hd : ∀ i, LinearMap.IsHomogeneous (d i).toLinearMap (ℳ i) (ℳ i) 1)
  (a : ∀ i, X i ⟶ M i) (ha : ∀ i v, (a i).toLinearMap v ∈ ℳ i 0)
  (π : ∀ i, (M i).V →ₗ[R] (X i).V) (h : ∀ i, Module.End R (M i).V)
  (hh : ∀ i, LinearMap.IsHomogeneous (h i) (ℳ i) (ℳ i) (-1))
  (hπa : ∀ i v, π i ((a i).toLinearMap v) = v)
  (hπ : ∀ i p, 0 < p → ∀ v ∈ ℳ i p, π i v = 0)
  (hneg : ∀ i p, p < 0 → ℳ i p = ⊥)
  (hdh : ∀ i v, (d i).toLinearMap (h i v) + h i ((d i).toLinearMap v) =
    v - (a i).toLinearMap (π i v))
  [LinearOrder I]

omit [DiscreteTopology R] [IsTopologicalGroup G] in
include ha hh hπ hneg in
/-- The ordered slot homotopy lowers the total degree by one. -/
theorem isHomogeneous_piTensorProductSlotHomotopy :
    LinearMap.IsHomogeneous
      (PiTensorProduct.slotHomotopy I (fun i ↦ (a i).toLinearMap ∘ₗ π i) h)
      (PiTensorProduct.totalDegreePiece I ℳ) (PiTensorProduct.totalDegreePiece I ℳ) (-1) := by
  refine PiTensorProduct.isHomogeneous_slotHomotopy (fun i ↦ ?_) hh
  exact LinearMap.isHomogeneous_def.2 fun p v hv ↦ by
    rw [add_zero]
    rcases lt_trichotomy p 0 with hp | rfl | hp
    · rw [hneg i p hp, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact zero_mem _
    · exact ha i _
    · rw [LinearMap.comp_apply, hπ i p hp v hv, map_zero]
      exact zero_mem _

/-- The finite dependent tensor product of contracted graded smooth discrete representations is
contracted onto the tensor product of their coefficients. The tensor augmentation and retraction
are factorwise, and the homotopy is the ordered slot homotopy. No equivariance is required of the
factor retractions and homotopies. -/
noncomputable def smoothPiTensorProductContraction :
    TopRep.ResolutionContraction.{u, v, max u w x}
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct X)).obj
      ((((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)).obj).gradedCochainComplex
        (PiTensorProduct.totalDegreePiece I ℳ)
        (piTensorProduct_totalDegreePiece_ρ_mem M ℳ hρ)
        (smoothPiTensorProductDifferential M d).hom
        (isHomogeneous_smoothPiTensorProductDifferential M d ℳ hd)
        (smoothPiTensorProductDifferential_sq M d hM hdd)) := by
  classical
  -- Tensor the augmentation and retraction, then use the ordered slot homotopy.
  -- Smooth discreteness supplies the conjugate-continuity conditions at the end.
  let A := ((toSmoothDiscrete R G).map ((DiscreteRep.piTensorProductFunctor R G I).map a)).hom
  have hA (z : ⨂[R] i, (X i).V) : A.hom z =
      PiTensorProduct.map (fun i ↦ (a i).toLinearMap) z :=
    (toSmoothDiscrete_map_hom_hom_apply R G
      ((DiscreteRep.piTensorProductFunctor R G I).map a) z).trans
        (LinearMap.congr_fun (DiscreteRep.piTensorProductFunctor_map_toLinearMap a) z)
  have hh₀ (i : I) (v : (M i).V) (hv : v ∈ ℳ i 0) : h i v = 0 := by
    have hv' := (hh i).map_mem hv
    rw [zero_add, hneg i (-1) (by decide)] at hv'
    exact (Submodule.mem_bot R).mp hv'
  exact TopRep.ResolutionContraction.ofGraded.{u, v, max u w x} _ A
    (fun z ↦ (hA z).symm ▸ PiTensorProduct.map_mem_totalDegreePiece_zero ha z)
    (PiTensorProduct.map π)
    (PiTensorProduct.slotHomotopy I (fun i ↦ (a i).toLinearMap ∘ₗ π i) h)
    (isHomogeneous_piTensorProductSlotHomotopy M X ℳ a ha π h hh hπ hneg)
    (fun z ↦ by
      have he : ∀ i, π i ∘ₗ (a i).toLinearMap = LinearMap.id :=
        fun i ↦ LinearMap.ext (hπa i)
      exact (congrArg (PiTensorProduct.map π) (hA z)).trans <|
        (LinearMap.congr_fun (PiTensorProduct.map_comp π
        (fun i ↦ (a i).toLinearMap)) z).symm.trans
          ((congrArg (fun f ↦ f z) (congrArg PiTensorProduct.map (funext he))).trans
            (LinearMap.congr_fun PiTensorProduct.map_id z)))
    (fun n _ hz ↦ PiTensorProduct.map_eq_zero_of_mem_totalDegreePiece_of_pos hπ
      (Int.natCast_pos.2 n.succ_pos) hz)
    (fun _ hz ↦ PiTensorProduct.slotHomotopy_eq_zero_of_mem_totalDegreePiece_zero hneg hh₀ hz)
    (fun z ↦ by
      -- A differential commutes with its contraction projector because its square vanishes.
      have hde (i : I) : (d i).toLinearMap ∘ₗ ((a i).toLinearMap ∘ₗ π i) =
          ((a i).toLinearMap ∘ₗ π i) ∘ₗ (d i).toLinearMap := by
        exact (commute_of_sq_zero_of_homotopy (hdd i) (LinearMap.ext (hdh i))).eq
      have hh' := LinearMap.congr_fun (PiTensorProduct.slotSum_comp_slotHomotopy_add hM hde
        (fun i ↦ LinearMap.ext (hdh i))) z
      exact (congrArg₂ (fun (v w : ⨂[R] i, (M i).V) ↦ v + w)
        (smoothPiTensorProductDifferential_apply M d _)
        (congrArg (PiTensorProduct.slotHomotopy I (fun i ↦ (a i).toLinearMap ∘ₗ π i) h)
          (smoothPiTensorProductDifferential_apply M d z))).trans
            (hh'.trans <| (congrArg (z - ·) (LinearMap.congr_fun
              (PiTensorProduct.map_comp (fun i ↦ (a i).toLinearMap) π) z)).trans
                (congrArg (z - ·) (hA (PiTensorProduct.map π z)).symm)))
    (IsSmoothDiscrete.continuous_conj
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)).property
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct X)).property _)
    (IsSmoothDiscrete.continuous_conj
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)).property
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)).property _)

/-- The augmentation of the dependent tensor contraction applies each factor augmentation. -/
theorem smoothPiTensorProductContraction_ι_apply (z : ⨂[R] i, (X i).V) :
    ((smoothPiTensorProductContraction M d hM hdd X ℳ hρ hd a ha π h hh hπa hπ hneg
      hdh).ι.hom z).1 = PiTensorProduct.map (fun i ↦ (a i).toLinearMap) z := by
  -- Naming the graded term keeps its module instance fixed when evaluating the morphism
  -- equality across the sealed tensor-product carrier.
  let J := (((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)).obj).gradedCochainComplex
    (PiTensorProduct.totalDegreePiece I ℳ) (piTensorProduct_totalDegreePiece_ρ_mem M ℳ hρ)
    (smoothPiTensorProductDifferential M d).hom
    (isHomogeneous_smoothPiTensorProductDifferential M d ℳ hd)
    (smoothPiTensorProductDifferential_sq M d hM hdd)
  exact (congrArg (fun f : ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct X)).obj ⟶
      J.X 0 ↦ (f.hom z).1)
    (TopRep.ResolutionContraction.ofGraded_ι.{u, v, max u w x}
      _ _ _ _ _ _ _ _ _ _ _ _)).trans
    ((TopRep.gradedCochainComplexLift_apply
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct M)).obj
      (PiTensorProduct.totalDegreePiece I ℳ) (piTensorProduct_totalDegreePiece_ρ_mem M ℳ hρ)
      (smoothPiTensorProductDifferential M d).hom
      (isHomogeneous_smoothPiTensorProductDifferential M d ℳ hd)
      (smoothPiTensorProductDifferential_sq M d hM hdd) 0
      ((toSmoothDiscrete R G).map ((DiscreteRep.piTensorProductFunctor R G I).map a)).hom
      _ z).trans
      ((toSmoothDiscrete_map_hom_hom_apply R G
        ((DiscreteRep.piTensorProductFunctor R G I).map a) z).trans
          (LinearMap.congr_fun (DiscreteRep.piTensorProductFunctor_map_toLinearMap a) z)))

/-- The retraction of the dependent tensor contraction applies each factor retraction. -/
theorem smoothPiTensorProductContraction_proj_apply (z) :
    (smoothPiTensorProductContraction M d hM hdd X ℳ hρ hd a ha π h hh hπa hπ hneg
      hdh).proj z = PiTensorProduct.map π z.1 := by
  unfold smoothPiTensorProductContraction
  exact TopRep.ResolutionContraction.ofGraded_proj_apply.{u, v, max u w x}
    _ _ _ _ _ _ _ _ _ _ _ _ z

/-- The homotopy of the dependent tensor contraction is the ordered slot homotopy. -/
theorem smoothPiTensorProductContraction_hom_apply (n : ℕ) (z) :
    ((smoothPiTensorProductContraction M d hM hdd X ℳ hρ hd a ha π h hh hπa hπ hneg
      hdh).hom n z).1 =
      PiTensorProduct.slotHomotopy I (fun i ↦ (a i).toLinearMap ∘ₗ π i) h z.1 := by
  unfold smoothPiTensorProductContraction
  exact TopRep.ResolutionContraction.ofGraded_hom_apply.{u, v, max u w x}
    _ _ _ _ _ _ _ _ _ _ _ _ n z

end Contraction

end TauCeti
