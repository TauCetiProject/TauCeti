/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Graph
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Gluing lattices with opposite discriminant forms

An isometry between the discriminant form of an even lattice `L` and the negative
discriminant form of `M` determines an even unimodular overlattice of `L ⊥ M`.
Its vectors are precisely the pairs in the two dual carriers whose discriminant
classes correspond under the isometry. In particular, its intersection with either
coordinate space is the original lattice, the condition needed for primitive embeddings.

The construction uses the existing discriminant-product isometry and isotropic-subgroup
gluing correspondence. The ambient rational form is the orthogonal sum form throughout.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.6.1.
-/

public section

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
variable (hL : L.IsEven) (hM : M.IsEven)
variable (e : FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
  (M.discriminantQuadraticModule hM).neg)

/-- The graph glue subgroup, transported to the actual discriminant group of `L ⊥ M`. -/
noncomputable def discriminantGraph : AddSubgroup (L.orthogonalSum M).DiscriminantGroup :=
  e.toAddEquiv.toAddMonoidHom.graph.comap (L.discriminantGroupOrthogonalSumEquiv M).toAddMonoidHom

/-- A class lies in the glue subgroup exactly when its components correspond under `e`. -/
@[simp]
theorem mem_discriminantGraph_iff (x : (L.orthogonalSum M).DiscriminantGroup) :
    x ∈ L.discriminantGraph M hL hM e ↔
      e (L.discriminantGroupOrthogonalSumEquiv M x).1 =
        (L.discriminantGroupOrthogonalSumEquiv M x).2 :=
  (Iff.rfl)

/-- The graph glue is quadratic Lagrangian in the discriminant form of the orthogonal sum. -/
theorem isLagrangian_discriminantGraph :
    ((L.orthogonalSum M).discriminantQuadraticModule
      ((L.isEven_orthogonalSum_iff M).mpr ⟨hL, hM⟩)).IsLagrangian
        (L.discriminantGraph M hL hM e) := by
  let f := L.discriminantQuadraticIsometryOrthogonalSum M hL hM
  have hgraph := ((L.discriminantQuadraticModule hL).isLagrangian_graph_iff
    (M.discriminantQuadraticModule hM) e.toAddEquiv
      (L.isNondegenerate_discriminantQuadraticModule hL)).mpr
        (fun x ↦ by
          -- Read the negative quadratic map on the unchanged carrier of the target.
          have h : -(M.discriminantQuadraticModule hM).quadratic (e x) =
              (L.discriminantQuadraticModule hL).quadratic x := e.map_app x
          exact neg_eq_iff_eq_neg.mp h)
  apply (FiniteQuadraticModule.Isometry.isLagrangian_map_iff _ f
    (L.discriminantGraph M hL hM e)).mp
  convert hgraph using 1
  ext x
  -- Reveal the graph and image predicates on the canonical discriminant-group carriers.
  -- The bundled quadratic modules hide these carrier identifications from rewriting.
  change (∃ y, e (L.discriminantGroupOrthogonalSumEquiv M y).1 =
    (L.discriminantGroupOrthogonalSumEquiv M y).2 ∧ f y = x) ↔ e x.1 = x.2
  have hf (y : (L.orthogonalSum M).DiscriminantGroup) :
      f y = L.discriminantGroupOrthogonalSumEquiv M y :=
    L.discriminantQuadraticIsometryOrthogonalSum_apply M hL hM y
  simp_rw [hf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    have hd := (L.discriminantGroupOrthogonalSumEquiv M).apply_symm_apply x
    exact ⟨(L.discriminantGroupOrthogonalSumEquiv M).symm x, hd.symm ▸ hx, hd⟩

/-- Glue two even nondegenerate lattices along an isometry of opposite discriminant forms. -/
noncomputable def glueAlongDiscriminant : IntegralLattice (V × W) :=
  (L.orthogonalSum M).ofIsotropicSubgroup
    ((L.isEven_orthogonalSum_iff M).mpr ⟨hL, hM⟩)
    (L.discriminantGraph M hL hM e)
    (L.isLagrangian_discriminantGraph M hL hM e).isIsotropic

/-- Gluing retains the rational orthogonal sum form. -/
@[simp]
theorem glueAlongDiscriminant_form :
    (L.glueAlongDiscriminant M hL hM e).form = (L.orthogonalSum M).form :=
  (L.orthogonalSum M).ofIsotropicSubgroup_form _ _ _

/-- Graph gluing preserves nondegeneracy of the rational orthogonal sum. -/
instance instIsNondegenerateGlueAlongDiscriminant :
    (L.glueAlongDiscriminant M hL hM e).IsNondegenerate :=
  ⟨by rw [glueAlongDiscriminant_form]; exact (L.orthogonalSum M).form_nondegenerate⟩

/-- The graph-glued lattice is even. -/
theorem isEven_glueAlongDiscriminant : (L.glueAlongDiscriminant M hL hM e).IsEven :=
  (L.orthogonalSum M).isEven_ofIsotropicSubgroup _ _ _

/-- The graph-glued lattice is unimodular. -/
theorem isUnimodular_glueAlongDiscriminant :
    (L.glueAlongDiscriminant M hL hM e).IsUnimodular := by
  apply ((L.orthogonalSum M).isUnimodular_ofIsotropicSubgroup_iff_isLagrangian _ _ _).mpr
  exact (L.isLagrangian_discriminantGraph M hL hM e).toFiniteBilinearModule

/-- Membership of a pair of dual vectors is exactly the equality of their glue classes. -/
@[simp]
theorem mem_glueAlongDiscriminant_iff (x : L.dualCarrier) (y : M.dualCarrier) :
    (x.1, y.1) ∈ (L.glueAlongDiscriminant M hL hM e).carrier ↔
      e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  rw [glueAlongDiscriminant, ofIsotropicSubgroup_carrier]
  have h := (L.orthogonalSum M).coe_mem_intermediateCarrierOfDiscriminantSubgroup_iff
    (L.discriminantGraph M hL hM e) ((L.orthogonalSumDualCarrierEquiv M).symm (x, y))
  simpa only [coe_orthogonalSumDualCarrierEquiv_symm_apply, mem_discriminantGraph_iff,
    discriminantGroupOrthogonalSumEquiv_mk, LinearEquiv.apply_symm_apply] using h

/-- The orthogonal sum carrier is contained in its graph-glued overlattice. -/
theorem orthogonalSum_carrier_le_glueAlongDiscriminant :
    (L.orthogonalSum M).carrier ≤ (L.glueAlongDiscriminant M hL hM e).carrier := by
  rw [glueAlongDiscriminant, ofIsotropicSubgroup_carrier]
  exact ((L.orthogonalSum M).intermediateCarrierOfDiscriminantSubgroup _).2.1

/-- An arbitrary pair belongs to the glued carrier precisely when both coordinates are dual
vectors and their discriminant classes correspond. -/
@[simp low]
theorem mem_glueAlongDiscriminant_iff_exists (x : V × W) :
    x ∈ (L.glueAlongDiscriminant M hL hM e).carrier ↔
      ∃ (hx : x.1 ∈ L.dualCarrier) (hy : x.2 ∈ M.dualCarrier),
        e (Submodule.Quotient.mk (⟨x.1, hx⟩ : L.dualCarrier)) =
          Submodule.Quotient.mk (⟨x.2, hy⟩ : M.dualCarrier) := by
  constructor
  · intro hx
    have hd : x ∈ (L.orthogonalSum M).dualCarrier := by
      rw [glueAlongDiscriminant, ofIsotropicSubgroup_carrier] at hx
      exact ((L.orthogonalSum M).intermediateCarrierOfDiscriminantSubgroup _).2.2 hx
    obtain ⟨hx', hy'⟩ := (L.mem_dualCarrier_orthogonalSum M x).mp hd
    exact ⟨hx', hy', (L.mem_glueAlongDiscriminant_iff M hL hM e _ _).mp hx⟩
  · rintro ⟨hx, hy, h⟩
    exact (L.mem_glueAlongDiscriminant_iff M hL hM e _ _).mpr h

/-- The glued lattice intersects the first coordinate space in exactly `L`. -/
@[simp]
theorem mem_glueAlongDiscriminant_left_iff (x : V) :
    (x, 0) ∈ (L.glueAlongDiscriminant M hL hM e).carrier ↔ x ∈ L.carrier := by
  constructor
  · intro hx
    obtain ⟨hx', hy', h⟩ := (L.mem_glueAlongDiscriminant_iff_exists M hL hM e _).mp hx
    have hzero : (Submodule.Quotient.mk (⟨x, hx'⟩ : L.dualCarrier) : L.DiscriminantGroup) = 0 :=
      e.toAddEquiv.injective
        ((h.trans ((M.discriminantGroup_mk_eq_zero_iff _).mpr M.carrier.zero_mem)).trans
          (map_zero e).symm)
    exact (L.discriminantGroup_mk_eq_zero_iff _).mp hzero
  · intro hx
    apply L.orthogonalSum_carrier_le_glueAlongDiscriminant M hL hM e
    rw [orthogonalSum_carrier, Submodule.mem_prod]
    exact ⟨hx, M.carrier.zero_mem⟩

/-- The glued lattice intersects the second coordinate space in exactly `M`. -/
@[simp]
theorem mem_glueAlongDiscriminant_right_iff (y : W) :
    (0, y) ∈ (L.glueAlongDiscriminant M hL hM e).carrier ↔ y ∈ M.carrier := by
  constructor
  · intro hy
    obtain ⟨hx', hy', h⟩ := (L.mem_glueAlongDiscriminant_iff_exists M hL hM e _).mp hy
    apply (M.discriminantGroup_mk_eq_zero_iff (⟨y, hy'⟩ : M.dualCarrier)).mp
    exact h.symm.trans (congrArg e
      ((L.discriminantGroup_mk_eq_zero_iff _).mpr L.carrier.zero_mem)) |>.trans (map_zero e)
  · intro hy
    apply L.orthogonalSum_carrier_le_glueAlongDiscriminant M hL hM e
    rw [orthogonalSum_carrier, Submodule.mem_prod]
    exact ⟨L.carrier.zero_mem, hy⟩

/-- The first lattice's integral inclusion into the graph-glued overlattice. -/
noncomputable def glueLeft : L →ₗ[ℤ] L.glueAlongDiscriminant M hL hM e :=
  ((LinearMap.inl ℤ V W).comp L.carrier.subtype).codRestrict _
    (fun x ↦ (L.mem_glueAlongDiscriminant_left_iff M hL hM e x).mpr x.2)

/-- The second lattice's integral inclusion into the graph-glued overlattice. -/
noncomputable def glueRight : M →ₗ[ℤ] L.glueAlongDiscriminant M hL hM e :=
  ((LinearMap.inr ℤ V W).comp M.carrier.subtype).codRestrict _
    (fun y ↦ (L.mem_glueAlongDiscriminant_right_iff M hL hM e y).mpr y.2)

@[simp]
theorem coe_glueLeft_apply (x : L) :
    (L.glueLeft M hL hM e x : V × W) = ((x : V), 0) := (rfl)

@[simp]
theorem coe_glueRight_apply (y : M) :
    (L.glueRight M hL hM e y : V × W) = (0, (y : W)) := (rfl)

/-- The first inclusion preserves the integral bilinear form. -/
@[simp]
theorem integralForm_glueLeft (x y : L) :
    (L.glueAlongDiscriminant M hL hM e).integralForm
      (L.glueLeft M hL hM e x) (L.glueLeft M hL hM e y) = L.integralForm x y := by
  apply Int.cast_injective (α := ℚ)
  simp [glueAlongDiscriminant_form]

/-- The second inclusion preserves the integral bilinear form. -/
@[simp]
theorem integralForm_glueRight (x y : M) :
    (L.glueAlongDiscriminant M hL hM e).integralForm
      (L.glueRight M hL hM e x) (L.glueRight M hL hM e y) = M.integralForm x y := by
  apply Int.cast_injective (α := ℚ)
  simp [glueAlongDiscriminant_form]

/-- The two canonical inclusions have mutually orthogonal images. -/
@[simp]
theorem integralForm_glueLeft_glueRight (x : L) (y : M) :
    (L.glueAlongDiscriminant M hL hM e).integralForm
      (L.glueLeft M hL hM e x) (L.glueRight M hL hM e y) = 0 := by
  apply Int.cast_injective (α := ℚ)
  simp [glueAlongDiscriminant_form]

/-- The mixed integral pairing also vanishes with the second inclusion first. -/
@[simp]
theorem integralForm_glueRight_glueLeft (x : M) (y : L) :
    (L.glueAlongDiscriminant M hL hM e).integralForm
      (L.glueRight M hL hM e x) (L.glueLeft M hL hM e y) = 0 :=
  ((L.glueAlongDiscriminant M hL hM e).isSymm_integralForm.eq _ _).trans
    (L.integralForm_glueLeft_glueRight M hL hM e y x)

/-- The first coordinate inclusion is injective. -/
theorem glueLeft_injective : Function.Injective (L.glueLeft M hL hM e) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : L.glueAlongDiscriminant M hL hM e ↦ (z : V × W).1) h

/-- The second coordinate inclusion is injective. -/
theorem glueRight_injective : Function.Injective (L.glueRight M hL hM e) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : L.glueAlongDiscriminant M hL hM e ↦ (z : V × W).2) h

/-- The first lattice is the kernel of the second-coordinate projection on the glued carrier. -/
theorem range_glueLeft :
    LinearMap.range (L.glueLeft M hL hM e) =
      LinearMap.ker ((LinearMap.snd ℤ V W).comp
        (L.glueAlongDiscriminant M hL hM e).carrier.subtype) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearMap.snd_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    have hmem : x.1.1 ∈ L.carrier :=
      (L.mem_glueAlongDiscriminant_left_iff M hL hM e _).mp
        ((Prod.ext rfl hx.symm : (x.1.1, 0) = x.1).symm ▸ x.2)
    exact ⟨⟨x.1.1, hmem⟩, Subtype.ext (Prod.ext rfl hx.symm)⟩

/-- The second lattice is the kernel of the first-coordinate projection on the glued carrier. -/
theorem range_glueRight :
    LinearMap.range (L.glueRight M hL hM e) =
      LinearMap.ker ((LinearMap.fst ℤ V W).comp
        (L.glueAlongDiscriminant M hL hM e).carrier.subtype) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearMap.fst_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    have hmem : x.1.2 ∈ M.carrier :=
      (L.mem_glueAlongDiscriminant_right_iff M hL hM e _).mp
        ((Prod.ext hx.symm rfl : (0, x.1.2) = x.1).symm ▸ x.2)
    exact ⟨⟨x.1.2, hmem⟩, Subtype.ext (Prod.ext hx.symm rfl)⟩

/-- The first inclusion is primitive: its integral cokernel is torsion-free. -/
theorem isTorsionFree_quotient_range_glueLeft :
    Module.IsTorsionFree ℤ
      (L.glueAlongDiscriminant M hL hM e ⧸ LinearMap.range (L.glueLeft M hL hM e)) := by
  rw [range_glueLeft]
  let f := (LinearMap.snd ℤ V W).comp (L.glueAlongDiscriminant M hL hM e).carrier.subtype
  let : Module.IsTorsionFree ℤ W :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ W
  exact f.quotKerEquivRange.injective.moduleIsTorsionFree _ (map_smul _)

/-- The second inclusion is primitive: its integral cokernel is torsion-free. -/
theorem isTorsionFree_quotient_range_glueRight :
    Module.IsTorsionFree ℤ
      (L.glueAlongDiscriminant M hL hM e ⧸ LinearMap.range (L.glueRight M hL hM e)) := by
  rw [range_glueRight]
  let f := (LinearMap.fst ℤ V W).comp (L.glueAlongDiscriminant M hL hM e).carrier.subtype
  let : Module.IsTorsionFree ℤ V :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ V
  exact f.quotKerEquivRange.injective.moduleIsTorsionFree _ (map_smul _)

/-- The glued lattice has the sum of the two original signatures. -/
theorem signature_glueAlongDiscriminant :
    (L.glueAlongDiscriminant M hL hM e).signature =
      (L.sigPos + M.sigPos, L.sigNull + M.sigNull, L.sigNeg + M.sigNeg) := by
  rw [← signature_orthogonalSum]
  have hr : (L.glueAlongDiscriminant M hL hM e).radical = (L.orthogonalSum M).radical := by
    ext x
    simp only [mem_radical_iff, glueAlongDiscriminant_form]
  have hn : (L.glueAlongDiscriminant M hL hM e).sigNull = (L.orthogonalSum M).sigNull :=
    congrArg (fun S : Submodule ℚ (V × W) ↦ Module.finrank ℚ S) hr
  simp only [signature, hn, sigPos, sigNeg, glueAlongDiscriminant_form]

end TauCeti.IntegralLattice
