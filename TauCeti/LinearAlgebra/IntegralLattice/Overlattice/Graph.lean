/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Graph
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual

/-!
# Gluing lattices with opposite discriminant forms

An isometry between the discriminant form of an even lattice `L` and the negative
discriminant form of `M` determines an even unimodular overlattice of `L ⊥ M`.
Its vectors are precisely the pairs in the two dual carriers whose discriminant
classes correspond under the isometry. In particular, its intersection with either
coordinate space is the original lattice, the condition needed for primitive embeddings.

The construction uses the existing discriminant-product isometry and isotropic-subgroup
gluing correspondence. The ambient rational form is the orthogonal sum form throughout.

Conversely, every even unimodular lattice for the orthogonal sum form which contains `L ⊥ M`
and meets the two coordinate spaces in exactly `L` and `M` arises by this construction. Its
subgroup of the discriminant group of `L ⊥ M` is a Lagrangian meeting both factors trivially,
hence the graph of an isometry of opposite discriminant forms. This is the orthogonal-sum model of
the statement that a nondegenerate primitive sublattice of an even unimodular lattice and its
orthogonal complement have opposite discriminant forms.

Finally, isometries extend across the gluing exactly when their discriminant actions are
compatible with it: integral isometries `g : L ≃ L'` and `h : M ≃ M'` extend, necessarily uniquely
and by `g × h`, from the lattice glued along `e` to the lattice glued along `e'` if and only if
`e' ∘ g_A = h_A ∘ e`, where `g_A` and `h_A` are the induced maps of discriminant groups
(`TauCeti.IntegralLattice.Isometry.discriminantGroupEquiv`). Conversely, an isometry of glued
lattices preserving both coordinate spaces restricts to such a compatible pair and is its
extension. This is the criterion used to decide which pairs of isometries of a primitive
sublattice and its orthogonal complement come from an isometry of the ambient even unimodular
lattice.

## Main declarations

* `TauCeti.IntegralLattice.glueAlongDiscriminant`: the lattice glued along a discriminant
  anti-isometry.
* `TauCeti.IntegralLattice.exists_eq_glueAlongDiscriminant`: every even unimodular overlattice
  meeting both coordinate spaces exactly in `L` and `M` is such a gluing.
* `TauCeti.IntegralLattice.Isometry.mapsTo_prodMap_glueAlongDiscriminant_iff`: `g × h` preserves
  the gluing exactly when the discriminant actions are compatible.
* `TauCeti.IntegralLattice.Isometry.glueAlongDiscriminant`: the extension of a compatible pair.
* `TauCeti.IntegralLattice.Isometry.existsUnique_glueAlongDiscriminant_iff`: the extension
  criterion.
* `TauCeti.IntegralLattice.Isometry.restrictGlueLeft`,
  `TauCeti.IntegralLattice.Isometry.restrictGlueRight` and
  `TauCeti.IntegralLattice.Isometry.glueAlongDiscriminant_restrictGlueLeft_restrictGlueRight`:
  restriction of an isometry preserving both coordinate spaces, inverse to extension.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.6.1 and §1.5.
* D. Huybrechts, *Lectures on K3 surfaces*, Chapter 14, §2.2.
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
    (x.val, y.val) ∈ (L.glueAlongDiscriminant M hL hM e).carrier ↔
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
  exact ((L.orthogonalSum M).intermediateCarrierOfDiscriminantSubgroup _).property.1

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
      exact ((L.orthogonalSum M).intermediateCarrierOfDiscriminantSubgroup _).property.2 hx
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
    (fun x ↦ (L.mem_glueAlongDiscriminant_left_iff M hL hM e x).mpr x.property)

/-- The second lattice's integral inclusion into the graph-glued overlattice. -/
noncomputable def glueRight : M →ₗ[ℤ] L.glueAlongDiscriminant M hL hM e :=
  ((LinearMap.inr ℤ V W).comp M.carrier.subtype).codRestrict _
    (fun y ↦ (L.mem_glueAlongDiscriminant_right_iff M hL hM e y).mpr y.property)

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
    have hmem : x.val.1 ∈ L.carrier :=
      (L.mem_glueAlongDiscriminant_left_iff M hL hM e _).mp
        ((Prod.ext rfl hx.symm : (x.val.1, 0) = x.val).symm ▸ x.property)
    exact ⟨⟨x.val.1, hmem⟩, Subtype.ext (Prod.ext rfl hx.symm)⟩

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
    have hmem : x.val.2 ∈ M.carrier :=
      (L.mem_glueAlongDiscriminant_right_iff M hL hM e _).mp
        ((Prod.ext hx.symm rfl : (0, x.val.2) = x.val).symm ▸ x.property)
    exact ⟨⟨x.val.2, hmem⟩, Subtype.ext (Prod.ext hx.symm rfl)⟩

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
      (L.sigPos + M.sigPos, L.sigNull + M.sigNull, L.sigNeg + M.sigNeg) :=
  (signature_eq_of_equivalent (glueAlongDiscriminant_form L M hL hM e ▸ .refl _)).trans
    (signature_orthogonalSum L M)

/-! ## Even unimodular overlattices are graph gluings -/

omit [L.IsNondegenerate] [M.IsNondegenerate] in
/-- A pair of dual vectors has its pair of classes in the image of `N / (L ⊥ M)` exactly when it
lies in `N`. -/
private theorem mk_mem_map_discriminantSubgroup_iff (N : (L.orthogonalSum M).IntermediateCarrier)
    (x : L.dualCarrier) (y : M.dualCarrier) :
    ((Submodule.Quotient.mk x, Submodule.Quotient.mk y) :
        L.DiscriminantGroup × M.DiscriminantGroup) ∈
        ((L.orthogonalSum M).discriminantSubgroup N).map
          (L.discriminantGroupOrthogonalSumEquiv M).toAddEquiv.toAddMonoidHom ↔
      ((x : V), (y : W)) ∈ N.val := by
  set z := (L.orthogonalSumDualCarrierEquiv M).symm (x, y)
  have hz : (L.discriminantGroupOrthogonalSumEquiv M).toAddEquiv.toAddMonoidHom
      (Submodule.Quotient.mk z) = (Submodule.Quotient.mk x, Submodule.Quotient.mk y) := by
    simp [z]
  rw [← hz, AddSubgroup.mem_map_iff_mem (AddEquiv.injective _),
    mk_mem_discriminantSubgroup_iff, coe_orthogonalSumDualCarrierEquiv_symm_apply]

/-- **Even unimodular overlattices of `L ⊥ M` are graph gluings.** Let `N` be an even unimodular
lattice for the orthogonal sum form which contains `L ⊥ M` and meets the two coordinate spaces in
exactly `L` and `M`. Then `N` is obtained by gluing along an isometry from the discriminant form of
`L` to the negative of that of `M`. This is the converse of the construction
`TauCeti.IntegralLattice.glueAlongDiscriminant`, and the orthogonal-sum model of the statement
that a nondegenerate primitive sublattice of an even unimodular lattice and its orthogonal
complement have opposite discriminant forms. -/
theorem exists_eq_glueAlongDiscriminant (N : IntegralLattice (V × W))
    (hform : N.form = (L.orthogonalSum M).form)
    (hle : (L.orthogonalSum M).carrier ≤ N.carrier) (hNe : N.IsEven) (hNu : N.IsUnimodular)
    (hleft : ∀ x : V, (x, 0) ∈ N.carrier → x ∈ L.carrier)
    (hright : ∀ y : W, (0, y) ∈ N.carrier → y ∈ M.carrier) :
    ∃ f : FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
      (M.discriminantQuadraticModule hM).neg, N = L.glueAlongDiscriminant M hL hM f := by
  set S := L.orthogonalSum M
  have hS : S.IsEven := (L.isEven_orthogonalSum_iff M).mpr ⟨hL, hM⟩
  -- `N` is an intermediate carrier of `L ⊥ M`, even and with unimodular underlying lattice.
  set P := N.toIntermediateCarrier hform hle
  have hPc : P.val = N.carrier := N.coe_toIntermediateCarrier hform hle
  have hdual : N.carrier ≤ S.dualCarrier := hPc ▸ P.property.2
  -- Its subgroup of the discriminant group is a quadratic Lagrangian.
  have hlag : (S.discriminantQuadraticModule hS).IsLagrangian (S.discriminantSubgroup P) :=
    (S.isLagrangian_discriminantSubgroup_toIntermediateCarrier_iff hS N hform hle).mpr ⟨hNe, hNu⟩
  have hlag' := ((L.discriminantQuadraticIsometryOrthogonalSum M hL hM).isLagrangian_map_iff
    _ (S.discriminantSubgroup P)).mpr hlag
  rw [discriminantQuadraticIsometryOrthogonalSum_toAddEquiv] at hlag'
  have hmem := L.mk_mem_map_discriminantSubgroup_iff M P
  rw [hPc] at hmem
  -- The transported subgroup meets both factors trivially, so it is the graph of an isometry.
  obtain ⟨f, hf⟩ := FiniteQuadraticModule.exists_isometry_neg_mem_iff_of_isLagrangian _ _ hlag'
    (fun a ha ↦ by
      induction a using Submodule.Quotient.induction_on with
      | _ x =>
        exact (L.discriminantGroup_mk_eq_zero_iff x).mpr (hleft _ ((hmem x 0).mp ha)))
    (fun b hb ↦ by
      induction b using Submodule.Quotient.induction_on with
      | _ y =>
        exact (M.discriminantGroup_mk_eq_zero_iff y).mpr (hright _ ((hmem 0 y).mp hb)))
  refine ⟨f, IntegralLattice.ext ?_ (by rw [glueAlongDiscriminant_form, hform])⟩
  ext z
  rw [mem_glueAlongDiscriminant_iff_exists]
  constructor
  · intro hz
    obtain ⟨hx, hy⟩ := (L.mem_dualCarrier_orthogonalSum M z).mp (hdual hz)
    exact ⟨hx, hy, (hf _ _).mp ((hmem ⟨z.1, hx⟩ ⟨z.2, hy⟩).mpr hz)⟩
  · rintro ⟨hx, hy, h⟩
    exact (hmem ⟨z.1, hx⟩ ⟨z.2, hy⟩).mp ((hf _ _).mpr h)

/-- **The gluing is injective in the isometry.** An even unimodular overlattice of `L ⊥ M` obtained
by gluing determines the isometry of discriminant forms used to build it. Together with
`TauCeti.IntegralLattice.exists_eq_glueAlongDiscriminant` this is the uniqueness half of
Nikulin's correspondence. -/
theorem glueAlongDiscriminant_injective :
    Function.Injective (L.glueAlongDiscriminant M hL hM) := by
  intro e e' h
  apply DFunLike.coe_injective
  funext a
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk x))
    have hmem := (L.mem_glueAlongDiscriminant_iff M hL hM e x y).mpr hy.symm
    rw [h] at hmem
    exact (((L.mem_glueAlongDiscriminant_iff M hL hM e' x y).mp hmem).trans hy).symm

/-- Two gluings of `L ⊥ M` are equal if and only if they use the same isometry of discriminant
forms. -/
@[simp]
theorem glueAlongDiscriminant_inj
    {e e' : FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
      (M.discriminantQuadraticModule hM).neg} :
    L.glueAlongDiscriminant M hL hM e = L.glueAlongDiscriminant M hL hM e' ↔ e = e' :=
  (L.glueAlongDiscriminant_injective M hL hM).eq_iff

/-! ## Extending isometries across the gluing

A pair of integral isometries `g : L ≃ L'` and `h : M ≃ M'` acts on the ambient product by
`g × h`. This map carries the lattice glued along `e` onto the lattice glued along `e'` exactly
when the induced discriminant actions `g_A` and `h_A` intertwine the two gluing isometries,
`e' ∘ g_A = h_A ∘ e`. -/

section Extension

variable {L M hL hM e}
variable {V' W' : Type*} [AddCommGroup V'] [Module ℚ V'] [AddCommGroup W'] [Module ℚ W']
variable {L' : IntegralLattice V'} {M' : IntegralLattice W'} [L'.IsNondegenerate]
  [M'.IsNondegenerate] {hL' : L'.IsEven} {hM' : M'.IsEven}
  {e' : FiniteQuadraticModule.Isometry (L'.discriminantQuadraticModule hL')
    (M'.discriminantQuadraticModule hM').neg}

namespace Isometry

/-- **The product map preserves the gluing exactly when the discriminant actions intertwine the
gluing isometries.** For integral isometries `g : L ≃ L'` and `h : M ≃ M'`, the ambient map
`g × h` sends the lattice glued along `e` into the lattice glued along `e'` if and only if
`e' ∘ g_A = h_A ∘ e` on the discriminant group of `L`. -/
theorem mapsTo_prodMap_glueAlongDiscriminant_iff (g : Isometry L L') (h : Isometry M M') :
    Set.MapsTo (Prod.map g h) (L.glueAlongDiscriminant M hL hM e).carrier
        (L'.glueAlongDiscriminant M' hL' hM' e').carrier ↔
      ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a) := by
  constructor
  · intro hmaps a
    induction a using Submodule.Quotient.induction_on with
    | _ x =>
      -- Complete the class of `x` to a glued vector `(x, y)` and read off the image's membership.
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk x))
      have hxy := hmaps ((L.mem_glueAlongDiscriminant_iff M hL hM e x y).mpr hy.symm)
      rw [discriminantGroupEquiv_mk, ← hy, discriminantGroupEquiv_mk]
      apply (L'.mem_glueAlongDiscriminant_iff M' hL' hM' e' (g.dualCarrierEquiv x)
        (h.dualCarrierEquiv y)).mp
      simpa only [coe_dualCarrierEquiv_apply, Prod.map_apply, SetLike.mem_coe] using hxy
  · rintro hc ⟨v, w⟩ hp
    obtain ⟨hv, hw, hvw⟩ := (L.mem_glueAlongDiscriminant_iff_exists M hL hM e _).mp hp
    have hmem := (L'.mem_glueAlongDiscriminant_iff M' hL' hM' e' (g.dualCarrierEquiv ⟨v, hv⟩)
      (h.dualCarrierEquiv ⟨w, hw⟩)).mpr (by
        rw [← discriminantGroupEquiv_mk, hc, hvw, discriminantGroupEquiv_mk])
    simpa only [coe_dualCarrierEquiv_apply, Prod.map_apply, SetLike.mem_coe] using hmem

/-- Discriminant actions intertwining `e` with `e'` have inverses intertwining `e'` with `e`. -/
theorem symm_discriminantGroupEquiv_intertwine {g : Isometry L L'} {h : Isometry M M'}
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a))
    (b : L'.DiscriminantGroup) :
    e (g.symm.discriminantGroupEquiv b) = h.symm.discriminantGroupEquiv (e' b) := by
  rw [discriminantGroupEquiv_symm, discriminantGroupEquiv_symm]
  apply h.discriminantGroupEquiv.injective
  exact ((hc _).symm.trans (congrArg e' (g.discriminantGroupEquiv.apply_symm_apply b))).trans
    (h.discriminantGroupEquiv.apply_symm_apply _).symm

/-- **Extension of a compatible pair of isometries across the gluing.** Integral isometries
`g : L ≃ L'` and `h : M ≃ M'` whose discriminant actions intertwine the gluing isometries,
`e' ∘ g_A = h_A ∘ e`, extend to the isometry `g × h` from the lattice glued along `e` to the
lattice glued along `e'`. -/
noncomputable def glueAlongDiscriminant (g : Isometry L L') (h : Isometry M M')
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a)) :
    Isometry (L.glueAlongDiscriminant M hL hM e) (L'.glueAlongDiscriminant M' hL' hM' e') where
  toLinearEquiv := (g.orthogonalSum h).toLinearEquiv
  map_app' p q := by
    rw [glueAlongDiscriminant_form, glueAlongDiscriminant_form]
    exact (g.orthogonalSum h).map_app p q
  map_carrier := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact (orthogonalSum_apply g h p).symm ▸
        (g.mapsTo_prodMap_glueAlongDiscriminant_iff h).mpr hc hp
    · intro p hp
      refine Submodule.mem_map.mpr ⟨Prod.map g.symm h.symm p,
        (g.symm.mapsTo_prodMap_glueAlongDiscriminant_iff h.symm).mpr
          (symm_discriminantGroupEquiv_intertwine hc) hp, ?_⟩
      simp

/-- The extended isometry acts by `g` and `h` on the two coordinates. -/
@[simp]
theorem glueAlongDiscriminant_apply (g : Isometry L L') (h : Isometry M M')
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a)) (p : V × W) :
    g.glueAlongDiscriminant h hc p = (g p.1, h p.2) :=
  g.orthogonalSum_apply h p

/-- The extension of the inverse pair is the inverse of the extension. -/
@[simp]
theorem glueAlongDiscriminant_symm (g : Isometry L L') (h : Isometry M M')
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a)) :
    (g.glueAlongDiscriminant h hc).symm =
      g.symm.glueAlongDiscriminant h.symm (symm_discriminantGroupEquiv_intertwine hc) := by
  ext p : 1
  apply (g.glueAlongDiscriminant h hc).injective
  simp

/-- The extension of the pair of identities is the identity of the glued lattice. -/
@[simp]
theorem glueAlongDiscriminant_refl
    (hc : ∀ a, e ((refl L).discriminantGroupEquiv a) = (refl M).discriminantGroupEquiv (e a)) :
    (refl L).glueAlongDiscriminant (refl M) hc = refl (L.glueAlongDiscriminant M hL hM e) := by
  ext p : 1
  simp

/-- Discriminant actions intertwining `e` with `e'` and `e'` with `e''` compose to actions
intertwining `e` with `e''`. -/
theorem trans_discriminantGroupEquiv_intertwine {V'' W'' : Type*} [AddCommGroup V'']
    [Module ℚ V''] [AddCommGroup W''] [Module ℚ W''] {L'' : IntegralLattice V''}
    {M'' : IntegralLattice W''} [L''.IsNondegenerate] [M''.IsNondegenerate] {hL'' : L''.IsEven}
    {hM'' : M''.IsEven}
    {e'' : FiniteQuadraticModule.Isometry (L''.discriminantQuadraticModule hL'')
      (M''.discriminantQuadraticModule hM'').neg}
    {g : Isometry L L'} {h : Isometry M M'} {g' : Isometry L' L''} {h' : Isometry M' M''}
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a))
    (hc' : ∀ a, e'' (g'.discriminantGroupEquiv a) = h'.discriminantGroupEquiv (e' a))
    (a : L.DiscriminantGroup) :
    e'' ((g.trans g').discriminantGroupEquiv a) = (h.trans h').discriminantGroupEquiv (e a) := by
  rw [discriminantGroupEquiv_trans, discriminantGroupEquiv_trans]
  exact (hc' _).trans (congrArg h'.discriminantGroupEquiv (hc a))

/-- The extension of a composite pair is the composite of the extensions. -/
@[simp]
theorem glueAlongDiscriminant_trans {V'' W'' : Type*} [AddCommGroup V''] [Module ℚ V'']
    [AddCommGroup W''] [Module ℚ W''] {L'' : IntegralLattice V''} {M'' : IntegralLattice W''}
    [L''.IsNondegenerate] [M''.IsNondegenerate] {hL'' : L''.IsEven} {hM'' : M''.IsEven}
    {e'' : FiniteQuadraticModule.Isometry (L''.discriminantQuadraticModule hL'')
      (M''.discriminantQuadraticModule hM'').neg}
    (g : Isometry L L') (h : Isometry M M') (g' : Isometry L' L'') (h' : Isometry M' M'')
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a))
    (hc' : ∀ a, e'' (g'.discriminantGroupEquiv a) = h'.discriminantGroupEquiv (e' a)) :
    (g.glueAlongDiscriminant h hc).trans (g'.glueAlongDiscriminant h' hc') =
      (g.trans g').glueAlongDiscriminant (h.trans h')
        (trans_discriminantGroupEquiv_intertwine hc hc') := by
  ext p : 1
  simp

/-- The extension restricts to `g` on the first glued summand. -/
@[simp]
theorem glueAlongDiscriminant_carrierEquiv_glueLeft (g : Isometry L L') (h : Isometry M M')
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a)) (x : L) :
    (g.glueAlongDiscriminant h hc).carrierEquiv (L.glueLeft M hL hM e x) =
      L'.glueLeft M' hL' hM' e' (g.carrierEquiv x) := by
  apply Subtype.ext
  simp

/-- The extension restricts to `h` on the second glued summand. -/
@[simp]
theorem glueAlongDiscriminant_carrierEquiv_glueRight (g : Isometry L L') (h : Isometry M M')
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a)) (y : M) :
    (g.glueAlongDiscriminant h hc).carrierEquiv (L.glueRight M hL hM e y) =
      L'.glueRight M' hL' hM' e' (h.carrierEquiv y) := by
  apply Subtype.ext
  simp

/-- **Extension criterion for isometries of glued lattices.** Let `L` and `M` be even
nondegenerate lattices glued along an isometry `e` from the discriminant form of `L` to the
negative of that of `M`, and similarly `L'` and `M'` along `e'`. A pair of integral isometries
`g : L ≃ L'` and `h : M ≃ M'` extends to an integral isometry of the glued lattices, necessarily
unique, exactly when the induced discriminant actions satisfy `e' ∘ g_A = h_A ∘ e`. Taking
`L' = L`, `M' = M` and `e' = e`, a pair `g ∈ O(L)`, `h ∈ O(M)` extends to the glued lattice
exactly when `e ∘ g_A = h_A ∘ e`. -/
theorem existsUnique_glueAlongDiscriminant_iff (g : Isometry L L') (h : Isometry M M') :
    (∃! F : Isometry (L.glueAlongDiscriminant M hL hM e) (L'.glueAlongDiscriminant M' hL' hM' e'),
        ∀ v w, F (v, w) = (g v, h w)) ↔
      ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a) := by
  constructor
  · rintro ⟨F, hF, -⟩
    apply (g.mapsTo_prodMap_glueAlongDiscriminant_iff h).mp
    rintro ⟨v, w⟩ hp
    rw [Prod.map_apply, ← hF]
    exact (F.apply_mem_carrier_iff _).mpr hp
  · intro hc
    refine ⟨g.glueAlongDiscriminant h hc, fun v w ↦ glueAlongDiscriminant_apply g h hc (v, w),
      fun F hF ↦ Isometry.ext fun p ↦
        (hF p.1 p.2).trans (glueAlongDiscriminant_apply g h hc p).symm⟩

/-! ### Restriction to the summands

An isometry of glued lattices which preserves both coordinate spaces, sending `(v, 0)` into the
first and `(0, w)` into the second, restricts to isometries of the two summands, and is the
extension of that compatible pair. -/

section Restrict

variable (F : Isometry (L.glueAlongDiscriminant M hL hM e) (L'.glueAlongDiscriminant M' hL' hM' e'))
  (hF : ∀ v, (F (v, 0)).2 = 0) (hF' : ∀ w, (F (0, w)).1 = 0)

include hF hF' in
/-- An isometry preserving both coordinate spaces acts diagonally. -/
private theorem apply_eq_of_preserves (p : V × W) : F p = ((F (p.1, 0)).1, (F (0, p.2)).2) := by
  conv_lhs => rw [← Prod.fst_add_snd p, map_add]
  ext <;> simp [hF, hF']

include hF hF' in
private theorem bijective_fst_comp_inl :
    Function.Bijective fun v ↦ (F (v, 0)).1 := by
  constructor
  · intro v u h
    have huv : F (v, 0) = F (u, 0) := Prod.ext h ((hF v).trans (hF u).symm)
    exact congrArg Prod.fst (F.injective huv)
  · intro v'
    refine ⟨(F.symm (v', 0)).1, ?_⟩
    have h := congrArg Prod.fst (F.apply_eq_of_preserves hF hF' (F.symm (v', 0)))
    rw [apply_symm_apply] at h
    exact h.symm

include hF hF' in
private theorem bijective_snd_comp_inr :
    Function.Bijective fun w ↦ (F (0, w)).2 := by
  constructor
  · intro w u h
    have huw : F (0, w) = F (0, u) := Prod.ext ((hF' w).trans (hF' u).symm) h
    exact congrArg Prod.snd (F.injective huw)
  · intro w'
    refine ⟨(F.symm (0, w')).2, ?_⟩
    have h := congrArg Prod.snd (F.apply_eq_of_preserves hF hF' (F.symm (0, w')))
    rw [apply_symm_apply] at h
    exact h.symm

include hF in
private theorem apply_inl_eq (v : V) : F (v, 0) = ((F (v, 0)).1, 0) :=
  Prod.ext rfl (hF v)

include hF' in
private theorem apply_inr_eq (w : W) : F (0, w) = (0, (F (0, w)).2) :=
  Prod.ext (hF' w) rfl

include hF in
private theorem fst_apply_mem_carrier_iff (x : V) : (F (x, 0)).1 ∈ L'.carrier ↔ x ∈ L.carrier := by
  rw [← L'.mem_glueAlongDiscriminant_left_iff M' hL' hM' e', ← F.apply_inl_eq hF x,
    apply_mem_carrier_iff, mem_glueAlongDiscriminant_left_iff]

include hF' in
private theorem snd_apply_mem_carrier_iff (y : W) : (F (0, y)).2 ∈ M'.carrier ↔ y ∈ M.carrier := by
  rw [← L'.mem_glueAlongDiscriminant_right_iff M' hL' hM' e', ← F.apply_inr_eq hF' y,
    apply_mem_carrier_iff, mem_glueAlongDiscriminant_right_iff]

/-- **Restriction to the first summand.** An isometry of glued lattices preserving both
coordinate spaces restricts to an isometry `L ≃ L'`, acting by `v ↦ (F (v, 0)).1`. -/
noncomputable def restrictGlueLeft : Isometry L L' where
  toLinearEquiv := LinearEquiv.ofBijective
    ((LinearMap.fst ℚ V' W').comp (F.toLinearEquiv.toLinearMap.comp
      (LinearMap.inl ℚ V W))) (F.bijective_fst_comp_inl hF hF')
  map_app' v u := by
    have h := F.map_app (v, 0) (u, 0)
    rw [F.apply_inl_eq hF v, F.apply_inl_eq hF u] at h
    simp only [glueAlongDiscriminant_form, orthogonalSum_form, LinearMap.BilinForm.prod_apply,
      map_zero, add_zero] at h
    exact h
  map_carrier := by
    ext x'
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (F.fst_apply_mem_carrier_iff hF x).mpr hx
    · intro hx'
      obtain ⟨x, rfl⟩ := (F.bijective_fst_comp_inl hF hF').2 x'
      exact ⟨x, (F.fst_apply_mem_carrier_iff hF x).mp hx', rfl⟩

/-- **Restriction to the second summand.** An isometry of glued lattices preserving both
coordinate spaces restricts to an isometry `M ≃ M'`, acting by `w ↦ (F (0, w)).2`. -/
noncomputable def restrictGlueRight : Isometry M M' where
  toLinearEquiv := LinearEquiv.ofBijective
    ((LinearMap.snd ℚ V' W').comp (F.toLinearEquiv.toLinearMap.comp
      (LinearMap.inr ℚ V W))) (F.bijective_snd_comp_inr hF hF')
  map_app' w u := by
    have h := F.map_app (0, w) (0, u)
    rw [F.apply_inr_eq hF' w, F.apply_inr_eq hF' u] at h
    simp only [glueAlongDiscriminant_form, orthogonalSum_form, LinearMap.BilinForm.prod_apply,
      map_zero, zero_add] at h
    exact h
  map_carrier := by
    ext x'
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (F.snd_apply_mem_carrier_iff hF' x).mpr hx
    · intro hx'
      obtain ⟨x, rfl⟩ := (F.bijective_snd_comp_inr hF hF').2 x'
      exact ⟨x, (F.snd_apply_mem_carrier_iff hF' x).mp hx', rfl⟩

/-- The first restriction acts by the first coordinate of `F` on the first coordinate space. -/
@[simp]
theorem restrictGlueLeft_apply (v : V) : F.restrictGlueLeft hF hF' v = (F (v, 0)).1 :=
  (rfl)

/-- The second restriction acts by the second coordinate of `F` on the second coordinate
space. -/
@[simp]
theorem restrictGlueRight_apply (w : W) : F.restrictGlueRight hF hF' w = (F (0, w)).2 :=
  (rfl)

/-- The restrictions of an isometry preserving both coordinate spaces intertwine the gluing
isometries. -/
theorem restrictGlue_discriminantGroupEquiv_intertwine (a : L.DiscriminantGroup) :
    e' ((F.restrictGlueLeft hF hF').discriminantGroupEquiv a) =
      (F.restrictGlueRight hF hF').discriminantGroupEquiv (e a) := by
  refine ((F.restrictGlueLeft hF hF').mapsTo_prodMap_glueAlongDiscriminant_iff
    (F.restrictGlueRight hF hF')).mp ?_ a
  intro p hp
  -- On the ambient product, the pair of restrictions acts as `F` itself.
  have hmap : Prod.map (F.restrictGlueLeft hF hF') (F.restrictGlueRight hF hF') p = F p :=
    (F.apply_eq_of_preserves hF hF' p).symm
  rw [hmap]
  exact (F.apply_mem_carrier_iff _).mpr hp

/-- **Gluing inverts restriction.** An isometry of glued lattices preserving both coordinate
spaces is the extension of its two restrictions. -/
theorem glueAlongDiscriminant_restrictGlueLeft_restrictGlueRight :
    (F.restrictGlueLeft hF hF').glueAlongDiscriminant (F.restrictGlueRight hF hF')
      (F.restrictGlue_discriminantGroupEquiv_intertwine hF hF') = F := by
  ext p : 1
  rw [glueAlongDiscriminant_apply, F.apply_eq_of_preserves hF hF' p, restrictGlueLeft_apply,
    restrictGlueRight_apply]

end Restrict

/-- **Restriction inverts gluing**, on the first summand. -/
@[simp]
theorem restrictGlueLeft_glueAlongDiscriminant (g : Isometry L L') (h : Isometry M M')
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a))
    (hF : ∀ v, (g.glueAlongDiscriminant h hc (v, 0)).2 = 0)
    (hF' : ∀ w, (g.glueAlongDiscriminant h hc (0, w)).1 = 0) :
    (g.glueAlongDiscriminant h hc).restrictGlueLeft hF hF' = g := by
  ext v
  simp

/-- **Restriction inverts gluing**, on the second summand. -/
@[simp]
theorem restrictGlueRight_glueAlongDiscriminant (g : Isometry L L') (h : Isometry M M')
    (hc : ∀ a, e' (g.discriminantGroupEquiv a) = h.discriminantGroupEquiv (e a))
    (hF : ∀ v, (g.glueAlongDiscriminant h hc (v, 0)).2 = 0)
    (hF' : ∀ w, (g.glueAlongDiscriminant h hc (0, w)).1 = 0) :
    (g.glueAlongDiscriminant h hc).restrictGlueRight hF hF' = h := by
  ext w
  simp

end Isometry

end Extension

end TauCeti.IntegralLattice
