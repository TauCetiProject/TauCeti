/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.CartanMap
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Loewy
import Mathlib.CategoryTheory.Preadditive.Schur

/-!
# The graded socle of a zigzag vertex projective

For a finite simple graph without isolated vertices, the socle of the vertex projective
`P_i = Z e_i` is its second radical power. Its grading is the restriction of the path-length
grading of `P_i`, so the volume vector lies in degree two. Right multiplication by that vector
induces an isomorphism `S_i{2} ≅ soc P_i`, where `S_i` is the existing graded simple head.
This identifies the internal shift in the head–socle comparison, including in characteristic two.

These modules belong to the zigzag relation quotient. The assumption of no isolated vertices
ensures that it has the ordinary zigzag convention on every component.

## References

* Huerfano–Khovanov, *A category for the adjoint representation*, Section 3.
* Ehrig–Tubbenhauer, *Algebraic properties of zigzag algebras*, equation (2-1) and
  Proposition 2.8.
-/

public section

namespace TauCeti

open CategoryTheory _root_.DirectSum

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (hns : ∀ i : V, ∃ j, G.Adj i j)

local notation "Z" => nonisolatedZigzagQuotient k G

/-- The volume vector of a vertex projective is homogeneous of degree two. -/
theorem zigzagProjectiveVolume_mem_grade_two (i : V) :
    zigzagProjectiveVolume k G i ∈ (zigzagGradedProjective k G i).grading.piece 2 := by
  rw [zigzagGradedProjective_piece, mem_zigzagProjectiveGrade_iff,
    coe_zigzagProjectiveVolume]
  have h2 : zigzagIntegerGrade k G (2 : ℤ) = zigzagGrade k G 2 :=
    zigzagIntegerGrade_ofNat k G 2
  rw [h2, zigzagGrade_two_eq_span_range_zigzagVolume]
  exact Submodule.subset_span (Set.mem_range_self i)

include hns in
/-- The intersection `Z e_i ∩ J²` is a homogeneous left ideal. -/
theorem isHomogeneous_zigzagProjectiveSocleIdeal [GradedAlgebra (zigzagIntegerGrade k G)] (i : V) :
    (zigzagProjective k G i ⊓ Ring.jacobson Z ^ 2).IsHomogeneous
      (zigzagIntegerGrade k G) := by
  have h2 : (Ring.jacobson Z ^ 2).restrictScalars k = zigzagIntegerGrade k G 2 := by
    rw [restrictScalars_jacobson_sq_nonisolatedZigzagQuotient_eq_zigzagVolumeSpan hns]
    have hgrade : zigzagIntegerGrade k G (2 : ℤ) = zigzagGrade k G 2 :=
      zigzagIntegerGrade_ofNat k G 2
    rw [hgrade, zigzagGrade_two_eq_span_range_zigzagVolume,
      zigzagVolumeSpan_eq_span]
  intro p x hx
  refine ⟨isHomogeneous_zigzagProjective k G i p hx.1, ?_⟩
  have hx2 : x ∈ zigzagIntegerGrade k G 2 := h2 ▸ hx.2
  by_cases hp : (2 : ℤ) = p
  · subst p
    rw [decompose_of_mem_same (zigzagIntegerGrade k G) hx2]
    exact hx.2
  · rw [decompose_of_mem_ne (zigzagIntegerGrade k G) hx2 hp]
    exact Submodule.zero_mem _

/-- The graded socle of `P_i`, realized inside the algebra as `Z e_i ∩ J²`, with the
restricted path-length grading. -/
noncomputable abbrev zigzagGradedProjectiveSocle (i : V) :
    GradedModuleCat.{max u w} (zigzagIntegerGrade k G) :=
  let _ := zigzagIntegerGradedAlgebra k G
  GradedModuleCat.ofIdeal (zigzagIntegerGrade k G)
    (zigzagProjective k G i ⊓ Ring.jacobson Z ^ 2)
    (isHomogeneous_zigzagProjectiveSocleIdeal k G hns i)

/-- An element of the graded socle has degree `p` exactly when its ambient algebra element does. -/
theorem mem_zigzagGradedProjectiveSocle_piece_iff (i : V) (p : ℤ)
    (x : zigzagGradedProjectiveSocle k G hns i) :
    x ∈ (zigzagGradedProjectiveSocle k G hns i).grading.piece p ↔
      (x : Z) ∈ zigzagIntegerGrade k G p := by
  let _ := zigzagIntegerGradedAlgebra k G
  exact GradedModuleCat.mem_ofIdeal_piece_iff
    (isHomogeneous_zigzagProjectiveSocleIdeal k G hns i)

include hns in
/-- The underlying ideal of the graded socle pulls back to the ordinary projective socle. -/
theorem socle_zigzagProjective_eq_comap (i : V) :
    socle Z (zigzagProjective k G i) =
      Submodule.comap (zigzagProjective k G i).subtype
        (zigzagProjective k G i ⊓ Ring.jacobson Z ^ 2) := by
  rw [socle_zigzagProjective_eq_radicalPower_two hns]
  ext x
  rw [mem_zigzagProjectiveRadicalPower_iff, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.mem_inf]
  exact (and_iff_right x.2).symm

/-- The volume vector, regarded as an element of the graded socle. -/
noncomputable def zigzagGradedSocleVolume (i : V) : zigzagGradedProjectiveSocle k G hns i :=
  ⟨zigzagVolume k G i, ⟨by
    simp only [SetLike.mem_coe]
    rw [mem_zigzagProjective_iff]
    exact zigzagVolume_mul_zigzagMk_vertexIdempotent k G i, by
    simp only [SetLike.mem_coe]
    rw [← Submodule.restrictScalars_mem k,
      restrictScalars_jacobson_sq_nonisolatedZigzagQuotient_eq_zigzagVolumeSpan hns]
    exact zigzagVolume_mem_zigzagVolumeSpan i⟩⟩

@[simp]
theorem coe_zigzagGradedSocleVolume (i : V) :
    (zigzagGradedSocleVolume k G hns i : Z) = zigzagVolume k G i :=
  (rfl)

/-- The distinguished volume of the graded socle lies in degree two. -/
theorem zigzagGradedSocleVolume_mem_grade_two (i : V) :
    zigzagGradedSocleVolume k G hns i ∈
      (zigzagGradedProjectiveSocle k G hns i).grading.piece 2 := by
  rw [mem_zigzagGradedProjectiveSocle_piece_iff, coe_zigzagGradedSocleVolume]
  have hv := (mem_zigzagProjectiveGrade_iff k G).1 <|
    (zigzagGradedProjective_piece k G i 2) ▸ zigzagProjectiveVolume_mem_grade_two k G i
  rwa [coe_zigzagProjectiveVolume] at hv

private theorem positiveIdeal_smul_socleVolume (i : V) :
    ∀ y ∈ gradedPositiveMulIdeal (zigzagIntegerGrade k G) (zigzagVertexIdempotent k G i),
      y • zigzagGradedSocleVolume k G hns i = 0 := by
  let _ := zigzagIntegerGradedAlgebra k G
  let f := LinearMap.toSpanSingleton Z (zigzagGradedProjectiveSocle k G hns i)
    (zigzagGradedSocleVolume k G hns i)
  have hle : gradedPositiveMulIdeal (zigzagIntegerGrade k G)
      (zigzagVertexIdempotent k G i) ≤ LinearMap.ker f := by
    rw [gradedPositiveMulIdeal_le_iff]
    intro p hp x hx
    apply Subtype.ext
    simp only [f, LinearMap.toSpanSingleton_apply, Submodule.coe_smul, smul_eq_mul,
      coe_zigzagGradedSocleVolume, Submodule.coe_zero]
    rw [mul_assoc, zigzagMk_vertexIdempotent_mul_zigzagVolume]
    have hv := (mem_zigzagGradedProjectiveSocle_piece_iff k G hns i 2 _).1
      (zigzagGradedSocleVolume_mem_grade_two k G hns i)
    rw [coe_zigzagGradedSocleVolume] at hv
    have hm := mul_mem_zigzagIntegerGrade k G hx hv
    have hp2 : 0 ≤ p + 2 := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hp2
    rw [hn, zigzagIntegerGrade_ofNat,
      zigzagGrade_eq_bot_of_three_le k G (by omega)] at hm
    exact hm
  exact fun y hy => hle hy

/-- Right multiplication by the volume descends from `P_i` to its graded head and raises
internal degree by two. -/
noncomputable def zigzagGradedHeadToSocle (i : V) :
    zigzagGradedSimple k G i ⟶ (zigzagGradedProjectiveSocle k G hns i).shiftObj (-2) :=
  let _ := zigzagIntegerGradedAlgebra k G
  eqToHom (zigzagGradedSimple_def k G i) ≫
    GradedModuleCat.ofHom
      (gradedPositiveMulQuotientLift (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i)
        (zigzagGradedSocleVolume k G hns i) (positiveIdeal_smul_socleVolume k G hns i))
      (LinearMap.isHomogeneous_def.2 fun p y hy => by
        obtain ⟨x, hx, rfl⟩ := mem_gradedPositiveMulQuotient_piece_iff _ |>.1 hy
        rw [gradedPositiveMulQuotientLift_gradedPositiveMulQuotientMk,
          GradedModuleCat.mem_shiftObj_piece_iff]
        let _ := (zigzagGradedProjectiveSocle k G hns i).gradedSMul
        have hm := SetLike.GradedSMul.smul_mem
          (B := (zigzagGradedProjectiveSocle k G hns i).grading.piece) hx
          (zigzagGradedSocleVolume_mem_grade_two k G hns i)
        simpa only [vadd_eq_add, add_zero, sub_neg_eq_add] using hm)

/-- On a representative, the head-to-socle map is right multiplication by the volume. -/
@[simp]
theorem zigzagGradedHeadToSocle_mk (i : V)
    (x : (Ideal.span {zigzagVertexIdempotent k G i} : Ideal Z)) :
    ((zigzagGradedHeadToSocle k G hns i).hom (zigzagGradedSimpleMk k G i x) : Z) =
      (x : Z) * zigzagVolume k G i := by
  let _ := zigzagIntegerGradedAlgebra k G
  have hc := congrArg (fun f => f.hom)
    (eqToHom_trans (zigzagGradedSimple_def k G i).symm (zigzagGradedSimple_def k G i))
  simp only [GradedModuleCat.hom_comp, eqToHom_refl, GradedModuleCat.hom_id] at hc
  simp only [zigzagGradedHeadToSocle, zigzagGradedSimpleMk_def, GradedModuleCat.hom_comp,
    LinearMap.comp_apply]
  have hc' := LinearMap.congr_fun hc
    (gradedPositiveMulQuotientMk (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i) x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hc'
  rw [hc', gradedPositiveMulQuotientLift_gradedPositiveMulQuotientMk]
  simp only [Submodule.coe_smul, smul_eq_mul, coe_zigzagGradedSocleVolume]

private theorem headToSocle_ne_zero (i : V) : zigzagGradedHeadToSocle k G hns i ≠ 0 := by
  intro h
  have he := zigzagGradedHeadToSocle_mk k G hns i
    (spanSingletonGenerator (zigzagVertexIdempotent k G i))
  rw [h, GradedModuleCat.hom_zero, LinearMap.zero_apply, Submodule.coe_zero,
    coe_spanSingletonGenerator, zigzagMk_vertexIdempotent_mul_zigzagVolume] at he
  exact zigzagVolume_ne_zero k G (hns i).choose_spec he.symm

private theorem headToSocle_surjective (i : V) :
    Function.Surjective (zigzagGradedHeadToSocle k G hns i).hom := by
  intro x
  let p : zigzagProjective k G i := ⟨x.1, x.2.1⟩
  have hp : p ∈ zigzagProjectiveRadicalPower k G i 2 :=
    (mem_zigzagProjectiveRadicalPower_iff k G i 2 p).2 x.2.2
  obtain ⟨y, hy⟩ := zigzagProjectiveMulVolume_surjective k G hns i ⟨p, hp⟩
  let y' : (Ideal.span {zigzagVertexIdempotent k G i} : Ideal Z) :=
    ⟨(y.1 : Z), by rw [← zigzagProjective_def]; exact y.1.2⟩
  refine ⟨zigzagGradedSimpleMk k G i y', ?_⟩
  apply Subtype.ext
  rw [zigzagGradedHeadToSocle_mk]
  have he := congrArg (fun z : zigzagProjectiveRadicalPower k G i 2 =>
    ((z : zigzagProjective k G i) : Z)) hy
  rw [zigzagProjectiveMulVolume_apply] at he
  simpa only [y', p, mul_zigzagVolume hns, zigzagProjectiveHeadCoeff_apply,
    zigzagTrivialCoeff_apply_eq_repr hns, Module.Basis.coord_apply] using he

/-- Right multiplication by the volume is an isomorphism from the graded head to the
socle shifted down by two. -/
instance isIso_zigzagGradedHeadToSocle (i : V) :
    IsIso (zigzagGradedHeadToSocle k G hns i) := by
  let _ : Simple (zigzagGradedSimple k G i) := simple_zigzagGradedSimple k G i
  have := mono_of_nonzero_from_simple (headToSocle_ne_zero k G hns i)
  have := (GradedModuleCat.epi_iff_surjective _).2 (headToSocle_surjective k G hns i)
  exact isIso_of_mono_of_epi _

/-- The graded simple head shifted up by two is the graded socle of the vertex projective.
The isomorphism is induced by right multiplication by the volume at the vertex. -/
noncomputable def zigzagGradedHeadIsoSocle (i : V) :
    (zigzagGradedSimple k G i).shiftObj 2 ≅ zigzagGradedProjectiveSocle k G hns i :=
  let f := zigzagGradedHeadToSocle k G hns i
  let e : zigzagGradedSimple k G i ≃ₗ[Z]
      (zigzagGradedProjectiveSocle k G hns i).shiftObj (-2) :=
    LinearEquiv.ofBijective f.hom
      ⟨(GradedModuleCat.mono_iff_injective f).1 inferInstance,
        headToSocle_surjective k G hns i⟩
  GradedModuleCat.isoMk e (fun p x => by
    rw [GradedModuleCat.mem_shiftObj_piece_iff]
    have hf : LinearMap.IsHomogeneous e.toLinearMap
        (zigzagGradedSimple k G i).grading.piece
        ((zigzagGradedProjectiveSocle k G hns i).shiftObj (-2)).grading.piece 0 :=
      f.isHomogeneous
    have he := LinearMap.IsHomogeneous.linearEquiv_symm hf
    constructor
    · intro hx
      have hm := hf.map_mem hx
      have hm' := (GradedModuleCat.mem_shiftObj_piece_iff
        (M := zigzagGradedProjectiveSocle k G hns i) (-2) (p - 2) (e x)).1
          (by simpa only [add_zero, LinearEquiv.coe_toLinearMap] using hm)
      simpa only [sub_neg_eq_add, sub_add_cancel] using hm'
    · intro hx
      have hx' : e x ∈
          ((zigzagGradedProjectiveSocle k G hns i).shiftObj (-2)).grading.piece (p - 2) :=
        (GradedModuleCat.mem_shiftObj_piece_iff
          (M := zigzagGradedProjectiveSocle k G hns i) (-2) (p - 2) (e x)).2
            (by simpa only [sub_neg_eq_add, sub_add_cancel] using hx)
      have hm := he.map_mem hx'
      simpa only [add_zero, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] using hm)

/-- The shifted isomorphism has the same underlying map as right multiplication by the volume. -/
@[simp]
theorem zigzagGradedHeadIsoSocle_hom_apply (i : V) (x : zigzagGradedSimple k G i) :
    (zigzagGradedHeadIsoSocle k G hns i).hom.hom x =
      (zigzagGradedHeadToSocle k G hns i).hom x := by
  simp only [zigzagGradedHeadIsoSocle, GradedModuleCat.isoMk_hom_hom,
    LinearEquiv.coe_toLinearMap]
  exact LinearEquiv.ofBijective_apply _ x

/-- The inverse head–socle isomorphism sends the volume to the class of the vertex idempotent. -/
@[simp]
theorem zigzagGradedHeadIsoSocle_inv_volume (i : V) :
    (zigzagGradedHeadIsoSocle k G hns i).inv.hom (zigzagGradedSocleVolume k G hns i) =
      zigzagGradedSimpleMk k G i (spanSingletonGenerator (zigzagVertexIdempotent k G i)) := by
  apply (GradedModuleCat.mono_iff_injective
    (zigzagGradedHeadIsoSocle k G hns i).hom).1 inferInstance
  have hv : (zigzagGradedHeadIsoSocle k G hns i).hom.hom
      (zigzagGradedSimpleMk k G i (spanSingletonGenerator (zigzagVertexIdempotent k G i))) =
      zigzagGradedSocleVolume k G hns i := by
    apply Subtype.ext
    rw [zigzagGradedHeadIsoSocle_hom_apply, zigzagGradedHeadToSocle_mk,
      coe_spanSingletonGenerator, zigzagMk_vertexIdempotent_mul_zigzagVolume,
      coe_zigzagGradedSocleVolume]
  rw [hv]
  exact LinearMap.congr_fun
    (congrArg GradedModuleCat.Hom.hom (zigzagGradedHeadIsoSocle k G hns i).inv_hom_id)
    (zigzagGradedSocleVolume k G hns i)

end TauCeti
