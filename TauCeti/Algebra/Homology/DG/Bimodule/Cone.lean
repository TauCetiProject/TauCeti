/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.QuasiIso
public import TauCeti.Algebra.Homology.DG.Bimodule.Shift
import TauCeti.Algebra.Homology.SquareZero.Quotient
public import TauCeti.Algebra.Module.GradedModule.Prod

/-!
# Mapping cones of DG bimodule morphisms

Combining `LinearMap.mappingCone` and `DGBimoduleCat.shift`, the cone of a closed
degree-zero map `f : M ⟶ N` has graded carrier
`M[1] × N`, with differential `(x, y) ↦ (-d x, f x + d y)`. The shift twists the
left action by the Koszul sign. For a short exact sequence of DG bimodules the
cone of the first map augments by a quasi-isomorphism to the last term.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.DGBimoduleCat

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {M N P : DGBimoduleCat.{uR, uA, uB, uM} hA hB}

local notation "G" =>
  InternalGrading.prod
    (InternalGrading.ofDecomposition
      (DGRightModuleCat.grading (DGBimoduleCat.toDGRightModuleCat (DGBimoduleCat.shift M 1))))
    (InternalGrading.ofDecomposition
      (DGRightModuleCat.grading (DGBimoduleCat.toDGRightModuleCat N)))

local instance {C S : Type*} [SetLike S C] [SMul C (M.shift 1)] [SMul C N] (𝒞 : ℤ → S)
    [SetLike.GradedSMul 𝒞 (M.shift 1).grading] [SetLike.GradedSMul 𝒞 N.grading] :
    SetLike.GradedSMul 𝒞 (G).piece := by
  apply InternalGrading.instGradedSMulProd (hG := ?_) (hH := ?_) <;>
    rw [InternalGrading.ofDecomposition_piece] <;> infer_instance

private theorem mem_coneGrading {q : ℤ} {z : M.shift 1 × N} :
    z ∈ (G).piece q ↔ z.1 ∈ (M.shift 1).grading q ∧ z.2 ∈ N.grading q := by
  rw [InternalGrading.prod_piece, Submodule.mem_prod,
    InternalGrading.ofDecomposition_piece, InternalGrading.ofDecomposition_piece]

local notation "coneCarrierEquiv" =>
  LinearEquiv.prodCongr (DGBimoduleCat.shiftEquiv M 1) (LinearEquiv.refl R N)

local notation "Δ[" φ "]" =>
  LinearEquiv.conj (LinearEquiv.symm (coneCarrierEquiv))
    (LinearMap.mappingCone (DGRightModuleCat.differential (DGBimoduleCat.toDGRightModuleCat M))
      (DGRightModuleCat.differential (DGBimoduleCat.toDGRightModuleCat N))
      (LinearMap.restrictScalars R (DGRightModuleHom.toLinearMap (Subtype.val φ))))

private theorem coneDifferential_apply (f : M ⟶ N) (z : M.shift 1 × N) :
    Δ[f] z = ((M.shift 1).differential z.1,
      f (M.shiftEquiv 1 z.1) + N.differential z.2) := by
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearMap.mappingCone_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_symm, LinearEquiv.refl_apply,
    LinearEquiv.refl_symm, LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
    DGBimoduleHom.coe_val]
  apply Prod.ext
  · apply (M.shiftEquiv 1).injective
    simp only [LinearEquiv.apply_symm_apply, shiftEquiv_one_differential]
  · rfl

private theorem coneDifferential_mem (f : M ⟶ N) {q : ℤ} {z : M.shift 1 × N}
    (hz : z ∈ (G).piece q) : Δ[f] z ∈ (G).piece (q + 1) := by
  obtain ⟨hx, hy⟩ := mem_coneGrading.mp hz
  rw [coneDifferential_apply, mem_coneGrading]
  exact ⟨(M.shift 1).isDGLeftModule.isHomogeneous.map_mem hx,
    (N.grading (q + 1)).add_mem
      (GradedFunLike.map_mem f ((M.shiftEquiv_mem_grading_iff 1 q z.1).mpr hx))
      (N.isDGLeftModule.isHomogeneous.map_mem hy)⟩

private theorem coneDifferential_sq_zero (f : M ⟶ N) (z : M.shift 1 × N) :
    Δ[f] (Δ[f] z) = 0 := by
  let g := f.val.toLinearMap.restrictScalars R
  have h := LinearMap.mappingCone_comp_self g
    (LinearMap.ext M.isDGBimodule.sq_zero) (LinearMap.ext N.isDGBimodule.sq_zero)
    (LinearMap.ext fun x ↦ (map_d f x).symm)
  have hz := LinearMap.congr_fun h ((coneCarrierEquiv) z)
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  exact (coneCarrierEquiv).injective (by
    simpa only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      map_zero] using hz)

private theorem coneDifferential_leibniz_left (f : M ⟶ N) {p : ℤ} {a : A}
    (ha : a ∈ 𝒜 p) (z : M.shift 1 × N) :
    Δ[f] (a • z) =
      dA a • z + p.negOnePow • (a • Δ[f] z) := by
  simp only [coneDifferential_apply, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, shiftEquiv_smul_left, map_smul_left, (M.shift 1).isDGLeftModule.leibniz ha,
    N.isDGLeftModule.leibniz ha, true_and]
  rw [InternalGrading.koszulTwistAlgEquiv_apply_of_mem 𝒜 1 ha, one_mul, smul_assoc,
    smul_add, smul_add]
  abel

private theorem coneDifferential_leibniz_right (f : M ⟶ N) {q : ℤ} {z : M.shift 1 × N}
    (hz : z ∈ (G).piece q) (b : B) :
    Δ[f] (op b • z) =
      op b • Δ[f] z + q.negOnePow • (op (dB b) • z) := by
  obtain ⟨hx, hy⟩ := mem_coneGrading.mp hz
  simp only [coneDifferential_apply, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, shiftEquiv_smul_right, map_smul,
    (M.shift 1).isDGBimodule.leibniz_right hx, N.isDGBimodule.leibniz_right hy, true_and]
  rw [smul_add]
  abel

/-- The DG mapping cone, with the original right action and the shifted left action
on the source summand. -/
@[expose, implicit_reducible]
noncomputable def cone (f : M ⟶ N) : DGBimoduleCat hA hB := by
  exact DGBimoduleCat.of (ℳ := (G).piece) (dM := Δ[f])
    { toIsDGLeftModule :=
        { isHomogeneous := by exact LinearMap.isHomogeneous_def.mpr fun _ _ hz ↦
              coneDifferential_mem f hz
          sq_zero := by exact coneDifferential_sq_zero f
          leibniz := by exact coneDifferential_leibniz_left f }
      leibniz_right := by exact coneDifferential_leibniz_right f }

/-- A cone element is homogeneous when both components have the same shifted degree. -/
@[simp]
theorem mem_cone_grading_iff (f : M ⟶ N) {q : ℤ} {z : cone f} :
    z ∈ (cone f).grading q ↔ z.1 ∈ (M.shift 1).grading q ∧ z.2 ∈ N.grading q :=
  mem_coneGrading

/-- The left action is shifted on the source and unchanged on the target. -/
@[simp]
theorem cone_smul_left (f : M ⟶ N) (a : A) (z : cone f) :
    a • z = ((a • z.1 : M.shift 1), a • z.2) := (rfl)

/-- The right action on the cone acts componentwise. -/
@[simp]
theorem cone_smul_right (f : M ⟶ N) (b : Bᵐᵒᵖ) (z : cone f) :
    b • z = ((b • z.1 : M.shift 1), b • z.2) := (rfl)

/-- On the two cone components the differential is the shifted differential and the
sum of the boundary with the target differential. -/
@[simp]
theorem cone_differential_apply (f : M ⟶ N) (z : M.shift 1 × N) :
    (cone f).differential z = ((M.shift 1).differential z.1,
      f (M.shiftEquiv 1 z.1) + N.differential z.2) :=
  coneDifferential_apply f z

/-- The target includes as the second summand of the cone. -/
noncomputable def coneInclusion (f : M ⟶ N) : N ⟶ cone f := by
  let i : N →ₗ[Bᵐᵒᵖ] cone f := LinearMap.inr Bᵐᵒᵖ (M.shift 1) N
  have hi (z : N) : i z = (0, z) := rfl
  refine ⟨⟨i, ?_, ?_⟩, (mem_dgBimoduleHomSubmodule _ _ _).mpr ?_⟩
  · intro q z hz
    rw [hi, mem_cone_grading_iff]
    exact ⟨(M.shift 1 |>.grading q).zero_mem, hz⟩
  · intro z
    rw [hi, hi, cone_differential_apply]
    simp
  · intro a z
    simp only [DGRightModuleHom.coe_mk, hi, cone_smul_left, smul_zero]

/-- The target inclusion inserts zero in the shifted component. -/
@[simp]
theorem coneInclusion_apply (f : M ⟶ N) (z : N) : coneInclusion f z = (0, z) :=
  (rfl)

/-- Construct a map out of the cone from a closed map on the target and a degree-zero
bimodule map on the shifted source whose differential defect is the composite through `f`. -/
noncomputable def coneDescOf (f : M ⟶ N) (g : N ⟶ P) (s : M.shift 1 →ₗ[Bᵐᵒᵖ] P)
    (hgrade : ∀ {q : ℤ} {x : M.shift 1}, x ∈ (M.shift 1).grading q → s x ∈ P.grading q)
    (hleft : ∀ (a : A) (x : M.shift 1), s (a • x) = a • s x)
    (hd : ∀ x : M.shift 1,
      P.differential (s x) = s ((M.shift 1).differential x) + g (f (M.shiftEquiv 1 x))) :
    cone f ⟶ P := by
  let t : cone f →ₗ[Bᵐᵒᵖ] P := s.coprod g.val.toLinearMap
  have ht (z : cone f) : t z = s z.1 + g z.2 := rfl
  refine ⟨⟨t, ?_, ?_⟩, (mem_dgBimoduleHomSubmodule _ _ _).mpr ?_⟩
  · intro q z hz
    obtain ⟨hx, hy⟩ := (mem_cone_grading_iff f).mp hz
    rw [ht]
    exact (P.grading q).add_mem (hgrade hx) (GradedFunLike.map_mem g hy)
  · intro z
    simp only [ht, cone_differential_apply, map_add, hd, map_d, add_assoc]
  · intro a z
    simp only [DGRightModuleHom.coe_mk, ht, cone_smul_left, hleft,
      map_smul_left, smul_add]

/-- The descended map adds the values from the two summands. -/
@[simp]
theorem coneDescOf_apply (f : M ⟶ N) (g : N ⟶ P) (s : M.shift 1 →ₗ[Bᵐᵒᵖ] P)
    (hgrade hleft hd) (z : cone f) : coneDescOf f g s hgrade hleft hd z = s z.1 + g z.2 :=
  (rfl)

/-- Maps out of a cone are determined by their values on its two summands. -/
@[ext]
theorem cone_hom_ext {f : M ⟶ N} {g h : cone f ⟶ P}
    (h₁ : ∀ x : M.shift 1, g (x, 0) = h (x, 0))
    (h₂ : ∀ y : N, g (0, y) = h (0, y)) : g = h := by
  apply hom_ext
  intro z
  have hz : z = (z.1, 0) + (0, z.2) :=
    Prod.ext (add_zero z.1).symm (zero_add z.2).symm
  rw [hz, map_add, map_add, h₁, h₂]

/-- The map from the cone induced by a morphism on the target that kills the image
of the source. It sends `(x, y)` to `g y`. -/
noncomputable def coneDesc (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0) :
    cone f ⟶ P :=
  coneDescOf f g 0 (fun {q} {_} _ ↦ (P.grading q).zero_mem) (by simp) fun x ↦ by
    have hfg := DFunLike.congr_fun h (M.shiftEquiv 1 x)
    simpa only [comp_apply, zero_apply, LinearMap.zero_apply, map_zero, zero_add, eq_comm] using hfg

/-- The map induced by a closed map on the target ignores the shifted source. -/
@[simp]
theorem coneDesc_apply (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0) (z : cone f) :
    coneDesc f g h z = g z.2 := by
  simp [coneDesc]

/-- The induced map restricts to the given map on the target. -/
@[reassoc (attr := simp)]
theorem coneInclusion_comp_coneDesc (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0) :
    coneInclusion f ≫ coneDesc f g h = g := by
  apply hom_ext
  intro z
  rw [comp_apply, coneInclusion_apply, coneDesc_apply]

/-- In a short exact sequence the cone augments quasi-isomorphically to the last term.
This is `LinearMap.mappingConeProjectionHomologyEquiv` in the shifted carrier coordinates. -/
theorem isQuasiIso_forgetToRightModuleCat_map_coneDesc (f : M ⟶ N) (g : N ⟶ P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    DGRightModuleCat.IsQuasiIso
      (forgetToRightModuleCat.map (coneDesc f g (comp_eq_zero_of_exact hexact))) := by
  have hfg := comp_eq_zero_of_exact hexact
  apply (DGRightModuleHom.isQuasiIso_iff_bijective_homologyMap _).mpr
  let u := f.val.toLinearMap.restrictScalars R
  let v := g.val.toLinearMap.restrictScalars R
  have hM : M.differential ∘ₗ M.differential = 0 := LinearMap.ext M.isDGBimodule.sq_zero
  have hN : N.differential ∘ₗ N.differential = 0 := LinearMap.ext N.isDGBimodule.sq_zero
  have hP : P.differential ∘ₗ P.differential = 0 := LinearMap.ext P.isDGBimodule.sq_zero
  have hu : u ∘ₗ M.differential = N.differential ∘ₗ u :=
    LinearMap.ext fun x ↦ (map_d f x).symm
  have hv : v ∘ₗ N.differential = P.differential ∘ₗ v :=
    LinearMap.ext fun x ↦ (map_d g x).symm
  let carrierEquiv : cone f ≃ₗ[R] M × N := (coneCarrierEquiv)
  have hcone : carrierEquiv.toLinearMap ∘ₗ (cone f).differential =
      LinearMap.mappingCone M.differential N.differential u ∘ₗ carrierEquiv.toLinearMap :=
    LinearMap.ext fun z ↦ by
      -- The cone differential was defined by conjugation with the carrier equivalence.
      change carrierEquiv (carrierEquiv.symm (LinearMap.mappingCone
        M.differential N.differential u (carrierEquiv z))) = _
      exact LinearEquiv.apply_symm_apply _ _
  have hsq : (cone f).differential ∘ₗ (cone f).differential = 0 :=
    LinearMap.ext (cone f).isDGBimodule.sq_zero
  let E := carrierEquiv.homologyEquiv hsq (LinearMap.mappingCone_comp_self u hM hN hu) hcone
  let F := LinearMap.mappingConeProjectionHomologyEquiv hM hN hP hu hf (π := v) hg hexact hv
  let w := (coneDesc f g hfg).val.toLinearMap.restrictScalars R
  have hw : w ∘ₗ (cone f).differential = P.differential ∘ₗ w :=
    LinearMap.ext fun z ↦ (map_d (coneDesc f g hfg) z).symm
  -- Forgetting the left action leaves the underlying differential and right-linear map intact.
  change Function.Bijective (LinearMap.homologyMap w hsq hP hw)
  convert F.bijective.comp E.bijective using 1
  funext c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  simp only [Function.comp_apply, E, F, LinearEquiv.homologyEquiv_mk, LinearMap.homologyMap_mk]
  rw [LinearMap.mappingConeProjectionHomologyEquiv_mk hM hN hP hu hf (π := v) hg hexact hv]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (coneDesc_apply f g hfg z.val))

end TauCeti.DGBimoduleCat
