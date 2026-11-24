/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.QuasiIso
public import TauCeti.Algebra.Homology.DG.Bimodule.Shift
public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.Algebra.Module.GradedModule.Prod

/-!
# Mapping cones of DG bimodule morphisms

The mapping cone of a closed degree-zero map `f : M ⟶ N` has graded carrier
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

private theorem mem_coneGrading {q : ℤ} {z : M.shift 1 × N} :
    z ∈ (G).piece q ↔ z.1 ∈ (M.shift 1).grading q ∧ z.2 ∈ N.grading q := by
  rw [InternalGrading.prod_piece, Submodule.mem_prod,
    InternalGrading.ofDecomposition_piece, InternalGrading.ofDecomposition_piece]

local notation "e" =>
  LinearEquiv.prodCongr (DGBimoduleCat.shiftEquiv M 1) (LinearEquiv.refl R N)

local notation "Δ[" φ "]" =>
  LinearEquiv.conj (LinearEquiv.symm (e))
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
    simp only [LinearEquiv.apply_symm_apply, shiftEquiv_differential,
      Int.negOnePow_one, Units.neg_smul, one_smul]
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
  have hz := LinearMap.congr_fun h ((e) z)
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  exact (e).injective (by simpa only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, map_zero] using hz)

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
noncomputable abbrev mappingCone (f : M ⟶ N) : DGBimoduleCat hA hB := by
  letI : SetLike.GradedSMul 𝒜 (G).piece := ⟨by
    intro p q a z ha hz
    exact mem_coneGrading.mpr
      ⟨SetLike.GradedSMul.smul_mem ha (mem_coneGrading.mp hz).1,
        SetLike.GradedSMul.smul_mem ha (mem_coneGrading.mp hz).2⟩⟩
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece (G).piece :=
    ⟨by
      intro p q b z hb hz
      exact mem_coneGrading.mpr
        ⟨SetLike.GradedSMul.smul_mem hb (mem_coneGrading.mp hz).1,
          SetLike.GradedSMul.smul_mem hb (mem_coneGrading.mp hz).2⟩⟩
  exact DGBimoduleCat.of (ℳ := (G).piece) (dM := Δ[f])
    { toIsDGLeftModule :=
        { isHomogeneous := by exact LinearMap.isHomogeneous_def.mpr fun _ _ hz ↦
              coneDifferential_mem f hz
          sq_zero := by exact coneDifferential_sq_zero f
          leibniz := by exact coneDifferential_leibniz_left f }
      leibniz_right := by exact coneDifferential_leibniz_right f }

/-- On the two cone components the differential is the shifted differential and the
sum of the boundary with the target differential. -/
theorem mappingCone_differential_apply (f : M ⟶ N) (z : M.shift 1 × N) :
    (mappingCone f).differential z = ((M.shift 1).differential z.1,
      f (M.shiftEquiv 1 z.1) + N.differential z.2) :=
  coneDifferential_apply f z

/-- The map from the cone induced by a morphism on the target that kills the image
of the source. It sends `(x, y)` to `g y`. -/
noncomputable def mappingConeDesc (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0) :
    mappingCone f ⟶ P := by
  letI := (mappingCone f).gradedSMul
  letI := (mappingCone f).gradedLeft
  refine ⟨⟨g.val.toLinearMap ∘ₗ LinearMap.snd Bᵐᵒᵖ _ _,
    fun hz ↦ GradedFunLike.map_mem g (mem_coneGrading.mp hz).2,
    fun z ↦ by
      have hfg := DFunLike.congr_fun h (M.shiftEquiv 1 z.1)
      simp only [comp_apply, zero_apply] at hfg
      simp [hfg]⟩, (mem_dgBimoduleHomSubmodule _ _ _).mpr
      (fun a z ↦ map_smul_left g a z.2)⟩

@[simp]
theorem mappingConeDesc_apply (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0) (z : M.shift 1 × N) :
    mappingConeDesc f g h z = g z.2 := (rfl)

/-- In a short exact sequence, the map from the cone of the first morphism to the last term
is a quasi-isomorphism. -/
theorem isQuasiIso_mappingConeDesc (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g) :
    DGRightModuleCat.IsQuasiIso (forgetToRightModuleCat.map (mappingConeDesc f g h)) := by
  apply (DGRightModuleHom.isQuasiIso_iff_forall_exists _).mpr
  -- The criterion is stated on forgotten objects. Use the original carriers to read its equations.
  change ∀ (z : M.shift 1 × N) (y : P),
    (mappingCone f).differential z = 0 → mappingConeDesc f g h z = P.differential y →
    ∃ (u : M.shift 1 × N) (v : P),
      (mappingCone f).differential u = z ∧ mappingConeDesc f g h u + P.differential v = y
  intro z y hz hy
  rw [mappingCone_differential_apply] at hz
  have hz₂ : f (M.shiftEquiv 1 z.1) + N.differential z.2 = 0 := congrArg Prod.snd hz
  rw [mappingConeDesc_apply] at hy
  obtain ⟨v, rfl⟩ := hg y
  obtain ⟨u, hu⟩ := (hexact _).mp (by rw [map_sub, ← map_d, hy, sub_self] :
    g (z.2 - N.differential v) = 0)
  have hdu : -M.differential u = M.shiftEquiv 1 z.1 := hf (by
    rw [map_neg, ← map_d, hu, map_sub, N.isDGBimodule.sq_zero, sub_zero,
      ← neg_eq_of_add_eq_zero_right hz₂, neg_neg])
  refine ⟨((M.shiftEquiv 1).symm u, v), 0, Prod.ext ?_ ?_, ?_⟩
  · rw [mappingCone_differential_apply]
    apply (M.shiftEquiv 1).injective
    simpa only [Prod.fst, shiftEquiv_differential, LinearEquiv.apply_symm_apply,
      Int.negOnePow_one, Units.neg_smul, one_smul] using hdu
  · rw [mappingCone_differential_apply, Prod.snd, LinearEquiv.apply_symm_apply, hu,
      sub_add_cancel]
  · rw [mappingConeDesc_apply, Prod.snd, map_zero, add_zero]

end TauCeti.DGBimoduleCat
