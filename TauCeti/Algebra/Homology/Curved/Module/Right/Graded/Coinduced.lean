/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import TauCeti.Algebra.Category.GradedModuleCat.Coinduced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective.Basic

/-!
# Coinduced curved differential graded right modules over graded modules

Every graded right module `Y` over a curved differential graded algebra `(A, d, w)` coinduces a
curved right module `coinducedObj h Y`, Positselski's functor `G⁻` in the right-module convention,
realized as the free curved right module `freeObj h (Y{-1})` on the shifted graded module `Y{-1}`.
Elements in degree `p` represent formal expressions `ι u + d (ι v)` with `u ∈ Y_{p + 1}` and
`v ∈ Y_p`.

Projecting onto the `d (ι v)` coordinate defines a graded right-linear counit
`coinducedCounit h Y : toGradedModuleCat (coinducedObj h Y) ⟶ Y` fitting into a short exact
sequence `0 ⟶ Y{-1} ⟶ toGradedModuleCat (coinducedObj h Y) ⟶ Y ⟶ 0`. Every graded right-linear
morphism `g : toGradedModuleCat M ⟶ Y` lifts uniquely to a closed morphism
`coinducedLift g : M ⟶ coinducedObj h Y` sending `m` to `ι (g (d_M m)) + d (ι (g m))`, exhibiting
`coinducedFunctor` as right adjoint to `forgetDifferential`.

Because `coinducedObj h Y` is contractible in the curved homotopy category, preserves injective
graded right modules, and turns graded monomorphisms into closed monomorphisms, combining
`coinducedLift` with `EnoughInjectives` on `GradedModuleCat` embeds every curved right module into
a contractible graded-injective curved right module (`exists_mono_contractible_gradedInjective`).

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.coinducedObj`: the coinduced curved right module `G⁻(Y)`.
* `TauCeti.CurvedDGRightModuleCat.coinducedι` and
  `TauCeti.CurvedDGRightModuleCat.coinducedCounit`: the graded inclusion `Y{-1} ⟶ G⁻(Y)` and
  graded counit `G⁻(Y) ⟶ Y`.
* `TauCeti.CurvedDGRightModuleCat.coinducedLift` and
  `TauCeti.CurvedDGRightModuleCat.coinducedHomEquiv`: the closed lift `M ⟶ G⁻(Y)` of a graded
  morphism `toGradedModuleCat M ⟶ Y` and the `R`-linear adjunction equivalence.
* `TauCeti.CurvedDGRightModuleCat.coinducedFunctor` and
  `TauCeti.CurvedDGRightModuleCat.forgetDifferentialCoinducedAdjunction`: the right adjoint to
  `forgetDifferential` and the adjunction `forgetDifferential ⊣ coinducedFunctor`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.coinducedShortExact`: the underlying graded module of `G⁻(Y)` is
  an extension of `Y` by `Y{-1}`, hence injective whenever `Y` is injective.
* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_coinducedObj`: `G⁻(Y)` is zero in the curved
  homotopy category.
* `TauCeti.CurvedDGRightModuleCat.exists_mono_contractible_gradedInjective` and
  `TauCeti.CurvedDGRightModuleCat.exists_shortExact_contractible_of_hasInjectiveDimensionLT`:
  contractible graded-injective embeddings and dimension shifting for graded injective dimension.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6, Proof of Theorem.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Theorem 7.8(a) and Theorem 7.9(a).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uM u

section Objects

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  (h : IsCurvedDGAlgebra 𝒜 d w)
  (Y : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)

/-- The **coinduced curved differential graded right module** on a graded right module `Y`
(Positselski's functor `G⁻`), realized as `freeObj h (Y{-1})`. -/
def coinducedObj : CurvedDGRightModuleCat.{uR, uA, uM} h :=
  freeObj h (Y.shiftObj (-1))

/-- `coinducedObj h Y` is by definition `freeObj h (Y{-1})`. -/
theorem coinducedObj_eq : coinducedObj h Y = freeObj h (Y.shiftObj (-1)) :=
  (rfl)

attribute [local implicit_reducible] coinducedObj

/-- The canonical graded right-linear inclusion `Y{-1} ⟶ toGradedModuleCat (coinducedObj h Y)`. -/
def coinducedι : Y.shiftObj (-1) ⟶ toGradedModuleCat (coinducedObj h Y) :=
  freeUnit h (Y.shiftObj (-1))

/-- The canonical graded right-linear counit `toGradedModuleCat (coinducedObj h Y) ⟶ Y`. -/
def coinducedCounit : toGradedModuleCat (coinducedObj h Y) ⟶ Y :=
  freeProj h (Y.shiftObj (-1)) ≫
    ((GradedModuleCat.shiftFunctorAddIso
      (InternalGrading.ofDecomposition 𝒜).opposite.piece (-1) 1).hom.app Y ≫
    (GradedModuleCat.shiftFunctorZeroIso
      (InternalGrading.ofDecomposition 𝒜).opposite.piece).hom.app Y)

/-- The graded inclusion `Y{-1} ⟶ coinducedObj h Y` followed by `coinducedCounit h Y` is zero. -/
@[reassoc (attr := simp)]
theorem coinducedι_comp_coinducedCounit : coinducedι h Y ≫ coinducedCounit h Y = 0 := by
  rw [coinducedι, coinducedCounit, freeUnit_comp_freeProj_assoc, zero_comp]

/-- After forgetting the differential, `coinducedObj h Y` sits in the short exact sequence
`0 ⟶ Y{-1} ⟶ toGradedModuleCat (coinducedObj h Y) ⟶ Y ⟶ 0` of graded right modules. -/
theorem coinducedShortExact :
    (ShortComplex.mk (coinducedι h Y) (coinducedCounit h Y)
      (coinducedι_comp_coinducedCounit h Y)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (freeShortExact h (Y.shiftObj (-1)))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (((GradedModuleCat.shiftFunctorAddIso
        (InternalGrading.ofDecomposition 𝒜).opposite.piece (-1) 1).app Y) ≪≫
      (GradedModuleCat.shiftFunctorZeroIso
        (InternalGrading.ofDecomposition 𝒜).opposite.piece).app Y)
    (by simp [coinducedι])
    (by simp [coinducedCounit])

/-- The canonical graded inclusion `Y{-1} ⟶ toGradedModuleCat (coinducedObj h Y)` is a
monomorphism. -/
instance : Mono (coinducedι h Y) :=
  (coinducedShortExact h Y).mono_f

/-- The canonical graded counit `toGradedModuleCat (coinducedObj h Y) ⟶ Y` is an epimorphism. -/
instance : Epi (coinducedCounit h Y) :=
  (coinducedShortExact h Y).epi_g

/-- If `Y` is injective in the category of graded right modules, then the underlying graded right
module of `coinducedObj h Y` is injective as well, as an extension of `Y` by `Y{-1}`. -/
instance [Injective Y] : Injective (toGradedModuleCat (coinducedObj h Y)) :=
  injective_iff_hasInjectiveDimensionLT_one.mpr
    ((coinducedShortExact h Y).hasInjectiveDimensionLT_X₂ 1 inferInstance inferInstance)

/-- If `Y` is projective in the category of graded right modules, then the underlying graded right
module of `coinducedObj h Y` is projective as well. -/
instance [Projective Y] : Projective (toGradedModuleCat (coinducedObj h Y)) :=
  inferInstanceAs (Projective (toGradedModuleCat (freeObj h (Y.shiftObj (-1)))))

end Objects

-- Keep the closed and homotopy categories and `coinducedObj` transparent locally.
attribute [local implicit_reducible] ForgetEnrichment coinducedObj dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

section Homotopy

variable (h : IsCurvedDGAlgebra 𝒜 d w)
  (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)

/-- For an injective graded right module `Y`, `coinducedObj h Y` is graded-injective. -/
theorem gradedInjective_coinducedObj [Injective Y] :
    gradedInjective R h (DGHomotopyCategory.of R (coinducedObj h Y)) := by
  rw [gradedInjective_iff, DGHomotopyCategory.underlying_of]
  infer_instance

/-- Every coinduced curved right module `coinducedObj h Y` is zero in the curved homotopy
category. -/
theorem isZero_homotopy_coinducedObj :
    IsZero (DGHomotopyCategory.of R (coinducedObj h Y)) :=
  isZero_homotopy_freeObj h (Y.shiftObj (-1))

end Homotopy

section UniversalProperty

variable {h : IsCurvedDGAlgebra 𝒜 d w}
  {Y Z : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
  {M N : CurvedDGRightModuleCat.{u, u, u} h}

private theorem freeι_shift_neg_one_mem (g : toGradedModuleCat M ⟶ Y) {q : ℤ} {x : M}
    (hx : x ∈ M.grading q) :
    freeι h (Y.shiftObj (-1)) (g.hom x) ∈ (freeObj h (Y.shiftObj (-1))).grading (q - 1) := by
  have hg : g.hom x ∈ (Y.shiftObj (-1)).grading.piece (q - 1) := by
    rw [Y.mem_shiftObj_piece_iff (-1) (q - 1), show q - 1 - -1 = q by omega]
    exact GradedModuleCat.map_mem g (by simpa only [toGradedModuleCat_piece] using hx)
  simpa only [toGradedModuleCat_piece, hom_freeUnit] using
    GradedModuleCat.map_mem (freeUnit h (Y.shiftObj (-1))) hg

private theorem coinducedLift_map_smul_aux (g : toGradedModuleCat M ⟶ Y) (a : A) (m : M) :
    freeι h (Y.shiftObj (-1)) (g.hom (M.differential (op a • m))) +
        (freeObj h (Y.shiftObj (-1))).differential
          (freeι h (Y.shiftObj (-1)) (g.hom (op a • m))) =
      op a • (freeι h (Y.shiftObj (-1)) (g.hom (M.differential m)) +
        (freeObj h (Y.shiftObj (-1))).differential (freeι h (Y.shiftObj (-1)) (g.hom m))) := by
  let V := Y.shiftObj (-1)
  let ι := freeι h V
  let dF := (freeObj h V).differential
  induction m using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add m₁ m₂ hm₁ hm₂ =>
    calc
      ι (g.hom (M.differential (op a • (m₁ + m₂)))) + dF (ι (g.hom (op a • (m₁ + m₂))))
        = (ι (g.hom (M.differential (op a • m₁))) + dF (ι (g.hom (op a • m₁)))) +
            (ι (g.hom (M.differential (op a • m₂))) + dF (ι (g.hom (op a • m₂)))) := by
          simp only [smul_add, map_add]
          abel
      _ = op a • (ι (g.hom (M.differential (m₁ + m₂))) + dF (ι (g.hom (m₁ + m₂)))) := by
          rw [hm₁, hm₂]
          simp only [map_add, smul_add]
          abel
  | @homogeneous p m =>
    rcases m with ⟨m, hm⟩
    dsimp only
    have hιm : ι (g.hom m) ∈ (freeObj h V).grading (p - 1) := freeι_shift_neg_one_mem g hm
    have hsign : (p - 1).negOnePow = -p.negOnePow :=
      Int.negOnePow_eq_neg_of_odd_sub ⟨-1, by omega⟩
    rw [M.isCurvedDGRightModule.leibniz hm a, g.hom.map_add, ι.map_add, g.hom.map_smul,
      ι.map_smul, g.hom.map_smul, ι.map_smul, (freeObj h V).isCurvedDGRightModule.leibniz hιm a,
      hsign]
    simp only [Units.smul_def, Units.val_neg, map_zsmul, neg_zsmul, g.hom.map_smul, ι.map_smul,
      smul_add]
    abel

/-- Lift a graded right-linear morphism `g : toGradedModuleCat M ⟶ Y` to a closed morphism
`M ⟶ coinducedObj h Y` sending `m` to `ι (g (d_M m)) + d (ι (g m))`. -/
def coinducedLift (g : toGradedModuleCat M ⟶ Y) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y) :=
  let V := Y.shiftObj (-1)
  let ι := freeι h V
  let dF := (freeObj h V).differential
  closedHomOf
    { toFun := fun m ↦ ι (g.hom (M.differential m)) + dF (ι (g.hom m))
      map_add' := fun x y ↦ by
        simp only [map_add]
        abel
      map_smul' := fun z m ↦ by
        induction z using MulOpposite.rec' with | h a =>
        exact coinducedLift_map_smul_aux g a m }
    (fun p m hm ↦ by
      have hdm : M.differential m ∈ M.grading (p + 1) :=
        M.isCurvedDGRightModule.isHomogeneous.map_mem hm
      have h₁ : ι (g.hom (M.differential m)) ∈ (freeObj h V).grading p := by
        simpa only [add_sub_cancel_right] using freeι_shift_neg_one_mem g hdm
      have h₂ : dF (ι (g.hom m)) ∈ (freeObj h V).grading p := by
        simpa only [sub_add_cancel] using
          (freeObj h V).isCurvedDGRightModule.isHomogeneous.map_mem (freeι_shift_neg_one_mem g hm)
      exact Submodule.add_mem _ h₁ h₂)
    (fun m ↦ by
      dsimp only [coinducedObj, LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_add, (freeObj h V).isCurvedDGRightModule.sq_eq, M.isCurvedDGRightModule.sq_eq,
        g.hom.map_smul, ι.map_smul, add_comm])

private theorem closedHom_coinducedLift_apply (g : toGradedModuleCat M ⟶ Y) (m : M) :
    closedHom (coinducedLift g) m =
      freeι h (Y.shiftObj (-1)) (g.hom (M.differential m)) +
        (freeObj h (Y.shiftObj (-1))).differential (freeι h (Y.shiftObj (-1)) (g.hom m)) := by
  dsimp only [coinducedLift]
  rw [closedHom_closedHomOf]
  rfl

private theorem hom_freeUnit_comp_freeProj_apply
    (V : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (v : V) :
    (freeProj h V).hom (freeι h V v) = 0 := by
  have hv := congrArg (fun φ : V ⟶ V.shiftObj 1 ↦ φ.hom v) (freeUnit_comp_freeProj h V)
  simpa only [GradedModuleCat.hom_comp, LinearMap.comp_apply, hom_freeUnit,
    GradedModuleCat.hom_zero, LinearMap.zero_apply] using hv

/-- Forgetting the differential of `coinducedLift g` and postcomposing with `coinducedCounit h Y`
recovers `g`. -/
@[reassoc (attr := simp)]
theorem forgetDifferential_map_coinducedLift_comp_coinducedCounit (g : toGradedModuleCat M ⟶ Y) :
    (forgetDifferential (h := h)).map (coinducedLift g) ≫ coinducedCounit h Y = g := by
  apply GradedModuleCat.hom_ext
  ext m
  have hm := closedHom_coinducedLift_apply g m
  dsimp only [coinducedObj] at hm ⊢
  simp only [coinducedCounit, GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.hom_shiftFunctorZeroIso_hom_app,
    GradedModuleCat.hom_shiftFunctorAddIso_hom_app, LinearMap.id_apply,
    forgetDifferential_map_hom, hm, map_add]
  rw [hom_freeUnit_comp_freeProj_apply, freeProj_differential_freeι_apply, zero_add]

private theorem eq_zero_of_forgetDifferential_map_comp_coinducedCounit_eq_zero
    {θ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y)}
    (hθ : (forgetDifferential (h := h)).map θ ≫ coinducedCounit h Y = 0) :
    θ = 0 := by
  dsimp only [coinducedObj, coinducedCounit] at θ hθ
  have hproj : (forgetDifferential (h := h)).map θ ≫ freeProj h (Y.shiftObj (-1)) = 0 := by
    rw [← Category.assoc] at hθ
    exact (cancel_mono
      ((GradedModuleCat.shiftFunctorAddIso
        (InternalGrading.ofDecomposition 𝒜).opposite.piece (-1) 1).hom.app Y ≫
      (GradedModuleCat.shiftFunctorZeroIso
        (InternalGrading.ofDecomposition 𝒜).opposite.piece).hom.app Y)).mp
      (hθ.trans (zero_comp).symm)
  have hproj_apply (m : M) : (freeProj h (Y.shiftObj (-1))).hom (closedHom θ m) = 0 :=
    congrArg (fun ψ : toGradedModuleCat M ⟶ _ ↦ ψ.hom m) hproj
  apply closedHom_ext
  intro m
  rw [closedHom_zero, LinearMap.zero_apply]
  obtain ⟨u, v, huv⟩ := exists_eq_freeι_add_differential_freeι h (Y.shiftObj (-1)) (closedHom θ m)
  have hv : v = 0 := by
    have h₁ := hproj_apply m
    rw [huv, map_add, hom_freeUnit_comp_freeProj_apply, freeProj_differential_freeι_apply,
      zero_add] at h₁
    exact h₁
  subst hv
  rw [map_zero, map_zero, add_zero] at huv
  have hu : u = 0 := by
    have h₂ := hproj_apply (M.differential m)
    rw [← differential_closedHom, huv, freeProj_differential_freeι_apply] at h₂
    exact h₂
  rw [huv, hu, map_zero]

/-- Closed morphisms into `coinducedObj h Y` are uniquely determined by their postcomposition with
`coinducedCounit h Y`. -/
@[ext]
theorem coinducedObj_hom_ext
    {φ ψ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y)}
    (hφψ : (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y =
      (forgetDifferential (h := h)).map ψ ≫ coinducedCounit h Y) :
    φ = ψ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forgetDifferential_map_comp_coinducedCounit_eq_zero ?_
  rw [Functor.map_sub, Preadditive.sub_comp, sub_eq_zero]
  exact hφψ

/-- Every closed morphism `M ⟶ coinducedObj h Y` is `coinducedLift` of its counit composite. -/
@[simp]
theorem coinducedLift_unique
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y)) :
    coinducedLift ((forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y) = φ :=
  coinducedObj_hom_ext (forgetDifferential_map_coinducedLift_comp_coinducedCounit _)

/-- Lifting `coinducedCounit h Y` itself gives the identity on `coinducedObj h Y`. -/
@[simp]
theorem coinducedLift_coinducedCounit
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedLift (M := coinducedObj h Y) (coinducedCounit h Y) =
      𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y)) :=
  coinducedObj_hom_ext (by
    rw [forgetDifferential_map_coinducedLift_comp_coinducedCounit,
      CategoryTheory.Functor.map_id, Category.id_comp])

/-- Precomposing `coinducedLift g` with a closed morphism `f` lifts
`forgetDifferential.map f ≫ g`. -/
@[reassoc (attr := simp)]
theorem comp_coinducedLift
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)
    (g : toGradedModuleCat M ⟶ Y) :
    f ≫ coinducedLift g = coinducedLift ((forgetDifferential (h := h)).map f ≫ g) :=
  coinducedObj_hom_ext (by
    rw [CategoryTheory.Functor.map_comp, Category.assoc,
      forgetDifferential_map_coinducedLift_comp_coinducedCounit,
      forgetDifferential_map_coinducedLift_comp_coinducedCounit])

/-- The `R`-linear universal property of `coinducedObj h Y`: graded right-linear morphisms
`toGradedModuleCat M ⟶ Y` correspond `R`-linearly to closed morphisms `M ⟶ coinducedObj h Y`. -/
def coinducedHomEquiv
    (M : CurvedDGRightModuleCat.{u, u, u} h)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (toGradedModuleCat M ⟶ Y) ≃ₗ[R]
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y)) :=
  LinearEquiv.symm
    { toFun := fun φ ↦ (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y
      invFun := coinducedLift
      left_inv := coinducedLift_unique
      right_inv := forgetDifferential_map_coinducedLift_comp_coinducedCounit
      map_add' := fun φ ψ ↦ by rw [Functor.map_add, Preadditive.add_comp]
      map_smul' := fun r φ ↦ by rw [Functor.map_smul, Linear.smul_comp, RingHom.id_apply] }

/-- Forward direction of `coinducedHomEquiv`: lift a graded morphism by `coinducedLift`. -/
@[simp]
theorem coinducedHomEquiv_apply (g : toGradedModuleCat M ⟶ Y) :
    coinducedHomEquiv M Y g = coinducedLift g :=
  (rfl)

/-- Inverse direction of `coinducedHomEquiv`: postcompose with `coinducedCounit h Y`. -/
@[simp]
theorem coinducedHomEquiv_symm_apply
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y)) :
    (coinducedHomEquiv M Y).symm φ =
      (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y :=
  (rfl)

/-- Lifting a monomorphism of graded right modules gives a monomorphism in the closed category of
curved right modules. -/
instance mono_coinducedLift_of_mono (g : toGradedModuleCat M ⟶ Y) [Mono g] :
    Mono (coinducedLift g) := by
  have : Mono ((forgetDifferential (h := h)).map (coinducedLift g) ≫ coinducedCounit h Y) := by
    rw [forgetDifferential_map_coinducedLift_comp_coinducedCounit]
    infer_instance
  exact (forgetDifferential (h := h)).mono_of_mono_map (mono_of_mono _ (coinducedCounit h Y))

/-- The **coinduced curved right module functor** (`G⁻`), sending a graded right module to the
curved right module it coinduces. Its object map computes during type inference, matching
`forgetDifferential` and `freeFunctor`, while `coinducedObj` itself remains sealed. -/
@[expose, implicit_reducible]
def coinducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj Y := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y)
  map {Y Z} v := coinducedLift (coinducedCounit h Y ≫ v)
  map_id Y := by
    rw [Category.comp_id, coinducedLift_coinducedCounit]
  map_comp {X Y Z} u v := coinducedObj_hom_ext (by
    rw [CategoryTheory.Functor.map_comp, Category.assoc,
      forgetDifferential_map_coinducedLift_comp_coinducedCounit, ← Category.assoc,
      forgetDifferential_map_coinducedLift_comp_coinducedCounit, ← Category.assoc,
      forgetDifferential_map_coinducedLift_comp_coinducedCounit])

/-- Action of `coinducedFunctor` on objects. -/
@[simp]
theorem coinducedFunctor_obj
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinducedFunctor (h := h)).obj Y =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y) :=
  (rfl)

/-- Action of `coinducedFunctor` on morphisms via `coinducedLift`. -/
theorem coinducedFunctor_map (v : Y ⟶ Z) :
    (coinducedFunctor (h := h)).map v = coinducedLift (coinducedCounit h Y ≫ v) :=
  (rfl)

/-- Naturality of `coinducedCounit` with respect to `coinducedFunctor`. -/
@[reassoc (attr := simp)]
theorem forgetDifferential_map_coinducedFunctor_map_comp_coinducedCounit (v : Y ⟶ Z) :
    (forgetDifferential (h := h)).map ((coinducedFunctor (h := h)).map v) ≫ coinducedCounit h Z =
      coinducedCounit h Y ≫ v :=
  forgetDifferential_map_coinducedLift_comp_coinducedCounit (coinducedCounit h Y ≫ v)

/-- Postcomposing `coinducedLift g` with `coinducedFunctor.map v` lifts `g ≫ v`. -/
@[reassoc (attr := simp)]
theorem coinducedLift_comp_coinducedFunctor_map (g : toGradedModuleCat M ⟶ Y) (v : Y ⟶ Z) :
    coinducedLift g ≫ (coinducedFunctor (h := h)).map v = coinducedLift (g ≫ v) :=
  coinducedObj_hom_ext (by
    rw [CategoryTheory.Functor.map_comp, Category.assoc,
      forgetDifferential_map_coinducedFunctor_map_comp_coinducedCounit, ← Category.assoc,
      forgetDifferential_map_coinducedLift_comp_coinducedCounit,
      forgetDifferential_map_coinducedLift_comp_coinducedCounit])

instance : (coinducedFunctor (h := h)).Additive where
  map_add {Y Z u v} := by
    rw [coinducedFunctor_map, coinducedFunctor_map, coinducedFunctor_map,
      ← coinducedHomEquiv_apply (coinducedCounit h Y ≫ (u + v)),
      ← coinducedHomEquiv_apply (coinducedCounit h Y ≫ u),
      ← coinducedHomEquiv_apply (coinducedCounit h Y ≫ v), Preadditive.comp_add, map_add]

instance : (coinducedFunctor (h := h)).Linear R where
  map_smul {Y Z} v r := by
    rw [coinducedFunctor_map, coinducedFunctor_map,
      ← coinducedHomEquiv_apply (coinducedCounit h Y ≫ (r • v)),
      ← coinducedHomEquiv_apply (coinducedCounit h Y ≫ v), Linear.comp_smul, map_smul]

/-- Forgetting the differential is left adjoint to the coinduced curved right module functor. -/
def forgetDifferentialCoinducedAdjunction :
    forgetDifferential (h := h) ⊣ coinducedFunctor (h := h) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦ (coinducedHomEquiv (ForgetEnrichment.to _ X) Y).toEquiv
      homEquiv_naturality_left_symm := fun _ _ ↦ by
        dsimp [coinducedHomEquiv]
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := fun g v ↦
        (coinducedLift_comp_coinducedFunctor_map g v).symm }

/-- Forward hom-equivalence of `forgetDifferentialCoinducedAdjunction`: lift by `coinducedLift`. -/
@[simp]
theorem forgetDifferentialCoinducedAdjunction_homEquiv_apply (g : toGradedModuleCat M ⟶ Y) :
    (forgetDifferentialCoinducedAdjunction (h := h)).homEquiv
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) Y g =
      coinducedLift g := by
  rw [forgetDifferentialCoinducedAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Inverse hom-equivalence of `forgetDifferentialCoinducedAdjunction`: postcompose with
`coinducedCounit h Y`. -/
@[simp]
theorem forgetDifferentialCoinducedAdjunction_homEquiv_symm_apply
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h Y)) :
    ((forgetDifferentialCoinducedAdjunction (h := h)).homEquiv
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) Y).symm φ =
      (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y := by
  rw [forgetDifferentialCoinducedAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The unit of `forgetDifferentialCoinducedAdjunction` at `M` lifts `𝟙 (toGradedModuleCat M)`. -/
@[simp]
theorem forgetDifferentialCoinducedAdjunction_unit_app (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (forgetDifferentialCoinducedAdjunction (h := h)).unit.app
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
      coinducedLift (𝟙 (toGradedModuleCat M)) :=
  (rfl)

/-- The counit of `forgetDifferentialCoinducedAdjunction` at `Y` is `coinducedCounit h Y`. -/
@[simp]
theorem forgetDifferentialCoinducedAdjunction_counit_app
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (forgetDifferentialCoinducedAdjunction (h := h)).counit.app Y = coinducedCounit h Y := by
  rw [← (forgetDifferentialCoinducedAdjunction (h := h)).homEquiv_symm_id Y]
  dsimp only [coinducedFunctor]
  rw [forgetDifferentialCoinducedAdjunction_homEquiv_symm_apply,
    CategoryTheory.Functor.map_id, Category.id_comp]

instance : (forgetDifferential (h := h)).IsLeftAdjoint :=
  (forgetDifferentialCoinducedAdjunction (h := h)).isLeftAdjoint

instance : (coinducedFunctor (h := h)).IsRightAdjoint :=
  (forgetDifferentialCoinducedAdjunction (h := h)).isRightAdjoint

/-- **Existence of contractible graded-injective embeddings.** Every curved right module embeds in
the closed category into a contractible curved right module whose underlying graded right module is
injective. -/
theorem exists_mono_contractible_gradedInjective (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (Q : CurvedDGRightModuleCat.{u, u, u} h)
      (ι : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q),
      Mono ι ∧ Injective (toGradedModuleCat Q) ∧ IsZero (DGHomotopyCategory.of R Q) :=
  ⟨coinducedObj h (Injective.under (toGradedModuleCat M)),
    coinducedLift (Injective.ι (toGradedModuleCat M)),
    inferInstance, inferInstance, isZero_homotopy_coinducedObj h _⟩

/-- **Dimension shifting along a contractible graded-injective embedding.** If the underlying
graded module of a curved right module `M` has injective dimension `< m + 2`, then `M` is the
kernel of a short exact sequence `M ⟶ Q ⟶ C` of curved modules whose middle term `Q` is zero in
the curved homotopy category and whose cokernel `C` has underlying graded module of injective
dimension `< m + 1`. -/
theorem exists_shortExact_contractible_of_hasInjectiveDimensionLT {m : ℕ}
    (M : CurvedDGRightModuleCat.{u, u, u} h)
    (hM : HasInjectiveDimensionLT (toGradedModuleCat M) (m + 2)) :
    ∃ (Q C : CurvedDGRightModuleCat.{u, u, u} h)
      (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q)
      (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) C)
      (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact ∧ IsZero (DGHomotopyCategory.of R Q) ∧
        HasInjectiveDimensionLT (toGradedModuleCat C) (m + 1) := by
  obtain ⟨Q, f, hf, hQinj, hQ0⟩ := exists_mono_contractible_gradedInjective (R := R) M
  have hS : (ShortComplex.mk f (cokernelπ f) (comp_cokernelπ f)).ShortExact :=
    shortExact_cokernelπ f
  exact ⟨Q, cokernelObj f, f, cokernelπ f, comp_cokernelπ f, hS, hQ0,
    ((hS.map_of_exact (forgetDifferential (h := h))).hasInjectiveDimensionLT_X₃_iff
      m hQinj).mpr hM⟩

end UniversalProperty

end TauCeti.CurvedDGRightModuleCat
