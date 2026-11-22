/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.GradedDimension
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.Algebra.Homology.Curved.Module.Right.Resolution.Basic

/-!
# Product totalizations of left resolutions of curved right modules

Given a left resolution `r` of a curved differential graded right module `M` — a chain of short
exact sequences `0 ⟶ K_{n+1} ⟶ P_n ⟶ K_n ⟶ 0` with `K_0 ≅ M` — its **product totalization**
`Tot^Π(r)` is carried by the degreewise graded product `∏ₙ P_n[n]` with total differential

`(D y)_n = (-1)^n d_{P_n}(y_n) + ι_n(π_{n+1}(y_{n+1}))`,

equipped with the closed augmentation `Tot^Π(r) ⟶ M` given by `π_0` on the `0`-th coordinate
composed with `K_0 ≅ M`.

The main theorem is that the mapping cone of `Tot^Π(r) ⟶ M` is contraacyclic. Following
Positselski's Milnor-tower argument, we build inductively a sequence of partial totalizations
`G_k` with closed maps `β_k : K_k[k] ⟶ G_k` and finite truncations `F_k = cone(β_k)` linked by
degreewise-surjective transitions `t_k : F_{k+1} ⟶ F_k`. Each transition has contractible kernel
`cone(𝟙 (K_{k+1}[k+1]))`, so every `F_k` is contraacyclic by induction on `k`. Assembling the
tower into the Milnor short exact sequence `0 ⟶ cone(aug) ⟶ ∏ₖ F_k ⟶ ∏ₖ F_k ⟶ 0` in the closed
abelian category yields contraacyclicity of `cone(aug)` from closure of `contraacyclic` under
countable products and kernels of epimorphisms.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.LeftResolution.prodTotal`: the product totalization `Tot^Π(r)`
  of a left resolution `r`.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.prodTotalProj`: the `n`-th coordinate
  projection `Tot^Π(r) →ₗ[Aᵐᵒᵖ] P_n`.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.prodTotalToGradedIso`: the graded isomorphism
  identifying `toGradedModuleCat r.prodTotal` with the degreewise graded product `∏ₙ P_n[n]`.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.prodTotalToPiIso`: the categorical product
  isomorphism `toGradedModuleCat r.prodTotal ≅ ∏ᶜ (fun n ↦ toGradedModuleCat ((r.term n)[n]))`.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.prodTotalAug`: the closed augmentation morphism
  `Tot^Π(r) ⟶ M`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.LeftResolution.contraacyclic_cone_prodTotalAug`: the mapping
  cone of the augmentation `Tot^Π(r) ⟶ M` of any left resolution is contraacyclic.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.9, Theorem 7.9(b).
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DirectSum MulOpposite
open scoped Pointwise

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment EnrichedFunctor.ofDGMap
  dgClosedToHomotopy DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

local instance : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

namespace LeftResolution

variable {M : CurvedDGRightModuleCat.{u, u, u} h} (r : LeftResolution M)

/-! ### Product totalization and augmentation -/

/-- The horizontal component `(H y)_n = δ_n(y_{n+1})` of the total differential on the degreewise
graded product `∏ₙ P_n[n]`. -/
private noncomputable def prodTotalHorizontalDiff :
    product (fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)) →ₗ[R]
      product (fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)) :=
  InternalGrading.productLiftLinear
    (fun n : ULift.{u} ℕ ↦ (toGradedModuleCat ((r.term n.down).shift (n.down : ℤ))).grading)
    (GradedModuleCat.product fun n : ULift.{u} ℕ ↦
      toGradedModuleCat ((r.term n.down).shift (n.down : ℤ))).grading 1
    (fun n ↦
      ((closedHom (r.diff n.down)).restrictScalars R).comp
        (InternalGrading.productEval _ (ULift.up (n.down + 1))))
    (fun n ↦ by
      rw [LinearMap.isHomogeneous_def]
      intro p y hy
      have hy1 : y.val (ULift.up (n.down + 1)) ∈
          (r.term (n.down + 1)).grading (p + ((n.down + 1 : ℕ) : ℤ)) := by
        simpa only [toGradedModuleCat_piece, shift_grading] using
          (GradedModuleCat.mem_product_piece_iff _ p y).mp hy (ULift.up (n.down + 1))
      rw [toGradedModuleCat_piece, LinearMap.comp_apply, InternalGrading.productEval_apply,
        LinearMap.restrictScalars_apply, shift_grading]
      have hmem := closedHom_mem (r.diff n.down) hy1
      have heq : p + ((n.down + 1 : ℕ) : ℤ) = p + 1 + (n.down : ℤ) := by push_cast; omega
      rwa [heq] at hmem)

private theorem prodTotalHorizontalDiff_apply
    (y : product fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)) (n : ℕ) :
    (r.prodTotalHorizontalDiff y).val ⟨n⟩ =
      closedHom (r.diff n) (y.val ⟨n + 1⟩) := by
  dsimp only [prodTotalHorizontalDiff]
  rw [InternalGrading.productLiftLinear_apply, LinearMap.comp_apply,
    InternalGrading.productEval_apply, LinearMap.restrictScalars_apply]

private theorem prodTotalHorizontalDiff_isHomogeneous :
    LinearMap.IsHomogeneous r.prodTotalHorizontalDiff
      (product fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)).grading
      (product fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)).grading 1 := by
  dsimp only [prodTotalHorizontalDiff]
  exact InternalGrading.productLiftLinear_isHomogeneous _ _ 1 _ _

/-- The **product totalization** `Tot^Π(r)` of a left resolution `r`: carried by the degreewise
graded product `∏ₙ P_n[n]` with differential `(D y)_n = (-1)^n d_{P_n}(y_n) + δ_n(y_{n+1})`. -/
noncomputable def prodTotal : CurvedDGRightModuleCat.{u, u, u} h := by
  let B := product fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)
  letI : DirectSum.Decomposition B.grading := B.decomposition
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece B.grading :=
    B.gradedSMul
  refine
    { carrier := B
      grading := B.grading
      differential := B.differential + r.prodTotalHorizontalDiff
      isCurvedDGRightModule := ⟨?_, ?_, ?_⟩ }
  · rw [LinearMap.isHomogeneous_def]
    intro p y hy
    rw [LinearMap.add_apply]
    exact (B.grading (p + 1)).add_mem
      (B.isCurvedDGRightModule.isHomogeneous.map_mem hy)
      (r.prodTotalHorizontalDiff_isHomogeneous.map_mem hy)
  · intro p y hy a
    rw [LinearMap.add_apply, LinearMap.add_apply, B.isCurvedDGRightModule.leibniz hy a]
    have hhor : r.prodTotalHorizontalDiff (op a • y) = op a • r.prodTotalHorizontalDiff y := by
      apply Subtype.ext
      funext ⟨n⟩
      change (r.prodTotalHorizontalDiff (op a • y)).val ⟨n⟩ =
        op a • (r.prodTotalHorizontalDiff y).val ⟨n⟩
      rw [prodTotalHorizontalDiff_apply, prodTotalHorizontalDiff_apply]
      exact map_smul (closedHom (r.diff n)) (op a) (y.val ⟨n + 1⟩)
    rw [hhor, smul_add]
    abel
  · intro y
    apply Subtype.ext
    funext ⟨n⟩
    have hsq := congrArg (fun z ↦ z.val ⟨n⟩) (B.isCurvedDGRightModule.sq_eq y)
    dsimp only [B] at hsq ⊢
    simp only [LinearMap.add_apply, map_add]
    rw [Submodule.coe_add, Submodule.coe_add, Submodule.coe_add,
      Pi.add_apply, Pi.add_apply, Pi.add_apply,
      hsq, product_differential_apply, shift_differential_apply, prodTotalHorizontalDiff_apply,
      prodTotalHorizontalDiff_apply, product_differential_apply, shift_differential_apply,
      prodTotalHorizontalDiff_apply, prodTotalHorizontalDiff_apply]
    have hdd : closedHom (r.diff n) (closedHom (r.diff (n + 1)) (y.val ⟨n + 2⟩)) = 0 := by
      rw [← LinearMap.comp_apply, ← closedHom_comp, r.diff_comp_diff, closedHom_zero,
        LinearMap.zero_apply]
    have hcancel :
        closedHom (r.diff n)
            (((n + 1 : ℕ) : ℤ).negOnePow • (r.term (n + 1)).differential (y.val ⟨n + 1⟩)) +
          (n : ℤ).negOnePow •
            (r.term n).differential (closedHom (r.diff n) (y.val ⟨n + 1⟩)) = 0 := by
      simp only [Units.smul_def, Nat.cast_add, Nat.cast_one, Int.negOnePow_add,
        Int.negOnePow_one, mul_neg_one, Units.val_neg, neg_zsmul, map_neg, map_zsmul,
        differential_closedHom, neg_add_cancel]
    dsimp only
    rw [hdd, add_zero, add_assoc, hcancel, add_zero]

private noncomputable def prodTotalEquiv :
    r.prodTotal ≃ₗ[Aᵐᵒᵖ] product fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ) :=
  LinearEquiv.refl Aᵐᵒᵖ _

private theorem prodTotalEquiv_mem_iff (p : ℤ) (y : r.prodTotal) :
    y ∈ r.prodTotal.grading p ↔
      r.prodTotalEquiv y ∈
        (product fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)).grading p :=
  Iff.rfl

private theorem prodTotalEquiv_differential (y : r.prodTotal) :
    r.prodTotalEquiv (r.prodTotal.differential y) =
      (product fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)).differential
          (r.prodTotalEquiv y) +
        r.prodTotalHorizontalDiff (r.prodTotalEquiv y) :=
  rfl

/-- The `n`-th coordinate projection `Tot^Π(r) →ₗ[Aᵐᵒᵖ] P_n` out of the product totalization. -/
noncomputable def prodTotalProj (n : ℕ) : r.prodTotal →ₗ[Aᵐᵒᵖ] r.term n :=
  (GradedModuleCat.productπ
    (fun k : ULift.{u} ℕ ↦ toGradedModuleCat ((r.term k.down).shift (k.down : ℤ))) ⟨n⟩).hom.comp
    r.prodTotalEquiv.toLinearMap

private theorem prodTotalProj_eq_val (n : ℕ) (y : r.prodTotal) :
    r.prodTotalProj n y = (r.prodTotalEquiv y).val ⟨n⟩ := by
  dsimp only [prodTotalProj]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact GradedModuleCat.productπ_apply
    (fun k : ULift.{u} ℕ ↦ toGradedModuleCat ((r.term k.down).shift (k.down : ℤ)))
    ⟨n⟩ (r.prodTotalEquiv y)

/-- Elements of `r.prodTotal` are determined by their coordinate projections. -/
theorem prodTotal_ext {x y : r.prodTotal}
    (hxy : ∀ n : ℕ, r.prodTotalProj n x = r.prodTotalProj n y) : x = y := by
  apply r.prodTotalEquiv.injective
  apply Subtype.ext
  funext ⟨n⟩
  simpa only [prodTotalProj_eq_val] using hxy n

/-- Homogeneity in `r.prodTotal` is checked componentwise in each shifted term `(r.term n)[n]`. -/
@[simp]
theorem mem_prodTotal_grading_iff (p : ℤ) (y : r.prodTotal) :
    y ∈ r.prodTotal.grading p ↔ ∀ n : ℕ, r.prodTotalProj n y ∈ (r.term n).grading (p + n) := by
  rw [prodTotalEquiv_mem_iff, mem_product_grading_iff]
  exact ⟨fun hy n ↦ by simpa only [shift_grading, prodTotalProj_eq_val] using hy ⟨n⟩,
    fun hy ⟨n⟩ ↦ by simpa only [shift_grading, prodTotalProj_eq_val] using hy n⟩

/-- The `n`-th component of the differential on `r.prodTotal`. -/
@[simp]
theorem prodTotal_differential_apply (y : r.prodTotal) (n : ℕ) :
    r.prodTotalProj n (r.prodTotal.differential y) =
      (n : ℤ).negOnePow • (r.term n).differential (r.prodTotalProj n y) +
        closedHom (r.diff n) (r.prodTotalProj (n + 1) y) := by
  rw [prodTotalProj_eq_val, prodTotalEquiv_differential, Submodule.coe_add, Pi.add_apply,
    product_differential_apply, shift_differential_apply, prodTotalHorizontalDiff_apply,
    prodTotalProj_eq_val, prodTotalProj_eq_val]

private noncomputable def prodTotalToProductGradedIso :
    toGradedModuleCat r.prodTotal ≅
      toGradedModuleCat (product fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)) :=
  GradedModuleCat.isoMk r.prodTotalEquiv fun p y ↦ by
    simpa only [toGradedModuleCat_piece] using r.prodTotalEquiv_mem_iff p y

/-- Forgetting the differential of `r.prodTotal` recovers the degreewise graded product
`∏ₙ toGradedModuleCat ((r.term n)[n])`. -/
noncomputable def prodTotalToGradedIso :
    toGradedModuleCat r.prodTotal ≅
      GradedModuleCat.product fun n : ULift.{u} ℕ ↦
        toGradedModuleCat ((r.term n.down).shift (n.down : ℤ)) :=
  r.prodTotalToProductGradedIso ≪≫
    forgetDifferentialProductIso fun n : ULift.{u} ℕ ↦ (r.term n.down).shift (n.down : ℤ)

/-- On elements, each coordinate of `prodTotalToGradedIso.hom` is `prodTotalProj`. -/
@[simp]
theorem prodTotalToGradedIso_hom_apply_val (y : toGradedModuleCat r.prodTotal) (n : ULift.{u} ℕ) :
    (r.prodTotalToGradedIso.hom.hom y).val n = r.prodTotalProj n.down y := by
  rw [prodTotalToGradedIso, Iso.trans_hom, GradedModuleCat.hom_comp, LinearMap.comp_apply,
    forgetDifferentialProductIso_hom_hom, LinearMap.id_apply, prodTotalProj_eq_val]
  rfl

/-- On elements, `prodTotalToGradedIso.inv` has the given coordinate projections. -/
@[simp]
theorem prodTotalToGradedIso_inv_apply (n : ℕ)
    (y : GradedModuleCat.product fun k : ULift.{u} ℕ ↦
      toGradedModuleCat ((r.term k.down).shift (k.down : ℤ))) :
    r.prodTotalProj n (r.prodTotalToGradedIso.inv.hom y) = y.val ⟨n⟩ := by
  rw [prodTotalToGradedIso, Iso.trans_inv, GradedModuleCat.hom_comp, LinearMap.comp_apply,
    forgetDifferentialProductIso_inv_hom, LinearMap.id_apply, prodTotalProj_eq_val]
  rfl

/-- The underlying graded right module of `r.prodTotal` is isomorphic to the categorical product
`∏ᶜ (fun n : ULift ℕ ↦ toGradedModuleCat ((r.term n.down)[n.down]))`. -/
noncomputable def prodTotalToPiIso :
    toGradedModuleCat r.prodTotal ≅
      ∏ᶜ fun n : ULift.{u} ℕ ↦ toGradedModuleCat ((r.term n.down).shift (n.down : ℤ)) :=
  r.prodTotalToGradedIso ≪≫
    (limit.isoLimitCone
      ⟨GradedModuleCat.degreewiseProductFan _,
        GradedModuleCat.degreewiseProductFanIsLimit _⟩).symm

/-- Composing `prodTotalToPiIso.hom` with the `n`-th categorical product projection gives the
`n`-th degreewise product projection composed with `prodTotalToGradedIso.hom`. -/
@[reassoc (attr := simp)]
theorem prodTotalToPiIso_hom_comp_π (n : ULift.{u} ℕ) :
    r.prodTotalToPiIso.hom ≫
        Pi.π (fun k : ULift.{u} ℕ ↦
          toGradedModuleCat ((r.term k.down).shift (k.down : ℤ))) n =
      r.prodTotalToGradedIso.hom ≫ GradedModuleCat.productπ _ n := by
  simp only [prodTotalToPiIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    limit.isoLimitCone_inv_π]
  rfl

/-- On elements, composing `prodTotalToPiIso.hom` with the `n`-th categorical product projection
reads off the `n`-th coordinate of `y` via `prodTotalProj`. -/
@[simp]
theorem prodTotalToPiIso_hom_apply_π (n : ULift.{u} ℕ) (y : toGradedModuleCat r.prodTotal) :
    (Pi.π (fun k : ULift.{u} ℕ ↦
        toGradedModuleCat ((r.term k.down).shift (k.down : ℤ))) n).hom
      (r.prodTotalToPiIso.hom.hom y) = r.prodTotalProj n.down y := by
  have h := congrArg (fun f ↦ f.hom y) (r.prodTotalToPiIso_hom_comp_π n)
  simpa only [GradedModuleCat.hom_comp, LinearMap.comp_apply, GradedModuleCat.productπ_apply,
    prodTotalToGradedIso_hom_apply_val] using h

/-- The closed augmentation `r.prodTotal ⟶ r.syzygy 0`, given by `π_0` on the `0`-th factor. -/
private noncomputable def prodTotalAugZero :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) r.prodTotal ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.syzygy 0) :=
  closedHomOf ((closedHom (r.π 0)).comp (r.prodTotalProj 0))
    (fun p y hy ↦ by
      rw [LinearMap.comp_apply]
      have h0 : r.prodTotalProj 0 y ∈ (r.term 0).grading p := by
        simpa only [Nat.cast_zero, add_zero] using (r.mem_prodTotal_grading_iff p y).mp hy 0
      exact closedHom_mem (r.π 0) h0)
    (fun y ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, differential_closedHom,
        prodTotal_differential_apply, Nat.cast_zero, Int.negOnePow_zero, one_smul, map_add]
      have h0 : closedHom (r.π 0) (closedHom (r.diff 0) (r.prodTotalProj 1 y)) = 0 := by
        rw [← LinearMap.comp_apply, ← closedHom_comp, r.diff_comp_π 0, closedHom_zero,
          LinearMap.zero_apply]
      rw [h0, add_zero])

/-- On elements, `prodTotalAugZero` applies `π_0` to the `0`-th coordinate. -/
private theorem closedHom_prodTotalAugZero_apply (y : r.prodTotal) :
    closedHom r.prodTotalAugZero y = closedHom (r.π 0) (r.prodTotalProj 0 y) := by
  dsimp only [prodTotalAugZero]
  rw [closedHom_closedHomOf, LinearMap.comp_apply]

/-- The closed augmentation `r.prodTotal ⟶ M` of a left resolution. -/
noncomputable def prodTotalAug :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) r.prodTotal ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  r.prodTotalAugZero ≫ r.syzygyZeroIso.hom

/-- On elements, `prodTotalAug` applies `π_0` to the `0`-th coordinate followed by
`syzygyZeroIso.hom`. -/
@[simp]
theorem closedHom_prodTotalAug_apply (y : r.prodTotal) :
    closedHom r.prodTotalAug y =
      closedHom r.syzygyZeroIso.hom (closedHom (r.π 0) (r.prodTotalProj 0 y)) := by
  simp [prodTotalAug, closedHom_prodTotalAugZero_apply]

/-! ### Truncation tower and contraacyclicity of `cone prodTotalAug` -/

section MilnorTower

/-- Recursive construction of the partial totalization `G_k` together with the connecting closed
morphism `β_k : K_k[k] ⟶ G_k`:
* `G_0 = K_0` with `β_0 = closedShiftZeroIso K_0`;
* `G_{k+1} = cone(π_k[k] ≫ β_k)` with `β_{k+1}(x) = (-ι_k(x), 0)`. -/
private noncomputable def partialData :
    (k : ℕ) →
      Σ G : CurvedDGRightModuleCat.{u, u, u} h,
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ)) ⟶
          ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) G
  | 0 => ⟨r.syzygy 0, (closedShiftZeroIso (r.syzygy 0)).hom⟩
  | k + 1 =>
      let prev := partialData k
      let G := prev.1
      let β := prev.2
      let step : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
            ((r.term k).shift (k : ℤ)) ⟶
          ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) G :=
        ((closedShiftFunctor (h := h) (k : ℤ)).map (r.π k) :
          ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.term k).shift (k : ℤ)) ⟶
            ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ))) ≫ β
      let ιLin : ((r.syzygy (k + 1)).shift ((k + 1 : ℕ) : ℤ)).carrier →ₗ[Aᵐᵒᵖ]
          ((r.term k).shift (k : ℤ)).carrier :=
        (closedHom (r.ι k) : (r.syzygy (k + 1)).carrier →ₗ[Aᵐᵒᵖ] (r.term k).carrier)
      ⟨cone step,
        closedHomOf
          (-(LinearMap.inl Aᵐᵒᵖ ((r.term k).shift (k : ℤ)) G).comp ιLin)
          (fun p x hx ↦ by
            rw [shift_grading] at hx
            rw [cone_grading, Submodule.mem_prod, LinearMap.neg_apply, LinearMap.comp_apply,
              LinearMap.inl_apply, Prod.neg_mk, neg_zero, shift_grading]
            refine ⟨((r.term k).grading (p + 1 + (k : ℤ))).neg_mem ?_, (G.grading p).zero_mem⟩
            dsimp only [ιLin]
            have hmem := closedHom_mem (r.ι k) hx
            have heq : p + ((k + 1 : ℕ) : ℤ) = p + 1 + (k : ℤ) := by push_cast; omega
            rwa [heq] at hmem)
          (fun x ↦ by
            rw [LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.comp_apply,
              LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inl_apply, Prod.neg_mk,
              Prod.neg_mk, neg_zero, cone_differential_apply]
            dsimp only [ιLin]
            have h0 : closedHom step (closedHom (r.ι k) x) = 0 := by
              simp only [step, closedHom_comp, LinearMap.comp_apply,
                closedHom_closedShiftFunctor_map]
              have hιπ : closedHom (r.π k) (closedHom (r.ι k) x) = 0 := by
                rw [← LinearMap.comp_apply, ← closedHom_comp, r.ι_comp_π k, closedHom_zero,
                  LinearMap.zero_apply]
              rw [hιπ, map_zero]
            rw [shift_differential_apply, shift_differential_apply, map_neg, map_neg, h0, neg_zero,
              map_zero, add_zero]
            apply Prod.ext
            · simp only [Nat.cast_add, Nat.cast_one, Int.negOnePow_add, Int.negOnePow_one,
                mul_neg_one, Units.smul_def, Units.val_neg, neg_zsmul, smul_neg, neg_neg,
                map_neg, map_zsmul, differential_closedHom]
            · rfl)⟩

/-- The `k`-th partial totalization object `G_k`. -/
private noncomputable abbrev partialObj (k : ℕ) : CurvedDGRightModuleCat.{u, u, u} h :=
  (r.partialData k).fst

/-- The `k`-th connecting closed morphism `β_k : K_k[k] ⟶ G_k`. -/
private noncomputable abbrev partialMap (k : ℕ) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ)) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.partialObj k) :=
  (r.partialData k).snd

/-- First coordinate projection `G_{k+1} →ₗ[Aᵐᵒᵖ] P_k[k]`. -/
private noncomputable def partialFst (k : ℕ) :
    r.partialObj (k + 1) →ₗ[Aᵐᵒᵖ] (r.term k).shift (k : ℤ) :=
  LinearMap.fst Aᵐᵒᵖ ((r.term k).shift (k : ℤ)) (r.partialObj k)

/-- Second coordinate projection `G_{k+1} →ₗ[Aᵐᵒᵖ] G_k`. -/
private noncomputable def partialSnd (k : ℕ) :
    r.partialObj (k + 1) →ₗ[Aᵐᵒᵖ] r.partialObj k :=
  LinearMap.snd Aᵐᵒᵖ ((r.term k).shift (k : ℤ)) (r.partialObj k)

/-- Pairing `(y, g) ∈ P_k[k] × G_k` as an element of `G_{k+1}`. -/
private noncomputable def partialMk (k : ℕ) (y : (r.term k).shift (k : ℤ)) (g : r.partialObj k) :
    r.partialObj (k + 1) :=
  (y, g)

private theorem partialFst_partialMk (k : ℕ) (y : (r.term k).shift (k : ℤ)) (g : r.partialObj k) :
    r.partialFst k (r.partialMk k y g) = y := rfl

private theorem partialSnd_partialMk (k : ℕ) (y : (r.term k).shift (k : ℤ)) (g : r.partialObj k) :
    r.partialSnd k (r.partialMk k y g) = g := rfl

private theorem partial_ext (k : ℕ) {a b : r.partialObj (k + 1)}
    (h1 : r.partialFst k a = r.partialFst k b)
    (h2 : r.partialSnd k a = r.partialSnd k b) : a = b :=
  Prod.ext h1 h2

private theorem partialFst_differential (k : ℕ) (g : r.partialObj (k + 1)) :
    r.partialFst k ((r.partialObj (k + 1)).differential g) =
      -((k : ℤ).negOnePow • (r.term k).differential (r.partialFst k g)) := by
  have h1 := congrArg Prod.fst
    (cone_differential_apply
      (M := (r.term k).shift (k : ℤ))
      (f := ((closedShiftFunctor (h := h) (k : ℤ)).map (r.π k) :
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.term k).shift (k : ℤ)) ⟶
          ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ))) ≫
        r.partialMap k) g)
  rw [shift_differential_apply] at h1
  exact h1

private theorem partialSnd_differential (k : ℕ) (g : r.partialObj (k + 1)) :
    r.partialSnd k ((r.partialObj (k + 1)).differential g) =
      closedHom (r.partialMap k) (closedHom (r.π k) (r.partialFst k g)) +
        (r.partialObj k).differential (r.partialSnd k g) := by
  have h2 := congrArg Prod.snd
    (cone_differential_apply
      (f := ((closedShiftFunctor (h := h) (k : ℤ)).map (r.π k) :
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.term k).shift (k : ℤ)) ⟶
          ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ))) ≫
        r.partialMap k) g)
  dsimp only at h2
  rw [closedHom_comp, LinearMap.comp_apply, closedHom_closedShiftFunctor_map] at h2
  exact h2

private theorem mem_partialObj_succ_grading_iff (k : ℕ) (p : ℤ) (g : r.partialObj (k + 1)) :
    g ∈ (r.partialObj (k + 1)).grading p ↔
      r.partialFst k g ∈ (r.term k).grading (p + 1 + (k : ℤ)) ∧
        r.partialSnd k g ∈ (r.partialObj k).grading p := by
  dsimp only [partialObj, partialData, partialFst, partialSnd]
  rw [cone_grading, shift_grading]
  rfl

private theorem closedHom_partialMap_zero (x : r.syzygy 0) :
    closedHom (r.partialMap 0) x = x :=
  LinearMap.congr_fun (closedHom_closedShiftZeroIso_hom (r.syzygy 0)) x

private theorem closedHom_partialMap_succ (k : ℕ) (x : r.syzygy (k + 1)) :
    closedHom (r.partialMap (k + 1)) x = r.partialMk k (-closedHom (r.ι k) x) 0 := by
  have h : closedHom (r.partialData (k + 1)).snd =
      -(LinearMap.inl Aᵐᵒᵖ ((r.term k).shift (k : ℤ)) (r.partialObj k)).comp
        ((closedHom (r.ι k) : (r.syzygy (k + 1)).carrier →ₗ[Aᵐᵒᵖ] (r.term k).carrier) :
          ((r.syzygy (k + 1)).shift ((k + 1 : ℕ) : ℤ)).carrier →ₗ[Aᵐᵒᵖ]
            ((r.term k).shift (k : ℤ)).carrier) :=
    closedHom_closedHomOf _ _ _
  exact (LinearMap.congr_fun h x).trans (r.partial_ext k rfl neg_zero)

/-- The `k`-th truncation `F_k = cone(β_k)` in the Milnor tower of `cone(prodTotalAugZero)`. -/
private noncomputable abbrev truncObj (k : ℕ) : CurvedDGRightModuleCat.{u, u, u} h :=
  cone (r.partialMap k)

/-- The closed morphism `G_{k+1} ⟶ F_k` sending `(y_k, g_k)` to `(π_k(y_k), g_k)`. -/
private noncomputable def partialStepToTrunc (k : ℕ) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.partialObj (k + 1)) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.truncObj k) :=
  coneMap
    (((closedShiftFunctor (h := h) (k : ℤ)).map (r.π k) :
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.term k).shift (k : ℤ)) ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ))) ≫
      r.partialMap k)
    (r.partialMap k)
    ((closedShiftFunctor (h := h) (k : ℤ)).map (r.π k) :
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.term k).shift (k : ℤ)) ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ)))
    (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.partialObj k)))
    0 (by intro x; simp)

private theorem closedHom_partialStepToTrunc_apply (k : ℕ) (g : r.partialObj (k + 1)) :
    closedHom (r.partialStepToTrunc k) g =
      (closedHom (r.π k) (r.partialFst k g), r.partialSnd k g) := by
  have hmap := closedHom_coneMap_apply
    (f := ((closedShiftFunctor (h := h) (k : ℤ)).map (r.π k) :
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.term k).shift (k : ℤ)) ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ))) ≫
      r.partialMap k)
    (g := r.partialMap k)
    (a := ((closedShiftFunctor (h := h) (k : ℤ)).map (r.π k) :
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.term k).shift (k : ℤ)) ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) ((r.syzygy k).shift (k : ℤ))))
    (b := 𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.partialObj k)))
    (k := 0) (hsq := by intro x; simp) g
  simp only [closedHom_closedShiftFunctor_map, closedHom_id, LinearMap.id_apply,
    Submodule.coe_zero, LinearMap.zero_apply, add_zero] at hmap
  exact hmap

private theorem partialMap_comp_partialStepToTrunc (k : ℕ) :
    r.partialMap (k + 1) ≫ r.partialStepToTrunc k = 0 := by
  apply closedHom_ext
  intro x
  rw [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply,
    r.closedHom_partialMap_succ, r.closedHom_partialStepToTrunc_apply, r.partialFst_partialMk,
    r.partialSnd_partialMk, map_neg]
  have hιπ : closedHom (r.π k) (closedHom (r.ι k) x) = 0 := by
    rw [← LinearMap.comp_apply, ← closedHom_comp, r.ι_comp_π k, closedHom_zero,
      LinearMap.zero_apply]
  rw [hιπ, neg_zero]
  rfl

/-- The transition morphism `t_k : F_{k+1} ⟶ F_k`, sending `(x_{k+1}, (y_k, g_k))` to
`(π_k(y_k), g_k)`. -/
private noncomputable def truncTransition (k : ℕ) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.truncObj (k + 1)) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.truncObj k) :=
  coneDesc (r.partialMap (k + 1)) (r.partialStepToTrunc k)
    (r.partialMap_comp_partialStepToTrunc k)

private theorem closedHom_truncTransition_apply (k : ℕ) (z : r.truncObj (k + 1)) :
    closedHom (r.truncTransition k) z =
      (closedHom (r.π k) (r.partialFst k z.2), r.partialSnd k z.2) := by
  dsimp only [truncTransition]
  rw [closedHom_coneDesc, LinearMap.comp_apply, LinearMap.snd_apply,
    r.closedHom_partialStepToTrunc_apply]

/-- The closed inclusion `cone(𝟙 (K_{k+1}[k+1])) ⟶ F_{k+1}` identifying the kernel of
`truncTransition k`. -/
private noncomputable def truncKernelMap (k : ℕ) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
        (cone (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
          ((r.syzygy (k + 1)).shift ((k + 1 : ℕ) : ℤ))))) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.truncObj (k + 1)) :=
  coneMap (𝟙 _) (r.partialMap (k + 1)) (𝟙 _) (r.partialMap (k + 1)) 0 (by intro x; simp)

private theorem truncKernelMap_comp_truncTransition (k : ℕ) :
    r.truncKernelMap k ≫ r.truncTransition k = 0 := by
  apply closedHom_ext
  rintro ⟨x₁, x₂⟩
  rw [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
  dsimp only [truncKernelMap, truncTransition]
  rw [closedHom_coneMap_apply, closedHom_coneDesc, LinearMap.comp_apply, LinearMap.snd_apply]
  simp only [Submodule.coe_zero, LinearMap.zero_apply, add_zero]
  rw [← LinearMap.comp_apply, ← closedHom_comp, r.partialMap_comp_partialStepToTrunc k,
    closedHom_zero, LinearMap.zero_apply]

/-- Each transition `t_k : F_{k+1} ⟶ F_k` has contractible kernel `cone(𝟙 (K_{k+1}[k+1]))`. -/
private theorem truncTransition_shortExact (k : ℕ) :
    (ShortComplex.mk (r.truncKernelMap k) (r.truncTransition k)
      (r.truncKernelMap_comp_truncTransition k)).ShortExact := by
  refine shortExact_iff.2 ⟨?_, ?_, ?_⟩
  · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hz
    dsimp only [ShortComplex.mk, truncKernelMap] at hz
    rw [closedHom_coneMap_apply, closedHom_coneMap_apply] at hz
    simp only [closedHom_id, LinearMap.id_apply, Submodule.coe_zero, LinearMap.zero_apply,
      add_zero] at hz
    have h1 : a₁ = a₂ := congrArg Prod.fst hz
    have h2 : closedHom (r.partialMap (k + 1)) b₁ = closedHom (r.partialMap (k + 1)) b₂ :=
      congrArg Prod.snd hz
    rw [r.closedHom_partialMap_succ, r.closedHom_partialMap_succ] at h2
    have h2' : -closedHom (r.ι k) b₁ = -closedHom (r.ι k) b₂ := by
      simpa only [r.partialFst_partialMk] using congrArg (r.partialFst k) h2
    exact Prod.ext h1 (r.injective_ι k (neg_inj.mp h2'))
  · intro w
    dsimp only [ShortComplex.mk]
    obtain ⟨y, hy⟩ := r.surjective_π k w.1
    refine ⟨(0, r.partialMk k y w.2), ?_⟩
    rw [r.closedHom_truncTransition_apply, r.partialFst_partialMk, r.partialSnd_partialMk, hy]
    exact Prod.mk.eta
  · rintro ⟨x, g⟩
    dsimp only [ShortComplex.mk]
    rw [r.closedHom_truncTransition_apply]
    constructor
    · intro hz
      have hπ : closedHom (r.π k) (r.partialFst k g) = 0 := congrArg Prod.fst hz
      have hg : r.partialSnd k g = 0 := congrArg Prod.snd hz
      obtain ⟨b, hb⟩ := (r.exact_ι_π k (r.partialFst k g)).1 hπ
      refine ⟨(x, -b), ?_⟩
      dsimp only [truncKernelMap]
      rw [closedHom_coneMap_apply]
      simp only [closedHom_id, LinearMap.id_apply, Submodule.coe_zero, LinearMap.zero_apply,
        add_zero]
      congr 1
      rw [r.closedHom_partialMap_succ, map_neg, neg_neg, hb]
      exact r.partial_ext k rfl hg.symm
    · rintro ⟨u, hu⟩
      have h0 := congrArg (fun l ↦ closedHom l u) (r.truncKernelMap_comp_truncTransition k)
      rw [closedHom_comp, LinearMap.comp_apply, hu, closedHom_zero, LinearMap.zero_apply,
        r.closedHom_truncTransition_apply] at h0
      exact h0

/-- Every truncation `F_k` in the Milnor tower is contraacyclic. -/
private theorem contraacyclic_truncObj (k : ℕ) :
    contraacyclic R h (DGHomotopyCategory.of R (r.truncObj k)) := by
  induction k with
  | zero =>
    have : IsIso (r.partialMap 0) :=
      (inferInstance : IsIso (closedShiftZeroIso (r.syzygy 0)).hom)
    exact (contraacyclic R h).prop_of_isZero (isZero_homotopy_cone_isIso (r.partialMap 0))
  | succ k ih =>
    exact prop_X₂_of_shortExact (contraacyclic R h) (totalizations_le_contraacyclic R h)
      (r.truncTransition_shortExact k)
      ((contraacyclic R h).prop_of_isZero (isZero_homotopy_cone_isIso _)) ih

/-- The recursive right-linear projection `cone(prodTotalAugZero) →ₗ[Aᵐᵒᵖ] G_k`. -/
private noncomputable def coneToPartial :
    (k : ℕ) → cone r.prodTotalAugZero →ₗ[Aᵐᵒᵖ] r.partialObj k
  | 0 => LinearMap.snd Aᵐᵒᵖ r.prodTotal (r.syzygy 0)
  | k + 1 =>
      ((r.prodTotalProj k).comp
        (LinearMap.fst Aᵐᵒᵖ r.prodTotal (r.syzygy 0))).prod (coneToPartial k)

private theorem partialFst_coneToPartial_succ (k : ℕ) (u : cone r.prodTotalAugZero) :
    r.partialFst k (r.coneToPartial (k + 1) u) = r.prodTotalProj k u.1 :=
  rfl

private theorem partialSnd_coneToPartial_succ (k : ℕ) (u : cone r.prodTotalAugZero) :
    r.partialSnd k (r.coneToPartial (k + 1) u) = r.coneToPartial k u := rfl

private theorem coneToPartial_mem {p : ℤ} {u : cone r.prodTotalAugZero}
    (hu : u ∈ (cone r.prodTotalAugZero).grading p) (k : ℕ) :
    r.coneToPartial k u ∈ (r.partialObj k).grading p := by
  induction k with
  | zero =>
    rw [cone_grading] at hu
    exact hu.2
  | succ k ih =>
    rw [cone_grading] at hu
    rw [r.mem_partialObj_succ_grading_iff, r.partialFst_coneToPartial_succ,
      r.partialSnd_coneToPartial_succ]
    exact ⟨(r.mem_prodTotal_grading_iff (p + 1) u.1).mp hu.1 k, ih⟩

private theorem coneToPartial_differential (u : cone r.prodTotalAugZero) (k : ℕ) :
    r.coneToPartial k ((cone r.prodTotalAugZero).differential u) =
      (r.partialObj k).differential (r.coneToPartial k u) +
        closedHom (r.partialMap k) (closedHom (r.π k) (r.prodTotalProj k u.1)) := by
  induction k with
  | zero =>
    rw [cone_differential_apply, r.closedHom_partialMap_zero]
    -- Unfold `coneToPartial 0` and `partialObj 0` to `r.syzygy 0`.
    change closedHom r.prodTotalAugZero u.1 + (r.syzygy 0).differential u.2 =
      (r.syzygy 0).differential u.2 + closedHom (r.π 0) (r.prodTotalProj 0 u.1)
    rw [closedHom_prodTotalAugZero_apply, add_comm]
  | succ k ih =>
    apply r.partial_ext k
    · rw [r.partialFst_coneToPartial_succ, cone_differential_apply, map_add,
        r.closedHom_partialMap_succ, r.partialFst_partialMk, r.partialFst_differential,
        r.partialFst_coneToPartial_succ, map_neg, prodTotal_differential_apply]
      simp only [closedHom_diff_apply, neg_add]
    · rw [r.partialSnd_coneToPartial_succ, map_add, r.closedHom_partialMap_succ,
        r.partialSnd_partialMk, add_zero, r.partialSnd_differential,
        r.partialFst_coneToPartial_succ, r.partialSnd_coneToPartial_succ, ih, add_comm]

/-- The closed projection `q_k : cone(prodTotalAugZero) ⟶ F_k`, sending `(y, z_0)` to
`(π_k(y_k), coneToPartial k (y, z_0))`. -/
private noncomputable def coneToTrunc (k : ℕ) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone r.prodTotalAugZero) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.truncObj k) :=
  closedHomOf
    (((closedHom (r.π k)).comp
        ((r.prodTotalProj k).comp (LinearMap.fst Aᵐᵒᵖ r.prodTotal (r.syzygy 0)))).prod
      (r.coneToPartial k))
    (fun p u hu ↦ by
      rw [cone_grading, Submodule.mem_prod, LinearMap.prod_apply]
      dsimp only [Function.prod]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply]
      refine ⟨?_, r.coneToPartial_mem hu k⟩
      rw [shift_grading]
      rw [cone_grading] at hu
      exact closedHom_mem (r.π k) ((r.mem_prodTotal_grading_iff (p + 1) u.1).mp hu.1 k))
    (fun u ↦ by
      rw [LinearMap.prod_apply, LinearMap.prod_apply]
      dsimp only [Function.prod]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.fst_apply, cone_differential_apply,
        r.coneToPartial_differential u k, cone_differential_apply]
      dsimp only
      apply Prod.ext
      · rw [map_neg, prodTotal_differential_apply, map_neg, map_add, shift_differential_apply,
          Units.smul_def, Units.smul_def, map_zsmul, differential_closedHom]
        have h0 : closedHom (r.π k) (closedHom (r.diff k) (r.prodTotalProj (k + 1) u.1)) = 0 := by
          rw [← LinearMap.comp_apply, ← closedHom_comp, r.diff_comp_π k, closedHom_zero,
            LinearMap.zero_apply]
        rw [h0, add_zero]
      · rw [add_comm])

private theorem closedHom_coneToTrunc_apply (k : ℕ) (u : cone r.prodTotalAugZero) :
    closedHom (r.coneToTrunc k) u =
      (closedHom (r.π k) (r.prodTotalProj k u.1), r.coneToPartial k u) := by
  dsimp only [coneToTrunc]
  rw [closedHom_closedHomOf, LinearMap.prod_apply]
  dsimp only [Function.prod]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply]

private theorem coneToTrunc_succ_comp_transition (k : ℕ) :
    r.coneToTrunc (k + 1) ≫ r.truncTransition k = r.coneToTrunc k := by
  apply closedHom_ext
  intro u
  rw [closedHom_comp, LinearMap.comp_apply, r.closedHom_coneToTrunc_apply,
    r.closedHom_truncTransition_apply, r.closedHom_coneToTrunc_apply,
    r.partialFst_coneToPartial_succ, r.partialSnd_coneToPartial_succ]

/-- Surjectivity of `truncTransition k` on degree-`p` homogeneous pieces. -/
private theorem surjective_truncTransition_piece (k : ℕ) (p : ℤ)
    (w : r.truncObj k) (hw : w ∈ (r.truncObj k).grading p) :
    ∃ z : r.truncObj (k + 1), z ∈ (r.truncObj (k + 1)).grading p ∧
      closedHom (r.truncTransition k) z = w := by
  let g : toGradedModuleCat (r.truncObj (k + 1)) ⟶ toGradedModuleCat (r.truncObj k) :=
    forgetDifferential.map (r.truncTransition k)
  have hsurj := GradedModuleCat.smulPieceMap_surjective (e := (1 : Aᵐᵒᵖ)) (g := g)
    (by
      dsimp only [g]
      rw [forgetDifferential_map_hom]
      exact (shortExact_iff.1 (r.truncTransition_shortExact k)).2.1) p
  obtain ⟨⟨z, hz⟩, hzw⟩ := hsurj ⟨w, by rw [one_smul, toGradedModuleCat_piece]; exact hw⟩
  rw [one_smul, toGradedModuleCat_piece] at hz
  refine ⟨z, hz, ?_⟩
  simpa [g, GradedModuleCat.coe_smulPieceMap_apply, forgetDifferential_map_hom] using
    congrArg Subtype.val hzw

/-- The Milnor product `∏ₖ F_k` of all truncations in the tower. -/
private noncomputable abbrev truncProd : CurvedDGRightModuleCat.{u, u, u} h :=
  product fun k : ULift.{u} ℕ ↦ r.truncObj k.down

/-- Coordinate evaluation `∏ₖ F_k → F_k` typed directly on the curved module carrier `F_k`. -/
private noncomputable def truncProdEval (k : ℕ) (x : r.truncProd) : r.truncObj k :=
  x.val ⟨k⟩

/-- The closed inclusion `cone(prodTotalAugZero) ⟶ ∏ₖ F_k`. -/
private noncomputable def milnorIncl :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone r.prodTotalAugZero) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) r.truncProd :=
  closedProductLift (fun k : ULift.{u} ℕ ↦ r.truncObj k.down) fun k ↦ r.coneToTrunc k.down

/-- The closed product–difference endomorphism `1 - s : ∏ₖ F_k ⟶ ∏ₖ F_k`. -/
private noncomputable def milnorDiff :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) r.truncProd ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) r.truncProd :=
  closedProductLift (fun k : ULift.{u} ℕ ↦ r.truncObj k.down) fun k ↦
    closedProductπ (fun j : ULift.{u} ℕ ↦ r.truncObj j.down) k -
      closedProductπ (fun j : ULift.{u} ℕ ↦ r.truncObj j.down) (ULift.up (k.down + 1)) ≫
        r.truncTransition k.down

private theorem milnorIncl_comp_milnorDiff : r.milnorIncl ≫ r.milnorDiff = 0 := by
  apply closedProduct_hom_ext
  intro k
  simp only [milnorIncl, milnorDiff, Category.assoc, closedProductLift_π, Preadditive.comp_sub,
    closedProductLift_π_assoc, r.coneToTrunc_succ_comp_transition, sub_self, Limits.zero_comp]

/-- Extracting the `P_n`-coordinates from an element of `∏ₖ F_k` produces an element of
`r.prodTotal` with common finite degree support. -/
private noncomputable def truncProdToProdTotal :
    r.truncProd →ₗ[R] r.prodTotal :=
  (r.prodTotalEquiv.symm.toLinearMap.restrictScalars R).comp
    (InternalGrading.productLiftLinear
      (fun n : ULift.{u} ℕ ↦ (toGradedModuleCat ((r.term n.down).shift (n.down : ℤ))).grading)
      (GradedModuleCat.product fun k : ULift.{u} ℕ ↦ toGradedModuleCat (r.truncObj k.down)).grading
      1
      (fun n ↦
        ((r.partialFst n.down).restrictScalars R).comp
          (((LinearMap.snd Aᵐᵒᵖ ((r.syzygy (n.down + 1)).shift ((n.down + 1 : ℕ) : ℤ))
              (r.partialObj (n.down + 1))).restrictScalars R).comp
            (InternalGrading.productEval _ (ULift.up (n.down + 1)))))
      (fun n ↦ by
        rw [LinearMap.isHomogeneous_def]
        intro p x hx
        have hx' : x.val (ULift.up (n.down + 1)) ∈ (r.truncObj (n.down + 1)).grading p := by
          simpa only [toGradedModuleCat_piece] using
            (GradedModuleCat.mem_product_piece_iff _ p x).mp hx (ULift.up (n.down + 1))
        rw [cone_grading, Submodule.mem_prod] at hx'
        have hx'' := hx'.2
        rw [r.mem_partialObj_succ_grading_iff] at hx''
        rw [toGradedModuleCat_piece, shift_grading, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply,
          InternalGrading.productEval_apply, LinearMap.snd_apply]
        exact hx''.1))

private theorem truncProdToProdTotal_apply (x : r.truncProd) (n : ℕ) :
    r.prodTotalProj n (r.truncProdToProdTotal x) = r.partialFst n (x.val ⟨n + 1⟩).2 := by
  rw [prodTotalProj_eq_val]
  dsimp only [truncProdToProdTotal]
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, InternalGrading.productLiftLinear_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply,
    InternalGrading.productEval_apply, LinearMap.snd_apply]

/-- The `R`-module tower of degree-`p` homogeneous pieces of the truncation tower. -/
private noncomputable def truncPieceTower (p : ℤ) : ModuleTower.{u} R :=
  Functor.ofOpSequence
    (X := fun k ↦ ModuleCat.of R ((r.truncObj k).grading p))
    (fun k ↦ ModuleCat.ofHom
      (((closedHom (r.truncTransition k)).restrictScalars R).restrict fun _ hx ↦
        closedHom_mem (r.truncTransition k) hx))

private theorem truncPieceTower_transition_apply (p : ℤ) (k : ℕ)
    (x : (r.truncPieceTower p).obj (Opposite.op (k + 1))) :
    ((r.truncPieceTower p).transition k x).val = closedHom (r.truncTransition k) x.val := by
  simp only [truncPieceTower, ModuleTower.transition_def, Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private theorem injective_milnorIncl : Function.Injective (closedHom r.milnorIncl) := by
  intro (u₁ : cone r.prodTotalAugZero) (u₂ : cone r.prodTotalAugZero) hu
  have hcomp : ∀ k : ℕ, closedHom (r.coneToTrunc k) u₁ = closedHom (r.coneToTrunc k) u₂ := by
    intro k
    have hk := congrArg (fun x : r.truncProd ↦ x.val ⟨k⟩) hu
    dsimp only [milnorIncl] at hk
    rw [closedHom_closedProductLift_apply, closedHom_closedProductLift_apply] at hk
    exact hk
  apply Prod.ext
  · apply r.prodTotal_ext
    intro n
    have hn := congrArg (fun z : r.truncObj (n + 1) ↦ r.partialFst n z.2) (hcomp (n + 1))
    simpa only [r.closedHom_coneToTrunc_apply, r.partialFst_coneToPartial_succ] using hn
  · have h0 := congrArg Prod.snd (hcomp 0)
    rw [r.closedHom_coneToTrunc_apply, r.closedHom_coneToTrunc_apply] at h0
    exact h0

private theorem exists_milnorDiff_eq_of_mem (p : ℤ) (bp : r.truncProd)
    (hbp : bp ∈ r.truncProd.grading p) :
    ∃ a : r.truncProd, closedHom r.milnorDiff a = bp := by
  have hsurj : ∀ k : ℕ, Function.Surjective ((r.truncPieceTower p).transition k) :=
    fun k ⟨w, hw⟩ ↦ by
      obtain ⟨z, hz, hzw⟩ := r.surjective_truncTransition_piece k p w hw
      let z' : (r.truncPieceTower p).obj (Opposite.op (k + 1)) := ⟨z, hz⟩
      exact ⟨z', Subtype.ext (by
        change ((r.truncPieceTower p).transition k z').val = w
        rw [truncPieceTower_transition_apply, hzw])⟩
  obtain ⟨x, hx⟩ := (r.truncPieceTower p).shift_surjective hsurj fun k ↦
    ⟨r.truncProdEval k bp, (mem_product_grading_iff _ p bp).mp hbp ⟨k⟩⟩
  let a : r.truncProd :=
    ⟨fun k ↦ (x k.down).val,
      InternalGrading.productPiece_le_productCarrier _ p
        ((InternalGrading.mem_productPiece_iff _ p _).mpr fun k ↦ by
          simpa only [toGradedModuleCat_piece] using (x k.down).property)⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  funext ⟨k⟩
  dsimp only [milnorDiff]
  rw [closedHom_closedProductLift_apply, ← forgetDifferential_map_hom, Functor.map_sub,
    GradedModuleCat.hom_sub, forgetDifferential_map_hom, forgetDifferential_map_hom,
    LinearMap.sub_apply, closedHom_closedProductπ_apply, closedHom_comp, LinearMap.comp_apply,
    closedHom_closedProductπ_apply]
  have hxk := congrArg (fun f : (r.truncPieceTower p).Product ↦ (f k).val) hx
  rw [ModuleTower.shift_apply] at hxk
  change (x k).val - ((r.truncPieceTower p).transition k (x (k + 1))).val = r.truncProdEval k bp
    at hxk
  rwa [truncPieceTower_transition_apply] at hxk

private theorem surjective_milnorDiff : Function.Surjective (closedHom r.milnorDiff) := by
  intro (b : r.truncProd)
  change b ∈ LinearMap.range (closedHom r.milnorDiff)
  induction b using DirectSum.Decomposition.inductionOn r.truncProd.grading with
  | zero => exact Submodule.zero_mem _
  | @homogeneous p bp => exact r.exists_milnorDiff_eq_of_mem p bp.val bp.property
  | add _ _ hx hy => exact Submodule.add_mem _ hx hy

private theorem exact_milnorIncl_milnorDiff :
    Function.Exact (closedHom r.milnorIncl) (closedHom r.milnorDiff) := by
  intro (x : r.truncProd)
  constructor
  · intro hx
    have htrans : ∀ k : ℕ,
        closedHom (r.truncTransition k) (x.val ⟨k + 1⟩) = x.val ⟨k⟩ := by
      intro k
      have hk := congrArg (fun z : r.truncProd ↦ z.val ⟨k⟩) hx
      dsimp only [milnorDiff] at hk
      rw [closedHom_closedProductLift_apply, ← forgetDifferential_map_hom, Functor.map_sub,
        GradedModuleCat.hom_sub, forgetDifferential_map_hom, forgetDifferential_map_hom,
        LinearMap.sub_apply, closedHom_closedProductπ_apply, closedHom_comp, LinearMap.comp_apply,
        closedHom_closedProductπ_apply] at hk
      exact (sub_eq_zero.mp hk).symm
    let u : cone r.prodTotalAugZero := (r.truncProdToProdTotal x, (x.val ⟨0⟩).2)
    have hpartial : ∀ k : ℕ, r.coneToPartial k u = (x.val ⟨k⟩).2 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        have hk := congrArg Prod.snd (htrans k)
        rw [r.closedHom_truncTransition_apply] at hk
        apply r.partial_ext k
        · rw [r.partialFst_coneToPartial_succ, r.truncProdToProdTotal_apply]
        · rw [r.partialSnd_coneToPartial_succ, ih, ← hk]
    refine ⟨u, ?_⟩
    apply Subtype.ext
    funext ⟨k⟩
    dsimp only [milnorIncl]
    rw [closedHom_closedProductLift_apply, r.closedHom_coneToTrunc_apply,
      r.truncProdToProdTotal_apply, hpartial k]
    have hk := congrArg Prod.fst (htrans k)
    rw [r.closedHom_truncTransition_apply] at hk
    dsimp only at hk ⊢
    rw [hk]
    exact Prod.mk.eta
  · rintro ⟨u, rfl⟩
    have h0 := congrArg (fun l ↦ closedHom l u) r.milnorIncl_comp_milnorDiff
    simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
      using h0

/-- The Milnor sequence `0 ⟶ cone(prodTotalAugZero) ⟶ ∏ₖ F_k ⟶ ∏ₖ F_k ⟶ 0` is short exact
in the closed abelian category of curved right modules. -/
private theorem milnor_shortExact :
    (ShortComplex.mk r.milnorIncl r.milnorDiff r.milnorIncl_comp_milnorDiff).ShortExact :=
  shortExact_iff.2 ⟨r.injective_milnorIncl, r.surjective_milnorDiff,
    r.exact_milnorIncl_milnorDiff⟩

/-- The mapping cone of `prodTotalAugZero : r.prodTotal ⟶ r.syzygy 0` is contraacyclic. -/
private theorem contraacyclic_cone_prodTotalAugZero :
    contraacyclic R h (DGHomotopyCategory.of R (cone r.prodTotalAugZero)) := by
  have hProd : contraacyclic R h (DGHomotopyCategory.of R r.truncProd) :=
    (contraacyclic R h).prop_of_isLimit
      (homotopyProductFanIsLimit (fun k : ULift.{u} ℕ ↦ r.truncObj k.down))
      (fun ⟨k⟩ ↦ r.contraacyclic_truncObj k.down)
  exact prop_X₁_of_shortExact (contraacyclic R h) (totalizations_le_contraacyclic R h)
    r.milnor_shortExact hProd hProd

end MilnorTower

/-- **Contraacyclicity of the product totalization.** For any left resolution `r` of a curved
right module `M`, the mapping cone of the closed augmentation `r.prodTotalAug : Tot^Π(r) ⟶ M`
is contraacyclic. -/
theorem contraacyclic_cone_prodTotalAug :
    contraacyclic R h (DGHomotopyCategory.of R (cone r.prodTotalAug)) := by
  have h0 : (contraacyclic R h).trW ((dgClosedToHomotopy R).map r.prodTotalAugZero) :=
    ((contraacyclic R h).trW_iff_of_distinguished _
      (coneTriangle_distinguished r.prodTotalAugZero)).2 r.contraacyclic_cone_prodTotalAugZero
  have hiso : (contraacyclic R h).trW ((dgClosedToHomotopy R).map r.syzygyZeroIso.hom) :=
    ObjectProperty.trW_of_isIso _ _
  have hcomp : (contraacyclic R h).trW ((dgClosedToHomotopy R).map r.prodTotalAug) := by
    rw [prodTotalAug, Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ h0 hiso
  exact ((contraacyclic R h).trW_iff_of_distinguished _
    (coneTriangle_distinguished r.prodTotalAug)).1 hcomp

end LeftResolution

end TauCeti.CurvedDGRightModuleCat
