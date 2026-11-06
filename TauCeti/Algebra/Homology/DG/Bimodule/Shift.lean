/-
Copyright (c) 2026 Wentao Li and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Category
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.Algebra.Module.GradedModule.KoszulTwist.Algebra
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# Cohomological shifts of DG bimodules

The shift `M[n]` of an `(A,B)`-DG bimodule has `M[n]ᵖ = Mᵖ⁺ⁿ` and differential
`(-1)^n dM`. Its right action is unchanged, whereas a homogeneous left scalar `a` acts by
`(-1)^(n |a|) a`. Both signs are needed for the two Leibniz identities. These shifts supply,
in particular, the shifted inverse-dualizing bimodule used as a tensor-algebra generator in
Calabi--Yau completions.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
* B. Keller, *Deformed Calabi--Yau completions*, Section 4.

The grading and differential construction follows the right-module shift in
`TauCeti.Algebra.Homology.Curved.Module.Right.Shift`; the signed left action is additional.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.DGBimoduleCat

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- The cohomological shift of a DG bimodule, with the left action restricted along the
Koszul automorphism of parameter `n`, and the original right action. -/
-- The carrier must reduce to `M` to state the element-level action and differential formulas.
@[expose, implicit_reducible]
noncomputable def shift (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n : ℤ) :
    DGBimoduleCat.{uR, uA, uB, uM} hA hB := by
  let G := (InternalGrading.ofDecomposition M.grading).shift n
  let σ := InternalGrading.koszulTwistAlgEquiv 𝒜 n
  let act : A → M → M := (· • ·)
  have htower (r : R) (a : A) (x : M) :
      act (σ (r • a)) x = r • act (σ a) x := by
    simp only [act, map_smul, smul_assoc]
  have hcomm (a : A) (b : Bᵐᵒᵖ) (x : M) :
      act (σ a) (b • x) = b • act (σ a) x := smul_comm (σ a) b x
  -- First establish the identities in the original action. Keeping these local prevents
  -- instance inference from confusing the original and restricted actions on the same carrier.
  have hgrade {p q : ℤ} {a : A} {x : M} (ha : a ∈ 𝒜 p) (hx : x ∈ M.grading (q + n)) :
      act (σ a) x ∈ M.grading ((p + q) + n) := by
    simpa only [act, σ, InternalGrading.koszulTwistAlgEquiv_apply,
      vadd_eq_add, add_assoc] using
      (SetLike.GradedSMul.smul_mem (B := M.grading)
        (InternalGrading.koszulTwist_mem_ofDecomposition 𝒜 ha n) hx)
  have hleft {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (x : M) :
      negOnePowCast R n • M.differential (act (σ a) x) = act (σ (dA a)) x +
        p.negOnePow • act (σ a) (negOnePowCast R n • M.differential x) := by
    dsimp only [act, σ]
    rw [InternalGrading.koszulTwistAlgEquiv_apply_of_mem 𝒜 n ha,
      InternalGrading.koszulTwistAlgEquiv_apply_of_mem 𝒜 n (hA.map_mem ha)]
    simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), smul_assoc, map_smul,
      M.isDGLeftModule.leibniz ha x, smul_add]
    rw [smul_comm a (negOnePowCast R n)]
    simp only [← mul_smul, mul_add, mul_one, negOnePowCast_add]
    congr 1 <;> congr 1 <;> ring
  -- Install the restricted action only after the original-action calculations are complete.
  letI : Module A M := Module.compHom M σ.toRingHom
  letI : IsScalarTower R A M := ⟨fun r a x ↦ by
    -- Read the restricted action in the original module before using scalar compatibility.
    exact htower r a x⟩
  letI : SMulCommClass A Bᵐᵒᵖ M := ⟨fun a b x ↦ by
    -- The restricted left action still commutes with the original right action.
    exact hcomm a b x⟩
  letI : SetLike.GradedSMul 𝒜 G.piece := ⟨fun p q a x ha hx ↦ by
    -- The new action is the old action of the degree-preserving Koszul twist.
    simp only [G, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece,
      vadd_eq_add] at hx ⊢
    exact hgrade ha hx⟩
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece G.piece :=
    ⟨fun p q b x hb hx ↦ by
      simp only [G, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece,
        vadd_eq_add] at hx ⊢
      simpa only [vadd_eq_add, add_assoc] using
        (SetLike.GradedSMul.smul_mem (B := M.grading) hb hx)⟩
  -- Verify the right module first, then reuse its differential laws for the left module.
  have hR : IsDGRightModule hB G.piece (negOnePowCast R n • M.differential) := by
    refine ⟨?_, ?_, ?_⟩
    · apply LinearMap.isHomogeneous_shift_piece_iff.mpr
      simpa only [InternalGrading.ofDecomposition_piece] using
        M.isDGRightModule.isHomogeneous.smul (negOnePowCast R n)
    · intro x
      simp only [LinearMap.smul_apply, map_smul, negOnePowCast_smul_negOnePowCast_smul,
        M.isDGRightModule.sq_zero]
    · intro q x hx b
      simp only [G, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece] at hx
      simp only [LinearMap.smul_apply, M.isDGRightModule.leibniz hx b, smul_add]
      simp only [← negOnePow_smul_eq_negOnePowCast_smul]
      rw [smul_comm n.negOnePow (op b)]
      congr 1
      rw [← mul_smul, Int.negOnePow_add, mul_left_comm, Int.units_mul_self, mul_one]
  exact
    { carrier := M
      grading := G.piece
      differential := negOnePowCast R n • M.differential
      isDGRightModule := hR
      isDGLeftModule :=
        { isHomogeneous := hR.isHomogeneous
          sq_zero := hR.sq_zero
          leibniz := fun ha x ↦ hleft ha x } }

/-- The underlying base module is unchanged by cohomological shift. This identification is
not left `A`-linear in general: the left action is twisted. -/
noncomputable def shiftEquiv (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n : ℤ) :
    M.shift n ≃ₗ[R] M := LinearEquiv.refl R M

/-- The shifted grading reindexes the original pieces. -/
@[simp]
theorem shift_grading (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n p : ℤ) :
    (M.shift n).grading p = M.grading (p + n) := by
  simp only [shift, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece]

/-- The underlying-module identification sends shifted degree `p` to original degree `p+n`. -/
@[simp]
theorem shiftEquiv_mem_grading_iff (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n p : ℤ)
    (x : M.shift n) : shiftEquiv M n x ∈ M.grading (p + n) ↔ x ∈ (M.shift n).grading p := by
  rw [shift_grading]
  rfl

/-- The shifted differential is the original differential multiplied by the shift sign. -/
theorem shift_differential_apply (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n : ℤ)
    (x : M) : (M.shift n).differential x = n.negOnePow • M.differential x := by
  dsimp only [shift]
  rw [LinearMap.smul_apply, ← negOnePow_smul_eq_negOnePowCast_smul]

/-- The shifted left action is restriction along the Koszul algebra automorphism. -/
theorem shift_smul_left (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n : ℤ)
    (a : A) (x : M.shift n) :
    (a • x : M.shift n) =
      @SMul.smul A M M.moduleLeft.toSMul (InternalGrading.koszulTwistAlgEquiv 𝒜 n a) x :=
  (rfl)

/-- A homogeneous left scalar acts on the shifted bimodule with the shift sign. -/
theorem shift_smul_left_of_mem (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n : ℤ)
    {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (x : M.shift n) :
    (a • x : M.shift n) = (n * p).negOnePow • @SMul.smul A M M.moduleLeft.toSMul a x := by
  rw [shift_smul_left, InternalGrading.koszulTwistAlgEquiv_apply_of_mem 𝒜 n ha]
  have h (y : M) : ((n * p).negOnePow • a) • y = (n * p).negOnePow • (a • y) :=
    smul_assoc _ _ _
  exact h x

/-- Reading a shifted differential in the original module introduces the shift sign. -/
@[simp]
theorem shiftEquiv_differential (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n : ℤ)
    (x : M.shift n) :
    shiftEquiv M n ((M.shift n).differential x) =
      n.negOnePow • M.differential (shiftEquiv M n x) := shift_differential_apply M n x

/-- Reading the shifted left action twists the scalar by its Koszul automorphism. -/
@[simp]
theorem shiftEquiv_smul_left (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n : ℤ)
    (a : A) (x : M.shift n) :
    shiftEquiv M n (a • x) =
      InternalGrading.koszulTwistAlgEquiv 𝒜 n a • shiftEquiv M n x := shift_smul_left M n a x

/-- Reading the shifted right action leaves the scalar unchanged. -/
@[simp]
theorem shiftEquiv_smul_right (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (n : ℤ)
    (b : Bᵐᵒᵖ) (x : M.shift n) :
    shiftEquiv M n (b • x) = b • shiftEquiv M n x := (rfl)

/-- Cohomological shift as an endofunctor on closed degree-zero DG bimodule maps. -/
-- Reducing the object projection keeps its carrier usable in elementwise functor formulas.
@[expose, implicit_reducible]
noncomputable def shiftFunctor (n : ℤ) :
    DGBimoduleCat.{uR, uA, uB, uM} hA hB ⥤ DGBimoduleCat.{uR, uA, uB, uM} hA hB where
  obj M := M.shift n
  map {M N} f :=
    ⟨{ toLinearMap := f.val.toLinearMap
       map_mem' := by
         intro p x hx
         rw [shift_grading] at hx ⊢
         exact Graded.map_mem f hx
       map_d' := by
         intro x
         simp only [shift_differential_apply, Units.smul_def, map_zsmul,
           DGRightModuleHom.coe_toLinearMap, DGBimoduleHom.coe_val]
         exact congrArg (fun y : N ↦ (n.negOnePow : ℤ) • y) (DGBimoduleHom.map_d f x) }, by
      rw [mem_dgBimoduleHomSubmodule]
      intro a x
      simp only [DGRightModuleHom.coe_mk, DGRightModuleHom.coe_toLinearMap,
        DGBimoduleHom.coe_val, shift_smul_left]
      exact DGBimoduleHom.map_smul_left f _ x⟩
  map_id M := by
    ext x
    -- Read through the subtype of right-module morphisms to the original underlying map.
    change (𝟙 M) (x : M) = (𝟙 (M.shift n)) x
    simp only [id_apply]
  map_comp f g := by
    ext x
    rw [comp_apply]
    -- The shifted map stores the same underlying right-linear map.
    change (f ≫ g) x = g (f x)
    exact comp_apply f g x

/-- The shift functor has the specified cohomological shift as its object map. -/
@[simp]
theorem shiftFunctor_obj (n : ℤ) (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    (shiftFunctor n).obj M = M.shift n := (rfl)

/-- Shifting a closed degree-zero map leaves its underlying function unchanged. -/
theorem shiftFunctor_map_apply (n : ℤ) {M N : DGBimoduleCat.{uR, uA, uB, uM} hA hB}
    (f : M ⟶ N) (x : M.shift n) : (shiftFunctor n).map f x = f (x : M) := (rfl)

/-- Shifted maps commute with the identifications of underlying base modules. -/
@[simp]
theorem shiftEquiv_shiftFunctor_map (n : ℤ)
    {M N : DGBimoduleCat.{uR, uA, uB, uM} hA hB} (f : M ⟶ N) (x : M.shift n) :
    shiftEquiv N n ((shiftFunctor n).map f x) = f (shiftEquiv M n x) := (rfl)

instance (n : ℤ) : (shiftFunctor.{uR, uA, uB, uM} (hA := hA) (hB := hB) n).Additive where
  map_add := by intros; ext x; rfl

instance (n : ℤ) : (shiftFunctor.{uR, uA, uB, uM} (hA := hA) (hB := hB) n).Linear R where
  map_smul := by intros; ext x; rfl

/-- The identity comparison from the zero shift to the original DG bimodule. -/
noncomputable def shiftZeroIso (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    M.shift 0 ≅ M where
  hom := ⟨
    { toLinearMap := LinearMap.id
      map_mem' := by intro p x hx; simpa only [shift_grading, add_zero,
        LinearMap.id_apply] using hx
      map_d' := by intro x; simp only [LinearMap.id_apply, shift_differential_apply,
        Int.negOnePow_zero, one_smul] }, by
    rw [mem_dgBimoduleHomSubmodule]
    intro a x
    -- The identity right-linear map reads the restricted action on the same carrier.
    change (a • x : M.shift 0) = @SMul.smul A M M.moduleLeft.toSMul a x
    rw [shift_smul_left, InternalGrading.koszulTwistAlgEquiv_zero]
    rfl⟩
  inv := ⟨
    { toLinearMap := LinearMap.id
      map_mem' := by intro p x hx; simpa only [shift_grading, add_zero,
        LinearMap.id_apply] using hx
      map_d' := by intro x; simp only [LinearMap.id_apply, shift_differential_apply,
        Int.negOnePow_zero, one_smul] }, by
    rw [mem_dgBimoduleHomSubmodule]
    intro a x
    -- As above, only the left action differs on the two identity-map carriers.
    change @SMul.smul A M M.moduleLeft.toSMul a x =
      @SMul.smul A (M.shift 0) (M.shift 0).moduleLeft.toSMul a x
    have h := (shift_smul_left M 0 a x).symm
    rw [InternalGrading.koszulTwistAlgEquiv_zero] at h
    exact h⟩
  hom_inv_id := by ext x; rw [comp_apply, id_apply]; rfl
  inv_hom_id := by ext x; rw [comp_apply, id_apply]; rfl

/-- The zero-shift comparison is the identity on underlying elements. -/
@[simp]
theorem shiftZeroIso_hom_apply
    (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (x : M.shift 0) :
    (shiftZeroIso M).hom x = (x : M) := (rfl)

/-- The inverse zero-shift comparison is the identity on underlying elements. -/
@[simp]
theorem shiftZeroIso_inv_apply
    (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (x : M) :
    (shiftZeroIso M).inv x = (x : M.shift 0) := (rfl)

/-- Successive cohomological shifts add, including the signs in the left action. -/
noncomputable def shiftAddIso (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (m n : ℤ) :
    (M.shift m).shift n ≅ M.shift (m + n) where
  hom := ⟨
    { toLinearMap := LinearMap.id
      map_mem' := by
        intro p x hx
        simpa only [LinearMap.id_apply, shift_grading, add_assoc, add_comm n m] using hx
      map_d' := by
        intro x
        simp [shift_differential_apply, ← mul_smul, Int.negOnePow_add, mul_comm] }, by
    rw [mem_dgBimoduleHomSubmodule]
    intro a x
    -- Read the two restrictions of the left action as their composite automorphism.
    change @SMul.smul A M M.moduleLeft.toSMul
        (InternalGrading.koszulTwistAlgEquiv 𝒜 m
          (InternalGrading.koszulTwistAlgEquiv 𝒜 n a)) x =
      @SMul.smul A M M.moduleLeft.toSMul (InternalGrading.koszulTwistAlgEquiv 𝒜 (m + n) a) x
    rw [← AlgEquiv.trans_apply, InternalGrading.koszulTwistAlgEquiv_trans]⟩
  inv := ⟨
    { toLinearMap := LinearMap.id
      map_mem' := by
        intro p x hx
        simpa only [LinearMap.id_apply, shift_grading, add_assoc, add_comm n m] using hx
      map_d' := by
        intro x
        simp [shift_differential_apply, ← mul_smul, Int.negOnePow_add, mul_comm] }, by
    rw [mem_dgBimoduleHomSubmodule]
    intro a x
    -- The inverse identity map reads the same composite restriction in the reverse direction.
    change @SMul.smul A M M.moduleLeft.toSMul
        (InternalGrading.koszulTwistAlgEquiv 𝒜 (m + n) a) x =
      @SMul.smul A M M.moduleLeft.toSMul (InternalGrading.koszulTwistAlgEquiv 𝒜 m
        (InternalGrading.koszulTwistAlgEquiv 𝒜 n a)) x
    rw [← AlgEquiv.trans_apply, InternalGrading.koszulTwistAlgEquiv_trans]⟩
  hom_inv_id := by ext x; rw [comp_apply, id_apply]; rfl
  inv_hom_id := by ext x; rw [comp_apply, id_apply]; rfl

/-- The addition comparison leaves underlying elements unchanged. -/
@[simp]
theorem shiftAddIso_hom_apply (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (m n : ℤ)
    (x : (M.shift m).shift n) : (shiftAddIso M m n).hom x = (x : M.shift (m + n)) := (rfl)

/-- The inverse addition comparison leaves underlying elements unchanged. -/
@[simp]
theorem shiftAddIso_inv_apply (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (m n : ℤ)
    (x : M.shift (m + n)) : (shiftAddIso M m n).inv x = (x : (M.shift m).shift n) := (rfl)

/-- The zero-shift comparisons are natural in the DG bimodule. -/
noncomputable def shiftFunctorZeroIso :
    shiftFunctor.{uR, uA, uB, uM} (hA := hA) (hB := hB) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents shiftZeroIso (by
    intro M N f
    ext x
    simp only [comp_apply, Functor.id_map]
    rfl)

/-- The addition comparisons are natural in the DG bimodule. -/
noncomputable def shiftFunctorAddIso (m n : ℤ) :
    shiftFunctor.{uR, uA, uB, uM} (hA := hA) (hB := hB) m ⋙ shiftFunctor n ≅
      shiftFunctor (m + n) :=
  NatIso.ofComponents (fun M ↦ shiftAddIso M m n) (by
    intro M N f
    ext x
    simp only [Functor.comp_map, comp_apply]
    rfl)

/-- The natural zero comparison uses the elementwise zero-shift comparison. -/
@[simp]
theorem shiftFunctorZeroIso_hom_app (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    shiftFunctorZeroIso.hom.app M = (shiftZeroIso M).hom := (rfl)

/-- The inverse natural zero comparison uses the inverse elementwise comparison. -/
@[simp]
theorem shiftFunctorZeroIso_inv_app (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    shiftFunctorZeroIso.inv.app M = (shiftZeroIso M).inv := (rfl)

/-- The natural addition comparison uses the elementwise addition comparison. -/
@[simp]
theorem shiftFunctorAddIso_hom_app (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (m n : ℤ) :
    (shiftFunctorAddIso m n).hom.app M = (shiftAddIso M m n).hom := (rfl)

/-- The inverse natural addition comparison uses the inverse elementwise comparison. -/
@[simp]
theorem shiftFunctorAddIso_inv_app (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (m n : ℤ) :
    (shiftFunctorAddIso m n).inv.app M = (shiftAddIso M m n).inv := (rfl)

end TauCeti.DGBimoduleCat
