/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Shift
public import TauCeti.Algebra.Homology.DG.Algebra.KoszulTwist
public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.Algebra.Module.GradedModule.KoszulTwist.Algebra

/-!
# Shifts of DG right modules, with the suspension on either side

A DG right module `M` over a DG algebra `A` can be shifted by an integer `n` in two ways, according
to the side on which the suspension is written.

* **The shift** `M[n] = R[n] ⊗ M` (`TauCeti.DGRightModuleCat.shift`), with the suspension on the
  left: `M[n]ᵖ = Mᵖ⁺ⁿ`, differential `(-1)^n dM` and unchanged right action. This is the
  cohomological shift of `TauCeti.CurvedDGRightModuleCat.shift` at curvature zero, the convention
  `X[1]ᵖ = Xᵖ⁺¹` with differential `-d` of Mathlib's cochain complexes.
* **The right shift** `M ⊗ R[n]` (`TauCeti.DGRightModuleCat.rightShift`), with the suspension on
  the right, between `M` and the acting algebra: again `(M ⊗ R[n])ᵖ = Mᵖ⁺ⁿ`, but with the unsigned
  differential `dM`, while a homogeneous `a ∈ Aᵉ` now has to pass the suspension and acts by
  `(-1)^(n e) a`, that is, through the Koszul automorphism
  `TauCeti.InternalGrading.koszulTwistAlgEquiv` of `A`.

Neither sign can be dropped on its own: with the unsigned differential and the untwisted action,
the Leibniz rule fails for odd `n`. The two shifts are isomorphic, but not through the identity.
The Koszul rule for exchanging the two suspensions gives the isomorphism
`M ⊗ R[n] ≅ M[n]` (`TauCeti.DGRightModuleCat.rightShiftIsoShift`), which multiplies an element of
degree `p` of `M` by `(-1)^(n p)`. It commutes with the differentials and the actions exactly
because of this sign.

The right shift is the shape of a tensor product `𝓕 ⊗ L[n]` of a DG local system with a rank-one
local system placed in a nonzero degree, as in the graded twist of the Viterbo isomorphism of
Barraud–Damian–Humilière–Oancea, and the isomorphism compares it with the shift of `𝓕 ⊗ L`.

## Main definitions

* `TauCeti.DGRightModuleCat.shift`, `TauCeti.DGRightModuleCat.shiftFunctor`: the shift `M[n]`.
* `TauCeti.DGRightModuleCat.rightShift`, `TauCeti.DGRightModuleCat.rightShiftFunctor`: the right
  shift `M ⊗ R[n]`.
* `TauCeti.DGRightModuleCat.rightShiftIsoShift`: the Koszul isomorphism `M ⊗ R[n] ≅ M[n]`, and
  `TauCeti.DGRightModuleCat.rightShiftFunctorIsoShiftFunctor`, its naturality.

## Main results

* `TauCeti.DGRightModuleCat.rightShiftIsoShift_hom_apply_of_mem`: on an element of degree `p` of
  `M`, the isomorphism is multiplication by `(-1)^(n p)`.

## References

* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.DGRightModuleCat

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

/-! ### The shift `M[n]` -/

/-- **The shift** `M[n]` of a DG right module: `M[n]ᵖ = Mᵖ⁺ⁿ`, with differential `(-1)^n dM` and
unchanged right action. -/
-- The carrier must reduce to `M` to state the element-level grading and differential formulas.
@[expose, implicit_reducible]
noncomputable def shift (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) :
    DGRightModuleCat.{uR, uA, uM} h := by
  let S := (CurvedDGRightModuleCat.of M.isDGRightModule.isCurvedDGRightModule_zero).shift n
  let G := (InternalGrading.ofDecomposition M.grading).shift n
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece G.piece :=
    S.gradedSMul
  -- Reuse the curved right-module shift at zero curvature.
  have hR : IsDGRightModule h G.piece (negOnePowCast R n • M.differential) :=
    isCurvedDGRightModule_zero_iff.mp S.isCurvedDGRightModule
  exact
    { carrier := M
      grading := G.piece
      differential := negOnePowCast R n • M.differential
      isDGRightModule := hR }

/-- The degree-`p` piece of `M[n]` is the degree-`(p + n)` piece of `M`. -/
@[simp]
theorem shift_grading (M : DGRightModuleCat.{uR, uA, uM} h) (n p : ℤ) :
    (M.shift n).grading p = M.grading (p + n) := by
  simp only [shift, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece]

/-- The differential of `M[n]` is `(-1)^n dM`. -/
theorem shift_differential_apply (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) (x : M) :
    (M.shift n).differential x = n.negOnePow • M.differential x := by
  dsimp only [shift]
  rw [LinearMap.smul_apply, ← negOnePow_smul_eq_negOnePowCast_smul]

/-- The underlying right module of `M[n]` is that of `M`: the shift keeps the right action. -/
noncomputable def shiftEquiv (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) :
    M.shift n ≃ₗ[Aᵐᵒᵖ] M :=
  LinearEquiv.refl Aᵐᵒᵖ M

/-- The identification of `M[n]` with `M` is the identity on elements. -/
theorem shiftEquiv_apply (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) (x : M.shift n) :
    M.shiftEquiv n x = (x : M) :=
  (rfl)

/-- The inverse identification of `M[n]` with `M` is the identity on elements. -/
theorem shiftEquiv_symm_apply (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) (x : M) :
    (M.shiftEquiv n).symm x = (x : M.shift n) :=
  (rfl)

/-- An element of `M[n]` has degree `p` exactly when it has degree `p + n` in `M`. -/
@[simp]
theorem shiftEquiv_mem_grading_iff (M : DGRightModuleCat.{uR, uA, uM} h) (n p : ℤ)
    (x : M.shift n) : M.shiftEquiv n x ∈ M.grading (p + n) ↔ x ∈ (M.shift n).grading p := by
  rw [shift_grading]
  rfl

/-- Read in `M`, the differential of `M[n]` is `(-1)^n dM`. -/
@[simp]
theorem shiftEquiv_differential (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) (x : M.shift n) :
    M.shiftEquiv n ((M.shift n).differential x) =
      n.negOnePow • M.differential (M.shiftEquiv n x) :=
  M.shift_differential_apply n x

/-- **The shift functor** `M ↦ M[n]`, acting on morphisms by the same underlying maps. -/
-- Reducing the object projection keeps its carrier usable in elementwise functor formulas.
@[expose, implicit_reducible]
noncomputable def shiftFunctor (n : ℤ) :
    DGRightModuleCat.{uR, uA, uM} h ⥤ DGRightModuleCat.{uR, uA, uM} h where
  obj M := M.shift n
  map {M N} f :=
    { toLinearMap := f.toLinearMap
      map_mem' := fun {p x} hx ↦ by
        rw [shift_grading] at hx ⊢
        exact f.map_mem' hx
      map_d' := fun x ↦ by
        simp only [shift_differential_apply, map_zsmul_unit, DGRightModuleHom.coe_toLinearMap]
        rw [map_d] }
  map_id M := hom_ext fun x ↦ by
    -- The category identity is opaque; expose the stored underlying map to evaluate it.
    change (𝟙 M) (x : M) = (𝟙 (M.shift n)) x
    simp only [id_apply]
  map_comp f g := hom_ext fun x ↦ by
    rw [comp_apply]
    -- The category composition is opaque; expose the stored underlying map to evaluate it.
    change (f ≫ g) x = g (f x)
    exact comp_apply f g x

/-- The shift functor sends a module to its shift. -/
@[simp]
theorem shiftFunctor_obj (n : ℤ) (M : DGRightModuleCat.{uR, uA, uM} h) :
    (shiftFunctor n).obj M = M.shift n :=
  (rfl)

/-- Shifting a morphism keeps its underlying map. -/
@[simp]
theorem shiftEquiv_shiftFunctor_map (n : ℤ) {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N)
    (x : M.shift n) : N.shiftEquiv n ((shiftFunctor n).map f x) = f (M.shiftEquiv n x) :=
  (rfl)

/-! ### The right shift `M ⊗ R[n]` -/

/-- **The right shift** `M ⊗ R[n]` of a DG right module: `(M ⊗ R[n])ᵖ = Mᵖ⁺ⁿ`, with the unsigned
differential `dM`, on which a homogeneous `a ∈ Aᵉ` acts by `(-1)^(n e) a`, through the Koszul
automorphism of `A`. -/
-- The carrier must reduce to `M` to state the element-level action and differential formulas.
@[expose, implicit_reducible]
noncomputable def rightShift (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) :
    DGRightModuleCat.{uR, uA, uM} h := by
  let G := (InternalGrading.ofDecomposition M.grading).shift n
  let σ := InternalGrading.koszulTwistAlgEquiv 𝒜 n
  let act : Aᵐᵒᵖ → M → M := (· • ·)
  have htower (r : R) (a : A) (x : M) : act (op (σ (r • a))) x = r • act (op (σ a)) x := by
    simp only [act, map_smul, op_smul, smul_assoc]
  -- The differential of `A` anticommutes with the twist up to the sign `(-1)^n`.
  have hσd (a : A) : σ (d a) = n.negOnePow • d (σ a) := by
    rw [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
    simpa only [σ, InternalGrading.koszulTwistAlgEquiv_apply, mul_one] using
      h.toIsNonUnitalDGAlgebra.isHomogeneous.koszulTwist_apply n a
  -- First establish the identities in the original action. Keeping these local prevents
  -- instance inference from confusing the original and restricted actions on the same carrier.
  have hgrade {p q : ℤ} {a : A} {x : M} (ha : a ∈ 𝒜 p) (hx : x ∈ M.grading (q + n)) :
      act (op (σ a)) x ∈ M.grading ((p + q) + n) := by
    have hσ : op (σ a) ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece p := by
      rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]
      simpa only [σ, InternalGrading.koszulTwistAlgEquiv_apply] using
        InternalGrading.koszulTwist_mem_ofDecomposition 𝒜 ha n
    simpa only [act, vadd_eq_add, add_assoc] using
      SetLike.GradedSMul.smul_mem (B := M.grading) hσ hx
  have hleibniz {q : ℤ} {x : M} (hx : x ∈ M.grading (q + n)) (a : A) :
      M.differential (act (op (σ a)) x) =
        act (op (σ a)) (M.differential x) + q.negOnePow • act (op (σ (d a))) x := by
    simp only [act]
    rw [M.isDGRightModule.leibniz hx, hσd, op_smul, smul_assoc, smul_smul, ← Int.negOnePow_add]
  have hhom : LinearMap.IsHomogeneous M.differential G.piece G.piece 1 :=
    LinearMap.isHomogeneous_def.mpr fun q x hx ↦ by
      simp only [G, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece] at hx ⊢
      simpa only [add_right_comm] using M.isDGRightModule.isHomogeneous.map_mem hx
  have hsq := M.isDGRightModule.sq_zero
  -- The Koszul automorphism read on the opposite algebra, spelled out so that its values reduce.
  let σop : Aᵐᵒᵖ →+* Aᵐᵒᵖ :=
    { toFun := fun a ↦ op (σ a.unop)
      map_one' := by simp
      map_mul' := fun a b ↦ by simp
      map_zero' := by simp
      map_add' := fun a b ↦ by simp }
  -- Install the restricted action only after the original-action calculations are complete.
  letI : Module Aᵐᵒᵖ M := Module.compHom M σop
  letI : IsScalarTower R Aᵐᵒᵖ M := ⟨fun r a x ↦ by
    -- Read the restricted action in the original module before using scalar compatibility.
    exact htower r a.unop x⟩
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece G.piece :=
    ⟨fun {p q} a x ha hx ↦ by
      simp only [G, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece] at hx ⊢
      rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at ha
      exact hgrade ha hx⟩
  exact
    { carrier := M
      grading := G.piece
      differential := M.differential
      isDGRightModule :=
        { isHomogeneous := hhom
          sq_zero := hsq
          leibniz := fun {q x} hx a ↦ by
            simp only [G, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece] at hx
            exact hleibniz hx a } }

/-- The degree-`p` piece of `M ⊗ R[n]` is the degree-`(p + n)` piece of `M`. -/
@[simp]
theorem rightShift_grading (M : DGRightModuleCat.{uR, uA, uM} h) (n p : ℤ) :
    (M.rightShift n).grading p = M.grading (p + n) := by
  simp only [rightShift, InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece]

/-- The underlying module of `M ⊗ R[n]` over the ground ring is that of `M`. This identification
is not right `A`-linear: the action on `M ⊗ R[n]` is twisted. -/
noncomputable def rightShiftEquiv (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) :
    M.rightShift n ≃ₗ[R] M :=
  LinearEquiv.refl R M

/-- The identification of `M ⊗ R[n]` with `M` is the identity on elements. -/
theorem rightShiftEquiv_apply (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ)
    (x : M.rightShift n) : M.rightShiftEquiv n x = (x : M) :=
  (rfl)

/-- The inverse identification of `M ⊗ R[n]` with `M` is the identity on elements. -/
theorem rightShiftEquiv_symm_apply (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) (x : M) :
    (M.rightShiftEquiv n).symm x = (x : M.rightShift n) :=
  (rfl)

/-- An element of `M ⊗ R[n]` has degree `p` exactly when it has degree `p + n` in `M`. -/
@[simp]
theorem rightShiftEquiv_mem_grading_iff (M : DGRightModuleCat.{uR, uA, uM} h) (n p : ℤ)
    (x : M.rightShift n) :
    M.rightShiftEquiv n x ∈ M.grading (p + n) ↔ x ∈ (M.rightShift n).grading p := by
  rw [rightShift_grading]
  rfl

/-- Read in `M`, the differential of `M ⊗ R[n]` is the differential of `M`, with no sign. -/
@[simp]
theorem rightShiftEquiv_differential (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ)
    (x : M.rightShift n) :
    M.rightShiftEquiv n ((M.rightShift n).differential x) =
      M.differential (M.rightShiftEquiv n x) :=
  (rfl)

/-- Read in `M`, the right action on `M ⊗ R[n]` is the action of `M` through the Koszul
automorphism of parameter `n`. -/
@[simp]
theorem rightShiftEquiv_smul (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) (a : Aᵐᵒᵖ)
    (x : M.rightShift n) :
    M.rightShiftEquiv n (a • x) =
      op (InternalGrading.koszulTwistAlgEquiv 𝒜 n a.unop) • M.rightShiftEquiv n x :=
  (rfl)

/-- **The action on `M ⊗ R[n]`**: a homogeneous `a ∈ Aᵉ` passes the suspension and acts by
`(-1)^(n e) a`. -/
theorem rightShiftEquiv_op_smul_of_mem (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) {e : ℤ}
    {a : A} (ha : a ∈ 𝒜 e) (x : M.rightShift n) :
    M.rightShiftEquiv n (op a • x) = (n * e).negOnePow • (op a • M.rightShiftEquiv n x) := by
  rw [rightShiftEquiv_smul, unop_op, InternalGrading.koszulTwistAlgEquiv_apply_of_mem 𝒜 n ha,
    op_smul, smul_assoc]

/-- **The right shift functor** `M ↦ M ⊗ R[n]`, acting on morphisms by the same underlying maps. -/
-- Reducing the object projection keeps its carrier usable in elementwise functor formulas.
@[expose, implicit_reducible]
noncomputable def rightShiftFunctor (n : ℤ) :
    DGRightModuleCat.{uR, uA, uM} h ⥤ DGRightModuleCat.{uR, uA, uM} h where
  obj M := M.rightShift n
  map {M N} f :=
    { toLinearMap :=
        { toFun := fun x ↦ (f (x : M) : N)
          map_add' := fun x y ↦ map_add f (x : M) y
          -- The twisted actions on both sides are the original actions of the twisted scalar.
          map_smul' := fun a x ↦
            f.map_smul' (op (InternalGrading.koszulTwistAlgEquiv 𝒜 n a.unop)) (x : M) }
      map_mem' := fun {p x} hx ↦ by
        rw [rightShift_grading] at hx ⊢
        exact f.map_mem' hx
      map_d' := fun x ↦ map_d f (x : M) }
  map_id M := hom_ext fun x ↦ by
    -- The category identity is opaque; expose the stored underlying map to evaluate it.
    change (𝟙 M) (x : M) = (𝟙 (M.rightShift n)) x
    simp only [id_apply]
  map_comp f g := hom_ext fun x ↦ by
    rw [comp_apply]
    -- The category composition is opaque; expose the stored underlying map to evaluate it.
    change (f ≫ g) x = g (f x)
    exact comp_apply f g x

/-- The right shift functor sends a module to its right shift. -/
@[simp]
theorem rightShiftFunctor_obj (n : ℤ) (M : DGRightModuleCat.{uR, uA, uM} h) :
    (rightShiftFunctor n).obj M = M.rightShift n :=
  (rfl)

/-- Right-shifting a morphism keeps its underlying map. -/
@[simp]
theorem rightShiftEquiv_rightShiftFunctor_map (n : ℤ) {M N : DGRightModuleCat.{uR, uA, uM} h}
    (f : M ⟶ N) (x : M.rightShift n) :
    N.rightShiftEquiv n ((rightShiftFunctor n).map f x) = f (M.rightShiftEquiv n x) :=
  (rfl)

/-! ### Exchanging the two suspensions -/

/-- The Koszul twist of `M` intertwines the twisted and the original action: passing the
suspension costs the sign that the twist of the scalar records. -/
private theorem koszulTwist_op_koszulTwistAlgEquiv_smul (M : DGRightModuleCat.{uR, uA, uM} h)
    (n : ℤ) (b : A) (y : M) :
    (InternalGrading.ofDecomposition M.grading).koszulTwist n
        (op (InternalGrading.koszulTwistAlgEquiv 𝒜 n b) • y) =
      op b • (InternalGrading.ofDecomposition M.grading).koszulTwist n y := by
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add b b' hb hb' =>
    rw [map_add, MulOpposite.op_add, add_smul, map_add, hb, hb', MulOpposite.op_add, add_smul]
  | @homogeneous e b =>
    induction y using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
    | @homogeneous p y =>
      have hb : op (b : A) ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece e := by
        rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]
        exact b.property
      have hby : op (b : A) • (y : M) ∈ (InternalGrading.ofDecomposition M.grading).piece
          (e + p) := by
        rw [InternalGrading.ofDecomposition_piece]
        exact SetLike.GradedSMul.smul_mem hb y.property
      have hy : (y : M) ∈ (InternalGrading.ofDecomposition M.grading).piece p := by
        rw [InternalGrading.ofDecomposition_piece]
        exact y.property
      rw [InternalGrading.koszulTwistAlgEquiv_apply_of_mem 𝒜 n b.property, op_smul, smul_assoc,
        negOnePow_smul_eq_negOnePowCast_smul (R := R), map_smul,
        InternalGrading.koszulTwist_apply_of_mem _ hby,
        InternalGrading.koszulTwist_apply_of_mem _ hy, smul_comm (op (b : A)), smul_smul,
        ← negOnePowCast_eq_intCast, ← negOnePowCast_eq_intCast, ← negOnePowCast_add,
        show n * e + n * (e + p) = 2 * (n * e) + n * p by ring, negOnePowCast_add,
        negOnePowCast_two_mul, one_mul]

/-- The Koszul twist of `M` turns the unsigned differential into `(-1)^n dM`. -/
private theorem koszulTwist_differential (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) (y : M) :
    (InternalGrading.ofDecomposition M.grading).koszulTwist n (M.differential y) =
      n.negOnePow •
        M.differential ((InternalGrading.ofDecomposition M.grading).koszulTwist n y) := by
  have hd : LinearMap.IsHomogeneous M.differential
      (InternalGrading.ofDecomposition M.grading).piece
      (InternalGrading.ofDecomposition M.grading).piece 1 := by
    rw [InternalGrading.ofDecomposition_piece]
    exact M.isDGRightModule.isHomogeneous
  rw [hd.koszulTwist_apply n y, mul_one, ← negOnePowCast_eq_intCast,
    ← negOnePow_smul_eq_negOnePowCast_smul]

/-- The Koszul sign `(-1)^(n p)` on the elements of degree `p` of `M`, as a right-linear
equivalence from `M ⊗ R[n]` to `M[n]`. -/
private noncomputable def rightShiftLinearEquivShift (M : DGRightModuleCat.{uR, uA, uM} h)
    (n : ℤ) : M.rightShift n ≃ₗ[Aᵐᵒᵖ] M.shift n where
  toFun x := (M.shiftEquiv n).symm
    ((InternalGrading.ofDecomposition M.grading).koszulTwist n (M.rightShiftEquiv n x))
  invFun y := (M.rightShiftEquiv n).symm
    ((InternalGrading.ofDecomposition M.grading).koszulTwist n (M.shiftEquiv n y))
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    rw [rightShiftEquiv_smul, koszulTwist_op_koszulTwistAlgEquiv_smul, op_unop, map_smul,
      RingHom.id_apply]
  left_inv x := (InternalGrading.ofDecomposition M.grading).koszulTwist_koszulTwist n (x : M)
  right_inv y := (InternalGrading.ofDecomposition M.grading).koszulTwist_koszulTwist n (y : M)

/-- Read in `M`, the Koszul equivalence is the Koszul twist of `M`. -/
private theorem shiftEquiv_rightShiftLinearEquivShift (M : DGRightModuleCat.{uR, uA, uM} h)
    (n : ℤ) (x : M.rightShift n) :
    M.shiftEquiv n (M.rightShiftLinearEquivShift n x) =
      (InternalGrading.ofDecomposition M.grading).koszulTwist n (M.rightShiftEquiv n x) :=
  LinearEquiv.apply_symm_apply _ _

/-- Read in `M`, the inverse Koszul equivalence is the Koszul twist of `M`. -/
private theorem rightShiftEquiv_rightShiftLinearEquivShift_symm
    (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) (x : M.shift n) :
    M.rightShiftEquiv n ((M.rightShiftLinearEquivShift n).symm x) =
      (InternalGrading.ofDecomposition M.grading).koszulTwist n (M.shiftEquiv n x) :=
  LinearEquiv.apply_symm_apply _ _

/-- **Exchanging the suspensions**: the isomorphism `M ⊗ R[n] ≅ M[n]` which multiplies an element
of degree `p` of `M` by the Koszul sign `(-1)^(n p)`. -/
noncomputable def rightShiftIsoShift (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) :
    M.rightShift n ≅ M.shift n :=
  isoMk (M.rightShiftLinearEquivShift n)
    (fun q x ↦ by
      rw [← rightShiftEquiv_mem_grading_iff, ← shiftEquiv_mem_grading_iff,
        shiftEquiv_rightShiftLinearEquivShift]
      refine ⟨fun hx ↦ InternalGrading.koszulTwist_mem_ofDecomposition _ hx n, fun hx ↦ ?_⟩
      simpa only [InternalGrading.koszulTwist_koszulTwist] using
        InternalGrading.koszulTwist_mem_ofDecomposition _ hx n)
    (fun x ↦ (M.shiftEquiv n).injective <| by
      rw [shiftEquiv_differential, shiftEquiv_rightShiftLinearEquivShift,
        shiftEquiv_rightShiftLinearEquivShift, rightShiftEquiv_differential,
        koszulTwist_differential])

/-- Read in `M`, the isomorphism `M ⊗ R[n] ≅ M[n]` is the Koszul twist of `M`. -/
theorem shiftEquiv_rightShiftIsoShift_hom_apply (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ)
    (x : M.rightShift n) :
    M.shiftEquiv n ((M.rightShiftIsoShift n).hom x) =
      (InternalGrading.ofDecomposition M.grading).koszulTwist n (M.rightShiftEquiv n x) := by
  rw [rightShiftIsoShift, isoMk_hom_apply]
  exact M.shiftEquiv_rightShiftLinearEquivShift n x

/-- Read in `M`, the inverse isomorphism `M[n] ≅ M ⊗ R[n]` is the Koszul twist of `M`. -/
theorem rightShiftEquiv_rightShiftIsoShift_inv_apply (M : DGRightModuleCat.{uR, uA, uM} h)
    (n : ℤ) (x : M.shift n) :
    M.rightShiftEquiv n ((M.rightShiftIsoShift n).inv x) =
      (InternalGrading.ofDecomposition M.grading).koszulTwist n (M.shiftEquiv n x) := by
  rw [rightShiftIsoShift, isoMk_inv_apply]
  exact M.rightShiftEquiv_rightShiftLinearEquivShift_symm n x

/-- On an element of degree `p` of `M`, the isomorphism `M ⊗ R[n] ≅ M[n]` is multiplication by
`(-1)^(n p)`. -/
theorem shiftEquiv_rightShiftIsoShift_hom_apply_of_mem (M : DGRightModuleCat.{uR, uA, uM} h)
    (n : ℤ) {p : ℤ} {x : M.rightShift n} (hx : M.rightShiftEquiv n x ∈ M.grading p) :
    M.shiftEquiv n ((M.rightShiftIsoShift n).hom x) =
      (n * p).negOnePow • M.rightShiftEquiv n x := by
  rw [shiftEquiv_rightShiftIsoShift_hom_apply, InternalGrading.koszulTwist_apply_of_mem _
      (by rwa [InternalGrading.ofDecomposition_piece]),
    ← negOnePowCast_eq_intCast, ← negOnePow_smul_eq_negOnePowCast_smul]

/-- On an element of degree `p` of `M`, the inverse isomorphism `M[n] ≅ M ⊗ R[n]` is again
multiplication by `(-1)^(n p)`. -/
theorem rightShiftEquiv_rightShiftIsoShift_inv_apply_of_mem (M : DGRightModuleCat.{uR, uA, uM} h)
    (n : ℤ) {p : ℤ} {x : M.shift n} (hx : M.shiftEquiv n x ∈ M.grading p) :
    M.rightShiftEquiv n ((M.rightShiftIsoShift n).inv x) =
      (n * p).negOnePow • M.shiftEquiv n x := by
  rw [rightShiftEquiv_rightShiftIsoShift_inv_apply, InternalGrading.koszulTwist_apply_of_mem _
      (by rwa [InternalGrading.ofDecomposition_piece]),
    ← negOnePowCast_eq_intCast, ← negOnePow_smul_eq_negOnePowCast_smul]

/-- The isomorphisms `M ⊗ R[n] ≅ M[n]` are natural in `M`. -/
noncomputable def rightShiftFunctorIsoShiftFunctor (n : ℤ) :
    rightShiftFunctor.{uR, uA, uM} (h := h) n ≅ shiftFunctor n :=
  NatIso.ofComponents (fun M ↦ M.rightShiftIsoShift n) fun {M N} f ↦ hom_ext fun x ↦ by
    -- A morphism preserves degrees, so it commutes with the Koszul twists.
    have hf : LinearMap.IsHomogeneous (f.toLinearMap.restrictScalars R)
        (InternalGrading.ofDecomposition M.grading).piece
        (InternalGrading.ofDecomposition N.grading).piece 0 :=
      LinearMap.isHomogeneous_def.mpr fun q y hy ↦ by
        simpa only [InternalGrading.ofDecomposition_piece, add_zero,
          LinearMap.coe_restrictScalars] using
          f.map_mem' (by simpa only [InternalGrading.ofDecomposition_piece] using hy)
    refine (N.shiftEquiv n).injective ?_
    rw [comp_apply, comp_apply, shiftEquiv_rightShiftIsoShift_hom_apply,
      rightShiftEquiv_rightShiftFunctor_map, shiftEquiv_shiftFunctor_map,
      shiftEquiv_rightShiftIsoShift_hom_apply]
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.coe_restrictScalars, DGRightModuleHom.coe_toLinearMap] using
      hf.koszulTwist_apply n (M.rightShiftEquiv n x)

/-- The component of `rightShiftFunctorIsoShiftFunctor` at `M` is `rightShiftIsoShift`. -/
@[simp]
theorem rightShiftFunctorIsoShiftFunctor_hom_app (n : ℤ) (M : DGRightModuleCat.{uR, uA, uM} h) :
    (rightShiftFunctorIsoShiftFunctor n).hom.app M = (M.rightShiftIsoShift n).hom :=
  (rfl)

/-- The inverse component of `rightShiftFunctorIsoShiftFunctor` at `M` is the inverse of
`rightShiftIsoShift`. -/
@[simp]
theorem rightShiftFunctorIsoShiftFunctor_inv_app (n : ℤ) (M : DGRightModuleCat.{uR, uA, uM} h) :
    (rightShiftFunctorIsoShiftFunctor n).inv.app M = (M.rightShiftIsoShift n).inv :=
  (rfl)

end TauCeti.DGRightModuleCat
