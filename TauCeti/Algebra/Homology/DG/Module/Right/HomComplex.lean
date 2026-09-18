/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom

/-!
# The Hom complex of differential graded right modules

For two right modules over a differential graded algebra, the degree-`p` cochains are the
right-module linear maps which raise internal degree by `p`.  Their differential is the graded
commutator

`\delta(f) = d_N \circ f - (-1)^p f \circ d_M`.

The right-module convention is important here: homogeneous cochains are ordinary
`A\^op`-linear maps.  The two Leibniz terms involving the differential of the algebra cancel in
the displayed commutator, so it is again `A\^op`-linear and has degree `p + 1`.  This file packages
these cochains and their differential as a cochain complex of modules over the ground ring.  Its
degree-zero cocycles are exactly `TauCeti.DGRightModuleHom`.

## Main definitions

* `TauCeti.dgRightModuleCochains`: homogeneous cochains of a fixed degree between two right DG
  modules.
* `TauCeti.dgRightModuleHomComplex`: the cochain complex of homogeneous right-module maps.

## Implementation notes

`dgRightModuleHomComplex` is exposed because the component types of its public differential
application lemma reduce to the advertised homogeneous-cochain modules.  The element-level API is
given by `dgRightModuleCochains.differential_apply`.

## References

* B. Keller, *Deriving DG categories*, Section 2.
-/

public section

open CategoryTheory DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {ℳN : ℤ → Submodule R N}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
    [DirectSum.Decomposition ℳN] {dN : N →ₗ[R] N}

/-- The `R`-submodule of right-module maps of degree `p` between two differential graded right
modules.  The differential does not enter the definition; it supplies the differential between
successive cochain modules below. -/
def dgRightModuleCochains (p : ℤ) : Submodule R (M →ₗ[Aᵐᵒᵖ] N) where
  carrier := {f | LinearMap.IsHomogeneous (f.restrictScalars R) ℳ ℳN p}
  zero_mem' := LinearMap.isHomogeneous_zero ℳ ℳN p
  add_mem' hf hg := hf.add hg
  smul_mem' r f hf := by
    -- Expose the restricted `R`-linear map so `IsHomogeneous` can be applied degreewise.
    change LinearMap.IsHomogeneous ((r • f).restrictScalars R) ℳ ℳN p
    rw [LinearMap.isHomogeneous_def]
    intro q x hx
    simpa only [LinearMap.restrictScalars_apply, LinearMap.smul_apply] using
      (ℳN (q + p)).smul_mem r (hf.map_mem hx)

namespace dgRightModuleCochains

variable {hM : IsDGRightModule h ℳ dM} {hN : IsDGRightModule h ℳN dN}

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN] in
@[simp, grind =]
theorem mem_iff {p : ℤ} {f : M →ₗ[Aᵐᵒᵖ] N} :
    f ∈ dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p ↔
      LinearMap.IsHomogeneous (f.restrictScalars R) ℳ ℳN p :=
  Iff.rfl

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN] in
/-- A homogeneous right-module cochain applied to an element of degree `q` has degree `q + p`. -/
theorem map_mem {p q : ℤ}
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p)
    {x : M} (hx : x ∈ ℳ q) : f.1 x ∈ ℳN (q + p) :=
  (mem_iff.mp f.2).map_mem hx

private def differentialLinearMap (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) :
    M →ₗ[Aᵐᵒᵖ] N where
  toFun x := dN (f.1 x) - p.negOnePow • f.1 (dM x)
  map_add' x y := by simp only [map_add, smul_add, add_sub_add_comm]
  map_smul' a x := by
    classical
    rw [← DirectSum.sum_support_decompose ℳ x, Finset.smul_sum]
    simp only [map_sum, Finset.smul_sum]
    rw [smul_sub, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    let y : ℳ q := decompose ℳ x q
    have hNq := hN.leibniz (q := q + p) (x := f.1 (y : M))
      (map_mem f (SetLike.coe_mem y)) (unop a)
    have hMq := hM.leibniz (q := q) (x := (y : M)) (SetLike.coe_mem y) (unop a)
    simp only [op_unop] at hNq hMq
    rw [map_smul, hNq, hMq, map_add, map_smul]
    have fmap (z : M) : f.1 (q.negOnePow • z) = q.negOnePow • f.1 z := by
      simp only [Units.smul_def, map_zsmul]
    rw [fmap, map_smul, smul_add]
    have hsign (z : N) :
        (q + p).negOnePow • z = p.negOnePow • q.negOnePow • z := by
      rw [Int.negOnePow_add, mul_comm, mul_smul]
    have hcomm (z : N) : p.negOnePow • a • z = a • p.negOnePow • z :=
      smul_comm _ _ _
    simp only [RingHom.id_apply]
    rw [hsign, hcomm]
    -- Unfold the local homogeneous-component abbreviation so both sides have the same carrier.
    change a • dN (f.1 (y : M)) + _ - _ = a • dN (f.1 (y : M)) - _
    abel

@[simp]
private theorem differentialLinearMap_apply (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p)
    (x : M) :
    (dgRightModuleCochains.differentialLinearMap (hM := hM) (hN := hN) p f) x =
      dN (f.1 x) - p.negOnePow • f.1 (dM x) :=
  (rfl)

/-- The differential on homogeneous right-module cochains. -/
def differential (p : ℤ) :
    dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p →ₗ[R]
      dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) (p + 1) where
  toFun f := ⟨differentialLinearMap (hM := hM) (hN := hN) p f, by
    apply mem_iff.mpr
    rw [LinearMap.isHomogeneous_def]
    intro q x hx
    -- Align the restricted-linear-map coercion with the public application lemma.
    change (differentialLinearMap (hM := hM) (hN := hN) p f) x ∈ ℳN (q + (p + 1))
    rw [differentialLinearMap_apply]
    apply Submodule.sub_mem
    · simpa only [add_assoc] using
        hN.isHomogeneous.map_mem (map_mem f hx)
    · rw [Units.smul_def]
      apply zsmul_mem
      simpa only [add_assoc, add_comm (1 : ℤ) p] using
        map_mem f (hM.isHomogeneous.map_mem hx)⟩
  map_add' f g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    -- The target contains nested submodule coercions, so state their element-level equality.
    change dN ((f + g).1 x) - p.negOnePow • (f + g).1 (dM x) =
      (dN (f.1 x) - p.negOnePow • f.1 (dM x)) +
        (dN (g.1 x) - p.negOnePow • g.1 (dM x))
    simp only [Submodule.coe_add, LinearMap.add_apply, map_add, smul_add]
    abel
  map_smul' r f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    -- The target contains nested submodule coercions, so state their element-level equality.
    change dN ((r • f).1 x) - p.negOnePow • (r • f).1 (dM x) =
      r • (dN (f.1 x) - p.negOnePow • f.1 (dM x))
    simp only [Submodule.coe_smul_of_tower, LinearMap.smul_apply, map_smul, smul_sub]
    rw [smul_comm r p.negOnePow]

/-- Evaluating the differential gives the graded commutator with the module differentials. -/
@[simp]
theorem differential_apply (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p)
    (x : M) :
    ((differential (hM := hM) (hN := hN) p f).1 : M →ₗ[Aᵐᵒᵖ] N) x =
      dN (f.1 x) - p.negOnePow • f.1 (dM x) :=
  (rfl)

/-- The differential on right-module cochains squares to zero. -/
theorem differential_comp_self (p : ℤ) :
    (differential (hM := hM) (hN := hN) (p + 1)).comp
      (differential (hM := hM) (hN := hN) p) = 0 := by
  ext f x
  simp only [LinearMap.comp_apply, differential_apply, map_sub, hN.sq_zero, hM.sq_zero,
    map_zero, smul_zero, sub_zero, Int.negOnePow_succ, Submodule.coe_zero,
    LinearMap.zero_apply]
  rw [Units.smul_def, map_zsmul, ← Units.smul_def]
  simp

end dgRightModuleCochains

/-- The Hom complex between two differential graded right modules.  Its degree-`p` term consists
of the right-module linear maps raising internal degree by `p`, and its differential is the graded
commutator with the two module differentials. -/
@[expose]
def dgRightModuleHomComplex (hM : IsDGRightModule h ℳ dM)
    (hN : IsDGRightModule h ℳN dN) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of
    (fun p ↦ ModuleCat.of R
      (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p))
    (fun p ↦ ModuleCat.ofHom (dgRightModuleCochains.differential (hM := hM) (hN := hN) p))
    (fun p ↦ ModuleCat.hom_ext <| dgRightModuleCochains.differential_comp_self p)

/-- The degree-`p` term of the Hom complex is the module of degree-`p` homogeneous cochains. -/
@[simp]
theorem dgRightModuleHomComplex_X (hM : IsDGRightModule h ℳ dM)
    (hN : IsDGRightModule h ℳN dN) (p : ℤ) :
    (dgRightModuleHomComplex hM hN).X p = ModuleCat.of R
      (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) :=
  rfl

/-- The differential morphism of the Hom complex is induced by the graded commutator map. -/
@[simp]
theorem dgRightModuleHomComplex_d (hM : IsDGRightModule h ℳ dM)
    (hN : IsDGRightModule h ℳN dN) (p : ℤ) :
    (dgRightModuleHomComplex hM hN).d p (p + 1) =
      ModuleCat.ofHom (dgRightModuleCochains.differential (hM := hM) (hN := hN) p) := by
  apply CochainComplex.of_d

/-- The differential of the Hom complex is the graded commutator on homogeneous cochains. -/
@[simp]
theorem dgRightModuleHomComplex_d_apply (hM : IsDGRightModule h ℳ dM)
    (hN : IsDGRightModule h ℳN dN) (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) :
    ModuleCat.Hom.hom
        (A := ModuleCat.of R
          (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p))
        (B := ModuleCat.of R
          (dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) (p + 1)))
        ((dgRightModuleHomComplex hM hN).d p (p + 1)) f =
      dgRightModuleCochains.differential (hM := hM) (hN := hN) p f := by
  -- Identify the abstract complex differential with the map supplied to `CochainComplex.of`.
  rw [dgRightModuleHomComplex_d]
  rfl

/-- Closed degree-zero cochains in the Hom complex are exactly morphisms of differential graded
right modules. -/
def dgRightModuleHomEquivZeroCocycles (hM : IsDGRightModule h ℳ dM)
    (hN : IsDGRightModule h ℳN dN) :
    DGRightModuleHom hM hN ≃ LinearMap.ker
      (dgRightModuleCochains.differential (hM := hM) (hN := hN) 0) where
  toFun f := ⟨⟨f.toLinearMap, by
    apply dgRightModuleCochains.mem_iff.mpr
    rw [LinearMap.isHomogeneous_def]
    intro q x hx
    -- Align the restricted-linear-map projection with the morphism's `FunLike` coercion.
    change f x ∈ ℳN (q + 0)
    simpa only [add_zero] using Graded.map_mem f hx⟩, by
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      simp only [dgRightModuleCochains.differential_apply, Int.negOnePow_zero, one_smul]
      exact sub_eq_zero.mpr (f.map_d x)⟩
  invFun f := {
    toLinearMap := f.1.1
    map_mem' {q} {x} hx := by
      have := dgRightModuleCochains.map_mem f.1 hx
      simpa only [add_zero] using this
    map_d' x := by
      have hx := congrArg
        (fun g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) 1 ↦
          (g.1 : M →ₗ[Aᵐᵒᵖ] N) x) f.2
      simpa only [dgRightModuleCochains.differential_apply, Int.negOnePow_zero, one_smul,
        Submodule.coe_zero, LinearMap.zero_apply, sub_eq_zero] using hx }
  left_inv f := by
    ext x
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl

/-- The zero-cocycle associated to a DG right-module morphism has the same underlying map. -/
@[simp]
theorem dgRightModuleHomEquivZeroCocycles_apply (hM : IsDGRightModule h ℳ dM)
    (hN : IsDGRightModule h ℳN dN) (f : DGRightModuleHom hM hN) (x : M) :
    ((dgRightModuleHomEquivZeroCocycles hM hN f).1.1 : M →ₗ[Aᵐᵒᵖ] N) x = f x :=
  (rfl)

/-- The DG right-module morphism associated to a zero-cocycle has the same underlying map. -/
@[simp]
theorem dgRightModuleHomEquivZeroCocycles_symm_apply (hM : IsDGRightModule h ℳ dM)
    (hN : IsDGRightModule h ℳN dN)
    (f : LinearMap.ker
      (dgRightModuleCochains.differential (hM := hM) (hN := hN) 0)) (x : M) :
    (dgRightModuleHomEquivZeroCocycles hM hN).symm f x = (f.1.1 : M →ₗ[Aᵐᵒᵖ] N) x :=
  (rfl)

end TauCeti
