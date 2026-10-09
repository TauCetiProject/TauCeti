/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Complex

/-!
# The Hom complex of differential graded bimodules

For DG `(A, B)`-bimodules, a degree-`p` cochain is a homogeneous right `B`-linear map
satisfying `f(a • x) = (-1)^(p*r) • (a • f(x))` for `a` of degree `r`. Its differential
is `δ(f) = dN ∘ f - (-1)^p • f ∘ dM`. This differential preserves signed left linearity,
giving a subcomplex of the Hom complex of right DG `B`-modules.

The closed degree-zero cochains are linearly identified with `DGBimoduleHom`: in degree zero,
the signed left-action law is ordinary left linearity, and closedness is compatibility with
the module differentials.

## References

* B. Keller, *Deriving DG categories*, Sections 1.2, 2.1 and 6.1.
-/

public section

open CategoryTheory DirectSum

namespace TauCeti

universe uR uA uB uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {M : Type uM} {N : Type uN}
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}

/-- Homogeneous right-linear cochains with signed left linearity. For a degree-`p` map,
left multiplication by an element of degree `r` contributes the sign `(-1)^(p*r)`. -/
def dgBimoduleCochains (p : ℤ) :
    Submodule R (dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p) where
  carrier := {f | ∀ {r : ℤ} {a : A}, a ∈ 𝒜 r → ∀ x : M,
    f.1 (a • x) = (p * r).negOnePow • (a • f.1 x)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg r a ha x
    simp only [Submodule.coe_add, LinearMap.add_apply, hf ha, hg ha, smul_add]
  smul_mem' := by
    intro c f hf r a ha x
    simp only [Submodule.coe_smul_of_tower, LinearMap.smul_apply, hf ha]
    rw [smul_comm c (p * r).negOnePow, smul_comm c a]

namespace dgBimoduleCochains

section Elementary

omit [GradedAlgebra 𝒜] [IsScalarTower R A M]
  [SMulCommClass A Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ N]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩]

/-- Membership is the signed left-action law; right linearity and degree are supplied by
the ambient right-module cochain. -/
@[simp, grind =]
theorem mem_iff {p : ℤ}
    {f : dgRightModuleCochains (R := R) (A := B) (ℳ := ℳ) (ℳN := 𝒩) p} :
    f ∈ dgBimoduleCochains (B := B) (𝒜 := 𝒜) p ↔
      ∀ {r : ℤ} {a : A}, a ∈ 𝒜 r → ∀ x : M,
        f.1 (a • x) = (p * r).negOnePow • (a • f.1 x) :=
  (Iff.rfl)

/-- Two bimodule cochains agree if their underlying functions agree. -/
@[ext]
theorem ext {p : ℤ} {f g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p}
    (hfg : ∀ x, f.1.1 x = g.1.1 x) : f = g :=
  Subtype.ext (Subtype.ext (LinearMap.ext hfg))

/-- A degree-`p` bimodule cochain raises degree by `p`. -/
theorem map_mem {p q : ℤ}
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p)
    {x : M} (hx : x ∈ ℳ q) : f.1.1 x ∈ 𝒩 (q + p) :=
  dgRightModuleCochains.map_mem f.1 hx

/-- Evaluating a cochain on the left action of a homogeneous algebra element. -/
theorem map_smul_left {p r : ℤ}
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p)
    {a : A} (ha : a ∈ 𝒜 r) (x : M) :
    f.1.1 (a • x) = (p * r).negOnePow • (a • f.1.1 x) :=
  mem_iff.mp f.2 ha x

end Elementary

omit [IsScalarTower R A M] [SMulCommClass A Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ N]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] in
/-- In degree zero the signed law extends to the whole algebra, not only homogeneous elements. -/
@[simp]
theorem map_smul_left_zero
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) 0) (a : A) (x : M) :
    f.1.1 (a • x) = a • f.1.1 x := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_smul, map_sum]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_smul]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  simpa only [zero_mul, Int.negOnePow_zero, one_smul] using
    map_smul_left f (SetLike.coe_mem (decompose 𝒜 a r)) x

variable {hM : IsDGBimodule hA hB ℳ dM} {hN : IsDGBimodule hA hB 𝒩 dN}

private theorem differential_mem (p : ℤ)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p) :
    dgRightModuleCochains.differential
      (hM := hM.isDGRightModule) (hN := hN.isDGRightModule) p f.1 ∈
        dgBimoduleCochains (B := B) (𝒜 := 𝒜) (p + 1) := by
  apply mem_iff.mpr
  intro r a ha x
  simp only [dgRightModuleCochains.differential_apply]
  rw [map_smul_left f ha, map_zsmul_unit, hN.leibniz ha, hM.leibniz ha,
    map_add, map_zsmul_unit, map_smul_left f (hA.map_mem ha), map_smul_left f ha]
  -- The two occurrences of the degree-p sign cancel in the coefficient of dA(a).
  have hsign : (p + p * (r + 1)).negOnePow = (p * r).negOnePow := by
    rw [show p + p * (r + 1) = 2 * p + p * r by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]
  simp only [smul_add, smul_sub, smul_comm _ a, smul_smul, ← Int.negOnePow_add, hsign]
  rw [show p + (r + p * r) = (p + 1) * r + p by ring,
    show p * r + r = (p + 1) * r by ring]
  abel

/-- The restriction of the graded commutator `δ(f) = dN ∘ f - (-1)^p • f ∘ dM`
to homogeneous signed bimodule maps. -/
def differential (p : ℤ) :
    dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p →ₗ[R]
      dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) (p + 1) :=
  (dgRightModuleCochains.differential
    (hM := hM.isDGRightModule) (hN := hN.isDGRightModule) p).comp
      (dgBimoduleCochains (B := B) (𝒜 := 𝒜) p).subtype |>.codRestrict _
        (differential_mem (hM := hM) (hN := hN) p)

/-- Evaluation of the differential is the graded commutator. -/
@[simp↓]
theorem differential_apply (p : ℤ)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p) (x : M) :
    (differential (hM := hM) (hN := hN) p f).1.1 x =
      dN (f.1.1 x) - p.negOnePow • f.1.1 (dM x) :=
  dgRightModuleCochains.differential_apply p f.1 x

/-- The bimodule cochain differential squares to zero. -/
theorem differential_comp_self (p : ℤ) :
    (differential (hM := hM) (hN := hN) (p + 1)).comp
      (differential (hM := hM) (hN := hN) p) = 0 := by
  ext f x
  have hfg := LinearMap.congr_fun
    (dgRightModuleCochains.differential_comp_self
      (hM := hM.isDGRightModule) (hN := hN.isDGRightModule) p) f.1
  exact congrArg (fun g ↦ g.1 x) hfg

end dgBimoduleCochains

/-- The Hom cochain complex of DG `(A, B)`-bimodules, over their commutative ground ring. -/
-- Expose the body so its component carriers compute to the bimodule cochain modules.
@[expose]
def dgBimoduleHomComplex (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hA hB 𝒩 dN) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of
    (fun p ↦ ModuleCat.of R (dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p))
    (fun p ↦ ModuleCat.ofHom (dgBimoduleCochains.differential (hM := hM) (hN := hN) p))
    (fun p ↦ ModuleCat.hom_ext <| dgBimoduleCochains.differential_comp_self p)

/-- The degree-`p` term consists of homogeneous signed bimodule maps. -/
@[simp]
theorem dgBimoduleHomComplex_X (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hA hB 𝒩 dN) (p : ℤ) :
    (dgBimoduleHomComplex hM hN).X p =
      ModuleCat.of R (dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p) :=
  rfl

/-- The successor differential is the restricted graded commutator. -/
-- This is a named rewrite: dependent component carriers make simp matching sensitive to
-- normalization of successor indices.
theorem dgBimoduleHomComplex_d (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hA hB 𝒩 dN) (p : ℤ) :
    (dgBimoduleHomComplex hM hN).d p (p + 1) =
      ModuleCat.ofHom (dgBimoduleCochains.differential (hM := hM) (hN := hN) p) := by
  apply CochainComplex.of_d

/-- The Hom-complex differential evaluated on a cochain. -/
@[simp↓]
theorem dgBimoduleHomComplex_d_apply (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hA hB 𝒩 dN) (p : ℤ) (f : (dgBimoduleHomComplex hM hN).X p) :
    ((dgBimoduleHomComplex hM hN).d p (p + 1)).hom f =
      dgBimoduleCochains.differential (hM := hM) (hN := hN) p f := by
  rw [dgBimoduleHomComplex_d]
  exact LinearMap.congr_fun (ModuleCat.hom_ofHom _) f

/-- Closed degree-zero cochains are linearly identified with DG bimodule morphisms.
Both directions preserve the underlying map `M → N`. -/
def dgBimoduleHomLinearEquivZeroCocycles (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hA hB 𝒩 dN) :
    DGBimoduleHom hM hN ≃ₗ[R] LinearMap.ker
      (dgBimoduleCochains.differential (hM := hM) (hN := hN) 0) where
  toFun f := ⟨⟨(dgRightModuleHomLinearEquivZeroCocycles
    hM.isDGRightModule hN.isDGRightModule f.1).1, by
      apply dgBimoduleCochains.mem_iff.mpr
      intro r a ha x
      simpa only [zero_mul, Int.negOnePow_zero, one_smul,
        dgRightModuleHomLinearEquivZeroCocycles_apply, DGBimoduleHom.coe_val] using
        f.map_smul_left a x⟩, by
      apply Subtype.ext
      exact (dgRightModuleHomLinearEquivZeroCocycles
        hM.isDGRightModule hN.isDGRightModule f.1).2⟩
  invFun f := ⟨(dgRightModuleHomLinearEquivZeroCocycles
    hM.isDGRightModule hN.isDGRightModule).symm ⟨f.1.1, by
      -- Kernel membership unfolds to vanishing of the restricted differential;
      -- forgetting its subtype gives the same underlying right-module cochain.
      change dgRightModuleCochains.differential
        (hM := hM.isDGRightModule) (hN := hN.isDGRightModule) 0 f.1.1 = 0
      exact congrArg Subtype.val f.2⟩, by
      apply (mem_dgBimoduleHomSubmodule hM hN _).mpr
      intro a x
      simp only [dgRightModuleHomLinearEquivZeroCocycles_symm_apply]
      exact dgBimoduleCochains.map_smul_left_zero f.1 a x⟩
  left_inv f := by
    apply Subtype.ext
    exact (dgRightModuleHomLinearEquivZeroCocycles
      hM.isDGRightModule hN.isDGRightModule).symm_apply_apply f.1
  right_inv f := by
    ext x
    simp only [dgRightModuleHomLinearEquivZeroCocycles_apply,
      dgRightModuleHomLinearEquivZeroCocycles_symm_apply]
  map_add' f g := by
    ext x
    simp only [dgRightModuleHomLinearEquivZeroCocycles_apply,
      Submodule.coe_add, DGRightModuleHom.add_apply, LinearMap.add_apply]
  map_smul' c f := by
    ext x
    simp only [dgRightModuleHomLinearEquivZeroCocycles_apply,
      Submodule.coe_smul_of_tower, DGRightModuleHom.smul_apply, LinearMap.smul_apply,
      RingHom.id_apply]

/-- The zero-cocycle associated to a bimodule morphism has the same values. -/
@[simp↓]
theorem dgBimoduleHomLinearEquivZeroCocycles_apply (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hA hB 𝒩 dN) (f : DGBimoduleHom hM hN) (x : M) :
    (dgBimoduleHomLinearEquivZeroCocycles hM hN f).1.1.1 x = f x := by
  exact dgRightModuleHomLinearEquivZeroCocycles_apply
    hM.isDGRightModule hN.isDGRightModule f.1 x

/-- Recovering a bimodule morphism from a closed cochain preserves its values. -/
@[simp↓]
theorem dgBimoduleHomLinearEquivZeroCocycles_symm_apply (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hA hB 𝒩 dN)
    (f : LinearMap.ker (dgBimoduleCochains.differential (hM := hM) (hN := hN) 0))
    (x : M) :
    (dgBimoduleHomLinearEquivZeroCocycles hM hN).symm f x = f.1.1.1 x := by
  exact dgRightModuleHomLinearEquivZeroCocycles_symm_apply
    hM.isDGRightModule hN.isDGRightModule _ x

end TauCeti
