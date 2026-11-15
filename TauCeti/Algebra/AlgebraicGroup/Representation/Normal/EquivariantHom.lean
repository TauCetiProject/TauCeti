/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Invariants
public import TauCeti.Algebra.Coalgebra.Comodule.LinearHom

/-!
# Normal-subgroup equivariant linear maps

For the normal closed subgroup cut out by a Hopf ideal `I` in a reduced finite-type
Hopf algebra `H` over an algebraically closed field, the subgroup-invariant vectors in the
linear Hom comodule form an ambient subcomodule. The source is finite-dimensional and the
target is arbitrary; the Hom criteria work over any commutative base ring with a finite
projective source. Its elements are exactly the maps intertwining the subgroup's actions over
its coordinate algebra, equivalently over every commutative coefficient algebra. No reducedness
is assumed for the subgroup or for the coefficient algebra.

Applied to endomorphisms of a representation spanned by subgroup character spaces, this is the
conjugation representation on subgroup-equivariant endomorphisms. Such endomorphisms preserve
every character space. This representation is used to realize normal closed subgroups as
kernels of representations.

The construction uses `HopfIdeal.IsNormal.weightSpaceOneSubcomodule`, the existing
`Comodule.linearHom` and its scalar-extension conjugation formula; subgroup invariance is detected
at the universal subgroup point rather than at rational points of the subgroup.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §11.5.
* A. Borel, *Linear Algebraic Groups*, §5.5.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {M : Type w} {N : Type x}
variable [AddCommGroup M] [Module R M] [Comodule R H M]
variable [AddCommGroup N] [Module R N] [Comodule R H N]
variable [Module.Finite R M] [Module.Projective R M]
variable (I : HopfIdeal R H)

attribute [local instance] Comodule.linearHom

/-- A linear map is subgroup-invariant in the Hom comodule precisely when its scalar extension
intertwines the actions of the universal subgroup point. -/
@[simp↓]
theorem mem_weightSpace_linearHom_one_iff (f : M →ₗ[R] N) :
    f ∈ I.weightSpace (M →ₗ[R] N) 1 ↔
      f.baseChange (H ⧸ I.toIdeal) ∘ₗ
          Comodule.endOfPoint M (Ideal.Quotient.mkₐ R I.toIdeal) =
        Comodule.endOfPoint N (Ideal.Quotient.mkₐ R I.toIdeal) ∘ₗ
          f.baseChange (H ⧸ I.toIdeal) := by
  rw [mem_weightSpace_iff_endOfPoint, GroupLike.val_one]
  exact Comodule.endOfPoint_linearHom_one_tmul_eq_iff
    (toConv (Ideal.Quotient.mkₐ R I.toIdeal)) f

/-- A subgroup-invariant linear map intertwines subgroup actions over every commutative value
algebra, including nonreduced algebras. -/
theorem baseChange_comp_endOfPoint_of_mem_weightSpace_linearHom_one
    {B : Type y} [CommSemiring B] [Algebra R B]
    (g : H ⧸ I.toIdeal →ₐ[R] B) {f : M →ₗ[R] N}
    (hf : f ∈ I.weightSpace (M →ₗ[R] N) 1) :
    f.baseChange B ∘ₗ Comodule.endOfPoint M (g.comp (Ideal.Quotient.mkₐ R I.toIdeal)) =
      Comodule.endOfPoint N (g.comp (Ideal.Quotient.mkₐ R I.toIdeal)) ∘ₗ f.baseChange B := by
  have hfixed := endOfPoint_comp_mkₐ_tmul_of_mem_weightSpace g 1 hf
  simp only [GroupLike.val_one, map_one, mul_one] at hfixed
  exact (Comodule.endOfPoint_linearHom_one_tmul_eq_iff
    (toConv (g.comp (Ideal.Quotient.mkₐ R I.toIdeal))) f).mp hfixed

/-- Subgroup invariance is equivalent to intertwining every algebra-valued subgroup point. -/
theorem mem_weightSpace_linearHom_one_iff_forall_baseChange_comp_endOfPoint
    (f : M →ₗ[R] N) :
    f ∈ I.weightSpace (M →ₗ[R] N) 1 ↔
      ∀ (B : Type v) [CommSemiring B] [Algebra R B] (g : H ⧸ I.toIdeal →ₐ[R] B),
        f.baseChange B ∘ₗ Comodule.endOfPoint M (g.comp (Ideal.Quotient.mkₐ R I.toIdeal)) =
          Comodule.endOfPoint N (g.comp (Ideal.Quotient.mkₐ R I.toIdeal)) ∘ₗ
            f.baseChange B := by
  refine ⟨fun hf _ _ _ g ↦ I.baseChange_comp_endOfPoint_of_mem_weightSpace_linearHom_one g hf,
    fun hf ↦ (I.mem_weightSpace_linearHom_one_iff f).mpr ?_⟩
  simpa only [AlgHom.id_comp] using hf (H ⧸ I.toIdeal) (AlgHom.id R _)

/-- Composites of subgroup-equivariant linear maps are subgroup-equivariant. -/
theorem comp_mem_weightSpace_linearHom_one
    {P : Type y} [AddCommGroup P] [Module R P] [Comodule R H P]
    [Module.Finite R N] [Module.Projective R N]
    {f : N →ₗ[R] P} {g : M →ₗ[R] N}
    (hf : f ∈ I.weightSpace (N →ₗ[R] P) 1)
    (hg : g ∈ I.weightSpace (M →ₗ[R] N) 1) :
    f ∘ₗ g ∈ I.weightSpace (M →ₗ[R] P) 1 := by
  rw [I.mem_weightSpace_linearHom_one_iff] at hf hg ⊢
  rw [LinearMap.baseChange_comp, LinearMap.comp_assoc, hg, ← LinearMap.comp_assoc, hf,
    LinearMap.comp_assoc]

/-- Subgroup-equivariant linear maps preserve every scheme-theoretic character space. -/
theorem map_mem_weightSpace_of_mem_weightSpace_linearHom_one
    {f : M →ₗ[R] N} (hf : f ∈ I.weightSpace (M →ₗ[R] N) 1)
    {χ : GroupLike R (H ⧸ I.toIdeal)} {m : M} (hm : m ∈ I.weightSpace M χ) :
    f m ∈ I.weightSpace N χ := by
  rw [mem_weightSpace_iff_endOfPoint]
  have h := LinearMap.congr_fun ((I.mem_weightSpace_linearHom_one_iff f).mp hf)
    (1 ⊗ₜ[R] m)
  simp only [LinearMap.comp_apply] at h
  rw [(I.mem_weightSpace_iff_endOfPoint χ m).mp hm] at h
  simpa only [LinearMap.comp_apply, LinearMap.baseChange_tmul] using h.symm

/-- When subgroup character spaces span the source, equivariance is equivalent to preserving
each character space. -/
theorem mem_weightSpace_linearHom_one_iff_forall_mapsTo_weightSpace
    (hspan : ⨆ χ, I.weightSpace M χ = ⊤) (f : M →ₗ[R] N) :
    f ∈ I.weightSpace (M →ₗ[R] N) 1 ↔
      ∀ χ, Set.MapsTo f (I.weightSpace M χ) (I.weightSpace N χ) := by
  refine ⟨fun hf _ _ hm ↦ I.map_mem_weightSpace_of_mem_weightSpace_linearHom_one hf hm,
    fun hf ↦ ?_⟩
  let q := Ideal.Quotient.mkₐ R I.toIdeal
  let ι : M →ₗ[R] (H ⧸ I.toIdeal) ⊗[R] M := TensorProduct.mk R _ M 1
  let l := (f.baseChange _ ∘ₗ Comodule.endOfPoint M q).restrictScalars R ∘ₗ ι
  let r := (Comodule.endOfPoint N q ∘ₗ f.baseChange _).restrictScalars R ∘ₗ ι
  have hle : (⨆ χ, I.weightSpace M χ) ≤ LinearMap.eqLocus l r := by
    refine iSup_le fun χ m hm ↦ ?_
    rw [LinearMap.mem_eqLocus]
    simp only [l, r, ι, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      TensorProduct.mk_apply, LinearMap.baseChange_tmul]
    rw [(I.mem_weightSpace_iff_endOfPoint χ m).mp hm,
      (I.mem_weightSpace_iff_endOfPoint χ (f m)).mp (hf χ hm),
      LinearMap.baseChange_tmul]
  apply (I.mem_weightSpace_linearHom_one_iff f).mpr
  apply TensorProduct.AlgebraTensorModule.ext
  intro b m
  have hm : m ∈ LinearMap.eqLocus l r := hle (hspan ▸ Submodule.mem_top)
  have heq := LinearMap.mem_eqLocus.mp hm
  simp only [l, r, ι, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    TensorProduct.mk_apply] at heq
  -- Pure tensors are scalar multiples of the universal vector `1 ⊗ m`.
  have ht : b ⊗ₜ[R] m = b • (1 ⊗ₜ[R] m) := by simp [TensorProduct.smul_tmul']
  rw [ht]
  simpa only [LinearMap.comp_apply, map_smul] using congrArg (b • ·) heq

section Normal

variable {k : Type u} [Field k] [IsAlgClosed k]
variable [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
variable {V : Type w} {W : Type x}
variable [AddCommGroup V] [Module k V] [Comodule k H V]
variable [AddCommGroup W] [Module k W] [Comodule k H W]
variable [FiniteDimensional k V] {J : HopfIdeal k H}

/-- The normal-subgroup invariant linear Hom representation consists exactly of maps that
intertwine the universal subgroup action. -/
@[simp↓]
theorem IsNormal.mem_weightSpaceOneSubcomodule_linearHom_iff (hJ : J.IsNormal) (f : V →ₗ[k] W) :
    f ∈ hJ.weightSpaceOneSubcomodule (V →ₗ[k] W) ↔
      f.baseChange (H ⧸ J.toIdeal) ∘ₗ
          Comodule.endOfPoint V (Ideal.Quotient.mkₐ k J.toIdeal) =
        Comodule.endOfPoint W (Ideal.Quotient.mkₐ k J.toIdeal) ∘ₗ
          f.baseChange (H ⧸ J.toIdeal) := by
  rw [← Subcomodule.mem_toSubmodule, hJ.weightSpaceOneSubcomodule_toSubmodule]
  exact J.mem_weightSpace_linearHom_one_iff f

/-- If subgroup characters span the source, the normal-subgroup invariant Hom subcomodule
consists exactly of the maps preserving each character space. -/
theorem IsNormal.mem_weightSpaceOneSubcomodule_linearHom_iff_forall_mapsTo_weightSpace
    (hJ : J.IsNormal) (hspan : ⨆ χ, J.weightSpace V χ = ⊤) (f : V →ₗ[k] W) :
    f ∈ hJ.weightSpaceOneSubcomodule (V →ₗ[k] W) ↔
      ∀ χ, Set.MapsTo f (J.weightSpace V χ) (J.weightSpace W χ) := by
  rw [← Subcomodule.mem_toSubmodule, hJ.weightSpaceOneSubcomodule_toSubmodule]
  exact J.mem_weightSpace_linearHom_one_iff_forall_mapsTo_weightSpace hspan f

/-- The identity belongs to the subgroup-equivariant endomorphism representation. -/
theorem IsNormal.id_mem_weightSpaceOneSubcomodule_linearHom (hJ : J.IsNormal) :
    LinearMap.id ∈ hJ.weightSpaceOneSubcomodule (V →ₗ[k] V) := by
  rw [hJ.mem_weightSpaceOneSubcomodule_linearHom_iff]
  simp

/-- The normal-subgroup invariant endomorphism representation is closed under composition. -/
theorem IsNormal.comp_mem_weightSpaceOneSubcomodule_linearHom (hJ : J.IsNormal)
    {f g : V →ₗ[k] V}
    (hf : f ∈ hJ.weightSpaceOneSubcomodule (V →ₗ[k] V))
    (hg : g ∈ hJ.weightSpaceOneSubcomodule (V →ₗ[k] V)) :
    f ∘ₗ g ∈ hJ.weightSpaceOneSubcomodule (V →ₗ[k] V) := by
  rw [← Subcomodule.mem_toSubmodule, hJ.weightSpaceOneSubcomodule_toSubmodule] at hf hg ⊢
  exact J.comp_mem_weightSpace_linearHom_one hf hg

end Normal

end

end TauCeti.HopfIdeal
