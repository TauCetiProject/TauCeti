/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Order.SupIndep

/-!
# Products of submodules

Products of submodules commute with indexed suprema, and a family of products is independent
exactly when both families of factors are. The two coordinate copies `Submodule.fst` and
`Submodule.snd` of the factors of a product module are cut out by the vanishing of the other
coordinate and are complementary. The kernel of a product map `f.prodMap g` is the product of the
kernels, as a module.

## Main declarations

* `TauCeti.iSup_prod_submodule`: products commute with indexed suprema.
* `TauCeti.iSupIndep_prod_iff`, `iSupIndep.prod`: a family of products is independent exactly
  when both families of factors are.
* `Submodule.mem_fst_iff`, `Submodule.mem_snd_iff`: membership in the coordinate copies of the
  factors.
* `Submodule.isCompl_fst_snd`: the coordinate copies of the two factors are complementary.
* `LinearMap.kerProdMapEquiv`: the kernel of `f.prodMap g` is linearly equivalent to
  `ker f × ker g`.
-/

public section

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N]

/-- A vector of a product module lies in the copy of the first factor exactly when its second
coordinate vanishes. -/
@[simp]
theorem mem_fst_iff {x : M × N} : x ∈ Submodule.fst R M N ↔ x.2 = 0 :=
  mem_comap.trans (mem_bot R)

/-- A vector of a product module lies in the copy of the second factor exactly when its first
coordinate vanishes. -/
@[simp]
theorem mem_snd_iff {x : M × N} : x ∈ Submodule.snd R M N ↔ x.1 = 0 :=
  mem_comap.trans (mem_bot R)

variable (R M N)

/-- The copies of the two factors of a product module are complementary submodules. -/
theorem isCompl_fst_snd : IsCompl (Submodule.fst R M N) (Submodule.snd R M N) :=
  .of_eq (fst_inf_snd R M N) (fst_sup_snd R M N)

end Submodule

namespace LinearMap

variable {R M N M' N' : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- The kernel of the product map `f.prodMap g` is the product of the kernels of `f` and `g`
(`LinearMap.ker_prodMap`), here as a linear equivalence `ker (f.prodMap g) ≃ ker f × ker g`
through `Submodule.prodEquiv`. -/
def kerProdMapEquiv (f : M →ₗ[R] N) (g : M' →ₗ[R] N') :
    ker (f.prodMap g) ≃ₗ[R] ker f × ker g :=
  (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv _ _)

@[simp]
theorem coe_kerProdMapEquiv_apply_fst (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (x : ker (f.prodMap g)) :
    ((kerProdMapEquiv f g x).1 : M) = (x : M × M').1 := by
  simp [kerProdMapEquiv]

@[simp]
theorem coe_kerProdMapEquiv_apply_snd (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (x : ker (f.prodMap g)) :
    ((kerProdMapEquiv f g x).2 : M') = (x : M × M').2 := by
  simp [kerProdMapEquiv]

@[simp]
theorem coe_kerProdMapEquiv_symm_apply (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (x : ker f × ker g) :
    ((kerProdMapEquiv f g).symm x : M × M') = ((x.1 : M), (x.2 : M')) := by
  simp [kerProdMapEquiv]

end LinearMap

namespace TauCeti

/-- Taking products of submodules commutes with indexed suprema, including the empty one. -/
@[simp]
theorem iSup_prod_submodule {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (P : ι → Submodule R M) (Q : ι → Submodule R N) :
    (⨆ i, (P i).prod (Q i)) = (⨆ i, P i).prod (⨆ i, Q i) := by
  simp only [LinearMap.prod_eq_sup_map, Submodule.map_iSup, iSup_sup_eq]

/-- A family of componentwise products of submodules is independent exactly when both families
of factors are independent. -/
@[simp] theorem iSupIndep_prod_iff {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {P : ι → Submodule R M} {Q : ι → Submodule R N} :
    iSupIndep (fun i ↦ (P i).prod (Q i)) ↔ iSupIndep P ∧ iSupIndep Q := by
  simp only [iSupIndep, disjoint_iff, iSup_prod_submodule, Submodule.prod_inf_prod,
    Submodule.prod_eq_bot_iff, forall_and]

/-- Componentwise products of independent families of submodules are independent. -/
theorem _root_.iSupIndep.prod {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {P : ι → Submodule R M} {Q : ι → Submodule R N}
    (hP : iSupIndep P) (hQ : iSupIndep Q) : iSupIndep (fun i ↦ (P i).prod (Q i)) :=
  iSupIndep_prod_iff.2 ⟨hP, hQ⟩

end TauCeti
