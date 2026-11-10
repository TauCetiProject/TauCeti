/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.LinearAlgebra.Exact
public import TauCeti.LinearAlgebra.Dual.FiniteProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Homology of short complexes of modules

For a short complex `X₁ ⟶ X₂ ⟶ X₃` of modules, its homology is the kernel of the second map
modulo the range of the first.  The projection of Mathlib's explicit left homology data
`S.moduleCatLeftHomologyData` from the kernel onto the homology is surjective, and identifies two
elements exactly when their difference is in the range of the first map
(`CategoryTheory.ShortComplex.moduleCatLeftHomologyData_π_hom_eq_iff`).  This file also records
two finiteness consequences of that description:

* over a ring for which the middle module is noetherian, the homology is finitely generated;
* over a ring satisfying the strong rank condition, when the middle term is finite, the
  homology has rank at most that of the middle term; if the ring also satisfies rank-nullity
  (for instance a division ring or a commutative domain), the rank of the homology plus the rank
  of the range of the first map is the rank of the kernel of the second.

It also defines the `A`-dual `X₃* ⟶ X₂* ⟶ X₁*` of a short complex of left `A`-modules, a short
complex of right `A`-modules (`CategoryTheory.ShortComplex.moduleCatOpDual`), and shows that the
dual of a short exact sequence is short exact when every functional on `X₁` extends to `X₂`
(`CategoryTheory.ShortComplex.ShortExact.moduleCatOpDual`).

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.1 and 1.3.
-/

public section

open CategoryTheory Limits Module Cardinal

universe u v

namespace CategoryTheory.ShortComplex

/-- The homology of a short complex of modules with noetherian middle term is finitely generated. -/
theorem finite_homology {k : Type u} [Ring k] (S : ShortComplex (ModuleCat.{v} k))
    [IsNoetherian k S.X₂] : Module.Finite k S.homology :=
  -- The homology object of `S.moduleCatLeftHomologyData` is this quotient by construction.
  have : Module.Finite k S.moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles))
  .equiv S.moduleCatHomologyIso.toLinearEquiv.symm

variable {k : Type u} [Ring k] [StrongRankCondition k]

/-- For a short complex `X₁ ⟶ X₂ ⟶ X₃` of modules with `X₂` finite, over a ring satisfying
rank-nullity and the strong rank condition (for instance a division ring or a commutative domain),
the rank of the homology plus the rank of `im f` is the rank of `ker g`. -/
theorem finrank_homology_add_finrank_range_f [HasRankNullity.{v} k]
    (S : ShortComplex (ModuleCat.{v} k)) [Module.Finite k S.X₂] :
    finrank k S.homology + finrank k (LinearMap.range S.f.hom) =
      finrank k (LinearMap.ker S.g.hom) := by
  have hle : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom := by
    rintro _ ⟨y, rfl⟩
    exact S.moduleCat_zero_apply y
  -- Rank-nullity for the boundaries inside the cycles, at the level of cardinal ranks: the cycles
  -- need not be finitely generated, but their rank is finite as a submodule of `X₂`.
  have h := (LinearMap.range S.moduleCatToCycles).rank_quotient_add_rank
  have hK : Module.rank k (LinearMap.ker S.g.hom) < ℵ₀ :=
    (Submodule.rank_le _).trans_lt (Module.rank_lt_aleph0 k S.X₂)
  rw [← h, add_lt_aleph0_iff] at hK
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq, moduleCatLeftHomologyData_H,
    ← (Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
    ← LinearMap.range_codRestrict _ _ S.moduleCat_zero_apply]
  simp only [finrank, ← h, toNat_add hK.1 hK.2]

/-- The homology of a short complex of modules with finite middle term, over a ring satisfying
the strong rank condition, has rank at most that of the middle term. -/
theorem finrank_homology_le_finrank_X₂ (S : ShortComplex (ModuleCat.{v} k)) [Module.Finite k S.X₂] :
    finrank k S.homology ≤ finrank k S.X₂ := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq, moduleCatLeftHomologyData_H]
  exact toNat_le_toNat ((rank_quotient_le _).trans (Submodule.rank_le _))
    (Module.rank_lt_aleph0 k S.X₂)

section LeftHomologyData

variable {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R))

/-- Two cycles of a short complex of modules have the same class in the explicit left homology
exactly when their difference is a boundary. -/
lemma moduleCatLeftHomologyData_π_hom_eq_iff (c c' : LinearMap.ker S.g.hom) :
    S.moduleCatLeftHomologyData.π.hom c = S.moduleCatLeftHomologyData.π.hom c' ↔
      ∃ y, S.f.hom y = (c : S.X₂) - c' :=
  (Submodule.Quotient.eq _).trans
    ⟨fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩⟩

/-- Every class of the explicit left homology of a short complex of modules is the class of a
cycle. -/
lemma moduleCatLeftHomologyData_π_hom_surjective :
    Function.Surjective S.moduleCatLeftHomologyData.π.hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

end LeftHomologyData

section OpDual

variable {A : Type u} [Ring A] (S : ShortComplex (ModuleCat.{v} A))

/-- The `A`-dual `X₃* ⟶ X₂* ⟶ X₁*` of a short complex of left `A`-modules, a short complex of
right `A`-modules, that is, of `Aᵐᵒᵖ`-modules. Both maps are precomposition. The body is exposed so
that the `simps` lemmas for the two maps can be stated between the dual modules. -/
@[expose, simps X₁ X₂ X₃ f g]
noncomputable def moduleCatOpDual : ShortComplex (ModuleCat.{max u v} Aᵐᵒᵖ) where
  X₁ := ModuleCat.of Aᵐᵒᵖ (Module.Dual A S.X₃)
  X₂ := ModuleCat.of Aᵐᵒᵖ (Module.Dual A S.X₂)
  X₃ := ModuleCat.of Aᵐᵒᵖ (Module.Dual A S.X₁)
  f := ModuleCat.ofHom (S.g.hom.lcomp Aᵐᵒᵖ A)
  g := ModuleCat.ofHom (S.f.hom.lcomp Aᵐᵒᵖ A)
  zero := by
    ext φ x
    simp [← LinearMap.comp_apply S.g.hom S.f.hom, ← ModuleCat.hom_comp]

/-- The dual of a finitely generated projective middle term is projective. -/
instance [Module.Finite A S.X₂] [Module.Projective A S.X₂] : Projective S.moduleCatOpDual.X₂ := by
  rw [moduleCatOpDual_X₂]
  infer_instance

variable {S}

/-- **Dualizing a short exact sequence**: if every functional on `X₁` extends to `X₂`, the dual
`0 ⟶ X₃* ⟶ X₂* ⟶ X₁* ⟶ 0` of a short exact sequence is short exact. -/
theorem ShortExact.moduleCatOpDual (hS : S.ShortExact)
    (hext : Function.Surjective (S.f.hom.lcomp Aᵐᵒᵖ A)) : S.moduleCatOpDual.ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (((ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact).lcomp_of_surjective A
      hS.moduleCat_surjective_g)
    (LinearMap.lcomp_injective_of_surjective _ hS.moduleCat_surjective_g) hext

end OpDual

end CategoryTheory.ShortComplex
