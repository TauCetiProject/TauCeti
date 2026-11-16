/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.LinearAlgebra.Exact
public import TauCeti.LinearAlgebra.Dual.FiniteProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Homology and snake inputs of short complexes of modules

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

Finally, given a commuting morphism `(T₀, T₁, T₂)` between two exact sequences of `R`-modules
`E₀ → E₁ → E₂ → 0` and `0 → F₀ → F₁ → F₂`, `CategoryTheory.ShortComplex.moduleCatSnakeInput`
packages the diagram into Mathlib's `ShortComplex.SnakeInput (ModuleCat R)` with concrete kernel
and cokernel rows, and characterizes the categorical connecting morphism `δ` elementwise via
`SnakeInput.δ_eq` (`CategoryTheory.ShortComplex.moduleCatSnakeInput_δ_apply`).

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

section Snake

variable {R : Type u} [Ring R]
  {E₀ E₁ E₂ F₀ F₁ F₂ : Type v}
  [AddCommGroup E₀] [Module R E₀] [AddCommGroup E₁] [Module R E₁] [AddCommGroup E₂] [Module R E₂]
  [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₂] [Module R F₂]
  {i : E₀ →ₗ[R] E₁} {p : E₁ →ₗ[R] E₂}
  {j : F₀ →ₗ[R] F₁} {q : F₁ →ₗ[R] F₂}
  {T₀ : E₀ →ₗ[R] F₀} {T₁ : E₁ →ₗ[R] F₁} {T₂ : E₂ →ₗ[R] F₂}

/-- **Concrete `SnakeInput` in `ModuleCat R`.** Given exact sequences `E₀ --i--> E₁ --p--> E₂ → 0`
and `0 → F₀ --j--> F₁ --q--> F₂` with commuting vertical linear maps `(T₀, T₁, T₂)`, packages the
diagram into Mathlib's `ShortComplex.SnakeInput (ModuleCat R)` with concrete kernel row
`ker T₀ → ker T₁ → ker T₂` and concrete cokernel row
`F₀ ⧸ range T₀ → F₁ ⧸ range T₁ → F₂ ⧸ range T₂`. The body is exposed so that the categorical
connecting map `δ` has concrete domain `ker T₂` and codomain `F₀ ⧸ range T₀`. -/
@[expose, simps! L₀ L₁ L₂ L₃ v₀₁ v₁₂ v₂₃]
noncomputable def moduleCatSnakeInput
    (hip : Function.Exact i p) (hp : Function.Surjective p)
    (hj : Function.Injective j) (hjq : Function.Exact j q)
    (h₁ : j ∘ₗ T₀ = T₁ ∘ₗ i) (h₂ : q ∘ₗ T₁ = T₂ ∘ₗ p) :
    ShortComplex.SnakeInput (ModuleCat.{v} R) where
  L₀ := ShortComplex.moduleCatMk
    (i.restrict fun x hx ↦ LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, ← h₁, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero])
    (p.restrict fun x hx ↦ LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, ← h₂, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero])
    (by ext x; exact hip.apply_apply_eq_zero x.1)
  L₁ := ShortComplex.moduleCatMk i p hip.linearMap_comp_eq_zero
  L₂ := ShortComplex.moduleCatMk j q hjq.linearMap_comp_eq_zero
  L₃ := ShortComplex.moduleCatMk
    ((LinearMap.range T₀).mapQ (LinearMap.range T₁) j fun _ ⟨x, hx⟩ ↦
      ⟨i x, by rw [← hx, ← LinearMap.comp_apply, ← h₁, LinearMap.comp_apply]⟩)
    ((LinearMap.range T₁).mapQ (LinearMap.range T₂) q fun _ ⟨x, hx⟩ ↦
      ⟨p x, by rw [← hx, ← LinearMap.comp_apply, ← h₂, LinearMap.comp_apply]⟩)
    (by apply Submodule.linearMap_qext; ext y; simp [hjq.apply_apply_eq_zero y])
  v₀₁ :=
    { τ₁ := ModuleCat.ofHom (LinearMap.ker T₀).subtype
      τ₂ := ModuleCat.ofHom (LinearMap.ker T₁).subtype
      τ₃ := ModuleCat.ofHom (LinearMap.ker T₂).subtype
      comm₁₂ := by ext x; rfl
      comm₂₃ := by ext x; rfl }
  v₁₂ :=
    { τ₁ := ModuleCat.ofHom T₀
      τ₂ := ModuleCat.ofHom T₁
      τ₃ := ModuleCat.ofHom T₂
      comm₁₂ := ModuleCat.hom_ext h₁
      comm₂₃ := ModuleCat.hom_ext h₂ }
  v₂₃ :=
    { τ₁ := ModuleCat.ofHom (LinearMap.range T₀).mkQ
      τ₂ := ModuleCat.ofHom (LinearMap.range T₁).mkQ
      τ₃ := ModuleCat.ofHom (LinearMap.range T₂).mkQ
      comm₁₂ := by ext y; rfl
      comm₂₃ := by ext y; rfl }
  w₀₂ := by ext x <;> exact LinearMap.mem_ker.mp x.2
  w₁₃ := by ext x <;> exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
  h₀ := Fork.IsLimit.mk _
    (fun s ↦
      { τ₁ := ModuleCat.ofHom <| (Fork.ι s).τ₁.hom.codRestrict (LinearMap.ker T₀) fun x ↦
          LinearMap.mem_ker.mpr <|
            congrArg (fun f : s.pt ⟶ _ ↦ f.τ₁.hom x) (KernelFork.condition s)
        τ₂ := ModuleCat.ofHom <| (Fork.ι s).τ₂.hom.codRestrict (LinearMap.ker T₁) fun x ↦
          LinearMap.mem_ker.mpr <|
            congrArg (fun f : s.pt ⟶ _ ↦ f.τ₂.hom x) (KernelFork.condition s)
        τ₃ := ModuleCat.ofHom <| (Fork.ι s).τ₃.hom.codRestrict (LinearMap.ker T₂) fun x ↦
          LinearMap.mem_ker.mpr <|
            congrArg (fun f : s.pt ⟶ _ ↦ f.τ₃.hom x) (KernelFork.condition s)
        comm₁₂ := by ext x; exact Subtype.ext (congrArg (fun f ↦ f.hom x) (Fork.ι s).comm₁₂)
        comm₂₃ := by ext x; exact Subtype.ext (congrArg (fun f ↦ f.hom x) (Fork.ι s).comm₂₃) })
    (fun s ↦ by ext x <;> rfl)
    (fun s m hm ↦ by
      apply ShortComplex.hom_ext
      · ext x; exact Subtype.ext (congrArg (fun f : s.pt ⟶ _ ↦ f.τ₁.hom x) hm)
      · ext x; exact Subtype.ext (congrArg (fun f : s.pt ⟶ _ ↦ f.τ₂.hom x) hm)
      · ext x; exact Subtype.ext (congrArg (fun f : s.pt ⟶ _ ↦ f.τ₃.hom x) hm))
  h₃ := Cofork.IsColimit.mk _
    (fun s ↦
      { τ₁ := ModuleCat.ofHom <| (LinearMap.range T₀).liftQ (Cofork.π s).τ₁.hom <|
          LinearMap.range_le_ker_iff.mpr <| LinearMap.ext fun x ↦
            congrArg (fun f : _ ⟶ s.pt ↦ f.τ₁.hom x) (CokernelCofork.condition s)
        τ₂ := ModuleCat.ofHom <| (LinearMap.range T₁).liftQ (Cofork.π s).τ₂.hom <|
          LinearMap.range_le_ker_iff.mpr <| LinearMap.ext fun x ↦
            congrArg (fun f : _ ⟶ s.pt ↦ f.τ₂.hom x) (CokernelCofork.condition s)
        τ₃ := ModuleCat.ofHom <| (LinearMap.range T₂).liftQ (Cofork.π s).τ₃.hom <|
          LinearMap.range_le_ker_iff.mpr <| LinearMap.ext fun x ↦
            congrArg (fun f : _ ⟶ s.pt ↦ f.τ₃.hom x) (CokernelCofork.condition s)
        comm₁₂ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦
          congrArg (fun f ↦ f.hom y) (Cofork.π s).comm₁₂
        comm₂₃ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦
          congrArg (fun f ↦ f.hom y) (Cofork.π s).comm₂₃ })
    (fun s ↦ by ext y <;> rfl)
    (fun s m hm ↦ by
      apply ShortComplex.hom_ext
      · exact ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦
          congrArg (fun f : _ ⟶ s.pt ↦ f.τ₁.hom y) hm
      · exact ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦
          congrArg (fun f : _ ⟶ s.pt ↦ f.τ₂.hom y) hm
      · exact ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦
          congrArg (fun f : _ ⟶ s.pt ↦ f.τ₃.hom y) hm)
  L₁_exact := ModuleCat.shortComplex_exact _ hip
  epi_L₁_g := (ModuleCat.epi_iff_surjective _).mpr hp
  L₂_exact := ModuleCat.shortComplex_exact _ hjq
  mono_L₂_f := (ModuleCat.mono_iff_injective _).mpr hj

/-- **Elementwise characterization of the snake connecting map**: if `p x₁ = x₂` and
`j y₀ = T₁ x₁`, then `(moduleCatSnakeInput ...).δ` sends `x₂` to `[y₀]` in `F₀ ⧸ range T₀`. -/
theorem moduleCatSnakeInput_δ_apply
    (hip : Function.Exact i p) (hp : Function.Surjective p)
    (hj : Function.Injective j) (hjq : Function.Exact j q)
    (h₁ : j ∘ₗ T₀ = T₁ ∘ₗ i) (h₂ : q ∘ₗ T₁ = T₂ ∘ₗ p)
    (x₂ : LinearMap.ker T₂) {x₁ : E₁} (hx₁ : p x₁ = x₂)
    {y₀ : F₀} (hy₀ : j y₀ = T₁ x₁) :
    (moduleCatSnakeInput hip hp hj hjq h₁ h₂).δ.hom x₂ = Submodule.Quotient.mk y₀ := by
  let S := moduleCatSnakeInput hip hp hj hjq h₁ h₂
  -- Test `S.δ_eq` on the submodule `W` of all zigzag triples `(a₂, a₁, b₀)` with `p a₁ = a₂` and
  -- `j b₀ = T₁ a₁`, staying in universe `v` with no constraint on `R`.
  let W : Submodule R (LinearMap.ker T₂ × E₁ × F₀) :=
    { carrier := {w | p w.2.1 = w.1.1 ∧ j w.2.2 = T₁ w.2.1}
      add_mem' := fun {a b} ha hb ↦ ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun _ {_} ha ↦ ⟨by simp [ha.1], by simp [ha.2]⟩ }
  let π₁ : ModuleCat.of R W ⟶ S.L₀.X₃ :=
    ModuleCat.ofHom (LinearMap.fst R (LinearMap.ker T₂) (E₁ × F₀) ∘ₗ W.subtype)
  let π₂ : ModuleCat.of R W ⟶ S.L₁.X₂ :=
    ModuleCat.ofHom (LinearMap.fst R E₁ F₀ ∘ₗ
      LinearMap.snd R (LinearMap.ker T₂) (E₁ × F₀) ∘ₗ W.subtype)
  let π₃ : ModuleCat.of R W ⟶ S.L₂.X₁ :=
    ModuleCat.ofHom (LinearMap.snd R E₁ F₀ ∘ₗ
      LinearMap.snd R (LinearMap.ker T₂) (E₁ × F₀) ∘ₗ W.subtype)
  have hδ := S.δ_eq π₁ π₂ π₃ (by ext w; exact w.2.1) (by ext w; exact w.2.2)
  exact congrArg (fun f : ModuleCat.of R W ⟶ S.L₃.X₁ ↦ f.hom ⟨(x₂, x₁, y₀), hx₁, hy₀⟩) hδ

end Snake

end CategoryTheory.ShortComplex
