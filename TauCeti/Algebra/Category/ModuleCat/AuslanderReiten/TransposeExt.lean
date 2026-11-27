/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.ShortExact
public import TauCeti.Algebra.Category.ModuleCat.Projective.Presentation
public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.Algebra.Module.AuslanderReiten.DualPresentation
public import TauCeti.Algebra.Module.Injective.DivisionRing
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Defect
import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Hom
import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Stable.Basic
import TauCeti.Algebra.Homology.Ext.Copresentation
import TauCeti.LinearAlgebra.LinearMap.Range
import TauCeti.LinearAlgebra.LinearMap.RestrictScalars
import TauCeti.RingTheory.MatlisDuality.Semilocal

/-!
# The right transpose of a projective resolution of length one

For a right module `N` presented by `0 → P₁ → P₀ → N → 0`, the right transpose is naturally
`Ext¹(N, A)` in the category of right modules. The comparison sends a functional on `P₁` to
the pushout of the resolution along that functional. The left action of `A` on the transpose
corresponds to pushforward along left multiplication on the right regular module.

Over a field, dualizing the presentation of a right module over a finite-dimensional algebra
gives an injective copresentation of its dual. Computing Ext from that copresentation identifies
the same transpose with `Ext¹(D A, D N)`, where the left action comes from pullbacks in
`D A`. Both comparisons commute with morphisms of presentations.

This computes the transpose in the description of the inverse Auslander–Reiten translate over
hereditary algebras in Grant, *The Nakayama automorphism of a self-injective preprojective
algebra*, https://arxiv.org/abs/1906.11817, Section 2.3 and Proposition 2.5.
-/

public section

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace TauCeti.FiniteProjectivePresentation

universe u w

variable {A : Type u} [Ring A] {N : ModuleCat.{u} Aᵐᵒᵖ}
variable (Q : FiniteProjectivePresentation N)

variable (k : Type w) [CommRing k] [Algebra k A]

private noncomputable def rightTransposeHomCokernelEquiv :
    Q.rightTranspose ≃ₗ[k] HomCokernel k Q.shortComplex.f (ModuleCat.of Aᵐᵒᵖ A) :=
  ((Q.p.lcomp A A).cokerRestrictScalarsEquiv k).symm.trans
    (ModuleCat.covariantDefectEquivHomQuotient k (B := ModuleCat.of Aᵐᵒᵖ A)
      (LinearEquiv.refl Aᵐᵒᵖ A) Q.shortComplex.f)

private theorem rightTransposeHomCokernelEquiv_mk (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    let _ := Linear.homModule (R := k) Q.P₀ (ModuleCat.of Aᵐᵒᵖ A)
    let _ := Linear.homModule (R := k) Q.P₁ (ModuleCat.of Aᵐᵒᵖ A)
    Q.rightTransposeHomCokernelEquiv k (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (ModuleCat.ofHom g) := by
  -- Restricting scalars on `lcomp` gives precomposition over `k` with the same range.
  erw [rightTransposeHomCokernelEquiv, LinearEquiv.trans_apply,
    LinearMap.cokerRestrictScalarsEquiv_symm_mk, ModuleCat.covariantDefectEquivHomQuotient_mk]
  simp

private theorem smul_rightTranspose_functional (a : A) (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    a • g = LinearMap.mulLeft Aᵐᵒᵖ a ∘ₗ g := by
  ext x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_eq_mul]

/-- For a length-one projective resolution of a right module, the right transpose computes
`Ext¹(N, A)`. The left action is described by `rightTransposeEquivExt_smul`. -/
noncomputable def rightTransposeEquivExt (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[k] Ext N (ModuleCat.of Aᵐᵒᵖ A) 1 :=
  have : Projective Q.shortComplex.X₂ := inferInstanceAs (Projective Q.P₀)
  (Q.rightTransposeHomCokernelEquiv k).trans
    (homCokernelEquivExt k (Q.shortExact_shortComplex hp) (ModuleCat.of Aᵐᵒᵖ A))

/-- A functional represents the pushout of the short exact presentation along that functional. -/
@[simp]
theorem rightTransposeEquivExt_mk (hp : Function.Injective Q.p) (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquivExt k hp (Submodule.Quotient.mk g) =
      (Q.shortExact_shortComplex hp).extClass.comp (Ext.mk₀ (ModuleCat.ofHom g)) (add_zero 1) := by
  have : Projective Q.shortComplex.X₂ := inferInstanceAs (Projective Q.P₀)
  rw [rightTransposeEquivExt, LinearEquiv.trans_apply, rightTransposeHomCokernelEquiv_mk,
    homCokernelEquivExt_mk]

/-- Multiplication on the transpose corresponds to pushforward along left multiplication of the
right regular coefficient module. -/
theorem rightTransposeEquivExt_smul (hp : Function.Injective Q.p) (a : A)
    (x : Q.rightTranspose) :
    Q.rightTransposeEquivExt k hp (a • x) = (Q.rightTransposeEquivExt k hp x).comp
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a))) (add_zero 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, rightTransposeEquivExt_mk, rightTransposeEquivExt_mk]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    smul_rightTranspose_functional, ModuleCat.ofHom_comp]

/-- A comparison of resolutions acts on representatives by precomposition on relation modules
and on extension classes by pullback along the map of presented modules. -/
theorem rightTransposeEquivExt_comp {N' : ModuleCat.{u} Aᵐᵒᵖ}
    (P : FiniteProjectivePresentation N') (hQ : Function.Injective Q.p)
    (hP : Function.Injective P.p) (φ : Q.shortComplex ⟶ P.shortComplex) (g : P.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquivExt k hQ (Submodule.Quotient.mk (g ∘ₗ φ.τ₁.hom)) =
      (Ext.mk₀ φ.τ₃).comp (P.rightTransposeEquivExt k hP (Submodule.Quotient.mk g))
        (zero_add 1) := by
  rw [Q.rightTransposeEquivExt_mk k hQ, P.rightTransposeEquivExt_mk k hP,
    ModuleCat.ofHom_comp, ModuleCat.ofHom_hom, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero]
  rw [(Q.shortExact_shortComplex hQ).extClass_naturality (P.shortExact_shortComplex hP) φ,
    Ext.comp_assoc_of_third_deg_zero]

end TauCeti.FiniteProjectivePresentation

namespace TauCeti.FiniteProjectivePresentation

variable (k : Type w) [Field k] {A : Type (max u w)} [Ring A] [Algebra k A]
  [FiniteDimensional k A] {N : ModuleCat.{max u w} Aᵐᵒᵖ}
  (Q : FiniteProjectivePresentation N)

local notation "D" => ModuleCat.matlisDualOpObj k k
local notation "B" => ModuleCat.of Aᵐᵒᵖ A

-- The terms of the mapped opposite complex reduce to the bundled dual modules in rewrites.
attribute [local implicit_reducible] ModuleCat.matlisDualOp

private noncomputable def dualHomCokernelEquiv :
    HomCokernel k Q.shortComplex.f B ≃ₗ[k]
      ((D B ⟶ D Q.P₁) ⧸
        (Linear.rightComp k (D B)
          (Q.shortComplex.op.map (ModuleCat.matlisDualOp k k)).g).range) := by
  letI : Module k (Q.P₀ ⟶ B) := Linear.homModule Q.P₀ B
  letI : Module k (Q.P₁ ⟶ B) := Linear.homModule Q.P₁ B
  have hscalar : ModuleCat.moduleOfAlgebra k B = (inferInstance : Module k A) :=
    Module.ext' _ _ fun c x ↦ (Algebra.commutes c x).symm.trans (Algebra.smul_def c x).symm
  have hB : @IsFiniteLength k _ B _ (ModuleCat.moduleOfAlgebra k B) := by
    rw [hscalar]
    exact isFiniteLength_of_finite k A
  let e₀ : (Q.P₀ ⟶ B) ≃ₗ[k] (D B ⟶ D Q.P₀) :=
    ModuleCat.matlisDualOpHomLinearEquiv (length_quotient_linearMap_self_eq_one k) hB
  let e₁ : (Q.P₁ ⟶ B) ≃ₗ[k] (D B ⟶ D Q.P₁) :=
    ModuleCat.matlisDualOpHomLinearEquiv (length_quotient_linearMap_self_eq_one k) hB
  refine Submodule.Quotient.equiv _ _ e₁
    ((Linear.leftComp k B Q.shortComplex.f).map_range_eq_range_of_comp_eq e₀.surjective ?_)
  apply LinearMap.ext
  intro g
  simp [e₀, e₁, ModuleCat.matlisDualOpMap_comp]

private theorem dualHomCokernelEquiv_mk (f : Q.P₁ ⟶ B) :
    let _ := Linear.homModule (R := k) Q.P₁ B
    Q.dualHomCokernelEquiv k (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (ModuleCat.matlisDualOpMap k k f) := by
  simp only [dualHomCokernelEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.coe_coe, ModuleCat.matlisDualOpHomLinearEquiv_apply]

/-- The transpose of a length-one right projective resolution computes `Ext¹(D A, D N)`
via the dual injective copresentation. For a resolution of `N = D M`, this computes
the inverse Auslander–Reiten translate of `M`. -/
noncomputable def rightTransposeEquivExtDual (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[k] Ext (D B) (D N) 1 :=
  have : Injective (Q.shortComplex.op.map (ModuleCat.matlisDualOp k k)).X₂ :=
    (ExactStructure.abelian_isInjective_iff _).mp
    (isInjective_matlisDualOpObj_of_projective k k Q.P₀)
  (Q.rightTransposeHomCokernelEquiv k).trans
    ((Q.dualHomCokernelEquiv k).trans
      (homCokernelEquivExtOfInjective k ((Q.shortExact_shortComplex hp).matlisDualOp k k) (D B)))

/-- Under the dual comparison, a functional represents the pullback of the dual short exact
sequence along the dual of the functional. -/
@[simp]
theorem rightTransposeEquivExtDual_mk (hp : Function.Injective Q.p) (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquivExtDual k hp (Submodule.Quotient.mk g) =
      (Ext.mk₀ (ModuleCat.matlisDualOpMap k k (ModuleCat.ofHom g))).comp
        ((Q.shortExact_shortComplex hp).matlisDualOp k k).extClass (zero_add 1) := by
  have : Injective (Q.shortComplex.op.map (ModuleCat.matlisDualOp k k)).X₂ :=
    (ExactStructure.abelian_isInjective_iff _).mp
    (isInjective_matlisDualOpObj_of_projective k k Q.P₀)
  rw [rightTransposeEquivExtDual, LinearEquiv.trans_apply, rightTransposeHomCokernelEquiv_mk,
    LinearEquiv.trans_apply, dualHomCokernelEquiv_mk, homCokernelEquivExtOfInjective_mk]

/-- The left action on the transpose corresponds to pulling back along the dual of left
multiplication on the right regular module. -/
theorem rightTransposeEquivExtDual_smul (hp : Function.Injective Q.p) (a : A)
    (x : Q.rightTranspose) :
    Q.rightTransposeEquivExtDual k hp (a • x) =
      (Ext.mk₀ (ModuleCat.matlisDualOpMap k k (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)))).comp
        (Q.rightTransposeEquivExtDual k hp x) (zero_add 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, rightTransposeEquivExtDual_mk, rightTransposeEquivExtDual_mk]
  rw [Ext.mk₀_comp_mk₀_assoc, smul_rightTranspose_functional, ModuleCat.ofHom_comp,
    ModuleCat.matlisDualOpMap_comp]

/-- Precomposition on relation modules agrees, under the dual comparison, with pushforward along
the dual of the map of presented modules. -/
theorem rightTransposeEquivExtDual_comp {N' : ModuleCat.{max u w} Aᵐᵒᵖ}
    (P : FiniteProjectivePresentation N') (hQ : Function.Injective Q.p)
    (hP : Function.Injective P.p) (φ : Q.shortComplex ⟶ P.shortComplex)
    (g : P.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquivExtDual k hQ (Submodule.Quotient.mk (g ∘ₗ φ.τ₁.hom)) =
      (P.rightTransposeEquivExtDual k hP (Submodule.Quotient.mk g)).comp
        (Ext.mk₀ (ModuleCat.matlisDualOpMap k k φ.τ₃)) (add_zero 1) := by
  let Df := ModuleCat.matlisDualOp k k (A := A)
  let ψ : P.shortComplex.op.map Df ⟶ Q.shortComplex.op.map Df :=
    Df.mapShortComplex.map (ShortComplex.opMap φ)
  have hmap : ModuleCat.matlisDualOpMap k k (φ.τ₁ ≫ ModuleCat.ofHom g) =
      ModuleCat.matlisDualOpMap k k (ModuleCat.ofHom g) ≫ ψ.τ₃ := by
    simp [ψ, Df, ModuleCat.matlisDualOpMap_comp]
  have hclass :=
    ((P.shortExact_shortComplex hP).matlisDualOp k k).extClass_naturality
      ((Q.shortExact_shortComplex hQ).matlisDualOp k k) ψ
  rw [Q.rightTransposeEquivExtDual_mk k hQ, P.rightTransposeEquivExtDual_mk k hP,
    ModuleCat.ofHom_comp, ModuleCat.ofHom_hom, hmap, ← Ext.mk₀_comp_mk₀_assoc,
    ← hclass, ← Ext.comp_assoc_of_third_deg_zero]
  simp [ψ, Df]

end TauCeti.FiniteProjectivePresentation
