/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Modules.Annihilator
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Stalk
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Modules.AffineRestriction
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# The scheme-theoretic support of a quasi-coherent module

Let `M` be a quasi-coherent `𝒪_X`-module of finite type, so that its sections over every affine
open are finitely generated, and let `Ann(M)` be its annihilator ideal sheaf
(`AlgebraicGeometry.Scheme.Modules.annihilator`). This file shows that the closed subscheme
`V(Ann M)` is the scheme-theoretic support of `M`.

* Its underlying closed set is the support `{x | M_x ≠ 0}` of `M`, which is therefore closed.
* `M` is the pushforward of a module on `V(Ann M)`, and `V(Ann M)` is the smallest closed
  subscheme with this property: for a closed immersion `i : Z ⟶ X`, the module `M` is the
  pushforward of a module on `Z` exactly when the ideal sheaf of `i` is contained in `Ann(M)`,
  that is, when `Z` contains `V(Ann M)`.

For a closed immersion `i` whose ideal sheaf annihilates `M`, the module on `Z` is the pullback
`i^* M`: over an affine open `U ⊆ X`, the sections of `i^* M` over `i⁻¹ U` are
`Γ(Z, i⁻¹ U) ⊗ Γ(M, U)` with `Γ(Z, i⁻¹ U) = Γ(X, U) ⧸ I(U)`, and this is `Γ(M, U)` because
`I(U)` kills `Γ(M, U)`. So the unit `M ⟶ i_* i^* M` of the pullback-pushforward adjunction is an
isomorphism. Conversely, functions in the ideal sheaf of any morphism `f : Z ⟶ X` act by zero on
every pushforward `f_* G`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mem_support_annihilator_iff_nontrivial_stalk`: a point lies
  in the support of `Ann(M)` exactly when the stalk of `M` there is nonzero.
* `AlgebraicGeometry.Scheme.Modules.isClosed_setOf_nontrivial_stalk`: the support of a
  quasi-coherent module of finite type is closed.
* `AlgebraicGeometry.Scheme.Modules.isIso_unit_app_of_ker_ideal_le_annihilator`: if the ideal
  sheaf of a closed immersion `i` annihilates the sections of a quasi-coherent `M`, then
  `M ⟶ i_* i^* M` is an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.exists_iso_pushforward_iff_ker_le_annihilator`: `M` is the
  pushforward of a module along a closed immersion `i` exactly when `i.ker ≤ Ann(M)`.
* `AlgebraicGeometry.Scheme.Modules.exists_iso_pushforward_subschemeι_annihilator`: `M` is the
  pushforward of a module on `V(Ann M)`.

## References

* Stacks Project, Lemmas 29.5.1 (056I), 29.5.3 (056J), 29.5.4 (05JU) and
  [Definition 29.5.5](https://stacks.math.columbia.edu/tag/05JV): the support and the
  scheme-theoretic support of a quasi-coherent module of finite type.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Z : Scheme.{u}}

section Support

variable (M : X.Modules) [M.IsQuasicoherent]
  (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U))

/-- **The support of a quasi-coherent module of finite type.** A point `x` lies in the support of
the annihilator ideal sheaf `Ann(M)` exactly when the stalk `M_x` is nonzero. -/
theorem mem_support_annihilator_iff_nontrivial_stalk {x : X} :
    x ∈ (M.annihilator hM).support ↔ Nontrivial (M.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have := hM ⟨U, hU⟩
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have := M.isLocalizedModule_germₗ ⟨x, hxU⟩ hU
  have hzero : x ∈ X.zeroLocus (U := U) (Module.annihilator Γ(X, U) Γ(M, U)) ↔
      Module.annihilator Γ(X, U) Γ(M, U) ≤ p.asIdeal := by
    simp [Scheme.mem_zeroLocus_iff, hU.mem_basicOpen_iff_notMem_primeIdealOf hxU, p,
      IsConcreteLE.le_iff]
  -- Over `U`, both conditions say that `p` lies in the support of the finite module `Γ(M, U)`,
  -- whose localization at `p` is the stalk `M_x`.
  rw [IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU, annihilator_ideal, hzero,
    ← Module.mem_support_iff_of_finite, Module.mem_support_iff]
  let := M.moduleSectionStalk (U := U) ⟨x, hxU⟩
  exact (IsLocalizedModule.iso p.asIdeal.primeCompl (M.germₗ ⟨x, hxU⟩)).toEquiv.nontrivial_congr

include hM in
/-- **The support of a quasi-coherent module of finite type is closed.** It is the support of the
annihilator ideal sheaf. -/
theorem isClosed_setOf_nontrivial_stalk : IsClosed {x : X | Nontrivial (M.presheaf.stalk x)} := by
  convert (M.annihilator hM).support.isClosed using 1
  ext x
  exact (M.mem_support_annihilator_iff_nontrivial_stalk hM).symm

end Support

/-- Functions in the ideal sheaf of a morphism `f : Z ⟶ X` act by zero on the sections of every
pushforward `f_* G` over an affine open. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.ker_ideal_le_annihilator_pushforward (f : Z ⟶ X)
    (G : Z.Modules) (U : X.affineOpens) :
    f.ker.ideal U ≤ Module.annihilator Γ(X, U) Γ((pushforward f).obj G, U) := by
  intro r hr
  have hr := RingHom.mem_ker.mp (f.ideal_ker_le U hr)
  -- `r` acts on `Γ(f_* G, U) = Γ(G, f⁻¹ U)` through `f.app U r = 0`.
  exact Module.mem_annihilator.mpr fun s ↦ by
    rw [TauCeti.AlgebraicGeometry.pushforward_obj_smul, hr, zero_smul]
    -- The zero of `Γ(G, f⁻¹ U)` is the zero of `Γ(f_* G, U)`.
    rfl

/-- If a quasi-coherent module `M` of finite type is the pushforward of a module along a
morphism `f`, then the ideal sheaf of `f` is contained in `Ann(M)`. -/
theorem ker_le_annihilator_of_iso_pushforward {M : X.Modules} [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U)) (f : Z ⟶ X)
    {G : Z.Modules} (e : M ≅ (pushforward f).obj G) : f.ker ≤ M.annihilator hM :=
  IdealSheafData.le_def.mpr fun U ↦ by
    rw [annihilator_ideal, (sectionsLinearEquiv e U).annihilator_eq]
    exact f.ker_ideal_le_annihilator_pushforward G U

/-- **Modules annihilated by the ideal of a closed immersion.** If the ideal sheaf of a closed
immersion `i : Z ⟶ X` annihilates the sections of a quasi-coherent `M` over every affine open,
then the unit `M ⟶ i_* i^* M` of the pullback-pushforward adjunction is an isomorphism, so `M`
is the pushforward of the module `i^* M` on `Z`. -/
theorem isIso_unit_app_of_ker_ideal_le_annihilator (i : Z ⟶ X) [IsClosedImmersion i]
    (M : X.Modules) [M.IsQuasicoherent]
    (h : ∀ U : X.affineOpens, i.ker.ideal U ≤ Module.annihilator Γ(X, U) Γ(M, U)) :
    IsIso ((pullbackPushforwardAdjunction i).unit.app M) := by
  refine Hom.isIso_of_bijective_app (M := M) (N := (pushforward i).obj ((pullback i).obj M)) _
    (U := fun U : X.affineOpens ↦ U.1) (fun U ↦ U.2) (iSup_affineOpens_eq_top X) fun U ↦ ?_
  have hU : IsAffineOpen U.1 := U.2
  have hV := hU.preimage i
  let := (i.app U).hom.toAlgebra
  -- `Γ(X, U) → Γ(Z, i⁻¹ U)` is surjective with kernel `i.ker(U)`, which annihilates `Γ(M, U)`.
  have hb := TensorProduct.mk_one_bijective_of_ker_le_annihilator (R := Γ(X, U))
    (S := Γ(Z, i ⁻¹ᵁ U)) (M := Γ(M, U)) (i.app_surjective U hU)
    ((i.ker_apply U).ge.trans (h U))
  -- Pulling back sections over `U` is `s ↦ 1 ⊗ s` followed by the affine base-change comparison.
  let e := i.pullbackSectionsEquiv M hU hV
  have key : e.symm ∘ i.pullbackSections M U = TensorProduct.mk Γ(X, U) Γ(Z, i ⁻¹ᵁ U) Γ(M, U) 1 :=
    funext fun s ↦ i.pullbackSectionsEquiv_symm_pullbackSections M hU hV s
  have hp : Function.Bijective (i.pullbackSections M U) :=
    (e.symm.bijective.of_comp_iff' _).mp (key ▸ hb)
  -- `Scheme.Hom.pullbackSections` is the unit on sections over `U`.
  rwa [show ⇑(i.pullbackSections M U) = _ from funext (i.pullbackSections_apply M U)] at hp

/-- **Pushforwards along a closed immersion.** A quasi-coherent module `M` of finite type is the
pushforward of a module along a closed immersion `i : Z ⟶ X` exactly when the ideal sheaf of `i`
is contained in the annihilator ideal sheaf `Ann(M)`, that is, when the closed subscheme `Z`
contains `V(Ann M)`. -/
theorem exists_iso_pushforward_iff_ker_le_annihilator {M : X.Modules} [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U)) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (∃ G : Z.Modules, Nonempty (M ≅ (pushforward i).obj G)) ↔ i.ker ≤ M.annihilator hM := by
  refine ⟨fun ⟨_, ⟨e⟩⟩ ↦ ker_le_annihilator_of_iso_pushforward hM i e, fun hle ↦ ?_⟩
  have := isIso_unit_app_of_ker_ideal_le_annihilator i M fun U ↦
    (IdealSheafData.le_def.mp hle U).trans_eq (M.annihilator_ideal hM U)
  exact ⟨(pullback i).obj M, ⟨asIso ((pullbackPushforwardAdjunction i).unit.app M)⟩⟩

/-- **The scheme-theoretic support.** A quasi-coherent module `M` of finite type is the pushforward
of a module on the closed subscheme `V(Ann M)` cut out by its annihilator ideal sheaf. By
`exists_iso_pushforward_iff_ker_le_annihilator`, every closed subscheme with this property
contains `V(Ann M)`. -/
theorem exists_iso_pushforward_subschemeι_annihilator (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U)) :
    ∃ G : (M.annihilator hM).subscheme.Modules,
      Nonempty (M ≅ (pushforward (M.annihilator hM).subschemeι).obj G) :=
  (exists_iso_pushforward_iff_ker_le_annihilator hM _).mpr (IdealSheafData.ker_subschemeι _).le

end AlgebraicGeometry.Scheme.Modules
