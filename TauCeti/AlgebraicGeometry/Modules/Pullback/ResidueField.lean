/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
public import TauCeti.AlgebraicGeometry.ResidueField
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
import TauCeti.RingTheory.TensorProduct.IsBaseChange
import TauCeti.Topology.Sheaves.Presheaf

/-!
# The fibre of a quasi-coherent module at a point

For a point `x` of a scheme `X`, write `ι : Spec κ(x) ⟶ X` for the canonical morphism
`Scheme.fromSpecResidueField`. For a quasi-coherent `𝒪_X`-module `M`, the global sections of the
pullback `ι^* M` are the fibre `κ(x) ⊗_{𝒪_{X,x}} M_x` of `M` at `x`, as `κ(x)`-vector spaces
(`Scheme.Modules.residueFieldPullbackSectionsEquiv`). Under this identification, the value
`c ⊗ m_x` of the germ of a local section `m` of `M` near `x` is `c` times the pullback of `m`
(`Scheme.Modules.residueFieldPullbackSectionsEquiv_tmul_germ`).

The map `κ(x) ⊗_{𝒪_{X,x}} M_x → Γ(Spec κ(x), ι^* M)` is defined without choices, from the
pullback of local sections. It is bijective because on an affine open `U ∋ x` both sides are the
base change `κ(x) ⊗_{Γ(X, U)} Γ(M, U)`: the target by the affine computation of sections of a
pullback (`Scheme.Hom.pullbackSectionsEquiv`), the source because `M_x` is the base change
`𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)` (`Scheme.Modules.isBaseChange_germₗ`). Both computations use that
`ι` sends a function near `x` to its value at `x` (`Scheme.fromSpecResidueField_appLE`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.residueFieldPullbackSectionsEquiv`: the identification
  `κ(x) ⊗_{𝒪_{X,x}} M_x ≃ Γ(Spec κ(x), ι^* M)` for quasi-coherent `M`.

## References

* R. Hartshorne, *Algebraic Geometry*, Propositions II.5.1(b) and II.5.2(e).
* The Stacks Project, [Tag 01I9](https://stacks.math.columbia.edu/tag/01I9).
-/

public section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (x : X) (M : X.Modules)

private lemma top_le_preimage {V : X.Opens} (hx : x ∈ V) :
    (⊤ : (Spec (X.residueField x)).Opens) ≤ X.fromSpecResidueField x ⁻¹ᵁ V :=
  (fromSpecResidueField_preimage_eq_top x hx).ge

/-- The global sections of `ι^* M` over `Spec κ(x)` as an `𝒪_{X,x}`-module, through
`𝒪_{X,x} ⟶ κ(x)`. -/
private local instance stalkModuleFibre :
    Module (X.presheaf.stalk x) Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) :=
  Module.compHom _ (algebraMap (X.presheaf.stalk x) (X.residueField x))

private local instance isScalarTower_stalk_fibre : IsScalarTower (X.presheaf.stalk x)
    (X.residueField x) Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) :=
  IsScalarTower.of_compHom _ _ _

/-- An element of `κ(x)` acts on the global sections of `ι^* M` as the corresponding global
function on `Spec κ(x)`. -/
private lemma residueField_smul_fibre (c : X.residueField x)
    (t : Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤)) :
    c • t = (Scheme.ΓSpecIso (X.residueField x)).inv c • t := by
  rw [smul_Spec_def, TopCat.Presheaf.map_apply_eq_self]

/-- Pulling back to `Spec κ(x)` commutes with restriction between opens containing `x`. -/
private lemma pullbackSectionsLE_res {V W : X.Opens} (i : V ⟶ W) (hx : x ∈ V) (m : Γ(M, W)) :
    Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤ (top_le_preimage x hx)
        (M.presheaf.map i.op m) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M W ⊤
        (top_le_preimage x (i.le hx)) m := by
  rw [Scheme.Hom.pullbackSectionsLE_apply, Scheme.Hom.pullbackSectionsLE_apply,
    ← Scheme.Hom.pullbackSections_restrict, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  -- Both sides restrict along a morphism `⊤ ⟶ ι⁻¹ W`, and `congr` uses that there is only one.
  congr 2

/-- A function near `x` acts on pulled-back sections through its germ at `x`. -/
private lemma pullbackSectionsLE_smul {V : X.Opens} (hx : x ∈ V) (r : Γ(X, V)) (m : Γ(M, V)) :
    Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤ (top_le_preimage x hx)
        (r • m) =
      X.presheaf.germ V x hx r • Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤
        (top_le_preimage x hx) m := by
  have hr : ((X.fromSpecResidueField x).appLE V ⊤ (top_le_preimage x hx)).hom r =
      (Scheme.ΓSpecIso (X.residueField x)).inv (X.evaluation V x hx r) := by
    rw [fromSpecResidueField_appLE x hx, CommRingCat.comp_apply]
  rw [map_smulₛₗ, hr]
  exact (residueField_smul_fibre x M _ _).symm

/-- The value at `x` of local sections near `x`: a germ `m_x` goes to the pullback of `m` along
`ι : Spec κ(x) ⟶ X`. -/
private def fibreStalkMap :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) :=
  M.val.stalkLiftCommRing (S := X.presheaf) x
    (fun V hx ↦ (Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤
      (top_le_preimage x hx)).toAddMonoidHom)
    (fun i hx m ↦ pullbackSectionsLE_res x M i hx m)
    (fun _ hx r m ↦ pullbackSectionsLE_smul x M hx r m)

private lemma fibreStalkMap_germ {V : X.Opens} (hx : x ∈ V) (m : Γ(M, V)) :
    fibreStalkMap x M (M.presheaf.germ V x hx m) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤ (top_le_preimage x hx) m :=
  M.val.stalkLiftCommRing_germ (S := X.presheaf) x _ _ _ V hx m

/-- The fibre map `κ(x) ⊗_{𝒪_{X,x}} M_x → Γ(Spec κ(x), ι^* M)`, `c ⊗ m_x ↦ c • ι^* m`. -/
private def fibreMap :
    X.residueField x ⊗[X.presheaf.stalk x] M.presheaf.stalk x →ₗ[X.residueField x]
      Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) :=
  (fibreStalkMap x M).liftBaseChange (X.residueField x)

section AffineOpen

/-! Fix an open `U` and a point `y ∈ U`, and write `ι : Spec κ(y) ⟶ X`. Through evaluation at `y`
and through `ι`, the residue field `κ(y)`, the sections of `ι^* M` and the functions on `ι⁻¹ U`
are `Γ(X, U)`-modules. -/

variable {U : X.Opens} (y : U)

private local instance algebraSectionResidueField : Algebra Γ(X, U) (X.residueField y) :=
  (X.evaluation U y y.2).hom.toAlgebra

private local instance moduleSectionFibre :
    Module Γ(X, U) Γ((pullback (X.fromSpecResidueField y)).obj M, ⊤) :=
  Module.compHom _ (algebraMap Γ(X, U) (X.residueField y))

private local instance isScalarTower_section_fibre : IsScalarTower Γ(X, U) (X.residueField y)
    Γ((pullback (X.fromSpecResidueField y)).obj M, ⊤) :=
  IsScalarTower.of_compHom _ _ _

private local instance algebraSectionPreimage :
    Algebra Γ(X, U) Γ(Spec (X.residueField y), X.fromSpecResidueField y ⁻¹ᵁ U) :=
  ((X.fromSpecResidueField y).app U).hom.toAlgebra

private lemma isAffineOpen_preimage : IsAffineOpen (X.fromSpecResidueField y ⁻¹ᵁ U) := by
  rw [fromSpecResidueField_preimage_eq_top (y : X) y.2]
  exact isAffineOpen_top _

/-- `κ(y) ≅ Γ(Spec κ(y), ι⁻¹ U)` as `Γ(X, U)`-modules, by restriction from `⊤` to `ι⁻¹ U = ⊤`. -/
private def residueFieldEquivPreimage :
    X.residueField y ≃ₗ[Γ(X, U)] Γ(Spec (X.residueField y), X.fromSpecResidueField y ⁻¹ᵁ U) :=
  have : IsIso (homOfLE le_top : X.fromSpecResidueField y ⁻¹ᵁ U ⟶ ⊤) :=
    homOfLE_isIso_of_eq _ (fromSpecResidueField_preimage_eq_top (y : X) y.2)
  LinearEquiv.ofBijective
    { toFun c := (Spec (X.residueField y)).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (X.residueField y)).inv c)
      map_add' := by simp
      map_smul' r c := by
        -- `ι` acts on `r` as the global function given by its value at `y`.
        have hr : (Spec (X.residueField y)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso (X.residueField y)).inv (X.evaluation U y y.2 r)) =
              (X.fromSpecResidueField y).app U r := by
          rw [← CommRingCat.comp_apply (X.evaluation U y y.2),
            ← fromSpecResidueField_appLE (y : X) y.2 (top_le_preimage (y : X) y.2),
            Scheme.Hom.appLE, CommRingCat.comp_apply,
            ← ConcreteCategory.comp_apply, ← Functor.map_comp, TopCat.Presheaf.map_apply_eq_self]
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.id_apply, map_mul, map_mul]
        exact congrArg (· * _) hr }
    (ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (X.residueField y)).inv ≫
        (Spec (X.residueField y)).presheaf.map (homOfLE le_top).op))

private lemma residueFieldEquivPreimage_apply (c : X.residueField y) :
    residueFieldEquivPreimage y c = (Spec (X.residueField y)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (X.residueField y)).inv c) :=
  (rfl)

/-- Sections of `ι^* M` over `ι⁻¹ U` as the base change `Γ(Spec κ(y), ι⁻¹ U) ⊗_{Γ(X, U)} Γ(M, U)`,
which is Mathlib's `Scheme.Hom.pullbackSectionsEquiv`. -/
private def preimageSectionsEquiv [M.IsQuasicoherent] (hU : IsAffineOpen U) :
    Γ(Spec (X.residueField y), X.fromSpecResidueField y ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Spec
      (X.residueField y), X.fromSpecResidueField y ⁻¹ᵁ U)]
      Γ((pullback (X.fromSpecResidueField y)).obj M, X.fromSpecResidueField y ⁻¹ᵁ U) :=
  (X.fromSpecResidueField y).pullbackSectionsEquiv M hU (isAffineOpen_preimage y)

/-- Restriction from `⊤` to `ι⁻¹ U = ⊤` turns `c ⊗ m ↦ c • ι^* m` into the base change
computation of `Scheme.Hom.pullbackSectionsEquiv`, after `κ(y) ≅ Γ(Spec κ(y), ι⁻¹ U)` on the left
tensor factor. -/
private lemma map_liftBaseChange_eq [M.IsQuasicoherent] (hU : IsAffineOpen U)
    (f : Γ(M, U) →ₗ[Γ(X, U)] Γ((pullback (X.fromSpecResidueField y)).obj M, ⊤))
    (hf : ∀ m, f m = Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField y) M U ⊤
      (top_le_preimage (y : X) y.2) m)
    (t : X.residueField y ⊗[Γ(X, U)] Γ(M, U)) :
    ((pullback (X.fromSpecResidueField y)).obj M).presheaf.map (homOfLE le_top).op
        (f.liftBaseChange (X.residueField y) t) =
      preimageSectionsEquiv M y hU ((residueFieldEquivPreimage y).rTensor Γ(M, U) t) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c m =>
    have h1 : ((pullback (X.fromSpecResidueField y)).obj M).presheaf.map (homOfLE le_top).op
        (f m) = (X.fromSpecResidueField y).pullbackSections M U m := by
      rw [hf, Scheme.Hom.pullbackSectionsLE_apply, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, TopCat.Presheaf.map_apply_eq_self]
    have h2 : preimageSectionsEquiv M y hU (1 ⊗ₜ m) =
        (X.fromSpecResidueField y).pullbackSections M U m :=
      (X.fromSpecResidueField y).pullbackSectionsEquiv_one_tmul M hU (isAffineOpen_preimage y) m
    rw [LinearMap.liftBaseChange_tmul, residueField_smul_fibre, Scheme.Modules.map_smul, h1,
      LinearEquiv.rTensor_tmul, ← mul_one (residueFieldEquivPreimage y c), ← smul_eq_mul,
      ← TensorProduct.smul_tmul', LinearEquiv.map_smul, h2, residueFieldEquivPreimage_apply]

/-- On an affine open `U ∋ y`, the base change `κ(y) ⊗_{Γ(X, U)} Γ(M, U)` maps bijectively onto
the sections of `ι^* M` by `c ⊗ m ↦ c • ι^* m`; this is `Scheme.Hom.pullbackSectionsEquiv`,
transported along `Γ(Spec κ(y), ι⁻¹ U) = Γ(Spec κ(y), ⊤) ≅ κ(y)`. -/
private lemma bijective_liftBaseChange_pullbackSectionsLE [M.IsQuasicoherent]
    (hU : IsAffineOpen U)
    (f : Γ(M, U) →ₗ[Γ(X, U)] Γ((pullback (X.fromSpecResidueField y)).obj M, ⊤))
    (hf : ∀ m, f m = Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField y) M U ⊤
      (top_le_preimage (y : X) y.2) m) :
    Function.Bijective (f.liftBaseChange (X.residueField y)) := by
  -- Restriction from `⊤` to `ι⁻¹ U = ⊤` is bijective.
  have : IsIso (homOfLE le_top : X.fromSpecResidueField y ⁻¹ᵁ U ⟶ ⊤) :=
    homOfLE_isIso_of_eq _ (fromSpecResidueField_preimage_eq_top (y : X) y.2)
  have hρ : Function.Bijective (((pullback (X.fromSpecResidueField y)).obj M).presheaf.map
      (homOfLE le_top : X.fromSpecResidueField y ⁻¹ᵁ U ⟶ ⊤).op) :=
    ConcreteCategory.bijective_of_isIso _
  refine (hρ.of_comp_iff' _).1 ?_
  rw [show _ ∘ _ = _ from funext (map_liftBaseChange_eq M y hU f hf)]
  exact (preimageSectionsEquiv M y hU).bijective.comp
    ((residueFieldEquivPreimage y).rTensor Γ(M, U)).bijective

/-- The fibre map is bijective, by the base change computations on an affine open `U ∋ y`. -/
private lemma bijective_fibreMap_of_isAffineOpen [M.IsQuasicoherent] (hU : IsAffineOpen U) :
    Function.Bijective (fibreMap (y : X) M) := by
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk y) (X.residueField y) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk y)
      Γ((pullback (X.fromSpecResidueField y)).obj M, ⊤) :=
    IsScalarTower.to₁₂₄ _ _ (X.residueField y) _
  -- The composite `Γ(M, U) → M_y → Γ(Spec κ(y), ι^* M)` is pullback of sections, which is a
  -- base change to `κ(y)`; since `M_y` is the base change to `𝒪_{X,y}`, so is the fibre map.
  let f := (fibreStalkMap (y : X) M).restrictScalars Γ(X, U) ∘ₗ M.germₗ y
  have hc : IsBaseChange (X.residueField y) f := by
    refine IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange _)
      (bijective_liftBaseChange_pullbackSectionsLE M y hU f fun m ↦ by
        rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, germₗ_apply]
        exact fibreStalkMap_germ _ M y.2 m)) fun m ↦ ?_
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]
  exact (IsBaseChange.of_comp (M.isBaseChange_germₗ y hU) hc).liftBaseChange_bijective

end AffineOpen

/-- **The fibre of a quasi-coherent module at a point.** For a quasi-coherent `𝒪_X`-module `M`
and a point `x` of `X`, the global sections of the pullback of `M` along
`ι : Spec κ(x) ⟶ X` are the fibre `κ(x) ⊗_{𝒪_{X,x}} M_x`, as `κ(x)`-vector spaces. The value
`c ⊗ m_x` of the germ of a section `m` near `x` is `c` times the pullback of `m`
(`residueFieldPullbackSectionsEquiv_tmul_germ`). -/
def residueFieldPullbackSectionsEquiv [M.IsQuasicoherent] :
    X.residueField x ⊗[X.presheaf.stalk x] M.presheaf.stalk x ≃ₗ[X.residueField x]
      Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) :=
  LinearEquiv.ofBijective (fibreMap x M) (by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact bijective_fibreMap_of_isAffineOpen M ⟨x, hxU⟩ hU)

/-- The identification of the fibre `κ(x) ⊗_{𝒪_{X,x}} M_x` with the sections of the pullback of
`M` to `Spec κ(x)` sends `c ⊗ m_x`, for a section `m` of `M` over an open `V ∋ x`, to `c` times
the pullback of `m`. -/
@[simp]
theorem residueFieldPullbackSectionsEquiv_tmul_germ [M.IsQuasicoherent] {V : X.Opens}
    (hx : x ∈ V) (c : X.residueField x) (m : Γ(M, V)) :
    residueFieldPullbackSectionsEquiv x M (c ⊗ₜ M.presheaf.germ V x hx m) =
      c • Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤
        (fromSpecResidueField_preimage_eq_top x hx).ge m := by
  rw [residueFieldPullbackSectionsEquiv, LinearEquiv.ofBijective_apply, fibreMap,
    LinearMap.liftBaseChange_tmul, fibreStalkMap_germ]

end AlgebraicGeometry.Scheme.Modules
