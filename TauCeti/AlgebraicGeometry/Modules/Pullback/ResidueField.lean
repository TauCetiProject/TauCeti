/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
import TauCeti.RingTheory.TensorProduct.IsBaseChange

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
`𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)` (`Scheme.Modules.isBaseChange_germₗ`).

## Main declarations

* `AlgebraicGeometry.Scheme.fromSpecResidueField_appLE`: on an open containing `x`, the morphism
  `Spec κ(x) ⟶ X` sends a function to its value at `x`;
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

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (x : X)

/-- The inverse image of an open containing `x` under `Spec κ(x) ⟶ X` is everything. -/
lemma fromSpecResidueField_preimage_eq_top {V : X.Opens} (hx : x ∈ V) :
    X.fromSpecResidueField x ⁻¹ᵁ V = ⊤ :=
  Scheme.preimage_eq_top_of_closedPoint_mem _ (by
    convert hx using 1
    exact Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint (X.residueField x)))

/-- On an open `V` containing `x`, the morphism `Spec κ(x) ⟶ X` sends a function to its value at
`x`, as a global function on `Spec κ(x)`. -/
lemma fromSpecResidueField_appLE {V : X.Opens} (hx : x ∈ V)
    (h : (⊤ : (Spec (X.residueField x)).Opens) ≤ X.fromSpecResidueField x ⁻¹ᵁ V) :
    (X.fromSpecResidueField x).appLE V ⊤ h =
      X.evaluation V x hx ≫ (Scheme.ΓSpecIso (X.residueField x)).inv := by
  have hV : X.fromSpecResidueField x (IsLocalRing.closedPoint (X.residueField x)) ∈ V := by
    convert hx using 1
    exact Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint (X.residueField x))
  have : IsLocalHom (X.residue x).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  -- `Spec κ(x) ⟶ X` is `Spec κ(x) ⟶ Spec 𝒪_{X,x} ⟶ X`, whose action on sections near the
  -- closed point is computed by Mathlib's `Scheme.germ_stalkClosedPointTo`.
  rw [Iso.eq_comp_inv, ← X.germ_residue x hx,
    ← Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (X.residue x) V hV]
  refine Eq.trans ?_ (Scheme.germ_stalkClosedPointTo
    (Spec.map (X.residue x) ≫ X.fromSpecStalk x) V hV).symm
  rw [Scheme.Hom.appLE, Category.assoc, Iso.trans_hom, Functor.mapIso_hom]
  congr 2

end AlgebraicGeometry.Scheme

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
  rw [smul_Spec_def, show (⊤ : (Spec (X.residueField x)).Opens).leTop = 𝟙 _ from
    Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- Pulling back to `Spec κ(x)` commutes with restriction between opens containing `x`. -/
private lemma pullbackSectionsLE_res {V W : X.Opens} (i : V ⟶ W) (hx : x ∈ V) (m : Γ(M, W)) :
    Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤ (top_le_preimage x hx)
        (M.presheaf.map i.op m) =
      Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M W ⊤
        (top_le_preimage x (i.le hx)) m := by
  rw [Scheme.Hom.pullbackSectionsLE_apply, Scheme.Hom.pullbackSectionsLE_apply,
    ← Scheme.Hom.pullbackSections_restrict, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

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

/-- On an affine open `U ∋ x`, the base change `κ(x) ⊗_{Γ(X, U)} Γ(M, U)` maps bijectively onto
the sections of `ι^* M` by `c ⊗ m ↦ c • ι^* m`; this is `Scheme.Hom.pullbackSectionsEquiv`,
transported along `Γ(Spec κ(x), ι⁻¹ U) = Γ(Spec κ(x), ⊤) ≅ κ(x)`. -/
private lemma bijective_liftBaseChange_pullbackSectionsLE [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (hx : x ∈ U) :
    letI : Algebra Γ(X, U) (X.residueField x) := (X.evaluation U x hx).hom.toAlgebra
    letI : Module Γ(X, U) Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) :=
      Module.compHom _ (algebraMap Γ(X, U) (X.residueField x))
    haveI : IsScalarTower Γ(X, U) (X.residueField x)
        Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) := IsScalarTower.of_compHom _ _ _
    ∀ (f : Γ(M, U) →ₗ[Γ(X, U)] Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤)),
      (∀ m, f m = Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M U ⊤
        (top_le_preimage x hx) m) →
      Function.Bijective (f.liftBaseChange (X.residueField x)) := by
  -- Write `ι⁻¹ U = ⊤` and `pse` for `Scheme.Hom.pullbackSectionsEquiv`. We show that restriction
  -- `ρ : Γ(ι^* M, ⊤) ⟶ Γ(ι^* M, ι⁻¹ U)` after the map of the statement is `pse` after the
  -- isomorphism `κ(x) ≅ Γ(Spec κ(x), ι⁻¹ U)` on the left tensor factor; `ρ` is bijective.
  intro f hf
  -- The instances of the statement, which `intro` has unfolded.
  let : Algebra Γ(X, U) (X.residueField x) := (X.evaluation U x hx).hom.toAlgebra
  let : Module Γ(X, U) Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) :=
    Module.compHom _ (algebraMap Γ(X, U) (X.residueField x))
  have : IsScalarTower Γ(X, U) (X.residueField x)
      Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) := IsScalarTower.of_compHom _ _ _
  let g := X.fromSpecResidueField x
  let N := (pullback g).obj M
  have hpre : g ⁻¹ᵁ U = ⊤ := fromSpecResidueField_preimage_eq_top x hx
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := by
    rw [hpre]
    exact isAffineOpen_top _
  let : Algebra Γ(X, U) Γ(Spec (X.residueField x), g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  let pse : Γ(Spec (X.residueField x), g ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Spec (X.residueField x),
      g ⁻¹ᵁ U)] Γ(N, g ⁻¹ᵁ U) := g.pullbackSectionsEquiv M hU hV
  -- Restriction from `⊤` to `ι⁻¹ U = ⊤` is bijective, on sections of `N` and of `𝒪`.
  let i : g ⁻¹ᵁ U ⟶ ⊤ := homOfLE le_top
  have : IsIso i := homOfLE_isIso_of_eq _ hpre
  have hρ : Function.Bijective (N.presheaf.map i.op) := ConcreteCategory.bijective_of_isIso _
  have hres (t : Γ(Spec (X.residueField x), g ⁻¹ᵁ U)) :
      (Spec (X.residueField x)).presheaf.map i.op
        ((Spec (X.residueField x)).presheaf.map (homOfLE (top_le_preimage x hx)).op t) = t := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      show i ≫ homOfLE (top_le_preimage x hx) = 𝟙 _ from Subsingleton.elim _ _, op_id,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  -- `κ(x) ≅ Γ(Spec κ(x), ι⁻¹ U)` as `Γ(X, U)`-algebras.
  let φ : X.residueField x →ₗ[Γ(X, U)] Γ(Spec (X.residueField x), g ⁻¹ᵁ U) :=
    { toFun c := (Spec (X.residueField x)).presheaf.map i.op
        ((Scheme.ΓSpecIso (X.residueField x)).inv c)
      map_add' := by simp
      map_smul' r c := by
        have hr : ((Scheme.ΓSpecIso (X.residueField x)).inv ≫
            (Spec (X.residueField x)).presheaf.map i.op) (X.evaluation U x hx r) = g.app U r := by
          rw [← CommRingCat.comp_apply, ← Category.assoc,
            ← fromSpecResidueField_appLE x hx (top_le_preimage x hx), CommRingCat.comp_apply,
            Scheme.Hom.appLE, CommRingCat.comp_apply, hres]
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.id_apply, ← CommRingCat.comp_apply,
          map_mul, CommRingCat.comp_apply]
        exact congrArg (· * _) hr }
  have hφ : Function.Bijective φ := ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (X.residueField x)).inv ≫ (Spec (X.residueField x)).presheaf.map i.op)
  let φe := LinearEquiv.ofBijective φ hφ
  have key : ∀ t, N.presheaf.map i.op (f.liftBaseChange (X.residueField x) t) =
      pse (φe.rTensor Γ(M, U) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m =>
      have h1 : N.presheaf.map i.op (f m) = g.pullbackSections M U m := by
        rw [hf, Scheme.Hom.pullbackSectionsLE_apply, ← ConcreteCategory.comp_apply,
          ← Functor.map_comp, ← op_comp,
          show i ≫ homOfLE (top_le_preimage x hx) = 𝟙 _ from Subsingleton.elim _ _, op_id,
          CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
      have h2 : pse (1 ⊗ₜ m) = g.pullbackSections M U m :=
        g.pullbackSectionsEquiv_one_tmul M hU hV m
      rw [LinearMap.liftBaseChange_tmul, residueField_smul_fibre, Scheme.Modules.map_smul, h1,
        LinearEquiv.rTensor_tmul, ← mul_one (φe c), ← smul_eq_mul, ← TensorProduct.smul_tmul',
        pse.map_smul, h2]
      rfl
  have hcomp : N.presheaf.map i.op ∘ f.liftBaseChange (X.residueField x) =
      pse ∘ φe.rTensor Γ(M, U) := funext key
  refine (hρ.of_comp_iff' _).1 ?_
  rw [hcomp]
  exact pse.bijective.comp (φe.rTensor Γ(M, U)).bijective

/-- The fibre map is bijective, by the base change computations on an affine open `U ∋ x`. -/
private lemma bijective_fibreMap_of_isAffineOpen [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (y : U) : Function.Bijective (fibreMap (y : X) M) := by
  let : Algebra Γ(X, U) (X.residueField y) := (X.evaluation U y y.2).hom.toAlgebra
  let : Module Γ(X, U) Γ((pullback (X.fromSpecResidueField y)).obj M, ⊤) :=
    Module.compHom _ (algebraMap Γ(X, U) (X.residueField y))
  have : IsScalarTower Γ(X, U) (X.residueField y)
      Γ((pullback (X.fromSpecResidueField y)).obj M, ⊤) := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk y) (X.residueField y) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk y)
      Γ((pullback (X.fromSpecResidueField y)).obj M, ⊤) :=
    IsScalarTower.to₁₂₄ _ _ (X.residueField y) _
  -- The composite `Γ(M, U) → M_x → Γ(Spec κ(x), ι^* M)` is pullback of sections, which is a
  -- base change to `κ(x)`; since `M_x` is the base change to `𝒪_{X,x}`, so is the fibre map.
  let f := (fibreStalkMap (y : X) M).restrictScalars Γ(X, U) ∘ₗ M.germₗ y
  have hc : IsBaseChange (X.residueField y) f := by
    refine IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange _)
      (bijective_liftBaseChange_pullbackSectionsLE (y : X) M hU y.2 f fun m ↦ by
        rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, germₗ_apply]
        exact fibreStalkMap_germ _ M y.2 m)) fun m ↦ ?_
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]
  exact (IsBaseChange.of_comp (M.isBaseChange_germₗ y hU) hc).liftBaseChange_bijective

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
    exact bijective_fibreMap_of_isAffineOpen M hU ⟨x, hxU⟩)

/-- The identification of the fibre `κ(x) ⊗_{𝒪_{X,x}} M_x` with the sections of the pullback of
`M` to `Spec κ(x)` sends `c ⊗ m_x`, for a section `m` of `M` over an open `V ∋ x`, to `c` times
the pullback of `m`. -/
theorem residueFieldPullbackSectionsEquiv_tmul_germ [M.IsQuasicoherent] {V : X.Opens}
    (hx : x ∈ V) (c : X.residueField x) (m : Γ(M, V)) :
    residueFieldPullbackSectionsEquiv x M (c ⊗ₜ M.presheaf.germ V x hx m) =
      c • Scheme.Hom.pullbackSectionsLE (X.fromSpecResidueField x) M V ⊤
        (fromSpecResidueField_preimage_eq_top x hx).ge m := by
  rw [residueFieldPullbackSectionsEquiv, LinearEquiv.ofBijective_apply, fibreMap,
    LinearMap.liftBaseChange_tmul, fibreStalkMap_germ]

end AlgebraicGeometry.Scheme.Modules
