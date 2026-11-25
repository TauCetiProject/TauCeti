/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Algebra.Category.FGModuleCat.Zero
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts
public import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.Continuous.Intertwining
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Continuous finite-dimensional representations

Let `G` be a topological monoid, for instance a compact Lie group, and `k` a topological field,
for instance `ℂ`. A finite-dimensional representation `V` of `G` over `k` is *continuous* when all
of its matrix coefficients `g ↦ f (ρ g v)`, for `v ∈ V` and `f ∈ V*`, are continuous
(`FDRep.isContinuous`). Over a complete nontrivially normed field this is continuity of
`G → (V →L[k] V)` for the canonical topology of `V`
(`ContRepresentation.isContinuous_ofShrink_iff_continuous`), so these are the genuine continuous
representations, continuous in the operator norm and not only strongly continuous. Phrasing the
condition through matrix coefficients needs no topology on the carriers of `FDRep k G`.

The continuous representations are closed under isomorphisms, direct sums and tensor products
and contain the trivial representation, so they form a full monoidal additive subcategory
`TauCeti.ContFDRep k G` of `FDRep k G`. Its split Grothendieck ring, the representation ring of
continuous representations, is built in
`TauCeti.RepresentationTheory.RepresentationRing.Continuous`.

## Main definitions

* `FDRep.isContinuous k G`: the property of a finite-dimensional representation that its matrix
  coefficients are continuous.
* `TauCeti.ContFDRep k G`: the full monoidal subcategory of continuous finite-dimensional
  representations.
* `TauCeti.ContFDRep.ofContRepresentation`: a representation on a finite-dimensional normed space,
  in any universe, continuous for the operator norm, as an object of `ContFDRep k G`.
* `TauCeti.ContFDRep.ofContRepresentationIso`: an equivariant linear equivalence of carriers as an
  isomorphism of the corresponding objects of `ContFDRep k G`.
* `TauCeti.ContFDRep.ofContRepresentationEquiv`: the representation underlying
  `TauCeti.ContFDRep.ofContRepresentation π hπ` is equivalent to `π`.
* `TauCeti.ContFDRep.homOfContRepresentationLinearEquiv`: the morphisms between the objects of two
  continuous representations are their continuous intertwiners.

## Main statements

* `FDRep.isContinuous_biprod`, `FDRep.isContinuous_tensor` and `FDRep.isContinuous_tensorUnit`:
  continuous representations are closed under direct sums and tensor products, and the trivial
  representation is continuous. The zero representation is continuous as well, so
  `TauCeti.ContFDRep k G` has a zero object.
* `FDRep.isContinuous_ofShrink_iff`: continuity of a representation given on any carrier.
* `ContRepresentation.isContinuous_ofShrink_iff_continuous`: over a complete nontrivially normed
  field, a continuous representation on a finite-dimensional normed space has continuous matrix
  coefficients exactly when `G → (V →L[k] V)` is continuous.
* `TauCeti.ContFDRep.isZero_ofContRepresentation`: a representation on a zero space is a zero
  object of `ContFDRep k G`.
* `TauCeti.ContFDRep.finrank_hom_ofContRepresentation`: the morphisms between the objects of two
  continuous representations have the same dimension as their continuous intertwiners.
* `TauCeti.ContFDRep.exists_iso_ofContRepresentation`: every object of `ContFDRep 𝕜 G` comes from
  a continuous representation on a coordinate space `Fin n → 𝕜`.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ZeroObject

universe u v w w'

namespace FDRep

section Property

variable (k : Type u) (G : Type v) [Field k] [TopologicalSpace k] [Monoid G] [TopologicalSpace G]

/-- A finite-dimensional representation `V` of a topological monoid `G` over a topological field
`k` is **continuous** when every matrix coefficient `g ↦ f (ρ g v)`, for `v ∈ V` and a linear form
`f` on `V`, is continuous. -/
def isContinuous : ObjectProperty (FDRep k G) :=
  fun V => ∀ (f : Module.Dual k V) (v : V), Continuous fun g => f (V.ρ g v)

variable {k G}

/-- Unfolds `FDRep.isContinuous`: all matrix coefficients are continuous. -/
theorem isContinuous_iff {V : FDRep k G} :
    isContinuous k G V ↔ ∀ (f : Module.Dual k V) (v : V), Continuous fun g => f (V.ρ g v) :=
  Iff.rfl

/-- On a finite-dimensional representation with its module topology, continuity of all
matrix coefficients is equivalent to joint continuity of the action. -/
theorem isContinuous_iff_continuous_action [IsTopologicalRing k] (X : FDRep k G)
    [TopologicalSpace X] [IsModuleTopology k X] :
    isContinuous k G X ↔ Continuous fun p : G × X => X.ρ p.1 p.2 := by
  rw [isContinuous_iff]
  let b := Module.finBasis k X
  refine ⟨fun h => ?_, fun h f x => ?_⟩
  · apply (TauCeti.ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix b b X.ρ).2
    exact continuous_matrix fun i j => by
      simpa only [LinearMap.toMatrix_apply, Module.Basis.coord_apply] using h (b.coord i) (b j)
  · exact (IsModuleTopology.continuous_of_linearMap f).comp
      (h.comp (continuous_id.prodMk continuous_const))

/-- The matrix coefficients of the image of a continuous representation under a morphism are
continuous: `f (ρ g (φ x)) = (f ∘ φ) (ρ g x)`. -/
theorem continuous_apply_ρ_hom_apply {X Y : FDRep k G} (hX : isContinuous k G X)
    (φ : X ⟶ Y) (f : Module.Dual k Y) (x : X) :
    Continuous fun g => f (Y.ρ g (φ.hom.hom.hom x)) :=
  (hX (f ∘ₗ φ.hom.hom.hom) x).congr fun g => by
    simpa using congrArg f (LinearMap.congr_fun (hom_hom_hom_comm φ g) x)

instance : (isContinuous k G).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX f y := by
    have h : e.hom.hom.hom.hom (e.inv.hom.hom.hom y) = y := Iso.inv_hom_id_apply e y
    simpa only [h] using continuous_apply_ρ_hom_apply hX e.hom f (e.inv.hom.hom.hom y)

/-- Every representation of a discrete monoid is continuous. -/
theorem isContinuous_of_discreteTopology [DiscreteTopology G] (V : FDRep k G) :
    isContinuous k G V :=
  fun _ _ => continuous_of_discreteTopology

/-- **Direct sums of continuous representations are continuous**: a vector of `X ⊞ Y` is the sum
of its components, so its matrix coefficients are sums of those of `X` and `Y`. -/
theorem isContinuous_biprod [ContinuousAdd k] {X Y : FDRep k G} (hX : isContinuous k G X)
    (hY : isContinuous k G Y) : isContinuous k G (X ⊞ Y) := by
  intro f v
  rw [← LinearMap.id_apply (R := k) v, ← biprod_total_hom_hom_hom X Y]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
  exact (continuous_apply_ρ_hom_apply hX _ f _).add (continuous_apply_ρ_hom_apply hY _ f _)

instance [ContinuousAdd k] : (isContinuous k G).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun _ _ hX hY =>
    isContinuous_biprod hX hY

/-- The zero representation is continuous, so the continuous representations contain a zero
object and `TauCeti.ContFDRep k G` has a zero object. -/
instance : (isContinuous k G).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun f v => by
    have : Subsingleton (0 : FDRep k G).V := FGModuleCat.isZero_iff_subsingleton.mp
      ((Action.forget _ _).map_isZero (isZero_zero (FDRep k G)))
    simp only [Subsingleton.elim v 0, map_zero]
    exact continuous_const⟩

/-- The trivial one-dimensional representation, the tensor unit, is continuous. -/
theorem isContinuous_tensorUnit : isContinuous k G (𝟙_ (FDRep k G)) := fun f v => by
  simp only [tensorUnit_ρ, LinearMap.id_apply]
  exact continuous_const

/-- **Tensor products of continuous representations are continuous.** Expanding `ρ g y` in a
basis `(bᵢ)` of `Y` writes a matrix coefficient of `ρ g x ⊗ ρ g y` as
`∑ᵢ bᵢ* (ρ g y) · f (ρ g x ⊗ bᵢ)`, a sum of products of matrix coefficients of `X` and `Y`. -/
theorem isContinuous_tensor [ContinuousAdd k] [ContinuousMul k] {X Y : FDRep k G}
    (hX : isContinuous k G X) (hY : isContinuous k G Y) : isContinuous k G (X ⊗ Y) := by
  intro f t
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ =>
    simp only [map_add]
    exact h₁.add h₂
  | tmul x y =>
    let b := Module.Free.chooseBasis k Y
    have h (g : G) : f ((X ⊗ Y).ρ g (x ⊗ₜ y)) =
        ∑ i, b.coord i (Y.ρ g y) * (f ∘ₗ (TensorProduct.mk k X Y).flip (b i)) (X.ρ g x) := by
      conv_lhs => rw [tensor_ρ, TensorProduct.map_tmul, ← b.sum_repr (Y.ρ g y)]
      simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul, smul_eq_mul,
        LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        Module.Basis.coord_apply]
    simp only [h]
    exact continuous_finsetSum _ fun i _ => (hY _ y).mul (hX _ x)

instance [ContinuousAdd k] [ContinuousMul k] : (isContinuous k G).IsMonoidal where
  prop_unit := isContinuous_tensorUnit
  prop_tensor _ _ := isContinuous_tensor

end Property

section Shrink

variable {k : Type u} {G : Type v} [Field k] [TopologicalSpace k] [Monoid G] [TopologicalSpace G]
  {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A representation given on a carrier in any universe is continuous, after shrinking the carrier
into `FDRep k G`, exactly when its own matrix coefficients are continuous. -/
theorem isContinuous_ofShrink_iff (ρ : Representation k G V) :
    isContinuous k G (ofShrink ρ) ↔
      ∀ (f : Module.Dual k V) (v : V), Continuous fun g => f (ρ g v) := by
  let e := (ofShrinkEquiv ρ).toLinearEquiv
  have he (g : G) (v : ofShrink ρ) : e ((ofShrink ρ).ρ g v) = ρ g (e v) :=
    Representation.IntertwiningMap.isIntertwining _ _ (ofShrinkEquiv ρ).toIntertwiningMap g v
  refine ⟨fun h f v => ?_, fun h f v => ?_⟩
  · simpa [he] using h (f ∘ₗ e.toLinearMap) (e.symm v)
  · refine (h (f ∘ₗ e.symm.toLinearMap) (e v)).congr fun g => ?_
    simp [← he]

end Shrink

end FDRep

namespace ContRepresentation

variable {𝕜 : Type u} {G : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] {V : Type w} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **Genuine continuity through matrix coefficients.** A continuous representation `π` of `G` on
a finite-dimensional normed space over a complete nontrivially normed field has continuous matrix
coefficients exactly when `G → (V →L[𝕜] V)` is continuous for the operator norm. -/
theorem isContinuous_ofShrink_iff_continuous (π : ContRepresentation 𝕜 G V) :
    FDRep.isContinuous 𝕜 G (FDRep.ofShrink π.toRepresentation) ↔ Continuous π := by
  rw [FDRep.isContinuous_ofShrink_iff, continuous_clm_apply]
  refine ⟨fun h v => ?_, fun h f v => ?_⟩
  · let b := Module.finBasis 𝕜 V
    have hb : (fun g => π g v) = fun g => b.equivFunL.symm fun i => b.coord i (π g v) := by
      ext g
      simp
    rw [hb]
    exact b.equivFunL.symm.continuous.comp (continuous_pi fun i => h (b.coord i) v)
  · exact (LinearMap.continuous_of_finiteDimensional f).comp (h v)

end ContRepresentation

namespace TauCeti

variable (k : Type u) (G : Type v) [Field k] [TopologicalSpace k] [Monoid G] [TopologicalSpace G]

/-- The category of **continuous finite-dimensional representations** of a topological monoid
`G` over a topological field `k`: the full subcategory of `FDRep k G` on the representations with
continuous matrix coefficients. It inherits the additive and the (braided) monoidal structure of
`FDRep k G`. -/
abbrev ContFDRep : Type (max (u + 1) v) :=
  (FDRep.isContinuous k G).FullSubcategory

/-- Forget the action of a continuous finite-dimensional representation to its underlying module. -/
instance : HasForget₂ (ContFDRep k G) (ModuleCat k) where
  forget₂ := (FDRep.isContinuous k G).ι ⋙ Action.forget (FGModuleCat k) G ⋙
    forget₂ (FGModuleCat k) (ModuleCat k)
  forget_comp := rfl

instance : (forget₂ (ContFDRep k G) (ModuleCat k)).Additive where

variable {k G} in
/-- Forgetting an intertwiner gives its underlying module morphism. -/
@[simp]
theorem ContFDRep.forget₂_map {X Y : ContFDRep k G} (f : X ⟶ Y) :
    (forget₂ (ContFDRep k G) (ModuleCat k)).map f = f.hom.hom.hom := (rfl)

instance [ContinuousAdd k] : HasBinaryBiproducts (ContFDRep k G) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The inclusion of continuous finite representations preserves binary biproducts. -/
instance ContFDRep.preservesBinaryBiproducts_ι :
    PreservesBinaryBiproducts ((FDRep.isContinuous k G).ι) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

variable {G}

/-- A continuous representation `π` of `G` on a finite-dimensional normed space `V` over a complete
nontrivially normed field, in any universe, as an object of `ContFDRep 𝕜 G`. Its underlying object
is `FDRep.ofShrink π.toRepresentation`, whose representation is equivalent to `π`
(`FDRep.ofShrinkEquiv`). -/
noncomputable def ContFDRep.ofContRepresentation {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] {V : Type w} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ContFDRep 𝕜 G :=
  ⟨FDRep.ofShrink π.toRepresentation, π.isContinuous_ofShrink_iff_continuous.2 hπ⟩

/-- The underlying object of `TauCeti.ContFDRep.ofContRepresentation π hπ`. -/
@[simp]
theorem ContFDRep.ofContRepresentation_obj {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] {V : Type w} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    (ContFDRep.ofContRepresentation π hπ).obj = FDRep.ofShrink π.toRepresentation :=
  (rfl)

section Iso

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {V : Type w} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {V' : Type w'} [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [FiniteDimensional 𝕜 V']

/-- **Equivalent representations give isomorphic objects.** An equivariant linear equivalence
`e : V ≃ₗ[𝕜] V'` between the carriers of two continuous representations, in any universes, is an
isomorphism between the corresponding objects of `ContFDRep 𝕜 G`. No continuity of `e` is
assumed: it is automatic between finite-dimensional spaces. -/
noncomputable def ContFDRep.ofContRepresentationIso {π : ContRepresentation 𝕜 G V}
    {π' : ContRepresentation 𝕜 G V'} (e : V ≃ₗ[𝕜] V') (he : ∀ g v, e (π g v) = π' g (e v))
    (hπ : Continuous π) (hπ' : Continuous π') :
    ContFDRep.ofContRepresentation π hπ ≅ ContFDRep.ofContRepresentation π' hπ' :=
  let E := ((FDRep.ofShrinkEquiv π.toRepresentation).trans
    (Representation.Equiv.mk (σ := π'.toRepresentation) e fun g ↦ LinearMap.ext (he g))).trans
      (FDRep.ofShrinkEquiv π'.toRepresentation).symm
  ObjectProperty.isoMk _ <| E.toLinearEquiv.toFDRepIso fun g x ↦
    Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g x

/-- A continuous representation on a zero space is a zero object of `ContFDRep 𝕜 G`. -/
theorem ContFDRep.isZero_ofContRepresentation [Subsingleton V] (π : ContRepresentation 𝕜 G V)
    (hπ : Continuous π) : IsZero (ContFDRep.ofContRepresentation π hπ) := by
  refine IsZero.of_full_of_faithful_of_isZero (FDRep.isContinuous 𝕜 G).ι _ ?_
  rw [ObjectProperty.ι_obj, ContFDRep.ofContRepresentation_obj, IsZero.iff_id_eq_zero]
  have : Subsingleton (FDRep.ofShrink π.toRepresentation) :=
    (FDRep.ofShrinkEquiv π.toRepresentation).toLinearEquiv.toEquiv.subsingleton
  ext x
  rw [Subsingleton.elim x 0]
  simp

end Iso

variable {k : Type u} [Field k] [TopologicalSpace k] in
/-- The morphisms of `ContFDRep k G` form a finite-dimensional space. -/
instance (X Y : ContFDRep k G) : FiniteDimensional k (X ⟶ Y) :=
  (InducedCategory.homLinearEquiv (R := k)).symm.finiteDimensional

namespace ContFDRep

open ContRepresentation

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {V : Type w} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type w'} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}

/-- The representation underlying `ofContRepresentation π hπ` is equivalent to `π`, by
`FDRep.ofShrinkEquiv`. -/
noncomputable def ofContRepresentationEquiv (hπ : Continuous π) :
    Representation.Equiv (ofContRepresentation π hπ).obj.ρ π.toRepresentation :=
  FDRep.ofShrinkEquiv π.toRepresentation

/-- **Morphisms between continuous representations are their continuous intertwiners.** The
morphisms between the objects of `ContFDRep 𝕜 G` given by two continuous representations on
finite-dimensional normed spaces are the continuous intertwining maps between them. -/
noncomputable def homOfContRepresentationLinearEquiv (hπ : Continuous π) (hρ : Continuous ρ) :
    (ofContRepresentation π hπ ⟶ ofContRepresentation ρ hρ) ≃ₗ[𝕜] (π →ⁱL ρ) :=
  InducedCategory.homLinearEquiv ≪≫ₗ (FDRep.forget₂HomLinearEquiv _ _).symm ≪≫ₗ
    Rep.homLinearEquiv _ _ ≪≫ₗ
    (ofContRepresentationEquiv hπ).intertwiningMapCongr (ofContRepresentationEquiv hρ) ≪≫ₗ
    ContRepresentation.intertwiningMapEquiv.symm

/-- The continuous intertwiner of a morphism acts by the morphism on the underlying carriers. -/
@[simp]
theorem homOfContRepresentationLinearEquiv_apply_apply (hπ : Continuous π) (hρ : Continuous ρ)
    (f : ofContRepresentation π hπ ⟶ ofContRepresentation ρ hρ) (v : V) :
    homOfContRepresentationLinearEquiv hπ hρ f v =
      ofContRepresentationEquiv hρ (f.hom.hom.hom.hom ((ofContRepresentationEquiv hπ).symm v)) := by
  rw [homOfContRepresentationLinearEquiv, LinearEquiv.trans_apply,
    intertwiningMapEquiv_symm_apply_apply]
  exact Representation.Equiv.intertwiningMapCongr_apply (ofContRepresentationEquiv hπ)
    (ofContRepresentationEquiv hρ) _ v

/-- The morphism of a continuous intertwiner acts by the intertwiner on the underlying
carriers. -/
@[simp]
theorem homOfContRepresentationLinearEquiv_symm_apply_hom (hπ : Continuous π)
    (hρ : Continuous ρ) (f : π →ⁱL ρ) (v : (ofContRepresentation π hπ).obj) :
    ((homOfContRepresentationLinearEquiv hπ hρ).symm f).hom.hom.hom.hom v =
      (ofContRepresentationEquiv hρ).symm (f (ofContRepresentationEquiv hπ v)) := by
  rw [homOfContRepresentationLinearEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    intertwiningMapEquiv_apply]
  exact Representation.Equiv.intertwiningMapCongr_symm_apply (ofContRepresentationEquiv hπ)
    (ofContRepresentationEquiv hρ) f.toIntertwiningMap v

/-- The morphisms between the objects of `ContFDRep 𝕜 G` given by two continuous representations
on finite-dimensional normed spaces form a space of the same dimension as the continuous
intertwiners between them. -/
theorem finrank_hom_ofContRepresentation (hπ : Continuous π) (hρ : Continuous ρ) :
    Module.finrank 𝕜 (ofContRepresentation π hπ ⟶ ofContRepresentation ρ hρ) =
      Module.finrank 𝕜 (π →ⁱL ρ) :=
  (homOfContRepresentationLinearEquiv hπ hρ).finrank_eq

/-- **Every continuous finite-dimensional representation comes from a continuous representation
on a normed space.** Transporting along a basis, an object `X` of `ContFDRep 𝕜 G` is isomorphic to
the object of a continuous representation on the coordinate space `Fin (finrank 𝕜 X) → 𝕜`. -/
theorem exists_iso_ofContRepresentation (X : ContFDRep 𝕜 G) :
    ∃ (σ : ContRepresentation 𝕜 G (Fin (Module.finrank 𝕜 X.obj) → 𝕜)) (hσ : Continuous σ),
      Nonempty (X ≅ ofContRepresentation σ hσ) := by
  let b := Module.finBasis 𝕜 X.obj
  let σ : ContRepresentation 𝕜 G (Fin (Module.finrank 𝕜 X.obj) → 𝕜) :=
    .ofMonoidHom ((Module.End.toContinuousLinearMap _).toMonoidHom.comp
      (b.equivFun.conjRingEquiv.toMonoidHom.comp X.obj.ρ))
  -- `σ g` is `X.obj.ρ g` conjugated by `b.equivFun`, by construction.
  have hσ_apply (g : G) (v) : σ g v = b.equivFun (X.obj.ρ g (b.equivFun.symm v)) := rfl
  have hσ : Continuous σ := continuous_clm_apply.2 fun v ↦ continuous_pi fun i ↦
    (X.property (b.coord i) (b.equivFun.symm v)).congr fun g ↦ by
      simp [hσ_apply, Module.Basis.equivFun_apply]
  have hb (g : G) (x : X.obj) : σ g (b.equivFun x) = b.equivFun (X.obj.ρ g x) := by
    rw [hσ_apply, LinearEquiv.symm_apply_apply]
  let E := (Representation.Equiv.mk (ρ := X.obj.ρ) (σ := σ.toRepresentation) b.equivFun
    fun g ↦ LinearMap.ext fun x ↦ (hb g x).symm).trans
      (FDRep.ofShrinkEquiv σ.toRepresentation).symm
  exact ⟨σ, hσ, ⟨ObjectProperty.isoMk _ <| E.toLinearEquiv.toFDRepIso fun g x ↦
    Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g x⟩⟩

end ContFDRep

end TauCeti
