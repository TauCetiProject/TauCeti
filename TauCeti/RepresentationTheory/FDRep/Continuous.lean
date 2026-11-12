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
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.RepresentationTheory.FDRep.Basic

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

## Main statements

* `FDRep.isContinuous_biprod`, `FDRep.isContinuous_tensor` and `FDRep.isContinuous_tensorUnit`:
  continuous representations are closed under direct sums and tensor products, and the trivial
  representation is continuous.
* `FDRep.isContinuous_ofShrink_iff`: continuity of a representation given on any carrier.
* `ContRepresentation.isContinuous_ofShrink_iff_continuous`: over a complete nontrivially normed
  field, a continuous representation on a finite-dimensional normed space has continuous matrix
  coefficients exactly when `G → (V →L[k] V)` is continuous.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

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

instance [ContinuousAdd k] : HasBinaryBiproducts (ContFDRep k G) :=
  HasBinaryBiproducts.of_hasBinaryProducts

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

end TauCeti
