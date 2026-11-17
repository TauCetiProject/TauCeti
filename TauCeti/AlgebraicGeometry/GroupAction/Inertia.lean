/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Quotient.Affine
public import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Decomposition and inertia groups of a group acting on a scheme

Let a group `G` act on a scheme `Y` by automorphisms, `σ : G →* Aut Y`. For a point `y` of `Y`,
the *decomposition group* `D_y = decomposition σ y` is the stabilizer of `y`, and the
*inertia group* `I_y = inertia σ y` is the subgroup of `D_y` acting trivially on the residue
field `κ(y)`. These are the groups attached to a point of a Galois cover, such as the
normalization of a normal scheme in a finite Galois extension of its function field.

The inertia group is defined as the stabilizer of the canonical morphism `Spec κ(y) ⟶ Y` under
post-composition. Since a morphism from the spectrum of a field is a point together with an
embedding of its residue field, this is the subgroup of elements fixing `y` whose residue field
map at `y` is the identity (`mem_inertia_iff_residueFieldMap`). More generally, for every field
`K`, the elements fixing a `K`-valued point lying over `y` are exactly those of `I_y`
(`comp_eq_self_iff_mem_inertia`): the stabilizer of a geometric point over `y` is the inertia
group, not the decomposition group.

The decomposition group acts on `κ(y)` through `residueAction σ y`, whose kernel is the inertia
group (`ker_residueAction`); if `G` acts by automorphisms over a scheme `X`, this action fixes
the residue field of the image of `y` in `X`. Moving the point by `g` conjugates both groups by
`g` (`decomposition_apply_eq_map_conj`, `inertia_apply_eq_map_conj`).

Let `π : Y ⟶ X` be a `G`-invariant morphism and `x = π y`. Then `D_y` acts on `κ(y)` by
automorphisms over `κ(x)` (`residueAlgAction σ π hπ y`). Suppose moreover that any two points of
`Y` with values in a field and the same image in `X` differ by an element of `G`, as for the
projection to the quotient by a finite group with an invariant affine open cover
(`TauCeti.InvariantQuotient.asIso_hom_projection`,
`TauCeti.InvariantQuotient.exists_comp_eq_of_comp_projection_eq`). Then every automorphism of
`κ(y)` over `κ(x)` comes from `D_y` (`residueAlgAction_surjective`): if `τ` is one, the point
`Spec κ(y) ⟶ Y` and its twist by `τ` have the same image in `X`, so they differ by an element of
`G`, which then fixes `y` and acts on `κ(y)` by `τ`. Hence `D_y / I_y ≅ Aut(κ(y)/κ(x))`
(`decompositionQuotientInertiaEquiv`).

For a group acting on a commutative ring `A`, and so on `Spec A` by
`TauCeti.AffineInvariantQuotient.specAction`, the decomposition and inertia groups of a prime
`𝔭` are Mathlib's `MulAction.stabilizer G 𝔭` and `Ideal.inertia G 𝔭`
(`decomposition_specAction`, `inertia_specAction`). This makes Mathlib's ramification theory of
Galois extensions of rings available for affine Galois covers.

## Main definitions

* `pointMulAction σ`, `homMulAction σ X`: the actions of `G` on the points of `Y` and, by
  post-composition, on morphisms `X ⟶ Y`.
* `decomposition σ y`: the decomposition group of `y`.
* `inertia σ y`: the inertia group of `y`.
* `residueAction σ y`: the action of the decomposition group on `κ(y)`.
* `residueAlgAction σ π hπ y`: for `G` acting over `X`, the action of the decomposition group on
  `κ(y)` by automorphisms over `κ(π y)`.
* `decompositionQuotientInertiaEquiv σ π hπ horb y`: if points of `Y` with values in a field and
  the same image in `X` differ by an element of `G`, the isomorphism
  `D_y / I_y ≃* Aut(κ(y)/κ(π y))`.

## Main results

* `comp_eq_self_iff_mem_inertia`: the stabilizer of a point with values in a field is the inertia
  group of its image point.
* `ker_residueAction`, `ker_residueAlgAction`: the inertia group is the kernel of the action on
  the residue field.
* `residueAlgAction_surjective`: if points of `Y` with values in a field and the same image in `X`
  differ by an element of `G`, the decomposition group surjects onto the automorphisms of `κ(y)`
  over `κ(π y)`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé V, §2,
  Proposition 2.2.
* N. Bourbaki, *Commutative Algebra*, Chapter V, §2, no. 2.
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Pointwise

namespace TauCeti.SchemeInertia

universe u v

variable {Y : Scheme.{u}} {G : Type v} [Group G] (σ : G →* Aut Y)

/-- The action of `G` on the points of `Y` through `σ`. It is not an instance, since `σ` is
data; install it locally to select this action. -/
@[instance_reducible]
def pointMulAction : MulAction G Y where
  smul g y := (σ g).asIso.hom y
  -- The `•` in these goals is the `smul` field under construction, which `simp` cannot unfold
  -- (plain `by simp` makes no progress); `show` restates each law through that field's
  -- definition, where `simp` closes it since `σ` is a monoid homomorphism.
  one_smul y := show (σ 1).asIso.hom y = y by simp
  mul_smul a b y := show (σ (a * b)).asIso.hom y = (σ a).asIso.hom ((σ b).asIso.hom y) by simp

/-- An element acts on the points of `Y` through its automorphism. -/
theorem pointMulAction_smul (g : G) (y : Y) :
    letI := pointMulAction σ
    g • y = (σ g).asIso.hom y :=
  (rfl)

/-- The action of `G` on morphisms `X ⟶ Y` by post-composition with `σ`, induced from Mathlib's
action of `End Y`. It is not an instance, since `σ` is data; install it locally to select this
action. -/
@[instance_reducible]
def homMulAction (X : Scheme.{u}) : MulAction G (X ⟶ Y) :=
  MulAction.compHom _ (Aut.toEnd.comp σ)

/-- An element acts on morphisms into `Y` by post-composition with its automorphism. -/
theorem homMulAction_smul {X : Scheme.{u}} (g : G) (f : X ⟶ Y) :
    letI := homMulAction σ X
    g • f = f ≫ (σ g).asIso.hom :=
  (rfl)

/-- The **decomposition group** of a point `y` of a scheme with an action of `G`: the stabilizer
of `y`. -/
def decomposition (y : Y) : Subgroup G :=
  letI := pointMulAction σ
  MulAction.stabilizer G y

/-- An element lies in the decomposition group of `y` exactly when it fixes `y`. -/
@[simp]
theorem mem_decomposition {y : Y} {g : G} :
    g ∈ decomposition σ y ↔ (σ g).asIso.hom y = y :=
  Iff.rfl

/-- The **inertia group** of a point `y` of a scheme with an action of `G`: the subgroup of
elements fixing the canonical morphism `Spec κ(y) ⟶ Y`, that is, fixing `y` and acting trivially
on its residue field (`mem_inertia_iff_residueFieldMap`). -/
noncomputable def inertia (y : Y) : Subgroup G :=
  letI := homMulAction σ (Spec (Y.residueField y))
  MulAction.stabilizer G (Y.fromSpecResidueField y)

/-- An element lies in the inertia group of `y` exactly when it fixes the canonical morphism
`Spec κ(y) ⟶ Y`. -/
@[simp]
theorem mem_inertia {y : Y} {g : G} :
    g ∈ inertia σ y ↔ Y.fromSpecResidueField y ≫ (σ g).asIso.hom = Y.fromSpecResidueField y :=
  Iff.rfl

/-- The inertia group of a point is contained in its decomposition group. -/
theorem inertia_le_decomposition (y : Y) : inertia σ y ≤ decomposition σ y := fun g hg ↦ by
  obtain ⟨s⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
  have := Scheme.Hom.comp_apply (Y.fromSpecResidueField y) (σ g).asIso.hom s
  rw [(mem_inertia σ).mp hg, Scheme.fromSpecResidueField_apply] at this
  exact this.symm

/-- An element lies in the inertia group of `y` exactly when it fixes `y` and its residue field
map at `y` is the identity of `κ(y)`. -/
theorem mem_inertia_iff_residueFieldMap {y : Y} {g : G} :
    g ∈ inertia σ y ↔ ∃ h : (σ g).asIso.hom y = y,
      (σ g).asIso.hom.residueFieldMap y = (Y.residueFieldCongr h).hom := by
  refine ⟨fun hg ↦ ⟨(mem_decomposition σ).mp (inertia_le_decomposition σ y hg), ?_⟩,
    fun ⟨h, hres⟩ ↦ ?_⟩
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecResidueField ((σ g).asIso.hom y)),
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Scheme.residueFieldCongr_fromSpecResidueField]
    exact hg
  · rw [mem_inertia, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, hres,
      Scheme.residueFieldCongr_fromSpecResidueField]

/-- **Stabilizers of geometric points.** For a field `K`, an element of `G` fixes a `K`-valued
point `f` of `Y` exactly when it lies in the inertia group of the image point of `f`. -/
theorem comp_eq_self_iff_mem_inertia {K : Type u} [Field K] (f : Spec (.of K) ⟶ Y) {g : G} :
    f ≫ (σ g).asIso.hom = f ↔ g ∈ inertia σ (f (closedPoint K)) := by
  set y := f (closedPoint K)
  set φ := Y.descResidueField (Scheme.stalkClosedPointTo f)
  have hf : Spec.map φ ≫ Y.fromSpecResidueField y = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y f
  refine ⟨fun h ↦ ?_, fun hg ↦ by rw [← hf, Category.assoc, (mem_inertia σ).mp hg]⟩
  have hy : (σ g).asIso.hom y = y := by
    have := Scheme.Hom.comp_apply f (σ g).asIso.hom (closedPoint K)
    rw [h] at this
    exact this.symm
  refine (mem_inertia_iff_residueFieldMap σ).mpr ⟨hy, ?_⟩
  have : Mono φ := ConcreteCategory.mono_of_injective φ φ.hom.injective
  rw [← cancel_mono φ]
  apply Spec.map_injective
  rw [← cancel_mono (Y.fromSpecResidueField ((σ g).asIso.hom y)), Spec.map_comp,
    Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    Scheme.residueFieldCongr_fromSpecResidueField, reassoc_of% hf, hf, h]

/-- Moving a point by `g` conjugates its decomposition group by `g`. -/
theorem decomposition_apply_eq_map_conj (g : G) (y : Y) :
    decomposition σ ((σ g).asIso.hom y) = (decomposition σ y).map (MulAut.conj g).toMonoidHom :=
  letI := pointMulAction σ
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g y

/-- Moving a point by `g` conjugates its inertia group by `g`. -/
theorem inertia_apply_eq_map_conj (g : G) (y : Y) :
    inertia σ ((σ g).asIso.hom y) = (inertia σ y).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_inertia, mem_inertia, map_mul, map_mul,
    map_inv, Aut.mul_asIso, Aut.mul_asIso, Aut.inv_asIso, Iso.trans_hom, Iso.trans_hom,
    Iso.symm_hom, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (σ g).asIso.hom y, Category.assoc,
    cancel_epi]

/-- The residue field automorphism underlying `residueAction`. -/
private noncomputable def residueIso {y : Y} {g : G} (hg : g ∈ decomposition σ y) :
    Y.residueField y ≅ Y.residueField y :=
  (Y.residueFieldCongr ((mem_decomposition σ).mp (inv_mem hg))).symm ≪≫
    asIso ((σ g⁻¹).asIso.hom.residueFieldMap y)

private lemma SpecMap_residueIso_fromSpecResidueField {y : Y} {g : G}
    (hg : g ∈ decomposition σ y) :
    Spec.map (residueIso σ hg).hom ≫ Y.fromSpecResidueField y =
      Y.fromSpecResidueField y ≫ (σ g⁻¹).asIso.hom := by
  rw [residueIso, Iso.trans_hom, asIso_hom, Spec.map_comp, Category.assoc, Iso.symm_hom,
    Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- The **action of the decomposition group on the residue field** `κ(y)`: an element `g` acts by
the residue field map of `g⁻¹` at `y`, which makes this a left action. It is characterized by
`SpecMap_residueAction_fromSpecResidueField`, and its kernel is the inertia group
(`ker_residueAction`). -/
noncomputable def residueAction (y : Y) : decomposition σ y →* Aut (Y.residueField y) where
  toFun g := .of (residueIso σ g.2)
  map_one' := by
    ext1
    refine Iso.ext (Scheme.eq_of_SpecMap_comp_fromSpecResidueField ?_)
    simp [SpecMap_residueIso_fromSpecResidueField]
  map_mul' g h := by
    ext1
    refine Iso.ext (Scheme.eq_of_SpecMap_comp_fromSpecResidueField ?_)
    simp [SpecMap_residueIso_fromSpecResidueField]

/-- The automorphism of `κ(y)` induced by `g` is the residue field map of `g⁻¹`: on spectra, it
is compatible with the canonical morphism `Spec κ(y) ⟶ Y` and the action of `g⁻¹` on `Y`. -/
@[reassoc (attr := simp)]
theorem SpecMap_residueAction_fromSpecResidueField (y : Y) (g : decomposition σ y) :
    Spec.map (residueAction σ y g).asIso.hom ≫ Y.fromSpecResidueField y =
      Y.fromSpecResidueField y ≫ (σ (g : G)⁻¹).asIso.hom :=
  SpecMap_residueIso_fromSpecResidueField σ g.2

/-- The inertia group is the kernel of the action of the decomposition group on the residue
field. -/
theorem ker_residueAction (y : Y) :
    (residueAction σ y).ker = (inertia σ y).subgroupOf (decomposition σ y) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← inv_mem_iff, mem_inertia,
    ← SpecMap_residueAction_fromSpecResidueField, Aut.ext_iff, Aut.one_asIso]
  refine ⟨fun h ↦ by rw [h, Iso.refl_hom, Spec.map_id, Category.id_comp], fun h ↦ ?_⟩
  exact Iso.ext (Scheme.eq_of_SpecMap_comp_fromSpecResidueField
    (by rw [h, Iso.refl_hom, Spec.map_id, Category.id_comp]))

/-- The inertia group is normal in the decomposition group. -/
instance normal_inertia_subgroupOf (y : Y) :
    ((inertia σ y).subgroupOf (decomposition σ y)).Normal :=
  ker_residueAction σ y ▸ (residueAction σ y).normal_ker

/-- If an element `g` of the decomposition group of `y` acts by an automorphism over a scheme `X`,
for instance if `G` acts by automorphisms over `X`, then its action on `κ(y)` fixes the residue
field of the image of `y` in `X`. -/
@[reassoc]
theorem residueFieldMap_comp_residueAction {X : Scheme.{u}} (π : Y ⟶ X) (y : Y)
    (g : decomposition σ y) (hπ : (σ (g : G)).asIso.hom ≫ π = π) :
    π.residueFieldMap y ≫ (residueAction σ y g).asIso.hom = π.residueFieldMap y := by
  have hπ' : (σ (g : G)⁻¹).asIso.hom ≫ π = π := by
    rw [map_inv, Aut.inv_asIso, Iso.symm_hom, Iso.inv_comp_eq, hπ]
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecResidueField (π y)), Spec.map_comp, Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    SpecMap_residueAction_fromSpecResidueField_assoc, hπ']

section Quotient

variable {X : Scheme.{u}} (π : Y ⟶ X)

/-- **Automorphisms of the residue extension come from the decomposition group.** Suppose that
any two points of `Y` with values in a field and the same image in `X` differ by the action of an
element of `G`, as for the projection to the quotient by a finite group
(`TauCeti.InvariantQuotient.exists_comp_eq_of_comp_projection_eq`). Then every automorphism of
`κ(y)` fixing the residue field of the image of `y` in `X` is induced by an element of the
decomposition group of `y`. -/
theorem exists_residueAction_eq
    (horb : ∀ {K : Type u} [Field K] {x₁ x₂ : Spec (.of K) ⟶ Y}, x₁ ≫ π = x₂ ≫ π →
      ∃ g : G, x₁ ≫ (σ g).asIso.hom = x₂)
    (y : Y) (τ : Aut (Y.residueField y))
    (hτ : π.residueFieldMap y ≫ τ.asIso.hom = π.residueFieldMap y) :
    ∃ g : decomposition σ y, residueAction σ y g = τ := by
  -- The point `Spec κ(y) ⟶ Y` and its twist by `τ` have the same image in `X`.
  have h : Y.fromSpecResidueField y ≫ π =
      (Spec.map τ.asIso.hom ≫ Y.fromSpecResidueField y) ≫ π := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, hτ]
  obtain ⟨g, hg⟩ := horb (K := Y.residueField y) h
  -- `horb` is stated for spectra `Spec (.of K)`; restate `hg` for `Spec κ(y)`, which is the same
  -- scheme since `CommRingCat.of κ(y)` is `κ(y)` by structure eta.
  replace hg : Y.fromSpecResidueField y ≫ (σ g).asIso.hom =
      Spec.map τ.asIso.hom ≫ Y.fromSpecResidueField y := hg
  have hgy : g⁻¹ ∈ decomposition σ y := by
    obtain ⟨s⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
    have := congr(($hg) s)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
      Scheme.fromSpecResidueField_apply] at this
    exact inv_mem ((mem_decomposition σ).mpr this)
  refine ⟨⟨g⁻¹, hgy⟩, Aut.ext (Iso.ext (Scheme.eq_of_SpecMap_comp_fromSpecResidueField ?_))⟩
  rw [SpecMap_residueAction_fromSpecResidueField, inv_inv, hg]

/-- The **action of the decomposition group on the residue extension**. If `G` acts by
automorphisms over `X`, the decomposition group of `y` acts on `κ(y)` by automorphisms over the
residue field of the image of `y` in `X`, of which `κ(y)` is an algebra through the residue field
map of `π`. This is `residueAction σ y` (`residueAlgAction_apply`). -/
noncomputable def residueAlgAction (hπ : ∀ g : G, (σ g).asIso.hom ≫ π = π) (y : Y) :
    letI := (π.residueFieldMap y).hom.toAlgebra
    decomposition σ y →* (Y.residueField y ≃ₐ[X.residueField (π y)] Y.residueField y) :=
  letI := (π.residueFieldMap y).hom.toAlgebra
  { toFun g := AlgEquiv.ofRingEquiv (f := (residueAction σ y g).asIso.commRingCatIsoToRingEquiv)
      fun a ↦ congr(($(residueFieldMap_comp_residueAction σ π y g (hπ g))).hom a)
    map_one' := by ext; simp [Iso.commRingCatIsoToRingEquiv]
    map_mul' g h := by ext; simp [Iso.commRingCatIsoToRingEquiv] }

/-- An element of the decomposition group acts on the residue extension through
`residueAction`. -/
@[simp]
theorem residueAlgAction_apply (hπ : ∀ g : G, (σ g).asIso.hom ≫ π = π) (y : Y)
    (g : decomposition σ y) (a : Y.residueField y) :
    residueAlgAction σ π hπ y g a = (residueAction σ y g).asIso.hom a :=
  (rfl)

/-- The inertia group is the kernel of the action of the decomposition group on the residue
extension. -/
theorem ker_residueAlgAction (hπ : ∀ g : G, (σ g).asIso.hom ≫ π = π) (y : Y) :
    (residueAlgAction σ π hπ y).ker = (inertia σ y).subgroupOf (decomposition σ y) := by
  rw [← ker_residueAction]
  ext g
  simp [MonoidHom.mem_ker, AlgEquiv.ext_iff, Aut.ext_iff, Iso.ext_iff, CommRingCat.hom_ext_iff,
    RingHom.ext_iff]

/-- **The decomposition group surjects onto the automorphisms of the residue extension**, when
`G` acts by automorphisms over `X` and any two points of `Y` with values in a field and the same
image in `X` differ by the action of an element of `G`. -/
theorem residueAlgAction_surjective (hπ : ∀ g : G, (σ g).asIso.hom ≫ π = π)
    (horb : ∀ {K : Type u} [Field K] {x₁ x₂ : Spec (.of K) ⟶ Y}, x₁ ≫ π = x₂ ≫ π →
      ∃ g : G, x₁ ≫ (σ g).asIso.hom = x₂)
    (y : Y) : Function.Surjective (residueAlgAction σ π hπ y) := by
  let := (π.residueFieldMap y).hom.toAlgebra
  intro τ
  obtain ⟨g, hg⟩ := exists_residueAction_eq σ π horb y (.of τ.toRingEquiv.toCommRingCatIso)
    (by ext a; exact τ.commutes a)
  exact ⟨g, AlgEquiv.ext fun a ↦ by rw [residueAlgAction_apply, hg]; rfl⟩

/-- **The decomposition group modulo the inertia group is the automorphism group of the residue
extension**, when `G` acts by automorphisms over `X` and any two points of `Y` with values in a
field and the same image in `X` differ by the action of an element of `G`. -/
noncomputable def decompositionQuotientInertiaEquiv (hπ : ∀ g : G, (σ g).asIso.hom ≫ π = π)
    (horb : ∀ {K : Type u} [Field K] {x₁ x₂ : Spec (.of K) ⟶ Y}, x₁ ≫ π = x₂ ≫ π →
      ∃ g : G, x₁ ≫ (σ g).asIso.hom = x₂)
    (y : Y) :
    letI := (π.residueFieldMap y).hom.toAlgebra
    decomposition σ y ⧸ (inertia σ y).subgroupOf (decomposition σ y) ≃*
      (Y.residueField y ≃ₐ[X.residueField (π y)] Y.residueField y) :=
  QuotientGroup.liftEquiv _ (residueAlgAction_surjective σ π hπ horb y)
    (ker_residueAlgAction σ π hπ y).symm

/-- The isomorphism `decompositionQuotientInertiaEquiv` sends the class of `g` to the action of
`g` on the residue extension. -/
@[simp]
theorem decompositionQuotientInertiaEquiv_mk (hπ : ∀ g : G, (σ g).asIso.hom ≫ π = π)
    (horb : ∀ {K : Type u} [Field K] {x₁ x₂ : Spec (.of K) ⟶ Y}, x₁ ≫ π = x₂ ≫ π →
      ∃ g : G, x₁ ≫ (σ g).asIso.hom = x₂)
    (y : Y) (g : decomposition σ y) :
    decompositionQuotientInertiaEquiv σ π hπ horb y g = residueAlgAction σ π hπ y g := by
  rw [decompositionQuotientInertiaEquiv, QuotientGroup.liftEquiv_mk]

end Quotient

section Affine

open AffineInvariantQuotient

variable (A : Type u) (G) [CommRing A] [MulSemiringAction G A]

/-- For a group acting on a commutative ring `A`, the decomposition group of a prime ideal `𝔭`
of `A`, as a point of `Spec A`, is the stabilizer of `𝔭`. -/
@[simp]
theorem decomposition_specAction (P : Spec (.of A)) :
    decomposition (specAction A G) P = MulAction.stabilizer G P.asIdeal := by
  ext g
  -- `P` as a prime ideal, on which `G` acts
  let Q : PrimeSpectrum A := P
  have e : (specAction A G g).asIso.hom P = g • Q := specAction_apply A G g Q
  refine (mem_decomposition _).trans ⟨fun h ↦ ?_, fun h ↦ e.trans (PrimeSpectrum.ext ?_)⟩
  · exact (PrimeSpectrum.asIdeal_smul g Q).symm.trans
      (congrArg PrimeSpectrum.asIdeal (e.symm.trans h))
  · exact (PrimeSpectrum.asIdeal_smul g Q).trans h

/-- For a group acting on a commutative ring `A`, the inertia group of a prime ideal `𝔭` of `A`,
as a point of `Spec A`, is Mathlib's inertia group `Ideal.inertia G 𝔭` of elements acting
trivially on `A ⧸ 𝔭`. -/
@[simp]
theorem inertia_specAction (P : Spec (.of A)) :
    inertia (specAction A G) P = P.asIdeal.inertia G := by
  ext g
  refine (mem_inertia _).trans ?_
  simp only [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    specAction_asIso_hom, specComap_def, ← Spec.map_comp, Spec.map_inj, ← Category.assoc,
    cancel_mono, CommRingCat.hom_ext_iff, RingHom.ext_iff, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom, RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
  -- both sides say that `g⁻¹` acts trivially on `A` modulo `𝔭`
  rw [← inv_mem_iff, Ideal.mem_inertia]
  have : P.asIdeal.IsPrime := PrimeSpectrum.isPrime P
  refine forall_congr' fun a ↦ ?_
  rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]

end Affine

end TauCeti.SchemeInertia
