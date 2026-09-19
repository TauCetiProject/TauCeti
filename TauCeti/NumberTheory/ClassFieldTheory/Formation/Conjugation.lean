/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality

/-!
# Conjugation of a finite normal layer

An element `g` of the ambient group carries a finite normal layer `V ◁ U` of a formation to the
layer `gVg⁻¹ ◁ gUg⁻¹`. In field notation `g` is an automorphism of the big extension, and the
conjugate layer is the layer `gK/gF` obtained by transporting `K/F` along it. This file builds
that layer and the maps it induces, on the levels of the formation and on the cohomology of the
layer.

The conjugate subgroups are obtained by pulling `U` and `V` back along `x ↦ g⁻¹xg`, which is
continuous, so the conjugate layer is again a layer of open subgroups
(`NormalLayer.conjugate`). Conjugation is an action: it is trivial at `1` and composes
(`NormalLayer.conjugate_one`, `NormalLayer.conjugate_conjugate`). Unlike a restriction or a
refinement, conjugation moves *both* subgroups of the layer, so it changes neither the Galois
group nor the coefficient module up to isomorphism: `NormalLayer.conjugateGalEquiv` identifies
`U/V` with `gUg⁻¹/gVg⁻¹`, and the degree of the layer is unchanged
(`NormalLayer.degree_conjugate`).

On the coefficient side the map is the action of `g` itself. If `x` is fixed by `U` then `g · x`
is fixed by `gUg⁻¹`, so acting by `g` is an isomorphism `A^U ≃ A^{gUg⁻¹}` of levels
(`Formation.levelConjEquiv`); applied to the top and ground subgroups of a layer this gives
`NormalLayer.conjugateCoefficientEquiv` and `NormalLayer.conjugateGroundLevelEquiv`. The two
isomorphisms intertwine: `g · (u · x) = (gug⁻¹) · (g · x)`. That single identity
(`NormalLayer.conjugateCoefficientEquiv_rep_apply`) is what feeds both

* `NormalLayer.conjugateCohomologyIso`, conjugation on ordinary group cohomology
  `H^n(U/V, A^V) ≅ H^n(gUg⁻¹/gVg⁻¹, A^{gVg⁻¹})`, obtained from Mathlib's change-of-group
  isomorphism; and
* `NormalLayer.conjugateTateIso`, conjugation on the Tate groups in every integer degree,
  obtained from `TauCeti.TateCohomology.mapIso`, the functoriality of Tate cohomology in a
  compatible pair.

Three compatibilities fix the direction of these maps and let conjugation be read on the norm
quotient `A^U / N_{U/V}(A^V)`, the group the Artin map of a class formation lands in: in degree
zero the cohomological map is the action of `g` on the ground level
(`NormalLayer.groundLevelEquiv_conjugateCohomologyIso_zero_apply`), and conjugation carries the
norm of a layer to the norm of the conjugate layer
(`NormalLayer.conjugateGroundLevelEquiv_norm`), hence its norm subgroup onto the norm subgroup
there (`NormalLayer.map_normSubgroup_conjugateGroundLevelEquiv`). Finally,
`NormalLayer.tateHZeroEquivNormQuotient_conjugateTateIso_apply` identifies degree-zero Tate
conjugation with the resulting map on norm quotients.

The conjugation map on abelianized Galois groups needs no declaration of its own: it is
Mathlib's `MulEquiv.abelianizationCongr` applied to `NormalLayer.conjugateGalEquiv`.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.conjugate`: the conjugate layer `gVg⁻¹ ◁ gUg⁻¹`.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateGalEquiv`: the induced isomorphism
  `U/V ≃* gUg⁻¹/gVg⁻¹` of Galois groups.
* `TauCeti.ClassFieldTheory.Formation.levelConjEquiv`: acting by `g` is an isomorphism
  `A^U ≃ A^{gUg⁻¹}` of levels.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateCoefficientEquiv` and
  `TauCeti.ClassFieldTheory.NormalLayer.conjugateGroundLevelEquiv`: that isomorphism at the top
  and at the ground subgroup of a layer.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateCohomologyIso` and
  `TauCeti.ClassFieldTheory.NormalLayer.conjugateTateIso`: conjugation on the ordinary and Tate
  cohomology of a layer.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateNormQuotientEquiv`: conjugation on the norm
  quotient of a layer.

## Main statements

* `TauCeti.ClassFieldTheory.NormalLayer.conjugate_one` and
  `TauCeti.ClassFieldTheory.NormalLayer.conjugate_conjugate`: conjugation of layers is an action
  of the ambient group.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateCohomologyIso_one`,
  `TauCeti.ClassFieldTheory.NormalLayer.conjugateCohomologyIso_trans_conjugateCohomologyIso`,
  `TauCeti.ClassFieldTheory.NormalLayer.conjugateTateIso_one` and
  `TauCeti.ClassFieldTheory.NormalLayer.conjugateTateIso_trans_conjugateTateIso`: the induced maps
  on ordinary and Tate cohomology satisfy the same action laws, up to transport along
  `conjugate_one` and `conjugate_conjugate`; the Galois-group and norm-quotient equivalences satisfy
  matching transported laws, while the maps on ground subgroups, coefficient modules and ground
  levels satisfy them on underlying elements.
* `TauCeti.ClassFieldTheory.NormalLayer.degree_conjugate`: a conjugate layer has the same degree.
* `TauCeti.ClassFieldTheory.NormalLayer.card_gal_conjugate`: its simp-normal form, on the orders of
  the Galois groups.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateCoefficientEquiv_rep_apply`: the isomorphisms of
  Galois groups and of coefficient modules intertwine, restated as
  `TauCeti.ClassFieldTheory.NormalLayer.isIntertwiningMap_conjugateCoefficientEquiv`.
* `TauCeti.ClassFieldTheory.NormalLayer.groundLevelEquiv_conjugateCohomologyIso_zero_apply`: in
  degree zero, conjugation of cohomology is the action of `g` on the ground level.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateGroundLevelEquiv_norm` and
  `TauCeti.ClassFieldTheory.NormalLayer.map_normSubgroup_conjugateGroundLevelEquiv`: conjugation
  commutes with the norm of a layer and carries its norm subgroup onto that of the conjugate
  layer.
* `TauCeti.ClassFieldTheory.NormalLayer.conjugateNormQuotientEquiv_normQuotientMk`: conjugation on
  norm quotients sends the class of a representative to the class of its conjugate.
* `TauCeti.ClassFieldTheory.NormalLayer.tateHZeroEquivNormQuotient_conjugateTateIso_apply`:
  conjugation commutes with the canonical identification of degree-zero Tate cohomology with the
  norm quotient.

## Implementation notes

`NormalLayer.conjugate` takes the *comap* of `x ↦ g⁻¹xg` rather than the image of `x ↦ gxg⁻¹`,
so that membership in the conjugate subgroups is definitionally the membership condition
`g⁻¹xg ∈ U` and needs no image lemma to use.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Chapter I, §5.
-/

public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-! ### Conjugation of levels -/

namespace Formation

variable (F : Formation G)

/-- **Conjugation carries a level into the level of the conjugate subgroup.** If `U'` is the
conjugate `gUg⁻¹` then acting by `g` takes an element fixed by `U` to an element fixed by `U'`. -/
theorem ρ_mem_level_conj (g : G) {U U' : OpenSubgroup G}
    (h : ∀ x : G, g * x * g⁻¹ ∈ U' → x ∈ U) {a : F.toRep.V} (ha : a ∈ F.level U) :
    F.toRep.ρ g a ∈ F.level U' := by
  refine F.mem_level.2 fun w hw ↦ ?_
  have hw' : g⁻¹ * w * g ∈ U := by
    apply h _
    simpa [mul_assoc] using hw
  calc
    F.toRep.ρ w (F.toRep.ρ g a) = F.toRep.ρ (w * g) a := by
      rw [← Module.End.mul_apply, ← map_mul]
    _ = F.toRep.ρ (g * (g⁻¹ * w * g)) a := by
      congr 1
      group
    _ = F.toRep.ρ g (F.toRep.ρ (g⁻¹ * w * g) a) := by
      rw [← Module.End.mul_apply, ← map_mul]
    _ = F.toRep.ρ g a := congrArg _ (F.mem_level.1 ha _ hw')

/-- **Conjugation of levels:** acting by `g` is an isomorphism `A^U ≃ A^{gUg⁻¹}`. The hypothesis
says that `U'` is the conjugate `gUg⁻¹`. -/
def levelConjEquiv (g : G) {U U' : OpenSubgroup G}
    (h : ∀ x : G, g * x * g⁻¹ ∈ U' ↔ x ∈ U) : F.level U ≃ₗ[ℤ] F.level U' where
  toFun a := ⟨F.toRep.ρ g a, F.ρ_mem_level_conj g (fun x ↦ (h x).1) a.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)
  invFun b := ⟨F.toRep.ρ g⁻¹ b, F.ρ_mem_level_conj g⁻¹
    (fun x hx ↦ by
      have hx' : g⁻¹ * x * g ∈ U := by simpa using hx
      have := (h (g⁻¹ * x * g)).2 hx'
      simpa [mul_assoc] using this) b.2⟩
  left_inv a := Subtype.ext (F.toRep.ρ.inv_self_apply g a)
  right_inv b := Subtype.ext (F.toRep.ρ.self_inv_apply g b)

@[simp]
theorem levelConjEquiv_apply_coe (g : G) {U U' : OpenSubgroup G}
    (h : ∀ x : G, g * x * g⁻¹ ∈ U' ↔ x ∈ U) (a : F.level U) :
    ((F.levelConjEquiv g h a : F.level U') : F.toRep.V) = F.toRep.ρ g a :=
  (rfl)

@[simp]
theorem levelConjEquiv_symm_apply_coe (g : G) {U U' : OpenSubgroup G}
    (h : ∀ x : G, g * x * g⁻¹ ∈ U' ↔ x ∈ U) (b : F.level U') :
    (((F.levelConjEquiv g h).symm b : F.level U) : F.toRep.V) = F.toRep.ρ g⁻¹ b :=
  (rfl)

end Formation

namespace NormalLayer

/-! ### The conjugate layer -/

/-- The **conjugate layer** `gVg⁻¹ ◁ gUg⁻¹` of a finite normal layer `V ◁ U`. In field notation it
is the layer `gK/gF` obtained by transporting `K/F` along the automorphism `g` of the big
extension. -/
def conjugate (L : NormalLayer G) (g : G) : NormalLayer G where
  ground := L.ground.comap ((MulAut.conj g).symm : G ≃* G)
    ((continuous_mul_const g).comp (continuous_const_mul g⁻¹))
  top := L.top.comap ((MulAut.conj g).symm : G ≃* G)
    ((continuous_mul_const g).comp (continuous_const_mul g⁻¹))
  top_le_ground _ hx := OpenSubgroup.mem_comap.2 (L.top_le_ground (OpenSubgroup.mem_comap.1 hx))
  normal := by
    constructor
    rintro ⟨n, hn⟩ hmem ⟨u, hu⟩
    refine Subgroup.mem_subgroupOf.2 ?_
    have hnv : g⁻¹ * n * g ∈ L.top := Subgroup.mem_subgroupOf.1 hmem
    have huu : g⁻¹ * u * g ∈ L.ground := hu
    have hconj := L.conj_mem_top huu hnv
    have hgoal : g⁻¹ * (u * n * u⁻¹) * g ∈ L.top := by
      convert hconj using 1
      group
    exact hgoal

variable (L : NormalLayer G) (F : Formation G) (g h : G)

/-- Membership in the ground subgroup of the conjugate layer. -/
-- Both steps are definitional in Mathlib: `Subgroup.mem_comap` and `MulAut.conj_symm_apply`.
@[simp]
theorem mem_ground_conjugate {x : G} : x ∈ (L.conjugate g).ground ↔ g⁻¹ * x * g ∈ L.ground :=
  (Iff.rfl)

/-- Membership in the top subgroup of the conjugate layer. -/
@[simp]
theorem mem_top_conjugate {x : G} : x ∈ (L.conjugate g).top ↔ g⁻¹ * x * g ∈ L.top :=
  (Iff.rfl)

/-- **Conjugating by `1` does nothing.** -/
@[simp]
theorem conjugate_one : L.conjugate 1 = L := by
  ext x <;> simp

/-- **Conjugation of layers composes**, so it is an action of the ambient group on the layers of
a formation. -/
@[simp]
theorem conjugate_conjugate : (L.conjugate h).conjugate g = L.conjugate (g * h) := by
  ext x <;> simp [mul_assoc]

/-- The conjugate `gug⁻¹` of an element of the ground subgroup lies in the ground subgroup of the
conjugate layer, and only then. -/
theorem conj_mem_ground_conjugate {x : G} :
    g * x * g⁻¹ ∈ (L.conjugate g).ground ↔ x ∈ L.ground := by
  rw [mem_ground_conjugate]
  simp [mul_assoc]

/-- The conjugate `gvg⁻¹` of an element of the top subgroup lies in the top subgroup of the
conjugate layer, and only then. -/
theorem conj_mem_top_conjugate {x : G} :
    g * x * g⁻¹ ∈ (L.conjugate g).top ↔ x ∈ L.top := by
  rw [mem_top_conjugate]
  simp [mul_assoc]

/-! ### The Galois group of a conjugate layer -/

/-- Conjugation by `g` as an isomorphism `U ≃* gUg⁻¹` of the ground subgroups of a layer and its
conjugate. -/
def conjugateGroundEquiv : L.ground ≃* (L.conjugate g).ground :=
  Subgroup.congrOfMapEq (MulAut.conj g) <| by
    rw [Subgroup.map_equiv_eq_comap_symm]
    rfl

@[simp]
theorem conjugateGroundEquiv_apply_coe (u : L.ground) :
    ((L.conjugateGroundEquiv g u : (L.conjugate g).ground) : G) = g * u * g⁻¹ :=
  (Subgroup.coe_congrOfMapEq_apply _ _ u).trans (MulAut.conj_apply g u)

@[simp]
theorem conjugateGroundEquiv_symm_apply_coe (v : (L.conjugate g).ground) :
    (((L.conjugateGroundEquiv g).symm v : L.ground) : G) = g⁻¹ * v * g :=
  (Subgroup.coe_congrOfMapEq_symm_apply _ _ v).trans (MulAut.conj_symm_apply g v)

/-- Conjugation carries the top subgroup of a layer, read inside its ground subgroup, onto the
corresponding subgroup of the conjugate layer. This is what lets it descend to Galois groups. -/
theorem map_relativeTop_conjugateGroundEquiv :
    L.relativeTop.map (L.conjugateGroundEquiv g) = (L.conjugate g).relativeTop := by
  ext v
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hv := (L.conj_mem_top_conjugate g).2 (Subgroup.mem_subgroupOf.1 hu)
    rw [← conjugateGroundEquiv_apply_coe] at hv
    exact Subgroup.mem_subgroupOf.2 hv
  · intro hv
    refine ⟨(L.conjugateGroundEquiv g).symm v, Subgroup.mem_subgroupOf.2 ?_,
      (L.conjugateGroundEquiv g).apply_symm_apply v⟩
    simpa using (L.mem_top_conjugate g).1 (Subgroup.mem_subgroupOf.1 hv)

/-- **Conjugation by `g` as an isomorphism `U/V ≃* gUg⁻¹/gVg⁻¹` of Galois groups.** -/
def conjugateGalEquiv : L.Gal ≃* (L.conjugate g).Gal :=
  QuotientGroup.congr _ _ (L.conjugateGroundEquiv g) (L.map_relativeTop_conjugateGroundEquiv g)

@[simp]
theorem conjugateGalEquiv_mk (u : L.ground) :
    L.conjugateGalEquiv g (QuotientGroup.mk u) =
      QuotientGroup.mk (L.conjugateGroundEquiv g u) :=
  (rfl)

/-- **A conjugate layer has a Galois group of the same order.** This is the simp-normal form of
`degree_conjugate`: `simp` rewrites `degree` to `Fintype.card` of the Galois group via
`degree_eq_natCard_gal`, and this lemma then identifies the two cardinalities. -/
@[simp]
theorem card_gal_conjugate : Fintype.card (L.conjugate g).Gal = Fintype.card L.Gal :=
  Fintype.card_congr (L.conjugateGalEquiv g).symm.toEquiv

/-- **A conjugate layer has the same degree.** Not `@[simp]`, since its left-hand side is not in
simp-normal form; `simp` proves it through `card_gal_conjugate`. -/
theorem degree_conjugate : (L.conjugate g).degree = L.degree := by
  simp

/-! ### Conjugation of the levels and the coefficient module of a layer -/

/-- **Conjugation on the coefficient module of a layer:** acting by `g` is an isomorphism
`A^V ≃ A^{gVg⁻¹}`. -/
def conjugateCoefficientEquiv : F.level L.top ≃ₗ[ℤ] F.level (L.conjugate g).top :=
  F.levelConjEquiv g fun _ ↦ L.conj_mem_top_conjugate g

@[simp]
theorem conjugateCoefficientEquiv_apply_coe (x : F.level L.top) :
    ((L.conjugateCoefficientEquiv F g x : F.level (L.conjugate g).top) : F.toRep.V) =
      F.toRep.ρ g x :=
  (rfl)

/-- **Conjugation on the ground level of a layer:** acting by `g` is an isomorphism
`A^U ≃ A^{gUg⁻¹}`. This is the map the Artin map of a class formation is conjugated by. -/
def conjugateGroundLevelEquiv : F.level L.ground ≃ₗ[ℤ] F.level (L.conjugate g).ground :=
  F.levelConjEquiv g fun _ ↦ L.conj_mem_ground_conjugate g

@[simp]
theorem conjugateGroundLevelEquiv_apply_coe (x : F.level L.ground) :
    ((L.conjugateGroundLevelEquiv F g x : F.level (L.conjugate g).ground) : F.toRep.V) =
      F.toRep.ρ g x :=
  (rfl)

/-- On a representative of the Galois group, the coefficient isomorphism intertwines the two
actions by the identity `g · (u · x) = (gug⁻¹) · (g · x)`. -/
theorem conjugateCoefficientEquiv_rep_mk_apply (u : L.ground) (x : F.level L.top) :
    L.conjugateCoefficientEquiv F g ((L.rep F).ρ (QuotientGroup.mk u) x) =
      ((L.conjugate g).rep F).ρ (L.conjugateGalEquiv g (QuotientGroup.mk u))
        (L.conjugateCoefficientEquiv F g x) := by
  refine Subtype.ext ?_
  rw [conjugateGalEquiv_mk, conjugateCoefficientEquiv_apply_coe, rep_ρ_mk_apply_coe,
    rep_ρ_mk_apply_coe, conjugateGroundEquiv_apply_coe, conjugateCoefficientEquiv_apply_coe]
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 1
  group

/-- **The isomorphisms of Galois groups and of coefficient modules intertwine:**
`g · (γ · x) = (gγg⁻¹) · (g · x)`. -/
theorem conjugateCoefficientEquiv_rep_apply (γ : L.Gal) (x : F.level L.top) :
    L.conjugateCoefficientEquiv F g ((L.rep F).ρ γ x) =
      ((L.conjugate g).rep F).ρ (L.conjugateGalEquiv g γ) (L.conjugateCoefficientEquiv F g x) := by
  induction γ using QuotientGroup.induction_on with
  | H u => exact L.conjugateCoefficientEquiv_rep_mk_apply F g u x

/-- Conjugation is a **compatible pair** of a group isomorphism and an isomorphism of coefficient
modules, the datum `TauCeti.TateCohomology.mapIso` consumes. -/
theorem isIntertwiningMap_conjugateCoefficientEquiv :
    (L.rep F).ρ.IsIntertwiningMap
      (((L.conjugate g).rep F).ρ.comp
        ((L.conjugateGalEquiv g : L.Gal ≃* (L.conjugate g).Gal) : L.Gal →* (L.conjugate g).Gal))
      ((L.conjugateCoefficientEquiv F g : F.level L.top ≃ₗ[ℤ] F.level (L.conjugate g).top) :
        F.level L.top →ₗ[ℤ] F.level (L.conjugate g).top) :=
  ⟨fun γ x ↦ L.conjugateCoefficientEquiv_rep_apply F g γ x⟩

/-! ### Conjugation of the cohomology of a layer -/

/-- **Conjugation on the ordinary cohomology of a layer**, the isomorphism

`H^n(U/V, A^V) ≅ H^n(gUg⁻¹/gVg⁻¹, A^{gVg⁻¹})`

induced by the isomorphism of Galois groups and the action of `g` on the coefficients. -/
def conjugateCohomologyIso (n : ℕ) : L.H F n ≅ (L.conjugate g).H F n :=
  groupCohomology.mapIso (L.conjugateGalEquiv g) (L.conjugateCoefficientEquiv F g)
    (fun γ ↦ LinearMap.ext fun x ↦ L.conjugateCoefficientEquiv_rep_apply F g γ x) n

/-- **Conjugation on the Tate cohomology of a layer**, in every integer degree. In the degrees
where Mathlib compares Tate cohomology with ordinary cohomology or homology, it is the ordinary
change-of-group map of that theory, by `TauCeti.TateCohomology.map_comp_isoGroupCohomology_hom`
and `TauCeti.TateCohomology.map_comp_isoGroupHomology_hom`. -/
def conjugateTateIso (r : ℤ) : L.TateH F r ≅ (L.conjugate g).TateH F r :=
  TateCohomology.mapIso (L.isIntertwiningMap_conjugateCoefficientEquiv F g) r

/-- **In degree zero, conjugation of cohomology is the action of `g` on the ground level.** Read
through the identification of `H⁰(U/V, A^V)` with `A^U`, conjugating a class is applying `g` to
the corresponding element of the ground level. This is what fixes the direction of
`conjugateCohomologyIso`. -/
theorem groundLevelEquiv_conjugateCohomologyIso_zero_apply (x : L.H F 0) :
    (L.conjugate g).groundLevelEquiv F
        ((groupCohomology.H0Iso ((L.conjugate g).rep F)).hom.hom
          ((L.conjugateCohomologyIso F g 0).hom x)) =
      L.conjugateGroundLevelEquiv F g
        (L.groundLevelEquiv F ((groupCohomology.H0Iso (L.rep F)).hom.hom x)) := by
  refine Subtype.ext ?_
  rw [groundLevelEquiv_apply_coe, conjugateGroundLevelEquiv_apply_coe, groundLevelEquiv_apply_coe,
    conjugateCohomologyIso, groupCohomology.mapIso_hom]
  refine (congrArg Subtype.val (groupCohomology.map_H0Iso_hom_f_apply _ _ x)).trans ?_
  exact L.conjugateCoefficientEquiv_apply_coe F g _

/-! ### Conjugation and the norm of a layer -/

/-- **Conjugation commutes with the norm of a layer:** the isomorphism of Galois groups permutes
the summands of `N_{U/V}`. -/
theorem conjugateGroundLevelEquiv_norm (x : F.level L.top) :
    (L.conjugate g).norm F (L.conjugateCoefficientEquiv F g x) =
      L.conjugateGroundLevelEquiv F g (L.norm F x) := by
  refine Subtype.ext ?_
  rw [norm_apply_coe, conjugateGroundLevelEquiv_apply_coe, norm_apply_coe]
  have hnorm := LinearMap.congr_fun (Representation.IsIntertwiningMap.comp_norm
    (L.isIntertwiningMap_conjugateCoefficientEquiv F g)) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hnorm
  have hnorm' := congrArg (fun y : F.level (L.conjugate g).top ↦ (y : F.toRep.V)) hnorm.symm
  calc
    ∑ γ, ((((L.conjugate g).rep F).ρ γ (L.conjugateCoefficientEquiv F g x) :
        F.level (L.conjugate g).top) : F.toRep.V) =
        (((∑ γ, ((L.conjugate g).rep F).ρ γ)
          (L.conjugateCoefficientEquiv F g x) : F.level (L.conjugate g).top) : F.toRep.V) := by
      simp
    _ = ((L.conjugateCoefficientEquiv F g ((L.rep F).ρ.norm x) :
          F.level (L.conjugate g).top) : F.toRep.V) := by
      simpa only [LinearMap.comp_apply, Representation.norm] using hnorm'
    _ = F.toRep.ρ g ((L.rep F).ρ.norm x) :=
      L.conjugateCoefficientEquiv_apply_coe F g _
    _ = F.toRep.ρ g (∑ γ, ((L.rep F).ρ γ x : F.level L.top)) := by
      congr 1
      simp [Representation.norm]

/-- **Conjugation carries the norm subgroup of a layer onto the norm subgroup of the conjugate
layer**, so it descends to an isomorphism of the norm quotients the Artin map of a class
formation is read on. -/
theorem map_normSubgroup_conjugateGroundLevelEquiv :
    (L.normSubgroup F).map (L.conjugateGroundLevelEquiv F g).toLinearMap =
      (L.conjugate g).normSubgroup F := by
  ext y
  rw [Submodule.mem_map, mem_normSubgroup]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := (L.mem_normSubgroup F).1 hz
    exact ⟨L.conjugateCoefficientEquiv F g x, L.conjugateGroundLevelEquiv_norm F g x⟩
  · rintro ⟨w, rfl⟩
    refine ⟨L.norm F ((L.conjugateCoefficientEquiv F g).symm w),
      (L.mem_normSubgroup F).2 ⟨_, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, ← L.conjugateGroundLevelEquiv_norm F g,
      LinearEquiv.apply_symm_apply]

/-- **Conjugation on the norm quotient:** acting by `g` on the ground level descends through the
norm subgroups of a layer and its conjugate. -/
def conjugateNormQuotientEquiv : L.NormQuotient F ≃+ (L.conjugate g).NormQuotient F :=
  (Submodule.Quotient.equiv _ _ (L.conjugateGroundLevelEquiv F g)
    (L.map_normSubgroup_conjugateGroundLevelEquiv F g)).toAddEquiv

/-- Conjugation on norm quotients sends the class of a ground-level element to the class of its
conjugate. -/
@[simp]
theorem conjugateNormQuotientEquiv_normQuotientMk (x : F.level L.ground) :
    L.conjugateNormQuotientEquiv F g (L.normQuotientMk F x) =
      (L.conjugate g).normQuotientMk F (L.conjugateGroundLevelEquiv F g x) := by
  rw [normQuotientMk_apply, normQuotientMk_apply, conjugateNormQuotientEquiv,
    LinearEquiv.coe_toAddEquiv]
  exact (Submodule.Quotient.equiv_apply (L.normSubgroup F)
    ((L.conjugate g).normSubgroup F) (L.conjugateGroundLevelEquiv F g)
    (L.map_normSubgroup_conjugateGroundLevelEquiv F g) (Submodule.Quotient.mk x)).trans
      (Submodule.mapQ_apply (L.normSubgroup F) ((L.conjugate g).normSubgroup F)
        (L.conjugateGroundLevelEquiv F g).toLinearMap x)

/-- In degree zero, conjugation on Tate cohomology is conjugation on the norm quotient. -/
theorem tateHZeroEquivNormQuotient_conjugateTateIso_apply (x : L.TateH F 0) :
    (L.conjugate g).tateHZeroEquivNormQuotient F ((L.conjugateTateIso F g 0).hom x) =
      L.conjugateNormQuotientEquiv F g (L.tateHZeroEquivNormQuotient F x) := by
  induction x using TateCohomology.H0_induction_on with
  | h y =>
    rw [conjugateTateIso, TateCohomology.mapIso_hom,
      TateCohomology.H0π_comp_map_apply, tateHZeroEquivNormQuotient_H0π,
      tateHZeroEquivNormQuotient_H0π, conjugateNormQuotientEquiv_normQuotientMk]
    congr 1
    apply Subtype.ext
    rw [groundLevelEquiv_apply_coe, conjugateGroundLevelEquiv_apply_coe,
      groundLevelEquiv_apply_coe, TateCohomology.mapInvariants_apply_coe]
    simpa only [LinearEquiv.coe_coe] using
      L.conjugateCoefficientEquiv_apply_coe F g (y : F.level L.top)

/-! ### Conjugation by `1` and by a product

`conjugate_one` and `conjugate_conjugate` make conjugation an action on layers. The maps it
induces satisfy the matching laws. On subgroups and levels these are stated on underlying elements,
where no transport is needed; on cohomology they are stated up to the `eqToIso` along those two
equalities of layers. -/

/-- Conjugating the ground subgroup by `1` is the identity on underlying elements. -/
theorem conjugateGroundEquiv_one_apply_coe (u : L.ground) :
    ((L.conjugateGroundEquiv 1 u : (L.conjugate 1).ground) : G) = u := by
  simp

/-- Conjugating the ground subgroup by `h` and then by `g` is conjugating it by `g * h`. -/
theorem conjugateGroundEquiv_conjugateGroundEquiv_apply_coe (u : L.ground) :
    (((L.conjugate h).conjugateGroundEquiv g (L.conjugateGroundEquiv h u) :
        ((L.conjugate h).conjugate g).ground) : G) =
      (L.conjugateGroundEquiv (g * h) u : (L.conjugate (g * h)).ground) := by
  simp only [conjugateGroundEquiv_apply_coe]
  group

/-- Conjugating the coefficient module of a layer by `1` is the identity on underlying elements. -/
theorem conjugateCoefficientEquiv_one_apply_coe (x : F.level L.top) :
    ((L.conjugateCoefficientEquiv F 1 x : F.level (L.conjugate 1).top) : F.toRep.V) = x := by
  rw [conjugateCoefficientEquiv_apply_coe, map_one, Module.End.one_apply]

/-- Conjugating the coefficient module of a layer by `h` and then by `g` is conjugating it by
`g * h`. -/
theorem conjugateCoefficientEquiv_conjugateCoefficientEquiv_apply_coe (x : F.level L.top) :
    (((L.conjugate h).conjugateCoefficientEquiv F g (L.conjugateCoefficientEquiv F h x) :
        F.level ((L.conjugate h).conjugate g).top) : F.toRep.V) =
      (L.conjugateCoefficientEquiv F (g * h) x : F.level (L.conjugate (g * h)).top) := by
  rw [conjugateCoefficientEquiv_apply_coe, conjugateCoefficientEquiv_apply_coe,
    conjugateCoefficientEquiv_apply_coe, map_mul, Module.End.mul_apply]

/-- Conjugating the ground level of a layer by `1` is the identity on underlying elements. -/
theorem conjugateGroundLevelEquiv_one_apply_coe (x : F.level L.ground) :
    ((L.conjugateGroundLevelEquiv F 1 x : F.level (L.conjugate 1).ground) : F.toRep.V) = x := by
  rw [conjugateGroundLevelEquiv_apply_coe, map_one, Module.End.one_apply]

/-- Conjugating the ground level of a layer by `h` and then by `g` is conjugating it by `g * h`. -/
theorem conjugateGroundLevelEquiv_conjugateGroundLevelEquiv_apply_coe (x : F.level L.ground) :
    (((L.conjugate h).conjugateGroundLevelEquiv F g (L.conjugateGroundLevelEquiv F h x) :
        F.level ((L.conjugate h).conjugate g).ground) : F.toRep.V) =
      (L.conjugateGroundLevelEquiv F (g * h) x : F.level (L.conjugate (g * h)).ground) := by
  rw [conjugateGroundLevelEquiv_apply_coe, conjugateGroundLevelEquiv_apply_coe,
    conjugateGroundLevelEquiv_apply_coe, map_mul, Module.End.mul_apply]

private theorem conjugateGalEquiv_trans_cast_eq {L' : NormalLayer G}
    (hL : L.conjugate g = L') (e : L.Gal ≃* L'.Gal)
    (he : ∀ (u : L.ground) (v : L'.ground), (v : G) = g * u * g⁻¹ →
      e (QuotientGroup.mk u) = QuotientGroup.mk v) :
    (L.conjugateGalEquiv g).trans
        (MulEquiv.cast (M := fun K : NormalLayer G => K.Gal) hL) = e := by
  subst hL
  apply MulEquiv.ext
  intro γ
  induction γ using QuotientGroup.induction_on with
  | H u =>
    rw [MulEquiv.trans_apply, conjugateGalEquiv_mk]
    exact (he u _ (L.conjugateGroundEquiv_apply_coe g u)).symm

/-- **Conjugation by `1` is the identity on the Galois group**, after transporting along
`conjugate_one`. -/
theorem conjugateGalEquiv_one :
    (L.conjugateGalEquiv 1).trans
        (MulEquiv.cast (M := fun K : NormalLayer G => K.Gal) L.conjugate_one) =
      MulEquiv.refl L.Gal := by
  apply L.conjugateGalEquiv_trans_cast_eq 1 L.conjugate_one
  intro u v huv
  exact congrArg QuotientGroup.mk (Subtype.ext (by simpa using huv.symm))

/-- **Conjugation composes on the Galois group**: conjugating by `h` and then by `g` is
conjugating by `g * h`, up to transport along `conjugate_conjugate`. -/
theorem conjugateGalEquiv_trans_conjugateGalEquiv :
    (L.conjugateGalEquiv h).trans ((L.conjugate h).conjugateGalEquiv g) =
      (L.conjugateGalEquiv (g * h)).trans
        (MulEquiv.cast (M := fun K : NormalLayer G => K.Gal)
          (L.conjugate_conjugate g h).symm) := by
  symm
  apply L.conjugateGalEquiv_trans_cast_eq (g * h) (L.conjugate_conjugate g h).symm
  intro u v huv
  rw [MulEquiv.trans_apply, conjugateGalEquiv_mk, conjugateGalEquiv_mk]
  exact congrArg QuotientGroup.mk <| Subtype.ext <|
    (L.conjugateGroundEquiv_conjugateGroundEquiv_apply_coe g h u).trans
      ((L.conjugateGroundEquiv_apply_coe (g * h) u).trans huv.symm)

private theorem conjugateNormQuotientEquiv_trans_cast_eq {L' : NormalLayer G}
    (hL : L.conjugate g = L') (e : L.NormQuotient F ≃+ L'.NormQuotient F)
    (he : ∀ (x : F.level L.ground) (y : F.level L'.ground),
      (y : F.toRep.V) = F.toRep.ρ g x →
      e (L.normQuotientMk F x) = L'.normQuotientMk F y) :
    (L.conjugateNormQuotientEquiv F g).trans
        (AddEquiv.cast (M := fun K : NormalLayer G => K.NormQuotient F) hL) = e := by
  subst hL
  apply AddEquiv.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    rw [← normQuotientMk_apply, AddEquiv.trans_apply,
      conjugateNormQuotientEquiv_normQuotientMk]
    exact (he x _ (L.conjugateGroundLevelEquiv_apply_coe F g x)).symm

/-- **Conjugation by `1` is the identity on the norm quotient**, after transporting along
`conjugate_one`. -/
theorem conjugateNormQuotientEquiv_one :
    (L.conjugateNormQuotientEquiv F 1).trans
        (AddEquiv.cast (M := fun K : NormalLayer G => K.NormQuotient F) L.conjugate_one) =
      AddEquiv.refl (L.NormQuotient F) := by
  apply L.conjugateNormQuotientEquiv_trans_cast_eq F 1 L.conjugate_one
  intro x y hy
  rw [AddEquiv.refl_apply]
  congr 1
  exact Subtype.ext (by simpa using hy.symm)

/-- **Conjugation composes on the norm quotient**: conjugating by `h` and then by `g` is
conjugating by `g * h`, up to transport along `conjugate_conjugate`. -/
theorem conjugateNormQuotientEquiv_trans_conjugateNormQuotientEquiv :
    (L.conjugateNormQuotientEquiv F h).trans
        ((L.conjugate h).conjugateNormQuotientEquiv F g) =
      (L.conjugateNormQuotientEquiv F (g * h)).trans
        (AddEquiv.cast (M := fun K : NormalLayer G => K.NormQuotient F)
          (L.conjugate_conjugate g h).symm) := by
  symm
  apply L.conjugateNormQuotientEquiv_trans_cast_eq F (g * h)
    (L.conjugate_conjugate g h).symm
  intro x y hy
  rw [AddEquiv.trans_apply, conjugateNormQuotientEquiv_normQuotientMk,
    conjugateNormQuotientEquiv_normQuotientMk]
  congr 1
  exact Subtype.ext <|
    (L.conjugateGroundLevelEquiv_conjugateGroundLevelEquiv_apply_coe F g h x).trans
      ((L.conjugateGroundLevelEquiv_apply_coe F (g * h) x).trans hy.symm)

/-- Any change-of-group map on ordinary cohomology whose group part inverts conjugation by `g` on
representatives and whose coefficient part acts by `g` is `conjugateCohomologyIso`, up to the
transport along an equality of layers. -/
private theorem groupCohomologyMap_eq_conjugateCohomologyIso_hom {L' : NormalLayer G}
    (hL : L.conjugate g = L') (f : L'.Gal →* L.Gal) (φ : Rep.res f (L.rep F) ⟶ L'.rep F)
    (hf : ∀ (u : L.ground) (v : L'.ground), (v : G) = g * u * g⁻¹ →
      f (QuotientGroup.mk v) = QuotientGroup.mk u)
    (hφ : ∀ x, (φ.hom.toLinearMap x : F.toRep.V) = F.toRep.ρ g x) (n : ℕ) :
    groupCohomology.map f φ n =
      (L.conjugateCohomologyIso F g n).hom ≫ eqToHom (by rw [hL]) := by
  subst hL
  rw [eqToHom_refl, Category.comp_id, conjugateCohomologyIso, groupCohomology.mapIso_hom]
  refine groupCohomology.map_congr ?_ ?_ n
  · refine MonoidHom.ext fun γ ↦ ?_
    induction γ using QuotientGroup.induction_on with
    | H v =>
      refine (hf ((L.conjugateGroundEquiv g).symm v) v
        (by rw [conjugateGroundEquiv_symm_apply_coe]; group)).trans ?_
      rw [← MulEquiv.symm_apply_apply (L.conjugateGalEquiv g)
        (QuotientGroup.mk ((L.conjugateGroundEquiv g).symm v)), conjugateGalEquiv_mk,
        MulEquiv.apply_symm_apply]
      rfl
  · exact LinearMap.ext fun x ↦ Subtype.ext (hφ x)

/-- **Conjugation by `1` is the identity on ordinary cohomology**, up to the transport along
`conjugate_one`. -/
theorem conjugateCohomologyIso_one (n : ℕ) :
    L.conjugateCohomologyIso F 1 n = eqToIso (by rw [conjugate_one]) := by
  refine Iso.ext ?_
  have key := L.groupCohomologyMap_eq_conjugateCohomologyIso_hom F 1 L.conjugate_one
    (MonoidHom.id _) (𝟙 _)
    (fun u v huv ↦ congrArg QuotientGroup.mk (Subtype.ext (by simpa using huv)))
    (fun x ↦ by simp) n
  simpa using (comp_eqToHom_iff _ _ _).1
    ((groupCohomology.map_id (B := L.rep F) n).symm.trans key).symm

/-- **Conjugation composes on ordinary cohomology**: conjugating by `h` and then by `g` is
conjugating by `g * h`, up to the transport along `conjugate_conjugate`. -/
theorem conjugateCohomologyIso_trans_conjugateCohomologyIso (n : ℕ) :
    L.conjugateCohomologyIso F h n ≪≫ (L.conjugate h).conjugateCohomologyIso F g n =
      L.conjugateCohomologyIso F (g * h) n ≪≫ eqToIso (by rw [conjugate_conjugate]) := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, conjugateCohomologyIso,
    conjugateCohomologyIso, groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp]
  refine L.groupCohomologyMap_eq_conjugateCohomologyIso_hom F (g * h)
    (L.conjugate_conjugate g h).symm _ _ (fun u v huv ↦ ?_) (fun x ↦ ?_) n
  · rw [MonoidHom.comp_apply, MonoidHom.coe_coe, MonoidHom.coe_coe,
      MulEquiv.symm_apply_eq, MulEquiv.symm_apply_eq, conjugateGalEquiv_mk, conjugateGalEquiv_mk]
    exact congrArg QuotientGroup.mk <| Subtype.ext <| by
      rw [huv, conjugateGroundEquiv_conjugateGroundEquiv_apply_coe, conjugateGroundEquiv_apply_coe]
  · exact (L.conjugateCoefficientEquiv_conjugateCoefficientEquiv_apply_coe F g h x).trans
      (L.conjugateCoefficientEquiv_apply_coe F (g * h) x)

/-- Any Tate map of a compatible pair whose group part is conjugation by `g` on representatives and
whose coefficient part acts by `g` is `conjugateTateIso`, up to the transport along an equality of
layers. -/
private theorem tateCohomologyMap_eq_conjugateTateIso_hom {L' : NormalLayer G}
    (hL : L.conjugate g = L') {e : L.Gal ≃* L'.Gal} {φ : F.level L.top →ₗ[ℤ] F.level L'.top}
    (he' : (L.rep F).ρ.IsIntertwiningMap ((L'.rep F).ρ.comp (e : L.Gal →* L'.Gal)) φ)
    (he : ∀ (u : L.ground) (v : L'.ground), (v : G) = g * u * g⁻¹ →
      e (QuotientGroup.mk u) = QuotientGroup.mk v)
    (hφ : ∀ x, (φ x : F.toRep.V) = F.toRep.ρ g x) (r : ℤ) :
    TateCohomology.map he' r = (L.conjugateTateIso F g r).hom ≫ eqToHom (by rw [hL]) := by
  subst hL
  rw [eqToHom_refl, Category.comp_id, conjugateTateIso, TateCohomology.mapIso_hom]
  refine TateCohomology.map_congr ?_ ?_ r
  · refine MulEquiv.ext fun γ ↦ ?_
    induction γ using QuotientGroup.induction_on with
    | H u =>
      rw [conjugateGalEquiv_mk]
      exact he u _ (L.conjugateGroundEquiv_apply_coe g u)
  · exact LinearMap.ext fun x ↦ Subtype.ext (hφ x)

/-- **Conjugation by `1` is the identity on Tate cohomology**, up to the transport along
`conjugate_one`. -/
theorem conjugateTateIso_one (r : ℤ) :
    L.conjugateTateIso F 1 r = eqToIso (by rw [conjugate_one]) := by
  refine Iso.ext ?_
  have key := L.tateCohomologyMap_eq_conjugateTateIso_hom F 1 L.conjugate_one
    (Rep.isIntertwiningMap_id (L.rep F))
    (fun u v huv ↦ congrArg QuotientGroup.mk (Subtype.ext (by simpa using huv.symm)))
    (fun x ↦ by simp) r
  rw [TateCohomology.map_id] at key
  simpa using (comp_eqToHom_iff _ _ _).1 key.symm

/-- **Conjugation composes on Tate cohomology**: conjugating by `h` and then by `g` is conjugating
by `g * h`, up to the transport along `conjugate_conjugate`. -/
theorem conjugateTateIso_trans_conjugateTateIso (r : ℤ) :
    L.conjugateTateIso F h r ≪≫ (L.conjugate h).conjugateTateIso F g r =
      L.conjugateTateIso F (g * h) r ≪≫ eqToIso (by rw [conjugate_conjugate]) := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, conjugateTateIso, conjugateTateIso,
    TateCohomology.mapIso_hom, TateCohomology.mapIso_hom, TateCohomology.map_comp]
  refine L.tateCohomologyMap_eq_conjugateTateIso_hom F (g * h)
    (L.conjugate_conjugate g h).symm _ (fun u v huv ↦ ?_) (fun x ↦ ?_) r
  · rw [MulEquiv.trans_apply, conjugateGalEquiv_mk, conjugateGalEquiv_mk]
    exact congrArg QuotientGroup.mk <| Subtype.ext <| by
      rw [huv, conjugateGroundEquiv_conjugateGroundEquiv_apply_coe, conjugateGroundEquiv_apply_coe]
  · exact (L.conjugateCoefficientEquiv_conjugateCoefficientEquiv_apply_coe F g h x).trans
      (L.conjugateCoefficientEquiv_apply_coe F (g * h) x)

end NormalLayer

end TauCeti.ClassFieldTheory
