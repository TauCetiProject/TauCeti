/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore

/-!
# Moore paths and Moore loops in a product

A Moore path in a product `X × Y` is a pair of Moore paths in `X` and in `Y` run in the same time:
its two components have the same length. Two Moore paths of equal length `γ` and `δ` pair to the
Moore path `γ.prod δ` (`TauCeti.MoorePath.prod`), and the components of a Moore path in `X × Y`
identify the Moore paths in `X × Y` with the pairs of Moore paths of equal length
(`TauCeti.MoorePath.prodHomeomorph`).

For Moore loops this says that the Moore loop space of a product is the fibre product of the two
Moore loop spaces over their lengths, not their product:

`Ω_{(x, y)}(X × Y) ≅ Ω_x X ×_{[0, ∞)} Ω_y Y`

(`TauCeti.MooreLoopSpace.prodContinuousMulEquiv`), an isomorphism of topological monoids onto the
submonoid of pairs of loops of equal length (`TauCeti.MooreLoopSpace.lengthEqLocus`). A pair of
loops of different lengths, for instance a nonconstant loop in `X` and the unit of `Ω_y Y`, comes
from no Moore loop in `X × Y`.

Under this identification the Moore loop map of the first projection `X × Y → X` is the first
projection of the fibre product. Its fibre over a Moore loop `γ` at `x` is therefore the space of
Moore loops at `y` of the length of `γ` (`TauCeti.MooreLoopSpace.fiberFstHomeomorph`). For a loop
`γ` of positive length `L`, reparametrizing to the unit interval identifies these with the loop
space `Path y y` (`TauCeti.MooreLoopSpace.lengthLevelHomeomorph`), while over the unit, of length
zero, the fibre is a single point (`TauCeti.MooreLoopSpace.length_eq_zero_iff`). For a
general continuous map, `TauCeti.Topology.PathSpace.Moore.LoopFibration` identifies the fibre of
its Moore loop map with the loop space of the fibre only over the constant loops of positive length
(`TauCeti.MooreLoopSpace.fiberConstOfLengthHomeomorph`). For the first projection of a product the
description extends to every Moore loop of positive length.

## Main definitions

* `TauCeti.MoorePath.prod`: the Moore path in `X × Y` of two Moore paths of equal length.
* `TauCeti.MoorePath.prodHomeomorph`: Moore paths in `X × Y` are pairs of Moore paths of equal
  length.
* `TauCeti.MooreLoopSpace.lengthEqLocus`: the submonoid of pairs of Moore loops of equal length.
* `TauCeti.MooreLoopSpace.prodContinuousMulEquiv`: `Ω_{(x, y)}(X × Y) ≅ Ω_x X ×_{[0, ∞)} Ω_y Y`.
* `TauCeti.MooreLoopSpace.fiberFstHomeomorph`: the fibre of the Moore loop map of the first
  projection over `γ` is the space of Moore loops at `y` of the length of `γ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public noncomputable section

open Set
open scoped NNReal

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace MoorePath

/-! ### Moore paths in a product -/

/-- The **product of two Moore paths of equal length**: the Moore path `t ↦ (γ t, δ t)` in
`X × Y`, of the common length. -/
def prod (γ : MoorePath X) (δ : MoorePath Y) (h : γ.length = δ.length) : MoorePath (X × Y) where
  toFun t := (γ t, δ t)
  length := γ.length
  apply_of_length_le' t ht := Prod.ext (γ.apply_of_length_le' t ht) <| by
    simpa [h] using δ.apply_of_length_le' t (h ▸ ht)

@[simp]
theorem prod_apply (γ : MoorePath X) (δ : MoorePath Y) (h : γ.length = δ.length) (t : ℝ≥0) :
    γ.prod δ h t = (γ t, δ t) :=
  (rfl)

@[simp]
theorem length_prod (γ : MoorePath X) (δ : MoorePath Y) (h : γ.length = δ.length) :
    (γ.prod δ h).length = γ.length :=
  (rfl)

@[simp]
theorem source_prod (γ : MoorePath X) (δ : MoorePath Y) (h : γ.length = δ.length) :
    (γ.prod δ h).source = (γ.source, δ.source) := by
  simp [source_def]

@[simp]
theorem target_prod (γ : MoorePath X) (δ : MoorePath Y) (h : γ.length = δ.length) :
    (γ.prod δ h).target = (γ.target, δ.target) := by
  simp [target_def, h]

@[simp]
theorem map_fst_prod (γ : MoorePath X) (δ : MoorePath Y) (h : γ.length = δ.length) :
    (γ.prod δ h).map .fst = γ :=
  ext (by simp) fun _ ↦ by simp

@[simp]
theorem map_snd_prod (γ : MoorePath X) (δ : MoorePath Y) (h : γ.length = δ.length) :
    (γ.prod δ h).map .snd = δ :=
  ext (by simp [h]) fun _ ↦ by simp

/-- A Moore path in `X × Y` is the product of its two components. -/
@[simp]
theorem prod_map_fst_map_snd (γ : MoorePath (X × Y)) :
    (γ.map .fst).prod (γ.map .snd) ((length_map _ _).trans (length_map _ _).symm) = γ :=
  ext (by simp) fun _ ↦ by simp

/-- The product of continuous families of Moore paths of equal lengths is continuous. -/
@[fun_prop]
theorem _root_.Continuous.moorePath_prod {f : Z → MoorePath X} {g : Z → MoorePath Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ z, (f z).length = (g z).length) :
    Continuous fun z ↦ (f z).prod (g z) (h z) := by
  refine continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_length.comp hf).congr fun z ↦ (length_prod _ _ _).symm
  · exact ((hf.comp continuous_fst).moorePath_eval continuous_snd).prodMk
      ((hg.comp continuous_fst).moorePath_eval continuous_snd)

variable (X Y) in
/-- **Moore paths in a product are pairs of Moore paths of equal length**: a Moore path in `X × Y`
is sent to its two components, and a pair of Moore paths of equal length to their product. -/
def prodHomeomorph :
    MoorePath (X × Y) ≃ₜ {p : MoorePath X × MoorePath Y // p.1.length = p.2.length} where
  toFun γ := ⟨(γ.map .fst, γ.map .snd), (length_map _ _).trans (length_map _ _).symm⟩
  invFun p := p.val.1.prod p.val.2 p.property
  left_inv := prod_map_fst_map_snd
  right_inv _ := Subtype.ext <| Prod.ext (map_fst_prod _ _ _) (map_snd_prod _ _ _)
  continuous_toFun := ((continuous_map _).prodMk (continuous_map _)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtypeVal).moorePath_prod
    (continuous_snd.comp continuous_subtypeVal) _

@[simp]
theorem coe_prodHomeomorph_apply (γ : MoorePath (X × Y)) :
    (prodHomeomorph X Y γ : MoorePath X × MoorePath Y) = (γ.map .fst, γ.map .snd) :=
  (rfl)

@[simp]
theorem prodHomeomorph_symm_apply
    (p : {p : MoorePath X × MoorePath Y // p.1.length = p.2.length}) :
    (prodHomeomorph X Y).symm p = p.val.1.prod p.val.2 p.property :=
  (rfl)

end MoorePath

namespace MooreLoopSpace

variable {x : X} {y : Y}

/-! ### Moore loops in a product -/

/-- The **product of two Moore loops of equal length**, a Moore loop in `X × Y` at `(x, y)`. -/
def prod (γ : MooreLoopSpace X x) (δ : MooreLoopSpace Y y) (h : γ.length = δ.length) :
    MooreLoopSpace (X × Y) (x, y) :=
  ⟨γ.toMoorePath.prod δ.toMoorePath (by simpa using h), by simp, by simp⟩

@[simp]
theorem toMoorePath_prod (γ : MooreLoopSpace X x) (δ : MooreLoopSpace Y y)
    (h : γ.length = δ.length) :
    (γ.prod δ h).toMoorePath =
      γ.toMoorePath.prod δ.toMoorePath (by simpa using h) :=
  (rfl)

@[simp]
theorem length_prod (γ : MooreLoopSpace X x) (δ : MooreLoopSpace Y y) (h : γ.length = δ.length) :
    (γ.prod δ h).length = γ.length := by
  simp [← length_toMoorePath]

@[simp]
theorem map_fst_prod (γ : MooreLoopSpace X x) (δ : MooreLoopSpace Y y)
    (h : γ.length = δ.length) :
    map (ContinuousMap.fst : C(X × Y, X)) rfl (γ.prod δ h) = γ :=
  ext (by simp)

@[simp]
theorem map_snd_prod (γ : MooreLoopSpace X x) (δ : MooreLoopSpace Y y)
    (h : γ.length = δ.length) :
    map (ContinuousMap.snd : C(X × Y, Y)) rfl (γ.prod δ h) = δ :=
  ext (by simp)

/-- A Moore loop in `X × Y` is the product of its two components. -/
@[simp]
theorem prod_map_fst_map_snd (γ : MooreLoopSpace (X × Y) (x, y)) :
    (map (ContinuousMap.fst : C(X × Y, X)) rfl γ).prod
      (map (ContinuousMap.snd : C(X × Y, Y)) rfl γ)
      ((length_map _ _ _).trans (length_map _ _ _).symm) = γ :=
  ext (by simp)

/-- The second component of a Moore loop in `X × Y` whose first component is `γ` has the length
of `γ`. -/
theorem length_map_snd_of_map_fst_eq {γ : MooreLoopSpace X x}
    {η : MooreLoopSpace (X × Y) (x, y)} (hη : map (ContinuousMap.fst : C(X × Y, X)) rfl η = γ) :
    (map (ContinuousMap.snd : C(X × Y, Y)) rfl η).length = γ.length := by
  subst hη
  exact (length_map _ _ _).trans (length_map _ _ _).symm

/-- A Moore loop in `X × Y` whose first component is `γ` is the product of `γ` with its second
component. -/
theorem prod_map_snd_of_map_fst_eq {γ : MooreLoopSpace X x} {η : MooreLoopSpace (X × Y) (x, y)}
    (hη : map (ContinuousMap.fst : C(X × Y, X)) rfl η = γ)
    (h : γ.length = (map (ContinuousMap.snd : C(X × Y, Y)) rfl η).length) :
    γ.prod (map (ContinuousMap.snd : C(X × Y, Y)) rfl η) h = η := by
  subst hη
  exact prod_map_fst_map_snd η

/-- The product of continuous families of Moore loops of equal lengths is continuous. -/
@[fun_prop]
theorem _root_.Continuous.mooreLoopSpace_prod {f : Z → MooreLoopSpace X x}
    {g : Z → MooreLoopSpace Y y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z, (f z).length = (g z).length) :
    Continuous fun z ↦ (f z).prod (g z) (h z) :=
  isEmbedding_toMoorePath.continuous_iff.2 <|
    (continuous_toMoorePath.comp hf).moorePath_prod (continuous_toMoorePath.comp hg)
      fun z ↦ by simpa using h z

variable (x y) in
/-- The pairs of Moore loops at `x` and at `y` of equal length: the fibre product
`Ω_x X ×_{[0, ∞)} Ω_y Y` of the two lengths, a submonoid of `Ω_x X × Ω_y Y` since lengths add
under concatenation. -/
def lengthEqLocus : Submonoid (MooreLoopSpace X x × MooreLoopSpace Y y) :=
  ((lengthHom x : MooreLoopSpace X x →* Multiplicative ℝ≥0).comp (MonoidHom.fst _ _)).eqLocusM
    ((lengthHom y : MooreLoopSpace Y y →* Multiplicative ℝ≥0).comp (MonoidHom.snd _ _))

@[simp]
theorem mem_lengthEqLocus {p : MooreLoopSpace X x × MooreLoopSpace Y y} :
    p ∈ lengthEqLocus x y ↔ p.1.length = p.2.length := by
  simp [lengthEqLocus, MonoidHom.mem_eqLocusM, lengthHom_apply]

variable (x y) in
/-- **The Moore loop space of a product is the fibre product of the Moore loop spaces over their
lengths**: a Moore loop in `X × Y` at `(x, y)` is sent to its two components, which are Moore
loops of equal length, and this is an isomorphism of topological monoids onto the submonoid
`TauCeti.MooreLoopSpace.lengthEqLocus` of pairs of loops of equal length. -/
def prodContinuousMulEquiv : MooreLoopSpace (X × Y) (x, y) ≃ₜ* lengthEqLocus x y where
  toFun γ := ⟨(map (ContinuousMap.fst : C(X × Y, X)) rfl γ,
    map (ContinuousMap.snd : C(X × Y, Y)) rfl γ),
    mem_lengthEqLocus.2 ((length_map _ _ _).trans (length_map _ _ _).symm)⟩
  invFun p := p.val.1.prod p.val.2 (mem_lengthEqLocus.1 p.property)
  left_inv := prod_map_fst_map_snd
  right_inv _ := Subtype.ext <| Prod.ext (map_fst_prod _ _ _) (map_snd_prod _ _ _)
  map_mul' γ δ := Subtype.ext <| Prod.ext (map_mul _ γ δ) (map_mul _ γ δ)
  continuous_toFun := ((map _ _).continuous.prodMk (map _ _).continuous).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtypeVal).mooreLoopSpace_prod
    (continuous_snd.comp continuous_subtypeVal) _

@[simp]
theorem coe_prodContinuousMulEquiv_apply (γ : MooreLoopSpace (X × Y) (x, y)) :
    (prodContinuousMulEquiv x y γ : MooreLoopSpace X x × MooreLoopSpace Y y) =
      (map (ContinuousMap.fst : C(X × Y, X)) rfl γ,
        map (ContinuousMap.snd : C(X × Y, Y)) rfl γ) :=
  (rfl)

@[simp]
theorem prodContinuousMulEquiv_symm_apply (p : lengthEqLocus x y) :
    (prodContinuousMulEquiv x y).symm p =
      p.val.1.prod p.val.2 (mem_lengthEqLocus.1 p.property) :=
  (rfl)

/-- The product of Moore loops is multiplicative: concatenating products of loops of equal length
concatenates their components. -/
@[simp]
theorem prod_mul_prod (γ γ' : MooreLoopSpace X x) (δ δ' : MooreLoopSpace Y y)
    (h : γ.length = δ.length) (h' : γ'.length = δ'.length) :
    γ.prod δ h * γ'.prod δ' h' =
      (γ * γ').prod (δ * δ') (by rw [length_mul, length_mul, h, h']) :=
  ext <| MoorePath.ext (by simp) fun t ↦ by
    simp only [toMoorePath_mul, toMoorePath_prod, MoorePath.trans_apply, MoorePath.prod_apply,
      MoorePath.length_prod, length_toMoorePath, h]
    split_ifs <;> rfl

/-- The product of the units is the unit. -/
@[simp]
theorem prod_one_one :
    (1 : MooreLoopSpace X x).prod (1 : MooreLoopSpace Y y) (length_one.trans length_one.symm) =
      1 :=
  (prodContinuousMulEquiv x y).injective <| by
    rw [map_one]
    exact Subtype.ext (Prod.ext (by simp) (by simp))

/-! ### The fibres of the Moore loop map of the first projection -/

/-- **The fibre of the Moore loop map of the first projection** `X × Y → X` over a Moore loop `γ`
at `x` is the space of Moore loops at `y` of the length of `γ`: a loop in the fibre is sent to
its second component, and a loop `δ` of the length of `γ` to the product of `γ` and `δ`. -/
def fiberFstHomeomorph (γ : MooreLoopSpace X x) :
    (map (ContinuousMap.fst : C(X × Y, X)) rfl ⁻¹' {γ} : Set (MooreLoopSpace (X × Y) (x, y))) ≃ₜ
      (length ⁻¹' {γ.length} : Set (MooreLoopSpace Y y)) where
  toFun η := ⟨map (ContinuousMap.snd : C(X × Y, Y)) rfl η.val,
    length_map_snd_of_map_fst_eq (eq_of_mem_singleton η.property)⟩
  invFun δ := ⟨γ.prod δ.val (eq_of_mem_singleton δ.property).symm, map_fst_prod _ _ _⟩
  left_inv η := Subtype.ext <| prod_map_snd_of_map_fst_eq (eq_of_mem_singleton η.property)
    (length_map_snd_of_map_fst_eq (eq_of_mem_singleton η.property)).symm
  right_inv δ := Subtype.ext <| map_snd_prod γ δ.val (eq_of_mem_singleton δ.property).symm
  continuous_toFun := ((map _ _).continuous.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_const.mooreLoopSpace_prod continuous_subtypeVal
    fun δ ↦ (eq_of_mem_singleton (mem_preimage.1 δ.property)).symm).subtype_mk _

@[simp]
theorem coe_fiberFstHomeomorph_apply (γ : MooreLoopSpace X x)
    (η : (map (ContinuousMap.fst : C(X × Y, X)) rfl ⁻¹' {γ} :
      Set (MooreLoopSpace (X × Y) (x, y)))) :
    (fiberFstHomeomorph γ η : MooreLoopSpace Y y) =
      map (ContinuousMap.snd : C(X × Y, Y)) rfl η.val :=
  (rfl)

@[simp]
theorem coe_fiberFstHomeomorph_symm_apply (γ : MooreLoopSpace X x)
    (δ : (length ⁻¹' {γ.length} : Set (MooreLoopSpace Y y))) :
    ((fiberFstHomeomorph γ).symm δ : MooreLoopSpace (X × Y) (x, y)) =
      γ.prod δ.val (eq_of_mem_singleton δ.property).symm :=
  (rfl)

end MooreLoopSpace

end TauCeti
