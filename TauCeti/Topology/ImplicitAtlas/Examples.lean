/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Examples of implicit atlases

This file constructs the two basic examples of `TauCeti.ImplicitAtlas`, which are the test inputs
for the virtual fundamental class.

* **The manifold atlas** (`TauCeti.ImplicitAtlas.ofChartedSpace`). A Hausdorff space charted on
  `ℝⁿ` is an implicit atlas of virtual dimension `n` with an empty index set: the only thickening
  is `X_∅ = X`, it is regular everywhere, and its charts give the product model. In particular
  the regular locus of an atlas is part of its data and may be all of `X`.
* **The atlas `s(x) = xᵐ` on a point** (`TauCeti.ImplicitAtlas.powAtlas`, Pardon, Example 2.3.2).
  The point `X = {0}` of virtual dimension `0`, with one index `α`, trivial group `Γ_α`, obstruction
  space `E_α = ℝ`, thickening `X_α = ℝ` and Kuranishi map `s_α(x) = xᵐ`, `m ≥ 1`. The regular locus
  of `X_∅ = X` is empty, so the footprint `V_∅` is empty
  (`TauCeti.ImplicitAtlas.footprint_powAtlas_empty`), while `X_α` is regular. The zero set
  `Z_∅α = {0}` (`TauCeti.ImplicitAtlas.kuranishiZeroSet_powKuranishi_empty`) maps onto `X`, so the
  footprint `V_α = X` covers. For `m ≥ 2` the zero `0` of `s_α` is not transverse, so `X` is not
  cut out transversally by `s_α`; the atlas describes it through the regular thickening `X_α`.

The thickenings of `powAtlas` are the subtypes `{x : ℝ // I = ∅ → x = 0}` of `ℝ`
(`TauCeti.ImplicitAtlas.PowThickening`): the point `{0}` for `I = ∅` and `ℝ` for `I = {α}`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Example 2.3.2 and
  Definition 3.1.1.
-/

public section

open Set Topology

namespace TauCeti.ImplicitAtlas

/-! ### The manifold atlas -/

section ChartedSpace

variable {A : Type*} [IsEmpty A] [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
  [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
  [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
  (ρ : ∀ α, Representation ℝ (Γ α) (E α)) (n : ℕ) (X : Type*) [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- **The manifold atlas.** A Hausdorff space charted on `ℝⁿ` is an implicit atlas of virtual
dimension `n` with an empty index set, whose only thickening `X_∅ = X` is regular everywhere. -/
noncomputable def ofChartedSpace :
    ImplicitAtlas Γ E ρ (fun _ ↦ X) (fun _ ↦ 1) X n where
  baseHomeomorph := Homeomorph.refl X
  kuranishi _ α _ := (IsEmpty.false α.val).elim
  continuous_kuranishi _ α := (IsEmpty.false α.val).elim
  kuranishi_act _ α := (IsEmpty.false α.val).elim
  regLocus _ := univ
  isOpen_regLocus _ := isOpen_univ
  act_mem_regLocus _ _ _ _ := mem_univ _
  footprintMap _ _ _ x := x.val
  continuous_footprintMap _ _ _ := continuous_subtypeVal
  footprintMap_act _ _ _ _ _ _ := rfl
  footprintMap_self _ _ := rfl
  footprintMap_footprintMap _ _ _ _ _ _ _ _ := rfl
  kuranishi_footprintMap _ _ _ _ α := (IsEmpty.false α.val).elim
  isOpen_range_footprintMap _ _ _ := by
    rw [Subtype.range_coe, kuranishiZeroSet_eq_univ _ fun α ↦ (IsEmpty.false α).elim]
    exact isOpen_univ
  range_footprintMap_inter _ _ _ _ _ := by
    ext
    simp
  footprintMap_mem_range_iff _ _ _ _ _ _ := by simp
  isQuotientMap_footprintMap I J _ :=
    IsQuotientMap.of_inverse
      (f := fun y ↦ ⟨y.val, by simp⟩)
      (continuous_subtypeVal.subtype_mk _) continuous_subtypeVal.rangeFactorization
      fun _ ↦ rfl
  footprintMap_eq_footprintMap_iff _ _ _ x y :=
    ⟨fun h ↦ ⟨1, rfl, h⟩, fun ⟨_, _, h⟩ ↦ h⟩
  mem_regLocus_of_footprintMap_mem _ _ _ _ _ := mem_univ _
  eq_one_of_act_eq _ _ _ _ _ _ _ _ := funext fun α ↦ (IsEmpty.false α.val).elim
  exists_openPartialHomeomorph I J _ x _ := by
    have : IsEmpty ↥(J \ I) := ⟨fun α ↦ IsEmpty.false α.val⟩
    refine ⟨n, by simp [Finset.eq_empty_of_isEmpty I],
      (chartAt (EuclideanSpace ℝ (Fin n)) x.val).transHomeomorph (Homeomorph.prodUnique _ _).symm,
      by simp, fun _ _ ↦ funext fun α ↦ (IsEmpty.false α.val).elim⟩
  exists_footprintMap_eq y :=
    ⟨∅, ⟨y, by simp⟩, mem_univ _, rfl⟩

/-- The regular locus of the manifold atlas is the whole space. -/
@[simp]
theorem regLocus_ofChartedSpace (I : Finset A) : (ofChartedSpace Γ E ρ n X).regLocus I = univ :=
  (rfl)

/-- The regular footprint of the manifold atlas is the whole space. -/
@[simp]
theorem footprint_ofChartedSpace (I : Finset A) : (ofChartedSpace Γ E ρ n X).footprint I = univ :=
  eq_univ_of_forall fun y ↦ (ofChartedSpace Γ E ρ n X).mem_footprint.2
    ⟨⟨y, by simp⟩, mem_univ _, rfl⟩

end ChartedSpace

/-! ### The atlas `s(x) = xᵐ` on a point -/

section Pow

/-- The thickenings of `TauCeti.ImplicitAtlas.powAtlas`: the point `{0}` for `I = ∅` and the line
`ℝ` for `I = {α}`. -/
abbrev PowThickening (I : Finset Unit) : Type := {x : ℝ // I = ∅ → x = 0}

/-- The Kuranishi map `s_α(x) = xᵐ` of `TauCeti.ImplicitAtlas.powAtlas`. -/
def powKuranishi (m : ℕ) (J : Finset Unit) (_ : J) (x : PowThickening J) : ℝ := (x : ℝ) ^ m

@[simp]
theorem powKuranishi_apply (m : ℕ) (J : Finset Unit) (α : J) (x : PowThickening J) :
    powKuranishi m J α x = (x : ℝ) ^ m :=
  (rfl)

/-- A finite set of indices that misses the only index is empty. -/
private theorem eq_empty_of_notMem {I : Finset Unit} {α : Unit} (hα : α ∉ I) : I = ∅ :=
  Finset.eq_empty_of_forall_notMem fun β hβ ↦ hα (Subsingleton.elim β α ▸ hβ)

variable {m : ℕ}

/-- The zero set `Z_∅J` of the Kuranishi map `s(x) = xᵐ` of `TauCeti.ImplicitAtlas.powAtlas` is
`{0}`. -/
theorem kuranishiZeroSet_powKuranishi_empty (hm : m ≠ 0) (J : Finset Unit) :
    kuranishiZeroSet (E := fun _ ↦ ℝ) (powKuranishi m) ∅ J =
      {x : PowThickening J | (x : ℝ) = 0} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ mem_kuranishiZeroSet.2 fun _ _ ↦ by simp [hx.out, zero_pow hm]⟩
  by_cases hJ : J = ∅
  · exact x.property hJ
  · obtain ⟨α, hα⟩ := Finset.ne_empty_iff_nonempty.1 hJ
    exact pow_eq_zero_iff hm |>.1 <| mem_kuranishiZeroSet.1 hx ⟨α, hα⟩ (Finset.notMem_empty α)

/-- The footprint map of `TauCeti.ImplicitAtlas.powAtlas` keeps the real coordinate. -/
private def powFootprintMap (hm : m ≠ 0) {I J : Finset Unit} (_ : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ ↦ ℝ) (powKuranishi m) I J) : PowThickening I :=
  ⟨x.val.val, fun hI ↦ (kuranishiZeroSet_powKuranishi_empty hm J).subset (hI ▸ x.property)⟩

/-- A continuous section of `powFootprintMap`, so that it is onto and a quotient map. -/
private def powSection (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J) (y : PowThickening I) :
    kuranishiZeroSet (E := fun _ ↦ ℝ) (powKuranishi m) I J :=
  ⟨⟨y.val, fun hJ ↦ y.property (Finset.subset_empty.1 (hJ ▸ h))⟩, mem_kuranishiZeroSet.2 fun _ hα ↦
      by
    simp [y.property (eq_empty_of_notMem hα), zero_pow hm]⟩

private theorem continuous_powSection (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J) :
    Continuous (powSection hm h) :=
  (continuous_subtypeVal.subtype_mk _).subtype_mk _

private theorem powFootprintMap_powSection (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J)
    (y : PowThickening I) : powFootprintMap hm h (powSection hm h y) = y :=
  rfl

private theorem range_powFootprintMap (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J) :
    range (powFootprintMap hm h) = univ :=
  eq_univ_of_forall fun y ↦ ⟨_, powFootprintMap_powSection hm h y⟩

/-- A thickening at a nonempty index set is the line `ℝ`. -/
private def powThickeningHomeomorph {J : Finset Unit} (hJ : J.Nonempty) : PowThickening J ≃ₜ ℝ where
  toFun := Subtype.val
  invFun x := ⟨x, fun h ↦ (hJ.ne_empty h).elim⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtypeVal
  continuous_invFun := continuous_id.subtype_mk _

/-- **Pardon's Example 2.3.2.** The implicit atlas of virtual dimension `0` on the point
`X = {0}` with one index `α`, trivial group, obstruction space `E_α = ℝ`, thickening `X_α = ℝ`
and Kuranishi map `s_α(x) = xᵐ`, `m ≠ 0`. The regular locus of `X_∅ = X` is empty and `X_α` is
regular. -/
noncomputable def powAtlas (hm : m ≠ 0) :
    ImplicitAtlas (fun _ : Unit ↦ Unit) (fun _ ↦ ℝ) (fun _ ↦ Representation.trivial ℝ Unit ℝ)
      PowThickening (fun _ ↦ 1) (PowThickening ∅) 0 where
  baseHomeomorph := Homeomorph.refl _
  kuranishi := powKuranishi m
  continuous_kuranishi _ _ := continuous_subtypeVal.pow m
  kuranishi_act _ _ _ _ := by simp
  regLocus I := {_x | I.Nonempty}
  isOpen_regLocus _ := isOpen_const
  act_mem_regLocus _ _ _ h := h
  footprintMap _ _ := powFootprintMap hm
  continuous_footprintMap _ _ _ :=
    (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  footprintMap_act _ _ _ _ _ _ := by ext; simp [powFootprintMap]
  footprintMap_self _ _ := rfl
  footprintMap_footprintMap _ _ _ _ _ _ _ _ := rfl
  kuranishi_footprintMap _ _ _ _ _ := rfl
  isOpen_range_footprintMap _ _ h := by
    rw [range_powFootprintMap hm h]
    exact isOpen_univ
  range_footprintMap_inter _ _ _ _ _ := by simp only [range_powFootprintMap, inter_self]
  footprintMap_mem_range_iff _ _ _ _ _ _ := by simp only [range_powFootprintMap, mem_univ]
  isQuotientMap_footprintMap _ _ h :=
    IsQuotientMap.of_inverse (f := fun y : range (powFootprintMap hm h) ↦ powSection hm h y.val)
      ((continuous_powSection hm h).comp continuous_subtypeVal)
      (((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _).rangeFactorization)
      fun y ↦ Subtype.ext (powFootprintMap_powSection hm h y.val)
  footprintMap_eq_footprintMap_iff _ _ _ x y := by
    simp only [powFootprintMap, Subtype.mk.injEq, MonoidHom.one_apply, Homeomorph.one_apply]
    exact ⟨fun h ↦ ⟨1, Subsingleton.elim _ _, Subtype.ext h⟩, fun ⟨_, _, h⟩ ↦ congrArg _ h⟩
  mem_regLocus_of_footprintMap_mem _ _ h _ hx := Finset.Nonempty.mono h hx
  eq_one_of_act_eq _ _ _ _ _ _ _ _ := Subsingleton.elim _ _
  exists_openPartialHomeomorph I J h x hx := by
    have hJ : J.Nonempty := Finset.Nonempty.mono h hx
    obtain rfl : I = Finset.univ := hx.eq_univ
    have : IsEmpty ↥(J \ Finset.univ) := ⟨fun α ↦ (Finset.mem_sdiff.1 α.property).2
        (Finset.mem_univ _)⟩
    refine ⟨1, by simp, ((powThickeningHomeomorph hJ).trans <|
      ((Homeomorph.funUnique (Fin 1) ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 1) ℝ).symm.toHomeomorph).trans
        (Homeomorph.prodUnique _ _).symm).toOpenPartialHomeomorph, by simp,
      fun _ _ ↦ Subsingleton.elim _ _⟩
  exists_footprintMap_eq y :=
    ⟨Finset.univ, powSection hm (Finset.empty_subset _) y, Finset.univ_nonempty, rfl⟩

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.powAtlas` is everything for `I = {α}`
and empty for `I = ∅`. -/
theorem regLocus_powAtlas (hm : m ≠ 0) (I : Finset Unit) :
    (powAtlas hm).regLocus I = {_x | I.Nonempty} :=
  (rfl)

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.powAtlas` is `s_α(x) = xᵐ`. -/
@[simp]
theorem kuranishi_powAtlas (hm : m ≠ 0) : (powAtlas hm).kuranishi = powKuranishi m :=
  (rfl)

/-- The footprint maps of `TauCeti.ImplicitAtlas.powAtlas` keep the real coordinate. -/
@[simp]
theorem coe_footprintMap_powAtlas (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ : Unit ↦ ℝ) (powAtlas hm).kuranishi I J) :
    ((powAtlas hm).footprintMap h x : ℝ) = ((x : PowThickening J) : ℝ) :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.powAtlas` is empty. -/
@[simp]
theorem regLocus_powAtlas_empty (hm : m ≠ 0) : (powAtlas hm).regLocus ∅ = ∅ := by
  simp [regLocus_powAtlas]

/-- The footprint `V_∅` of `TauCeti.ImplicitAtlas.powAtlas` is empty, since the regular locus of
`X_∅` is. So the footprints of the subsets of the empty set of indices do not cover the point. -/
@[simp]
theorem footprint_powAtlas_empty (hm : m ≠ 0) : (powAtlas hm).footprint ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hy ↦ by
    obtain ⟨x, hx, -⟩ := (powAtlas hm).mem_footprint.1 hy
    simp at hx

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.powAtlas` is the whole point. -/
@[simp]
theorem footprint_powAtlas_singleton (hm : m ≠ 0) : (powAtlas hm).footprint {()} = univ :=
  eq_univ_of_forall fun y ↦ (powAtlas hm).mem_footprint.2
    ⟨powSection hm (Finset.empty_subset _) y, by simp [regLocus_powAtlas],
      Subtype.ext (coe_footprintMap_powAtlas hm (Finset.empty_subset _) _)⟩

end Pow

end TauCeti.ImplicitAtlas
