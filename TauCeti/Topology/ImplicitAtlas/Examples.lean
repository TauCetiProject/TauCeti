/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.DeformationSpace
public import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Examples of implicit atlases

This file constructs the basic examples of `TauCeti.ImplicitAtlas`, which are the test inputs for
the virtual fundamental class.

* **The manifold atlas** (`TauCeti.ImplicitAtlas.ofChartedSpace`). A Hausdorff space charted on
  `ℝⁿ` is an implicit atlas of virtual dimension `n` with an empty index set: the only thickening
  is `X_∅ = X`, it is regular everywhere, and its charts give the product model. In particular
  the regular locus of an atlas is part of its data and may be all of `X`.
* **The atlas `s = 0` on a point** (`TauCeti.ImplicitAtlas.zeroAtlas`). The point `X = X_∅ = X_α`
  with one index `α`, a finite isotropy group `Γ_α` acting trivially on the point, an obstruction
  representation `E_α` and Kuranishi map `s_α = 0`, of virtual dimension `d = -dim E_α`. The
  regular locus of `X_∅` is empty and `X_α` is regular. For `E_α = ℝ` this is an atlas of
  negative virtual dimension `-1` on a nonempty space; regular loci of negative expected dimension
  are empty (`TauCeti.ImplicitAtlas.regLocus_eq_empty_of_neg`), but the regular locus of `X_α` has
  expected dimension `d + dim E_α = 0`. For `E_α = 0` and a nontrivial `Γ_α` it is the
  *ineffective point*: `Γ_α` acts trivially, and freeness over `ψ_∅α⁻¹(X_∅^reg)` forces the
  regular locus of `X_∅` to be empty in every atlas with these data
  (`TauCeti.ImplicitAtlas.regLocus_empty_eq_empty_of_nontrivial`).
* **The atlas `s(x) = xᵐ` on a point** (`TauCeti.ImplicitAtlas.powAtlas`, Pardon, Example 2.3.2).
  The point `X = {0}` of virtual dimension `0`, with one index `α`, trivial group `Γ_α`, obstruction
  space `E_α = ℝ`, thickening `X_α = ℝ` and Kuranishi map `s_α(x) = xᵐ`, `m ≥ 1`. The regular locus
  of `X_∅ = X` is empty, so the footprint `V_∅` is empty
  (`TauCeti.ImplicitAtlas.footprint_powAtlas_empty`), while `X_α` is regular. The zero set
  `Z_∅α = {0}` (`TauCeti.ImplicitAtlas.kuranishiZeroSet_powKuranishi_empty`) maps onto `X`, so the
  footprint `V_α = X` covers. For `m ≥ 2` the zero `0` of `s_α` is not transverse, so `X` is not
  cut out transversally by `s_α`; the atlas describes it through the regular thickening `X_α`.
* **The reflection atlas** (`TauCeti.ImplicitAtlas.reflectionAtlas`). The same data with `m` even
  and the group `Γ_α = ℤˣ ≅ ℤ/2` acting on `X_α = ℝ` by the reflection `x ↦ -x`
  (`TauCeti.ImplicitAtlas.reflectionAct`) and trivially on `E_α`. The reflection fixes the zero
  set `Z_∅α = {0}`, so `Γ_α` does not act freely there, which is allowed because `X_∅` is not
  regular, and `Z_∅α / Γ_α = X`. The reflection reverses the orientation of `X_α` while fixing
  that of `E_α`; this makes the atlas, for `m = 2`, the test case for the failure of local
  orientability, which is not treated in this file.

For the atlas `s(x) = xᵐ`, whose regular locus `X_∅^reg` is empty, the deformation space
`D_(∅,α,α)` is empty (`TauCeti.ImplicitAtlas.deformationSpace_powAtlas_empty`), and
`D_(α,α,α)` is `{(e, t, x) | t > 0, xᵐ = t e}`
(`TauCeti.ImplicitAtlas.mem_deformationSpace_powAtlas_iff`): the points with `t = 0` are missing
because `X_∅^reg = ∅`. Its support `Z_X` is the half-line `x = 0, e = 0, t > 0`, without its
endpoint (`TauCeti.ImplicitAtlas.mem_deformationSupport_powAtlas_iff`).

The thickenings of `powAtlas` and `reflectionAtlas` are the subtypes `{x : ℝ // I = ∅ → x = 0}`
of `ℝ` (`TauCeti.ImplicitAtlas.PowThickening`): the point `{0}` for `I = ∅` and `ℝ` for
`I = {α}`.

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

/-! ### The atlas `s = 0` on a point -/

section Zero

/-- Over the single index of `Unit`, a nonempty `I` is everything, so `J \ I` is empty. -/
private theorem isEmpty_sdiff_of_nonempty {I J : Finset Unit} (hI : I.Nonempty) :
    IsEmpty ↥(J \ I) :=
  ⟨fun α ↦ (Finset.mem_sdiff.1 α.property).2 (by simp [hI.eq_univ])⟩

/-- Over the single index of `Unit`, an element of `Γ_J` whose restriction to a nonempty `I ⊆ J`
is trivial is itself trivial, since then `I = J`. -/
private theorem eq_one_of_restrict₂_eq_one {Γ : Unit → Type*} [∀ α, One (Γ α)]
    {I J : Finset Unit} (h : I ⊆ J) (hI : I.Nonempty) {g : (α : J) → Γ α}
    (hg : Finset.restrict₂ (π := Γ) h g = 1) : g = 1 :=
  funext fun α ↦ congr_fun hg ⟨α.val, hI.eq_univ ▸ Finset.mem_univ _⟩

variable (Γ : Type*) [Group Γ] [Finite Γ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (ρ : Representation ℝ Γ E) {d : ℤ}

/-- The zero sets of the Kuranishi maps `s = 0` are everything, so they are nonempty. -/
private instance (I J : Finset Unit) :
    Nonempty (kuranishiZeroSet (T := fun _ ↦ Unit) (E := fun _ : Unit ↦ E) (fun _ _ _ ↦ 0) I J) :=
  ⟨⟨(), mem_kuranishiZeroSet.2 fun _ _ ↦ rfl⟩⟩

/-- **The atlas `s = 0` on a point.** For a finite group `Γ` and a finite-dimensional real
representation `ρ` of `Γ` on `E`, the point `X = X_∅ = X_α` with one index `α`, isotropy group
`Γ_α = Γ` acting trivially on the point, obstruction space `E_α = E` and Kuranishi map `s_α = 0`
is an implicit atlas of virtual dimension `d = -dim E`. The regular locus of `X_∅` is empty and
`X_α` is regular, a manifold of dimension `d + dim E = 0`.

For `E = ℝ` and `d = -1` this is an atlas on a nonempty space of negative virtual dimension. For
`E = 0`, `d = 0` and a nontrivial `Γ` it is the *ineffective point*, on which `Γ_α` acts
trivially; its base `X_∅` cannot be regular
(`TauCeti.ImplicitAtlas.regLocus_empty_eq_empty_of_nontrivial`). -/
noncomputable def zeroAtlas (hd : d + Module.finrank ℝ E = 0) :
    ImplicitAtlas (fun _ : Unit ↦ Γ) (fun _ ↦ E) (fun _ ↦ ρ) (fun _ ↦ Unit) (fun _ ↦ 1) Unit d where
  baseHomeomorph := Homeomorph.refl Unit
  kuranishi _ _ _ := 0
  continuous_kuranishi _ _ := continuous_const
  kuranishi_act _ _ _ _ := (map_zero _).symm
  regLocus I := {_x | I.Nonempty}
  isOpen_regLocus _ := isOpen_const
  act_mem_regLocus _ _ _ h := h
  footprintMap _ _ _ _ := ()
  continuous_footprintMap _ _ _ := continuous_const
  footprintMap_act _ _ _ _ _ _ := rfl
  footprintMap_self _ _ := rfl
  footprintMap_footprintMap _ _ _ _ _ _ _ _ := rfl
  kuranishi_footprintMap _ _ _ _ _ := rfl
  isOpen_range_footprintMap _ _ _ := isOpen_discrete _
  range_footprintMap_inter _ _ _ _ _ := by
    simp only [range_const, inter_self]
  footprintMap_mem_range_iff _ _ _ _ _ _ := by
    simp only [range_const, mem_singleton_iff]
  isQuotientMap_footprintMap _ _ _ :=
    IsQuotientMap.of_inverse (f := fun _ ↦ ⟨(), mem_kuranishiZeroSet.2 fun _ _ ↦ rfl⟩)
      continuous_const (continuous_const.rangeFactorization) fun _ ↦ Subsingleton.elim _ _
  footprintMap_eq_footprintMap_iff _ _ _ _ _ :=
    ⟨fun _ ↦ ⟨1, rfl, Subsingleton.elim _ _⟩, fun _ ↦ rfl⟩
  mem_regLocus_of_footprintMap_mem _ _ h _ hx := Finset.Nonempty.mono h hx
  eq_one_of_act_eq _ _ h _ hx _ hg _ := eq_one_of_restrict₂_eq_one h hx hg
  exists_openPartialHomeomorph _ J _ _ hx := by
    have := isEmpty_sdiff_of_nonempty (J := J) hx
    refine ⟨0, by simp [hd, hx.eq_univ],
      ((Homeomorph.homeomorphOfUnique Unit (EuclideanSpace ℝ (Fin 0))).trans
        (Homeomorph.prodUnique _ _).symm).toOpenPartialHomeomorph, mem_univ _,
      fun _ _ ↦ Subsingleton.elim _ _⟩
  exists_footprintMap_eq _ :=
    ⟨Finset.univ, ⟨(), mem_kuranishiZeroSet.2 fun _ _ ↦ rfl⟩, Finset.univ_nonempty, rfl⟩

variable {Γ ρ}

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.zeroAtlas` is everything for `I = {α}`
and empty for `I = ∅`. -/
theorem regLocus_zeroAtlas (hd : d + Module.finrank ℝ E = 0) (I : Finset Unit) :
    (zeroAtlas Γ ρ hd).regLocus I = {_x | I.Nonempty} :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.zeroAtlas` is empty. -/
@[simp]
theorem regLocus_zeroAtlas_empty (hd : d + Module.finrank ℝ E = 0) :
    (zeroAtlas Γ ρ hd).regLocus ∅ = ∅ := by
  simp [regLocus_zeroAtlas]

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.zeroAtlas` is `s_α = 0`. -/
@[simp]
theorem kuranishi_zeroAtlas (hd : d + Module.finrank ℝ E = 0) (I : Finset Unit) (α : I)
    (x : Unit) : (zeroAtlas Γ ρ hd).kuranishi I α x = 0 :=
  (rfl)

/-- The footprint `V_∅` of `TauCeti.ImplicitAtlas.zeroAtlas` is empty, since the regular locus
of `X_∅` is. -/
@[simp]
theorem footprint_zeroAtlas_empty (hd : d + Module.finrank ℝ E = 0) :
    (zeroAtlas Γ ρ hd).footprint ∅ = ∅ :=
  footprint_eq_empty_of_regLocus_eq_empty _ (regLocus_zeroAtlas_empty hd)

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.zeroAtlas` is the whole point. -/
@[simp]
theorem footprint_zeroAtlas_singleton (hd : d + Module.finrank ℝ E = 0) :
    (zeroAtlas Γ ρ hd).footprint {()} = univ :=
  eq_univ_of_forall fun _ ↦ (zeroAtlas Γ ρ hd).mem_footprint.2
    ⟨⟨(), mem_kuranishiZeroSet.2 fun _ _ ↦ rfl⟩, Finset.univ_nonempty, rfl⟩

end Zero

/-! ### The atlas `s(x) = xᵐ` on a point -/

section Pow

/-- The thickenings of `TauCeti.ImplicitAtlas.powAtlas`: the point `{0}` for `I = ∅` and the line
`ℝ` for `I = {α}`. -/
abbrev PowThickening (I : Finset Unit) : Type := {x : ℝ // I = ∅ → x = 0}

/-- The thickening `X_∅ = {0}` of `TauCeti.ImplicitAtlas.powAtlas` is a point. -/
instance : Subsingleton (PowThickening ∅) :=
  ⟨fun x y ↦ Subtype.ext <| (x.property rfl).trans (y.property rfl).symm⟩

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

private theorem continuous_powFootprintMap (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J) :
    Continuous (powFootprintMap hm h) :=
  (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _

private theorem isOpen_range_powFootprintMap (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J) :
    IsOpen (range (powFootprintMap hm h)) := by
  rw [range_powFootprintMap hm h]
  exact isOpen_univ

private theorem isQuotientMap_powFootprintMap (hm : m ≠ 0) {I J : Finset Unit} (h : I ⊆ J) :
    IsQuotientMap (rangeFactorization (powFootprintMap hm h)) :=
  IsQuotientMap.of_inverse (f := fun y : range (powFootprintMap hm h) ↦ powSection hm h y.val)
    ((continuous_powSection hm h).comp continuous_subtypeVal)
    (continuous_powFootprintMap hm h).rangeFactorization
    fun y ↦ Subtype.ext (powFootprintMap_powSection hm h y.val)

/-- A thickening at a nonempty index set is the line `ℝ`. -/
private def powThickeningHomeomorph {J : Finset Unit} (hJ : J.Nonempty) : PowThickening J ≃ₜ ℝ where
  toFun := Subtype.val
  invFun x := ⟨x, fun h ↦ (hJ.ne_empty h).elim⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtypeVal
  continuous_invFun := continuous_id.subtype_mk _

/-- The product model of the atlases on the thickenings `PowThickening`: over a nonempty `I ⊆ J`
the thickening `X_J = ℝ` is a manifold of dimension `0 + dim ℝ = 1`, and `J \ I` is empty. -/
private theorem exists_powChart {I J : Finset Unit} (h : I ⊆ J) (hI : I.Nonempty)
    (x : PowThickening J) (f : PowThickening J → (α : ↥(J \ I)) → ℝ) :
    ∃ n : ℕ, (n : ℤ) = 0 + ∑ _α ∈ I, (Module.finrank ℝ ℝ : ℤ) ∧
      ∃ e : OpenPartialHomeomorph (PowThickening J)
          (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ I)) → ℝ)),
        x ∈ e.source ∧ ∀ y ∈ e.source, (e y).2 = f y := by
  have hJ : J.Nonempty := hI.mono h
  have := isEmpty_sdiff_of_nonempty (J := J) hI
  obtain rfl : I = Finset.univ := hI.eq_univ
  exact ⟨1, by simp, ((powThickeningHomeomorph hJ).trans <|
    ((Homeomorph.funUnique (Fin 1) ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 1) ℝ).symm.toHomeomorph).trans
      (Homeomorph.prodUnique _ _).symm).toOpenPartialHomeomorph, by simp,
    fun _ _ ↦ Subsingleton.elim _ _⟩

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
  continuous_footprintMap _ _ := continuous_powFootprintMap hm
  footprintMap_act _ _ _ _ _ _ := by ext; simp [powFootprintMap]
  footprintMap_self _ _ := rfl
  footprintMap_footprintMap _ _ _ _ _ _ _ _ := rfl
  kuranishi_footprintMap _ _ _ _ _ := rfl
  isOpen_range_footprintMap _ _ := isOpen_range_powFootprintMap hm
  range_footprintMap_inter _ _ _ _ _ := by simp only [range_powFootprintMap, inter_self]
  footprintMap_mem_range_iff _ _ _ _ _ _ := by simp only [range_powFootprintMap, mem_univ]
  isQuotientMap_footprintMap _ _ := isQuotientMap_powFootprintMap hm
  footprintMap_eq_footprintMap_iff _ _ _ x y := by
    simp only [powFootprintMap, Subtype.mk.injEq, MonoidHom.one_apply, Homeomorph.one_apply]
    exact ⟨fun h ↦ ⟨1, Subsingleton.elim _ _, Subtype.ext h⟩, fun ⟨_, _, h⟩ ↦ congrArg _ h⟩
  mem_regLocus_of_footprintMap_mem _ _ h _ hx := Finset.Nonempty.mono h hx
  eq_one_of_act_eq _ _ _ _ _ _ _ _ := Subsingleton.elim _ _
  exists_openPartialHomeomorph _ _ h x hx := exists_powChart h hx x.val _
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
  footprint_eq_empty_of_regLocus_eq_empty _ (regLocus_powAtlas_empty hm)

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.powAtlas` is the whole point. -/
@[simp]
theorem footprint_powAtlas_singleton (hm : m ≠ 0) : (powAtlas hm).footprint {()} = univ :=
  eq_univ_of_forall fun y ↦ (powAtlas hm).mem_footprint.2
    ⟨powSection hm (Finset.empty_subset _) y, Finset.singleton_nonempty _,
      powFootprintMap_powSection hm _ y⟩

/-! #### Deformation spaces -/

/-- For the atlas `s(x) = xᵐ` on a point, whose `X_∅^reg` is empty, the deformation space
`D_(∅,α,α)` is empty. -/
theorem deformationSpace_powAtlas_empty (hm : m ≠ 0) :
    (powAtlas hm).deformationSpace ∅ (subset_refl (Finset.univ : Finset Unit)) = ∅ :=
  deformationSpace_eq_empty fun S hS ↦ by
    rw [Finset.subset_empty.1 hS, regLocus_powAtlas_empty]

/-- For the atlas `s(x) = xᵐ` on a point, the deformation space `D_(α,α,α)` is
`{(e, t, x) | t > 0, xᵐ = t e}`. The points with `t = 0` are missing because `X_∅^reg = ∅`. -/
theorem mem_deformationSpace_powAtlas_iff (hm : m ≠ 0)
    {p : ((α : (Finset.univ : Finset Unit)) → ℝ) × (↥(Finset.univ : Finset Unit) → ℝ) ×
      PowThickening Finset.univ} :
    p ∈ (powAtlas hm).deformationSpace Finset.univ (subset_refl (Finset.univ : Finset Unit)) ↔
      0 < p.2.1 ⟨(), Finset.mem_univ _⟩ ∧
        (p.2.2 : ℝ) ^ m = p.2.1 ⟨(), Finset.mem_univ _⟩ * p.1 ⟨(), Finset.mem_univ _⟩ := by
  rw [mem_deformationSpace]
  constructor
  · rintro ⟨-, -, hs, h, hx, hreg⟩
    refine ⟨?_, by simpa using hs ⟨(), Finset.mem_univ _⟩⟩
    rw [regLocus_powAtlas] at hreg
    obtain ⟨α, hα⟩ := hreg
    exact (mem_positiveIndices.1 hα).2
  · rintro ⟨hpos, hs⟩
    have hT : positiveIndices p.2.1 = Finset.univ :=
      Finset.eq_univ_of_forall fun _ ↦ mem_positiveIndices.2 ⟨Finset.mem_univ _, hpos⟩
    refine ⟨fun ⟨(), _⟩ ↦ hpos.le, fun α hα ↦ (hα (Finset.mem_univ _)).elim,
      fun ⟨(), _⟩ ↦ by simpa using hs, ?_⟩
    rw [hT]
    refine ⟨subset_refl _, mem_kuranishiZeroSet_self _ _, ?_⟩
    rw [regLocus_powAtlas]
    exact Finset.univ_nonempty

/-- For the atlas `s(x) = xᵐ` on a point, the support `Z_X ⊆ D_(α,α,α)` is the half-line
`x = 0`, `e = 0`, `t > 0`, which does not contain its endpoint `t = 0`. -/
theorem mem_deformationSupport_powAtlas_iff (hm : m ≠ 0)
    {p : (powAtlas hm).deformationSpace Finset.univ (subset_refl (Finset.univ : Finset Unit))} :
    p ∈ (powAtlas hm).deformationSupport Finset.univ (subset_refl (Finset.univ : Finset Unit))
        univ ↔
      (p.val.2.2 : ℝ) = 0 := by
  obtain ⟨hpos, hs⟩ := (mem_deformationSpace_powAtlas_iff hm).1 p.property
  rw [mem_deformationSupport]
  constructor
  · rintro ⟨he, -⟩
    rw [he, Pi.zero_apply, mul_zero] at hs
    exact (pow_eq_zero_iff hm).1 hs
  · intro hx
    rw [hx, zero_pow hm] at hs
    have he : p.val.1 = 0 := funext fun ⟨(), _⟩ ↦
      (mul_eq_zero.1 hs.symm).resolve_left hpos.ne'
    exact ⟨he, mem_kuranishiZeroSet_empty_of_eq_zero p.property he, mem_univ _⟩


end Pow

/-! ### The reflection atlas `s(x) = xᵐ`, `m` even -/

section Reflection

/-- Multiplication by a unit `u = ±1` of `ℤ`, as a homeomorphism of the thickening
`PowThickening I`: the restriction of `Homeomorph.smul u`. -/
private def unitsMulHomeomorph (I : Finset Unit) (u : ℤˣ) : PowThickening I ≃ₜ PowThickening I :=
  (Homeomorph.smul u : ℝ ≃ₜ ℝ).subtype fun x ↦ by simp [Units.smul_def]

/-- The action of `ℤˣ` on the thickening `PowThickening I` by multiplication. -/
private def unitsMulHom (I : Finset Unit) : ℤˣ →* (PowThickening I ≃ₜ PowThickening I) where
  toFun := unitsMulHomeomorph I
  map_one' := Homeomorph.ext fun x ↦ Subtype.ext (one_smul ℤˣ x.val)
  map_mul' u v := Homeomorph.ext fun x ↦ Subtype.ext (mul_smul u v x.val)

/-- The action of `Γ_I = ∏_(α ∈ I) ℤˣ` on the thickenings `PowThickening I` of
`TauCeti.ImplicitAtlas.reflectionAtlas`: for `I = {α}` the element `g` acts on `X_α = ℝ` by the
reflection `x ↦ g_α x`, and for `I = ∅` the group is trivial. -/
noncomputable def reflectionAct (I : Finset Unit) :
    ((α : I) → ℤˣ) →* (PowThickening I ≃ₜ PowThickening I) :=
  if h : () ∈ I then (unitsMulHom I).comp (Pi.evalMonoidHom (fun _ : I ↦ ℤˣ) ⟨(), h⟩) else 1

/-- On `X_α = ℝ`, the element `g ∈ Γ_α = ℤˣ` acts by multiplication by `g_α = ±1`. -/
@[simp]
theorem coe_reflectionAct_apply {I : Finset Unit} (h : () ∈ I) (g : (α : I) → ℤˣ)
    (x : PowThickening I) : (reflectionAct I g x : ℝ) = ((g ⟨(), h⟩ : ℤ) : ℝ) * x := by
  simp [reflectionAct, h, unitsMulHom, unitsMulHomeomorph, Units.smul_def]

/-- The group `Γ_∅` acts trivially on the point `X_∅`. -/
theorem reflectionAct_of_notMem {I : Finset Unit} (h : () ∉ I) : reflectionAct I = 1 := by
  simp [reflectionAct, h]

/-- The reflection `x ↦ -x` of `X_α = ℝ` fixes the origin, so `Γ_α` does not act freely on
`X_α`. -/
theorem reflectionAct_neg_one_zero {I : Finset Unit} (h : () ∈ I) :
    reflectionAct I (-1) ⟨0, fun _ ↦ rfl⟩ = ⟨0, fun _ ↦ rfl⟩ :=
  Subtype.ext <| by simp [h]

variable {m : ℕ}

/-- For even `m`, the power `xᵐ` is invariant under the reflections `x ↦ ±x`. -/
private theorem pow_units_mul (hm : Even m) (u : ℤˣ) (x : ℝ) : (((u : ℤ) : ℝ) * x) ^ m = x ^ m := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [hm.neg_pow]

/-- **The reflection atlas.** The implicit atlas of virtual dimension `0` on the point `X = {0}`
with one index `α`, isotropy group `Γ_α = ℤˣ ≅ ℤ/2` acting on the thickening `X_α = ℝ` by the
reflection `x ↦ -x` and trivially on the obstruction space `E_α = ℝ`, and Kuranishi map
`s_α(x) = xᵐ` for an even `m ≠ 0`, invariant under the reflection. The regular locus of
`X_∅ = X` is empty and `X_α` is regular. The zero set `Z_∅α = {0}` is fixed by the reflection,
so `Γ_α` does not act freely on it, which the atlas allows since `ψ_∅α⁻¹(X_∅^reg)` is empty; its
quotient `Z_∅α / Γ_α = {0}` is `X`, and the footprint `V_α = X` covers. The reflection reverses
the orientation of `X_α` and fixes that of `E_α`. -/
noncomputable def reflectionAtlas (hm : Even m) (hm₀ : m ≠ 0) :
    ImplicitAtlas (fun _ : Unit ↦ ℤˣ) (fun _ ↦ ℝ) (fun _ ↦ Representation.trivial ℝ ℤˣ ℝ)
      PowThickening reflectionAct (PowThickening ∅) 0 where
  baseHomeomorph := Homeomorph.refl _
  kuranishi := powKuranishi m
  continuous_kuranishi _ _ := continuous_subtypeVal.pow m
  kuranishi_act _ α g x := by
    simp [coe_reflectionAct_apply (Subsingleton.elim α.val () ▸ α.property), pow_units_mul hm]
  regLocus I := {_x | I.Nonempty}
  isOpen_regLocus _ := isOpen_const
  act_mem_regLocus _ _ _ h := h
  footprintMap _ _ := powFootprintMap hm₀
  continuous_footprintMap _ _ := continuous_powFootprintMap hm₀
  footprintMap_act I J h g x hx := by
    by_cases hI : () ∈ I
    · exact Subtype.ext <| by simp [powFootprintMap, hI, h hI, Finset.restrict₂]
    · obtain rfl := eq_empty_of_notMem hI
      exact Subsingleton.elim _ _
  footprintMap_self _ _ := rfl
  footprintMap_footprintMap _ _ _ _ _ _ _ _ := rfl
  kuranishi_footprintMap _ _ _ _ _ := rfl
  isOpen_range_footprintMap _ _ := isOpen_range_powFootprintMap hm₀
  range_footprintMap_inter _ _ _ _ _ := by simp only [range_powFootprintMap, inter_self]
  footprintMap_mem_range_iff _ _ _ _ _ _ := by simp only [range_powFootprintMap, mem_univ]
  isQuotientMap_footprintMap _ _ := isQuotientMap_powFootprintMap hm₀
  footprintMap_eq_footprintMap_iff I J h x y := by
    refine ⟨fun hxy ↦ ⟨1, rfl, by simpa [powFootprintMap, Subtype.ext_iff] using hxy⟩, ?_⟩
    rintro ⟨g, hg, hxy⟩
    by_cases hI : I.Nonempty
    · rw [eq_one_of_restrict₂_eq_one h hI hg, map_one, Homeomorph.one_apply] at hxy
      simp [powFootprintMap, hxy]
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.1 hI
      exact Subsingleton.elim _ _
  mem_regLocus_of_footprintMap_mem _ _ h _ hx := Finset.Nonempty.mono h hx
  eq_one_of_act_eq _ _ h _ hx _ hg _ := eq_one_of_restrict₂_eq_one h hx hg
  exists_openPartialHomeomorph _ _ h x hx := exists_powChart h hx x.val _
  exists_footprintMap_eq y :=
    ⟨Finset.univ, powSection hm₀ (Finset.empty_subset _) y, Finset.univ_nonempty, rfl⟩

/-- The regular locus of `X_I` in `TauCeti.ImplicitAtlas.reflectionAtlas` is everything for
`I = {α}` and empty for `I = ∅`. -/
theorem regLocus_reflectionAtlas (hm : Even m) (hm₀ : m ≠ 0) (I : Finset Unit) :
    (reflectionAtlas hm hm₀).regLocus I = {_x | I.Nonempty} :=
  (rfl)

/-- The regular locus of `X_∅` in `TauCeti.ImplicitAtlas.reflectionAtlas` is empty. -/
@[simp]
theorem regLocus_reflectionAtlas_empty (hm : Even m) (hm₀ : m ≠ 0) :
    (reflectionAtlas hm hm₀).regLocus ∅ = ∅ := by
  simp [regLocus_reflectionAtlas]

/-- The Kuranishi map of `TauCeti.ImplicitAtlas.reflectionAtlas` is `s_α(x) = xᵐ`. -/
@[simp]
theorem kuranishi_reflectionAtlas (hm : Even m) (hm₀ : m ≠ 0) :
    (reflectionAtlas hm hm₀).kuranishi = powKuranishi m :=
  (rfl)

/-- The footprint maps of `TauCeti.ImplicitAtlas.reflectionAtlas` keep the real coordinate. -/
@[simp]
theorem coe_footprintMap_reflectionAtlas (hm : Even m) (hm₀ : m ≠ 0) {I J : Finset Unit}
    (h : I ⊆ J)
    (x : kuranishiZeroSet (E := fun _ : Unit ↦ ℝ) (reflectionAtlas hm hm₀).kuranishi I J) :
    ((reflectionAtlas hm hm₀).footprintMap h x : ℝ) = ((x : PowThickening J) : ℝ) :=
  (rfl)

/-- The footprint `V_∅` of `TauCeti.ImplicitAtlas.reflectionAtlas` is empty, since the regular
locus of `X_∅` is. -/
@[simp]
theorem footprint_reflectionAtlas_empty (hm : Even m) (hm₀ : m ≠ 0) :
    (reflectionAtlas hm hm₀).footprint ∅ = ∅ :=
  footprint_eq_empty_of_regLocus_eq_empty _ (regLocus_reflectionAtlas_empty hm hm₀)

/-- The footprint `V_α` of `TauCeti.ImplicitAtlas.reflectionAtlas` is the whole point. -/
@[simp]
theorem footprint_reflectionAtlas_singleton (hm : Even m) (hm₀ : m ≠ 0) :
    (reflectionAtlas hm hm₀).footprint {()} = univ :=
  eq_univ_of_forall fun y ↦ (reflectionAtlas hm hm₀).mem_footprint.2
    ⟨powSection hm₀ (Finset.empty_subset _) y, Finset.singleton_nonempty _,
      powFootprintMap_powSection hm₀ _ y⟩

end Reflection

end TauCeti.ImplicitAtlas
