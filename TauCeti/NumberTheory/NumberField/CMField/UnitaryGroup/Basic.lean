/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subalgebra
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The finite adelic unitary group of a CM field and its levels

Let `E` be a CM field with complex conjugation `x ↦ conj x`, `𝔸_f` its finite adeles with the
conjugation acting componentwise through the places (`NumberField.IsCMField.finiteAdeleConj`), and
`Ô ⊆ 𝔸_f` the integral finite adeles. For a finite index set `ι` (of size `n`), this file
defines the **finite adelic unitary group**
`G_f = U(1_n)(𝔸_f) = {g ∈ GL_n(𝔸_f) : g* g = 1}`, where `g* = (conj g)ᵀ` is the conjugate transpose,
with the subspace topology of `GL_n(𝔸_f)`; it is the group `Matrix.unitaryGroupOf 1` of
Tau Ceti's general theory of unitary groups, so its API applies. Then:

* `K₀ = G_f ∩ GL_n(Ô)` is the subgroup of unitary matrices with integral entries: the inverse
  `g⁻¹ = g*` of such a matrix is integral as well, since conjugation preserves `Ô`. Equivalently,
  `K₀` consists of the `g` whose component `g_w` lies in `GL_n(𝒪_w)` at every finite place `w`.
* `K₀` is open and compact in `G_f`; so `G_f` is locally compact.
* A **level** is an open subgroup `K` of `G_f` contained in `K₀`. A level is compact, of finite
  index in `K₀`, and the levels are stable under finite intersections.
* At a finite place `w` and its conjugate place `conj w`, the components of `g ∈ G_f` determine each
  other: `g_{conj w}` is the conjugate of the transpose of `(g_w)⁻¹`, read through the isomorphism
  `E_w ≃ E_{conj w}` extending the conjugation of `E`.

The levels index the spaces of automorphic forms on unitary groups over `E` and their Hecke
operators; `G_f` is the finite component of the adelic unitary groups of hermitian spaces with
an adelic frame (`TauCeti.FramedHermitianSpace`).

## Main definitions

* `TauCeti.finiteAdelicUnitaryGroup E ι`: the group `G_f`.
* `TauCeti.integralAdelicUnitaryGroup E ι`: its subgroup `K₀ = G_f ∩ GL_n(Ô)`.
* `TauCeti.IsUnitaryLevel K`: `K` is a level, an open subgroup of `G_f` contained in `K₀`.

## Main results

* `TauCeti.mem_finiteAdelicUnitaryGroup_iff`, `TauCeti.val_inv_of_mem_finiteAdelicUnitaryGroup`:
  `g ∈ G_f` means `g* g = 1`, and then `g⁻¹ = g*`.
* `TauCeti.val_apply_apply_eq_adicCompletionCongr`: the components of `g ∈ G_f` at a finite
  place and at its conjugate.
* `TauCeti.mem_integralAdelicUnitaryGroup_iff`: `K₀` is the set of `g ∈ G_f` with integral
  entries, and `TauCeti.mem_integralAdelicUnitaryGroup_iff_forall_place`: the set of `g` with
  `g_w ∈ GL_n(𝒪_w)` at every finite place `w`.
* `TauCeti.isOpen_integralAdelicUnitaryGroup`, `TauCeti.isCompact_integralAdelicUnitaryGroup`:
  `K₀` is open and compact.
* `TauCeti.isUnitaryLevel_integralAdelicUnitaryGroup`: `K₀` is a level;
  `TauCeti.IsUnitaryLevel.isCompact`, `TauCeti.IsUnitaryLevel.relIndex_ne_zero`,
  `TauCeti.IsUnitaryLevel.inf`, `TauCeti.IsUnitaryLevel.mono`: levels are compact, of finite
  index in `K₀`, and stable under intersections and enlargement inside `K₀`.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§2, 4.
* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.

## Attribution

The objects defined here, `G_f`, `K₀` and the levels, and the relation between the components of
`g ∈ G_f` at a place and at its conjugate, are those of `New.Gf`, `New.stdLevel`, `New.IsLevel` and
`New.Gf.atPlace_star` in the files `src/Lib/Adelic/Unitary/Defs.lean` and
`src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] (ι : Type*) [Fintype ι]
  [DecidableEq ι]

/-! ### The finite adelic unitary group -/

/-- The **finite adelic unitary group** `G_f = U(1_n)(𝔸_f)` of a CM field `E`: the invertible
matrices `g` over the finite adeles of `E` with `g* g = 1`, where `g*` is the conjugate transpose
for the complex conjugation of the finite adeles. It is `Matrix.unitaryGroupOf 1`, so the general
API of unitary groups applies to it; it carries the subspace topology of `GL_n(𝔸_f)`. -/
abbrev finiteAdelicUnitaryGroup : Subgroup (GL ι 𝔸ᶠ[E]) :=
  unitaryGroupOf (1 : Matrix ι ι 𝔸ᶠ[E])

variable {E ι}

/-- Membership in `G_f` is the equation `g* g = 1`. -/
theorem mem_finiteAdelicUnitaryGroup_iff {g : GL ι 𝔸ᶠ[E]} :
    g ∈ finiteAdelicUnitaryGroup E ι ↔ star (g : Matrix ι ι 𝔸ᶠ[E]) * g = 1 := by
  rw [mem_unitaryGroupOf_iff, Matrix.mul_one]

/-- The inverse of an element of `G_f` is its conjugate transpose. -/
theorem val_inv_of_mem_finiteAdelicUnitaryGroup {g : GL ι 𝔸ᶠ[E]}
    (hg : g ∈ finiteAdelicUnitaryGroup E ι) :
    (↑g⁻¹ : Matrix ι ι 𝔸ᶠ[E]) = star (g : Matrix ι ι 𝔸ᶠ[E]) := by
  rw [val_inv_of_mem_unitaryGroupOf isUnit_one hg, inv_one, Matrix.one_mul, Matrix.mul_one]

/-- **Components at conjugate places.** Let `w'` be the conjugate of the finite place `w`, that
is `|conj x|_{w'} = |x|_w` for `x ∈ E` (it exists, `exists_valuation_complexConj_eq`). For
`g ∈ G_f`, the entry `(i, j)` of the component `g_{w'}` is the image of the entry `(j, i)` of
`(g⁻¹)_w = (g_w)⁻¹` under the isomorphism `E_w ≃ E_{w'}` extending the conjugation of `E`:
`g_{w'}` is the conjugate of the transpose of `(g_w)⁻¹`. -/
theorem val_apply_apply_eq_adicCompletionCongr {g : GL ι 𝔸ᶠ[E]}
    (hg : g ∈ finiteAdelicUnitaryGroup E ι) {w w' : HeightOneSpectrum (𝓞 E)}
    (hw : ∀ x : E, w'.valuation E (complexConj E x) = w.valuation E x) (i j : ι) :
    (g : Matrix ι ι 𝔸ᶠ[E]) i j w' =
      adicCompletionCongr w w' (complexConj E).toRingEquiv hw
        ((↑g⁻¹ : Matrix ι ι 𝔸ᶠ[E]) j i w) := by
  have h := val_inv_of_mem_finiteAdelicUnitaryGroup (inv_mem hg)
  rw [inv_inv] at h
  rw [h, star_apply, finiteAdeleRing_star_apply hw]

/-! ### The integral subgroup `K₀` -/

variable (E ι) in
/-- The subgroup `K₀ = G_f ∩ GL_n(Ô)` of the finite adelic unitary group: the elements that are
integral matrices with integral inverse. As the inverse of `g ∈ G_f` is its conjugate transpose,
these are the elements with integral entries (`mem_integralAdelicUnitaryGroup_iff`), and the
elements whose component at every finite place `w` lies in `GL_n(𝒪_w)`
(`mem_integralAdelicUnitaryGroup_iff_forall_place`). -/
def integralAdelicUnitaryGroup : Subgroup (finiteAdelicUnitaryGroup E ι) :=
  (GeneralLinearGroup.map ((FiniteAdeleRing.integralAdeles (𝓞 E) E).val :
    FiniteAdeleRing.integralAdeles (𝓞 E) E →+* 𝔸ᶠ[E])).range.subgroupOf _

/-- `K₀` consists of the elements of `G_f` with integral entries. -/
theorem mem_integralAdelicUnitaryGroup_iff {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ integralAdelicUnitaryGroup E ι ↔
      ∀ i j,
        ((g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  rw [integralAdelicUnitaryGroup, Subgroup.mem_subgroupOf, MonoidHom.mem_range,
    GeneralLinearGroup.mem_range_map_val_iff]
  refine ⟨And.left, fun h ↦ ⟨h, fun i j ↦ ?_⟩⟩
  rw [val_inv_of_mem_finiteAdelicUnitaryGroup g.property, star_apply,
    star_mem_integralAdeles_iff]
  exact h j i

/-- **`K₀` is the group of elements integral at every place**: `g ∈ G_f` lies in `K₀` exactly when
at every finite place `w` its component `g_w` lies in `GL_n(𝒪_w)`, that is the entries of `g_w`
and of `(g_w)⁻¹ = (g⁻¹)_w` lie in the local integers `𝒪_w`. -/
theorem mem_integralAdelicUnitaryGroup_iff_forall_place {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ integralAdelicUnitaryGroup E ι ↔ ∀ w : HeightOneSpectrum (𝓞 E),
      (∀ i j, ((g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j w ∈ w.adicCompletionIntegers E) ∧
        ∀ i j, ((g⁻¹ : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j w ∈ w.adicCompletionIntegers E := by
  refine ⟨fun hg w ↦ ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩, fun h ↦ ?_⟩
  · exact FiniteAdeleRing.mem_integralAdeles.1 (mem_integralAdelicUnitaryGroup_iff.1 hg i j) w
  · exact FiniteAdeleRing.mem_integralAdeles.1
      (mem_integralAdelicUnitaryGroup_iff.1 (inv_mem hg) i j) w
  · exact mem_integralAdelicUnitaryGroup_iff.2 fun i j ↦
      FiniteAdeleRing.mem_integralAdeles.2 fun w ↦ (h w).1 i j

/-- The entry `(i, j)` of an element of `G_f`, as a continuous function on `G_f`. -/
private theorem continuous_val_apply (i j : ι) :
    Continuous fun g : finiteAdelicUnitaryGroup E ι ↦ ((g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j :=
  (Units.continuous_val.comp continuous_subtypeVal).matrix_elem i j

/-- `K₀` as the set of elements of `G_f` with integral entries. -/
private theorem coe_integralAdelicUnitaryGroup :
    (integralAdelicUnitaryGroup E ι : Set (finiteAdelicUnitaryGroup E ι)) =
      ⋂ i, ⋂ j, (fun g : finiteAdelicUnitaryGroup E ι ↦
        ((g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j) ⁻¹'
          (FiniteAdeleRing.integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E]) := by
  ext g
  simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
  exact mem_integralAdelicUnitaryGroup_iff

variable (E ι) in
/-- `K₀` is open in `G_f`: integrality of the entries is an open condition, `Ô` being open in
`𝔸_f`. -/
theorem isOpen_integralAdelicUnitaryGroup :
    IsOpen (integralAdelicUnitaryGroup E ι : Set (finiteAdelicUnitaryGroup E ι)) := by
  rw [coe_integralAdelicUnitaryGroup]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
    (FiniteAdeleRing.isOpen_integralAdeles (𝓞 E) E).preimage (continuous_val_apply i j)

variable (E ι) in
/-- `K₀` is compact: `G_f` is a closed subset of the matrices, and `K₀` is its intersection with
the compact set `M_n(Ô)`. -/
theorem isCompact_integralAdelicUnitaryGroup :
    IsCompact (integralAdelicUnitaryGroup E ι : Set (finiteAdelicUnitaryGroup E ι)) := by
  have hM : IsCompact
      {M : Matrix ι ι 𝔸ᶠ[E] | ∀ i j, M i j ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E} := by
    exact isCompact_pi_infinite fun _ ↦ isCompact_pi_infinite fun _ ↦
      FiniteAdeleRing.isCompact_integralAdeles (R := 𝓞 E) (K := E)
  convert (unitaryGroupOf.isClosedEmbedding_val (A := (1 : Matrix ι ι 𝔸ᶠ[E]))
    isUnit_one).isCompact_preimage hM using 1
  ext g
  exact mem_integralAdelicUnitaryGroup_iff

instance : CompactSpace (integralAdelicUnitaryGroup E ι) :=
  isCompact_iff_compactSpace.mp (isCompact_integralAdelicUnitaryGroup E ι)

/-- The finite adelic unitary group is locally compact, as its subgroup `K₀` is a compact
neighbourhood of `1`. -/
instance : LocallyCompactSpace (finiteAdelicUnitaryGroup E ι) :=
  (isCompact_integralAdelicUnitaryGroup E ι).locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_integralAdelicUnitaryGroup E ι).mem_nhds (one_mem _))

/-! ### Levels -/

/-- A **level** of the finite adelic unitary group `G_f` of a CM field: an open subgroup `K` of
`G_f` contained in `K₀ = G_f ∩ GL_n(Ô)`. -/
structure IsUnitaryLevel (K : Subgroup (finiteAdelicUnitaryGroup E ι)) : Prop where
  /-- A level is contained in `K₀`. -/
  le_integralAdelicUnitaryGroup : K ≤ integralAdelicUnitaryGroup E ι
  /-- A level is open in `G_f`. -/
  isOpen : IsOpen (K : Set (finiteAdelicUnitaryGroup E ι))

variable (E ι) in
/-- `K₀` is a level, the largest one. -/
theorem isUnitaryLevel_integralAdelicUnitaryGroup :
    IsUnitaryLevel (integralAdelicUnitaryGroup E ι) :=
  ⟨le_rfl, isOpen_integralAdelicUnitaryGroup E ι⟩

namespace IsUnitaryLevel

variable {K K' : Subgroup (finiteAdelicUnitaryGroup E ι)}

/-- A level is closed in `G_f`, as an open subgroup. -/
theorem isClosed (hK : IsUnitaryLevel K) : IsClosed (K : Set (finiteAdelicUnitaryGroup E ι)) :=
  K.isClosed_of_isOpen hK.isOpen

/-- A level is compact, as a closed subset of the compact group `K₀`. -/
theorem isCompact (hK : IsUnitaryLevel K) : IsCompact (K : Set (finiteAdelicUnitaryGroup E ι)) :=
  (isCompact_integralAdelicUnitaryGroup E ι).of_isClosed_subset hK.isClosed
    hK.le_integralAdelicUnitaryGroup

/-- A level has finite index in `K₀`: it is an open subgroup of a compact group. -/
theorem relIndex_ne_zero (hK : IsUnitaryLevel K) :
    K.relIndex (integralAdelicUnitaryGroup E ι) ≠ 0 := by
  have := Subgroup.quotient_finite_of_isOpen _
    (Subgroup.subgroupOf_isOpen (integralAdelicUnitaryGroup E ι) K hK.isOpen)
  exact Subgroup.index_ne_zero_of_finite

/-- The intersection of two levels is a level. -/
theorem inf (hK : IsUnitaryLevel K) (hK' : IsUnitaryLevel K') : IsUnitaryLevel (K ⊓ K') :=
  ⟨inf_le_left.trans hK.le_integralAdelicUnitaryGroup, hK.isOpen.inter hK'.isOpen⟩

/-- A subgroup of `K₀` containing a level is a level. -/
theorem mono (hK : IsUnitaryLevel K) (hKK' : K ≤ K') (hK' : K' ≤ integralAdelicUnitaryGroup E ι) :
    IsUnitaryLevel K' :=
  ⟨hK', Subgroup.isOpen_mono hKK' hK.isOpen⟩

end IsUnitaryLevel

end TauCeti
