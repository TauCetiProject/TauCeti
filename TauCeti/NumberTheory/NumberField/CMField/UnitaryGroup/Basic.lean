/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralGL
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The finite adelic unitary group of a CM field and its levels

Let `E` be a CM field with complex conjugation `x ↦ conj x`, `𝔸_f` its finite adeles with the
conjugation carrying the component at a finite place `w` to the component at the conjugate place
`conj w` (`NumberField.IsCMField.finiteAdeleConj`), and `Ô ⊆ 𝔸_f` the integral finite adeles.
For a finite index set `ι` (of size `n`), this file defines the **finite adelic unitary group**
`G_f = U(1_n)(𝔸_f) = {g ∈ GL_n(𝔸_f) : g* g = 1}`, where `g* = (conj g)ᵀ` is the conjugate transpose,
with the subspace topology of `GL_n(𝔸_f)`; it is the group `Matrix.unitaryGroupOf 1` of
Tau Ceti's general theory of unitary groups, so its API applies. Then:

* The component `g_w ∈ GL_n(E_w)` of `g ∈ G_f` at a finite place `w` is a group homomorphism
  `TauCeti.finiteAdelicUnitaryGroup.proj`.
* `K₀ = G_f ∩ GL_n(Ô)`, the intersection of `G_f` with the image of
  `IsDedekindDomain.FiniteAdeleRing.integralGL`, is the subgroup of unitary matrices with integral
  entries: the inverse `g⁻¹ = g*` of such a matrix is integral as well, since conjugation preserves
  `Ô`. Equivalently, `K₀` consists of the `g` whose component `g_w` lies in `GL_n(𝒪_w)` at every
  finite place `w`.
* `K₀` is open in `G_f`, as `GL_n(Ô)` is open in `GL_n(𝔸_f)`
  (`IsDedekindDomain.FiniteAdeleRing.isOpenEmbedding_integralGL`), and compact; so `G_f` is
  locally compact.
* A **level** is an open subgroup `K` of `G_f` contained in `K₀`. A level is compact, of finite
  index in `K₀`, and the levels are stable under finite intersections.
* At a finite place `w` and its conjugate place `conj w`
  (`IsDedekindDomain.HeightOneSpectrum.conjPlace`), the components of `g ∈ G_f` determine each
  other: `g_{conj w}` is the conjugate of the transpose of
  `(g_w)⁻¹`, read through the isomorphism `E_w ≃ E_{conj w}` extending the conjugation of `E`. At
  a finite place split in `E / E⁺` these are two different places.

The levels index the spaces of automorphic forms on unitary groups over `E` and their Hecke
operators; `G_f` is the finite component of the adelic unitary groups of hermitian spaces with
an adelic frame (`TauCeti.FramedHermitianSpace`).

## Main definitions

* `TauCeti.finiteAdelicUnitaryGroup E ι`: the group `G_f`.
* `TauCeti.finiteAdelicUnitaryGroup.proj E ι w`: the component `G_f → GL_n(E_w)` at a finite
  place `w`.
* `TauCeti.integralAdelicUnitaryGroup E ι`: its subgroup `K₀ = G_f ∩ GL_n(Ô)`.
* `TauCeti.IsUnitaryLevel K`: `K` is a level, an open subgroup of `G_f` contained in `K₀`.

## Main results

* `TauCeti.mem_finiteAdelicUnitaryGroup_iff`, `TauCeti.val_inv_of_mem_finiteAdelicUnitaryGroup`:
  `g ∈ G_f` means `g* g = 1`, and then `g⁻¹ = g*`.
* `TauCeti.finiteAdelicUnitaryGroup.proj_conjPlace_apply`: the components of `g ∈ G_f` at a
  finite place and at its conjugate.
* `TauCeti.mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL`: `K₀ = G_f ∩ GL_n(Ô)`;
  `TauCeti.mem_integralAdelicUnitaryGroup_iff`: `K₀` is the set of `g ∈ G_f` with integral
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
open scoped NumberField.AdeleRing ComplexConjugate

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

variable (E ι) in
/-- The **component** `g ↦ g_w` of the finite adelic unitary group at a finite place `w`: the
homomorphism `G_f → GL_n(E_w)` reading each entry of `g` at `w`. -/
def finiteAdelicUnitaryGroup.proj (w : HeightOneSpectrum (𝓞 E)) :
    finiteAdelicUnitaryGroup E ι →* GL ι (w.adicCompletion E) :=
  (GeneralLinearGroup.map (FiniteAdeleRing.proj E w).toRingHom).comp
    (finiteAdelicUnitaryGroup E ι).subtype

/-- The entries of the component `g_w` are the components at `w` of the entries of `g`. -/
@[simp]
theorem finiteAdelicUnitaryGroup.proj_apply (w : HeightOneSpectrum (𝓞 E))
    (g : finiteAdelicUnitaryGroup E ι) (i j : ι) :
    (finiteAdelicUnitaryGroup.proj E ι w g : Matrix ι ι (w.adicCompletion E)) i j =
      ((g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j w := by
  simp only [finiteAdelicUnitaryGroup.proj, AlgHom.toRingHom_eq_coe, MonoidHom.coe_comp,
    Subgroup.coe_subtype, Function.comp_apply, GeneralLinearGroup.map_apply, RingHom.coe_coe,
    ContinuousAlgHom.coe_coe, FiniteAdeleRing.proj_apply]

/-- **Components at conjugate places.** For `g ∈ G_f` and a finite place `w` with conjugate
`conj w` (`conjPlace`), the entry `(i, j)` of the component `g_{conj w}` is the image of the entry
`(j, i)` of `(g_w)⁻¹` under the isomorphism `E_w ≃ E_{conj w}` extending the conjugation of `E`:
`g_{conj w}` is the conjugate of the transpose of `(g_w)⁻¹`. -/
theorem finiteAdelicUnitaryGroup.proj_conjPlace_apply (g : finiteAdelicUnitaryGroup E ι)
    (w : HeightOneSpectrum (𝓞 E)) (i j : ι) :
    (finiteAdelicUnitaryGroup.proj E ι w.conjPlace g : Matrix ι ι (w.conjPlace.adicCompletion E))
        i j =
      adicCompletionCongr w w.conjPlace (complexConj E).toRingEquiv (valuation_conjPlace w)
        ((↑(finiteAdelicUnitaryGroup.proj E ι w g)⁻¹ : Matrix ι ι (w.adicCompletion E)) j i) := by
  have h := val_inv_of_mem_finiteAdelicUnitaryGroup (inv_mem g.property)
  rw [inv_inv] at h
  rw [← map_inv, finiteAdelicUnitaryGroup.proj_apply, finiteAdelicUnitaryGroup.proj_apply,
    InvMemClass.coe_inv, h, star_apply, FiniteAdeleRing.star_apply_conjPlace]

/-! ### The integral subgroup `K₀` -/

variable (E ι) in
/-- The subgroup `K₀ = G_f ∩ GL_n(Ô)` of the finite adelic unitary group: the elements that are
integral matrices with integral inverse. As the inverse of `g ∈ G_f` is its conjugate transpose,
these are the elements with integral entries (`mem_integralAdelicUnitaryGroup_iff`), and the
elements whose component at every finite place `w` lies in `GL_n(𝒪_w)`
(`mem_integralAdelicUnitaryGroup_iff_forall_place`). -/
def integralAdelicUnitaryGroup : Subgroup (finiteAdelicUnitaryGroup E ι) :=
  (FiniteAdeleRing.integralGL E ι (R := 𝓞 E)).range.subgroupOf _

variable (E ι) in
/-- `K₀` is the trace on `G_f` of the image `GL_n(Ô)` of `integralGL`. -/
theorem integralAdelicUnitaryGroup_def :
    integralAdelicUnitaryGroup E ι =
      (FiniteAdeleRing.integralGL E ι (R := 𝓞 E)).range.subgroupOf _ :=
  (rfl)

/-- `K₀ = G_f ∩ GL_n(Ô)`: an element of `G_f` lies in `K₀` exactly when it lies in `GL_n(Ô)`. -/
theorem mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL
    {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ integralAdelicUnitaryGroup E ι ↔
      (g : GL ι 𝔸ᶠ[E]) ∈ (FiniteAdeleRing.integralGL E ι (R := 𝓞 E)).range := by
  rw [integralAdelicUnitaryGroup_def, Subgroup.mem_subgroupOf]

/-- `K₀` consists of the elements of `G_f` with integral entries. -/
theorem mem_integralAdelicUnitaryGroup_iff {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ integralAdelicUnitaryGroup E ι ↔
      ∀ i j,
        ((g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  rw [mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL,
    FiniteAdeleRing.mem_range_integralGL_iff]
  refine ⟨And.left, fun h ↦ ⟨h, fun i j ↦ ?_⟩⟩
  rw [val_inv_of_mem_finiteAdelicUnitaryGroup g.property, star_apply,
    star_mem_integralAdeles_iff]
  exact h j i

/-- **`K₀` is the group of elements integral at every place**: `g ∈ G_f` lies in `K₀` exactly when
at every finite place `w` its component `g_w` lies in `GL_n(𝒪_w)`, that is the entries of `g_w`
and of `(g_w)⁻¹` lie in the local integers `𝒪_w`. -/
theorem mem_integralAdelicUnitaryGroup_iff_forall_place {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ integralAdelicUnitaryGroup E ι ↔ ∀ w : HeightOneSpectrum (𝓞 E),
      (∀ i j, (finiteAdelicUnitaryGroup.proj E ι w g : Matrix ι ι (w.adicCompletion E)) i j ∈
        w.adicCompletionIntegers E) ∧
      ∀ i j, (↑(finiteAdelicUnitaryGroup.proj E ι w g)⁻¹ : Matrix ι ι (w.adicCompletion E)) i j ∈
        w.adicCompletionIntegers E := by
  simp only [← map_inv, finiteAdelicUnitaryGroup.proj_apply, InvMemClass.coe_inv]
  refine ⟨fun hg w ↦ ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩, fun h ↦ ?_⟩
  · exact FiniteAdeleRing.mem_integralAdeles.1 (mem_integralAdelicUnitaryGroup_iff.1 hg i j) w
  · exact FiniteAdeleRing.mem_integralAdeles.1
      (mem_integralAdelicUnitaryGroup_iff.1 (inv_mem hg) i j) w
  · exact mem_integralAdelicUnitaryGroup_iff.2 fun i j ↦
      FiniteAdeleRing.mem_integralAdeles.2 fun w ↦ (h w).1 i j

variable (E ι) in
/-- `K₀` is open in `G_f`: it is the preimage of `GL_n(Ô)`, which is open in `GL_n(𝔸_f)`. -/
theorem isOpen_integralAdelicUnitaryGroup :
    IsOpen (integralAdelicUnitaryGroup E ι : Set (finiteAdelicUnitaryGroup E ι)) :=
  (FiniteAdeleRing.isOpenEmbedding_integralGL E ι).isOpen_range.preimage continuous_subtypeVal

variable (E ι) in
/-- `K₀` is compact: `G_f` is a closed subset of the matrices, and `K₀` is its intersection with
the compact set `M_n(Ô)`. -/
theorem isCompact_integralAdelicUnitaryGroup :
    IsCompact (integralAdelicUnitaryGroup E ι : Set (finiteAdelicUnitaryGroup E ι)) := by
  have hM := (FiniteAdeleRing.isCompact_integralAdeles (R := 𝓞 E) (K := E)).matrix (m := ι) (n := ι)
  convert (unitaryGroupOf.isClosedEmbedding_val (A := (1 : Matrix ι ι 𝔸ᶠ[E]))
    isUnit_one).isCompact_preimage hM using 1
  ext g
  rw [Set.mem_preimage, Set.mem_matrix]
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
