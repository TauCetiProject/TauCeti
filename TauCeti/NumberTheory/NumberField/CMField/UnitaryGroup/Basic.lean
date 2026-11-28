/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralGL
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The adelic unitary groups of a CM field and their levels

Let `E` be a CM field with complex conjugation `x ↦ conj x`, `E_∞ = ∏_w E_w` its infinite adeles,
`𝔸_f` its finite adeles, with the conjugation transported to both
(`NumberField.IsCMField.infiniteAdeleConj`, `NumberField.IsCMField.finiteAdeleConj`), and
`Ô ⊆ 𝔸_f` the integral finite adeles. For a finite index set `ι` (of size `n`), this file defines
the **finite adelic unitary group** `G_f = U(1_n)(𝔸_f) = {g ∈ GL_n(𝔸_f) : g* g = 1}`, where
`g* = (conj g)ᵀ` is the conjugate transpose, with the subspace topology of `GL_n(𝔸_f)`; it is
Mathlib's unitary subgroup `unitarySubgroup (GL ι 𝔸ᶠ[E])`, which is `Matrix.unitaryGroupOf 1`
(`Matrix.unitaryGroupOf_one`). Then:

* The component `g_w ∈ GL_n(E_w)` of `g ∈ G_f` at a finite place `w` is a continuous group
  homomorphism `TauCeti.finiteAdelicUnitaryGroup.proj`.
* `K₀ = G_f ∩ GL_n(Ô)`, the intersection of `G_f` with the image of
  `IsDedekindDomain.FiniteAdeleRing.integralGL`, is the subgroup of unitary matrices with integral
  entries: the inverse `g⁻¹ = g*` of such a matrix is integral as well, since conjugation preserves
  `Ô`. Equivalently, `K₀` consists of the `g` whose component `g_w` lies in `GL_n(𝒪_w)` at every
  finite place `w`, and `integralGL` identifies the unitary subgroup of `GL_n(Ô)` with `K₀`.
* `K₀` is open in `G_f`, as `GL_n(Ô)` is open in `GL_n(𝔸_f)`
  (`IsDedekindDomain.FiniteAdeleRing.isOpenEmbedding_integralGL`), and compact; so `G_f` is
  locally compact.
* A **level** is an open subgroup `K` of `G_f` contained in `K₀`. A level is compact, of finite
  index in `K₀`, and the levels are stable under finite intersections.
* At a finite place `w` and its conjugate place `conj w`
  (`IsDedekindDomain.HeightOneSpectrum.conjPlace`), the components of `g ∈ G_f` determine each
  other: `g_{conj w}` is the inverse transpose of the image of `g_w` under the isomorphism
  `E_w ≃ E_{conj w}` extending the conjugation of `E`. When `conj w ≠ w`, that is when the place
  of `E⁺` below `w` splits in `E`, these are components at two different places.

For a sign vector `s ∈ {±1}^ι`, used at every infinite place, the **archimedean adelic unitary
group** is `G_∞(s) = U(diag s)(E_∞)`, which only needs `E` to be an algebraic CM field, and the
**adelic unitary group** is `G(s) = G_∞(s) × G_f ⊆ GL_n(E_∞) × GL_n(𝔸_f)` (Mathlib's
`Matrix.GeneralLinearGroup.prodEquiv` identifies `GL_n(E_∞) × GL_n(𝔸_f)` with `GL_n(𝔸)`). Its
elements are the pairs of matrices preserving the forms `diag(s)` and `1_n`.

The levels index the spaces of automorphic forms on unitary groups over `E` and their Hecke
operators; `G(s)` acts on the hermitian spaces with an adelic frame
(`TauCeti.FramedHermitianSpace`).

## Main definitions

* `TauCeti.finiteAdelicUnitaryGroup E ι`: the group `G_f`.
* `TauCeti.finiteAdelicUnitaryGroup.proj E ι w`: the component `G_f → GL_n(E_w)` at a finite
  place `w`.
* `TauCeti.integralAdelicUnitaryGroup E ι`: its subgroup `K₀ = G_f ∩ GL_n(Ô)`, and
  `TauCeti.integralAdelicUnitaryGroupEquiv E ι`: the isomorphism from the unitary subgroup of
  `GL_n(Ô)` onto `K₀` induced by `integralGL`.
* `TauCeti.IsUnitaryLevel K`: `K` is a level, an open subgroup of `G_f` contained in `K₀`.
* `TauCeti.infiniteAdelicUnitaryGroup E s`, `TauCeti.adelicUnitaryGroup E s`: `G_∞(s)` and
  `G(s)`, with the finite component `TauCeti.adelicUnitaryGroup.finitePart : G(s) → G_f`, the
  embedding `TauCeti.adelicUnitaryGroup.ofFinite : G_f → G(s)`, `g ↦ (1, g)`, their archimedean
  counterparts `TauCeti.adelicUnitaryGroup.infinitePart : G(s) → G_∞(s)` and
  `TauCeti.adelicUnitaryGroup.ofInfinite : G_∞(s) → G(s)`, `g ↦ (g, 1)`, and the element
  `TauCeti.adelicUnitaryGroup.ofMatrix` of `G(s)` defined by a pair of matrices preserving the
  forms.

## Main results

* `TauCeti.finiteAdelicUnitaryGroup.proj_conjPlace`: the components of `g ∈ G_f` at a finite
  place and at its conjugate.
* `TauCeti.finiteAdelicUnitaryGroup.ext_proj`: an element of `G_f` is determined by its
  components at the finite places.
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
* `TauCeti.exists_mem_adelicUnitaryGroup_iff`: an adelic matrix lies in `G(s)` exactly when it
  preserves the form `diag(s)` at the infinite places and `1_n` at the finite places.
* `TauCeti.finiteAdelicUnitaryGroup.continuous_proj`,
  `TauCeti.adelicUnitaryGroup.continuous_finitePart`,
  `TauCeti.adelicUnitaryGroup.continuous_ofFinite`,
  `TauCeti.adelicUnitaryGroup.continuous_infinitePart`,
  `TauCeti.adelicUnitaryGroup.continuous_ofInfinite`: the component maps are continuous.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§2, 4.
* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.

## Attribution

The objects defined here, `G_f`, `K₀`, the levels, `G_∞(s)` and `G(s)`, the relation between the
components of `g ∈ G_f` at a place and at its conjugate, and the statement on the elements of
`G(s)`, are those of `New.Gf`, `New.stdLevel`, `New.IsLevel`, `New.GInf`, `New.G`,
`New.Gf.atPlace_star` and `New.G.ofMatrix` in the files `src/Lib/Adelic/Unitary/Defs.lean`,
`src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` and `src/Lib/Adelic/Unitary/GramMatrix.lean`
of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing ComplexConjugate

namespace TauCeti

section FiniteAdelicUnitaryGroup

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] (ι : Type*) [Fintype ι]
  [DecidableEq ι]

/-! ### The finite adelic unitary group -/

/-- The **finite adelic unitary group** `G_f = U(1_n)(𝔸_f)` of a CM field `E`: the invertible
matrices `g` over the finite adeles of `E` with `g* g = 1`, where `g*` is the conjugate transpose
for the complex conjugation of the finite adeles. It is Mathlib's unitary subgroup of
`GL_n(𝔸_f)`, so that `TauCeti.mem_unitarySubgroup_GL_iff_mem_unitaryGroup` describes membership
and `TauCeti.coe_inv_eq_star_of_mem_unitarySubgroup` inverses, and it is the unitary group
`Matrix.unitaryGroupOf 1` of the identity form (`Matrix.unitaryGroupOf_one`). It carries the
subspace topology of `GL_n(𝔸_f)`. -/
abbrev finiteAdelicUnitaryGroup : Subgroup (GL ι 𝔸ᶠ[E]) :=
  unitarySubgroup (GL ι 𝔸ᶠ[E])

variable {E ι}

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

/-- The component `g ↦ g_w` at a finite place is continuous. -/
@[fun_prop]
theorem finiteAdelicUnitaryGroup.continuous_proj (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (finiteAdelicUnitaryGroup.proj E ι w) :=
  (Continuous.generalLinearGroup_map (FiniteAdeleRing.proj E w).continuous).comp
    continuous_subtypeVal

/-- The component of `g ∈ G_f` at a finite place `w` is the component of `g` read in
`GL_n(𝔸_f)`. -/
theorem finiteAdelicUnitaryGroup.proj_eq_map (w : HeightOneSpectrum (𝓞 E))
    (g : finiteAdelicUnitaryGroup E ι) :
    finiteAdelicUnitaryGroup.proj E ι w g =
      GeneralLinearGroup.map (FiniteAdeleRing.proj E w : _ →+* w.adicCompletion E)
        (g : GL ι 𝔸ᶠ[E]) :=
  GeneralLinearGroup.ext fun i j ↦ by
    simp only [finiteAdelicUnitaryGroup.proj_apply, GeneralLinearGroup.map_apply,
      RingHom.coe_coe, FiniteAdeleRing.proj_apply]

/-- **The adjoint of an adelic matrix at a conjugate place.** For `x ∈ GL_n(𝔸_f)` and a finite
place `w`, the component at `conj w` of the inverse of the adjoint `x* = (conj x)ᵀ` is the inverse
transpose of the image of `x_w` under the isomorphism `σ : E_w ≃ E_{conj w}` extending the
conjugation of `E`: `((x*)⁻¹)_{conj w} = (σ(x_w)⁻¹)ᵀ`. For `x ∈ G_f`, where `(x*)⁻¹ = x`, this is
`TauCeti.finiteAdelicUnitaryGroup.proj_conjPlace`. -/
theorem _root_.IsDedekindDomain.FiniteAdeleRing.map_proj_conjPlace_star_inv (x : GL ι 𝔸ᶠ[E])
    (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (FiniteAdeleRing.proj E w.conjPlace :
        _ →+* w.conjPlace.adicCompletion E) (star x)⁻¹ =
      GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map
        (adicCompletionCongr w w.conjPlace (complexConj E).toRingEquiv (valuation_conjPlace w) :
          w.adicCompletion E →+* w.conjPlace.adicCompletion E)
        (GeneralLinearGroup.map (FiniteAdeleRing.proj E w : _ →+* w.adicCompletion E) x)) := by
  refine GeneralLinearGroup.ext fun i j ↦ ?_
  rw [← star_inv, GeneralLinearGroup.coe_inverseTranspose, transpose_apply, ← map_inv, ← map_inv]
  simp only [GeneralLinearGroup.map_apply, RingHom.coe_coe, FiniteAdeleRing.proj_apply,
    Units.coe_star, star_apply]
  exact FiniteAdeleRing.star_apply_conjPlace _ w

/-- **Components at conjugate places.** For `g ∈ G_f` and a finite place `w` with conjugate
`conj w` (`conjPlace`), the component `g_{conj w}` is the inverse transpose of the image of `g_w`
under the isomorphism `σ : E_w ≃ E_{conj w}` extending the conjugation of `E`:
`g_{conj w} = (σ(g_w)⁻¹)ᵀ`. It is the case `(g*)⁻¹ = g` of
`IsDedekindDomain.FiniteAdeleRing.map_proj_conjPlace_star_inv`. -/
theorem finiteAdelicUnitaryGroup.proj_conjPlace (g : finiteAdelicUnitaryGroup E ι)
    (w : HeightOneSpectrum (𝓞 E)) :
    finiteAdelicUnitaryGroup.proj E ι w.conjPlace g =
      GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map
        (adicCompletionCongr w w.conjPlace (complexConj E).toRingEquiv (valuation_conjPlace w) :
          w.adicCompletion E →+* w.conjPlace.adicCompletion E)
        (finiteAdelicUnitaryGroup.proj E ι w g)) := by
  rw [proj_eq_map, proj_eq_map, ← FiniteAdeleRing.map_proj_conjPlace_star_inv,
    inv_eq_of_mul_eq_one_left (Unitary.mul_star_self_of_mem (mem_unitarySubgroup_iff.1 g.property))]

/-- **Components at conjugate places**, entrywise. For `g ∈ G_f` and a finite place `w` with
conjugate `conj w` (`conjPlace`), the entry `(i, j)` of the component `g_{conj w}` is the image of
the entry `(j, i)` of `(g_w)⁻¹` under the isomorphism `E_w ≃ E_{conj w}` extending the conjugation
of `E`. -/
theorem finiteAdelicUnitaryGroup.proj_conjPlace_apply (g : finiteAdelicUnitaryGroup E ι)
    (w : HeightOneSpectrum (𝓞 E)) (i j : ι) :
    (finiteAdelicUnitaryGroup.proj E ι w.conjPlace g : Matrix ι ι (w.conjPlace.adicCompletion E))
        i j =
      adicCompletionCongr w w.conjPlace (complexConj E).toRingEquiv (valuation_conjPlace w)
        ((↑(finiteAdelicUnitaryGroup.proj E ι w g)⁻¹ : Matrix ι ι (w.adicCompletion E)) j i) := by
  rw [proj_conjPlace, GeneralLinearGroup.coe_inverseTranspose, transpose_apply, ← map_inv,
    GeneralLinearGroup.map_apply, RingHom.coe_coe]

/-- An element of `G_f` is determined by its components at the finite places. -/
theorem finiteAdelicUnitaryGroup.ext_proj {g h : finiteAdelicUnitaryGroup E ι}
    (H : ∀ w : HeightOneSpectrum (𝓞 E), proj E ι w g = proj E ι w h) : g = h :=
  Subtype.ext <| FiniteAdeleRing.generalLinearGroup_ext H

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
  rw [coe_inv_eq_star_of_mem_unitarySubgroup g.property, star_apply,
    star_mem_integralAdeles_iff]
  exact h j i

/-- **`K₀` is the group of elements integral at every place**: `g ∈ G_f` lies in `K₀` exactly when
at every finite place `w` its component `g_w` lies in the image `GL_n(𝒪_w)` of the general linear
group over the local integers. -/
theorem mem_integralAdelicUnitaryGroup_iff_forall_place {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ integralAdelicUnitaryGroup E ι ↔ ∀ w : HeightOneSpectrum (𝓞 E),
      finiteAdelicUnitaryGroup.proj E ι w g ∈
        (GeneralLinearGroup.map (n := ι) (w.adicCompletionIntegers E).subtype).range := by
  -- Membership in `GL_n(𝒪_w)` is integrality of the entries of `g_w` and of `(g_w)⁻¹`; here
  -- `ValuationSubring.subtype A` is by definition the inclusion of the subring `A.toSubring`.
  have hS (w : HeightOneSpectrum (𝓞 E)) (h : GL ι (w.adicCompletion E)) :
      h ∈ (GeneralLinearGroup.map (n := ι) (w.adicCompletionIntegers E).subtype).range ↔
        (∀ i j, (h : Matrix ι ι _) i j ∈ w.adicCompletionIntegers E) ∧
          ∀ i j, (↑h⁻¹ : Matrix ι ι _) i j ∈ w.adicCompletionIntegers E :=
    GeneralLinearGroup.mem_range_map_subtype_iff (w.adicCompletionIntegers E).toSubring
  simp only [hS, ← map_inv, finiteAdelicUnitaryGroup.proj_apply, InvMemClass.coe_inv]
  refine ⟨fun hg w ↦ ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩, fun h ↦ ?_⟩
  · exact FiniteAdeleRing.mem_integralAdeles.1 (mem_integralAdelicUnitaryGroup_iff.1 hg i j) w
  · exact FiniteAdeleRing.mem_integralAdeles.1
      (mem_integralAdelicUnitaryGroup_iff.1 (inv_mem hg) i j) w
  · exact mem_integralAdelicUnitaryGroup_iff.2 fun i j ↦
      FiniteAdeleRing.mem_integralAdeles.2 fun w ↦ (h w).1 i j

/-- The inclusion `integralGL : GL_n(Ô) → GL_n(𝔸_f)` commutes with conjugate transposition. -/
theorem integralGL_star (h : GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) :
    FiniteAdeleRing.integralGL E ι (star h) = star (FiniteAdeleRing.integralGL E ι h) :=
  Units.ext <| Matrix.ext fun i j ↦ by
    simp only [FiniteAdeleRing.integralGL_apply, Units.coe_star, star_apply,
      coe_star_integralAdeles]

/-- The image of `h ∈ GL_n(Ô)` lies in `G_f` exactly when `h` is unitary for the conjugation of
`Ô`. -/
theorem integralGL_mem_finiteAdelicUnitaryGroup_iff
    {h : GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)} :
    FiniteAdeleRing.integralGL E ι h ∈ finiteAdelicUnitaryGroup E ι ↔
      h ∈ unitarySubgroup (GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) := by
  simp only [mem_unitarySubgroup_iff, Unitary.mem_iff, ← integralGL_star, ← map_mul,
    (FiniteAdeleRing.integralGL_injective E ι).eq_iff' (map_one _)]

variable (E ι) in
/-- **`K₀` is the group of unitary matrices over `Ô`**: the inclusion
`integralGL : GL_n(Ô) → GL_n(𝔸_f)` restricts to an isomorphism from the unitary subgroup of
`GL_n(Ô)`, for the conjugation of `Ô`, onto `K₀`. -/
def integralAdelicUnitaryGroupEquiv :
    unitarySubgroup (GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E)) ≃*
      integralAdelicUnitaryGroup E ι :=
  MulEquiv.ofBijective
    ((((FiniteAdeleRing.integralGL E ι).comp (unitarySubgroup _).subtype).codRestrict
        (finiteAdelicUnitaryGroup E ι) fun h ↦
          integralGL_mem_finiteAdelicUnitaryGroup_iff.2 h.property).codRestrict
      (integralAdelicUnitaryGroup E ι) fun h ↦
        mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL.2 ⟨h, rfl⟩)
    ⟨fun h h' hh ↦ Subtype.ext <| FiniteAdeleRing.integralGL_injective E ι <|
        congrArg (fun g : integralAdelicUnitaryGroup E ι ↦ ((g : finiteAdelicUnitaryGroup E ι) :
          GL ι 𝔸ᶠ[E])) hh,
      fun g ↦ by
        obtain ⟨h, hh⟩ := mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL.1 g.property
        refine ⟨⟨h, integralGL_mem_finiteAdelicUnitaryGroup_iff.1
          (hh ▸ (g : finiteAdelicUnitaryGroup E ι).property)⟩, ?_⟩
        exact Subtype.ext (Subtype.ext hh)⟩

/-- The isomorphism from the unitary subgroup of `GL_n(Ô)` onto `K₀` is `integralGL`. -/
@[simp]
theorem coe_integralAdelicUnitaryGroupEquiv
    (h : unitarySubgroup (GL ι (FiniteAdeleRing.integralAdeles (𝓞 E) E))) :
    ((integralAdelicUnitaryGroupEquiv E ι h : finiteAdelicUnitaryGroup E ι) : GL ι 𝔸ᶠ[E]) =
      FiniteAdeleRing.integralGL E ι h :=
  (rfl)

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
  have he := unitaryGroupOf.isClosedEmbedding_val (A := (1 : Matrix ι ι 𝔸ᶠ[E])) isUnit_one
  rw [unitaryGroupOf_one] at he
  convert he.isCompact_preimage hM using 1
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

end FiniteAdelicUnitaryGroup

/-! ### The adelic unitary group of a sign vector -/

section InfiniteAdelicUnitaryGroup

variable (E : Type*) [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E] {ι : Type*}
  [Fintype ι] [DecidableEq ι]

/-- The archimedean adelic unitary group `G_∞(s) = U(diag s)(E_∞)` of a CM field `E` and a sign
vector `s`: the invertible matrices `g` over the infinite adeles with `g* diag(s) g = diag(s)`. As
conjugation acts within each infinite completion `E_w`, it is the product over the infinite places
`w` of the unitary groups `U(diag s)(E_w) ≅ U(p, n - p)`, `p` being the number of signs `+1`. -/
abbrev infiniteAdelicUnitaryGroup (s : ι → ℤˣ) : Subgroup (GL ι (InfiniteAdeleRing E)) :=
  unitaryGroupOf (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E))

end InfiniteAdelicUnitaryGroup

section AdelicUnitaryGroup

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- The **adelic unitary group** `G(s) = G_∞(s) × G_f` of a CM field `E` and a sign vector `s`,
inside `GL_n(E_∞) × GL_n(𝔸_f) ≅ GL_n(𝔸)`: the adelic matrices preserving the form that is
`diag(s)` at every infinite place and `1_n` at every finite place. `Subgroup.prodEquiv`
identifies it with the product of `G_∞(s)` and `G_f`. -/
abbrev adelicUnitaryGroup (s : ι → ℤˣ) : Subgroup (GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) :=
  (infiniteAdelicUnitaryGroup E s).prod (finiteAdelicUnitaryGroup E ι)

/-- The finite component `G(s) → G_f`, `(g_∞, g_f) ↦ g_f`. -/
def adelicUnitaryGroup.finitePart (s : ι → ℤˣ) :
    adelicUnitaryGroup E s →* finiteAdelicUnitaryGroup E ι :=
  ((MonoidHom.snd _ _).comp (adelicUnitaryGroup E s).subtype).codRestrict _
    fun g ↦ g.property.2

/-- The embedding `G_f → G(s)`, `g ↦ (1, g)`. -/
def adelicUnitaryGroup.ofFinite (s : ι → ℤˣ) :
    finiteAdelicUnitaryGroup E ι →* adelicUnitaryGroup E s :=
  ((MonoidHom.inr _ _).comp (finiteAdelicUnitaryGroup E ι).subtype).codRestrict _
    fun g ↦ ⟨one_mem _, g.property⟩

/-- The archimedean component `G(s) → G_∞(s)`, `(g_∞, g_f) ↦ g_∞`. -/
def adelicUnitaryGroup.infinitePart (s : ι → ℤˣ) :
    adelicUnitaryGroup E s →* infiniteAdelicUnitaryGroup E s :=
  ((MonoidHom.fst _ _).comp (adelicUnitaryGroup E s).subtype).codRestrict _
    fun g ↦ g.property.1

/-- The embedding `G_∞(s) → G(s)`, `g ↦ (g, 1)`. -/
def adelicUnitaryGroup.ofInfinite (s : ι → ℤˣ) :
    infiniteAdelicUnitaryGroup E s →* adelicUnitaryGroup E s :=
  ((MonoidHom.inl _ _).comp (infiniteAdelicUnitaryGroup E s).subtype).codRestrict _
    fun g ↦ ⟨g.property, one_mem _⟩

variable {E}

/-- The finite component of `g ∈ G(s)` is `g_f`. -/
@[simp]
theorem adelicUnitaryGroup.coe_finitePart {s : ι → ℤˣ} (g : adelicUnitaryGroup E s) :
    (adelicUnitaryGroup.finitePart E s g : GL ι 𝔸ᶠ[E]) =
      (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 :=
  (rfl)

/-- The embedding of `G_f` in `G(s)` is `g ↦ (1, g)`. -/
@[simp]
theorem adelicUnitaryGroup.coe_ofFinite {s : ι → ℤˣ} (g : finiteAdelicUnitaryGroup E ι) :
    (adelicUnitaryGroup.ofFinite E s g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) =
      (1, (g : GL ι 𝔸ᶠ[E])) :=
  (rfl)

/-- The finite component of `(1, g)` is `g`. -/
@[simp]
theorem adelicUnitaryGroup.finitePart_ofFinite {s : ι → ℤˣ} (g : finiteAdelicUnitaryGroup E ι) :
    adelicUnitaryGroup.finitePart E s (adelicUnitaryGroup.ofFinite E s g) = g :=
  (rfl)

/-- The archimedean component of `g ∈ G(s)` is `g_∞`. -/
@[simp]
theorem adelicUnitaryGroup.coe_infinitePart {s : ι → ℤˣ} (g : adelicUnitaryGroup E s) :
    (adelicUnitaryGroup.infinitePart E s g : GL ι (InfiniteAdeleRing E)) =
      (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1 :=
  (rfl)

/-- The embedding of `G_∞(s)` in `G(s)` is `g ↦ (g, 1)`. -/
@[simp]
theorem adelicUnitaryGroup.coe_ofInfinite {s : ι → ℤˣ} (g : infiniteAdelicUnitaryGroup E s) :
    (adelicUnitaryGroup.ofInfinite E s g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) =
      ((g : GL ι (InfiniteAdeleRing E)), 1) :=
  (rfl)

/-- The archimedean component of `(g, 1)` is `g`. -/
@[simp]
theorem adelicUnitaryGroup.infinitePart_ofInfinite {s : ι → ℤˣ}
    (g : infiniteAdelicUnitaryGroup E s) :
    adelicUnitaryGroup.infinitePart E s (adelicUnitaryGroup.ofInfinite E s g) = g :=
  (rfl)

/-- The archimedean component of `(1, g)` is `1`. -/
@[simp]
theorem adelicUnitaryGroup.infinitePart_ofFinite {s : ι → ℤˣ} (g : finiteAdelicUnitaryGroup E ι) :
    adelicUnitaryGroup.infinitePart E s (adelicUnitaryGroup.ofFinite E s g) = 1 :=
  (rfl)

/-- The finite component of `(g, 1)` is `1`. -/
@[simp]
theorem adelicUnitaryGroup.finitePart_ofInfinite {s : ι → ℤˣ}
    (g : infiniteAdelicUnitaryGroup E s) :
    adelicUnitaryGroup.finitePart E s (adelicUnitaryGroup.ofInfinite E s g) = 1 :=
  (rfl)

/-- The archimedean component `G(s) → G_∞(s)` is continuous. -/
@[fun_prop]
theorem adelicUnitaryGroup.continuous_infinitePart (s : ι → ℤˣ) :
    Continuous (adelicUnitaryGroup.infinitePart E s) :=
  continuous_induced_rng.2 (continuous_fst.comp continuous_subtypeVal)

/-- The embedding `G_∞(s) → G(s)`, `g ↦ (g, 1)`, is continuous. -/
@[fun_prop]
theorem adelicUnitaryGroup.continuous_ofInfinite (s : ι → ℤˣ) :
    Continuous (adelicUnitaryGroup.ofInfinite E s) :=
  continuous_induced_rng.2 (continuous_subtypeVal.prodMk continuous_const)

/-- The finite component `G(s) → G_f` is continuous. -/
@[fun_prop]
theorem adelicUnitaryGroup.continuous_finitePart (s : ι → ℤˣ) :
    Continuous (adelicUnitaryGroup.finitePart E s) :=
  continuous_induced_rng.2 (continuous_snd.comp continuous_subtypeVal)

/-- The embedding `G_f → G(s)`, `g ↦ (1, g)`, is continuous. -/
@[fun_prop]
theorem adelicUnitaryGroup.continuous_ofFinite (s : ι → ℤˣ) :
    Continuous (adelicUnitaryGroup.ofFinite E s) :=
  continuous_induced_rng.2 (continuous_const.prodMk continuous_subtypeVal)

/-- The element of `G(s)` defined by a pair `(M, N)` of matrices over the infinite and the finite
adeles preserving the forms, `M* diag(s) M = diag(s)` and `N* N = 1`: such matrices are
invertible. -/
def adelicUnitaryGroup.ofMatrix {s : ι → ℤˣ} (M : Matrix ι ι (InfiniteAdeleRing E))
    (hM : star M * diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) * M =
      diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)))
    (N : Matrix ι ι 𝔸ᶠ[E]) (hN : star N * N = 1) : adelicUnitaryGroup E s :=
  have hs : IsUnit (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) :=
    isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i ↦ (s i).isUnit.map (Int.castRingHom _))
  have hN' : star N * 1 * N = 1 := by rwa [Matrix.mul_one]
  ⟨((unitaryGroupOf.ofMatrix hs M hM : GL ι _),
      (unitaryGroupOf.ofMatrix isUnit_one N hN' : GL ι _)),
    (unitaryGroupOf.ofMatrix _ M hM).property,
    unitaryGroupOf_one.le (unitaryGroupOf.ofMatrix _ N hN').property⟩

/-- The archimedean component of `adelicUnitaryGroup.ofMatrix M hM N hN` is `M`. -/
@[simp]
theorem adelicUnitaryGroup.val_fst_ofMatrix {s : ι → ℤˣ} (M : Matrix ι ι (InfiniteAdeleRing E))
    (hM : star M * diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) * M =
      diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)))
    (N : Matrix ι ι 𝔸ᶠ[E]) (hN : star N * N = 1) :
    (((adelicUnitaryGroup.ofMatrix M hM N hN : adelicUnitaryGroup E s) :
      GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1 : Matrix ι ι (InfiniteAdeleRing E)) = M :=
  unitaryGroupOf.val_ofMatrix _ _ _

/-- The finite component of `adelicUnitaryGroup.ofMatrix M hM N hN` is `N`. -/
@[simp]
theorem adelicUnitaryGroup.val_snd_ofMatrix {s : ι → ℤˣ} (M : Matrix ι ι (InfiniteAdeleRing E))
    (hM : star M * diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) * M =
      diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)))
    (N : Matrix ι ι 𝔸ᶠ[E]) (hN : star N * N = 1) :
    (((adelicUnitaryGroup.ofMatrix M hM N hN : adelicUnitaryGroup E s) :
      GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 : Matrix ι ι 𝔸ᶠ[E]) = N :=
  unitaryGroupOf.val_ofMatrix _ _ _

/-- **The adelic matrices preserving the form are the elements of `G(s)`.** A pair `(M, N)` of
matrices over the infinite and the finite adeles is the adelic matrix of an element of `G(s)`
exactly when `M* diag(s) M = diag(s)` and `N* N = 1`; in particular such matrices are invertible,
and the element is `adelicUnitaryGroup.ofMatrix M hM N hN`. -/
theorem exists_mem_adelicUnitaryGroup_iff {s : ι → ℤˣ} {M : Matrix ι ι (InfiniteAdeleRing E)}
    {N : Matrix ι ι 𝔸ᶠ[E]} :
    (∃ g ∈ adelicUnitaryGroup E s,
        (g.1 : Matrix ι ι (InfiniteAdeleRing E)) = M ∧ (g.2 : Matrix ι ι 𝔸ᶠ[E]) = N) ↔
      star M * diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) * M =
          diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) ∧
        star N * N = 1 := by
  refine ⟨?_, fun ⟨hM, hN⟩ ↦ ?_⟩
  · rintro ⟨g, ⟨hg₁, hg₂⟩, rfl, rfl⟩
    exact ⟨mem_unitaryGroupOf_iff.1 hg₁,
      mem_unitaryGroup_iff'.1 (mem_unitarySubgroup_GL_iff_mem_unitaryGroup.1 hg₂)⟩
  · exact ⟨adelicUnitaryGroup.ofMatrix M hM N hN, (adelicUnitaryGroup.ofMatrix M hM N hN).property,
      adelicUnitaryGroup.val_fst_ofMatrix M hM N hN, adelicUnitaryGroup.val_snd_ofMatrix M hM N hN⟩

end AdelicUnitaryGroup

end TauCeti
