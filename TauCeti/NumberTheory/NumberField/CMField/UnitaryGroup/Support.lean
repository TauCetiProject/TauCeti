/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Idempotent
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
import TauCeti.Data.Set.Image

/-!
# Supports of elements of the finite adelic unitary group

Let `E` be a CM field and `G_f = U(1_n)(𝔸_f)` its finite adelic unitary group
(`TauCeti.finiteAdelicUnitaryGroup`). An element `g ∈ G_f` is **supported on** a set `S` of finite
places if its component `g_w` is `1` at every finite place `w ∉ S`; these elements form a subgroup
`TauCeti.finiteAdelicUnitaryGroup.supportedOn E ι S`. Being trivial on `S` is being supported on
the complement of `S`.

For a set `S` of finite places stable under conjugation `w ↦ conj w`, the **cut**
`TauCeti.finiteAdelicUnitaryGroup.cut E ι S hS g` of `g ∈ G_f` along `S` is the element with
component `g_w` at the places `w ∈ S` and `1` elsewhere. It is `e_S • g + (1 - e_S) • 1` for the
idempotent `e_S ∈ 𝔸_f` with component `1` on `S` and `0` elsewhere
(`IsDedekindDomain.FiniteAdeleRing.indicatorOne`); conjugation fixes `e_S` because `S` is stable,
so cutting preserves `G_f`. Cutting is a group endomorphism of `G_f`, and `g` is the product of
its cuts along `S` and along the complement of `S`. Since the components at `w` and `conj w` of an
element of `G_f` determine each other (`TauCeti.finiteAdelicUnitaryGroup.proj_conjPlace`), the
supports that occur for such a decomposition are naturally the sets stable under conjugation, and
an arbitrary set `S` is replaced by `S ∪ conj S`.

These decompositions reduce statements about `G_f` to finitely many places: they relate `G_f` to
its integral subgroup `K₀` and to its elements supported at a single place and its conjugate.

## Main definitions

* `TauCeti.finiteAdelicUnitaryGroup.supportedOn E ι S`: the subgroup of the `g ∈ G_f` with
  `g_w = 1` for every finite place `w ∉ S`.
* `TauCeti.finiteAdelicUnitaryGroup.cut E ι S hS`: for `S` stable under conjugation
  (`hS : conjPlace ⁻¹' S = S`), the endomorphism of `G_f` keeping the components on `S` and
  replacing the others by `1`.

## Main results

* `TauCeti.finiteAdelicUnitaryGroup.proj_cut`: the components of a cut.
* `TauCeti.finiteAdelicUnitaryGroup.range_cut`, `TauCeti.finiteAdelicUnitaryGroup.ker_cut`: the
  cut along `S` has image the elements supported on `S` and kernel the elements trivial on `S`;
  `TauCeti.finiteAdelicUnitaryGroup.continuous_cut`: it is continuous.
* `TauCeti.finiteAdelicUnitaryGroup.cut_mul_cut_compl`: `g` is the product of its cuts along `S`
  and along the complement of `S`.
* `TauCeti.finiteAdelicUnitaryGroup.exists_supportedOn_mul_eq`: for every set `S` of finite
  places, every `g ∈ G_f` is a product `a * b` with `a` supported on `S ∪ conj S` and `b` trivial
  there, with `a, b ∈ K₀` when `g ∈ K₀`.
* `TauCeti.finiteAdelicUnitaryGroup.cut_mem_integralAdelicUnitaryGroup_iff_forall_mem_range`: the
  cut of `g` along `S` lies in `K₀` exactly when `g_w ∈ GL_n(𝒪_w)` at every place `w ∈ S`.
* `TauCeti.finiteAdelicUnitaryGroup.eventually_proj_mem_range`: `g_w ∈ GL_n(𝒪_w)` for all but
  finitely many finite places `w`.
* `TauCeti.finiteAdelicUnitaryGroup.eq_top_of_integralAdelicUnitaryGroup_le`: a subgroup of `G_f`
  containing `K₀` and the elements supported on `{w, conj w}` for every finite place `w` is all
  of `G_f`.

## References

* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.

## Attribution

The statements on supports, `TauCeti.finiteAdelicUnitaryGroup.exists_supportedOn_mul_eq` and
`TauCeti.finiteAdelicUnitaryGroup.eq_top_of_integralAdelicUnitaryGroup_le`, are those of
`New.Gf.exists_supportedOn_mul_trivialOn` and `New.Gf.mem_of_stdLevel_le_of_supportedOn_le` in
the file `src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti.finiteAdelicUnitaryGroup

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-! ### Supports -/

variable (E ι) in
/-- The subgroup of the elements of `G_f` **supported on** a set `S` of finite places: those whose
component `g_w` is `1` at every finite place `w ∉ S`. The elements supported on the complement of
`S` are those trivial on `S`. -/
def supportedOn (S : Set (HeightOneSpectrum (𝓞 E))) : Subgroup (finiteAdelicUnitaryGroup E ι) :=
  ⨅ w ∈ Sᶜ, (proj E ι w).ker

/-- `g` is supported on `S` exactly when `g_w = 1` at every finite place `w ∉ S`. -/
@[simp low]
theorem mem_supportedOn_iff {S : Set (HeightOneSpectrum (𝓞 E))}
    {g : finiteAdelicUnitaryGroup E ι} :
    g ∈ supportedOn E ι S ↔ ∀ w ∉ S, proj E ι w g = 1 := by
  simp only [supportedOn, Subgroup.mem_iInf, MonoidHom.mem_ker, Set.mem_compl_iff]

/-- Being supported on a set of places is inherited by larger sets. -/
theorem supportedOn_mono : Monotone (supportedOn E ι) := fun _ _ hST ↦
  iInf_le_iInf_of_subset (Set.compl_subset_compl.2 hST)

/-- Every element is supported on the set of all finite places. -/
@[simp]
theorem supportedOn_univ : supportedOn E ι Set.univ = ⊤ := by
  rw [supportedOn, Set.compl_univ, iInf_emptyset]

/-- Only `1` is supported on the empty set of places. -/
@[simp]
theorem supportedOn_empty : supportedOn E ι ∅ = ⊥ :=
  eq_bot_iff.2 fun _ hg ↦ Subgroup.mem_bot.2 <| ext_proj fun w ↦ by
    rw [mem_supportedOn_iff.1 hg w (Set.notMem_empty w), map_one]

/-- An element supported on `S` and on `T` is supported on `S ∩ T`. -/
theorem supportedOn_inter (S T : Set (HeightOneSpectrum (𝓞 E))) :
    supportedOn E ι (S ∩ T) = supportedOn E ι S ⊓ supportedOn E ι T := by
  rw [supportedOn, supportedOn, supportedOn, Set.compl_inter, iInf_union]

/-! ### Cutting along a set of places stable under conjugation -/

/-- Cutting an element of `G_f` along the indicator of a set stable under conjugation stays in
`G_f`. -/
private theorem cutGL_mem {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S)
    (g : finiteAdelicUnitaryGroup E ι) :
    (FiniteAdeleRing.isIdempotentElem_indicatorOne S).cutGL (g : GL ι 𝔸ᶠ[E]) ∈
      finiteAdelicUnitaryGroup E ι := by
  have hstar : star (FiniteAdeleRing.indicatorOne (K := E) S) = FiniteAdeleRing.indicatorOne S := by
    rw [FiniteAdeleRing.star_indicatorOne, hS]
  -- Along a self-adjoint idempotent, cutting is a star monoid endomorphism of `GL_n(𝔸_f)`, so it
  -- preserves unitary elements.
  let f : GL ι 𝔸ᶠ[E] →⋆* GL ι 𝔸ᶠ[E] :=
    { (FiniteAdeleRing.isIdempotentElem_indicatorOne S).cutGL with
      map_star' := fun x ↦ by simp only [MonoidHom.toFun_eq_coe, IsIdempotentElem.star_cutGL,
        hstar] }
  exact mem_unitarySubgroup_iff.2 (Unitary.map_mem f (mem_unitarySubgroup_iff.1 g.property))

variable (E ι) in
/-- The **cut** of `g ∈ G_f` along a set `S` of finite places stable under conjugation: the
element with component `g_w` at the places `w ∈ S` and `1` elsewhere (`proj_cut`). It is
`e_S • g + (1 - e_S) • 1` for the indicator `e_S` of `S`. -/
def cut (S : Set (HeightOneSpectrum (𝓞 E))) (hS : conjPlace ⁻¹' S = S) :
    finiteAdelicUnitaryGroup E ι →* finiteAdelicUnitaryGroup E ι :=
  ((FiniteAdeleRing.isIdempotentElem_indicatorOne S).cutGL.comp
    (finiteAdelicUnitaryGroup E ι).subtype).codRestrict _ (cutGL_mem hS)

/-- As an element of `GL_n(𝔸_f)`, the cut of `g` along `S` is the cut of `g` along the indicator
`e_S` of `S`. -/
theorem coe_cut (S : Set (HeightOneSpectrum (𝓞 E))) (hS : conjPlace ⁻¹' S = S)
    (g : finiteAdelicUnitaryGroup E ι) :
    (cut E ι S hS g : GL ι 𝔸ᶠ[E]) =
      (FiniteAdeleRing.isIdempotentElem_indicatorOne S).cutGL (g : GL ι 𝔸ᶠ[E]) := by
  rfl

/-- The underlying matrix of the cut of `g` along `S` is `e_S • g + (1 - e_S) • 1`. -/
theorem val_cut (S : Set (HeightOneSpectrum (𝓞 E))) (hS : conjPlace ⁻¹' S = S)
    (g : finiteAdelicUnitaryGroup E ι) :
    ((cut E ι S hS g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) =
      FiniteAdeleRing.indicatorOne (K := E) S • (g : GL ι 𝔸ᶠ[E]).val +
        (1 - FiniteAdeleRing.indicatorOne (K := E) S) • 1 :=
  IsIdempotentElem.val_cutGL _ _

/-- Cutting along `S` is continuous. -/
@[fun_prop]
theorem continuous_cut (S : Set (HeightOneSpectrum (𝓞 E))) (hS : conjPlace ⁻¹' S = S) :
    Continuous (cut E ι S hS) :=
  ((FiniteAdeleRing.isIdempotentElem_indicatorOne S).continuous_cutGL.comp
    continuous_subtypeVal).subtype_mk _

open Classical in
/-- **Components of a cut.** The component of the cut of `g` along `S` at a finite place `w` is
`g_w` if `w ∈ S` and `1` otherwise. -/
theorem proj_cut (S : Set (HeightOneSpectrum (𝓞 E))) (hS : conjPlace ⁻¹' S = S)
    (g : finiteAdelicUnitaryGroup E ι) (w : HeightOneSpectrum (𝓞 E)) :
    proj E ι w (cut E ι S hS g) = if w ∈ S then proj E ι w g else 1 := by
  refine Units.ext <| Matrix.ext fun i j ↦ ?_
  rw [proj_apply, val_cut]
  by_cases hw : w ∈ S <;> simp [hw, Matrix.one_apply, apply_ite (fun a : 𝔸ᶠ[E] ↦ a w)]

/-- At a place of `S`, the cut of `g` along `S` has the component of `g`. -/
@[simp]
theorem proj_cut_of_mem {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S)
    (g : finiteAdelicUnitaryGroup E ι) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) :
    proj E ι w (cut E ι S hS g) = proj E ι w g := by
  classical
  rw [proj_cut, ite_eq_left hw]

/-- Away from `S`, the cut of `g` along `S` has component `1`. -/
@[simp]
theorem proj_cut_of_notMem {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S)
    (g : finiteAdelicUnitaryGroup E ι) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    proj E ι w (cut E ι S hS g) = 1 := by
  classical
  rw [proj_cut, ite_eq_right hw]

/-- The cut of `g` along `S` is supported on `S`. -/
@[simp]
theorem cut_mem_supportedOn {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S)
    (g : finiteAdelicUnitaryGroup E ι) : cut E ι S hS g ∈ supportedOn E ι S :=
  mem_supportedOn_iff.2 fun _ hw ↦ proj_cut_of_notMem hS g hw

/-- Cutting along `S` fixes exactly the elements supported on `S`. -/
@[simp]
theorem cut_eq_self_iff {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S)
    {g : finiteAdelicUnitaryGroup E ι} : cut E ι S hS g = g ↔ g ∈ supportedOn E ι S := by
  refine ⟨fun h ↦ h ▸ cut_mem_supportedOn hS g, fun hg ↦ ext_proj fun w ↦ ?_⟩
  by_cases hw : w ∈ S
  · exact proj_cut_of_mem hS g hw
  · rw [proj_cut_of_notMem hS g hw, mem_supportedOn_iff.1 hg w hw]

/-- The image of cutting along `S` is the subgroup of elements supported on `S`. -/
@[simp]
theorem range_cut {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S) :
    (cut E ι S hS).range = supportedOn E ι S :=
  le_antisymm (by rintro _ ⟨g, rfl⟩; exact cut_mem_supportedOn hS g)
    fun _ hg ↦ ⟨_, (cut_eq_self_iff hS).2 hg⟩

/-- The kernel of cutting along `S` is the subgroup of elements trivial on `S`, that is supported
on the complement of `S`. -/
@[simp]
theorem ker_cut {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S) :
    (cut E ι S hS).ker = supportedOn E ι Sᶜ := by
  ext g
  rw [MonoidHom.mem_ker, mem_supportedOn_iff]
  refine ⟨fun h w hw ↦ ?_, fun h ↦ ext_proj fun w ↦ ?_⟩
  · rw [← proj_cut_of_mem hS g (Set.notMem_compl_iff.1 hw), h, map_one]
  · by_cases hw : w ∈ S
    · rw [proj_cut_of_mem hS g hw, h w (Set.notMem_compl_iff.2 hw), map_one]
    · rw [proj_cut_of_notMem hS g hw, map_one]

/-- Cutting along the set of all finite places is the identity. -/
@[simp]
theorem cut_univ (h : conjPlace ⁻¹' (Set.univ : Set (HeightOneSpectrum (𝓞 E))) = Set.univ) :
    cut E ι Set.univ h = MonoidHom.id _ :=
  MonoidHom.ext fun g ↦ ext_proj fun _ ↦ proj_cut_of_mem h g (Set.mem_univ _)

/-- Cutting along the empty set of places is trivial. -/
@[simp]
theorem cut_empty (h : conjPlace ⁻¹' (∅ : Set (HeightOneSpectrum (𝓞 E))) = ∅) :
    cut E ι ∅ h = 1 :=
  MonoidHom.ext fun g ↦ ext_proj fun w ↦ by
    rw [proj_cut_of_notMem h g (Set.notMem_empty w), MonoidHom.one_apply, map_one]

/-- Cutting along `T` and then along `S` is cutting along `S ∩ T`. -/
@[simp]
theorem cut_cut {S T : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S)
    (hT : conjPlace ⁻¹' T = T) (g : finiteAdelicUnitaryGroup E ι) :
    cut E ι S hS (cut E ι T hT g) =
      cut E ι (S ∩ T) (by rw [Set.preimage_inter, hS, hT]) g := by
  refine Subtype.ext ?_
  simp only [coe_cut, IsIdempotentElem.cutGL_cutGL, FiniteAdeleRing.indicatorOne_mul_indicatorOne]

/-- **Decomposition along a set of places.** An element of `G_f` is the product of its cuts along
a set `S` of finite places stable under conjugation and along the complement of `S`. -/
@[simp]
theorem cut_mul_cut_compl {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S)
    (g : finiteAdelicUnitaryGroup E ι) :
    cut E ι S hS g * cut E ι Sᶜ (by rw [Set.preimage_compl, hS]) g = g := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_cut, ← FiniteAdeleRing.one_sub_indicatorOne,
    IsIdempotentElem.cutGL_mul_cutGL_one_sub]

/-! ### Cuts and the integral subgroup `K₀` -/

/-- The cut of `g` along `S` lies in `K₀` exactly when the entries of `g` are integral at every
place of `S`. -/
theorem cut_mem_integralAdelicUnitaryGroup_iff {S : Set (HeightOneSpectrum (𝓞 E))}
    (hS : conjPlace ⁻¹' S = S) {g : finiteAdelicUnitaryGroup E ι} :
    cut E ι S hS g ∈ integralAdelicUnitaryGroup E ι ↔
      ∀ w ∈ S, ∀ i j, ((g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j w ∈ w.adicCompletionIntegers E := by
  simp_rw [mem_integralAdelicUnitaryGroup_iff, FiniteAdeleRing.mem_integralAdeles, val_cut]
  refine ⟨fun h w hw i j ↦ by simpa [hw] using h i j w, fun h i j w ↦ ?_⟩
  by_cases hw : w ∈ S
  · simpa [hw] using h w hw i j
  · by_cases hij : i = j <;> simp [hw, hij, zero_mem, one_mem]

/-- **Integrality of a cut, place by place.** The cut of `g` along `S` lies in `K₀` exactly when
the component `g_w` lies in the image `GL_n(𝒪_w)` of the general linear group over the local
integers at every place `w ∈ S`. -/
theorem cut_mem_integralAdelicUnitaryGroup_iff_forall_mem_range
    {S : Set (HeightOneSpectrum (𝓞 E))} (hS : conjPlace ⁻¹' S = S)
    {g : finiteAdelicUnitaryGroup E ι} :
    cut E ι S hS g ∈ integralAdelicUnitaryGroup E ι ↔ ∀ w ∈ S, proj E ι w g ∈
      (GeneralLinearGroup.map (n := ι) (w.adicCompletionIntegers E).subtype).range := by
  rw [mem_integralAdelicUnitaryGroup_iff_forall_place]
  refine ⟨fun h w hw ↦ proj_cut_of_mem hS g hw ▸ h w, fun h w ↦ ?_⟩
  by_cases hw : w ∈ S
  · exact (proj_cut_of_mem hS g hw).symm ▸ h w hw
  · exact (proj_cut_of_notMem hS g hw).symm ▸ one_mem _

/-- The cut of an element of `K₀` lies in `K₀`. -/
theorem cut_mem_integralAdelicUnitaryGroup {S : Set (HeightOneSpectrum (𝓞 E))}
    (hS : conjPlace ⁻¹' S = S) {g : finiteAdelicUnitaryGroup E ι}
    (hg : g ∈ integralAdelicUnitaryGroup E ι) : cut E ι S hS g ∈ integralAdelicUnitaryGroup E ι :=
  (cut_mem_integralAdelicUnitaryGroup_iff hS).2 fun w _ i j ↦
    FiniteAdeleRing.mem_integralAdeles.1 (mem_integralAdelicUnitaryGroup_iff.1 hg i j) w

/-- **Decomposition along a set of places**, for an arbitrary set `S` of finite places: every
`g ∈ G_f` is a product `a * b` with `a` supported on `S ∪ conj S` and `b` trivial there, and
`a, b ∈ K₀` when `g ∈ K₀`. -/
theorem exists_supportedOn_mul_eq (S : Set (HeightOneSpectrum (𝓞 E)))
    (g : finiteAdelicUnitaryGroup E ι) :
    ∃ a ∈ supportedOn E ι (S ∪ conjPlace ⁻¹' S), ∃ b ∈ supportedOn E ι (S ∪ conjPlace ⁻¹' S)ᶜ,
      a * b = g ∧ (g ∈ integralAdelicUnitaryGroup E ι →
        a ∈ integralAdelicUnitaryGroup E ι ∧ b ∈ integralAdelicUnitaryGroup E ι) := by
  have hS := Function.Involutive.preimage_union_preimage conjPlace_conjPlace S
  exact ⟨_, cut_mem_supportedOn hS g, _, cut_mem_supportedOn _ g, cut_mul_cut_compl hS g,
    fun hg ↦ ⟨cut_mem_integralAdelicUnitaryGroup hS hg, cut_mem_integralAdelicUnitaryGroup _ hg⟩⟩

/-! ### Almost all components are integral, and local generation -/

/-- **Almost all components are integral**: for `g ∈ G_f`, the component `g_w` lies in
`GL_n(𝒪_w)` at all but finitely many finite places `w`. This is the case of `G_f` of
`IsDedekindDomain.FiniteAdeleRing.eventually_map_proj_mem_range`. -/
theorem eventually_proj_mem_range (g : finiteAdelicUnitaryGroup E ι) :
    ∀ᶠ w in Filter.cofinite, proj E ι w g ∈
      (GeneralLinearGroup.map (n := ι) (w.adicCompletionIntegers E).subtype).range := by
  filter_upwards [FiniteAdeleRing.eventually_map_proj_mem_range (g : GL ι 𝔸ᶠ[E])] with w hw
  convert hw using 1
  exact GeneralLinearGroup.ext fun i j ↦ by simp

/-- The elements supported on `F ∪ conj F`, for a finite set `F` of places, lie in every subgroup
containing the elements supported on `{w, conj w}` for each finite place `w`. -/
private theorem supportedOn_union_preimage_le {H : Subgroup (finiteAdelicUnitaryGroup E ι)}
    (hH : ∀ w : HeightOneSpectrum (𝓞 E), supportedOn E ι {w, w.conjPlace} ≤ H)
    (F : Finset (HeightOneSpectrum (𝓞 E))) :
    supportedOn E ι ((F : Set _) ∪ conjPlace ⁻¹' F) ≤ H := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert u F _ ih =>
    intro x hx
    -- Split `x` along `A = F ∪ conj F`: the part on `A` is handled by induction, and the part
    -- away from `A` is supported on `{u, conj u}`.
    have hA := Function.Involutive.preimage_union_preimage conjPlace_conjPlace
      (F : Set (HeightOneSpectrum (𝓞 E)))
    rw [← cut_mul_cut_compl hA x]
    refine H.mul_mem (ih (cut_mem_supportedOn hA x)) (hH u (mem_supportedOn_iff.2 fun w hw ↦ ?_))
    by_cases hwA : w ∈ (F : Set _) ∪ conjPlace ⁻¹' F
    · exact proj_cut_of_notMem _ x (Set.notMem_compl_iff.2 hwA)
    · rw [proj_cut_of_mem _ x hwA]
      refine mem_supportedOn_iff.1 hx w fun h ↦ ?_
      simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at h hw hwA
      rcases h with (h | h) | (h | h)
      · exact hw (Or.inl h)
      · exact hwA (Or.inl h)
      · exact hw (Or.inr (by rw [← h, conjPlace_conjPlace]))
      · exact hwA (Or.inr h)

/-- **Local generation of `G_f`.** A subgroup of `G_f` containing `K₀` and the elements supported
on `{w, conj w}` for every finite place `w` is all of `G_f`. -/
theorem eq_top_of_integralAdelicUnitaryGroup_le {H : Subgroup (finiteAdelicUnitaryGroup E ι)}
    (hK : integralAdelicUnitaryGroup E ι ≤ H)
    (hH : ∀ w : HeightOneSpectrum (𝓞 E), supportedOn E ι {w, w.conjPlace} ≤ H) : H = ⊤ := by
  refine eq_top_iff.2 fun g _ ↦ ?_
  -- Split `g` along `T ∪ conj T`, for the finite set `T` of places where `g_w ∉ GL_n(𝒪_w)`.
  have hT := Filter.eventually_cofinite.1 (eventually_proj_mem_range g)
  have hS := Function.Involutive.preimage_union_preimage conjPlace_conjPlace
    (hT.toFinset : Set (HeightOneSpectrum (𝓞 E)))
  rw [← cut_mul_cut_compl hS g]
  refine H.mul_mem (supportedOn_union_preimage_le hH _ (cut_mem_supportedOn hS g)) (hK ?_)
  refine (cut_mem_integralAdelicUnitaryGroup_iff_forall_mem_range _).2 fun w hw ↦ ?_
  by_contra h
  exact hw (Or.inl (hT.mem_toFinset.2 h))

end TauCeti.finiteAdelicUnitaryGroup
