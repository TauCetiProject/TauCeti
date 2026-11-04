/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Disk
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.MappingCylinder
public import TauCeti.Topology.CWComplex.Classical.CWType
public import TauCeti.Topology.CWComplex.Classical.Cylinder

/-!
# Whitehead's theorem

**Whitehead's theorem** says that a weak homotopy equivalence between CW complexes is a homotopy
equivalence (Hatcher, *Algebraic Topology*, Theorem 4.5). This file proves it for spaces of
CW type, using Mathlib's classical CW complexes as models, as
`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`, whose
forward map is the given weak homotopy equivalence.

The proof goes through the surjectivity half of Hatcher's Proposition 4.22, i.e. surjectivity of
`[K, X] → [K, Y]`: if `f : X → Y` is a weak homotopy equivalence, then every map `g : K → Y` out of
a space `K` of CW type lifts through `f` up to homotopy
(`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`).

* In the mapping cylinder `M_f`, which contains `X` as the bottom face `incl f` and deformation
  retracts onto `Y`, the relative homotopy groups `π_{n+1}(M_f, X, x)` all vanish
  (`ContinuousMap.IsWeakHomotopyEquivalence.subsingleton_relHomotopyGroup_mappingCylinder`). The
  inclusion `X ↪ M_f` composed with the retraction `M_f → Y` is `f`, so it induces bijections on
  all homotopy groups, and the exact sequence of the pair `(M_f, X)` does the rest
  (`TauCeti.RelHomotopyGroup.subsingleton_of_injective_of_surjective`).
* The compression lemma (`TauCeti.exists_homotopicRel_range_subset_of_relHomotopyGroup`) then
  deforms `K → Y ↪ M_f` into `X`, and retracting back to `Y` gives the lift.
* For a space homotopy equivalent to a CW complex, compose with the inverse of the
  equivalence, lift on the CW complex, and compose back. The inverse law gives the
  required homotopy on the original space.

The same compression gives the injectivity half of Proposition 4.22: if `g₀, g₁ : K → X` become
homotopic after composing with `f`, then they are homotopic
(`ContinuousMap.IsWeakHomotopyEquivalence.homotopic_of_comp_homotopic`). In `M_f` the inclusion
of the bottom face `X` is homotopic to `f` followed by the inclusion of `Y`, so a homotopy
`f ∘ g₀ ≃ f ∘ g₁` gives a homotopy `K × I → M_f` which already maps the two ends `K × {0, 1}` into
`X`. For a CW complex `K` the cylinder `K × I` is a CW complex relative to its two ends
(`TauCeti.relCWComplexCylinder`), so the compression lemma deforms this homotopy into `X` relative
to the ends. Together, the two halves say that composition with `f` is a bijection
`[K, X] → [K, Y]` of homotopy classes
(`ContinuousMap.IsWeakHomotopyEquivalence.comp_homotopic_comp_iff` and
`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`).

Consequently a map `φ : X → Y`, together with `a : A → X` out of a space of CW type and a weak
homotopy equivalence `b : B → Y`, induces a map `A → B` making the square commute up to homotopy
(`ContinuousMap.IsWeakHomotopyEquivalence.lift`), unique up to homotopy and functorial up to
homotopy in `φ` (Hatcher, Proposition 4.18, for arbitrary CW approximations `a` and `b`).

Applied to the identity of `Y`, when `Y` has CW type, the lift is a map `g : Y → X` with
`f ∘ g ≃ id`. By two out of three, `g` is again a weak homotopy equivalence, so when `X` has CW
type `g` has a right homotopy inverse `h` in turn. Then `f ≃ f ∘ g ∘ h ≃ h`, and so
`g ∘ f ≃ g ∘ h ≃ id`. Unlike Hatcher's proof of Theorem 4.5, this argument needs neither a CW
structure on the mapping cylinder nor cellular approximation: the only cell-by-cell argument is
the skeletal induction inside the compression lemma.

## Main declarations

* `ContinuousMap.IsWeakHomotopyEquivalence.subsingleton_relHomotopyGroup_mappingCylinder`: the
  relative homotopy groups of the mapping cylinder of a weak homotopy equivalence vanish.
* `ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`: maps out of spaces of CW
  type lift through a weak homotopy equivalence up to homotopy.
* `ContinuousMap.IsWeakHomotopyEquivalence.homotopic_of_comp_homotopic` and
  `ContinuousMap.IsWeakHomotopyEquivalence.comp_homotopic_comp_iff`: such lifts are unique up to
  homotopy.
* `ContinuousMap.IsWeakHomotopyEquivalence.lift`: the map induced on CW approximations, with
  `ContinuousMap.IsWeakHomotopyEquivalence.comp_lift_homotopic`,
  `ContinuousMap.IsWeakHomotopyEquivalence.homotopic_lift`,
  `ContinuousMap.IsWeakHomotopyEquivalence.lift_id_homotopic` and
  `ContinuousMap.IsWeakHomotopyEquivalence.lift_comp_homotopic`.
* `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`: **Whitehead's theorem**.
* `ContinuousMap.IsWeakHomotopyEquivalence.exists_homotopyEquiv_comp_homotopic`: CW approximations
  are unique up to homotopy equivalence.
* `TauCeti.contractibleSpace_of_subsingleton_homotopyGroup`: a weakly contractible space of CW
  type is contractible.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Theorem 4.5 (Whitehead's theorem), Lemma 4.6 (the compression lemma),
  Proposition 4.18 and the uniqueness of CW approximations stated after it, Proposition 4.22, and
  the corollary after Theorem 4.5 on weakly contractible CW complexes.
-/

public section

universe w

open Set Topology Topology.RelCWComplex
open scoped unitInterval

namespace ContinuousMap.IsWeakHomotopyEquivalence

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {f : C(X, Y)}

/-- The relative homotopy groups `π_{n+1}(M_f, X, x)` of the mapping cylinder of a weak homotopy
equivalence `f : X → Y`, relative to its bottom face `X`, are trivial at every basepoint of the
bottom face. -/
theorem subsingleton_relHomotopyGroup_mappingCylinder (hf : f.IsWeakHomotopyEquivalence)
    (N : Type w) [Finite N] (b : range (TauCeti.MappingCylinder.incl f)) :
    Subsingleton (TauCeti.RelHomotopyGroup N
      ⟨TopPair.ofSubset (X := TopCat.of (TauCeti.MappingCylinder f))
        (range (TauCeti.MappingCylinder.incl f)), b⟩) := by
  open TauCeti.MappingCylinder in
  let ψ := inclHomeomorph f
  -- The inclusion `ι` of the bottom face, composed with `ψ : X ≃ₜ range (incl f)` and with the
  -- projection `M_f → Y`, is `f`; the outer two maps are homotopy equivalences.
  let ι := ContinuousMap.subtypeVal (range (incl f))
  -- By two out of three `ι ∘ ψ` is a weak homotopy equivalence, hence so is `ι = ι ∘ ψ ∘ ψ⁻¹`.
  have hιψ : (ι.comp (ψ : C(X, range (incl f)))).IsWeakHomotopyEquivalence :=
    (homotopyEquiv_toFun (f := f) ▸ (homotopyEquiv f).isWeakHomotopyEquivalence).of_postcomp
      (by rwa [proj_comp_subtypeVal_comp_inclHomeomorph])
  have hι : ι.IsWeakHomotopyEquivalence := by
    have h : (ι.comp (ψ : C(X, range (incl f)))).comp (ψ.symm : C(range (incl f), X)) = ι := by
      ext m
      exact congrArg ι (ψ.apply_symm_apply m)
    rw [← h]
    exact hιψ.comp ψ.symm.toHomotopyEquiv.isWeakHomotopyEquivalence
  exact TauCeti.RelHomotopyGroup.subsingleton_of_injective_of_surjective
    (hι.map_bijective N b).injective (hι.map_bijective (Option N) b).surjective

variable {X' : Type*} [TopologicalSpace X'] [T2Space X'] {C : Set X'} [CWComplex C]

/-- **Maps out of a CW complex lift through a weak homotopy equivalence up to homotopy**
(the surjectivity half of Hatcher, Proposition 4.22). If `f : X → Y` is a weak homotopy
equivalence and `C` is a CW complex, then every map `g : C → Y` is homotopic to `f ∘ g'` for some
`g' : C → X`. -/
private theorem exists_comp_homotopic_cwComplex (hf : f.IsWeakHomotopyEquivalence) (g : C(C, Y)) :
    ∃ g' : C(C, X), (f.comp g').Homotopic g := by
  open TauCeti TauCeti.MappingCylinder in
  -- Compress `mkBase f ∘ g : C → M_f` into the bottom face `range (incl f)`, to which every point
  -- of the mapping cylinder is joined by a path.
  obtain ⟨g₁, hg₁, hrange⟩ := exists_homotopicRel_range_subset_of_relHomotopyGroup
    (C := C) (D := ∅) (Y := TopCat.of (MappingCylinder f)) (B := range (incl f))
    (fun _ ↦ exists_mem_range_incl_joined hf.exists_joined)
    (fun _ _ b ↦ hf.subsingleton_relHomotopyGroup_mappingCylinder _ b) ((mkBase f).comp g)
    (fun _ hx ↦ absurd hx (notMem_empty _))
  -- Read the compressed map in `X` through the homeomorphism `X ≃ₜ range (incl f)`.
  let ψ := inclHomeomorph f
  let g' : C(C, X) := (ψ.symm : C(range (incl f), X)).comp
    ⟨fun c ↦ (⟨g₁ c, hrange (mem_range_self c)⟩ : range (incl f)), g₁.continuous.subtype_mk _⟩
  have hg' : (incl f).comp g' = g₁ := by
    ext c
    rw [ContinuousMap.comp_apply, ← inclHomeomorph_apply_coe]
    exact congrArg Subtype.val (ψ.apply_symm_apply ⟨g₁ c, hrange (mem_range_self c)⟩)
  -- Then `f ∘ g' = proj ∘ incl ∘ g' = proj ∘ g₁ ≃ proj ∘ mkBase ∘ g = g`.
  refine ⟨g', ?_⟩
  have h := (ContinuousMap.Homotopic.refl (proj f)).comp hg₁.homotopic.symm
  rwa [← comp_assoc, proj_comp_mkBase, id_comp, ← hg', ← comp_assoc, proj_comp_incl] at h

/-- Maps out of a CW complex that become homotopic after composition with a weak homotopy
equivalence are homotopic (the injectivity half of Hatcher, Proposition 4.22, for a CW complex). -/
private theorem homotopic_of_comp_homotopic_cwComplex (hf : f.IsWeakHomotopyEquivalence)
    {g₀ g₁ : C(C, X)} (h : (f.comp g₀).Homotopic (f.comp g₁)) : g₀.Homotopic g₁ := by
  open TauCeti TauCeti.MappingCylinder in
  -- In `M_f`, `incl ∘ gᵢ ≃ mkBase ∘ f ∘ gᵢ` by the deformation onto the base.
  have hM : ((incl f).comp g₀).Homotopic ((incl f).comp g₁) := by
    have h₀ := (incl_homotopic_mkBase_comp (f := f)).comp (ContinuousMap.Homotopic.refl g₀)
    have h₁ := (incl_homotopic_mkBase_comp (f := f)).comp (ContinuousMap.Homotopic.refl g₁)
    rw [comp_assoc] at h₀ h₁
    exact h₀.trans (((ContinuousMap.Homotopic.refl (mkBase f)).comp h).trans h₁.symm)
  obtain ⟨F⟩ := hM
  -- Read `F` on the cylinder `C × I`, a CW complex relative to its two ends `C × {0, 1}`, which
  -- `F` maps into the bottom face; compress it into the bottom face relative to the ends.
  let _ := relCWComplexCylinder C (∅ : Set X')
  let Φ : C(↥(C ×ˢ (univ : Set I)), TopCat.of (MappingCylinder f)) :=
    ⟨fun p ↦ F (p.1.2, ⟨p.1.1, p.2.1⟩), by fun_prop⟩
  have hΦ : MapsTo Φ {p | (p : X' × I) ∈ C ×ˢ {0, 1} ∪ ∅ ×ˢ univ} (range (incl f)) := by
    rintro ⟨⟨x, t⟩, hx, -⟩ (⟨-, (rfl | rfl)⟩ | ⟨⟨⟩, -⟩)
    · exact ⟨g₀ ⟨x, hx⟩, (F.apply_zero _).symm⟩
    · exact ⟨g₁ ⟨x, hx⟩, (F.apply_one _).symm⟩
  obtain ⟨Φ', ⟨H⟩, hrange⟩ := exists_homotopicRel_range_subset_of_relHomotopyGroup
    (C := C ×ˢ (univ : Set I)) (D := C ×ˢ {0, 1} ∪ ∅ ×ˢ univ)
    (Y := TopCat.of (MappingCylinder f)) (B := range (incl f)) (fun h ↦ isEmptyElim h.some)
    (fun _ _ b ↦ hf.subsingleton_relHomotopyGroup_mappingCylinder _ b) Φ hΦ
  -- The compressed homotopy agrees with `F` on the ends; read it in `X` through
  -- `X ≃ₜ range (incl f)`.
  let ψ := inclHomeomorph f
  let κ : C(I × C, ↥(C ×ˢ (univ : Set I))) :=
    ⟨fun q ↦ ⟨(q.2, q.1), q.2.2, mem_univ _⟩, by fun_prop⟩
  have hend (c : C) (t : I) (ht : t ∈ ({0, 1} : Set I)) : Φ' (κ (t, c)) = F (t, c) :=
    (H.fst_eq_snd (Or.inl ⟨c.2, ht⟩)).symm
  refine ⟨⟨(ψ.symm : C(range (incl f), X)).comp
    ((⟨fun p ↦ ⟨Φ' p, hrange (mem_range_self p)⟩, Φ'.continuous.subtype_mk _⟩ :
      C(↥(C ×ˢ (univ : Set I)), range (incl f))).comp κ), fun c ↦ ?_, fun c ↦ ?_⟩⟩
  · refine ψ.symm_apply_eq.2 (Subtype.ext ?_)
    exact (hend c 0 (Or.inl rfl)).trans ((F.apply_zero c).trans (inclHomeomorph_apply_coe _).symm)
  · refine ψ.symm_apply_eq.2 (Subtype.ext ?_)
    exact (hend c 1 (Or.inr rfl)).trans ((F.apply_one c).trans (inclHomeomorph_apply_coe _).symm)

variable {K : Type*} [TopologicalSpace K] [hK : TauCeti.CWType K]

/-- Maps out of a space of CW type lift through a weak homotopy equivalence up to homotopy
(the surjectivity half of Hatcher, Proposition 4.22). -/
theorem exists_comp_homotopic (hf : f.IsWeakHomotopyEquivalence) (g : C(K, Y)) :
    ∃ g' : C(K, X), (f.comp g').Homotopic g := by
  obtain ⟨Z, _, _, C, _, ⟨e⟩⟩ := hK.exists_homotopyEquiv
  obtain ⟨g', hg'⟩ := hf.exists_comp_homotopic_cwComplex (g.comp e.invFun)
  refine ⟨g'.comp e.toFun, ?_⟩
  have h := hg'.comp (ContinuousMap.Homotopic.refl e.toFun)
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc] at h
  exact h.trans (by simpa only [ContinuousMap.comp_id] using
    (ContinuousMap.Homotopic.refl g).comp e.left_inv)

/-- **Lifts through a weak homotopy equivalence are unique up to homotopy** (the injectivity half
of Hatcher, Proposition 4.22). If `f : X → Y` is a weak homotopy equivalence and `K` has CW type,
then two maps `g₀, g₁ : K → X` are homotopic as soon as `f ∘ g₀` and `f ∘ g₁` are. -/
theorem homotopic_of_comp_homotopic (hf : f.IsWeakHomotopyEquivalence) {g₀ g₁ : C(K, X)}
    (h : (f.comp g₀).Homotopic (f.comp g₁)) : g₀.Homotopic g₁ := by
  obtain ⟨Z, _, _, C, _, ⟨e⟩⟩ := hK.exists_homotopyEquiv
  -- Transport to the CW complex `C` along `e : K ≃ₕ C`, and back.
  have he := h.comp (ContinuousMap.Homotopic.refl e.invFun)
  rw [comp_assoc, comp_assoc] at he
  have hC := hf.homotopic_of_comp_homotopic_cwComplex he
  have h₀ := (ContinuousMap.Homotopic.refl g₀).comp e.left_inv
  have h₁ := (ContinuousMap.Homotopic.refl g₁).comp e.left_inv
  rw [comp_id, ← comp_assoc] at h₀ h₁
  exact h₀.symm.trans ((hC.comp (ContinuousMap.Homotopic.refl e.toFun)).trans h₁)

/-- **Composition with a weak homotopy equivalence is injective on homotopy classes** of maps
out of a space of CW type (Hatcher, Proposition 4.22): `f ∘ g₀ ≃ f ∘ g₁` exactly when
`g₀ ≃ g₁`. Surjectivity is `ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`. -/
@[simp]
theorem comp_homotopic_comp_iff (hf : f.IsWeakHomotopyEquivalence) {g₀ g₁ : C(K, X)} :
    (f.comp g₀).Homotopic (f.comp g₁) ↔ g₀.Homotopic g₁ :=
  ⟨hf.homotopic_of_comp_homotopic, (ContinuousMap.Homotopic.refl f).comp⟩

variable [TauCeti.CWType X] [TauCeti.CWType Y]

/-- **Whitehead's theorem** (Hatcher, Theorem 4.5). A weak homotopy equivalence `f` between spaces
of CW type is a homotopy equivalence. This is the homotopy equivalence whose forward map is `f`
itself (`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv_toFun`); its homotopy inverse is a
lift of the identity through `f` given by
`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`. -/
noncomputable def homotopyEquiv (hf : f.IsWeakHomotopyEquivalence) : X ≃ₕ Y :=
  have hfg := (hf.exists_comp_homotopic (ContinuousMap.id Y)).choose_spec
  { toFun := f
    invFun := (hf.exists_comp_homotopic (ContinuousMap.id Y)).choose
    left_inv := by
      -- The homotopy inverse `g` is a weak homotopy equivalence by two out of three, so it has a
      -- right homotopy inverse `h`; then `f ≃ f ∘ g ∘ h ≃ h` and `g ∘ f ≃ g ∘ h ≃ id`.
      set g := (hf.exists_comp_homotopic (ContinuousMap.id Y)).choose
      obtain ⟨h, hgh⟩ := (hf.of_postcomp (IsWeakHomotopyEquivalence.id.of_homotopic hfg.symm))
        |>.exists_comp_homotopic (ContinuousMap.id X)
      have hfh : f.Homotopic h := by
        have := (ContinuousMap.Homotopic.refl f).comp hgh.symm
        have hfgh := hfg.comp (ContinuousMap.Homotopic.refl h)
        rw [comp_id, ← comp_assoc] at this
        rw [id_comp] at hfgh
        exact this.trans hfgh
      exact ((ContinuousMap.Homotopic.refl g).comp hfh).trans hgh
    right_inv := hfg }

@[simp]
theorem homotopyEquiv_toFun (hf : f.IsWeakHomotopyEquivalence) : hf.homotopyEquiv.toFun = f :=
  (rfl)

end ContinuousMap.IsWeakHomotopyEquivalence

namespace ContinuousMap.IsWeakHomotopyEquivalence

variable {A A' B D X Y Z : Type*} [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B]
  [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TauCeti.CWType A]

/-- **CW approximations are unique up to homotopy equivalence** (Hatcher, after Proposition 4.18).
If `a : A → X` and `a' : A' → X` are weak homotopy equivalences out of spaces of CW type, there is
a homotopy equivalence `e : A ≃ₕ A'` with `a' ∘ e ≃ a`. -/
theorem exists_homotopyEquiv_comp_homotopic [TauCeti.CWType A'] {a : C(A, X)} {a' : C(A', X)}
    (ha : a.IsWeakHomotopyEquivalence) (ha' : a'.IsWeakHomotopyEquivalence) :
    ∃ e : A ≃ₕ A', (a'.comp e.toFun).Homotopic a := by
  obtain ⟨g, hg⟩ := ha'.exists_comp_homotopic a
  -- `a' ∘ g ≃ a` is a weak homotopy equivalence, so `g` is one by two out of three.
  have hg' : g.IsWeakHomotopyEquivalence := ha'.of_postcomp (ha.of_homotopic hg.symm)
  exact ⟨hg'.homotopyEquiv, by rwa [homotopyEquiv_toFun]⟩

/-- The map `A → B` induced by `φ : X → Y` between spaces over `X` and `Y`: given `a : A → X` with
`A` of CW type and a weak homotopy equivalence `b : B → Y`, a lift of `φ ∘ a` through `b`, so that
the square of `φ` and the lift with `a` and `b` commutes up to homotopy
(`ContinuousMap.IsWeakHomotopyEquivalence.comp_lift_homotopic`). It is determined up to homotopy
by this property (`ContinuousMap.IsWeakHomotopyEquivalence.homotopic_lift`). -/
noncomputable def lift {b : C(B, Y)} (hb : b.IsWeakHomotopyEquivalence) (a : C(A, X))
    (φ : C(X, Y)) : C(A, B) :=
  (hb.exists_comp_homotopic (φ.comp a)).choose

/-- The square of `φ` and its lift commutes up to homotopy: `b ∘ lift ≃ φ ∘ a`. -/
theorem comp_lift_homotopic {b : C(B, Y)} (hb : b.IsWeakHomotopyEquivalence) (a : C(A, X))
    (φ : C(X, Y)) : (b.comp (hb.lift a φ)).Homotopic (φ.comp a) :=
  (hb.exists_comp_homotopic (φ.comp a)).choose_spec

/-- **Uniqueness of the lift.** Every map `ψ : A → B` with `b ∘ ψ ≃ φ ∘ a` is homotopic to the
lift of `φ`. -/
theorem homotopic_lift {b : C(B, Y)} (hb : b.IsWeakHomotopyEquivalence) {a : C(A, X)}
    {φ : C(X, Y)} {ψ : C(A, B)} (hψ : (b.comp ψ).Homotopic (φ.comp a)) :
    ψ.Homotopic (hb.lift a φ) :=
  hb.homotopic_of_comp_homotopic (hψ.trans (hb.comp_lift_homotopic a φ).symm)

/-- Homotopic maps have homotopic lifts. -/
theorem lift_homotopic_of_homotopic {b : C(B, Y)} (hb : b.IsWeakHomotopyEquivalence)
    (a : C(A, X)) {φ φ' : C(X, Y)} (h : φ.Homotopic φ') :
    (hb.lift a φ).Homotopic (hb.lift a φ') :=
  hb.homotopic_lift ((hb.comp_lift_homotopic a φ).trans (h.comp (Homotopic.refl _)))

/-- **The identity lifts to the identity up to homotopy.** -/
theorem lift_id_homotopic {a : C(A, X)} (ha : a.IsWeakHomotopyEquivalence) :
    (ha.lift a (ContinuousMap.id X)).Homotopic (ContinuousMap.id A) :=
  (ha.homotopic_lift (φ := ContinuousMap.id X) (ψ := ContinuousMap.id A)
    (by rw [comp_id, id_comp])).symm

/-- **Composites lift to composites up to homotopy**: the lift of `χ ∘ φ` is homotopic to the
composite of the lifts of `φ` and `χ`. -/
theorem lift_comp_homotopic [TauCeti.CWType B] {b : C(B, Y)} {d : C(D, Z)}
    (hb : b.IsWeakHomotopyEquivalence) (hd : d.IsWeakHomotopyEquivalence) (a : C(A, X))
    (χ : C(Y, Z)) (φ : C(X, Y)) :
    (hd.lift a (χ.comp φ)).Homotopic ((hd.lift b χ).comp (hb.lift a φ)) := by
  refine (hd.homotopic_lift ?_).symm
  -- `d ∘ lift χ ∘ lift φ ≃ χ ∘ b ∘ lift φ ≃ χ ∘ φ ∘ a`.
  have h₁ := (hd.comp_lift_homotopic b χ).comp (Homotopic.refl (hb.lift a φ))
  have h₂ := (Homotopic.refl χ).comp (hb.comp_lift_homotopic a φ)
  rw [comp_assoc] at h₁ ⊢
  exact h₁.trans h₂

/-- **The lift of `φ` is a weak homotopy equivalence exactly when `φ` is**, when `a` is also a
weak homotopy equivalence. -/
@[simp]
theorem isWeakHomotopyEquivalence_lift_iff {a : C(A, X)} {b : C(B, Y)}
    (ha : a.IsWeakHomotopyEquivalence) (hb : b.IsWeakHomotopyEquivalence) {φ : C(X, Y)} :
    (hb.lift a φ).IsWeakHomotopyEquivalence ↔ φ.IsWeakHomotopyEquivalence := by
  have h := hb.comp_lift_homotopic a φ
  refine ⟨fun hψ ↦ ha.of_precomp ((hb.comp hψ).of_homotopic h), fun hφ ↦ ?_⟩
  exact hb.of_postcomp ((hφ.comp ha).of_homotopic h.symm)

end ContinuousMap.IsWeakHomotopyEquivalence

/-- Between spaces of CW type, a map is a weak homotopy equivalence exactly when it is
the forward map of a homotopy equivalence. -/
theorem ContinuousMap.isWeakHomotopyEquivalence_iff_exists_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TauCeti.CWType X] [TauCeti.CWType Y] (f : C(X, Y)) :
    f.IsWeakHomotopyEquivalence ↔ ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f :=
  ⟨fun hf ↦ ⟨hf.homotopyEquiv, hf.homotopyEquiv_toFun⟩,
    fun ⟨e, he⟩ ↦ he ▸ e.isWeakHomotopyEquivalence⟩

/-- **A weakly contractible space of CW type is contractible** (Hatcher, the corollary after
Theorem 4.5). A path-connected space of CW type whose homotopy groups in every positive dimension
vanish at one base point is contractible: its map to a point is a weak homotopy equivalence, hence
a homotopy equivalence by Whitehead's theorem. -/
theorem TauCeti.contractibleSpace_of_subsingleton_homotopyGroup {X : Type w} [TopologicalSpace X]
    [TauCeti.CWType X] [PathConnectedSpace X] (x : X)
    (h : ∀ n : ℕ, Subsingleton (π_ (n + 1) X x)) : ContractibleSpace X := by
  let f : C(X, PUnit.{w + 1}) := ContinuousMap.const X PUnit.unit
  have hf : f.IsWeakHomotopyEquivalence := by
    refine (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective x).2 fun n ↦ ?_
    have : Subsingleton (π_ n X x) := by
      cases n with
      | zero => exact HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
      | succ n => exact h n
    exact Function.bijective_of_subsingleton' _
  exact hf.homotopyEquiv.contractibleSpace
