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

Applied to the identity of `Y`, when `Y` has CW type, the lift is a map `g : Y → X` with
`f ∘ g ≃ id`. By two out of three, `g` is again a weak homotopy equivalence, so when `X` has CW
type `g` has a right homotopy inverse `h` in turn. Then `f ≃ f ∘ g ∘ h ≃ h`, and so
`g ∘ f ≃ g ∘ h ≃ id`. Unlike Hatcher's proof of Theorem 4.5, this argument needs neither a CW
structure on the mapping cylinder nor cellular approximation: the only cell-by-cell argument is
the skeletal induction inside the compression lemma.

The injectivity half of Proposition 4.22 compresses homotopies in the same way: if `f ∘ g₀ ≃ f ∘ g₁`
for maps `g₀ g₁ : K → X`, then `g₀ ≃ g₁`
(`ContinuousMap.IsWeakHomotopyEquivalence.homotopic_of_comp_homotopic`). In `M_f` the maps
`incl ∘ gᵢ` are homotopic to `mkBase ∘ f ∘ gᵢ`, so to each other. For a CW complex `C`, a homotopy
between them is a map out of the cylinder `C × I`, which is a CW complex relative to its two ends
(`TauCeti.relCWComplexCylinder`), and the ends go into the bottom face. Compressing it into the
bottom face relative to the ends gives a homotopy from `g₀` to `g₁`. So `f` induces a bijection
`[K, X] → [K, Y]` (`ContinuousMap.IsWeakHomotopyEquivalence.comp_homotopic_comp_iff`). With
Whitehead's theorem this shows that CW approximations of a space are unique up to homotopy
equivalence (`ContinuousMap.IsWeakHomotopyEquivalence.exists_homotopyEquiv_comp_homotopic`).

## Main declarations

* `ContinuousMap.IsWeakHomotopyEquivalence.subsingleton_relHomotopyGroup_mappingCylinder`: the
  relative homotopy groups of the mapping cylinder of a weak homotopy equivalence vanish.
* `ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`: maps out of spaces of CW
  type lift through a weak homotopy equivalence up to homotopy.
* `ContinuousMap.IsWeakHomotopyEquivalence.homotopic_of_comp_homotopic`,
  `ContinuousMap.IsWeakHomotopyEquivalence.comp_homotopic_comp_iff`: maps out of spaces of CW type
  are homotopic when their composites with a weak homotopy equivalence are.
* `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`: **Whitehead's theorem**.
* `ContinuousMap.IsWeakHomotopyEquivalence.exists_homotopyEquiv_comp_homotopic`: CW
  approximations are unique up to homotopy equivalence.
* `TauCeti.contractibleSpace_of_subsingleton_homotopyGroup`: a weakly contractible space of CW
  type is contractible.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Theorem 4.5 (Whitehead's theorem), Lemma 4.6 (the compression lemma),
  Corollary 4.19 (uniqueness of CW approximations), Proposition 4.22, and the corollary after
  Theorem 4.5 on weakly contractible CW complexes.
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

/-- **Maps out of a CW complex that become homotopic after a weak homotopy equivalence are
homotopic** (the injectivity half of Hatcher, Proposition 4.22). If `f : X → Y` is a weak homotopy
equivalence and `C` is a CW complex, then two maps `g₀ g₁ : C → X` with `f ∘ g₀ ≃ f ∘ g₁` are
homotopic. -/
private theorem homotopic_of_comp_homotopic_cwComplex (hf : f.IsWeakHomotopyEquivalence)
    {g₀ g₁ : C(C, X)} (h : (f.comp g₀).Homotopic (f.comp g₁)) : g₀.Homotopic g₁ := by
  open TauCeti TauCeti.MappingCylinder in
  -- In the mapping cylinder, `incl ∘ gᵢ ≃ mkBase ∘ proj ∘ incl ∘ gᵢ = mkBase ∘ f ∘ gᵢ`, so
  -- `incl ∘ g₀` and `incl ∘ g₁` are homotopic through `mkBase ∘ (f ∘ g₀ ≃ f ∘ g₁)`.
  have hd : ((mkBase f).comp (proj f)).Homotopic (ContinuousMap.id _) :=
    ⟨(deformation f).toHomotopy.symm⟩
  have hincl (g : C(C, X)) : ((mkBase f).comp (f.comp g)).Homotopic ((incl f).comp g) := by
    have h := hd.comp (ContinuousMap.Homotopic.refl ((incl f).comp g))
    rwa [id_comp, comp_assoc, ← comp_assoc (proj f), proj_comp_incl] at h
  obtain ⟨H⟩ := (hincl g₀).symm.trans
    (((ContinuousMap.Homotopic.refl (mkBase f)).comp h).trans (hincl g₁))
  -- `H` is a map out of the cylinder `C × I`, a CW complex relative to its two ends, which `H`
  -- sends into the bottom face. Compress it into the bottom face relative to the ends.
  let := relCWComplexCylinder C ∅
  let F : C(C ×ˢ (univ : Set I), TopCat.of (MappingCylinder f)) :=
    ⟨fun p ↦ H (p.1.2, ⟨p.1.1, p.2.1⟩),
      H.continuous.comp ((continuous_snd.comp continuous_subtype_val).prodMk
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _))⟩
  have hbase : MapsTo F {p | (p : X' × I) ∈ C ×ˢ ({0, 1} : Set I) ∪ (∅ : Set X') ×ˢ univ}
      (range (incl f)) := by
    rintro ⟨⟨c, t⟩, hc, _⟩ hp
    simp only [mem_ofPred_eq, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff,
      mem_empty_iff_false, false_and, or_false] at hp
    obtain ⟨-, rfl | rfl⟩ := hp
    · exact ⟨g₀ ⟨c, hc⟩, (H.apply_zero ⟨c, hc⟩).symm⟩
    · exact ⟨g₁ ⟨c, hc⟩, (H.apply_one ⟨c, hc⟩).symm⟩
  obtain ⟨F', hF', hrange⟩ := exists_homotopicRel_range_subset_of_relHomotopyGroup
    (Y := TopCat.of (MappingCylinder f)) (B := range (incl f))
    (fun h₀ ↦ isEmptyElim h₀.some)
    (fun _ _ b ↦ hf.subsingleton_relHomotopyGroup_mappingCylinder _ b) F hbase
  -- Read the compressed homotopy in `X` through the homeomorphism `X ≃ₜ range (incl f)`; on the
  -- two ends it agrees with `H`, which is `incl ∘ g₀` and `incl ∘ g₁` there.
  let ψ := inclHomeomorph f
  have hF'end (t : I) (ht : t ∈ ({0, 1} : Set I)) (c : C) :
      F' ⟨((c : X'), t), c.2, mem_univ t⟩ = H (t, c) :=
    (hF'.fst_eq_snd (Or.inl ⟨c.2, ht⟩)).symm
  have hψ (x : X) (hx : incl f x ∈ range (incl f)) : ψ.symm ⟨incl f x, hx⟩ = x :=
    ψ.symm_apply_eq.2 (Subtype.ext (inclHomeomorph_apply_coe x).symm)
  refine ⟨{ toFun q := ψ.symm ⟨F' ⟨((q.2 : X'), q.1), q.2.2, mem_univ _⟩, hrange (mem_range_self _)⟩
            continuous_toFun := ψ.symm.continuous.comp (Continuous.subtype_mk (F'.continuous.comp
              (((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst).subtype_mk _))
                _)
            map_zero_left c := ?_
            map_one_left c := ?_ }⟩
  · simp_rw [hF'end 0 (mem_insert 0 _) c, H.apply_zero, ContinuousMap.comp_apply]
    exact hψ _ _
  · simp_rw [hF'end 1 (mem_insert_of_mem _ rfl) c, H.apply_one, ContinuousMap.comp_apply]
    exact hψ _ _

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

/-- Maps out of a space of CW type that become homotopic after composition with a weak homotopy
equivalence are homotopic (the injectivity half of Hatcher, Proposition 4.22). -/
theorem homotopic_of_comp_homotopic (hf : f.IsWeakHomotopyEquivalence) {g₀ g₁ : C(K, X)}
    (h : (f.comp g₀).Homotopic (f.comp g₁)) : g₀.Homotopic g₁ := by
  obtain ⟨Z, _, _, C, _, ⟨e⟩⟩ := hK.exists_homotopyEquiv
  -- Transfer to the CW complex `C` through `e⁻¹`, and back through `gᵢ ≃ gᵢ ∘ e⁻¹ ∘ e`.
  have h' : (g₀.comp e.invFun).Homotopic (g₁.comp e.invFun) :=
    hf.homotopic_of_comp_homotopic_cwComplex <| by
      simpa only [comp_assoc] using h.comp (ContinuousMap.Homotopic.refl e.invFun)
  have hback (g : C(K, X)) : ((g.comp e.invFun).comp e.toFun).Homotopic g := by
    simpa only [comp_assoc, comp_id] using (ContinuousMap.Homotopic.refl g).comp e.left_inv
  exact (hback g₀).symm.trans ((h'.comp (ContinuousMap.Homotopic.refl e.toFun)).trans (hback g₁))

/-- **A weak homotopy equivalence `f : X → Y` induces a bijection `[K, X] → [K, Y]` of homotopy
classes of maps out of a space `K` of CW type** (Hatcher, Proposition 4.22): two maps `K → X` are
homotopic exactly when their composites with `f` are, and every map `K → Y` is homotopic to such a
composite (`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`). -/
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

omit [TauCeti.CWType Y] in
/-- **CW approximations are unique up to homotopy equivalence** (Hatcher, Corollary 4.19). If
`f : X → Y` and `g : K → Y` are weak homotopy equivalences out of spaces of CW type, then there is a
homotopy equivalence `e : K ≃ₕ X` with `f ∘ e ≃ g`. -/
theorem exists_homotopyEquiv_comp_homotopic (hf : f.IsWeakHomotopyEquivalence) {g : C(K, Y)}
    (hg : g.IsWeakHomotopyEquivalence) :
    ∃ e : K ≃ₕ X, (f.comp e.toFun).Homotopic g := by
  obtain ⟨g', hg'⟩ := hf.exists_comp_homotopic g
  -- The lift `g'` is a weak homotopy equivalence by two out of three, hence one by Whitehead.
  have hw : g'.IsWeakHomotopyEquivalence := hf.of_postcomp (hg.of_homotopic hg'.symm)
  exact ⟨hw.homotopyEquiv, hg'⟩

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
