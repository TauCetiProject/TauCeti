/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.MapFiber

/-!
# Smooth fibre bundles given by their total space

Let `proj : P → B` be a map between manifolds, and let `A` be an atlas of trivializations of
`proj` (`TauCeti.MapFiber.Atlas`), whose trivializations are `C^n` diffeomorphisms from open sets
`proj⁻¹ U` of `P` onto the open sets `U × F` of the product manifold `B × F`
(`TauCeti.MapFiber.Atlas.IsContMDiff`). Then the fibre bundle of `proj` built from `A` is a `C^n`
fibre bundle (`TauCeti.MapFiber.Atlas.contMDiffFiberBundle`), and its total space, charted through
the fibre by `TauCeti.ManifoldTotalSpace`, is `C^n` diffeomorphic to `P` by `⟨b, p⟩ ↦ p`
(`TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph`). This diffeomorphism carries the bundle
projection to `proj`, and a right action of a group `G` on `P` preserving the fibres of `proj` to
the fibrewise action on the total space. So a bundle given by its total space `P`, as in classical
differential geometry, is a `C^n` fibre bundle in the sense of `TauCeti.ContMDiffFiberBundle`, and
the two smooth structures on its total space agree. When `G` is the model fibre and the
trivializations are equivariant, it is a principal bundle (`TauCeti.MapFiber.Atlas.principalBundle`)
presented by `P`.

Transported along this diffeomorphism, smooth descent along the bundle projection becomes descent
along `proj` itself: for a nonempty model fibre, a map out of `B` is `C^n` exactly when its
composite with `proj` is (`TauCeti.MapFiber.Atlas.IsContMDiff.contMDiff_comp_iff`), and a `C^n` map
on `P` that is constant on the fibres of `proj` is the composite with `proj` of a unique `C^n` map
on `B` (`TauCeti.MapFiber.Atlas.IsContMDiff.existsUnique_contMDiff_comp_eq`). In the principal
case, the fibres are the orbits of `G`, so this applies to invariant maps
(`TauCeti.MapFiber.Atlas.IsContMDiff.existsUnique_contMDiff_comp_eq_of_smul`).

## Main definitions

* `TauCeti.MapFiber.Atlas.IsContMDiff`: the trivializations of an atlas of `proj` are `C^n`
  diffeomorphisms onto their images.
* `TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph`: the charted total space of the fibres of `proj`
  is `C^n` diffeomorphic to `P`.

## Main results

* `TauCeti.MapFiber.Atlas.IsContMDiff.contMDiff_proj`: `proj` is `C^n`.
* `TauCeti.MapFiber.Atlas.contMDiffFiberBundle`: the fibres of `proj` form a `C^n` fibre bundle.
* `TauCeti.MapFiber.Atlas.proj_totalSpaceDiffeomorph`: the diffeomorphism lies over `B`.
* `TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph_smul`: it is equivariant for a fibre-preserving
  action on `P`.
* `TauCeti.MapFiber.Atlas.IsContMDiff.contMDiff_comp_iff` and
  `TauCeti.MapFiber.Atlas.IsContMDiff.existsUnique_contMDiff_comp_eq`: smooth descent along
  `proj`.
* `TauCeti.MapFiber.Atlas.IsContMDiff.existsUnique_contMDiff_comp_eq_of_smul`: an invariant
  smooth map on the total space of a principal bundle descends to the base.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (differentiable principal bundles given by their total space).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §9.1 and §10.2.
-/

public section

open Bundle Set Filter Function MulOpposite
open scoped Manifold Topology ContDiff

namespace TauCeti.MapFiber.Atlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] {HP : Type*} [TopologicalSpace HP]
  {IP : ModelWithCorners 𝕜 EP HP} {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {proj : P → B}

variable (n IB IF IP) in
/-- An atlas of a map `proj : P → B` between manifolds is `C^n` when each of its trivializations is
a `C^n` diffeomorphism from its source, an open set of `P`, onto its target, an open set of the
product manifold `B × F`. -/
structure IsContMDiff (A : Atlas F proj) : Prop where
  /-- Each trivialization of the atlas is `C^n` on its source. -/
  contMDiffOn_trivAt : ∀ b, ContMDiffOn IP (IB.prod IF) n (A.trivAt b) (A.trivAt b).source
  /-- The inverse of each trivialization of the atlas is `C^n` on its target. -/
  contMDiffOn_trivAt_symm : ∀ b,
    ContMDiffOn (IB.prod IF) IP n (A.trivAt b).toOpenPartialHomeomorph.symm (A.trivAt b).target

variable {A : Atlas F proj}

/-- The map `proj` of a `C^n` atlas is `C^n`: near each point it is the first coordinate of a
trivialization. -/
theorem IsContMDiff.contMDiff_proj (hA : A.IsContMDiff n IB IF IP) : ContMDiff IP IB n proj :=
  fun p ↦
    let e := A.trivAt (proj p)
    have hp : p ∈ e.source := e.mem_source.2 (A.mem_baseSet_trivAt (proj p))
    (contMDiffAt_fst.comp p ((hA.contMDiffOn_trivAt _).contMDiffAt
      (e.open_source.mem_nhds hp))).congr_of_eventuallyEq
      (e.coe_fst_eventuallyEq_proj hp).symm

/-- **The fibres of a map with a `C^n` atlas form a `C^n` fibre bundle.** Its coordinate changes
are those of the trivializations of the atlas. -/
theorem contMDiffFiberBundle (hA : A.IsContMDiff n IB IF IP) :
    letI := A.fiberBundle
    ContMDiffFiberBundle n F (MapFiber proj) IB IF := by
  let := A.fiberBundle
  refine ⟨fun e e' he he' ↦ ?_⟩
  obtain ⟨a, rfl⟩ := (A.mem_trivializationAtlas_iff e).1 he.out
  obtain ⟨c, rfl⟩ := (A.mem_trivializationAtlas_iff e').1 he'.out
  rw [Bundle.Trivialization.toMapFiber_coordChange]
  -- The coordinate change from `a` to `c` reads `(b, v) ↦ (trivAt c ((trivAt a)⁻¹ (b, v))).2`.
  refine (contMDiff_snd.comp_contMDiffOn (hA.contMDiffOn_trivAt c) |>.comp
    ((hA.contMDiffOn_trivAt_symm a).mono fun y hy ↦ ?_) fun y hy ↦ ?_).congr fun y _ ↦ rfl
  · simp only [Bundle.Trivialization.toMapFiber_baseSet] at hy
    exact (A.trivAt a).mem_target.2 hy.1.1
  · simp only [Bundle.Trivialization.toMapFiber_baseSet] at hy
    rw [mem_preimage, (A.trivAt c).mem_source,
      (A.trivAt a).proj_symm_apply ((A.trivAt a).mem_target.2 hy.1.1)]
    exact hy.1.2

/-- For a `C^n` atlas of `proj`, the map `⟨b, p⟩ ↦ p` from the charted total space of the fibres
to `P` is `C^n`: near a point over `b` it is the inverse of `trivAt b` after `trivAt b`. -/
private theorem contMDiff_totalSpaceHomeomorph (hA : A.IsContMDiff n IB IF IP) :
    letI := A.fiberBundle
    ContMDiff (IB.prod IF) IP n fun x : ManifoldTotalSpace F (MapFiber proj) ↦
      totalSpaceHomeomorph F proj ((ManifoldTotalSpace.homeomorph F (MapFiber proj)).symm x) := by
  let := A.fiberBundle
  have := A.contMDiffFiberBundle hA
  intro x
  obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F (MapFiber proj)).surjective x
  let t := A.trivAt z.proj
  have : MemTrivializationAtlas t.toMapFiber :=
    ⟨(A.mem_trivializationAtlas_iff _).2 ⟨z.proj, rfl⟩⟩
  -- Read through the bundle of fibres, `t` is `C^n` on the preimage of its source.
  have ht := ManifoldTotalSpace.contMDiffOn_trivialization (n := n) (IB := IB) (IF := IF)
    t.toMapFiber
  simp only [Bundle.Trivialization.toMapFiber_apply,
    Bundle.Trivialization.toMapFiber_source] at ht
  have hz : totalSpaceHomeomorph F proj z ∈ t.source := by
    rw [t.mem_source, proj_totalSpaceHomeomorph (proj := proj)]
    exact A.mem_baseSet_trivAt z.proj
  have hU : (ManifoldTotalSpace.homeomorph F (MapFiber proj)).symm ⁻¹'
      ((totalSpaceHomeomorph F proj) ⁻¹' t.source) ∈
        𝓝 (ManifoldTotalSpace.homeomorph F (MapFiber proj) z) :=
    ((t.open_source.preimage (Homeomorph.continuous _)).preimage
      (Homeomorph.continuous _)).mem_nhds (by simpa using hz)
  refine (((hA.contMDiffOn_trivAt_symm z.proj).comp ht fun y hy ↦ t.map_source hy).contMDiffAt
    hU).congr_of_eventuallyEq (eventually_of_mem hU fun y hy ↦ ?_)
  exact (t.left_inv hy).symm

/-- For a `C^n` atlas of `proj`, the map `p ↦ ⟨proj p, p⟩` from `P` to the charted total space of
the fibres is `C^n`: its projection is `proj`, and its fibre coordinate in the trivialization at
`proj p` is that of `trivAt (proj p)`. -/
private theorem contMDiff_totalSpaceHomeomorph_symm (hA : A.IsContMDiff n IB IF IP) :
    letI := A.fiberBundle
    ContMDiff IP (IB.prod IF) n fun p : P ↦
      ManifoldTotalSpace.homeomorph F (MapFiber proj) ((totalSpaceHomeomorph F proj).symm p) := by
  let := A.fiberBundle
  intro p
  refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨?_, ?_⟩
  · simpa only [proj_totalSpaceHomeomorph_symm] using hA.contMDiff_proj p
  have hp : p ∈ (A.trivAt (proj p)).source :=
    (A.trivAt (proj p)).mem_source.2 (A.mem_baseSet_trivAt (proj p))
  simp only [proj_totalSpaceHomeomorph_symm, A.trivializationAt_eq,
    Bundle.Trivialization.toMapFiber_apply, Homeomorph.apply_symm_apply]
  exact contMDiffAt_snd.comp p
    ((hA.contMDiffOn_trivAt (proj p)).contMDiffAt ((A.trivAt (proj p)).open_source.mem_nhds hp))

variable (A) in
/-- **The total space of a bundle given by its total space.** For a `C^n` atlas of `proj`, the
total space of the fibres of `proj`, charted through the fibre, is `C^n` diffeomorphic to `P` by
`⟨b, p⟩ ↦ p`. -/
noncomputable def totalSpaceDiffeomorph (hA : A.IsContMDiff n IB IF IP) :
    letI := A.fiberBundle
    ManifoldTotalSpace F (MapFiber proj) ≃ₘ^n⟮IB.prod IF, IP⟯ P :=
  letI := A.fiberBundle
  { toEquiv :=
      ((ManifoldTotalSpace.homeomorph F (MapFiber proj)).symm.trans
        (totalSpaceHomeomorph F proj)).toEquiv
    contMDiff_toFun := contMDiff_totalSpaceHomeomorph hA
    contMDiff_invFun := contMDiff_totalSpaceHomeomorph_symm hA }

variable (hA : A.IsContMDiff n IB IF IP)

/-- The diffeomorphism `totalSpaceDiffeomorph` sends a point of the fibre over `b` to itself, as a
point of `P`. -/
theorem totalSpaceDiffeomorph_apply (x : ManifoldTotalSpace F (MapFiber proj)) :
    letI := A.fiberBundle
    A.totalSpaceDiffeomorph hA x =
      totalSpaceHomeomorph F proj ((ManifoldTotalSpace.homeomorph F (MapFiber proj)).symm x) :=
  (rfl)

@[simp]
theorem totalSpaceDiffeomorph_homeomorph (z : TotalSpace F (MapFiber proj)) :
    letI := A.fiberBundle
    A.totalSpaceDiffeomorph hA (ManifoldTotalSpace.homeomorph F (MapFiber proj) z) =
      totalSpaceHomeomorph F proj z := by
  rw [totalSpaceDiffeomorph_apply, Homeomorph.symm_apply_apply]

/-- The inverse of `totalSpaceDiffeomorph` sends `p` to itself, as a point of the fibre over
`proj p`. -/
@[simp]
theorem totalSpaceDiffeomorph_symm_apply (p : P) :
    letI := A.fiberBundle
    (A.totalSpaceDiffeomorph hA).symm p =
      ManifoldTotalSpace.homeomorph F (MapFiber proj) ((totalSpaceHomeomorph F proj).symm p) :=
  (rfl)

/-- The diffeomorphism `totalSpaceDiffeomorph` lies over `B`: it carries the bundle projection to
`proj`. -/
theorem proj_totalSpaceDiffeomorph (x : ManifoldTotalSpace F (MapFiber proj)) :
    letI := A.fiberBundle
    proj (A.totalSpaceDiffeomorph hA x) =
      ((ManifoldTotalSpace.homeomorph F (MapFiber proj)).symm x).proj := by
  rw [totalSpaceDiffeomorph_apply, proj_totalSpaceHomeomorph (proj := proj)]

/-- For a right action on `P` preserving the fibres of `proj`, the diffeomorphism
`totalSpaceDiffeomorph` carries the fibrewise action on the total space to the action on `P`. -/
theorem totalSpaceDiffeomorph_smul {α : Type*} [Monoid α] [MulAction α P]
    (hproj : ∀ (a : α) (p : P), proj (a • p) = proj p) (a : α)
    (x : ManifoldTotalSpace F (MapFiber proj)) :
    letI := A.fiberBundle
    letI := mulAction hproj
    A.totalSpaceDiffeomorph hA (a • x) = a • A.totalSpaceDiffeomorph hA x := by
  let := A.fiberBundle
  let := mulAction hproj
  obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F (MapFiber proj)).surjective x
  rw [ManifoldTotalSpace.smul_homeomorph, totalSpaceDiffeomorph_homeomorph,
    totalSpaceDiffeomorph_homeomorph, totalSpaceHomeomorph_apply, totalSpaceHomeomorph_apply]
  exact coe_smul hproj a z.snd

/-! ### Smooth descent along `proj` -/

namespace IsContMDiff

section

include hA

/-- **Smooth maps out of the base.** For a `C^n` atlas of `proj` with nonempty model fibre, a map
out of `B` is `C^n` exactly when its composite with `proj` is. -/
theorem contMDiff_comp_iff [Nonempty F] {h : B → M} :
    ContMDiff IP IM n (h ∘ proj) ↔ ContMDiff IB IM n h := by
  let := A.fiberBundle
  have hfun : (h ∘ proj) ∘ A.totalSpaceDiffeomorph hA =
      fun y ↦ h ((ManifoldTotalSpace.homeomorph F (MapFiber proj)).symm y).proj :=
    funext fun x ↦ congrArg h (A.proj_totalSpaceDiffeomorph hA x)
  rw [← (A.totalSpaceDiffeomorph hA).contMDiff_comp_diffeomorph_iff le_rfl, hfun,
    ManifoldTotalSpace.contMDiff_comp_proj_iff (IF := IF)]

/-- **Smooth descent along `proj`.** For a `C^n` atlas of `proj` with nonempty model fibre, a `C^n`
map on `P` that is constant on the fibres of `proj` is the composite with `proj` of a unique `C^n`
map on `B`. -/
theorem existsUnique_contMDiff_comp_eq [Nonempty F] {g : P → M} (hg : ContMDiff IP IM n g)
    (hfib : FactorsThrough g proj) :
    ∃! h : B → M, ContMDiff IB IM n h ∧ h ∘ proj = g := by
  let := A.fiberBundle
  let Φ := A.totalSpaceDiffeomorph hA
  obtain ⟨h, ⟨hh, hcomp⟩, huniq⟩ :=
    ManifoldTotalSpace.existsUnique_contMDiff_comp_proj_eq (F := F) (E := MapFiber proj)
      (IF := IF) (hg.comp Φ.contMDiff) fun x y hxy ↦ hfib (by
        rw [A.proj_totalSpaceDiffeomorph hA, A.proj_totalSpaceDiffeomorph hA]
        simpa using hxy)
  -- The composite with the projection is read on `P` through `⟨b, p⟩ ↦ p`.
  have hcomp' : h ∘ proj = g := funext fun p ↦ by
    simpa [Φ] using hcomp ((totalSpaceHomeomorph F proj).symm p)
  refine ⟨h, ⟨hh, hcomp'⟩, fun h' ⟨hh', hcomp''⟩ ↦ huniq h' ⟨hh', fun x ↦ ?_⟩⟩
  rw [← hcomp'', comp_apply, comp_apply, totalSpaceDiffeomorph_homeomorph,
    proj_totalSpaceHomeomorph (proj := proj)]

end

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HF G] [MulAction Gᵐᵒᵖ P]

/-- **Descent of invariant maps.** Let the fibres of `proj` form a principal `G`-bundle for a
`C^n` atlas of equivariant trivializations. Then a `C^n` map on `P` invariant under the action of
`G` is the composite with `proj` of a unique `C^n` map on `B`, since the fibres of `proj` are the
orbits of `G`. -/
theorem existsUnique_contMDiff_comp_eq_of_smul {A : Atlas G proj}
    (hA : A.IsContMDiff n IB IF IP) (hproj : ∀ (g : Gᵐᵒᵖ) (p : P), proj (g • p) = proj p)
    (hequiv : ∀ b (p : P), proj p ∈ (A.trivAt b).baseSet → ∀ g : G,
      (A.trivAt b (op g • p)).2 = (A.trivAt b p).2 * g)
    {f : P → M} (hf : ContMDiff IP IM n f) (hinv : ∀ (g : G) (p : P), f (op g • p) = f p) :
    ∃! h : B → M, ContMDiff IB IM n h ∧ h ∘ proj = f := by
  let := A.fiberBundle
  let := mulAction hproj
  have := A.principalBundle hproj hequiv
  refine hA.existsUnique_contMDiff_comp_eq hf fun p q hpq ↦ ?_
  -- In the fibre over `proj p`, `q` is obtained from `p` by the action of `division p q`.
  let p' : MapFiber proj (proj p) := ⟨p, rfl⟩
  let q' : MapFiber proj (proj p) := ⟨q, hpq.symm⟩
  have h := congrArg Subtype.val (PrincipalBundle.smul_division (G := G) p' q')
  rw [coe_smul hproj] at h
  rw [← hinv (PrincipalBundle.division G p' q') p]
  exact congrArg f h

end IsContMDiff

end TauCeti.MapFiber.Atlas
