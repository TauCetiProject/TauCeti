/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.LeftToRight
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.GroupAction.Orbit
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.LinearAlgebra.LinearMap.Comp

/-!
# Free proper quotients are smooth principal bundles

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on the left on a
finite-dimensional boundaryless smooth manifold `M`. The quotient manifold theorem
(`ProperSMul.instIsManifoldOrbitRelQuotient`) makes the orbit space `M ⧸ G` a smooth manifold for
which the orbit projection is a submersion. This file proves that the projection is moreover a
smooth principal `G`-bundle, for the right action `x · g = g⁻¹ • x` of `G` on `M`.

The right action lives on the type copy `TauCeti.LeftToRightAction G M` of `M`, and the orbit
projection read on it is `TauCeti.orbitFiber.proj G M`. Its fibre over an orbit `q` is
`TauCeti.orbitFiber G M q`, the orbit `q` itself as a subspace of `M`, on which `G` acts on the
right by `TauCeti.orbitFiber.rightAction`.

The trivializations come from smooth local sections. If `s` is a smooth section of the orbit
projection over an open set `U`, the map `(q, g) ↦ s q · g = g⁻¹ • s q` from `U × G` onto the
preimage of `U` is a bijection (the action is free) and a local diffeomorphism. The latter holds
because `(g, q) ↦ g • s q` is a transverse slice map: its differential at `(1, q)` is
`(ξ, v) ↦ ξ_M(s q) + ds v`, and the range of `ds` is a complement of the orbit tangent space
`𝔤 · s q = ker dπ`, since `dπ ∘ ds` is the identity
(`ProperSMul.isLocalDiffeomorphAt_smul_section`). Its inverse
`ProperSMul.orbitFiberTrivialization` is therefore a smooth trivialization, and it intertwines the
right action with right multiplication on `G`. Choosing a section through every orbit gives an
atlas (`ProperSMul.orbitFiberAtlas`), and the presentation of bundles by their total space
(`TauCeti.MapFiber.Atlas`) turns it into a smooth principal bundle whose charted total space is
diffeomorphic to `M` by `⟨q, x⟩ ↦ x` (`ProperSMul.orbitFiberDiffeomorph`).

## Main definitions

* `TauCeti.orbitFiber.proj G M`: the orbit projection on `LeftToRightAction G M`.
* `TauCeti.orbitFiber G M q`: the orbit `q` as a fibre of the orbit projection.
* `TauCeti.orbitFiber.rightAction`: the right action `x · g = g⁻¹ • x` on an orbit.
* `ProperSMul.orbitFiberTrivialization`: the equivariant trivialization induced by a smooth local
  section.
* `ProperSMul.orbitFiberAtlas`: an atlas of such trivializations, one around every orbit.
* `ProperSMul.orbitFiberBundle`: the resulting fibre bundle structure on the orbits.
* `ProperSMul.orbitFiberDiffeomorph`: the diffeomorphism from its charted total space onto `M`.

## Main results

* `ProperSMul.isLocalDiffeomorphAt_smul_section`: a smooth local section of the orbit projection
  is a transverse slice.
* `ProperSMul.principalBundle_orbitFiber`: the orbits form a principal `G`-bundle.
* `ProperSMul.contMDiffFiberBundle_orbitFiber`: this principal bundle is smooth.
* `ProperSMul.exists_principalBundle_orbitFiber`: the existential form, for a free proper smooth
  action.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 21.10.
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5.
-/

public section

noncomputable section

open Bundle Function Set Filter Manifold MulOpposite Topology TauCeti
open scoped ContDiff Manifold

namespace TauCeti

section Fiber

variable {G M : Type*} [Group G] [MulAction G M]

variable (G M) in
/-- The orbit projection of a left action of `G` on `M`, read on the type copy
`LeftToRightAction G M` of `M` that carries the right action `x · g = g⁻¹ • x`. -/
def orbitFiber.proj (p : LeftToRightAction G M) : MulAction.orbitRel.Quotient G M :=
  Quotient.mk _ ((LeftToRightAction.equiv G M).symm p)

theorem orbitFiber.proj_apply (p : LeftToRightAction G M) :
    orbitFiber.proj G M p = Quotient.mk _ ((LeftToRightAction.equiv G M).symm p) :=
  (rfl)

@[simp]
theorem orbitFiber.proj_equiv (x : M) :
    orbitFiber.proj G M (LeftToRightAction.equiv G M x) = Quotient.mk _ x :=
  (rfl)

/-- The right action `x · g = g⁻¹ • x` preserves the orbits. -/
@[simp]
theorem orbitFiber.proj_smul (g : Gᵐᵒᵖ) (p : LeftToRightAction G M) :
    orbitFiber.proj G M (g • p) = orbitFiber.proj G M p := by
  obtain ⟨x, rfl⟩ := (LeftToRightAction.equiv G M).surjective p
  rw [LeftToRightAction.smul_equiv, orbitFiber.proj_equiv, orbitFiber.proj_equiv]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

variable (G M) in
/-- The fibre of the orbit projection over an orbit `q`: the orbit `q` itself, as a subspace of
`M` (through the type copy `LeftToRightAction G M`). -/
abbrev orbitFiber (q : MulAction.orbitRel.Quotient G M) : Type _ :=
  MapFiber (orbitFiber.proj G M) q

/-- The right action `x · g = g⁻¹ • x` of `G` on an orbit of a left action. -/
instance orbitFiber.rightAction (q : MulAction.orbitRel.Quotient G M) :
    MulAction Gᵐᵒᵖ (orbitFiber G M q) :=
  MapFiber.mulAction orbitFiber.proj_smul q

/-! ### The inverse of the trivialization induced by a section -/

section SectionSMul

variable {U : Set (MulAction.orbitRel.Quotient G M)}
  {s : MulAction.orbitRel.Quotient G M → M}

/-- The map `(q, g) ↦ s q · g = g⁻¹ • s q`, the inverse of the trivialization induced by a
section `s` of the orbit projection. -/
private def sectionSMul (s : MulAction.orbitRel.Quotient G M → M)
    (p : MulAction.orbitRel.Quotient G M × G) : LeftToRightAction G M :=
  op p.2 • LeftToRightAction.equiv G M (s p.1)

private theorem proj_sectionSMul (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q)
    {p : MulAction.orbitRel.Quotient G M × G} (hp : p.1 ∈ U) :
    orbitFiber.proj G M (sectionSMul s p) = p.1 := by
  rw [sectionSMul, orbitFiber.proj_smul, orbitFiber.proj_equiv, hsec p.1 hp]

/-- Over `U`, the map `(q, g) ↦ s q · g` is injective, since the action is free. -/
private theorem injOn_sectionSMul [IsCancelSMul G M] (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q) :
    InjOn (sectionSMul s) (U ×ˢ univ) := by
  rintro ⟨q, g⟩ ⟨hq, -⟩ ⟨q', g'⟩ ⟨hq', -⟩ h
  have hqq : q = q' := by
    simpa only [proj_sectionSMul hsec hq, proj_sectionSMul hsec hq'] using
      congrArg (orbitFiber.proj G M) h
  subst hqq
  have h' : g⁻¹ • s q = g'⁻¹ • s q := (LeftToRightAction.equiv G M).injective h
  rw [inv_inj.1 (IsCancelSMul.right_cancel _ _ _ h')]

/-- The map `(q, g) ↦ s q · g` sends `U × G` onto the preimage of `U`. -/
private theorem image_sectionSMul (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q) :
    sectionSMul s '' (U ×ˢ univ) = orbitFiber.proj G M ⁻¹' U := by
  refine Subset.antisymm ?_ fun p hp ↦ ?_
  · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
    rw [mem_preimage, proj_sectionSMul hsec hp]
    exact hp
  obtain ⟨x, rfl⟩ := (LeftToRightAction.equiv G M).surjective p
  rw [mem_preimage, orbitFiber.proj_equiv] at hp
  -- The point `x` lies on the orbit of `s [x]`.
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1
    (Quotient.exact (hsec _ hp).symm))
  refine ⟨(Quotient.mk _ x, g⁻¹), ⟨hp, mem_univ _⟩, ?_⟩
  rw [sectionSMul, LeftToRightAction.op_smul_equiv, inv_inv, hg]

end SectionSMul

end Fiber

end TauCeti

namespace ProperSMul

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul G M] [IsCancelSMul G M]
  {U : Set (MulAction.orbitRel.Quotient G M)} {s : MulAction.orbitRel.Quotient G M → M}

/-! ### Smooth local sections are transverse slices -/

/-- **Smooth local sections are slices.** Let `s` be a smooth section of the orbit projection over
an open set `U` of `M ⧸ G`. Then the slice map `(g, q) ↦ g • s q` is a smooth local
diffeomorphism at every point of `G × U`: the range of `ds` is a complement of the orbit tangent
space `𝔤 · s q`, the kernel of the differential of the projection. -/
theorem isLocalDiffeomorphAt_smul_section (hU : IsOpen U)
    (hs : letI := orbitRelQuotientChartedSpace I G I' M
      ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ s U)
    (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q) {q : MulAction.orbitRel.Quotient G M} (hq : q ∈ U)
    (g : G) :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
      (fun p : G × MulAction.orbitRel.Quotient G M ↦ p.1 • s p.2) (g, q) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  set J := 𝓘(ℝ, QuotientModelSpace E E')
  have hsd : MDifferentiableAt J I' s q :=
    (hs.contMDiffAt (hU.mem_nhds hq)).mdifferentiableAt (by simp)
  have hπd : MDifferentiableAt I' J (Quotient.mk (MulAction.orbitRel G M)) (s q) :=
    (contMDiff_quotientMk (I := I) (G := G) (I' := I') (M := M) (s q)).mdifferentiableAt
      (by simp)
  -- The differential of the projection is a left inverse of that of the section.
  have hcomp : (mfderiv I' J (Quotient.mk (MulAction.orbitRel G M)) (s q)).toLinearMap ∘ₗ
      (mfderiv J I' s q).toLinearMap = LinearMap.id := by
    have hev : Quotient.mk (MulAction.orbitRel G M) ∘ s =ᶠ[𝓝 q] id :=
      eventually_of_mem (hU.mem_nhds hq) hsec
    have h : mfderiv J J (Quotient.mk (MulAction.orbitRel G M) ∘ s) q = mfderiv J J id q :=
      hev.mfderiv_eq
    rw [mfderiv_id, mfderiv_comp q hπd hsd] at h
    exact LinearMap.ext fun v ↦ DFunLike.congr_fun h v
  have hbij : Bijective ((mfderiv I' J (Quotient.mk (MulAction.orbitRel G M)) (s q)).toLinearMap ∘ₗ
      (mfderiv J I' s q).toLinearMap) := by
    rw [hcomp]
    exact bijective_id
  obtain ⟨hinj, hcompl, -⟩ := LinearMap.bijective_comp_iff.1 hbij
  have hslice := (isLocalDiffeomorphAt_smul_slice_iff (I := I) (G := G) hs hU hq).2
    ⟨isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot
      (IsCancelSMul.stabilizer_eq_bot (s q)), hinj, by
        rw [← ker_mfderiv_quotientMk (I := I) (G := G) (s q)]
        exact hcompl.symm⟩
  exact hslice.eventually_forall_smul_slice.self_of_nhds g

/-- Over `U`, the map `(q, g) ↦ s q · g` is a smooth local diffeomorphism: up to the
diffeomorphism `(q, g) ↦ (g⁻¹, q)` it is the slice map of `s`. -/
private theorem isLocalDiffeomorphOn_sectionSMul (hU : IsOpen U)
    (hs : letI := orbitRelQuotientChartedSpace I G I' M
      ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ s U)
    (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q) :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsLocalDiffeomorphOn (𝓘(ℝ, QuotientModelSpace E E').prod I) I' ∞ (sectionSMul s)
      (U ×ˢ univ) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  set J := 𝓘(ℝ, QuotientModelSpace E E')
  rintro ⟨⟨q, g⟩, hq, -⟩
  let ψ := (Diffeomorph.prodComm J I (MulAction.orbitRel.Quotient G M) G ∞).trans
    ((Lie.invDiffeomorph I ∞ G).prodCongr (Diffeomorph.refl J (MulAction.orbitRel.Quotient G M) ∞))
  have hψ : ψ (q, g) = (g⁻¹, q) := by simp [ψ]
  have h := ((ψ.isLocalDiffeomorph (q, g)).comp (hg := hψ ▸
    isLocalDiffeomorphAt_smul_section (I := I) hU hs hsec hq g⁻¹)).comp
    (hg := (LeftToRightAction.diffeomorph I' ∞ G M).isLocalDiffeomorph _)
  have hfun : sectionSMul s = LeftToRightAction.diffeomorph I' ∞ G M ∘
      (fun p : G × MulAction.orbitRel.Quotient G M ↦ p.1 • s p.2) ∘ ψ :=
    funext fun p ↦ by simp [ψ, sectionSMul]
  rw [hfun]
  exact h

/-! ### The trivialization induced by a local section -/

/-- **The trivialization induced by a local section.** A smooth section `s` of the orbit
projection over an open set `U` trivializes the projection over `U`: the trivialization is the
inverse of `(q, g) ↦ s q · g = g⁻¹ • s q`, a bijection from `U × G` onto the preimage of `U`. -/
def orbitFiberTrivialization [Nonempty M] (hU : IsOpen U)
    (hs : letI := orbitRelQuotientChartedSpace I G I' M
      ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ s U)
    (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q) :
    Trivialization G (orbitFiber.proj G M) :=
  letI := orbitRelQuotientChartedSpace I G I' M
  haveI : Nonempty (MulAction.orbitRel.Quotient G M × G) :=
    ⟨(Quotient.mk _ (Classical.arbitrary M), 1)⟩
  let Φ := (isLocalDiffeomorphOn_sectionSMul hU hs hsec).partialDiffeomorphOfInjOn
    (hU.prod isOpen_univ) (injOn_sectionSMul hsec)
  { toOpenPartialHomeomorph := Φ.symm.toOpenPartialHomeomorph
    baseSet := U
    open_baseSet := hU
    source_eq := by simpa [Φ] using image_sectionSMul hsec
    target_eq := by simp [Φ]
    proj_toFun p hp := by
      have hp' : p ∈ Φ.toPartialEquiv.target := by simpa [Φ] using hp
      have hmem : Φ.toPartialEquiv.symm p ∈ U ×ˢ univ := by
        simpa [Φ] using Φ.toPartialEquiv.map_target hp'
      have h := proj_sectionSMul hsec hmem.1
      have hinv : sectionSMul s (Φ.toPartialEquiv.symm p) = p := by
        simpa [Φ] using Φ.toPartialEquiv.right_inv hp'
      rw [hinv] at h
      simpa [Φ] using h.symm }

variable [Nonempty M] (hU : IsOpen U)
  (hs : letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ s U)
  (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q)

@[simp]
theorem orbitFiberTrivialization_baseSet : (orbitFiberTrivialization hU hs hsec).baseSet = U :=
  (rfl)

/-- The inverse of the trivialization induced by `s` sends `(q, g)` to `s q · g = g⁻¹ • s q`. -/
@[simp]
theorem orbitFiberTrivialization_symm_apply (q : MulAction.orbitRel.Quotient G M) (g : G) :
    (orbitFiberTrivialization hU hs hsec).toOpenPartialHomeomorph.symm (q, g) =
      op g • LeftToRightAction.equiv G M (s q) := by
  simp [orbitFiberTrivialization, sectionSMul]

/-- The trivialization induced by `s` sends `s q` to `(q, 1)`. -/
theorem orbitFiberTrivialization_apply_section {q : MulAction.orbitRel.Quotient G M} (hq : q ∈ U) :
    orbitFiberTrivialization hU hs hsec (LeftToRightAction.equiv G M (s q)) = (q, 1) := by
  have h := (orbitFiberTrivialization hU hs hsec).apply_symm_apply
    (x := (q, 1)) ((orbitFiberTrivialization hU hs hsec).mem_target.2 hq)
  rwa [orbitFiberTrivialization_symm_apply, op_one, one_smul] at h

/-- **Equivariance.** The trivialization induced by `s` turns the right action
`x · g = g⁻¹ • x` into right multiplication on `G`. -/
theorem orbitFiberTrivialization_apply_op_smul {p : LeftToRightAction G M}
    (hp : orbitFiber.proj G M p ∈ U) (g : G) :
    (orbitFiberTrivialization hU hs hsec (op g • p)).2 =
      (orbitFiberTrivialization hU hs hsec p).2 * g := by
  have hsymm := orbitFiberTrivialization_symm_apply hU hs hsec
  have hbase := orbitFiberTrivialization_baseSet hU hs hsec
  generalize orbitFiberTrivialization hU hs hsec = e at hsymm hbase ⊢
  have hps : p ∈ e.source := e.mem_source.2 (hbase ▸ hp)
  have hq : (e p).1 ∈ e.baseSet := by rwa [e.coe_fst hps, hbase]
  -- Write `p` as `s q · h`, so that `p · g = s q · (h * g)`.
  have hp' : op (e p).2 • LeftToRightAction.equiv G M (s (e p).1) = p := by
    rw [← hsymm, Prod.mk.eta]
    exact e.left_inv hps
  have h := e.apply_symm_apply (x := ((e p).1, (e p).2 * g)) (e.mem_target.2 hq)
  rw [hsymm, op_mul, mul_smul, hp'] at h
  rw [h]

/-- The trivialization induced by `s` is smooth on its source. -/
theorem contMDiffOn_orbitFiberTrivialization :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffOn I' (𝓘(ℝ, QuotientModelSpace E E').prod I) ∞
      (orbitFiberTrivialization hU hs hsec) (orbitFiberTrivialization hU hs hsec).source :=
  letI := orbitRelQuotientChartedSpace I G I' M
  haveI : Nonempty (MulAction.orbitRel.Quotient G M × G) :=
    ⟨(Quotient.mk _ (Classical.arbitrary M), 1)⟩
  ((isLocalDiffeomorphOn_sectionSMul hU hs hsec).partialDiffeomorphOfInjOn
    (hU.prod isOpen_univ) (injOn_sectionSMul hsec)).symm.contMDiffOn

/-- The inverse of the trivialization induced by `s` is smooth on its target. -/
theorem contMDiffOn_orbitFiberTrivialization_symm :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffOn (𝓘(ℝ, QuotientModelSpace E E').prod I) I' ∞
      (orbitFiberTrivialization hU hs hsec).toOpenPartialHomeomorph.symm
      (orbitFiberTrivialization hU hs hsec).target :=
  letI := orbitRelQuotientChartedSpace I G I' M
  haveI : Nonempty (MulAction.orbitRel.Quotient G M × G) :=
    ⟨(Quotient.mk _ (Classical.arbitrary M), 1)⟩
  ((isLocalDiffeomorphOn_sectionSMul hU hs hsec).partialDiffeomorphOfInjOn
    (hU.prod isOpen_univ) (injOn_sectionSMul hsec)).contMDiffOn

omit [Nonempty M] hU hs hsec

/-! ### The principal bundle of orbits -/

variable (I G I' M) in
/-- An atlas of the orbit projection: around every orbit, the trivialization induced by a smooth
local section through it. -/
def orbitFiberAtlas : MapFiber.Atlas G (orbitFiber.proj G M) where
  trivAt q :=
    haveI : Nonempty M := ⟨q.out⟩
    have h := exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I') q.out
    orbitFiberTrivialization h.choose_spec.1 h.choose_spec.2.2.choose_spec.2.1
      h.choose_spec.2.2.choose_spec.2.2
  mem_baseSet_trivAt q := by
    have : Nonempty M := ⟨q.out⟩
    rw [orbitFiberTrivialization_baseSet]
    exact (Quotient.out_eq q).subst (motive := (· ∈ _))
      (exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I') q.out).choose_spec.2.1

/-- The trivializations of `orbitFiberAtlas` turn the right action into right multiplication. -/
private theorem orbitFiberAtlas_apply_op_smul (q : MulAction.orbitRel.Quotient G M)
    {p : LeftToRightAction G M}
    (hp : orbitFiber.proj G M p ∈ ((orbitFiberAtlas I G I' M).trivAt q).baseSet) (g : G) :
    ((orbitFiberAtlas I G I' M).trivAt q (op g • p)).2 =
      ((orbitFiberAtlas I G I' M).trivAt q p).2 * g := by
  have : Nonempty M := ⟨q.out⟩
  have h := exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I') q.out
  exact orbitFiberTrivialization_apply_op_smul h.choose_spec.1 h.choose_spec.2.2.choose_spec.2.1
    h.choose_spec.2.2.choose_spec.2.2 (by simpa [orbitFiberAtlas] using hp) g

/-- The trivializations of `orbitFiberAtlas` are diffeomorphisms onto their images. -/
theorem isContMDiff_orbitFiberAtlas :
    letI := orbitRelQuotientChartedSpace I G I' M
    (orbitFiberAtlas I G I' M).IsContMDiff ∞ 𝓘(ℝ, QuotientModelSpace E E') I I' := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  refine ⟨fun q ↦ ?_, fun q ↦ ?_⟩ <;> have : Nonempty M := ⟨q.out⟩ <;>
    have h := exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I') q.out
  · exact contMDiffOn_orbitFiberTrivialization h.choose_spec.1
      h.choose_spec.2.2.choose_spec.2.1 h.choose_spec.2.2.choose_spec.2.2
  · exact contMDiffOn_orbitFiberTrivialization_symm h.choose_spec.1
      h.choose_spec.2.2.choose_spec.2.1 h.choose_spec.2.2.choose_spec.2.2

variable (I G I' M) in
/-- **The bundle of orbits.** For a free proper smooth action of `G` on `M`, the orbits
`orbitFiber G M q` form a fibre bundle over `M ⧸ G` with model fibre `G`, whose total space is `M`
with its own topology and whose trivializations are induced by smooth local sections. -/
@[instance_reducible]
def orbitFiberBundle : FiberBundle G (orbitFiber G M) :=
  (orbitFiberAtlas I G I' M).fiberBundle

/-- **Free proper quotients are principal bundles.** For a free proper smooth action of `G` on
`M`, the orbits form a principal `G`-bundle for the right action `x · g = g⁻¹ • x`. -/
theorem principalBundle_orbitFiber :
    letI := orbitFiberBundle I G I' M
    PrincipalBundle G (orbitFiber G M) :=
  (orbitFiberAtlas I G I' M).principalBundle orbitFiber.proj_smul fun q _ hp g ↦
    orbitFiberAtlas_apply_op_smul q hp g

/-- **Free proper quotients are smooth bundles.** The bundle of orbits of a free proper smooth
action has smooth coordinate changes for the quotient manifold structure on `M ⧸ G`. -/
theorem contMDiffFiberBundle_orbitFiber :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitFiberBundle I G I' M
    ContMDiffFiberBundle ∞ G (orbitFiber G M) 𝓘(ℝ, QuotientModelSpace E E') I :=
  letI := orbitRelQuotientChartedSpace I G I' M
  (orbitFiberAtlas I G I' M).contMDiffFiberBundle isContMDiff_orbitFiberAtlas

variable (I G I' M) in
/-- **The total space of the bundle of orbits is `M`.** The charted total space of the bundle of
orbits is diffeomorphic to `M` by `⟨q, x⟩ ↦ x`. -/
def orbitFiberDiffeomorph :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitFiberBundle I G I' M
    ManifoldTotalSpace G (orbitFiber G M) ≃ₘ^∞⟮𝓘(ℝ, QuotientModelSpace E E').prod I, I'⟯ M :=
  letI := orbitRelQuotientChartedSpace I G I' M
  letI := orbitFiberBundle I G I' M
  ((orbitFiberAtlas I G I' M).totalSpaceDiffeomorph isContMDiff_orbitFiberAtlas).trans
    (LeftToRightAction.diffeomorph I' ∞ G M).symm

@[simp]
theorem orbitFiberDiffeomorph_homeomorph (z : TotalSpace G (orbitFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitFiberBundle I G I' M
    orbitFiberDiffeomorph I G I' M (ManifoldTotalSpace.homeomorph G (orbitFiber G M) z) =
      (LeftToRightAction.equiv G M).symm z.snd.val := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitFiberBundle I G I' M
  simp [orbitFiberDiffeomorph]

/-- The diffeomorphism `orbitFiberDiffeomorph` sends a point of the orbit over `q` to itself, as a
point of `M`. -/
theorem orbitFiberDiffeomorph_apply (x : ManifoldTotalSpace G (orbitFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitFiberBundle I G I' M
    orbitFiberDiffeomorph I G I' M x = (LeftToRightAction.equiv G M).symm
      ((ManifoldTotalSpace.homeomorph G (orbitFiber G M)).symm x).snd.val := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitFiberBundle I G I' M
  rw [← orbitFiberDiffeomorph_homeomorph (I := I) (G := G) (I' := I'),
    Homeomorph.apply_symm_apply]

/-- The inverse of `orbitFiberDiffeomorph` sends `x` to itself, as a point of its orbit. -/
@[simp]
theorem orbitFiberDiffeomorph_symm_apply (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitFiberBundle I G I' M
    (orbitFiberDiffeomorph I G I' M).symm x = ManifoldTotalSpace.homeomorph G (orbitFiber G M)
      ⟨Quotient.mk _ x, ⟨LeftToRightAction.equiv G M x, orbitFiber.proj_equiv x⟩⟩ := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitFiberBundle I G I' M
  conv_lhs => rw [← Equiv.symm_apply_apply (LeftToRightAction.equiv G M) x,
    ← orbitFiberDiffeomorph_homeomorph (I := I) (G := G) (I' := I')
      ⟨Quotient.mk _ x, ⟨LeftToRightAction.equiv G M x, orbitFiber.proj_equiv x⟩⟩]
  exact Diffeomorph.symm_apply_apply _ _

/-- The diffeomorphism `orbitFiberDiffeomorph` lies over `M ⧸ G`: it carries the bundle projection
to the orbit projection. -/
theorem quotientMk_orbitFiberDiffeomorph (x : ManifoldTotalSpace G (orbitFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitFiberBundle I G I' M
    Quotient.mk _ (orbitFiberDiffeomorph I G I' M x) =
      ((ManifoldTotalSpace.homeomorph G (orbitFiber G M)).symm x).proj := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitFiberBundle I G I' M
  rw [orbitFiberDiffeomorph_apply]
  exact ((ManifoldTotalSpace.homeomorph G (orbitFiber G M)).symm x).snd.property

/-- The diffeomorphism `orbitFiberDiffeomorph` carries the right action of `g` on the total space
to the left action of `g⁻¹` on `M`. -/
theorem orbitFiberDiffeomorph_op_smul (g : G) (x : ManifoldTotalSpace G (orbitFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitFiberBundle I G I' M
    orbitFiberDiffeomorph I G I' M (op g • x) = g⁻¹ • orbitFiberDiffeomorph I G I' M x := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitFiberBundle I G I' M
  obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph G (orbitFiber G M)).surjective x
  rw [ManifoldTotalSpace.smul_homeomorph, orbitFiberDiffeomorph_homeomorph,
    orbitFiberDiffeomorph_homeomorph, MapFiber.coe_smul, LeftToRightAction.equiv_symm_smul,
    unop_op]

omit [ContMDiffSMul I I' ∞ G M] [IsCancelSMul G M] in
/-- **Free proper quotients are smooth principal bundles (existential form).** Let a
finite-dimensional real Lie group `G` act smoothly, freely and properly on a finite-dimensional
boundaryless smooth real manifold `M`. For some smooth atlas on `M ⧸ G`, modelled on
`ℝ^(dim M - dim G)` and with its quotient topology, the orbits `orbitFiber G M q`, with the right
action `x · g = g⁻¹ • x`, form a smooth principal `G`-bundle whose charted total space is
diffeomorphic to `M` by `⟨q, x⟩ ↦ x`. No separation or countability hypotheses are needed, and `M`
may be empty. -/
theorem exists_principalBundle_orbitFiber
    (hsm : ContMDiff (I.prod I') I' ∞ (fun gx : G × M ↦ gx.1 • gx.2))
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ∃ (_ : ChartedSpace (QuotientModelSpace E E') (MulAction.orbitRel.Quotient G M))
      (_ : FiberBundle G (orbitFiber G M)),
      IsManifold 𝓘(ℝ, QuotientModelSpace E E') ∞ (MulAction.orbitRel.Quotient G M) ∧
      PrincipalBundle G (orbitFiber G M) ∧
      ContMDiffFiberBundle ∞ G (orbitFiber G M) 𝓘(ℝ, QuotientModelSpace E E') I ∧
      ∃ φ : ManifoldTotalSpace G (orbitFiber G M) ≃ₘ^∞⟮𝓘(ℝ, QuotientModelSpace E E').prod I, I'⟯ M,
        ∀ x, φ x = (LeftToRightAction.equiv G M).symm
          ((ManifoldTotalSpace.homeomorph G (orbitFiber G M)).symm x).snd.val := by
  let _ : ContMDiffSMul I I' ∞ G M := ⟨hsm⟩
  let _ : IsCancelSMul G M := isCancelSMul_iff_eq_one_of_smul_eq.2 hfree
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitFiberBundle I G I' M
  exact ⟨_, _, instIsManifoldOrbitRelQuotient, principalBundle_orbitFiber,
    contMDiffFiberBundle_orbitFiber, orbitFiberDiffeomorph I G I' M,
    orbitFiberDiffeomorph_apply⟩

end ProperSMul
