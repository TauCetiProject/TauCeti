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
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Free proper quotients are smooth principal bundles

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on the left on a
finite-dimensional boundaryless smooth manifold `M`. The quotient manifold theorem
(`ProperSMul.instIsManifoldOrbitRelQuotient`) makes the orbit space `M ⧸ G` a smooth manifold for
which the orbit projection is a submersion. This file proves that the projection is moreover a
smooth principal `G`-bundle, for the right action `x · g = g⁻¹ • x` of `G` on `M`.

The right action lives on the type copy `TauCeti.LeftToRightAction G M` of `M`, and the orbit
projection read on it is `TauCeti.orbitRelFiber.proj G M`. Its fibre over an orbit `q` is
`TauCeti.orbitRelFiber G M q`, the orbit `q` itself as a subspace of `M`, on which `G` acts on the
right by `TauCeti.orbitRelFiber.rightAction`.

The trivializations come from smooth local sections. If `s` is a smooth section of the orbit
projection over an open set `U`, the map `(q, g) ↦ s q · g = g⁻¹ • s q` from `U × G` onto the
preimage of `U` is a bijection (the action is free) and a local diffeomorphism. The latter holds
because `(g, q) ↦ g • s q` is a transverse slice map: its differential at `(1, q)` is
`(ξ, v) ↦ ξ_M(s q) + ds v`, and the range of `ds` is a complement of the orbit tangent space
`𝔤 · s q = ker dπ`, since `dπ ∘ ds` is the identity
(`ProperSMul.isLocalDiffeomorphAt_smul_section`). Its inverse
`ProperSMul.orbitRelFiberTrivialization` is therefore a smooth trivialization, and it intertwines
the right action with right multiplication on `G`. Choosing a section through every orbit gives an
atlas (`ProperSMul.orbitRelFiberAtlas`), and the presentation of bundles by their total space
(`TauCeti.MapFiber.Atlas`) turns it into a smooth principal bundle whose charted total space is
diffeomorphic to `M` by `⟨q, x⟩ ↦ x` (`ProperSMul.orbitRelFiberDiffeomorph`).

## Main definitions

* `TauCeti.orbitRelFiber.proj G M`: the orbit projection on `LeftToRightAction G M`.
* `TauCeti.orbitRelFiber G M q`: the orbit `q` as a fibre of the orbit projection.
* `TauCeti.orbitRelFiber.rightAction`: the right action `x · g = g⁻¹ • x` on an orbit.
* `ProperSMul.orbitRelFiberTrivialization`: the equivariant trivialization induced by a smooth
  local section.
* `ProperSMul.orbitRelFiberAtlas`: an atlas of such trivializations, one around every orbit.
* `ProperSMul.orbitRelFiberBundle`: the resulting fibre bundle structure on the orbits.
* `ProperSMul.orbitRelFiberDiffeomorph`: the diffeomorphism from its charted total space onto `M`.

## Main results

* `ProperSMul.principalBundle_orbitRelFiber`: the orbits form a principal `G`-bundle.
* `ProperSMul.contMDiffFiberBundle_orbitRelFiber`: this principal bundle is smooth.
* `ProperSMul.exists_principalBundle_orbitRelFiber`: the existential form, for a free proper
  smooth action.

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
def orbitRelFiber.proj (p : LeftToRightAction G M) : MulAction.orbitRel.Quotient G M :=
  Quotient.mk _ ((LeftToRightAction.equiv G M).symm p)

theorem orbitRelFiber.proj_apply (p : LeftToRightAction G M) :
    orbitRelFiber.proj G M p = Quotient.mk _ ((LeftToRightAction.equiv G M).symm p) :=
  (rfl)

@[simp]
theorem orbitRelFiber.proj_equiv (x : M) :
    orbitRelFiber.proj G M (LeftToRightAction.equiv G M x) = Quotient.mk _ x :=
  (rfl)

/-- The right action `x · g = g⁻¹ • x` preserves the orbits. -/
@[simp]
theorem orbitRelFiber.proj_smul (g : Gᵐᵒᵖ) (p : LeftToRightAction G M) :
    orbitRelFiber.proj G M (g • p) = orbitRelFiber.proj G M p := by
  obtain ⟨x, rfl⟩ := (LeftToRightAction.equiv G M).surjective p
  rw [LeftToRightAction.smul_equiv, orbitRelFiber.proj_equiv, orbitRelFiber.proj_equiv]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

variable (G M) in
/-- The fibre of the orbit projection over an orbit `q`: the orbit `q` itself, as a subspace of
`M` (through the type copy `LeftToRightAction G M`). -/
abbrev orbitRelFiber (q : MulAction.orbitRel.Quotient G M) : Type _ :=
  MapFiber (orbitRelFiber.proj G M) q

/-- The right action `x · g = g⁻¹ • x` of `G` on an orbit of a left action. -/
instance orbitRelFiber.rightAction (q : MulAction.orbitRel.Quotient G M) :
    MulAction Gᵐᵒᵖ (orbitRelFiber G M q) :=
  MapFiber.mulAction orbitRelFiber.proj_smul q

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
    orbitRelFiber.proj G M (sectionSMul s p) = p.1 := by
  rw [sectionSMul, orbitRelFiber.proj_smul, orbitRelFiber.proj_equiv, hsec p.1 hp]

/-- Over `U`, the map `(q, g) ↦ s q · g` is injective, since the action is free. -/
private theorem injOn_sectionSMul [IsCancelSMul G M] (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q) :
    InjOn (sectionSMul s) (U ×ˢ univ) := by
  rintro ⟨q, g⟩ ⟨hq, -⟩ ⟨q', g'⟩ ⟨hq', -⟩ h
  have hqq : q = q' := by
    simpa only [proj_sectionSMul hsec hq, proj_sectionSMul hsec hq'] using
      congrArg (orbitRelFiber.proj G M) h
  subst hqq
  have h' : g⁻¹ • s q = g'⁻¹ • s q := (LeftToRightAction.equiv G M).injective h
  rw [inv_inj.1 (IsCancelSMul.right_cancel _ _ _ h')]

/-- The map `(q, g) ↦ s q · g` sends `U × G` onto the preimage of `U`. -/
private theorem image_sectionSMul (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q) :
    sectionSMul s '' (U ×ˢ univ) = orbitRelFiber.proj G M ⁻¹' U := by
  refine Subset.antisymm ?_ fun p hp ↦ ?_
  · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
    rw [mem_preimage, proj_sectionSMul hsec hp]
    exact hp
  obtain ⟨x, rfl⟩ := (LeftToRightAction.equiv G M).surjective p
  rw [mem_preimage, orbitRelFiber.proj_equiv] at hp
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

/-! ### The inverse trivialization is a local diffeomorphism -/

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

variable [Nonempty M] (hU : IsOpen U)
  (hs : letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ s U)
  (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q)

/-- The map `(q, g) ↦ s q · g`, as a smooth partial diffeomorphism from `U × G` onto the preimage
of `U`. -/
private def sectionSMulDiffeom :
    letI := orbitRelQuotientChartedSpace I G I' M
    PartialDiffeomorph (𝓘(ℝ, QuotientModelSpace E E').prod I) I'
      (MulAction.orbitRel.Quotient G M × G) (LeftToRightAction G M) ∞ :=
  letI := orbitRelQuotientChartedSpace I G I' M
  haveI : Nonempty (MulAction.orbitRel.Quotient G M × G) :=
    ⟨(Quotient.mk _ (Classical.arbitrary M), 1)⟩
  (isLocalDiffeomorphOn_sectionSMul hU hs hsec).partialDiffeomorphOfInjOn
    (hU.prod isOpen_univ) (injOn_sectionSMul hsec)

private theorem sectionSMulDiffeom_source :
    letI := orbitRelQuotientChartedSpace I G I' M
    (sectionSMulDiffeom hU hs hsec).source = U ×ˢ univ := by
  simp [sectionSMulDiffeom]

private theorem sectionSMulDiffeom_target :
    letI := orbitRelQuotientChartedSpace I G I' M
    (sectionSMulDiffeom hU hs hsec).target = orbitRelFiber.proj G M ⁻¹' U := by
  simpa [sectionSMulDiffeom] using image_sectionSMul hsec

private theorem sectionSMulDiffeom_apply (p : MulAction.orbitRel.Quotient G M × G) :
    letI := orbitRelQuotientChartedSpace I G I' M
    sectionSMulDiffeom hU hs hsec p = sectionSMul s p := by
  simp [sectionSMulDiffeom]

/-- **The trivialization induced by a local section.** A smooth section `s` of the orbit
projection over an open set `U` trivializes the projection over `U`: the trivialization is the
inverse of `(q, g) ↦ s q · g = g⁻¹ • s q`, a bijection from `U × G` onto the preimage of `U`. -/
def orbitRelFiberTrivialization : Trivialization G (orbitRelFiber.proj G M) :=
  letI := orbitRelQuotientChartedSpace I G I' M
  let Φ := sectionSMulDiffeom hU hs hsec
  { toOpenPartialHomeomorph := Φ.symm.toOpenPartialHomeomorph
    baseSet := U
    open_baseSet := hU
    source_eq := sectionSMulDiffeom_target hU hs hsec
    target_eq := sectionSMulDiffeom_source hU hs hsec
    proj_toFun p hp := by
      -- Write `p` as `Φ (Φ⁻¹ p)`, with `Φ⁻¹ p` over `U`.
      have hp' : p ∈ Φ.target := hp
      have hmem : Φ.toPartialEquiv.symm p ∈ U ×ˢ univ :=
        sectionSMulDiffeom_source hU hs hsec ▸ Φ.map_target hp'
      have h := proj_sectionSMul hsec hmem.1
      rw [← sectionSMulDiffeom_apply hU hs hsec, Φ.right_inv hp'] at h
      exact h.symm }

/-- The trivialization induced by `s` is the inverse of the partial diffeomorphism
`(q, g) ↦ s q · g`. -/
private theorem orbitRelFiberTrivialization_toOpenPartialHomeomorph :
    letI := orbitRelQuotientChartedSpace I G I' M
    (orbitRelFiberTrivialization hU hs hsec).toOpenPartialHomeomorph =
      (sectionSMulDiffeom hU hs hsec).symm.toOpenPartialHomeomorph :=
  (rfl)

@[simp]
theorem orbitRelFiberTrivialization_baseSet :
    (orbitRelFiberTrivialization hU hs hsec).baseSet = U :=
  (rfl)

/-- The inverse of the trivialization induced by `s` sends `(q, g)` to `s q · g = g⁻¹ • s q`. -/
@[simp]
theorem orbitRelFiberTrivialization_symm_apply (q : MulAction.orbitRel.Quotient G M) (g : G) :
    (orbitRelFiberTrivialization hU hs hsec).toOpenPartialHomeomorph.symm (q, g) =
      op g • LeftToRightAction.equiv G M (s q) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  rw [orbitRelFiberTrivialization_toOpenPartialHomeomorph]
  exact sectionSMulDiffeom_apply hU hs hsec (q, g)

/-- The trivialization induced by `s` sends `s q` to `(q, 1)`. -/
theorem orbitRelFiberTrivialization_apply_section {q : MulAction.orbitRel.Quotient G M}
    (hq : q ∈ U) :
    orbitRelFiberTrivialization hU hs hsec (LeftToRightAction.equiv G M (s q)) = (q, 1) := by
  have h := (orbitRelFiberTrivialization hU hs hsec).apply_symm_apply
    (x := (q, 1)) ((orbitRelFiberTrivialization hU hs hsec).mem_target.2 hq)
  rwa [orbitRelFiberTrivialization_symm_apply, op_one, one_smul] at h

/-- **Equivariance.** The trivialization induced by `s` turns the right action
`x · g = g⁻¹ • x` into right multiplication on `G`. -/
theorem orbitRelFiberTrivialization_apply_op_smul {p : LeftToRightAction G M}
    (hp : orbitRelFiber.proj G M p ∈ U) (g : G) :
    (orbitRelFiberTrivialization hU hs hsec (op g • p)).2 =
      (orbitRelFiberTrivialization hU hs hsec p).2 * g := by
  have hsymm := orbitRelFiberTrivialization_symm_apply hU hs hsec
  have hbase := orbitRelFiberTrivialization_baseSet hU hs hsec
  generalize orbitRelFiberTrivialization hU hs hsec = e at hsymm hbase ⊢
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
theorem contMDiffOn_orbitRelFiberTrivialization :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffOn I' (𝓘(ℝ, QuotientModelSpace E E').prod I) ∞
      (orbitRelFiberTrivialization hU hs hsec)
      (orbitRelFiberTrivialization hU hs hsec).source := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  rw [← Trivialization.coe_coe, orbitRelFiberTrivialization_toOpenPartialHomeomorph]
  exact (sectionSMulDiffeom hU hs hsec).symm.contMDiffOn

/-- The inverse of the trivialization induced by `s` is smooth on its target. -/
theorem contMDiffOn_orbitRelFiberTrivialization_symm :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffOn (𝓘(ℝ, QuotientModelSpace E E').prod I) I' ∞
      (orbitRelFiberTrivialization hU hs hsec).toOpenPartialHomeomorph.symm
      (orbitRelFiberTrivialization hU hs hsec).target := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  rw [orbitRelFiberTrivialization_toOpenPartialHomeomorph]
  exact (sectionSMulDiffeom hU hs hsec).contMDiffOn

omit [Nonempty M] hU hs hsec

/-! ### The principal bundle of orbits -/

section Atlas

variable (I G I' M) (q : MulAction.orbitRel.Quotient G M)

/-- The open set of a smooth local section of the orbit projection through the orbit `q`. -/
private def orbitRelFiberAtlasSet : Set (MulAction.orbitRel.Quotient G M) :=
  (exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I') q.out).choose

/-- A smooth local section of the orbit projection through the orbit `q`. -/
private def orbitRelFiberAtlasSection : MulAction.orbitRel.Quotient G M → M :=
  (exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I') q.out).choose_spec.2.2.choose

private theorem isOpen_orbitRelFiberAtlasSet : IsOpen (orbitRelFiberAtlasSet I G I' M q) :=
  (exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I') q.out).choose_spec.1

private theorem mem_orbitRelFiberAtlasSet : q ∈ orbitRelFiberAtlasSet I G I' M q :=
  (Quotient.out_eq q).subst (motive := (· ∈ orbitRelFiberAtlasSet I G I' M q))
    (exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I') q.out).choose_spec.2.1

private theorem contMDiffOn_orbitRelFiberAtlasSection :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ (orbitRelFiberAtlasSection I G I' M q)
      (orbitRelFiberAtlasSet I G I' M q) :=
  (exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I')
    q.out).choose_spec.2.2.choose_spec.2.1

private theorem quotientMk_orbitRelFiberAtlasSection :
    ∀ q' ∈ orbitRelFiberAtlasSet I G I' M q,
      Quotient.mk _ (orbitRelFiberAtlasSection I G I' M q q') = q' :=
  (exists_contMDiffOn_section_quotientMk (I := I) (G := G) (I' := I')
    q.out).choose_spec.2.2.choose_spec.2.2

end Atlas

variable (I G I' M) in
/-- An atlas of the orbit projection: around every orbit, the trivialization induced by a smooth
local section through it. -/
def orbitRelFiberAtlas : MapFiber.Atlas G (orbitRelFiber.proj G M) where
  trivAt q :=
    haveI : Nonempty M := ⟨q.out⟩
    orbitRelFiberTrivialization (isOpen_orbitRelFiberAtlasSet I G I' M q)
      (contMDiffOn_orbitRelFiberAtlasSection I G I' M q)
      (quotientMk_orbitRelFiberAtlasSection I G I' M q)
  mem_baseSet_trivAt q := mem_orbitRelFiberAtlasSet I G I' M q

/-- The trivializations of `orbitRelFiberAtlas` turn the right action into right multiplication. -/
private theorem orbitRelFiberAtlas_apply_op_smul (q : MulAction.orbitRel.Quotient G M)
    {p : LeftToRightAction G M}
    (hp : orbitRelFiber.proj G M p ∈ ((orbitRelFiberAtlas I G I' M).trivAt q).baseSet) (g : G) :
    ((orbitRelFiberAtlas I G I' M).trivAt q (op g • p)).2 =
      ((orbitRelFiberAtlas I G I' M).trivAt q p).2 * g :=
  haveI : Nonempty M := ⟨q.out⟩
  orbitRelFiberTrivialization_apply_op_smul (isOpen_orbitRelFiberAtlasSet I G I' M q)
    (contMDiffOn_orbitRelFiberAtlasSection I G I' M q)
    (quotientMk_orbitRelFiberAtlasSection I G I' M q) hp g

/-- The trivializations of `orbitRelFiberAtlas` are diffeomorphisms onto their images. -/
theorem isContMDiff_orbitRelFiberAtlas :
    letI := orbitRelQuotientChartedSpace I G I' M
    (orbitRelFiberAtlas I G I' M).IsContMDiff ∞ 𝓘(ℝ, QuotientModelSpace E E') I I' := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  refine ⟨fun q ↦ ?_, fun q ↦ ?_⟩ <;> have : Nonempty M := ⟨q.out⟩
  · exact contMDiffOn_orbitRelFiberTrivialization (isOpen_orbitRelFiberAtlasSet I G I' M q)
      (contMDiffOn_orbitRelFiberAtlasSection I G I' M q)
      (quotientMk_orbitRelFiberAtlasSection I G I' M q)
  · exact contMDiffOn_orbitRelFiberTrivialization_symm (isOpen_orbitRelFiberAtlasSet I G I' M q)
      (contMDiffOn_orbitRelFiberAtlasSection I G I' M q)
      (quotientMk_orbitRelFiberAtlasSection I G I' M q)

variable (I G I' M) in
/-- **The bundle of orbits.** For a free proper smooth action of `G` on `M`, the orbits
`orbitRelFiber G M q` form a fibre bundle over `M ⧸ G` with model fibre `G`, whose total space is
`M` with its own topology and whose trivializations are induced by smooth local sections. -/
@[instance_reducible]
def orbitRelFiberBundle : FiberBundle G (orbitRelFiber G M) :=
  (orbitRelFiberAtlas I G I' M).fiberBundle

/-- **Free proper quotients are principal bundles.** For a free proper smooth action of `G` on
`M`, the orbits form a principal `G`-bundle for the right action `x · g = g⁻¹ • x`. -/
theorem principalBundle_orbitRelFiber :
    letI := orbitRelFiberBundle I G I' M
    PrincipalBundle G (orbitRelFiber G M) :=
  (orbitRelFiberAtlas I G I' M).principalBundle orbitRelFiber.proj_smul fun q _ hp g ↦
    orbitRelFiberAtlas_apply_op_smul q hp g

/-- **Free proper quotients are smooth bundles.** The bundle of orbits of a free proper smooth
action has smooth coordinate changes for the quotient manifold structure on `M ⧸ G`. -/
theorem contMDiffFiberBundle_orbitRelFiber :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    ContMDiffFiberBundle ∞ G (orbitRelFiber G M) 𝓘(ℝ, QuotientModelSpace E E') I :=
  letI := orbitRelQuotientChartedSpace I G I' M
  (orbitRelFiberAtlas I G I' M).contMDiffFiberBundle isContMDiff_orbitRelFiberAtlas

variable (I G I' M) in
/-- **The total space of the bundle of orbits is `M`.** The charted total space of the bundle of
orbits is diffeomorphic to `M` by `⟨q, x⟩ ↦ x`. -/
def orbitRelFiberDiffeomorph :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    ManifoldTotalSpace G (orbitRelFiber G M) ≃ₘ^∞⟮𝓘(ℝ, QuotientModelSpace E E').prod I, I'⟯ M :=
  letI := orbitRelQuotientChartedSpace I G I' M
  letI := orbitRelFiberBundle I G I' M
  ((orbitRelFiberAtlas I G I' M).totalSpaceDiffeomorph isContMDiff_orbitRelFiberAtlas).trans
    (LeftToRightAction.diffeomorph I' ∞ G M).symm

@[simp]
theorem orbitRelFiberDiffeomorph_homeomorph (z : TotalSpace G (orbitRelFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    orbitRelFiberDiffeomorph I G I' M (ManifoldTotalSpace.homeomorph G (orbitRelFiber G M) z) =
      (LeftToRightAction.equiv G M).symm z.snd.val := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  simp [orbitRelFiberDiffeomorph]

/-- The diffeomorphism `orbitRelFiberDiffeomorph` sends a point of the orbit over `q` to itself, as
a point of `M`. -/
theorem orbitRelFiberDiffeomorph_apply (x : ManifoldTotalSpace G (orbitRelFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    orbitRelFiberDiffeomorph I G I' M x = (LeftToRightAction.equiv G M).symm
      ((ManifoldTotalSpace.homeomorph G (orbitRelFiber G M)).symm x).snd.val := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  rw [← orbitRelFiberDiffeomorph_homeomorph (I := I) (G := G) (I' := I'),
    Homeomorph.apply_symm_apply]

/-- The inverse of `orbitRelFiberDiffeomorph` sends `x` to itself, as a point of its orbit. -/
@[simp]
theorem orbitRelFiberDiffeomorph_symm_apply (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    (orbitRelFiberDiffeomorph I G I' M).symm x =
      ManifoldTotalSpace.homeomorph G (orbitRelFiber G M)
      ⟨Quotient.mk _ x, ⟨LeftToRightAction.equiv G M x, orbitRelFiber.proj_equiv x⟩⟩ := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  conv_lhs => rw [← Equiv.symm_apply_apply (LeftToRightAction.equiv G M) x,
    ← orbitRelFiberDiffeomorph_homeomorph (I := I) (G := G) (I' := I')
      ⟨Quotient.mk _ x, ⟨LeftToRightAction.equiv G M x, orbitRelFiber.proj_equiv x⟩⟩]
  exact Diffeomorph.symm_apply_apply _ _

/-- The diffeomorphism `orbitRelFiberDiffeomorph` lies over `M ⧸ G`: it carries the bundle
projection to the orbit projection. -/
theorem quotientMk_orbitRelFiberDiffeomorph (x : ManifoldTotalSpace G (orbitRelFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    Quotient.mk _ (orbitRelFiberDiffeomorph I G I' M x) =
      ((ManifoldTotalSpace.homeomorph G (orbitRelFiber G M)).symm x).proj := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  rw [← orbitRelFiber.proj_equiv, orbitRelFiberDiffeomorph, Diffeomorph.coe_trans,
    Function.comp_apply, LeftToRightAction.coe_diffeomorph_symm, Equiv.apply_symm_apply]
  exact (orbitRelFiberAtlas I G I' M).proj_totalSpaceDiffeomorph isContMDiff_orbitRelFiberAtlas x

/-- The diffeomorphism `orbitRelFiberDiffeomorph` carries the right action of `g` on the total space
to the left action of `g⁻¹` on `M`. -/
theorem orbitRelFiberDiffeomorph_op_smul (g : G) (x : ManifoldTotalSpace G (orbitRelFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    orbitRelFiberDiffeomorph I G I' M (op g • x) = g⁻¹ • orbitRelFiberDiffeomorph I G I' M x := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  rw [orbitRelFiberDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply, Function.comp_apply,
    (orbitRelFiberAtlas I G I' M).totalSpaceDiffeomorph_smul isContMDiff_orbitRelFiberAtlas
      orbitRelFiber.proj_smul, LeftToRightAction.coe_diffeomorph_symm,
    LeftToRightAction.equiv_symm_op_smul]

omit [ContMDiffSMul I I' ∞ G M] [IsCancelSMul G M] in
/-- **Free proper quotients are smooth principal bundles (existential form).** Let a
finite-dimensional real Lie group `G` act smoothly, freely and properly on a finite-dimensional
boundaryless smooth real manifold `M`. For some smooth atlas on `M ⧸ G`, modelled on
`ℝ^(dim M - dim G)` and with its quotient topology, the orbits `orbitRelFiber G M q`, with the right
action `x · g = g⁻¹ • x`, form a smooth principal `G`-bundle whose charted total space is
diffeomorphic to `M` by `⟨q, x⟩ ↦ x`. No separation or countability hypotheses are needed, and `M`
may be empty. -/
theorem exists_principalBundle_orbitRelFiber
    (hsm : ContMDiff (I.prod I') I' ∞ (fun gx : G × M ↦ gx.1 • gx.2))
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ∃ (_ : ChartedSpace (QuotientModelSpace E E') (MulAction.orbitRel.Quotient G M))
      (_ : FiberBundle G (orbitRelFiber G M)),
      IsManifold 𝓘(ℝ, QuotientModelSpace E E') ∞ (MulAction.orbitRel.Quotient G M) ∧
      PrincipalBundle G (orbitRelFiber G M) ∧
      ContMDiffFiberBundle ∞ G (orbitRelFiber G M) 𝓘(ℝ, QuotientModelSpace E E') I ∧
      ∃ φ : ManifoldTotalSpace G (orbitRelFiber G M) ≃ₘ^∞⟮𝓘(ℝ, QuotientModelSpace E E').prod I,
        I'⟯ M,
        ∀ x, φ x = (LeftToRightAction.equiv G M).symm
          ((ManifoldTotalSpace.homeomorph G (orbitRelFiber G M)).symm x).snd.val := by
  let _ : ContMDiffSMul I I' ∞ G M := ⟨hsm⟩
  let _ : IsCancelSMul G M := isCancelSMul_iff_eq_one_of_smul_eq.2 hfree
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  exact ⟨_, _, instIsManifoldOrbitRelQuotient, principalBundle_orbitRelFiber,
    contMDiffFiberBundle_orbitRelFiber, orbitRelFiberDiffeomorph I G I' M,
    orbitRelFiberDiffeomorph_apply⟩

end ProperSMul
