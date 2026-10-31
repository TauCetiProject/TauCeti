/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.DehnSurgery.Link.Filling
public import TauCeti.LowDimTopology.DehnSurgery.Uniqueness
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.DisjointOpens

/-!
# Existence of Dehn fillings

A Dehn filling of a knot exterior `E` along a slope `s` (`TauCeti.DehnFilling h s Y`) is recorded
inside the filled space `Y`. This file constructs such a space for every slope, and likewise for
the exteriors of links with finitely many components (`TauCeti.LinkDehnFilling`). So every Dehn
surgery on a knot or a link, such as the rational surgeries on links in `S³`
(`TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope`), exists.

The filled space is the space obtained from the exterior by attaching solid tori `V = D² × S¹`
along homeomorphisms `g` of their boundary tori: the pushout in `TopCat` of the boundary
inclusions `S¹ × S¹ → D² × S¹` and of the parametrized boundary tori of the exterior, precomposed
with the gluings (`TauCeti.IsSolidTorusNeighborhood.dehnFillingSpace`,
`TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingSpace`). Its properties are those of the
cobase change of a closed embedding in `TopCat`:

* both maps into the pushout are closed embeddings
  (`TauCeti.TopCat.isClosedEmbedding_of_isPushout`), the boundary torus of the exterior and the
  boundary tori of the solid tori being compact and embedded;
* the pushout is Hausdorff (`TauCeti.TopCat.t2Space_of_isPushout`), since the boundary inclusion
  extends disjoint open sets: an open subset `U` of `S¹ × S¹` is the trace of the open collar
  `{(w, z) | 1 / 2 < ‖w‖, (w / ‖w‖, z) ∈ U}`, as for the boundary sphere of a disk
  (`TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion`);
* it is compact when the ambient space is.

Every slope is the filling slope of a gluing induced by an invertible integral matrix
(`TauCeti.IsSolidTorusNeighborhood.exists_fillingSlope_torusHomeomorph_eq`): a primitive class
with coordinates `(p, q)` extends to a basis, by a matrix `[[p, -b], [q, a]]` with `a p + b q = 1`.

## Main definitions

* `TauCeti.IsSolidTorusNeighborhood.dehnFillingSpace h g`: the knot exterior with a solid torus
  attached along the gluing `g`.
* `TauCeti.IsSolidTorusNeighborhood.dehnFillingOfGluing h g`: the Dehn filling of the knot exterior
  in that space, along the filling slope of `g`.
* `TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingSpace h g`,
  `TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingOfGluing h g`: the same for the exterior of
  a link with finitely many components, with one gluing `g i` for each component.

## Main results

* `TauCeti.IsSolidTorusNeighborhood.exists_fillingSlope_torusHomeomorph_eq`: every slope is the
  filling slope of a matrix gluing.
* `TauCeti.IsSolidTorusNeighborhood.exists_dehnFilling`: a knot exterior has a Dehn filling along
  every slope.
* `TauCeti.IsSolidTorusLinkNeighborhood.exists_linkDehnFilling`: the exterior of a link with
  finitely many components has a Dehn filling along every family of slopes.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Sections 9F and 9G (Dehn
  surgery: a solid torus is sewn to each boundary torus of the exterior, its meridian going to the
  chosen slope).
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Function

namespace TauCeti

/-! ### Attaching solid tori along their boundary tori -/

section Attach

variable {ι : Type} {E : Type} [TopologicalSpace E]

/-- The boundary inclusions `S¹ × S¹ → D² × S¹` of a family of solid tori, as a map of `TopCat`. -/
private def sigmaBoundaryInclusion (ι : Type) :
    TopCat.of (Σ _ : ι, Circle × Circle) ⟶ TopCat.of (Σ _ : ι, SolidTorus) :=
  TopCat.ofHom ⟨Sigma.map id fun _ ↦ SolidTorus.boundaryInclusion,
    Continuous.sigma_map fun _ ↦ SolidTorus.isEmbedding_boundaryInclusion.continuous⟩

private theorem sigmaBoundaryInclusion_apply (i : ι) (q : Circle × Circle) :
    sigmaBoundaryInclusion ι ⟨i, q⟩ = ⟨i, SolidTorus.boundaryInclusion q⟩ :=
  rfl

/-- Attaching maps `e i` of the boundary tori of a family of solid tori, as a map of `TopCat`. -/
private def sigmaAttach (e : ι → C(Circle × Circle, E)) :
    TopCat.of (Σ _ : ι, Circle × Circle) ⟶ TopCat.of E :=
  TopCat.ofHom ⟨fun p ↦ e p.1 p.2, continuous_sigma fun i ↦ (e i).continuous⟩

/-- The space obtained from `E` by attaching a solid torus along the map `e i` of its boundary
torus, for every `i`. -/
private abbrev attach (e : ι → C(Circle × Circle, E)) : TopCat :=
  pushout (sigmaAttach e) (sigmaBoundaryInclusion ι)

private theorem isPushout_attach (e : ι → C(Circle × Circle, E)) :
    IsPushout (sigmaAttach e) (sigmaBoundaryInclusion ι)
      (pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι))
      (pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι)) :=
  .of_hasPushout _ _

/-- The boundary inclusion of the solid tori extends disjoint open sets: an open subset `U` of the
boundary tori is the trace of the open collar of points `(w, z)` with `1 / 2 < ‖w‖` and
`(w / ‖w‖, z) ∈ U`, and collars over disjoint sets are disjoint. -/
private theorem extendsDisjointOpens_sigmaBoundaryInclusion :
    TopCat.extendsDisjointOpens (sigmaBoundaryInclusion ι) := by
  -- The coordinates of the boundary tori in `ℂ × S¹`.
  let μ (q : Circle × Circle) : ℂ × Circle := ((q.1 : ℂ), q.2)
  have hμ : IsEmbedding μ := IsEmbedding.subtypeVal.prodMap IsEmbedding.id
  -- The radial projection onto the boundary torus, continuous away from the core.
  let N : Set SolidTorus := {p | 1 / 2 < ‖(p.1 : ℂ)‖}
  let ρ (p : SolidTorus) : ℂ × Circle := (‖(p.1 : ℂ)‖⁻¹ • (p.1 : ℂ), p.2)
  have hN : IsOpen N := isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst).norm
  have hρ : ContinuousOn ρ N := by
    have hw : Continuous fun p : SolidTorus ↦ (p.1 : ℂ) :=
      continuous_subtype_val.comp continuous_fst
    refine ContinuousOn.prodMk ((ContinuousOn.inv₀ hw.norm.continuousOn fun p hp ↦ ?_).smul
      hw.continuousOn) continuous_snd.continuousOn
    exact (lt_trans (by norm_num) hp).ne'
  have hρμ (q : Circle × Circle) : ρ (SolidTorus.boundaryInclusion q) = μ q := by
    simp [ρ, μ]
  -- An open subset `U` of the `i`-th boundary torus extends to an open collar in the `i`-th solid
  -- torus, whose points project into `U`.
  have collar (U : Set (Circle × Circle)) (hU : IsOpen U) :
      ∃ U' : Set SolidTorus, IsOpen U' ∧ SolidTorus.boundaryInclusion ⁻¹' U' = U ∧
        ∀ p ∈ U', ∃ q ∈ U, μ q = ρ p := by
    obtain ⟨W, hW, rfl⟩ := hμ.isInducing.isOpen_iff.1 hU
    refine ⟨N ∩ ρ ⁻¹' W, hρ.isOpen_inter_preimage hN hW, ?_, ?_⟩
    · ext q
      simp [N, hρμ, show (2⁻¹ : ℝ) < 1 by norm_num]
    · rintro p ⟨hp, hpW⟩
      have h₁ : ‖‖(p.1 : ℂ)‖⁻¹ • (p.1 : ℂ)‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (lt_trans (by norm_num) hp).ne']
      exact ⟨(⟨_, mem_sphere_zero_iff_norm.2 h₁⟩, p.2), hpW, rfl⟩
  have hμinj : Injective μ := hμ.injective
  rw [TopCat.extendsDisjointOpens_iff]
  intro U V hU hV hUV
  choose U' hU' hU'U hU'ρ using fun i ↦ collar _ (isOpen_sigma_iff.1 hU i)
  choose V' hV' hV'V hV'ρ using fun i ↦ collar _ (isOpen_sigma_iff.1 hV i)
  refine ⟨{p | p.2 ∈ U' p.1}, {p | p.2 ∈ V' p.1}, isOpen_sigma_iff.2 hU', isOpen_sigma_iff.2 hV',
    disjoint_left.2 fun p hpU hpV ↦ ?_, ?_, ?_⟩
  · obtain ⟨q, hq, hqp⟩ := hU'ρ p.1 p.2 hpU
    obtain ⟨q', hq', hq'p⟩ := hV'ρ p.1 p.2 hpV
    obtain rfl := hμinj (hqp.trans hq'p.symm)
    exact disjoint_left.1 hUV hq hq'
  · ext ⟨i, q⟩
    exact Set.ext_iff.1 (hU'U i) q
  · ext ⟨i, q⟩
    exact Set.ext_iff.1 (hV'V i) q

private theorem range_inl_union_range_inr (e : ι → C(Circle × Circle, E)) :
    range (pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι)) ∪
      range (pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι)) = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨y, rfl⟩ | ⟨p, rfl, -⟩ :=
    Types.eq_or_eq_of_isPushout' ((forget TopCat).map_isPushout (isPushout_attach e)) x
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨p, rfl⟩

private theorem inl_apply_eq_inr (e : ι → C(Circle × Circle, E)) (i : ι) (q : Circle × Circle) :
    pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι) (e i q) =
      pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι) ⟨i, SolidTorus.boundaryInclusion q⟩ :=
  ConcreteCategory.congr_hom (isPushout_attach e).w ⟨i, q⟩

/-- When the attaching maps are jointly injective, a point of `E` and a point of a solid torus are
identified exactly when the latter is a point of the boundary torus attached to the former. -/
private theorem inl_eq_inr_iff {e : ι → C(Circle × Circle, E)}
    (he : Injective fun p : Σ _ : ι, Circle × Circle ↦ e p.1 p.2) (x : E)
    (p : Σ _ : ι, SolidTorus) :
    pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι) x =
        pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι) p ↔
      ∃ q : Σ _ : ι, Circle × Circle, e q.1 q.2 = x ∧
        (⟨q.1, SolidTorus.boundaryInclusion q.2⟩ : Σ _ : ι, SolidTorus) = p :=
  Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    ((forget TopCat).map_isPushout (isPushout_attach e)).isColimit he x p

variable [Finite ι]

private theorem isClosedEmbedding_sigmaBoundaryInclusion :
    IsClosedEmbedding (sigmaBoundaryInclusion ι) :=
  (sigmaBoundaryInclusion ι).hom.continuous.isClosedEmbedding fun ⟨i, q⟩ ⟨j, q'⟩ hq ↦ by
    rw [sigmaBoundaryInclusion_apply, sigmaBoundaryInclusion_apply, Sigma.mk.inj_iff] at hq
    obtain ⟨rfl, hq⟩ := hq
    rw [SolidTorus.isEmbedding_boundaryInclusion.injective (eq_of_heq hq)]

private theorem isClosedEmbedding_inl (e : ι → C(Circle × Circle, E)) :
    IsClosedEmbedding (pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι)) :=
  TopCat.isClosedEmbedding_of_isPushout (isPushout_attach e)
    isClosedEmbedding_sigmaBoundaryInclusion

/-- The space obtained by attaching finitely many solid tori to a Hausdorff space is Hausdorff. -/
private theorem t2Space_attach [T2Space E] (e : ι → C(Circle × Circle, E)) :
    T2Space (attach e) := by
  have : T2Space (TopCat.of E) := inferInstanceAs (T2Space E)
  have : T2Space (TopCat.of (Σ _ : ι, SolidTorus)) := inferInstanceAs (T2Space (Σ _ : ι, _))
  have : RegularSpace (TopCat.of (Σ _ : ι, SolidTorus)) :=
    inferInstanceAs (RegularSpace (Σ _ : ι, _))
  exact TopCat.t2Space_of_isPushout (isPushout_attach e)
    extendsDisjointOpens_sigmaBoundaryInclusion
    isClosedEmbedding_sigmaBoundaryInclusion.isClosed_range

/-- The space obtained by attaching finitely many solid tori to a compact space is compact. -/
private theorem compactSpace_attach [CompactSpace E] (e : ι → C(Circle × Circle, E)) :
    CompactSpace (attach e) := by
  refine ⟨?_⟩
  rw [← range_inl_union_range_inr e]
  exact (isCompact_range (pushout.inl (sigmaAttach e) _).hom.continuous).union
    (isCompact_range (pushout.inr _ (sigmaBoundaryInclusion ι)).hom.continuous)

/-- When the attaching maps are jointly injective, the solid tori are embedded in the space
obtained by attaching them to a Hausdorff space. -/
private theorem isClosedEmbedding_inr [T2Space E] {e : ι → C(Circle × Circle, E)}
    (he : Injective fun p : Σ _ : ι, Circle × Circle ↦ e p.1 p.2) :
    IsClosedEmbedding (pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι)) :=
  TopCat.isClosedEmbedding_of_isPushout (isPushout_attach e).flip
    ((sigmaAttach e).hom.continuous.isClosedEmbedding he)

end Attach

/-! ### Every slope is the filling slope of a matrix gluing -/

namespace IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}

/-- **Every slope is the filling slope of a matrix gluing.** A primitive class with coordinates
`(p, q)` in the framing of `Φ` is the first column of an invertible integral matrix
`[[p, -b], [q, a]]`, with `a p + b q = 1`, and gluing the solid torus by the homeomorphism of
`S¹ × S¹` that this matrix induces sends its meridian to the class. -/
theorem exists_fillingSlope_torusHomeomorph_eq (h : IsSolidTorusNeighborhood f Φ)
    (s : Slope h.framedBoundaryTorus.H) :
    ∃ A : GL (Fin 2) ℤ, h.fillingSlope A.torusHomeomorph = s := by
  induction s using Slope.induction_on with
  | h v hv =>
    set c := h.framedBoundaryTorus.coord v with hc
    have hcop : IsCoprime c.1 c.2 :=
      isPrimitive_prod_iff.1 ((h.framedBoundaryTorus.coord.isPrimitive_iff).2 hv)
    obtain ⟨a, b, hab⟩ := hcop
    let M : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![c.1, -b; c.2, a], by rw [Matrix.det_fin_two_of]; linear_combination hab⟩
    have hM : ((Matrix.SpecialLinearGroup.toGL M : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![c.1, -b; c.2, a] :=
      rfl
    refine ⟨Matrix.SpecialLinearGroup.toGL M, ?_⟩
    rw [fillingSlope_torusHomeomorph]
    refine Slope.mk_eq_mk _ _ (Or.inl (h.framedBoundaryTorus.coord.injective ?_))
    rw [FramedBoundaryTorus.coord_torusCurveClass, ← hc, hM]
    simp

/-! ### Dehn fillings of knot exteriors -/

/-- The attaching map of the filling solid torus of a knot exterior along a gluing `g`: the point
`q` of the boundary torus of the solid torus goes to the point `Φ (g q)` of the boundary torus of
the exterior. -/
private def fillingAttach (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) : Unit → C(Circle × Circle, knotExterior (Φ := Φ)) :=
  fun _ ↦ ⟨h.exteriorBoundaryInclusion ∘ g,
    h.isEmbedding_exteriorBoundaryInclusion.continuous.comp g.continuous⟩

omit [T2Space X] in
private theorem injective_fillingAttach (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) :
    Injective fun p : Σ _ : Unit, Circle × Circle ↦ h.fillingAttach g p.1 p.2 := by
  rintro ⟨⟨⟩, q⟩ ⟨⟨⟩, q'⟩ hq
  obtain rfl := g.injective (h.exteriorBoundaryInclusion_injective hq)
  rfl

/-- **The Dehn filling space** of a knot exterior along a gluing `g` of the boundary tori: the
exterior with a solid torus `D² × S¹` attached, the point `q` of the boundary torus of the solid
torus being identified with the point `Φ (g q)` of the boundary torus of the exterior. The Dehn
filling it carries is `TauCeti.IsSolidTorusNeighborhood.dehnFillingOfGluing`. -/
def dehnFillingSpace (h : IsSolidTorusNeighborhood f Φ) (g : Circle × Circle ≃ₜ Circle × Circle) :
    TopCat :=
  attach (h.fillingAttach g)

/-- A Dehn filling space of a knot exterior in a Hausdorff space is Hausdorff. -/
instance (h : IsSolidTorusNeighborhood f Φ) (g : Circle × Circle ≃ₜ Circle × Circle) :
    T2Space (h.dehnFillingSpace g) :=
  t2Space_attach (h.fillingAttach g)

/-- A Dehn filling space of a knot exterior in a compact space is compact. -/
instance [CompactSpace X] (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) : CompactSpace (h.dehnFillingSpace g) :=
  have : CompactSpace (knotExterior (Φ := Φ)) := isCompact_iff_compactSpace.1 h.isCompact_exterior
  compactSpace_attach (h.fillingAttach g)

/-- **The Dehn filling along a gluing.** The knot exterior and the solid torus are closed subsets
of the Dehn filling space `TauCeti.IsSolidTorusNeighborhood.dehnFillingSpace h g`, glued along
`g`, so that space is a Dehn filling of the exterior along the filling slope of `g`. -/
def dehnFillingOfGluing (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) :
    DehnFilling h (h.fillingSlope g) (h.dehnFillingSpace g) where
  exteriorEmbedding := pushout.inl (sigmaAttach (h.fillingAttach g)) (sigmaBoundaryInclusion Unit)
  isClosedEmbedding_exteriorEmbedding := isClosedEmbedding_inl _
  solidTorusEmbedding p :=
    pushout.inr (sigmaAttach (h.fillingAttach g)) (sigmaBoundaryInclusion Unit) ⟨(), p⟩
  isClosedEmbedding_solidTorusEmbedding :=
    (isClosedEmbedding_inr (h.injective_fillingAttach g)).comp IsClosedEmbedding.sigmaMk
  gluing := g
  exteriorEmbedding_exteriorBoundaryInclusion q := inl_apply_eq_inr (h.fillingAttach g) () q
  range_union_range := by
    refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hx⟩ | ⟨⟨⟨⟩, p⟩, hp⟩ :=
      eq_univ_iff_forall.1 (range_inl_union_range_inr (h.fillingAttach g)) y
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨p, hp⟩
  range_inter_range_subset := by
    rintro _ ⟨⟨x, rfl⟩, p, hp⟩
    obtain ⟨⟨⟨⟩, q⟩, -, hq⟩ :=
      (inl_eq_inr_iff (h.injective_fillingAttach g) x ⟨(), p⟩).1 hp.symm
    obtain rfl : SolidTorus.boundaryInclusion q = p := eq_of_heq (Sigma.mk.inj_iff.1 hq).2
    exact ⟨q, hp⟩
  fillingSlope_gluing := rfl

/-- The Dehn filling along a gluing glues the boundary tori by that gluing. -/
@[simp]
theorem dehnFillingOfGluing_gluing (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) : (h.dehnFillingOfGluing g).gluing = g :=
  (rfl)

/-- **Existence of Dehn fillings.** A knot exterior has a Dehn filling along every slope, with a
gluing induced by an invertible integral matrix. -/
theorem exists_dehnFilling (h : IsSolidTorusNeighborhood f Φ) (s : Slope h.framedBoundaryTorus.H) :
    ∃ A : GL (Fin 2) ℤ, Nonempty (DehnFilling h s (h.dehnFillingSpace A.torusHomeomorph)) := by
  obtain ⟨A, rfl⟩ := h.exists_fillingSlope_torusHomeomorph_eq s
  exact ⟨A, ⟨h.dehnFillingOfGluing _⟩⟩

end IsSolidTorusNeighborhood

/-! ### Dehn fillings of link exteriors -/

namespace IsSolidTorusLinkNeighborhood

variable {ι : Type} {X : Type} [TopologicalSpace X] [T2Space X] {f : ι → Circle → X}
  {Φ : ι → SolidTorus → X}

/-- The attaching maps of the filling solid tori of a link exterior along gluings `g i`: the point
`q` of the boundary torus of the `i`-th solid torus goes to the point `Φ i (g i q)` of the `i`-th
boundary torus of the exterior. -/
private def fillingAttach (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) : ι → C(Circle × Circle, linkExterior Φ) :=
  fun i ↦ ⟨h.exteriorBoundaryInclusion i ∘ g i,
    (h.isEmbedding_exteriorBoundaryInclusion i).continuous.comp (g i).continuous⟩

omit [T2Space X] in
/-- The boundary tori of distinct components are disjoint, so the attaching maps are jointly
injective. -/
private theorem injective_fillingAttach (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) :
    Injective fun p : Σ _ : ι, Circle × Circle ↦ h.fillingAttach g p.1 p.2 := by
  rintro ⟨i, q⟩ ⟨j, q'⟩ hq
  obtain rfl : i = j := by
    by_contra hij
    have hx : Φ i (SolidTorus.boundaryInclusion (g i q)) =
        Φ j (SolidTorus.boundaryInclusion (g j q')) := by
      simpa [fillingAttach] using congrArg Subtype.val hq
    exact (h.pairwiseDisjoint_range hij).ne_of_mem (mem_range_self _) (mem_range_self _) hx
  obtain rfl := (g i).injective (h.exteriorBoundaryInclusion_injective i hq)
  rfl

/-- **The Dehn filling space** of the exterior of a link with finitely many components along
gluings `g i` of the boundary tori: the exterior with a solid torus `D² × S¹` attached for each
component `i`, the point `q` of its boundary torus being identified with the point `Φ i (g i q)`
of the `i`-th boundary torus of the exterior. The Dehn filling it carries is
`TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingOfGluing`. -/
def linkDehnFillingSpace (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) : TopCat :=
  attach (h.fillingAttach g)

variable [Finite ι]

/-- A Dehn filling space of the exterior of a link with finitely many components in a Hausdorff
space is Hausdorff. -/
instance (h : IsSolidTorusLinkNeighborhood f Φ) (g : ι → Circle × Circle ≃ₜ Circle × Circle) :
    T2Space (h.linkDehnFillingSpace g) :=
  t2Space_attach (h.fillingAttach g)

/-- A Dehn filling space of the exterior of a link with finitely many components in a compact
space is compact. -/
instance [CompactSpace X] (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) : CompactSpace (h.linkDehnFillingSpace g) :=
  have : CompactSpace (linkExterior Φ) := isCompact_iff_compactSpace.1 h.isCompact_linkExterior
  compactSpace_attach (h.fillingAttach g)

/-- **The Dehn filling of a link exterior along gluings.** The link exterior and the solid tori are
closed subsets of the Dehn filling space `TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingSpace
h g`, the `i`-th solid torus being glued along `g i`, so that space is a Dehn filling of the
exterior along the filling slopes of the `g i`. -/
def linkDehnFillingOfGluing (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) :
    LinkDehnFilling h (fun i ↦ (h.neighborhood i).fillingSlope (g i))
      (h.linkDehnFillingSpace g) where
  exteriorEmbedding := pushout.inl (sigmaAttach (h.fillingAttach g)) (sigmaBoundaryInclusion ι)
  isClosedEmbedding_exteriorEmbedding := isClosedEmbedding_inl _
  solidTorusEmbedding i p :=
    pushout.inr (sigmaAttach (h.fillingAttach g)) (sigmaBoundaryInclusion ι) ⟨i, p⟩
  isClosedEmbedding_solidTorusEmbedding _ :=
    (isClosedEmbedding_inr (h.injective_fillingAttach g)).comp IsClosedEmbedding.sigmaMk
  gluing := g
  exteriorEmbedding_exteriorBoundaryInclusion i q := inl_apply_eq_inr (h.fillingAttach g) i q
  range_union_iUnion_range := by
    refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hx⟩ | ⟨⟨i, p⟩, hp⟩ :=
      eq_univ_iff_forall.1 (range_inl_union_range_inr (h.fillingAttach g)) y
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr (mem_iUnion.2 ⟨i, p, hp⟩)
  range_inter_range_subset i := by
    rintro _ ⟨⟨x, rfl⟩, p, hp⟩
    obtain ⟨⟨j, q⟩, -, hq⟩ :=
      (inl_eq_inr_iff (h.injective_fillingAttach g) x ⟨i, p⟩).1 hp.symm
    cases hq
    exact ⟨q, hp⟩
  pairwiseDisjoint_range i j hij := by
    refine disjoint_left.2 ?_
    rintro _ ⟨p, rfl⟩ ⟨p', hp'⟩
    exact hij (congrArg Sigma.fst ((isClosedEmbedding_inr (h.injective_fillingAttach g)).injective
      hp')).symm
  fillingSlope_gluing _ := rfl

/-- The Dehn filling of a link exterior along gluings glues the boundary tori by those
gluings. -/
@[simp]
theorem linkDehnFillingOfGluing_gluing (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) : (h.linkDehnFillingOfGluing g).gluing = g :=
  (rfl)

/-- **Existence of Dehn fillings of link exteriors.** The exterior of a link with finitely many
components has a Dehn filling along every family of slopes, one on each boundary torus, with
gluings induced by invertible integral matrices. In particular every rational surgery on a link in
`S³` (`TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope`) exists. -/
theorem exists_linkDehnFilling (h : IsSolidTorusLinkNeighborhood f Φ)
    (s : ∀ i, Slope (h.neighborhood i).framedBoundaryTorus.H) :
    ∃ A : ι → GL (Fin 2) ℤ,
      Nonempty (LinkDehnFilling h s (h.linkDehnFillingSpace fun i ↦ (A i).torusHomeomorph)) := by
  choose A hA using fun i ↦ (h.neighborhood i).exists_fillingSlope_torusHomeomorph_eq (s i)
  obtain rfl : (fun i ↦ (h.neighborhood i).fillingSlope (A i).torusHomeomorph) = s := funext hA
  exact ⟨A, ⟨h.linkDehnFillingOfGluing _⟩⟩

end IsSolidTorusLinkNeighborhood

end TauCeti
