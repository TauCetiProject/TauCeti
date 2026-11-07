/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.AffineAction
public import TauCeti.Algebra.Module.ZLattice.Family.Manifold
public import TauCeti.Algebra.Module.ZLattice.Family.Topology

/-!
# Smooth affine actions on a family of tori

For a `C^n` family of full period lattices `P : Y → (Λ →ₗ[ℤ] E)`, fibrewise translation
`v +ᵥ [y, w] = [y, v + w]` is jointly `C^n` for the quotient atlas on `(Y × E)/Λ`
(`TauCeti.contMDiffVAdd_torusFamilyTranslationAddAction`). Consequently the affine map
`[y, v] ↦ R g y v +ᵥ b g y` is `C^n` whenever the evaluation `(y, v) ↦ R g y v` and the
section `b g` are `C^n` (`TauCeti.contMDiff_torusFamilyAffineMap`). The section is valued in
the torus family itself: it is not required to admit a global vector-space lift.

For cocycles defining an action, `TauCeti.contMDiffConstSMul_torusFamilyAffineMulAction`
provides Mathlib's pointwise regularity class. For a group, installing this class makes
`Diffeomorph.constSmul` available, with inverse given by the inverse group element. In particular,
over `ℂ` with holomorphic periods, linear-part evaluations and translation sections, every
affine action map is biholomorphic. No freeness of the action on the base is required.

If moreover `Γ` acts properly discontinuously on the base (for instance, if `Γ` is finite) and
freely on the family, the orbit space `X / Γ` of the family `X = (Y × E)/Λ` carries Mathlib's
quotient atlas (`TauCeti.torusFamilyAffineQuotientChartedSpace`), for which it is a `C^n` manifold
(`TauCeti.isManifold_torusFamilyAffineQuotient`) and the orbit map `X → X / Γ` is a `C^n` local
diffeomorphism (`TauCeti.isLocalDiffeomorph_torusFamilyAffineQuotient_mk`). Freeness on the
family is weaker than freeness on the base: a base stabilizer can act on its fibre by a
translation without fixed points. Over `ℂ` with holomorphic data, `X / Γ` is a complex manifold.
The inverse of each of its charts is the inverse of a chart of `X` followed by the orbit map
(`TauCeti.exists_symm_eq_mk_of_mem_atlas_torusFamilyAffineQuotient`).

The regularity statements use any normed scalar field `𝕜`; the real structure of `E` is used
only for the full-lattice hypotheses. Smoothness is checked before taking the period quotient,
using its surjective local diffeomorphism, rather than through a real period frame (which need
not be holomorphic).

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Function.Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)

/-- Fibrewise translation is jointly `C^n` for the quotient manifold structure of a `C^n`
family of full lattices. For holomorphic periods over `ℂ`, it is jointly holomorphic. -/
theorem contMDiffVAdd_torusFamilyTranslationAddAction :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyTranslationAddAction P
    ContMDiffVAdd 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) n E
      (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyTranslationAddAction P
  have hq := isLocalDiffeomorph_torusFamily_mk P hinj hP
  refine ⟨(hq.contMDiff_comp_prodMap_iff Quotient.mk_surjective le_rfl).1 ?_⟩
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, Pi.add_apply,
    torusFamilyTranslationAddAction_vadd_mk] using
    hq.contMDiff.comp (contMDiff_snd.fst.prodMk (contMDiff_fst.add contMDiff_snd.snd))

section Affine

variable {Γ : Type*} [Monoid Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)

/-- The affine map of `g` is `C^n` if its linear-part evaluation and its torus-valued translation
section are `C^n`. No global vector-space lift of the section is needed. -/
theorem contMDiff_torusFamilyAffineMap {g : Γ}
    (hR : ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) n
      (torusFamilyAffineMap R P ρ hequiv b hb g) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyTranslationAddAction P
  have := contMDiffVAdd_torusFamilyTranslationAddAction P hinj hP
  refine ((isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff_comp_iff
    Quotient.mk_surjective le_rfl).1 ?_
  simpa only [Function.comp_def, torusFamilyAffineMap_mk] using
    (contMDiff_vadd (I := 𝓘(𝕜, E)) (I' := I.prod 𝓘(𝕜, E))).comp
      (hR.prodMk (hbc.comp contMDiff_fst))

variable (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

/-- A `C^n` affine cocycle acts by `C^n` maps on the torus family. For a group, this class
also supplies `C^n` inverses through `Diffeomorph.constSmul`; over `ℂ` with holomorphic data,
these are biholomorphisms. Neither a free base action nor global vector lifts are required. -/
theorem contMDiffConstSMul_torusFamilyAffineMulAction
    (hR : ∀ g : Γ,
      ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ∀ g, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    ContMDiffConstSMul (I.prod 𝓘(𝕜, E)) n Γ
      (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  refine ⟨fun g ↦ ?_⟩
  simpa only [torusFamilyAffineMulAction_smul] using
    contMDiff_torusFamilyAffineMap P hinj hP R ρ hequiv b hb (hR g) (hbc g)

end Affine

/-! ### The quotient by a free affine action -/

section Quotient

variable {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

/-- **The atlas of the quotient by a free affine action.** Let `Γ` act properly discontinuously
on `Y`, and freely on the family of tori `X = (Y × E)/Λ` of a continuous family of full lattices
by an affine cocycle with continuous linear-part evaluations and translation sections. This is
Mathlib's quotient atlas `MulAction.instChartedSpaceQuotient` on the orbit space `X / Γ`: its
charts are local sections of the orbit map followed by charts of `X`. It does not depend on the
proofs of the hypotheses. -/
@[instance_reducible]
noncomputable def torusFamilyAffineQuotientChartedSpace (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hRc : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
    (hfree : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E))) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    ChartedSpace (ModelProd H E)
      (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := H) P hcont hinj
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  haveI := continuousConstVAdd_periodAddAction P hcont
  haveI := t2Space_torusFamily P hcont hinj
  haveI := (AddAction.isOpenQuotientMap_quotientMk (Γ := Λ) (T := Y × E)).locallyCompactSpace
  haveI := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul
  haveI := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    hcont hRc hbc
  haveI := hfree
  MulAction.instChartedSpaceQuotient (H := ModelProd H E)

/-- The inverse of a chart of the quotient atlas on `X / Γ` is the inverse of a chart of the
family `X` followed by the orbit map `X → X / Γ`. -/
theorem exists_symm_eq_mk_of_mem_atlas_torusFamilyAffineQuotient
    (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hRc : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
    (hfree : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
    {e : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      OpenPartialHomeomorph (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
        (ModelProd H E)}
    (he : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
        hbone hbmul hcont hRc hbc hfree
      e ∈ atlas (ModelProd H E)
        (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E)))) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P hcont hinj
    ∃ x : AddAction.orbitRel.Quotient Λ (Y × E), ∀ w ∈ e.target,
      w ∈ (chartAt (ModelProd H E) x).target ∧
        e.symm w = Quotient.mk _ ((chartAt (ModelProd H E) x).symm w) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P hcont hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := continuousConstVAdd_periodAddAction P hcont
  have := t2Space_torusFamily P hcont hinj
  have := (AddAction.isOpenQuotientMap_quotientMk (Γ := Λ) (T := Y × E)).locallyCompactSpace
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    hcont hRc hbc
  have := hfree
  exact exists_symm_eq_quotientMk_of_mem_atlas_quotient he

variable (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g))
  (hfree : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))

/-- The orbit map `X → X / Γ` of a free `C^n` affine action is a `C^n` local diffeomorphism, and
`X / Γ` is a `C^n` manifold. -/
private theorem isLocalDiffeomorph_torusFamilyAffineQuotient_mk_and_isManifold :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul hbone
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
      hfree
    IsLocalDiffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) n
        (Quotient.mk (MulAction.orbitRel Γ (AddAction.orbitRel.Quotient Λ (Y × E)))) ∧
      IsManifold (I.prod 𝓘(𝕜, E)) n
        (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
  have := t2Space_torusFamily P (fun l ↦ (hP l).continuous) hinj
  have := (AddAction.isOpenQuotientMap_quotientMk (Γ := Λ) (T := Y × E)).locallyCompactSpace
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
  have := hfree
  have := isManifold_torusFamily P hinj hP
  have := contMDiffConstSMul_torusFamilyAffineMulAction P hinj hP R ρ hequiv b hb hone hmul hbone
    hbmul hR hbc
  exact ⟨isLocalDiffeomorph_quotientMk, instIsManifoldQuotient⟩

/-- **The quotient by a free affine action is a manifold.** Let `Γ` act properly discontinuously
on `Y`, and freely on the family of tori `X = (Y × E)/Λ` of a `C^n` family of full lattices by an
affine cocycle with `C^n` linear-part evaluations and translation sections. Then the orbit space
`X / Γ` is a `C^n` manifold for the quotient atlas. Over `ℂ` with holomorphic data and `n = ω`, it
is a complex manifold. -/
theorem isManifold_torusFamilyAffineQuotient :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul hbone
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
      hfree
    IsManifold (I.prod 𝓘(𝕜, E)) n
      (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) :=
  (isLocalDiffeomorph_torusFamilyAffineQuotient_mk_and_isManifold P hinj hP R ρ hequiv b hb hone
    hmul hbone hbmul hR hbc hfree).2

/-- **The orbit map of a free affine action is a local diffeomorphism.** Under the hypotheses of
`TauCeti.isManifold_torusFamilyAffineQuotient`, the orbit map `X → X / Γ` is a `C^n` local
diffeomorphism. Over `ℂ` with holomorphic data and `n = ω`, it is a local biholomorphism. -/
theorem isLocalDiffeomorph_torusFamilyAffineQuotient_mk :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul hbone
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
      hfree
    IsLocalDiffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) n
      (Quotient.mk (MulAction.orbitRel Γ (AddAction.orbitRel.Quotient Λ (Y × E)))) :=
  (isLocalDiffeomorph_torusFamilyAffineQuotient_mk_and_isManifold P hinj hP R ρ hequiv b hb hone
    hmul hbone hbmul hR hbc hfree).1

end Quotient

end TauCeti
