/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Action
public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.AffineAction
public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.ContMDiff
public import TauCeti.Algebra.Module.ZLattice.Family.Topology
public import TauCeti.Geometry.Manifold.Quotient.Descent

/-!
# Smooth equivariant base change of actions on families of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a `C^n` family of full period lattices over a `C^n` manifold `Y`,
carrying a `C^n` affine action `g • [y, v] = R g y v +ᵥ b g y` of `Γ`
(`TauCeti.torusFamilyAffineMulAction`, `TauCeti.contMDiffConstSMul_torusFamilyAffineMulAction`).
Given a `C^n` map `f : Z → Y` intertwining an action of `Γ'` on a `C^n` manifold `Z` with the
action of `Γ` on `Y` along `σ : Γ' →* Γ`, this file proves that the pulled-back affine action on
`(Z × E)/Λ` is `C^n`, descends `C^m`-smoothly (`m ≤ n`) to free properly discontinuous second
quotients `((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ`, and restricts any properly discontinuous `C^n` affine
action over `Y` to a free properly discontinuous `C^n` action over `TauCeti.freeLocus Γ Y`.

* `TauCeti.contMDiff_torusFamilyBaseChangeTranslation` proves that the pulled-back torus-valued
  translation section `TauCeti.torusFamilyBaseChangeTranslation` is `C^n`, using the smooth
  universal property `TauCeti.contMDiff_torusFamilyBaseChangeEquiv_symm` rather than vector-space
  lifts.
* `TauCeti.contMDiff_torusFamilyBaseChangeAffineMap`,
  `TauCeti.contMDiffConstSMul_torusFamilyBaseChangeAffineMulAction`, and
  `TauCeti.contMDiffConstSMul_torusFamilyBaseChangeLinearMulAction` give `C^n` regularity of the
  pulled-back affine and linear actions.
* `TauCeti.contMDiff_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom` proves that when `Γ` and
  `Γ'` act properly discontinuously on the bases and freely on the total spaces `(Y × E)/Λ` and
  `(Z × E)/Λ` (freeness on the bases is not required), the induced map of second-quotient
  manifolds `((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` is `C^m` for `m ≤ n`. Over `𝕜 = ℂ` with holomorphic
  data, it is holomorphic.
* Restricting along `Subtype.val : TauCeti.freeLocus Γ Y → Y` needs no freeness assumption on `Y`
  or on `(Y × E)/Λ`: the second quotient `((freeLocus Γ Y × E)/Λ)/Γ` is a `C^n` manifold
  (`TauCeti.isManifold_torusFamilyAffineQuotient_freeLocus`), embeds as an open subset into the
  full second quotient `((Y × E)/Λ)/Γ`
  (`TauCeti.isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_freeLocus`), and
  maps `C^m`-smoothly into `((Y × E)/Λ)/Γ` whenever `Γ` acts freely on `(Y × E)/Λ`
  (`TauCeti.contMDiff_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_freeLocus`).

## Main results

* `TauCeti.contMDiff_torusFamilyBaseChangeTranslation`: the pulled-back torus-valued translation
  section is `C^n`.
* `TauCeti.contMDiffConstSMul_torusFamilyBaseChangeAffineMulAction`,
  `TauCeti.contMDiffConstSMul_torusFamilyBaseChangeLinearMulAction`: `C^n` regularity of the
  pulled-back affine and linear actions.
* `TauCeti.contMDiff_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom`: the induced map of
  second-quotient manifolds `((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` is `C^m` for `m ≤ n`.
* `TauCeti.isManifold_torusFamilyAffineQuotient_freeLocus`,
  `TauCeti.contMDiff_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_freeLocus`: manifold
  structure and smoothness of the open embedding (see
  `TauCeti.isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_freeLocus`) for an
  equivariant torus family restricted to the free locus of the base action.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices, and the actions of discrete groups on them).
-/

public section

open Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  {HY : Type*} [TopologicalSpace HY]
  {I : ModelWithCorners 𝕜 EY HY}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace HY Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace 𝕜 E] {n : ℕ∞ω} [IsManifold I n Y]

section BaseChange

variable {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
  {HZ : Type*} [TopologicalSpace HZ] {J : ModelWithCorners 𝕜 EZ HZ}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z] [T2Space Z] [LocallyCompactSpace Z]
  [IsManifold J n Z]
  (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y))
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)

/-! ### Smoothness of pulled-back actions -/

section Pullback

/-- **Smoothness of the pulled-back translation section.** When the period family `P`, the
equivariant base map `f : Z → Y`, the base action map `z ↦ g • z`, and the torus-valued
translation section `b (σ g)` are `C^n`, the pulled-back section
`torusFamilyBaseChangeTranslation P f σ hf b hb g` is `C^n`. Over `ℂ` with holomorphic data, it is
holomorphic without requiring any vector-space lift. -/
theorem contMDiff_torusFamilyBaseChangeTranslation {Γ Γ' : Type*} [SMul Γ Y] [SMul Γ' Z]
    (f : Z → Y) (hf_diff : ContMDiff J I n f) (σ : Γ' → Γ)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    {g : Γ'} (hg : ContMDiff J J n (g • · : Z → Z))
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
      ContMDiff I (I.prod 𝓘(𝕜, E)) n (b (σ g))) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
    ContMDiff J (J.prod 𝓘(𝕜, E)) n
      (torusFamilyBaseChangeTranslation P f σ hf b hb g) := by
  let : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (DiscreteTopology (LinearMap.range (P (f z))))
  let : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (IsZLattice ℝ (LinearMap.range (P (f z))))
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyChartedSpace (H := HZ) (P ∘ f)
    (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
  refine (contMDiff_torusFamilyBaseChangeEquiv_symm P hinj hP f hf_diff (g • ·)
    (fun z ↦ b (σ g) (f z)) (fun z ↦ (hb (σ g) (f z)).trans (hf g z).symm)
    hg (hbc.comp hf_diff)).congr fun z ↦ ?_
  symm
  exact (eq_torusFamilyBaseChangeTranslation_iff P f σ hf b hb g z).2
    ⟨torusFamilyProjection_baseChangeEquiv_symm P f _,
      torusFamilyBaseChangeMap_baseChangeEquiv_symm P f _⟩

omit [T2Space Y] [LocallyCompactSpace Y] [IsManifold I n Y] in
/-- A `C^n` linear cocycle pulled back along a `C^n` `σ`-equivariant map `f : Z → Y` acts by `C^n`
maps on `(Z × E)/Λ` whenever `Γ'` acts by `C^n` maps on `Z`. -/
theorem contMDiffConstSMul_torusFamilyBaseChangeLinearMulAction
    {Γ Γ' : Type*} [Monoid Γ] [Monoid Γ'] [MulAction Γ Y] [MulAction Γ' Z]
    [ContMDiffConstSMul J n Γ' Z]
    (R : Γ → Y → E →+ E) (hone : ∀ (y : Y) (v : E), R 1 y v = v)
    (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
    (ρ : Representation ℤ Γ Λ)
    (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
    (σ : Γ' →* Γ) (f : Z → Y) (hf_diff : ContMDiff J I n f)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
    letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
    ContMDiffConstSMul (J.prod 𝓘(𝕜, E)) n Γ' (AddAction.orbitRel.Quotient Λ (Z × E)) := by
  let : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (DiscreteTopology (LinearMap.range (P (f z))))
  let : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (IsZLattice ℝ (LinearMap.range (P (f z))))
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyChartedSpace (H := HZ) (P ∘ f)
    (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
  let _ := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
  have hq := isLocalDiffeomorph_torusFamily_mk (P ∘ f) (fun z ↦ hinj (f z))
    (fun l ↦ (hP l).comp hf_diff)
  refine ⟨fun g ↦ (hq.contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 ?_⟩
  have hcomm : (g • · : AddAction.orbitRel.Quotient Λ (Z × E) → _) ∘ Quotient.mk _ =
      Quotient.mk _ ∘ fun p : Z × E ↦ (g • p.1, R (σ g) (f p.1) p.2) := by
    funext ⟨z, v⟩
    simp
  rw [hcomm]
  exact hq.contMDiff.comp (((contMDiff_const_smul g).comp contMDiff_fst).prodMk
    ((hR (σ g)).comp (hf_diff.prodMap (contMDiff_id (I := 𝓘(𝕜, E))))))

/-- The pulled-back affine map of `g` on `(Z × E)/Λ` is `C^n` when `f`, `z ↦ g • z`, the linear
evaluation of `R (σ g)`, and the translation section `b (σ g)` are `C^n`. -/
theorem contMDiff_torusFamilyBaseChangeAffineMap
    {Γ Γ' : Type*} [Monoid Γ] [Monoid Γ'] [MulAction Γ Y] [MulAction Γ' Z]
    (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
    (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (σ : Γ' →* Γ) (f : Z → Y) (hf_diff : ContMDiff J I n f)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    {g : Γ'} (hg : ContMDiff J J n (g • · : Z → Z))
    (hR : ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R (σ g) p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
      ContMDiff I (I.prod 𝓘(𝕜, E)) n (b (σ g))) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
    ContMDiff (J.prod 𝓘(𝕜, E)) (J.prod 𝓘(𝕜, E)) n
      (torusFamilyAffineMap (fun g z ↦ R (σ g) (f z)) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb) g) :=
  let : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (DiscreteTopology (LinearMap.range (P (f z))))
  let : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (IsZLattice ℝ (LinearMap.range (P (f z))))
  contMDiff_torusFamilyAffineMap (P ∘ f) (fun z ↦ hinj (f z)) (fun l ↦ (hP l).comp hf_diff)
    (fun g z ↦ R (σ g) (f z)) (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (hR.comp (hf_diff.prodMap (contMDiff_id (I := 𝓘(𝕜, E)))))
    (contMDiff_torusFamilyBaseChangeTranslation P hinj hP f hf_diff σ hf b hb hg hbc)

/-- **Smoothness of the pulled-back affine action.** A `C^n` affine cocycle on `(Y × E)/Λ` pulled
back along a `C^n` `σ`-equivariant map `f : Z → Y` acts by `C^n` maps on `(Z × E)/Λ` whenever `Γ'`
acts by `C^n` maps on `Z`. Over `ℂ` with holomorphic data and a group `Γ'`, the pulled-back action
is by biholomorphisms; neither freeness on the bases nor vector lifts of `b` are required. -/
theorem contMDiffConstSMul_torusFamilyBaseChangeAffineMulAction
    {Γ Γ' : Type*} [Monoid Γ] [Monoid Γ'] [MulAction Γ Y] [MulAction Γ' Z]
    [ContMDiffConstSMul J n Γ' Z]
    (R : Γ → Y → E →+ E) (hone : ∀ (y : Y) (v : E), R 1 y v = v)
    (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
    (ρ : Representation ℤ Γ Λ)
    (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
    (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
    (σ : Γ' →* Γ) (f : Z → Y) (hf_diff : ContMDiff J I n f)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
      ∀ g : Γ, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g)) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    ContMDiffConstSMul (J.prod 𝓘(𝕜, E)) n Γ' (AddAction.orbitRel.Quotient Λ (Z × E)) :=
  let : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (DiscreteTopology (LinearMap.range (P (f z))))
  let : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (IsZLattice ℝ (LinearMap.range (P (f z))))
  contMDiffConstSMul_torusFamilyAffineMulAction (P ∘ f) (fun z ↦ hinj (f z))
    (fun l ↦ (hP l).comp hf_diff) (fun g z ↦ R (σ g) (f z)) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    (fun g ↦ (hR (σ g)).comp (hf_diff.prodMap (contMDiff_id (I := 𝓘(𝕜, E)))))
    (fun g ↦ contMDiff_torusFamilyBaseChangeTranslation P hinj hP f hf_diff σ hf b hb
      (contMDiff_const_smul g) (hbc (σ g)))

end Pullback

/-! ### Smooth descent to second quotients and restriction to the free locus -/

section SecondQuotient

variable {Γ : Type*} [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

/-- **Smoothness of the descended map of second quotients.** Suppose `Γ` and `Γ'` act properly
discontinuously on `Y` and `Z`, `Γ'` acts by `C^n` maps on `Z`, the affine cocycle `(R, b)` is
`C^n` on `Y`, and the total-space affine actions on `(Y × E)/Λ` and `(Z × E)/Λ` are free
(freeness of the actions on `Y` and `Z` is not required; see
`TauCeti.isCancelSMul_torusFamilyBaseChangeAffineMulAction`). Then for any `C^n` `σ`-equivariant
map `f : Z → Y` and `m ≤ n`, the induced map of quotient manifolds
`((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` is `C^m`. -/
theorem contMDiff_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom
    {Γ' : Type*} [Group Γ'] [MulAction Γ' Z]
    [ProperlyDiscontinuousSMul Γ Y] [ProperlyDiscontinuousSMul Γ' Z]
    [ContMDiffConstSMul J n Γ' Z]
    (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
      ∀ g : Γ, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g))
    (σ : Γ' →* Γ) (f : Z → Y) (hf_diff : ContMDiff J I n f)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hfreeY : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
    (hfreeZ : letI := periodAddAction (P ∘ f)
      letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      IsCancelSMul Γ' (AddAction.orbitRel.Quotient Λ (Z × E)))
    {m : ℕ∞ω} (hm : m ≤ n) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
    letI := t2Space_torusFamily P (fun l ↦ (hP l).continuous) hinj
    letI := t2Space_torusFamily (P ∘ f)
      (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
    letI := continuousConstVAdd_periodAddAction P (fun l ↦ (hP l).continuous)
    letI := continuousConstVAdd_periodAddAction (P ∘ f)
      (fun l ↦ ((hP l).comp hf_diff).continuous)
    letI : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
      AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
    letI : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Z × E)) :=
      AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    letI := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
      hbone hbmul
    letI := properlyDiscontinuousSMul_torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    letI := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
    letI : ContinuousConstSMul Γ' Z :=
      ⟨fun g ↦ (contMDiff_const_smul (I := J) (n := n) g).continuous⟩
    letI := continuousConstSMul_torusFamilyBaseChangeAffineMulAction R hone hmul P
      (fun l ↦ (hP l).continuous) ρ hequiv b hb hbone hbmul σ hf_diff.continuous hf
      (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
    letI := hfreeY
    letI := hfreeZ
    ContMDiff (J.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) m
      (MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineBaseChangeHom P b hb R ρ hequiv hone hmul hbone hbmul σ f hf)) := by
  let : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (DiscreteTopology (LinearMap.range (P (f z))))
  let : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (IsZLattice ℝ (LinearMap.range (P (f z))))
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyChartedSpace (H := HZ) (P ∘ f)
    (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
  have := t2Space_torusFamily P (fun l ↦ (hP l).continuous) hinj
  have := t2Space_torusFamily (P ∘ f)
    (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj (f z))
  have := continuousConstVAdd_periodAddAction P (fun l ↦ (hP l).continuous)
  have := continuousConstVAdd_periodAddAction (P ∘ f)
    (fun l ↦ ((hP l).comp hf_diff).continuous)
  have : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
    AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  have : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Z × E)) :=
    AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  have := isManifold_torusFamily P hinj hP
  have := isManifold_torusFamily (P ∘ f) (fun z ↦ hinj (f z)) (fun l ↦ (hP l).comp hf_diff)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
    hbone hbmul
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := contMDiffConstSMul_torusFamilyAffineMulAction P hinj hP R ρ hequiv b hb hone hmul
    hbone hbmul hR hbc
  have := contMDiffConstSMul_torusFamilyBaseChangeAffineMulAction P hinj hP R hone hmul ρ hequiv
    b hb hbone hbmul σ f hf_diff hf hR hbc
  have : ContinuousConstSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)) :=
    ⟨fun g ↦ (contMDiff_const_smul (I := I.prod 𝓘(𝕜, E)) (n := n) g).continuous⟩
  have : ContinuousConstSMul Γ' (AddAction.orbitRel.Quotient Λ (Z × E)) :=
    ⟨fun g ↦ (contMDiff_const_smul (I := J.prod 𝓘(𝕜, E)) (n := n) g).continuous⟩
  have := hfreeY
  have := hfreeZ
  refine contMDiff_orbitRelQuotientMap (I := J.prod 𝓘(𝕜, E)) (I' := I.prod 𝓘(𝕜, E)) (n := n) hm ?_
  rw [coe_torusFamilyAffineBaseChangeHom]
  exact (contMDiff_torusFamilyBaseChangeMap P hinj hP f hf_diff).of_le hm

end SecondQuotient

end BaseChange

/-! ### Restriction to the free locus of the base action -/

section FreeLocus

variable (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y))
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)
  {Γ : Type*} [Group Γ] [MulAction Γ Y]
  [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y] [ContMDiffConstSMul I n Γ Y]
  (R : Γ → Y → E →+ E) (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

/-- **Manifold structure of the second quotient over the free locus.** Let `Γ` act properly
discontinuously and by `C^n` maps on `Y` (possibly with fixed points), and act on `(Y × E)/Λ` by a
`C^n` affine cocycle `(R, b)`. Pulling the family and action back to `TauCeti.freeLocus Γ Y`
makes `((freeLocus Γ Y × E)/Λ)/Γ` a `C^n` manifold without assuming freeness on `Y` or on
`(Y × E)/Λ`. -/
theorem isManifold_torusFamilyAffineQuotient_freeLocus
    (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
      ∀ g : Γ, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g)) :
    letI : ∀ z : freeLocus Γ Y,
        DiscreteTopology (LinearMap.range ((P ∘ (Subtype.val : freeLocus Γ Y → Y)) z)) :=
      fun z ↦ inferInstanceAs (DiscreteTopology (LinearMap.range (P z.1)))
    letI : ∀ z : freeLocus Γ Y,
        IsZLattice ℝ (LinearMap.range ((P ∘ (Subtype.val : freeLocus Γ Y → Y)) z)) :=
      fun z ↦ inferInstanceAs (IsZLattice ℝ (LinearMap.range (P z.1)))
    letI := periodAddAction P
    letI := periodAddAction (P ∘ (Subtype.val : freeLocus Γ Y → Y))
    letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyChartedSpace (H := HY) (P ∘ (Subtype.val : freeLocus Γ Y → Y))
      (fun l ↦ (hP l).continuous.comp continuous_subtype_val) (fun z ↦ hinj z.1)
    letI := t2Space_torusFamily (P ∘ (Subtype.val : freeLocus Γ Y → Y))
      (fun l ↦ (hP l).continuous.comp continuous_subtype_val) (fun z ↦ hinj z.1)
    letI := continuousConstVAdd_periodAddAction (P ∘ (Subtype.val : freeLocus Γ Y → Y))
      (fun l ↦ (hP l).continuous.comp continuous_subtype_val)
    letI : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (freeLocus Γ Y × E)) :=
      AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
    letI := torusFamilyAffineMulAction
      (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (z : Y))
      (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) Subtype.val)
      (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (P ∘ (Subtype.val : freeLocus Γ Y → Y)) (ρ.comp (MonoidHom.id Γ))
      (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (torusFamilyBaseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y) (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) b hb)
      (torusFamilyProjection_baseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y)
        (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) hbmul)
    letI := properlyDiscontinuousSMul_torusFamilyAffineMulAction
      (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (z : Y))
      (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) Subtype.val)
      (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (P ∘ (Subtype.val : freeLocus Γ Y → Y)) (ρ.comp (MonoidHom.id Γ))
      (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (torusFamilyBaseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y) (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) b hb)
      (torusFamilyProjection_baseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y)
        (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) hbmul)
    letI := continuousConstSMul_torusFamilyBaseChangeAffineMulAction
      R hone hmul P (fun l ↦ (hP l).continuous) ρ hequiv b hb hbone hbmul
      (MonoidHom.id Γ) (f := (Subtype.val : freeLocus Γ Y → Y)) continuous_subtype_val
      (fun _ _ ↦ rfl) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
    letI := isCancelSMul_torusFamilyAffineMulAction
      (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (z : Y))
      (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) Subtype.val)
      (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (P ∘ (Subtype.val : freeLocus Γ Y → Y)) (ρ.comp (MonoidHom.id Γ))
      (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (torusFamilyBaseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y) (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) b hb)
      (torusFamilyProjection_baseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y)
        (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) hbmul)
    IsManifold (I.prod 𝓘(𝕜, E)) n
      (MulAction.orbitRel.Quotient Γ
        (AddAction.orbitRel.Quotient Λ (freeLocus Γ Y × E))) := by
  let f : freeLocus Γ Y → Y := Subtype.val
  -- `freeLocus.instChartedSpace` is the open-subset charted space on `(freeLocus Γ Y : Set Y)`.
  have hf_diff : ContMDiff I I n f := contMDiff_subtype_val (U := ⟨_, isOpen_freeLocus Γ Y⟩)
  let : ∀ z : freeLocus Γ Y, DiscreteTopology (LinearMap.range ((P ∘ f) z)) :=
    fun z ↦ inferInstanceAs (DiscreteTopology (LinearMap.range (P z.1)))
  let : ∀ z : freeLocus Γ Y, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) :=
    fun z ↦ inferInstanceAs (IsZLattice ℝ (LinearMap.range (P z.1)))
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyChartedSpace (H := HY) (P ∘ f)
    (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj z.1)
  have := t2Space_torusFamily (P ∘ f)
    (fun l ↦ ((hP l).comp hf_diff).continuous) (fun z ↦ hinj z.1)
  have := continuousConstVAdd_periodAddAction (P ∘ f)
    (fun l ↦ ((hP l).comp hf_diff).continuous)
  have : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (freeLocus Γ Y × E)) :=
    AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  have := isManifold_torusFamily (P ∘ f) (fun z ↦ hinj z.1) (fun l ↦ (hP l).comp hf_diff)
  let _ := torusFamilyAffineMulAction
    (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (f z))
    (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) f)
    (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
    (P ∘ f) (ρ.comp (MonoidHom.id Γ))
    (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
    (torusFamilyBaseChangeTranslation P f (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
    (torusFamilyProjection_baseChangeTranslation P f (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
    (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
      (fun _ _ ↦ rfl) hbmul)
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction
    (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (f z))
    (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) f)
    (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
    (P ∘ f) (ρ.comp (MonoidHom.id Γ))
    (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
    (torusFamilyBaseChangeTranslation P f (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
    (torusFamilyProjection_baseChangeTranslation P f (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
    (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
      (fun _ _ ↦ rfl) hbmul)
  have := contMDiffConstSMul_torusFamilyBaseChangeAffineMulAction P hinj hP R hone hmul ρ hequiv
    b hb hbone hbmul (MonoidHom.id Γ) f hf_diff (fun _ _ ↦ rfl) hR hbc
  have : ContinuousConstSMul Γ (AddAction.orbitRel.Quotient Λ (freeLocus Γ Y × E)) :=
    ⟨fun g ↦ (contMDiff_const_smul (I := I.prod 𝓘(𝕜, E)) (n := n) g).continuous⟩
  have := isCancelSMul_torusFamilyAffineMulAction
    (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (f z))
    (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) f)
    (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
    (P ∘ f) (ρ.comp (MonoidHom.id Γ))
    (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
    (torusFamilyBaseChangeTranslation P f (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
    (torusFamilyProjection_baseChangeTranslation P f (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
    (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
      (fun _ _ ↦ rfl) hbmul)
  exact instIsManifoldQuotient

/-- **Smoothness of the inclusion of the free-locus second quotient.** When `Γ` acts properly
discontinuously and by `C^n` maps on `Y`, and its `C^n` affine action on `(Y × E)/Λ` is free (even
though `Γ` may have fixed points on `Y`), the canonical open embedding
`((freeLocus Γ Y × E)/Λ)/Γ → ((Y × E)/Λ)/Γ` is `C^m` for every `m ≤ n`. -/
theorem contMDiff_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_freeLocus
    (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
      ∀ g : Γ, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g))
    (hfreeY : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
    {m : ℕ∞ω} (hm : m ≤ n) :
    letI : ∀ z : freeLocus Γ Y,
        DiscreteTopology (LinearMap.range ((P ∘ (Subtype.val : freeLocus Γ Y → Y)) z)) :=
      fun z ↦ inferInstanceAs (DiscreteTopology (LinearMap.range (P z.1)))
    letI : ∀ z : freeLocus Γ Y,
        IsZLattice ℝ (LinearMap.range ((P ∘ (Subtype.val : freeLocus Γ Y → Y)) z)) :=
      fun z ↦ inferInstanceAs (IsZLattice ℝ (LinearMap.range (P z.1)))
    letI := periodAddAction P
    letI := periodAddAction (P ∘ (Subtype.val : freeLocus Γ Y → Y))
    letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyChartedSpace (H := HY) (P ∘ (Subtype.val : freeLocus Γ Y → Y))
      (fun l ↦ (hP l).continuous.comp continuous_subtype_val) (fun z ↦ hinj z.1)
    letI := t2Space_torusFamily P (fun l ↦ (hP l).continuous) hinj
    letI := t2Space_torusFamily (P ∘ (Subtype.val : freeLocus Γ Y → Y))
      (fun l ↦ (hP l).continuous.comp continuous_subtype_val) (fun z ↦ hinj z.1)
    letI := continuousConstVAdd_periodAddAction P (fun l ↦ (hP l).continuous)
    letI := continuousConstVAdd_periodAddAction (P ∘ (Subtype.val : freeLocus Γ Y → Y))
      (fun l ↦ (hP l).continuous.comp continuous_subtype_val)
    letI : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
      AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
    letI : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (freeLocus Γ Y × E)) :=
      AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineMulAction
      (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (z : Y))
      (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) Subtype.val)
      (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (P ∘ (Subtype.val : freeLocus Γ Y → Y)) (ρ.comp (MonoidHom.id Γ))
      (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (torusFamilyBaseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y) (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) b hb)
      (torusFamilyProjection_baseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y)
        (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) hbmul)
    letI := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
      hbone hbmul
    letI := properlyDiscontinuousSMul_torusFamilyAffineMulAction
      (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (z : Y))
      (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) Subtype.val)
      (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (P ∘ (Subtype.val : freeLocus Γ Y → Y)) (ρ.comp (MonoidHom.id Γ))
      (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (torusFamilyBaseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y) (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) b hb)
      (torusFamilyProjection_baseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y)
        (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) hbmul)
    letI := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
    letI := continuousConstSMul_torusFamilyBaseChangeAffineMulAction
      R hone hmul P (fun l ↦ (hP l).continuous) ρ hequiv b hb hbone hbmul
      (MonoidHom.id Γ) (f := (Subtype.val : freeLocus Γ Y → Y)) continuous_subtype_val
      (fun _ _ ↦ rfl) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
    letI := hfreeY
    letI := isCancelSMul_torusFamilyAffineMulAction
      (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (z : Y))
      (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) Subtype.val)
      (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (P ∘ (Subtype.val : freeLocus Γ Y → Y)) (ρ.comp (MonoidHom.id Γ))
      (period_baseChange_equivariant R P ρ hequiv (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (torusFamilyBaseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y) (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) b hb)
      (torusFamilyProjection_baseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y)
        (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) hbmul)
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) m
      (MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineBaseChangeHom P b hb R ρ hequiv hone hmul hbone hbmul
          (MonoidHom.id Γ) (Subtype.val : freeLocus Γ Y → Y) fun _ _ ↦ rfl)) :=
  contMDiff_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom P hinj hP R hone hmul ρ hequiv
    b hb hbone hbmul hR hbc (MonoidHom.id Γ) (Subtype.val : freeLocus Γ Y → Y)
    (contMDiff_subtype_val (U := ⟨_, isOpen_freeLocus Γ Y⟩) :
      ContMDiff I I n (Subtype.val : freeLocus Γ Y → Y))
    (fun _ _ ↦ rfl) hfreeY
    (isCancelSMul_torusFamilyAffineMulAction _ _ _ _ _ _ _ _ _ _) hm

end FreeLocus

end TauCeti
