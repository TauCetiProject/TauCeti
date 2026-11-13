/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# Smooth translations and diffeomorphisms from group actions

This file packages the action of an element of a group with a `ContMDiffConstSMul` instance as a
self-diffeomorphism. Unlike `Diffeomorph.smul`, this construction does not require a manifold
structure on the acting group or joint smoothness of the action. Smooth multiplication supplies
the required smoothness of individual left translations via a self-action instance, as does
smooth addition for additive translations.

It also records that pointwise smoothness of the action of an element of finite order passes to
the finite cyclic group it generates, since every element of that group acts by an iterate.

Finally, an action by `C^n` maps stays one after a continuous linear change of the model vector
space, and after restricting the scalars of a self-modelled manifold. Both operations keep the
charted space, so the quotient atlas of a free, properly discontinuous action
(`MulAction.instChartedSpaceQuotient`) is literally the same atlas for the new model. The quotient
manifold theorem `TauCeti.instIsManifoldQuotient` and the local diffeomorphism
`TauCeti.isLocalDiffeomorph_quotientMk` therefore apply to the new model on the same orbit space.
For a linear change of model, Mathlib's `ContinuousLinearEquiv.toTransContinuousLinearEquiv`
is the identity comparison diffeomorphism there. In particular, the quotient of a complex
manifold by an action by biholomorphisms has as underlying real manifold the quotient of the
underlying real manifold.

## Main declarations

* `ContMDiffMul.contMDiffConstSMul`: smooth multiplication gives smooth left translations.
* `SetLike.contMDiffConstSMul`: a subobject, such as a submonoid, a subgroup or a submodule, of
  a type acting by `C^n` maps also acts by `C^n` maps.
* `ContMDiffSMul.contMDiff_smul_const`: the orbit maps `g ↦ g • x` of a `C^n` action are `C^n`.
* `ContMDiffSMul.mdifferentiableAt_smul_const`: the orbit maps of a `C^1` action are
  differentiable.
* `ContMDiffSMul.prod_of_smul_eq`: an action on `M × N` through `C^n` maps to groups acting by
  `C^n` actions on `M` and on `N`, such as the factorwise action of a product group, is `C^n`.
* `ContMDiffSMul.contMDiffOn_comp_smul_symm`: in the coordinates `(w, g) ↦ e (g • e.symm w)` of
  a `C^n` partial homeomorphism `e` with `C^n` inverse, a `C^n` action is jointly `C^n`.
* `ContinuousLinearEquiv.contMDiffConstSMul_transContinuousLinearEquiv_iff`: a linear change of
  the model vector space does not change whether an action is by `C^n` maps.
* `ContMDiffConstSMul.restrictScalars`: an action by maps that are `C^n` over `𝕜'` is by maps that
  are `C^n` over a smaller field `𝕜`; for instance, biholomorphisms are diffeomorphisms.
* `Diffeomorph.constSmul`: the diffeomorphism given by a fixed element of a pointwise-smooth
  group action. It sends the identity element to the identity diffeomorphism and products to
  composites (`Diffeomorph.constSmul_one`, `Diffeomorph.constSmul_mul`).
* `Diffeomorph.constSmul_injective`, `Diffeomorph.infinite_of_faithfulSMul`: for a faithful
  action these diffeomorphisms are distinct, so an infinite group acting faithfully gives
  infinitely many diffeomorphisms.
* `TauCeti.contMDiff_smul_of_mem_zpowers`: if an element of finite order acts by a `C^n` map, so
  does every element of the cyclic group it generates.
-/

public section

open scoped ContDiff Manifold

/-- Smooth multiplication makes each left translation smooth. -/
@[to_additive /-- Smooth addition makes each left translation smooth. -/]
instance ContMDiffMul.contMDiffConstSMul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H G]
    {n : ℕ∞ω} [ContMDiffMul I n G] : ContMDiffConstSMul I n G G where
  contMDiff_const_smul _ := contMDiff_mul_left

/-- A subobject `s` of a type `G` acting on `M` by `C^n` maps, such as a submonoid, a subgroup or a
submodule of `G`, also acts on `M` by `C^n` maps. -/
@[to_additive /-- A subobject `s` of a type `G` acting additively on `M` by `C^n` maps, such as an
additive submonoid, an additive subgroup or a submodule of `G`, also acts on `M` by `C^n` maps. -/]
instance SetLike.contMDiffConstSMul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {G S : Type*} [SetLike S G] [SMul G M]
    [ContMDiffConstSMul I n G M] (s : S) : ContMDiffConstSMul I n s M where
  contMDiff_const_smul g := contMDiff_const_smul (g : G)

/-- The orbit map `g ↦ g • x` of a `C^n` action is `C^n`. -/
@[to_additive /-- The orbit map `g ↦ g +ᵥ x` of a `C^n` additive action is `C^n`. -/]
theorem ContMDiffSMul.contMDiff_smul_const {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [SMul G M] {n : ℕ∞ω}
    [ContMDiffSMul I I' n G M] (x : M) : ContMDiff I I' n fun g : G ↦ g • x :=
  contMDiff_id.smul contMDiff_const

/-- The orbit map `g ↦ g • x` of a `C^1` action is differentiable. -/
@[to_additive /-- The orbit map `g ↦ g +ᵥ x` of a `C^1` additive action is differentiable. -/]
theorem ContMDiffSMul.mdifferentiableAt_smul_const {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [SMul G M]
    [ContMDiffSMul I I' 1 G M] (x : M) (g : G) : MDifferentiableAt I I' (fun h : G ↦ h • x) g :=
  (contMDiff_smul_const (n := 1) x).mdifferentiableAt one_ne_zero

/-- **Factorwise actions on products.** Let `K` act on `M × N` through `C^n` maps `φ : K → G` and
`ψ : K → G'` into groups acting by `C^n` actions on `M` and on `N`,
`k • (x, y) = (φ k • x, ψ k • y)`. Then the action of `K` is `C^n`. For instance, `G × G'` acting
factorwise on `M × N`, with `φ` and `ψ` the two projections. -/
theorem ContMDiffSMul.prod_of_smul_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 F HF}
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {HF' : Type*} [TopologicalSpace HF'] {IF' : ModelWithCorners 𝕜 F' HF'}
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK]
    {HK : Type*} [TopologicalSpace HK] {IK : ModelWithCorners 𝕜 EK HK}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
    {G' : Type*} [TopologicalSpace G'] [ChartedSpace HF G']
    {K : Type*} [TopologicalSpace K] [ChartedSpace HK K]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace HF' N]
    [SMul G M] [SMul G' N] [SMul K (M × N)] {n : ℕ∞ω}
    [ContMDiffSMul I I' n G M] [ContMDiffSMul IF IF' n G' N] {φ : K → G} {ψ : K → G'}
    (hφ : ContMDiff IK I n φ) (hψ : ContMDiff IK IF n ψ)
    (hsmul : ∀ (k : K) (p : M × N), k • p = (φ k • p.1, ψ k • p.2)) :
    ContMDiffSMul IK (I'.prod IF') n K (M × N) where
  contMDiff_smul := by
    simp only [hsmul]
    exact ((hφ.comp contMDiff_fst).smul (contMDiff_fst.comp contMDiff_snd)).prodMk
      ((hψ.comp contMDiff_fst).smul (contMDiff_snd.comp contMDiff_snd))

/-- In the coordinates of a `C^n` partial homeomorphism `e` with `C^n` inverse, a `C^n` action is
the jointly `C^n` map `(w, g) ↦ e (g • e.symm w)` on the set of pairs for which it is defined.
That set is open (`OpenPartialHomeomorph.isOpen_setOf_mem_target_smul_symm_mem_source`). -/
@[to_additive /-- In the coordinates of a `C^n` partial homeomorphism `e` with `C^n` inverse, a
`C^n` additive action is the jointly `C^n` map `(w, g) ↦ e (g +ᵥ e.symm w)` on the set of pairs
for which it is defined. -/]
theorem ContMDiffSMul.contMDiffOn_comp_smul_symm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [SMul G M] {n : ℕ∞ω}
    [ContMDiffSMul I I' n G M] {e : OpenPartialHomeomorph M F}
    (he : ContMDiffOn I' 𝓘(𝕜, F) n e e.source) (hes : ContMDiffOn 𝓘(𝕜, F) I' n e.symm e.target) :
    ContMDiffOn (𝓘(𝕜, F).prod I) 𝓘(𝕜, F) n (fun p : F × G ↦ e (p.2 • e.symm p.1))
      {p : F × G | p.1 ∈ e.target ∧ p.2 • e.symm p.1 ∈ e.source} := by
  have hj : ContMDiffOn (𝓘(𝕜, F).prod I) (I.prod I') n (fun p : F × G ↦ (p.2, e.symm p.1))
      {p : F × G | p.1 ∈ e.target ∧ p.2 • e.symm p.1 ∈ e.source} :=
    contMDiffOn_snd.prodMk (hes.comp contMDiffOn_fst fun p hp ↦ hp.1)
  exact he.comp ((contMDiff_smul (I := I) (I' := I') (n := n)).comp_contMDiffOn hj)
    fun p hp ↦ hp.2

/-! ### Changes of model -/

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SMul G M] {n : ℕ∞ω}

/-- Changing the vector-space coordinates of the model by a continuous linear equivalence does not
change whether a type acts by `C^n` maps. The charted space is unchanged. -/
@[to_additive (attr := simp) /-- Changing the vector-space coordinates of the model by a
continuous linear equivalence does not change whether a type acts additively by `C^n` maps. The
charted space is unchanged. -/]
theorem contMDiffConstSMul_transContinuousLinearEquiv_iff (e : E ≃L[𝕜] F) :
    ContMDiffConstSMul (I.transContinuousLinearEquiv e) n G M ↔ ContMDiffConstSMul I n G M :=
  ⟨fun h ↦ ⟨fun g ↦ by simpa using h.contMDiff_const_smul g⟩,
    fun h ↦ ⟨fun g ↦ by simpa using h.contMDiff_const_smul g⟩⟩

/-- An action by `C^n` maps remains an action by `C^n` maps after a linear change of the model
vector space, so that quotients by it inherit the transported model. -/
@[to_additive /-- An additive action by `C^n` maps remains an additive action by `C^n` maps after
a linear change of the model vector space. -/]
instance instContMDiffConstSMulTransContinuousLinearEquiv [ContMDiffConstSMul I n G M]
    (e : E ≃L[𝕜] F) : ContMDiffConstSMul (I.transContinuousLinearEquiv e) n G M :=
  (contMDiffConstSMul_transContinuousLinearEquiv_iff e).2 ‹_›

end ContinuousLinearEquiv

namespace ContMDiffConstSMul

variable (𝕜 : Type*) {𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {G M : Type*} [TopologicalSpace M] [ChartedSpace E M] [SMul G M]
  {n : ℕ∞ω}

/-- An action by maps which are `C^n` over `𝕜'` is an action by maps which are `C^n` over the
smaller field `𝕜`, for the same charts. For instance, an action by biholomorphisms of a complex
manifold is an action by diffeomorphisms of the underlying real manifold. -/
@[to_additive (dont_translate := 𝕜 𝕜') /-- An additive action by maps which are `C^n` over `𝕜'`
is an additive action by maps which are `C^n` over the smaller field `𝕜`, for the same charts. -/]
theorem restrictScalars (h : ContMDiffConstSMul 𝓘(𝕜', E) n G M) :
    ContMDiffConstSMul 𝓘(𝕜, E) n G M :=
  ⟨fun g ↦ by simpa using (h.contMDiff_const_smul g).restrictScalars 𝕜⟩

end ContMDiffConstSMul

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [Group G] [MulAction G M] {n : ℕ∞ω} [ContMDiffConstSMul I n G M] (g : G)

variable (I n) in
/-- The diffeomorphism given by a fixed element of a pointwise `Cⁿ` group action. Its inverse is
scalar multiplication by the inverse group element. -/
@[to_additive
/-- The diffeomorphism given by a fixed element of a pointwise `Cⁿ` additive group action. Its
inverse is addition by the negated group element. -/]
def constSmul : M ≃ₘ^n⟮I, I⟯ M where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := contMDiff_const_smul g
  contMDiff_invFun := contMDiff_const_smul g⁻¹

/-- Evaluating the diffeomorphism associated to a fixed group element agrees with its action. -/
@[to_additive (attr := simp)
  /-- Evaluating the diffeomorphism associated to a fixed additive-group element agrees with its
  action. -/]
lemma constSmul_apply (x : M) : constSmul I n g x = g • x := (rfl)

/-- The inverse of the diffeomorphism associated to a fixed group element acts by its inverse. -/
@[to_additive (attr := simp)
  /-- The inverse of the diffeomorphism associated to a fixed additive-group element acts by its
  negation. -/]
lemma constSmul_symm_apply (x : M) : (constSmul I n g).symm x = g⁻¹ • x := (rfl)

/-- The diffeomorphism associated to a fixed group element is the function `x ↦ g • x`. -/
@[to_additive
  /-- The diffeomorphism associated to a fixed additive-group element is the function
  `x ↦ g +ᵥ x`. -/]
lemma coe_constSmul : ⇑(constSmul I n g : M ≃ₘ^n⟮I, I⟯ M) = fun x ↦ g • x := (rfl)

/-- The inverse of the diffeomorphism associated to a fixed group element is the function
`x ↦ g⁻¹ • x`. -/
@[to_additive
  /-- The inverse of the diffeomorphism associated to a fixed additive-group element is the
  function `x ↦ -g +ᵥ x`. -/]
lemma coe_constSmul_symm :
    ⇑(constSmul I n g : M ≃ₘ^n⟮I, I⟯ M).symm = fun x ↦ g⁻¹ • x := (rfl)

/-- Taking the inverse of a fixed-action diffeomorphism inverts the acting group element. -/
@[to_additive
  /-- Taking the inverse of a fixed-action diffeomorphism negates the acting additive-group
  element. -/]
lemma constSmul_symm :
    (constSmul I n g : M ≃ₘ^n⟮I, I⟯ M).symm = constSmul I n g⁻¹ :=
  Diffeomorph.ext fun x ↦ by
    rw [constSmul_symm_apply, constSmul_apply]

/-- The identity element acts by the identity diffeomorphism. -/
@[to_additive (attr := simp)
  /-- The zero element acts by the identity diffeomorphism. -/]
lemma constSmul_one : constSmul I n (1 : G) = Diffeomorph.refl I M n :=
  Diffeomorph.ext fun x ↦ one_smul G x

/-- The diffeomorphism of a product of group elements is the composite of their diffeomorphisms,
the right-hand factor acting first. -/
@[to_additive
  /-- The diffeomorphism of a sum of additive-group elements is the composite of their
  diffeomorphisms, the right-hand summand acting first. -/]
lemma constSmul_mul (h : G) :
    constSmul I n (g * h) = (constSmul I n h).trans (constSmul I n g : M ≃ₘ^n⟮I, I⟯ M) :=
  Diffeomorph.ext fun x ↦ mul_smul g h x

/-- Distinct elements of a group acting faithfully give distinct diffeomorphisms. -/
@[to_additive
  /-- Distinct elements of an additive group acting faithfully give distinct diffeomorphisms. -/]
theorem constSmul_injective [FaithfulSMul G M] :
    Function.Injective (constSmul I n : G → M ≃ₘ^n⟮I, I⟯ M) :=
  fun _ _ h ↦ eq_of_smul_eq_smul fun x ↦ DFunLike.congr_fun h x

/-- An infinite group acting faithfully by `C^n` maps gives infinitely many `C^n`
self-diffeomorphisms. -/
@[to_additive /-- An infinite additive group acting faithfully by `C^n` maps gives infinitely many
`C^n` self-diffeomorphisms; for instance the translations of an infinite additive Lie group. -/]
theorem infinite_of_faithfulSMul [Infinite G] [FaithfulSMul G M] : Infinite (M ≃ₘ^n⟮I, I⟯ M) :=
  Infinite.of_injective _ (constSmul_injective (I := I) (n := n) (G := G))

end Diffeomorph

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [Group G] [MulAction G M]

/-- If `g` has finite order and acts by a `C^n` map, so does every element of the cyclic group
generated by `g`: it acts by an iterate of the action of `g`. -/
theorem contMDiff_smul_of_mem_zpowers {n : ℕ∞ω} {g : G} (hg : IsOfFinOrder g)
    (hsmooth : ContMDiff I I n fun x : M ↦ g • x) {k : G} (hk : k ∈ Subgroup.zpowers g) :
    ContMDiff I I n fun x : M ↦ k • x := by
  obtain ⟨m, rfl⟩ := hg.mem_powers_iff_mem_zpowers.mpr hk
  simpa [smul_iterate] using hsmooth.iterate m

end TauCeti
